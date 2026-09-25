#!/usr/bin/env python3
"""Content-aware local cache for the complete Bedrock site build.

Agda's highlighted anchors and expression ranges describe code, while its
source hash also includes literate prose. When fenced code is byte-for-byte
unchanged, keep those certified code surfaces and weave the new prose around
them. Any change to the code blocks or their partition invokes Agda again.
"""

from __future__ import annotations

import argparse
import hashlib
import html
import json
import os
from pathlib import Path
import re
import subprocess
from outcrop.adapters.python_inputs import dependency_files


ROOT = Path(__file__).resolve().parents[2]
BUILD = ROOT / '_build'
HTML = BUILD / 'html'
STAMP = HTML / '.bedrock-checked'
TRACE = BUILD / 'outcrop-agda-types.jsonl'
TYPES = (BUILD / 'types.json', BUILD / 'expression-types.json')
CACHE = BUILD / 'cache'
INTERFACES = BUILD / '2.8.0/agda/src'
AGDA_HOME = BUILD / 'agda-home'
BACKEND_STATE = CACHE / 'site-backend.json'
FENCE = re.compile(r'^```agda[^\n]*\n(.*?)^```[ \t]*$', re.M | re.S)
PRE = re.compile(r'<pre class="Agda">(.*?)</pre>', re.S)
TAG = re.compile(r'<[^>]*>')


def digest(path: Path) -> str:
    return hashlib.sha256(path.read_bytes()).hexdigest()


def combined_digest(paths: list[Path]) -> str | None:
    result = hashlib.sha256()
    for path in sorted(paths):
        if not path.is_file():
            return None
        name = path.relative_to(ROOT) if path.is_relative_to(ROOT) else path
        result.update(str(name).encode() + b'\0')
        result.update(bytes.fromhex(digest(path)))
    return result.hexdigest()


def source_paths() -> dict[str, Path]:
    return {'.'.join(path.relative_to(ROOT / 'src').with_suffix('').with_suffix('').parts): path
            for path in sorted((ROOT / 'src').rglob('*.lagda.md'))}


def source_inventory(paths: dict[str, Path]) -> dict[str, dict]:
    result = {}
    for module, path in paths.items():
        raw = path.read_bytes()
        blocks = [hashlib.sha256(match.group(1).encode()).hexdigest()
                  for match in FENCE.finditer(raw.decode('utf-8'))]
        result[module] = {'source': hashlib.sha256(raw).hexdigest(), 'blocks': blocks}
    return result


def backend_inputs() -> list[Path]:
    agda_adapter = ROOT / 'outcrop/src/outcrop/adapters/agda'
    return [
        BUILD / 'outcrop-agda/install/outcrop-agda.json',
        AGDA_HOME / '.bedrock-library-lock.json',
        ROOT / 'bedrock.agda-lib',
        ROOT / 'outcrop/src/outcrop/core/source_syntax.py',
        ROOT / 'site/agda-libraries.json',
        *(path for path in agda_adapter.rglob('*') if path.is_file()
          and '__pycache__' not in path.parts
          and path.suffix in {'.py', '.json', '.patch', '.hs'}),
    ]


def backend_identity() -> str | None:
    return combined_digest(backend_inputs())


def extractor_inputs() -> list[Path]:
    return [
        ROOT / 'outcrop/src/outcrop/adapters/extract_types.py',
        ROOT / 'outcrop/src/outcrop/adapters/extract_expression_types.py',
        ROOT / 'scripts/site/extract-types.py',
        ROOT / 'scripts/site/extract-expression-types.py',
    ]


def extractor_identity() -> str | None:
    return combined_digest(extractor_inputs())


def render_identity() -> str | None:
    from outcrop.site.site_config import SiteConfig
    package = ROOT / 'outcrop/src/outcrop'
    config_path = ROOT / 'site/project.json'
    config = SiteConfig.load(config_path, root=ROOT)
    inputs = [*dependency_files(package, [ROOT / 'scripts/site/render-site.py']),
              ROOT / 'outcrop/pyproject.toml', config_path,
              *(config.path(value) for value in
                (config.catalog, config.glossary, config.favicon, config.logo) if value),
              *(path for path in (package / 'site/resources').rglob('*') if path.is_file())]
    return combined_digest(list(set(inputs)))


def key_digest(value) -> str:
    return hashlib.sha256(json.dumps(value, sort_keys=True).encode()).hexdigest()


def validate_artifact(backend, paths, current):
    if (backend is None or backend.get('sources') != current
            or not backend.get('producer')
            or backend.get('extractor') != extractor_identity()
            or not all(highlighted_path(module).is_file() for module in paths)
            or not all(path.is_file() for path in TYPES)):
        raise RuntimeError('site backend artifact is missing or does not match source/extractor')


def archive_keys(args):
    """Use the same content identities locally and in Actions, not broad globs.

    Archive prefixes only choose a candidate. Restored files still pass the
    normal producer/source/extractor checks before any work can be skipped.
    """
    paths = source_paths()
    current = source_inventory(paths)
    keys = {'source': key_digest({module: item['source'] for module, item in current.items()})}
    if args.cache_keys == 'backend':
        keys.update(backend=backend_identity(), extractor=extractor_identity())
    else:
        backend = read_state(BACKEND_STATE)
        validate_artifact(backend, paths, current)
        keys['render'] = key_digest(render_build_key(current, backend, args.langs.split(','), args.base_url))
    if any(value is None for value in keys.values()):
        raise RuntimeError('cannot fingerprint missing cache inputs')
    return keys


def read_state(path: Path) -> dict | None:
    try:
        state = json.loads(path.read_text(encoding='utf-8'))
        return state if state.get('schema') == 1 else None
    except (OSError, ValueError, AttributeError):
        return None


def write_state(path: Path, state: dict) -> None:
    path.parent.mkdir(parents=True, exist_ok=True)
    temporary = path.with_suffix('.tmp')
    temporary.write_text(json.dumps(state, ensure_ascii=False, sort_keys=True) + '\n',
                         encoding='utf-8')
    temporary.replace(path)


def highlighted_path(module: str) -> Path:
    return HTML / f'{module}.md'


def reweave(module: str, path: Path) -> str | None:
    """Return fresh prose with certified code blocks, or decline unsafe reuse."""
    highlighted = highlighted_path(module)
    if not highlighted.is_file():
        return None
    source = path.read_text(encoding='utf-8')
    old = highlighted.read_text(encoding='utf-8')
    blocks = list(FENCE.finditer(source))
    pres = list(PRE.finditer(old))
    if len(blocks) != len(pres):
        return None
    for block, pre in zip(blocks, pres):
        plain = html.unescape(TAG.sub('', pre.group(1)))
        if plain != block.group(1):
            return None
    replacement = iter(pre.group(0) for pre in pres)
    return FENCE.sub(lambda _: next(replacement), source)


def adopt_backend(paths: dict[str, Path]) -> bool:
    """Trust an earlier full build only when its outputs still match every master."""
    if not STAMP.is_file() or not TRACE.is_file():
        return False
    built_at = STAMP.stat().st_mtime_ns
    if any(path.stat().st_mtime_ns > built_at
           for path in [*paths.values(), *backend_inputs()]):
        return False
    return all(reweave(module, path) is not None for module, path in paths.items())


def run(command: list[str]) -> None:
    print('+ ' + ' '.join(command), flush=True)
    subprocess.run(command, cwd=ROOT, check=True)


def make_command(args, target):
    """Pass supported paths explicitly across the Python/Make boundary."""
    return [args.make, target, f'PY={args.py}', f'AGDA_JOBS={args.agda_jobs}',
            f'LOCAL_PARALLEL={args.local_parallel}', f'HTML_DIR={HTML}',
            f'AGDA_TRACE={TRACE}', f'AGDA_DIR={AGDA_HOME}', f'SITE_IFACES={INTERFACES}']


def site_state_path(out: Path) -> Path:
    name = hashlib.sha256(str(out.resolve()).encode()).hexdigest()[:16]
    return CACHE / f'render-{name}.json'


def output_present(out: Path, langs: list[str]) -> bool:
    return ((out / 'search-content.json').is_file()
            and all((out / lang / 'index.html').is_file() for lang in langs))


def render_build_key(current: dict[str, dict], backend: dict, langs: list[str],
                     base_url: str) -> dict:
    code = {module: info['blocks'] for module, info in current.items()}
    code_hash = hashlib.sha256(json.dumps(code, sort_keys=True).encode()).hexdigest()
    return {'render': render_identity(), 'producer': backend['producer'],
            'code': code_hash, 'types': [digest(path) for path in TYPES],
            'langs': langs, 'base_url': base_url}


def render_command(args):
    return [args.py, 'scripts/site/render-site.py', '--html-dir', str(HTML),
            '--out', str(args.site_out), '--langs', args.langs, '--base-url', args.base_url]


def build(args) -> None:
    if getattr(args, 'force_render', False):
        # Preserve the diagnostic site-render contract: no compiler or backend
        # state is required. Invalidate only this output's render receipt, so a
        # manual render with different options cannot become a false cache hit.
        site_state_path(Path(args.site_out)).unlink(missing_ok=True)
        run(render_command(args))
        return
    paths = source_paths()
    current = source_inventory(paths)
    backend = read_state(BACKEND_STATE)
    if args.render_only:
        validate_artifact(backend, paths, current)
    else:
        backend = prepare_backend(args, paths, current, backend)
    if args.backend_only:
        return

    out = Path(args.site_out)
    langs = args.langs.split(',')
    site_state = read_state(site_state_path(out))
    build_key = render_build_key(current, backend, langs, args.base_url)
    source_hashes = {module: info['source'] for module, info in current.items()}
    output_valid = output_present(out, langs)
    if (output_valid and site_state is not None and site_state.get('key') == build_key
            and site_state.get('sources') == source_hashes):
        print('site cache: pages, search and assets are current', flush=True)
        return

    code_key = key_digest(build_key)
    command = render_command(args) + ['--code-cache', str(CACHE / 'code-context.json.gz'),
                                      '--code-cache-key', code_key]
    site_changed = {module for module, source in source_hashes.items()
                    if source != (site_state or {}).get('sources', {}).get(module)}
    incremental = (output_valid and site_state is not None
                   and site_state.get('key') == build_key and site_changed
                   and set(site_state.get('sources', {})) == set(source_hashes))
    if incremental:
        selected = sorted(site_changed | {'Origin'})
        for module in selected:
            command.extend(['--module', module])
        command.append('--incremental')
        print(f'site cache: updating {len(selected)} affected chapter(s)', flush=True)
    else:
        print('site cache: rendering the complete site', flush=True)
    run(command)
    write_state(site_state_path(out), {'schema': 1, 'key': build_key,
                                       'sources': source_hashes})


def prepare_backend(args, paths: dict[str, Path], current: dict[str, dict],
                    backend: dict | None) -> dict:
    producer = backend_identity()
    extractor = extractor_identity()
    adopted = False
    # Local adoption supports a manual `make html` build predating receipts.
    # CI archive fallback must never certify evidence by restored timestamps.
    allow_adoption = os.environ.get('CI', '').lower() not in {'1', 'true'}
    if backend is None and producer is not None and allow_adoption and adopt_backend(paths):
        types_fresh = (all(path.is_file() for path in TYPES)
                       and all(input_.stat().st_mtime_ns <= min(path.stat().st_mtime_ns
                                                                for path in TYPES)
                               for input_ in extractor_inputs()))
        backend = {'schema': 1, 'producer': producer, 'sources': current,
                   'extractor': extractor if types_fresh else None,
                   'compile_stamp': STAMP.stat().st_mtime_ns,
                   'stamp': STAMP.stat().st_mtime_ns}
        write_state(BACKEND_STATE, backend)
        adopted = True

    changed = {module for module in current
               if backend is None or current[module]['source'] != backend['sources'].get(module, {}).get('source')}
    code_changed = (getattr(args, 'cold', False) or backend is None or producer != backend.get('producer')
                    or set(current) != set(backend.get('sources', {}))
                    or any(current[module]['blocks'] != backend['sources'].get(module, {}).get('blocks')
                           for module in current))
    external_rebuild = (not args.backend_only and backend is not None and STAMP.is_file()
                        and STAMP.stat().st_mtime_ns != backend.get('stamp'))
    if (not STAMP.is_file() or not TRACE.is_file()
            or any(not highlighted_path(module).is_file() for module in paths)):
        code_changed = True

    refreshed = {}
    if not code_changed:
        for module in changed:
            woven = reweave(module, paths[module])
            if woven is None:
                code_changed = True
                break
            refreshed[module] = woven

    rebuilt = False
    if code_changed:
        print('site cache: Agda inputs changed; rebuilding compiler evidence', flush=True)
        if backend is not None and producer == backend.get('producer'):
            for module in current:
                if current[module]['blocks'] != backend['sources'].get(module, {}).get('blocks'):
                    interface = INTERFACES / (module.replace('.', '/') + '.agdai')
                    interface.unlink(missing_ok=True)
            # Checkout/compiler-wrapper timestamps are not content identities.
            # Only a validated compatible producer may refresh the trace before
            # entering Make's timestamp-based lower-level HTML target.
            if TRACE.is_file():
                TRACE.touch()
        else:
            # An incompatible compiler or library must not reuse old trace records.
            TRACE.unlink(missing_ok=True)
            import shutil
            shutil.rmtree(INTERFACES, ignore_errors=True)
        STAMP.unlink(missing_ok=True)
        target = 'html-cold-parallel' if getattr(args, 'cold', False) else 'html'
        run(make_command(args, target))
        producer = backend_identity()
        backend = {'schema': 1, 'producer': producer, 'sources': current,
                   'extractor': None,
                   'compile_stamp': STAMP.stat().st_mtime_ns,
                   'stamp': STAMP.stat().st_mtime_ns}
        rebuilt = True
    elif external_rebuild:
        print('site cache: compiler output was rebuilt externally', flush=True)
        backend['compile_stamp'] = STAMP.stat().st_mtime_ns
        backend['stamp'] = STAMP.stat().st_mtime_ns
        rebuilt = True
    elif refreshed:
        for module, woven in refreshed.items():
            highlighted_path(module).write_text(woven, encoding='utf-8')
        backend['sources'] = current
        print(f'site cache: reused Agda evidence for {len(refreshed)} prose-only module(s)',
              flush=True)
    if code_changed or external_rebuild or refreshed or adopted:
        write_state(BACKEND_STATE, backend)

    missing_types = any(not path.is_file() for path in TYPES)
    extractor_changed = backend.get('extractor') != extractor
    if rebuilt or missing_types or extractor_changed:
        # A failed extractor must not certify leftover files from an older
        # compilation. The raw target cannot re-enter Make's timestamp check.
        backend['extractor'] = None
        write_state(BACKEND_STATE, backend)
        print('site cache: refreshing semantic products (rebuilt, missing or changed extractor)', flush=True)
        run(make_command(args, '_types'))
        backend['extractor'] = extractor
        write_state(BACKEND_STATE, backend)

    if not (rebuilt or missing_types or extractor_changed or refreshed):
        print('site cache: compiler evidence and semantic products are current', flush=True)

    return backend


def main(argv=None) -> int:
    global HTML, STAMP, TRACE, INTERFACES, AGDA_HOME
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--site-out', default='_build/site')
    parser.add_argument('--langs', default='en,zh,ja')
    parser.add_argument('--base-url', default='')
    parser.add_argument('--py', default='.venv/bin/python')
    parser.add_argument('--make', default='make')
    parser.add_argument('--agda-jobs', default='2')
    parser.add_argument('--local-parallel', default='1')
    parser.add_argument('--html-dir', type=Path, default=BUILD / 'html')
    parser.add_argument('--trace', type=Path, default=BUILD / 'outcrop-agda-types.jsonl')
    parser.add_argument('--agda-dir', type=Path,
                        default=Path(os.environ.get('AGDA_DIR', BUILD / 'agda-home')))
    parser.add_argument('--interface-root', type=Path, default=BUILD / '2.8.0/agda/src')
    parser.add_argument('--cold', action='store_true', help='explicitly rebuild the entire backend')
    parser.add_argument('--force-render', action='store_true', help='force rendering existing evidence without cache checks')
    parser.add_argument('--cache-keys', choices=('backend', 'render'),
                        help='print content fingerprints for Actions; do not build or change caches')
    mode = parser.add_mutually_exclusive_group()
    mode.add_argument('--backend-only', action='store_true')
    mode.add_argument('--render-only', action='store_true')
    args = parser.parse_args(argv)
    if args.cold and args.render_only:
        parser.error('--cold cannot be combined with --render-only')
    if args.force_render and not args.render_only:
        parser.error('--force-render requires --render-only')
    HTML, TRACE = args.html_dir.resolve(), args.trace.resolve()
    STAMP = HTML / '.bedrock-checked'
    INTERFACES, AGDA_HOME = args.interface_root.resolve(), args.agda_dir.resolve()
    if not INTERFACES.is_relative_to(BUILD) or INTERFACES == BUILD:
        parser.error('--interface-root must be a dedicated cache beneath _build')
    if args.cache_keys:
        for name, value in archive_keys(args).items():
            print(f'{name}={value}')
    else:
        build(args)
    return 0


if __name__ == '__main__':
    raise SystemExit(main())
