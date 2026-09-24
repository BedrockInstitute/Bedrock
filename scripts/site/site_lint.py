"""Strict reusable textbook lint, independent of an Agda toolchain or repository.

The pure engines are also used by the existing project gate adapters. Policies
select applicable source conventions; supplied exceptions are exact data, never
whole-project skip switches or inferred project-name special cases.
"""
from pathlib import Path
from dataclasses import dataclass
import argparse
import json
import re
from site_config import SiteConfig
from reading_routes import build_reading_data
from term_registry import load_entries
from term_lint import check_terms
from outline_lint import outline_errors
from chapter_structure import opening_errors
from prose_lint import analyze, ProsePolicy
from agda_lint import lint_text, AgdaPolicy, agda_lines
from fence_lint import fenced_comments, tight_language_boundaries, suspects
from diagram_style import check_text as diagram_errors
from glossary_lint import build_checks, build_presence, check_text, master_presence_violations
from i18n_markers import parse, lint_markers


@dataclass(frozen=True)
class Diagnostic:
    source: str
    line: int
    rule: str
    message: str

    def __str__(self):
        return f'{self.source}:{self.line}: [{self.rule}] {self.message}'


def lint_site(config, *, literary=False, project_checks=()):
    """Validate the configured corpus and all authored metadata; never mutate it."""
    root = config.path(config.sources)
    paths = {str(path.relative_to(root))[:-len(config.source_extension)].replace('/', '.'): path
             for path in sorted(root.rglob('*' + config.source_extension))}
    sources = {module: path.read_text(encoding='utf-8') for module, path in paths.items()}
    config.validate_references(sources)
    reading = build_reading_data(root, config.path(config.catalog), extension=config.source_extension,
        previews={config.landing_module} if config.landing_module else (),
        prerequisites=config.values.get('prerequisites'))
    entries = load_entries(config.path(config.glossary)) if config.glossary else []
    rows = [(entry['en'], entry['zh'], entry['ja'], entry.get('avoid', []),
             bool(entry.get('presence', False))) for entry in entries]
    checks, presence = build_checks(rows), build_presence(rows)
    results = []
    def report(source, rule, message, line=1):
        results.append(Diagnostic(str(source), line, rule, message))
    for error in check_terms(sources, entries, reading):
        report('terms', 'term-introduction', error)
    positions = {node['id']: node['order'] for node in reading['nodes']}
    for node in reading['nodes']:
        for dependency in node['prerequisites']:
            if dependency == config.landing_module or positions[dependency] >= node['order']:
                report(node['id'], 'reading-order', f'chapter precedes prerequisite {dependency}')
    legacy = {}
    if config.values.get('variable_legacy'):
        recorded = json.loads(config.path(config.values['variable_legacy']).read_text(encoding='utf-8'))
        if recorded.get('version') != 1:
            raise ValueError('variable_legacy: expected version 1')
        legacy = {chapter: set(lines) for chapter, lines in recorded['lines'].items()}
    agda_policy = AgdaPolicy(**config.values.get('agda_policy', {}))
    pragma = '{-# OPTIONS ' + ' '.join(agda_policy.options) + ' #-}'
    for module, text in sources.items():
        path = paths[module]
        marker_errors = lint_markers(text)
        for line, message in marker_errors:
            report(path, 'language-markers', message, line)
        if marker_errors:
            continue
        if literary:
            from literary_lint import analyze_text
            audit = analyze_text(text, str(path), module=module, internal=sources,
                visible_import_chapters=config.values.get('visible_import_chapters', ()),
                options=pragma)
            for error in audit['errors']:
                report(path, error['rule'], error['message'], error['line'] or 1)
        chapter = str(path.relative_to(root))
        policy = ProsePolicy(chapter=chapter, variable_legacy=legacy,
            numbered_theorems=tuple(config.values.get('numbered_theorems', {}).get(module, ())))
        _, fixable, manual = analyze(text, policy=policy)
        for item in fixable + manual:
            report(path, 'prose', item.message, text.count('\n', 0, item.index) + 1)
        if config.policies.get('trilingual', True):
            errors, count = outline_errors(text)
            if not count:
                errors.append('missing chapter title')
            for error in errors:
                report(path, 'chapter-outline', error)
            for kind, payload in parse(text):
                if kind == 'shared' and re.search(r'[\u3000-\u303f\u3400-\u9fff\uff01-\uff5e]', '\n'.join(payload)):
                    # Formal code is language-neutral, and its own character
                    # rule already diagnoses invalid prose inside a fence.
                    shared = re.sub(r'(?ms)^```.*?^```\s*$', '', '\n'.join(payload))
                    if re.search(r'[\u3000-\u303f\u3400-\u9fff\uff01-\uff5e]', shared):
                        report(path, 'shared-language', 'CJK prose outside a language group')
        if config.policies.get('formal_setup', True):
            for error in opening_errors(text, module, sources, options=pragma,
                    visible_import_chapters=config.values.get('visible_import_chapters', ())):
                report(path, 'chapter-opening', error)
        if agda_lines(text):
            for line, rule, message in lint_text(text, agda_policy):
                report(path, rule, message, line)
        for line, _ in fenced_comments(text):
            report(path, 'fenced-comment', 'move the comment into prose', line)
        for line in tight_language_boundaries(text):
            report(path, 'fence-language-boundary', 'insert a blank line before the language marker', line)
        for line, _ in suspects(text, 3):
            report(path, 'unfenced-agda', 'declaration-shaped code outside a fence', line)
        for error in diagram_errors(text):
            report(path, 'diagram', error)
        for line, _, message in check_text(text, checks):
            report(path, 'glossary', message, line)
        for _, message in master_presence_violations(str(path), text, presence):
            report(path, 'glossary-presence', message)
    for check in project_checks:
        results.extend(check(config))
    return results


def main(argv=None):
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--config', type=Path, required=True)
    parser.add_argument('--project-root', type=Path, required=True)
    parser.add_argument('--literary', action='store_true', help='also audit fence-local trilingual exposition')
    args = parser.parse_args(argv)
    config = SiteConfig.load(args.config, root=args.project_root)
    diagnostics = lint_site(config, literary=args.literary)
    for item in diagnostics:
        print(item)
    print(f'textbook-lint: {len(diagnostics)} error(s)')
    return bool(diagnostics)


if __name__ == '__main__':
    raise SystemExit(main())
