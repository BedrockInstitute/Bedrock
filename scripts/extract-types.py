#!/usr/bin/env python3
"""Extract per-module identifier types for type-on-hover and typed search, on stock Agda 2.8.0.

This is what makes type-on-hover possible WITHOUT forking 1lab's Agda-as-a-library tooling.
We drive Agda's batch interaction protocol (`agda --interaction-json`,
`Cmd_show_module_contents_toplevel`), which returns {name, type} for a module's contents.

To also cover the cubical / Agda library identifiers Bedrock references (so cubical defs get
hover too), we extract types for the WHOLE reachable module graph, i.e. every module that
`agda --html` emitted. A transitively-imported module is not in scope from `Everything`, so
we generate a small build-only loader that `import`s every reachable module directly, load it
once, then query each module. If that loader fails to typecheck (e.g. an unusual primitive
module), we fall back to loading `src/Everything.lagda.md` and extracting the internal
modules only (external hover is then simply absent, logged).

Output (JSON, to --out or stdout): { "<Module>": { "<bare-name>": "<type string>" } }.

Usage:
  extract-types.py [--html-dir _build/html] [--src src]
                   [--everything src/Everything.lagda.md] [--out FILE]
"""

import glob
import json
import os
import subprocess
import sys

AGGREGATOR = "Everything"   # no own definitions; never queried


def reachable_modules(html_dir):
    # agda --html emits <Module>.md for literate sources and <Module>.html for library
    # (non-literate) modules; both are reachable modules we want types for.
    files = glob.glob(os.path.join(html_dir, "*.md")) + glob.glob(os.path.join(html_dir, "*.html"))
    return sorted(set(os.path.basename(p).rsplit(".", 1)[0] for p in files))


def internal_modules(src):
    return set(os.path.relpath(p, src)[:-len(".lagda.md")].replace(os.sep, ".")
               for p in glob.glob(os.path.join(src, "**", "*.lagda.md"), recursive=True))


def run_agda(commands):
    proc = subprocess.run(["agda", "--interaction-json"], input=commands,
                          capture_output=True, text=True)
    if proc.returncode != 0 and not proc.stdout:
        sys.stderr.write(proc.stderr)
        raise SystemExit(f"agda --interaction-json failed (exit {proc.returncode})")
    return proc.stdout


def parse_contents(stdout):
    """In-order list of query responses: a {name: type} dict, or None on a query error."""
    out = []
    for line in stdout.splitlines():
        line = line.strip()
        if line.startswith("JSON> "):
            line = line[len("JSON> "):]
        if not line:
            continue
        try:
            obj = json.loads(line)
        except json.JSONDecodeError:
            continue
        if obj.get("kind") != "DisplayInfo":
            continue
        info = obj.get("info", {})
        if info.get("kind") == "ModuleContents":
            out.append({c["name"]: c["term"] for c in info.get("contents", [])})
        elif info.get("kind") == "Error":
            out.append(None)
    return out


def query(loader_abs, modules):
    cmds = f'IOTCM "{loader_abs}" NonInteractive Direct (Cmd_load "{loader_abs}" [])\n'
    for m in modules:
        cmds += (f'IOTCM "{loader_abs}" None Direct '
                 f'(Cmd_show_module_contents_toplevel Normalised "{m}")\n')
    responses = parse_contents(run_agda(cmds))
    result = {}
    for i, m in enumerate(modules):
        contents = responses[i] if i < len(responses) else None
        result[m] = contents or {}
    return result, sum(1 for v in result.values() if v)


def write_loader(typeext_dir, src_abs, modules):
    os.makedirs(typeext_dir, exist_ok=True)
    with open(os.path.join(typeext_dir, "typeext.agda-lib"), "w", encoding="utf-8") as fh:
        fh.write(f"name: bedrock-typeext\ninclude: . {src_abs}\ndepend: cubical\n"
                 f"flags: -WnoUnsupportedIndexedMatch\n")
    body = "{-# OPTIONS --cubical --safe --guardedness #-}\nmodule types-loader where\n"
    body += "".join(f"import {m}\n" for m in modules)
    path = os.path.join(typeext_dir, "types-loader.agda")
    with open(path, "w", encoding="utf-8") as fh:
        fh.write(body)
    return os.path.abspath(path)


def extract(html_dir, src, everything):
    reachable = reachable_modules(html_dir)
    queryable = [m for m in reachable if m != AGGREGATOR]
    if not queryable:
        return {}

    # Preferred path: a loader importing every reachable module, so all are in scope.
    typeext = os.path.join(os.path.dirname(html_dir) or ".", "typeext")
    loader = write_loader(typeext, os.path.abspath(src), reachable)
    result, hits = query(loader, queryable)
    if hits:
        return result

    # Fallback: internal modules only, via the committed aggregator.
    sys.stderr.write("warning: reachable-set loader yielded no types; "
                     "falling back to internal modules only (no external hover)\n")
    internal = internal_modules(src)
    internal_q = [m for m in queryable if m in internal]
    result, _ = query(os.path.abspath(everything), internal_q)
    return result


def main(argv):
    html_dir, src, everything, out = "_build/html", "src", "src/Everything.lagda.md", None
    i = 0
    while i < len(argv):
        a = argv[i]
        if a == "--html-dir": i += 1; html_dir = argv[i]
        elif a == "--src": i += 1; src = argv[i]
        elif a == "--everything": i += 1; everything = argv[i]
        elif a == "--out": i += 1; out = argv[i]
        else: sys.stderr.write(f"unknown option: {a}\n"); return 2
        i += 1

    data = extract(html_dir, src, everything)
    text = json.dumps(data, ensure_ascii=False, indent=2)
    if out:
        os.makedirs(os.path.dirname(out) or ".", exist_ok=True)
        with open(out, "w", encoding="utf-8") as fh:
            fh.write(text + "\n")
        typed = sum(1 for v in data.values() if v)
        sys.stderr.write(f"wrote types for {typed}/{len(data)} module(s) to {out}\n")
    else:
        print(text)
    return 0


if __name__ == "__main__":
    raise SystemExit(main(sys.argv[1:]))
