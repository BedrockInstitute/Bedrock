#!/usr/bin/env python3
"""Extract per-module identifier types for type-on-hover and typed search, on stock Agda 2.8.0.

This is what makes type-on-hover possible WITHOUT forking 1lab's Agda-as-a-library tooling.
We drive Agda's batch interaction protocol (`agda --interaction-json`,
`Cmd_show_module_contents_toplevel`), which returns {name, type} for a module's contents.

To also cover the cubical / Agda library identifiers Bedrock references (so cubical defs get
hover too), we extract types for the WHOLE reachable module graph, i.e. every module that
`agda --html` emitted. We generate a small build-only loader that `import`s every reachable
module directly, load it once, then query each module.

Output (JSON, to --out or stdout): { "<Module>": { "<bare-name>": "<type string>" } }.

Usage:
  extract-types.py [--agda PATH] [--html-dir _build/html] [--src src]
                   [--out FILE]
"""

import glob
import html
import json
import os
import re
import subprocess
import sys


DEF_RE = re.compile(
    r'<a id="(?P<name>[^"]+)"></a><a id="(?P<pos>\d+)"[^>]*'
    r'\bclass="(?P<aspect>[^"]+)"'
)
RENAMED_RE = re.compile(
    r'<a id="\d+" class="Symbol">to</a>[ \t]*'
    r'<a id="\d+" class="(?P<aspect>[^"]+)">(?P<name>[^<]+)</a>'
)

def reachable_modules(html_dir):
    """Follow generated module links from Origin, ignoring stale build files."""
    files = glob.glob(os.path.join(html_dir, "*.md")) + glob.glob(os.path.join(html_dir, "*.html"))
    available = {os.path.basename(path).rsplit(".", 1)[0]: path for path in files}
    if "Origin" not in available:
        return sorted(available)
    seen, pending = set(), ["Origin"]
    link = re.compile(r'href="([^"#]+)\.html(?:#[^"]*)?"')
    while pending:
        module = pending.pop()
        if module in seen or module not in available:
            continue
        seen.add(module)
        text = open(available[module], encoding="utf-8").read()
        pending.extend(target for target in link.findall(text)
                       if target in available and target not in seen)
    return sorted(seen)


def run_agda(commands, agda):
    proc = subprocess.run([agda, "--interaction-json"], input=commands,
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


def parse_inferred(stdout):
    """In-order inferred types delimited by explicit normal-form markers."""
    out, pending = [], None
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
        if info.get("kind") == "InferredType":
            pending = info.get("expr")
        elif info.get("kind") == "Error":
            pending = None
        elif (info.get("kind") == "NormalForm"
              and str(info.get("expr", "")).startswith('"BEDROCK-TYPE-MARK-')):
            out.append(pending)
            pending = None
    return out


def definition_names(html_dir, modules):
    """Return names which Agda made linkable at declaration sites."""
    result = {module: [] for module in modules}
    for module in modules:
        paths = [
            os.path.join(html_dir, module + suffix)
            for suffix in (".md", ".html")
        ]
        path = next((candidate for candidate in paths if os.path.exists(candidate)), None)
        if path is None:
            continue
        with open(path, encoding="utf-8") as source_file:
            source = source_file.read()
        result[module] = [
            (html.unescape(match.group("name")), match.group("aspect").split()[-1])
            for match in DEF_RE.finditer(source)
        ]
        result[module].extend(
            (html.unescape(match.group("name")), match.group("aspect").split()[-1])
            for match in RENAMED_RE.finditer(source)
            if match.group("aspect") not in {"Keyword", "Module"}
        )
    return result


def query(loader_abs, modules, agda):
    cmds = f'IOTCM "{loader_abs}" NonInteractive Direct (Cmd_load "{loader_abs}" [])\n'
    for m in modules:
        cmds += (f'IOTCM "{loader_abs}" None Direct '
                 f'(Cmd_show_module_contents_toplevel Simplified "{m}")\n')
    responses = parse_contents(run_agda(cmds, agda))
    result = {}
    for i, m in enumerate(modules):
        contents = responses[i] if i < len(responses) else None
        result[m] = contents or {}
    return result, sum(1 for v in result.values() if v)


def query_missing(loader_abs, missing, agda):
    """Infer linkable declarations omitted by the module-contents command.

    Agda 2.8's module listing omits pattern synonyms (including ``tt*``), as
    well as some declarations nested in records and modules.  A qualified
    top-level inference recovers every externally queryable omission while
    harmlessly leaving inaccessible private declarations unanswered.
    """
    if not missing:
        return {}
    commands = f'IOTCM {json.dumps(loader_abs)} NonInteractive Direct (Cmd_load {json.dumps(loader_abs)} [])\n'
    expressions = []
    for index, (module, name) in enumerate(missing):
        expression = f"{module}.{name}"
        expressions.append((module, name))
        commands += (
            f'IOTCM {json.dumps(loader_abs)} None Direct '
            f'(Cmd_infer_toplevel Simplified {json.dumps(expression)})\n'
            f'IOTCM {json.dumps(loader_abs)} None Direct '
            f'(Cmd_compute_toplevel DefaultCompute '
            f'{json.dumps(json.dumps(f"BEDROCK-TYPE-MARK-{index}"))})\n'
        )
    inferred = parse_inferred(run_agda(commands, agda))
    result = {}
    for (module, name), type_ in zip(expressions, inferred):
        if type_:
            result.setdefault(module, {})[name] = type_
    return result


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


def extract(html_dir, src, agda="agda"):
    reachable = reachable_modules(html_dir)
    queryable = reachable
    if not queryable:
        return {}

    # Preferred path: a loader importing every reachable module, so all are in scope.
    typeext = os.path.join(os.path.dirname(html_dir) or ".", "typeext")
    loader = write_loader(typeext, os.path.abspath(src), reachable)
    result, hits = query(loader, queryable, agda)
    if not hits:
        sys.stderr.write("warning: reachable-set loader yielded no type responses\n")
    definitions = definition_names(html_dir, reachable)
    missing = [
        (module, name)
        for module in reachable
        for name, aspect in definitions[module]
        if (aspect != "Module"
            and name not in result[module]
            and ("." in name or name.split(".")[-1] not in result[module]))
    ]
    recovered = query_missing(loader, missing, agda)
    for module, types in recovered.items():
        result[module].update(types)
    if missing:
        recovered_count = sum(len(types) for types in recovered.values())
        sys.stderr.write(
            f"recovered {recovered_count}/{len(missing)} omitted declaration type(s)\n"
        )
    return result


def main(argv):
    agda, html_dir, src, out = "agda", "_build/html", "src", None
    i = 0
    while i < len(argv):
        a = argv[i]
        if a == "--agda": i += 1; agda = argv[i]
        elif a == "--html-dir": i += 1; html_dir = argv[i]
        elif a == "--src": i += 1; src = argv[i]
        elif a == "--out": i += 1; out = argv[i]
        else: sys.stderr.write(f"unknown option: {a}\n"); return 2
        i += 1

    data = extract(html_dir, src, agda)
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
