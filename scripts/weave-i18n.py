#!/usr/bin/env python3
"""Weave a multilingual literate-Agda master into per-language reading copies.

A master `.lagda.md` holds the Agda code once plus prose for every language, wrapped in
HTML-comment markers (grammar: dev/STYLE-i18n.md, implemented in i18n_markers.py).

For language L the weaver keeps the shared lines plus, in each group, the L sub-block
(falling back to English, then the first present language, when L is absent). Because the
code blocks live outside groups, they are copied verbatim and can never drift.

Usage:
  weave-i18n.py --lang LANG FILE                 weave one master -> stdout
  weave-i18n.py --gen --out DIR [--langs a,b,c] [--root src] [FILE ...]
                                                 weave masters -> DIR/<lang>/<relpath>
  weave-i18n.py --check [FILE ...]               validate marker integrity (exit 1 on error)

With no FILE, operates on the working-tree masters src/**/*.lagda.md.
"""

import glob
import os
import sys

from i18n_markers import LANGS, lint_markers, weave


def discover_masters():
    """All master .lagda.md under src/ in the working tree (tracked or not)."""
    return sorted(glob.glob("src/**/*.lagda.md", recursive=True))


def read(path):
    with open(path, encoding="utf-8") as fh:
        return fh.read()


def cmd_check(files):
    files = files or discover_masters()
    total = 0
    for path in files:
        for ln, msg in lint_markers(read(path)):
            print(f"{path}:{ln}: {msg}")
            total += 1
    if total:
        print(f"\n{total} marker problem(s).", file=sys.stderr)
        return 1
    return 0


def cmd_lang(lang, path):
    if lang not in LANGS:
        sys.stderr.write(f"unknown language: {lang} (known: {', '.join(LANGS)})\n")
        return 2
    sys.stdout.write(weave(read(path), lang))
    return 0


def cmd_gen(files, out_dir, langs, root):
    files = files or discover_masters()
    if not files:
        sys.stderr.write("no master .lagda.md files to weave\n")
        return 0
    root = root.rstrip("/") + "/" if root else ""
    written = 0
    for path in files:
        text = read(path)
        problems = lint_markers(text)
        if problems:
            for ln, msg in problems:
                print(f"{path}:{ln}: {msg}", file=sys.stderr)
            sys.stderr.write(f"refusing to weave {path}: fix marker problems first\n")
            return 1
        rel = path[len(root):] if root and path.startswith(root) else os.path.basename(path)
        for lang in langs:
            dest = os.path.join(out_dir, lang, rel)
            os.makedirs(os.path.dirname(dest), exist_ok=True)
            with open(dest, "w", encoding="utf-8") as fh:
                fh.write(weave(text, lang))
            written += 1
    # Drop a per-language .agda-lib so each woven tree is directly type-checkable and
    # `agda --html`-able on its own (the standard-toolchain compatibility guarantee).
    for lang in langs:
        lib_dir = os.path.join(out_dir, lang)
        if os.path.isdir(lib_dir):
            with open(os.path.join(lib_dir, "bedrock.agda-lib"), "w", encoding="utf-8") as fh:
                fh.write(f"name: bedrock-woven-{lang}\ninclude: .\ndepend: cubical\n"
                         f"flags: -WnoUnsupportedIndexedMatch\n")
    print(f"woven {written} file(s) into {out_dir}/<lang>/", file=sys.stderr)
    return 0


def main(argv):
    mode = None
    lang = None
    out_dir = "_build/woven"
    langs = LANGS[:]
    root = "src"
    files = []
    i = 0
    while i < len(argv):
        a = argv[i]
        if a == "--check":
            mode = "check"
        elif a == "--gen":
            mode = "gen"
        elif a == "--lang":
            mode = "lang"; i += 1; lang = argv[i]
        elif a == "--out":
            i += 1; out_dir = argv[i]
        elif a == "--langs":
            i += 1; langs = [x for x in argv[i].split(",") if x]
        elif a == "--root":
            i += 1; root = argv[i]
        elif a.startswith("-"):
            sys.stderr.write(f"unknown option: {a}\n")
            return 2
        else:
            files.append(a)
        i += 1

    if mode == "check":
        return cmd_check(files)
    if mode == "lang":
        if len(files) != 1:
            sys.stderr.write("--lang LANG needs exactly one FILE\n")
            return 2
        return cmd_lang(lang, files[0])
    if mode == "gen":
        return cmd_gen(files, out_dir, langs, root)
    sys.stderr.write(__doc__)
    return 2


if __name__ == "__main__":
    raise SystemExit(main(sys.argv[1:]))
