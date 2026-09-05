#!/usr/bin/env python3
"""[LJ-1.210] fence extractor.

Writes the ```agda fences of a literate master to a plain .agda file, in order
and with nothing else. The probe then edits only the header. Run it from the
repository root.

    .venv/bin/python agents/tasks/LJ-1-210/extract.py \
        src/L/Coding/Model.lagda.md agents/tasks/LJ-1-210/Gen/ModelBody.agda
"""

import sys


def main() -> None:
    src, dst = sys.argv[1], sys.argv[2]
    out: list[str] = []
    inside = False
    for line in open(src, encoding="utf-8"):
        stripped = line.rstrip("\n")
        if stripped.startswith("```agda"):
            inside = True
            continue
        if stripped.startswith("```"):
            inside = False
            continue
        if inside:
            out.append(stripped)
    with open(dst, "w", encoding="utf-8") as fh:
        fh.write("\n".join(out) + "\n")
    print(f"{dst}: {len(out)} lines, {sum(1 for x in out if x.strip())} non-blank")


if __name__ == "__main__":
    main()
