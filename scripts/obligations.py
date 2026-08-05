#!/usr/bin/env python3
"""Count PROOF OBLIGATIONS per master, so cost can be judged at a fair caliber.

WHY THIS EXISTS. The project measured check cost as seconds per LINE and got a
comparison that flatters one tree and slanders the other. The retiring subtree
reads 0.013 s/line and the surviving trunk 0.104, an eight-fold gap, but lines
are not units of mathematical content:

  - A generic pattern instantiated sixteen times writes sixteen short bodies
    and counts as sixteen times the content. It is not.
  - A hard theorem whose proof is four dense lines counts as almost nothing.
  - Verbose bookkeeping and a deep argument weigh the same per line.

So `s/line` cannot answer the question the owner actually asked, which is how
much of the surviving trunk's cost is MATHEMATICS and how much is engineering.
A tree with many cheap mechanical obligations will always look efficient per
line no matter how it is written.

The fair unit is the OBLIGATION: one named result that has to be discharged.
That is what a formalization actually produces, and it is invariant to how
verbosely the discharge is written.

WHAT COUNTS AS ONE OBLIGATION. A top-level type signature in the module body:
`name : Type`, including operators (`_∈ˢ_ : ...`) and multi-name signatures
(`f g : A` counts as two, since each is separately discharged).

WHAT DOES NOT. Everything that is structure rather than a discharged claim:
`data`, `record`, and `module` headers, `open`/`import`, `variable`, fixity,
`syntax`, `pattern`, pragmas, and anything indented, which is a `where`-local
helper rather than a stated result. Locals are counted separately and reported,
because a module that hides forty helpers under one export is doing real work
that the export count alone would miss.

THE LIMIT OF THIS TOOL, STATED PLAINLY. It counts obligations; it cannot weigh
them. One `Σ₁`-absoluteness theorem is not one `refl` lemma. So the per-
obligation figure is FAIRER than per-line, not FAIR: it removes the verbosity
bias and the mechanical-multiplicity bias, and it leaves the difficulty bias
untouched. Read it as a floor on the comparison, not a verdict. Where two
modules differ by an order of magnitude per obligation, that gap survives any
plausible reweighting; where they differ by 30 percent, it does not.

USAGE
    python3 scripts/obligations.py                    # every master, with s/obligation
    python3 scripts/obligations.py --by-tree          # retiring vs surviving
    python3 scripts/obligations.py src/L/Foo.lagda.md
"""

from __future__ import annotations

import argparse
import re
import sys
import tomllib
from pathlib import Path

ROOT = Path(__file__).resolve().parent.parent
SRC = ROOT / "src"
LEDGER = ROOT / "dev" / "ledger.toml"

# Structure, not a discharged claim.
STRUCTURE = re.compile(
    r"^(data|record|module|open|import|private|variable|instance|postulate|"
    r"infix\w*|syntax|pattern|abstract|opaque|mutual|unquote|macro|where|"
    r"interleaved|primitive|constructor|field|renaming|using|hiding|"
    r"\{-#|--|\{-)\b"
)

# `name : type` or `f g h : type` at column 0. Names may be operators
# (`_∈ˢ_`), primed, subscripted, or unicode; Agda allows nearly anything that
# is not whitespace, a bracket, or a lone colon.
SIGNATURE = re.compile(r"^([^\s:;{}()@\"]+(?:\s+[^\s:;{}()@\"]+)*)\s*:(?!:)\s")


def scan(path: Path) -> dict:
    """Return counts for one master: obligations, locals, structure, lines."""
    obligations = 0
    local_obligations = 0
    structures = 0
    lines = 0
    inside = False

    for raw in path.read_text(encoding="utf-8").splitlines():
        stripped = raw.strip()
        if stripped.startswith("```"):
            if not inside and re.match(r"^```+\s*agda\b", stripped):
                inside = True
            elif inside:
                inside = False
            continue
        if not inside or not stripped:
            continue
        lines += 1

        # Agda's layout rule makes a continuation line indent past the
        # declaration it continues, so a column-0 line is ALWAYS a new
        # declaration. No continuation tracking is needed, and the first
        # version of this file was wrong because it tried: it swallowed the
        # declaration that ended each signature, halving the count.
        top_level = raw[:1] not in (" ", "\t")

        if STRUCTURE.match(stripped):
            if top_level:
                structures += 1
            continue

        m = SIGNATURE.match(raw if top_level else stripped)
        if not m:
            continue
        # `f g : A` discharges two obligations.
        names = [n for n in m.group(1).split() if n not in ("|",)]
        # A definition clause `f x y = ...` has no colon, so it never lands
        # here; but a lambda-bound `(x : A)` would, hence the column check.
        if top_level:
            obligations += len(names)
        else:
            local_obligations += len(names)

    return {
        "obligations": obligations,
        "locals": local_obligations,
        "structures": structures,
        "lines": lines,
    }


def module_name(path: Path) -> str:
    return str(path.relative_to(SRC)).removesuffix(".lagda.md").replace("/", ".")


RETIRING_ROOTS = ("L.Coding", "L.Godel", "L.Choice")


def main() -> int:
    ap = argparse.ArgumentParser(
        description=__doc__, formatter_class=argparse.RawDescriptionHelpFormatter
    )
    ap.add_argument("paths", nargs="*", type=Path)
    ap.add_argument("--by-tree", action="store_true")
    args = ap.parse_args()

    if args.paths:
        masters = [p if p.is_absolute() else ROOT / p for p in args.paths]
    else:
        masters = sorted(SRC.rglob("*.lagda.md"))
    masters = [p for p in masters if p.name != "Everything.lagda.md"]

    seconds = {}
    if LEDGER.exists():
        data = tomllib.loads(LEDGER.read_text(encoding="utf-8"))
        seconds = {r["module"]: r["seconds"] for r in data.get("hot", [])}

    rows = []
    for path in masters:
        r = scan(path)
        if r["lines"] == 0:
            continue
        r["module"] = module_name(path)
        r["seconds"] = seconds.get(r["module"])
        rows.append(r)

    if args.by_tree:
        for label, pred in (
            ("retiring subtree", lambda m: m.startswith(RETIRING_ROOTS)),
            ("surviving trunk", lambda m: not m.startswith(RETIRING_ROOTS)),
        ):
            sel = [r for r in rows if pred(r["module"])]
            ob = sum(r["obligations"] for r in sel)
            lo = sum(r["locals"] for r in sel)
            ln = sum(r["lines"] for r in sel)
            print(f"{label:22s} {len(sel):3d} modules  {ln:6d} lines  "
                  f"{ob:5d} obligations  {lo:5d} locals   "
                  f"{ln / ob:5.1f} lines/obligation")
        return 0

    print(f"{'module':38s} {'lines':>6} {'oblig':>6} {'local':>6} {'L/ob':>6} {'s/ob':>7}")
    for r in sorted(rows, key=lambda r: -(r["seconds"] or 0)):
        per = f"{r['lines'] / r['obligations']:6.1f}" if r["obligations"] else "     -"
        sob = (f"{r['seconds'] / r['obligations']:7.2f}"
               if r["seconds"] and r["obligations"] else "      -")
        print(f"{r['module']:38s} {r['lines']:6d} {r['obligations']:6d} "
              f"{r['locals']:6d} {per} {sob}")
    return 0


if __name__ == "__main__":
    sys.exit(main())
