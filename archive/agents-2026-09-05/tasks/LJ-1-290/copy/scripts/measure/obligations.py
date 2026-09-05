#!/usr/bin/env python3
"""Count the size of a formalization at SEVERAL calibers at once.

WHY MORE THAN ONE. The project measured check cost as seconds per LINE, got an
eight-fold gap between two trees, and built a plan on it. Lines are a poor unit
of mathematical content, so a second caliber was added, and the second caliber
was wrong twice in one day in opposite directions. The owner's ruling
(2026-08-06) is therefore not to pick a winner: **report every caliber side by
side and read them together.** A conclusion that holds at one caliber and
collapses at another was never a conclusion, and the only way to know which
kind you have is to see them next to each other.

THE CALIBERS

  lines        Non-blank lines inside ```agda fences. The project's standing
               unit. Cheap, exact, and biased by how verbosely a proof is
               written.

  signatures   Type signatures at any depth: one named thing that must be
               given a value. Closer to mathematical content, and applied
               identically to both trees, so it compares even where it is a
               poor absolute measure. Its limits are real and are listed
               below; read them before quoting it.

  definitions  Agda's OWN count, ingested from `agda --profile=definitions`
               via `--profile <file>`. This is the caliber to trust most when
               dividing SECONDS, because the seconds come from that same
               profile: numerator and denominator then share one notion of
               what a definition is, and this file's parser drops out of the
               arithmetic entirely. It is absent until somebody runs the
               profile, and absent is reported as absent, never guessed.

WHAT `signatures` COUNTS. A line matching `name : type`, at any indentation.
Multi-name signatures (`f0 f1 ... f15 : Op16`) count once per name, since each
is separately discharged.

WHAT IT DOES NOT COUNT, each exclusion added because it was once counted:

  - Structure: `data`, `record`, `module`, `open`, `import`, `variable`,
    fixity, `syntax`, `pattern`, pragmas.
  - **Comments.** A first version excluded `--` with a trailing `\\b`, which
    never matches, because neither `-` nor the following space is a word
    character. So every English comment containing a colon was read as a
    signature and counted once per word: `-- The range read, at the meta
    level: x` scored 8. This inflated the retiring tree by 10.3 percent and
    the surviving trunk by 11.7 percent. Block comments `{- -}` are tracked
    across lines for the same reason.
  - **`let` and `with` bindings.** `let z∈m : ⟨ ... ⟩` scored 2, once for
    `let` and once for the name. Ninety-six such in the retiring tree.

WHAT NO STATIC COUNT CAN DO, stated so the figure is not over-read. It counts
declarations, not difficulty: one absoluteness theorem and one `refl` lemma
both score 1. It conflates construction with proof, which matters because the
rud route builds more and proves less than the rest of the tree. And it cannot
see a definition written without a signature. These are reasons to read it
beside the other two calibers, which is the point of this file.

USAGE
    python3 scripts/measure/obligations.py --by-tree
    python3 scripts/measure/obligations.py --by-tree --profile /tmp/defs-profile.txt
    python3 scripts/measure/obligations.py src/L/Rud/Bridge.lagda.md
"""

from __future__ import annotations

import argparse
import re
import sys
import tomllib
from pathlib import Path

ROOT = Path(__file__).resolve().parent.parent.parent
SRC = ROOT / "src"
LEDGER = ROOT / "dev" / "ledger.toml"

# Structure, not a discharged claim. Comments are handled separately: they
# cannot go here, because `--`'s trailing word boundary never matches.
STRUCTURE = re.compile(
    r"^(data|record|module|open|import|private|variable|instance|postulate|"
    r"infix\w*|syntax|pattern|abstract|opaque|mutual|unquote|macro|where|"
    r"interleaved|primitive|constructor|field|renaming|using|hiding)\b"
)

# Binders that introduce a local name inside a term. `let z : A = ...` is a
# binding, not a stated obligation, and the leading keyword must not be
# counted as a name in its own right.
BINDERS = {"let", "with", "rewrite", "in", "where", "do", "case", "of"}

# `name : type`, or `f g h : type`. Names may be operators (`_∈ˢ_`), primed,
# subscripted, or unicode: Agda allows nearly anything that is not whitespace,
# a bracket, or a lone colon.
SIGNATURE = re.compile(r"^([^\s:;{}()@\"]+(?:\s+[^\s:;{}()@\"]+)*)\s*:(?!:)\s")

RETIRING_ROOTS = ("L.Coding", "L.Godel", "L.Choice")


def scan(path: Path) -> dict:
    """Count one master at every static caliber."""
    lines = signatures = top_level = local = 0
    in_fence = False
    in_block_comment = False

    for raw in path.read_text(encoding="utf-8").splitlines():
        stripped = raw.strip()

        if stripped.startswith("```"):
            if not in_fence and re.match(r"^```+\s*agda\b", stripped):
                in_fence = True
            elif in_fence:
                in_fence = False
            continue
        if not in_fence or not stripped:
            continue
        lines += 1

        # Block comments span lines, so they need state rather than a match.
        if in_block_comment:
            if "-}" in stripped:
                in_block_comment = False
            continue
        if stripped.startswith("{-"):
            if "-}" not in stripped:
                in_block_comment = True
            continue
        # Line comments. This is the exclusion the first version got wrong.
        if stripped.startswith("--"):
            continue

        if STRUCTURE.match(stripped):
            continue

        is_top = raw[:1] not in (" ", "\t")
        m = SIGNATURE.match(raw if is_top else stripped)
        if not m:
            continue

        names = [n for n in m.group(1).split() if n not in ("|",)]
        # Drop a leading binder keyword: `let z : A` declares z, not `let`.
        if names and names[0] in BINDERS:
            names = names[1:]
        if not names:
            continue

        signatures += len(names)
        if is_top:
            top_level += len(names)
        else:
            local += len(names)

    return {
        "lines": lines,
        "signatures": signatures,
        "top_level": top_level,
        "local": local,
    }


def module_name(path: Path) -> str:
    return str(path.relative_to(SRC)).removesuffix(".lagda.md").replace("/", ".")


def read_definition_profile(path: Path) -> dict[str, int]:
    """Ingest `agda --profile=definitions` and count definitions per module.

    Agda's rows name a definition, and the module is its dotted prefix. This
    is deliberately forgiving about the exact row format: a format change
    should yield an EMPTY result, reported as unmeasured, rather than a wrong
    number that looks measured.
    """
    counts: dict[str, int] = {}
    for line in path.read_text(encoding="utf-8").splitlines():
        m = re.match(r"\s*([A-Za-z][\w.']*\.[\w']+)\s+[\d,]+\s*ms", line)
        if not m:
            continue
        qualified = m.group(1)
        module = qualified.rsplit(".", 1)[0]
        counts[module] = counts.get(module, 0) + 1
    return counts


def main() -> int:
    ap = argparse.ArgumentParser(
        description=__doc__, formatter_class=argparse.RawDescriptionHelpFormatter
    )
    ap.add_argument("paths", nargs="*", type=Path)
    ap.add_argument("--by-tree", action="store_true")
    ap.add_argument("--profile", type=Path,
                    help="an `agda --profile=definitions` output to ingest as "
                         "the third caliber")
    args = ap.parse_args()

    defs = read_definition_profile(args.profile) if args.profile else {}

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
        r["definitions"] = defs.get(r["module"])
        rows.append(r)

    if args.by_tree:
        print(f"{'':22s} {'modules':>7} {'lines':>7} {'signatures':>11} "
              f"{'definitions':>12}")
        for label, pred in (
            ("retiring subtree", lambda m: m.startswith(RETIRING_ROOTS)),
            ("surviving trunk", lambda m: not m.startswith(RETIRING_ROOTS)),
        ):
            sel = [r for r in rows if pred(r["module"])]
            d = sum(r["definitions"] or 0 for r in sel)
            print(f"{label:22s} {len(sel):7d} {sum(r['lines'] for r in sel):7d} "
                  f"{sum(r['signatures'] for r in sel):11d} "
                  f"{d if d else 'not measured':>12}")
        if not defs:
            print("\n  `definitions` is UNMEASURED. It needs "
                  "`agda --profile=definitions` over the tree, then "
                  "`--profile <file>`. It is the caliber to prefer when "
                  "dividing seconds, because the seconds come from that same "
                  "profile.")
        return 0

    print(f"{'module':34s} {'lines':>6} {'sigs':>6} {'defs':>6} "
          f"{'s/sig':>7} {'s/def':>7}")
    for r in sorted(rows, key=lambda r: -(r["seconds"] or 0)):
        ssig = f"{r['seconds'] / r['signatures']:7.3f}" if r["seconds"] and r["signatures"] else "      -"
        sdef = f"{r['seconds'] / r['definitions']:7.3f}" if r["seconds"] and r["definitions"] else "      -"
        print(f"{r['module']:34s} {r['lines']:6d} {r['signatures']:6d} "
              f"{r['definitions'] or 0:6d} {ssig} {sdef}")
    return 0


if __name__ == "__main__":
    sys.exit(main())
