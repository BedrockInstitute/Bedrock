#!/usr/bin/env python3
"""Generate the SHARED half of every `dev/pod/instructions/<slot>.md`, from `AGENTS.md`.

WHY THIS FILE EXISTS. The owner ruled on 2026-08-17 that `AGENTS.md` survives the
cutover, rewritten to a minimum project summary, the current milestone, the most
important SHARED Boundary, and a pointer to the per-slot instruction files. Amendment
A8 of `dev/memos/LJ-4-pod-program-design.md` carries the ruling and names `AGENTS.md`
the ONE hand-written source of the shared half.

WHAT MEASURED FAILURE IT ANSWERS. A rule restated in a second file is a rule that
drifts. On 2026-08-04 a bulk refresh wrote "one Agda process at a time" into the
rulebook two days AFTER the owner had widened the canonical law to four concurrent
writers; three rewrites polished the sentence and nobody re-checked it, and the wrong
rule steered dispatch for three days. Five slot files, each carrying its own copy of
the shared Boundary, is that failure five times over. So the shared half is GENERATED
and never typed.

THE TWO HALVES, and the split is the whole design.

  ABOVE the marker: the shared half. This program writes it. Editing it by hand is
  pointless, because the next run overwrites it.
  BELOW the marker: that slot's OWN clauses, hand-written. This program never touches
  them. Section 3.1 of the design gives each clause a role, and a clause scoped to one
  slot belongs in that slot's file and nowhere else.

The marker is MARKER below. It is a comment, so it never renders.

USAGE
  instructions.py --check    exit 1 when any slot file's shared half is stale
  instructions.py --write    regenerate every slot file's shared half

`--check` is what a gate runs. `--write` is what a person runs after editing
`AGENTS.md`.
"""

from __future__ import annotations

import argparse
import re
import sys
from pathlib import Path

ROOT = Path(__file__).resolve().parent.parent.parent
AGENTS = ROOT / "AGENTS.md"
OUT_DIR = ROOT / "dev" / "pod" / "instructions"

MARKER = "<!-- GENERATED ABOVE. HAND-WRITTEN BELOW. instructions.py rewrites only the part above. -->"

# The five head slots of section 6.1. `POD-REFILL.md` is NOT a slot: it is a
# standing BRIEF that rule (g) sends, so this program leaves it alone.
SLOTS = [
    "mathematician",
    "mathematician_adversarial",
    "coder",
    "coder_adversarial",
    "maintainer",
]

# The sections of AGENTS.md that make up the shared half, in order. A heading that
# AGENTS.md does not carry is a DEFECT and not a silent skip: the owner ruled the
# file holds exactly these, so a missing one means the rulebook moved under us.
SHARED_SECTIONS = ["What Bedrock is", "The milestone", "Boundary"]


def read_agents() -> str:
    if not AGENTS.is_file():
        die(f"{AGENTS.relative_to(ROOT)} is missing. It is the one source of the shared half.")
    return AGENTS.read_text(encoding="utf-8")


def die(msg: str, code: int = 2) -> None:
    print(f"instructions: {msg}", file=sys.stderr)
    raise SystemExit(code)


def section(text: str, heading: str) -> str | None:
    """The body under a `## <heading>` line, up to the next `## `. None when absent."""
    pat = re.compile(r"^##\s+" + re.escape(heading) + r"\s*$", re.M)
    m = pat.search(text)
    if not m:
        return None
    start = m.end()
    nxt = re.compile(r"^##\s+\S", re.M).search(text, start)
    return text[start : nxt.start() if nxt else len(text)].strip()


def shared_half(agents: str, slot: str) -> str:
    """The generated block for one slot. Every line of it comes from AGENTS.md."""
    missing = [h for h in SHARED_SECTIONS if section(agents, h) is None]
    if missing:
        die(
            "AGENTS.md is missing the section(s) the shared half is built from: "
            + ", ".join(missing)
            + ". Either restore them or update SHARED_SECTIONS with the owner's ruling."
        )
    parts = [
        f"# Standing instruction: `{slot}`",
        "",
        "**The block below is GENERATED from `AGENTS.md` by "
        "`scripts/pod/instructions.py`. Do not edit it here.** Edit `AGENTS.md`, then "
        "run `instructions.py --write`. Your own clauses are below the marker and this "
        "program never touches them.",
        "",
    ]
    for h in SHARED_SECTIONS:
        parts += [f"## {h}", "", section(agents, h), ""]
    parts += [
        "## Your slot",
        "",
        f"You are the **`{slot}`** head. The clauses below the marker are yours, and "
        "the program injects this whole file ahead of your brief at every dispatch.",
        "",
        MARKER,
    ]
    return "\n".join(parts).rstrip() + "\n"


def split(path: Path) -> tuple[str, str]:
    """(generated half, hand-written half) of an existing slot file."""
    if not path.is_file():
        return "", ""
    text = path.read_text(encoding="utf-8")
    if MARKER not in text:
        # No marker means the whole file is hand-written. Keep ALL of it: this program
        # never destroys prose it did not write.
        return "", text.strip()
    head, _, tail = text.partition(MARKER)
    return (head + MARKER).rstrip() + "\n", tail.strip()


def render(agents: str, slot: str, hand: str) -> str:
    out = shared_half(agents, slot)
    return out + ("\n\n" + hand + "\n" if hand else "\n")


def main() -> int:
    ap = argparse.ArgumentParser(description=__doc__.splitlines()[0])
    g = ap.add_mutually_exclusive_group(required=True)
    g.add_argument("--check", action="store_true", help="exit 1 when a shared half is stale")
    g.add_argument("--write", action="store_true", help="regenerate every shared half")
    args = ap.parse_args()

    agents = read_agents()
    OUT_DIR.mkdir(parents=True, exist_ok=True)

    stale: list[str] = []
    for slot in SLOTS:
        path = OUT_DIR / f"{slot}.md"
        _, hand = split(path)
        want = render(agents, slot, hand)
        have = path.read_text(encoding="utf-8") if path.is_file() else ""
        if want == have:
            continue
        stale.append(str(path.relative_to(ROOT)))
        if args.write:
            path.write_text(want, encoding="utf-8")

    if args.write:
        print(f"instructions: wrote {len(stale)} of {len(SLOTS)} slot file(s)")
        return 0
    if stale:
        print("instructions: FAIL. The shared half is stale in:", file=sys.stderr)
        for s in stale:
            print(f"  {s}", file=sys.stderr)
        print("  Run `instructions.py --write`.", file=sys.stderr)
        return 1
    print(f"instructions: clean ({len(SLOTS)} slot file(s) match AGENTS.md)")
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
