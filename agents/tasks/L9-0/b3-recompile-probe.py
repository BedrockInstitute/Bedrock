#!/usr/bin/env python3
"""Times the POD acceptance test after a comment-only edit, one depth class at a time.

WHY THIS EXISTS. `dev/memos/L9-pod-program-design.md:3192-3202` records gap B3: the
acceptance test cost is unmeasured across a 34-fold band. The floor is measured at 2.84
to 3.18 s warm (`:1506-1509`), and the whole variable price is the recompile term. Three
recorded rates bracket that term 34-fold apart, so no throughput plan can rest on it. The
design's day 1 row (`:3168`) names the cure: a scratch worktree, one cold build, then one
comment-character change in each of five masters, one per depth class, timing
`agda src/Everything.lagda.md` after each.

WHAT A COMMENT CHARACTER BUYS. In a `.lagda.md` master, Agda reads the fenced code and
never the prose. A change to one prose character therefore changes the source hash and
nothing else, so the recompile it forces is pure DEPENDENCY cost with no new elaboration.
That isolates the term B3 cannot bound.

THE CALIBER IS THE DESIGN'S, NOT THIS FILE'S. `run_agda()` at
`dev/memos/L9-pod-program-design.md:437` pins `CAP = "-A64m -I0 -M8g"` under R13, and it
adds `--safe` when the target declares it. This probe runs the same argv and the same
environment, because a price measured at another caliber does not transfer:
`scripts/measure/check-timing.py:255-258` measured the two GC flags at 22.3 percent
(163.49 s against 133.69 s on one tree).

ONE PROCESS AT A TIME, per C-12. The script refuses to start when Agda already runs.

Usage:
  b3-recompile-probe.py --root <worktree> --out <dir> [--dry-run]

Exit status: 0 every run completed, 1 a run failed, 2 usage error, 3 refused.
"""

from __future__ import annotations

import argparse
import os
import re
import subprocess
import sys
import time
from pathlib import Path

# The design's caliber, copied from run_agda() and never re-invented here.
CAP = "-A64m -I0 -M8g"
TARGET = "src/Everything.lagda.md"

FENCE = re.compile(r"^```agda\s*$(.*?)^```\s*$", re.M | re.S)

# The five depth classes. `revfiles` and `revlines` are the COUNTABLE-caliber reverse
# import closure at HEAD, computed by scripts/measure/ledger.py: the master itself plus
# every master that transitively imports it, minus the two UNCOUNTED catalogs. That set
# is exactly what Agda must re-check after the master changes, so it is the depth.
MASTERS = [
    ("d1-leaf", "src/L/BoundedSubset.lagda.md"),
    ("d2-shallow", "src/L/Ordinal/SquareLaw.lagda.md"),
    ("d3-mid", "src/L/Coding/Sound.lagda.md"),
    ("d4-deep", "src/L/Coding/Model.lagda.md"),
    ("d5-base", "src/Base/Prelude.lagda.md"),
]


def slots() -> int:
    """Live Agda processes. The same reading `agents/tasks/LJ-1-331/run.sh:14` takes."""
    out = subprocess.run(["ps", "ax"], capture_output=True, text=True).stdout
    return sum(1 for line in out.splitlines()
               if "libexec" in line and "bin/agda" in line)


def load_average() -> str:
    return subprocess.run(["uptime"], capture_output=True, text=True).stdout.strip()


def prose_lines(text: str) -> list[int]:
    """Indices of the lines OUTSIDE every ```agda fence. Agda treats them as comment."""
    spans = [(m.start(), m.end()) for m in FENCE.finditer(text)]
    out, pos = [], 0
    for i, line in enumerate(text.split("\n")):
        end = pos + len(line)
        if not any(a <= pos and end <= b for a, b in spans):
            out.append(i)
        pos = end + 1
    return out


def flip_one_comment_char(path: Path) -> tuple[int, str, str]:
    """Toggle the case of ONE ASCII letter in the last plain prose line.

    The line count does not move, the fenced code does not move, and the in-fence line
    count does not move. An i18n marker line is skipped, because `<!--en-->` is grammar
    and not prose. Returns (line number, before, after)."""
    text = path.read_text(encoding="utf-8")
    lines = text.split("\n")
    for i in reversed(prose_lines(text)):
        line = lines[i]
        if not line.strip() or line.lstrip().startswith("<"):
            continue
        hit = [j for j, c in enumerate(line) if c.isascii() and c.isalpha()]
        if not hit:
            continue
        j = hit[-1]
        c = line[j]
        lines[i] = line[:j] + (c.upper() if c.islower() else c.lower()) + line[j + 1:]
        path.write_text("\n".join(lines), encoding="utf-8")
        return i + 1, line, lines[i]
    raise SystemExit(f"no plain prose line found in {path}")


def declares_safe(path: Path) -> bool:
    """run_agda() reads the first 4000 characters for the --safe pragma. So does this."""
    head = path.read_text(encoding="utf-8", errors="replace")[:4000]
    return bool(re.search(r"^\{-#\s+OPTIONS\b[^#]*--safe", head, re.M))


def run_once(label: str, root: Path, out_dir: Path, note: str) -> dict:
    """One timed `agda src/Everything.lagda.md`, written to its own run file."""
    argv = ["agda"] + (["--safe"] if declares_safe(root / TARGET) else []) + [TARGET]
    rec = out_dir / f"{label}.out"
    before = slots()
    header = [f"# arm {label}", f"# note {note}", f"# argv {' '.join(argv)}",
              f"# GHCRTS {CAP}", f"# root {root}", f"# agda slots before {before}",
              f"# load before {load_average()}",
              f"# started {time.strftime('%Y-%m-%d %H:%M:%S')}"]
    rec.write_text("\n".join(header) + "\n", encoding="utf-8")
    env = dict(os.environ, GHCRTS=CAP)
    start = time.monotonic()
    proc = subprocess.run(argv, cwd=root, env=env, capture_output=True, text=True)
    wall = time.monotonic() - start
    with rec.open("a", encoding="utf-8") as fh:
        fh.write(proc.stdout + proc.stderr)
        fh.write(f"# wall seconds {wall:.2f}\n# exit {proc.returncode}\n"
                 f"# agda slots after {slots()}\n# load after {load_average()}\n")
    return {"label": label, "seconds": round(wall, 2), "rc": proc.returncode}


def main(argv: list[str]) -> int:
    ap = argparse.ArgumentParser()
    ap.add_argument("--root", required=True)
    ap.add_argument("--out", required=True)
    ap.add_argument("--dry-run", action="store_true")
    args = ap.parse_args(argv)
    root, out_dir = Path(args.root), Path(args.out)
    out_dir.mkdir(parents=True, exist_ok=True)
    tsv = out_dir / "results.tsv"

    if args.dry_run:
        for label, master in MASTERS:
            path = root / master
            n, before, after = flip_one_comment_char(path)
            print(f"{label} {master}:{n}\n  - {before!r}\n  + {after!r}")
            subprocess.run(["git", "checkout", "--", master], cwd=root, check=True)
        return 0

    if slots():
        print(f"REFUSED: {slots()} agda processes already run (C-12).")
        return 3

    tsv.write_text("label\tmaster\tseconds\trc\n", encoding="utf-8")

    def record(row: dict, master: str) -> None:
        with tsv.open("a", encoding="utf-8") as fh:
            fh.write(f"{row['label']}\t{master}\t{row['seconds']}\t{row['rc']}\n")
        print(f"{row['label']}: {row['seconds']} s, exit {row['rc']}", flush=True)

    # 1. The cold build. The worktree carries no _build, so it is cold by construction.
    subprocess.run(["rm", "-rf", str(root / "_build")], check=True)
    record(run_once("00-cold", root, out_dir, "no _build present"), "-")

    # 2. The warm floor, with nothing changed. This is conjunct 1's measured floor.
    record(run_once("01-warm-nochange", root, out_dir, "no edit"), "-")

    # 3. One comment character per master, cheapest depth class first.
    rc = 0
    for label, master in MASTERS:
        n, _, _ = flip_one_comment_char(root / master)
        row = run_once(label, root, out_dir, f"one comment char at {master}:{n}")
        record(row, master)
        rc = rc or (1 if row["rc"] != 0 else 0)

    # 4. The warm floor again, so drift in the machine is visible and not hidden.
    record(run_once("99-warm-nochange", root, out_dir, "no edit, closing floor"), "-")
    return rc


if __name__ == "__main__":
    sys.exit(main(sys.argv[1:]))
