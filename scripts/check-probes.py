#!/usr/bin/env python3
"""Never-commit checker: probe files and generated files must not enter the repository.

Two standing rules from AGENTS.md's Never list, both of which have already been broken once:

- **Probes are never committed** (dev/LESSONS.md D-1's lifecycle). A probe prices what one
  setting costs and is then thrown away; the verdict lives in a report under _build/, not in
  the tree. On 2026-08-04 a single `git add -A src/` committed 13 probe files, 3,274 lines,
  which had to be untracked afterwards.
- **Generated files are never committed**: anything under _build/, and the woven mono-lingual
  .lagda.md copies that `make gen` produces.

.gitignore already covers both, which is why this script exists rather than not existing:
an ignore rule is a default, not a gate. `git add -f` walks straight past it, a pattern that
does not match a new naming shape silently stops covering it, and neither case produces any
signal at all. This script is the gate. It runs in two places:

  check-probes.py --check      every TRACKED file; this is what `make check` runs, and it
                               catches anything that got in historically or past a bypass
  check-probes.py --staged     the STAGED files only; this is what the pre-commit hook runs,
                               and it is what stops the commit before it happens

It also carries the other half of D-1, the one an ignore rule cannot express: a probe is
THROWN AWAY once its verdict is recorded. Untracked probes accumulate in src/ and are then
mistaken for committed ones, which is what prompted this tool.

  check-probes.py --stale      list probes on disk that are safe to delete
  check-probes.py --stale --delete   delete them

A probe is safe to delete only when BOTH hold, and the script refuses otherwise:

- **its verdict survives**: some report under _build/ names it, which is where D-1 says the
  verdict lives once the file is gone; and
- **nobody is writing it**: it has not been modified within the freshness window (default 6
  hours), because a live agent's probe file must never be pulled out from under it. Two
  agents were killed on 2026-08-05 by exactly that class of carelessness.

Exit status: 0 clean, 1 violations found, 2 usage error.
"""

from __future__ import annotations

import subprocess
import sys
from pathlib import Path

ROOT = Path(__file__).resolve().parent.parent


def classify(path: str) -> str | None:
    """Return the rule a path breaks, or None. Matching is on shape, not on an ignore list."""
    p = Path(path)
    # Probe files: the doctrine names src/Probe*.agda, but a probe is a probe wherever it is
    # written and whatever extension it carries, so match the basename shape anywhere.
    if p.name.startswith("Probe") and p.suffix in {".agda", ".agdai", ".md"}:
        return "probe file (D-1: probes are never committed; the verdict goes in a report under _build/)"
    if p.name.startswith("Probe") and p.name.endswith(".lagda.md"):
        return "probe file (D-1: probes are never committed)"
    # Generated: the build tree, and the woven mono-lingual copies.
    if path.startswith("_build/"):
        return "generated file under _build/ (never committed)"
    if "/woven/" in path or path.startswith("woven/"):
        return "woven mono-lingual copy (a `make gen` output, never committed)"
    return None


def tracked() -> list[str]:
    return subprocess.run(
        ["git", "ls-files"], cwd=ROOT, capture_output=True, text=True, check=True
    ).stdout.split("\n")


def staged() -> list[str]:
    return subprocess.run(
        ["git", "diff", "--cached", "--name-only", "--diff-filter=ACM"],
        cwd=ROOT, capture_output=True, text=True, check=True,
    ).stdout.split("\n")


FRESH_HOURS = 6.0


def stale_probes(fresh_hours: float = FRESH_HOURS):
    """Probes on disk, split into safe-to-delete and protected, with the reason for each."""
    import time
    reports = list((ROOT / "_build").glob("*.md")) if (ROOT / "_build").is_dir() else []
    corpus = {r: r.read_text(encoding="utf-8", errors="ignore") for r in reports}
    safe, kept = [], []
    for f in sorted((ROOT / "src").glob("Probe*.agda")):
        stem = f.stem
        named_in = next((r.name for r, txt in corpus.items() if stem in txt), None)
        age_h = (time.time() - f.stat().st_mtime) / 3600.0
        if named_in is None:
            kept.append((f, f"no report under _build/ names it, so deleting it would destroy "
                            f"the verdict D-1 says must outlive the file"))
        elif age_h < fresh_hours:
            kept.append((f, f"modified {age_h:.1f}h ago, inside the {fresh_hours:.0f}h freshness "
                            f"window: an agent may still be writing it"))
        else:
            safe.append((f, named_in, age_h))
    return safe, kept


def cmd_stale(delete: bool, fresh_hours: float) -> int:
    safe, kept = stale_probes(fresh_hours)
    if kept:
        print("PROTECTED, not deletable:")
        for f, why in kept:
            print(f"  {f.relative_to(ROOT)}\n      {why}")
        print("")
    if not safe:
        print("check-probes: no stale probe on disk")
        return 0
    print(f"STALE, verdict recorded and untouched for over {fresh_hours:.0f}h:")
    for f, rep, age in safe:
        print(f"  {f.relative_to(ROOT)}  ({age:.0f}h old; verdict in _build/{rep})")
    if not delete:
        print(f"\n{len(safe)} probe(s) safe to delete. Re-run with --delete to remove them.")
        return 0
    for f, _, _ in safe:
        f.unlink()
        agdai = f.with_suffix(".agdai")
        if agdai.exists():
            agdai.unlink()
    print(f"\ncheck-probes: deleted {len(safe)} stale probe(s); their verdicts remain in _build/")
    return 0


def main(argv: list[str]) -> int:
    mode = "check"
    delete = False
    fresh = FRESH_HOURS
    args = argv[1:]
    for i, arg in enumerate(args):
        if arg == "--staged":
            mode = "staged"
        elif arg == "--check":
            mode = "check"
        elif arg == "--stale":
            mode = "stale"
        elif arg == "--delete":
            delete = True
        elif arg == "--fresh-hours":
            fresh = float(args[i + 1])
        elif i > 0 and args[i - 1] == "--fresh-hours":
            pass
        else:
            print(__doc__, file=sys.stderr)
            return 2

    if mode == "stale":
        return cmd_stale(delete, fresh)

    files = [f for f in (staged() if mode == "staged" else tracked()) if f]
    bad = [(f, why) for f in files if (why := classify(f))]

    if bad:
        where = "staged for commit" if mode == "staged" else "tracked in the repository"
        print(f"check-probes: {len(bad)} file(s) {where} that must never be committed:",
              file=sys.stderr)
        for f, why in bad:
            print(f"  {f}\n      {why}", file=sys.stderr)
        print("", file=sys.stderr)
        if mode == "staged":
            print("Unstage them and commit the rest:", file=sys.stderr)
            print(f"    git restore --staged {' '.join(f for f, _ in bad)}", file=sys.stderr)
            print("Never use `git add -A src/` while probes are on disk; stage explicit paths.",
                  file=sys.stderr)
        else:
            print("Untrack them, keeping the files on disk:", file=sys.stderr)
            print(f"    git rm --cached {' '.join(f for f, _ in bad)}", file=sys.stderr)
        return 1

    scope = "staged" if mode == "staged" else f"{len(files)} tracked"
    print(f"check-probes: clean ({scope} files, no probe and no generated file)")
    return 0


if __name__ == "__main__":
    sys.exit(main(sys.argv))
