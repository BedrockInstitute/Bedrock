#!/usr/bin/env python3
"""PROBE, unwired (LJ-1.358). R3 corrected: the three over-reaches fixed.

`[LJ-1.357]` refuted R3's headline (92/93) and split it: 51 fail only on a
missing LITERATURE USED heading, 30 of 55 unanswered paths are answered by a
DEEPER path, and one decline is spelled relative to the archive root. This
probe re-measures with:

  1. PREFIX MATCH. A brief citing a directory is answered by a report citing
     a file inside it (fixes the 30).
  2. SUFFIX MATCH. A decline spelled `L/LevelFormula.lagda.md` answers a
     brief citing `archive/src/.../L/LevelFormula.lagda.md` (fixes LJ-1-168).
  3. CONDITIONAL LITERATURE. The LITERATURE USED heading is demanded only
     when the brief's LITERATURE section cites a `dev/literature/` path.
     The unconditional count is printed beside it for comparison.
  4. SCOPE SPLIT. Failures under DD18's own four corpora (`archive/` only)
     versus the wide scope that also counts `agents/tasks/archive/`.

Usage: probe_358_r3_fixed.py [--wide]
"""

from __future__ import annotations

import re
import sys
import time
from pathlib import Path

_HERE = Path(__file__).resolve()
_ROOT = next((p for p in _HERE.parents if (p / "AGENTS.md").is_file()), None)
if _ROOT is None:
    raise FileNotFoundError(f"no repo root above {_HERE}")
sys.path.insert(0, str(_ROOT / "scripts"))
import agents_tree  # noqa: E402

ROOT = _ROOT

SECTION = {
    "ARCHIVE": re.compile(
        r"^#{1,}\s*(?:\d+\.?\s*)?ARCHIVE\b(?!\s*USED).*?$(.*?)(?=^#{1,}\s|\Z)", re.S | re.M),
    "ARCHIVE USED": re.compile(
        r"^#{1,}\s*(?:\d+\.?\s*)?ARCHIVE\s+USED\b.*?$(.*?)(?=^#{1,}\s|\Z)", re.S | re.M),
    "LITERATURE": re.compile(
        r"^#{1,}\s*(?:\d+\.?\s*)?LITERATURE\b(?!\s*USED).*?$(.*?)(?=^#{1,}\s|\Z)", re.S | re.M),
    "LITERATURE USED": re.compile(
        r"^#{1,}\s*(?:\d+\.?\s*)?LITERATURE\s+USED\b.*?$(.*?)(?=^#{1,}\s|\Z)", re.S | re.M),
}

CITED = re.compile(r"((?:archive|agents/tasks/archive)/[A-Za-z0-9./_-]+)")
LIT = re.compile(r"dev/literature/[A-Za-z0-9./_-]+")
#: Any file-shaped token. Declines are spelled relative to a root
#: ("L/LevelFormula.lagda.md: NOT read"), so the answer set must include
#: bare spellings, matched by suffix against the brief's full path.
BARE = re.compile(r"\b[A-Za-z0-9][A-Za-z0-9./_+-]*\.(?:md|toml|py|agda)\b")


def code_of(p: Path) -> int:
    m = re.search(r"(\d+)$", p.parent.name.split("-")[-1])
    return int(m.group(1)) if m else 0


def answered(want: str, have_set: set[str]) -> bool:
    """Exact, deeper answer, or relative spelling of the SAME file.

    The prefix rule is ONE-WAY: a report may answer a brief's directory by
    citing a file inside it, but a vaguer parent mention is NOT an answer
    (LJ-1-183's report mentions `archive/dev/` and answers nothing).
    """
    if want in have_set:
        return True
    for h in have_set:
        if h.startswith(want.rstrip("/") + "/"):
            return True  # report went deeper than the brief asked
        if h.endswith(want) or want.endswith(h):
            return True  # decline spelled relative to a root
    return False


def main(argv: list[str]) -> int:
    wide = "--wide" in argv
    t0 = time.time()
    tasks = sorted((ROOT / "agents" / "tasks").iterdir(), key=code_of)
    epoch = min((code_of(p) for p in agents_tree.reports(include_archive=False)
                 if SECTION["ARCHIVE USED"].search(p.read_text(encoding="utf-8"))),
                default=0)
    lit_epoch = min((code_of(p) for p in agents_tree.reports(include_archive=False)
                     if SECTION["LITERATURE USED"].search(p.read_text(encoding="utf-8"))),
                    default=0)
    n = lit_uncond = lit_cond = au_absent = 0
    dd18_fail: list[str] = []
    wide_fail: list[str] = []
    for d in tasks:
        code = code_of(d / "x")
        if not d.is_dir() or d.name == "archive" or code < epoch:
            continue
        btexts = [p for p in d.glob("*.md") if agents_tree.is_brief(p)]
        rtexts = [p for p in d.glob("*.md") if agents_tree.is_report(p)]
        if not btexts or not rtexts:
            continue
        btext = btexts[0].read_text(encoding="utf-8")
        rtext = rtexts[0].read_text(encoding="utf-8")
        n += 1
        if not SECTION["ARCHIVE USED"].search(rtext):
            au_absent += 1
            dd18_fail.append(f"{d.name}: report carries no ARCHIVE USED heading")
        has_lit_used = bool(SECTION["LITERATURE USED"].search(rtext))
        lit_uncond += not has_lit_used
        lit_sec = SECTION["LITERATURE"].search(btext)
        brief_cites_lit = bool(lit_sec and LIT.search(lit_sec.group(1)))
        if brief_cites_lit and not has_lit_used:
            lit_cond += 1
            if code >= lit_epoch:
                dd18_fail.append(f"{d.name}: brief cites dev/literature/, report "
                                 f"carries no LITERATURE USED heading")
        want = {m.group(1) for m in CITED.finditer(
            SECTION["ARCHIVE"].search(btext).group(1)
            if SECTION["ARCHIVE"].search(btext) else "")}
        have = ({m.group(1) for m in CITED.finditer(rtext)}
                | set(LIT.findall(rtext))
                | {t for t in BARE.findall(rtext) if len(t) > 8})
        for w in sorted(want):
            if not answered(w, have):
                wide_fail.append(f"{d.name}: {w}")
                if w.startswith("archive/"):
                    dd18_fail.append(f"{d.name}: {w}")
    print(f"epoch LJ-1-{epoch}, {n} tasks with brief+report, "
          f"checked in {time.time() - t0:.1f}s")
    print(f"ARCHIVE USED heading absent: {au_absent}")
    print(f"LITERATURE USED absent, unconditional: {lit_uncond}")
    print(f"LITERATURE USED absent, conditional on brief citing literature: {lit_cond}")
    print(f"unanswered brief citations, DD18 scope (archive/): {len(dd18_fail) - au_absent - lit_cond}")
    print(f"unanswered brief citations, wide scope (+agents/tasks/archive/): {len(wide_fail)}")
    for label, rows in (("DD18", dd18_fail), ("WIDE-only", [r for r in wide_fail if not r.startswith("archive")])) if wide else (("DD18", dd18_fail),):
        print(f"\n{label} failures:")
        for r in rows:
            print(f"  {r}")
    return 0


if __name__ == "__main__":
    sys.exit(main(sys.argv))
