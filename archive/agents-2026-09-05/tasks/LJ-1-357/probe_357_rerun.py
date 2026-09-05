#!/usr/bin/env python3
"""PROTOTYPE, unwired (LJ-1.356). A mechanism that SHOUTS when DD18 decays.

Four signals, one file, layered so that what one misses the next catches:

  R1  SURVEY ENUMERATION (brief side). DD18 names FOUR retired-route corpora.
      The rule-bundle precedent enumerates required rule codes and checks
      presence; the same is enumerable here. A brief's ARCHIVE section must
      NAME each corpus, cited or declined. MEASURED today: the eleven briefs
      LJ-1.344..354 name exactly ONE of the four.

  R2  TEMPLATE DETECTOR (brief side). A bullet whose normalized reason text
      repeats verbatim across >= K briefs is a template, not a survey.
      MEASURED today: "taking SHAPE and never a claim" in 63 briefs.

  R3  RETURN GATE (report side, MODE-PROOF). The report must carry ARCHIVE
      USED and LITERATURE USED, and every archive path the BRIEF cited must
      appear in the report. The brief itself defines the enumerable universe,
      which is what makes a content check possible where dispatch.py could
      only read a heading. Fires on files that exist in BOTH dispatch modes.

  R4  TERM XREF (advisory, the price made visible). Distinctive identifiers
      in the brief are grepped against archived CODE; a hit the brief did not
      cite is printed as a MISSED CANDIDATE. This is the mechanized form of
      the owner telling LJ-1.353 that a green CSB was sitting in the archive.

Costs, measured on this machine over the live corpus, are printed at the end.
This file lives under agents/tasks/ and typechecks nothing; it is a probe.
"""

from __future__ import annotations

import re
import subprocess
import sys
import time
from collections import defaultdict
from pathlib import Path

_HERE = Path(__file__).resolve()
_ROOT = next((p for p in _HERE.parents if (p / "AGENTS.md").is_file()), None)
if _ROOT is None:
    raise FileNotFoundError(f"no repo root above {_HERE}")
sys.path.insert(0, str(_ROOT / "scripts"))
import agents_tree  # noqa: E402

ROOT = _ROOT
ARCHIVE_SRC = ROOT / "archive" / "src"

#: The four corpora DD18 names, in its own words (dev/PLAN.md section 3, DD18).
CORPORA = {
    "CODE": re.compile(r"archive/src/"),
    "TASKS": re.compile(r"TASKS-archived"),
    "JOURNAL": re.compile(r"JOURNAL-archived"),
    "DECISIONS": re.compile(r"DECISIONS-archived"),
}

SECTION = {
    "ARCHIVE": re.compile(r"^#{1,}\s*(?:\d+\.?\s*)?ARCHIVE\b(?!\s*USED).*?$(.*?)(?=^#{1,}\s|\Z)", re.S | re.M),
    "ARCHIVE USED": re.compile(r"^#{1,}\s*(?:\d+\.?\s*)?ARCHIVE\s+USED\b.*?$(.*?)(?=^#{1,}\s|\Z)", re.S | re.M),
    "LITERATURE USED": re.compile(r"^#{1,}\s*(?:\d+\.?\s*)?LITERATURE\s+USED\b.*?$(.*?)(?=^#{1,}\s|\Z)", re.S | re.M),
}

CITED = re.compile(r"(?:archive|agents/tasks/archive)/[A-Za-z0-9./_-]+")

#: An identifier worth xref-ing. MEASURED on this corpus: camel-case
#: identifiers (shapedAt, levelIn) and hyphen-joined proper names
#: (Cantor-Bernstein) are the mathematics; shouting caps (MEASURED, BEFORE)
#: and prose words (merely, modules) are vocabulary. Advisory only.
IDENT = re.compile(r"\b(?:[a-z]+[A-Z][A-Za-z-]{4,}|[A-Z][a-z]+-[A-Z][A-Za-z-]{3,})\b")
STOP: set[str] = set()


def doc_frequency(briefs: list[tuple[Path, str]]) -> dict[str, int]:
    df: dict[str, int] = defaultdict(int)
    for _, text in briefs:
        for w in set(w.lower() for w in IDENT.findall(text)):
            df[w] += 1
    return df


def section_of(text: str, name: str) -> str:
    m = SECTION[name].search(text)
    return m.group(1) if m else ""


def code_of(p: Path) -> int:
    m = re.search(r"(\d+)$", p.parent.name.split("-")[-1])
    return int(m.group(1)) if m else 0


def r1_defects(brief: Path, text: str) -> list[str]:
    sec = section_of(text, "ARCHIVE")
    if not sec:
        return ["no ARCHIVE section at all"]
    missing = [name for name, rx in CORPORA.items() if not rx.search(sec)]
    return [f"names {len(CORPORA) - len(missing)} of 4 corpora, absent: {', '.join(missing)}"] if missing else []


def norm_bullet(b: str) -> str:
    return re.sub(r"\s+", " ", re.sub(CITED.pattern, "<PATH>", b)).strip()


def r2_templates(briefs: list[tuple[Path, str]], k: int = 5) -> dict[str, list[str]]:
    """Bullets whose reason text repeats verbatim across >= k briefs."""
    seen: dict[str, list[str]] = defaultdict(list)
    for p, text in briefs:
        sec = section_of(text, "ARCHIVE")
        if not sec:
            continue
        for bullet in re.findall(r"^\s*-\s+(.*?)(?=\n\s*-\s|\Z)", sec, re.S | re.M):
            if CITED.search(bullet):
                seen[norm_bullet(bullet)].append(p.parent.name)
    return {t: codes for t, codes in seen.items() if len(codes) >= k}


def r3_defects(task: Path) -> list[str]:
    btexts = [p for p in task.glob("*.md") if agents_tree.is_brief(p)]
    rtexts = [p for p in task.glob("*.md") if agents_tree.is_report(p)]
    if not btexts or not rtexts:
        return []
    btext = btexts[0].read_text(encoding="utf-8")
    rtext = rtexts[0].read_text(encoding="utf-8")
    out = []
    if not SECTION["ARCHIVE USED"].search(rtext):
        out.append("report carries no ARCHIVE USED heading")
    if not SECTION["LITERATURE USED"].search(rtext):
        out.append("report carries no LITERATURE USED heading")
    wanted = {m.group(0) for m in CITED.finditer(section_of(btext, "ARCHIVE"))}
    have = {m.group(0) for m in CITED.finditer(rtext)}
    for w in sorted(wanted - have):
        out.append(f"report never answers the brief's citation of {w}")
    return out


def r4_candidates(brief: Path, text: str, df: dict[str, int], total: int,
                  limit: int = 6) -> list[str]:
    """Terms that are RARE in the corpus (df <= 15 percent) are the subject.
    MEASURED on this corpus: without the df filter the hits are shouting
    vocabulary (MEASURED, BEFORE, NOTHING); with it they are mathematics."""
    cited = {m.group(0) for m in CITED.finditer(text)}
    words = defaultdict(int)
    for w in IDENT.findall(text):
        if w in STOP:
            continue
        if df.get(w.lower(), 0) > max(3, 0.15 * total):
            continue
        words[w] += 1
    keep = sorted((w for w, n in words.items() if n >= 2),
                  key=lambda w: -words[w])[:10]
    hits: dict[str, set[str]] = defaultdict(set)
    for w in keep:
        try:
            out = subprocess.run(["grep", "-ril", "--", w, str(ARCHIVE_SRC)],
                                 capture_output=True, text=True, timeout=20)
        except subprocess.TimeoutExpired:
            continue
        for line in out.stdout.splitlines():
            rel = str(Path(line).relative_to(ROOT))
            if rel not in cited:
                hits[rel].add(w)
    return [f"{f} matches terms {sorted(ts)}" for f, ts in
            sorted(hits.items(), key=lambda x: -len(x[1]))[:limit]] if hits else []


def main(argv: list[str]) -> int:
    recent_only = "--recent" in argv
    t0 = time.time()
    live = [(p, p.read_text(encoding="utf-8")) for p in agents_tree.briefs(include_archive=False)]
    live.sort(key=lambda pr: code_of(pr[0]))
    print(f"corpus: {len(live)} live briefs, read in {time.time() - t0:.1f}s")

    # R1, over the whole corpus
    t0 = time.time()
    r1 = [(p, d) for p, text in live if (d := r1_defects(p, text))]
    print(f"\nR1 ENUMERATION: {len(r1)} of {len(live)} briefs do not name all four corpora "
          f"({time.time() - t0:.1f}s)")
    for p, d in r1[-12:]:
        print(f"  {p.parent.name}: {d[0]}")

    # R2, whole corpus
    t0 = time.time()
    templ = r2_templates(live)
    print(f"\nR2 TEMPLATE: {len(templ)} bullet text(s) repeat across >=5 briefs ({time.time() - t0:.1f}s)")
    for t, codes in sorted(templ.items(), key=lambda x: -len(x[1]))[:4]:
        print(f"  {len(codes)} briefs: \"{t[:90]}\"")

    # R3, from the DD18 epoch only: the rule was ruled 2026-08-09 and reports
    # before it are frozen records a gate must not judge (the check-dd4-stated
    # PRE_EPOCH precedent).
    t0 = time.time()
    epoch = min((code_of(p) for p in agents_tree.reports(include_archive=False)
                 if SECTION["ARCHIVE USED"].search(p.read_text(encoding="utf-8"))),
                default=0)
    r3 = []
    for d in sorted((ROOT / "agents" / "tasks").iterdir()):
        m = re.search(r"(\d+)$", d.name.split("-")[-1])
        if not d.is_dir() or d.name == "archive" or not m or int(m.group(1)) < epoch:
            continue
        if (defects := r3_defects(d)):
            r3.append((d.name, defects))
    print(f"\nR3 RETURN GATE from epoch LJ-1-{epoch}: {len(r3)} task(s) whose report does not answer "
          f"its brief ({time.time() - t0:.1f}s)")
    for name, defects in r3[-12:]:
        print(f"  {name}: {'; '.join(defects[:3])}")

    # R4, recent slice only (it greps the archive per term)
    if recent_only:
        t0 = time.time()
        df = doc_frequency(live)
        print(f"\nR4 TERM XREF over the last 12 briefs (advisory)")
        for p, text in live[-12:]:
            cands = r4_candidates(p, text, df, len(live))
            if cands:
                print(f"  {p.parent.name}: MISSED CANDIDATES in archive/src:")
                for c in cands:
                    print(f"      {c}")
        print(f"  ({time.time() - t0:.1f}s total)")
    return 0


if __name__ == "__main__":
    sys.exit(main(sys.argv))
