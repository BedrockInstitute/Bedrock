#!/usr/bin/env python3
"""Emit the rules a task must carry, mechanically rather than from memory.

WHY THIS EXISTS. `dev/LESSONS.md` holds 105 entries and 16,972 words. A brief
cites five to nine of them, so an agent honouring the citation loads about four
times what it was pointed at; and the orchestrator picks that set by recall.
For five days in August 2026 the recalled set omitted an entire imported
playbook that had just landed, and nothing noticed.

`[L3.32-T105]` refuted the claim that this omission CAUSED the campaign's three
expensive modules, and that refutation stands: the laws covering those defects
were written later. This tool is built on a narrower justification. The
alternative is a sentence in `dev/ORCHESTRATION.md` telling the orchestrator to
remember, and `AGENTS.md` says a rule whose enforcement point is a person's
intention is a wish. **The orchestrator is the component that drifted.**

WHAT IT DOES

    rules.py --for build        the bundle for a kind, with each rule's
                                statement, ready to paste into a brief
    rules.py --for-scope src/L/Ordinal/SquareLaw.lagda.md
                                DERIVES the kind from the write scope, which
                                is the point: an author who declares the kind
                                picks the bundle ([T105])
    rules.py --grep opaque      the trigger layer: what applies to a term
    rules.py --check            validate rules.toml against LESSONS and the cap

WHAT IT DOES NOT DO. It cannot make a cited rule apply. `[T105]` established
that citation is not application, measuring a subtree that follows the playbook
in code whose briefs never named it. This tool removes one failure only: a rule
that exists and never reaches the work.
"""

from __future__ import annotations

import argparse
import re
import sys
import tomllib
from pathlib import Path

ROOT = Path(__file__).resolve().parent.parent
LESSONS = ROOT / "dev" / "LESSONS.md"
RULES = ROOT / "dev" / "rules.toml"

HEADING = re.compile(
    r"^###\s+((?:Rule\s+\d+)|(?:P-[a-z](?![a-z]))|(?:[RTIDC]-\d+))\b.*$", re.M)


def entries() -> dict[str, tuple[str, str]]:
    """Each LESSONS entry as (title line, first paragraph of its body)."""
    text = LESSONS.read_text(encoding="utf-8")
    hits = list(HEADING.finditer(text))
    out: dict[str, tuple[str, str]] = {}
    for i, m in enumerate(hits):
        end = hits[i + 1].start() if i + 1 < len(hits) else len(text)
        body = text[m.end():end].strip()
        # The first non-empty paragraph is the rule statement by house style.
        para = next((p.strip() for p in body.split("\n\n") if p.strip()), "")
        out[re.sub(r"\s+", " ", m.group(1))] = (
            m.group(0).lstrip("# ").strip(), re.sub(r"\s+", " ", para))
    return out


def config() -> dict:
    return tomllib.loads(RULES.read_text(encoding="utf-8"))


def kind_for_scope(paths: list[str]) -> str:
    """Derive the task kind from what the brief may WRITE.

    [T105]: a self-declared kind lets an author pick the smallest bundle. The
    write scope is already in every brief and is not a matter of opinion.
    """
    src = [p for p in paths if p.startswith("src/") or "/src/" in p]
    if not src:
        return "recon"
    # A scratch-only write is a probe; a master write is a build.
    if all("Probe" in p or "/tmp" in p for p in src):
        return "probe"
    return "build"


def emit(ids: list[str], ents: dict, header: str) -> int:
    missing = [i for i in ids if i not in ents]
    print(header)
    print()
    for rid in ids:
        if rid not in ents:
            continue
        title, para = ents[rid]
        print(f"- **{title}**")
        if para:
            wrapped = para if len(para) <= 400 else para[:397] + "..."
            print(f"  {wrapped}")
    if missing:
        print(f"\n  WARNING: {len(missing)} id(s) not found in LESSONS: "
              f"{', '.join(missing)}")
        return 1
    return 0


def main() -> int:
    ap = argparse.ArgumentParser(
        description=__doc__, formatter_class=argparse.RawDescriptionHelpFormatter)
    g = ap.add_mutually_exclusive_group(required=True)
    g.add_argument("--for", dest="kind", help="bundle for a task kind")
    g.add_argument("--for-scope", nargs="+", help="derive the kind from write paths")
    g.add_argument("--grep", help="trigger term")
    g.add_argument("--check", action="store_true")
    args = ap.parse_args()

    cfg = config()
    ents = entries()

    if args.check:
        cap = cfg.get("config", {}).get("max_ids", 12)
        bad: list[str] = []
        for name, b in cfg.get("bundle", {}).items():
            ids = b.get("ids", [])
            if len(ids) > cap:
                bad.append(f"bundle.{name} holds {len(ids)} ids, over the cap of "
                           f"{cap}. Evict one: the cap is the design, and a "
                           f"bundle that grows without eviction becomes the "
                           f"corpus again.")
            for rid in ids:
                if rid not in ents:
                    bad.append(f"bundle.{name} cites `{rid}`, which is not a "
                               f"heading in dev/LESSONS.md")
        for term, ids in cfg.get("triggers", {}).items():
            for rid in ids:
                if rid not in ents:
                    bad.append(f"triggers.\"{term}\" cites `{rid}`, which is not "
                               f"a heading in dev/LESSONS.md")
        if bad:
            for b in bad:
                print(f"  DEFECT: {b}")
            print(f"\nrules: {len(bad)} defect(s) in dev/rules.toml")
            return 1
        print(f"rules: clean ({len(cfg.get('bundle', {}))} bundles, cap {cap}, "
              f"{len(ents)} lessons)")
        return 0

    if args.grep:
        hits = {rid for term, ids in cfg.get("triggers", {}).items()
                if args.grep.lower() in term.lower() for rid in ids}
        if not hits:
            print(f"rules: no trigger matches `{args.grep}`")
            return 0
        return emit(sorted(hits), ents, f"Rules triggered by `{args.grep}`:")

    kind = args.kind or kind_for_scope(args.for_scope)
    b = cfg.get("bundle", {}).get(kind)
    if not b:
        print(f"rules: no bundle named `{kind}`; have "
              f"{', '.join(sorted(cfg.get('bundle', {})))}")
        return 1
    return emit(b["ids"], ents,
                f"MANDATORY for kind `{kind}` ({b.get('detail','')}):")


if __name__ == "__main__":
    sys.exit(main())
