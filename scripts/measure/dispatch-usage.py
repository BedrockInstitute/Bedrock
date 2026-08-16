#!/usr/bin/env python3
"""Token usage per dispatch, joined from the agent's own session file.

WHY THIS EXISTS. `[R1]`'s cost model priced a dispatch at about 1,757 words of
orchestrator prose and about 35 delivered Agda lines, and then named the one
input a cost decision actually needs and could not supply: **tokens and money
per dispatch are recorded nowhere.** The registry record carries pid,
proc_start, brief, started, model, harness, log, final, reported, agda,
sandbox, session, resumed_from and events, and no usage field. `dev/vendors.toml`
holds price BANDS per vendor and nothing joins a band to a task code. Every
ratio in that model is therefore a proxy, and this tool is what converts them.

WHY IT DOES NOT TOUCH `dispatch.py`, and the owner authorised touching it.
Three reasons, and the third is the one that decided it.

  1. The data already exists. Both agents write per-turn usage into their own
     session files; nothing needs to be captured at launch that is not already
     captured.
  2. `dispatch.py` is 143 kB, UNTRACKED, and live. Its own comment records that
     "this file is untracked, so no gate reads it", and a directory move once
     broke its mandatory-rule refusal for four hours while briefs citing zero
     rules passed clean. A new field written at launch time would be one more
     behaviour no gate can see.
  3. **A launch-time field could only price dispatches from today forward.**
     This reads the history: 237 of 467 registry records join to a session file
     TODAY, so the model gets a retrospective answer instead of waiting a week
     for one.

THE TWO STORES HAVE OPPOSITE SEMANTICS, AND THIS IS THE WHOLE CORRECTNESS
QUESTION. Both were MEASURED on 2026-08-16, not read off a document.

  codex  `~/.codex/sessions/**/*.jsonl`
         `{"type":"token_count","info":{"total_token_usage":{...}}}`, and it
         is CUMULATIVE: measured strictly monotonic over 791 events in one
         session, rising 18,839 to 391,252,172. **Take the LAST.** Summing
         them returns 135,799,471,908, which is 347 times the truth.

  pi     `~/.pi/agent/sessions/**/*.jsonl`
         `"usage":{"input","output","cacheRead","cacheWrite","reasoning",
         "totalTokens","cost":{...}}`, and it is PER TURN: measured NOT
         monotonic, and `totalTokens` equals `input + output + cacheRead +
         cacheWrite` for that turn (2,660 + 306 + 7,936 + 0 = 10,902 at the
         first turn of the sampled session). **SUM them.** Taking the last
         returns 103,750 against a true 12,604,087, which is 121 times low.

WHAT IT CANNOT DO, and the gap is money. `dev/vendors.toml` names price BANDS
(`peak`, `off_peak`, flat) and carries no per-token rate, so no cost figure is
derivable here. pi's own `cost` object reads zero on the sampled runs, which is
what a local or subscription vendor reports. **This tool reports TOKENS. A cost
per dispatch needs a per-token rate that this repository does not hold, and
inventing one would write a certainty no evidence gives** (DD8).

IT IS A MEASUREMENT AND NEVER A GATE, which is why it lives in `scripts/measure/`
rather than beside the dispatcher: it reports a number and exits 0 whatever it
finds.

USAGE
    dispatch-usage.py                 every joinable dispatch, plus the summary
    dispatch-usage.py --task LJ-1.377 one dispatch
    dispatch-usage.py --summary       the summary alone
    dispatch-usage.py --json          machine-readable, for a later join
"""

from __future__ import annotations

import argparse
import glob
import json
import os
import re
import statistics
import sys
from pathlib import Path

_HERE = Path(__file__).resolve()
sys.path.insert(0, str(_HERE.parent))
_SCRIPTS = next((p for p in _HERE.parents if (p / "repo_root.py").is_file()), None)
if _SCRIPTS is None:
    raise FileNotFoundError(
        f"no repo_root.py above {_HERE}: refusing to guess the scripts root (C-43)")
sys.path.insert(0, str(_SCRIPTS))
from repo_root import find_root  # noqa: E402

ROOT = find_root(__file__)
REGISTRY = ROOT / ".claude" / "skills" / "codex-dispatch" / ".state" / "registry.json"

SESSION_GLOBS = [
    os.path.expanduser("~/.codex/sessions/**/*.jsonl"),
    os.path.expanduser("~/.pi/agent/sessions/**/*.jsonl"),
]

UUID = re.compile(
    r"[0-9a-f]{8}-[0-9a-f]{4}-[0-9a-f]{4}-[0-9a-f]{4}-[0-9a-f]{12}")

# codex: cumulative, take the last.
CODEX = re.compile(
    r'"total_token_usage":\{"input_tokens":(\d+),"cached_input_tokens":(\d+),'
    r'"cache_write_input_tokens":(\d+),"output_tokens":(\d+),'
    r'"reasoning_output_tokens":(\d+),"total_tokens":(\d+)\}')
# pi: per turn, sum them.
PI = re.compile(
    r'"usage":\{"input":(\d+),"output":(\d+),"cacheRead":(\d+),'
    r'"cacheWrite":(\d+),"reasoning":(\d+),"totalTokens":(\d+)')
# The pi session path a herdr log announces in its first event.
PI_IN_LOG = re.compile(r'"value":"([^"]*?/\.pi/agent/sessions/[^"]+\.jsonl)"')

FIELDS = ("input", "output", "cached", "cache_write", "reasoning", "total")


def session_index() -> dict[str, str]:
    """Every session file on this machine, keyed by any UUID in its name."""
    idx: dict[str, str] = {}
    for pattern in SESSION_GLOBS:
        for path in glob.glob(pattern, recursive=True):
            for u in UUID.findall(os.path.basename(path)):
                idx.setdefault(u, path)
    return idx


def locate(record: dict, idx: dict[str, str]) -> tuple[str | None, str]:
    """The session file for one dispatch, and how it was found.

    TWO JOINS, and the second one exists because the first misses. MEASURED
    2026-08-16: the `session` field is populated on 237 of 467 records and
    every one of those 237 resolves to a file. For the rest, the herdr log
    announces the pi session path in its opening `cli:agent:start` event, which
    recovers a further set.
    """
    sid = record.get("session")
    if sid and sid in idx:
        return idx[sid], "session-field"
    log = record.get("log") or ""
    if log and os.path.exists(log):
        try:
            with open(log, errors="ignore") as fh:
                m = PI_IN_LOG.search(fh.read(20000))
        except OSError:
            m = None
        if m and os.path.exists(m.group(1)):
            return m.group(1), "log-header"
    return None, "unjoined"


def read_usage(path: str) -> dict | None:
    """Tokens for one session, with each store read on its own semantics."""
    try:
        with open(path, errors="ignore") as fh:
            text = fh.read()
    except OSError:
        return None

    hits = CODEX.findall(text)
    if hits:
        # CUMULATIVE. The last event carries the run's whole total.
        i, c, w, o, r, t = (int(x) for x in hits[-1])
        # codex: `total = input + output`, and `cached` is a SUBSET of input.
        # MEASURED on the first event of a sampled session: 15,861 input,
        # 4,736 cached, 2 output, 15,863 total, and 15,861 + 2 = 15,863.
        return {"input": i, "output": o, "cached": c, "cache_write": w,
                "reasoning": r, "total": t, "fresh": i - c, "turns": len(hits),
                "store": "codex", "semantics": "cumulative, last event"}

    hits = PI.findall(text)
    if hits:
        # PER TURN. Sum them.
        agg = dict.fromkeys(FIELDS, 0)
        for i, o, cr, cw, r, t in hits:
            agg["input"] += int(i)
            agg["output"] += int(o)
            agg["cached"] += int(cr)
            agg["cache_write"] += int(cw)
            agg["reasoning"] += int(r)
            agg["total"] += int(t)
        # pi: `totalTokens = input + output + cacheRead + cacheWrite`, so
        # `cacheRead` is DISJOINT from input, the opposite of codex. MEASURED
        # on the first turn of a sampled session: 2,660 + 306 + 7,936 + 0 =
        # 10,902. Reading the two schemas the same way made aggregate
        # `input - cached` come out NEGATIVE at minus 245,596,874, which is how
        # this was caught.
        agg["fresh"] = agg["input"]
        agg.update(turns=len(hits), store="pi",
                   semantics="per turn, summed")
        return agg
    return None


def rows() -> tuple[list[dict], dict]:
    reg = json.loads(REGISTRY.read_text(encoding="utf-8"))["dispatches"]
    idx = session_index()
    out: list[dict] = []
    how = {"session-field": 0, "log-header": 0, "unjoined": 0, "no-usage": 0}
    for code, rec in reg.items():
        if not isinstance(rec, dict):
            continue
        path, join = locate(rec, idx)
        if path is None:
            how["unjoined"] += 1
            continue
        usage = read_usage(path)
        if usage is None:
            how["no-usage"] += 1
            continue
        how[join] += 1
        out.append({"code": code, "model": rec.get("model"),
                    "harness": rec.get("harness"), "join": join, **usage})
    return out, {"records": len(reg), **how}


def main() -> int:
    ap = argparse.ArgumentParser(
        description=__doc__, formatter_class=argparse.RawDescriptionHelpFormatter)
    ap.add_argument("--task", help="one dispatch code")
    ap.add_argument("--summary", action="store_true")
    ap.add_argument("--json", action="store_true")
    args = ap.parse_args()

    if not REGISTRY.is_file():
        print(f"dispatch-usage: no registry at {REGISTRY}")
        return 0

    data, cov = rows()
    if args.task:
        data = [d for d in data if d["code"].lower().startswith(args.task.lower())]

    if args.json:
        print(json.dumps({"coverage": cov, "dispatches": data}, indent=2))
        return 0

    if not args.summary:
        for d in sorted(data, key=lambda x: -x["total"]):
            print(f"  {d['code']:<16} {d['total']:>13,}  "
                  f"in {d['input']:>11,}  out {d['output']:>9,}  "
                  f"cached {d['cached']:>11,}  {d['turns']:>4} turns  "
                  f"{d['store']}  {d.get('model') or '-'}")
        print()

    if not data:
        print("dispatch-usage: nothing joined; nothing to report")
        return 0

    tot = [d["total"] for d in data]
    print(f"dispatch-usage: {len(data)} of {cov['records']} registry records "
          f"priced ({100 * len(data) / cov['records']:.1f} percent)")
    print(f"  joined by session field {cov['session-field']}, "
          f"by log header {cov['log-header']}, "
          f"unjoined {cov['unjoined']}, joined with no usage {cov['no-usage']}")
    fresh = [d["fresh"] for d in data]
    outs = [d["output"] for d in data]
    print(f"  TOTAL tokens processed over the priced set: {sum(tot):,}")
    print(f"  per dispatch, PROCESSED: median {statistics.median(tot):,.0f}, "
          f"mean {statistics.mean(tot):,.0f}, "
          f"min {min(tot):,}, max {max(tot):,}")
    # THE PROCESSED FIGURE IS DOMINATED BY CACHE READS and is the wrong number
    # to reason about price with: a cache read is billed at a fraction of a
    # fresh input token by every vendor here. The pair below is the one a cost
    # question needs.
    print(f"  per dispatch, FRESH INPUT: median {statistics.median(fresh):,.0f}"
          f"   (cache reads excluded, per each store's own schema)")
    print(f"  per dispatch, OUTPUT:      median {statistics.median(outs):,.0f}")
    by: dict[str, list[int]] = {}
    for d in data:
        by.setdefault(d["store"], []).append(d["total"])
    for store, vals in sorted(by.items()):
        print(f"  {store:<6} n={len(vals):<4} median {statistics.median(vals):,.0f}")
    print("  NO COST FIGURE. dev/vendors.toml carries price BANDS and no "
          "per-token rate, so money is not derivable here (DD8).")
    return 0


if __name__ == "__main__":
    sys.exit(main())
