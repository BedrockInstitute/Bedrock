#!/usr/bin/env python3
"""Probe for LJ-1.371: can the tree see an in-harness dispatch?

Three measurements, all from the live tree, no dispatcher cooperation:

  1. BYPASS COUNT. Live task dirs whose dispatch never passed through
     dispatch.py, taken as "absent from the registry", cross-checked
     against dispatch logs. Ruling-only dirs are excluded.

  2. TREE INFERENCE, NOW. The candidate rule: a task dir is LIVE when
     its report mtime is younger than N minutes AND the task's PLAN
     section 11 row shows no verdict. Ground truth NOW: the registry
     (pids alive) plus `herdr agent list` plus this process itself.

  3. FP WINDOW FROM GIT. For every landed return, the audit delay
     (commit time minus report mtime) is the window in which the task
     is DEAD but the rule still reads it live, bounded by N.

Run: .venv/bin/python agents/tasks/LJ-1-371/probe_registry_inference.py
"""
import json
import re
import subprocess
import time
from pathlib import Path

ROOT = Path("/Users/alsg/Agentic/Bedrock")
REG = ROOT / ".claude/skills/codex-dispatch/.state/registry.json"
LOGS = ROOT / ".claude/skills/codex-dispatch/.state/logs"
PLAN = ROOT / "dev/PLAN.md"


def code(name: str) -> int:
    m = re.search(r"(\d+)$", name)
    return int(m.group(1)) if m else 0


def is_ruling_only(d: Path) -> bool:
    """A dir with no tier-bearing brief and no report: an owner ruling."""
    has_brief = has_report = False
    for md in d.glob("*.md"):
        if md.name.lower().endswith("-report.md") or md.name == "REPORT.md":
            has_report = True
            continue
        if re.search(r"tier:", md.read_text(errors="ignore")[:1000]):
            has_brief = True
    return not has_brief and not has_report


def task_dirs() -> list[Path]:
    base = ROOT / "agents/tasks"
    return sorted((p for p in base.iterdir()
                   if p.is_dir() and p.name != "archive"), key=lambda p: p.name)


def measurement_1() -> None:
    reg = json.loads(REG.read_text())["dispatches"]
    log_names = {l.name for l in LOGS.iterdir()} if LOGS.exists() else set()
    dispatches, bypass, ruled = 0, [], []
    for d in task_dirs():
        if is_ruling_only(d):
            ruled.append(d.name)
            continue
        dispatches += 1
        key = d.name.replace("1-", "1.", 1)
        if d.name in reg or key in reg:
            continue
        # cross-check: a dispatch log proves it went through dispatch.py
        # even if the record was later culled.
        stem = key + "-"
        if any(n.startswith(stem) for n in log_names):
            continue
        bypass.append(d.name)
    print("== 1. BYPASS COUNT (live corpus) ==")
    print(f"dispatch-bearing task dirs: {dispatches}")
    print(f"ruling-only dirs excluded : {len(ruled)} ({', '.join(ruled)})")
    print(f"never through dispatch.py : {len(bypass)} "
          f"({len(bypass)/dispatches*100:.0f}% of dispatches)")
    eras = [(1, 122, "pre-override (registryed codex)"),
            (123, 199, "override era, opus in-harness"),
            (200, 281, "deepseek mode, adversarial row in-harness"),
            (282, 355, "in-harness-subagent-mode"),
            (356, 999, "pi-subagent-mode (today on)")]
    for lo, hi, label in eras:
        sub = [x for x in bypass if lo <= code(x) <= hi]
        allsub = [d.name for d in task_dirs() if lo <= code(d.name) <= hi
                  and d.name not in ruled]
        if allsub:
            print(f"  {label}: {len(sub)}/{len(allsub)} bypassed")


def live_ground_truth() -> set[str]:
    truth = set()
    reg = json.loads(REG.read_text())["dispatches"]
    for t, d in reg.items():
        pid = int(d.get("pid", 0) or 0)
        started = d.get("proc_start", "")
        try:
            import os
            os.kill(pid, 0)
        except OSError:
            continue
        if started:
            # pid recycling check, same reasoning as dispatch.py alive()
            out = subprocess.run(["ps", "-o", "lstart=", "-p", str(pid)],
                                 capture_output=True, text=True)
            if out.stdout.strip() != started:
                continue
        truth.add(t.replace(".", "-"))
    try:
        out = subprocess.run(["herdr", "agent", "list"], capture_output=True,
                             text=True, timeout=15)
        for a in json.loads(out.stdout)["result"]["agents"]:
            if a.get("agent_status") == "working" and a.get("name"):
                truth.add(a["name"].replace(".", "-"))
    except Exception:
        pass
    # only task-shaped names are claims about dispatches
    return {t for t in truth if re.fullmatch(r"[Ll][Jj]-1-\d+", t)}


def plan_rows_with_verdict() -> set[str]:
    """Task codes whose PLAN section 11 row carries a verdict marker.

    A returned task's row starts '| LJ-1.NNN | <title> | <verdict>' where a
    live row says DISPATCHED. Any word other than DISPATCHED counts as a
    verdict, mirroring what an orchestrator leaves behind on audit.
    """
    done = set()
    for line in PLAN.read_text().splitlines():
        m = re.match(r"\| (LJ-1[\.-]\d+) \| [^|]+ \| ([^|]+)", line)
        if not m:
            continue
        verdict = m.group(2).strip()
        if verdict and verdict.upper() != "DISPATCHED":
            done.add(m.group(1).replace(".", "-").lower())
    return done


def report_of(d: Path) -> Path | None:
    want = d.name.lower().replace(".", "-") + "-report"
    for p in sorted(d.glob("*.md")):
        if p.stem.lower().replace(".", "-") == want:
            return p
    r = list(d.glob("REPORT.md"))
    return r[0] if r else None


def measurement_2() -> None:
    print("\n== 2. TREE INFERENCE vs GROUND TRUTH, NOW ==")
    truth = live_ground_truth()
    done = plan_rows_with_verdict()
    now = time.time()
    print(f"ground truth live agents now: {sorted(truth) or 'NONE'}")
    for n in (5, 10, 15, 20):
        inferred, missed = [], []
        for d in task_dirs():
            r = report_of(d)
            if r is None or d.name in done:
                continue
            age = (now - r.stat().st_mtime) / 60
            if age < n:
                inferred.append(f"{d.name} (report {age:.1f} min old)")
        missed = [t for t in truth if t.lower() not in
                  {x.split()[0].lower() for x in inferred}]
        fp = [x for x in inferred if x.split()[0].lower() not in
              {t.lower() for t in truth}]
        print(f"  N={n:2d} min: inferred live {len(inferred)}, "
              f"FALSE NEGATIVES {len(missed)} {missed}, "
              f"FALSE POSITIVES {len(fp)} {fp}")
        for x in inferred:
            print(f"      + {x}")


def measurement_3() -> None:
    print("\n== 3. FP WINDOW: audit delay (commit time - report mtime) ==")
    out = subprocess.run(
        ["git", "log", "--format=%h|%ad|%s", "--date=format:%Y-%m-%d %H:%M:%S",
         "-200"],
        cwd=ROOT, capture_output=True, text=True).stdout
    delays = []
    for row in out.splitlines():
        h, date, _ = row.split("|", 2)
        files = subprocess.run(["git", "show", "--name-only", "--format=",
                                h], cwd=ROOT, capture_output=True,
                               text=True).stdout.splitlines()
        for f in files:
            m = re.match(r"agents/tasks/(LJ-1-\d+)/lj-1\.\d+-report\.md$", f)
            if not m:
                continue
            p = ROOT / f
            if not p.exists():
                continue
            mt = time.strptime(p.stat().st_mtime and
                               time.strftime("%Y-%m-%d %H:%M:%S",
                                             time.localtime(p.stat().st_mtime)),
                               "%Y-%m-%d %H:%M:%S")
            ct = time.strptime(date, "%Y-%m-%d %H:%M:%S")
            delay = (time.mktime(ct) - time.mktime(mt)) / 60
            if -5 <= delay <= 600:
                delays.append((m.group(1), delay))
    delays.sort(key=lambda x: -x[1])
    if delays:
        vals = sorted(d for _, d in delays)
        med = vals[len(vals)//2]
        print(f"landed returns measured: {len(delays)}")
        print(f"audit delay median {med:.1f} min, max {delays[0][1]:.0f} min "
              f"({delays[0][0]}), min {vals[0]:.1f} min")
        over = [x for x in delays if x[1] > 10]
        print(f"returns whose audit took >10 min: {len(over)} of {len(delays)}")
        for t, dly in delays[:5]:
            print(f"  {t}: {dly:.0f} min")


if __name__ == "__main__":
    measurement_1()
    measurement_2()
    measurement_3()
