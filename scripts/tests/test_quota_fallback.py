#!/usr/bin/env python3
"""Pins the quota fallback of [LJ-1.296]: refuse on the vendor's own refusal.

WHAT THIS PINS. The dispatch tool reads a finished run's artifacts for the
vendor's terminal refusal, classifies it, sticks a block on the PROVIDER, and
refuses every further pi launch on that provider until a probe clears it. The
matcher's vocabulary is INFERRED, copied verbatim from pi's own error
classifier (`.../pi-ai/dist/utils/retry.js`), because no refusal has ever
been observed on this machine (MEASURED 2026-08-15). An inferred matcher must
fail loudly on a shape it does not know, so the test pins that an
unclassified terminal error is REPORTED and never silently dropped.

WHAT THE SUBJECT IS. The patch lands in `.claude/skills/codex-dispatch/
dispatch.py`, which is gitignored and therefore invisible to a fresh clone,
so the test's subject is the TRACKED patched copy beside this task's probe
(`agents/tasks/LJ-1-296/probe/dispatch_patched.py`). When the gitignored
original exists on this machine, the test first re-derives the copy from it
through `apply_edits.py` and demands a byte-identical result, so a drift
between the diff and the shipped copy cannot pass silently.

THE HAND-OFF IS NOT A RE-ROUTE. The tool cannot start an in-harness agent,
and [LJ-1.296] forbids dressing the message up as one. The test pins the
words.
"""

import importlib.util
import json
import subprocess
import sys
import tempfile
from pathlib import Path

REPO = Path(__file__).resolve().parent.parent.parent
PROBE = REPO / "agents" / "tasks" / "LJ-1-296" / "probe"
PATCHED = PROBE / "dispatch_patched.py"
PRISTINE = REPO / ".claude" / "skills" / "codex-dispatch" / "dispatch.py"

checks = 0


def ok(cond: bool, what: str) -> None:
    global checks
    if not cond:
        print(f"test_quota_fallback: FAIL: {what}")
        sys.exit(1)
    checks += 1


def load_module():
    """Import the patched copy under a private state directory."""
    tmp = tempfile.mkdtemp(prefix="lj1296-")
    spec = importlib.util.spec_from_file_location("dispatch_lj1296", PATCHED)
    mod = importlib.util.module_from_spec(spec)
    sys.modules["dispatch_lj1296"] = mod
    spec.loader.exec_module(mod)
    mod.QUOTA_BLOCKS_FILE = Path(tmp) / "quota-blocks.json"
    return mod, Path(tmp)


# ---------------------------------------------------------------- 0. the diff still applies
if PRISTINE.exists() and (PROBE / "apply_edits.py").exists():
    r = subprocess.run(
        [sys.executable, str(PROBE / "apply_edits.py")],
        capture_output=True, text=True, cwd=str(PROBE))
    ok(r.returncode == 0, f"apply_edits.py failed: {r.stdout} {r.stderr}")
    regen = PROBE / "dispatch_patched.py"
    ok(regen.read_text() == PATCHED.read_text(),
       "regenerated copy differs from the shipped copy; re-copy it")

D, tmp = load_module()

# ---------------------------------------------------------------- 1. the vocabulary
# Every string below is pi-ai's own, from NON_RETRYABLE_PROVIDER_LIMIT_ERROR_
# PATTERN (quota class) and RETRYABLE_PROVIDER_ERROR_PATTERN (rate class).
for text in ["insufficient_quota", "You exceeded your current quota, please check "
             "your plan and billing details",
             "Monthly usage limit reached", "out of budget",
             "GoUsageLimitError", "FreeUsageLimitError"]:
    ok(D.classify_vendor_error(text) == "quota", f"quota class missed: {text!r}")
for text in ["429 Too Many Requests", "rate limit exceeded, retry in 30s",
             "server error 503 while streaming",
             "ResourceExhausted"]:
    ok(D.classify_vendor_error(text) == "rate", f"rate class missed: {text!r}")
for text in ["context overflow", "tool bash exited 1", ""]:
    ok(D.classify_vendor_error(text) is None, f"false positive on: {text!r}")

# ---------------------------------------------------------------- 2. the structured reader
# A pi events sidecar whose last assistant message died on the vendor.
ev = tmp / "events.jsonl"
ev.write_text(
    '{"type":"session","id":"abc"}\n'
    '{"type":"message_end","message":{"role":"user"}}\n'
    '{"type":"message_end","message":{"role":"assistant","stopReason":"stop"}}\n'
    '{"type":"message_end","message":{"role":"assistant","stopReason":"error",'
    '"errorMessage":"insufficient_quota: your balance is gone"}}\n')
hit = D.read_vendor_terminal_error({"events": str(ev), "log": ""})
ok(hit is not None, "sidecar error not read")
ok(hit[0].startswith("events sidecar"), f"wrong source named: {hit[0]}")
ok("insufficient_quota" in hit[1], "error text not carried")
# A CLEAN run reads as no refusal.
ev2 = tmp / "clean.jsonl"
ev2.write_text('{"type":"message_end","message":{"role":"assistant","stopReason":"stop"}}\n')
ok(D.read_vendor_terminal_error({"events": str(ev2), "log": ""}) is None,
   "clean sidecar read as a refusal")

# ---------------------------------------------------------------- 3. the herdr-pi reader
# The herdr log names the pi session file; the refusal is a message record.
sess = tmp / "pi-session.jsonl"
sess.write_text(
    '{"type":"message","message":{"role":"user"}}\n'
    '{"type":"message","message":{"role":"assistant","stopReason":"error",'
    '"errorMessage":"quota exceeded for this subscription"}}\n')
hlog = tmp / "herdr.log"
hlog.write_text(
    '{"id":"cli:agent:start","result":{"agent":{"agent_session":{"kind":"path",'
    '"value":"' + str(sess) + '"},"agent_status":"idle"}}}}\n')
hit = D.read_vendor_terminal_error({"events": "", "log": str(hlog)})
ok(hit is not None, "herdr session file not read")
ok("quota exceeded" in hit[1], "session error text not carried")

# ---------------------------------------------------------------- 4. the launch-time shape
# pi died before any event; its stderr passed through and the wrapper recorded
# a non-zero exit.
plog = tmp / "pi-launch.log"
plog.write_text("[pi] launching: pi --mode json -p ...\n"
                "Error: 429 rate limit reached, retry later\n"
                "[pi] exit rc=1\n")
hit = D.read_vendor_terminal_error({"events": "", "log": str(plog)})
ok(hit is not None, "launch-time refusal not read")
ok("rate limit" in hit[1], "stderr line not carried")

# ---------------------------------------------------------------- 5. prose cannot stick a block
# The word quota everywhere, but no structured error: the reader must refuse
# to conclude. This is the false-positive half of an INFERRED matcher.
prose = tmp / "prose.log"
prose.write_text("the report discusses quota at length\n" * 40 + "[pi] exit rc=0\n")
ok(D.read_vendor_terminal_error({"events": "", "log": str(prose)}) is None,
   "prose with rc=0 read as a refusal")
prose2 = tmp / "prose2.jsonl"
prose2.write_text(
    '{"type":"message_end","message":{"role":"assistant","stopReason":"stop"}}\n')
ok(D.read_vendor_terminal_error({"events": str(prose2),
                                 "log": str(prose)}) is None,
   "clean sidecar + quota-heavy prose read as a refusal")

# ---------------------------------------------------------------- 6. the launch gate
prov = D.PI_PROVIDER
ok(D.check_quota(prov, allow=False) is None, "gate fired with no block file")
D.stick_quota_block(prov, "glm-5.3", "quota", "test: synthetic")
why = D.check_quota(prov, allow=False)
ok(why is not None, "gate silent with a stuck block")
ok("NOT A RE-ROUTE" in why, "refusal does not name the hand-off")
ok(f"quota-clear {prov}" in why, "refusal does not name the clear command")
ok(D.check_quota(prov, allow=True) is None, "--allow-quota does not bypass once")
ok(D.check_quota("someothervendor", allow=False) is None,
   "block on one vendor gates another")

# ---------------------------------------------------------------- 7. the scan acts and fails loud
import io
import contextlib
buf = io.StringIO()
with contextlib.redirect_stdout(buf):
    D.scan_quota_refusal("LJ-9.99", {"events": str(ev), "log": "",
                                      "model": "glm-5.3",
                                      "brief": "agents/tasks/LJ-9-99/x.md"})
out = buf.getvalue()
ok("ENDED ON A VENDOR REFUSAL" in out, "scan banner missing")
ok("NOT an automatic re-route" in out, "hand-off does not disclaim the re-route")
ok(D.QUOTA_BLOCKS_FILE.exists(), "scan did not stick the state")
stuck = json.loads(D.QUOTA_BLOCKS_FILE.read_text())
ok(stuck.get(prov, {}).get("kind") == "quota", "stuck record malformed")
ok(stuck[prov]["evidence"].startswith("LJ-9.99:"), "evidence does not name the task")
# UNCLASSIFIED terminal error: reported, never silent, nothing stuck.
ev3 = tmp / "weird.jsonl"
ev3.write_text('{"type":"message_end","message":{"role":"assistant",'
               '"stopReason":"error","errorMessage":"mystery vendor failure 70007"}}\n')
D.QUOTA_BLOCKS_FILE.unlink()
buf = io.StringIO()
with contextlib.redirect_stdout(buf):
    D.scan_quota_refusal("LJ-9.98", {"events": str(ev3), "log": ""})
out = buf.getvalue()
ok("UNCLASSIFIED VENDOR ERROR" in out, "unclassified error dropped silently")
ok("quota-block" in out, "unclassified report does not name the by-hand command")
ok(not D.QUOTA_BLOCKS_FILE.exists(), "unclassified error stuck a block")

# ---------------------------------------------------------------- 8. clear and block round trip
D.stick_quota_block(prov, "glm-5.3", "quota", "test: round trip")
blocks = D.load_quota_blocks()
ok(prov in blocks, "round trip lost the record")
blocks.pop(prov)
D.save_quota_blocks(blocks)
ok(D.load_quota_blocks() == {}, "save/load round trip drifted")

print(f"test_quota_fallback: all checks passed ({checks})")
