#!/usr/bin/env python3
"""`scripts/pod/keeper.sh`: the restart policy, exercised rather than read.

**THIS FILE EXISTS BECAUSE OF WHEN THE KEEPER RUNS.** It runs on the day the loop is
already broken, so a defect in it is discovered at the worst possible moment and by
nobody. Every number it acts on is overridable from the environment for exactly this
reason, and every branch below is driven with a fake loop that exits on command.

THE THREE ENDINGS THAT MUST NOT RESTART are the point. Until 2026-08-18 `pod run` gave
exit 1 to a rule (d) STOP, to a startup refusal and to an unhandled exception alike, and
a keeper cannot be written against that: restarting a STOP repeals the STOP rule, and
restarting a lock refusal hot-loops against the runner that already holds the lock.

**`herdr` IS SHADOWED ON `PATH` AND THIS SUITE HAD A LIVE SIDE EFFECT WITHOUT IT.**
MEASURED 2026-08-19: `tell()` calls `herdr agent prompt` unconditionally, and these tests
drive exactly the three endings that call it, so every run of this file fired four real
prompts at the resident maintainer's live session. The owner asked why the loop kept
dying while everything sat idle. Nothing was dying: the timestamps marched through this
file's own test order. A stub on `PATH` is preferred over a test-only branch inside
`keeper.sh`, because a branch that exists to be switched off in tests is a branch that
can be switched off anywhere, and because the stub lets the tests read what was SENT.
"""
from __future__ import annotations

import os
import subprocess
import tempfile
import unittest
from pathlib import Path

ROOT = Path(__file__).resolve().parent.parent.parent
KEEPER = ROOT / "scripts" / "pod" / "keeper.sh"

FAKE = """#!/bin/sh
echo x >> "$COUNT"
%s
exit ${FAKE_RC:-1}
"""


class Keeper(unittest.TestCase):
    def setUp(self):
        self.dir = tempfile.TemporaryDirectory()
        self.tmp = Path(self.dir.name)
        self.count = self.tmp / "count"
        self.count.write_text("")
        self.retry = ROOT / ".pod-state" / "keeper-retry"
        self.retry.unlink(missing_ok=True)
        self.addCleanup(self.dir.cleanup)
        self.addCleanup(lambda: self.retry.unlink(missing_ok=True))

    def _loop(self, body=""):
        p = self.tmp / "loop.sh"
        p.write_text(FAKE % body)
        p.chmod(0o755)
        return p

    def _no_herdr(self, e):
        """Shadow `herdr` so no test can prompt the LIVE maintainer. Returns the log."""
        bin_dir = self.tmp / "bin"
        bin_dir.mkdir(exist_ok=True)
        sent = self.tmp / "prompts"
        stub = bin_dir / "herdr"
        stub.write_text('#!/bin/sh\nprintf \'%s\\n\' "$*" >> "' + str(sent) + '"\n')
        stub.chmod(0o755)
        e["PATH"] = str(bin_dir) + os.pathsep + e.get("PATH", "")
        return sent

    def herdr_calls(self):
        """EVERY `herdr` call the keeper made, prompts and workspace stamping alike."""
        p = self.tmp / "prompts"
        return p.read_text().splitlines() if p.is_file() else []

    def prompts(self):
        return [l for l in self.herdr_calls() if l.startswith("agent prompt")]

    def _run(self, rc, timeout=20, body="", **env):
        e = dict(os.environ, COUNT=str(self.count), FAKE_RC=str(rc),
                 KEEPER_PY="/bin/sh", KEEPER_LOOP=str(self._loop(body)),
                 KEEPER_MAX_FAST="2", KEEPER_BACKOFF="1", KEEPER_HEALTHY="300")
        e.update({k: str(v) for k, v in env.items()})
        self._no_herdr(e)
        return subprocess.run(["sh", str(KEEPER)], capture_output=True, text=True,
                              timeout=timeout, env=e, cwd=str(ROOT))

    def _runs(self):
        return len(self.count.read_text().split())

    def test_a_signal_exit_stops_the_keeper_and_restarts_nothing(self):
        out = self._run(0)
        self.assertEqual(out.returncode, 0)
        self.assertEqual(self._runs(), 1, "exit 0 is the owner stopping the loop")

    def test_a_rule_d_STOP_is_never_restarted(self):
        """Restarting a STOP would repeal rule (d), which exists to hold for a human."""
        out = self._run(3)
        self.assertEqual(out.returncode, 3)
        self.assertEqual(self._runs(), 1)
        self.assertIn("resume", out.stdout, "it must say how to come back")

    def test_NO_TEST_EVER_PROMPTS_THE_LIVE_MAINTAINER(self):
        """The regression this suite caused. It fired four real prompts at the resident
        session on every run, and the owner read them as a loop dying while idle."""
        out = self._run(3)
        self.assertIn("STOPPED", out.stdout, "the ending under test did not fire")
        self.assertTrue(self.prompts(),
                        f"the stub caught no prompt; herdr calls were {self.herdr_calls()}")
        # EVERY herdr call went to the stub, so none reached the live session. The stub is
        # the only `herdr` on PATH, so a call that ran at all was intercepted.
        self.assertTrue(all(c.split()[:1] in (["agent"], ["workspace"], ["pane"])
                            for c in self.herdr_calls()),
                        f"the keeper called herdr in an unexpected way: {self.herdr_calls()}")

    def test_every_prompt_carries_the_WALL_CLOCK_it_was_written_at(self):
        """A prompt QUEUES while the maintainer is busy and arrives hours later, where
        `$ran` cannot place it: the pane said `exit 3 after 6947 s` while the prompt in
        hand said `after 0 s`. MEASURED 2026-08-19."""
        self._run(3)
        self.assertTrue(self.prompts())
        for line in self.prompts():
            self.assertRegex(line, r"\[keeper \d{4}-\d{2}-\d{2} \d{2}:\d{2}:\d{2}\]")

    def test_a_startup_refusal_is_never_restarted(self):
        """Exit 4 means it never ticked. A second runner holding the lock gives this,
        and restarting it is a hot loop against a healthy pod."""
        out = self._run(4)
        self.assertEqual(out.returncode, 4)
        self.assertEqual(self._runs(), 1)

    def test_a_crash_restarts_until_the_ceiling_then_asks_and_waits(self):
        """The ceiling is what stops a crash-restart-crash loop from spinning forever."""
        e = dict(os.environ, COUNT=str(self.count), FAKE_RC="1",
                 KEEPER_PY="/bin/sh", KEEPER_LOOP=str(self._loop()),
                 KEEPER_MAX_FAST="2", KEEPER_BACKOFF="1", KEEPER_HEALTHY="300")
        self._no_herdr(e)
        proc = subprocess.Popen(["sh", str(KEEPER)], stdout=subprocess.PIPE,
                                stderr=subprocess.STDOUT, text=True, env=e, cwd=str(ROOT))
        try:
            with self.assertRaises(subprocess.TimeoutExpired):
                proc.wait(timeout=8)            # it must still be waiting, not exited
            self.assertEqual(self._runs(), 2, "it restarted to the ceiling and no more")
            self.retry.parent.mkdir(parents=True, exist_ok=True)
            self.retry.touch()                  # the maintainer says it landed a repair
            proc.wait(timeout=8)
        except subprocess.TimeoutExpired:
            pass
        finally:
            proc.kill()
            out = proc.communicate()[0]
        self.assertGreater(self._runs(), 2, "the retry file did not wake the keeper")
        self.assertIn("keeper-retry", out, "it must name the file that wakes it")

    def test_a_run_that_lasted_resets_the_fast_counter(self):
        """A loop that works for a while and then dies is NOT a crash loop, and treating
        it as one would stop restarting a pod that is merely unlucky."""
        e = dict(os.environ, COUNT=str(self.count), FAKE_RC="1",
                 KEEPER_PY="/bin/sh", KEEPER_LOOP=str(self._loop("sleep 2")),
                 KEEPER_MAX_FAST="2", KEEPER_BACKOFF="1", KEEPER_HEALTHY="1")
        self._no_herdr(e)
        proc = subprocess.Popen(["sh", str(KEEPER)], stdout=subprocess.PIPE,
                                stderr=subprocess.STDOUT, text=True, env=e, cwd=str(ROOT))
        try:
            proc.wait(timeout=10)
        except subprocess.TimeoutExpired:
            pass
        proc.kill()
        out = proc.communicate()[0]
        self.assertGreaterEqual(self._runs(), 3, "it stopped restarting a healthy loop")
        self.assertNotIn("STOPPED restarting", out)


class WorkspaceStamp(unittest.TestCase):
    """The keeper records which herdr workspace the agent panes belong in.

    **A MISSING OR STALE RECORD IS NOT INERT.** The dispatch driver reads
    `.pod-state/herdr-workspace` to pick the pane it splits from, and when it cannot read
    one it CREATES a workspace, so every agent opens somewhere the owner is not looking.
    MEASURED 2026-08-19: the file still named `wM`, a workspace closed hours earlier.
    Making this the owner's manual first step was the wrong shape; the keeper knows which
    pane it is in.
    """

    WSFILE = ROOT / ".pod-state" / "herdr-workspace"

    def setUp(self):
        self.saved = self.WSFILE.read_text() if self.WSFILE.exists() else None
        self.dir = tempfile.TemporaryDirectory()
        self.addCleanup(self.dir.cleanup)
        self.addCleanup(self._restore)

    def _restore(self):
        if self.saved is None:
            self.WSFILE.unlink(missing_ok=True)
        else:
            self.WSFILE.write_text(self.saved)

    def _run(self):
        loop = Path(self.dir.name) / "loop.sh"
        loop.write_text("#!/bin/sh\nexit 0\n")
        loop.chmod(0o755)
        e = dict(os.environ, KEEPER_PY="/bin/sh", KEEPER_LOOP=str(loop))
        return subprocess.run(["sh", str(KEEPER)], capture_output=True, text=True,
                              timeout=30, env=e, cwd=str(ROOT)).stdout

    def _herdr(self):
        return subprocess.run(["sh", "-c", "command -v herdr"],
                              capture_output=True).returncode == 0

    def test_a_live_setting_is_never_overwritten(self):
        """A workspace id that still resolves is a deliberate choice."""
        if not self._herdr():
            self.skipTest("herdr is not installed")
        live = subprocess.run(
            ["sh", "-c", "herdr pane current | " + str(ROOT / ".venv/bin/python") +
             " -c 'import json,sys; print(json.load(sys.stdin)[\"result\"]"
             "[\"pane\"][\"workspace_id\"])'"],
            capture_output=True, text=True).stdout.strip()
        if not live:
            self.skipTest("not running inside a herdr pane")
        self.WSFILE.write_text(live)
        self._run()
        self.assertEqual(self.WSFILE.read_text(), live, "a live setting was clobbered")

    def test_an_absent_record_is_stamped_with_this_pane(self):
        if not self._herdr():
            self.skipTest("herdr is not installed")
        self.WSFILE.unlink(missing_ok=True)
        out = self._run()
        if "not inside a herdr pane" in out:
            self.skipTest("not running inside a herdr pane")
        self.assertTrue(self.WSFILE.exists(), "the keeper left the record absent")
        self.assertIn(self.WSFILE.read_text().strip(), out)

    def test_a_DEAD_workspace_is_replaced_and_not_kept(self):
        """This is the case that was live on 2026-08-19 and would have scattered every
        agent pane into a workspace the driver invented."""
        if not self._herdr():
            self.skipTest("herdr is not installed")
        self.WSFILE.write_text("wZZZ-does-not-exist")
        out = self._run()
        if "not inside a herdr pane" in out:
            self.skipTest("not running inside a herdr pane")
        self.assertNotEqual(self.WSFILE.read_text().strip(), "wZZZ-does-not-exist")

    def test_the_stamp_does_not_borrow_the_LOOP_interpreter(self):
        """`$PY` is the loop's interpreter and tests override it. Borrowing it for the
        stamp made this feature fail under exactly that override, and report「not inside
        a herdr pane」on a machine that was. Two jobs, two names."""
        src = KEEPER.read_text()
        i = src.index("stamp_workspace() {")
        j = src.index("}", src.index("herdr pane current", i))
        self.assertNotIn('"$PY"', src[i:j], "the stamp borrows the loop's interpreter")


if __name__ == "__main__":
    unittest.main(verbosity=2)
