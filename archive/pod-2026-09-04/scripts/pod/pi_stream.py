#!/usr/bin/env python3
"""Run `pi --mode json` and turn its event stream into a log a human can read.

WHY THIS FILE EXISTS. `pi -p` prints NOTHING until it exits, so a pi dispatch left
its log empty for the whole run and nobody could watch it. [LJ-1.121] produced a
2071-byte log that never changed size. `pi --mode json` fixes that, but its raw
output is one JSON object per TOKEN: a 27-second run wrote 27 KB over 269 lines,
of which 237 were `message_update` deltas. Raw JSONL is streamed but not readable.

So this wrapper sits between pi and the log. It does four things:

  1. STREAMS. Every event is rendered and flushed the moment it arrives, so the
     log grows during the run.
  2. PRINTS A CODEX-SHAPED SESSION LINE. pi's session id is the `id` field of the
     FIRST event. This wrapper re-emits it as `session id: <uuid>`, which is
     exactly what dispatch.py's SESSION_RE already matches. Resume needed no new
     scraper: the one that codex uses now works for pi too.
  3. KEEPS EVERY RAW EVENT. The rendered log drops detail, so the untouched JSONL
     goes to a sidecar file. Nothing measured is thrown away.
  4. WRITES THE FINAL MESSAGE. The authoritative answer is the LAST `message_end`
     whose `message.role` is `assistant`, not the concatenated deltas, and not
     `agent_end`.

WHAT THE RENDERED LOG DROPS, and it is listed so nobody has to guess:
  - `tool_execution_update`, the partial tool output. The final result is kept.
  - `toolcall_delta`, the token-by-token tool arguments. `toolcall_end` carries
    the complete arguments and IS kept.
  - the `agent_end` message array, which repeats every message of the whole run.
  - `message_start`/`message_end` for `user` and `toolResult` roles, whose content
    is already shown by the prompt and by `tool_execution_end`.
All of these stay in the sidecar `.jsonl` verbatim.

TERMINATION. `agent_settled` is the last event, and it can follow more than one
`agent_end`, because `agent_end` carries `willRetry`. This wrapper does not stop
on any event; it stops when pi closes its stdout and exits, and it returns pi's
own exit code. That keeps the dispatcher's rule intact: one pid, alive for
exactly as long as the run.

USAGE
    pi_stream.py --events EVENTS.jsonl --final FINAL.md -- pi --mode json ...
"""

from __future__ import annotations

import argparse
import json
import signal
import subprocess
import sys
from pathlib import Path

# Wrap a long delta run so no single log line grows without bound. A thinking
# block arrives as ~200 deltas of a few characters each; without a wrap the log
# holds one 4000-character line and `tail` is useless on it.
WRAP = 100

# Tool arguments are shown inline, so cap them. The full arguments are in the
# sidecar. 300 characters holds a shell command or a file path and a range.
ARG_CAP = 300
RESULT_CAP = 300


class Renderer:
    """Turn pi events into readable lines on stdout. Flushes after every write."""

    def __init__(self, out, events_fh, final_path: Path):
        self.out = out
        self.events = events_fh
        self.final_path = final_path
        self.col = 0            # characters written on the current unfinished line
        self.open_line = False  # a delta run is in progress
        self.session_seen = False
        self.final_msg = None   # the last assistant message_end payload
        self.calls: dict[str, str] = {}   # toolCallId -> toolName

    # -- low level -----------------------------------------------------------

    def _w(self, text: str) -> None:
        self.out.write(text)
        self.out.flush()

    def _close_line(self) -> None:
        if self.open_line:
            self._w("\n")
            self.open_line = False
            self.col = 0

    def line(self, text: str) -> None:
        self._close_line()
        self._w(text + "\n")

    def delta(self, text: str) -> None:
        """Append streamed text to the current line, wrapping at WRAP columns."""
        if not text:
            return
        for ch in text:
            if ch == "\n":
                self._w("\n  ")
                self.col = 2
                continue
            self._w(ch)
            self.col += 1
            if self.col >= WRAP:
                self._w("\n  ")
                self.col = 2
        self.open_line = True

    # -- events --------------------------------------------------------------

    def raw(self, raw_line: str) -> None:
        self.events.write(raw_line if raw_line.endswith("\n") else raw_line + "\n")
        self.events.flush()

    def event(self, ev: dict) -> None:
        t = ev.get("type")
        if t == "session":
            self.session_seen = True
            # THE CODEX SHAPE IS DELIBERATE. dispatch.py's SESSION_RE looks for
            # `session id:` followed by a hex-and-dash token. Emitting that exact
            # shape makes both the launch-time scrape and `resume`'s log rescan
            # work for pi without a second pattern.
            self.line(f"session id: {ev.get('id', '')}")
            self.line(f"[pi] cwd={ev.get('cwd', '')} session-version={ev.get('version', '')}")
        elif t == "agent_start":
            self.line("[pi] agent start")
        elif t == "turn_start":
            self.line("[pi] --- turn start ---")
        elif t == "turn_end":
            self.line("[pi] --- turn end ---")
        elif t == "agent_settled":
            self.line("[pi] agent settled")
        elif t == "agent_end":
            self.line(f"[pi] agent end (willRetry={ev.get('willRetry')})")
        elif t == "message_start":
            role = (ev.get("message") or {}).get("role")
            if role == "user":
                self.line("[user] prompt sent")
        elif t == "message_end":
            self._message_end(ev)
        elif t == "message_update":
            self._update(ev.get("assistantMessageEvent") or {})
        elif t == "tool_execution_start":
            name = ev.get("toolName", "?")
            self.calls[ev.get("toolCallId", "")] = name
            self.line(f"[tool] {name} {_short(ev.get('args'), ARG_CAP)}")
        elif t == "tool_execution_end":
            name = ev.get("toolName") or self.calls.get(ev.get("toolCallId", ""), "?")
            mark = "ERROR" if ev.get("isError") else "ok"
            self.line(f"[tool] {name} -> {mark}: "
                      f"{_short(_result_text(ev.get('result')), RESULT_CAP)}")
        elif t == "tool_execution_update":
            pass  # dropped: partial tool output, kept raw in the sidecar
        elif t in ("bash_execution_update", "queue_update", "entry_appended",
                   "session_info_changed", "thinking_level_changed"):
            pass  # dropped: high volume or no operator value; kept in the sidecar
        elif t in ("compaction_start", "compaction_end",
                   "auto_retry_start", "auto_retry_end", "extension_error"):
            # Rare and load-bearing. A retry or a compaction changes what the run
            # did, so it must be visible in the readable log.
            self.line(f"[pi] {t} {_short(ev, 400)}")
        else:
            self.line(f"[pi] {t}")

    def _update(self, a: dict) -> None:
        k = a.get("type")
        if k == "thinking_start":
            self._close_line()
            self._w("[think] ")
            self.col, self.open_line = 8, True
        elif k == "text_start":
            self._close_line()
            self._w("[reply] ")
            self.col, self.open_line = 8, True
        elif k in ("thinking_delta", "text_delta"):
            self.delta(a.get("delta") or "")
        elif k in ("thinking_end", "text_end"):
            self._close_line()
        # toolcall_start, toolcall_delta and toolcall_end are all dropped.
        # `tool_execution_start` carries the same tool name and the same complete
        # arguments, and it fires when the call actually RUNS, so rendering both
        # printed every tool call twice. The sidecar keeps all three.

    def _message_end(self, ev: dict) -> None:
        msg = ev.get("message") or {}
        if msg.get("role") != "assistant":
            return
        self.final_msg = msg
        u = msg.get("usage") or {}
        self._close_line()
        self.line(f"[usage] in={u.get('input')} out={u.get('output')} "
                  f"cacheRead={u.get('cacheRead')} total={u.get('totalTokens')} "
                  f"stop={msg.get('stopReason')}")
        # WRITE THE FINAL FILE ON EVERY ASSISTANT MESSAGE, not once at exit. A
        # killed run then still leaves the last complete answer on disk, which is
        # the only thing `resume --note` has to work from.
        self._write_final()

    def _write_final(self) -> None:
        if not self.final_msg:
            return
        parts = [c.get("text", "") for c in (self.final_msg.get("content") or [])
                 if c.get("type") == "text"]
        try:
            self.final_path.write_text("\n".join(parts), encoding="utf-8")
        except OSError as exc:
            self.line(f"[pi] could not write the final message: {exc}")

    def close(self) -> None:
        self._close_line()
        self._write_final()


def _result_text(result) -> str:
    if isinstance(result, dict):
        parts = [c.get("text", "") for c in (result.get("content") or [])
                 if isinstance(c, dict) and c.get("type") == "text"]
        if parts:
            return " ".join(parts)
    return _short(result, RESULT_CAP)


def _short(value, cap: int) -> str:
    if not isinstance(value, str):
        try:
            value = json.dumps(value, ensure_ascii=False)
        except (TypeError, ValueError):
            value = str(value)
    value = value.replace("\n", " ").replace("\r", " ").strip()
    return value if len(value) <= cap else value[:cap] + f"...(+{len(value) - cap})"


def main() -> int:
    ap = argparse.ArgumentParser(description=__doc__)
    ap.add_argument("--events", required=True, help="sidecar file for the raw JSONL")
    ap.add_argument("--final", required=True, help="file for the final assistant message")
    ap.add_argument("cmd", nargs=argparse.REMAINDER,
                    help="-- then the full pi command line")
    a = ap.parse_args()

    cmd = a.cmd[1:] if a.cmd and a.cmd[0] == "--" else a.cmd
    if not cmd:
        print("pi_stream: no command after --", file=sys.stderr)
        return 2

    out = sys.stdout
    events_path = Path(a.events)
    events_path.parent.mkdir(parents=True, exist_ok=True)

    # stdin=DEVNULL IS LOAD-BEARING AND IT COST A PROBE. Measured 2026-08-13: pi
    # launched as a background job with a terminal on stdin writes NOTHING for
    # 75 seconds, because reading a terminal from the background raises SIGTTIN
    # and stops the process. With /dev/null the same run streamed from t=3s.
    with open(events_path, "a", encoding="utf-8") as events_fh:
        r = Renderer(out, events_fh, Path(a.final))
        r.line(f"[pi] launching: {' '.join(cmd[:6])} ... ({len(cmd)} argv items)")
        try:
            proc = subprocess.Popen(
                cmd, stdout=subprocess.PIPE, stderr=subprocess.STDOUT,
                stdin=subprocess.DEVNULL, text=True, encoding="utf-8",
                errors="replace", bufsize=1)
        except OSError as exc:
            r.line(f"[pi] could not launch: {exc}")
            return 1

        # A SIGTERM to this wrapper must reach pi. Without this the dispatcher
        # kills the wrapper, the log stops growing, and pi keeps burning tokens
        # with nobody reading it.
        def _forward(signum, _frame):
            try:
                proc.send_signal(signum)
            except OSError:
                pass
        for sig in (signal.SIGTERM, signal.SIGINT, signal.SIGHUP):
            try:
                signal.signal(sig, _forward)
            except (ValueError, OSError):
                pass

        try:
            for raw_line in proc.stdout:
                line = raw_line.rstrip("\n")
                if not line.strip():
                    continue
                r.raw(line)
                try:
                    ev = json.loads(line)
                except json.JSONDecodeError:
                    # pi writes its own diagnostics to stderr, which is merged in
                    # here. Pass such a line through rather than losing it.
                    r.line(line)
                    continue
                if isinstance(ev, dict):
                    r.event(ev)
                else:
                    r.line(_short(ev, 400))
        finally:
            rc = proc.wait()
            r.close()
            r.line(f"[pi] exit rc={rc}")
            if not r.session_seen:
                r.line("[pi] WARNING: no session event arrived, so this run "
                       "cannot be resumed")
        return rc


if __name__ == "__main__":
    sys.exit(main())
