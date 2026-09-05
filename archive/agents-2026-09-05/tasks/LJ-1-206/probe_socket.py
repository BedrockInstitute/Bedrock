#!/usr/bin/env python3
"""Socket probe for LJ-1.206: raw herdr socket client.

Measures the documented Agent Automation wait surface against a live
throwaway agent:
  - events.subscribe pushes one event per agent without re-arming
  - events.wait one-shot semantics, including the at-once-idle question
  - the event vocabulary for RETURN, DEATH and BLOCK
  - agent.prompt embedded wait (--wait --until working)

Wire protocol (https://herdr.dev/docs/socket-api/ "Socket transport"):
newline-delimited JSON over a Unix domain socket at ~/.config/herdr/herdr.sock.

Usage:
  probe.py ping
  probe.py snapshot
  probe.py subscribe <pane_id> [seconds]
  probe.py wait <pane_id> <event> [seconds]     e.g. pane_agent_status_changed
  probe.py prompt-wait <target> <text> <until>  <timeout_ms>
  probe.py get <target>
"""

import json
import os
import socket
import sys
import time

SOCK = os.path.expanduser("~/.config/herdr/herdr.sock")


def request(sock, method, params, rid=None, timeout=15.0):
    rid = rid or f"req_{int(time.time()*1000)}"
    line = json.dumps({"id": rid, "method": method, "params": params}) + "\n"
    sock.sendall(line.encode())
    sock.settimeout(timeout)
    while True:
        resp = sock.recv(1 << 20)
        if not resp:
            raise RuntimeError("socket closed")
        for ln in resp.decode(errors="replace").splitlines():
            if not ln.strip():
                continue
            msg = json.loads(ln)
            if msg.get("id") == rid:
                return msg
        # otherwise it was a pushed event on this connection; keep reading


def connect():
    s = socket.socket(socket.AF_UNIX, socket.SOCK_STREAM)
    s.connect(SOCK)
    return s


def cmd_ping():
    s = connect()
    try:
        r = request(s, "ping", {})
        print(json.dumps(r))
    finally:
        s.close()


def cmd_snapshot():
    s = connect()
    try:
        r = request(s, "session.snapshot", {})
        snap = r.get("result", {})
        for a in snap.get("agents", []):
            print(f"{a.get('name','') or a.get('agent','')}  "
                  f"{a.get('agent_status')}  {a.get('pane_id')}")
    finally:
        s.close()


def cmd_subscribe(pane_id, seconds):
    s = connect()
    try:
        subs = [
            {"type": "pane.agent_status_changed", "pane_id": pane_id},
            {"type": "pane.exited", "pane_id": pane_id},
            {"type": "pane.agent_detected", "pane_id": pane_id},
            {"type": "pane.closed", "pane_id": pane_id},
        ]
        r = request(s, "events.subscribe", {"subscriptions": subs}, rid="sub_1")
        print("ACK:", json.dumps(r))
        s.settimeout(seconds)
        start = time.time()
        n = 0
        while time.time() - start < seconds:
            try:
                data = s.recv(1 << 20)
                if not data:
                    print("socket closed")
                    break
                for ln in data.decode(errors="replace").splitlines():
                    if not ln.strip():
                        continue
                    msg = json.loads(ln)
                    ev = msg.get("event") or msg
                    print(f"[{time.time()-start:6.1f}s] {json.dumps(ev)[:400]}")
                    n += 1
            except socket.timeout:
                print(f"--- timeout after {seconds}s, {n} events")
                break
    finally:
        s.close()


def cmd_wait(pane_id, event, seconds):
    s = connect()
    try:
        params = {"match_event": {"event": event, "pane_id": pane_id},
                  "timeout_ms": int(seconds * 1000)}
        r = request(s, "events.wait", params, rid="wait_1", timeout=seconds + 5)
        print(json.dumps(r))
    finally:
        s.close()


def cmd_prompt_wait(target, text, until, timeout_ms):
    s = connect()
    try:
        params = {"target": target, "text": text,
                  "wait": {"until": until, "timeout_ms": timeout_ms}}
        start = time.time()
        r = request(s, "agent.prompt", params, rid="pw_1", timeout=timeout_ms / 1000 + 5)
        print(f"elapsed {time.time()-start:.2f}s")
        print(json.dumps(r)[:600])
    finally:
        s.close()


def cmd_get(target):
    s = connect()
    try:
        r = request(s, "agent.get", {"target": target})
        a = r.get("result", {}).get("agent", {})
        print(json.dumps({"name": a.get("name"), "agent_status": a.get("agent_status"),
                          "pane_id": a.get("pane_id")}))
    finally:
        s.close()


def main():
    cmd = sys.argv[1]
    if cmd == "ping":
        cmd_ping()
    elif cmd == "snapshot":
        cmd_snapshot()
    elif cmd == "subscribe":
        cmd_subscribe(sys.argv[2], int(sys.argv[3]))
    elif cmd == "wait":
        cmd_wait(sys.argv[2], sys.argv[3], int(sys.argv[4]))
    elif cmd == "prompt-wait":
        cmd_prompt_wait(sys.argv[2], sys.argv[3], sys.argv[4].split(","),
                        int(sys.argv[5]))
    elif cmd == "get":
        cmd_get(sys.argv[2])
    else:
        sys.exit("unknown command")


if __name__ == "__main__":
    main()
