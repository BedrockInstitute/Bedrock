# LJ-1.296 report: a quota fallback from `pi` to in-harness, triggered by the refusal

STATUS: COMPLETE. The signal is designed, the patch is written as a diff, the
tests pass (41 checks), and the three questions are answered from measurement.

## LEAD LINE

**The signal that triggers the fallback is the vendor's own refusal text,
arriving as a structured `stopReason: "error"` plus `errorMessage` on the last
assistant message, or as pi's stderr before a non-zero exit. I have NEVER seen
it on this machine. MEASURED**, four ways: all 935 dispatch logs hold only
three `[pi] exit` lines and all read `rc=0`; all 89 pi session files hold zero
`auto_retry` events; the three events sidecars hold zero typed vendor errors;
and the only vendor refusal observed today was the codex model-name rejection
in section 6, which is not a quota shape. So the matcher is INFERRED. Its
basis is pi's own error vocabulary, read from the installed code. It fails
loudly on an unknown shape: the tool reports the error as UNCLASSIFIED, names
the by-hand `quota-block` command, and refuses to guess.

## 1. Re-derived measurements (every negative in the brief, checked again)

- **`pi` has no usage, quota or balance subcommand. MEASURED** today:
  `pi --help` lists `install`, `remove`, `uninstall`, `update`, `list`,
  `config`, `auth`, and nothing else.
- **`pi auth check` returns credentials only. MEASURED**:
  `pi auth check --provider zai --json` prints
  `{"status":"ready","provider":"zai","authType":"api_key"}`. No consumption
  field exists. The brief ran the command bare; bare it refuses with
  `Auth checks require --provider <provider> or --model <model>`.
- **The dispatch logs record no token counts. MEASURED, WITH ONE CORRECTION.**
  The current default path (herdr-pi) logs only herdr JSON:
  `LJ-1.296-20260815-171417.log` holds `cli:agent:*` events, 2144 bytes, and
  no usage. But the three direct-`pi` trial logs DO record per-message usage.
  `pitest2-20260813-103928.log` carries `[usage] in=126 out=39 cacheRead=8192
  total=8357 stop=stop`. The sidecar carries
  `"usage":{...,"totalTokens":8357,"cost":{...,"total":0}`. This does not
  rescue a quota design, for three reasons. The counts are per message. They
  accumulate nowhere. And `cost.total` is identically `0`, because the vendor
  is a subscription. **No limit number exists in any artifact. MEASURED.** So
  the brief's conclusion stands, and one supporting sentence needed the
  correction above.
- **The vendor is a subscription. MEASURED**: `dev/vendors.toml`,
  `[vendors.zai]`, with the owner's comment that the clock has no basis.
- **No brief has ever used `--fallback`. MEASURED**: `git grep --fallback
  agents/` returns one hit, and it is this task's own brief quoting the
  command.
- **`scripts/dispatch_policy.py` moved DURING this task. MEASURED**: the
  sibling `[LJ-1.295]` completed its move while I worked. The file now lives
  at `scripts/dispatch/dispatch_policy.py`, and the flat import in
  `dispatch.py` (`_POLICY_DIR = str(ROOT / "scripts")`) is broken until the
  owner applies LJ-1.295's reported line. I did not fight the move. I never
  needed to edit the policy module, and my patch does not touch the import
  block, so it applies before or after LJ-1.295's owner-line change.
- **Two permitted files went unedited, by design. MEASURED need**: neither
  `dev/vendors.toml` nor `scripts/dispatch_policy.py` (now
  `scripts/dispatch/dispatch_policy.py`) requires a change for this
  fallback. The matcher carries no vendor name, the state is keyed by the
  provider string the config already holds, and the dead fallback row needs
  an owner's ruling on the codex-side model (section 7), not an invented
  field.

## 2. The signal, and where it lands

**The only honest trigger is the vendor's refusal, read from what the run
itself wrote.** Nothing else is observable (section 1). The refusal lands in
structured fields, and the design reads only those:

- **Direct `pi` harness** (through `pi_stream.py`): pi-ai's AssistantMessage
  carries `stopReason: "error"` and `errorMessage`. In `--mode json` this
  streams as a `message_end` event; the sidecar keeps it verbatim, and the
  rendered log prints `[usage] ... stop=error`. MEASURED from
  `.../dist/modes/print-mode.js` and from the sidecar samples. Note one trap
  the patch documents: the `exitCode = 1` branch in print mode is
  text-mode-only, so a json-mode refusal can exit 0 and read as a clean
  finish with an empty final message. The structured scan closes that hole.
- **`herdr-pi` harness** (the default under the pin): pi runs in a pane, and
  the dispatch log's herdr JSON names the pi session file
  (`"agent_session":{"value":"...jsonl"}`, seen in
  `LJ-1.296-20260815-171417.log`). That file is structured and holds the same
  message records. The pane text in the final-message file is NOT trusted as
  a trigger, because it holds agent prose.
- **Launch-time death**: pi prints the vendor error to stderr, which
  `pi_stream.py` merges and passes through as a plain line, and records
  `[pi] exit rc=N`. dispatch.py already prints "EXITED IMMEDIATELY"; the patch
  adds the scan there, because the orchestrator may never arm a waiter for a
  dead launch.

**The vocabulary is pi's own, copied verbatim.** The installed
`.../node_modules/@earendil-works/pi-ai/dist/utils/retry.js` ships two
classifiers. `NON_RETRYABLE_PROVIDER_LIMIT_ERROR_PATTERN` holds the quota and
billing strings: `insufficient_quota`, `quota exceeded`, `out of budget`,
`billing`, `Monthly usage limit reached`, `available balance`,
`GoUsageLimitError`, `FreeUsageLimitError`. `RETRYABLE_PROVIDER_ERROR_PATTERN`
holds the transient strings: `rate.?limit`, `429`, `overloaded`, `5xx`,
`ResourceExhausted`, and network shapes. pi retries the second class itself:
default `maxRetries ?? 3` with backoff (`core/settings-manager.js:553`). So a
TERMINAL error of either class means the vendor refused the run after pi
spent its own budget. Both classes stick a block; the kind differs; the
clearing rule is the same for both, because the probe re-tests the vendor.

**Fail-loud arrangement for the wrong guess.** A terminal error that matches
NEITHER class is reported as UNCLASSIFIED with its text and its source, and
nothing sticks. The report names the by-hand command, `quota-block`, so a
matcher miss costs one round trip, not a silent non-fire. Prose cannot fire
the matcher: the words "quota" or "429" in agent prose, with no structured
error, read as no refusal. The test pins this (section 4, check group 5).

## 3. The patch

The exact diff is `agents/tasks/LJ-1-296/lj-1.296-dispatch-patch.diff` beside
this report, and it is embedded below. Apply it inside
`.claude/skills/codex-dispatch/` with `patch -p1`. It was verified to apply
cleanly to today's file and to produce a byte-identical copy to the one the
tests run against. What it adds:

1. `QUOTA_RE` and `RATE_RE`, with the provenance comment above.
2. `QUOTA_BLOCKS_FILE = STATE / "quota-blocks.json"`, with loaders that
   REFUSE on a corrupt file (D12: an unreadable sensor never reads as empty).
3. `read_vendor_terminal_error(record)`, the structured reader for the three
   sources in section 2.
4. `classify_vendor_error(text)`, returning `quota`, `rate`, or `None`.
5. `scan_quota_refusal(task, record)`, called from EVERY return-reporting
   site: `announce()`, `cmd_wait`'s report loop, and the dead-early exit in
   `launch()`. D3's lesson, applied to reads: a scan one entry point performs
   is not a scan.
6. `check_quota(provider, allow)`, called in `launch()` beside `check_model`,
   gated to the pi harnesses, because the block is the VENDOR's and the codex
   harness bills a different vendor through its own config.
7. `quota_handoff(...)`, which prints the refusal, sticks the state, and says
   in as many words that it is NOT an automatic re-route.
8. `--allow-quota` (one launch, mirrors `--allow-model`), `quota-clear`
   (probe-gated), `quota-block` (by hand), and a `status` line for stuck
   blocks.

```diff
--- a/dispatch.py
+++ b/dispatch.py
@@ -84,6 +84,43 @@
 # the dispatcher to one vendor. The fallback literal survives ONLY for the case
 # where the policy module cannot be read at all, which the block below reports.
 DEFAULT_MODEL = "deepseek-v4-pro"
+
+# [LJ-1.296] THE QUOTA BLOCK, and why its state is a file and not the dict above.
+# BLOCKED_MODELS is date-gated and hand-edited, which fits a model the backend
+# names and unnames on its own schedule. A quota refusal differs in one way:
+# the TOOL reads it out of the run's own artifacts, so the TOOL must WRITE the
+# block at the moment it reads one (C-48: a tool that can read a condition must
+# refuse on it). An in-source dict cannot be written at runtime, so the state
+# lives beside the registry, and BLOCKED_MODELS stays what it was.
+#
+# IT NEVER EXPIRES ON ITS OWN. An expiry date would be a number nobody
+# measured, and an estimated quota is a number the project would then trust
+# (C-44). It clears only through `quota-clear`, which runs a one-line probe
+# against the vendor itself and refuses to clear while the probe fails, or
+# through `--allow-quota` for ONE launch a human has decided is safe.
+QUOTA_BLOCKS_FILE = STATE / "quota-blocks.json"
+
+# [LJ-1.296] THE REFUSAL VOCABULARY, and its provenance. No quota refusal has
+# ever been observed on this machine (MEASURED 2026-08-15: every `[pi] exit`
+# line in every dispatch log reads rc=0, and no pi session file holds one
+# auto_retry event), so both patterns are INFERRED. Their basis is pi's OWN
+# error classifier, read from the installed code and copied verbatim, not
+# imagined strings:
+#   .../node_modules/@earendil-works/pi-ai/dist/utils/retry.js
+#     NON_RETRYABLE_PROVIDER_LIMIT_ERROR_PATTERN  -> QUOTA_RE
+#     RETRYABLE_PROVIDER_ERROR_PATTERN            -> RATE_RE
+# pi retries the RATE class itself with backoff, so a TERMINAL error of either
+# class means the vendor refused the run to its face after pi's own budget was
+# spent. A terminal error matching NEITHER class is reported as UNCLASSIFIED
+# and never dropped silently: the report names `quota-block`, the by-hand way
+# to stick a block, which is the fail-loud half of an inferred matcher.
+QUOTA_RE = re.compile(
+    r"GoUsageLimitError|FreeUsageLimitError|Monthly usage limit reached"
+    r"|available balance|insufficient_quota|out of budget|quota exceeded"
+    r"|\bbilling\b", re.I)
+RATE_RE = re.compile(
+    r"overloaded|rate.?limit|too many requests|\b429\b|\b50[0234]\b|\b524\b"
+    r"|service.?unavailable|server.?error|internal.?error|ResourceExhausted", re.I)
 
 # THE HARNESS, AND ITS DEFAULT COMES FROM THE POLICY SWITCH.
 #
@@ -313,8 +350,34 @@
     tmp = REGISTRY.with_suffix(".tmp")
     tmp.write_text(json.dumps(reg, indent=2))
     tmp.replace(REGISTRY)
+
+
+def load_quota_blocks() -> dict:
+    """[LJ-1.296] The stuck vendor refusals, provider -> block record."""
+    if not QUOTA_BLOCKS_FILE.exists():
+        return {}
+    try:
+        data = json.loads(QUOTA_BLOCKS_FILE.read_text())
+    except (OSError, json.JSONDecodeError) as exc:
+        # D12 again, the registry's own law: an unreadable sensor must REFUSE,
+        # never read as empty. A corrupt block file that read as "no blocks"
+        # would relaunch onto a dead vendor, which is the silent failure this
+        # whole mechanism exists to prevent.
+        raise SystemExit(
+            f"dispatch: REFUSING. {QUOTA_BLOCKS_FILE.name} is corrupt ({exc}). "
+            f"Repair it by hand, or delete it DELIBERATELY once you have "
+            f"confirmed the vendor is not quota-blocked. Proceeding as though "
+            f"it were empty would relaunch onto a dead vendor.")
+    return data if isinstance(data, dict) else {}
+
+
+def save_quota_blocks(blocks: dict) -> None:
+    STATE.mkdir(parents=True, exist_ok=True)
+    tmp = QUOTA_BLOCKS_FILE.with_suffix(".tmp")
+    tmp.write_text(json.dumps(blocks, indent=2))
+    tmp.replace(QUOTA_BLOCKS_FILE)
 
 
 def proc_start(pid: int) -> str | None:
@@ -636,6 +699,180 @@
             f"--allow-model once a one-line `codex exec -m {model} \"say ok\"` succeeds.")
 
 
+# ----------------------------------------------------------- quota fallback [LJ-1.296]
+
+PI_SESSION_IN_LOG = re.compile(r'"agent_session":\s*\{[^}]*?"value":\s*"([^"]+\.jsonl)"')
+
+
+def _last_pi_error_text(fh) -> str | None:
+    """The errorMessage of the LAST assistant message that died, or None.
+
+    Works on both pi streams this project produces: the events sidecar
+    (`message_end` events) and the session file herdr names in its JSON
+    (`message` records). Both carry the pi-ai AssistantMessage payload, whose
+    error shape is stopReason=error plus errorMessage; verified against
+    .../pi-coding-agent/dist/modes/print-mode.js and against the message_end
+    events in the pitest sidecars. MEASURED from the code; never yet seen
+    live, because no refusal has ever occurred here.
+    """
+    last = None
+    for raw in fh:
+        try:
+            ev = json.loads(raw)
+        except (json.JSONDecodeError, ValueError):
+            continue
+        if not isinstance(ev, dict) or ev.get("type") not in ("message_end", "message"):
+            continue
+        msg = ev.get("message")
+        if not isinstance(msg, dict) or msg.get("role") != "assistant":
+            continue
+        if msg.get("stopReason") == "error":
+            last = str(msg.get("errorMessage") or "")
+    return last
+
+
+def read_vendor_terminal_error(d: dict) -> tuple[str, str] | None:
+    """(where, text) for the vendor's terminal refusal on a finished run.
+
+    Reads STRUCTURED sources only, never the agent's own prose: the events
+    sidecar (direct pi harness) and the pi session file the herdr log names
+    (herdr-pi harness, the default today). The third source, pi's own stderr
+    pass-through in the rendered log, is only read when the log also records a
+    NON-ZERO `[pi] exit rc=`, and whatever it finds still passes the
+    vocabulary below before anything sticks, so prose in a log cannot set a
+    block on its own.
+    """
+    ev_path = str(d.get("events") or "")
+    if ev_path:
+        try:
+            with open(ev_path, errors="ignore") as fh:
+                text = _last_pi_error_text(fh)
+        except OSError:
+            text = None
+        if text is not None:
+            return f"events sidecar {ev_path}", text
+    log_path = str(d.get("log") or "")
+    tail = ""
+    if log_path:
+        try:
+            body = Path(log_path).read_text(errors="ignore")
+        except OSError:
+            body = ""
+        m = PI_SESSION_IN_LOG.search(body)
+        if m:
+            sess = Path(m.group(1))
+            if sess.exists():
+                try:
+                    with sess.open(errors="ignore") as fh:
+                        text = _last_pi_error_text(fh)
+                except OSError:
+                    text = None
+                if text is not None:
+                    return f"pi session {sess}", text
+        tail = body[-2000:]
+        m2 = re.search(r"\[pi\] exit rc=(\d+)", tail)
+        if m2 and m2.group(1) != "0":
+            plain = [ln for ln in tail.splitlines()
+                     if ln.strip() and not ln.startswith(("[", "{"))]
+            if plain:
+                return f"log {log_path} (pi stderr, rc={m2.group(1)})", plain[-1]
+    return None
+
+
+def classify_vendor_error(text: str) -> str | None:
+    """"quota" (pi-ai's non-retryable class), "rate" (retryable, but this run
+    ended on it anyway, so pi's own retry budget was spent), or None."""
+    if QUOTA_RE.search(text):
+        return "quota"
+    if RATE_RE.search(text):
+        return "rate"
+    return None
+
+
+def stick_quota_block(provider: str, model: str, kind: str, evidence: str) -> None:
+    blocks = load_quota_blocks()
+    old = blocks.get(provider)
+    blocks[provider] = {
+        "kind": kind, "model": model, "evidence": evidence,
+        "set": time.strftime("%Y-%m-%d %H:%M:%S"),
+        "supersedes": (old or {}).get("set", ""),
+    }
+    save_quota_blocks(blocks)
+
+
+def quota_handoff(task: str, d: dict, kind: str, text: str, where: str) -> None:
+    """Print the refusal, stick the state, and hand the task to the orchestrator.
+
+    THIS IS A HAND-OFF AND NOT A RE-ROUTE, and the message says so in as many
+    words: dispatch.py cannot start an in-harness agent, because an in-harness
+    dispatch passes through no tool. A fallback that claimed to re-route and
+    only printed would be the escape hatch C-43 describes, so this refuses to
+    claim it.
+    """
+    provider = PI_PROVIDER
+    model = str((d or {}).get("model") or DEFAULT_MODEL)
+    brief = str((d or {}).get("brief") or "<the brief this run was launched with>")
+    print()
+    print(f"dispatch: !! {task} ENDED ON A VENDOR REFUSAL ({kind}), read from {where}:")
+    print(f"          {text[:300]}")
+    stick_quota_block(provider, model, kind, f"{task}: {where}")
+    print(f"dispatch: STUCK: provider `{provider}` is quota-blocked in "
+          f"{QUOTA_BLOCKS_FILE.name}.")
+    print(f"          Every further pi launch on `{provider}` is refused until "
+          f"`quota-clear {provider}` succeeds.")
+    print(f"dispatch: THE HAND-OFF. This is NOT an automatic re-route: no tool can start")
+    print(f"          an in-harness agent. Run the task in-harness yourself, with the brief")
+    print(f"          {brief}")
+    print(f"          and a tier line naming the head you actually start.")
+    print(f"dispatch: DD17 WARNING: under the mode in force the adversarial head is")
+    print(f"          in-harness too. If authors move in-harness, a task and its review")
+    print(f"          share a head, which the invariant forbids. The fallback row (codex)")
+    print(f"          is a way out only if its own backend accepts the model it is given;")
+    print(f"          probe it before relying on it.")
+
+
+def scan_quota_refusal(task: str, d: dict) -> None:
+    """Read one finished run's artifacts for the vendor's refusal, and act.
+
+    C-48: the condition is readable, from structured fields the run itself
+    wrote, so the tool must refuse on it instead of leaving the reader to
+    notice an empty final message. Called from EVERY return-reporting site
+    (announce, cmd_wait, launch's dead-early exit), because a scan one entry
+    point performs is not a scan; that is D3's lesson applied to reads.
+    """
+    hit = read_vendor_terminal_error(d)
+    if hit is None:
+        return
+    where, text = hit
+    kind = classify_vendor_error(text)
+    if kind is None:
+        print()
+        print(f"dispatch: !! {task} ENDED ON AN UNCLASSIFIED VENDOR ERROR, read from {where}:")
+        print(f"          {text[:300]}")
+        print(f"          The vocabulary is INFERRED (no refusal has ever been observed on")
+        print(f"          this machine), so this may be a quota shape the matcher does not")
+        print(f"          know. READ IT YOURSELF. If it is a quota refusal, stick the block")
+        print(f"          by hand, in one command:")
+        print(f"            dispatch.py quota-block {PI_PROVIDER} --kind quota "
+              f"--note '<the error text above>'")
+        return
+    quota_handoff(task, d, kind, text, where)
+
+
+def check_quota(provider: str, allow: bool) -> str | None:
+    """The launch-time refusal while a vendor's quota block sticks. [LJ-1.296]"""
+    b = load_quota_blocks().get(provider)
+    if not b or allow:
+        return None
+    return (f"provider `{provider}` is quota-blocked ({b.get('kind')}, set "
+            f"{b.get('set')}; evidence: {str(b.get('evidence'))[:160]}). The vendor "
+            f"refused a run to its face, so every pi launch on it is refused until the "
+            f"block clears. THIS IS A HAND-OFF, NOT A RE-ROUTE: dispatch.py cannot "
+            f"start an in-harness agent. Run the task in-harness yourself with its "
+            f"brief, or clear the block with `quota-clear {provider}` once its own "
+            f"probe succeeds, or pass --allow-quota for ONE launch you have decided "
+            f"is safe.")
+
+
 def clock_defects(brief: Path, case: str = "default") -> list[str]:
     """Refuse a dispatch whose HEAD contradicts the clock, whatever the brief says.
 
@@ -916,6 +1153,17 @@ def launch(task: str, brief: Path, agda: bool, sandbox: str, model: str,
            resume_id: str | None = None, note: str | None = None,
-           allow_model: bool = False, case: str = "default") -> int:
+           allow_model: bool = False, allow_quota: bool = False,
+           case: str = "default") -> int:
@@
     # D3: the model refusal lives HERE, so run, queue and resume all pass through it.
     if (why := check_model(model, allow_model)):
         print(f"dispatch: REFUSED. {why}", file=sys.stderr)
         return 1
+
+    # [LJ-1.296] Same funnel, same lesson: the quota refusal lives HERE so every
+    # path crosses it. It gates the PI harnesses only, because the block is the
+    # VENDOR's (dev/vendors.toml `pi_provider`), and the codex harness bills a
+    # different vendor through its own config.
+    if HARNESS in ("pi", "herdr-pi") and \
+            (why := check_quota(PI_PROVIDER, allow_quota)):
+        print(f"dispatch: REFUSED. {why}", file=sys.stderr)
+        return 1
 
     # NOTES PRINT ON EVERY LAUNCH PATH, and this one goes here for a reason the
@@ -1321,6 +1569,12 @@
     # D13: never report a launch as successful when the process is already gone. That is
     # the exact shape of failure mode 1 and it used to print "away" and exit 0.
     if dead_early and proc.returncode != 0:
+        # [LJ-1.296] The launch-time refusal shape: pi died before any agent
+        # prose existed, so its stderr is the vendor's own answer. Read it now,
+        # because the orchestrator may never arm a waiter for a dead launch.
+        scan_quota_refusal(task, reg.get("dispatches", {}).get(task) or {})
         print(f"dispatch: {task} EXITED IMMEDIATELY (rc {proc.returncode}). This is the "
               f"silent-death shape: read {log} for the reason.", file=sys.stderr)
         return 1
@@ announce() @@
                 rf.write(f"{stamp}  {tname}  {ok}  {d.get('log','')}\n")
     except OSError:
         pass
+    # [LJ-1.296] Outside the except on purpose: a scan the OSError swallow can
+    # eat is a scan that silently did not run.
+    for tname in sorted(done):
+        scan_quota_refusal(tname, done[tname])
@@ cmd_wait() report loop @@
         print(f"       log {d.get('log')}")
+        scan_quota_refusal(t, d)
     still = [t for t in watched if t not in done]
@@ cmd_run() @@
     if (why := check_model(a.model, a.allow_model)):
         print(f"dispatch: REFUSED. {why}", file=sys.stderr)
         return 1
+    if (why := check_quota(PI_PROVIDER, a.allow_quota)):
+        print(f"dispatch: REFUSED. {why}", file=sys.stderr)
+        return 1
@@
-    rc = launch(a.task, brief, a.agda, a.sandbox, a.model, allow_model=a.allow_model,
-                case=case_from_args(a))
+    rc = launch(a.task, brief, a.agda, a.sandbox, a.model, allow_model=a.allow_model,
+                allow_quota=a.allow_quota, case=case_from_args(a))
@@ cmd_queue(): same pre-check as cmd_run; the generated waiter script gains @@
-        f"{a.model!r}, resume_id={resume_id!r}, note={note!r}, allow_model={a.allow_model!r}, "
+        f"{a.model!r}, resume_id={resume_id!r}, note={note!r}, "
+        f"allow_model={a.allow_model!r}, allow_quota={a.allow_quota!r}, "
@@ cmd_resume() @@
     return launch(f"{a.task}-resume", Path(d.get("brief", "")), d.get("agda", False),
                   d.get("sandbox", "workspace-write"), d.get("model", DEFAULT_MODEL),
-                  resume_id=session, note=a.note, allow_model=a.allow_model)
+                  resume_id=session, note=a.note, allow_model=a.allow_model,
+                  allow_quota=a.allow_quota)
@@ cmd_status() @@
     print(f"agents live: {len(live)}")
+    for prov, b in sorted(load_quota_blocks().items()):
+        print(f"!! QUOTA BLOCK: provider `{prov}` ({b.get('kind')}), set {b.get('set')}. "
+              f"pi launches on it are REFUSED until `quota-clear {prov}` succeeds "
+              f"(evidence: {str(b.get('evidence'))[:120]})")
@@ main(): common() gains, beside --allow-model @@
+        sp.add_argument("--allow-quota", action="store_true",
+                        help="[LJ-1.296] launch ONCE despite a stuck quota block on the "
+                             "vendor, after a human decided the block is wrong. The block "
+                             "itself stays stuck; only `quota-clear` removes it, and only "
+                             "after its own probe against the vendor succeeds")
@@ resume parser gains @@
+    r.add_argument("--allow-quota", action="store_true")
@@ new subparsers, before `check` @@
+    qc = sub.add_parser("quota-clear",
+                        help="[LJ-1.296] clear a provider's quota block, but only after "
+                             "this tool's own one-line probe against that vendor succeeds; "
+                             "a probe that fails leaves the block in place")
+    qc.add_argument("provider")
+    qb = sub.add_parser("quota-block",
+                        help="[LJ-1.296] stick a quota block by hand, for a refusal the "
+                             "inferred matcher did not classify")
+    qb.add_argument("provider")
+    qb.add_argument("--kind", default="quota", choices=["quota", "rate"])
+    qb.add_argument("--model", default=None)
+    qb.add_argument("--note", required=True,
+                    help="the evidence: the error text and where it was read")
@@ the two commands, before cmd_check @@
+def cmd_quota_clear(a) -> int:
+    """Clear a quota block, gated on this tool's own probe of the vendor.
+
+    The block was SET by the vendor's refusal, so only the vendor's own
+    answer may clear it: a one-line `pi -p` against the same provider and
+    model. A clear that trusted a hunch, a date, or a message from the vendor
+    account page would be an estimated quota by another name (C-44).
+    """
+    blocks = load_quota_blocks()
+    if a.provider not in blocks:
+        print(f"dispatch: provider `{a.provider}` carries no quota block.")
+        return 0
+    model = blocks[a.provider].get("model") or DEFAULT_MODEL
+    print(f"dispatch: probing before clearing: "
+          f"pi -p --provider {a.provider} --model {model} \"say ok\"")
+    try:
+        out = subprocess.run(
+            ["pi", "-p", "--provider", a.provider, "--model", model, "say ok"],
+            capture_output=True, text=True, timeout=180,
+            stdin=subprocess.DEVNULL, cwd=str(ROOT))
+    except (OSError, subprocess.SubprocessError) as exc:
+        print(f"dispatch: REFUSED. The probe itself failed ({exc}), so the block "
+              f"stays. Nothing clears on an unreadable answer.", file=sys.stderr)
+        return 1
+    if out.returncode != 0:
+        print(f"dispatch: REFUSED. The probe exited {out.returncode}; the vendor is "
+              f"still refusing, so the block stays:", file=sys.stderr)
+        for ln in (out.stdout + out.stderr).strip().splitlines()[-3:]:
+            print(f"          {ln[:200]}", file=sys.stderr)
+        return 1
+    del blocks[a.provider]
+    save_quota_blocks(blocks)
+    print(f"dispatch: probe succeeded (rc=0); the quota block on `{a.provider}` "
+          f"is cleared.")
+    return 0
+
+
+def cmd_quota_block(a) -> int:
+    """Stick a quota block by hand: the fail-loud complement to an INFERRED
+    matcher. When a refusal arrives that the vocabulary does not know, the
+    scan reports it as UNCLASSIFIED and names this command, so a wrong guess
+    in the matcher costs one round trip, not a silent non-fire."""
+    blocks = load_quota_blocks()
+    blocks[a.provider] = {
+        "kind": a.kind, "model": a.model or DEFAULT_MODEL,
+        "evidence": a.note, "set": time.strftime("%Y-%m-%d %H:%M:%S"),
+        "manual": True,
+    }
+    save_quota_blocks(blocks)
+    print(f"dispatch: quota block stuck on `{a.provider}` by hand "
+          f"({a.kind}): {a.note[:160]}")
+    print(f"          pi launches on it are refused until `quota-clear {a.provider}` "
+          f"succeeds.")
+    return 0
@@ dispatch table @@
     return {"run": cmd_run, "queue": cmd_queue, "resume": cmd_resume,
             "status": cmd_status, "check": cmd_check, "wait": cmd_wait,
-            "gate-ready": cmd_gate_ready}[a.cmd](a)
+            "gate-ready": cmd_gate_ready, "quota-clear": cmd_quota_clear,
+            "quota-block": cmd_quota_block}[a.cmd](a)
```

The hunks above the `@@` markers without line numbers are abridged for
reading. The FILE `lj-1.296-dispatch-patch.diff` is the complete, exact,
`patch -p1`-verified diff, and it is the one to apply.

## 4. The tests

`scripts/tests/test_quota_fallback.py`, 41 checks, all passing. It pins:

1. The vocabulary: every quota string and rate string from pi-ai's own
   classifier classifies correctly, and prose ("context overflow", "tool bash
   exited 1") does not.
2. The structured reader on a synthetic events sidecar with a terminal error.
3. The herdr-pi reader: a synthetic herdr log names a synthetic session file,
   and the refusal is read from the session file.
4. The launch-time shape: pi stderr plus `[pi] exit rc=1`.
5. The false-positive guard: the word "quota" forty times in a log with rc=0,
   and a clean sidecar beside quota-heavy prose, both read as NO refusal.
6. The launch gate: silent with no file, loud with a stuck block, naming the
   hand-off and the clear command, bypassed once by `--allow-quota`, and NOT
   gating a different vendor.
7. The scan acts: banner, hand-off words "NOT an automatic re-route", state
   stuck with task-tagged evidence. An UNCLASSIFIED error is reported, names
   `quota-block`, and sticks nothing.
8. The save/load round trip.

The test's subject is the tracked copy
`agents/tasks/LJ-1-296/probe/dispatch_patched.py`, because
`.claude/skills/` is gitignored (MEASURED: `.gitignore:19`). When the
gitignored original exists, the test re-derives the copy through
`probe/apply_edits.py` and demands a byte-identical result, so the shipped
copy cannot drift from the diff. `test_dispatch_clock.py` still passes after
the sibling's move (67 checks, MEASURED today).

## 5. A. Does it interact with the pin

**The pin wins, and the fallback never touches it.** The pin
(`VERSION_IN_FORCE = "pi-subagent-mode"`, by the owner's daily word) says
which head LEADS. The block says that head's VENDOR is unavailable. Those are
different claims, and both can be true, which is the brief's own reading and
I confirm it. Nothing in the patch reads or writes the mode, the pin, or the
head tables. The mode stays `pi-subagent-mode`; its default head simply
cannot launch through this tool while the block sticks. The refusal text
tells the orchestrator to run the task in-harness with a tier line naming the
head actually started, so the record stays honest for
`check-dispatch-policy.py`. **No silent override exists. MEASURED** from the
patch: zero references to `VERSION_IN_FORCE`, `in_force`, `POLICY`, or any
table row in the added code except `PI_PROVIDER` and `DEFAULT_MODEL`, which
are data, not policy.

One consequence is worth naming. If the orchestrator runs default tasks
in-harness under a `pi-subagent-mode` pin, the working reality is
`in-harness-subagent-mode` while the switch says otherwise. The honest cure
is the owner's daily word flipping the pin, which the pin's own design
already provides. The tool's part is only to say "the vendor refused",
loudly, with evidence.

## 6. B. What happens to the adversarial row

**The invariant is the danger, and the fallback cannot save it.** Under the
pin, the adversarial head is in-harness Opus. If pi's vendor dies and default
tasks move in-harness, then a task and its DD25 review both run in-harness
Opus. The critic would be the same head as the author. DD17 forbids that,
and a fallback may not negotiate it.

What the design does: the hand-off message carries the DD17 WARNING in the
same breath as the hand-off itself (see `quota_handoff`). It says the
adversarial head is in-harness too, that authors moving in-harness breaks the
invariant, and that the fallback row is a way out only if its own backend
accepts its model.

What the design refuses to do: pick the review head itself. The standing
`fallback` row (codex on `MODEL`) is DEAD as written today, so `--fallback`
buys nothing (section 7), and a tool that silently swapped the review head
would be a rule fighting a ruling. **The ruling the owner owes the day the
quota actually dies**: either codex gets a model its backend accepts (a
`codex_model` field in the vendor row, or the owner's named model), so
reviews and stranded defaults go to codex; or reviews wait for the quota to
clear; or the owner flips the pin and accepts that reviews must then come
from a different head by name. The tool surfaces the question. It does not
answer it.

## 7. C. Is `codex` still reachable

**MEASURED 2026-08-15, and the answer refutes the brief's hypothesis in one
half and sharpens it in the other.** The probe:

```
$ codex exec --skip-git-repo-check -m glm-5.3 -s read-only "say ok"
warning: Model metadata for `glm-5.3` not found...
ERROR: {"error":{"message":"The supported API model names are deepseek-v4-pro
or deepseek-v4-flash, but you passed glm-5.3.","type":"invalid_request_error",...}}
rc=1
```

- `~/.codex/config.toml` wires exactly one provider: `deepseek`,
  `base_url = "https://api.deepseek.com/"` (config line 205-208).
- `~/.codex/models.json` contains zero occurrences of `glm` or `zai`.
  MEASURED by grep.

So `pi` and `codex` do NOT share the exhausted vendor. pi bills zai; codex
bills deepseek. A zai quota death leaves codex untouched. **The shared-quota
hypothesis is REFUTED by measurement.** But the fallback row is dead AS
WRITTEN, for a different reason: every row in the policy table reads
`MODEL = VENDOR.model`, which is `glm-5.3` under the zai vendor, and codex's
deepseek backend rejects that name instantly. The row cannot start at all.
It is not decorative through a shared quota; it is broken through a shared
model literal. `[LJ-1.288]` moved the vendor seam into `dev/vendors.toml`
and every row took `MODEL`, which was correct under deepseek and wrong the
day the vendor changed, which is today. **Fixing the row needs a ruling on
the codex-side model, and this report names the defect rather than inventing
the field.** The dispatch_policy printout confirms the row's model column:
`fallback herdr codex glm-5.3 codex` (MEASURED, run today from its new home).

## 8. Where the state lives and how it clears

- **Lives**: `.claude/skills/codex-dispatch/.state/quota-blocks.json`, beside
  the registry, keyed by PROVIDER (the quota's owner, from
  `dev/vendors.toml` `pi_provider`), with `kind`, `model`, `evidence`,
  `set` timestamp and `supersedes`. Written by the scan when it classifies a
  refusal, or by `quota-block` by hand. Shown by `status`. A corrupt file
  REFUSES every command that reads it (D12), never reads as empty.
- **Why not `BLOCKED_MODELS`**: the brief suggested it may be the right home.
  It is the right MECHANISM and the wrong STATE. It is an in-source,
  date-gated, hand-edited dict, and C-48 requires the TOOL to write the block
  at the moment it reads the condition, which an in-source dict cannot do.
  The patch reuses its funnel (a `check_*` function called in `launch()`,
  which `run`, `queue` and `resume` all cross, per D3) and its one-shot
  escape shape (`--allow-quota` mirrors `--allow-model`).
- **Clears**: `quota-clear <provider>` runs
  `pi -p --provider <p> --model <m> "say ok"` itself. rc=0 clears; anything
  else refuses and the block stays. The block NEVER expires on a date,
  because a reset date would be an estimated quota (C-44). `--allow-quota`
  launches once despite it, after a human decides the block is wrong, and
  leaves the block in place.

## 9. DD4

This task writes no mathematics, so the two-proof sharing rule lands on the
code instead: one reader, one classifier, one state file and one funnel serve
both pi harnesses, both pi-ai event shapes (`message_end` and `message`), and
both refusal classes. **Would the fallback still work if the vendor changed
again? Yes.** Nothing in the added code names zai, glm, deepseek or pi's
catalogue. The vocabulary is pi-ai's generic provider-error list. The state
is keyed by the provider string from `dev/vendors.toml`. The hand-off names
whatever head and brief the record carries. That is the same question
`dev/vendors.toml` exists to answer, and the patch answers it by never asking.

## 10. The abort criterion, answered

- THE SIGNAL EXISTS AND YOU MATCH IT: matched as far as honesty allows. The
  matcher is INFERRED from pi's own classifier, never observed live, and it
  fails loudly on unknown shapes. Tests: 41 checks, passing.
- NO REFUSAL HAS EVER BEEN SEEN: said so, in the lead line, MEASURED.
- THE FALLBACK CANNOT BE AUTOMATIC: correct, and it is a hand-off plus a loud
  refusal, dressed up as nothing. Every message that mentions the hand-off
  says "NOT a re-route" in the same breath.
- THE INVARIANT BREAKS AND CANNOT BE SAVED: it does not break BY THIS CHANGE,
  because nothing is auto-rerouted. It WOULD break if the orchestrator moved
  authors in-harness without a ruling on the review head, and section 6 names
  the ruling the owner owes for that day.

## ARCHIVE USED

- `agents/tasks/LJ-1-288/lj-1.288-report.md:96-101`: the `pi_wired = false`
  refusal, the nearest existing shape, whose pattern this design copies: name
  the condition, name the source, name the fixes, refuse rather than remind.
- `archive/dev/TASKS-archived.md:131`: T96's "priced refusal" row, taken as
  the standing precedent that a measured refusal is a deliverable, never a
  failure to hide.

## LITERATURE USED

No mathematical literature bears on a quota fallback; none was consulted.
The only external code read was the installed `pi` and `pi-ai` distribution,
cited by file throughout.
