# [LJ-1.303] report: slim the dispatch scripts, function unchanged

STATUS: COMPLETE. Verdict: **THE SLACK IS SMALL, and the number is 32 code lines.**
No behaviour changed in the slimming. A separate, larger finding is below: one refusal
in `dispatch.py` is **currently dead**, and it died today.

## 0. THE HEADLINE, BEFORE THE DETAIL

**Total lines: 4,379 to 4,373. Minus 6 lines, minus 0.14 per cent.**
**Code lines: 2,910 to 2,878. Minus 32 lines, minus 1.10 per cent.**

The total barely moves because the code that came out was replaced by the measurements
that justify the change, which this repository requires. **The four files are already
tight.** The brief said to say that number plainly if it is the answer, and it is.

**THE REAL FINDING IS NOT SIZE.** `dispatch.py`'s mandatory-rule-bundle refusal has
been disarmed since `[LJ-1.295]` moved `rules.py` this afternoon. MEASURED: a brief
citing ZERO mandatory rules passes `dispatch.py check` clean right now. Section 5.

## 1. LINE COUNTS, PER FILE

| file | total before/after | code before/after | comment before/after | total delta |
|---|---|---|---|---|
| `.claude/skills/codex-dispatch/dispatch.py` | 2514 / 2499 | 1634 / 1606 | 653 / 669 | **-15 (-0.60%)** |
| `scripts/dispatch/dispatch_policy.py` | 1094 / 1099 | 754 / 747 | 200 / 208 | **+5 (+0.46%)** |
| `scripts/dispatch/check-dispatch-policy.py` | 333 / 337 | 225 / 228 | 62 / 62 | **+4 (+1.20%)** |
| `scripts/tests/test_dispatch_clock.py` | 438 / 438 | 297 / 297 | 92 / 92 | **0 (0.00%)** |
| **TOTAL** | **4379 / 4373** | **2910 / 2878** | | **-6 (-0.14%)** |

A `code` line is a non-blank line that does not begin with `#`. A docstring line counts
as code, which is why `check-dispatch-policy.py` reads +3 code: its only added code is a
three-line docstring paragraph that says why a parameter now exists.

**The counts for `dispatch.py` are the SLIMMING ONLY** (section 6, Part 1). Part 2, the
defect fixes, adds 34 lines and is a separate decision.

**MEASURED, and it is the honest summary: of 2,910 code lines across four files, 32 were
removable without losing a measurement.** That is 1.1 per cent. These files are not
carrying fat. They are carrying history, and the history is the enforcement.

## 2. THE SEVEN BEHAVIOUR CHECKS

Every baseline was captured BEFORE any edit. Command outputs are in
`/private/tmp/.../scratchpad/base/` and `.../after/`.

### Check 1. `dispatch_policy.py` full output, byte-identical

    $ diff base/policy.txt after/policy.txt
    IDENTICAL

exit 0 both times, 24 lines both times.

### Check 2. The alias still renders

    $ .venv/bin/python scripts/dispatch/dispatch_policy.py deepseek-subagent-mode
    DISPATCH POLICY: `pi-subagent-mode` is IN FORCE   (NOT the switch's value)
    ...
    $ diff base/policy_alias.txt after/policy_alias.txt
    IDENTICAL

### Check 2b (ADDED, and the brief's checks 1 and 2 do not cover it)

The live config is FLAT and the switch is PINNED, so a plain run enters ONE of `render()`'s
three branches. This task hoisted three lines out of ALL THREE. A diff of the one branch
that runs would have proved almost nothing, so I built
`agents/tasks/LJ-1-303/probe-render-equivalence.py`, which loads the pre-edit module beside
the live one and compares every rendered string:

    $ .venv/bin/python agents/tasks/LJ-1-303/probe-render-equivalence.py \
          agents/tasks/LJ-1-303/probe/dispatch_policy_before.py
    IDENTICAL: 1645 rendered strings match across 5 vendor configs x 4 switch
    values x 7 render arguments.

That covers `render`, `render_vendor`, `in_force`, `auto_mode`, `head`,
`expected_tier_tokens`, `default_harness`, `clock_state`, `clock_mode` and
`next_boundary`, under the shipped config, a banded vendor, a flat vendor, an unwired
vendor and the built-in floor.

### Check 3. The clock test

    $ .venv/bin/python scripts/tests/test_dispatch_clock.py
    test_dispatch_clock: all checks passed (67)
    $ diff base/tests.txt after/tests.txt
    IDENTICAL

**I did not touch `scripts/tests/test_dispatch_clock.py`.** Section 4 says why, with the
number.

### Check 4. `check-dispatch-policy.py` over every brief

    before: dispatch policy OK: `pi-subagent-mode` in force, 601 brief(s) read,
            30 pre-epoch note(s) not judged (run with --notes to see them)   exit 0
    after:  ... 602 brief(s) read, 30 pre-epoch note(s) ...                  exit 0

**The +1 is a file THIS TASK created, not a code change.** `agents/tasks/LJ-1-303/probe-rulebundle-brief.md`
carries a `tier:` line, so `candidate_briefs()` counts it. PROVED by moving that one file
aside and re-running:

    $ diff base/checkpolicy.txt after/checkpolicy_nohold.txt
    IDENTICAL to baseline

I also re-ran the four error paths through the edited `check_briefs`, over synthetic briefs
(missing `tier:`, illegal token, missing version, adversarial mismatch). All four fire with
the same messages. Section 3 lists them.

### Check 5. `dispatch.py status` census

Compared through one harness, so the comparison is of code and not of address
(`agents/tasks/LJ-1-303/probe/run-patched.py` re-points the copy's `STATE` at the live one):

    $ diff <(mask status_orig_via_runner) <(mask status_slimmed)
    IDENTICAL

455 lines, exit 0. The mask is only `last write NNNs ago`, the live clock, which advances
between two runs. The raw CLI baseline differs from both by one line,
`agda: 1 live, one per parent, within C-12.`, because a sibling agent started an Agda
process between the two runs. MEASURED, not INFERRED: the unpatched module run at the same
instant through the same runner prints that line too.

### Check 6. `dispatch.py check` on three briefs

| brief | what it tests | before | after |
|---|---|---|---|
| `agents/tasks/LJ-1-301/LJ-1.301.md` | passes | `LJ-1.301.md is well formed for sandbox workspace-write`, exit 0 | IDENTICAL |
| `agents/tasks/LJ-1-300/LJ-1.300.md` | fails the clock guard | `tier line names head 'opus' ... that head runs IN-HARNESS (case: adversarial) ...`, exit 1 | IDENTICAL |
| `agents/tasks/LJ-1-303/probe-rulebundle-brief.md` | should fail the rule bundle | **`is well formed`, exit 0** | IDENTICAL |

`diff` reports IDENTICAL on all three.

**THE THIRD ROW IS THE FINDING.** The brief asked for a brief that fails the rule bundle.
**No such brief exists, because the refusal cannot fire.** Section 5.

### Check 7. The vendor refusals still fire

The brief said to add a temporary row to `dev/vendors.toml`. **That file is outside this
task's write scope**, and the same seam is reachable without it: `dispatch.py` reads the
vendor THROUGH `dispatch_policy`, and `require_vendor_wired()` reads the module-level
`VENDOR` at call time. `agents/tasks/LJ-1-303/probe-vendor-refusal.py` imports the policy
first, puts an unwired vendor in force from a temporary TOML, and only then imports the
dispatcher. **No row was added to `dev/vendors.toml` and none had to be removed.**

    1. IMPORT SURVIVED an unwired vendor.
       HARNESS      = 'herdr'
       POLICY_ERROR = ''
       VENDOR_ERROR starts: 'dispatch_policy: the vendor in force is `acme`, ...'
       vendor named in the error: True
       field named in the error: True
    2. STATUS STILL WORKS: rc=0, 454 line(s) printed.
       first line: Agda slots: 2/2 held by LJ-1.301, LJ-1.302
    3. LAUNCH REFUSED: rc=SystemExit(1)
       stderr: dispatch: REFUSED: dispatch_policy: the vendor in force is `acme`,
               and its row says `pi_wired = false`. ...
       the word REFUSED is present: True

    $ diff <(mask vendor_original) <(mask vendor_slimmed)
    IDENTICAL

### Check 8 (ADDED, and it is the one with real risk)

The largest slimming hunk replaces eleven lines at the foot of `cmd_wait` with one call to
`announce()`. **None of the seven checks runs that code.** `status` and `check` never enter
`cmd_wait`, and waiting on a real agent costs an agent. So I built
`agents/tasks/LJ-1-303/probe/probe-wait-tail.py`, which drives `cmd_wait` to completion
over a throwaway state directory holding one clean return and one death:

    $ diff wait_original.txt wait_slimmed.txt
    IDENTICAL

Both the stdout report (both branches, clean and death) and the durable `returns.log` lines
match. The probe touches no live state and launches nothing.

**SUMMARY: eight checks, eight identical. NO BEHAVIOUR CHANGED.**

## 3. WHAT I CHANGED, AND WHY EACH ONE IS NOT A MEASUREMENT

### `scripts/dispatch/dispatch_policy.py`, code -7

**3.1 The `fallback` row was written twice, with the same seven-line comment twice.**
`:703-715` and `:737-749`. Both modes name the same head and the same model, and the
comment recording `[LJ-1.296]`'s measurement was duplicated verbatim. Hoisted to
`FALLBACK_HEAD`, ONE object, referenced by both tables. **The comment is kept in full,
once.** DD13, from the rewrite side: written fresh today nobody would type that row twice.

Sharing one object is safe because a case row is read and never written. **MEASURED, by
enumerating every reader:** `head()`, `tier_token()`, `default_harness()`,
`expected_tier_tokens()` and `render()`; each reads or rebinds and none assigns into a
row. I recorded that measurement at the new definition.

I did NOT hoist the `default` and `adversarial` rows, though they are the same three
distinct heads permuted. `scripts/tests/test_dispatch_clock.py:174-179` asserts that pi's
default row EQUALS in-harness's adversarial row. Sharing the objects would make those two
checks tautologies. Section 7.

**3.2 The provenance block was written three times in `render()`.** `:926-928`,
`:939-941`, `:944-946`. All three branches end with the same `set` / `reason` / `revert`
lines. Hoisted below the branch, which preserves the print order exactly. The nested
`if VERSION_IN_FORCE != AUTO:` inside the `else` was also redundant, because the `else`
already means exactly that.

**3.3 The band-order walk was written twice.** `_window_lines()` and `_bands()` each
carried the same four-line "unique states in declaration order" loop. One helper,
`_states_in_order()`. A third price band now costs one place instead of two that can
disagree.

**3.4 `main()` tested `which and which != AUTO` twice in a row.** Merged into one block.

### `scripts/dispatch/check-dispatch-policy.py`, one dead line and one double walk

**3.5 A dead assignment.** `:229` computed `adversarial_ok` before the loop, and `:272`
overwrote it on every iteration before any read. Every path to the read passes the
reassignment. Removed.

**3.6 The task tree was walked twice.** `check_briefs()` called `T.candidate_briefs()`,
and `main()` called it AGAIN for the summary line. Two walks can disagree, and the number
printed would then not be the number judged. The list is now built once in `main()` and
passed in.

### `.claude/skills/codex-dispatch/dispatch.py`, code -28 (diff only, section 6)

**3.7 `announce()`'s body was written out a second time** at the foot of `cmd_wait`,
`:2158-2168`, eleven lines identical to `:1366-1376`. Replaced by `announce(done)`.
`announce()`'s own docstring records the session where the two report paths disagreed and
ten returns went unlogged, so a second copy re-opens exactly that defect.

**3.8 `already_announced()` is dead**, `:2006-2022`. Confirmed: no caller in the repository
outside archived reports and two frozen task copies. **Its measurement was NOT deleted.**
The rule it encoded (a waiter must not spend its single report on old news) is enforced by
the `not d.get("reported")` test in `cmd_wait`, and I moved the 2026-08-06 T117 measurement
onto that line, where the rule actually lives.

**3.9 A no-op branch in `cmd_status`**, `:1836-1837`: an `if` whose body is `pass`. Replaced
by the one comment line its `pass` carried.

### COMMENTS I REMOVED, with the line and why

**Two, and they are the same comment.** Everything else was moved, not removed.

| line | comment | why it carried no measurement |
|---|---|---|
| `dispatch_policy.py:706-712` | the seven-line `CODEX IS FIXED ON DEEPSEEK` block | It is the SECOND verbatim copy of `:740-746`. The measurement survives in full at the new `FALLBACK_HEAD`. Nothing was lost; one of two identical copies went. |
| `dispatch.py:1837` | `# still shown: an exited agent with no final message is the signal` | Kept, reworded, moved two lines up. It annotated a `pass`. |

**I deleted no dated line and no measured figure anywhere.** The one comment I judged
genuinely stale I CORRECTED rather than removed; see 4.2.

## 4. WHAT I MEASURED AND DID NOT CHANGE

**4.1 `scripts/tests/test_dispatch_clock.py`: measured at ZERO net saving, so untouched.**
Ten malformed-config checks repeat the prefix
`'in_force = "acme"\n[vendors.acme]\nmodel = "m"\npi_provider = "a"\n'`. A `cfg(*extra)`
helper is the obvious cure and it is what the brief points at. I costed it: **it saves 5
lines and costs a 6-line helper. Net +1.** It also removes the explicitness that makes each
check show the whole config it feeds. The brief says not to manufacture a saving, so I did
not. **0 lines changed, 67 checks still pass.**

**4.2 A MEASUREMENT THAT HAS EXPIRED, at `dispatch_policy.py:470`.** The comment reads
`MEASURED 2026-08-15: no file outside this one reads it`, about `PEAK_WINDOWS`. **That
reading is now FALSE.** `scripts/tests/test_dispatch_clock.py:319` and `:324` both read
`P.PEAK_WINDOWS`, added the same day. I did not delete the line. I **attributed the original
reading to `[LJ-1.288]`, kept its date, and added the re-measurement underneath**, so the
next reader does not retire the name believing it free. Retiring it now costs those two
checks.

**4.3 No vendor handling was stranded by `[LJ-1.288]`.** The brief asked for branches that
cannot be reached now that the vendor config exists. I looked and found NONE in the policy.
`BUILTIN_VENDOR` is reached whenever the config is absent, and
`scripts/tests/test_dispatch_clock.py:287-293` pins that path. `dispatch.py`'s
`DEFAULT_MODEL` and `PI_PROVIDER` literals are reached only when the policy module will not
import at all, which the code reports rather than hides. MEASURED, not INFERRED: the
render-equivalence probe exercises the absent-config path and it answers.

**4.4 The bootstrap block is duplicated across 25 scripts, not 2.**
`dispatch_policy.py:146-153` and `check-dispatch-policy.py:71-78` carry the same eight-line
`repo_root.py` walk. So do 23 other files under `scripts/`, MEASURED by
`grep -rln "no repo_root.py above" scripts/`. Collapsing it is a repo-wide change touching
`scripts/gate/` and `scripts/measure/`, which are outside this task's write scope, and it is
self-referential: the block is what makes an import possible. **NOT DONE, and it is the
single largest duplication in the writable files: about 190 lines repo-wide.** It wants its
own task.

## 5. THE FINDING THAT MATTERS MORE THAN THE LINE COUNT

**`dispatch.py`'s mandatory-rule-bundle refusal is DEAD, and it died today.**

`dispatch.py:2389` reads:

    rules_py = ROOT / "scripts" / "rules.py"
    if not rules_py.exists():
        return []

`scripts/rules.py` **does not exist.** `[LJ-1.295]` moved it to `scripts/dispatch/rules.py`
this afternoon. MEASURED:

    $ ls scripts/rules.py
    ls: scripts/rules.py: No such file or directory
    $ ls -la scripts/dispatch/rules.py
    -rw-r--r--@ 1 alsg staff 8173 15 Aug 17:25 scripts/dispatch/rules.py

So the guard returns NO DEFECTS for every brief. **MEASURED end to end**, with a brief
written to cite zero mandatory rules:

    $ .venv/bin/python .claude/skills/codex-dispatch/dispatch.py check \
          agents/tasks/LJ-1-303/probe-rulebundle-brief.md
    dispatch: probe-rulebundle-brief.md is well formed for sandbox workspace-write
    exit=0

**This is C-40's shape inside the enforcement itself, and this file's own founding lesson:
a checker that reads nothing prints green.** The docstring of `rule_bundle_defects` says
the refusal exists because "the orchestrator is precisely the component that drifted for
five days while an entire imported playbook sat uncited in 102 of 112 briefs". It has been
off since about 17:25 today.

**WHAT IT ALREADY LET THROUGH. MEASURED over the eight most recent task briefs**, with the
refusal re-armed:

| brief | verdict with the gate live |
|---|---|
| LJ-1.295, LJ-1.296, LJ-1.297, LJ-1.298, LJ-1.299, LJ-1.301, LJ-1.302 | clean |
| **LJ-1.300** | **REFUSED: does not cite 1 mandatory rule: P-l** |
| **LJ-1.303 (this task's own brief)** | **REFUSED: does not cite 2 mandatory rules: D-10, P-l** |

Two of nine went out short. This brief is one of them. C-44 asked me to re-derive every
figure in it; this is the figure it did not carry.

The fix is one path and one guard, in section 6 Part 2. **The guard is the real hazard, not
the path**: a missing rule table now REPORTS instead of returning "no defects".

**Three further defects, all measured, all in Part 2.**

**5.1 A missing `f` prefix makes a refusal branch unreachable.** `dispatch.py:1138`:

    "  if herdr agent get {hname} 2>/dev/null | grep -q '\"agent_status\":\"blocked\"'; then\n"

That literal has no `f`, so the driver runs `herdr agent get {hname}` verbatim, which cannot
resolve, so `grep -q` never matches and the whole blocked-detection branch is dead. A pause
for approval is then filed as a not-stopped run for the full ten-iteration retry loop.
MEASURED with `ast`: **it is the ONLY plain string literal in the file carrying a
placeholder**, out of every string in 2,514 lines. This is `[LJ-1.205]`'s owner ruling of
2026-08-14 half-landed.

**5.2 Five refusal messages name a path that does not exist.** `:140`, `:708`, `:804`,
`:836` and the `--harness` help at `:2443` all tell the reader to run
`python3 scripts/dispatch_policy.py`. `[LJ-1.295]` moved it to `scripts/dispatch/`. A
refusal whose instruction fails is a refusal a reader cannot act on. `:2406` names
`scripts/rules.py` the same way.

**5.3 The stall detector's quiet-deliverable half is dead again**, `dispatch.py:1717-1718`.
It derives the report path from `_build/` only. The reports moved into
`agents/tasks/<CODE>/` on 2026-08-14. MEASURED: `_build/` holds **no** `*report*.md` at all,
while `agents/tasks/LJ-1-301/lj-1.301-report.md` exists. **This is the same defect
`[LJ-1.127]` recorded at this exact site**, one home later: that entry says the retired
`L3.32` shape was the only one tried, so the detector was dead for the whole live series.
It was fixed by adding the live shape under the OLD directory, and the directory then moved.

## 6. THE DIFF FOR `dispatch.py`

`.claude/skills/codex-dispatch/dispatch.py` is untracked and outside my write scope, so
**both diffs are given here and neither was applied.** Both were tested against a patched
copy at `agents/tasks/LJ-1-303/probe/dispatch_after.py` (Part 1) and
`.../dispatch_fixed.py` (Part 1 plus Part 2), driven through
`agents/tasks/LJ-1-303/probe/run-patched.py`, which re-points the copy's `STATE` at the
live `.state` so the census is comparable.

### PART 1: SLIMMING ONLY. Function unchanged, proved by checks 5, 6, 7 and 8.

2514 to 2499 lines. Code 1634 to 1606, minus 28.

```diff
--- a/.claude/skills/codex-dispatch/dispatch.py
+++ b/.claude/skills/codex-dispatch/dispatch.py
@@ -1833,8 +1833,8 @@
     items = sorted(reg.get("dispatches", {}).items())
     for t, d in items:
         is_live = rec_alive(d)
-        if not is_live and not a.all and not final_is_clean(d.get("final", "")):
-            pass  # still shown: an exited agent with no final message is the signal
+        # Every record prints, live or not: an exited agent with no final message IS
+        # the signal this census exists for.
         state = "RUNNING" if is_live else "exited "
         log = Path(d.get("log", ""))
         age = ""
@@ -2001,25 +2001,6 @@
 # What catches it instead, and did: the durable returns.log, and `status`'s
 # loud NO WAITER IS ARMED banner. Detection after the fact plus a cheap recovery
 # beat a detector that fires on the wrong cases.
-
-
-def already_announced() -> set[str]:
-    """Task names the durable log has already reported.
-
-    MEASURED DEFECT, 2026-08-06: a freshly armed waiter re-announced T117, a
-    return that had been audited half an hour earlier, treated that as its one
-    report, and exited. The live agent it was armed for was left unwatched.
-    A waiter must not spend its single report on old news.
-    """
-    log = STATE / "returns.log"
-    if not log.exists():
-        return set()
-    out = set()
-    for line in log.read_text().splitlines():
-        parts = line.split()
-        if len(parts) >= 3:
-            out.add(parts[2])
-    return out
 
 
 WAITER_PID = STATE / "waiter.pid"
@@ -2130,6 +2111,15 @@
             # D3 (T73): adopting only LIVE records missed an agent that was dispatched after
             # this waiter began and died inside one 15 s tick: never watched, never
             # announced, never flagged. Adopt any unreported record we have not seen.
+            #
+            # `reported` IS WHAT KEEPS OLD NEWS OUT, and that rule is measured.
+            # MEASURED DEFECT, 2026-08-06: a freshly armed waiter re-announced T117,
+            # a return audited half an hour earlier, treated that as its one report
+            # and exited, leaving the live agent it was armed for unwatched. A
+            # waiter must not spend its single report on old news. A second reader
+            # of returns.log, `already_announced()`, was written for the same rule
+            # and had NO CALLER, so it enforced nothing; [LJ-1.303] removed it
+            # 2026-08-15 and the rule lives on this line.
             if t not in watched and t not in done and not d.get("reported"):
                 watched[t] = d
                 print(f"dispatch: also watching {t}, dispatched after this wait began")
@@ -2155,17 +2145,12 @@
     # reports: it marks `reported` and the message reaches no one. T90's return was lost that
     # way. The waiter cannot know where its stdout goes, so it also writes every return to a
     # durable log; a lost notification is then recoverable instead of gone.
-    stamp = time.strftime("%Y-%m-%d %H:%M:%S")
-    try:
-        LOGS.mkdir(parents=True, exist_ok=True)
-        with open(STATE / "returns.log", "a") as rf:
-            for tname in sorted(done):
-                d = done[tname]
-                final = Path(d.get("final", ""))
-                ok = "clean" if final_is_clean(final) else "NO-FINAL-MESSAGE"
-                rf.write(f"{stamp}  {tname}  {ok}  {d.get('log','')}\n")
-    except OSError:
-        pass
+    #
+    # ONE WRITER, NOT TWO. This was `announce()`'s body written out a second time,
+    # line for line. `announce()`'s own docstring records the session where the two
+    # report paths disagreed and ten returns went unlogged, which is the defect a
+    # second copy re-opens. [LJ-1.303], 2026-08-15.
+    announce(done)
     print(f"dispatch: {len(done)} agent(s) RETURNED after "
           f"{int(time.time() - start)}s: {', '.join(sorted(done))}")
     for t, d in sorted(done.items()):
```

**The `stamp` local is removed with the block. VERIFIED with `ast`: `cmd_wait` no longer
references it anywhere.**

### PART 2: THE DEFECTS. Each one CHANGES behaviour, on purpose.

**Apply this separately and knowingly.** Part 2 re-arms a refusal that is currently dead,
so two recent briefs stop passing. That is the point.

```diff
--- a/.claude/skills/codex-dispatch/dispatch.py
+++ b/.claude/skills/codex-dispatch/dispatch.py
@@ -104,7 +104,7 @@
 #
-# THE DEFAULT IS NOT A CONSTANT HERE ANY MORE. `scripts/dispatch_policy.py`
+# THE DEFAULT IS NOT A CONSTANT HERE ANY MORE. `scripts/dispatch/dispatch_policy.py`
 # holds the one switch that selects the dispatch policy version, and the
@@ -137,7 +137,7 @@
 except Exception as _exc:                       # pragma: no cover
     POLICY = None
     HARNESS = "herdr"
-    POLICY_ERROR = (f"scripts/dispatch_policy.py could not be read ({_exc}); "
+    POLICY_ERROR = (f"scripts/dispatch/dispatch_policy.py could not be read ({_exc}); "
                     f"the default harness fell back to {HARNESS!r}")
@@ -1135,7 +1135,13 @@
                 "&& { STOPPED=1; break; }\n"
                 # And say WHICH not-stopped it is, so a pause for approval is
                 # never filed as a death. The pane stays open either way.
-                "  if herdr agent get {hname} 2>/dev/null | grep -q '\"agent_status\":\"blocked\"'; then\n"
+                # THE `f` PREFIX IS LOAD-BEARING AND IT WAS MISSING. Without it
+                # the driver ran `herdr agent get {hname}` literally, which
+                # cannot resolve, so `grep -q` never matched and this whole
+                # blocked-detection branch was unreachable. A pause for approval
+                # was then filed as a not-stopped run for the full retry loop.
+                # MEASURED 2026-08-15 by `[LJ-1.303]`, with `ast`: it was the
+                # ONLY plain string literal in this file carrying a placeholder.
+                f"  if herdr agent get {hname} 2>/dev/null | grep -q '\"agent_status\":\"blocked\"'; then\n"
                 "    echo \"HERDR agent is BLOCKED: it is waiting for input.\"\n"
@@ -705,7 +705,7 @@
         return [f"tier line names head `{token}`, which is not the head for ANY case under "
                 f"`{version}`, the mode in force right now. Under it: {want}. Run "
-                f"`python3 scripts/dispatch_policy.py` and read the clock line."]
+                f"`python3 scripts/dispatch/dispatch_policy.py` and read the clock line."]
@@ -801,8 +801,8 @@
         defects.append("brief has no `tier:` line. The tier line names the head, the mode "
                        "and the version, so an audit can trace the choice. The head for "
-                       "each case lives in scripts/dispatch_policy.py; a head other than "
-                       "the table's must name why, and if the sentence will not write, "
+                       "each case lives in scripts/dispatch/dispatch_policy.py; a head other "
+                       "than the table's must name why, and if the sentence will not write, "
                        "take the head the table gives")
@@ -833,7 +833,8 @@
                 defects.append(
                     f"brief's tier line names mode `{named[0]}` (canonically `{got}`) but "
-                    f"`{want}` is IN FORCE right now. Run `python3 scripts/dispatch_policy.py` "
+                    f"`{want}` is IN FORCE right now. Run "
+                    f"`python3 scripts/dispatch/dispatch_policy.py` "
                     f"and read the clock line. Under `{want}` the default head is "
@@ -1714,7 +1714,14 @@
         # of this detector was dead for every task since 2026-08-09. Try the
         # live shape first.
-        for cand in (ROOT / "_build" / f"{task.lower()}-report.md",
+        # [LJ-1.303] 2026-08-15: THE SAME DEFECT, ONE HOME LATER. The reports
+        # moved out of `_build/` into `agents/tasks/<CODE>/` on 2026-08-14, and
+        # this derivation still looked only in `_build/`. MEASURED: `_build/`
+        # holds NO `*report*.md` at all today, so the quiet-deliverable half was
+        # dead for every live task, exactly as [LJ-1.127] found it dead for the
+        # retired series. The task directory is tried FIRST, and the two old
+        # shapes are kept because an old record still names them.
+        for cand in (ROOT / "agents" / "tasks" / task.upper().replace(".", "-")
+                     / f"{task.lower()}-report.md",
+                     ROOT / "_build" / f"{task.lower()}-report.md",
                      ROOT / "_build" / f"l3.32-{task.lower()}-report.md"):
@@ -2386,8 +2386,20 @@
     text = brief.read_text(encoding="utf-8")
-    rules_py = ROOT / "scripts" / "rules.py"
-    if not rules_py.exists():
-        return []
+    # THE PATH MOVED AND THIS REFUSAL WENT SILENT. `[LJ-1.295]` moved `rules.py`
+    # into `scripts/dispatch/` on 2026-08-15. This line still named
+    # `scripts/rules.py`, and the `exists()` guard below then returned NO
+    # DEFECTS for every brief, so the mandatory-bundle refusal was disarmed the
+    # moment the file moved. MEASURED 2026-08-15 by `[LJ-1.303]`: a brief citing
+    # ZERO mandatory rules passed `dispatch.py check` clean.
+    #
+    # THE GUARD IS THE HAZARD, not the path. A missing checker that returns
+    # "no defects" is C-40's shape and this file's own founding lesson. So the
+    # absence is now REPORTED instead of waved through.
+    rules_py = ROOT / "scripts" / "dispatch" / "rules.py"
+    if not rules_py.exists():
+        return [f"the rule table is missing: {rules_py} does not exist, so the "
+                f"mandatory-bundle refusal cannot run. It was disarmed exactly "
+                f"this way once, when `[LJ-1.295]` moved the file and this line "
+                f"kept the old path. Restore it or fix this path; do not "
+                f"dispatch on an unchecked bundle."]
@@ -2403,7 +2415,7 @@
     return [f"brief is kind `{kind}` (derived from its write scope) and does "
             f"not cite {len(missing)} mandatory rule(s): {', '.join(missing)}. "
-            f"Run `python3 scripts/rules.py --for {kind}` and paste the bundle "
+            f"Run `python3 scripts/dispatch/rules.py --for {kind}` and paste the bundle "
             f"into SCOPE (read). This is a refusal, not a reminder: the "
```

**Part 2's measured effect**, driven through the same runner:

- `status`: IDENTICAL to Part 1. Both live agents are recent, so no stall warning fires
  either way; the fix re-arms the detector without changing today's census.
- `check LJ-1.301`: IDENTICAL, still clean.
- `check LJ-1.300`: now ALSO reports `does not cite 1 mandatory rule(s): P-l`.
- `check probe-rulebundle-brief.md`: now REFUSED, `does not cite 5 mandatory rule(s):
  D-10, C-22, P-l, D-26, C-42`, exit 1. It was `well formed`, exit 0.

## 7. WOULD CHANGE, DID NOT, BECAUSE IT TOUCHES AN INTERFACE OR A CHECK

**7.1 Hoist the `default` and `adversarial` rows too.** There are only THREE distinct heads
in `POLICY`, and the two modes are permutations of them, which
`scripts/tests/test_dispatch_clock.py:174-179` asserts outright. Hoisting all three would
save about 20 more lines and make DD17's invariant STRUCTURAL rather than checked. **The
cost: those two checks become tautologies.** The test's own comment says it "CONFIRMS it
rather than assuming it, because the clock makes the swap load-bearing twice a day".
Structural impossibility is stronger than a check, but hollowing a check that records why
it exists is your call, not mine. NOT DONE.

**7.2 `cmd_run` pre-checks what `launch()` checks immediately afterwards**, `:1412-1418`,
seven lines. `launch()` calls `check_model` and `launch_defects` itself, with identical
messages. **`cmd_queue`'s copy is NOT redundant** and must stay: its launch happens later
in a detached process whose log nobody reads, which `D9` records at that line. Removing
cmd_run's copy is safe today because `BLOCKED_MODELS` is empty, but it reorders one edge
case: with an unwired vendor AND a defective brief, the vendor refusal would print instead
of the defect list. **7 lines, one reordered edge case. Your call.** NOT DONE.

**7.3 `BLOCKED_MODELS` is empty, so `check_model()` always returns `None`.** The date-gated
blocklist, its comment, the function and the `--allow-model` flag total about 35 lines and
three call sites, and none of it can fire. **This is the single largest removable block in
`dispatch.py`.** I did not touch it and I do not recommend it: **it is a REFUSAL mechanism,
and C-43 says a slimming that removes a refusal is the shape a wrong choice hides in.** It
cost 35 lines and it has fired historically. NOT DONE, reported for completeness.

**7.4 The two herdr driver scripts share a wait-and-retry shape.** The fresh driver is about
152 lines and the resume driver about 40, and the resume driver repeats `agent get`,
`agent prompt`, `wait --until working` and the `STOPPED` loop. About 12 lines are genuinely
shareable. **I did not touch it.** That f-string is the single most dangerous code path in
the file: its comments record eight separately measured failures, including two that killed
live agents. Twelve lines is not worth restructuring it. NOT DONE.

**7.5 The 25-file bootstrap block**, section 4.4. Repo-wide, outside scope, wants its own
task. NOT DONE.

## 8. DD4

**One line, as asked.** The slimmed files survive a third dispatch mode and a third vendor,
and they survive them BETTER than before: `POLICY` and `CLOCK_STATES` are still plain dicts
keyed by name, a third mode is one `POLICY` entry that can now REFERENCE `FALLBACK_HEAD`
instead of copying it, a third price band is one `CLOCK_STATES` row and now ONE band-order
walk instead of two that can disagree, and a third vendor is still one edit to `in_force` in
`dev/vendors.toml` because no vendor literal was added anywhere.

## 9. WHAT I WROTE

Write territory only. Nothing committed, nothing pushed, no `dev/vendors.toml` edit, no
Agda run.

- `agents/tasks/LJ-1-303/LJ-1.303.md`, the brief, written first.
- `agents/tasks/LJ-1-303/lj-1.303-report.md`, this file.
- `scripts/dispatch/dispatch_policy.py`, `scripts/dispatch/check-dispatch-policy.py`, edited.
- `agents/tasks/LJ-1-303/probe-render-equivalence.py`, the 1,645-string branch proof.
- `agents/tasks/LJ-1-303/probe-vendor-refusal.py`, check 7 without touching the config.
- `agents/tasks/LJ-1-303/probe-rulebundle-brief.md`, the brief that proves the dead refusal.
- `agents/tasks/LJ-1-303/probe/dispatch_after.py`, Part 1 applied and tested.
- `agents/tasks/LJ-1-303/probe/dispatch_fixed.py`, Part 1 plus Part 2, applied and tested.
- `agents/tasks/LJ-1-303/probe/run-patched.py`, the runner that re-points `STATE`.
- `agents/tasks/LJ-1-303/probe/probe-wait-tail.py`, check 8.
- `agents/tasks/LJ-1-303/probe/dispatch_policy_before.py`, `repo_root.py`, the pre-edit
  copies the equivalence probe reads.

The probes are tracked and stay, as D-1 requires. `scripts/tests/test_dispatch_clock.py` is
UNCHANGED.

## ARCHIVE USED

- `agents/tasks/LJ-1-288/lj-1.288-report.md:256`, "The policy file holds zero vendor
  literals outside `BUILTIN_VENDOR`". TAKEN: it told me where to look for stranded vendor
  handling, and I re-derived the claim rather than believing it. It still holds, so the
  brief's "branches that cannot be reached now that the vendor config exists" found NOTHING.
  That is a negative and it is MEASURED, by the render-equivalence probe exercising the
  absent-config path.
- `agents/tasks/LJ-1-285/lj-1.285-report.md:28`, "Over the 189 frozen occurrences of
  `deepseek-subagent-mode` under `agents/`". TAKEN: it is why I did not go near the
  `ALIASES` block or `VERSION_RE`, and why check 2 re-proves the alias renders after my
  edits.
- `archive/dev/TASKS-archived.md:93`,
  `| L3.32-T58 | Adversarial review of the dispatch wrapper | COMPLETE (18 defects) |`.
  TAKEN as SHAPE and never as a claim: an adversarial review of this same wrapper once found
  18 defects with reproductions, which is why every refusal in `dispatch.py` carries its
  measurement, and why I removed none of them and moved two.

## LITERATURE USED

**NONE, and the brief says so itself: no mathematical literature bears on code size.** I
read `dev/literature/BIBLIOGRAPHY.md`'s subject matter is the orthodox L construction,
condensation and Devlin's errata. WHY NOT: this task writes no mathematics, states no
theorem and touches no master. Nothing in `dev/literature/` bears on a Python dispatcher.
