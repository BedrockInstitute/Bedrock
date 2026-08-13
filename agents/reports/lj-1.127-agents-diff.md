# `AGENTS.md`: the diff `[LJ-1.127]` prepared, for the owner's ruling

**NOTHING IS APPLIED.** DD19 guards this file: it takes no edit without the
owner's ruling on the diff and a dated `AGENTS-diff-approved:` trailer, which
`scripts/check-agents-guard.py` refuses to go without. `AGENTS.md` on disk is
unchanged.

## Why an edit is owed at all

`AGENTS.md` line 95 states the dispatch rule as **"Codex is the default for
EVERY dispatch"**. The owner replaced that on 2026-08-13. The sentence is now
wrong in both directions: under the normal version the default is pi, and under
the override it is in-harness Opus 5. A wrong sentence in `AGENTS.md` steers
every session of every agent, which is the failure `check-agents-guard.py`'s
own docstring records from 2026-08-04.

## The size constraint, measured

`AGENTS.md` is **2,257 words** against `check-dev-docs.py`'s **2,300-word cap**,
so there are 43 words of headroom. **The replacement below is 15 words LONGER
than the row it replaces**, which takes the file to **2,272 words** and leaves
28 words of headroom. A first draft of this diff ran to 2,278 and claimed in
this paragraph that it SHRANK the file. Both figures are measured with
`len(line.split())`, and the claim is stated because the cap is close enough
that a wrong one would matter.

## The diff, one row

```diff
--- a/AGENTS.md
+++ b/AGENTS.md
@@ -95 +95 @@
-| **Dispatch, slots, briefs, audits.** **Codex is the default for EVERY dispatch** (DD17). An in-harness Opus subagent needs the owner's word for that task, which never carries forward, or a very-very-heavy judgment. The brief header carries a `tier:` line: if the justifying sentence will not write, the tier is codex | `dev/ORCHESTRATION.md` section 1 | the orchestrator, at the points it names |
+| **Dispatch, slots, briefs, audits.** **DD17 has TWO versions and ONE switch picks between them:** `scripts/dispatch_policy.py`, which prints the version in force and why. The brief's `tier:` line names the head AND the version; if the justifying sentence will not write, take the head the table gives | `scripts/dispatch_policy.py`, operated by `dev/ORCHESTRATION.md` section 1 | **PARTIAL.** `check-dispatch-policy.py` reads every brief against the switch. It CANNOT see which head actually RAN: an in-harness dispatch passes through no tool |
```

## What the new row claims, and what it deliberately does not

**It does not restate the tables.** The two head tables live in
`scripts/dispatch_policy.py` and nowhere else. `dev/ORCHESTRATION.md` section 1
and `dev/PLAN.md` DD17 point at the switch for the same reason: a table
restated in a second file is a table that will drift, and DD19 forbids a rule
that is canonical twice. `check-dispatch-policy.py` gates that: a governed
document naming the head model without pointing at the switch fails.

**It marks its enforcement PARTIAL, in the column that exists for it.** The
switch drives the dispatcher's default harness, what the checker accepts and
what the inspection command prints. It cannot force the orchestrator's choice,
because an in-harness Opus dispatch never reaches `dispatch.py`. `AGENTS.md`'s
own preamble says a row that claims more than its checker delivers turns a rule
into false safety, so the row says so.

**It moves the canonical home.** The old row named
`dev/ORCHESTRATION.md` section 1. The rule now lives in the switch, and
ORCHESTRATION operates it, so the home column names both in that order.

## If the owner approves

1. Apply the one-line change.
2. Commit with the trailer `AGENTS-diff-approved: 2026-08-13`.
3. `make check` runs `agentsguard` and `dispatchpolicy`, both of which the
   working tree passes today.
