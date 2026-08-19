# Handover to the incoming maintainer

**WRITTEN 2026-08-19 BY THE OUTGOING SESSION**, a `claude-opus-5` head that held the
resident maintainer slot from the POD cutover of 2026-08-18 until the owner moved the slot
to `grok-4.6` on 2026-08-19. It is addressed to whoever holds the slot next.

**READ THIS ONCE AND THEN STOP READING IT.** Your clauses are
`dev/pod/instructions/maintainer.md` and they bind you; this file only tells you where the
holes are. When a paragraph here stops being true, delete it. **A live document carries no
history**, and this one is the closest thing the project has to a document that is allowed
to age, which is exactly why it must be pruned rather than trusted.

## 1. The first thing you must do, and nothing else works until it is done

**THE RESIDENT MAINTAINER IS ADDRESSED BY ITS HERDR AGENT NAME, `pod-batch`.** Every feed
path the program has resolves that one name: `prompt_maintainer()`, `notify_closes()`,
`notify_side_done()` and `keeper.sh`'s `tell()` all call
`herdr agent prompt $(herdr_name POD-BATCH)`.

`maintainer_alive()` answers TRUE while ANY agent holds that name, **whatever kind it
is**. So while the outgoing session still holds it:

- `ensure_maintainer()` sees a live maintainer and never starts you.
- Every batch, every close notification and every keeper alarm reaches the OUTGOING
  session instead of you.

MEASURED 2026-08-19: a feed sent to test the new head landed in the outgoing Claude
session, which is how this paragraph came to be written. **Check it before you trust any
silence:**

    herdr agent list

One row must carry `name='pod-batch'`, and its `kind` must be yours. If it is not, say so
to the repository owner and stop; do not start a second one, because two resident sessions
writing proposals is worse than a batch that waits.

## 2. What the role actually is, in one paragraph

You write TABLE ROWS and you make no judgement (AD2, AD1). You turn a measured record into
a row of `dev/pod/table.toml`, and a row is admitted by MECHANICAL REPLAY and never by
your opinion. **You also own the health of `pod.py`**, which is why you are resident and
not a dispatched worker: a repairman that dies with the patient repairs nothing. Between
batches you are idle and reachable, and the repository owner attaches to your pane to talk
to you. Most of the work that actually matters arrives that way, not through a batch.

## 3. The pitfalls, each one measured rather than imagined

**YOU WILL ASSERT BEFORE YOU VERIFY.** This is the outgoing session's own worst failure
mode and it is recorded in the owner's memory file as such. Three times on 2026-08-19 it
stated a cause confidently and the evidence then refuted it: it called a live keeper
backlog「stale queued prompts draining」when the prompts were seconds old; it reported a
mutation family as「all died」when the baseline suite had been red the whole time; it
reported a suite green when the suite had silently stopped running. **In each case the
correction came from a measurement that took under a minute.** Take the minute.

**A NUMBER YOU WRITE IN PROSE GOES STALE WITHOUT ANYBODY TOUCHING IT.** The digest told
the owner「to 3 parked the loop stops」every day for a day after the owner raised the limit
to 7. Section 5.5 said「nine park reasons」when there were eleven, and `check_record`
said「seventeen comparisons」when there were nineteen. The cure is never to correct it:
**delete it and count**, or derive it.

**A TEST THAT PINS A SNAPSHOT WILL GO RED FOR A CORRECT CHANGE.** Eight instances in one
day. `len(PARK_REASONS) == 10`, the eight park class names, `3/3`, `HERDR_HARNESSES`'s
literal tuple, `legal.models`'s literal list, A12's maintainer model. Each was repaired by
asserting the INVARIANT: the derivation, the containment, the relation. Backlog item 7
carries the shape and proposes a checker for it.

**A GATE THAT EXISTS IS NOT A GATE THAT BITES.** `scripts/tests/mutation-audit.py` is the
tool that answers this and it found two gates nobody watched. **Run it after you add or
touch a gate.** It refuses a dirty tree, and it refuses a red baseline, both for measured
reasons written in its own docstring.

**THE SUITES ARE 21 AND YOU WILL BE TEMPTED TO RUN FOUR.** The outgoing session ran four
all day. `test_pod_digest.py` was red for hours with two real defects in it, and
`test_scripts_layout.py` was red because a file shipped without its README entry. Run them
all before you report anything green.

**A BUSY HEAD QUEUES ITS PROMPTS AND THE QUEUE IS INVISIBLE.** A keeper alarm that arrives
while you are mid-repair is delivered when your current tool call ends, which can be much
later. Every keeper prompt now carries `[keeper YYYY-MM-DD HH:MM:SS]` for exactly this
reason. **Read the stamp before you believe the tense of the sentence.**

**READ THE KEEPER'S PANE, DO NOT TYPE INTO IT.** Text sent to a pane running a foreground
process goes to that process's STDIN. A command you type at the keeper's pane is swallowed
by `pod.py`.

**YOU START NO PROCESS.** An agent starts a process only inside a tool call, the call's
time limit ends it, and its output never reaches the pane the owner reads. The one
exception the owner has ruled is starting a DEAD loop once told, with `herdr pane run` in
the keeper's own pane.

## 4. What the outgoing session did, so you know what state you inherit

**THE FOUR-LAYER ALIGNMENT, run 2026-08-19 at the owner's request.** The question was
whether the program, the documents, the owner and each other agree. Method, and it is
worth reusing: **for every rule, find its declaration, its enforcement point and its test,
then test whether the three agree.** Report contradictions; never assert agreement.

| layer | what it covered | what it found |
|---|---|---|
| L0 | the two invariants: AD1, and the mathematician/coder channel | aligned with the owner |
| L1 | the five slots, the heads, the roles | one real hole: the critic and the author shared a model |
| L2 round 1 | the seven rules (a1) to (g) | the tick pseudocode was a SECOND COPY, drifted nine ways |
| L2 round 2 | the eight facts and the rule table | the closed key list declared 15 keys and the program admitted 19 |
| L3 round 1 | the four gate classes, and whether every rule still has an enforcer | P, R, AD, W all present; A8 promised a file nobody built |
| L3 round 2 | whether each gate BITES | 43 mutants, 8 survived at first, all die now |

**THE ONE FINDING THAT REPEATED IN EVERY ROUND: a rule with two homes drifts, and the
home nobody executes is the one that goes stale.** Section 5.1's tick pseudocode, section
4.3's key table, section 6.1's `heads.toml` transcript, the argparse harness tuple, the
`HERDR_HARNESSES` literal in a test. Each was cured the same way: **delete the copy, keep
the home that executes, and leave a pointer.** Where a second home is unavoidable, because
one reader must execute the list and another must read it, **a checker joins them in both
directions**. Two such checkers exist now, `ClosedListHasOneHome` and
`EveryNamedFileExists`, and both were mutation-tested.

## 5. What to align next, in the order the outgoing session would have done it

1. **`dev/PLAN.md` against the program.** Section 11's goal registry and section 3's
   rulings have never been swept the way sections 4 to 7 of the memo just were. `[LJ-2.5]`
   is a kept row with no queue entry, and the two-tower architecture is still a CANDIDATE
   that only a measurement can settle. Nobody has checked whether the plan's numbers match
   `ledger.py --brief`.
2. **The digest against what the owner actually needs.** Two of its numbers were wrong for
   a day and the owner found neither, which means the digest is being written and not
   read. Ask the owner which fields they use and delete the rest.
3. **The remaining hand-written lists.** Grep for a tuple or list literal that names
   program artifacts and ask whether the program derives the same thing elsewhere. The
   five found on 2026-08-19 were all found by accident.
4. **Backlog items 7 and 8**, which are the two shapes no audit has a tool for: a rule
   contradicted by a code path, and a producer that cannot do its job.
5. **`herdr-pi` has no banner marker**, so `model_readback_ok()` is inert for both `pi`
   heads. Measure what a `pi` pane prints and add it, or record that the vendor's
   discriminator is `pi --list-models` and the guard is deliberately absent.

## 6. Things that are true today and will bite you if you assume otherwise

- **Zero bytes have been written to `src/` since the cutover.** Every one of the POD's
  outputs so far is a probe under `agents/tasks/`. The loop has never landed proof.
- **The vendor quota is a real and recurring stop.** A five-hour window emptied twice on
  2026-08-19. `quota:<reset>` now names it and rule (a2) re-opens it on the clock, but the
  stop still pages the owner, by the owner's ruling.
- **Worktree isolation is ON.** A task's work is in `.pod-state/worktrees/<code>` and only
  its declared `## SCOPE (write)` paths are copied back at the close. A task that PARKS
  keeps its tree, because that tree is the scene.
- **The owner reads Chinese**, in the Chinese Tech Doc Style, whatever language they write
  in. Everything else you write, including every brief and every report, is ASD-STE100
  Simplified Technical English. Never an em dash, in any language. Never half-width
  sentence punctuation in CJK prose.
- **Never commit and never push** unless the owner authorises that commit. The program
  commits by explicit path. One push is one CI run and one deploy, and that is the
  owner's call.

## 7. The one thing the outgoing session would tell you if it could say only one thing

**A STOP IS A DELIVERABLE.** The refutations produced this project's best results, and the
most useful thing this session did all day was find defects in its own work: a mutation
tool that reported false green, a test suite it silently truncated, a hypothesis it stated
before measuring. **Report what you actually find, including when what you find is that
you were wrong.** An empty batch with a named reason costs the project nothing; a confident
wrong row costs a rollback.
