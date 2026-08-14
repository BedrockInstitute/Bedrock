# ORCHESTRATION: the orchestrator's operating rules

How work is dispatched, audited and landed. Developer doc, English only, not
translated. **This file is canonical for everything on it.** It exists because
these rules used to live only in the orchestrator's session memory, where the
owner could neither read nor amend them, and where their execution depended on
one party remembering.

**Enforcement.** Rules here are enforced by the orchestrator at named points,
listed per rule. A rule with no enforcement point is a wish, not a rule: if you
add one here, name where it fires.

## 1. Who does the work

**THE POLICY IS ONE SWITCH, AND IT LIVES IN `scripts/dispatch_policy.py`.** That
module holds the two versions of DD17, the head for each case, the date the
current version was set, the reason, and the condition that reverts it. **This
section does NOT restate the tables**, because a table restated in a second file
is a table that will drift, and DD19 forbids a rule that is canonical twice.

**Read the policy in force with one command:**

```sh
python3 scripts/dispatch_policy.py
```

It prints the version, the full table, the reason and the revert condition.
Nobody reads code to answer "which head runs this task".

**TWO VERSIONS SINCE 2026-08-13, and exactly one is in force.**

- The **normal** version and the **override** version each name a head per
  case, **and THIS FILE NAMES NEITHER.** `scripts/dispatch_policy.py` is the one
  home; run it. **A head restated here is canonical twice, which DD19 forbids,
  and it is how the old fixed-tier text drifted.** The normal version's default
  changed once already, and `[LJ-1.126]` made that possible on 2026-08-13 by
  landing
  streaming and resume.
- One version is TEMPORARY and its reason is QUOTA, never quality.
  **It is TEMPORARY and its reason is QUOTA, never quality.** The owner has most
  of the week's allowance left, and `[LJ-1.121]` measured pi's return quality as
  fully acceptable. The owner cancels it by word, and the state to return to is
  the normal version.

**THE INVARIANT UNDER BOTH VERSIONS: the critic is never the same head as the
author.** That is why the two tables swap the default row and the adversarial
row. `.claude/skills/codex-dispatch/SKILL.md` states the same rule.

**THE EMERGENCY TIER SITS OUTSIDE BOTH TABLES.** DD17's Fable 5 escalation is
unchanged and it is never a default: both its conditions bind and the brief
names its trigger.

**Say WHY in the brief, not merely WHICH.** The head that the version in force
gives for the case needs no justification. Any other head must name why, and
**if that sentence will not write, take the head the table gives.**

*Enforcement, and it is honest about its own reach.* The brief header carries a
`tier:` line before dispatch, and it names the version it was chosen under:
`tier: opus (override)`. `scripts/check-dispatch-policy.py` reads every brief
against the switch. **The switch cannot force the choice**, because an
in-harness Opus dispatch never passes through
`.claude/skills/codex-dispatch/dispatch.py`. What the switch DOES drive is the
default harness that dispatcher picks, what the checker accepts, and what the
inspection command prints. **So a wrong head is detectable by an audit and is
not impossible.** Anything stronger would be false safety.

### 1.1 A negative return is adversarially reviewed (PLAN DD25)

**Ruled by the owner 2026-08-10.** When a return's headline verdict is
negative, dispatch a review at maximum effort to attack that return. Do it
**before** auditing the return and before acting on it. Then read the two
together.

**THE HEAD FOLLOWS THE SWITCH, and the mechanism does not.** DD25 says a
negative return is reviewed; `scripts/dispatch_policy.py` says by whom. Under
each version the critic is whichever head the switch's adversarial row gives.
**The rule that survives both is that the critic is never the author**, so
a return the review's own head produced goes to the other head.

**The trigger.** A refusal, a NO-GO, a RED gate, a stop taken as the
deliverable, a refutation of the brief's premise, or a landed result that
misses its band floor. **If the verdict line would disappoint the person who
wrote the brief, it is negative.**

**What the reviewer attacks is the NEGATIVE, not the task.** Not a re-run and
not a second attempt. Four questions: is the refusal correct on its own
numbers; is the measurement sound; did the BRIEF cause the outcome; is there a
cure the return missed. **A review that agrees is a real result.**

**Then both are read together.** Audit the codex return and the Opus review as
one pair, and report both to the owner, including where they disagree. Neither
is accepted alone.

**Write DD4, ARCHIVE and LITERATURE into the prompt by hand WHEN THE HEAD IS
IN-HARNESS.** An in-harness dispatch never passes through
`.claude/skills/codex-dispatch/dispatch.py`, so those three refusals do not
fire. `[LJ-1.11]` went out short two mandatory rules through exactly this gap.
**A pi or codex review goes through the dispatcher and the refusals DO fire**,
so the hand-application follows the head rather than the rule. Check which head
the version in force gives before you decide.

**This does not contradict DD17's "a RED is never a trigger".** That clause
forbids re-dispatching the TASK on a RED and it still binds. This dispatches a
REVIEW of the RED, which is the opposite move.

*Why, from measurement.* Four blocks refused on measurement in `[LJ-0.4]` and
the orchestrator accepted all four. `[LJ-0.8]` then found a propagated sign
error standing in five places and a refusal blamed on the wrong party. **A
negative return closes a line of work, so a wrong one is the most expensive
kind there is, and it is the kind nobody re-checks.**

*Enforcement:* the audit, and the PLAN section 11 row for a negative return
names its review's code. **No machine enforces the trigger**, because reading
a verdict as negative is a judgment. The honest enforcement is that the row is
empty and visible.

## 2. Slots

Concurrency and heap ceilings are LESSONS C-12: agent Agda runs at
`GHCRTS=-M8g` with at most four concurrent, or `-M12g` with at most two; the
orchestrator's own runs at `-M16g`; one Agda process per agent, always. Agents
that run no Agda do not consume a slot.

**An idle slot is a defect** (PLAN DD17). At every return, before writing the
report: name what is unblocked, name what blocks the rest, and dispatch into
the free slots. Blocked means waiting on an owner ruling, on a sibling's write
territory, on a measurement that would make the work fundable, or on the
ceilings above. Auditing a return is not a reason to idle.

**The emergency tier belongs to PLAN DD17's standing loop, and this section
does not restate it.** The short form: a codex return that does not do its
task well, AT a critical breakthrough, may be re-dispatched to Fable 5 at
maximum effort. Both conditions bind. A stop, a refutation or a RED is a good
return and never a trigger. Read DD17 before using it; the ruling names what
must be recorded.

*Enforcement:* the return-handling checklist in section 6.

### 2.1 A quiet machine is the ORCHESTRATOR's to confirm, never the agent's

**Never write "confirm you are alone before you measure" into a brief.** A
dispatched agent cannot do it. Inside the codex sandbox `os.kill` returns
EPERM for any pid outside the agent's view and `ps` is blocked, so the
registry's liveness check reads a long-dead agent as RUNNING and cannot be
cleared from there.

**Measured, `[LJ-0.5]` 2026-08-10.** The brief ordered exactly that check. The
agent found a stale RUNNING record for `[T77]`, whose log ended on 2026-08-05,
fell back to `lsof` as ground truth, proved the pid gone, and measured anyway
with the reasoning written out. That was the right call and it was not the
call the brief asked for. **A weaker agent stops forever or skips the check
in silence, and both are worse than the truth.**

**So the orchestrator confirms quiet from its own side, where the registry is
truthful, and the brief says so:** "I have confirmed no sibling is live. If
you see evidence otherwise, report it and stop." That asks for an observation
the agent CAN make instead of a verdict it cannot reach.

**This matters because timing tasks recur.** DD24 wants the baseline
re-measured after every compression block, so `[LJ-0.5]` is a standing task
and this trap is standing with it. A contended cold gate measured 150.09 s
against 133.69 s quiet, so the check is worth having; it just belongs on the
other side.

*Enforcement:* brief review, at the point a brief orders a measurement.

## 3. The brief

Every brief is pinned in `agents/tasks/<TASK>/` before dispatch, so it survives
a reboot and the owner can read what was actually asked. **The brief, the report
and every probe of one task share ONE directory** (owner's ruling 2026-08-13,
built by `[LJ-1.142]`); `<TASK>` is the task code with `.` written `-`, in
capitals, because that directory is an Agda module name component. A brief
carries:

- **`tier:`** (section 1) and a one-line GOAL.
- **CWD**, and **SCOPE (write)** naming every file the agent may write.
  Territories must be disjoint across concurrent agents, and the brief names
  the files siblings own so the agent knows what not to touch.
- **SCOPE (read), in order**, with the load-bearing documents first. This is
  how the law book actually reaches an agent: `dev/LESSONS.md` binds, and the
  brief must say so and name the hot entries.
- **CONSTRAINTS**: the heap cap, one Agda process, no git, never
  `src/Everything.lagda.md`, never `.claude/`, the stop-line, and the wall
  protocol.
- **RETURN**: the exact deliverable, evidence as `file:line`, and the
  measurements that decide the next ruling.

**DD4 GOES IN EVERY BRIEF, WHATEVER THE KIND, AND THIS CLAUSE IS ITS ONLY
ENFORCEMENT.** Ruled by the owner 2026-08-09, together with the decision that
DD4 gets NO hard metric. The two halves are one rule: **maximize the code the
two proofs share, and write it generic.** There is no shared-line count and no
checker, because a count would be gamed the moment it gated anything, so the
principle survives only if it is said out loud every time. Say it in the
brief, and require the return to answer it:

- **A RECON** asks whether the content can be written once at a generic
  carrier and instantiated, and prices BOTH shapes. A recon that returns only
  the fixed shape has not finished.
- **A BUILD** is told generic or fixed, and why. The default is generic. A
  build that chose fixed without saying so is rejected at the audit.
- **A REVIEW, AUDIT OR PROBE** reports what it saw about reuse, even when
  nobody asked: these are the tasks that read the most code.
- **A STOP-LINE IS NEVER A REASON TO WRITE FIXED.** Say so and stop for a
  re-price. Do not deliver the fixed shape quietly inside the cap.
- The one measured exception is `dev/LESSONS.md` P-r, and it is narrow: a fold
  over a clause list whose result type every consumer must UNFOLD costs about
  3x the hand-written conjunction.

*Enforcement:* this clause, the route-planning clause in section 5, and the
return audit in section 6. Nothing mechanical checks it, which is exactly why
it is repeated.

Standing clauses that go in every build or probe brief:

- **D-1**: write the probe in `agents/tasks/<TASK>/`, the SAME directory that
  already holds this brief, and never in `src/`; your report goes there too, so
  one task is one directory; the verdict still goes in the report; write the
  deliverable incrementally, never at the end (C-22).
- **D-10**: check the target's truth at the intended generality before proving
  it, and record any correction beside the original.
- **DD8**: name the block's widest unmeasured term and the probe that would
  measure it; a brief that cannot is not ready to send.
- **At every return that touched a master, run
  `python3 scripts/check-timing.py --changed`.** It is the only gate in the
  repository that can fail a module for being EXPENSIVE: a slow module
  typechecks correctly, so `make check`, both linters and the whole gate are
  structurally blind to it. `SquareLaw` reached 0.94 s/line and 44 percent of
  the tree's cost without tripping anything. It is deliberately NOT in
  `make check` (a warm module check costs minutes; the commit gate must stay
  cheap enough to actually be run), which means if the orchestrator does not
  run it at the return, nobody does.
- **Bring the ledger current BEFORE starting the gate, never during.** The
  gate reads `dev/ledger.toml`, so an update landing
  mid-run fails on a staleness that was true for about one second. This
  happened twice on 2026-08-06 and cost two full gate runs, roughly thirty
  minutes each, on a tree whose check cost the campaign is spending its days
  reducing. The order is: audit the return, update the ledger, run
  `scripts/ledger.py --write`, THEN gate.
- **Paste the rule bundle: `python3 scripts/rules.py --for <kind>`.** Do not
  select the rules by recall. The bundle is declared in `dev/rules.toml`,
  capped so it cannot become the corpus again, and the dispatch path REFUSES a
  brief that does not carry it, with the kind DERIVED from the brief's write
  scope rather than declared by its author. **An earlier version of this clause
  said "remember to name P-k and P-l", which is a wish by this project's own
  definition: its enforcement point was the orchestrator's intention, and the
  orchestrator is the component that let an imported playbook sit uncited in
  102 of 112 briefs for five days.** The emitted bundle is about 836 words
  against `dev/LESSONS.md`'s 16,972, so the brief carries the operative
  statements and the full entry is one grep away when the evidence is needed.
- **A timed run gets the machine to itself.** Any brief that measures seconds
  says "one Agda process, nothing else running", and the orchestrator holds the
  second slot open while it is live. The dispatcher's ceiling of two cannot
  enforce this, because it cannot see what an agent profiles: two
  `--profile=definitions` runs corrupt each other's numbers, and this campaign
  funds decisions on those numbers. `[L3.32-T88]` had to disclose a contended
  baseline for exactly this reason. **A wrong measurement is not slow, it is
  believed.**
- **THE LITERATURE SURVEY, for any brief that writes a master** (DD18,
  extended by the owner 2026-08-10). `dev/literature/` holds the digested
  mathematics: `digest.md` for the orthodox route, `j-hierarchy.md` for
  condensation, `fine-structure.md`, `rudimentary-functions.md`,
  `devlin-errata.md` for the known errors in the primary text,
  `primary-sources.md` and `BIBLIOGRAPHY.md` for what was fetched and what
  consumed it, `formalizations-landscape.md` for prior art. The brief carries
  a **LITERATURE** section naming what may bear on the task; the return
  carries **LITERATURE USED**, saying what it read, what it took, and WHY NOT
  for anything skipped. **The why-not earns its keep:** a note that a source
  is OCR-degraded, or covers the wrong chapter, stops the next agent paying
  the same reading twice. **BOTH SURVEYS ARE ENFORCED AT DISPATCH, identically
  and on every brief** (owner, 2026-08-10): `dispatch.py` refuses a brief with
  no ARCHIVE section and one with no LITERATURE section, whatever its kind. One
  honest line naming the corpus satisfies either. **The scope is every brief
  because a recon needs the literature most:** `[LJ-1.1]` planned the whole GCH
  wing and wrote only a report, so a build-only gate would have exempted it.
  **The limit: this binds the CODEX path.** An in-harness dispatch skips
  `dispatch.py` entirely, so the orchestrator applies both surveys by hand
  there and sends back a return that lacks either USED section.
- **THE ARCHIVE SURVEY, and it is a section of the brief rather than a hope.**
  Ruled by the owner 2026-08-09. Before a brief is sent it carries an
  **ARCHIVE** section listing what may bear on the task in each of the four
  archives: `archive/` for retired code, with `archive/src/2026-08-09-rud-route/` holding the
  72 files of the retired route and `dev/ARCHIVE.md` describing the modules
  retired before it; `archive/dev/TASKS-archived.md` for what each of the 265 earlier
  dispatches found; `archive/dev/JOURNAL-archived.md` for why; and
  `archive/dev/DECISIONS-archived.md` for the rulings that route ran on.
  `dev/LESSONS.md` is NOT archived and still binds, so it is cited the usual
  way through `scripts/rules.py`.
- **AND THE RETURN NAMES WHAT IT USED.** A report carries an **ARCHIVE USED**
  section: what it actually read, and what it took from each item, at
  `file:line`. "I looked at the archive" is not a return. A brief whose
  archive section is empty must say why it is empty.
- **A port is priced against a fresh write, never assumed** (DD13). The
  archive is reference material, not a shortcut, and P-l holds: a measured
  cure does not transfer by analogy.
- **A PHASE-1 BRIEF IS NOT TOLD IT IS SETTING A BAR** (DD5, measure 2). The
  internalization GCH wing's measured size becomes the benchmark the two-tower
  route must beat, so the project writes its own examination paper. A brief
  that says "your output sets the bar phase 3 must clear" hands the agent a
  reason to write long, and it would be acting rationally. **So the brief says
  the opposite and means it: write this as the deliverable, as tight as if it
  shipped.** The defence that does the real work is not this clause but the
  a-priori ceiling: `[LJ-1.1]`'s projection is recorded before any build, and
  the benchmark is the SMALLER of that and the measurement, so writing long
  cannot raise the bar. **Do not confuse this with hiding information.** An
  agent that asks what the wing is for gets a straight answer. The rule is
  that the brief does not volunteer an incentive nobody needs to do the work.
- **DD8, the gate, FIRST.** Before you fund a block, name its widest unmeasured
  term and the probe that measures it. **A build brief that cannot name both is
  not ready to send.** A green gate narrows the band and lowers its top, which
  is what decides whether a projection fits, so this is arithmetic and not
  caution.

  **The old text here forbade dispatching NEW MATHEMATICS outright**, which was
  D30's check-cost freeze. **That freeze is CLOSED**: it belonged to the retired
  route, it was exit-condition-complete, and the two-tower route replaced its
  wall gate with DD5's relative constraint. Phase 1 of the live plan is five
  new-mathematics builds, so the clause as written forbade the plan. `[LJ-0.1]`
  found it and `[LJ-0.2]` ranked it blocking. **The only freeze still standing
  is DD23, and it covers mathematical PROSE, not mathematics.**
- **DD4, generic writing and maximum reuse, in EVERY brief.** For a recon: ask explicitly whether
  the content can be written once at a generic carrier and instantiated, and
  require the report to price BOTH shapes. For a build: state which shape is to
  be written and why, with generic as the default. **Add the attitude clause
  verbatim, because it is the part agents drop:** a stop-line is not a reason to
  write fixed; if the generic shape does not fit the budget, say so and stop for
  a re-price rather than delivering the fixed shape inside the cap.
- **Seconds, not only lines** (owner's ruling, 2026-08-06). Every build brief
  requires the module's own check time BEFORE and AFTER, measured with
  `GHCRTS=-M8g agda --profile=modules <file>` (or `--profile=definitions` for a
  breakdown), warm deps, one process, stating which. Every recon that prices a
  lever prices it in both dimensions. **A change that saves lines and costs
  seconds is not automatically good, and one that costs lines and saves seconds
  may be excellent**: the measured Bridge fix is six lines for 769 seconds. The
  ledger carries the seconds beside the lines (`dev/ledger.toml`'s `[timing]`,
  `[[hot]]` and `[[tree_cost]]`).
- **DD13 at a retirement question.** If the brief touches what retires, quote
  DD13 into it: "X must stay because Y consumes it" is not an answer, the
  ideal-form rewrite of what Y actually needs is priced first, and the old
  chapter then retires WHOLESALE. Say explicitly that D-19's port rates must
  not be quoted at a rewrite question, because that substitution is the
  specific error DD13 names and an agent will make it unprompted.
- **DD2 and DD5, what is ruled and what is open.** State BOTH in the brief's header.
  **Ruled (DD2), and NOT reopenable:** both trophies, `L ⊨ AC` and `L ⊨ GCH`,
  both stated in L; and where a bridge is built it delivers BOTH directions of
  the two-definition identification. The core constraint is architectural,
  MAXIMIZE THE CODE THE TWO PROOFS SHARE (DD4).
  **CANDIDATE, not ruled (DD2, amended 2026-08-09):** the two towers and the
  bridge, L plus J through rud. It is the leading architecture and the plan
  builds toward it, and **the binding ruling is `[LJ-2.5]`**, after the
  benchmark and the reuse map exist. Say this in the header exactly this way.
  An agent told the architecture is ruled will not report evidence against it,
  which is the whole reason the ruling moved.
  **Open: how to walk it**, which results decide, so name the current working
  direction as a working direction and not as law. This half is load-bearing and is not a courtesy: the technique is
  empirical, and archived D26(B), which the DD consolidation did not re-home,
  has no other home. Say
  that a line count is a measurement, recorded once with its basis and worked down
  as a best-effort target, never argued from. A gate asks which TECHNIQUE to
  use, so a red must return the next candidate technique, named and priced, on
  the obligation that defeated the last one.
- **A stop is a deliverable.** Say so explicitly, so an agent that finds the
  target false reports instead of forcing it.
- **Adversarial honesty**, named in the direction the brief is biased: if the
  brief argues for a rewrite, say that over-optimism about rewrite cost is the
  failure mode to guard against.

*Enforcement:* the brief is written to `agents/tasks/<TASK>/` and re-read before
the dispatch command is issued. `scripts/check-dispatch-policy.py` reads every
brief through `scripts/agents_tree.py` and prints the count it read, so a layout
change that emptied the census fails instead of passing quietly (C-40).

## 4. Tree-wide sweeps

A sweep that rewrites many files at once (a terminology change, a mechanical
refactor) **must not run while dispatched agents hold write territories**,
unless it excludes those files explicitly. The danger is not a merge conflict,
which git would show, but a SILENT CLOBBER: the sweep reads a file, the agent
writes it, the sweep writes back its own version, and the agent's work is gone
with no diff to show for it.

*Enforcement:* before a sweep, list the write territories of every running
agent and exclude them; after it, confirm each excluded file is untouched. **And the
exclusion creates a debt: an agent dispatched before a sweep returns work
written to the old convention, so every excluded territory is re-swept when it
lands.** That debt came due within the hour: a chapter dispatched before a
terminology sweep landed carrying a rendering the sweep had just retired, and
the pre-commit hook caught it.
On 2026-08-05 a seven-term sweep ran across 43 files with four agents holding
territories and escaped only because none of their files contained a swept
term. That is luck, not method.

## 5. Registration, and the shape question before it

**Before a route is planned, ask the generic question of the route itself**
(DD4): can the content be written once at a generic carrier and instantiated,
rather than written per carrier and unified later? The cheapest generic decision
is the one made before two chapters exist to unify, and this campaign has twice
paid for making it late. Record the answer in the registration, so the briefs
that follow inherit a decision rather than re-opening one.

A task is registered in `dev/PLAN.md` **before** the work starts, never
backfilled (PLAN section 6.0 rule 6). This was breached once, for four tasks,
and the breach is recorded in the row rather than tidied away.

*Enforcement:* the PLAN commit precedes the dispatch command in the same turn.

### 5.1 Route triage: which route, under which condition

**A route awaiting a decision is KEPT** (owner ruling, 2026-08-06). Nothing
is deleted for being unfunded; a route leaves the board only by being refuted
or done. The conditions are these prose rules, which were moved here when the
ledger was stripped to measurements (`[L3.32-T113]`). They were also drawn as
a flowchart on the generated dashboard, which the owner abolished on
2026-08-09; the prose below is now the only statement of them:

- **While DD23 stands, mathematical prose is not funded work.** Nothing else
  is frozen. The retired route's resume order, which named the bridge
  landing, the choice re-home, the StepInL rewrite, W3 and W7's residue, is
  SUPERSEDED: every item belonged to code now in `archive/src/2026-08-09-rud-route/`, and
  the freeze that gated them closed with the route. **The live order is the
  LJ phase barrier in `dev/PLAN.md` section 11**, and no other document
  states it.
- **When a compression lever is considered**, run this order: if it is
  refuted it is not a route (recorded closed); if ruled work already did part
  of it, re-price before considering (the delivered part is not still owed);
  if it is priced at x3 with an unmeasured widest term, probe first (DD8);
  if its region is being touched by ruled work anyway, take it now (marginal
  cost near zero); if the endpoint projection needs the lines, rank by net
  lines per unit of risk and take the cheapest first; otherwise keep and
  wait (DD8: an estimate is ONE best-effort number that names its basis, and
  an overage is recorded rather than argued from).

*Enforcement:* the standing brief clauses in section 3 (DD8 for the gate,
DD13 for pricing a port against a fresh write) and the return audit in
section 6 step 2. The generated route board that used to draw these
conditions was abolished on 2026-08-09, so this prose is the only statement
of them.

## 6. Handling a return

**THE ORCHESTRATOR'S OWN WORK GETS THIS CHECKLIST TOO, and until 2026-08-09 it
did not.** `[LJ-0.3]` found that the thirteen commits which changed the route
were the one piece of work in the campaign that skipped the return audit. It
was audited afterward, by `[LJ-0.1]`, which found 30 defects, six of them
load-bearing: the commit gate went RED with the rebuild itself, the document
that generates every brief named the RETIRED route, and the status screen
described the retired route for the whole day of the change.

**A change that rewrites the rulebook needs the rulebook's own gate more than
any other change does.** So: when the orchestrator writes rather than wires,
it runs steps 2, 5 and 6 against its own diff before the turn closes, and a
change to the rules themselves is DISPATCHED for audit rather than
self-reviewed, because the critic must not be the author.

In this order, every time:

1. **Read the final message**, then the report if the finding is load-bearing.
2. **Verify independently.** Re-run the agent's own typecheck under the
   orchestrator's cap. Spot-check the load-bearing claims at `file:line`,
   especially absence claims (grep them) and any claim that a wall is gone.
   **Reject any report that reasons from a line overage to a route change**
   (DD8): the route is ruled, the number is recorded, and the report
   is sent back for the next technique. A report that changes a TECHNIQUE on a
   measured obligation is doing its job and is not caught by this.
   **A build that wrote fixed where generic was possible, without saying so,
   is returned** (DD4): the choice is legitimate, hiding it is not.

   **Run `python3 scripts/check-sources-read.py <task>`** (DD18). It diffs the
   sources the brief NAMED against the paths the agent actually OPENED in a
   tool call. **A miss is a question, never a verdict**, and it is answered in
   this order.

   - **Did the return say WHY NOT?** DD18 asks for a reason, not for
     compliance. A reasoned skip that holds is the end of it. `[LJ-1.16]`
     skipped `devlin-errata.md` because the brief itself said the errata do
     not reach Chapter II section 5.
   - **On a POSITIVE return, read the missed source yourself.** It is usually
     one grep, and it is cheap insurance against a delivered result that a
     named source contradicts. Do NOT re-dispatch for the miss alone.
   - **On a NEGATIVE return, put the miss into the DD25 review as a NAMED
     question.** This is the expensive case and the reason the checker exists:
     `[LJ-1.6]` refused, and the cure had been sitting in the archive file its
     brief named and it never opened. DD25 already escalates every negative
     return, so the miss costs nothing extra to chase and it is exactly what
     an adversarial reviewer can settle.
   - **Then ask whether the BRIEF caused it.** A brief that names a FILE
     invites a topic-shaped grep; a brief that names the ROW, or demands an
     artifact only reading produces, gets the read. The controlled comparison
     is one day old: `[LJ-1.6]`'s brief said "`archive/dev/TASKS-archived.md`
     for what the dispatches found" and the agent grepped by topic and missed
     the row it needed; `[LJ-1.19]`'s said "FIND IT and cite it at
     `file:line`" and the agent returned `LevelSigma.lagda.md:203`.

   **The checker proves a path was OPENED, never that the right part was
   read.** It would have passed `[LJ-1.6]`. Its own docstring says so.
   **A cold-check regression is a defect**, not a cost of doing business; if a
   chapter's cold check has grown, say by how much and why before wiring it.
   **The return must carry the number**: a build that reports lines without
   seconds is incomplete, since 2026-08-06.
3. **Fill the free slots** (section 2) before writing anything up.
4. **Wire** `src/Everything.lagda.md` (agents never touch it) and any catalog
   prose the change makes stale.
5. **Gate**: `make check`, or the individual checks when a sibling holds the
   Agda slot, saying which was run. **A full cold typecheck is launched as a
   harness-tracked background job and never in the foreground** (DD15): it runs
   about twelve minutes, it must not hold the turn, and its result is read from
   the completion notification. **Do not arm it while any agent is live**: it
   would read masters they are mid-write on, which produced a spurious failure
   the first time and could as easily produce a spurious green. Section 4's
   rule against tree-wide writes during dispatch has this read-side twin;
   `dispatch.py gate-ready` checks it. **And because each full gate costs one
   quiet dispatch window, full gates are BATCHED**: after an ordinary return
   run the warm check, which is seconds when the change is shallow and still
   catches a broken consumer, and spend a window only when
   `scripts/check-tree.py --gate-debt` says one is due (about three to four
   returns, or roughly 1,000 added in-fence lines under `src/`). Record a
   green one with `--gate-passed`. Do not report a wiring as verified before that
   notification lands; a turn may close with the check still running as long as
   it says so and names what is not yet known.
6. **Commit** with the goal code, recording what was measured and what was
   refuted. Never push.
7. **Record** in PLAN (the ruling and the number) and, if a law was learned, in
   `dev/LESSONS.md`. **If the return could move the size ledger, bring
   `dev/ledger.toml` current in the same turn** (DD15): narrow or close the
   remaining row the work landed against, say whether it came in inside its
   band, and move a gated row's class from x3 toward x1.3 when its gate goes
   green. Standing needs no edit: `scripts/ledger.py` measures it from the tree
   and it is written down nowhere. **If the chapter introduced a load-bearing term the
   glossary does not carry, dispatch the terminology dossier (section 8) before
   the chapter counts as landed.**

8. **Report the standing figures to the owner in the return.** The generated
   dashboard was abolished on 2026-08-09, so there is no page to refresh and
   no step here beyond quoting `python3 scripts/ledger.py --brief`, which is
   the only admissible source for a standing figure.

   **There is no hand-written half.** `_build/workbench.md` was deleted on
   2026-08-07 by the owner's ruling, superseding the 2026-08-06 ruling that
   had required it be written by hand at every return. It existed because a
   board cannot know what the orchestrator intends to dispatch next; the cost
   was a hand-edited file at every return, a parser for it, and a placement
   pass onto the route graph. The agent table's `next` column now reads the
   ledger's `[[owed]]` queue instead. **That is weaker in one stated way: the
   owed rows say what is READY, not what will be dispatched first.** Ordering
   is a judgement and it now reaches the ledger, `dev/PLAN.md` and the commit
   messages, all of which are committed and reviewable, rather than a
   git-ignored scratch file that was neither.


## 7. Committing

**Committing.** The orchestrator commits; dispatched agents never do. Commit
after the audit and the gate, with the goal code in brackets, recording what
was measured and what was refuted. **Never push** without the owner's word: one
push is one CI run and one deploy.

## 8. Research and translation

**Web research always goes to a sub-agent** and comes back as a dossier with
sources, never inline in the orchestrator's loop; the owner rules on the
presented evidence.

**A term not in `dev/glossary.toml` is not invented, and settling it is a
TWO-AGENT PIPELINE, not a judgement call** (DD19, ruled as D35 2026-08-07; it
replaces the owner's default review). **Arm 1, codex:** search the web for the
literature provenance of each rendering, with sources; only where the
literature is silent, draft two or three candidates by analogy FROM terms that
have provenance, each with the analogy it rests on and the collision it
avoids; mark every guess as a guess; give the Japanese rendering where a
source supplies one. **Arm 2, opus tier, adversarial:** verify the sources,
attack each recommendation's collisions and its in-tree consistency claims,
and return PASS or FAIL per term. **A term that PASSES lands in the glossary
without the owner's review**; the commit cites the dossier and the review. A
term that FAILS, or that the review leaves as a genuine fork, escalates to
the owner, and only that term does. The owner's veto always stands: any
ruling they make overrides the pipeline. The orchestrator still never settles
a term inline: an inline choice is unsourced by construction and nobody can
audit it.

Renderings that pass the pipeline or the owner's ruling then go into
`dev/glossary.toml`, with an `avoid` list for renderings that are actively
wrong, and nowhere else. **An `avoid` entry that bans a common word will fire
on its innocent uses**, so ban a rendering only when it is wrong in every
context; otherwise leave it to review and say so in the term's notes.

*Enforcement:* section 6 step 7 (the return-handling checklist: a chapter that
introduces a term the glossary lacks is not fully landed until the dossier is
dispatched), and `check-glossary.py` in `make check`.

## 9. What stays out of the repository

Owner-private context (private sibling repositories, local machine paths,
anything the owner marked private) lives only in the orchestrator's session
memory and never reaches `AGENTS.md`, `CONTRIBUTING.md`, the README, this file
or the site.
