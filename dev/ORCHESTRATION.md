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

**Codex is the default for every dispatch.** The orchestrator uses an in-harness
Opus subagent in exactly two cases: the owner says so for that task (a past
override never carries forward), or the orchestrator judges the task
very-very-heavy, a deliberately high bar meaning whole-campaign synthesis or
wall-class mathematics beyond measured scale. Ordinary probes, recons, polish
passes and implementation batches are codex work, and codex has delivered all
of those green.

*Enforcement:* the brief header carries a `tier:` line before dispatch.
`tier: codex (default)` needs no justification; `tier: opus` must name which
exception applies and, for the second, why codex cannot carry it. **If that
sentence will not write, the tier is codex.**

## 2. Slots

Concurrency and heap ceilings are LESSONS C-12: agent Agda runs at
`GHCRTS=-M8g` with at most four concurrent, or `-M12g` with at most two; the
orchestrator's own runs at `-M16g`; one Agda process per agent, always. Agents
that run no Agda do not consume a slot.

**An idle slot is a defect** (PLAN D23). At every return, before writing the
report: name what is unblocked, name what blocks the rest, and dispatch into
the free slots. Blocked means waiting on an owner ruling, on a sibling's write
territory, on a measurement that would make the work fundable, or on the
ceilings above. Auditing a return is not a reason to idle.

*Enforcement:* the return-handling checklist in section 6.

## 3. The brief

Every brief is pinned in `_build/briefs/` before dispatch, so it survives a
reboot and the owner can read what was actually asked. A brief carries:

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

Standing clauses that go in every build or probe brief:

- **D-1**: probes are never committed; the verdict goes in a report under
  `_build/`; write the deliverable incrementally, never at the end (C-22).
- **D-10**: check the target's truth at the intended generality before proving
  it, and record any correction beside the original.
- **D22**: name the block's widest unmeasured term and the probe that would
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
- **D30, the craft freeze, FIRST.** While it stands, **do not write a brief
  that dispatches new mathematics.** Defect repair, profiling, the fixes a
  profile licenses, and capturing the retiring tree's craft are the plan and
  are dispatched normally. If a brief would advance a trophy rather than the
  check-cost data, it waits. When in doubt the test is: would this dispatch add
  in-fence lines to a surviving master in order to prove something new? Then it
  waits.
- **D29, generic writing, in EVERY brief.** For a recon: ask explicitly whether
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
- **D17 at a retirement question.** If the brief touches what retires, quote
  D17 into it: "X must stay because Y consumes it" is not an answer, the
  ideal-form rewrite of what Y actually needs is priced first, and the old
  chapter then retires WHOLESALE. Say explicitly that D-19's port rates must
  not be quoted at a rewrite question, because that substitution is the
  specific error D17 names and an agent will make it unprompted.
- **D26, what is ruled and what is open.** State BOTH in the brief's header.
  Ruled: the campaign route, R2' with the trophy stated in L, which the return
  may not reopen or re-table. Open: how to walk it, which results decide, so
  name the current working direction as a working direction and not as law. Say
  that a line count is a measurement, recorded in both calibers and worked down
  as a best-effort target, never argued from. A gate asks which TECHNIQUE to
  use, so a red must return the next candidate technique, named and priced, on
  the obligation that defeated the last one.
- **A stop is a deliverable.** Say so explicitly, so an agent that finds the
  target false reports instead of forcing it.
- **Adversarial honesty**, named in the direction the brief is biased: if the
  brief argues for a rewrite, say that over-optimism about rewrite cost is the
  failure mode to guard against.

*Enforcement:* the brief is written to `_build/briefs/` and re-read before the
dispatch command is issued.

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
(D29): can the content be written once at a generic carrier and instantiated,
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
or done. The flowchart the owner asked for is rendered on the dashboard
(`[L3.32-T114]`); the conditions it draws are these prose rules, which were
moved here when the ledger was stripped to measurements
(`[L3.32-T113]`):

- **While D30's freeze stands, the check-cost campaign is the only funded
  work.** The frozen mathematics resumes in this order when the exit
  condition is met: the bridge landing (below-lim), then the choice re-home,
  then AC on surviving machinery; and the StepInL rewrite, then W3, then
  W7's residue and the GCH sentence.
- **When a compression lever is considered**, run this order: if it is
  refuted it is not a route (recorded closed); if ruled work already did part
  of it, re-price before considering (the delivered part is not still owed);
  if it is priced at x3 with an unmeasured widest term, probe first (D22);
  if its region is being touched by ruled work anyway, take it now (marginal
  cost near zero); if the endpoint projection needs the lines, rank by net
  lines per unit of risk and take the cheapest first; otherwise keep and
  wait (D26: a line overage never changes the route).

*Enforcement:* the standing brief clauses in section 3 (D22, D26, D17) and
the return audit in section 6 step 2; the route board itself is generated
for the owner by `[L3.32-T114]` from the canonical data.

## 6. Handling a return

In this order, every time:

1. **Read the final message**, then the report if the finding is load-bearing.
2. **Verify independently.** Re-run the agent's own typecheck under the
   orchestrator's cap. Spot-check the load-bearing claims at `file:line`,
   especially absence claims (grep them) and any claim that a wall is gone.
   **Reject any report that reasons from a line overage to a route change**
   (D26): the campaign route is ruled, the number is recorded, and the report
   is sent back for the next technique. A report that changes a TECHNIQUE on a
   measured obligation is doing its job and is not caught by this.
   **A build that wrote fixed where generic was possible, without saying so,
   is returned** (D29): the choice is legitimate, hiding it is not.
   **A cold-check regression is a defect**, not a cost of doing business; if a
   chapter's cold check has grown, say by how much and why before wiring it.
   **The return must carry the number**: a build that reports lines without
   seconds is incomplete, since 2026-08-06.
3. **Fill the free slots** (section 2) before writing anything up.
4. **Wire** `src/Everything.lagda.md` (agents never touch it) and any catalog
   prose the change makes stale.
5. **Gate**: `make check`, or the individual checks when a sibling holds the
   Agda slot, saying which was run. **A full cold typecheck is launched as a
   harness-tracked background job and never in the foreground** (D28): it runs
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
   `dev/ledger.toml` current in the same turn** (D27): narrow or close the
   remaining row the work landed against, say whether it came in inside its
   band, and move a gated row's class from x3 toward x1.3 when its gate goes
   green. Standing needs no edit: `scripts/ledger.py` measures it from the tree
   and it is written down nowhere. **If the chapter introduced a load-bearing term the
   glossary does not carry, dispatch the terminology dossier (section 8) before
   the chapter counts as landed.**

8. **Refresh the owner's dashboard, and write its hand-written half.** Run
   `make dashboard`, which regenerates every measured panel from the canonical
   data. Then edit `_build/workbench.md` BY HAND: what is dispatched now, what
   is queued and what releases each, what condition would change the next
   dispatch, and what is deliberately not being dispatched with the reason.
   **That half exists nowhere in committed data** (live dispatch state is in
   `.claude/`, which is never committed), so a generator cannot produce it and
   must not pretend to. **Owner's ruling, 2026-08-06: this is done by hand at
   every return**, because doing it forces a review of the whole board that a
   regeneration does not. `scripts/check-dashboard.py` reports staleness and
   exits 0 by design: `_build/` is git-ignored, so a gate that failed on a
   missing dashboard would fail every fresh clone.


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
DISPATCH, not a judgement call.** When a delivered chapter uses a load-bearing
term that the glossary does not carry, the orchestrator sends a sub-agent to
produce a terminology dossier: search the Chinese literature for the
established rendering FIRST, with sources; only where the literature is silent,
draft two or three candidates by analogy, each with the analogy it rests on and
the collision it avoids; mark every guess as a guess; and give the Japanese
rendering where a source supplies one. The owner rules on the dossier. The
orchestrator does not choose, and does not settle a term inline: an inline
choice is unsourced by construction, and the owner cannot audit it.

Confirmed renderings then go into `dev/glossary.toml`, with an `avoid` list for
renderings that are actively wrong, and nowhere else. **An `avoid` entry that
bans a common word will fire on its innocent uses**, so ban a rendering only
when it is wrong in every context; otherwise leave it to review and say so in
the term's notes.

*Enforcement:* section 6 step 7 (the return-handling checklist: a chapter that
introduces a term the glossary lacks is not fully landed until the dossier is
dispatched), and `check-glossary.py` in `make check`.

## 9. What stays out of the repository

Owner-private context (private sibling repositories, local machine paths,
anything the owner marked private) lives only in the orchestrator's session
memory and never reaches `AGENTS.md`, `CONTRIBUTING.md`, the README, this file
or the site.
