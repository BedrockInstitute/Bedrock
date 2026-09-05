# LJ-1.377 report: the enforcement point for the live-record-unread detour

tier: pi (pi-subagent-mode), model `glm-5.3`. RECON that became a small
build. Written incrementally (C-22). Every negative is MEASURED or INFERRED.
No commit, no push. `make check` was NOT run. My one target ran alone.

## LEAD

**An enforcement point exists and I built it:
`scripts/gate/check-live-record-claims.py`, wired as the `liverecord` target
in `make check`, epoch 2026-08-16, live numbers 274 briefs, 73 frozen, 0 new
defects, exit 0.** It holds two narrow triggers: a negative-existence claim
about the record must be answered by the rows the record actually holds, and
a brief that names a goal code must answer the open-work list. Two wider
designs were killed by measurement first, because they fired on 100 percent
of briefs. The shape follows `check-premises-stated.py` (trigger table plus
epoch) and `check-dd18-survey.py` (a narrow gate plus a broad print), with
`check-baseline-home.py`'s rule that the guarded set is derived, not
hardcoded.

## THE ABORT BRANCH TAKEN

Branch 1: a mechanism exists and is cheap. It is built and wired. Two
candidate mechanisms were REFUSED by measurement before the surviving one,
which is the discipline `check-premises-stated.py` set:

- Whole-brief token overlap against all 377 index rows fires on 274 of 274
  briefs, MEASURED by `agents/tasks/LJ-1-377/probe_live_record.py`. That is
  the 118-of-118 failure again. A gate that fires on everything trains
  pasting.
- A duty to answer every row adjacent to every cited code fires on 274 of
  274 briefs, MEASURED the same way. The adjacency read survives only as a
  print in `--brief` mode, never as a gate.

## WHICH OF THE THIRTEEN A MECHANISM CATCHES, AND AT WHICH MOMENT

The four moments: brief-writing (the `--brief` print), the gate
(`make liverecord`, run before commit), dispatch (nothing of mine lives
there, C-48 and the one-checker limit), and return (DD18 B2's side, not
mine).

1. **The step-6 renaming chain (LIVE RECORD, cost about 2).** PARTIAL, at
   brief-writing and at the gate. The goal trigger forces the juxtaposition:
   run on `LJ-1.250` at its own historical screen, the checker's duties
   include `open work item 1`, which reads "The supply chain for the
   satisfaction layer" at PLAN:53 and carries the sentence "Step 6
   re-prices at about 255 and is UNBUILT" two lines below. MEASURED, by
   `.venv/bin/python scripts/gate/check-live-record-claims.py --brief
   agents/tasks/LJ-1-250/LJ-1.250.md`. NOT a catch: no token bridge exists.
   The chain's briefs share at most one token ("unbuilt") with the open-work
   item, MEASURED by the probe, and `dev/JOURNAL.md:1030` says the same in
   its own words: "Step 6 and the leaf supply share no word". The gate puts
   the row in front of the writer and demands one written line. The
   connection stays the writer's. For the FUTURE class the gate is stronger:
   once any row or screen line names both names, the claim search links
   them, and a future ep1 becomes an ep3. INFERRED.
2. **BandChoice (KIND A and C, cost about 1.5).** Already served: DD28
   rules the survey-first order, ruled at `dev/PLAN.md:624`. My checker
   reads `dev/PLAN.md` only and adds nothing. Not this task's kind.
3. **The wall already measured GO (LIVE RECORD, cost about 1.5).** CAUGHT,
   decisively, at both moments. Run on `LJ-1.230` against the index as it
   stood the day that brief was written, the FIRST duty is
   `LJ-1.124: claim line 1 shares decode, probe with a positive row
   (GO, 147 LINES) at PLAN:677`. MEASURED, command as above with
   `LJ-1-230/LJ-1.230.md`. That is the exact row `[LJ-1.233]` found by
   hand at `agents/tasks/LJ-1-233/lj-1.233-report.md:19`. Four false
   companions fire beside it, so the duty is an answer or a written
   decline, never an automatic red on one row.
4. **The term cured five dispatches earlier (LIVE RECORD, cost about 1).**
   PARTIAL, at brief-writing only. `LJ-1.177` carries no claim trigger, so
   the gate is silent, MEASURED. The missed row `LJ-1.158` appears in the
   advisory adjacency print: uncited, within three rows of the cited
   `LJ-1.155`, sharing five raw tokens (agree, code, only, wing, worse),
   MEASURED. But generic neighbours out-rank it, so the print shows it
   without forcing it. Honest verdict: visible, not caught.
5. to 7., 10. to 12. **The KIND B archive episodes.** Not this task's kind.
   DD18 B2's quote duty gates the return side and already landed,
   `scripts/gate/check-dd18-survey.py`.
8. **The 5,047 anchor (LIVE RECORD, P-l).** NOT caught, and no token
   mechanism can: the figure had an archive basis, so a premises gate
   passes it, and the missing act was re-measurement at its own site, which
   is P-l and stays review. MEASURED as out of reach, not asserted.
9. **The wrong object (KIND A borderline, LIVE RECORD, cost about 0.5).**
   NOT caught. The brief delegated a type check it should have performed.
   No lexical shape exists. The enforcement point is the review step, named
   below.
13. **The premise-caused aggregate (8 of 10 overturns).** Already served:
   `check-premises-stated.py`, landed 2026-08-16 from the same
   `[LJ-1.211]` finding. My claim trigger is its narrow second half for the
   negative-existence shape: of the 11 briefs the sweep finds with claim
   hits, four are the audit's own episodes (LJ-1-228, LJ-1-230, LJ-1-246,
   LJ-1-250), MEASURED. The C-42 count for the shape is 11 of 274 briefs.

## WHAT THE MISSED RECORDS HAD IN COMMON

A shared shape exists in exactly two of the six live-record episodes, and it
is positional, not lexical:

- **Episodes 3 and 4 share a shape.** The missed row sat in `dev/PLAN.md`
  section 11, within three rows of a code the brief DID cite, and shared
  two or more tokens with the brief. MEASURED: `LJ-1.124` sits three rows
  below the cited `LJ-1.123` and shares decode and probe with `LJ-1.230`'s
  title; `LJ-1.158` sits three rows below the cited `LJ-1.155` and shares
  five tokens with `LJ-1.177`. Both briefs cited the table and never read
  around the citation.
- **Episode 1 shares the surface but not the bridge.** The missed record
  was section 0.0's open-work list, on the screen the writer maintains, and
  no token connects the two names, MEASURED above.
- **Episodes 8 and 9 share nothing with the above.** They are a
  re-measurement failure and a delegation failure. Said plainly: the missed
  records do not share one checkable shape, and any design that assumes
  they do is wrong.

## PERSONAL OR STRUCTURAL

**Structural, for the lookup episodes (1, 3, 4). Personal-shaped for the
judgement episodes (2, 9). Mixed, and the split is what should be built
on.** The evidence for structural:

- The index holds 377 rows today. A brief cites a median of 6.5 codes,
  maximum 21, MEASURED over the 274 live briefs. A writer that cites six
  codes reads none of their neighbours under rate pressure. A machine reads
  all of them for free. The failure is a tool-shaped failure.
- The RETIRED route made the adjacent mistakes on its own 265-row index,
  which nothing enforced reading:
  `archive/dev/JOURNAL-archived.md:2235` records "[T79] already measured
  700 to 850 standing lines written twice", and `:3593` records a defect in
  the orchestrator's own brief that "nearly bought the target twice". Two
  routes, two indexes, the same shape.
- The archive's own answer to enforcement was a document sentence only:
  `archive/dev/TASKS-archived.md:16` says the owner's standing instruction
  of 2026-08-09 "require[s] a brief on the new route to survey the archive
  BEFORE it is sent", and `scripts/check-task-index.py` only RESOLVES
  citations against the file. A policy only a document states is not
  enforced (C-48). The predecessor's cure was a wish, and this task exists
  because the live route repeated the shape.

## WHAT I BUILT

One checker, `scripts/gate/check-live-record-claims.py`, and one Makefile
target, `liverecord`, appended to `check:`. Nothing else. `src/` untouched
(I-5). The two triggers:

1. **The claim trigger.** An ACTIVE phrase from a measured table ("nobody
   has run", "nothing on record", "exists nowhere", 11 ACTIVE rows, 3
   REFUSED rows with their fire rates) marks a claim line. The checker
   searches the section 11 rows with a positive status (GO, BUILT, GREEN,
   ...) and the section 0.0 screen, as they stood at the parent of the
   commit that added the brief, for two or more shared tokens. Each hit
   must be answered.
2. **The goal trigger.** A brief naming a goal code from the section 0.0
   blocked table must answer that goal's blocked row and every numbered
   open-work item. This is the journal's one-grep cure at
   `dev/JOURNAL.md:1026-1029` made mechanical.

Compliance is a `## LIVE RECORD` section, one line per flagged object,
quote or written decline. A decline is compliance, the `[LJ-1.357]` lesson:
the duty forces the row into view and the text into review. The checker
answers a function-level compliance test, 10 duties to 0 unanswered.

## LIVE NUMBERS AND THE EPOCH

All commands run with `.venv/bin/python`, exit read with no pipe:

- `scripts/gate/check-live-record-claims.py`:
  "274 briefs, 73 frozen pre-epoch with a trigger and no LIVE RECORD
  section, 0 new defects", exit 0.
- `make liverecord`: same line, exit 0.
- The corpus: 274 live briefs, 377 section 11 rows, 363 section 0.0 lines,
  8 open-work items on 2026-08-16.
- Trigger rates over the corpus, MEASURED: the ACTIVE claim union fires on
  30 briefs (10.9 percent); "nobody has" bare fires on 18.2 percent and is
  REFUSED; the goal trigger fires on 70 briefs (25.5 percent).
- The failing set: 73 of 274 (26.6 percent), median 4 duties per failing
  brief, maximum 22. For scale, `check-premises-stated.py` froze 49 across
  its two epochs.
- The epoch is the FROZEN set in the checker's source, 73 names, written
  once and never failed. Its scale lives in the comment, not in any commit
  message (C-59).

## THE REVIEW STEP THAT STILL CARRIES RULES THIS GATE CANNOT

Named so a brief can be written from it, per the third abort branch, which
applies to the residue even though I built:

- **P-l at the pricing surface.** A figure quoted from any record is
  re-measured at its own site before it prices anything. Episode 8's class.
- **The delegation audit.** A brief that delegates a type check to its
  agent performs it first. Episode 9's class.
- **Relevance.** The gate cannot tell whether a row BEARS. The decline line
  is where the author says so, and the DD25 review reads it before anything
  else, as it reads the PREMISES list.

## PREMISES, EACH MARKED

- **P1, the dominant kind is the live record unread, at
  `agents/tasks/LJ-1-376/lj-1.376-report.md:1`.** VERIFIED at the LEAD,
  lines 5 to 8, and by my own read of the whole report. One caliber note:
  the lead's "the four costliest episodes" is loose. By the report's own
  single-episode costs, three of the top four are live-record (episodes 1,
  3, 4) and the second-costliest (episode 2, BandChoice) is not. The class
  still dominates by spend. INFERRED, from the report's own cost table.
- **P2, briefs caused 8 of 10 overturned DD25 reviews and the reviewer 0,
  at `agents/tasks/LJ-1-211/lj-1.211-report.md:21`.** VERIFIED at `:15` to
  `:27`, marked MEASURED there from the reviews' own brief-cause sections.
- **P3, the costliest case re-derived a price standing in section 0.0, at
  `dev/JOURNAL.md:1002`.** VERIFIED at `:1000` to `:1004`, and at the
  historical screen: the parent of the commit adding `LJ-1-250` carries
  "Step 6 re-prices at about 255 and is UNBUILT" at its line 55, read by
  `git show`.
- **P4, its cure has no enforcement point, at `dev/JOURNAL.md:1026-1029`.**
  VERIFIED at `:1026` to `:1029`, and MEASURED that no prior checker
  enforces it: `grep -rn "open.work|OPEN WORK" scripts/ --include="*.py"`
  returns nothing outside my own checker.

## DID I ADOPT THE BRIEF'S FRAME

I checked, as instructed. Two frames were adopted after testing, one was
refused:

- Adopted: the live-record class is dominant. The episodes support it.
- Adopted: the four-moment surface analysis. The cheap moment is
  brief-writing, confirmed by the demo output.
- Refused: the implication that one mechanism serves the class. MEASURED:
  episodes 8 and 9 have no lexical shape, and episode 1 has no token
  bridge. The gate serves episodes 3 and 13's shape fully, 1 and 4
  partially. A brief that claims more would be false safety.

## DD4

My axis is not the two towers, and I say so plainly. What is live:
`[LJ-1.376]` priced the worst episode at about two dispatches and the class
at about 8 dispatch-equivalents, and every one of those buys back budget
the shared condensation supply needs. The checker itself is written generic
along the re-instantiation axis: the trigger table, the row parser and the
open-work parser carry no LJ-1 assumption, so an LJ-2 index and screen need
zero changes.

## ARCHIVE USED (DD18)

- **`archive/dev/JOURNAL-archived.md`**: CITED, grepped and read at the
  named windows. Line read, `:3593`: "A DEFECT IN THE ORCHESTRATOR'S OWN
  BRIEF IS RECORDED HERE TOO, because it nearly bought the target twice".
  Took the predecessor's double-buy defect and the `[T79]` duplicated-lines
  record at `:2235` as the structural evidence above.
- **`archive/dev/TASKS-archived.md`**: CITED, read at the header. Line
  read, `:16`: "both require a brief on the new route to survey the archive
  BEFORE it is sent". Took the finding that the retired route's 265-row
  index had a document sentence and no mechanism, which is C-48's shape.
- **`archive/dev/DECISIONS-archived.md`**: CITED, grepped and read at the
  named rows. Line read, `:46` (D24): "a rule that is not machine-enforced
  must name its enforcement point". Took D24 as DD19's ancestor, and D26's
  ENFORCEMENT POINT at `:47` ("Every dispatched brief states what is ruled
  and what is open in its header") as the precedent for a brief-header
  duty. No ruling requires reading the live record before dispatching;
  the nearest is D22's block gating. DECLINED beyond these rows.
- **`archive/src/2026-08-09-rud-route/`**: DECLINED. Checked by directory
  listing and the `Cardinal.lagda.md` citation already read by `[LJ-1.376]`.
  Nothing under it bears on process mechanisms. WHY NOT: it is Agda source
  of the retired route, and this task is a process task.

## LITERATURE USED (DD18)

`dev/literature/` bears nothing on process mechanisms. MEASURED three
times, by `[LJ-1.356]`, `[LJ-1.357]` and `[LJ-1.371]`, and cited by my
brief. I did not re-open the corpus. WHY NOT: this task designs a checker
against `dev/PLAN.md`, and no digest describes that.

## FILES

- Created: `scripts/gate/check-live-record-claims.py` (the checker).
- Edited: `Makefile` (the `liverecord` target, plus one word appended to
  the `check:` prerequisite list, which the brief's build branch orders).
- Created: `agents/tasks/LJ-1-377/probe_live_record.py` (the measurement
  harness; runs stand-alone) and this report.
- Not touched: `dev/PLAN.md`, `dev/LESSONS.md`, `dev/JOURNAL.md`,
  `AGENTS.md`, `src/`, `scripts/dispatch/`. Proposed text for the ruling is
  below, and the rulings are the orchestrator's.

## PROPOSED RULE TEXT, for the orchestrator to rule or cut

A brief answers the live record its own words implicate. A claim that the
record lacks something is checked by `scripts/gate/check-live-record-claims.py`,
and every row the search implicates is answered in a `## LIVE RECORD`
section, quoted or declined in writing. A brief that names a goal code
answers the open-work list. Enforcement: `make liverecord`, epoch
2026-08-16, 74 briefs frozen. The cure at `dev/JOURNAL.md:1026-1029`
thereby names its enforcement point, and DD19 is satisfied for the
live-record class as far as tokens reach. Where tokens do not reach, the
review steps named above carry the rule, and this report says which those
are.
