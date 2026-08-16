# LJ-1.357: DD25 review of `[LJ-1.356]`'s DD18 mechanism, and of its refutation of my premise

tier: opus (pi-subagent-mode), **the switch's ADVERSARIAL row.** `[LJ-1.356]`
was authored by `pi` / `glm-5.3`, this mode's DEFAULT row, so the adversarial
row is in-harness opus. **DD17's invariant holds: the critic is not the
author.** I ran `scripts/dispatch/dispatch_policy.py` before writing this line.

## WHY DD25 FIRES

**`[LJ-1.356]` refuted its brief's premise**, which is one of DD25's named
triggers. **My brief claimed「the form survived and the substance decayed」.**
**Its section 8 measured that this OVERSTATES**, and gave the honest form:

> **the form survived, the LIVE-route substance survived, and the
> RETIRED-archive substance decayed to a ritual that every enforcement point
> counts as compliance.**

**That correction NARROWS the cure**, and the design is then aimed only at the
retired half. **If the correction is wrong, the cure is aimed at the wrong
target and the healthy half is left unguarded, or the healthy half is taxed
for nothing.** **That is why this review exists and it is the FIRST thing to
attack.**

**The stakes are not one task.** The design proposes edits to `dev/PLAN.md`'s
DD18 row and to `AGENTS.md`, and it proposes a new `make check` target. **The
owner rules on those. They should not rule on an unreviewed measurement.**

## THE TARGET

`agents/tasks/LJ-1-356/lj-1.356-report.md`, 353 lines, and the prototype
`agents/tasks/LJ-1-356/probe_dd18_shout.py`. **Read the report WHOLE and RUN
the prototype yourself.**

**The design in one line, its own words:** *gate the ENUMERATION, not the
relevance.* Four signals: **R1** refuses a brief whose ARCHIVE section does not
name each of DD18's four corpora, cited or declined; **R2** shouts TEMPLATE
when one bullet's reason text repeats verbatim across five briefs; **R3**
refuses a report that does not answer every archive path its own brief cited;
**R4**, advisory, prints archived CODE matching the brief's subject terms and
uncited.

## WHAT TO ATTACK, in priority order

**1. THE PREMISE REFUTATION, section 8.** **Its claim: the live half did NOT
decay, and only the retired half went ritual.** Its evidence is that each of
the eleven briefs cites two to four live prior-task reports with task-specific
reasons, and that the reports answer them with TOOK, CORRECTED, REFUTED.
**Re-derive that on the eleven yourself.** **Ask the harder question it did not
ask: is a citation of a LIVE prior task a DD18 survey AT ALL?** **DD18's four
corpora are the ARCHIVES. `agents/tasks/LJ-1-3xx/` is the LIVE tree.** **If
the live citations are not DD18 compliance in the first place, then「the live
half is healthy」is a measurement of something DD18 never asked for, and my
original framing was closer to right than its correction.** **This single
question can overturn the report's central finding, and it is the reason this
review is dispatched.**

**2. THE R4「DECISIVE RUN」, and I think it is oversold.** The report calls the
LJ-1.353 run decisive because R4 printed `CardinalPredicates.lagda.md` and
`Everything.lagda.md` as missed candidates. **But its own section 5 admits R4
did NOT print `L/Cardinal.lagda.md`, which is the file that actually holds the
82-line CSB**, because the archive spells it「Cantor-Schroeder-Bernstein」and
the brief says「Cantor-Bernstein」. **So the mechanism missed the target and
hit two neighbours.** **Decide honestly: is that a catch or a near-miss
presented as a catch?** **Would a reader of R4's output have opened
`Cardinal.lagda.md`?** **Run R4 yourself and look at the actual printout.**

**3. R1's「256 of 256 FAIL」.** **A rule that the entire corpus fails is
suspicious in both directions.** **Either the corpus really is uniformly
non-compliant, or R1 demands something DD18 does not.** **Read DD18's own text
at `dev/PLAN.md` and decide whether「names each of the four corpora, cited or
declined」is DD18's demand or the report's invention.** **The report leans on
`dev/PLAN.md:608`,「listing what may bear on the task in each archive」. Open
that line and judge whether「in each archive」carries the enumeration.** **If it
does not, R1 is a NEW rule wearing DD18's clothes, and it needs the owner's
ruling as a new rule rather than as an enforcement of an old one.**

**4. THE DD4 PRECEDENT, section 7, which is the design's load-bearing
argument.** Its conclusion: **a heading gate holds when the gated form forces
TASK-SPECIFIC content, and decays when the minimal compliant form is
CORPUS-GENERIC.** **That is a genuinely good idea and it is why the design has
the shape it has.** **Verify its three numbers** (244 of 256 state DD4; the
engagement paragraph distinct in 241 of 243; only two duplicate pairs).
**Then attack the inference: does「distinct text」prove「task-specific
substance」?** **I write those DD4 paragraphs, and I can tell you that distinct
is cheap.** **Sample ten at random and read them as a critic.** **If DD4's own
substance is thinner than its distinctness suggests, the precedent supports
LESS than the report claims.**

**5. R3's 93 FAILING TASKS.** **That is a large number and it decides whether
the return gate is fair.** **Sample at least five and say whether each is real
non-compliance or checker over-reach**, for instance a report that cites a
better source and says why, which DD18 explicitly allows through WHY NOT.

**6. THE PROPOSED DIFFS, section 11.** **They go to the owner.** **Read both
as an editor: are they accurate, do they promise what the mechanism delivers,
and does the `AGENTS.md` insert survive its own prose rules?** **Anything
overstated in a rulebook edit is worse than a bug, because nothing re-measures
a rulebook.**

## THE ABORT CRITERION (D-1)

- **UPHOLD.** Then the design goes to the owner with a review behind it.
- **OVERTURN.** **Most likely at attack 1: if live-tree citations are not DD18
  compliance, the「live half is healthy」finding evaporates and the cure is
  mis-aimed.** **Say so plainly; that is the valuable outcome.**
- **SPLIT.** **Likeliest shape: the design is sound and R4's decisive run is
  oversold, or R1 is a new rule rather than an enforcement.** **A split is not
  a hedge. Say which parts stand and which fall, each with evidence.**
- **A WALL.** No Agda is required by this task. If you run any, count the slots
  first with the command below; a sibling holds one.

## CONSTRAINTS

- **LAND NOTHING, REPAIR NOTHING.** Write only in `agents/tasks/LJ-1-357/`.
  **`src/` is forbidden** (I-5). **Do NOT edit `AGENTS.md` or `dev/PLAN.md`**;
  DD19 gates the first and the owner rules on both.
- **You MAY run and modify a COPY of the prototype in your own directory.**
  **Do not edit `agents/tasks/LJ-1-356/`.**
- **`agents/tasks/LJ-1-344/Supply344.agda` and
  `agents/tasks/LJ-1-350/MustFail350.agda` are EXPECTED RED. Repair neither.**
- **`[LJ-1.355]` is LIVE and holds one Agda slot and writes under `src/V/`.**
  **Do not touch its territory.** Count slots with exactly
  `ps aux | awk '/libexec.*bin\/agda/ && !/awk/' | wc -l`; **both obvious
  alternatives OVER-COUNT, MEASURED.**
- **Never commit, never push**, never `git checkout .`, `git stash`,
  `git reset --hard` or `git clean`. Do not run `make check`.
- **Create `agents/tasks/LJ-1-357/lj-1.357-report.md` in your FIRST five
  minutes** (C-22).
- Run `.venv/bin/python scripts/gate/lint-prose.py --check` on what you write.
  **No em dash.** ASD-STE100. Evidence is `file:line`, and for a rate, the
  command. Mark every negative **MEASURED** or **INFERRED**.

## THE VERDICT WORD

**UPHOLD, OVERTURN or SPLIT**, the first word of your return. **13 of 32
decided DD25 reviews here have overturned, 41 percent. An overturn is the
valuable outcome and you are not rewarded for agreeing.**

## THE PREMISE OF MINE MOST LIKELY TO BE WRONG

**My brief for `[LJ-1.356]` already had one premise corrected.** **The one at
risk now: that the correction itself is right.** **I accepted it inside an
hour because it was well argued and because it was flattering to the corpus.**
**`[LJ-1.356]` is the only agent that has looked at this, its finding narrows
the work I must do, and I have a standing failure mode of asserting before
verifying. Treat my acceptance as evidence of nothing.**

## THE RULES

**C-48: a policy that only a document states is not enforced.** **C-45: `exit
0` is not a supply.** **C-57: a search that RETURNS the answer and a reading
that discards it are different failures, and this task turns on exactly that
distinction at R4.** **D-10, C-42, C-44, C-53, P-l, P-k.**
**C-12, C-22, C-32, C-36, C-39, C-40.** I-5. **D-1, D-26.**
**DD0, DD4, DD17, DD18, DD19, DD23, DD25.**

Run `.venv/bin/python scripts/dispatch/rules.py --for review` and read every
statement, opening the full entry for any law you act on.

## DD4

**Maximize the code the two proofs share, and write it generic.** One rule, two
ends, no metric and no checker. **NAME YOUR AXIS** (C-46), fixed at
`scripts/measure/ledger.py:50`.

**DD4 is not background here, it is the evidence base**, because section 7
argues from DD4's own mechanism to DD18's. **Say whether that argument treats
DD4 fairly**, and note that DD4's no-metric ruling exists because a shared-line
count would be gamed the moment it gated anything. **The same objection applies
to any DD18 count, including R2's five-brief threshold. Test it.**

## ARCHIVE (DD18)

**This section is under the same test the task is about. Do not let it be
boilerplate, and report if I made it one.**

- **`archive/src/2026-08-09-rud-route/L/Cardinal.lagda.md:7` and `:89`.** **The
  file R4 MISSED. Open it and confirm the spelling at `:7` is what defeated the
  term match.** That is attack 2's evidence.
- **`archive/dev/JOURNAL-archived.md:1368-1377`**, the trap the archived CSB
  closes, which `[LJ-1.356]` cites as DD18's founding cost. **Verify the
  quotation.**
- **`archive/dev/DECISIONS-archived.md:30-59`.** **`[LJ-1.356]` reports a
  NEGATIVE here: the retired route had NO archive-survey rule, so no rule died
  once.** **Check that negative; a missed rule would change the history the
  design rests on.**
- **`archive/dev/TASKS-archived.md:7`**, the header the decay reads.

**Return an ARCHIVE USED section naming ONE line read per archived file.**
**Cite archived CODE and not only records.**

## LITERATURE (DD18)

**`[LJ-1.356]` returned that nothing in `dev/literature/` bears on rule
design, after checking 16 files by name.** **Spot-check that negative: open
`formalizations-landscape.md`, which it named as the nearest, and say whether
it holds any process mechanism.** Return a **LITERATURE USED** section with
WHY NOT.

## SCOPE (read)

`agents/tasks/LJ-1-356/lj-1.356-report.md` sections 7 and 8 FIRST: the
precedent argument and the premise refutation are the two halves that decide
this review.

## SCOPE (write)

`agents/tasks/LJ-1-357/` only.

## RETURN

**Lead with ONE word: UPHOLD, OVERTURN or SPLIT.** Then attack 1, whether a
live-tree citation is DD18 compliance at all. Then R4's run, re-run by you,
with the actual printout. Then whether R1 enforces DD18 or invents a rule.
Then DD4's precedent, its three numbers verified and its inference judged.
Then five sampled R3 failures. Then the proposed diffs as an editor. **Mark
every negative MEASURED or INFERRED.**
