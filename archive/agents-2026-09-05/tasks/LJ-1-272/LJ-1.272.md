# LJ-1.272: label every DD4 figure in this phase with its axis

tier: pi (deepseek-subagent-mode), **model `deepseek-v4-flash`**: this task
runs NO Agda, holds no slot, and is natural-language work over reports. **The
model rule gives flash and I take it.** The clock selected the mode.

## GOAL

**DD4 is the rule that has cost this project most, and by the owner's ruling it
has NO METRIC. So its only enforcement is that every brief states it and every
return answers it.**

**`[LJ-1.262]` measured that this phase has been answering DD4 on TWO DIFFERENT
AXES, and that no figure says which.** Its section 7 states both:

- **Devlin's axis is Def tower against J tower.** `dev/literature/devlin-II5.md:375`
  marks the C2 row PER-TOWER because Def uses satisfaction coding and J uses
  sixteen op-graphs.
- **The port's axis is L against the ambient class.** `[LJ-1.238]`'s residual
  ZERO measures genericity in the class parameter `M`, that is L against
  `Full`.

**The two are consistent and neither implies the other.** `[LJ-1.262]` says it
in one line: **a coding can be generic in `M` and still have no J analogue.**

**`[LJ-1.225]` mixed them, and that mix is the misattribution in a DD25
verdict**: it applied a Def-against-J mark to an L-against-ambient figure.

**So: every DD4 figure this phase produced is unlabelled, and one of them is
already MEASURED wrong because of it. Sweep them and label them.**

**C-42 is the law: a refutation measures the site it names and never measures
how far that site extends. `[LJ-1.262]` named ONE site. This task is the
sweep, and the COUNT is the deliverable.**

## WHAT TO SWEEP

**Every DD4 answer in `agents/tasks/LJ-1-*/`'s reports for the `LJ-1` phase.**
Every brief carries a DD4 heading and every return answers it, so the corpus is
mechanical to find: grep the reports for `DD4`, `tower-neutral`, `per-tower`,
`PER-TOWER` and `residual`.

**These carry figures I know of, and my list is a CLAIM, not the corpus**
(C-44):

| report | the figure |
|---|---|
| `LJ-1-238` | residual **ZERO** against `Full` |
| `LJ-1-248` | the per-tower half at **146 to 196 lines**, a BAND |
| `LJ-1-227` | A2 and A7 **TOWER-NEUTRAL**; A1, A3, A4 **PER-TOWER** |
| `LJ-1-258` | **none of fifteen fields is per-tower**, all over `(K, Ktr)` |
| `LJ-1-267` | the seven `module Whole` parameters, each with an axis |
| `LJ-1-268` | the landing order, per block, with an axis |
| `LJ-1-269` | the slot layout, **tower-neutral by construction** |

**Find the ones I have not listed. That is most of the value here.**

## THE THREE THINGS TO BRING BACK

**1. THE TABLE.** One row per DD4 figure: the report, the figure, and **its
axis: `DEF-VS-J`, `L-VS-AMBIENT`, `BOTH`, or `UNLABELLABLE`.** **Cite the
`file:line` that decides each.** **A figure whose own report states its axis is
the easy case; say so and move on.**

**2. THE COUNT, which is what C-42 asks for.** **How many figures carry NO
axis in their own words?** **That number is the size of the defect
`[LJ-1.262]` found at one site.**

**3. EVERY FIGURE THAT CHANGES MEANING ONCE LABELLED.** **This is the finding
that matters.** **A figure read on the wrong axis can be a false claim, as
`[LJ-1.225]`'s was.** **For each unlabelled figure, ask: if a reader assumed
the OTHER axis, would the figure say something false?** **Name every one where
the answer is yes.**

## THE ABORT CRITERION, fixed BEFORE the run (D-1)

- **THE SWEEP COMPLETES.** Give the table, the count, and the figures that
  change meaning. STOP.
- **THE COUNT IS SMALL, meaning most reports DO name their axis.** **Say so
  plainly.** **Then `[LJ-1.262]` found an isolated defect rather than a
  pattern, and this phase's DD4 accounting is in better shape than I think.**
  **That is a real and welcome answer.**
- **A THIRD AXIS EXISTS.** **If some figure is on neither axis, name it.**
  **`[LJ-1.262]` measured two and did not claim there are only two.**
- **A FIGURE IS FALSE ON BOTH AXES.** **Then it is not an axis problem and you
  have found something better. Report it separately and loudly.**

## WHAT YOU MUST NOT DO

- **DO NOT RUN AGDA.** **A sibling is measuring SECONDS right now and needs a
  quiet machine.** **This is the hardest constraint in this brief.**
- **Do not re-derive any figure's VALUE.** **You label axes. `[LJ-1.262]`
  already re-derived ten numbers and this task does not repeat that.**
- **Do not edit any master, brief or report.** **Write your own report and
  nothing else.** **I write the status screen.**
- **Do not touch `agents/tasks/LJ-1-266/`.** A sibling is live there.
- **Create your report file in your FIRST five minutes (C-22).**
- Never `src/Everything.lagda.md`. Never commit, never push, never
  `git checkout .`, `git stash`, `git reset --hard` or `git clean`.
- Do not run `make check`; the orchestrator runs it.

## SIX RULES THIS CHAIN EARNED

**C-42: A REFUTATION MEASURES THE SITE IT NAMES.** **This task is that law
applied to `[LJ-1.262]`'s finding. The COUNT comes before any cure.**

**DERIVE A FIGURE OR DO NOT WRITE IT** (C-44). **My seven-row table above is a
claim and I have re-derived none of it.**

**CARRY A CLAIM'S QUALIFIER OR CARRY NEITHER.** **An axis IS a qualifier, and
this whole defect is that one was dropped.**

**AN ESCAPE HATCH IS THE SHAPE A WRONG CHOICE HIDES IN** (C-43).
**`UNLABELLABLE` is that shape here. Use it only when you can say WHY the
figure admits no axis, and never as a place to put the hard ones.**

**SEARCH THE OPEN-WORK LIST BY CONTENT, NOT BY NAME.** **Ten dispatches once
re-derived a price the plan already carried.**

**A FAILED SUBSTITUTION IS NOT A PROOF OF IMPOSSIBILITY** (C-36).

## THE CLASSIFICATION I WANT ON EVERY NEGATIVE

**MEASURED or INFERRED, in those words.**

## DD4

**Maximize the code the two proofs share, and write it generic.** One rule, two
ends, no metric and no checker.

**This task IS the DD4 question, applied to the phase's own record.** **So the
DD4 section of your report is not a formality: say whether the phase's DD4
accounting, once labelled, still supports the claims the plan makes from it.**

**And answer one thing directly: WHICH AXIS DOES DD4 ITSELF MEAN?** **DD4 says
「the two proofs」. AGENTS.md says「re-instantiation」.** **Read DD4's own text
in `dev/PLAN.md` section 3 and say which axis its words name.** **If DD4 means
Def-against-J, then every `L-VS-AMBIENT` figure in your table answers a
different question than DD4 asked, and the plan should hear that.**

## ARCHIVE (DD18)

- **`agents/tasks/LJ-1-262/lj-1.262-report.md`, section 7, read WHOLE.** **The
  source of the two axes and the object of this sweep.**
- **`agents/tasks/LJ-1-238/lj-1.238-report.md:140-146`**: the residual zero and
  its own INFERRED caveat. **The report that got this RIGHT.**
- **`agents/tasks/LJ-1-225/lj-1.225-report.md:97-99` and `:106`**: the two
  sites where the axes were mixed. **The report that got this WRONG.**
- `agents/tasks/LJ-1-248/`, `LJ-1-227/`, `LJ-1-258/`, `LJ-1-267/`, `LJ-1-268/`,
  `LJ-1-269/`: the figures.
- **`archive/dev/TASKS-archived.md`.** **The retired RUD route answered DD4
  too. Did it name an axis, or is this defect older than this phase?** **Take
  SHAPE from the archive, never a claim.**

**Return an ARCHIVE USED section naming ONE line read per archived file.**

## LITERATURE (DD18)

**`dev/literature/devlin-II5.md:375` and `:387-389` fix the Def-against-J axis
in the literature's own words.** **Read both and say whether Devlin's twelve
rows admit the L-against-ambient axis at all**, or whether that axis is purely
the port's. Return a **LITERATURE USED** section.

## SCOPE (read)

`agents/tasks/LJ-1-262/lj-1.262-report.md` FIRST, whole.

## SCOPE (write)

`agents/tasks/LJ-1-272/` only. **No master, no ledger, no plan, no other
report.**

## MANDATORY RULES

Run `.venv/bin/python scripts/rules.py --for recon` and read every statement.
**The tool prints `Full entry: dev/LESSONS.md:<line>` for every rule and says
THIS IS AN EXCERPT when it truncated. OPEN the full entry for any law you act
on.**

- **C-42.** **A refutation measures the site it names. The centre of this
  task.**
- **D-10.** Price the truth of a recorded residue before pricing its proof.
- **C-22.** Write your deliverable incrementally.
- **P-l.** A judgement at one site is a hypothesis at another.
- **D-26.** A well-founded key on a tower needs generation data, or syntax.
  **D-26 is exactly where the two axes come apart: it is a Def-against-J
  statement.**
- **C-32, C-36, C-38, C-39, C-40, C-43, C-44, C-45. I-5. DD0, DD2, DD4, DD5,
  DD8, DD18, DD24.**

## CONSTRAINTS

- Run `.venv/bin/python scripts/lint-prose.py --check` on your report.
- **No em dash in any language.**
- Evidence is `file:line`. Write ASD-STE100.

## RETURN

**Lead with THE COUNT: how many DD4 figures carry no axis in their own words.**
Then the table, one row per figure with its axis and the `file:line` that
decides it. Then every figure that would say something FALSE if read on the
other axis. Then the answer to which axis DD4's own text names. **Mark every
negative MEASURED or INFERRED.**
