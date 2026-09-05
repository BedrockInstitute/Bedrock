# LJ-1.270: why the Coq reification framework is unused on the AC side, and whether it still says nothing to GCH

tier: pi (deepseek-subagent-mode), **model `deepseek-v4-flash`**: this task
runs NO Agda, holds no slot, and is natural-language investigation over
documents. **The model rule gives flash and I take it.** The clock selected the
mode.

## GOAL

**The owner asks three questions:**

1. **Why is the Coq reification framework that the antecedent development
   referenced NOT used on Bedrock's AC side?**
2. **Why was it not needed?**
3. **Does it have no reference value for the GCH side either?**

**Questions 1 and 2 have a recorded answer and question 3 may not. Find out
which.**

## THE DOCUMENT THAT ALREADY ANSWERS MOST OF THIS

**`../fol-reification/docs/governance/METAZF-REVIEW.md`** is a full comparison
of MetaZF, the Coq development, against the antecedent project. **It was
settled on 2026-06-15 by a fourteen-agent workflow, source line by source
line**, and `../fol-reification/docs/governance/GOAL-DRIVEN-DECISIONS.md:5`
records the ruling in seven numbered points.

**Read both, whole, before you write anything.**

**Its verdict on questions 1 and 2, in its own words:「架构已验证,无需重写」**,
with a per-item table of where cubical wins: `℩` over `δ`, hProp membership
over `ProofIrrelevance`, `foundationV` over the regularity axiom, `∈-asFiber`
plus `identityPrinciple` over classical `iota`, `_↾_` over `proof_irrelevance`
Σ-carriers, SIP over hand-proved bisimulation.

**And it lists EIGHT things not to borrow, and four that are transferable but
deferred.** **Report both lists.**

## THE LINE THAT BEARS ON QUESTION 3, and it is the reason this task exists

**`GOAL-DRIVEN-DECISIONS.md:5`, point ⑤, says:**

> **MetaZF 沉默处=一阶核心(无 `Formula` 层):无界 φ 反射、序数↔数码⊆、凝聚
> Σ₁-绝对——全是我们的活。**

**MetaZF has NO `Formula` layer at all.** **So exactly the three things the GCH
side is doing today are exactly where it is silent.**

**BUT THAT VERDICT IS DATED 2026-06-15 AND IT WAS WRITTEN ABOUT THE RETIRED
RUD ROUTE.** **Bedrock's route changed to the two-tower bridge, and the GCH
wing has been built since.** **So question 3's real form is: does that silence
still hold, or has the GCH side grown a part MetaZF DOES speak to?**

## WHAT BEDROCK'S GCH SIDE ACTUALLY DOES TODAY, so you can test the silence

- **A first-order syntax layer**, `src/FOL/Syntax.lagda.md`, with `Formula K n`
  and de Bruijn variables `var : Fin n → Term K n` at `:44`.
- **Five manipulation files**, `src/FOL/Manipulation/`: `Renaming.lagda.md`
  163 lines, `Relabelling.lagda.md` 260, `Bounding.lagda.md` 248,
  `Parameters.lagda.md` 484, `Relativize.lagda.md` 177. **I counted those.**
- **A coding layer**, `src/L/Coding/`, that turns formulas into sets.
- **Condensation with Σ₁ absoluteness**, `src/L/Condensation.lagda.md`.

**Those are the four the review's point ⑤ says MetaZF is silent on. Check that
against MetaZF itself, not against the review's summary of it.**

## THE THREE QUESTIONS TO ANSWER

**1. WHY UNUSED ON AC.** Summarise the recorded verdict, at `file:line`, and
say whether anything has changed since 2026-06-15 that would reopen it.

**2. WHY NOT NEEDED.** **The per-item table is the answer and it is
measured.** **Report it, and say plainly whether each item is a REAL win or a
preference.**

**3. DOES IT BEAR ON GCH.** **This is the one that may not be answered.**
**Test the silence: does MetaZF have anything that speaks to a `Formula`
layer, to de Bruijn slot handling, or to satisfaction coding?** **If it does
not, say so and the question closes for good. If it does, name it at
`file:line` and say what it would buy.**

## THE ABORT CRITERION, fixed BEFORE the run (D-1)

- **THE SILENCE HOLDS.** MetaZF has no `Formula` layer and nothing that bears
  on Bedrock's GCH work. **Then question 3 is answered NO, with evidence, and
  the project can stop wondering.** STOP.
- **THE SILENCE DOES NOT HOLD.** **Name what MetaZF has, at `file:line`, and
  say what it would buy.** **That is the most valuable outcome here.**
- **THE 2026-06-15 VERDICT IS STALE ON THE AC SIDE.** **If the route change
  reopened something the review closed, say which item.**
- **THE FOUR DEFERRED TRANSFERABLES ARE STILL OWED.** The review lists
  `adj`, a `defSet≡target` reuse lemma, a `hasInfinity` round trip, and an
  intersection reserve. **Say whether Bedrock took any of them, and whether
  any still applies.**

## WHAT YOU MUST NOT DO

- **DO NOT RUN AGDA.** Two siblings hold both Agda slots (C-12).
- **Do not copy code from the sibling repository.** **Read it, cite it, and
  report what it says.** **The antecedent development is the owner's and
  copying from it is not this task's business.**
- **Do not edit anything in `../fol-reification/`.** **It is a separate
  checkout and read-only to you.**
- **Do not edit any Bedrock master, brief or report.** **Write your own report
  and nothing else.**
- **Do not touch `agents/tasks/LJ-1-266/` or `LJ-1-269/`.** Siblings are live.
- **Create your report file in your FIRST five minutes (C-22).**
- Never commit, never push, never `git checkout .`, `git stash`,
  `git reset --hard` or `git clean`.
- Do not run `make check`; the orchestrator runs it.

## WRITE FOR A READER WHO HAS NOT READ EITHER REPOSITORY

**Your reader is the orchestrator and then the owner.** **The owner knows both
repositories; I do not know MetaZF at all.** **So say what a thing IS before
you say whether it transfers.**

## FIVE RULES THIS CHAIN EARNED

**DERIVE A FIGURE OR DO NOT WRITE IT** (C-44). **The line counts above are
mine and I ran them; everything else in this brief is the review's and I have
re-derived none of it.**

**THE ARCHIVE BEARS UNTIL YOU OPEN IT.** **Three times this week a report
called absent what a repository held.**

**A DATED VERDICT IS A CLAIM ABOUT ITS OWN DATE.** **2026-06-15 predates the
route change.**

**CARRY A CLAIM'S QUALIFIER OR CARRY NEITHER.**

**AN ESCAPE HATCH IS THE SHAPE A WRONG CHOICE HIDES IN** (C-43). **「It was
already decided」is that shape if the decision was about a different route.**

## THE CLASSIFICATION I WANT ON EVERY NEGATIVE

**MEASURED or INFERRED, in those words.**

## DD4

**Maximize the code the two proofs share, and write it generic.** One rule, two
ends, no metric and no checker.

**MetaZF is a THIRD development beside Bedrock's two towers.** **So the DD4
question here is unusual and worth one paragraph: does MetaZF's architecture
suggest anything about sharing between Def and J that Bedrock has not
considered?** **The review says MetaZF's layer comparison rests on `幂单调`,
power-set monotonicity, which the `𝒟` step does NOT have.** **Say whether that
difference bears on the two-tower bridge at all.**

## ARCHIVE (DD18)

- **`../fol-reification/docs/governance/METAZF-REVIEW.md`, read WHOLE.**
- **`../fol-reification/docs/governance/GOAL-DRIVEN-DECISIONS.md:5`**, the
  seven-point ruling.
- `../fol-reification/docs/WORKLOG.md`: `dev/STYLE-agda.md:264` cites its
  section 5 as the source playbook, so Bedrock already borrows from it.
- **`dev/PLAN.md:28-29`**: Bedrock's own record of the sibling checkout and its
  pinned commit.
- **`archive/dev/DECISIONS-archived.md` and `archive/dev/TASKS-archived.md`**:
  **the RUD route the 2026-06-15 verdict was written about.** **Take SHAPE from
  the archive, never a claim.**

**Return an ARCHIVE USED section naming ONE line read per file.**

## LITERATURE (DD18)

**Say in one line whether Devlin or any source in `dev/literature/` bears on
the choice between a `Formula` layer and a `Formula`-free second-order
presentation.** Return a **LITERATURE USED** section.

## SCOPE (read)

`../fol-reification/docs/governance/METAZF-REVIEW.md` FIRST, whole.

## SCOPE (write)

`agents/tasks/LJ-1-270/` only. **No master, no ledger, no plan, no sibling
repository.**

## MANDATORY RULES

Run `.venv/bin/python scripts/rules.py --for recon` and read every statement.
**The tool prints `Full entry: dev/LESSONS.md:<line>` for every rule and says
THIS IS AN EXCERPT when it truncated. OPEN the full entry for any law you act
on.**

- **D-10.** Price the truth of a recorded residue before pricing its proof.
  **A dated verdict is exactly that kind of record.**
- **C-44.** A brief's claim is unchecked until you check it.
- **C-32.** A cure invalidates every downstream measurement. **The route change
  is the cure here.**
- **P-l.** A judgement made for one route is a hypothesis for another.
- **D-26.** A well-founded key on a tower needs generation data, or syntax.
  **MetaZF's absence of a `Formula` layer is D-26's other horn.**
- **C-22, C-36, C-38, C-39, C-40, C-42, C-43, C-45. I-5. DD0, DD2, DD5, DD8,
  DD18, DD24.**

## CONSTRAINTS

- Run `.venv/bin/python scripts/lint-prose.py --check` on your report.
- **No em dash in any language.**
- Evidence is `file:line`. Write ASD-STE100.

## RETURN

**Lead with ONE word on question 3: does MetaZF bear on Bedrock's GCH side,
YES or NO.** Then questions 1 and 2 with the recorded verdict and whether it is
stale. Then the eight not-to-borrow items and the four deferred transferables,
with whether Bedrock took any. Then the DD4 paragraph on power-set
monotonicity. **Mark every negative MEASURED or INFERRED.**
