# LJ-1.341: are `envK` and `defPairK` TRUE as stated?

tier: opus (in-harness-subagent-mode), the switch's DEFAULT row. I ran
`scripts/dispatch/dispatch_policy.py` before writing this line.

## D-10 IS THE WHOLE TASK

**Price the TRUTH of a recorded residue before pricing its proof.**

**`[LJ-1.338]` measured the seven's ambient tie supply at 327 lines and then
flagged that 51 of those lines STATE a residue nothing proves, and that TWO of
the ties may be FALSE:**

> **`envK` and `defPairK` may be FALSE as stated: both quantify over `z` with
> no bounding hypothesis and conclude a set built over `z` is inside the
> bound.** **INFERRED, by reading `src/L/Condensation.lagda.md:7183-7186`; I
> built no counterexample.**

**I read both. They are, verbatim:**

```agda
(envK : (E z : S) → ⟨ (E ∷ z ∷ γ) ⊨ envOneAt zero (suc zero) ⟩
       → ⟨ fst E ∈ fst (lookup (suc (suc (suc K))) γ) ⟩)
(defPairK : (E z w' : S) → ⟨ (w' ∷ E ∷ z ∷ γ) ⊨ tagAtL zero 0 (suc (suc zero)) ⟩
           → ⟨ fst w' ∈ fst (lookup (suc (suc (suc K))) γ) ⟩)
```

**`z` is universally quantified and appears in no conclusion. Nothing bounds
it.**

## AND NOBODY HAS EVER MET THEM

**`LeafAgree` has ZERO consumers in `src/`. MEASURED by `[LJ-1.338]`.** **So
these two hypotheses have never been discharged by anything, and their truth has
never been tested.**

**That is the exact shape D-10 exists for: a residue that was recorded, carried
forward, and priced, without anyone asking whether it is true.**

## THE QUESTION

**Are `envK` and `defPairK` true? If not, what is the right statement?**

## THE THREE OUTCOMES, and each is a full answer

1. **TRUE.** **Then say WHY the satisfaction hypothesis bounds `z` implicitly**,
   at `file:line`, and the 327 stands. **A term is better than an argument.**
2. **FALSE.** **Give the countermodel.** **Then 51 of the 327 lines are pricing
   a false statement, `LeafAgree`'s telescope needs restating, and the tie
   figure is wrong.** **This is the most valuable outcome and it is why the task
   is funded.**
3. **TRUE BUT ONLY UNDER AN EXTRA HYPOTHESIS.** **Name the hypothesis and say
   what it costs at the four sites `LeafAgree` hands its ties to.**

## WHERE TO LOOK FIRST

**The satisfaction premise is the only thing that could bound `z`.** Read
`envOneAt` and `tagAtL` whole and ask: **does satisfying them at an environment
containing `z` force `z` into anything?** **`[LJ-1.338]` did not do that
reading; it read the telescope only.**

**And check the L side.** `[LJ-1.338]` measured that **`module KValue` at
`src/L/Condensation.lagda.md:7264-7318` discharges the upward ties at the L
class and has ZERO consumers anywhere in `src/`, including its own chapter.**
**If `KValue` proves anything of this shape, the L side already knows the
answer.** **The L side built the value and never wired it.**

## THE ABORT CRITERION, fixed BEFORE the run (D-1)

- **A COUNTERMODEL.** **Build it, report it, STOP.** The tie figure and the
  telescope both move.
- **A TERM PROVING THEM.** **Report it and the 327 is confirmed.**
- **THE SATISFACTION PREMISE DOES BOUND `z`, and you show how.** Same as above,
  but say which conjunct does the work.
- **IT CANNOT BE SETTLED WITHOUT THE MISSING CONSUMER.** **`LeafAgree` has no
  consumer, so its intended use is not visible.** **If that blocks you, say so:
  a hypothesis whose intended use nobody can see is a design question and not a
  proof one.**
- **A WALL.** 30 minutes on one invocation is a wall: interrupt, report ELAPSED
  SECONDS, bisect. **NEVER raise the cap.**

## WHAT YOU MUST NOT DO

- **LAND NOTHING. This is a probe.** Write and run only in
  `agents/tasks/LJ-1-341/`. **`src/` is forbidden** (I-5).
- **Do not restate `LeafAgree` in `src/`.** **If it needs restating, say what to
  and STOP: that is the orchestrator's, and DD23 freezes mathematical prose.**
- **Do not edit another task directory.** You may READ and RE-RUN the probes in
  `agents/tasks/LJ-1-338/`, `LJ-1-336/` and `LJ-1-302/`.
- **COUNT THE AGDA SLOTS BEFORE EVERY INVOCATION.** C-12 caps this machine at
  TWO and a sibling is live. Use exactly:
  ```sh
  ps aux | awk '/libexec.*bin\/agda/ && !/awk/' | wc -l
  ```
  **The two obvious alternatives both OVER-COUNT, MEASURED 2026-08-15.**
- **ONE agda process, `GHCRTS="-A64m -I0 -M8g"`, cap NEVER raised.** Report the
  load beside every figure.
- **RUN A NEGATIVE CONTROL that MEASURES.** **`[LJ-1.338]` ran three and one of
  them tested NON-VACUITY specifically, which is exactly the risk here: a tie
  can be「provable」because nothing inhabits its premise.**
- **Never commit, never push**, never `git checkout .`, `git stash`,
  `git reset --hard` or `git clean`. Do not run `make check`.
- **Create `agents/tasks/LJ-1-341/lj-1.341-report.md` in your FIRST five
  minutes** (C-22).
- Run `.venv/bin/python scripts/gate/lint-prose.py --check` and
  `.venv/bin/python scripts/gate/lint-agda.py --check` on what you write. **No
  em dash in any language.** DD23 freezes mathematical prose in `src/`.
- Evidence is `file:line`. Write ASD-STE100. Mark every negative **MEASURED**
  or **INFERRED**, in those words.

## C-57, WRITTEN YESTERDAY FROM THIS CHAIN

**A search that RETURNS the answer and a reading that DISCARDS it are two
different failures, and the second is invisible.** **Say how many hits you read
and name the ones you rejected.** **On this leg that failure cost three briefs
and one funded task.**

## THE PREMISE OF MINE MOST LIKELY TO BE WRONG

**Seven of my last thirteen briefs carried a claim an agent measured FALSE.**
**The one at risk: 「nothing bounds `z`」.** **That is my reading of four lines
and `[LJ-1.338]`'s, and NEITHER of us read `envOneAt` or `tagAtL`.** **Read
them first; the bound may be inside the formula.**

## THE RULES

**D-10** is the task. **C-45: `exit 0` is not a supply, and a hypothesis that
typechecks says nothing about its truth.** **C-36, C-42, C-44, C-57, P-l,
C-22, C-32, C-39, C-40.** I-5. **D-1, D-26.**
**DD0, DD4, DD8, DD18, DD23, DD24.**

Run `.venv/bin/python scripts/dispatch/rules.py --for probe` and read every
statement, opening the full entry for any law you act on.

## DD4

**Maximize the code the two proofs share, and write it generic.** One rule, two
ends, no metric and no checker. **NAME YOUR AXIS** (C-46), which is
AC-against-GCH, fixed at `scripts/measure/ledger.py:50`.

**`[LJ-1.338]` measured that on the L-against-ambient axis the paid instance is
now 5,626 copied lines for 114 hand-written.** **If these two ties are false,
that figure includes lines pricing a false statement.** **Say what your answer
does to it.**

## ARCHIVE (DD18)

- **`agents/tasks/LJ-1-338/lj-1.338-report.md`, read WHOLE.** It funds you and
  its section on the third kind of debt is your subject.
- **`agents/tasks/LJ-1-336/lj-1.336-report.md`**, the downward and upward debts.
- **`archive/dev/TASKS-archived.md`**, taking SHAPE and never a claim: the
  retired route carried unbounded hypotheses too. **Say what would not
  transfer.**

**Return an ARCHIVE USED section naming ONE line read per archived file.**

## LITERATURE (DD18)

**`dev/literature/devlin-II5.md`.** **Devlin's bounded formulas bound every
quantifier by construction.** **Say in one line whether his corresponding step
has an unbounded variable at all**, because if it does not, the answer may be
that this telescope is a port artefact rather than a mathematical claim. Return
a **LITERATURE USED** section.

## SCOPE (read)

`src/L/Condensation.lagda.md:7183-7186` and then `envOneAt` and `tagAtL` WHOLE,
FIRST.

## SCOPE (write)

`agents/tasks/LJ-1-341/` only.

## RETURN

**Lead with ONE word: TRUE, FALSE or NEEDS-A-HYPOTHESIS.** Then the term or the
countermodel at `file:line`. Then whether the satisfaction premise bounds `z`,
and which conjunct if so. Then what `KValue` knows, given it has zero consumers.
Then what the 327 becomes. Then your negative control, non-vacuity included.
**Mark every negative MEASURED or INFERRED.**
