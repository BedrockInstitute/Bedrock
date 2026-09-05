# LJ-1.345: DD25 adversarial review of `[LJ-1.341]`'s vacuity claim

tier: pi (in-harness-subagent-mode), **the switch's ADVERSARIAL row.** I ran
`scripts/dispatch/dispatch_policy.py` before writing this line. `[LJ-1.341]` was
authored **in-harness by opus**, this mode's DEFAULT row, so the adversarial row
is `herdr` / `pi` / `glm-5.3` and DD17's invariant holds: the critic is not the
author.

## WHY THIS REVIEW EXISTS, and the reason is a lapse of mine

**`[LJ-1.341]` returned FALSE: two hypotheses of two delivered modules are false
and their types are EMPTY.** **DD25 requires a negative return to be
adversarially reviewed IMMEDIATELY.**

**I did not review it. I dispatched a REPAIR and LANDED it in `src/`.**
`src/L/Condensation.lagda.md` now carries 20 insertions and 7 deletions made on
the strength of an unreviewed refutation. **`make check` caught the lapse
through `check-dd25-review-named.py`, which is that gate's declared purpose.**

**So this review runs against a claim the tree has already acted on.** **If the
refutation is wrong, a delivered chapter has been edited on a false premise and
that must be found now.**

## THE CLAIM

**Instantiate `z` with the BOUND ITSELF, the set the conclusion names. Nothing
forbids it.** Then

- `defPairK` asserts `pr (# 0) b ∈ b`, a three-step membership cycle;
- `envK` asserts `{pr (# 0) b} ∈ b`, a four-step one;

**and `regularityV` at `src/V/Hierarchy.lagda.md:139-144` refutes both.**

Terms: `agents/tasks/LJ-1-341/ProbeTies341.agda:185-190` and `:231-238`.
Controls restating the chapter's own two types VERBATIM at both index forms:
`ControlA341.agda:54-91`, all four discharged into `⊥`.

## WHAT TO ATTACK, in order

**1. THE INSTANTIATION.** **Is `z := b` really admissible?** The whole
refutation is one substitution. **Check the telescope's own binders: is `z`
genuinely unconstrained at the point of use, in BOTH modules, at BOTH index
forms?** **If any earlier parameter constrains it, the countermodel evaporates.**

**2. NON-VACUITY, which the target answered TWICE and you must re-check.** It
claims `ProbeTies341.agda:180-182` and `:208-229` INHABIT both premises at the
refutation's own witnesses. **If a premise is empty, the「refutation」refutes
nothing and the hypothesis is merely unusable rather than false.** **That
distinction changes what the repair means.**

**3. THE REPAIRED STATEMENT, which is now IN THE TREE.** `[LJ-1.343]` landed it:
`z` is bounded by the CARRIER slot rather than the bound slot, and it measured
that the needed hypothesis and the available one are ONE type, by passing it
through the identity function both ways. **Re-run that.** **And ask the harder
question: is the REPAIRED statement the one the call sites actually need, or
merely one that typechecks?** **C-45 is the law of this whole episode.**

**4. THE EXTENT.** `[LJ-1.341]` swept and reported the count is **TWO**, and
named them. **`[LJ-1.343]` then found the stale-copy count was 38 where my brief
said two.** **So one of these agents' sweeps was narrow. Re-run the extent sweep
over the seven modules and say whether two is right.**

**5. THE LITERATURE READING.** It claims Devlin binds every quantifier by the
concrete set, so his corresponding step has NO unbounded variable, and that our
telescope lost the binder in the port. **Check that against
`dev/literature/devlin-II5.md:245-250`.** **If true, the repair puts the bound
back where the mathematics has it, which is the strongest evidence the repair is
right.**

## THE ABORT CRITERION, fixed BEFORE the run (D-1)

- **THE REFUTATION HOLDS.** **UPHOLD**, and say which of the five attacks came
  closest. The landed repair stands.
- **THE INSTANTIATION IS INADMISSIBLE.** **OVERTURN, and say so immediately.**
  **A delivered chapter has then been edited on a false premise and the edit
  must be reverted.** **This is the outcome the gate exists to catch.**
- **THE PREMISES ARE EMPTY.** **SPLIT**: the hypotheses are unusable but not
  false, and the repair is still an improvement for a different reason. **Say
  which reason.**
- **THE REPAIRED STATEMENT IS WRONG.** **Then the tree is worse than before and
  that is urgent.**
- **A WALL.** A single `agda` invocation past 30 MINUTES is a wall: interrupt,
  report ELAPSED SECONDS, bisect. **NEVER raise the cap.** **The chapter itself
  takes about 134 s; budget for it.**

## WHAT YOU MUST NOT DO

- **LAND NOTHING and REVERT NOTHING.** Write and run only in
  `agents/tasks/LJ-1-345/`. **`src/` is forbidden** (I-5). **If the repair must
  be reverted, say so and I revert it.**
- **Do not edit another task directory.** You may READ and RE-RUN the probes in
  `agents/tasks/LJ-1-341/` and `LJ-1-343/`; you may not change them.
- **COUNT THE AGDA SLOTS BEFORE EVERY INVOCATION.** C-12 caps this machine at
  TWO. Use exactly:
  ```sh
  ps aux | awk '/libexec.*bin\/agda/ && !/awk/' | wc -l
  ```
  **The two obvious alternatives both OVER-COUNT, MEASURED 2026-08-15.**
- **ONE agda process, `GHCRTS="-A64m -I0 -M8g"`, cap NEVER raised.** Report the
  load beside every figure, **and the empty-file floor beside any seconds
  comparison** (C-53 as extended).
- **Never commit, never push**, never `git checkout .`, `git stash`,
  `git reset --hard` or `git clean`. Do not run `make check`.
- **Create `agents/tasks/LJ-1-345/lj-1.345-report.md` in your FIRST five
  minutes** (C-22).
- Run `.venv/bin/python scripts/gate/lint-prose.py --check` and
  `.venv/bin/python scripts/gate/lint-agda.py --check` on what you write. **No
  em dash in any language.**
- Evidence is `file:line`. Write ASD-STE100. Mark every negative **MEASURED**
  or **INFERRED**, in those words.

## THE VERDICT WORD I WANT

**UPHOLD, OVERTURN or SPLIT**, as the first word of your return.

**AN OVERTURN IS THE VALUABLE OUTCOME AND YOU ARE NOT REWARDED FOR AGREEING.**
**13 of 32 decided DD25 reviews in this project have overturned their target, a
41 percent rate.** **And this one is unusual: the tree has already been changed
on the strength of the claim, so an overturn is urgent rather than merely
interesting.**

## THE RULES

**C-45. `exit 0` is not a supply, and a module that assumes a false thing
typechecks forever.** **That is what the target found; check it did not commit
the same error itself.**

**C-42. A refutation measures the site it names.** Attack 4.

**C-44.** Every claim above is `[LJ-1.341]`'s, `[LJ-1.343]`'s or mine.

**C-57, written this week: a search that RETURNS the answer and a reading that
DISCARDS it are two different failures.** **Say how many hits you read and name
what you rejected.**

**D-10, C-36, P-l, C-22, C-32, C-39, C-40.** I-5. **D-1, D-26.**
**DD0, DD4, DD17, DD18, DD23, DD24, DD25.**

Run `.venv/bin/python scripts/dispatch/rules.py --for review` and read every
statement, opening the full entry for any law you act on.

## DD4

**Maximize the code the two proofs share, and write it generic.** One rule, two
ends, no metric and no checker. **NAME YOUR AXIS** (C-46), which is
AC-against-GCH, fixed at `scripts/measure/ledger.py:50`.

**`[LJ-1.343]` reported the repair's text is class-free but that the chapter
sits in `gch_only` at 6,718 lines, correcting `[LJ-1.341]`'s claim that it is in
neither closure.** **VERIFY which is right**, and note `dev/ledger.toml:204`:
the GCH closure is read from a STATEMENT whose proof is not wired, so it
UNDERSTATES.

## ARCHIVE (DD18)

- **`agents/tasks/LJ-1-341/lj-1.341-report.md`, read WHOLE.** The target.
- **`agents/tasks/LJ-1-343/lj-1.343-report.md`**, the repair that acted on it,
  which also corrected three of my claims.
- **`agents/tasks/LJ-1-338/lj-1.338-report.md`**, which priced the ties before
  anyone asked whether they were true.
- **`archive/dev/TASKS-archived.md`**, taking SHAPE and never a claim.

**Return an ARCHIVE USED section naming ONE line read per archived file.**

## LITERATURE (DD18)

**`dev/literature/devlin-II5.md:245-250`**, which is attack 5 and may be the
strongest evidence either way. Return a **LITERATURE USED** section.

## SCOPE (read)

`agents/tasks/LJ-1-341/ControlA341.agda:54-91` FIRST: it restates the delivered
types verbatim and is the shortest path to judging the claim.

## SCOPE (write)

`agents/tasks/LJ-1-345/` only.

## RETURN

**Lead with ONE word: UPHOLD, OVERTURN or SPLIT.** Then attack 1, whether the
instantiation is admissible, which is the whole refutation. Then non-vacuity,
re-checked. Then whether the LANDED repaired statement is what the call sites
need. Then the extent sweep. Then the Devlin reading. **Mark every negative
MEASURED or INFERRED.**
