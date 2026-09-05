# LJ-1.354: DD25 review of `[LJ-1.351]`'s `graphWitK` refutation

tier: pi (in-harness-subagent-mode), **the adversarial row of the mode
`[LJ-1.351]` was dispatched under.** `[LJ-1.351]` was authored in-harness by
opus, so **DD17's invariant holds: the critic is not the author.** **A review
takes the mode its TARGET was dispatched under** (owner's ruling, 2026-08-15).

> **CORRECTED IN PLACE 2026-08-16, and only the tier line.** As dispatched this
> line read `tier: pi (pi-subagent-mode)` and called `pi` BOTH the adversarial
> row and today's default. **The HEAD was right and the MODE NAME was wrong.**
> The mode flipped to `pi-subagent-mode` at 08:50 and this task went out at
> 08:53, so「today's default」was accurate; but under `pi-subagent-mode` the
> adversarial row is `opus`, so naming that mode contradicted the head the same
> line carried. `check-dispatch-policy.py` judges a brief by the mode it NAMES,
> and it went red on exactly that contradiction. The mode this review actually
> ran under is its TARGET's, `in-harness-subagent-mode`, whose adversarial row
> IS `pi`. **Nothing about the dispatch changed; the record now says which row
> was taken.** Same remedy as `[LJ-1.318]`.

## WHY

**`[LJ-1.351]` returned FALSE.** DD25 requires the review immediately. **The
gate flagged the row and I let the gate rule rather than deciding myself**,
because I skipped this once this session and `make check` caught it after a
repair had landed.

**This is the FOURTH of six construction ties to come back false.** **At that
point the family is a route-level fact, and a wrong verdict in it is expensive.**

## THE CLAIM

`agents/tasks/LJ-1-351/Refute351.agda`, **exit 0 in 12.38 s**, floor 0.90 s.

- **All FIVE conjuncts of `graphWitK`** (`src/L/Condensation.lagda.md:7288-7297`)
  **are inhabited by a closed term** at `:364-370`.
- **The first conclusion `d ∈ K` is refuted** at `:408-412`.
- **VACUOUS is ruled out, MEASURED**: eleven of twelve clauses are vacuous
  because `closedAt` speaks only at tags 2, 3, 4, 5, 8, 9, 10 and 11, **but the
  twelfth, `botClauseAt` at tag 7, is NOT vacuous and is discharged by a real
  term** at `:299-308`.
- **The countermodel is「a one-entry satisfaction table and correct
  mathematics」**: the code of the constant `bot`, given its TRUE value.

## WHAT TO ATTACK

**1. NON-VACUITY, which is this chain's pivot every time.** It claims FOUR
layers, including `module Wire` at `:476-504` running the whole thing on
`KValue.facts`, **the chapter's only `KFacts` value, with NO extra hypothesis**,
unlike a sibling's which needed one. **Verify that; a premise inhabited only
under an extra assumption is a weaker result.**

**2. THE THREE-INSTANCE CONTROL.** `module Point` takes the arity and the
payload; at one pair the premise is inhabited and the conclusion **HOLDS**, at
two others it is **REFUTED**, one argument apart in one file. **That is the
standard this week set. Check it holds.**

**3. THE CLAIM THAT THE DELIVERED BOUND DOES NOT CLOSE IT.** **My brief's
premise was that `arityNumAtL` might close this tie as it closed a sibling's.**
**It says MEASURED FALSE by a term, with the reason: `[LJ-1.350]`'s tie failed
at an ARITY conjunct and `graphWitK` has none, its three conclusions being
memberships.** **Check the reason, not just the term.**

**4. THE SWEEP.** It reports **one statement at two sites**, `:7009-7018` and
`:7288-7297`, **not a family.** **Re-derive that: three sweeps on this chain
have been measured short.**

**5. THE WORD.** `[LJ-1.349]` ruled that a sibling's「MEASURED FALSE」was right
but needed the qualifier「no uniform supplier」. **Say whether this one needs a
qualifier too, or whether the closed premise makes it unqualified.**

## THE ABORT CRITERION (D-1)

- **UPHOLD.** Then four of six are false and the family is a route-level
  finding.
- **OVERTURN.** **Nothing has been landed on it, so an overturn costs only the
  task.** Say it plainly.
- **SPLIT.** Likeliest on the word or the sweep.
- **A WALL.** **C-58: replace a numeral pattern-match split with the library
  eliminator first.** The target honoured it and never walled.

## CONSTRAINTS

- **LAND NOTHING, REPAIR NOTHING.** Write only in `agents/tasks/LJ-1-354/`.
  **`src/` is forbidden** (I-5).
- **Two sibling probes are EXPECTED RED and documented.** Repair neither.
- **Chapter line numbers have DRIFTED.** Re-derive every citation (C-44).
- **The public pair access is `ChainZ` in the chapter**; four tasks have now
  measured it. **Do not re-write those four lines.**
- **COUNT THE AGDA SLOTS** before every invocation, exactly:
  `ps aux | awk '/libexec.*bin\/agda/ && !/awk/' | wc -l`. **Both obvious
  alternatives OVER-COUNT, MEASURED.** A sibling is live.
- **ONE agda process, `GHCRTS="-A64m -I0 -M8g"`, cap NEVER raised.** **Report
  the empty-file floor beside any seconds figure** (C-53 as extended).
- **Never commit, never push**, never `git checkout .`, `git stash`,
  `git reset --hard` or `git clean`. Do not run `make check`.
- **Create `agents/tasks/LJ-1-354/lj-1.354-report.md` in your FIRST five
  minutes** (C-22).
- Run `.venv/bin/python scripts/gate/lint-prose.py --check` and
  `.venv/bin/python scripts/gate/lint-agda.py --check`. **No em dash.**
- Evidence is `file:line`. ASD-STE100. Mark every negative **MEASURED** or
  **INFERRED**, in those words.

## THE VERDICT WORD

**UPHOLD, OVERTURN or SPLIT**, first word. **13 of 32 decided DD25 reviews here
have overturned, 41 percent. You are not rewarded for agreeing.**

## THE RULES

**C-45, C-42, C-44, C-57, C-58, C-53, C-36, D-10, P-l.**
**C-12, C-22, C-32, C-39, C-40.** I-5. **D-1, D-26.**
**DD0, DD4, DD17, DD18, DD24, DD25.**

Run `.venv/bin/python scripts/dispatch/rules.py --for review` and read every
statement, opening the full entry for any law you act on.

## DD4

**Maximize the code the two proofs share, and write it generic.** One rule, two
ends, no metric and no checker. **NAME YOUR AXIS** (C-46), fixed at
`scripts/measure/ledger.py:50`. **Say whether the refutation is class-free, as
its three siblings were, so the falsity holds at both carriers by one file.**

## ARCHIVE (DD18)

- **`agents/tasks/LJ-1-351/lj-1.351-report.md`, read WHOLE.** The target.
- **`agents/tasks/LJ-1-349/lj-1.349-report.md`**, the review that commissioned
  it and set the non-vacuity standard.
- **`agents/tasks/LJ-1-350/lj-1.350-report.md`**, whose bound the target
  measured does NOT transfer here.
- **`archive/dev/TASKS-archived.md`**, taking SHAPE and never a claim.

**Return an ARCHIVE USED section naming ONE line read per archived file.**

## LITERATURE (DD18)

**`dev/literature/devlin-II5.md`.** **Say in one line whether a tie of this
shape has any counterpart in his text.** Return a **LITERATURE USED** section.

## SCOPE (read)

`agents/tasks/LJ-1-351/Refute351.agda:299-308` FIRST: the non-vacuous twelfth
clause is what separates FALSE from VACUOUS.

## SCOPE (write)

`agents/tasks/LJ-1-354/` only.

## RETURN

**Lead with ONE word: UPHOLD, OVERTURN or SPLIT.** Then non-vacuity, all four
layers. Then the three-instance control. Then whether the delivered bound really
cannot close it, and the reason. Then the sweep, re-derived. Then whether the
verdict word needs a qualifier. **Mark every negative MEASURED or INFERRED.**
