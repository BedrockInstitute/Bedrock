# LJ-1.22: price the counting interaction the fork creates

tier: codex (default)

## GOAL

Price what counting `Code` costs against counting `Formula K 1`, and say
whether the index-type fork makes the wing's ONE measured failure better,
worse, or neutral. **Write no Agda and hold no Agda slot. You price; you do
not build.**

## CWD

`/Users/alsg/Agentic/Bedrock`, on branch `two-tower-bridge`.

## WHY THIS EXISTS, AND WHY IT BLOCKS AN OWNER RULING

The owner is being asked to rule an architecture fork: keep the hull indexed by
`Formula ⟪X⟫ 1`, or move to a meta term algebra `Code`.

- **Keep**: the bridge costs 1.0 to 3.0k lines and 220 to 890 s, 17 to 23x
  DD24's bar. Unaffordable (`_build/lj-1.16-report.md`).
- **Move**: MEASURED at 116 probe lines and 0.0103 s/line, plus about 30 lines
  of named follow-on (`_build/lj-1.18-report.md`).

**One cost is unpriced, and it is the reason the ruling is waiting.**
`[LJ-1.18]` named the countable union at the counting site and explicitly
scoped it out of its miniature. Nobody has priced it, and it lands on the one
part of the wing that has already failed.

## THE INTERACTION, stated precisely

`src/L/StageCardinal.lagda.md:165` counts over **`Formula K 1`**, a single
formula type. Devlin 5.4 counts the hull by counting its index
(`_build/literature/dev2.txt:1357-1360`).

`Code`'s `wit` constructor is
`wit : (k : ℕ) → Formula (⊥*) (suc k) → Vec Code k → Code`, so it ranges over
**every arity**. Counting `Code` therefore looks like a **countable union over
ℕ** of formulas times vectors, which the delivered one-step hull escapes.

**And `[LJ-1.17]` measured the square law, the cardinal arithmetic behind this
counting, at 0.0322 s/line, 2.44x DD24's bar, taking 28 to 42 percent of the
wing's 99.6-to-147.7-second budget.** So if counting `Code` needs MORE
arithmetic than counting `Formula K 1`, the fork worsens the wing's only
measured failure. If it needs the same or less, that objection dies.

## THE HYPOTHESIS I WANT TESTED FIRST, because it may end the task cheaply

**`src/FOL/Count.lagda.md` may already carry the countable union.** I read two
of its exports and neither was written for this:

- `shape-count-inj` at `:211`:
  `Σ[ f ∈ ((k : ℕ) → Formula (⊥* {ℓ}) k → ℕ) ]` with injectivity. **That is an
  injection from parameter-free formulas AT EVERY ARITY into ℕ.**
- `codeByCount` at `:648`:
  `(φ : Formula K 1) (n : ℕ) → countFo φ ≡ n → Σ[ k ∈ ℕ ] (Formula (⊥*) k × Vec K k)`.

**If `shape-count-inj` already gives the arity-indexed half, the marginal cost
of counting `Code` may be small and the objection may be answered by delivered
code.** Test that FIRST and report it plainly either way. `[LJ-1.6]` delivered
`FOL.Count` at 620 lines, 0.0011 s/line, generic in `K` with zero `L` imports.

**Do not assume it works because I found the names.** `[LJ-1.18]` found that
`FOL.Count.encode` is NOT `wit`'s payload, off by one, after a review claimed
it was. D-10: my reading is a residue.

## THE FOUR QUESTIONS

1. **What does counting `Code` need that counting `Formula K 1` does not?**
   State it as a list of obligations, not as an impression.
2. **How much of that is already delivered** in `FOL.Count` and
   `StageCardinal`? Name each at `file:line`.
3. **The marginal price**, in lines and in SECONDS, with its content class
   against P-m's bands. **Seconds are the scarce resource here, not lines.**
4. **The verdict on the interaction**: does the fork make `[LJ-1.17]`'s
   failure better, worse, or neutral? **Answer in those words**, with the
   arithmetic.

## THE SECOND-ORDER QUESTION, and it may matter more

`Code` is an inductive type of the META language. `Formula K 1` is also
meta. **So is counting `Code` actually a HARDER counting problem, or merely a
different one?** A tree of formulas over a countable alphabet may count no
worse than a formula does. **If the two are the same problem in different
clothes, say so; that dissolves the whole objection.**

**Bring the square law into the answer.** `[LJ-1.17]` says the chain needs
`|α × α| = |α|` at every infinite cardinal and limit. Does counting `Code`
need the same law, a weaker one, or a stronger one? A `Vec Code k` is a finite
tuple, and finite tuples over an infinite set usually need only `|ℕ × A| = |A|`.

## DD4, WHICH GOES IN EVERY BRIEF

**Maximize the code the two proofs share, and write it generic.** One rule,
two ends. It has NO metric and no checker by the owner's ruling, so it is
stated in every brief and answered in every return; the repetition is its only
enforcement.

**The fork's DD4 case is already made and you are not re-litigating it.**
`[LJ-1.16-R]` found the obstruction hits BOTH towers, so the blocked shape
buys the definable well-order twice, while the term algebra needs only a meta
well-order both towers have. `[LJ-1.18]` verified `Code`, `val` and `Hull` are
generic in carrier, order and junk.

**Your DD4 question is narrower: does the counting work you price stay
template?** `FOL.Count` is template today, zero `L` imports. **If counting
`Code` would force L-specific content into it, that is a real cost and it
belongs in your verdict.**

## LITERATURE (DD18)

- **`dev/literature/devlin-II5.md` sections 1.4 and 2.5**, Devlin 5.4 and the
  counting step. `_build/literature/dev2.txt:1357-1360` for 5.4 itself.
- **What does Devlin count?** He counts the LANGUAGE `ℒ_X`, which has
  `max(|X|, ω)` many formulas. **Say whether his object is closer to
  `Formula K 1` or to `Code`**, because his one-line proof is the standard the
  tree is trying to match.
- `dev/literature/devlin-II5.md` section 5.2 on II.1.1(vii), the counting half.

Return a **LITERATURE USED** section, with WHY NOT for anything skipped.

## ARCHIVE (DD18)

- **`_build/lj-1.18-report.md`**, which named the countable union and scoped
  it out, and its finding F4 that `encode` is off by one from `wit`.
- **`_build/lj-1.17-report.md`**, the square-law wall and its measured rates.
  `[LJ-1.17-R]` is reviewing it right now and may reframe the arithmetic as
  TEMPLATE content billed to the project rather than to the wing. **Say
  whether your answer changes under that reframing.**
- `_build/lj-1.6-report.md` for what `FOL.Count` and `StageCardinal` deliver,
  and `_build/lj-1.6-review.md` for the quotient argument at the carrier.
- `archive/rud-route/src/L/CardinalCount.lagda.md` (166 in-fence) and
  `L/CardinalPredicates.lagda.md` (399): **the retired route counted
  something. FIND what it counted and cite it at `file:line`.**
- `dev/LESSONS.md` is NOT archived and still binds. **P-m, P-n, P-s and D-10
  decide this block.**

Return an **ARCHIVE USED** section at `file:line`.

## MANDATORY RULES FOR A RECON

From `python3 scripts/rules.py --for recon`. Run it and read each statement.

- **D-10. Price the truth of a recorded residue before pricing its proof.**
  My `shape-count-inj` hypothesis is a residue and so is every figure above.
- **C-22. Write the deliverable incrementally.**
- **P-l. A statement may be ABOUT a concrete stage without dragging that
  stage's PRESENTATION into its type.**
- **D-26. A well-founded key on a tower needs generation data, or it needs
  syntax.** Say whether it bears; counting may sit below that line.

## SCOPE (read)

`src/FOL/Count.lagda.md` at `:211` and `:648` FIRST, then
`src/L/StageCardinal.lagda.md:165`, then `_build/lj-1.18-report.md`, then
`src/L/Hull.lagda.md:248-297`, then the archive.

## SCOPE (write)

`_build/lj-1.22-report.md` only. **No file under `src/` and no file under
`dev/`.**

## CONSTRAINTS

- **Run NO `agda` and NO `make check`.** Two siblings hold the Agda slots.
- **Never commit and never push.**
- **ONE best-effort number per obligation, naming its basis** (DD8).
- **Separate MEASURED from ESTIMATED everywhere.**
- **Evidence is `file:line`.**
- **A finding that the objection dissolves is the BEST outcome** and it is
  worth as much as a price. Say it plainly if you find it.
- Write ASD-STE100 in the report.

## RETURN

Write `_build/lj-1.22-report.md` INCREMENTALLY, skeleton first.

1. **THE VERDICT**, first line: better, worse, or neutral for `[LJ-1.17]`'s
   failure, with the arithmetic.
2. **DOES `shape-count-inj` ALREADY GIVE IT?** answered first.
3. **THE OBLIGATIONS** counting `Code` adds, as a list.
4. **THE MARGINAL PRICE**, lines and SECONDS, with the content class.
5. **WHICH CARDINAL LAW** counting `Code` needs, against the square law.
6. **IS IT THE SAME PROBLEM IN DIFFERENT CLOTHES?**
7. **DOES IT STAY TEMPLATE?** (DD4.)
8. **UNDER `[LJ-1.17-R]`'s POSSIBLE REFRAMING**, does your answer change?
9. **LITERATURE USED.**
10. **ARCHIVE USED.**
11. **WHAT I AM NOT SURE OF.**
