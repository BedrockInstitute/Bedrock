# LJ-1.72: repair TwelveAgree's telescope, and prove it by consuming it

tier: codex (default)

## GOAL

`TwelveAgree`'s telescope is unsatisfiable, so the module is vacuous. **Fix
the statement, then instantiate it at `SatGraphAgree`'s frame.** The
instantiation is the acceptance test; nothing else is.

## CWD

`/Users/alsg/Agentic/Bedrock`, on branch `two-tower-bridge`, **clean at
`61c499c`**. There are no working-tree edits.

## THE DEFECT, machine-checked and re-verified by me

`src/L/Condensation.lagda.md:6415`:

```agda
(tagEq : (k : ℕ) (N : Fin (11 + n)) → fst (lookup N γ) ≡ fst (numeralL k))
```

**Every slot equals every numeral.** Take `k = 0` and `k = 1` at one slot and
you have `numeralL 0 ≡ numeralL 1`, refuted by the delivered `numeralL-inj`
(`src/L/Coding/Model.lagda.md:370-372`). **The type is uninhabited at EVERY
frame**, so nothing can instantiate the module and its `out`/`back` are
vacuously true.

`[LJ-1.71]` proved it at `src/ProbeLJ171A.agda:170-173` (`tagEq-refutes`) and
I re-ran that probe myself: green, 1.52 s.

`numK` (`:6416`) has the same over-general shape, quantified over every `k`.
`[LJ-1.71]` classed that one INFERRED, so **check it rather than assume it**.

## WHAT IS NOT WRONG, so you do not re-open it

**The `[LJ-1.55]` slot fix HOLDS.** `[LJ-1.71]` machine-checked that the
frame's row facts land at the telescope's slots definitionally: `tagEq0'`,
`numK0'`, `innerK'`, `pairK'`, `num1K'`, `codesK'`, `codesK-un'` all check
(`src/ProbeLJ171A.agda:118-158`). **The slot convention cost four dispatches
to build and it is sound. Do not change it.**

The twelve row modules and their proofs are sound. **This is a statement
repair plus an instantiation, not a re-proof.** If you find yourself proving
a row, stop and say which.

## THE REPAIR, named by `[LJ-1.71]`

1. **State the tag-dependent facts PER ROW, not universally in `k`.** Twelve
   `tagEq` fields and twelve `numK` fields, exactly as `KFacts` already does
   (`src/L/Condensation.lagda.md:5677-5706`). The row modules each need their
   own tag, and the frame supplies exactly those twelve.
2. **Give the graph frame the union telescope it lacks.** `[LJ-1.71]`
   measured the gap: **the frame carries 35 facts where the telescope demands
   47** (`_build/lj-1.71-report.md` section 2). Add what is missing to
   `SatGraphAgree`'s own telescope, or derive it from what the frame has and
   say which.
3. **Then instantiate.** `SatGraphAgree` applies `TwelveAgree` at
   `(f ∷ e ∷ d ∷ γ)` and supplies `twelve-out` and `twelve-back` from its
   `out` and `back`. Those two parameters leave `SatGraphAgree`'s telescope.

**`SatGraphAgree`'s and `LeafAgree`'s statements do not change.**

## THE ACCEPTANCE TEST, and it is the only one

**The instantiation must GO THROUGH.** That is C-38, admitted today:

> A hypothesis is discharged when something SUPPLIES it, never when it is
> restated. Counting parameters down to zero is not a discharge. Until
> something instantiates the module, "discharged" means "restated", and a
> restatement nothing can satisfy makes the module vacuously true.

**Do not report a discharge on a parameter count.** Report it on the
instantiation, at `file:line`.

**And say plainly whether every fact of your repaired telescope is
inhabited at the frame that uses it.** If any is not, that is the finding and
you stop.

## THE ABORT CRITERION, fixed in advance per D-1

- **The instantiation goes through**: report the measured cost, three cold
  runs each side, gate caliber, loads. Then run
  `python3 scripts/check-ratio.py --check` and quote its aggregate **with
  both multiples, or with the seconds against the ceiling**. Then STOP; do
  not go on to `LeafAgree`'s consumption, the post-leaf five, `levelIn` or
  `cover`.
- **It does not go through**: **STOP** and write the term you could not
  write, with the fact that is uninhabited and the frame that refutes it.

**Either way this dispatch ends at the instantiation.**

**The file has heap-walled twice at the 8 GB cap** (`[LJ-1.70]`: a record
carrying the union telescope, and twenty-four inferred aliases). **A heap
exhaustion is a WALL with its seconds; report it and never raise the cap.**
P-o says a record whose FIELD has a carrier-indexed type hangs the
elaborator and a right-nested `Σ` does not; the module telescope is the shape
that worked.

## WHAT YOU MUST NOT DO

- **You may not weaken a statement and you may not narrow a direction.** Both
  directions of `TwelveAgree` are needed and that is settled. **Making a
  hypothesis easier to satisfy by weakening the conclusion is the defect this
  dispatch repairs, not a repair.**
- **Do not make the telescope satisfiable by making it vacuous in the other
  direction.** If a fact cannot be supplied, say so.
- **Do not delete the band or any part of it.** It is the discharge.
- **Do not touch anything under `src/L/Coding/`.**
- All masters carry ZERO placement of `absFo` or a placed `Δ₀`.
- **Count a module's exports and its facts by finding its boundary**, and say
  where the module ends if you report a count.

## THE CLASSIFICATION I WANT ON EVERY NEGATIVE

State for every negative whether its deciding claim is **MEASURED** or
**INFERRED**, in those words. **A negative that rests on an inference sets no
verdict.**

## DD4

**Maximize the code the two proofs share, and write it generic.** One rule,
two ends, no metric and no checker, so it is stated in every brief and
answered in every return.

Twelve per-row fields are more statement than one universal field, and the
universal one was wrong. **Say what the J tower inherits from the repaired
telescope**, and whether the per-row shape still lets it instantiate at its
own slots.

## ARCHIVE (DD18)

- **`_build/lj-1.71-report.md`**, read WHOLE, and **`src/ProbeLJ171A.agda`**,
  read WHOLE. The refutation, the slot-fix confirmation and the 35-against-47
  count.
- **`_build/lj-1.70-report.md`**, read WHOLE. The telescope you are
  repairing, and the two heap walls.
- `_build/lj-1.55-report.md` and `src/ProbeLJ155B.agda:788-979`, the slot fix
  and the composition.
- `_build/lj-1.62-report.md` sections 2-3, `KFacts` and `SatGraphAgree`.
- `dev/LESSONS.md` **C-38 (new today)**, C-35, P-w as amended, P-o (`:2509`),
  P-t (`:2601`), D-29, read WHOLE.
- `archive/rud-route/` for SHAPE only.

Return an **ARCHIVE USED** section at `file:line`.

## LITERATURE (DD18)

**Nothing in the literature prices a spelling.** Say so in one line and spend
nothing.

## SCOPE (read)

`src/ProbeLJ171A.agda` FIRST, then
`src/L/Condensation.lagda.md:6412-6470` (the telescope) and `:5677-5706`
(`KFacts`, the per-row shape to copy), then `:6608-6660`
(`SatGraphAgree`'s telescope).

## SCOPE (write)

`src/L/Condensation.lagda.md` and `src/ProbeLJ172*.agda`. Your report is
`_build/lj-1.72-report.md`. **No other master. Never
`src/Everything.lagda.md`.**

## MANDATORY RULES FOR A BUILD

Run `python3 scripts/rules.py --for build` and read every statement.

- **C-38.** A hypothesis is discharged when something SUPPLIES it. **This
  brief's acceptance test.**
- **C-35.** A block with no consumer is UNTESTED.
- **P-w as amended.** The copy is paid at use.
- **P-o.** A record field at a carrier-indexed type hangs the elaborator; use
  a nested Σ, or the module telescope that worked.
- **P-h.** Module-parameterized, never function-parameterized.
- **P-k.** A read lemma is stated where its consumers use it.
- **P-l, P-m, P-n, P-q, P-t, P-u, P-v** as above, each with its action.
- **P-c, R-36, R-38.** Seal at the birth site; expose with a read lemma.
- **R-35.** State the membership at the SMALL index and climb.
- **R-40.** State a membership witness SHALLOW and climb.
- **I-5.** The inference trap this tree has paid for.
- **C-12.** `GHCRTS="-A64m -I0 -M8g" agda <file>`, ONE process, cap never
  raised.
- **C-22.** Write the deliverable incrementally.
- **C-31, C-32, C-33, C-34, C-36, C-37.**
- **D-1, D-8, D-10, D-26, D-29, D-30.**

## CONSTRAINTS

- Never commit, never push, never `git checkout .`, `git stash`,
  `git reset --hard` or `git clean`. **The tree is clean; keep your work
  visible in it.**
- Typecheck what you touch and every consumer. Do NOT run `make check`.
- **Run `scripts/check-fences.py --check` before you report anything closed.**
- Count with `scripts/ledger.py`. Run `scripts/lint-prose.py --check` and
  `scripts/lint-agda.py --check`.
- DD23 freezes mathematical prose. Code and its own comments only.
- **The machine is quiet and both Agda slots are yours. Report the load
  average beside every absolute figure.**
- Evidence is `file:line`. Write ASD-STE100.

## RETURN

Write `_build/lj-1.72-report.md` incrementally, skeleton first.

**Lead with whether `SatGraphAgree` now INSTANTIATES `TwelveAgree`**, at
`file:line`, and whether `twelve-out` and `twelve-back` have left its
telescope. Then, for every fact of the repaired telescope, that it is
inhabited at the frame. Then the measured cost and the gate's aggregate.
**Mark every negative MEASURED or INFERRED.** Then the DD4 answer and **the
convergence answer.**
