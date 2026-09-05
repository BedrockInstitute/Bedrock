# LJ-1.85: repair witK with a premise its consumer can supply

tier: codex (default)

## GOAL

`witK` is false. **Find the premise that makes it true AND that a real
consumer can supply**, and check both halves.

## CWD

`/Users/alsg/Agentic/Bedrock`, on branch `two-tower-bridge`, **clean at
`9669576`**. HEAD is green.

## WHAT IS SETTLED, machine-checked

`witK` (`src/L/Condensation.lagda.md:6227-6229`) has no inhabitant.
`src/ProbeLJ184A.agda` refutes it at the stage for every ordinal.

**The cause, and I verified it in the source:**

```agda
unForm k rel = ∃̇ (∃̇ (arityTagAtL (suc (suc zero)) (suc zero) k zero ∧̇ rel))
zeroPay      = var zero ≐ con (numeralL 0)
```

`unForm` binds the arity slot existentially and never constrains it, and tag
6's shapedness clause constrains only the payload. So a closed shaped code
set can be extended by `pr K (pr (# 6) (numeralL 0))`, whose arity slot is
the bound itself. Tag 6 fires no closedness clause, so the extension stays
closed and shaped and still contains the key, while its rank reaches the
bound's. **Shapedness does not bound a witness.**

**`shapes` is not wrong.** It is a definition on the machine side and it is
off-limits. `witK` assumed more than `shapes` gives.

## THE REPAIR, and BOTH halves must hold

**C-38: a hypothesis is discharged when something SUPPLIES it.** So a premise
that makes `witK` true is worth nothing unless a consumer can supply it.

1. **Find the premise.** The obvious candidate is that `w` is BOUNDED rather
   than an arbitrary closed shaped set: `w ⊆ AllCodes A`
   (`src/L/Coding/CodeSet.lagda.md:434-461`), or the arity slots of `w`'s
   members lie in `K`, or something else you can argue. **You choose it and
   you justify it.**
2. **Check the refutation dies.** Adapt `src/ProbeLJ184A.agda` and report
   that it no longer typechecks against the repaired statement. **Say plainly
   that this is not the same as exhibiting an inhabitant.**
3. **Check a consumer can supply it.** `WitnessAgree`'s `witK` is used inside
   `out`/`back`; the witness `w` there comes from `hasWitnessAt`'s
   existential. **Find where a real instantiation gets `w` and say whether
   your premise is available there, at `file:line`.**

**If the premise that makes `witK` true is one no consumer can supply, say
so and STOP.** That is the finding, and it would mean the obligation has to
move rather than be repaired.

## THE ABORT CRITERION, fixed in advance per D-1

- **A premise makes `witK` true AND a consumer can supply it**: report both,
  with the refutation's failure and the supply point at `file:line`, and
  STOP. Do not carry the chain further.
- **No suppliable premise exists**: STOP, write the term you could not write,
  and say where the obligation would have to move to.
- **Anything walls**: STOP, report the wall with its seconds.

**Work in `src/ProbeLJ185*.agda`.** If you touch a master it is GREEN when
you finish or you revert it.

## C-12, AND THIS IS NOT BOILERPLATE

`[LJ-1.80]` left **SIX agda processes alive at once**, all children of one
wrapper, all on the same probe, none of the earlier ones killed. Each carried
`-M8g`: 48 GB of worst case on a 64 GB machine at load 19. **The owner caught
it; no tool did.**

**ONE agda process at a time. If a check does not return, KILL IT before you
start another, and report the wall with its seconds.**

## WHAT YOU MUST NOT DO

- **Do not weaken the CONCLUSION of `witK` or of anything above it.** Only
  the premise changes.
- **Do not touch `shapes`, `closedAt`, or anything under `src/L/Coding/` or
  `src/V/`.** If the machine side looks wrong, STOP and report it.
- **Do not invent a premise nobody can supply.** That moves the defect; it
  has happened three times this phase.
- **Never `src/Everything.lagda.md`.**
- **Do not raise the heap cap.** C-12.
- **Read line numbers and counts from the source, never from a report.**

## THE CLASSIFICATION I WANT ON EVERY NEGATIVE

State for every negative whether its deciding claim is **MEASURED** or
**INFERRED**, in those words. **A negative that rests on an inference sets no
verdict.**

## DD4

**Maximize the code the two proofs share, and write it generic.** One rule,
two ends, no metric and no checker, so it is stated in every brief and
answered in every return.

**Say whether the repaired premise is generic**, so the J tower's witnesses
satisfy it the same way.

## ARCHIVE (DD18)

- **`_build/lj-1.84-report.md`**, read WHOLE, and **`src/ProbeLJ184A.agda`**.
  The refutation and its junk-member construction.
- `_build/lj-1.83-report.md` and `src/ProbeLJ183A.agda`, the four modules
  already fed and the transitivity route.
- `_build/lj-1.80-report.md` and `src/ProbeLJ180A.agda`, the stage value.
- `src/L/Coding/CodeSet.lagda.md`, `AllCodes` and `hasWitnessAt`.
  **Read-only.**
- `dev/LESSONS.md` **C-38 as extended**, C-35, C-36, D-30, read WHOLE.
- `archive/rud-route/` for SHAPE only.

Return an **ARCHIVE USED** section at `file:line`.

## LITERATURE (DD18)

**Devlin bounds his witness somehow, and this dispatch is about that bound.**
`dev/literature/devlin-II5.md` Step C. **Say in two lines what bounds his
code set**, and whether the tree's `AllCodes` is the analogue. Return a
**LITERATURE USED** section.

## SCOPE (read)

`src/ProbeLJ184A.agda` FIRST, then
`src/L/Condensation.lagda.md:6224-6240`, then
`src/L/Coding/CodeSet.lagda.md`'s `AllCodes` and `hasWitnessAt`.

## SCOPE (write)

`src/ProbeLJ185*.agda`, and any master **only if you revert it before
finishing**. Your report is `_build/lj-1.85-report.md`. **Never
`src/Everything.lagda.md`.**

## MANDATORY RULES FOR A BUILD

Run `python3 scripts/rules.py --for build` and read every statement.

- **C-38 as extended.** A hypothesis is discharged when something SUPPLIES
  it. **Both halves of this brief are C-38.**
- **C-36.** Write the term you could not write.
- **C-35.** A block with no consumer is UNTESTED.
- **D-30.** Price what the CONSUMER needs.
- **P-h.** Module-parameterized, never function-parameterized.
- **P-k, P-l, P-m, P-n, P-o, P-q, P-t, P-u, P-v** as the bundle gives them.
- **P-c, R-36, R-38.** Seal at the birth site; expose with a read lemma.
- **R-35, R-40.** State the membership SHALLOW and climb.
- **I-5.** The inference trap this tree has paid for.
- **C-12.** ONE agda process, cap never raised, **kill a hung check before
  starting another.**
- **C-22.** Write the deliverable incrementally.
- **C-31, C-32, C-33, C-34, C-37.**
- **D-1, D-8, D-10, D-26, D-29.**

## CONSTRAINTS

- Never commit, never push, never `git checkout .`, `git stash`,
  `git reset --hard` or `git clean`.
- Typecheck what you touch. Do NOT run `make check`.
- **Run `scripts/check-fences.py --check` before you report anything closed**
  and say the master count.
- Run `scripts/lint-prose.py --check` and `scripts/lint-agda.py --check`.
- DD23 freezes mathematical prose.
- **Report the load average beside every absolute figure.**
- Evidence is `file:line`. Write ASD-STE100.

## RETURN

Write `_build/lj-1.85-report.md` incrementally, skeleton first.

**Lead with the premise you chose and why**, then that the refutation no
longer applies, then **where a real consumer supplies the premise, at
`file:line`**. Keep the distinction between "the refutation fails" and "an
inhabitant exists". **Mark every negative MEASURED or INFERRED.** Then what
bounds Devlin's code set. Then the DD4 answer. Confirm every master is green
or untouched.
