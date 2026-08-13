# LJ-1.43: close the six remaining row agreements and block 1

tier: codex (default)

## GOAL

Six row agreements and block 1's agreement remain open. Close them, or return a
measured wall for each one that does not close.

## CWD

`/Users/alsg/Agentic/Bedrock`, on branch `two-tower-bridge`.

## THE STATE

`src/L/Condensation.lagda.md` is GREEN. Nine of twelve row agreements close:
And, Or, Top, Neg, Forall, plus the earlier Bot, and the shared machinery.

**Open:** Exist, Mem, Eq, Imp, AllIn, ExIn, and block 1's agreement
(`existClauseAt` against `Clause.existBndAt`).

`[LJ-1.42]` measured ONE blocker and did not attempt the rest. Its words, and
it classified them itself: **"This is a measured wall, not an impossibility
claim."** The machine's `consAtL` is `liftFo (consAt ...) (bddCons ...)`
(`src/L/Coding/Model.lagda.md:1484-1485`), so its satisfaction inside the
machine's clause is not definitionally the written `⟨ env ⊨ consAtL ... ⟩`. It
says the fix is a transport along the adequacy and that it did not complete it.

**So the deciding claim is INFERRED, not measured.** Treat it as an open
question. **Attempt the transport before concluding anything about the other
five**, which `[LJ-1.42]` grouped with Exist without testing them.

## WHAT DECIDES A CLAIM IN THIS REPOSITORY

If you report that something cannot be done, **write the term you could not
write, or name the constructor that is missing and show nothing supplies it**
(`dev/LESSONS.md` C-36). A failed coercion says two types differ; it never says
no term connects them. That mistake cost this phase two dispatches and two
reviews.

**You may strengthen a statement. You may not weaken one.** A cure is often a
strengthening, and the last cure here was.

## THREE OPEN OBLIGATIONS YOU INHERIT, from `[LJ-1.42]`'s own uncertainties

1. **`envInK` is unproved at the class carrier.** The rows do not force the
   arity to be a numeral, so the three newly closed agreements are conditional
   on a site fact. **Discharge it or state plainly that the closures are
   conditional.**
2. **About 210 of 921 lines are dead scaffolding**: the unused `QuantBody` and
   the scaffolded `ExistAgree`. **Remove what stays dead.**
3. **Line-count caliber**: `[LJ-1.42]`'s counter and `scripts/ledger.py`
   disagree. **Use `ledger.py` and say what the difference was.**

## THE FENCE

A new gate exists because `[LJ-1.41]` reported two theorems closed that sat
OUTSIDE the ` ```agda ` fence, as prose, carrying four defects. Agda never read
them and the line counter never counted them, so every existing check passed.
**Run `python3 scripts/check-fences.py --check` before you report anything
closed.**

## THE LAWS THAT DECIDE THE SHAPE

- **P-u.** Certify before you place. The master has zero placement and that is
  load-bearing. If you need `absFo` or a placed `Δ₀`, stop and report it.
- **P-v.** One formula, one spelling, decided at the formula level.
- **P-l** and **P-t**: what a type names is what costs, and the class follows
  the formula.
- **C-12.** `GHCRTS="-A64m -I0 -M8g" agda <file>`, one process, cap never
  raised.
- **C-35.** No consumer, no DELIVERED. The agreement is the consumer.
- **D-29.** Audit a shared assembly before instantiating it six times.

- **D-10.** Every figure in this brief is a residue, including the ones I
  copied from `[LJ-1.42]`. Re-verify before you build on them.
- **C-22.** Write the deliverable incrementally.
- **D-26.** A well-founded key on a tower needs generation data or syntax.
  **Say in one line whether it bears.** The rows key on the Def syntax because
  `Lset` is a definable power, so it may bear on which transports are per-tower.

- **P-h.** Module-parameterized, never function-parameterized.
- **P-k.** A read lemma is stated where its consumers use it.
- **P-m.** The check-cost rate is a content-class certificate.
- **P-n.** Satisfaction content at a concrete carrier is a payable floor.
- **R-35.** Union representations are meta-poisoned: state the membership at
  the SMALL index and climb.
- **R-38.** Seal at the birth site, and do NOT unseal.
- **R-40.** State a membership witness SHALLOW and climb.
- **I-5.** The inference trap this tree has paid for.

Run `python3 scripts/rules.py --for build` and read every statement. **The
bundle is the gate, not boilerplate**: this brief was refused three times for
trimming it, and each refusal was correct.

## DD4

**Maximize the code the two proofs share, and write it generic.** One rule, two
ends, no metric and no checker, so it is stated in every brief and answered in
every return.

Five rows closed off one shared assembly this phase and nothing row-specific
was written for And and Or. **If the six need six different transports, say so;
that is evidence the sharing is thinner than it looked.**

## ARCHIVE AND LITERATURE (DD18)

Read whole, not by section: `_build/lj-1.42-report.md`,
`_build/lj-1.41-review.md`, `src/L/Condensation.lagda.md`,
`src/L/Coding/Model.lagda.md`. `dev/LESSONS.md` binds and is not archived.

Literature: `dev/literature/devlin-II5.md` Step C only. Devlin asserts
absoluteness where this block proves a decode, so the book cannot price these
rows. Say so in one line if nothing else bears.

Return **ARCHIVE USED** and **LITERATURE USED** at `file:line`.

## SCOPE (read)

Read what you need, and read the archive documents WHOLE rather than by
section.

## SCOPE (write)

`src/L/Condensation.lagda.md` and `src/ProbeLJ143*.agda`. Your report is
`_build/lj-1.43-report.md`. **Never `src/Everything.lagda.md`, never another
master.**

## CONSTRAINTS

- Never commit, never push, never `git checkout .`, `git stash`,
  `git reset --hard` or `git clean`.
- Typecheck the master and every consumer. Do NOT run `make check`.
- Count with `scripts/ledger.py`. Report cold seconds, the marginal rate and
  the module-load cone separately, against DD24's 0.013193.
- Run `scripts/lint-prose.py --check`, `scripts/lint-agda.py --check` and
  `scripts/check-fences.py --check`.
- DD23 freezes mathematical prose. Code and its own comments only.
- Evidence is `file:line`. Write ASD-STE100.
- **The machine is quiet and both Agda slots are yours.**

## RETURN

Write `_build/lj-1.43-report.md` incrementally, skeleton first.

Lead with the verdict: how many of the seven closed, and the rate. Then, for
each one that did not close, the term you could not write. Then the three
inherited obligations. Then the numbers, the DD4 answer, and what you are not
sure of.
