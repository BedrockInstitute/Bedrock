# LJ-1.90: instantiate BoundedSubsetAt for the first time

tier: codex (default)

## GOAL

**Be the first consumer.** `BoundedSubsetAt` has never been instantiated.
Instantiate it, and report the first hypothesis nothing can supply.

## CWD

`/Users/alsg/Agentic/Bedrock`, on branch `two-tower-bridge`, **clean at
`e49628a`**. HEAD is green.

## WHY THIS ONE, and why it is the whole test

Four statement-level defects were found this phase, and **every one was found
by a first consumer or by an adversarial review, never by a shape audit**:

| defect | how it ended |
|---|---|
| `TwelveAgree`'s `tagEq` uninhabitable | deleted |
| `KFacts`'s closure family uninhabitable | guarded, refutation dead |
| `witK` false | premise found, assembly PROVED at `src/ProbeLJ189A.agda:266-306` |
| the witness step suspected circular | shown NOT circular, by finiteness |

**All four repairs are staged, not discharged.** `BoundedSubsetAt` has no
instantiation anywhere in `src/`, so nothing has ever supplied the layer's
hypotheses at a real site. **This dispatch is that site.**

## WHAT TO DO

**Instantiate `BoundedSubsetAt`** (`src/L/BoundedSubset.lagda.md:1396-1402`)
at a concrete carrier and stage, supplying its telescope:

- `lam`, `ordλ`, `succλ`: a limit stage and its closure.
- `x ∈ Lset lam`: the frame already asks for this.
- **`AllCodes A ∈ Lset lam`**: the new hypothesis `[LJ-1.89]` needs. The
  consumer that names `lam` must produce it. **Say whether it can.**
- whatever else the telescope carries. **Read it; do not work from this
  list.**

**Go as far as the supply reaches and report the FIRST hypothesis nothing
can supply**, at `file:line`.

## THE ACCEPTANCE TEST

**C-38: a hypothesis is discharged when something SUPPLIES it.**

- **Every hypothesis you supply must receive a VALUE**, not another
  parameter. Report each at `file:line`.
- **Say plainly how far the supply reaches.**
- **Do not report a discharge on a parameter count.** That error has been
  made three times this phase, once by me.

## THE ABORT CRITERION, fixed in advance per D-1

- **The instantiation goes through**: report it and STOP. Do not go on to
  `levelIn`, `cover` or the post-leaf five. **That would be the phase's first
  real consumer and it needs auditing before anything is built on it.**
- **A hypothesis cannot be supplied**: STOP there, write the term you could
  not write, and say what the tower would have to provide.
- **Anything walls**: STOP, report the wall with its seconds.

**Work in `src/ProbeLJ190*.agda`.** If you touch a master it is GREEN when
you finish or you revert it; `[LJ-1.72]` and `[LJ-1.80]` each left one broken
and each cost a revert.

## C-12, AND THIS IS NOT BOILERPLATE

`[LJ-1.80]` left **SIX agda processes alive at once**, all children of one
wrapper, all on the same probe, none killed. Each carried `-M8g`: 48 GB of
worst case on a 64 GB machine at load 19. **The owner caught it; no tool
did.**

**ONE agda process at a time. If a check does not return, KILL IT before you
start another, and report the wall with its seconds.**

## WHAT YOU MUST NOT DO

- **You may not weaken a hypothesis to make it suppliable.** If it cannot be
  supplied, that is the finding.
- **Do not add a hypothesis to the instantiation site.** A site that assumes
  what it should supply has moved the obligation, not discharged it.
- **Do not touch anything under `src/L/Coding/` or `src/V/`.**
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

**Say whether the instantiation is generic in the stage**, so the J tower
instantiates its own the same way.

## ARCHIVE (DD18)

- **`_build/lj-1.89-report.md`**, read WHOLE, and **`src/ProbeLJ189A.agda`**.
  The proved `witK` and who it says must supply the frame hypothesis.
- `_build/lj-1.88-report.md`, `src/ProbeLJ188A.agda`: the finiteness route.
- `_build/lj-1.83-report.md`, `src/ProbeLJ183A.agda`: the four modules
  already fed, and the `C = K` convenience that is NOT admissible as a
  discharge.
- `_build/lj-1.80-report.md`, `src/ProbeLJ180A.agda`: the stage `KFacts`
  value.
- `src/L/BoundedSubset.lagda.md:1390-1410`, the telescope you must supply.
- `dev/LESSONS.md` **C-38 as extended**, C-35, C-36, D-30, read WHOLE.
- `archive/rud-route/` for SHAPE only.

Return an **ARCHIVE USED** section at `file:line`.

## LITERATURE (DD18)

**Banked.** `[LJ-1.88]` settled how Devlin bounds his witness. Say so in one
line and spend nothing.

## SCOPE (read)

`src/L/BoundedSubset.lagda.md:1390-1410` FIRST, then
`src/ProbeLJ189A.agda:266-306`, then `src/ProbeLJ180A.agda:186-226`.

## SCOPE (write)

`src/ProbeLJ190*.agda`, and any master **only if you revert it before
finishing**. Your report is `_build/lj-1.90-report.md`. **Never
`src/Everything.lagda.md`.**

## MANDATORY RULES FOR A BUILD

Run `python3 scripts/rules.py --for build` and read every statement.

- **C-38 as extended.** A hypothesis is discharged when something SUPPLIES
  it. **This dispatch is the supply site.**
- **C-35.** A block with no consumer is UNTESTED. **You are the consumer.**
- **C-36.** Write the term you could not write.
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

Write `_build/lj-1.90-report.md` incrementally, skeleton first.

**Lead with how far the instantiation reached**, hypothesis by hypothesis at
`file:line`, and what the first unsuppliable one is. Then whether anything
is now discharged rather than staged, in those words. **Mark every negative
MEASURED or INFERRED.** Then the DD4 answer. Confirm every master is green or
untouched.
