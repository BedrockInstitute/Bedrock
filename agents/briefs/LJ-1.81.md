# LJ-1.81: is the STAGE enough, or does the proof need KFacts at the hull?

tier: codex (default)

## GOAL

**Answer one question before building anything.** A `KFacts` value exists at
a limit stage. **Does the condensation proof need one at the HULL, or is the
stage the site it actually uses?**

## CWD

`/Users/alsg/Agentic/Bedrock`, on branch `two-tower-bridge`, **clean at
`45a395a`**. HEAD is green. I reverted `[LJ-1.80]`'s edit to
`src/L/BoundedSubset.lagda.md`: it did not typecheck.

## WHAT `[LJ-1.80]` ACHIEVED, and I verified it myself

**`KFacts` is INHABITABLE. Machine-checked.**

`src/ProbeLJ180A.agda` builds `kfacts : KFactsNS.KFacts {14} A₀ K₀ ...`
(`:186-226`) and typechecks at 1.59 s user. The site:

- **`K` slot: `LsetS lam ordλ`**, a LIMIT stage;
- `A` slot: `LsetS α ordα`;
- the twelve numeral slots.

All 27 fields have suppliers. `arityK` comes from
`layer-trans (Lset-layer lam)`, the stage's transitivity; the pairing
closures come from `pr∈Lset-suc` with trichotomy and `succλ`.

**That settles C-38 for the record itself**: `KFacts` is no longer "not known
false", it is **known satisfiable**.

## THE QUESTION

`[LJ-1.80]`'s own section 2 names the wall it did not cross:

> The brief points at the Skolem hull `M` (`HullStage`,
> `src/L/BoundedSubset.lagda.md:902-915`) or its collapse `C.πX`. The slots
> of `KFacts` are constructible sets (`S` is the carrier of `𝒮ʟ`), and no
> `isL` certificate for `M` or `πX` is delivered.

**So: which site does the proof actually need?**

**Answer this by reading the consumers, not by preference.** `SatGraphAgree`
and `LeafAgree` take `KFacts` at some `γ`. Follow where that `γ` comes from
in the chain that reaches `levelIn` and `cover`
(`src/L/BoundedSubset.lagda.md:916-917`), and say at `file:line` what the
`K` slot must be there.

- **If the stage suffices**, say so and say why the hull is not needed. **That
  would mean the phase's remaining obstruction is smaller than believed**,
  and it is the answer I most want checked rather than assumed.
- **If the hull is required**, say exactly what is missing: an `isL`
  certificate for `M` or for `πX`, or something else. **Then price it**: is
  it delivered anywhere, is it provable from `hull-closed` and the collapse,
  or is it a genuine gap.

**This is a reading and pricing task. Do not build the hull certificate.**

## THE ABORT CRITERION, fixed in advance per D-1

- **The stage suffices**: report the consumer chain at `file:line` and STOP.
- **The hull is required**: report what is missing, where it would come from,
  and a price with its basis (DD8: one best-effort figure that names its
  basis). Then STOP.
- **You cannot tell from the delivered tree**: say so plainly and name what
  would settle it. **That is a full deliverable.**

**Do not edit any master.** Work in `src/ProbeLJ181*.agda` only if you need
to check a type. **Leave the tree byte-identical and say so.**

## C-12, AND THIS IS NOT BOILERPLATE

`[LJ-1.80]` left **SIX agda processes alive at once**, all children of one
wrapper, all checking the same probe, started a minute or two apart with none
of the earlier ones killed. Each carried `-M8g`, so the worst case was 48 GB
on a 64 GB machine, and the load average reached 19. **The owner caught it;
no tool did.**

**ONE agda process at a time. If a check does not return, KILL IT before you
start another, and report the wall with its seconds.** A retry that leaves
the previous run alive is how a per-process cap becomes a machine-level risk.

**And `[LJ-1.80]` left a master that did not typecheck**, for the second time
this phase. **If you touch a master, it is green when you finish or you
revert it.**

## THE CLASSIFICATION I WANT ON EVERY NEGATIVE

State for every negative whether its deciding claim is **MEASURED** or
**INFERRED**, in those words. **A negative that rests on an inference sets no
verdict.**

## DD4

**Maximize the code the two proofs share, and write it generic.** One rule,
two ends, no metric and no checker, so it is stated in every brief and
answered in every return.

**Say whether the site you identify is generic**, so the J tower supplies
`KFacts` the same way, or whether it is specific to the L tower's hull.

## ARCHIVE (DD18)

- **`_build/lj-1.80-report.md`**, read WHOLE, and **`src/ProbeLJ180A.agda`**,
  read WHOLE. The value that exists and the wall it names.
- `_build/lj-1.79-report.md`, the repaired fields and their suppliers.
- **`_build/lj-1.52-report.md`** and **`_build/lj-1.51-report.md`**, read
  WHOLE. **They name the hull's delivered properties and what `levelIn` and
  `cover` still need, written as terms.** That is your main evidence.
- `_build/diag-twelve-row-math.md` section 3, on what the proof needs.
- `dev/LESSONS.md` C-38 as extended, C-35, C-36, D-30, read WHOLE.
- `archive/rud-route/` for SHAPE only.

Return an **ARCHIVE USED** section at `file:line`.

## LITERATURE (DD18)

**This is where the literature decides.** `dev/literature/devlin-II5.md`
Step C and `_build/literature/dev2.txt:1372-1385`. **Devlin takes the hull OF
`L_α ∪ {x}` and collapses it. Say in two lines what his bounding set is**,
and whether it is a stage or the hull. Return a **LITERATURE USED** section.

## SCOPE (read)

`src/ProbeLJ180A.agda` FIRST, then `_build/lj-1.80-report.md` section 2, then
`src/L/BoundedSubset.lagda.md:900-960` and `:916-917`, then
`_build/lj-1.52-report.md`.

## SCOPE (write)

`src/ProbeLJ181*.agda` only. Your report is `_build/lj-1.81-report.md`.
**No master. Never `src/Everything.lagda.md`.**

## MANDATORY RULES FOR A BUILD

Run `python3 scripts/rules.py --for build` and read every statement.

- **D-30.** Price what the CONSUMER needs. **This brief is D-30 applied to a
  site.**
- **C-38 as extended.** A hypothesis is discharged when something SUPPLIES
  it.
- **C-35.** A block with no consumer is UNTESTED.
- **C-36.** Write the term you could not write.
- **D-8.** One best-effort figure, and it names its basis.
- **P-h, P-k, P-l, P-m, P-n, P-o, P-q, P-t, P-u, P-v** as the bundle gives
  them.
- **P-c, R-36, R-38.** Seal at the birth site; expose with a read lemma.
- **R-35, R-40.** State the membership SHALLOW and climb.
- **I-5.** The inference trap this tree has paid for.
- **C-12.** ONE agda process, `GHCRTS="-A64m -I0 -M8g"`, cap never raised,
  **and kill a hung check before starting another.**
- **C-22.** Write the deliverable incrementally. **`[LJ-1.80]` did this and
  it is why its work survived being killed.**
- **C-31, C-32, C-33, C-34, C-37.**
- **D-1, D-10, D-26, D-29.**

## CONSTRAINTS

- Never commit, never push, never `git checkout .`, `git stash`,
  `git reset --hard` or `git clean`.
- Do NOT run `make check`. You need not run `check-ratio`.
- **Run `scripts/check-fences.py --check` before you report anything closed**
  and say the master count.
- Run `scripts/lint-prose.py --check` and `scripts/lint-agda.py --check` on
  anything you touch.
- DD23 freezes mathematical prose.
- **Report the load average beside every absolute figure.**
- Evidence is `file:line`. Write ASD-STE100.

## RETURN

Write `_build/lj-1.81-report.md` incrementally, skeleton first.

**Lead with the site the proof needs: stage or hull**, with the consumer
chain at `file:line`. Then, if the hull, exactly what is missing and its
price with its basis. **Mark every negative MEASURED or INFERRED.** Then what
Devlin's bounding set is. Then the DD4 answer. Confirm the tree is
byte-identical to your start.
