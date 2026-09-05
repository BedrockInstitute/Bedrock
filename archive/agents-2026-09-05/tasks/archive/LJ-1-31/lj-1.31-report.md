# LJ-1.31 Report: Build the constant-free reader in the coding layer

## 1. THE VERDICT

DELIVERED. The constant-free reader lands in the two masters. Environment
gains 110 in-fence lines. Model loses one. The six consumers keep their text
byte-identical. Every one of them typechecks. The delivered `consAtL` has
count zero at the real carrier. The delivered `erase` accepts it. Environment
checks at 0.00347 seconds per line. Model checks at 0.00409. Both are far
below the gate's GO line at 0.013 and below DD24's bar at 0.013193.

The [LJ-1.30] price is confirmed almost exactly. It priced about 110 lines
over two masters and zero consumer edits. The build lands at 109 lines and
zero consumer edits.

One finding qualifies the brief's clause-level claim. The real exported
clause forms do NOT reach count zero. They keep the arity tag and the
term-value tags from other readers. Section 6 states this with the machine
evidence.

## 2. DID ANY CONSUMER NEED AN EDIT?

No. The six consumer masters are byte-identical to HEAD. They are `Sat`,
`Bridge`, `Sound`, `Unique`, `Internal` and `Adequate`. Each typechecks cold,
one Agda process at a time. The use-site counts match the brief exactly:
Sat 11, Bridge 17, Sound 9, Unique 9, Internal 7, Adequate 5.

The direct-import cone of the two masters also re-checks green. All 25
masters that import `L.Coding.Model` typecheck. The catalog check re-checks
`L.Model`, `Landmarks` and `L.Hull` green.

## 3. IS `consAt-adequate`'s STATEMENT UNCHANGED?

Yes. The statement text is byte-identical to HEAD. I diffed the two texts.
The proof body swaps four `tagAt-adequate` calls and three hypothesis
annotations. Each swap names `tag0At-adequate` with the dropped constant
argument. Nothing else in the proof changes.

## 4. THE NUMBER

In-fence non-blank lines at the ledger caliber. Before is HEAD. After is the
working tree.

| file | before | after | delta |
|---|---:|---:|---:|
| `L.Coding.Environment` | 305 | 415 | +110 |
| `L.Coding.Model` | 1289 | 1288 | -1 |
| `L.Coding.Sat` | 179 | 179 | 0 |
| `L.Coding.Bridge` | 294 | 294 | 0 |
| `L.Coding.Sound` | 801 | 801 | 0 |
| `L.Coding.Unique` | 630 | 630 | 0 |
| `L.Choice.Internal` | 780 | 780 | 0 |
| `L.Choice.Adequate` | 563 | 563 | 0 |

The two masters move by 109 lines in total. The [LJ-1.30] price was about
110. The six consumers move by zero.

## 5. SECONDS AND RATE

Protocol: one Agda process at a time, `GHCRTS="-A64m -I0 -M8g"`, each file's
own interface stashed, dependencies warm, `/usr/bin/time -p`, user seconds.

| file | user s | lines | rate | gate |
|---|---:|---:|---:|---|
| `L.Coding.Environment` | 1.44 | 415 | 0.00347 | GO |
| `L.Coding.Model` | 5.27 | 1288 | 0.00409 | GO |
| `L.Coding.Sat` | 1.47 | 179 | 0.00821 | GO |
| `L.Coding.Bridge` | 1.53 | 294 | 0.00520 | GO |
| `L.Coding.Sound` | 5.02 | 801 | 0.00627 | GO |
| `L.Coding.Unique` | 5.38 | 630 | 0.00854 | GO |
| `L.Choice.Internal` | 7.55 | 780 | 0.00968 | GO |
| `L.Choice.Adequate` | 14.65 | 563 | 0.02602 | OVER |

The gate's GO line is 0.013. DD24's bar is 0.013193. Seven of eight files
land below both.

Adequate is above the line. Its source is byte-identical, so the rate is
pre-existing. It is a consumer with instantiation content, not the wing
content class the gate governs.

The masters have two cold samples each. Environment measured 1.42 and 1.44
seconds. Model measured 5.29 and 5.27. Both pairs are flat under the noise
rule.

## 6. DID THE CLAUSE'S COUNT REACH 0 IN THE REAL MASTERS?

The task's target reaches zero. `countFo (consAtL ...)` is 0 in the real
master, by refl, at arities 1, 3 and 11. The delivered `erase` accepts the
real reader at arities 1 and 3. The real quantifier-clause bodies `body∃`
and `body∀` are also 0.

The full real clause forms do not reach zero. `existClauseAt` and
`forallClauseAt` each count 1. `allInClauseAt` and `exInClauseAt` each count
5. Their constants are `numeralL 10`, `numeralL 1`, `numeralL 0`,
`numeralL 1`, `numeralL 0`, verified by lookup. None of them is `consAtL`.
The arity tag `# k` sits in `binClauseAt` through `arityTagPairAtL`. The
term-value tags `# 0` and `# 1` sit in `tmValAt` through `tagAtL`.

The count-zero clause exists only in the probe shape where the arity tag is
a slot. That is the [LJ-1.27] variant. The real masters keep the arity tag
as a constant. Slotting it changes `binClause-out`'s statement and the
proofs that use it. That change is outside this brief's scope.

The probe is `src/ProbeLJ131.agda`. It is untracked and never committed.

## 7. DD4: WHAT THE J TOWER GETS

Nothing today. The tree has no J modules. `consAtL` has no J consumer. Its
consumers are only the `L.Coding.*` and `L.Choice.*` masters.

The J tower is planned at `[LJ-3.4]` (`dev/PLAN.md:488`). The [LJ-1.27-R]
finding stands: the J certificate is structural and avoids the syntax
entirely, under D-26 (`dev/PLAN.md:168`).

So the J tower does not use `consAtL` today. I state that plainly. The
constant-free shape is still the shared shape. A fresh J
environment-extension clause should use the same readers.

## 8. ARCHIVE USED

- `src/ProbeLJ130B.agda` in full. It is the adequacy proof model. I ported
  it into `Environment`. I corrected one type: `Emptyₛ` uses `E.⊥`, not
  `E.⊥* {ℓ-suc ℓ}`.
- `src/ProbeLJ130A.agda` in full. It is the cured clause, its count checks,
  and the ride on the delivered `erase`.
- `_build/lj-1.30-report.md` in full. It prices the rewrite, records the
  `# 0 = ∅` finding, and lists the consumer counts.
- `_build/lj-1.27-review.md:114-256`. Sections 4 to 6 wall the placement
  route and name the constant-free route as the fourth way out.
- `_build/lj-1.29-report.md:1-25`. Section 1 rules that the crossing keeps
  the shared formula and the placement must go.
- `src/FOL/Count.lagda.md:598-611` for `erase`, and `:617-637` for
  `erase-inv`.
- `src/L/Coding/Base.lagda.md:100-340` for `sgl-char`, `pair-char`,
  `prChar-fwd`, `prChar-bwd`, `tagAt` and `tagAt-adequate`.
- `src/L/Coding/Environment.lagda.md` in full, and
  `src/L/Coding/Model.lagda.md:1420-1516` and `:1860-1960`.
- `dev/LESSONS.md`: P-h at `:174`, P-l at `:2305`, P-m at `:2460`, P-n at
  `:2483`, P-t at `:2601`, P-u at `:2908`, R-35 at `:782`, R-38 at `:829`,
  R-40 at `:929`, I-5 at `:1196`, C-12 at `:2075`, C-22 at `:2237`, D-10 at
  `:1316`. I read the build bundle through `scripts/rules.py --for build`.
- `dev/PLAN.md:168` for D-26, and `:488` for `[LJ-3.4]`.

## 9. WHAT I AM NOT SURE OF

- The real clause forms do not reach count zero. The residue is the arity
  tag and the term-value tags, not `consAtL`. Reaching zero in the real
  masters needs the arity tag slotted. That edit changes statement types in
  the clause machinery. It is outside this brief.
- I could not fully decompose `allInClauseAt`'s five constants by reading
  the definitions. The machine-verified list is `10, 1, 0, 1, 0`. Two of
  them match `tmValAt`. The other `1, 0` pair I did not locate by hand. The
  counts stand, and none of the constants is `consAtL`.
- `Adequate` checks at 0.02602 seconds per line, above the gate line. Its
  text is byte-identical, so the rate is pre-existing.
- I corrected two prose paragraphs in `Model`, English and Chinese. The code
  change made the old text false. DD23 freezes mathematical prose. I treated
  the correction as part of the change, not as new prose.
- I deleted the private `bddSglCon`, `bddPairCon` and `bddTag` from `Model`.
  The tagged readers stay in `L.Coding.Base`. `numL` stays; `InL` and `Sat`
  import it.
- I did not run `make check`. I ran `lint-prose.py --check`,
  `lint-agda.py --check` and `weave-i18n.py --check`. All three pass. The
  remaining gate checks belong to the orchestrator.
- The consumer rates come from one clean cold run each. The masters come
  from two runs each.
