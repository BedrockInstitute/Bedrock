# LJ-1.32 report: does the placement wall scale with the constant count?

Status: COMPLETE. Probe, written incrementally. Untracked probes, no
commit, no push. ASD-STE100.

## 1. THE VERDICT

**NO. The wall does not scale with the constant count. It is present at
count 0. Route A does not fund through the placement route.**

The [LJ-1.27-R] walling clause exhausts an 8 GB heap in 62.9 to 65.4
seconds at every constant count 0, 1, 2 and 5. The same clause without
the placement checks in 2.6 to 3.6 seconds. A small count-0 formula
places in 3.2 seconds. The wall is a full-tree placement cost. It does
not depend on the number of constants.

The delivered clause forms cannot carry the certificate themselves. They
are not Delta-0 formulas. Their frames use the unbounded quantifiers
`∀̇` and `∃̇`, and `Δ₀` has no constructor for them. The certificate the
crossing needs is for the bounded matrix, and that matrix walls at every
positive count and at count 0.

Route A funds only through the erase route with no placement. The real
clause forms are not erase-eligible today. Their arity tag and their
term-value tags keep their counts at 1 and 5.

DD4. The wall is a Def-tower cost shared by both proofs. The J tower
inherits no relief from lowering the count, because the wall does not
scale with it. The shared shape is the erase route with no placement.

## 2. THE LADDER

The ladder measures the [LJ-1.27-R] walling matrix at the delivered tree.
Each ladder file asserts its count by `refl` BEFORE the placement
witness. Each assertion passed. Then each file reached the placement
witness and exhausted the heap.

| count | probe | result | seconds |
|---|---:|---|---:|
| 0 | `src/ProbeLJ132C0.agda` | WALL | 63.4, then 63.1 |
| 1 | `src/ProbeDD25D.agda` | WALL | 65.4 |
| 2 | `src/ProbeLJ132C2.agda` | WALL | 64.4 |
| 5 | `src/ProbeLJ132C5.agda` | WALL | 62.9 |
| 17 | [LJ-1.27-R], old tree | WALL | 55.5 |

The count-17 figure comes from `_build/lj-1.27-review.md:142`. The other
four figures are from this session.

The controls, same session, one process:

| probe | content | result | seconds |
|---|---|---|---:|
| `src/ProbeLJ132Ctrl1.agda` | count 1, unplaced witness only | GREEN | 3.6 |
| `src/ProbeLJ132Ctrl0.agda` | count 0, unplaced witness, delivered erase | GREEN | 2.6 |
| `src/ProbeLJ132Small0.agda` | count 0, small reader, placed | GREEN | 3.2 |
| `src/ProbeLJ132NotD0.agda` | `Δ₀ (∀̇ φ)` and `Δ₀ (∃̇ φ)` are empty | GREEN | 1.8 |
| `src/ProbeLJ132Counts.agda` | the delivered counts, re-verified | GREEN | 1.0 |

All runs used `GHCRTS="-A64m -I0 -M8g"`, one process, cold. Interfaces
live in `_build/2.8.0/agda/src/`. I never raised the cap. I never
deleted an interface next to a source file.

## 3. WHERE THE BOUNDARY IS

There is no count boundary. The wall is present at count 0. The only
boundary is placement versus no placement.

The wall time is flat in the count. The four ladder points give 63.1,
65.4, 64.4 and 62.9 seconds. The spread is about 4 percent. I report it
as run noise. The count-0 point reproduced at 63.4 and 63.1 seconds.

## 4. THE REAL CLAUSES

The delivered clause forms are not Delta-0 formulas. `existClauseAt` at
`src/L/Coding/Model.lagda.md:1614` and `exInClauseAt` at `:1949` use the
frames `unClauseAt` at `:989` and `binClauseAt` at `:897`, which bind
with the unbounded `∀̇`. The readers `tagAtL` at `:586`, `tmValAt` at
`:1701`, `arityTagAtL` at `:763` and `arityTagPairAtL` at `:730` use the
unbounded `∃̇`. `Δ₀` has no constructor for `∀̇` or `∃̇`
(`src/FOL/LevyHierarchy.lagda.md:47-58`). `src/ProbeLJ132NotD0.agda`
machine-checks the consequence: `Δ₀ (∀̇ φ)` and `Δ₀ (∃̇ φ)` are empty
types for every φ.

So the certificate of a placed formula is for the bounded matrix, not
for the delivered clause as a whole. The ladder measures that matrix at
the delivered counts. The matrix is [LJ-1.27-R]'s walling clause in
`src/ProbeDD25D.agda`. At the delivered tree it has count 1: its only
constant is `con (numeralL 8)`, and `consAtL` is constant-free after
[LJ-1.31]. Counts 2 and 5 add the real clause's tag numerals in bounded
positions.

What the counts mean in the delivered tree: `existClauseAt`'s one
constant is the arity tag `# 8` inside `arityTagAtL`. `exInClauseAt`'s
five constants are the arity tag `# 11` plus the term-value tags `# 1`
and `# 0` from `tmValAt`, counted twice because `extAt` at
`Model.lagda.md:662-664` is a biconditional. The machine-verified
constant list is 11, 1, 0, 1, 0. This also explains the [LJ-1.31]
report's unlocated `1, 0` pair.

## 5. THE LAW

The wall is a full-tree placement cost. It does not depend on the
constant count.

The quantitative clause for P-u (`dev/LESSONS.md:2908`): a Levy witness
travels along a placement at no count. On the [LJ-1.27-R] clause matrix,
the placed witness exhausts 8 GB in 62.9 to 65.4 seconds at counts 0,
1, 2 and 5. The same matrix without the placement checks in 2.6 to 3.6
seconds. A small count-0 formula places in 3.2 seconds. The cost tracks
the formula tree, not the constants.

## 6. ARCHIVE USED

- `src/ProbeDD25D.agda` in full. It is the walling clause and the
  placement witness. I re-ran it at the delivered tree: WALL, 65.4 s.
- `_build/lj-1.27-review.md:114-166`. Section 4 locates the wall in
  building the placed Delta-0 witness, not in absoluteness.
- `src/ProbeLJ131.agda` in full. It names the delivered forms and their
  counts.
- `_build/lj-1.31-report.md:93-117`. Section 6 records the counts and
  the constant list.
- `_build/lj-1.30-report.md:1-30`. It prices the constant-free
  `consAtL`.
- `_build/lj-1.29-report.md:1-42`. It rules that the crossing keeps the
  shared formula and the placement must go.
- `src/L/Coding/Model.lagda.md` at `:585-586`, `:662-664`, `:730-732`,
  `:763-765`, `:817-819`, `:897-902`, `:989-997`, `:1405-1407`,
  `:1484-1485`, `:1565-1568`, `:1608-1615`, `:1701-1703`,
  `:1879-1891`, `:1940-1950`. These are the delivered clause forms and
  their readers.
- `src/FOL/LevyHierarchy.lagda.md:47-58`. The `Δ₀` constructors have no
  `∀̇` or `∃̇` case.
- `dev/LESSONS.md`: P-u at `:2908`, and P-m, P-t, D-1, D-10, C-12,
  C-22 through `scripts/rules.py --for probe` and `--for recon`.
- `dev/literature/`: nothing bears. This is an elaborator cost
  measurement on this tree's own formulas.

## 7. WHAT I AM NOT SURE OF

- The wall location in the count-2 and count-5 probes is inferred. The
  count-1 wall is located by the control pair: `ProbeDD25D` walls and
  `ProbeLJ132Ctrl1` is green. The count-2 and count-5 probes add only
  tag conjuncts to the same cheap Clause module. I did not build a
  per-count unplaced control for counts 2 and 5.
- The count-0 wall has a mechanism I did not profile. `placeFo` still
  recurses over the whole tree with zero constants, and the witness
  forces the recursion to normalize. The evidence is the control pair:
  the same clause walls placed and is green unplaced.
- The wall times spread from 62.9 to 65.4 seconds. I report the spread
  as noise. I did not repeat the ladder for statistics.
- The count-17 figure is from the old tree. I did not rebuild a
  count-17 clause at the delivered tree.
- The crossing's exact matrix is not in the delivered masters. The
  ladder uses the [LJ-1.27-R] matrix, which is the probe's own bounded
  restatement of the clause content. The delivered clause forms are not
  Delta-0, so they cannot be the placement target themselves.
