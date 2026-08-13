# LJ-1.74: split the twelve, so no module elaborates all of them

Status: COMPLETE, written incrementally per C-22. No commit, no push.
ASD-STE100. This report is `_build/lj-1.74-report.md`.

## 0. THE VERDICT

**THE WALL FOLLOWS THE PEAK, MEASURED, AND THE SPLIT WORKS ONLY ACROSS
SEPARATE AGDA INVOCATIONS.** The ladder breaks between six and nine rows:
three rows green (167.60 s), six rows green (209.82 s), nine rows WALL
(259.74 s), twelve rows WALL (274.99 s re-run this dispatch; 265.18 s
known from `[LJ-1.73]`). Splitting across module boundaries WITHIN one
file does not cure it: four three-row partials plus a composer in one
probe wall at 373.50 s, because the partials' elaborated content
accumulates in the one process. Splitting across separate invocations
does cure it: four partial probe files, each elaborating three rows, are
green (161.42 / 162.23 / 158.72 / 139.02 s), and a composer file that
only applies the partials' already-proved `out`/`back` is green at
28.98 s.

The production form of the split needs separate masters under `src/L/`,
which the brief reserves to the owner. Per the pre-fixed abort criterion
(D-1): a rung is green and the split shape is green, so this dispatch
STOPS at the measurement. Nothing was wired, and no master was touched.

## 1. THE LADDER

Caliber: `GHCRTS="-A64m -I0 -M8g"`, one process, warm dependencies, cold
probe file, the `[LJ-1.73]` abstract frame (an abstract environment
`γ' : S ^ (11 + n)`, the sixty-nine telescope facts stated at `γ'`, the
where-block forced through `out`/`back` aliases). Every rung keeps
`TwelveAgree`'s FULL 69-fact telescope; only the where-block row count and
the partial conjunction change, so the argument-check floor is constant
and the where-block is the only variable (the isolation `[LJ-1.72]`
CUT2tel set up).

| rung | rows in the where-block | result | seconds | load |
|---|---:|---:|---:|---|
| 3 | Mem, Eq, And | green | 167.60 | 3.80 to 4.14 |
| 6 | + Or, Imp, Neg | green | 209.82 | 3.80 to 4.85 |
| 9 | + Top, Bot, Exist | **WALL** | 259.74 | 4.57 to 5.94 |
| 12 | + Forall, AllIn, ExIn (control) | **WALL** | 274.99 re-run; 265.18 known | 13.47 to 27.63 |

The two walls are heap exhaustion at the C-12 cap (exit 251, "Heap
exhausted; Current maximum heap size is 8589934592 bytes"), not type
errors and not load: the rung-12 load rose during its run, but a heap wall
is an allocation event at a fixed cap. The rung-12 control file is the
`[LJ-1.73]` probe verbatim (module renamed only), so the re-run and the
known figure measure the same shape.

The decisive comparisons:

| comparison | result |
|---|---|
| same telescope, empty body (`[LJ-1.72]` CUT2tel) | green, about 105 s |
| six rows in one module (this dispatch) | green, 209.82 s |
| nine rows in one module (this dispatch) | **WALL**, 259.74 s |

The sixty-nine argument checks are affordable. The wall is the built
formula content inside the rows (P-t), and the count at which one process
dies is between six and nine rows.

## 2. THE SPLIT SHAPE

Two split shapes were measured:

| split shape | files | result | seconds |
|---|---:|---|---:|
| one file: four three-row partials + one composer (E) | one probe | **WALL** | 373.50 |
| separate invocations: four partial files + one composer file (P0..P3, F) | five probes | **green** | 161.42 / 162.23 / 158.72 / 139.02 / 28.98 |

Each partial module proves a partial conjunction of three rows (rows 0-2,
3-5, 6-8, 9-11), keeps the full sixty-nine-fact telescope, and is applied
at the abstract frame in its own file. The composer file imports the four
partials and applies their exported `out`/`back` as functions at the
frame's facts, conjoining the results:

```text
twelveB = p0b ∧̇ (p1b ∧̇ (p2b ∧̇ p3b))
out h   = ( P0.out h , ( P1.out h , ( P2.out h , P3.out h ) ))
```

The composer does NOT re-apply the rows: it uses the partials' already
elaborated `out`/`back`, whose bodies were checked in the partials' own
processes. That is conjoining results, not re-exporting a target, so
P-w's interposition finding does not bite.

The one-file split (E) walls because module instances in one process keep
their elaborated content live: four telescopes and twelve rows in one
heap exceed the cap, although each three-row module alone is green.

## 3. THE QUESTION: TOTAL OR PEAK

**The wall follows the peak, MEASURED.** Six rows in one process are
green; nine rows in one process wall. The one-file split (E) walls at
373.50 s even though no single module elaborates more than three rows,
MEASURED: the peak is bounded per PROCESS, not per module instance.
Splitting across separate invocations bounds the peak per process, and
the whole split is green, MEASURED.

The wall does NOT follow total seconds, MEASURED: the separate-invocation
split's total check time (about 650 s across five processes) is far larger
than the twelve-row single process (about 275 s to the wall), yet the
split is green and the single process is not. Total seconds predict
nothing; per-process peak decides.

## 4. NEGATIVES AND THEIR STATUS

1. The wall follows the total: **MEASURED FALSE**. The split's total is
   about 650 s and green; rungs 9 and 12, about 260 and 275 s in one
   process, wall. The deciding claim is the peak (item 2), MEASURED.
2. The wall follows the peak, with the peak bounded per module instance:
   **MEASURED FALSE as stated**. E, four three-row modules in one file,
   walls at 373.50 s. The peak is bounded per process.
3. The wall follows the peak, with the peak bounded per process:
   **MEASURED TRUE**. Each partial file is green; the composer file is
   green at 28.98 s.
4. The split composition cannot be built at all in this shape:
   **MEASURED FALSE**. The separate-invocation split checks green.
5. The composer re-applies the rows: **MEASURED FALSE**. F checks in
   28.98 s and its body applies the imported `out`/`back` functions. The
   mechanism (an imported function application does not re-elaborate the
   body) is INFERRED from Agda semantics; the green result is MEASURED.
6. Twelve row applications in one module are affordable at the C-12 cap:
   **MEASURED FALSE**. The wall appears at nine rows.
7. The wall is load: **MEASURED FALSE**. The exits are heap exhaustion at
   a fixed cap, allocation events; the rung-12 load rose during its run
   and cannot cause a heap wall.
8. The sixty-nine argument checks are the wall: **MEASURED FALSE**.
   Rungs 3 and 6 pay the same floor and are green; `[LJ-1.72]` CUT2tel
   measured the empty-body floor at about 105 s.

The deciding claims are items 2 and 3, both MEASURED.

## 5. THE DD4 ANSWER

The split is more modules and the same content. No row is dropped and no
statement is weakened: a partial conjunction of three rows is a partial
conjunction, not a weakening, and the full sixty-nine-fact telescope is
kept at every rung and in every partial.

The partials are generic in the slots exactly as the rows are, MEASURED
by construction: each partial module takes the same fifteen slots
(`N0`..`N11`, `t0`, `t1`, `K : Fin (5 + n)`) and the per-row facts at an
abstract environment, the same parameter shape as `TwelveAgree` and the
rows it applies. The composer is generic in the same slots.

Whether the J tower inherits the split unchanged: **INFERRED, NOT
MEASURED**. The split is the same content in more modules, so a J tower
that states the same telescope at its own frame would apply the same
partials and the same composer; but no J-site measurement exists, and the
J tower's masters would have to adopt the separate-invocation shape,
which is the owner's architecture call. No inference here sets a verdict
on the J tower.

## 6. THE CONVERGENCE ANSWER

NOT CLOSING in the one-module form. `TwelveAgree` as a single module
cannot be consumed at the C-12 cap: nine rows wall, MEASURED. The
composition CAN be built green as a split across separate invocations,
MEASURED (four partial files plus a composer file, all green), but that
production shape requires separate masters under `src/L/`, which the
brief reserves to the owner. Per the pre-fixed abort criterion, this
dispatch ends at the measurement: `SatGraphAgree` is not wired, and
`LeafAgree`, `levelIn` and `cover` are untouched.

## 7. ARCHIVE USED

- `_build/lj-1.73-report.md`, read WHOLE. TOOK the abstract wall
  (265.18 s), the probe to extend, and the abort discipline.
- `src/ProbeLJ173A.agda`, read WHOLE (7,038 lines). TOOK the
  `TwelveAgree` module (`:6386`), the `AbstractFrame` module (`:6761`)
  and the sixty-nine-fact telescope text that every rung and partial was
  generated from.
- `_build/lj-1.72-report.md`, read WHOLE. TOOK sections 1a and 1b (the
  per-row repair), section 4 (the wall table; CUT2tel's 105 s empty-body
  floor) and the where-block mechanism.
- `_build/lj-1.69-report.md`, read WHOLE. TOOK the one-row 3.6 s
  measurement and the finding that a module application is paid at USE,
  which is why every rung and partial forces its where-block through
  `out`/`back` aliases.
- `_build/lj-1.71-report.md`, read WHOLE. TOOK the refutation the per-row
  form answers.
- `dev/LESSONS.md`, read WHOLE for P-t (`:2601-2632`), P-w as amended
  (`:3094-3256`), C-38 (`:3427-3477`), C-35 (`:3200-3242`), P-o
  (`:2509-2532`), P-n (`:2483-2508`), P-m (`:2460-2482`). TOOK P-t (the
  cost follows the built formula content, so the where-block walls at any
  frame), P-w (a composer that conjoins results is not an interposition),
  C-12 (the cap and one-process discipline).
- `src/L/Condensation.lagda.md:6412-6470`, read. TOOK the master's
  `TwelveAgree` telescope, unchanged by this dispatch.
- `archive/rud-route/`, SHAPE only (README and file list). Took nothing.

## 8. LITERATURE USED

Nothing in the literature prices a spelling. One line, nothing spent.

## 9. GATES

`scripts/check-fences.py --check` clean (84 masters).
`scripts/lint-prose.py --check` exit 0.
`scripts/lint-agda.py --check` exit 0.
`scripts/ledger.py --brief`: standing 27,673 lines over 82 masters,
measured from HEAD.
No `make check`, per the brief. No commit, no push.

The working tree is byte-identical to the dispatch start at `787044d`:
`git status --porcelain` empty, `git diff HEAD --stat` empty. The probes
(`src/ProbeLJ174A..F.agda`, `src/ProbeLJ174P0..P3.agda`) and this report
are gitignored by design. `src/L/Condensation.lagda.md`,
`src/L/Coding/` and `src/Everything.lagda.md` are untouched.
