# LJ-1.75: give each partial only the facts its rows use

Status: COMPLETE, written incrementally per C-22. No commit, no push.
ASD-STE100. This report is `_build/lj-1.75-report.md`.

## 0. THE VERDICT

**THE FLOOR SCALES WITH THE FACT COUNT, MEASURED, AND THE SPLIT GETS
CHEAPER BY MORE THAN THE FRACTION REMOVED.** Each six-row half uses 43 of
the sixty-nine facts. A six-row partial carrying only its 43 facts is
GREEN at **122.45 s** (quiet run; 125.02 s on a busy machine), against
the 209.82 s full-telescope figure. The implied two-partial total is
**2 x 122.45 + 28.98 = 273.88 s**, against the brief's 448.62 s
(2 x 209.82 + 28.98). That is 174.74 s less, 38.9 percent cheaper,
while the telescope shrank by 26 of 69 facts, 37.7 percent.

Per the pre-fixed abort criterion (D-1): the reduced-fact six-row partial
is green and cheaper. STOP at the one comparison. Nothing was wired, and
no master was created or touched.

## 1. THE FACT COUNTS

The sixty-nine facts are the repaired per-row telescope
(`src/ProbeLJ174B.agda` `TwelveAgree6` header, `:6386-6590`, and the
identical `AbstractFrame6` telescope, `:6678-6955`). Each row's
application passes the facts it consumes; the union over a half is what
that half's partial telescope must carry.

| rows | row modules | facts used | facts dropped | shared with the other half |
|---|---:|---:|---:|---:|
| 0 to 5 | Mem, Eq, And, Or, Imp, Neg | **43** | 26 | 17 |
| 6 to 11 | Top, Bot, Exist, Forall, AllIn, ExIn | **43** | 26 | 17 |

The halves' used sets are disjoint in the 52 half-specific facts and share
17; the union is exactly the sixty-nine. Both halves are 43, so the fact
reduction per partial is the same.

Per-row consumption, from the applications in the `[LJ-1.74]` probes (the
master's twelve applications carry the same sets,
`src/L/Condensation.lagda.md:6594-6671`):

| row | module | facts consumed | count | evidence |
|---|---|---:|---:|---|
| 0 | Mem | tagEq0 numK0 innerK pairK codesK valK t0eq t1eq t0K tmKeyK num1K envK-mem entryK arSubK-mem envInK-mem valV valW | 17 | ProbeLJ174B:6586-6591 |
| 1 | Eq | same shape with tagEq1 numK1 | 17 | ProbeLJ174B:6593-6598 |
| 2 | And | tagEq2 numK2 innerK pairK codesK valK transK subK₁-and subK₀-and someEnv | 10 | ProbeLJ174B:6600-6604 |
| 3 | Or | tagEq3 numK3 innerK pairK codesK valK transK subK₁-and subK₀-and someEnv | 10 | ProbeLJ174B:6606-6610 |
| 4 | Imp | tagEq4 numK4 innerK pairK codesK valK subK₁-imp subK₀-imp envK-imp entryK arSubK-imp envInK-imp | 12 | ProbeLJ174B:6612-6616 |
| 5 | Neg | tagEq5 numK5 innerK codesK-un valK-un keyK-neg subK-neg envK-neg entryK arSubK-neg envInK-neg | 11 | ProbeLJ174B:6618-6622 |
| 6 | Top | tagEq6 numK6 innerK codesK-un valK-un envK-top entryK arSubK-top envInK-top | 9 | ProbeLJ174C:6624-6628 |
| 7 | Bot | tagEq7 numK7 innerK codesK-un valK-un | 5 | ProbeLJ174C:6630-6633 |
| 8 | Exist | tagEq8 numK8 innerK codesK-un valK-un succK keyK-un subK-un envK-neg entryK arSubK-neg envInK-neg consK-exist | 13 | ProbeLJ174C:6635-6641 |
| 9 | Forall | tagEq9 numK9 innerK codesK-un valK-un succK keyK-un subK-un envK-neg entryK arSubK-neg envInK-neg consK-forall | 13 | ProbeLJ174D:6643-6649 |
| 10 | AllIn | tagEq10 numK10 innerK pairK codesK valK succK-allin keyK-allin subK-allin envK-allin entryK arSubK-imp envInK-imp t0eq t1eq t0K tmKeyK num1K wKfact consK-allin | 20 | ProbeLJ174D:6651-6656 |
| 11 | ExIn | tagEq11 numK11 innerK pairK codesK valK succK-allin keyK-allin subK-allin envK-allin entryK arSubK-imp envInK-imp t0eq t1eq t0K tmKeyK num1K wKfact consK-allin | 20 | ProbeLJ174D:6658-6663 |

The seventeen shared facts are `innerK`, `pairK`, `codesK`, `codesK-un`,
`valK`, `valK-un`, `t0eq`, `t1eq`, `t0K`, `tmKeyK`, `num1K`, `entryK`,
`envK-neg`, `arSubK-neg`, `arSubK-imp`, `envInK-neg`, `envInK-imp`.

Rows 0 to 5 drop the twenty-six facts only rows 6 to 11 use: `tagEq6` to
`tagEq11`, `numK6` to `numK11`, `envK-top`, `envK-allin`, `arSubK-top`,
`envInK-top`, `wKfact`, `succK`, `keyK-un`, `subK-un`, `consK-exist`,
`consK-forall`, `succK-allin`, `keyK-allin`, `subK-allin`,
`consK-allin`. Rows 6 to 11 drop the mirror set (`tagEq0` to `tagEq5`,
`numK0` to `numK5`, and the Mem/And/Or/Imp/Neg-only facts).

No row of either half names a fact of the other half's set in its
application. The counts are read from the applications, not inferred from
the row parameter lists: the row modules' own parameter names are
generic (`tagEq`, `envK`, `succK`), and the mapping to the frame's
sixty-nine is the argument list of each application
(`src/L/Condensation.lagda.md:6594-6671`, per-row ranges in the table).
The parameter line ranges of the row modules are
`src/L/Condensation.lagda.md:2720-2726` (Bot), `:3336-3350` (And),
`:3386-3400` (Or), `:3455-3464` (Top), `:3520-3530` (Neg),
`:3625-3638` (Forall), `:3727-3740` (Exist), `:4117-4132` (Mem),
`:4668-4688` (AllIn), `:4788-4808` (ExIn), `:4907-4920` (Imp),
`:4998-5013` (Eq).

## 2. THE MEASUREMENT

`src/ProbeLJ175A.agda` is `src/ProbeLJ174B.agda` with the twenty-six
dead facts deleted from both telescopes and from the frame application:
`TwelveAgree6` now carries the 43 facts rows 0 to 5 pass
(`:6386-6509`), `AbstractFrame6` states the same 43 at `γ'`
(`:6604-6727`), and the application passes 43 arguments
(`:6730-6772`). The six row applications and their bodies are verbatim;
no fact a row uses was touched, and no statement was weakened. The diff
against `ProbeLJ174B` is exactly the 26 deleted declarations, twice, and
the 26 deleted arguments, once.

Caliber: `GHCRTS="-A64m -I0 -M8g"`, one process, fresh probe file (no
stale `.agdai`; C-12), warm dependencies, cold probe, per
`[LJ-1.74]`. Load comes from `uptime` before and after each run.

| configuration | facts | result | seconds | load (start / end) |
|---|---:|---|---:|---|
| six-row partial, full 69-fact telescope (`[LJ-1.74]`) | 69 | green | 209.82 | 3.80 to 4.85 |
| same, full telescope, this session's cold control (`ProbeLJ174B`) | 69 | green | 202.11 | 37.00 / 7.92 |
| six-row partial, its own 43 facts, run 1 (`ProbeLJ175A`) | 43 | green | 125.02 | 47.81 / 29.73 |
| six-row partial, its own 43 facts, run 2 (`ProbeLJ175A`) | 43 | green | **122.45** | 7.22 / 7.51 |
| composer (`[LJ-1.74]` F) | - | green | 28.98 | - |

Run 2 is the quiet comparison figure: 122.45 s against 209.82 s. The
delta is 87.37 s, a 41.6 percent reduction, while the telescope shrank
37.7 percent. Run 1 differs by 2.6 s (2.1 percent) at a much higher
load, and the same-session control (202.11 s at load 37 falling to 8)
sits within 4 percent of the quiet reference, so the wall seconds at
this site are not materially load-sensitive at these loads, MEASURED.

**Implied two-partial total: 2 x 122.45 + 28.98 = 273.88 s**, against
2 x 209.82 + 28.98 = 448.62 s. The 28.98 s composer is the measured
four-way composer of `[LJ-1.74]`; a two-way composer for two six-row
partials is not measured, and would only be cheaper, INFERRED.

## 3. DOES THE FLOOR SCALE WITH THE FACT COUNT

**YES, MEASURED.** The 105 s empty-body floor is the sixty-nine argument
checks (`[LJ-1.72]` CUT2tel; `_build/lj-1.72-report.md` section 4). The
43-fact partial's total is 122.45 s against 209.82 s at 69 facts. A
linear-floor projection (105 x 43/69 = 65.4 s of checks plus an unchanged
104.8 s of row content = about 170 s) is above the observed 122.45 s, so
the floor scales at least proportionally, and the observed reduction
exceeds the removed fraction. Where the extra saving comes from (the
row applications' argument elaboration reads the telescope, so fewer
facts cheapen the where-block too, not only the empty-body floor) is
INFERRED from the endpoints; the endpoints themselves are MEASURED.

## 4. THE DD4 TRADE

Per-partial telescopes are less shared statement than one union
telescope. The union states the sixty-nine facts once at the frame. Two
partials state 86 fact parameters: the 52 half-specific facts once each,
and the 17 shared facts twice. The price of the 174.74 s saving is that
statement split and the 17-fact restatement.

The J tower would inherit the split shape, and the split shape is the
owner's architecture call: it needs separate masters under `src/L/`,
which this dispatch does not create. Whether the J tower restates the
facts per partial at its own frame is INFERRED (no J-site measurement
exists); the restatement structure would mirror the L tower's.

Two narrower telescopes are still generic in the slots, MEASURED by
construction: both reduced telescopes take the same fifteen slots
(`N0` to `N11`, `t0`, `t1`, `K : Fin (5 + n)`) and the same abstract
`γ' : S ^ (11 + n)`. Only fact parameters were dropped; no slot was
dropped, and no row application was changed.

## 5. NEGATIVES AND THEIR STATUS

1. A six-row partial carrying only its own facts walls or is not
   cheaper: **MEASURED FALSE**. `ProbeLJ175A` is green at 122.45 s
   (quiet run), exit 0, C-12 cap, against 209.82 s for the full
   telescope.
2. The 105 s floor does not scale with the fact count: **MEASURED
   FALSE**. The reduction (87.37 s, 41.6 percent) exceeds the removed
   fraction (37.7 percent), and the linear-floor projection (about
   170 s) is above the observed 122.45 s.
3. Dropping the 26 facts weakens a row: **MEASURED FALSE by
   construction**. No row 0 to 5 application names a dropped fact
   (`ProbeLJ174B:6586-6622`), the reduced probe keeps those
   applications verbatim, and it checks green.
4. The reduction is a load artifact: **MEASURED FALSE**. Runs 1 and 2
   of the reduced probe differ by 2.6 s across loads 47.81 and 7.22;
   the full-telescope control at load 37 to 8 (202.11 s) is within
   4 percent of the quiet reference (209.82 s).
5. The J tower inherits the narrowing free: **INFERRED, NOT MEASURED**.
   No J-site measurement exists, and the separate-masters split is the
   owner's call. No inference here sets a verdict on the J tower.

The deciding claims are items 1 and 2, both MEASURED.

## 6. THE CONVERGENCE ANSWER

The split is cheaper per partial than the brief priced: 122.45 s against
209.82 s. The cheapest measured production shape is now two six-row
partials of 43 facts each plus a composer, about 273.88 s across three
separate invocations, all green. That shape still needs separate masters
under `src/L/`, reserved to the owner. `SatGraphAgree` is not wired, and
`LeafAgree`, `levelIn` and `cover` are untouched.

## 7. ARCHIVE USED

- `_build/lj-1.74-report.md`, read WHOLE. TOOK the ladder (the 209.82 s
  six-row figure, section 1), the split shape and composer (section 2),
  the per-process peak verdict (sections 3 and 4), the probe list, and
  the abort discipline.
- `src/ProbeLJ174B.agda`, read. TOOK the six-row partial shape
  (`TwelveAgree6` `:6386-6590`, applications `:6586-6622`,
  `AbstractFrame6` `:6678-6955`), which `ProbeLJ175A` was generated
  from. The same-session cold control ran this dispatch (202.11 s).
- `src/ProbeLJ174C.agda` `:6624-6641` and `src/ProbeLJ174D.agda`
  `:6643-6663`, read. TOOK the rows 6 to 11 applications for the fact
  count.
- `_build/lj-1.72-report.md`, read WHOLE. TOOK sections 1a and 1b (the
  repaired per-row telescope) and section 4 (CUT2tel's about-105 s
  empty-body floor).
- `_build/lj-1.70-report.md`, read WHOLE. TOOK section 1's twelve row
  modules' parameter line ranges and the discharge shape.
- `_build/lj-1.73-report.md`, read WHOLE, and `src/ProbeLJ173A.agda`
  (frame shape). TOOK the abstract-frame discipline the partials rest on.
- `dev/LESSONS.md`, read WHOLE for P-t (`:2601-2632`), P-w as amended
  (`:3094-3256`), C-38 (`:3427-3477`), D-30 (`:3332-3381`), P-m
  (`:2460-2482`), P-n (`:2483-2508`). TOOK D-30 (this dispatch prices
  what the consumer, the six rows, needs), P-w class (b) (narrow what a
  consumer reaches; the reduced partial is that narrowing), P-t (the
  cost follows the formula content, so the floor is the argument
  checks), C-12 (the cap), C-22 (incremental writing). Also read the
  brief's remaining mandatory rules: P-c (`:71`), P-h (`:174`), P-i
  (`:203`), P-k (`:2401`), P-l (`:2305`), P-o (`:2509`), P-q
  (`:2633`), P-u (`:2908`), P-v (`:3037`), R-35 (`:782`), R-36
  (`:808`), R-38 (`:829`), R-40 (`:929`), I-5 (`:1196`), C-12
  (`:2075`), C-22 (`:2237`), C-31 (`:1855`), C-32 (`:2947`), C-33
  (`:2987`), C-34 (`:3171`), C-35 (`:3200`), C-36 (`:3284`), C-37
  (`:3381`), D-8 (`:1377`), D-10 (`:1316`), D-26 (`:1676`), D-29
  (`:3242`). Applied: none of the negative-verdict machinery fired.
- `archive/rud-route/`, SHAPE only (README and file list). Took nothing.

## 8. LITERATURE USED

Nothing in the literature prices a spelling. One line, nothing spent.

## 9. GATES

`scripts/check-fences.py --check` clean (84 masters).
`scripts/lint-prose.py --check` exit 0 on this report.
`scripts/lint-agda.py --check` exit 0 on `src/ProbeLJ175A.agda`.
No `make check`, per the brief. No commit, no push.

The working tree is byte-identical to the dispatch start at `00220e7`:
`git status --porcelain` empty, `git diff HEAD --stat` empty. The probe
(`src/ProbeLJ175A.agda`) and this report are gitignored by design.
`src/L/Condensation.lagda.md`, `src/L/Coding/` and
`src/Everything.lagda.md` are untouched.
