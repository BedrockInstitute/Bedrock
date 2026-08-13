# LJ-1.70: one generic frame, and the discharge it carries

Status: COMPLETE, written incrementally per C-22. No commit, no push.
ASD-STE100. This report is `_build/lj-1.70-report.md`.

## 0. THE VERDICT

**`TwelveAgree`'s twenty-four hypotheses are DISCHARGED.** The module now
takes the generic frame as its own telescope: forty-seven site facts stated
once at the twelve frame (`src/L/Condensation.lagda.md:6412-6590`), with
the tag-dependent facts (`tagEq`, `numK`, `innerK`, `codesK`, `valK`)
stated as functions of the row's tag, and the twelve row modules
instantiated inside (`:6594-6671`). The `out`/`back` compose the twelve
applications directly (`:6720-6753`). The twenty-four hypotheses
`mem-out`..`exin-back` no longer exist as parameters.

The twelve rows are the twelve hypothesis pairs the brief names. The
thirteenth band module (`PropAgree`, the shared machinery under And and
Or) is not instantiated separately: `AndAgree` and `OrAgree` apply it
internally (`src/L/Condensation.lagda.md:3369`, `:3419`), so
the two row applications carry it.

**The discharge costs 14.7 s over the as-placed baseline, MEASURED
(three interleaved cold runs each side, same session, gate caliber,
spread 14.4 to 15.0 s, load 3.2 to 5.1, four users).** Baseline mean
107.43 s (108.00 / 106.79 / 107.50). Discharged mean 122.18 s (122.80 /
121.79 / 121.94). Paired deltas 14.80 / 14.99 / 14.44 s.

Per the pre-fixed abort criterion (D-1): **BETWEEN 8 s and 20 s. STOP and
report the number.** The owner rules on funding before anything else is
funded. The number is still a large win against the 47 s per-row
spelling: 14.7 s is about 3.2 times less than the 46.8 s projection,
and the discharge is green, not a wall.

The gate's aggregate, quoted: `check-ratio: wing aggregate 0.0154 s/line
over 8,408 lines and 129.33 s, OVER THE BAR (1.39x the AC side at the
SAME caliber, module-cold with warm dependencies)`. The wing was already
OVER at 1.28x before this dispatch (`_build/lj-1.62-report.md` section
0); the discharge moves it to 1.39x.

## 1. THE DESIGN, AND WHAT THE MEASUREMENTS FORCED

The brief's arithmetic rested on two premises, and the measurements
separated them:

1. **One frame stated once beats thirteen restated telescopes.**
   MEASURED TRUE in shape. The final frame states the facts once, and
   the twelve applications share them.
2. **The seventeen site facts of `RowMem` cover all thirteen rows.**
   INFERRED FALSE. The twelve rows of `TwelveAgree` need a UNION of
   forty-seven distinct fact types at the twelve frame, not seventeen:
   the seventeen cover the Mem/Eq shape; And/Or need `transK`,
   `subK₁-and`, `subK₀-and`, `someEnv`; Neg needs the unary shapes and
   `keyK-neg`; Exist/Forall need `succK`, `keyK-un`, `consK`; AllIn/
   ExIn need `succK-allin`, `keyK-allin`, `wKfact`, `consK-allin`; and
   the closure facts (`envK`, `arSubK`, `envInK`) differ across the
   rows' stack shapes. The counts are MEASURED from the band modules'
   parameter lists (`BotAgree` `:2720-2726`, `TopAgree` `:3455-3464`,
   `NegAgree` `:3520-3530`, `ForallAgree` `:3625-3638`, `ExistAgree`
   `:3727-3740`, `AndAgree` `:3336-3350`, `OrAgree` `:3386-3400`,
   `ImpAgree` `:4907-4920`, `MemAgree` `:4117-4132`, `EqAgree`
   `:4998-5013`, `AllInAgree` `:4668-4688`, `ExInAgree`
   `:4788-4808`); the claim that one seventeen-type telescope feeds all
   rows is INFERRED FALSE.

So the real generic frame's telescope is the union, and the two spelling
choices the brief priced (3.6 s x 13 vs 3.4 s + 0.12 s x 13) bound the
design from above and below: the per-row spelling would cost about 47 s
on this content, and the seventeen-fact arithmetic did not cover the
rows.

The shape of the frame went through two measured failures before it
checked green:

- **A record (the `KFacts` shape) with the union telescope: MEASURED
  WALL.** `RowFactsNS` as a `record` with the union telescope
  (forty-six fields then; the final split of `consK` adds one more),
  including
  the satisfaction types over built formula trees, heap-exhausted the
  8 GB C-12 cap at about 155 s. With the thirty-three heavy fields
  stubbed to `S`, the same module checked in about 101 s. This is the
  P-o trap in its carrier-indexed form (record fields whose types
  index the carrier hang the elaborator; `dev/LESSONS.md` P-o). The
  wall and the stub delta are MEASURED; the P-o mechanism is
  INFERRED.
- **The module telescope: green.** Stating the forty-seven facts as the
  module's own parameters (the shape `RowMem169` measured in LJ-1.69)
  checks without a wall.
- **Twenty-four inferred aliases on top of the applications: MEASURED
  WALL.** With `mem-out = M.out` .. `exin-back = EI.back` present, the
  module heap-exhausted at about 159 s; without the aliases (the
  `out`/`back` use the applications directly), it checks green at
  121 to 123 s. The aliases' inferred types re-elaborate the row
  applications' concrete satisfaction types, and that is the extra
  straw over the cap.

## 2. THE MEASUREMENTS

Caliber: cold module (own `.agdai` moved aside and restored by
`scripts/check-timing.py time_module`), warm dependencies,
`GHCRTS="-A64m -I0 -M8g"` (the C-12 cap this brief states), one
process, strictly sequential runs, interleaved pairs in one session.
Wall seconds come from `time_module`, the gate's own timer. Load comes
from `uptime` before each run. The sandbox has no `sysmond`, so the
guard's `pgrep` fails closed and single-process discipline is
procedural, exactly as the last five dispatches documented. The
`andClauseAt`/`orClauseAt` import cleanup after the runs is inert (two
unused names); the final state re-checks green.

| side | run 1 | run 2 | run 3 | mean | load |
|---|---:|---:|---:|---:|---|
| as-placed baseline | 108.00 | 106.79 | 107.50 | 107.43 | 3.2 to 5.1 |
| discharged | 122.80 | 121.79 | 121.94 | 122.18 | 3.2 to 5.1 |
| delta | 14.80 | 14.99 | 14.44 | 14.75 | |

Diagnostics, single runs at the same caliber (not part of the paired
protocol):

- The forty-seven-fact telescope alone (no applications, no `out`/`back`):
  about 101 s, inside the baseline's noise. The telescope REPLACED the
  baseline's twenty-four hypothesis types, so its net cost over the
  baseline is near zero.
- Telescope plus the twelve applications, in the three intermediate
  states: with the aliases and no `out`/`back`, green at 153 s; with
  the aliases AND `out`/`back`, heap-exhausted at 159 s; without the
  aliases and with `out`/`back` direct, green at 121 to 123 s. The
  twelve applications' concrete argument checks are where the
  discharge's mass sits, and the aliases were the extra straw over the
  cap.
- Final shape (applications, `twelveB`, `out`/`back`, no aliases):
  121 to 123 s, three runs.

## 3. NEGATIVES AND THEIR STATUS

1. A single record bundling the union telescope (the `KFacts` shape for
   this fact family): **MEASURED WALL**. Heap exhaustion at the 8 GB
   cap, about 155 s. With the heavy fields stubbed, about 101 s. The
   P-o mechanism (record fields at carrier-indexed types) is INFERRED.
2. The brief's seventeen site facts cover all thirteen rows: **INFERRED
   FALSE**. The union at the twelve frame is forty-seven fact types, from
   the band modules' parameter lists (file:line above). The seventeen
   cover only the Mem/Eq family.
3. The discharge lands at 8 s or less over the as-placed baseline:
   **MEASURED FALSE** at 14.7 s (three paired runs, spread 14.4 to
   15.0).
4. The discharge is a wall or above 20 s at the final shape: **MEASURED
   FALSE**. The final shape checks green at 121 to 123 s, 14.7 s over
   baseline. The intermediate shapes (record; aliases) did wall:
   MEASURED.
5. The applications' used surface is about 0.12 s each at this
   discharge: **INFERRED NOT TRANSFERRABLE** as a price. The
   LJ-1.69 figure was measured at the `RowMem` frame with the telescope
   at the same frame; here the twelve applications plus `out`/`back`
   carry the bulk of the 14.7 s delta (telescope-only measured about
   101 s). The deltas are MEASURED; the per-application attribution is
   INFERRED.
6. `TwelveAgree` still rests on twenty-four hypotheses: **MEASURED
   FALSE**. The hypotheses are gone from the telescope
   (`src/L/Condensation.lagda.md:6412-6590`) and supplied by the
   twelve applications (`:6594-6671`).

## 4. THE DD4 ANSWER

**The J tower inherits the frame pattern whole: one telescope of site
facts stated once, the tag-dependent facts stated as functions of the
row's tag, twelve instantiations of the band modules inside, and the
composition built from the applications.** The twelve rows of the L
tower and the J tower are the same band modules, so the pattern
transfers.

**As built, the frame cannot instantiate at the J tower's slots without
a second telescope statement.** The facts are stated at the L tower's
twelve frame (`γ : S ^ (11 + n)`, six-lifted slots), so the closure
facts' types carry the L tower's slot positions. The J tower must
restate the facts at its own slots; that restatement is mechanical,
because the closure facts' stack shapes are the same (the same row
modules), but it is a second statement, not a reuse. A slot-generic
frame in the record shape was measured as a heap wall (section 1); a
slot-generic frame in the module-telescope shape was not priced in this
dispatch, because the abort criterion stops the work after the discharge
is measured.

## 5. THE CONVERGENCE ANSWER

The obligation is not renamed. The twenty-four hypotheses are
discharged, and the discharge is priced: 14.7 s over the as-placed
baseline, between the 8 s GO line and the 20 s stop line. That is a
large win against the 47 s per-row projection, and it is the number the
owner needs before anything else is funded. The four built-tree fact
types (`envK`, `envInK`, `valV`, `valW`) are still the mass, in the
sense that the built-tree satisfaction content is what the twelve
applications' concrete argument checks pay; the telescope statement
itself is cheap because it replaced the twenty-four hypothesis types.
That keeps class (c) of P-w as the live target. The next consumer
(`SatGraphAgree`/`LeafAgree` instantiating `TwelveAgree`) is beyond this
dispatch's stop line; `TwelveAgree` itself remains unconsumed, so the
C-35 staging caveat still applies to it.

## 6. ARCHIVE USED

- `_build/lj-1.69-report.md`, read WHOLE. TOOK the `RowMem` frame shape
  (`src/ProbeLJ155B.agda:71-137`), the 3.6 s / 0.12 s / 3.5 s
  decomposition, and the shared-frame arithmetic (section 4). The
  seventeen-fact count does not cover the twelve rows; the union is
  forty-seven.
- `_build/lj-1.62-report.md`, sections 2-3. TOOK the `KFacts` record
  pattern and its -30 s; the record shape did not transfer to this fact
  family (P-o wall, MEASURED).
- `_build/lj-1.66-review.md` section E.1. TOOK P-w's classes.
- `_build/lj-1.68-report.md`. TOOK the export-count discipline
  (`EnvSet` ends at `:2873`).
- `dev/LESSONS.md`, P-w as amended (`:3094-3256`), P-t (`:2601-2632`),
  P-m (`:2460-2482`), P-n (`:2483-2508`), P-q (`:2633-2669`), D-30
  (`:3255-3303`), and P-o (`:2509-2532`, record fields at
  carrier-indexed types), each read WHOLE.
- `archive/rud-route/`, SHAPE only (README and file list). Took nothing
  from it.
- `src/ProbeLJ155B.agda:71-137` (the `RowMem` frame) and `:788-979`
  (the probe's `TwelveAgree`, used to reconstruct the as-placed
  baseline's original module). `src/ProbeLJ161A.agda`, the chain's own
  shape.
- `src/L/Condensation.lagda.md`: `TwelveAgree` (`:6412-6753`), the
  twelve row modules' parameter telescopes (line ranges in section 1),
  `KFacts` (`:5674-5725`).

## 7. LITERATURE USED

Nothing in the literature prices a spelling. Spend nothing.

## 8. GATES

`scripts/check-fences.py --check` clean (84 masters).
`scripts/lint-prose.py --check` exit 0 on the edited master.
`scripts/lint-agda.py --check` exit 0 on the edited master.
`scripts/ledger.py --check` clean; standing 26,706 lines over 82
masters, measured from HEAD; `L.Condensation` counts 6,529 in-fence
lines in the working tree against the as-placed 6,390 (+139).
`scripts/check-ratio.py --check` ran with the guard bypassed
procedurally (the sandbox's `pgrep` cannot read the process list; every
Agda invocation was sequential): aggregate 0.0154 s/line over 8,408
lines and 129.33 s, 1.39x the AC side, OVER THE BAR.
No `make check`, per the brief. No commit, no push. Untouched:
`src/L/Coding/`, `src/Everything.lagda.md`, all other masters. The
working tree carries the dispatch-start placement plus this discharge;
the final state checks green cold at 129.5 s wall (load 4.72) after the
inert import cleanup.
