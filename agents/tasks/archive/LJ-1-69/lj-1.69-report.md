# LJ-1.69: price one discharge, the number the campaign does not have

Status: COMPLETE, written incrementally per C-22. No commit, no push.
ASD-STE100. This report is `_build/lj-1.69-report.md`.

## 0. THE VERDICT

**One row module at the discharge frame costs about 3.6 s, MEASURED
(median of three interleaved pairs, spread 2.7 to 5.8 s).** The frame is
the `RowMem` shape of `src/ProbeLJ155B.agda:71-137`: the twelve-frame
telescope of seventeen site facts, one `MemAgree` application, and the
`out`/`back` aliases. Times thirteen, the discharge projects to about
47 s, 35 to 75 s across the spread. That is 15 to 32 times the wing's
2.33 s residual. **The discharge alone exceeds the wing's whole budget,
under every reading of the frame shape.**

The brief's literal instrument does not register at this site. Three
extra UNUSED module-level applications cost about 0.09 s each, inside the
noise, and `agda --profile=definitions` shows that no copy of the applied
module is elaborated at all. Unused module-level instance bindings are
lazy. This is a MEASURED negative for the instrument's shape, and it is
the first price of a row application in either direction: the copy is
paid when the application is USED, not when it is written.

## 1. THE PROBE

The instrument is `[LJ-1.66]`'s, applied at the discharge frame:

1. Pick one row module. `MemAgree` (`src/L/Condensation.lagda.md:4117`,
ends `:4204`; exports `φB`, `out`, `back`: three public definitions,
verified by the profile below) because its `out`/`back` are exactly
`mem-out`/`mem-back` of `TwelveAgree` (`:6406`).
2. Add N = 3 extra applications at the frame the discharge would use, as
   unused bindings.
3. Measure `L.Condensation` cold, three runs each side, same session,
   gate caliber, loads reported.
4. Unit cost = delta / N.

The discharge frame does not exist in the master yet, so the instrument
built it: a private module with the probe's `RowMem` telescope (17 site
facts at `γ : S ^ (11 + n)`, slots `suc (suc zero)`, `suc zero`, `zero`,
and the six-successor lifts of `N0`, `K`, `t0`, `t1`) and the application

```text
module A = MemAgree {11 + n} (suc (suc zero)) (suc zero) zero
  (suc (suc (suc (suc (suc (suc N0))))))
  (suc (suc (suc (suc (suc (suc K))))))
  (suc (suc (suc (suc (suc (suc t0))))))
  (suc (suc (suc (suc (suc (suc t1)))))) γ
  tagEq numK innerK pairK codesK valK t0eq t1eq t0K tmKeyK num1K
  envK entryK arSubK envInK valV valW
```

Three states were measured:

| state | content |
|---|---|
| S0 | the as-placed tree (dispatch start, zero `MemAgree` applications) |
| S1 | S0 plus the discharge-frame module with ONE real application and `out`/`back` aliases |
| S2 | S1 plus THREE unused extra applications (`X1`, `X2`, `X3`), verbatim copies of the first |

The states isolate what the brief's arithmetic needs: S2 minus S1 is the
pure cost of the three extra applications, and S1 minus S0 is the cost of
one row module as the discharge writes it.

Caliber: cold module (own interface moved aside and restored by
`scripts/check-timing.py time_module`), warm dependencies,
`GHCRTS="-A64m -I0 -M8g"` (the C-12 cap this brief states), one process,
strictly sequential runs, same session. Wall seconds come from
`time_module`, the gate's own timer. Load comes from `uptime` before each
run. The sandbox has no `sysmond`, so `pgrep` fails closed and
single-process discipline is procedural, exactly as
`_build/lj-1.62-report.md` documented.

The machine carried 4 users through the session. The load fell from 190
at the start to about 3 to 5. Every absolute figure carries the caveat.
The S0 and S1 states were re-measured interleaved at the stable low load
(three pairs), because the early high-load runs are not comparable.

## 2. THE MEASUREMENTS

All times are cold wall seconds of `L.Condensation`, one process,
`GHCRTS="-A64m -I0 -M8g"`.

| state | run 1 | run 2 | run 3 | run 4 | run 5 | run 6 | run 7 | run 8 | run 9 | mean | load |
|---|---:|---:|---:|---:|---:|---:|---:|---:|---:|---:|---:|
| S0 early | 108.126 | 109.165 | 106.335 | | | | | | | 107.875 | 34 to 64 |
| S0 fresh | 106.124 | 106.197 | 106.742 | | | | | | | 106.354 | 3.6 to 5.1 |
| S1 | 112.477 | 108.476 | 109.557 | 110.245 | 110.194 | 109.083 | 112.015 | 109.417 | 109.731 | 110.133 | 2.9 to 49 |
| S2 | 111.438 | 110.546 | 110.349 | 110.817 | 110.062 | 109.194 | | | | 110.401 | 2.4 to 5.0 |

S1 runs 7 to 9 and S0 runs 4 to 6 were interleaved at stable load, one
pair at a time. The paired deltas are 5.818 s, 2.675 s and 3.607 s. The
ranges are disjoint: S0 fresh is 106.124 to 106.742 s; S1 fresh is
109.417 to 112.015 s.

The deciding claims:

1. One row module at the discharge frame: **3.6 s (median of the three
   interleaved pairs, spread 2.7 to 5.8 s), MEASURED.** The S1 and S0
   ranges do not overlap.
2. The three extra unused applications: **0.268 s total, 0.089 s each,
   inside the noise, MEASURED as a null result.** The profile below shows
   why: no copy of the applied module is elaborated.

## 3. THE PROFILE, AND WHY THE INSTRUMENT REGISTERS NOTHING

`agda --profile=definitions` on the S2 tree (cold, same cap) shows
`L.Condensation.RowMem169.row` at 52 ms, `RowMem169.out` at 34 ms and
`RowMem169.back` at 34 ms: the frame's own definitions. There are NO
`RowMem169.A.*`, `X1.*`, `X2.*` or `X3.*` rows. The copies do not exist
as elaborated definitions.

The module application is lazy at module level. An unused
`module X1 = MemAgree ...` binding costs nothing until something uses
`X1`. What the discharge pays is the USED surface: the `row` formula, the
`out` and `back` aliases, about 120 ms per row at this frame. This is why
`[LJ-1.66]`'s instrument worked there and fails here: its extra
applications were let-bound inside proof bodies, where Agda elaborates
eagerly. The mechanism statement is INFERRED from Agda 2.8.0 semantics;
the observation (zero copies in the profile, zero wall delta) is
MEASURED.

The profile also attributes the frame's 3.6 s. Only about 0.12 s
is the named definitions. The rest is the telescope: seventeen fact
types, four of which state satisfaction over the BUILT trees `envSetAt`,
`envOverAt` and `tmValAt` (`envK`, `envInK`, `valV`, `valW` in the
frame). Those are P-t content, and the profile puts them in
`Miscellaneous`. The built-tree mechanism is INFERRED from the type
shapes; the size of the telescope term (about 3.5 s) is MEASURED as the
residual.

## 4. THE ARITHMETIC

The unit the discharge pays, one row module at the twelve frame, is
**3.6 s** (median; the three interleaved pairs give 2.7, 3.6 and 5.8 s,
and the two tighter pairs give 2.7 to 3.6 s). The brief's count of the
band is thirteen row modules. Times thirteen:

```text
3.6 s x 13 = 46.8 s        (spread 35.1 to 75.4 s)
```

Against the wing's 2.33 s residual, that is 15 to 32 times the whole
remaining budget. Against the wing's ceiling, the discharge alone is
about 45 percent of the module's current check time (about 106 s), for a
few hundred lines of wiring.

**The discharge alone exceeds the wing's whole budget. MEASURED for one
row (3.6 s > 2.33 s); the factor of 15 to 32 is the ×13
projection over the band, INFERRED as linear.**

The twelve hypothesis pairs of `TwelveAgree` name twelve rows; the
brief's thirteen includes one more band module. At twelve, the projection
is 32.4 to 69.6 s across the spread. The verdict does not change.

The cheapest possible reading also exceeds the budget. If the wiring
shares ONE frame instead of writing one per row, it pays the frame once
(3.2 to 3.6 s) plus thirteen used surfaces (about 0.12 s each per the
profile, 1.6 s total): about 4.8 to 5.2 s, still over twice the
2.33 s residual. The wiring's remaining pieces (the `TwelveAgree`
instantiation and the composition) are additional and were not priced
here.

## 5. THE DD4 ANSWER

The row modules are the layer the J tower inherits. The application
surface cost, about 0.12 s per row, and the frame cost, about 3.6 s, are
MEASURED at the L tower's twelve frame. That the J tower pays the same
numbers is INFERRED: the band and the frame shape are the ones the probe
ports, but no J-site measurement exists.

DD4's two ends meet in the swing factor. Writing one frame per row pays
the 3.6 s telescope thirteen times: about 47 s. Writing ONE
generic frame, the seventeen facts parameterized by the row tag, pays it
once plus the thirteen used surfaces: about 5 s. "Write it generic" is
exactly the lever that separates the two readings, and it is the shape
`KFacts` already took for the other fact family at `:5674-5725` (the
LJ-1.62 -30 s win). The generic frame is NOT priced here; the brief
forbids a cure.

## 6. THE CONVERGENCE ANSWER

The obligation is not renamed. The number the campaign lacked is now
measured: one row's discharge frame costs about 3.6 s at this site, and
the thirteen-row discharge projects to about 47 s, 15 to 32 times the
2.33 s residual. The discharge alone exceeds the wing's whole budget
under every reading of the frame shape. The residual is not reachable
through any per-application lever, because the applications themselves
are cheap (0.12 s used, 0 s unused): the cost sits in the frame
telescopes, whose heavy types state satisfaction over built formula
trees. That points at P-w class (c), cheaper types on the copied
definitions, and at DD4's generic frame, as the only directions with
purchase. Both are unpriced here, per the brief.

## 7. NEGATIVES AND THEIR STATUS

1. One row application costs minutes, P-w's worst case: **MEASURED
   FALSE**. The module-level application is lazy. The used surface is
   about 0.12 s per row (profile: `row` 52 ms, `out` 34 ms, `back`
   34 ms), and the frame is about 3.6 s.
2. The brief's instrument, three unused extra applications, registers
   the copy cost: **MEASURED FALSE**. S2 (six runs, mean 110.401 s)
   minus S1 (nine runs, mean 110.133 s) is 0.268 s, 0.089 s per
   application, inside the noise; one interleaved pair was negative; the
   profile shows no `X1`/`X2`/`X3` definitions.
3. An unused module-level application is elaborated: **MEASURED FALSE**
   at this site. The profile has no rows for the unused instances.
   That the same holds for let-bound applications is **INFERRED NOT
   MEASURED**: `[LJ-1.66]`'s let-bound extras measured 1.016 s each, so
   the two shapes behave differently.
4. The frame telescope is cheap parameterized content: **MEASURED
   FALSE** as a rate. The 72 in-fence lines of the frame cost about
   3.6 s, 0.038 to 0.081 s per line across the pair spread, above the
   parameterized band (0.01 to 0.013 s per line) and at or above the
   wiring's own measured marginal rate (0.045 to 0.047 s per line). The
   built-tree mechanism is INFERRED via P-t from the four heavy fact
   types.
5. The discharge fits inside the 2.33 s residual: **MEASURED FALSE for
   one row** (3.6 s > 2.33 s). The ×13 projection making it 15 to 32
   times the residual is INFERRED as linear over the band.
6. A shared single frame brings the discharge under the residual:
   **MEASURED FALSE** as arithmetic over measured parts (4.8 to 5.2 s
   versus 2.33 s); the shared-frame shape itself is INFERRED, since the
   master has no such frame.
7. The J tower pays the same per-row cost: **INFERRED, NOT MEASURED**.
   The band and frame shape port, but no J-site measurement exists. An
   inference sets no verdict on the J tower.
8. The working tree is back to the dispatch start: **MEASURED**. 6,390
   in-fence lines; `git diff --stat` reads 956 insertions and 79
   deletions, identical to the dispatch start; no `RowMem169` remnant;
   fences and both linters clean; the reverted tree checks green cold
   (106.509 s at load 5.01 / 5.14 / 7.52).

## 8. ARCHIVE USED

- `_build/lj-1.66-report.md`, read WHOLE. TOOK section 1's instrument
  (N extra applications, cold three runs each side, unit = delta / N),
  the 1.016 s `EnvSet` unit, and the gate-caliber protocol. Its unused
  bindings were let-bound; this dispatch measured the module-level shape
  and found it lazy.
- `_build/lj-1.68-report.md`, read WHOLE. TOOK the export-count
  discipline (boundary at `:2873`, `TmVal` starts `:2874`) and the
  revert protocol. Applied here: `MemAgree` ends at `:4204`.
- `_build/lj-1.66-review.md` section E.1, read. TOOK P-w's copy
  semantics and the class split. This dispatch measured that the copy is
  lazy at module level and paid at use.
- `_build/lj-1.62-report.md`, sections 2-3. TOOK the wiring's 0.045 to
  0.047 s per line (`:87-88`) and the P-n profile attribution.
- `dev/LESSONS.md`: P-w (`:3094-3256`), P-m (`:2460-2482`), P-n
  (`:2483-2508`), P-l (`:2305-2400`), P-t (`:2601-2632`), P-q
  (`:2633-2669`), P-p (`:2670`), C-31 (`:1855`), C-32 (`:2947`),
  C-33 (`:2987`), C-34 (`:3144`), C-35 (`:3173`), D-29 (`:3215`),
  C-36 (`:3257`), D-30 (`:3305`), C-37 (`:3354`), D-8 (`:1377`),
  D-26 (`:1676`), each read WHOLE. TOOK P-t (built trees unfold, which
  explains the frame telescope cost), P-q (line levers are not seconds
  levers), D-30 (a consumer audit cannot make required content
  cheaper), and C-35 (delivered-and-unconsumed is not delivered).
- `scripts/rules.py --for build` and `--for probe`, every statement.
- `archive/rud-route/`, SHAPE only (README and file list), per the
  brief. Took nothing from it.
- `src/L/Condensation.lagda.md`: `TwelveAgree` (`:6406-6604`),
  `MemAgree` (`:4117-4204`), the `KFacts` record (`:5674-5725`).
- `src/ProbeLJ155B.agda` section 6 (`:71-137`): the discharge frame the
  instrument mirrors. `src/ProbeLJ161A.agda`: the shape the master
  carries.

## 9. LITERATURE USED

Nothing in the literature prices a spelling. Spend nothing.

## 10. GATES

`scripts/check-fences.py --check` clean (84 masters).
`scripts/lint-prose.py --check` exit 0 on the edited master.
`scripts/lint-agda.py --check` exit 0 on the edited master.
`scripts/ledger.py --check` clean; standing 26,706 lines over 82
masters; `L.Condensation` counts 6,390 in-fence lines in the working
tree, the dispatch-start figure.
The reverted tree checks green cold at 106.509 s (load 5.01 / 5.14 /
7.52), and the dispatch-start interface was restored to the cache.
No `make check` was run, per the brief. No commit, no push. The working
tree carries the dispatch-start placement in
`src/L/Condensation.lagda.md` and this report; no probe file was left
behind. Untouched: `src/L/Coding/`, `src/Everything.lagda.md`, all
other masters, all probes. The final `L.Condensation` source is
byte-identical to the dispatch start (verified by line count, diff stat
and the absence of any instrument remnant).
