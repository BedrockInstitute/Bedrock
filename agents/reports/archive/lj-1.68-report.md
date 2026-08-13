# LJ-1.68: narrow EnvSet to what its consumers reach

Status: COMPLETE, written incrementally per C-22. No commit, no push.
ASD-STE100. This report is `_build/lj-1.68-report.md`.

## 0. THE VERDICT

**Class (b) is measured FALSE at this site.** `EnvSet`'s consumers reach
ten of its eleven exports, and the split that removes the one dead export
**REGRESSED by +3.18 s** (after mean 107.788 s against before mean
104.604 s, three cold runs each side, same session, gate caliber, disjoint
ranges, load bias conservative). The pre-fixed D-1 criterion says: saving
under 1.0 s or any regression stops the dispatch. It stopped here. The
split was reverted; the working tree is byte-identical to the dispatch
start.

This is the first measurement of the copy-count lever in the removal
direction, and it is a negative. The per-application cost does not scale
with the number of copied definitions at the granularity available here
(one removable definition of eleven). The residual 2.33 s is not reachable
through this lever.

## 1. STEP 1, THE CLOSURE, MEASURED BY READING

`EnvSet` (`src/L/Condensation.lagda.md:2761-2873`) exports **eleven**
definitions, not fifteen. The brief's count and the `[LJ-1.66]` review's
sixteen both add five definitions of the adjacent module `TmVal` (`t0eq`,
`t1eq`, `t0K`, `keyK`, `num1K`, `:2875-2888`). `TmVal` starts at `:2874`
and is never applied in this master (`rg "= TmVal"` returns zero hits).
The closure question for `EnvSet` is over its own eleven exports.

The transitive closure of `{out, back, memE-bnd}` inside `EnvSet`:

| definition | line | reachable |
|---|---|---:|
| `out` | 2860 | seed |
| `back` | 2863 | seed |
| `memE-bnd` | 2866 | seed |
| `bnd→over` | 2809 | yes, via all three seeds |
| `over→bnd` | 2835 | yes, via `out` and `back` |
| `app3` | 2781 | yes, via `bnd→over`/`over→bnd` |
| `app3'` | 2792 | yes, via `bnd→over`/`over→bnd` |
| `app2` | 2801 | yes, via `bnd→over`/`over→bnd` |
| `φB` | 2773 | yes, via `out` and `back` |
| `φ` | 2777 | yes, via `out` and `back` |
| `memE-at` | 2870 | **NO** |

`out = extAtB→extAt E K φB φ γ bnd→over over→bnd envInK` (`:2861`);
`back = extAt→extAtB E K φB φ γ bnd→over over→bnd` (`:2864`);
`memE-bnd h z zE = envInK z (bnd→over z (h .fst z zE))` (`:2870`).
`memE-at h z zE = envInK z (h .fst z zE)` references only the parameter
`envInK`; no seed references it. The closure is **ten of eleven**:
proper, and the dead weight is exactly `memE-at`, four lines with a
one-application body.

`memE-at` has zero consumers: `rg "memE-at" src/` returns only its
definition at `:2867` and `:2870`. The eighteen sites use exactly
`E'.out` (9), `E'.back` (9), `E'.memE-bnd` (9), and nothing else
(`rg -o "E'\.[a-zA-Z0-9'→-]+"`: three distinct hits). The review's
"thirteen copied and used never" is not right for `EnvSet` itself:
ten of eleven are reached, one is dead.

## 2. STEP 2, THE SPLIT

The split was built in `src/L/Condensation.lagda.md`, exactly once, and
measured.

The thin module kept the name `EnvSet` so the eighteen sites needed no
edit. It contains the three reached definitions and their closure:
`out`, `back`, `memE-bnd`, `bnd→over`, `over→bnd`, `app3`, `app3'`,
`app2`, `φB`, `φ` (ten definitions).

**The thin module does NOT apply `EnvSet`, and it does not apply anything
that applies `EnvSet`.** All ten definitions are inline bodies copied from
the original module. There is no `module E = EnvSet` anywhere in it. No
interposition was built.

The remainder module `EnvSetMem` carried the identical parameter telescope
and one definition, `memE-at`, inline. No site applies `EnvSetMem`, and
`memE-at` has zero consumers, so the remainder was never applied. If any
consumer of the remainder existed, it is at none of the eighteen sites and
nowhere else in `src/` (MEASURED, `rg "memE-at" src/`).

Statements and proofs did not change. Only where `memE-at` lives moved.

## 3. THE MEASUREMENTS

Caliber: the gate's own, cold module (own interface moved aside and
restored by `scripts/check-timing.py time_module`), warm dependencies,
`GHCRTS="-A64m -I0 -M8g"` (the C-12 cap this brief states), one process,
strictly sequential runs, same session, 4 users on the machine. Wall
seconds come from `time_module`, the gate's own timer. Load comes from
`uptime` before each run. The sandbox has no `sysmond`, so `pgrep` fails
closed and single-process discipline is procedural, exactly as
`_build/lj-1.62-report.md` documented.

| state | run 1 s | run 2 s | run 3 s | mean | spread | load at start |
|---|---:|---:|---:|---:|---:|---:|
| before (as-placed tree) | 107.065 | 103.049 | 103.699 | 104.604 | 4.016 | 6.81, 5.42, 3.53 |
| after (split tree) | 108.880 | 107.210 | 107.274 | 107.788 | 1.670 | 3.20, 3.63, 3.70 |

Delta: **+3.184 s**, in the wrong direction on every run. The run ranges
are disjoint: before is 103.049 to 107.065 s, after is 107.210 to
108.880 s, with a 0.145 s gap between the worst before run and the best
after run. The after side ran at a LOWER mean load (3.51 against 5.25),
so the load bias points against the regression. If load biased anything,
it made the after side look faster. The deciding claim is MEASURED.

All three after runs typechecked green (exit 0; `time_module` returns
`None` on failure and all three returned seconds). The split is
syntactically and type-theoretically sound; the regression is not a failed
check.

The load spread is wider than in `[LJ-1.66]` and `[LJ-1.67]` (before
spread 4.016 s here against 0.775 and 0.847 there), because the machine
carried 4 users at load averages up to 6.81 through the session. The
verdict does not depend on the magnitude: the direction is consistent on
all six runs and the ranges do not overlap.

## 4. WHAT THIS IMPLIES FOR THE WIRING

The wiring's marginal cost is 0.045 to 0.047 s per in-fence line
(`_build/lj-1.62-report.md:87-88`), and its profile attributes that cost
to named definitions of consumed content, `LeafAgree.out`/`back` at
4,113/4,095 ms and `SatGraphAgree.out`/`back` at 1,950/3,289 ms
(`_build/lj-1.62-report.md`, section 3). That is P-n content, not copy
count.

The value of this probe was whether class (b) works at all. It does not
here: the only removable definition was one trivial four-line export, and
removing it regressed. For the wiring, class (b) requires un-consumed
definitions inside the wiring's applied modules. D-30 states the limit
itself: a consumer audit finds unreached generality; it does not make
required content cheaper (`dev/LESSONS.md:3305-3360`). The wiring's hot
definitions are all consumed, so class (b) has no purchase there.

**INFERRED:** the wiring's 0.045 to 0.047 s per line stands, and the
projection that the wing lands about 19 s over at 500 more wiring lines
stands with it. This inference rests on the wiring's measured profile
class, not on the EnvSet measurement.

## 5. THE DD4 ANSWER

Had the split stayed, the J tower would inherit the same thin `EnvSet`
(ten definitions), because the J tower applies the same module by name and
the split was packaging, not content. The remainder module `EnvSetMem`
would remain available to the J tower as an ordinary module; nothing
imports it today, so no J consumer would notice its absence.

The split is REVERTED on the measured regression. The delivered tree gives
the J tower the original eleven-definition `EnvSet`, byte-identical to the
dispatch start. The remainder module does not exist in the delivered tree.

DD4's two ends are unaffected. Nothing shared was deleted: `EnvSet` stays
one generic artifact over abstract slot positions, the shape the J tower
inherits unchanged. The attempted packaging moved one definition and
returned a regression, so the original single module is the DD4 answer
that stands. The D-30 shape that measured 5.45x elsewhere removed whole
un-consumed SECTIONS; here the un-consumed remainder is one cheap
definition, and the arithmetic is different at this granularity.

## 6. THE CONVERGENCE ANSWER

The obligation is not renamed. The copy-count lever, class (b), is now
measured false at this site: narrowing `EnvSet` from eleven exports to the
ten its consumers reach regressed by +3.184 s (MEASURED). The residual of
2.33 s is not reachable through this lever.

The `[LJ-1.66]` review's load-bearing inference, "whether the copy-count
scaling law holds" (section E.8), now has its first removal-direction
measurement. The answer is a negative at the granularity available here:
one removable definition of eleven, and removing it costs more than it
saves.

The remaining named lever for `EnvSet` is class (c), P-t's: the types of
the CONSUMED definitions `out`, `back` and `memE-bnd` mention the built
formula trees `envSetB` and `envSetAt`. Nobody has priced a type-level
move there, and this dispatch does not fund one.

The pending wiring remains the wing's real problem. Its 0.045 to 0.047 s
per line is consumed-content cost, and the wing's completion still
projects about 19 s over its own bar.

## 7. NEGATIVES AND THEIR STATUS

1. The closure is all fifteen: **MEASURED FALSE**. The closure is ten of
   eleven, and `EnvSet` exports eleven, not fifteen; the count conflates
   `TmVal`'s five exports, which no site applies.
2. Class (b) saves 1.0 s or more across the eighteen sites:
   **MEASURED FALSE**. The split regressed by +3.184 s, three cold runs
   each side, same session, gate caliber, disjoint ranges.
3. The split helps: **MEASURED FALSE**. Same numbers as negative 2.
4. The regression is an artifact of load: **MEASURED FALSE**. The after
   side ran at lower mean load (3.51 against 5.25), so the bias points
   against the regression; the direction is consistent on all three runs.
5. `memE-at` is dead weight at every site: **MEASURED TRUE**. Zero
   consumers across `src/`; the eighteen sites use only `E'.out`,
   `E'.back` and `E'.memE-bnd` (nine each).
6. The thin module interposes `EnvSet`: **MEASURED FALSE**. The thin
   module's ten definitions are inline; it contains no `EnvSet`
   application (section 2).
7. Per-application cost scales with the number of copied definitions:
   **MEASURED FALSE** at this granularity. Removing one of eleven
   definitions regressed. The likely mechanism is INFERRED: the added
   remainder module re-checks the same telescope, whose `envInK` type
   mentions the built tree `envOverAt`, and that one-time P-t cost
   exceeds the eighteen sites' savings on one trivial definition.
8. The residual 2.33 s is reachable by narrowing `EnvSet`:
   **MEASURED FALSE**. The narrowing regressed.
9. The result transfers to the wiring's content: **INFERRED**. The
   wiring's hot content is consumed definitions (P-n), where a consumer
   audit cannot remove cost (D-30's own caveat). No measurement was taken
   there. An inference sets no verdict on the wiring itself.
10. The working tree is back to the dispatch start: **MEASURED**. 6,390
    in-fence lines; `git diff --stat HEAD` reads 956 insertions and 79
    deletions, identical to the dispatch start; no `EnvSetMem` remnant;
    fences and both linters clean; consumer re-check green.

## 8. ARCHIVE USED

- `_build/lj-1.66-review.md`, WHOLE. TOOK section 4.1's narrow-face shape
  and its sixteen-count, E.1's P-w evidence, E.5's discriminator, and
  E.8's untested copy-count scaling law, which this dispatch measured.
- `_build/lj-1.66-report.md`, WHOLE. TOOK the 1.016 s unit cost, the
  +10.88 s hoist regression, and the gate-caliber protocol.
- `_build/lj-1.67-report.md`, WHOLE. TOOK the +2.82 s regression and the
  revert-on-regression discipline.
- `_build/lj-1.47-report.md`, WHOLE. TOOK D-30's 5.45x and the
  consumer-audit shape, whose granularity differs from this split.
- `_build/lj-1.62-report.md`, sections 2-3. TOOK the wiring marginal
  class, 0.045 to 0.047 s per line (`:87-88`), and the P-n profile
  attribution of the chain's hot definitions.
- `dev/LESSONS.md`: P-w (`:3094-3256`), D-30 (`:3305-3360`), P-l
  (`:2305`), P-m (`:2460`), P-t (`:2601`), P-q (`:2633`), each read
  whole. TOOK P-w's exception clause (class (b) is interposition that
  narrows), D-30's caveat that a consumer audit cannot make required
  content cheaper, and P-t's built-tree unfolding as the inferred
  mechanism of the regression.
- `scripts/rules.py --for build` and `--for probe`, every statement.
- `archive/rud-route/`, SHAPE only: `README.md` (archived 2026-08-09,
  72 files, nothing checked or imported), `rud-route-src.patch`, `src/`.
  Took nothing from it.

## 9. LITERATURE USED

Nothing in the literature prices a spelling. I spent nothing.

## 10. GATES

`scripts/check-fences.py --check` clean (84 masters).
`scripts/lint-prose.py --check` exit 0 on the edited master.
`scripts/lint-agda.py --check` exit 0 on the edited master.
`scripts/ledger.py --check` clean; standing 26,706 lines over 82 masters;
`L.Condensation` counts 6,390 in-fence lines in the working tree against
5,562 at HEAD, the dispatch-start figures.
`L.BoundedSubset` re-checks green (exit 0, 3.39 s wall at load 2.74,
warm interfaces). The timer restored the dispatch-start interface after
every cold run, so the reverted source and its interface are both at the
dispatch-start state.
No `make check` was run, per the brief. No `check-ratio --check` was run,
per the brief. No commit, no push. The working tree carries the
dispatch-start placement in `src/L/Condensation.lagda.md` and this
report; no probe file was left behind. Untouched: `src/L/Coding/`,
`src/Everything.lagda.md`, all other masters, all probes. The final
`L.Condensation` source is byte-identical to the dispatch start (verified
by line count, diff stat and the restored `EnvSet` region).
