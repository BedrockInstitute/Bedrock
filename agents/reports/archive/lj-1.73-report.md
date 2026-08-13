# LJ-1.73: does the repaired TwelveAgree instantiate at an ABSTRACT frame?

Status: COMPLETE, written incrementally per C-22. No commit, no push.
ASD-STE100. This report is `_build/lj-1.73-report.md`.

## 0. THE VERDICT

**THE ABSTRACT APPLICATION WALLS. STOP, per the pre-fixed abort criterion
(D-1).** Applying the repaired `TwelveAgree` at an abstract
`γ' : S ^ (11 + n)`, with all sixty-nine facts stated at `γ'` and the
where-block forced through `out`/`back`, heap-exhausts the C-12 cap in
about 265 s (`src/ProbeLJ173A.agda`, measured this dispatch). The
concrete-env contrast, the same application at the graph frame's cons-env
with the body forced, heap-exhausts in about 210 s (measured in
`[LJ-1.72]`, `_build/lj-1.72-report.md` section 4, row CUT2c). Both walls
are heap exhaustion at `-M8g`, not type errors and not load effects.

**So the answer to the question is NO: the repaired `TwelveAgree` does NOT
instantiate affordably at an abstract frame either. MEASURED.** The
where-block is unaffordable at ANY frame, abstract or concrete. The
twelve-row composition has to be built differently. This is the more
valuable answer and it goes to the owner.

Per the abort criterion, the dispatch ends at this one comparison. No
restructure of `SatGraphAgree` was attempted. No master was edited.

## 1. THE PROBE

`src/ProbeLJ173A.agda` is the `[LJ-1.72]` probe file family
(`/private/tmp/ProbeLJ172CUT2post.agda.scratch`) rebuilt verbatim, with one
change: `module AbstractFrame` replaces the concrete application.

`AbstractFrame` takes the fifteen slots
(`N0`..`N11`, `t0`, `t1`, `K : Fin (5 + n)`), an abstract environment
`γ' : S ^ (11 + n)`, and the sixty-nine repaired telescope facts stated at
`γ'` (the twelve `tagEq0`..`tagEq11`, the twelve `numK0`..`numK11`,
`innerK`, `pairK`, `codesK`, `codesK-un`, and the forty union facts
`valK` through `consK-allin`, all with `γ` replaced by `γ'`). Inside, it
applies the repaired `TwelveAgree` at `γ'` with those sixty-nine facts as
the arguments, then exposes

```text
out  : ⟨ γ' ⊨ twelveAt (suc (suc zero)) (suc zero) zero ⟩ → ⟨ γ' ⊨ T.twelveB ⟩
back : ⟨ γ' ⊨ T.twelveB ⟩ → ⟨ γ' ⊨ twelveAt (suc (suc zero)) (suc zero) zero ⟩
```

as `T.out` / `T.back`. The aliases force the where-block, exactly as the
concrete application's aliases force it in the `[LJ-1.72]` walled runs. The
`someEnv` fact uses the real named definition (`someEnvDef`), not a
postulate: the scaffold's `postulate` form failed the where-block's type
check, and the real definition (present in the `[LJ-1.72]` scratch family)
repaired that.

The repaired `TwelveAgree` is verbatim `[LJ-1.72]` section 1a: per-row
`tagEq`/`numK` fields, and the where-block with the twelve row
applications at the module's own `γ` parameter. At the abstract application,
that parameter is `γ'`, so the twelve row applications are elaborated at an
environment on which `lookup` does not reduce.

## 2. MEASUREMENTS

One cold run, C-12 caliber (`GHCRTS="-A64m -I0 -M8g"`, one process, warm
dependencies), load 3.5 to 11.4 (4 users; the load rose during the run):

| configuration | result | seconds |
|---|---:|---:|
| abstract application, full body forced (this dispatch) | **WALL** | 265.18 |
| concrete application, full body forced ([LJ-1.72] CUT2c) | **WALL** | about 210 |
| same telescope, empty body, concrete env ([LJ-1.72] CUT2tel) | green | about 105 |

The abstract run: `real 265.18`, `user 262.38`, `sys 2.00`, exit 251
(`Heap exhausted`, current maximum heap size 8 GB). The load average read
3.46 / 5.28 / 8.89 at 15:47 before the run, and 10.59 / 6.51 / 7.57 at
15:56 at its end. The verdict does not depend on load: the exit is heap
exhaustion, an allocation event, and the cap is fixed by C-12. The probe
is a fresh file, so no stale `.agdai` can explain the wall (P-p).

The concrete contrast is the `[LJ-1.72]` measured wall (same telescope,
same sixty-nine arguments, same body forcing, at `(f ∷ e ∷ d ∷ γ)`), about
210 s at load 4 to 10. Both walls are at `-M8g`. The one structural
difference between the two probes is the application's environment:
concrete cons-chain in `[LJ-1.72]`, abstract variable here.

The empty-body row (CUT2tel, green about 105 s) is the argument check only.
The delta to the full-body runs is the where-block. Both full-body runs
wall; the where-block is the measured cause at both sites.

## 3. NEGATIVES AND THEIR STATUS

1. The repaired `TwelveAgree` instantiates affordably at an abstract env:
   **MEASURED FALSE**. `src/ProbeLJ173A.agda` heap-exhausts at `-M8g` in
   265.18 s. This negative sets the verdict.
2. The abstract env removes the where-block cost: **MEASURED FALSE**. The
   abstract application walls at the same cap. The wall is allocation, not
   a type error: the same file checks the frame and telescope past the
   sixty-nine argument checks and dies in the forced body.
3. The wall is the concrete env's reduction: **MEASURED FALSE**. The
   abstract env's `lookup` does not reduce, and the application still
   walls. The expensive object is the built formula content inside the
   twelve row applications (P-t), which unfolds regardless of the carrier.
   That attribution is INFERRED from this pair of measurements; no profile
   ran.
4. The wall is load: **MEASURED FALSE**. A heap-exhausted exit at a fixed
   cap is allocation, not time. The load rose during the run but cannot
   cause a heap wall.
5. The scaffold's `someEnvDef` postulate is the repair's shape: **MEASURED
   FALSE**. The rows demand the full `someEnv` statement; a postulate
   fails the type check at the application. The real definition (the
   `[LJ-1.72]` `someEnvDef`) is transparent and matches.

The deciding claim of the verdict is item 1, MEASURED.

## 4. THE DD4 ANSWER

An abstract-frame discharge is the more generic shape, and it does NOT
change what the J tower pays: the discharge walls at the abstract env,
MEASURED. The where-block's twelve row applications at an abstract
environment still heap-exhaust the cap in 265 s, so a J tower that
discharges at its own abstract frame pays the same measured class of cost.
That the J tower inherits the wall is INFERRED (no J-tower measurement
exists), but the mechanism is measured at the L tower: the cost follows the
formula content inside the rows, not the concreteness of the environment.

The green-and-affordable branch did not occur, so the consumer question
(what `SatGraphAgree` would have to do, and whether it can restructure to
take the discharge at an abstract frame) does not arise. The report
answers the abort branch instead: the twelve-row composition must be built
differently, and that answer goes to the owner.

## 5. THE CONVERGENCE ANSWER

NOT CLOSING. `TwelveAgree` remains unconsumed at any frame. The `[LJ-1.72]`
repair is sound as a statement (per-row telescope and union frame both
green in isolation) but unaffordable at the concrete cons-env (about 210 s
wall) and now measured unaffordable at an abstract env too (265.18 s wall).
The abstract environment is not the lever. The remaining candidates from
`[LJ-1.72]` section 6 stand unpriced: restructure the where-block so a
consumer does not re-elaborate the twelve row applications, or re-open the
cap question with the owner. This dispatch prices none of them.

## 6. ARCHIVE USED

- `_build/lj-1.72-report.md`, read WHOLE. TOOK sections 1a and 1b (the
  repair to rebuild), section 4 (the wall table; the concrete contrast
  figure 210 s) and the abort criterion.
- `/private/tmp/ProbeLJ172CUT2post.agda.scratch`, read WHOLE. TOOK the
  repaired telescope text and the concrete frame application verbatim.
  The abstract probe is this file with the application moved to an
  abstract env.
- `/private/tmp/cut2opq_naive.agda`, read. TOOK the real `someEnvDef`
  definition (the postulate scaffold does not typecheck the rows).
- `/private/tmp/ProbeLJ172CUT2.agda.scratch`, read. TOOK the concrete
  full-body application shape (out/back aliases forcing the where-block).
- `_build/lj-1.71-report.md` and `src/ProbeLJ171A.agda`, read WHOLE. TOOK
  the refutation the repair answers and the frame shape.
- `_build/lj-1.25-report.md`, `_build/lj-1.24-report.md`, read WHOLE. TOOK
  the abstract-the-source cure (12.8x) and its stop discipline. This site
  does not reproduce it, MEASURED.
- `_build/lj-1.67-report.md`, read WHOLE. TOOK the abstract-stack
  regression (+2.82 s) and the same-site re-measure discipline (P-l).
- `dev/LESSONS.md`, read WHOLE for P-h (`:174`), C-38 (`:3427`), C-35
  (`:3200`), P-w (`:3094`), P-o (`:2509`), P-t (`:2601`), P-l (`:2305`),
  P-m (`:2460`), P-n (`:2483`), P-i (`:210`), P-k (`:2398`), P-q
  (`:2633`), P-u (`:2908`), P-v (`:3037`), P-c (`:71`), R-35 (`:782`),
  R-36 (`:808`), R-38 (`:829`), R-40 (`:929`), I-5 (`:1196`), C-12
  (`:2075`), C-22 (`:2237`), C-31 (`:1855`), C-32 (`:2947`), C-33
  (`:2987`), C-34 (`:3171`), C-36 (`:3284`), C-37 (`:3381`), D-1
  (`:1038`), D-8 (`:1377`), D-10 (`:1316`), D-26 (`:1676`), D-29
  (`:3242`), D-30 (`:3332`).
- `archive/rud-route/`, SHAPE only. Took nothing.

## 7. LITERATURE USED

Nothing in the literature prices a spelling. One line, nothing spent.

## 8. GATES

`scripts/check-fences.py --check` clean (84 masters).
`scripts/lint-prose.py --check` exit 0.
`scripts/lint-agda.py --check` exit 0.
`scripts/ledger.py --brief`: standing 27,673 lines over 82 masters,
measured from HEAD.
No `make check` was run, per the brief. No commit, no push. The working
tree is byte-identical to the dispatch start: `git status --porcelain`
empty, `git diff HEAD --stat` empty. The probe (`src/ProbeLJ173A.agda`)
and this report are gitignored by design. `src/L/Condensation.lagda.md`,
`src/L/Coding/` and `src/Everything.lagda.md` are untouched.
