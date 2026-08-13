# LJ-1.102: does the Mem row prove itself in tied form?

Status: COMPLETE, written incrementally per C-22. No commit, no push.
ASD-STE100. This report is `_build/lj-1.102-report.md`.

## 0. THE VERDICT

**NO. The row does not prove itself in tied form. MEASURED.**

The out direction fails at the EnvSet transfer. The term I could not
write is at `src/ProbeLJ1102A.agda:196.55-56`. It is the second
component of `EnvSetTied.out`. The check is exit 42, 4.03 s total,
2.98 s user, load average 3.81 at start and 3.75 at finish, one
process at the C-12 cap.

The failing premise is `z ∈ E`. The row's own binders give `E ∈ K`
(the `EK` binder at `Condensation.lagda.md:4195`, derived at `:4219`)
and `z ∈ E` for the first component only. The second component has
only `z ∈ K` (`envInK z hz`). The tied entryK demands `z ∈ E`. The
row has no transitivity `z ∈ E → z ∈ K`. So the alternative ChainZ
tie also fails, at the first component. Both failures are measured in
the probe.

## 1. WHAT WAS RESTATED

The row is `MemAgree`, `src/L/Condensation.lagda.md:4141-4240`. It
takes three of the eleven refuted frame facts:

| hypothesis | source line | refuted at |
|---|---|---|
| `tmKeyK` | `:4159` | `src/ProbeLJ195A.agda:45-48` |
| `entryK` | `:4165-4166` | `src/ProbeLJ197A.agda:239-240` |
| `arSubK` | `:4167-4169` | `src/ProbeLJ197A.agda:251-254` |

The probe restates them in tied form. The tied forms come from
`src/ProbeLJ199A.agda` and `src/ProbeLJ1100A.agda`:

| refuted hypothesis | tied form |
|---|---|
| `tmKeyK` | `keyValK`: `(k : S) → ⟨ (k ∷ γ) ⊨ tagAtL (suc (suc (suc (suc (suc (suc (suc zero))))))) 1 zero ⟩ → k ∈ K`. The tag satisfaction pins `k`; the row's back reaches the use at `TmVal.in'` `Condensation.lagda.md:2948` with the tag satisfaction `ht` bound |
| `entryK` | `entryK-tied`: `(E : S) → E ∈ K → (z x y : S) → z ∈ E → pr x y ∈ z → x ∈ K × y ∈ K`. This is the four-step chain of `[LJ-1.99]` and the Extended shape of `[LJ-1.100]` |
| `arSubK` | `arSubK-tied`: `x ∈ ar → ar ∈ K → x ∈ K`. This is `arityK` exactly once, `src/ProbeLJ199A.agda` module `Chain` |

The row's own binders supply the ties. The out direction binds `EK`
at `:4195` and `arK` at `:4195`. The back direction derives `EK`
from `envK` at `:4219` and `arK` from `codesK` at `:4215`. The use
lines the brief named are verified in the source: `EK` at `:4195`,
`entryK` at `:4201`, `valK` at `:4216`, back `EK` at `:4219`.
`valK` is not refuted. It stays untied. It is one of the 28
additions of `[LJ-1.100]`.

The probe copies the EnvSet transfer
(`Condensation.lagda.md:2771-2874`) as `EnvSetTied`
(`src/ProbeLJ1102A.agda:91-196`) with the tied facts. The row
instantiates it with `entryK-tied E EK` and
`(λ x hx → arSubK-tied yc b a ar c x hx arK)`. The instantiation
typechecks. The failure is inside the transfer.

## 2. THE FAILING STEP

The row's out direction applies `E'.out henv`. `EnvSetTied.out` has
two components:

```agda
out h = extAt-in-both E φ γ
  (λ z z∈ → bnd→over-tied z z∈ (h .fst z z∈))
  (λ z hz → h .snd z (envInK z hz) (over→bnd-tied z ? hz))
```

The first component binds `z ∈ E` and closes. The second component
has only `z ∈ K`. The hole is `z ∈ E`. It stays unsolved.

The use that needed the untied form: `entryK` inside
`EnvSet.over→bnd`, `Condensation.lagda.md:2850-2854`. The master's
`over→bnd` ran with the untied entryK at any `z`. The tied form
demands `z ∈ E`. The second component does not have it.

The alternative ChainZ tie has premise `z ∈ K`. It closes the second
component. It fails the first component. The hole is `z ∈ K` at
`src/ProbeLJ1102A.agda:279.31-32`. The row's telescope
(`Condensation.lagda.md:4142-4185`) has no `arityK` and no `transK`.
So it cannot derive `z ∈ K` from `z ∈ E` and `E ∈ K`. MEASURED by
listing.

## 3. THE DIFF SIZE

All counts are non-blank lines. The original row block is
`Condensation.lagda.md:4141-4240`.

| part | lines |
|---|---:|
| original `MemAgree` (telescope, `out`, `back`) | 96 |
| original telescope | 44 |
| restated telescope (`src/ProbeLJ1102A.agda:315-367`) | 53 |
| restated row module (telescope plus the out's first step) | 81 |
| `EnvSetTied` copy (`:91-196`) | 98 |
| `EnvSetTiedChainZ` copy (`:208-303`) | 89 |

The telescope change is 44 to 53 lines. Three hypotheses are
restated. The ties supplied: `E ∈ K` from the row's `EK` binder,
`ar ∈ K` from the row's `arK` binder, `z ∈ E` from the bounded
condition's first component, `z ∈ K` from `envInK`. The out direction
does not elaborate past `E'.out henv`. The row's tail
(`:4204-4208`) is unchanged and unreached. The back direction was
not attempted, per the abort criterion.

## 4. NEGATIVES AND THEIR STATUS

1. The row proves itself in tied form: **MEASURED FALSE**. Exit 42,
   one unsolved meta at `src/ProbeLJ1102A.agda:196.55-56`.
2. The tied `entryK` (Chain form) closes the out direction:
   **MEASURED FALSE**. The second component's `z ∈ E` is unsolved.
3. The ChainZ alternative closes the out direction: **MEASURED
   FALSE**. The first component's `z ∈ K` is unsolved at
   `:279.31-32`.
4. The row's telescope supplies transitivity `z ∈ E → z ∈ K`:
   **MEASURED FALSE by listing**. `Condensation.lagda.md:4142-4185`
   has no `arityK` and no `transK`.
5. The back direction survives with the Chain tied form: **INFERRED
   FALSE**. Its second component runs `bnd→over` with only `z ∈ K`,
   the same mechanism as the out failure. The ChainZ form closes the
   back direction but fails the out direction. It was not attempted,
   per the abort criterion.
6. The J tower gets the restated row unchanged: **INFERRED**. No J
   site exists in this tree. The tied forms are slot-generic. The
   failure is the missing transitivity in the row's frame.

## 5. THE DD4 ANSWER

The restated row is still generic in its slots. All set arguments are
`S` variables. The slots are `Fin` positions. The tied forms are more
generic than what they replace. They condition the closure on the
actual membership. They say what they mean.

The row's proof does not survive with one tied `entryK`. The EnvSet
transfer uses `entryK` at two component sites. The sites have
different available premises. One has `z ∈ E`. The other has
`z ∈ K`. No single tied form serves both, without transitivity. The
row's frame has no transitivity. The untied form's over-generality
was load-bearing at both sites. This is the finding that makes
retirement the honest answer.

## 6. ARCHIVE USED

- `src/ProbeLJ199A.agda`, read WHOLE, and
  `_build/lj-1.99-report.md`, read WHOLE. TOOK the tied forms
  (`Chain.entryK-tied`, `ChainZ.entryK-tied-zK`,
  `Chain.arSubK-tied`) and the per-row supply table. The `EK` binder
  rows verified at `Condensation.lagda.md:4195` and `:4219`.
- `_build/lj-1.100-report.md`, read WHOLE, and
  `src/ProbeLJ1100A.agda`, read. TOOK the Extended frame's
  `entryK-tied` shape (`(E : S) → E ∈ K → (z x y : S) → z ∈ E →
  ...`) and the `keyValK` shape for `tmKeyK`.
- `_build/lj-1.97-report.md`, read WHOLE, and
  `src/ProbeLJ197A.agda`, read. TOOK the ten refutations and the
  `entryK` / `arSubK` refutation lines.
- `_build/lj-1.96-report.md`, read WHOLE. TOOK the per-use table and
  the `keyValK` no-home analysis.
- `_build/lj-1.98-report.md`, read WHOLE. TOOK the tied-form table
  and the `tmKeyK` tied shape.
- `src/L/Condensation.lagda.md:4141-4240`, read. TOOK the `MemAgree`
  telescope, `out` and `back`, and the binder types.
- `src/L/Condensation.lagda.md:2764-2870`, read. TOOK `EnvSet`'s
  telescope and both transfer directions, including the `entryK`
  uses at `:2815-2834` and `:2850-2854`.
- `src/L/Condensation/TwelveAgree.lagda.md:45-243`, read WHOLE.
  TOOK the eleven refuted fact types and the `transK` field.
- `dev/LESSONS.md`, C-38 as extended (`:3427-3511`), C-35
  (`:3200-3242`), C-36 (`:3284-3332`), D-29 (`:3242-3284`), D-30
  (`:3332-3380`), P-i (`:203-262`), P-w (`:3094-3164`), read WHOLE.
  TOOK the conditional-closure standard, the failed-substitution
  discipline, and the copy-priced-at-use rule.
- `scripts/rules.py --for build`, read all statements.
- `archive/rud-route/`, SHAPE only. Took nothing.

## 7. LITERATURE USED

Banked; nothing spent.

## 8. GATES

- `src/ProbeLJ1102A.agda`: RED as designed, exit 42, one process at
  the C-12 cap. The final timed run: 4.03 s total, 2.98 s user,
  0.25 s sys, load average 3.81 at start and 3.75 at finish. The
  range across runs: 3.08 to 4.03 s total, load average 2.62 to
  4.07. Two unsolved interaction metas: `:196.55-56` (`z ∈ E` in
  `EnvSetTied.out`) and `:279.31-32` (`z ∈ K` in
  `EnvSetTiedChainZ.out`). The check runs after warm dependencies
  from `_build`.
- `scripts/lint-agda.py --check src/ProbeLJ1102A.agda`: exit 0.
- `scripts/lint-prose.py --check _build/lj-1.102-report.md`: exit 0.
- No master was touched by this dispatch. `src/L/Condensation/`,
  `src/L/Coding/`, `src/V/`, `src/Everything.lagda.md` untouched.
  No `make check`. No commit, no push.
- Working tree note: HEAD moved from `563c0d5` to `b07d411` while
  this dispatch ran. The sibling agent committed `[LJ-1.101]`, which
  touched `dev/PLAN.md`. `src/L/BoundedSubset.lagda.md` carries the
  sibling agent's uncommitted changes (timestamp 03:40:48). This
  dispatch did not touch it.
