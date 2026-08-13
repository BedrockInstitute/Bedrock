# LJ-1.122 report: land the generic environment-set by adding it

Status: COMPLETE. No commit, no push. ASD-STE100.

## 0. The verdict

Both masters are green. The acceptance probe is green. The numeral version was
left in place and derived as an extensional equality from the generic one.

The generic constructor is `Generic.envSetGen` at
`src/L/Coding/EnvSet.lagda.md:456`. The generic adequacy is
`AmbientHoldsGen.holds` at `src/L/Coding/Sound.lagda.md:287`. The derivation
of the numeral version is `NumeralFromGeneric.derived` at
`src/L/Coding/Sound.lagda.md:300`.

The acceptance probe `src/ProbeLJ1122B.agda` re-points `wired` at the master
versions. It closes in 1.77 s after the interfaces are built. Its first cold
run was 217.22 s because the changed `EnvSet` interface rebuilt the coding and
condensation import chain.

No consumer broke. The consumer list is complete. `make check` was not run.
The files `src/L/BoundedSubset.lagda.md`, `src/L/Condensation*`, and `src/V/`
were not touched. `src/Everything.lagda.md` was not touched.

## 1. The diff

The change adds content. It does not replace the numeral constructor.

`src/L/Coding/EnvSet.lagda.md` adds the `Generic` module at `:396`. The module
contains the arbitrary-arity construction, the separation specification, the
two membership directions, and the `Holds` adequacy. The numeral constructor
`envSet : (n : ℕ) → S` at `:183` keeps its name and type. The generic set is
sealed `opaque` at `:456`. This is the same discipline as the numeral set.

`src/L/Coding/Sound.lagda.md` adds two modules. `AmbientHoldsGen` at `:287`
is the generic counterpart of the numeral `AmbientHolds`. `NumeralFromGeneric`
at `:298` proves that the numeral set and the generic set at the numeral arity
are extensionally equal.

Non-blank in-fence lines:

| master | before | after | delta |
|---|---:|---:|---:|
| `src/L/Coding/EnvSet.lagda.md` | 229 | 359 | +130 |
| `src/L/Coding/Sound.lagda.md` | 801 | 850 | +49 |

The count is non-blank lines inside the one `agda` fence of each file. The
standing ledger reports 28,432 lines over 85 masters. It measures `HEAD`, not
the working tree.

## 2. C-40 consumers

I ran `git grep -l "Coding.EnvSet\|Coding.Sound" src/`. I verified the list
with `rg -n 'L\.Coding\.(EnvSet|Sound)|Coding\.EnvSet|Coding\.Sound' src/`.
The two searches agree. The list is complete.

`src/Everything.lagda.md:339` and `:343` import both modules. I did not run
`src/Everything.lagda.md`. The brief says never touch it and says the
orchestrator runs `make check`. Running that master alone is the whole tree,
so it is outside this dispatch.

Each other consumer is green. The result is exit 0.

| consumer | import | result |
|---|---|---|
| `src/L/Coding/Sat.lagda.md` | `:44` | exit 0, 1.95 s |
| `src/L/Coding/Bridge.lagda.md` | `:62` | exit 0, 1.12 s |
| `src/L/Coding/Powerset.lagda.md` | `:66` | exit 0, 1.33 s |
| `src/L/Coding/Uniform.lagda.md` | `:79` | exit 0, 1.28 s |
| `src/L/Coding/Unique.lagda.md` | `:61-62` | exit 0, 1.19 s |
| `src/L/Choice/Adequate.lagda.md` | `:44` | exit 0, 23.71 s |
| `src/L/Choice/Internal.lagda.md` | `:62` | exit 0, 1.68 s |

The `Choice/Adequate` run recompiled `Choice/Internal`. Both are green.

The changed masters themselves are green:

| master | result |
|---|---|
| `src/L/Coding/EnvSet.lagda.md` | exit 0 |
| `src/L/Coding/Sound.lagda.md` | exit 0 |

## 3. Numeral version

The numeral version was derived. The name and the type are byte-identical.

`NumeralFromGeneric.derived` states
`fst (envSet B n) ≡ fst (Generic.envSetGen B (nn n))` at
`src/L/Coding/Sound.lagda.md:300`. It uses the numeral `AmbientHolds` and the
generic `Holds` adequacy in one four-slot frame. It closes by `extensionalV`.

The existing opaque numeral definition was not changed. Its consumers do not
move. `src/ProbeLJ1122A.agda` consumes the master lemma and is green in 1.12 s.

## 4. C-39 section

The overrule to add did not block the route. It did cost real lines.

ADDING instead of replacing costs 130 lines in `EnvSet` and 49 lines in
`Sound`, for 179 in-fence lines total. The stable check-time delta is inside
the run-to-run spread. The first cold runs were longer because the new
`EnvSet` interface forced a rebuild of the import chain.

One prohibition was kept. The brief says not to run `make check`. That
prohibition blocked checking `src/Everything.lagda.md`. It did not block any
other route.

No other brief line blocked a route.

## 5. Negatives classified

One negative occurred during the work. It is MEASURED.

Before `envSetGen` was sealed, `src/ProbeLJ1122A.agda` importing
`NumeralFromGeneric` ran for 334.97 s with no output. I killed it under C-12.
The cause was the transparent `Generic.envSetGen` in the lemma's type. The
probe normalized the construction at every use. I made `envSetGen` and
`envSetGen-spec` `opaque`. The same probe then checked in 1.27 s. The wall is
MEASURED, and the cure is MEASURED.

No consumer broke. This negative is MEASURED FALSE by the exit-0 runs in
section 2.

## 6. DD4 answer

The construction is still tower-free. `Generic` imports the L axioms, the L
constructibility layers, the L stage, and the V hierarchy. It does not import a
condensation tower or a rud tower. The type of `envSetGen` is `S`. No tower
object enters the generic type. The J tower inherits this content unchanged.

## 7. Measurements

One Agda process at a time. The heap cap was `-A64m -I0 -M8g`. The cap was
never raised. Load is reported at each start.

The two touched masters:

| master | before | after, stable runs | load at start |
|---|---:|---:|---|
| `EnvSet.lagda.md` | 1.88 s | 1.13 s, 1.92 s, 1.06 s | 4.48, 5.38, 5.27 |
| `Sound.lagda.md` | 1.13 s | 2.05 s, 1.15 s, 1.26 s | 4.84, 5.49, 5.29 |

The `EnvSet` after spread is 0.86 s. The `Sound` after spread is 0.90 s. The
stable deltas are inside that spread.

The first post-edit cold runs were:

| master | first post-edit | load at start |
|---|---:|---:|
| `EnvSet.lagda.md` | 2.70 s | 4.24 |
| `Sound.lagda.md` | 6.59 s | 2.92 |

The `Sound` first post-edit run included a recheck of `Sat` and `Table`.

Acceptance and derivation probes:

| probe | result | seconds | load at start |
|---|---|---:|---:|
| `ProbeLJ1122B.agda`, first cold | exit 0 | 217.22 | 5.47 |
| `ProbeLJ1122B.agda`, stable | exit 0 | 1.77 | 4.77 |
| `ProbeLJ1122A.agda`, before seal | killed | 334.97 | 4.35 |
| `ProbeLJ1122A.agda`, after seal | exit 0 | 1.27 | 5.49 |
| `ProbeLJ1122A.agda`, stable | exit 0 | 1.12 | 4.95 |

The `ProbeLJ1122B` first cold run rebuilt `Slot`, `Unique`, `Bridge`,
`Uniform`, `Powerset`, `Sequence`, `Hierarchy`, `Condensation`,
`Condensation.LowerAgree`, and `ProbeLJ1115A`. The stable run does not.

Checks:

| check | result |
|---|---|
| `check-unbound-hyp.py --check` on both masters and both probes | clean, 4 files |
| `lint-agda.py --check` on both masters and both probes | exit 0 |
| `lint-prose.py --check` on this report | exit 0 |
| `check-fences.py --check` | clean, 87 masters |
| `ledger.py --brief` | standing 28,432 lines over 85 masters |

No `make check` was run.

The working tree also has an unrelated change to `dev/PLAN.md`. It is not mine.
The dispatch started at `HEAD a38687c`, not `cc0ea60`. `a38687c` is the
registration commit for this dispatch.

## ARCHIVE USED

- `_build/lj-1.120-report.md`, read WHOLE. TOOK the construction and the
  wiring.
- `src/ProbeLJ1120A.agda`, read WHOLE. TOOK `Generic` at `:64`,
  `envSetGen` at `:123`, and `Holds.holds` at `:207`.
- `src/ProbeLJ1120B.agda`, read WHOLE. TOOK `envSetK` at `:34` and `wired`
  at `:71`.
- `_build/lj-1.115-report.md`, read WHOLE. TOOK the four properties and the
  acceptance wire.
- `_build/lj-1.113-report.md`, read WHOLE. TOOK the twenty-nine count and the
  canonical-home naming.
- `src/L/Coding/EnvSet.lagda.md`, read WHOLE. TOOK `Ix` at `:122`, `nn` at
  `:171`, and the numeral `envSet` at `:183`.
- `src/L/Coding/Sound.lagda.md`, read WHOLE. TOOK `AmbientHolds` at
  `:262-284`.
- `dev/LESSONS.md`, read the cited entries whole. The line ranges are C-40
  `:3602-3637`, P-x `:3564-3601`, C-38 `:3427-3520`, C-39 `:3521-3563`,
  C-35 `:3200-3241`, C-36 `:3284-3331`, D-30 `:3332-3380`, P-l
  `:2305-2400`, P-w `:3094-3170`.
- `scripts/rules.py --for build` and `--for rewrite`, read all statements.

## LITERATURE

Banked. Nothing spent.
