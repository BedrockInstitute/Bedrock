# LJ-1.276 report: land step 6 as `src/L/Coding/EnvSupply.lagda.md`

tier: pi (deepseek-subagent-mode), model `deepseek-v4-pro`. One Agda slot held.
A new master written. No commit, no push. Written incrementally (C-22). Every
negative is MEASURED or INFERRED, in those words.

## 0. LEAD

**833 in-fence non-blank lines. 482.73 s cold, exit 0.**

**`L.Condensation` re-runs cold at 137.60 s, exit 0.** The measured control
is 137.36 s. The chapter moved +0.17 percent. It gained zero lines and zero
seconds.

**The `Everything.lagda.md` line:** add `import L.Coding.EnvSupply` after
line 377 (`import L.Condensation.TwelveAgree`) and before line 378
(`import L.BoundedSubset`).

**The rate:** 482.73 s / 833 lines = **0.5795 s/line, 55.1x the 0.010514
bar.** The 482.73 s differs from the measured 465.59 s arm by +3.68 percent.
That is inside the 10 percent band, so the run stands.

## 1. WHAT THE MASTER IS

The master is `src/L/Coding/EnvSupply.lagda.md`, module
`L.Coding.EnvSupply {ℓ} (lem)`. It imports `L.Condensation` and carries step
6's whole block. The content is transplanted, not rewritten. MEASURED: `diff`
of the master against the green arm
`agents/tasks/LJ-1-275/SupplyFullNew.lagda.md`, from the line `pattern one`
to end of file, is EMPTY. The 805 content lines are byte-for-byte the arm.

The only changes are the ones the brief demands. The module name changed from
the probe name `LJ-1-275.SupplyFullNew` to `L.Coding.EnvSupply`. The import
header was trimmed: the arm's 74-line import header carried the whole
`L.Condensation` header; the master's header is 28 lines, which is the 833
line total minus the 805 content lines. MEASURED: `lint-agda.py` reported 121
unused names in the copied header; all 121 are removed, plus the dead
`module Cnt` and the dead `import Cubical.Data.Empty`. The master's
interface is 925,681 bytes, which proves the block was really elaborated.

## 2. WHAT IT EXPORTS, AND WHO CONSUMES IT

The master exports six top-level names.

- `module SupplyEnv (lam ordλ succλ ∅∈λ gam ordγ γ∈λ ω∈γ)`: the env supply at
  the concrete site. `envSetK`, the five `envK-*`, `envInK-gen`, the four
  `envInK-*`, and `someEnv`.
- `module Fact (K Ktr)`: the tower-neutral fields over `(K, Ktr)`: `prK`,
  `valK`, `valK-un`, the seven `subK-*`, `tmValK`, `valV`, `valW`, `wKfact`,
  `module ConsK`, `module EnvClosure`, `module ConsKClosed`.
- `levelK : (α : V ℓ) → IsOrd α → S`.
- `module AtLevel (α o)`: `Fact` instantiated at `levelK α o`.
- `Lset-fin`: the finite set lands in `Lset (sucV σ)`.
- `module SupplyMerge (lam ordλ succλ ∅∈λ)`: the finite-supremum merge and
  `finSetK`.

**The consumer is `[LJ-1.7]`'s `module Whole`.** MEASURED, from
`agents/tasks/LJ-1-267/lj-1.267-report.md`: step 6 is the supply of the
`lh` hypothesis, and `lh` is what the built parameters `sl` and `sc` stand
over. The site is `src/L/BoundedSubset.lagda.md:1555-1556` (`levelIn`,
`cover`). P-k holds: the read lemmas (`envSetAt-ident`, `envOverAt-in`, the
`envK-*`/`envInK-*` forms) are stated at the concrete carrier where the
condensation step consumes them, not in a generic shell.

## 3. THE `Everything.lagda.md` LINE

Add one line:

```
import L.Coding.EnvSupply
```

after line 377 (`import L.Condensation.TwelveAgree`) and before line 378
(`import L.BoundedSubset`). MEASURED: `src/Everything.lagda.md:374-379` is
the `L.Condensation` group followed by `L.BoundedSubset`. The new master
imports `L.Condensation`, so it must follow line 374. Its consumer is the
`module Whole` site in `L.BoundedSubset`, so it must precede line 378.

## 4. THE MEASUREMENT

| quantity | value |
|---|---|
| delivered master, in-fence non-blank lines | **833** |
| delivered master, cold elapsed | **482.73 s, exit 0** |
| load before to after (1-minute) | 3.98 to 4.87 |
| rate | 0.5795 s/line |
| rate over the 0.010514 bar | **55.1x** |
| deviation from the 465.59 s arm | **+3.68 percent** (no stop) |
| `L.Condensation`, cold elapsed | **137.60 s, exit 0** |
| `L.Condensation` load before to after | 6.93 to 4.54 |
| `L.Condensation` deviation from the 137.36 s control | **+0.17 percent** |

The content is the arm's 805 lines. The import header shrank from 74 to 28
lines, so the whole file is 833 lines, not the arm's 879. The 482.73 s is a
single cold run, one process, `GHCRTS="-A64m -I0 -M8g"`, cap never raised.
The 3.68 percent sits inside the run-to-run spread around the arm and inside
the 10 percent band the brief fixes, so no stop fired.

`L.Condensation` did NOT move. MEASURED: `git status --porcelain` is empty
for `src/L/Condensation.lagda.md`, `src/Everything.lagda.md` and
`src/L/Choice/Name.lagda.md`. Its cold re-run is 137.60 s against the
measured 137.36 s control, +0.17 percent.

## 5. WHICH PARAMETER THIS SUPPLIES AND WHICH IT BUILDS

The seven `module Whole` parameters are `el, fwd, bwd, sl, sc, s₁, amb`
(`lj-1.267-report.md` section 1). Step 6 is NOT one of the seven. It is the
supply of the `lh` hypothesis that two of them stand over.

- **SUPPLIES:** the `lh` hypothesis, by landing the step-6 block. `lh` is the
  level-hood hypothesis (`lj-1.267-report.md` section 1.3), and step 6 is its
  supply.
- **BUILDS:** `sl` (`StageLevels`) and `sc` (`StageCovered`). Both remain
  BUILT over `lh`; this landing discharges the hypothesis they stand over.
  It does not write their terms.
- **UNTOUCHED:** `el`, `fwd`, `bwd` (already SUPPLIED elsewhere), `s₁`
  (BUILT), `amb` (OPEN).

So this landing supplies none of the seven directly. It supplies the
condition that makes two of them reachable.

## 6. DD4, WITH ITS AXIS

**Axis 1, AC-against-GCH (DD4's own axis): NEUTRAL, paid once. MEASURED.**
The `SupplyEnv` telescope names `lam`, `ordλ`, `succλ`, `∅∈λ`, `gam`, `ordγ`,
`γ∈λ`, `ω∈γ`. Every one is an ordinal fact about elements of `V ℓ`. No
well-order, no cardinal, no trophy. The seconds are paid once on this axis.

**Axis 2, Def-against-J: the fields are generic, the env supply is Def-only.**
The `Fact` module's fields are stated over `(K, Ktr)`, a generic transitive
carrier, so the J tower re-instantiates them unchanged and pays once. The
`SupplyEnv` module is Def-side: it consumes `L.Coding.EnvSet`, `L.Coding.Key`,
`L.Coding.Sound`, `L.Definability` and `L.Condensation`'s `envSetB`. The J
tower never builds it. D-26 rules that the J tower's certificate is
structural and syntax-free, so it has no codes, no satisfaction and no
environment set. Nothing in step 6 is paid twice.

**Axis 3, L-against-ambient (this phase's mix): L-side.** `SupplyEnv` and
`SupplyMerge` are stage facts at `Lset lam` and `Lset gam`. Nothing is
ambient-side.

**What changes for the J tower:** nothing in `Fact`. Its `(K, Ktr)` fields
re-instantiate with the J carrier. `SupplyEnv` and `SupplyMerge` are not
re-instantiated at all: the J tower's level story is generation data
(D-26), so this master's Def-side content has no J counterpart to pay.

## 7. THE THREE ENV MODULES, DISTINGUISHED

- `L.Coding.Environment` (`src/L/Coding/Environment.lagda.md`): ONE
  environment, encoded as its graph. It builds `env`, `cons` and the Δ₀
  readers. It is not a set-of-environments.
- `L.Coding.EnvSet` (`src/L/Coding/EnvSet.lagda.md`): the SET of all
  environments over a carrier at a fixed length, as one element of `L`. It
  is the complement-clause substrate (`envSet`, `Generic`).
- `L.Coding.EnvSupply` (this master): the step-6 CLOSURE facts. It proves
  that an environment, and each component of it, STAYS inside the level
  `Lset lam` when the carrier does. A reader who confuses the three imports
  the wrong module: `Environment` gives one environment, `EnvSet` gives the
  set of them, `EnvSupply` gives the closure that keeps them in the level.

## 8. ARCHIVE USED (DD18)

- `agents/tasks/LJ-1-275/SupplyFullNew.lagda.md`, read WHOLE. **Line read
  `:10`**: the module header `module LJ-1-275.SupplyFullNew {ℓ} (lem)`.
  **TOOK:** the content, not the name.
- `agents/tasks/LJ-1-275/lj-1.275-report.md`, read WHOLE. **Line read
  `:4.2`**, the sentence "The heap wall is a layout artifact. MEASURED."
  **TOOK:** the proof that the same content is green in a new master.
- `agents/tasks/LJ-1-263/lj-1.263-report.md`, read WHOLE. **Line read
  `:3`**, "All three landed, and `src/L/Coding/Key.lagda.md` is GREEN."
  **TOOK:** the shape of a landing: land, then re-run against the master to
  prove it was a landing and not a copy.
- `agents/tasks/LJ-1-267/lj-1.267-report.md`, read WHOLE. **Line read
  `:7`**, the seven-parameter table. **TOOK:** which parameter step 6
  supplies.
- `archive/dev/TASKS-archived.md`, read for SHAPE only. **Line read `:1`**,
  "The whole `L3.32-T` series was ARCHIVED on 2026-08-09." **TOOK SHAPE,
  NEVER A CLAIM:** the retired route landed masters too; no seconds figure
  for a step-6 supply is taken from it.

## 9. LITERATURE USED (DD18)

`dev/literature/devlin-II5.md`, read the twelve-row table (section 4) and
the Step C rows (section 2.3).

**This master serves row C1** (level-hood formula, Σ₁-with-Σ₀-matrix,
uniform Δ₁, witness in carrier). Its env-supply content is exactly the
bounded satisfaction substrate (row C2, the `K(u)`-bound analogue) that makes
the C1 witness provable inside the carrier. Rows C3-C6, D, E, F and G are not
this master's content; the well-order (D, G) is not in this chain.

## 10. EVERY NEGATIVE, CLASSIFIED

| statement | class |
|---|---|
| the master typechecks as a master | **MEASURED TRUE.** exit 0, 482.73 s |
| the content is the arm's content | **MEASURED TRUE.** diff empty from `pattern one` to EOF |
| `L.Condensation` moved | **MEASURED FALSE.** 137.60 s vs 137.36 s, +0.17 percent |
| the master's figure differs from 465.59 s by over 10 percent | **MEASURED FALSE.** +3.68 percent |
| a wall (30 minutes, or heap) | **MEASURED FALSE.** longest run 482.73 s, no heap exhaustion |
| the heap cap was raised | **MEASURED FALSE.** `-A64m -I0 -M8g` on every invocation |
| more than one agda process | **MEASURED FALSE.** one at a time |
| I touched `Everything.lagda.md`, `L.Condensation`, `L.Choice.Name` | **MEASURED FALSE.** `git status` empty for all three |
| I wrote into `LJ-1-266/` or `LJ-1-275/` | **MEASURED FALSE.** read and copied only |
| I touched `agents/tasks/LJ-1-277/` | **MEASURED FALSE.** never opened |
| I ran `make check`, committed or pushed | **MEASURED FALSE** |

## 11. CHECKERS

| checker | result |
|---|---|
| `lint-agda.py --check` on the master | exit 0 |
| `lint-prose.py --check` on the master | exit 0 |
| `lint-prose.py --check` on this report | exit 0 |
| `ledger.py count(at_head=False)` on the master | 833 |
| `make check` | NOT RUN, the orchestrator runs it |
| agda | ONE process, `GHCRTS="-A64m -I0 -M8g"`, cap never raised |

`git status --porcelain` shows only `src/L/Coding/EnvSupply.lagda.md` and
`agents/tasks/LJ-1-276/` as my contributions. `agents/tasks/LJ-1-223/`
and `scripts/tests/test_premises_stated.py` were already present and I did
not touch them.
