# LJ-1.252 report: can `ω ∈ lam` be supplied, and does step 6 become fundable?

**STATUS: branch 2 of the four, MUST BE ADDED — and the addition is cheap.**
**`ω ∈ lam`'s status in one word: UNDERIVABLE** (from the telescope as it
stands; DERIVABLE at the one consumer from `α∉ω`). Written incrementally from
a skeleton (C-22). Every negative is **MEASURED** or **INFERRED** (C-36).

## 0. LEAD

**Which way it went: branch 2, MUST BE ADDED.** `ω ∈ lam` is NOT derivable
from `∅∈λ + succλ + ordλ` (branch 1 is false, MEASURED by countermodel). It
is NOT false at the actual site (branch 3 is false, MEASURED: `α∉ω` forces
it). No second bound exists (branch 4 is false, MEASURED by grep). So the
hypothesis must be added to the supply module's telescope, and the whole price
of that addition is **five lines at one consumer**.

**Step 6 becomes fundable.** The join that stopped `[LJ-1.199]` at ZERO lines
is real, but it is a one-hypothesis addition plus a five-line derivation, not
a new bound for the layer. `[LJ-1.199]` read it and never ran Agda; this
probe ran Agda and the derivation typechecks in 0.75 seconds.

## 1. WHAT I BUILT

`agents/tasks/LJ-1-252/ProbeLJ1252A.agda`, 99 lines total, 29 in-fence
content lines, three claims. ONE agda process,
`GHCRTS="-A64m -I0 -M8g"`, cap never raised. Check time **0.75 seconds**
(4 runs: 0.78 / 0.76 / 0.74 / 0.79; warm, interface cached; load trivial).
No wall. No heap figure needed.

The three claims, each MEASURED by typecheck:

| claim | content | verdict |
|---|---|---|
| `Countermodel` | `lam = ω` satisfies `ordλ, succλ, ∅∈λ` while `ω ∈ lam` is empty | branch 1 refuted |
| `ω∈λ-from-α` | `α∉ω + α∈λ + ordα + ordλ` gives `ω ∈ lam` | branch 3 refuted at the site |
| `ω∈sucα` | `α∉ω + ordα` gives `ω ∈ sucV α` | the `σ` the bound needs |

## 2. THE FOUR WAYS, ANSWERED

### 2.1 Branch 1, DERIVABLE — **MEASURED FALSE**

`∅∈λ + succλ + ordλ` do not derive `ω ∈ lam`. The countermodel is `lam = ω`.
`ω-ord : IsOrd ω` (delivered, `src/L/Ordinal.lagda.md:263`). `ω` is
successor-closed: `ω-next` (cubical `Constructions.agda:195-196`), read at the
structure membership, gives `succω : (d) → d ∈ˢ ω → sucV d ∈ˢ ω`. `∅ ∈ˢ ω`
is `#∈ω 0` (`src/L/Ordinal.lagda.md:248`). At `lam = ω`, `ω ∈ lam` is
`ω ∈ˢ ω`, and `∈-irrefl ω` (`src/V/Hierarchy.lagda.md:155`) refutes it. **All
three hypotheses hold at `lam = ω` and the conclusion fails, so the three do
not imply it.**

### 2.2 Branch 3, FALSE AT THE SITE — **MEASURED FALSE at the real site**

At the one consumer, `ω ∈ lam` is TRUE. `ω∈λ-from-α` derives it from
`α∉ω`, `α∈λ`, `ordα`, `ordλ` in five lines: trichotomy gives
`α ∈ˢ ω ∨ α ≡ ω ∨ ω ∈ˢ α`; `α∉ω` kills the first; `α≡ω` substitutes into
`α∈λ`; `ω ∈ˢ α` closes by `lam`'s transitivity. **The value is false only at
degenerate instantiations (`lam = ω`) that the real consumer already excludes
by carrying `α∉ω`.** `[LJ-1.199]`'s fear — "if `lam` can be a limit below
`ω`" — is exactly the case `α∉ω` rules out.

### 2.3 Branch 2, MUST BE ADDED — **TRUE, and the price is five lines**

Add the hypothesis to the supply module's telescope. The cheaper form is
`ω∈γ : ⟨ ω ∈ˢ sucV gam ⟩`, not `ω∈λ`: it matches `envSetNumeral∈`'s `ω ∈ σ`
directly at `σ = sucV gam`, and it avoids the two-ordinal merge below the
limit. At the consumer `gam = α`, and `ω∈sucα` (three lines) supplies it from
`α∉ω` alone. **Equivalently, the supply can take `gam∉ω : ⟨ gam ∈ˢ ω ⟩ → ⊥`
raw — that is literally the hypothesis `BoundedSubsetAt` already holds at
`:1387` — and derive `ω ∈ sucV gam` internally.** **MEASURED: the
consumer-side price is the two derivations, 8 lines total, and both
typecheck.**

### 2.4 Branch 4, A SECOND BOUND — **MEASURED FALSE**

`envSetNumeral∈` is the only delivered bound. `grep -rn "envSetNumeral∈"
src/` returns its own declaration only; it has ZERO consumers. No other lemma
concludes `fst (envSet B n) ∈ Lset …` or `fst (Generic.envSetGen …) ∈ …`
(grep over `src/L/Coding/`). **The `ω ∈ σ` requirement is intrinsic, not an
artifact of the one lemma:** the numerals live at `Lset ω`
(`numeral∈limit`, `src/L/Choice/Name.lagda.md:120-121`), the carrier members
live at `Lset σ`, and any single bound for the environment must dominate both,
so it must dominate `ω`. That is the `ω ∈ σ` hypothesis under any bound shape.
**INFERRED as a shape argument** (I did not build an alternate bound);
**MEASURED as a grep** (no second bound delivered).

## 3. EVERY CONSUMER OF `HullStage` (C-40)

**One consumer exists.** `grep -rn "HullStage" src/` returns exactly:

- `src/L/BoundedSubset.lagda.md:1405` —
  `module HS = HullStage lam ordλ succλ UK.X UK.X⊆Lλ UK.∅∈λ`, inside
  `BoundedSubsetAt` (`:1385`).

`BoundedSubsetAt` already holds the ingredients to supply `ω∈λ`:
`α : S`, `ordα : IsOrd α`, `α∈λ : ⟨ α ∈ˢ lam ⟩`
(`:1392`), and `α∉ω : ⟨ α ∈ˢ ω ⟩ → Empty.⊥` (`:1387`). So the consumer pays
`ω∈λ-from-α` (five lines) or, if the supply takes `ω∈γ`, `ω∈sucα` (three
lines). **Nothing else consumes `HullStage`, so no other site pays.**

The supply module itself (`KValue`, the step-5 analogue,
`src/L/Condensation.lagda.md:7222`) is standalone, NOT under `HullStage`
(`L.BoundedSubset` imports `L.Condensation`, never the reverse). So the
change lands in the step-6 supply module's telescope, not in `HullStage`.
`HullStage` needs NO edit; the brief's branch-2 phrasing over-prices the
blast radius.

## 4. DD4 — TOWER ANSWER

**Tower-neutral, paid once.** `ω ∈ sucV gam` is a statement about the carrier
ordinal `gam`; it names no tower and no `Lset` presentation. The two towers
(`L ⊨ AC`, `L ⊨ GCH`) share the supply module, so the hypothesis is paid once
and the two towers each re-instantiate only their own per-tower fields, which
`[LJ-1.113]:219-239` already counted at 3 of 28.

## 5. EVERY NEGATIVE, CLASSIFIED

| statement | class |
|---|---|
| `ω ∈ lam` derivable from `∅∈λ + succλ + ordλ` | **MEASURED FALSE.** `Countermodel` typechecks |
| `ω ∈ lam` false at the actual site | **MEASURED FALSE.** `ω∈λ-from-α` typechecks |
| `ω ∈ lam` must be added | **MEASURED TRUE** (it is the remaining case) |
| a second bound exists | **MEASURED FALSE** (grep); the no-free-bound shape is **INFERRED** |
| `envSetNumeral∈` has a consumer | **MEASURED FALSE.** grep returns its own declaration only |
| `HullStage` has more than one consumer | **MEASURED FALSE.** one site, `:1405` |
| the supply sits under `HullStage` | **MEASURED FALSE.** `KValue` is standalone; import is `L.BoundedSubset → L.Condensation` |
| `[LJ-1.199]` ran Agda | **MEASURED FALSE.** its section 3 says zero invocations |
| step 6 was built | **MEASURED FALSE.** this probe gates it; ZERO master lines |
| a wall occurred | **MEASURED FALSE.** 0.75 s, no heap figure |
| I edited a master | **MEASURED FALSE.** only `agents/tasks/LJ-1-252/` written |

## 6. ARCHIVE USED (DD18)

- **`agents/tasks/LJ-1-199/lj-1.199-report.md`, READ WHOLE.** TOOK the join
  (`envSetNumeral∈` needs `ω ∈ σ`, the telescope lacks it). **Its
  `envSetK` impossibility was a READING (section 8: "I built no Agda
  counterexample"); this probe upgrades the join from read to measured.**
- **`agents/tasks/LJ-1-251/lj-1.251-report.md`, READ the verdict and the one
  sentence.** TOOK `[LJ-1.7]` = step 6 = the 28 fields at 255. No correction.
- **`agents/tasks/LJ-1-113/lj-1.113-report.md:219-239`.** TOOK the 25-3
  split. The `ω ∈ lam` hypothesis is on the shared side.
- **`agents/tasks/LJ-1-173/lj-1.173-report.md:857`.** TOOK "step 6 IS the 28
  fields" and the stop-before-build grade.
- **`src/L/Coding/Key.lagda.md:476`.** TOOK `envSetNumeral∈`'s `ω ∈ σ`
  hypothesis, and `:470` the fixed iterate 4.
- **`src/L/BoundedSubset.lagda.md:903-905`.** TOOK `HullStage`'s telescope
  `lam, ordλ, succλ, X, X⊆L, ∅∈λ`; re-derived, matches the brief.
- **`src/L/Condensation.lagda.md:7222`.** TOOK `KValue`'s telescope
  `lam, ordλ, succλ, ∅∈λ, gam, ordγ, γ∈λ`, no `ω∈λ`.
- **`archive/dev/TASKS-archived.md:10`.** TOOK the shape note that the
  retired route's records say which approaches died. No claim taken.
- **`archive/src/2026-08-09-rud-route/L/Coding/EnvSet.lagda.md:85-87`.**
  TOOK the `stageFor`/`boundingOrd` shape. **What would NOT transfer:** the
  retired bound never states the set in the tower's stage, so it never faced
  the `ω ∈ σ` discharge; and its shape still needs a bound above `ω` to merge
  the numerals' `Lset ω` with the carrier's `Lset σ`.

## 7. LITERATURE USED (DD18)

- **`dev/literature/devlin-II5.md:339,345`.** Devlin's uniform-Δ₁ facts are
  stated at **limit α > ω**. So `ω` inside the stage is part of Devlin's own
  setup (`α > ω`), exactly the term the tree's `HullStage`/`KValue` telescope
  drops. Devlin does not take the bound differently; he assumes the limit is
  above `ω`, and the tree must state that assumption.

## 8. PROHIBITIONS, ANSWERED ONE BY ONE

- Did not build step 6. Did not edit any master. `git status --porcelain src/`
  is empty (checked).
- `src/L/Choice/Name.lagda.md`: **read only**, lines 120-121, 153; never
  edited (DD23).
- `agents/tasks/LJ-1-253/`: **never touched.**
- Probe in `agents/tasks/LJ-1-252/`, tracked, never deleted.
- ONE agda process, `GHCRTS="-A64m -I0 -M8g"`, cap never raised.
- `src/Everything.lagda.md`: **never opened.**
- No commit, push, `checkout .`, `stash`, `reset --hard`, `clean`.
- `make check`: **not run** (reserved for the orchestrator).
