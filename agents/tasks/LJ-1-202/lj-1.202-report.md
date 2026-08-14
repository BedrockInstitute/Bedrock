# LJ-1.202 report: is `ω ∈ lam` derivable at the sole `HullStage` site?

**STATUS: STOP, clean answer.** The lead is CONFIRMED by a typecheck. Every
negative is marked **MEASURED** or **INFERRED** (C-36).

## 0. LEAD

**DERIVABLE.** Step 6 is unblocked on the `ω ∈ lam` question. The lead is
**CONFIRMED**.

`ω ∈ lam` needs no new hypothesis. The sole `HullStage` instantiator can
derive it from facts already in its telescope. The join from `[LJ-1.199]`
dissolves.

## 1. CRITERIA, FIXED BEFORE THE RUN (D-1)

ONE agda process, `GHCRTS="-A64m -I0 -M8g"`, cap never raised. **30 minutes
per invocation.** Count: in-fence non-blank lines, ledger caliber.

- **DERIVABLE, NO PARAMETER.** Consumer derives `ω ∈ lam` in place. STOP.
- **DERIVABLE, PARAMETER CHEAPER.** Price both shapes.
- **NOT DERIVABLE.** Name what would supply it and stop.
- **A WALL.** Interrupt past 30 minutes, report elapsed seconds, bisect.

The run landed the first criterion. **MEASURED.**

## 2. THE DERIVATION

The probe is `agents/tasks/LJ-1-202/probeWInLam.lagda.md`. Its module
`Derive` takes exactly the hypotheses in scope at the instantiation site
`src/L/BoundedSubset.lagda.md:1385-1405`: `ordα` (`:1387`), `ordλ` and
`α∈λ` (`:1393`), `α∉ω` (`:1387`). It derives `ω ∈ lam` at
`probeWInLam.lagda.md:37-42`:

```agda
module Derive
  (α lam : S) (ordα : IsOrd α) (ordλ : IsOrd lam)
  (α∈λ : ⟨ α ∈ˢ lam ⟩) (α∉ω : ⟨ α ∈ˢ ω ⟩ → Empty.⊥) where

  ω∈λ : ⟨ ω ∈ˢ lam ⟩
  ω∈λ = Sum.rec
    (λ α∈ω → Empty.rec (α∉ω α∈ω))
    (Sum.rec (λ α≡ω → subst (λ w → ⟨ w ∈ˢ lam ⟩) α≡ω α∈λ)
             (λ ω∈α → ordλ .fst ω∈α α∈λ))
    (ord-tri α ordα ω ω-ord)
```

The trichotomy `ord-tri α ordα ω ω-ord` gives
`α ∈ ω ⊎ (α ≡ ω ⊎ ω ∈ α)`. The first branch dies on `α∉ω`. The equal
branch substitutes `α∈λ` along `α ≡ ω`. The third branch closes by
transitivity of `lam` (`ordλ .fst`). **MEASURED: the probe typechecks,
exit code 0.**

The pattern is already in the master, at `src/L/BoundedSubset.lagda.md:1207-1210`
(`UnionKit.one∈α`), which runs the same trichotomy but concludes
`sucV ∅ ∈ α`. **MEASURED by reading.**

## 3. THE SHAPE TAKEN, AND WHY

**DERIVABLE, NO PARAMETER.** The derivation is 4 lines and uses only facts
already in scope. No fourth `HullStage` hypothesis. No debt for any future
instantiator. The standing prohibition stands, and it is not even
suspended: no new hypothesis is needed.

## 4. WHERE THE DERIVATION GOES (DD4)

The derivation names no tower. It is a pure ordinal fact:

```agda
ω-below-infinite : (α lam : S) → IsOrd α → IsOrd lam
                 → (⟨ α ∈ˢ ω ⟩ → Empty.⊥) → ⟨ α ∈ˢ lam ⟩ → ⟨ ω ∈ˢ lam ⟩
```

Both towers use ordinals and `ord-tri`. So the generic home is
`L.Ordinal.Linear` (where `ord-tri` lives), one lemma plus one import of
`ω-ord`. The consumer in the satisfaction layer then applies it. That is
the DD4-clean shape. An in-place 4-line derivation inside `BoundedSubsetAt`
also works but is not the generic home.

## 5. LINES AND SECONDS

- Probe: **33 in-fence non-blank lines**, counted with `awk` over the
  ` ```agda ` fence.
- The derivation core: **4 lines** (`:37-42`).
- **1 agda invocation, 1 second**, `GHCRTS="-A64m -I0 -M8g"`. One process.
  No wall. Load: cold interfaces were warm; the figure is the warm check.

## 6. EVERY NEGATIVE, CLASSIFIED

| statement | class |
|---|---|
| `ω ∈ lam` is derivable at the sole instantiation site | **MEASURED TRUE.** `probeWInLam.lagda.md:37-42`, exit 0 |
| `ω ∈ lam` needs a new `HullStage` hypothesis | **MEASURED FALSE.** The derivation needs none |
| the lead's dichotomy `ω ∈ α ⊎ ω ≡ α` from `α∉ω` | **MEASURED TRUE.** It is `ord-tri` minus the `α ∈ ω` branch |
| the third branch needs a two-ordinal merge | **NOT CLAIMED here.** `[LJ-1.199]` priced that merge with `ord-tri`; this task measures only the `ω ∈ lam` link |
| a wall occurred | **MEASURED FALSE.** 1 second, no heap figure |
| `make check` was run | **MEASURED FALSE.** Reserved for the orchestrator |
| I edited a master under `src/` | **MEASURED FALSE.** `src/` is untouched |
| the 21 cured fields were touched | **MEASURED FALSE.** `src/` untouched |

## 7. ARCHIVE USED (DD18)

- **`agents/tasks/LJ-1-199/lj-1.199-report.md`, READ WHOLE.** TOOK the join
  and its three citations. The join is real as far as it goes: `ω ∈ lam` is
  not a `HullStage` parameter. Its section 2.3 already said `ω ∈ lam` is
  "the weakest fact that would discharge it", and its section 7 prices only
  the merge. **This report measures the one link it did not measure: that
  `ω ∈ lam` is derivable at the site.**
- **`src/L/BoundedSubset.lagda.md:1380-1405`, READ.** TOOK the exact
  in-scope hypotheses. The lead's citation is exact.
- **`src/L/BoundedSubset.lagda.md:1205-1210`, READ.** TOOK the existing
  `UnionKit.one∈α` trichotomy as the delivered pattern.
- **`src/L/Ordinal.lagda.md:263-264`**, `src/L/Ordinal/Linear.lagda.md:136`:
  TOOK `ω-ord` and `ord-tri`.
- **`archive/dev/TASKS-archived.md`.** Took SHAPE only. The retired route's
  `EnvSet` never stated the set in a stage, so it never faced this
  discharge (`[LJ-1.199]` section 10). **What would NOT transfer: nothing
  here; the retired route has no analogue of `ω ∈ lam` to copy.**
- **`scripts/rules.py --for probe` and `--for build`, READ.** TOOK C-22
  (wrote this report in the first minutes), C-36, C-42, D-1, C-12.

## 8. LITERATURE USED (DD18)

- **`dev/literature/devlin-II5.md`, READ the limit-stage passages.**
  Devlin's construction runs at **limit α > ω** (`:218`, `:339`, `:345`).
  **The `ω ∈ α` fact is a HYPOTHESIS of his setup, not a construction.**
  The condition `α > ω` is assumed at the top. The tree dropped it; this
  report shows the tree's site can recover it.
- **`dev/literature/devlin-errata.md`, READ the `ω` passages.** The errata
  use the same standing form "for limit λ > ω" (`:140`). They do not touch
  II.5's use of it. **MEASURED by reading.**

## 9. PROHIBITIONS, ANSWERED ONE BY ONE

- `src/L/Choice/Name.lagda.md`: **NEVER OPENED.**
- The 21 cured fields: **NOT TOUCHED.**
- Probe location: `agents/tasks/LJ-1-202/probeWInLam.lagda.md`, tracked.
- `src/Everything.lagda.md`: **NEVER OPENED.**
- Commit, push, `checkout .`, `stash`, `reset --hard`, `clean`: **NONE.**
- `make check`: **NOT RUN.**
- Heap cap: `GHCRTS="-A64m -I0 -M8g"`, one process, never approached.
