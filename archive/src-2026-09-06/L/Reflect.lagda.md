# The single-matrix ladder (retired 2026-09-06)

The tail of `module Single` in `src/L/Reflect.lagda.md`: the iterated
step `βₙ` with its ordinal-hood and its ascent `βₙ-step` (and the
unfolding `σ∈Fstep` that supplied the ascent), the instance
`module L = Ladder βₙ βₙ-ord βₙ-step`, its limit `βω`, the answering
hypothesis `answers` discharged by `pickLand`, and the two results the
ladder buys, `closed : ClosedFor βω ψ` and `reflect`.

THE TREE HAD NO CONSUMER FOR ANY OF IT.  The one importer of
`L.Reflect` is `src/L/ReflectFo.lagda.md:60`, which takes `Below`,
`LsetEnv`, `pickStage`, `ClosedFor`, `module Ladder` and `module
Single`, and every use it makes of `Single` is `Single.Fstep`,
`Single.Fstep-ord` or `Single.pickLand`.  It builds its own ladder,
`Gₙ` with `module Lad = Ladder Gₙ Gₙ-ord Gₙ-step`, whose single step
closes all the matrices of a formula at once, which is what the chapter
prose says it is for.  `module Ladder`, `closure` and `Ladder.reflect`
stay in the live file: they are the general ones `ReflectFo` runs.

```agda
    σ∈Fstep : (σ : V ℓ) (oσ : IsOrd σ) → ⟨ σ ∈ Fstep σ oσ ⟩
    σ∈Fstep σ oσ =
      bound2 (Fbnd σ oσ .fst) σ (Fbnd σ oσ .snd .fst) oσ .snd .snd .snd

  βₙ : ℕ → V ℓ
  βₙ-ord : (n : ℕ) → IsOrd (βₙ n)
  βₙ zero        = ∅
  βₙ (suc n)     = Fstep (βₙ n) (βₙ-ord n)
  βₙ-ord zero    = ∅-ord
  βₙ-ord (suc n) = Fstep-ord (βₙ n) (βₙ-ord n)

  βₙ-step : (n : ℕ) → ⟨ βₙ n ∈ βₙ (suc n) ⟩
  βₙ-step n = σ∈Fstep (βₙ n) (βₙ-ord n)

  module L = Ladder βₙ βₙ-ord βₙ-step

  βω : V ℓ
  βω = L.top

  answers : (n : ℕ) (ms : ⟪ Lset (βₙ n) ⟫ ^ k)
          → ⟨ pickStage ψ (LsetEnv (βₙ n) (βₙ-ord n) ms) ∈ βₙ (suc n) ⟩
  answers n = pickLand (βₙ n) (βₙ-ord n)

  closed : ClosedFor βω ψ
  closed = L.closure ψ answers

  reflect : (ρ : S ^ k) → Below βω ρ → (ρ ⊨ (∃̇ ψ)) ≡ Wit ψ ρ βω
  reflect = L.reflect ψ answers
```
