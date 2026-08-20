{-# OPTIONS --cubical --safe --guardedness #-}

-- [LJ-1.419] PROBE.  Does the rank route discharge the consumer
-- WITHOUT the pairing parameter?
--
--   TERM      `from-two-hyps`.  The composition the brief names:
--             `stage-into-bound`, then `bound-into-ord`, then
--             `comp-inj`.  No sq in any telescope.
--
--   OBLIGATION  `upper-from-rank`.  Same type as the consumer.  Left
--               as a hole: D-10, the residue as stated is false, and
--               a green inhabitant of this name would fire branch go.
--
--   TWO MODULE HYPOTHESES, not imported, not rebuilt:
--             `stage-into-bound` at [LJ-1.418]'s delivered type
--               (Probe418.agda:64-65, GO at lj-1.418-report.md:19;
--               this worktree has no LJ-1-418/, opened in the main
--               tree agents/tasks/LJ-1-418/),
--             `bound-into-ord`, the residue, as the brief names it
--               (LJ-1.419.md:27-29). Not attempted. D-10: false.
--
-- ONE Agda process per run, GHCRTS as the program set it on this pane.
-- Nothing lands in src/.

open import Base.Prelude
open import Base.Truth
open import Base.Classical using ( LEM )
open import Cubical.HITs.CumulativeHierarchy.Base using ( V )
open import Cubical.HITs.CumulativeHierarchy.Properties using ( ⟪_⟫ )
open import Cubical.HITs.CumulativeHierarchy.Constructions
  using ( module InfinitySet )
open InfinitySet using ( ω; sucV )
open import L.Constructible using ( IsOrd )
import Cubical.Data.Empty as Empty

module LJ-1-419.Probe419 {ℓ : Level} (lem : LEM (ℓ-suc ℓ))
  (α₀ : V ℓ) (oα₀ : IsOrd α₀) where

open import FOL.ZFStructure using ( module hPropStructure )
open import V.Hierarchy {ℓ} using ( 𝒮ᵥ )
open import L.Constructible {ℓ} using ( Lset )
open import Cubical.Data.Sigma using ( Σ; Σ-syntax )

open TruthAlgebra (hPropAlgebra (ℓ-suc ℓ))
open hPropStructure 𝒮ᵥ

_↪_ : Type ℓ → Type ℓ → Type ℓ
X ↪ Y = Σ[ f ∈ (X → Y) ] ((x y : X) → f x ≡ f y → x ≡ y)

comp-inj : {A B C : Type ℓ} → A ↪ B → B ↪ C → A ↪ C
comp-inj (f , injf) (g , injg) =
  (λ x → g (f x)) , λ x y e → injf x y (injg (f x) (f y) e)

-- =====================================================================
-- TWO MODULE HYPOTHESES.  Not imported.  Not rebuilt.  The residue is
-- not attempted.
-- =====================================================================

module _
  (stage-into-bound :
      (α : S) → IsOrd α
    → Σ[ β ∈ S ] (IsOrd β × (⟪ Lset α ⟫ ↪ ⟪ β ⟫)))
  (bound-into-ord :
      (α : S) → IsOrd α → (⟨ α ∈ˢ ω ⟩ → Empty.⊥)
    → (β : S) → IsOrd β → (⟪ Lset α ⟫ ↪ ⟪ β ⟫)
    → ⟪ β ⟫ ↪ ⟪ α ⟫)
  where

  -- The composition the brief names.  The band hypothesis is unused:
  -- neither supplier reads it.  It is kept so the type matches the
  -- consumer verbatim.
  from-two-hyps :
      (α : S) → IsOrd α → ⟨ α ∈ˢ sucV α₀ ⟩
    → (⟨ α ∈ˢ ω ⟩ → Empty.⊥) → ⟪ Lset α ⟫ ↪ ⟪ α ⟫
  from-two-hyps α oα _ infα =
    comp-inj emb (bound-into-ord α oα infα β oβ emb)
    where
    pack : Σ[ β ∈ S ] (IsOrd β × (⟪ Lset α ⟫ ↪ ⟪ β ⟫))
    pack = stage-into-bound α oα
    β : S
    β = fst pack
    oβ : IsOrd β
    oβ = fst (snd pack)
    emb : ⟪ Lset α ⟫ ↪ ⟪ β ⟫
    emb = snd (snd pack)

  -- The consumer's target, verbatim, with no sq in scope.
  -- src/L/StageCardinal.lagda.md:564-565.
  ConsumerShape : Type (ℓ-suc ℓ)
  ConsumerShape =
      (α : S) → IsOrd α → ⟨ α ∈ˢ sucV α₀ ⟩
    → (⟨ α ∈ˢ ω ⟩ → Empty.⊥) → ⟪ Lset α ⟫ ↪ ⟪ α ⟫

  -- D-10: the residue as stated is false (review-of-bound-into-ord.md).
  -- A green upper-from-rank would fire branch go and claim the
  -- pairing parameter is replaceable.  The composition is exhibited
  -- as from-two-hyps.  This name stays a hole.
  upper-from-rank : ConsumerShape
  upper-from-rank = {!!}
