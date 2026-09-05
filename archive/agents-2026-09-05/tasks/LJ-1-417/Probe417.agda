{-# OPTIONS --cubical --safe --guardedness #-}

-- [LJ-1.417] PROBE.  Rank injectivity, then an untruncated injection
-- of a generic well-ordered small carrier into an ordinal.
--
--   W3 FIRST  `rank-inj`.  Trichotomy plus irreflexivity.  Stated
--             alone and run before the Sigma.
--
--   TERM      `swo-into-ord`.  `boundingOrd` on the rank, then the
--             fibre map into ⟪ β ⟫, paired as the tree's `_↪_`.
--             No ∥ ∥₁ in the type.
--
--   THREE MODULE HYPOTHESES, not imported, not rebuilt:
--             `swo-rank`, `swo-rank-ord`, `swo-rank-mono`
--             at [LJ-1.416]'s types.
--
-- ONE Agda process per run.  GHCRTS is the wide caliber the program
-- set on this pane.  Nothing lands in src/.

open import Base.Prelude
open import Base.Truth

module LJ-1-417.Probe417 {ℓ : Level} where

open import FOL.ZFStructure using ( module hPropStructure )
open import V.Hierarchy {ℓ} using ( 𝒮ᵥ; ∈-irrefl )
open import V.Presentation {ℓ} using ( fiber )
open import L.Constructible {ℓ} using ( IsOrd )
open import L.Ordinal {ℓ} using ( boundingOrd )
open import L.WellOrder.Base {ℓ-suc ℓ}
  using ( SWO; Tri; lt; eq; gt; module SWO )

open import Cubical.HITs.CumulativeHierarchy.Properties using ( ⟪_⟫; ⟪_⟫↪ )
import Cubical.Data.Empty as Empty

open TruthAlgebra (hPropAlgebra (ℓ-suc ℓ))
open hPropStructure 𝒮ᵥ

-- The tree's embedding type, as StageCardinal and Cardinal write it
-- (src/L/StageCardinal.lagda.md:221-222, src/L/Cardinal.lagda.md:47-48).
_↪_ : Type ℓ → Type ℓ → Type ℓ
X ↪ Y = Σ[ f ∈ (X → Y) ] ((x y : X) → f x ≡ f y → x ≡ y)

module _
  {A : Type ℓ}
  (w : SWO {ℓc = ℓ} A)
  (swo-rank : A → S)
  (swo-rank-ord : (a : A) → IsOrd (swo-rank a))
  (swo-rank-mono : (a b : A) → SWO._<∙_ w a b
                 → ⟨ swo-rank a ∈ˢ swo-rank b ⟩)
  where

  open SWO w

  -- ===================================================================
  -- W3.  Injectivity of the rank.  Trichotomy plus irreflexivity.
  -- No induction.  Stated and proved before the Sigma.
  -- ===================================================================

  rank-inj : (a b : A) → swo-rank a ≡ swo-rank b → a ≡ b
  rank-inj a b p = go (tri∙ a b)
    where
    go : Tri (a <∙ b) (a ≡ b) (b <∙ a) → a ≡ b
    go (lt a<b) = Empty.rec (∈-irrefl (swo-rank a) loop)
      where
      loop : ⟨ swo-rank a ∈ˢ swo-rank a ⟩
      loop = subst (λ r → ⟨ swo-rank a ∈ˢ r ⟩) (sym p)
               (swo-rank-mono a b a<b)
    go (eq a≡b) = a≡b
    go (gt b<a) = Empty.rec (∈-irrefl (swo-rank b) loop)
      where
      loop : ⟨ swo-rank b ∈ˢ swo-rank b ⟩
      loop = subst (λ r → ⟨ swo-rank b ∈ˢ r ⟩) p
               (swo-rank-mono b a b<a)

  -- ===================================================================
  -- THE OBLIGATION.  Bound the rank, map into the member type, pair.
  -- ===================================================================

  swo-into-ord : Σ[ β ∈ S ] (IsOrd β × (A ↪ ⟪ β ⟫))
  swo-into-ord = β , (ordβ , (toMem , toMem-inj))
    where
    pack = boundingOrd A swo-rank swo-rank-ord
    β : S
    β = fst pack
    ordβ : IsOrd β
    ordβ = pack .snd .fst
    memβ : (a : A) → ⟨ swo-rank a ∈ˢ β ⟩
    memβ = pack .snd .snd

    toMem : A → ⟪ β ⟫
    toMem a = fiber β (memβ a) .fst

    toMem-inj : (a b : A) → toMem a ≡ toMem b → a ≡ b
    toMem-inj a b e = rank-inj a b
      (sym (fiber β (memβ a) .snd)
       ∙ cong (⟪ β ⟫↪) e
       ∙ fiber β (memβ b) .snd)
