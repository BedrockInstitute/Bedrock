{-# OPTIONS --cubical --safe --guardedness #-}

-- ProbeLJ1235A: strengthen hasReplacementL's conclusion so the bounding stage
-- comes out.  The internal module `Images` already computes `βimg`, the bound
-- on the stages of the images, and proves `img∈βimg`; the existing conclusion
-- throws both away.  This probe writes the sibling lemma that returns `βimg`
-- beside the contractible replacement set, together with the fact that every
-- member of the replacement set lands in `Lset βimg`.

open import Base.Prelude
open import Base.Truth
open import Base.Classical using ( LEM )

module ProbeLJ1235A {ℓ : Level} (lem : LEM (ℓ-suc ℓ)) where

open import FOL.ZFStructure using ( module hPropStructure )
open import FOL.Syntax using ( Formula )
open import V.Hierarchy {ℓ} using ( 𝒮ᵥ )
open import L.Constructible {ℓ}
  using ( 𝒮ʟ; isL; isL-trans; IsOrd; Lset )
import FOL.ZFModel
import FOL.Absoluteness
open import L.Axioms.Full {ℓ} lem
  using ( module Images; hasReplacementL )

import Cubical.HITs.PropositionalTruncation as PT
open import Cubical.HITs.CumulativeHierarchy.Base using ( V; _∈_ )

open TruthAlgebra (hPropAlgebra (ℓ-suc ℓ))
open hPropStructure 𝒮ʟ

module ModelL = FOL.ZFModel 𝒮ʟ
open ModelL using ( SetOf )

module AbsL = FOL.Absoluteness.Single 𝒮ᵥ isL isL-trans
open AbsL renaming ( _⊨ᵐ_ to _⊨_ )

-- The class the replacement set realizes.
replQ : (a : S) (φ : Formula S 2) → S → Ω
replQ a φ y = ⋁ S (λ x → (x ∈ˢ a) ⊓ ((y ∷ x ∷ []) ⊨ φ))

-- The strengthened conclusion.  `βimg` is the bound `hasReplacementL` computes
-- internally and discards; it is stated in terms of the input `a` and `φ`.
hasReplacementL-bound : (a : S) (φ : Formula S 2)
  → (fc : (x : S) → ⟨ x ∈ˢ a ⟩
       → isContr (Σ[ y ∈ S ] ⟨ (y ∷ x ∷ []) ⊨ φ ⟩))
  → Σ[ β ∈ V ℓ ] (IsOrd β
       × isContr (SetOf (replQ a φ))
       × ((y : S) → ⟨ replQ a φ y ⟩ → ⟨ fst y ∈ Lset β ⟩))
hasReplacementL-bound a φ fc =
  βimg , (βimg-ord , (hasReplacementL a φ fc , img-mem))
  where
  open Images a φ fc

  img-mem : (y : S) → ⟨ replQ a φ y ⟩ → ⟨ fst y ∈ Lset βimg ⟩
  img-mem y = PT.rec (snd (fst y ∈ Lset βimg))
    (λ { (x , (x∈a , h)) →
        subst (λ w → ⟨ fst w ∈ Lset βimg ⟩)
          (img-uniq (x , x∈a) y h)
          (img∈βimg (x , x∈a)) })
