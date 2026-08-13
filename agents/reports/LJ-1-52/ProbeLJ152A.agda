{-# OPTIONS --cubical --safe --guardedness #-}

-- [LJ-1.52] probe A: PIN THE SEMANTICS OF THE LEVEL-HOOD MATRIX.
--
-- The obligation's semantic core at the CLASS carrier: the bounded
-- level-hood matrix decodes to "w = Lset gamma".  The decode needs the
-- bounded-graph agreement (graphBndAt vs LsetGraphAt), which is NOT
-- delivered; this probe states that agreement as a hypothesis and
-- closes the decode from it plus the delivered ride-only.  It pins the
-- statement shape the twelve-row re-basing must prove at the hull.
--
-- Untracked probe; one Agda process under GHCRTS="-A64m -I0 -M8g";
-- never committed.

open import Base.Prelude
open import Base.Truth
open import Base.Classical using ( LEM )

module ProbeLJ152A {ℓ : Level} (lem : LEM (ℓ-suc ℓ)) where

open import FOL.ZFStructure using ( module hPropStructure )
open import FOL.Syntax using ( Formula; var; _≐_; _∧̇_; ∃̇∈ )
import FOL.Absoluteness
open import V.Hierarchy {ℓ} using ( 𝒮ᵥ )
import Cubical.HITs.PropositionalTruncation as PT
open PT using ( ∥_∥₁; ∣_∣₁; squash₁ )
open import Cubical.HITs.CumulativeHierarchy.Base using ( setIsSet )
open import Cubical.Data.Vec using ( map )
open import L.Constructible {ℓ} using ( 𝒮ʟ; isL; isL-trans; IsOrd; Lset )
open import L.Coding.Sequence {ℓ} lem using ( LsetGraphAt )
open import L.Condensation {ℓ} lem using ( ride-only )
open import L.BoundedSubset {ℓ} lem using ( module LevelHood0 )

open TruthAlgebra (hPropAlgebra (ℓ-suc ℓ))
open hPropStructure 𝒮ʟ

module AbsL = FOL.Absoluteness.Single 𝒮ᵥ isL isL-trans
open AbsL renaming ( _⊨ᵐ_ to _⊨_ )

module LH0 = LevelHood0
  zero zero zero zero zero zero zero zero zero zero zero zero zero zero
  zero zero zero zero zero zero zero zero zero zero zero zero zero zero

-- The bounded-graph agreement, stated as the obligation's unbuilt half.
-- At env x ∷ w ∷ v ∷ γ ∷ K, the bounded graph implies the machine
-- graph at the value slot w (slot 1) and the index slot γ (slot 3).
-- This slot reading is what the probe exists to pin.
GraphAgree : Type (ℓ-suc ℓ)
GraphAgree =
  (x w v γ K : S) (oγ : IsOrd (fst γ))
  → ⟨ (x ∷ w ∷ v ∷ γ ∷ K ∷ []) ⊨ LH0.LH.G.graphBndAt ⟩
  → ⟨ (x ∷ w ∷ v ∷ γ ∷ K ∷ []) ⊨
       LsetGraphAt {5} (suc zero) (suc (suc (suc zero))) ⟩

-- The matrix decode at the class carrier: from the bounded matrix at
-- env w ∷ v ∷ γ ∷ K, get w = Lset γ, given the index's ordinality and
-- the graph agreement.
matrix-decode : (ga : GraphAgree) (w v γ K : S) (oγ : IsOrd (fst γ))
              → ⟨ (w ∷ v ∷ γ ∷ K ∷ []) ⊨ LH0.matrix ⟩
              → fst w ≡ Lset (fst γ)
matrix-decode ga w v γ K oγ h =
  PT.rec (setIsSet (fst w) (Lset (fst γ))) go h
  where
  go : Σ[ x ∈ S ]
         (⟨ x ∈ˢ K ⟩
        × ⟨ (x ∷ w ∷ v ∷ γ ∷ K ∷ []) ⊨
             (LH0.LH.G.graphBndAt ∧̇ (var (suc zero) ≐ var zero)) ⟩)
     → fst w ≡ Lset (fst γ)
  go (x , x∈K , hx) =
    let env : S ^ 5
        env = x ∷ w ∷ v ∷ γ ∷ K ∷ []
    in ride-only {5} (suc zero) (suc (suc (suc zero))) env
         (ga x w v γ K oγ (fst hx)) oγ

-- The adequacy statement at an ordinal m: the level at the index m
-- (a parameter) is witnessed inside some K'.  The matrix is at env
-- w' ∷ v' ∷ m ∷ K', so the index slot (slot 2) holds m.
Adeq : S → Type (ℓ-suc ℓ)
Adeq m =
  ∥ Σ[ K' ∈ S ] Σ[ v' ∈ S ] Σ[ w' ∈ S ]
    (⟨ w' ∈ˢ K' ⟩ × ⟨ (w' ∷ v' ∷ m ∷ K' ∷ []) ⊨ LH0.matrix ⟩) ∥₁

-- The decode of the adequacy at the parameter index: Adeq m gives
-- the level at m.
adeq-decode : (ga : GraphAgree) (m : S) (om : IsOrd (fst m))
            → Adeq m
            → ∥ Σ[ K' ∈ S ] Σ[ w' ∈ S ]
                (⟨ w' ∈ˢ K' ⟩ × (fst w' ≡ Lset (fst m))) ∥₁
adeq-decode ga m om = PT.rec squash₁ go
  where
  go : Σ[ K' ∈ S ] Σ[ v' ∈ S ] Σ[ w' ∈ S ]
         (⟨ w' ∈ˢ K' ⟩ × ⟨ (w' ∷ v' ∷ m ∷ K' ∷ []) ⊨ LH0.matrix ⟩)
     → ∥ Σ[ K' ∈ S ] Σ[ w' ∈ S ]
         (⟨ w' ∈ˢ K' ⟩ × (fst w' ≡ Lset (fst m))) ∥₁
  go (K' , v' , w' , w∈K , h) =
    ∣ K' , w' , (w∈K , matrix-decode ga w' v' m K' om h) ∣₁
