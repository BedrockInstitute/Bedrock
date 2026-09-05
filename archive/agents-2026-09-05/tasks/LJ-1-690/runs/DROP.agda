{-# OPTIONS --cubical --safe --guardedness #-}

-- [LJ-1.690] LsetGraphAt strengthening, inverse of [LJ-1.685] lift13.
-- Does NOT import Probe520 or DefBodyB.  P-l: the type names the
-- sealed graph, not a transparent twelve-row table.

open import Base.Prelude
open import Base.Truth
open import Base.Classical using ( LEM )

module LJ-1-690.runs.DROP {ℓ : Level} (lem : LEM (ℓ-suc ℓ)) where

open import FOL.ZFStructure using ( module hPropStructure )
open import FOL.Manipulation.Renaming using ( module Sat )
import FOL.Absoluteness
open import V.Hierarchy {ℓ} using ( 𝒮ᵥ )
open import L.Constructible {ℓ} using ( 𝒮ʟ; isL; isL-trans )
open import L.Coding.Sequence {ℓ} lem using ( LsetGraphAt )
open import Cubical.Data.Vec using ( lookup; _∷_ )
open import Cubical.Data.Nat using ( _+_ )

import LJ-1-690.runs.RENAME3 {ℓ} lem as RG

open TruthAlgebra (hPropAlgebra (ℓ-suc ℓ))
open hPropStructure 𝒮ʟ
module AbsL = FOL.Absoluteness.Single 𝒮ᵥ isL isL-trans
open AbsL using ( _^_ ) renaming ( _⊨ᵐ_ to _⊨_ )
module RSat = Sat (hPropAlgebra (ℓ-suc ℓ)) 𝒮ʟ {K = S} (λ x → x)

private
  sh13 : {n : ℕ} → Fin n → Fin (13 + n)
  sh13 i = suc (suc (suc (suc (suc (suc (suc (suc (suc (suc (suc (suc (suc (i)))))))))))))

  cons13 : {n : ℕ} → S → S → S → S → S → S → S → S → S → S → S → S → S
         → S ^ n → S ^ (13 + n)
  cons13 a0 a1 a2 a3 a4 a5 a6 a7 a8 a9 a10 a11 a12 γ =
    a0 ∷ a1 ∷ a2 ∷ a3 ∷ a4 ∷ a5 ∷ a6 ∷ a7 ∷ a8 ∷ a9 ∷ a10 ∷ a11 ∷ a12 ∷ γ

drop13 : {n : ℕ} (w b : Fin n) (γ : S ^ n)
       → (a0 a1 a2 a3 a4 a5 a6 a7 a8 a9 a10 a11 a12 : S)
       → ⟨ cons13 a0 a1 a2 a3 a4 a5 a6 a7 a8 a9 a10 a11 a12 γ
             ⊨ LsetGraphAt (sh13 w) (sh13 b) ⟩
       → ⟨ γ ⊨ LsetGraphAt w b ⟩
drop13 w b γ a0 a1 a2 a3 a4 a5 a6 a7 a8 a9 a10 a11 a12 hG =
  subst ⟨_⟩ (RSat.⊨-rename sh13 (LsetGraphAt w b) env γ agrees)
    (subst ⟨_⟩ (cong (env ⊨_) (sym (RG.rename-graph sh13 w b))) hG)
  where
  env = cons13 a0 a1 a2 a3 a4 a5 a6 a7 a8 a9 a10 a11 a12 γ
  agrees : RSat.Agrees sh13 env γ
  agrees i = refl
