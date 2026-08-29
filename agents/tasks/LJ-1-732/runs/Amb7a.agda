{-# OPTIONS --cubical --safe --guardedness #-}

open import Base.Prelude
open import Base.Truth
open import Base.Classical using ( LEM )

module LJ-1-732.runs.Amb7a {ℓ : Level} (lem : LEM (ℓ-suc ℓ)) where

open import FOL.ZFStructure using ( module hPropStructure )
open import V.Hierarchy {ℓ} using ( 𝒮ᵥ )
open import LJ-1-652.Probe652 {ℓ} lem as P652
open import LJ-1-732.runs.Num {ℓ} lem
open import LJ-1-732.runs.Amb1 {ℓ} lem

open TruthAlgebra (hPropAlgebra (ℓ-suc ℓ))
open hPropStructure 𝒮ᵥ

-- the approximation reading at the empty instance, named once (P-l:
-- downstream use sites name the reading, never the erased
-- presentation)
ApproxAt : Type (ℓ-suc ℓ)
ApproxAt = ⟨ (n 0 ∷ γ15) P652.⊨ₚ CntS.erase Mx.G.A.approxBndAt countA ⟩

-- the step reading under the two binders, named once so the body's
-- motive shares one normal form instead of recomputing it.  The
-- value is the hProp record; the body takes its .snd.
MotiveEmpty : (u v : S) → hProp (ℓ-suc ℓ)
MotiveEmpty u v =
  (v ∷ u ∷ n 0 ∷ γ15) P652.⊨ₚ CntS.erase Mx.G.A.S.stepBndAt countAS
