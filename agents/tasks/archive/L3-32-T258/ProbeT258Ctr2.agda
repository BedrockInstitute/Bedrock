{-# OPTIONS --cubical --guardedness #-}

-- [L3.32-T258] Minimal discriminator: the master's exact conversion
-- shapes at depth 3 (Tγ∈C) and depth 6 (segγ∈C), as definition
-- boundaries and as Ctr application premises.  Untracked probe, no
-- git, no master.

open import Base.Prelude
open import Base.Truth
open import Base.Classical using ( LEM )
open import Cubical.HITs.CumulativeHierarchy.Base using ( V )
open import FOL.ZFStructure using ( module hPropStructure )
open import Cubical.HITs.CumulativeHierarchy.Constructions
  using ( module InfinitySet )
open InfinitySet using ( sucV )
open import L.Constructible using ( isTransV )

module ProbeT258Ctr2 {ℓ : Level} (lem : LEM (ℓ-suc ℓ))
  (C : V ℓ) (Ctr : isTransV C) (γ : V ℓ) where

open import L.Constructible {ℓ} using ( Lset )
open import V.Hierarchy {ℓ} using ( 𝒮ᵥ )
open hPropStructure 𝒮ᵥ

postulate
  segγ : S

  p3 : ⟨ segγ ∈ˢ Lset (sucV (sucV (sucV γ))) ⟩
  g3 : ⟨ Lset (sucV (sucV (sucV γ))) ∈ˢ C ⟩

  p6 : ⟨ segγ ∈ˢ Lset (sucV (sucV (sucV (sucV (sucV (sucV γ)))))) ⟩
  g6 : ⟨ Lset (sucV (sucV (sucV (sucV (sucV (sucV γ)))))) ∈ˢ C ⟩

δγ₃ : S
δγ₃ = sucV (sucV (sucV γ))

δγ₆ : S
δγ₆ = sucV (sucV (sucV γ))

-- A. The master's Tγ∈C conversion at a definition boundary.
g3δ' : ⟨ Lset δγ₃ ∈ˢ C ⟩
g3δ' = g3

p3δ' : ⟨ segγ ∈ˢ Lset δγ₃ ⟩
p3δ' = p3

-- B. The master's segγ∈C conversion at a definition boundary.
g6δ' : ⟨ Lset (sucV (sucV (sucV δγ₆))) ∈ˢ C ⟩
g6δ' = g6

p6δ' : ⟨ segγ ∈ˢ Lset (sucV (sucV (sucV δγ₆))) ⟩
p6δ' = p6

-- C. The same conversions inside a Ctr application.
testApp3 : ⟨ segγ ∈ˢ C ⟩
testApp3 = Ctr {x = Lset δγ₃} {y = segγ} p3 g3

testApp6 : ⟨ segγ ∈ˢ C ⟩
testApp6 = Ctr {x = Lset (sucV (sucV (sucV δγ₆)))}
  {y = segγ} p6 g6

-- D. Matching-premise applications, for the baseline.
test3 : ⟨ segγ ∈ˢ C ⟩
test3 = Ctr {x = Lset (sucV (sucV (sucV γ)))} {y = segγ} p3 g3

test6 : ⟨ segγ ∈ˢ C ⟩
test6 = Ctr {x = Lset (sucV (sucV (sucV (sucV (sucV (sucV γ))))))}
  {y = segγ} p6 g6
