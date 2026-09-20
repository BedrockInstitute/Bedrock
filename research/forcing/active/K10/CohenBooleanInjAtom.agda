{-# OPTIONS --cubical --safe --guardedness #-}

open import Base.Prelude
open import Base.Truth
open import Base.Classical using ( LEM )
open import FOL.ZFStructure using ( ZFStructure )
import NameKernel
import OrdinaryProfile
import K10.CohenBooleanInjMaps

-- Fourth extraction layer: the four conjuncts of hitAtom, still as
-- formula satisfaction. No memAtˢ-reading and no checks-reading.

module K10.CohenBooleanInjAtom
  {ℓ} (𝒮 : ZFStructure (hPropAlgebra ℓ))
  (families : NameKernel.Families 𝒮)
  (accessible : NameKernel.Accessibility 𝒮)
  (images : NameKernel.MemberImage 𝒮)
  (pow : OrdinaryProfile.PowerSet 𝒮)
  (κ w : ZFStructure.S 𝒮)
  (lem : LEM ℓ)
  (paths : (x y : ZFStructure.S 𝒮)
         → (ZFStructure._≈ˢ_ 𝒮 x y) ≡ ((x ≡ y) , ZFStructure.isSetS 𝒮 x y))
  where

open import FOL.ZFStructure using ( module hPropStructure )
open import FOL.Syntax using ( _∈̇_ ; var )
open import FOL.Semantics (hPropAlgebra ℓ) 𝒮 using ( module At )
open import CodedVocabulary 𝒮 using ( isKPairΔ ; instFo )

open TruthAlgebra (hPropAlgebra ℓ)
open hPropStructure 𝒮
open At S id using ( _⊨_ )

module Maps = K10.CohenBooleanInjMaps 𝒮 families accessible images pow κ w lem paths
open Maps using ( hitAtom ; checkPair ; pairDom )
open Maps.CD.G.AtomicGraph Maps.CD.atomicGraph using ( memAtˢ )

atom-env : (b τ pair n r y ξ p σ B : S) → _
atom-env b τ pair n r y ξ p σ B =
  b ∷ τ ∷ pair ∷ n ∷ r ∷ y ∷ ξ ∷ p ∷ σ ∷ B ∷ []

MemSat : (b τ pair n r y ξ p σ B : S) → Ω
MemSat b τ pair n r y ξ p σ B =
  atom-env b τ pair n r y ξ p σ B
    ⊨ memAtˢ zero (suc zero)
        (suc (suc (suc (suc (suc (suc (suc (suc zero))))))))
        (suc (suc (suc (suc (suc (suc (suc (suc (suc zero)))))))))

hit-atom-parts : (ω₁ b τ pair n r y ξ p σ B : S)
  → ⟨ atom-env b τ pair n r y ξ p σ B ⊨ hitAtom ω₁ ⟩
  → ⟨ isKPairΔ pair ξ n ⟩
    × ⟨ atom-env b τ pair n r y ξ p σ B
          ⊨ instFo checkPair (Maps.Chk.checks (pairDom ω₁)) ⟩
    × ⟨ atom-env b τ pair n r y ξ p σ B
          ⊨ memAtˢ zero (suc zero)
              (suc (suc (suc (suc (suc (suc (suc (suc zero))))))))
              (suc (suc (suc (suc (suc (suc (suc (suc (suc zero))))))))) ⟩
    × ⟨ r ∈ˢ b ⟩
hit-atom-parts ω₁ b τ pair n r y ξ p σ B (pairξn , checksτ , memb , rinb) =
  pairξn , checksτ , memb , rinb
