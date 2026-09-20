{-# OPTIONS --cubical --safe --guardedness #-}

open import Base.Prelude
open import Base.Truth
open import FOL.ZFStructure using ( ZFStructure )

module K7.ValueAbstraction {ℓ} (𝒮 : ZFStructure (hPropAlgebra ℓ)) where

open import FOL.Syntax using ( Formula; var; _∈̇_; _∧̇_; ∃̇_ )
open import FOL.Manipulation.Renaming using ( renameFo )
open import FOL.Manipulation.ParameterAbstraction using ( absFo )
open import FOL.Manipulation.ConstantOccurrences using ( constantsFo )
import CardinalBridge
import K7.PossibleValues
import K7.FunctionalValuesAtNames

open TruthAlgebra (hPropAlgebra ℓ)
open ZFStructure 𝒮 using ( S; isSetS; _≈ˢ_ )
private module Cardinal = CardinalBridge 𝒮

pairφ : Formula (⊥* {ℓ}) 3
pairφ = absFo Cardinal.PairφK

functionφ : Formula (⊥* {ℓ}) 1
functionφ = absFo Cardinal.IsFunctionφ

pair-slots : Fin 3 → Fin 4
pair-slots zero = zero
pair-slots (suc zero) = suc zero
pair-slots (suc (suc zero)) = suc (suc zero)

valueφ : Formula (⊥* {ℓ}) 3
valueφ = ∃̇ (renameFo pair-slots pairφ
  ∧̇ (var zero ∈̇ var (suc (suc (suc zero)))))

module Names
  (paths : (x y : S) → (x ≈ˢ y) ≡ ((x ≡ y) , isSetS x y))
  (IsNm : S → Ω)
  where

  module Values = K7.PossibleValues.Names 𝒮 paths IsNm

  -- K6.Definability.srcOf and parsOf are absFo and constantsFo. These
  -- equalities fix both the source formula and the complete environment
  -- layout used by K6.ForcesTruth, without a constant-renaming assumption.
  value-source : (f : Values.Nm) → absFo (Values.valueFo f) ≡ valueφ
  value-source f = refl

  value-parameters : (f : Values.Nm) → constantsFo (Values.valueFo f) ≡ (f ∷ [])
  value-parameters f = refl

  module AtG (_≈[G]_ _∈[G]_ : S → S → Ω) where
    private module Extension = K7.FunctionalValuesAtNames 𝒮 paths IsNm _≈[G]_ _∈[G]_

    function-source : absFo Extension.CB.IsFunctionφ ≡ functionφ
    function-source = refl

    function-parameters : constantsFo Extension.CB.IsFunctionφ ≡ []
    function-parameters = refl
