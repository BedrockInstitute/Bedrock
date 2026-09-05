{-# OPTIONS --cubical --safe --guardedness #-}

open import Base.Prelude
open import Base.Truth
open import Base.Classical using ( LEM )

open import FOL.ZFStructure using ( module hPropStructure )
import FOL.Absoluteness
open import V.Hierarchy using ( 𝒮ᵥ )
open import Cubical.Foundations.Prelude using ( _≡_ )
open import Cubical.HITs.CumulativeHierarchy.Base using ( V; setIsSet )
open import Cubical.Functions.Logic using ( ⇔toPath )

module LJ-1-213.DefAtStage {ℓ : Level} (lem : LEM (ℓ-suc ℓ)) where

open import L.Constructible {ℓ}
  using ( 𝒮ʟ; isL; isL-trans; IsOrd; Lset; 𝒟ₒ )
open import L.Axioms.Basic {ℓ} using ( 𝒟ₒ→isL; LsetS )
open import L.Coding.Powerset {ℓ} lem using ( DefAt; DefAt-in; DefAt-out )

open TruthAlgebra (hPropAlgebra (ℓ-suc ℓ))
open hPropStructure 𝒮ʟ

module AbsL = FOL.Absoluteness.Single 𝒮ᵥ isL isL-trans
open AbsL using ( _^_ ) renaming ( _⊨ᵐ_ to _⊨_ )

DefAt-stage : (β : V ℓ) (oβ : IsOrd β) → ∀ {n} (u w : Fin n) (γ : S ^ n)
            → fst (lookup w γ) ≡ Lset β
            → (γ ⊨ DefAt u w)
              ≡ ( (fst (lookup u γ) ≡ 𝒟ₒ (Lset β))
                , setIsSet (fst (lookup u γ)) (𝒟ₒ (Lset β)) )
DefAt-stage β oβ u w γ qw = ⇔toPath
  (DefAt-out (LsetS β oβ) u w γ (𝒟ₒ→isL β oβ) qw)
  (DefAt-in (LsetS β oβ) u w γ qw)
