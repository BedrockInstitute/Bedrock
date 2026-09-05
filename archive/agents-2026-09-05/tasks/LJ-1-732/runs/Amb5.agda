{-# OPTIONS --cubical --safe --guardedness #-}

open import Base.Prelude
open import Base.Truth
open import Base.Classical using ( LEM )

module LJ-1-732.runs.Amb5 {ℓ : Level} (lem : LEM (ℓ-suc ℓ)) where

open import FOL.ZFStructure using ( module hPropStructure )
open import FOL.Syntax using ( Formula; var; _∈̇_; ⊥̇; ∃̇∈; ∀̇∈ )
open import FOL.Manipulation.Parameters using ( countFo )
import FOL.Count
open import V.Hierarchy {ℓ} using ( 𝒮ᵥ )
open import L.Constructible {ℓ} using ( 𝒮ʟ; Lset )
open import L.Condensation {ℓ} lem using ( domB )
open import Cubical.Data.Nat using ( ℕ )
open import Cubical.Data.Vec using ( lookup; _∷_; [] )
import Cubical.Data.Empty as Empty
import Cubical.HITs.PropositionalTruncation as PT
open PT using ( ∣_∣₁; ∥_∥₁; squash₁ )
open import Cubical.Data.Sigma using ( _×_ )
open import Cubical.Data.Sum using ( _⊎_; inl; inr )
open import Cubical.HITs.CumulativeHierarchy.Constructions
  using ( ∅ )
open import LJ-1-652.Probe652 {ℓ} lem as P652
open import LJ-1-667.Probe667 {ℓ} lem as P667
import LJ-1-520.Probe520 {ℓ} lem as P520
open import V.Model {ℓ} using ( empty-spec )
open import LJ-1-732.runs.Num {ℓ} lem
open import LJ-1-732.runs.Amb1 {ℓ} lem

open TruthAlgebra (hPropAlgebra (ℓ-suc ℓ))
open hPropStructure 𝒮ᵥ

-- the approximation's domain row at the empty instance: the
-- z'-edges of the empty table never exist, and the parameter is empty
domB-part :
    ⟨ (n 0 ∷ γ15) P652.⊨ₚ
        CntS.erase (domB zero (suc bb) (suc kk)) countDomB ⟩
domB-part = λ u u∈ →
    ( λ ant → PT.rec
                ((u ∈ˢ lookup (suc (suc bb)) (u ∷ n 0 ∷ γ15)) .snd)
                (λ { (s , s∈z , appat) →
                      PT.rec
                        ((u ∈ˢ lookup (suc (suc bb))
                            (u ∷ n 0 ∷ γ15)) .snd)
                        (λ { (pr , pr∈∅ , _) →
                              Empty.rec*
                                (subst ⟨_⟩ (empty-spec pr) pr∈∅) })
                        appat })
                ant )
  , ( λ h → Empty.rec* (subst ⟨_⟩ (empty-spec u) h) )
