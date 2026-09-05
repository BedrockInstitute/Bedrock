{-# OPTIONS --cubical --safe --guardedness #-}

open import Base.Prelude
open import Base.Truth
open import Base.Classical using ( LEM )

module LJ-1-732.runs.Amb2 {ℓ : Level} (lem : LEM (ℓ-suc ℓ)) where

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
open import LJ-1-732.runs.Num {ℓ} lem
open import LJ-1-732.runs.Amb1 {ℓ} lem

open TruthAlgebra (hPropAlgebra (ℓ-suc ℓ))
open hPropStructure 𝒮ᵥ

open import LJ-1-732.runs.Amb3 {ℓ} lem
open import LJ-1-732.runs.Amb4 {ℓ} lem

-- =====================================================================
-- THE AMBIENT READING AT THE EMPTY INSTANCE.  a' = Lset ∅ and
-- p' = ∅ kill isOrd-at-p at its first binder; the twelve numerals
-- ride Z; the table is the empty set and every extAtB row dies at
-- its own first binder.
-- =====================================================================

ambient-matrix :
    ⟨ (Lset ∅ ∷ ∅ ∷ n 12 ∷ []) P652.⊨ₚ P667.matrix₃ ⟩
ambient-matrix = isOrd-part , erased-part
  where
  isOrd-part :
      ⟨ (Lset ∅ ∷ ∅ ∷ n 12 ∷ []) P652.⊨ₚ P667.isOrd-at-p ⟩
  isOrd-part =
      (λ x h → Empty.rec* (subst ⟨_⟩ (empty-spec x) h))
    , (λ x h → Empty.rec* (subst ⟨_⟩ (empty-spec x) h))

  -- φ₃ at the empty instance: the twelve numerals ride Z, and the
  -- 520 matrix survives with the empty table.  The goal at the
  -- matrix's depth is the erasure named in Amb1: the erase result
  -- does not depend on which zero-count proof is passed down.
  erased-part :
      ⟨ (Lset ∅ ∷ ∅ ∷ n 12 ∷ []) P652.⊨ₚ P667.φ₃ ⟩
  erased-part =
    ∣ n 11 , (mem11 ,
    ∣ n 10 , (mem10 ,
    ∣ n 9 , (mem9 ,
    ∣ n 8 , (mem8 ,
    ∣ n 7 , (mem7 ,
    ∣ n 6 , (mem6 ,
    ∣ n 5 , (mem5 ,
    ∣ n 4 , (mem4 ,
    ∣ n 3 , (mem3 ,
    ∣ n 2 , (mem2 ,
    ∣ n 1 , (mem1 ,
    ∣ n 0 , (mem0 , matrix15) ∣₁) ∣₁) ∣₁) ∣₁) ∣₁) ∣₁)
    ∣₁) ∣₁) ∣₁) ∣₁) ∣₁) ∣₁
    where
    matrix15 : ⟨ γ15 P652.⊨ₚ erased-matrix ⟩
    matrix15 = transK-part , (pins-part , graph-part)
