-- LJ-1.155, probe A2.  THE IMPORT TAX.
--
-- ONE question: does a module pay `DeadCode.DeadCodeReachable` for
-- IMPORTING `L.Condensation`, before it writes any content of its own?
--
-- The import list below is `src/L/Condensation/UpperAgree.lagda.md:21-40`
-- VERBATIM.  The body is one trivial definition.  So the only difference
-- from A1 is the import closure, and the only difference from the master
-- is the master's 270 lines of content.
--
-- Read with `agda --profile=internal`.

{-# OPTIONS --cubical --safe --guardedness #-}

open import Base.Prelude
open import Base.Truth
open import Base.Classical using ( LEM )

module LJ-1-155.ProbeLJ1155A2 {ℓ : Level} (lem : LEM (ℓ-suc ℓ)) where

open import FOL.ZFStructure using ( module hPropStructure )
open import FOL.Syntax using ( Formula; var; _∈̇_; _∧̇_ )
import FOL.Absoluteness
open import V.Hierarchy {ℓ} using ( 𝒮ᵥ )
open import V.Coding {ℓ} using ( pr )
open import L.Constructible {ℓ} using ( 𝒮ʟ; isL; isL-trans )
open import L.Axioms.Numerals {ℓ} using ( numeralL; sucʟ; sucʟ-fst )
open import L.Coding.Model {ℓ}
  using ( prʟ; prʟ-fst; envSetAt; envOverAt; tmValAt; consAtL; subValSuccAt
        ; topClauseAt; botClauseAt; existClauseAt; forallClauseAt
        ; allInClauseAt; exInClauseAt )
open import L.Coding.Graph {ℓ} lem using ( twelveAt )
open import L.Condensation {ℓ} lem using
  ( succU; keyU; module Top; module Bot; module Exist; module Forall
  ; module AllIn; module ExIn; module TopAgree; module BotAgree
  ; module ExistAgree; module ForallAgree; module AllInAgree
  ; module ExInAgree )
open import Cubical.Data.Nat using ( _+_ )
open import Cubical.HITs.CumulativeHierarchy.Base using ( _∈_ )
open import Cubical.HITs.CumulativeHierarchy.Constructions using ( module InfinitySet )
open InfinitySet using ( #_; sucV )

open TruthAlgebra (hPropAlgebra (ℓ-suc ℓ))
open hPropStructure 𝒮ʟ

module AbsL = FOL.Absoluteness.Single 𝒮ᵥ isL isL-trans
open AbsL renaming ( _⊨ᵐ_ to _⊨_ )

-- One trivial definition, so the module is not empty.
triv : {n : ℕ} (φ : Formula S n) (γ : S ^ n) → ⟨ γ ⊨ φ ⟩ → ⟨ γ ⊨ φ ⟩
triv φ γ x = x
