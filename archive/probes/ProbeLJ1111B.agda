{-# OPTIONS --cubical --safe --guardedness #-}

-- [LJ-1.111] probe B: the cheapest cure, machine-checked NO.
--
-- From the delivered LeastCard data (κ = |α|, the leastness κ-min-at,
-- and the truncated witness κ-eqα), the honest injection
-- ⟪ α ⟫ ↪ ⟪ κ ⟫ cannot be extracted:  PT.rec requires isProp of the
-- injection type, and the leastness constrains only strictly smaller
-- equinumerous ordinals, never two witnesses at κ.  The term below is
-- the [LJ-1.107] wall reproduced with the leastness in scope; it is a
-- type error.  This file is RED BY DESIGN; it documents the error.
--
-- Untracked probe; ONE agda process under GHCRTS="-A64m -I0 -M8g";
-- never committed.

open import Base.Prelude
open import Base.Truth
open import Base.Classical using ( LEM )

module ProbeLJ1111B {ℓ : Level} (lem : LEM (ℓ-suc ℓ)) where

import ProbeLJ1107A {ℓ} lem as P107
open P107 using ( module LeastCard; _↪_ )
open import L.Constructible {ℓ} using ( IsOrd )
open import V.Hierarchy {ℓ} using ( 𝒮ᵥ )
open import FOL.ZFStructure using ( module hPropStructure )
open import Cubical.HITs.CumulativeHierarchy.Properties using ( ⟪_⟫ )
import Cubical.HITs.PropositionalTruncation as PT
open PT using ( ∥_∥₁ )
import Cubical.Foundations.Equiv as Eq
open Eq using ( _≃_; invEq; equivFun; secEq )
import Cubical.Data.Empty as Empty

open hPropStructure 𝒮ᵥ

module CheapCure (α : S) (oα : IsOrd α) where

  module LC = LeastCard α oα
  open LC

  -- The extraction that cannot be written:  the first argument of
  -- PT.rec must be a proof of isProp (⟪ α ⟫ ↪ ⟪ κ ⟫), and nothing in
  -- the LeastCard data (in particular κ-min-at) supplies it.  The
  -- checker rejects the attempted proof below.
  attempt : ⟪ α ⟫ ↪ ⟪ κ ⟫
  attempt = PT.rec (λ x y → x ≡ y)
    (λ e → (invEq e , λ x y p → sym (secEq e x) ∙ cong (equivFun e) p ∙ secEq e y))
    κ-eqα
