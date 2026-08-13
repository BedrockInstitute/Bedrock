{-# OPTIONS --cubical --safe --guardedness #-}

-- [LJ-1.156] Probe B.  THE CONTROL FOR PROBE A.
--
-- Probe A's import block, exactly, with NO body.  The difference B to A
-- is the chain and nothing else.
--
-- ABORT CRITERION: none.  This is a control, not a decision.
--
-- Tracked probe; ONE agda process under GHCRTS="-A64m -I0 -M8g";
-- never committed to src/.

open import Base.Prelude
open import Base.Truth
open import Base.Classical using ( LEM )

module LJ-1-156.ProbeLJ1156B {ℓ : Level} (lem : LEM (ℓ-suc ℓ)) where

import L.Ordinal.SquareLaw {ℓ} lem as SQ
open SQ using ( module FiniteBase; ordSWO )
import L.Ordinal {ℓ} as Ord
open Ord using ( mem-ord; suc-ord; ω-ord; #∈ω )
open import L.Constructible {ℓ} using ( IsOrd )
import L.Ordinal.Linear {ℓ} lem as Lin
open Lin using ( ord-tri )
import FOL.Count {ℓ} as Count
import L.Choice.Finite {ℓ} lem as LF
open LF using ( natOrder )
import V.Hierarchy {ℓ} as Hier
open Hier using ( 𝒮ᵥ; ∈-irrefl; ∈-induction )
import V.Model {ℓ} as VModel
open VModel using ( ∈sucV-elim; ∈sucV-inl; self∈sucV )
import V.Presentation {ℓ} as VPres
open VPres using ( member; fiber; ↪-inj )
import V.Coding {ℓ} as VCoding
open VCoding using ( #-inj′ )
import FOL.ZFStructure as ZF
open ZF using ( module hPropStructure )
import Cubical.HITs.CumulativeHierarchy.Base as CHB
open CHB using ( setIsSet )
import Cubical.HITs.CumulativeHierarchy.Properties as CH
open CH using ( ∈∈ₛ; ⟪_⟫; ⟪_⟫↪; isEmb⟪_⟫↪; ∈ₛ⟪_⟫↪_ )
import Cubical.HITs.CumulativeHierarchy.Constructions as CHC
open CHC using ( module InfinitySet )
open InfinitySet {ℓ} using ( ω; sucV; #_ )
import Cubical.Functions.Embedding as Emb
open Emb using ( isEmbedding→hasPropFibers; Embedding-into-isSet→isSet )
import Cubical.Data.Sigma as Sig
open Sig using ( ΣPathP; Σ≡Prop )
import L.WellOrder.Base {ℓₚ = ℓ-suc ℓ} as WOBase
open WOBase using ( SWO; IsLeast; leastOf; module SWO )
import Cubical.Data.Nat as Nat
open Nat using ( ℕ; zero; suc )
import Cubical.Data.Nat.Properties as NatProp
open NatProp using ( injSuc; znots; snotz )
import Cubical.Data.Sum as Sum
open Sum using ( _⊎_; inl; inr )
import Cubical.Data.Sum.Properties as SumProp
open SumProp using ( isProp⊎ )
import Cubical.Data.Empty as Empty
import Cubical.HITs.PropositionalTruncation as PT
open PT using ( ∣_∣₁; ∥_∥₁; squash₁ )

open hPropStructure 𝒮ᵥ
