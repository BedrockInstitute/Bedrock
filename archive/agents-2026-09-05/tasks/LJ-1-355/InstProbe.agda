{-# OPTIONS --cubical --safe --guardedness #-}

-- [LJ-1.355] PROBE.  The corollary instantiated at the trophy's own two
-- injections.  This measures the wiring price an orchestrator pays in
-- src/L/: the readback from the truncated code existential to an honest
-- injection between the small member types, and one module application.
--
-- WHAT THIS FILE DECIDES.  GCHStatement states cardinal equality as
-- InjL (P k) d and InjL d (P k) (src/L/GCH.lagda.md:66-68).  The
-- delivered readback `Small` (src/L/Coding/Injection.lagda.md:103) turns
-- an untruncated InjCode witness into an injective map between the small
-- index types.  This file assembles: InjL a b and InjL b a give a
-- truncated ambient bijection between the small member types of a and b.
-- Exit 0 means the wiring is the measured price below, and no L-side
-- object is missing.

open import Base.Prelude
open import Base.Truth
open import Base.Classical using ( LEM; lowerLEM )

module LJ-1-355.InstProbe {ℓ : Level} (lem : LEM (ℓ-suc ℓ)) where

open import FOL.ZFStructure using ( module hPropStructure )
open import V.Hierarchy {ℓ} using ( 𝒮ᵥ )
open import V.CantorBernstein {ℓ} (lowerLEM lem)
open import L.Constructible {ℓ} using ( 𝒮ʟ )
open import L.Cardinal {ℓ} lem using ( InjCode )
open import L.Coding.Injection {ℓ} lem using ( module Small )
open import L.GCH {ℓ} lem using ( InjL )
open import Cubical.HITs.CumulativeHierarchy.Base using ( V; setIsSet )
open import Cubical.HITs.CumulativeHierarchy.Properties
  using ( ⟪_⟫; ⟪_⟫↪; isEmb⟪_⟫↪ )
open import Cubical.Functions.Embedding using ( Embedding-into-isSet→isSet )
import Cubical.HITs.PropositionalTruncation as PT
open PT using ( ∥_∥₁ )

open hPropStructure 𝒮ʟ using ( S )

-- The carrier-level set-ness, from the master's exported fact.
setPL : (a : S) → isSet (⟪ fst a ⟫)
setPL a = small-set (fst a)

-- The readback, untruncated: an InjCode witness is four satisfaction
-- facts, and `Small` consumes exactly those four.
readL : (a b : S) → Σ[ F ∈ S ] InjCode F a b
      → Σ[ f ∈ (⟪ fst a ⟫ → ⟪ fst b ⟫) ]
          ((x y : ⟪ fst a ⟫) → f x ≡ f y → x ≡ y)
readL a b (F , sv , dm , ij , ran) = SM.small , SM.small-inj
  where
  module SM = Small F a b sv dm ij ran

module MI = MutualInj S (λ a → ⟪ fst a ⟫) (λ a b → Σ[ F ∈ S ] InjCode F a b)
  setPL readL

-- The corollary the set-theorist reading wants, checked by machine:
-- the trophy's two injections give an ambient bijection between the
-- small types.  InjL is definitionally the truncation of the R above,
-- so this is MI.∃bijection read at the trophy's own notion.
csb-corollary : (a b : S) → InjL a b → InjL b a
  → ∥ Σ[ h ∈ (⟪ fst a ⟫ → ⟪ fst b ⟫) ]
       (((x y : ⟪ fst a ⟫) → h x ≡ h y → x ≡ y)
     × ((y : ⟪ fst b ⟫) → ∥ Σ[ x ∈ ⟪ fst a ⟫ ] (h x ≡ y) ∥₁)) ∥₁
csb-corollary = MI.∃bijection
