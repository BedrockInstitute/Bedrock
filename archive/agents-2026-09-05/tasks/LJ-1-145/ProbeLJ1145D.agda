{-# OPTIONS --cubical --safe --guardedness #-}

-- LJ-1.145, probe D.  THE CURE TEST.
--
-- Probe C isolated the master's term.  Splitting `⟨ γ ⊨ DefBody w ⟩`
-- and rebuilding it costs 12 ms.  Applying the supplier to a variable
-- of the supplier's own stated type costs 15 ms.  Taking the component
-- OUT of the split and naming its folded type costs 2,526 ms, and that
-- one coercion is 65 percent of `LeafAgree.out`.
--
-- The mechanism, INFERRED: a pattern split reduces the satisfaction
-- type, so the component arrives UNFOLDED, and the consumer's signature
-- names it FOLDED.  The heads differ, so the conversion checker walks
-- the whole formula tree.  When both sides are the same term it takes
-- the syntactic short cut instead.
--
-- If that is right, sealing the machine formula fixes it: a sealed head
-- cannot unfold, so both sides stay folded and the conversion is
-- syntactic.  P-t licenses exactly this move.
--
-- This probe builds `DefBody`'s own shape twice, once with the machine's
-- `satGraphAt` open and once with it sealed, and coerces the middle
-- component out of each.  Read with `agda --profile=definitions`.

open import Base.Prelude
open import Base.Truth
open import Base.Classical using ( LEM )

module LJ-1-145.ProbeLJ1145D {ℓ : Level} (lem : LEM (ℓ-suc ℓ)) where

open import FOL.ZFStructure using ( module hPropStructure )
open import FOL.Syntax using ( Formula; _∧̇_ )
import FOL.Absoluteness
open import V.Hierarchy {ℓ} using ( 𝒮ᵥ )
open import L.Constructible {ℓ} using ( 𝒮ʟ; isL; isL-trans )
open import L.Coding.Graph {ℓ} lem using ( satGraphAt )
open import L.Coding.Powerset {ℓ} lem using ( isCodeAt; DefinesAt )
open import Cubical.Data.Nat using ( _+_ )

open TruthAlgebra (hPropAlgebra (ℓ-suc ℓ))
open hPropStructure 𝒮ʟ

module AbsL = FOL.Absoluteness.Single 𝒮ᵥ isL isL-trans
open AbsL renaming ( _⊨ᵐ_ to _⊨_ )

-- The sealed machine formula.  Nothing but `satGraphAt` behind a seal.
opaque
  sgSealed : ∀ {m} → Fin m → Fin m → Fin m → Formula S m
  sgSealed B x y = satGraphAt B x y

-- `DefBody`'s own shape, written twice.  `bodyOpen` is the control and
-- reproduces `src/L/Coding/Powerset.lagda.md:437-440` exactly.
bodyOpen : ∀ {m} → Fin m → Formula S (suc (suc (suc m)))
bodyOpen w = isCodeAt (suc zero) (suc (suc (suc w)))
           ∧̇ ( satGraphAt (suc (suc (suc w))) (suc zero) zero
             ∧̇ DefinesAt (suc (suc zero)) (suc (suc (suc w))) zero )

bodySealed : ∀ {m} → Fin m → Formula S (suc (suc (suc m)))
bodySealed w = isCodeAt (suc zero) (suc (suc (suc w)))
             ∧̇ ( sgSealed (suc (suc (suc w))) (suc zero) zero
               ∧̇ DefinesAt (suc (suc zero)) (suc (suc (suc w))) zero )

module Site {n : ℕ} (w : Fin (5 + n)) (γ : S ^ (8 + n)) where

  -- CONTROL: today's shape.  Expect probe C's 2,526 ms.
  midOpen : ⟨ γ ⊨ bodyOpen {5 + n} w ⟩
          → ⟨ γ ⊨ satGraphAt (suc (suc (suc w))) (suc zero) zero ⟩
  midOpen (_ , (h , _)) = h

  -- THE CURE: the identical coercion with the machine formula sealed.
  midSealed : ⟨ γ ⊨ bodySealed {5 + n} w ⟩
            → ⟨ γ ⊨ sgSealed (suc (suc (suc w))) (suc zero) zero ⟩
  midSealed (_ , (h , _)) = h

  -- The floor: split and rebuild, both sides the same term.
  ctrlOpen : ⟨ γ ⊨ bodyOpen {5 + n} w ⟩ → ⟨ γ ⊨ bodyOpen {5 + n} w ⟩
  ctrlOpen (a , (b , c)) = (a , (b , c))
