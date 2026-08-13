{-# OPTIONS --cubical --safe --guardedness #-}

-- DD25 review probe H2: THE EXIT THE RETURN NAMED AND DID NOT BUILD.
--
-- The return says the exit is "a restatement of the connector's
-- obligation on the delivered `EraseTransfer` route
-- (src/L/Condensation.lagda.md:273-306), which never runs erase-Δ₀ at
-- all", and calls it "a design decision ... not measured here".
--
-- This probe BUILDS it, at the SAME leaf the 150 s control measures:
-- the `DefBodyB` leaf at n = 0, all sixteen slots at zero.
--
-- The delivered `RowTransfer` (:1772-1783) is the same instantiation
-- at the twelve rows, and it is green in the tree.  This probe applies
-- that template to the leaf.  Nothing here calls `erase-Δ₀`.

open import Base.Prelude
open import Base.Truth
open import Base.Classical using ( LEM )

module ProbeDD25H2 {ℓ : Level} (lem : LEM (ℓ-suc ℓ)) where

open import FOL.ZFStructure using ( module hPropStructure )
open import V.Hierarchy {ℓ} using ( 𝒮ᵥ )
open import FOL.Syntax using ( Formula )
open import FOL.LevyHierarchy using ( Δ₀ )
open import FOL.Manipulation.Parameters using ( countFo )
import FOL.Absoluteness
open import L.Constructible {ℓ} using ( 𝒮ʟ; isL; isL-trans )
open import L.Condensation {ℓ} lem using
  ( DefBodyB; Δ₀-DefBodyB; module EraseTransfer )
open import Cubical.Data.Vec using ( map )

open hPropStructure 𝒮ʟ

module AbsL = FOL.Absoluteness.Single 𝒮ᵥ isL isL-trans
open AbsL renaming ( _⊨ᵐ_ to _⊨_ )

-- The leaf at n = 0, arity 8, all sixteen slots at zero.  Same object
-- as ProbeLJ150Control :28-36 and ProbeDD25H1 :42-50.
defb : Formula S 8
defb = DefBodyB {0}
  zero zero zero zero zero zero zero zero
  zero zero zero zero zero zero zero zero

Δ₀-defb : Δ₀ defb
Δ₀-defb = Δ₀-DefBodyB {0}
  zero zero zero zero zero zero zero zero
  zero zero zero zero zero zero zero zero

count-defb : countFo defb ≡ 0
count-defb = refl

-- THE EXIT.  The delivered `RowTransfer` shape (:1772-1783), at the
-- leaf instead of at a row.  Every field is named and typed, so
-- nothing is left unforced.
module LeafTransfer (γ : S ^ 8) where
  module E = EraseTransfer defb count-defb Δ₀-defb γ

  σL : Formula S 8
  σL = E.σL

  σL≡ : σL ≡ defb
  σL≡ = E.σL≡

  σL-eq : ⟨ γ ⊨ defb ⟩ ≡ ⟨ γ ⊨ σL ⟩
  σL-eq = E.σL-eq

  σL-transfer : ⟨ γ ⊨ σL ⟩ ≡ ⟨ map fst γ ⊨ᵛ σL ⟩
  σL-transfer = E.σL-transfer

  σL-up : ⟨ γ ⊨ σL ⟩ → ⟨ map fst γ ⊨ᵛ σL ⟩
  σL-up = E.σL-up
