-- LJ-1.145, probe A.  ONE question: what does a SEAL buy on a built
-- object-language formula that stands in a TYPE?
--
-- The master's dominant term is `Typing.CheckLHS` + `Typing.CheckRHS`
-- (54 percent of 122.5 s), and 56 percent of the master's named
-- definition time sits in definitions called `out` or `back`, whose
-- bodies are three to five lines.  So the cost is the TYPE, not the
-- proof.  This probe reproduces that site at the master's own scale
-- and measures four spellings of the same statement.
--
-- Read with `agda --profile=definitions`: each name below is billed
-- separately, so ONE cold run prices all four.

{-# OPTIONS --cubical --safe --guardedness #-}

open import Base.Prelude
open import Base.Truth
open import Base.Classical using ( LEM )

module LJ-1-145.ProbeLJ1145A {ℓ : Level} (lem : LEM (ℓ-suc ℓ)) where

open import FOL.ZFStructure using ( module hPropStructure )
open import FOL.Syntax using ( Formula )
import FOL.Absoluteness
open import V.Hierarchy {ℓ} using ( 𝒮ᵥ )
open import L.Constructible {ℓ} using ( 𝒮ʟ; isL; isL-trans )
open import L.Condensation {ℓ} lem using ( DefBodyB )
open import L.Coding.Powerset {ℓ} lem using ( DefBody )
open import Cubical.Data.Nat using ( _+_ )

open TruthAlgebra (hPropAlgebra (ℓ-suc ℓ))
open hPropStructure 𝒮ʟ

module AbsL = FOL.Absoluteness.Single 𝒮ᵥ isL isL-trans
open AbsL renaming ( _⊨ᵐ_ to _⊨_ )

-- The sealed alias.  Nothing but a name for the same formula.
opaque
  bodyS : {n : ℕ} (w K N0 N1 N2 N3 N4 N5 N6 N7 N8 N9 N10 N11 t0 t1 : Fin (5 + n))
        → Formula S (8 + n)
  bodyS w K N0 N1 N2 N3 N4 N5 N6 N7 N8 N9 N10 N11 t0 t1 =
    DefBodyB w K N0 N1 N2 N3 N4 N5 N6 N7 N8 N9 N10 N11 t0 t1

module Site {n : ℕ} (w K N0 N1 N2 N3 N4 N5 N6 N7 N8 N9 N10 N11 t0 t1 : Fin (5 + n))
            (γ : S ^ (8 + n)) where

  -- (1) TRANSPARENT, no pattern.  Type elaboration only.
  sigT : ⟨ γ ⊨ DefBodyB w K N0 N1 N2 N3 N4 N5 N6 N7 N8 N9 N10 N11 t0 t1 ⟩
       → ⟨ γ ⊨ DefBodyB w K N0 N1 N2 N3 N4 N5 N6 N7 N8 N9 N10 N11 t0 t1 ⟩
  sigT x = x

  -- (2) SEALED, no pattern.  The same statement, one name in the way.
  sigS : ⟨ γ ⊨ bodyS w K N0 N1 N2 N3 N4 N5 N6 N7 N8 N9 N10 N11 t0 t1 ⟩
       → ⟨ γ ⊨ bodyS w K N0 N1 N2 N3 N4 N5 N6 N7 N8 N9 N10 N11 t0 t1 ⟩
  sigS x = x

  -- (3) TRANSPARENT, WITH the pattern the master's `out` and `back`
  -- write.  This is today's shape.
  patT : ⟨ γ ⊨ DefBodyB w K N0 N1 N2 N3 N4 N5 N6 N7 N8 N9 N10 N11 t0 t1 ⟩
       → ⟨ γ ⊨ DefBodyB w K N0 N1 N2 N3 N4 N5 N6 N7 N8 N9 N10 N11 t0 t1 ⟩
  patT (a , (b , c)) = (a , (b , c))

  -- (5) THE MACHINE SIDE.  `LeafAgree.out` takes `⟨ γ ⊨ DefBody w ⟩` on
  -- the left.  `DefBody` is the imported machine formula, not the
  -- master's built one.  Same two spellings.
  sigM : ⟨ γ ⊨ DefBody {5 + n} w ⟩ → ⟨ γ ⊨ DefBody {5 + n} w ⟩
  sigM x = x

  patM : ⟨ γ ⊨ DefBody {5 + n} w ⟩ → ⟨ γ ⊨ DefBody {5 + n} w ⟩
  patM (a , (b , c)) = (a , (b , c))

  -- (6) THE CROSS TYPE, elaborated and never proved.  This is exactly
  -- `LeafAgree.out`'s signature.  If the signature is what costs, this
  -- one definition carries it.
  Cross : Type (ℓ-suc ℓ)
  Cross = ⟨ γ ⊨ DefBody {5 + n} w ⟩
        → ⟨ γ ⊨ DefBodyB w K N0 N1 N2 N3 N4 N5 N6 N7 N8 N9 N10 N11 t0 t1 ⟩

-- (4) SEALED, with the pattern, inside the one block that unfolds.
-- This is the CURE's shape: the signature is sealed everywhere and
-- exactly one block pays the unfolding.
module SiteU {n : ℕ} (w K N0 N1 N2 N3 N4 N5 N6 N7 N8 N9 N10 N11 t0 t1 : Fin (5 + n))
             (γ : S ^ (8 + n)) where

  opaque
    unfolding bodyS

    patU : ⟨ γ ⊨ bodyS w K N0 N1 N2 N3 N4 N5 N6 N7 N8 N9 N10 N11 t0 t1 ⟩
         → ⟨ γ ⊨ bodyS w K N0 N1 N2 N3 N4 N5 N6 N7 N8 N9 N10 N11 t0 t1 ⟩
    patU (a , (b , c)) = (a , (b , c))
