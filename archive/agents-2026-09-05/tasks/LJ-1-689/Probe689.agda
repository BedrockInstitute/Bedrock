{-# OPTIONS --cubical --safe --guardedness #-}

-- [LJ-1.689] PROBE.  Convert from hull-closed's hypothesis form
-- mapFo val (inBound ca cp), taking [LJ-1.686]'s equation as a
-- HYPOTHESIS.  Lands nothing in src/.
--
--   W3              whether the hull hypothesis form unpacks once
--                   the equation is given
--                   (agents/tasks/LJ-1-682/lj-1.682-report.md:1).
--   THE OBLIGATION  hull-convert.  pin₃-map, then subst along the
--                   leftover equation at pin₃, then convert-generic.
--                   The equation is not formed.  val and slide are
--                   parameters, so the hull telescope does not leak
--                   into this type.
--
-- ONE Agda process per run, GHCRTS="-A64m -I0 -M2g", the wide
-- caliber, set on the pane by the program and untouched here.
-- Nothing is postulated.  No hole.

open import Base.Prelude
open import Base.Truth

module LJ-1-689.Probe689 {ℓ : Level} where

open import FOL.ZFStructure using ( module hPropStructure )
open import FOL.Syntax using ( Formula )
open import FOL.LevyHierarchy using ( Δ₀ )
open import FOL.Manipulation.Relabelling using ( embed; mapFo )
open import V.Hierarchy {ℓ} using ( 𝒮ᵥ )
open import V.Collapse {ℓ} using ( isTrans )
open import Cubical.Data.Vec using ( _∷_; [] )
import LJ-1-680.Probe680 {ℓ} as P680

open hPropStructure 𝒮ᵥ
open P680 using ( pin₃; pin₃-map; _⊨ₚ_ )

-- inBound at a generic formula is pin₃ (mapFo slide φ), which is
-- Probe673.agda:83-87 at a generic alphabet.

module Convert (U : S) (Utr : isTrans U) where
  open P680.Unpack U Utr

  inBound : {ℓc : Level} {K : Type ℓc}
          → Formula (⊥* {ℓ-suc ℓ}) 3
          → (⊥* {ℓ-suc ℓ} → K) → K → K → Formula K 1
  inBound φ slide ca cp = pin₃ (mapFo slide φ) ca cp

  -- W2: written once at a generic carrier.  convert-generic is the
  -- unpack; this is the transport from hull-closed's hypothesis
  -- form onto that unpack.  [LJ-1.686]'s equation is a hypothesis
  -- and is not formed.
  hull-convert :
      {ℓc : Level} {K : Type ℓc}
      {φ : Formula (⊥* {ℓ-suc ℓ}) 3}
    → Δ₀ φ
    → (slide : ⊥* {ℓ-suc ℓ} → K)
    → (val : K → Ab.SM)
    → (eq : mapFo val (mapFo slide φ) ≡ embed φ)
    → (ca cp : K) (a : Ab.SM)
    → ⟨ (a ∷ []) Ab.⊨ᵐ (mapFo val (inBound φ slide ca cp)) ⟩
    → ⟨ (fst (val ca) ∷ fst (val cp) ∷ fst a ∷ []) ⊨ₚ φ ⟩
  hull-convert {φ = φ} dφ slide val eq ca cp a h =
    convert-generic {φ = φ} dφ (val ca) (val cp) a
      (subst (λ ψ → ⟨ (a ∷ []) Ab.⊨ᵐ (pin₃ ψ (val ca) (val cp)) ⟩) eq
        (subst (λ ψ → ⟨ (a ∷ []) Ab.⊨ᵐ ψ ⟩)
               (pin₃-map val (mapFo slide φ) ca cp)
               h))

-- THE OBLIGATION.  Lifted off the carrier module so the witness
-- meter reads Target.hull-convert (scripts/pod/witness.py:278).
hull-convert = Convert.hull-convert
