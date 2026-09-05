{-# OPTIONS --cubical --safe --guardedness #-}

-- [LJ-1.476] W3 first: one member of the bound slot at the
-- [LJ-1.457] frame. Layout from Probe457.agda:52-55 and :74-75,
-- instance from Probe467.agda:83-95. K is lookup iK Kenv, LsetS lam.
-- W3 is Countermodel.witness. The obligation ar-numeral names the
-- type; the body is a hole. The refutation ar-numeral-refute is the
-- return.
--
-- ONE Agda process per run, GHCRTS="-A64m -I0 -M8g", the wide
-- caliber, set on the pane by the program and untouched here.
-- Nothing lands in src/.

open import Base.Prelude
open import Base.Truth
open import Base.Classical using ( LEM )

module LJ-1-476.Probe476 {ℓ : Level} (lem : LEM (ℓ-suc ℓ)) where

open import FOL.ZFStructure using ( module hPropStructure )
open import L.Constructible {ℓ} using ( 𝒮ʟ; IsOrd )
open import L.Axioms.Numerals {ℓ} using ( numeralL; numeralL-fst )
open import L.Coding.Model {ℓ} using ( prʟ; prʟ-fst )
open import L.Condensation {ℓ} lem using ( module KValue; module KFactsNS )
open import L.Ordinal {ℓ} using ( ω-ord; #∈ω; ∅-ord; numeral-ord )
open import V.Coding {ℓ} using ( pr )
open import V.Hierarchy {ℓ} using ( ∈-irrefl )
open import V.Model {ℓ} using ( pair-singleton )
open import Cubical.HITs.CumulativeHierarchy.Base using ( V; _∈_ )
open import Cubical.HITs.CumulativeHierarchy.Properties using ( ∈∈ₛ )
open import Cubical.HITs.CumulativeHierarchy.Constructions
  using ( module InfinitySet; ∅; ⁅_,_⁆; ⁅_⁆s; pairing-ax )
open InfinitySet {ℓ} using ( sucV; ω; ω-next; #_ )
import Cubical.Data.Empty as Empty
import Cubical.Data.Sum as Sum
open Sum using ( _⊎_; inl; inr )
import Cubical.HITs.PropositionalTruncation as PT
open PT using ( ∣_∣₁; ∥_∥₁ )

open TruthAlgebra (hPropAlgebra (ℓ-suc ℓ))
open hPropStructure 𝒮ʟ
open KFactsNS

-- =====================================================================
-- D-10.  K at this frame is LsetS lam.  Members of a constructible
--   level are not all numerals.  W3 exhibits one member.  The
--   obligation ar-numeral is omitted on the W3 runs.
-- =====================================================================

-- Legal instance of the KValue / [LJ-1.457] telescope.
-- lam = ω is successor-closed and contains ∅ ([LJ-1.467] Countermodel).
-- gam = ∅ lies in ω.  Re-measured at this site, not transferred.
module Countermodel where

  ∅∈ω : ⟨ ∅ ∈ ω ⟩
  ∅∈ω = #∈ω 0

  succω : (d : V ℓ) → ⟨ d ∈ ω ⟩ → ⟨ sucV d ∈ ω ⟩
  succω d d∈ω =
    ∈∈ₛ {a = sucV d} {b = ω} .snd
      (ω-next d (∈∈ₛ {a = d} {b = ω} .fst d∈ω))

  module Inst = KValue ω ω-ord succω ∅∈ω ∅ ∅-ord ∅∈ω

  open KFacts Inst.facts

  K : S
  K = lookup Inst.iK Inst.Kenv

  -- W3. One member of the bound slot. pairK of two copies of
  -- numeralL 0, from KValue.facts (Condensation.lagda.md:7423).
  witness : Σ[ ar ∈ S ] ⟨ fst ar ∈ fst K ⟩
  witness = prʟ (numeralL 0) (numeralL 0)
          , pairK (numeralL 0) (numeralL 0) numK0 numK0

  -- Classification of the Kuratowski pair, copied from
  -- Condensation.lagda.md:2827-2844, at a = b = # 0.  pairing-ax
  -- only.  No nested brace goal.
  a0 : V ℓ
  a0 = # 0

  a0∈singl : ⟨ a0 ∈ ⁅ a0 ⁆s ⟩
  a0∈singl = subst (λ w → ⟨ a0 ∈ w ⟩) (pair-singleton a0)
    (∈∈ₛ {a = a0} {b = ⁅ a0 , a0 ⁆} .snd
      (pairing-ax a0 a0 a0 .snd ∣ inl refl ∣₁))

  a0∈pair : ⟨ a0 ∈ ⁅ a0 , a0 ⁆ ⟩
  a0∈pair = ∈∈ₛ {a = a0} {b = ⁅ a0 , a0 ⁆} .snd
    (pairing-ax a0 a0 a0 .snd ∣ inl refl ∣₁)

  singl∈pr00 : ⟨ ⁅ a0 ⁆s ∈ pr a0 a0 ⟩
  singl∈pr00 = ∈∈ₛ {a = ⁅ a0 ⁆s} {b = pr a0 a0} .snd
    (pairing-ax ⁅ a0 ⁆s ⁅ a0 , a0 ⁆ ⁅ a0 ⁆s .snd ∣ inl refl ∣₁)

  -- A Kuratowski pair is not a numeral: # n is an ordinal, so
  -- transitive, so a0 ∈ pr a0 a0, so a0 is a member of the pair,
  -- so a0 equals ⁅ a0 ⁆s or ⁅ a0 , a0 ⁆, so a0 ∈ a0.
  pr00≢# : (n : ℕ) → pr a0 a0 ≡ # n → Empty.⊥
  pr00≢# n e = PT.rec Empty.isProp⊥
    (Sum.rec
      (λ p → ∈-irrefl a0 (subst (λ w → ⟨ a0 ∈ w ⟩) (sym p) a0∈singl))
      (λ p → ∈-irrefl a0 (subst (λ w → ⟨ a0 ∈ w ⟩) (sym p) a0∈pair)))
    classified
    where
    singl∈# : ⟨ ⁅ a0 ⁆s ∈ # n ⟩
    singl∈# = subst (λ w → ⟨ ⁅ a0 ⁆s ∈ w ⟩) e singl∈pr00
    a0∈# : ⟨ a0 ∈ # n ⟩
    a0∈# = numeral-ord n .fst {x = ⁅ a0 ⁆s} {y = a0} a0∈singl singl∈#
    a0∈pr : ⟨ a0 ∈ pr a0 a0 ⟩
    a0∈pr = subst (λ w → ⟨ a0 ∈ w ⟩) (sym e) a0∈#
    classified : ∥ (a0 ≡ ⁅ a0 ⁆s) ⊎ (a0 ≡ ⁅ a0 , a0 ⁆) ∥₁
    classified = pairing-ax ⁅ a0 ⁆s ⁅ a0 , a0 ⁆ a0 .fst
      (∈∈ₛ {a = a0} {b = pr a0 a0} .fst a0∈pr)

  fst-witness≡pr00 : fst (fst witness) ≡ pr a0 a0
  fst-witness≡pr00 =
    prʟ-fst (numeralL 0) (numeralL 0)
    ∙ cong₂ pr (numeralL-fst 0) (numeralL-fst 0)

  -- The refutation at the W3 witness.  Green is the return.
  ar-numeral-refute :
      (∥ Σ[ n ∈ ℕ ] (fst (fst witness) ≡ # n) ∥₁) → Empty.⊥
  ar-numeral-refute = PT.rec Empty.isProp⊥
    (λ { (n , e) → pr00≢# n (sym fst-witness≡pr00 ∙ e) })

-- =====================================================================
-- THE OBLIGATION.  The type is the numeral truncation at K, the bound
-- slot of [LJ-1.457]'s frame, instantiated at the legal KValue
-- instance lam = ω, gam = ∅.  Countermodel.ar-numeral-refute shows
-- the type is empty at the W3 witness.  No body.
-- =====================================================================

ar-numeral :
    (ar : S)
  → ⟨ fst ar ∈ fst Countermodel.K ⟩
  → ∥ Σ[ n ∈ ℕ ] (fst ar ≡ # n) ∥₁
ar-numeral = {!!}
