{-# OPTIONS --cubical --safe --guardedness #-}

-- K5 Track I, PROBE 0 scaffold. NOT a deliverable.
--
-- What this file measures. Two things, before either of the two nesting
-- probes is run, so that a negative in those probes is attributable to the
-- nesting and not to the scaffold.
--
--   1. That the coded completion can be reached through K4's instance file
--      rather than by a second application of CodedCompletion.Core. K4 writes
--      `module CO = CodedCompletion.Core ...` inside K4/InstanceCoded.agda:112,
--      so a consumer that applies K4.InstanceCoded once gets BOTH the sealed
--      lattice and the whole Core surface out of ONE heavy module application.
--      That is preamble rule 10 obeyed by construction rather than by care.
--   2. The cost of that one application, which is the budget every Track I
--      file is measured against.
--
-- The sixth seal is declared here too, in its OWN opaque block, and its
-- specification is the only thing proved inside the seal. Preamble rule 2b:
-- K2 contains no seal at all, so iᴮ is an unsealed description-operator term
-- (iSet p = separateOf sep carrier (coneφ p), CodedCompletion.agda:559-560),
-- and every nest that mentions it twice meets the third threshold.

open import Base.Prelude
open import Base.Truth
open import FOL.ZFStructure using ( ZFStructure )
import OrdinaryProfile
import CodedCompletion
import K4.Algebra
import K4.InstanceCoded

module K5.ProbeI1
  {ℓ} (𝒮 : ZFStructure (hPropAlgebra ℓ))
  (ext   : OrdinaryProfile.Extensionality 𝒮)
  (pow   : OrdinaryProfile.PowerSet 𝒮)
  (sep   : OrdinaryProfile.Separation 𝒮)
  (paths : (x y : ZFStructure.S 𝒮)
         → (ZFStructure._≈ˢ_ 𝒮 x y) ≡ ((x ≡ y) , ZFStructure.isSetS 𝒮 x y))
  (𝔓     : CodedCompletion.Presentation 𝒮)
  (laws  : CodedCompletion.Coded.ForcingLaws 𝒮 𝔓)
  where

open import FOL.ZFStructure using ( module hPropStructure )
open import FOL.ZFModel 𝒮 using ( _⊆ˢ_ )

open TruthAlgebra (hPropAlgebra ℓ)
open hPropStructure 𝒮

open K4.Algebra 𝒮 using ( Pt; _≤ᴮ_; Lattice; Complement; CodedComplete )

-- The light application: the presentation layer, which carries carrier,
-- order, Cond and the order vocabulary. CodedCompletion.agda:210-224.

module CD = CodedCompletion.Coded 𝒮 𝔓
open CD using ( carrier; order; Cond; _≼ᴵ_ )

-- The ONE heavy application, and the Core surface taken out of it.

module IC = K4.InstanceCoded 𝒮 ext pow sep paths 𝔓 laws
module CO = IC.CO

--------------------------------------------------------------------------------
-- The sixth seal
--------------------------------------------------------------------------------

-- K4 sealed five coded operations in five separate blocks
-- (K4/InstanceCoded.agda:144-168) and touched iᴮ nowhere. This is the sixth,
-- in its own block for the reason K4 records at :141-144: one block holding
-- all six would be useless, because opening it to unfold the embedding would
-- also unfold the meet and the nest would be transparent again.

opaque
  iᴷ : Cond → Pt CO.B
  iᴷ = CO.iᴮ

-- The specification, and the three pointwise facts, all at DEPTH ONE in the
-- seal. Everything a later proof needs about iᴷ is proved here, so that no
-- later proof has to open this seal.

opaque
  unfolding iᴷ

  iᴷ-code : (p : Cond) → fst (iᴷ p) ≡ CO.iSet (fst p)
  iᴷ-code p = refl

  iᴷ-self : (p : Cond) → ⟨ fst p ∈ˢ fst (iᴷ p) ⟩
  iᴷ-self = CO.i-self

  iᴷ-mono : (p q : Cond) → ⟨ fst q ≼ᴵ fst p ⟩ → ⟨ iᴷ q ≤ᴮ iᴷ p ⟩
  iᴷ-mono = CO.i-mono

  iᴷ-nonzero : (p : Cond) → (iᴷ p ≡ CO.⊥ᴮ) → ⟨ ⊥ ⟩
  iᴷ-nonzero p = CO.positive→nonzero (iᴷ p) (CO.i-pos p)
