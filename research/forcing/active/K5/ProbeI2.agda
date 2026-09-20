{-# OPTIONS --cubical --safe --guardedness #-}

-- K5 Track I, PROBE 0 ITEM 2. NOT a deliverable.
--
-- The statement architecture section 6.7 says nobody has measured: the
-- compatibility clause of ForcingBase, whose TYPE nests the sealed meet of
-- K4/InstanceCoded.agda:150 over two applications of K2's embedding. Here the
-- embedding is SEALED as iᴷ in its own block, so the nest is
--
--     sealed-meet (sealed-i p) (sealed-i q)
--
-- and every argument of the nest is neutral. The companion file ProbeI3 is the
-- same statement with the embedding UNSEALED, which is the shape
--
--     sealed-meet (unsealed-description) (unsealed-description)
--
-- that 6.7 names as unmeasured.
--
-- Both directions of the clause are stated, because only one of them is
-- classical and the free one is the one K2 measured three drafts killed on
-- (CodedCompletion.agda:1148-1155).

open import Base.Prelude
open import Base.Truth
open import Base.Classical using ( LEM )
open import FOL.ZFStructure using ( ZFStructure )
import Cubical.HITs.PropositionalTruncation as PT
import OrdinaryProfile
import CodedCompletion
import K4.Algebra
import K4.InstanceCoded

module K5.ProbeI2
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

module CD = CodedCompletion.Coded 𝒮 𝔓
open CD using ( carrier; order; Cond; _≼ᴵ_ )

module IC = K4.InstanceCoded 𝒮 ext pow sep paths 𝔓 laws
module CO = IC.CO
module CL = CodedCompletion.Classical 𝒮 ext pow sep paths 𝔓 laws

open Lattice IC.codedLattice using ( _⊓ᴮ_; ⊓-lb₁; ⊓-lb₂; ⊓-glb )

--------------------------------------------------------------------------------
-- The sixth seal
--------------------------------------------------------------------------------

opaque
  iᴷ : Cond → Pt CO.B
  iᴷ = CO.iᴮ

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

--------------------------------------------------------------------------------
-- The two members of the meet, at VARIABLES
--------------------------------------------------------------------------------

-- Rule 3's remedy in the only form that works here: the two projections of
-- the meet are read off the lattice's own universal property, so nothing in
-- this file ever opens the meet's seal. K2's meet-split (:1154) is a
-- membership statement about the coded meet; ⊓-lb₁ and ⊓-lb₂ say the same
-- thing at any lattice, because ⟨ u ≤ᴮ v ⟩ IS ⟨ fst u ⊆ˢ fst v ⟩.

meetᴷ-split : (u v : Pt CO.B) (z : S) → ⟨ z ∈ˢ fst (u ⊓ᴮ v) ⟩
            → ⟨ (z ∈ˢ fst u) ⊓ (z ∈ˢ fst v) ⟩
meetᴷ-split u v z hz = ⊓-lb₁ u v z hz , ⊓-lb₂ u v z hz

--------------------------------------------------------------------------------
-- ITEM 2: the clause at the sealed embedding
--------------------------------------------------------------------------------

-- The free direction. No seal is opened: iᴷ-mono and iᴷ-self carry everything
-- across, and the contradiction is taken at the bottom's own emptiness rather
-- than through antisymmetry, so neither ext nor paths is spent here.

i-compat→K : (p q : Cond) → ⟨ CO.compatibleᴵ (fst p) (fst q) ⟩
           → ((iᴷ p ⊓ᴮ iᴷ q) ≡ CO.⊥ᴮ) → ⟨ ⊥ ⟩
i-compat→K p q hc eq = PT.rec (snd ⊥) go hc
  where
    go : Σ[ r ∈ S ] ⟨ (r ∈ˢ carrier) ⊓ ((r ≼ᴵ fst p) ⊓ (r ≼ᴵ fst q)) ⟩ → ⟨ ⊥ ⟩
    go (r , hr , hrp , hrq) =
      CO.⊥ᴮ-empty r
        (subst (λ w → ⟨ iᴷ (r , hr) ≤ᴮ w ⟩) eq
          (⊓-glb (iᴷ p) (iᴷ q) (iᴷ (r , hr))
            (iᴷ-mono p (r , hr) hrp) (iᴷ-mono q (r , hr) hrq))
          r (iᴷ-self (r , hr)))

-- The classical direction. LEM ℓ is an explicit FIRST argument, ledger clause
-- L1. The composite is abstracted into m only at the CALL, which is K2's own
-- i-compat←-at pattern (:1359); the statement itself is AT the composite,
-- which is the thing K4's instance track found unreachable unsealed.

i-compat←K : LEM ℓ → (p q : Cond)
           → (((iᴷ p ⊓ᴮ iᴷ q) ≡ CO.⊥ᴮ) → ⟨ ⊥ ⟩)
           → ⟨ CO.compatibleᴵ (fst p) (fst q) ⟩
i-compat←K lem p q nz =
  CO.compat-transfer← p q
    (CL.i-compat←-at lem p q (iᴷ p ⊓ᴮ iᴷ q) split
      (CL.nonzero→positive lem (iᴷ p ⊓ᴮ iᴷ q) nz))
  where
    split : (z : S) → ⟨ z ∈ˢ fst (iᴷ p ⊓ᴮ iᴷ q) ⟩
          → ⟨ (z ∈ˢ CO.iSet (fst p)) ⊓ (z ∈ˢ CO.iSet (fst q)) ⟩
    split z hz =
        subst (λ w → ⟨ z ∈ˢ w ⟩) (iᴷ-code p) (meetᴷ-split (iᴷ p) (iᴷ q) z hz .fst)
      , subst (λ w → ⟨ z ∈ˢ w ⟩) (iᴷ-code q) (meetᴷ-split (iᴷ p) (iᴷ q) z hz .snd)
