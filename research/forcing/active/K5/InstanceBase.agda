{-# OPTIONS --cubical --safe --guardedness #-}

-- K5 Track I, file 1 of 2: THE FORCING FRAME AT THE CODED COMPLETION.
--
-- What this file is. Tracks A to H state every K5 theorem over an abstract
-- ForcingBase (K5/Frame.agda:148) and never apply CodedCompletion.Core; that
-- is ledger clause L2 and it is what keeps the abstract layer immune to the
-- elaboration thresholds recorded below. This file is the other half of that
-- bargain: it APPLIES the completion and builds the record, so that the
-- abstract layer is a theory about something rather than a theory about
-- nothing. Everything K5 proves abstractly holds at the coded completion of
-- an arbitrary presentation the moment excluded middle is supplied at ℓ.
--
-- THE ONE HEAVY MODULE APPLICATION, and how the Core surface is reached
-- without a second one. K4/InstanceCoded.agda:112 writes
-- `module CO = CodedCompletion.Core 𝒮 ext pow sep paths 𝔓 laws` INSIDE the
-- instance module, so a consumer that applies K4.InstanceCoded once gets both
-- the sealed lattice and the whole Core surface out of that single
-- application. Preamble rule 10 is therefore obeyed by construction. The
-- second application in the file is CodedCompletion.Classical, which supplies
-- exactly two lemmas and is measured beside the first in REPORT-I.
--
-- THE SIXTH SEAL, and why it is in its own block. Preamble rule 2b: a
-- declaration whose type nests two operations of an UNSEALED coded algebra
-- does not elaborate, and rule 3's remedy does not reach it because what
-- fails is supplying the composite as an argument. K4 sealed five coded
-- operations in five separate blocks (K4/InstanceCoded.agda:144-168) and
-- touched the embedding nowhere (its own note at :32). K2 contains no seal at
-- all: iᴮ is iSet (fst p) with iSet p = separateOf sep carrier (coneφ p)
-- (CodedCompletion.agda:559-560, :579-580), a description-operator term over
-- GroundDescription.agda's `the`. The compatibility clause of ForcingBase
-- mentions the meet of two such terms, so the sixth seal below is what stands
-- between this file and that threshold. It is in its OWN block, on K4's
-- recorded reason (:141-144): one block holding all six would be useless,
-- because opening it to unfold the embedding would also unfold the meet.
--
-- No proof below opens more than one seal, and the four declarations that
-- open the embedding's seal are each at DEPTH ONE in it. Every other proof in
-- the file reads the embedding only through those four.
--
-- MEASURED, and this is a correction to architecture section 6.7, which says
-- the shape `sealed-meet (unsealed-description) (unsealed-description)` has
-- never been measured. It has now. See REPORT-I section 2 for the ladder and
-- for what it does and does not license.
--
-- HYPOTHESES, the whole list: the structure, Extensionality, PowerSet,
-- Separation, the path realization, a Presentation and its forcing laws.
-- That is CodedCompletion.Core's telescope verbatim (CodedCompletion.agda:
-- 256-263) and nothing is added. Excluded middle is NOT a parameter of this
-- module: LEM ℓ is an explicit first argument of the three declarations that
-- spend it and of nothing else, which is ledger clause L1 and K2's own
-- pattern (CodedCompletion.agda:1275-1283).
--
-- WHAT THIS FILE DOES NOT CLAIM. It does not claim that any Presentation
-- exists: `grep -rn ": Presentation"` over this compile root finds the type
-- and no inhabitant, which is obstruction O4 and is K8's. It makes no
-- genericity claim on the Boolean side, which is O6. It touches no host
-- value, which is O2. It ships no L instance, which is O1 and L8.

open import Base.Prelude
open import Base.Truth
open import Base.Classical using ( LEM )
open import FOL.ZFStructure using ( ZFStructure )
import Cubical.HITs.PropositionalTruncation as PT
import OrdinaryProfile
import CodedVocabulary
import CodedCompletion
import K4.Algebra
import K4.InstanceCoded
import K5.Frame
import K5.Dense

module K5.InstanceBase
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

-- The record TYPE names come from K4.Algebra and never from a module that
-- re-exports them, which is K4/Implication.agda:64-76's scope contract and
-- K5/Frame.agda's too. CodedCompletion.Core declares a second _≤ᴮ_ with the
-- same body (:488-489 against K4/Algebra.agda:76-77); this file never opens
-- Core, so the ambiguity the architecture's section 1.1 ruling guards against
-- cannot arise here at all, and the `hiding` clause it prescribes is not
-- needed.

open K4.Algebra 𝒮 using ( Pt; _≤ᴮ_; Lattice; Complement; CodedComplete )
open CodedVocabulary 𝒮 using ( coneΔ )

-- The light application: the presentation layer, which carries carrier,
-- order, Cond and the order vocabulary (CodedCompletion.agda:210-224).

module CD = CodedCompletion.Coded 𝒮 𝔓
open CD using ( carrier; order; Cond; _≼ᴵ_ )

-- The heavy one, and the Core surface taken out of it.

module IC = K4.InstanceCoded 𝒮 ext pow sep paths 𝔓 laws
module CO = IC.CO

-- The classical two: nonzero→positive (:1314) and i-compat←-at (:1359).
-- Nothing else of this module is named anywhere below.

module CL = CodedCompletion.Classical 𝒮 ext pow sep paths 𝔓 laws

-- Track A's record, at this presentation's two codes.

module P = K5.Frame.Poset 𝒮 carrier order

open Lattice IC.codedLattice using ( _⊓ᴮ_; ⊓-lb₁; ⊓-lb₂; ⊓-glb )

--------------------------------------------------------------------------------
-- The sixth seal
--------------------------------------------------------------------------------

opaque
  iᴷ : Cond → Pt CO.B
  iᴷ = CO.iᴮ

-- Everything a later proof needs about the embedding, proved here at depth
-- one, so that no later proof has to open this seal. K2's names, restated:
-- i-self at :588, i-mono at :594, i-pos at :591 with positive→nonzero at
-- :1130. The first is the specification and is the one the compatibility
-- clause consumes.

opaque
  unfolding iᴷ

  -- The seal's specification, in the form preamble rule 2 prescribes: sealed
  -- together with the thing it names, in the same block, so that a consumer
  -- never has to open the seal to know what iᴷ is. The second is the form the
  -- compatibility clause below consumes, and it is the one that keeps that
  -- clause's proof outside this block.

  iᴷ-spec : (p : Cond) → iᴷ p ≡ CO.iᴮ p
  iᴷ-spec p = refl

  iᴷ-code : (p : Cond) → fst (iᴷ p) ≡ CO.iSet (fst p)
  iᴷ-code p = refl

  iᴷ-self : (p : Cond) → ⟨ fst p ∈ˢ fst (iᴷ p) ⟩
  iᴷ-self = CO.i-self

  iᴷ-mono : (p q : Cond) → ⟨ fst q ≼ᴵ fst p ⟩ → ⟨ iᴷ q ≤ᴮ iᴷ p ⟩
  iᴷ-mono = CO.i-mono

  iᴷ-nonzero : (p : Cond) → (iᴷ p ≡ CO.⊥ᴮ) → ⟨ ⊥ ⟩
  iᴷ-nonzero p = CO.positive→nonzero (iᴷ p) (CO.i-pos p)

  -- Density of the image, at NONZERO rather than at K2's inhabited. The one
  -- conversion is nonzero→positive, and it is where this field's LEM ℓ is
  -- actually spent; K2 isolates that and says so at :1312-1313.

  iᴷ-dense : LEM ℓ → (b : Pt CO.B) → ((b ≡ CO.⊥ᴮ) → ⟨ ⊥ ⟩)
           → ⟨ ⋁ Cond (λ p → iᴷ p ≤ᴮ b) ⟩
  iᴷ-dense lem b nz = CO.i-dense b (CL.nonzero→positive lem b nz)

  -- The backward half of the adjunction. This is the `where`-bound `below`
  -- inside K2's i-dense (CodedCompletion.agda:615-630) lifted to a standalone
  -- lemma and stated at the seal. A regular open is downward closed, so the
  -- cone of one of its members is inside it, and the regularization is
  -- monotone. No Separation is spent: K5/ProbeD1.agda measured that at exit 0
  -- and REPORT-A section 2 records it.

  belowᴷ-out : (b : Pt CO.B) (p : Cond) → ⟨ fst p ∈ˢ fst b ⟩ → ⟨ iᴷ p ≤ᴮ b ⟩
  belowᴷ-out b p hp y hy =
    CO.B-regular (fst b) (snd b) .fst y yc
      (CO.star²-mono (CO.cone (fst p)) (CO.mem (fst b)) sub y yc (w .snd))
    where
      sub : CO._⊑_ (CO.cone (fst p)) (CO.mem (fst b))
      sub z hz k = CO.B-down (fst b) (snd b) z (fst p) hz (snd p) k hp
      w : ⟨ (y ∈ˢ carrier) ⊓ coneΔ carrier order (fst p) y ⟩
      w = subst ⟨_⟩ (CO.iSet-mem (fst p) y) hy
      yc : ⟨ y ∈ˢ carrier ⟩
      yc = w .fst

--------------------------------------------------------------------------------
-- The two members of the meet, and no seal opened to get them
--------------------------------------------------------------------------------

-- K2 states its pointwise unpacking of the coded meet as meet-split (:1154)
-- and warns in the same comment that the statement must never be written at
-- the composite. It need not be written at all here: ⟨ u ≤ᴮ v ⟩ IS
-- ⟨ fst u ⊆ˢ fst v ⟩ (K4/Algebra.agda:76-77), so the lattice's own two lower
-- bounds ALREADY say that a member of the meet's code is a member of both.
-- The meet's seal is therefore never opened in this file, and K4's five
-- blocks stay shut.

meetᴷ-split : (u v : Pt CO.B) (z : S) → ⟨ z ∈ˢ fst (u ⊓ᴮ v) ⟩
            → ⟨ (z ∈ˢ fst u) ⊓ (z ∈ˢ fst v) ⟩
meetᴷ-split u v z hz = ⊓-lb₁ u v z hz , ⊓-lb₂ u v z hz

--------------------------------------------------------------------------------
-- The compatibility clause, in both directions
--------------------------------------------------------------------------------

-- THE FREE DIRECTION, and it is free for a reason the architecture's table
-- does not give. Section 1.2 routes it through K2's i-compat→-at (:1171) with
-- meet-join (:1162), which needs the meet's membership specification and so
-- needs the meet's seal opened. It does not: compatibility hands over a
-- common refinement r, i-mono puts its image under both, ⊓-glb puts it under
-- the meet, and a meet equal to the bottom would then make r a member of the
-- empty code. Three lattice laws and no coded membership fact at all. Neither
-- Extensionality nor the path realization is spent, so no antisymmetry is
-- used either.

i-compat→K : (p q : Cond) → ⟨ P.compatᶜ p q ⟩
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

-- THE PAID DIRECTION. This is the declaration the whole seal exists for: its
-- type is at the composite, which is what K2 could not write (:1148-1155,
-- three drafts killed at 19, 11 and 11 minutes near 1.15 GB) and what K4's
-- instance track met from the other side. K2's own remedy is used at the
-- CALL, where the composite is handed to i-compat←-at as the variable m; the
-- statement stays at the composite because a ForcingBase field is exactly
-- that statement and there is no caller left to push it to.
--
-- The two transfers are the ones REPORT-A's correction A-6 names, and the
-- pairing is fixed here: i-compat←-at delivers HOST compatibility
-- (ForcingNotion.agda:104-105) and compat-transfer← (:1027) brings it back to
-- the coded compatibleΔ that P.compatᶜ is.

i-compat←K : LEM ℓ → (p q : Cond)
           → (((iᴷ p ⊓ᴮ iᴷ q) ≡ CO.⊥ᴮ) → ⟨ ⊥ ⟩)
           → ⟨ P.compatᶜ p q ⟩
i-compat←K lem p q nz =
  CO.compat-transfer← p q
    (CL.i-compat←-at lem p q (iᴷ p ⊓ᴮ iᴷ q) split
      (CL.nonzero→positive lem (iᴷ p ⊓ᴮ iᴷ q) nz))
  where
    split : (z : S) → ⟨ z ∈ˢ fst (iᴷ p ⊓ᴮ iᴷ q) ⟩
          → ⟨ (z ∈ˢ CO.iSet (fst p)) ⊓ (z ∈ˢ CO.iSet (fst q)) ⟩
    split z hz =
        subst (λ w → ⟨ z ∈ˢ w ⟩) (iᴷ-code p)
          (meetᴷ-split (iᴷ p) (iᴷ q) z hz .fst)
      , subst (λ w → ⟨ z ∈ˢ w ⟩) (iᴷ-code q)
          (meetᴷ-split (iᴷ p) (iᴷ q) z hz .snd)

--------------------------------------------------------------------------------
-- The coded extension, which is the element's own code
--------------------------------------------------------------------------------

-- Decision D1. K3's module Reverse takes below, below-sub and below-spec as
-- parameters with no supplier (TranslateReverse.agda:255-258) and K2 ships no
-- certified completion, so the architecture's section 6.2 had to rule on what
-- `below` costs. It costs nothing: the extension of a Boolean element is the
-- element's own code, and the adjunction is the two entailments below. The
-- decisive check, that K3's standing hypothesis below-⊤ (StandardNames.agda:
-- 683) is then refl, is in K5/ProbeD1.agda at exit 0.

belowᴷ-sub : (b : Pt CO.B) → ⟨ fst b ⊆ˢ carrier ⟩
belowᴷ-sub b = CO.B-sub (fst b) (snd b)

-- Forward: a condition lies in its own image, so an inclusion of the image
-- into b delivers the condition into b. This is where iᴷ-self is spent, and
-- it is the only place the seal's specification is needed outside the block.

belowᴷ-in : (b : Pt CO.B) (p : Cond) → ⟨ iᴷ p ≤ᴮ b ⟩ → ⟨ fst p ∈ˢ fst b ⟩
belowᴷ-in b p h = h (fst p) (iᴷ-self p)

-- Regularity, the one field that is a genuine property of a COMPLETION. It is
-- the universal property that replaces K2's equational recover, which needs
-- Collection and an internal image former that Core's telescope lacks. K2
-- proves the content and records in its own source (:1136-1142) that the
-- architecture had charged this direction a LEM and that it does not cost one.

belowᴷ-regular : (b : Pt CO.B) (p : Cond)
               → ⟨ K5.Frame.denseBelowΔ 𝒮 carrier order (fst p) (fst b) ⟩
               → ⟨ iᴷ p ≤ᴮ b ⟩
belowᴷ-regular b p db =
  belowᴷ-out b p (CO.denseBelow→mem (fst b) (snd b) (fst p) (snd p) db)

--------------------------------------------------------------------------------
-- The frame
--------------------------------------------------------------------------------

-- The whole of Track I's first obligation. Read the type first: for every
-- presentation of a forcing notion inside the model, and every excluded
-- middle at ℓ, the coded completion of that presentation together with K2's
-- embedding IS a K5 forcing frame. Everything tracks A to H prove about an
-- abstract frame therefore holds here.
--
-- LEM ℓ is spent at exactly two fields, i-compat← and i-dense, and both spend
-- it through the same lemma, nonzero→positive. That is the section 5.2 row
-- unchanged, and at 𝒮ʟ it is LEM (ℓ-suc ℓ₀), which is the hypothesis the two
-- landmarks already carry (K4/InstanceL.agda:50-51). Nothing here adds to the
-- ledger.

codedBase : LEM ℓ → P.ForcingBase CO.B IC.codedLattice IC.codedComplement
codedBase lem = record
  { ≼-refl        = CO.refl≼
  ; ≼-trans       = CO.trans≼
  ; inhabited     = CD.inhabited
  ; i             = iᴷ
  ; i-mono        = iᴷ-mono
  ; i-nonzero     = iᴷ-nonzero
  ; i-compat→     = i-compat→K
  ; i-compat←     = i-compat←K lem
  ; i-dense       = iᴷ-dense lem
  ; below         = fst
  ; below-sub     = belowᴷ-sub
  ; below-in      = belowᴷ-in
  ; below-out     = belowᴷ-out
  ; below-regular = belowᴷ-regular }

-- The completion datum, so that a consumer writes one telescope. It is K4's
-- and is re-exported rather than rebuilt (preamble rule 9 is about records;
-- this is the same inhabitant, not a second one).

codedKc : CodedComplete CO.B IC.codedLattice
codedKc = IC.codedComplete

--------------------------------------------------------------------------------
-- Decision D1 as Track C consumes it
--------------------------------------------------------------------------------

-- Track C found that at an ABSTRACT ForcingBase the record relates `below` to
-- the order and never to the code, so neither entailment between `below b`
-- and `fst b` is derivable there, and it put both in the types of the three
-- witnessAt lemmas that spend them (K5/Dense.agda:579-583). They are Track
-- I's to discharge, and under decision D1 both are the identity.
--
-- The types are taken from Track C's own module rather than retyped, which is
-- ledger clause L10 in its strongest form: this is not a copy that could
-- drift, it is Track C's definition applied to this instance, so the two
-- declarations below are a seam check and not a restatement. They also prove
-- the consumer line rather than asserting it: the arguments K5.Dense is
-- applied to here are exactly the ones every other consumer of the abstract
-- layer will write.
--
-- Neither depends on `lem`. It is a parameter of this module only because
-- `codedBase` is, and `codedBase`'s `below` field is `fst` whatever excluded
-- middle is supplied.

module AtDense (lem : LEM ℓ) where

  module C = K5.Dense 𝒮 ext paths sep carrier order
               CO.B IC.codedLattice IC.codedComplement IC.codedComplete
               (codedBase lem)

  codeOfBelow : C.CodeOfBelow
  codeOfBelow b x h = h

  belowOfCode : C.BelowOfCode
  belowOfCode b x h = h
