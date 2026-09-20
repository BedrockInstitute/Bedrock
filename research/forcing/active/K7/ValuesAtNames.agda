{-# OPTIONS --cubical --safe --guardedness #-}

-- K7 TRACK E'S SEAM PROBE. The only file of this track that applies
-- K5.Structures, K6.NameBuild or O7.Supply, and it answers three questions
-- that K7/PossibleValues.agda cannot answer about itself.
--
--   SEAM 1, THE STRUCTURE. K7/PossibleValues.agda builds the extension
--   structure as a record LITERAL out of two flat relations rather than by
--   applying K5.Structures, which is what keeps it at 1.57 s. The one thing a
--   reader cannot take on trust is that the literal is the SAME structure, and
--   `structure-agrees` below is that check by refl. Without this line the
--   track ships a well typed theorem about nothing.
--
--   SEAM 2, THE RESIDUE. The main file takes O7's GENERAL datum, forcesΔ with
--   its reading, as two parameters. This file fills both from O7/Supply.agda's
--   module Chain, whose own telescope is the landed K5 below pair, K6's free
--   forced set and ONE residue, valΔ. So the application below is the machine
--   check of the sentence "valΔ is the entire forcing side residue of Track E",
--   and `valuesOf` is reached from valΔ and nothing stronger.
--
--   SEAM 3, TRACK A. The four Separation cut data are filled from the real
--   K6.NameBuild.Calculus exports rather than from copied types.
--
-- SCHEDULING. Nothing here applies K6.ForcesTruth, K5.Truth, K5.Frame,
-- CodedCompletion.Core or Certificate.Nonzero, so ruling Q8's lone machine
-- seam is not touched and this file schedules on the ordinary two process gate.

open import Base.Prelude
open import Base.Truth
open import FOL.ZFStructure using ( ZFStructure )
open import FOL.Syntax using ( con; Formula; ∃̇∈ )
open import Cubical.Induction.WellFounded using ( WellFounded )
import FOL.Semantics
import OrdinaryProfile
import CodedVocabulary
import Valuation
import K5.Structures
import K6.NameBuild
import O7.Supply
import K7.PossibleValues
import Cubical.HITs.PropositionalTruncation as PT

open PT using ( ∥_∥₁ )

module K7.ValuesAtNames {ℓ} (𝒮 : ZFStructure (hPropAlgebra ℓ)) where

open import FOL.ZFStructure using ( module hPropStructure )

open TruthAlgebra (hPropAlgebra ℓ)
open hPropStructure 𝒮

open OrdinaryProfile 𝒮 using ( Separation; Collection )

private module SemG = FOL.Semantics (hPropAlgebra ℓ) 𝒮
open SemG.At S id using () renaming ( _⊨_ to _⊨ᴳ_ )

private module VL = Valuation 𝒮
open VL using ( Conditions )

open CodedVocabulary 𝒮 using ( isKPairΔ; prAtˢ; refinesΔ )

--------------------------------------------------------------------------------
-- The K3 and K5 spine, flat, in the shape K6/SeparationAtStructure.agda:54-72
--------------------------------------------------------------------------------

module Probe
  (entry       : S → S → S)
  (Child       : S → S → Type ℓ)
  (isPropChild : (x n : S) → isProp (Child x n))
  (child-entry : (x b n : S) → ⟨ entry x b ∈ˢ n ⟩ → Child x n)
  (child-wf    : WellFounded Child)
  (∅ᴺ          : S)
  (∅ᴺ-spec     : (z : S) → (z ∈ˢ ∅ᴺ) ≡ ⊥)
  (carrierᶠ    : S)
  (_≼ᶠ_        : Conditions carrierᶠ → Conditions carrierᶠ → Ω)
  (orderᶠ       : S)
  (≼ᶠ-reading : (p q : Conditions carrierᶠ)
               → (p ≼ᶠ q) ≡ refinesΔ orderᶠ (fst p) (fst q))
  (≼ᶠ-refl     : (p : Conditions carrierᶠ) → ⟨ p ≼ᶠ p ⟩)
  (≼ᶠ-trans    : {p q r : Conditions carrierᶠ} → ⟨ p ≼ᶠ q ⟩ → ⟨ q ≼ᶠ r ⟩ → ⟨ p ≼ᶠ r ⟩)
  (inhabitedᶠ  : ∥ Conditions carrierᶠ ∥₁)
  (IsNm        : S → Ω)
  (child-name  : (n : S) → ⟨ IsNm n ⟩ → (x : S) → Child x n → ⟨ IsNm x ⟩)
  (paths       : (x y : S) → (x ≈ˢ y) ≡ ((x ≡ y) , isSetS x y))
  where

  module KS = K5.Structures.Kernel 𝒮
                entry Child isPropChild child-entry child-wf ∅ᴺ ∅ᴺ-spec
  module SD = KS.Side carrierᶠ _≼ᶠ_ ≼ᶠ-refl ≼ᶠ-trans inhabitedᶠ IsNm child-name

  module PV = K7.PossibleValues 𝒮 paths
  module NM = PV.Names IsNm

  -- Slot one. The name type of the track is the name type K5 ships. Both are
  -- the same Sigma, so this is refl, and a Sigma is not generative; the line
  -- is here to make the check and not to prove a theorem.

  name-agrees : NM.Nm ≡ SD.Nm
  name-agrees = refl

  cond-agrees : Conditions carrierᶠ ≡ SD.Cond
  cond-agrees = refl

------------------------------------------------------------------------------
-- SEAM 1. The structure
------------------------------------------------------------------------------

  module At (G : SD.Sub)
    (entry-inj : {x b y c : S} → entry x b ≡ entry y c → (x ≡ y) × (b ≡ c))
    (ext-path  : {a b : S} → ((x : S) → (x ∈ˢ a) ≡ (x ∈ˢ b)) → a ≡ b)
    (chk       : S → S)
    (chk-spec  : (a e : S) → (e ∈ˢ chk a)
               ≡ ⋁ S (λ y → (y ∈ˢ a) ⊓ ⋁ S (λ p → (p ∈ˢ carrierᶠ)
                      ⊓ (e ≈ˢ entry (chk y) p))))
    (Γ         : S)
    (Γ-spec    : (e : S) → (e ∈ˢ Γ)
               ≡ ⋁ S (λ p → (p ∈ˢ carrierᶠ) ⊓ (e ≈ˢ entry (chk p) p)))
    (chk-name  : (a : S) → ⟨ IsNm (chk a) ⟩)
    where

    module E  = SD.Ext G
    module CP = E.Copy entry-inj paths ext-path chk chk-spec Γ Γ-spec chk-name

    -- The condition rebuilt from its code. At the instance Cond is the plain
    -- Sigma Conditions carrierᶠ (Valuation.agda:121-122), so both are the eta
    -- law and the round trip is refl. This is what K6/Replacement.agda:128-130
    -- records in prose and what O7/Definability.agda:277-278 takes as a
    -- parameter; here it is discharged.

    cndOf : (q : S) → ⟨ q ∈ˢ carrierᶠ ⟩ → SD.Cond
    cndOf q hq = q , hq

    cnd-cndOf : (q : S) (hq : ⟨ q ∈ˢ carrierᶠ ⟩) → fst (cndOf q hq) ≡ q
    cnd-cndOf q hq = refl

    orderFo : Formula S 2
    orderFo = ∃̇∈ (con orderᶠ)
      (prAtˢ zero (suc zero) (suc (suc zero)))

    orderFo-reading : (r p : SD.Cond)
                    → ((fst r ∷ fst p ∷ []) ⊨ᴳ orderFo) ≡ (r ≼ᶠ p)
    orderFo-reading r p = sym (≼ᶠ-reading r p)

    module VA = NM.AtG carrierᶠ SD.Cond fst snd cndOf cnd-cndOf
                  (SD._∈ᴾ G) E._≈[G]_ E._∈[G]_ CP.groundName

    -- THE LOAD BEARING LINE. The record literal of K7/PossibleValues.agda is
    -- the structure K5 ships, so every satisfaction below is the landed one.

    structure-agrees : VA.𝒮ᴱ ≡ E.structure
    structure-agrees = refl

    sat-agrees : ∀ {k} (ν : Vec NM.Nm k) (φ : Formula NM.Nm k)
               → (ν VA.⊨ φ) ≡ (ν E.⊨ φ)
    sat-agrees ν φ = refl

    -- And the check map is K5's own, not a second copy: the parameter `chk` of
    -- the track is filled by Copy.groundName (K5/Structures.agda:588-589).

    chk-agrees : S → NM.Nm
    chk-agrees = CP.groundName

----------------------------------------------------------------------------
-- SEAMS 2 AND 3. The residue and the cut
----------------------------------------------------------------------------

    -- Track A's calculus, applied. Its thirteen parameters are the flat spine
    -- K6/NameBuildAtGround.agda supplies; here they are the probe's own, which
    -- is all the seam needs: the four data the track consumes come out of the
    -- REAL module and not out of a copied type.

    module Cut
      (kpair-unique : (q x b : S) → ⟨ isKPairΔ q x b ⟩ → q ≡ entry x b)
      (entry-isKPair : (x b : S) → ⟨ isKPairΔ (entry x b) x b ⟩)
      (colAt         : ∀ {k} → Formula S (suc (suc k)) → Vec S k → Formula S 2)
      (colAt-reading : ∀ {k} (φ : Formula S (suc (suc k))) (ps : Vec S k) (y x : S)
                     → ((y ∷ x ∷ []) ⊨ᴳ colAt φ ps) ≡ ((y ∷ x ∷ ps) ⊨ᴳ φ))
      (separateOf      : Separation → (a : S) → Formula S 1 → S)
      (separateOf-spec : (sep : Separation) (a : S) (φ : Formula S 1) (x : S)
                       → (x ∈ˢ separateOf sep a φ)
                         ≡ ((x ∈ˢ a) ⊓ ((x ∷ []) ⊨ᴳ φ)))
      (graph→image : Collection → Separation → (f : S → S) (a : S)
                   → (graph : Formula S 2)
                   → ((x : S) → ⟨ x ∈ˢ a ⟩ → ⟨ (f x ∷ x ∷ []) ⊨ᴳ graph ⟩)
                   → ((x : S) → ⟨ x ∈ˢ a ⟩ → (y : S)
                      → ⟨ (y ∷ x ∷ []) ⊨ᴳ graph ⟩ → y ≡ f x)
                   → Σ[ T ∈ S ] ((z : S) → (z ∈ˢ T)
                       ≡ ⋁ S (λ x → (x ∈ˢ a) ⊓ (z ≈ˢ f x))))
      (⋃ᴳ      : S → S)
      (⋃ᴳ-spec : (a x : S) → (x ∈ˢ ⋃ᴳ a) ≡ ⋁ S (λ y → (y ∈ˢ a) ⊓ (x ∈ˢ y)))
      -- Track E2's two exports, still ABSTRACT: ruling Q8 forbids composing
      -- K6.ForcesTruth down to truth-at anywhere in K7, and this probe obeys
      -- it. What is checked here is the O7 side, not the engine side.
      (forces   : ∀ {k} → SD.Cond → Formula NM.Nm k → Vec NM.Nm k → Ω)
      (truth-at : ∀ {k} (φ : Formula NM.Nm k) (ν : Vec NM.Nm k)
                → (ν VA.⊨ φ)
                  ≡ ⋁ SD.Cond (λ r → (r SD.∈ᴾ G) ⊓ forces r φ ν))
      (forces-mono : ∀ {k} (r p : SD.Cond) → ⟨ r ≼ᶠ p ⟩
                   → (φ : Formula NM.Nm k) (ν : Vec NM.Nm k)
                   → ⟨ forces p φ ν ⟩ → ⟨ forces r φ ν ⟩)
      (directed : (p q : SD.Cond) → ⟨ p SD.∈ᴾ G ⟩ → ⟨ q SD.∈ᴾ G ⟩
                → ⟨ ⋁ SD.Cond (λ r → (r SD.∈ᴾ G)
                    ⊓ ((r ≼ᶠ p) ⊓ (r ≼ᶠ q))) ⟩)
      -- O7/Supply.agda's module Chain, telescope for telescope. Everything
      -- above valΔ is landed: below is a ForcingBase field (K5/Frame.agda:198),
      -- the two directions between below and the point's code are K5's
      -- CodeOfBelow and BelowOfCode (K5/Dense.agda:579-583), discharged by the
      -- identity at K5/InstanceBase.agda:361 and :364, and the two forces
      -- entailments are K6's free forced set (K6/ForcesTruth.agda:340, :345).
      (Pt     : Type ℓ)
      (ptCode : Pt → S)
      (below  : Pt → S)
      (valAt  : ∀ {k} → Formula NM.Nm k → Vec NM.Nm k → Pt)
      (forces-below : ∀ {k} (φ : Formula NM.Nm k) (ν : Vec NM.Nm k) (r : SD.Cond)
                    → ⟨ forces r φ ν ⟩ → ⟨ fst r ∈ˢ below (valAt φ ν) ⟩)
      (below-forces : ∀ {k} (φ : Formula NM.Nm k) (ν : Vec NM.Nm k) (r : SD.Cond)
                    → ⟨ fst r ∈ˢ below (valAt φ ν) ⟩ → ⟨ forces r φ ν ⟩)
      (cob : (b : Pt) (x : S) → ⟨ x ∈ˢ below b ⟩ → ⟨ x ∈ˢ ptCode b ⟩)
      (boc : (b : Pt) (x : S) → ⟨ x ∈ˢ ptCode b ⟩ → ⟨ x ∈ˢ below b ⟩)
      -- THE ONE RESIDUE.
      (valΔ : ∀ {k} → Formula NM.Nm k → Formula S (suc k))
      (valΔ-reading : ∀ {k} (φ : Formula NM.Nm k) (ν : Vec NM.Nm k) (w : S)
                    → ((w ∷ NM.codesOf ν) ⊨ᴳ valΔ φ)
                      ≡ (w ≈ˢ ptCode (valAt φ ν)))
      where

      module NB = K6.NameBuild.Calculus 𝒮 paths ext-path carrierᶠ
                    entry entry-isKPair kpair-unique colAt colAt-reading
                    separateOf separateOf-spec graph→image ⋃ᴳ ⋃ᴳ-spec

      module SUP = O7.Supply 𝒮
      module RED = SUP.Reduce IsNm paths
      module CH  = RED.Chain SD.Cond fst forces Pt ptCode below valAt
                     forces-below below-forces cob boc valΔ valΔ-reading

      -- THE TWO SEAMS, AS ONE APPLICATION. Every forcing side slot is filled
      -- by Chain's export and every cut slot by Track A's, so if this line
      -- elaborates then the track's telescope is the landed one.

      module VV = VA.Values forces truth-at _≼ᶠ_ forces-mono directed
                    orderFo orderFo-reading CH.forcesΔ CH.forcesΔ-reading
                    NB.mk NB.mk-in NB.mk-bound NB.mk-sat

      -- And the bound itself, at a table. Everything below valΔ and the table
      -- is discharged above.

      module AtTable
        (β       : S)
        (tab     : S)
        (tab-in  : (x : S) → ⟨ x ∈ˢ β ⟩
                 → ⟨ entry x (fst (CP.groundName x)) ∈ˢ tab ⟩)
        (tab-out : (e x u : S) → ⟨ x ∈ˢ β ⟩ → ⟨ e ∈ˢ tab ⟩
                 → ⟨ isKPairΔ e x u ⟩ → u ≡ fst (CP.groundName x))
        where

        module FT = VV.FromTable β entry entry-isKPair tab tab-in tab-out

        -- The shipped theorem, at the landed instance, with its type written
        -- out. `valuesOf` really is a ground SET former whose set argument is
        -- an element of S and whose formula argument is a Formula S 1 supplied
        -- by the file, so no class can be substituted at either slot.

        values-of : Separation → (p : SD.Cond) → (f : SD.Nm) (ξ : S) → S
        values-of = FT.valuesOf

        values-spec
          : (sep : Separation) (p : SD.Cond) (f : SD.Nm) (ξ a : S)
          → (a ∈ˢ values-of sep p f ξ)
            ≡ ((a ∈ˢ β)
               ⊓ ⋁ SD.Cond (λ r → (r ≼ᶠ p)
                   ⊓ forces r (NM.valueFo f)
                    (CP.groundName ξ ∷ CP.groundName a ∷ [])))
        values-spec = FT.valuesOf-spec
