{-# OPTIONS --cubical --safe --guardedness #-}

-- K7 Track C, SEAM PROBE.
--
-- K7/CCCEquivalence.agda takes Track A's whole vocabulary as flat module
-- parameters, because the shared spine of the architecture (4.0) says a
-- consumer takes a producer's export as an explicit parameter typed verbatim.
-- A track that does that and stops there ships a well typed theorem about
-- nothing: the parameters could describe a notion nobody has, and the arrows
-- would still elaborate. This file is the check that they do not.
--
-- Four things are measured here and nowhere else.
--
-- 1. EVERY parameter of module Presented and of module Free is filled with
--    Track A's actual export. If any type in that telescope had drifted from
--    K7/ChainConditions.agda by one argument or one abbreviation, the module
--    application below would be a type error.
--
-- 2. The alias check. Track A owns MaximalExtension and MaximalExtensionIn
--    (K7/ChainConditions.agda:443-454) and asks Track C to alias rather than
--    retype them. Track C cannot apply Track A, so it writes the two types
--    out at a fixed carrier and order. The two refl lines below are what makes
--    that an ALIAS instead of a second opinion.
--
-- 3. The arrow-type check against Track A's own reading of what remains open.
--    CCC₁to₂ and CCC₂to₃ (:457-461) are Track A's statements of the two paid
--    arrows. Track C's proofs are ascribed to them here, so the reduction
--    Track C shipped is the reduction Track A asked for and not a neighbour.
--
-- 4. compat-refl, Track C's one presentation hypothesis, is DISCHARGED from
--    the real ForcingLaws (CodedCompletion.agda:228) rather than assumed. A
--    condition is compatible with itself because it refines itself.

open import Base.Prelude
open import Base.Truth
open import Base.Classical using ( LEM )
open import FOL.ZFStructure using ( ZFStructure )
import OrdinaryProfile

module K7.CCCEquivalenceAtA
  {ℓ} (𝒮 : ZFStructure (hPropAlgebra ℓ))
  (ext : OrdinaryProfile.Extensionality 𝒮)
  (paths : (x y : ZFStructure.S 𝒮)
         → (ZFStructure._≈ˢ_ 𝒮 x y) ≡ ((x ≡ y) , ZFStructure.isSetS 𝒮 x y))
  where

open import FOL.ZFStructure using ( module hPropStructure )
import Cubical.HITs.PropositionalTruncation as PT
open PT using ( ∣_∣₁ )

import CodedVocabulary
import CardinalBridge
import CodedCompletion

open TruthAlgebra (hPropAlgebra ℓ)
open hPropStructure 𝒮

module OP = OrdinaryProfile 𝒮
module CV = CodedVocabulary 𝒮
module CB = CardinalBridge 𝒮
module CCo = CodedCompletion 𝒮

open CV using ( compatibleΔ; subsetΔ; predenseΔ )
open CB using ( injectable )

open import K7.ChainConditions 𝒮 ext paths
  using ( antichainΔ; antichain-use; antichain-intro
        ; maximalΔ; maximal-intro
        ; countableΔ; injectable-mono-dom
        ; CCC₁ᴵ; CCC₂ᴵ; CCC₃ᴵ
        ; ccc₁-use; ccc-use; ccc-intro; ccc₃-intro; ccc₃→ccc₁
        ; MaximalExtension; MaximalExtensionIn; CCC₁to₂; CCC₂to₃ )

import K7.CCCEquivalence
module K7C = K7.CCCEquivalence 𝒮 ext paths

--------------------------------------------------------------------------------
-- The record, and the level that makes it inhabitable
--------------------------------------------------------------------------------

-- Rule 8 says check a record's FIELDS before believing a count or a level, and
-- K7 has added the uninhabitable-record variant to that rule. The ascription
-- is the control: GroundWellOrder really does live one universe up, because
-- lt : S → S → Ω and Ω = hProp ℓ is Type (ℓ-suc ℓ). At Type ℓ the declaration
-- is rejected outright, which K7/breaks/GroundWellOrderLevel.agda-break
-- measures, and the PARAMETER form at Type ℓ is accepted and uninhabitable,
-- which is the shape no grep finds.

_ : Type (ℓ-suc ℓ)
_ = K7C.GroundWellOrder

-- The converse of the gap ruling Q3 names. Ascribed to the profile's own
-- internal choice sentence so a ledger reader can see the conclusion is
-- OrdinaryProfile.ChoiceSet (:115-124) and nothing weaker.

wo→choiceSet-type : (wo : K7C.GroundWellOrder)
                  → OP.Separation → OP.Collection
                  → K7C.ToChoice.LtDefinable wo → OP.ChoiceSet
wo→choiceSet-type wo = K7C.ToChoice.wo→choiceSet wo

--------------------------------------------------------------------------------
-- The presentation, and the one hypothesis discharged at it
--------------------------------------------------------------------------------

module AtPresentation (𝔓 : CCo.Presentation) where

  -- The K2Bridge spelling trap (K2Bridge.agda:53-59): a record declared
  -- inside a parameterized module takes the enclosing parameters implicitly,
  -- so CCo.Coded.ForcingLaws 𝔓 does not elaborate. Open first.

  open CCo.Coded 𝔓

  module AtLaws (laws : ForcingLaws) where

    open ForcingLaws laws

    -- Check 4. Track C's compat-refl is the presentation's reflexivity,
    -- witnessed by the condition itself. _≼ᴵ_ is refinesΔ order
    -- (CodedCompletion.agda:218-219), so the two refinement slots of
    -- compatibleΔ are filled by the same proof.

    compat-refl : (p : S) → ⟨ p ∈ˢ carrier ⟩ → ⟨ compatibleΔ carrier order p p ⟩
    compat-refl p hp = ∣ p , hp , ≼ᴵ-refl p hp , ≼ᴵ-refl p hp ∣₁

    -- Check 1. Every parameter of Track C, filled by Track A's export.

    module P = K7C.Presented carrier order compat-refl
                 antichainΔ antichain-use antichain-intro
                 maximalΔ maximal-intro
                 injectable injectable-mono-dom

    module F = P.Free CCC₁ᴵ CCC₂ᴵ CCC₃ᴵ
                 ccc₁-use ccc-use ccc-intro ccc₃-intro ccc₃→ccc₁

    -- Check 2. The alias, both directions of the reduction vocabulary.

    maximal-extension-agrees : P.MaximalExtension ≡ MaximalExtension carrier order
    maximal-extension-agrees = refl

    maximal-extension-in-agrees :
      P.MaximalExtensionIn ≡ MaximalExtensionIn carrier order
    maximal-extension-in-agrees = refl

    -- Check 3. The two paid arrows, ascribed to Track A's own arrow types.
    -- These are the deliverables of this track, read at the real vocabulary.

    ccc₁→ccc₂-at : (w : S) → CCC₁to₂ carrier order w
    ccc₁→ccc₂-at w mx = F.ccc₁→ccc₂ mx w

    ccc₂→ccc₃-at : (w : S) → CCC₂to₃ carrier order w
    ccc₂→ccc₃-at w mxi = F.ccc₂→ccc₃ mxi w

    -- And the assembled equivalence, whose third component is Track A's free
    -- arrow. Nothing here is λ x → x: the first two components each run a
    -- truncation elimination and a monotonicity step.

    equivalence-at :
        MaximalExtension carrier order → MaximalExtensionIn carrier order
      → (w : S)
      → (⟨ CCC₁ᴵ carrier order w ⟩ → ⟨ CCC₂ᴵ carrier order w ⟩)
      × ((⟨ CCC₂ᴵ carrier order w ⟩ → ⟨ CCC₃ᴵ carrier order w ⟩)
        × (⟨ CCC₃ᴵ carrier order w ⟩ → ⟨ CCC₁ᴵ carrier order w ⟩))
    equivalence-at = F.ccc-equivalent

    -- The countability abbreviation, checked rather than assumed: Track A's
    -- countableΔ w d is this file's injectable d w by definition
    -- (K7/ChainConditions.agda:265-266), which is why Track C's telescope may
    -- write one where Track A writes the other.

    countable-agrees : (w d : S) → countableΔ w d ≡ injectable d w
    countable-agrees w d = refl

    -- The greedy reduction at the real vocabulary. The gap between the ground
    -- well ordering and MaximalExtension is exactly GreedySupply, and this is
    -- that statement with every parameter filled.

    greedy-at : (wo : K7C.GroundWellOrder) → LEM ℓ
              → P.FromChoice.GreedySupply wo → MaximalExtension carrier order
    greedy-at wo lem = P.FromChoice.greedy→extension wo lem

    -- And the refutation of MaximalExtensionIn, at the real predicate, so
    -- that the hypotheses it is refuted from are read against Track A's
    -- antichain and CodedVocabulary's predensity and not against a lookalike.

    refutation-at :
        (b p₁ p₂ r₁ r₂ : S)
      → ⟨ subsetΔ b carrier ⟩
      → ⟨ predenseΔ carrier order b ⟩
      → ⟨ p₁ ∈ˢ b ⟩ → ⟨ p₂ ∈ˢ b ⟩
      → ((u : S) → ⟨ u ∈ˢ b ⟩ → ⟨ (u ≈ˢ p₁) ⊔ (u ≈ˢ p₂) ⟩)
      → ⟨ compatibleΔ carrier order p₁ p₂ ⟩
      → (⟨ p₁ ≈ˢ p₂ ⟩ → ⟨ ⊥ ⟩)
      → ⟨ r₁ ∈ˢ carrier ⟩ → (⟨ compatibleΔ carrier order p₁ r₁ ⟩ → ⟨ ⊥ ⟩)
      → ⟨ r₂ ∈ˢ carrier ⟩ → (⟨ compatibleΔ carrier order p₂ r₂ ⟩ → ⟨ ⊥ ⟩)
      → MaximalExtensionIn carrier order → ⟨ ⊥ ⟩
    refutation-at = P.MaximalExtensionIn-refuted
