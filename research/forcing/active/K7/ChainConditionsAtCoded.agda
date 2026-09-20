{-# OPTIONS --cubical --safe --guardedness #-}

-- K7 Track A, SEAM PROBE.
--
-- K7/ChainConditions.agda is written against a bare ZFStructure and takes
-- its vocabulary from CodedVocabulary and CardinalBridge, which are
-- parameterized by nothing but that structure. What it does NOT do is apply
-- CodedCompletion, whose module Core is on the forbidden list for every K7
-- file outside a named seam probe. This is that probe, and it exists
-- because a track that builds its own lookalike and does not add one ships
-- a well typed theorem about nothing.
--
-- Four things are checked here and nowhere else.
--
-- 1. The ascription control. CCC₁ᴵ, CCC₂ᴵ and CCC₃ᴵ at the presentation's
--    own carrier and order really do land in S → Ω, the model's truth
--    values, and not in Type (ℓ-suc ℓ). That is
--    CodedCompletion.agda:987-993's own diagnostic for a host-quantified
--    draft, run at the real presentation.
--
-- 2. The transcription check. antichainᴴ, which K7/ChainConditions.agda
--    transcribes from CodedCompletion.agda:1012-1017 because it may not
--    import it, is the real antichainᴵ. By refl.
--
-- 3. The vocabulary agreement. subsetΔ, predenseΔ, denseΔ and compatibleΔ
--    at this carrier and order are Core's own subsetOf, predenseᴵ, denseᴵ
--    and compatibleᴵ. By refl. Without these the chain conditions could be
--    about a different notion than the completion is built from.
--
-- 4. The consumer telescope. Track D
--    (K7/CompletionTransfer.agda:266-273, :526-534) takes six of this
--    track's exports as flat parameters. Each is aliased below with the
--    CONSUMER's type written out and the PRODUCER's export as the body, so
--    a drift in either direction is a type error here rather than a silent
--    mismatch at assembly time.

open import Base.Prelude
open import Base.Truth
open import FOL.ZFStructure using ( ZFStructure )
import OrdinaryProfile

module K7.ChainConditionsAtCoded
  {ℓ} (𝒮 : ZFStructure (hPropAlgebra ℓ))
  (ext : OrdinaryProfile.Extensionality 𝒮)
  (paths : (x y : ZFStructure.S 𝒮)
         → (ZFStructure._≈ˢ_ 𝒮 x y) ≡ ((x ≡ y) , ZFStructure.isSetS 𝒮 x y))
  where

open import FOL.ZFStructure using ( module hPropStructure )
open import FOL.Syntax using ( Formula; var )
open import FOL.LevyHierarchy using ( Δ₀; checkΔ₀ )
open import FOL.Semantics (hPropAlgebra ℓ) 𝒮 using ( module At; _^_ )
open import FOL.ZFModel 𝒮 using ( _⊆ˢ_ )
open import Cubical.Data.Unit using ( tt )

import CodedVocabulary
import CardinalBridge
import CodedCompletion

open TruthAlgebra (hPropAlgebra ℓ)
open hPropStructure 𝒮

module OP = OrdinaryProfile 𝒮
module CV = CodedVocabulary 𝒮
module CB = CardinalBridge 𝒮
module CC = CodedCompletion 𝒮

open CV using ( compatibleΔ; subsetΔ; denseΔ; predenseΔ )
open CB using ( injectable )
open At S id using ( _⊨_ )

-- The export surface this track is consumed through, listed rather than
-- opened wholesale: a name that leaves K7/ChainConditions.agda and is not
-- here is not part of the interface, and a name here that disappears is a
-- scope error in this file.

open import K7.ChainConditions 𝒮 ext paths
  using ( antichainAtˢ; Δ₀-antichainAtˢ; antichainAtˢ-reading
        ; antichainΔ; antichain-use; antichain-intro; antichainΔ-mono
        ; antichainᴴ; antichainΔ-is-antichainᴵ; member-cong
        ; maximalΔ; maximal-intro; maximal-antichain; maximal-predense
        ; countableΔ; injectable-mono-dom
        ; CCC₁ᴵ; CCC₂ᴵ; CCC₃ᴵ
        ; ccc₁-use; ccc₁-intro; ccc-use; ccc-intro; ccc₃-use; ccc₃-intro
        ; ccc₂→ccc₁; ccc₃→ccc₁
        ; MaximalExtension; MaximalExtensionIn; CCC₁to₂; CCC₂to₃ )

--------------------------------------------------------------------------------
-- The two checks that need no presentation
--------------------------------------------------------------------------------

-- The Δ₀ certificate and the reading, at concrete Fin indices rather than
-- at variables, so that checkΔ₀ really computes and refl really elaborates.
-- Three distinct slots in a three-variable environment: the carrier at 0,
-- the order at 1, the coded subset at 2.

Δ₀-check : Δ₀ (antichainAtˢ {3} zero (suc zero) (suc (suc zero)))
Δ₀-check = checkΔ₀ (antichainAtˢ {3} zero (suc zero) (suc (suc zero))) tt

reading-check : (c o d : S)
              → ((c ∷ o ∷ d ∷ []) ⊨ antichainAtˢ zero (suc zero) (suc (suc zero)))
                ≡ antichainΔ c o d
reading-check c o d = refl

--------------------------------------------------------------------------------
-- The consumer telescope, Track D's parameter types written out
--------------------------------------------------------------------------------

-- K7/CompletionTransfer.agda:266-273. The antichain pair.

antichainΔᴰ : S → S → S → Ω
antichainΔᴰ = antichainΔ

antichain-useᴰ : (c o d p q : S) → ⟨ antichainΔᴰ c o d ⟩
               → ⟨ p ∈ˢ c ⟩ → ⟨ p ∈ˢ d ⟩ → ⟨ q ∈ˢ c ⟩ → ⟨ q ∈ˢ d ⟩
               → ⟨ compatibleΔ c o p q ⟩ → ⟨ p ≈ˢ q ⟩
antichain-useᴰ = antichain-use

antichain-introᴰ : (c o d : S)
                 → ((p q : S) → ⟨ p ∈ˢ c ⟩ → ⟨ p ∈ˢ d ⟩ → ⟨ q ∈ˢ c ⟩ → ⟨ q ∈ˢ d ⟩
                    → ⟨ compatibleΔ c o p q ⟩ → ⟨ p ≈ˢ q ⟩)
                 → ⟨ antichainΔᴰ c o d ⟩
antichain-introᴰ = antichain-intro

-- K7/CompletionTransfer.agda:526-534. The CCC₂ pair, with the ground ω code
-- in the third slot. Note that the consumer's conclusion is spelled
-- injectable d v and not countableΔ v d, so this alias is also the check
-- that countableΔ is a definition and not an opaque wrapper.

CCC₂ᴵᴰ : S → S → S → Ω
CCC₂ᴵᴰ = CCC₂ᴵ

ccc-useᴰ : (c o v d : S) → ⟨ CCC₂ᴵᴰ c o v ⟩ → ⟨ subsetΔ d c ⟩
         → ⟨ antichainΔᴰ c o d ⟩ → ⟨ injectable d v ⟩
ccc-useᴰ = ccc-use

ccc-introᴰ : (c o v : S)
           → ((d : S) → ⟨ subsetΔ d c ⟩ → ⟨ antichainΔᴰ c o d ⟩
              → ⟨ injectable d v ⟩)
           → ⟨ CCC₂ᴵᴰ c o v ⟩
ccc-introᴰ = ccc-intro

--------------------------------------------------------------------------------
-- At a real presentation
--------------------------------------------------------------------------------

-- The presentation's four fields arrive as the record, because here they
-- may: this file is allowed the applications the parametric file is not.
-- CodedCompletion.agda:201-208.

module AtPresentation (𝔓 : CC.Presentation) where

  -- The K2Bridge spelling trap, measured at K2Bridge.agda:53-59: a record
  -- declared inside a parameterized module takes the enclosing parameters
  -- implicitly, so CC.Coded.ForcingLaws 𝔓 does not elaborate. Open first.

  open CC.Coded 𝔓

  -- Ruling Q1, followed: the three conditions live at the CODED
  -- presentation, whose order is a set of the model, and not at
  -- Certificate.Presentation, whose order is a host relation on Pt carrier.
  -- The ascription is the whole of the control. Each of the three is a
  -- function into Ω; had any quantifier ranged over a host subset the
  -- ascription would demand Type (ℓ-suc ℓ) and this block would not
  -- elaborate.

  _ : S → Ω
  _ = CCC₁ᴵ carrier order

  _ : S → Ω
  _ = CCC₂ᴵ carrier order

  _ : S → Ω
  _ = CCC₃ᴵ carrier order

  -- The vocabulary agreement, all four by refl. Core's own notions are
  -- CodedCompletion.agda:996-1005.

  subset-agrees : (d : S) → subsetΔ d carrier ≡ (d ⊆ˢ carrier)
  subset-agrees d = refl

  module AtLaws (laws : ForcingLaws)
                (pow : OP.PowerSet) (sep : OP.Separation) where

    module Core𝔓 = CC.Core ext pow sep paths 𝔓 laws

    -- Check 2, the transcription. K7/ChainConditions.agda's antichainᴴ is
    -- a hand copy of CodedCompletion.agda:1012-1017 because Core may not be
    -- applied there. This is the copy checked against the original.

    antichain-agrees : (d : S) → antichainᴴ carrier order d ≡ Core𝔓.antichainᴵ d
    antichain-agrees d = refl

    -- Check 3, the rest of the vocabulary.

    dense-agrees : (d : S) → denseΔ carrier order d ≡ Core𝔓.denseᴵ d
    dense-agrees d = refl

    predense-agrees : (d : S) → predenseΔ carrier order d ≡ Core𝔓.predenseᴵ d
    predense-agrees d = refl

    compat-agrees : (p q : S) → compatibleΔ carrier order p q ≡ Core𝔓.compatibleᴵ p q
    compat-agrees p q = refl

    subsetOf-agrees : (d : S) → subsetΔ d carrier ≡ Core𝔓.subsetOf d
    subsetOf-agrees d = refl

    -- And the realization lemma at the real object, which is what makes the
    -- paths cost concrete rather than notional.

    antichain-is-antichainᴵ : (d : S) → antichainΔ carrier order d ≡ Core𝔓.antichainᴵ d
    antichain-is-antichainᴵ d = antichainΔ-is-antichainᴵ paths carrier order d
