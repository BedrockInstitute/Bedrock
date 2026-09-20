{-# OPTIONS --cubical --safe --guardedness #-}

-- K7 Track D, seam probe. THE ONLY K7 FILE THAT APPLIES Certificate.Nonzero.
--
-- K7/CompletionTransfer.agda takes the whole B-plus block flat, because the
-- type of PropertyTransfer.transfer names Nonzero.B⁺ 𝔓 c sep, which is rule
-- 3's exact shape and rule 2b's nested-operation shape. This file is where
-- that application is made once, and it asks the question no grep over the
-- parametric file can answer:
--
--   IS THE PRESENTATION THE PARAMETRIC TRANSFER IS ABOUT THE PRESENTATION
--   Certificate.Nonzero ACTUALLY BUILDS?
--
-- Nothing is proved here. Every declaration is refl, a projection, or a
-- forwarded parameter.

open import Base.Prelude
open import Base.Truth
open import FOL.ZFStructure using ( ZFStructure )
import OrdinaryProfile
import Certificate
import CodedVocabulary
import K7.CompletionTransfer

module K7.TransferAtCertificate
  {ℓ} (𝒮 : ZFStructure (hPropAlgebra ℓ))
  (ext : OrdinaryProfile.Extensionality 𝒮)
  (paths : (x y : ZFStructure.S 𝒮)
         → (ZFStructure._≈ˢ_ 𝒮 x y) ≡ ((x ≡ y) , ZFStructure.isSetS 𝒮 x y))
  where

open import FOL.ZFStructure using ( module hPropStructure )
open import Cubical.Data.Sigma using ( _×_ )
open import Cubical.Data.Sum using ( _⊎_ )
import Cubical.HITs.PropositionalTruncation as PT
open PT using ( ∥_∥₁ )

open TruthAlgebra (hPropAlgebra ℓ)
open hPropStructure 𝒮

module OP = OrdinaryProfile 𝒮
module G  = Certificate 𝒮 ext paths
module CV = CodedVocabulary 𝒮
module CT = K7.CompletionTransfer 𝒮 ext paths

open CV using ( refinesΔ; compatibleΔ; subsetΔ )

-- The certificate layer, applied for real. 𝔓, c and sep are the three
-- parameters Certificate.Nonzero takes (Certificate.agda:956-957).

module Seam
  (𝔓   : G.Presentation)
  (cert : G.Over.CertifiedCompletion 𝔓)
  (sep : OP.Separation)
  (Φ Ψ : G.Presentation → Ω)
  where

  module C  = G.Over.Theory 𝔓 cert
  module N  = G.Nonzero 𝔓 cert sep
  module Pr = G.Property 𝔓 cert sep Φ Ψ

  ----------------------------------------------------------------------------
  -- THE ALIASES. Each TYPE is K7.CompletionTransfer's parameter type,
  -- character for character; each BODY is the producer's export.
  ----------------------------------------------------------------------------

  HostPresentation : Type (ℓ-suc ℓ)
  HostPresentation = G.Presentation

  𝔓ᴴ : HostPresentation
  𝔓ᴴ = 𝔓

  Bcode : S
  Bcode = C.B

  botCode : S
  botCode = N.botCode

  B⁺set : S
  B⁺set = N.B⁺set

  B⁺ : HostPresentation
  B⁺ = N.B⁺

  B⁺spec : (x : S) → (x ∈ˢ B⁺set) ≡ ((x ∈ˢ Bcode) ⊓ ((x ≈ˢ botCode) ⇒ ⊥))
  B⁺spec = N.B⁺spec

  B⁺carrier : G.Presentation.carrier B⁺ ≡ B⁺set
  B⁺carrier = refl

  ----------------------------------------------------------------------------
  -- CHECK ONE. The Ψ-argument of the parametric transfer really is
  -- Nonzero.B⁺ 𝔓 cert sep, and not a lookalike presentation.
  ----------------------------------------------------------------------------

  target-agrees : Ψ B⁺ ≡ Ψ (G.Nonzero.B⁺ 𝔓 cert sep)
  target-agrees = refl

  ----------------------------------------------------------------------------
  -- CHECK TWO, and it is the one that protects a consumer. The parametric
  -- file's transfer-runs has type CCCHypotheses → ⟨ Φ 𝔓ᴴ ⟩ → ⟨ Ψ B⁺ ⟩ with
  -- B⁺ flat. This declaration demands that that type be the record field's
  -- type, which names Nonzero.B⁺ applied. If the two drifted, this line and
  -- not a later K8 consumer is where it shows.
  ----------------------------------------------------------------------------

  transfer-type : (T : Pr.PropertyTransfer)
                → Pr.PropertyTransfer.hypotheses T → ⟨ Φ 𝔓ᴴ ⟩ → ⟨ Ψ B⁺ ⟩
  transfer-type T = Pr.PropertyTransfer.transfer T

  package : (H : Type ℓ) → (H → ⟨ Φ 𝔓ᴴ ⟩ → ⟨ Ψ B⁺ ⟩) → Pr.PropertyTransfer
  package H t = record { hypotheses = H ; transfer = t }

--------------------------------------------------------------------------------
-- THE CHOICE SEAM. WHERE M's WELL ORDERING MEETS THE TRANSFER.
--------------------------------------------------------------------------------

-- K7/CompletionTransfer.agda proves its two structural lemmas with the well
-- ordering out of scope, and takes the selection relation as a parameter. That
-- arrangement is worthless unless the parameter can actually be filled by M's
-- choice and by nothing weaker. This module is where the composition is made,
-- and it is the only place in K7 where it is made.
--
-- The three aliases are K6/Choice.agda:418-422, character for character.

module ChoiceSeam
  (lt       : S → S → Ω)
  (lt-tri   : (z z' : S) → ∥ ⟨ lt z z' ⟩ ⊎ ((z ≡ z') ⊎ ⟨ lt z' z ⟩) ∥₁)
  (wo-least : (d : S) → ⟨ ⋁ S (λ z → z ∈ˢ d) ⟩
            → ⟨ ⋁ S (λ z → (z ∈ˢ d)
                  ⊓ ⋀ S (λ z' → (z' ∈ˢ d) ⇒ ((lt z' z) ⇒ ⊥))) ⟩)
  where

  -- The opaque carrier the assembly sees. K6/Choice.agda:939 takes exactly
  -- this shape, a Type (ℓ-suc ℓ) and nothing else, so that no ZF field can
  -- look inside the well ordering. Track C will publish it as a record; until
  -- it does, this Sigma is the same three components at the same level and the
  -- record projections will fill the three arguments below unchanged.

  GWO : Type (ℓ-suc ℓ)
  GWO = Σ[ r ∈ (S → S → Ω) ]
          ( ((z z' : S) → ∥ ⟨ r z z' ⟩ ⊎ ((z ≡ z') ⊎ ⟨ r z' z ⟩) ∥₁)
          × ((d : S) → ⟨ ⋁ S (λ z → z ∈ˢ d) ⟩
             → ⟨ ⋁ S (λ z → (z ∈ˢ d)
                   ⊓ ⋀ S (λ z' → (z' ∈ˢ d) ⇒ ((r z' z) ⇒ ⊥))) ⟩) )

  theWO : GWO
  theWO = lt , lt-tri , wo-least

  module W = CT.Well GWO fst (λ g → fst (snd g)) (λ g → snd (snd g))

  -- The selection is the lt-least element and nothing else, by refl.

  selection-is-least : (fam : S → S) (u p : S)
                     → W.selectAt theWO fam u p ≡ W.leastIn theWO (fam u) p
  selection-is-least fam u p = refl

  module Compose
    (carrier order  : S)
    (B⁺set  order⁺  : S)
    (img       : S → S)
    (img-in    : (p : S) → ⟨ p ∈ˢ carrier ⟩ → ⟨ img p ∈ˢ B⁺set ⟩)
    (img-mono  : (r p : S) → ⟨ r ∈ˢ carrier ⟩ → ⟨ p ∈ˢ carrier ⟩
               → ⟨ refinesΔ order r p ⟩ → ⟨ refinesΔ order⁺ (img r) (img p) ⟩)
    (below         : S → S)
    (below-sub     : (b p : S) → ⟨ p ∈ˢ below b ⟩ → ⟨ p ∈ˢ carrier ⟩)
    (below-refines : (b p : S) → ⟨ p ∈ˢ below b ⟩
                   → ⟨ refinesΔ order⁺ (img p) b ⟩)
    (refines⁺-trans : (u v z : S) → ⟨ refinesΔ order⁺ u v ⟩
                    → ⟨ refinesΔ order⁺ v z ⟩ → ⟨ refinesΔ order⁺ u z ⟩)
    (antichainΔ : S → S → S → Ω)
    (antichain-use : (c o d p q : S) → ⟨ antichainΔ c o d ⟩
                   → ⟨ p ∈ˢ c ⟩ → ⟨ p ∈ˢ d ⟩ → ⟨ q ∈ˢ c ⟩ → ⟨ q ∈ˢ d ⟩
                   → ⟨ compatibleΔ c o p q ⟩ → ⟨ p ≈ˢ q ⟩)
    (antichain-intro : (c o d : S)
                     → ((p q : S) → ⟨ p ∈ˢ c ⟩ → ⟨ p ∈ˢ d ⟩ → ⟨ q ∈ˢ c ⟩
                        → ⟨ q ∈ˢ d ⟩ → ⟨ compatibleΔ c o p q ⟩ → ⟨ p ≈ˢ q ⟩)
                     → ⟨ antichainΔ c o d ⟩)
    where

    module St = CT.Structural carrier order B⁺set order⁺ img img-in img-mono
                  below below-sub below-refines refines⁺-trans
                  antichainΔ antichain-use antichain-intro

    -- CHECK THREE, AND IT IS THE ONE THIS TRACK EXISTS FOR. Module Well's three
    -- exports fill module WithSelection's three parameters with no adapter.
    -- If the selection the transfer consumes and the selection M's well
    -- ordering produces had drifted, this application and not a later K8
    -- consumer is where it would show.

    module WS = St.WithSelection
                  (W.selectAt theWO below)
                  (W.select-in theWO below)
                  (W.select-unique theWO below)

    module Tr
      (HostPresentation : Type (ℓ-suc ℓ))
      (𝔓ᴴ B⁺ : HostPresentation)
      (Φ Ψ   : HostPresentation → Ω)
      (CCC₂ᴵ      : S → S → S → Ω)
      (injectable : S → S → Ω)
      (w : S)
      (ccc-use   : (c o v d : S) → ⟨ CCC₂ᴵ c o v ⟩ → ⟨ subsetΔ d c ⟩
                 → ⟨ antichainΔ c o d ⟩ → ⟨ injectable d v ⟩)
      (ccc-intro : (c o v : S)
                 → ((d : S) → ⟨ subsetΔ d c ⟩ → ⟨ antichainΔ c o d ⟩
                    → ⟨ injectable d v ⟩)
                 → ⟨ CCC₂ᴵ c o v ⟩)
      (Φ-reading : Φ 𝔓ᴴ ≡ CCC₂ᴵ carrier order  w)
      (Ψ-reading : Ψ B⁺  ≡ CCC₂ᴵ B⁺set  order⁺ w)
      where

      module T = WS.Transfer HostPresentation 𝔓ᴴ B⁺ Φ Ψ CCC₂ᴵ injectable w
                   ccc-use ccc-intro Φ-reading Ψ-reading

      -- CHECK FOUR. The one field of CCCHypotheses that M's choice pays for is
      -- exactly what module Well delivers, given the density of i[P] in B⁺.
      -- The density hypothesis is Bell's "P will be regarded as a dense subset
      -- of B" (fulltext:3486) and is the certificate's own `below` at a
      -- positive element; it is NOT a choice principle.

      total-from-choice :
          ((u : S) → ⟨ u ∈ˢ B⁺set ⟩ → ⟨ ⋁ S (λ p → p ∈ˢ below u) ⟩)
        → T.SelTotal
      total-from-choice dense u hu = W.select-total theWO below u (dense u hu)
