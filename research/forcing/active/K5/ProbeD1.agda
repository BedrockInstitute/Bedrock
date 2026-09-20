{-# OPTIONS --cubical --safe --guardedness #-}

-- K5 Track A, PROBE. NOT A DELIVERABLE and not imported by K5/Frame.agda.
--
-- What this file is for. The K5 architecture's decision D1 rules that the
-- coded extension of a Boolean element is the element's OWN CODE, so that
-- `below := fst` and no Separation is spent. Track A was told to verify that
-- ruling before building on it, and the decisive check named in the ruling is
-- that K3's standing hypothesis
--
--   below-⊤ : below (⊤ᴮ , ⊤ᴮ∈B) ≡ carrier          StandardNames.agda:683
--
-- is then discharged by refl, because CO.⊤ᴮ = carrier , inB carrier …
-- (CodedCompletion.agda:512-513).
--
-- This file therefore applies CodedCompletion.Core, which ledger clause L2
-- forbids to every deliverable of tracks A to H. A probe is evidence and not
-- a deliverable, so the prohibition is honoured by keeping the application
-- here and out of K5/Frame.agda, which applies K4.Algebra, K4.Implication and
-- CodedVocabulary and nothing else.
--
-- Four of the thirteen ForcingBase fillers of architecture section 1.2 are
-- transcribed below as well, since they cost nothing once Core is open.

open import Base.Prelude
open import Base.Truth
open import FOL.ZFStructure using ( ZFStructure )
import OrdinaryProfile
import CodedVocabulary
import CodedCompletion

module K5.ProbeD1
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

open CodedVocabulary 𝒮 using ( coneΔ )

module CC = CodedCompletion 𝒮
open CC.Coded 𝔓
open CC.Core ext pow sep paths 𝔓 laws

--------------------------------------------------------------------------------
-- Decision D1, transcribed
--------------------------------------------------------------------------------

-- `below` is stated over the pair of a code and its membership proof, because
-- that is the shape K3's module Reverse takes (StandardNames.agda:682) and the
-- shape El already is.

belowK : (Σ[ b ∈ S ] ⟨ b ∈ˢ B ⟩) → S
belowK = fst

--------------------------------------------------------------------------------
-- The decisive check
--------------------------------------------------------------------------------

-- K3's standing hypothesis, character for character from StandardNames.agda:683
-- with below := belowK, ⊤ᴮ := fst CC.⊤ᴮ and ⊤ᴮ∈B := snd CC.⊤ᴮ.

below-⊤ : belowK (fst ⊤ᴮ , snd ⊤ᴮ) ≡ carrier
below-⊤ = refl

-- And the reason, isolated: the code of the Boolean top IS the carrier.

⊤-code : fst ⊤ᴮ ≡ carrier
⊤-code = refl

--------------------------------------------------------------------------------
-- The adjunction, constructively in both directions
--------------------------------------------------------------------------------

-- Forward: a condition lies in its own image (i-self, CodedCompletion.agda:588),
-- so an inclusion of the image into b delivers the condition into b.

below-in : (b : El) (p : Cond) → ⟨ iᴮ p ≤ᴮ b ⟩ → ⟨ fst p ∈ˢ belowK b ⟩
below-in b p h = h (fst p) (i-self p)

-- Backward: this is the `where`-bound `below` inside i-dense
-- (CodedCompletion.agda:615-630) lifted to a standalone lemma. A regular open
-- is downward closed, so the cone of one of its members is inside it, and the
-- regularization is monotone.

below-out : (b : El) (p : Cond) → ⟨ fst p ∈ˢ belowK b ⟩ → ⟨ iᴮ p ≤ᴮ b ⟩
below-out b p hp y hy =
  B-regular (fst b) (snd b) .fst y yc
    (star²-mono (cone (fst p)) (mem (fst b)) sub y yc (w .snd))
  where
    sub : cone (fst p) ⊑ mem (fst b)
    sub z hz k = B-down (fst b) (snd b) z (fst p) hz (snd p) k hp
    w : ⟨ (y ∈ˢ carrier) ⊓ coneΔ carrier order (fst p) y ⟩
    w = subst ⟨_⟩ (iSet-mem (fst p) y) hy
    yc : ⟨ y ∈ˢ carrier ⟩
    yc = w .fst

--------------------------------------------------------------------------------
-- The three remaining free fillers that mention below
--------------------------------------------------------------------------------

below-sub : (b : El) → ⟨ belowK b ⊆ˢ carrier ⟩
below-sub b = B-sub (fst b) (snd b)

below-regular : (b : El) (p : Cond)
              → ⟨ denseBelowᴵ (fst p) (belowK b) ⟩ → ⟨ iᴮ p ≤ᴮ b ⟩
below-regular b p db =
  below-out b p (denseBelow→mem (fst b) (snd b) (fst p) (snd p) db)

i-nonzero : (p : Cond) → (iᴮ p ≡ ⊥ᴮ) → ⟨ ⊥ ⟩
i-nonzero p = positive→nonzero (iᴮ p) (i-pos p)
