{-# OPTIONS --cubical --safe --guardedness #-}

-- K2 closure: the coded presentation of track F drives the certificate layer
-- of track G, so the two halves of K2 compose.
--
-- The two tracks each declare a record called Presentation and they differ.
-- Track F carries the order as a ground SET of Kuratowski pairs; track G
-- carries it as a host relation on points. Both stated their reason, and the
-- reasons do not conflict.
--
-- Track F's is a necessity argument. Separation reads a Formula S 1, and every
-- object of the construction table is a Separation whose formula takes the
-- order code as a constant slot, so with a host order there is no formula to
-- hand to Separation and the completion cannot be built at all.
--
-- Track G's is a decoupling argument, stated in its own file header: it
-- declares the record rather than importing it so that the coded presentation
-- can change without touching anything below, and it records that the decoded
-- forcing notion has exactly these five components and that the instantiation
-- is one record expression.
--
-- This file is that record expression, plus the theorem that makes it worth
-- writing: the two routes to a forcing notion, track G's notion applied to the
-- decoded presentation and track F's own decode, are the same notion. Without
-- that, the host structural vocabulary track G imports could have drifted from
-- the one track F's completeness statements are about.

open import Base.Prelude
open import Base.Truth
open import FOL.ZFStructure using ( ZFStructure )
import OrdinaryProfile

module K2Bridge
  {ℓ} (𝒮 : ZFStructure (hPropAlgebra ℓ))
  (ext : OrdinaryProfile.Extensionality 𝒮)
  (paths : (x y : ZFStructure.S 𝒮)
         → (ZFStructure._≈ˢ_ 𝒮 x y) ≡ ((x ≡ y) , ZFStructure.isSetS 𝒮 x y))
  where

open import FOL.ZFStructure using ( module hPropStructure )
import ForcingNotion as FN
import CodedCompletion
import Certificate

open TruthAlgebra (hPropAlgebra ℓ)
open hPropStructure 𝒮

module F = CodedCompletion 𝒮
module G = Certificate 𝒮 ext paths

-- The record expression track G's header predicts.
--
-- Written with the module opened rather than qualified, because track G
-- measured that a record declared inside a parameterized module takes the
-- enclosing parameters IMPLICITLY, so the qualified spelling does not
-- elaborate. That fact is reproduced here rather than taken on trust: the
-- first draft of this file used the qualified form and failed at exit 42 with
-- F.Presentation not being a ForcingLaws.

module Bridge (𝔓 : F.Presentation) (laws : F.Coded.ForcingLaws 𝔓) where

  open F.Coded 𝔓
  open ForcingLaws laws

  hostPresentation : G.Presentation
  hostPresentation = record
    { carrier   = carrier
    ; _≼_       = λ p q → fst p ≼ᴵ fst q
    ; ≼-refl    = λ p → ≼ᴵ-refl (fst p) (snd p)
    ; ≼-trans   = λ {p} {q} {r} h k →
                    ≼ᴵ-trans (fst p) (fst q) (fst r) (snd p) (snd q) (snd r) h k
    ; inhabited = inhabited
    }

  -- The theorem. Track G reaches the host structural vocabulary through its
  -- own notion; track F reaches it through decode. They agree, so
  -- compatibility, density, antichains, separativity and Bell's separative
  -- equality mean the same thing on both sides of K2, and no second
  -- definition of any of them is in play.

  bridge-agrees : G.notion hostPresentation ≡ decode laws
  bridge-agrees = refl
