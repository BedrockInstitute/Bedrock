{-# OPTIONS --cubical --safe --guardedness #-}

-- K5 Track I, PROBE. NOT a deliverable. One scope question, answered by the
-- typechecker rather than by reading the language manual.
--
-- CodedCompletion.Core opens Coded 𝔓 at CodedCompletion.agda:265 WITHOUT
-- `public`, so carrier, order, Cond and _≼ᴵ_ are in scope inside Core and are
-- not re-exported by it. A consumer that reaches Core through K4's instance
-- file therefore cannot write CO.carrier and needs the second, LIGHT
-- application CodedCompletion.Coded 𝒮 𝔓 for the presentation vocabulary.
-- This file asserts the positive half; the negative half is the commented
-- line, which fails with [NotInScope] when uncommented.

open import Base.Prelude
open import Base.Truth
open import FOL.ZFStructure using ( ZFStructure )
import OrdinaryProfile
import CodedCompletion
import K4.InstanceCoded

module K5.ProbeI5
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
open TruthAlgebra (hPropAlgebra ℓ)
open hPropStructure 𝒮

module IC = K4.InstanceCoded 𝒮 ext pow sep paths 𝔓 laws
module CO = IC.CO
module CD = CodedCompletion.Coded 𝒮 𝔓

-- Reachable through the instance file: Core's own definitions.

reachable : S
reachable = CO.B

-- Reachable only through the light application: the presentation's own.

alsoReachable : S
alsoReachable = CD.carrier

-- NOT reachable: uncommenting this gives
--   error: [NotInScope] Not in scope: CO.carrier
-- unreachable : S
-- unreachable = CO.carrier
