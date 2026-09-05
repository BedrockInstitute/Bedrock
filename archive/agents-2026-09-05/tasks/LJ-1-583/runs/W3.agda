{-# OPTIONS --cubical --safe --guardedness #-}

-- [LJ-1.583] W3, ALONE, TYPECHECKED BEFORE ANY OTHER AGDA OF THIS TASK.
--
-- The brief's W3 is "the gap count itself", and it says the value is a
-- LIST rather than a type.  A list is not a term, so this file is W3's
-- SECOND half: the two module applications the list points at, applied
-- and NOT described.  If either fails to apply, the gap list is wrong
-- and everything after it is wasted.
--
-- The list, read at agents/tasks/LJ-1-576/Probe576.agda:327-382, is in
-- Probe583.agda section 1.  It names THREE gaps.  This file settles the
-- two that [LJ-1.576] said were constructions in src/.

open import Base.Prelude
open import Base.Truth
open import Base.Classical using ( LEM )

module LJ-1-583.runs.W3 {ℓ : Level} (lem : LEM (ℓ-suc ℓ)) where

open import FOL.ZFStructure using ( module hPropStructure )
open import L.Constructible {ℓ} using ( 𝒮ʟ )
open import L.Cardinal {ℓ} lem using ( InjCode )
open import L.GCH {ℓ} lem using ( InjL )
open import L.InjChain {ℓ} lem using ( module InclGraph; module Comp )

import Cubical.HITs.PropositionalTruncation as PT
open PT using ( ∣_∣₁; ∥_∥₁; squash₁ )

open TruthAlgebra (hPropAlgebra (ℓ-suc ℓ))
open hPropStructure 𝒮ʟ using ( S )

-- GAP A.  `IdCoded` (agents/tasks/LJ-1-576/Probe576.agda:421-422).
-- [LJ-1.576] wrote "`Carve` is hardwired to the shift formula `shiftFo`
-- ... so it does not serve".  THAT IS `L.Absorption`'s `Carve`
-- (src/L/Absorption.lagda.md:386, :413).  There is a SECOND module of
-- the same name, `L.InjChain.Carve` (src/L/InjChain.lagda.md:468),
-- hardwired to `inclFo` (:446, :480) instead, and `inclFo` IS the
-- identity graph's formula.  Its L instantiation is `InclGraph` (:575).
idCoded : (a : S) → InjL a a
idCoded a = ∣ IG.G , (IG.sv , IG.dm , IG.ij , IG.ran) ∣₁
  where
  module IG = InclGraph a a (λ _ z∈a → z∈a)

-- GAP C.  `CodedComp` (agents/tasks/LJ-1-576/Probe576.agda:394-395).
-- [LJ-1.576] measured "the tree has no such term" from
-- `grep -rn "comp-inj :" src/`, which finds the AMBIENT composites.
-- `L.InjChain.Comp` (src/L/InjChain.lagda.md:314-422) composes two
-- CODES by one separation and delivers the four conjuncts at
-- `γK = K ∷ D ∷ []` with `ranK` into C.  That is `InjCode K a c`.
codedComp : (a b c : S) → InjL a b → InjL b c → InjL a c
codedComp a b c =
  PT.rec (isPropΠ (λ _ → squash₁))
    (λ { (F , svF , dmF , ijF , ranF) →
      PT.map (λ { (H , svH , dmH , ijH , ranH) →
        let module K = Comp a b c F H svF dmF ijF ranF svH dmH ijH ranH
        in K.K , (K.svK , K.dmK , K.ijK , K.ranK) }) })
