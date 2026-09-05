{-# OPTIONS --cubical --safe --guardedness #-}

-- [LJ-1.744-SPLIT] FLOOR.  The frame of Probe744Split without the
-- obligation: the exact import block of Probe744.agda and the erased
-- leaf AppC / countAppC / App, nothing else.  Prices what the frame
-- itself costs before the transcribed term is attempted (owner's
-- ruling 2026-08-23: measure the floor, trim the imports, then prove).

open import Base.Prelude
open import Base.Truth
open import Base.Classical using ( LEM )

module LJ-1-744-SPLIT.runs.Floor744Split {ℓ : Level} (lem : LEM (ℓ-suc ℓ)) where

open import FOL.ZFStructure using ( module hPropStructure )
open import FOL.Syntax using ( Formula )
open import FOL.Manipulation.Parameters using ( countFo )
open import L.Coding.Model {ℓ} using ( appAt )
open import V.Hierarchy {ℓ} using ( 𝒮ᵥ )
open import Cubical.Data.Vec using ( _∷_; [] )
import Cubical.Data.Empty as Empty
import Cubical.HITs.PropositionalTruncation as PT
open import LJ-1-652.Probe652 {ℓ} lem as P652
open import V.Model {ℓ} using ( empty-spec )
open import LJ-1-732.runs.Num {ℓ} lem
open import LJ-1-732.runs.Amb1 {ℓ} lem
open import LJ-1-732.runs.Amb7a {ℓ} lem

open TruthAlgebra (hPropAlgebra (ℓ-suc ℓ))
open hPropStructure 𝒮ᵥ

AppC : Formula CS.S 18
AppC = appAt (suc (suc zero)) (suc zero) zero

countAppC : countFo AppC ≡ 0
countAppC = refl

App : Formula (⊥* {ℓ-suc ℓ}) 18
App = CntS.erase AppC countAppC
