{-# OPTIONS --cubical --safe --guardedness #-}

-- [LJ-1.531]  THE OBLIGATION'S TYPE, PINNED IN A SEPARATE MODULE.
--
-- `Obligation` below is the brief's type transcribed, with one change
-- and no other: `rank-at′` is qualified `P521.`, which is what its name
-- is outside [LJ-1.521].  `obligation-is-delivered` inhabits it by
-- `P531.rank-at′-inj` and by nothing else, so it typechecks only if the
-- delivered term's type is DEFINITIONALLY the brief's.  This is
-- [LJ-1.529]'s `range-is-fourth-of-InjCode` device
-- (agents/tasks/LJ-1-529/Probe529.agda:190-191) turned on the brief
-- instead of on `InjCode`.

open import Base.Prelude
open import Base.Truth
open import Base.Classical using ( LEM )

module LJ-1-531.runs.Pin {ℓ : Level} (lem : LEM (ℓ-suc ℓ)) where

open import FOL.ZFStructure using ( module hPropStructure )
open import L.Constructible {ℓ} using ( 𝒮ʟ; IsOrd )
open import Cubical.HITs.CumulativeHierarchy.Base using ( _∈_ )

import LJ-1-521.Probe521 {ℓ} lem as P521
import LJ-1-531.Probe531 {ℓ} lem as P531

open TruthAlgebra (hPropAlgebra (ℓ-suc ℓ))
open hPropStructure 𝒮ʟ using ( S )

Obligation : Type (ℓ-suc ℓ)
Obligation =
    (a : S) (oa : IsOrd (fst a)) (m m' : S)
    (mx : ⟨ fst m ∈ fst a ⟩) (mx' : ⟨ fst m' ∈ fst a ⟩)
  → fst (P521.rank-at′ a oa m mx) ≡ fst (P521.rank-at′ a oa m' mx')
  → fst m ≡ fst m'

obligation-is-delivered : Obligation
obligation-is-delivered = P531.rank-at′-inj
