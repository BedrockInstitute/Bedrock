{-# OPTIONS --cubical --safe --guardedness #-}

-- [LJ-1.541]  THE OBLIGATION'S TYPE, PINNED IN A SEPARATE MODULE.
--
-- The brief's type is
--
--   domAt-at-carve : (the domAt conjunct of InjCode, over the rank carve,
--                     with Q instantiated)
--
-- and all three of "the domAt conjunct", "the rank carve" and "with Q
-- instantiated" are prose.  `Obligation` below spells each one out and
-- uses NO name of Probe541:
--
--   * the conjunct is `⟨ (F ∷ a ∷ []) ⊨ domAt zero (suc zero) ⟩`, and
--     `is-the-second-conjunct` reads that very type out of `InjCode`
--     (src/L/Cardinal.lagda.md:223-228) so the reading cannot drift;
--   * the carve is `[LJ-1.529]`'s, written as its BODY
--     (Probe529.agda:150-154 at Probe529.agda:222-223) and not as
--     `P529.Carve.G`, because Probe541 section 4 measures that the name
--     is unreachable;
--   * `Q` is `[LJ-1.521]`'s witness (Probe521.agda:1162-1164), applied
--     here and not quantified.
--
-- `obligation-is-delivered` inhabits it by `P541.domAt-at-carve` and by
-- nothing else.  This is `[LJ-1.531]`'s device (runs/Pin.agda:30-38),
-- which `[LJ-1.537]` also used.

open import Base.Prelude
open import Base.Truth
open import Base.Classical using ( LEM )

module LJ-1-541.runs.PinBody {ℓ : Level} (lem : LEM (ℓ-suc ℓ)) where

open import FOL.ZFStructure using ( module hPropStructure )
import FOL.Absoluteness
open import V.Hierarchy {ℓ} using ( 𝒮ᵥ )
open import L.Constructible {ℓ} using ( 𝒮ʟ; isL; isL-trans; IsOrd )
open import L.Cardinal {ℓ} lem using ( InjCode )
open import L.Coding.Model {ℓ} using ( domAt )
open import Cubical.Data.FinData using ( Fin; zero; suc )

import LJ-1-521.Probe521 {ℓ} lem as P521
import LJ-1-529.Probe529 {ℓ} lem as P529
import LJ-1-541.Probe541 {ℓ} lem as P541

open TruthAlgebra (hPropAlgebra (ℓ-suc ℓ))
open hPropStructure 𝒮ʟ using ( S )

module AbsL = FOL.Absoluteness.Single 𝒮ᵥ isL isL-trans
open AbsL renaming ( _⊨ᵐ_ to _⊨_ )

Obligation : Type (ℓ-suc ℓ)
Obligation =
    (a : S) (oa : IsOrd (fst a))
  → ⟨ ( fst (P529.rank-graph (P521.ord-set-witness a oa .fst) a
                             (P529.Bound′.bnd a oa))
      ∷ a ∷ [] )
      ⊨ domAt zero (suc zero) ⟩

-- the type above is `InjCode`'s SECOND component and not another reading
-- of the words "the domAt conjunct".
is-the-second-conjunct :
    (F a b : S) → InjCode F a b → ⟨ (F ∷ a ∷ []) ⊨ domAt zero (suc zero) ⟩
is-the-second-conjunct F a b h = h .snd .fst

obligation-is-delivered : Obligation
obligation-is-delivered = P541.domAt-at-carve
