{-# OPTIONS --cubical --safe --guardedness #-}

-- [LJ-1.336] SEAL PROBE, and it is EXPECTED TO FAIL.
--
-- `satGraphAt` is sealed `opaque` at src/L/Coding/Graph.lagda.md:203-205,
-- and the seal is a measurement, not a taste: the comment at :194-202
-- records 2,459 ms for one coercion with the seal open.  Wave 2's port
-- re-states the definition and keeps the seal, so the port holds a SECOND
-- opaque declaration of the same body.
--
-- Two opaque declarations do not convert, whatever their bodies say.  This
-- file states the `refl` that a naive replacement would need, so the
-- boundary is MEASURED rather than assumed.  `DefBody` inherits the
-- failure, because its body names `satGraphAt`.
--
-- A GREEN run here would REFUTE this report's section on the seal.
--
-- ONE agda process under GHCRTS="-A64m -I0 -M8g".

open import Base.Prelude
open import Base.Truth
open import Base.Classical using ( LEM )

module LJ-1-336.ProbeSeal336 {ℓ : Level} (lem : LEM (ℓ-suc ℓ)) where

open import FOL.ZFStructure using ( module hPropStructure )
open import FOL.Syntax using ( Formula )
open import V.Hierarchy {ℓ} using ( 𝒮ᵥ )
open import L.Constructible {ℓ} using ( 𝒮ʟ; isL; isL-trans )
open import L.Axioms.Numerals {ℓ}
  using ( numeralL; numeralL-fst; pairʟ; pairʟ-fst; sucʟ; sucʟ-fst )
open import L.Coding.Graph {ℓ} lem using ( satGraphAt )
open import L.Coding.Powerset {ℓ} lem using ( DefBody )
open import Cubical.Data.Nat using ( _+_ )

import LJ-1-336.GenDirty

open TruthAlgebra (hPropAlgebra (ℓ-suc ℓ))
open hPropStructure 𝒮ʟ

module Fam = LJ-1-336.GenDirty {ℓ} isL isL-trans
               numeralL numeralL-fst pairʟ pairʟ-fst sucʟ sucʟ-fst

chk-satGraphAt : ∀ {n : ℕ} (B x y : Fin n)
               → Fam.satGraphAt B x y ≡ satGraphAt B x y
chk-satGraphAt B x y = refl

chk-DefBody : ∀ {n : ℕ} (w : Fin n)
            → Fam.DefBody w ≡ DefBody w
chk-DefBody w = refl
