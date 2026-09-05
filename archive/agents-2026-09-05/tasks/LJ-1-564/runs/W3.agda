{-# OPTIONS --cubical --safe --guardedness #-}

-- [LJ-1.564]  W3, THE WIDEST UNMEASURED TERM, WRITTEN FIRST AND ALONE.
--
-- The brief names it:  "whether `InjCode` can even be stated with
-- `𝒫 κ` as its source", written as
--
--     -- InjCode F (𝒫 κ) δ, at this frame, TYPE ONLY, no inhabitant
--
-- `[LJ-1.546]` asked the same question for the other direction.  This
-- file is TYPE ONLY: no inhabitant, no hole, no postulate.  It exits 0,
-- so the number it costs is comparable with a full run of the same
-- import set.

open import Base.Prelude
open import Base.Truth
open import Base.Classical using ( LEM )

module LJ-1-564.runs.W3 {ℓ : Level} (lem : LEM (ℓ-suc ℓ)) where

open import FOL.ZFStructure using ( module hPropStructure )
open import V.Hierarchy {ℓ} using ( 𝒮ᵥ )
open import L.Constructible {ℓ} using ( 𝒮ʟ )
open import L.Cardinal {ℓ} lem using ( InjCode )
open import L.GCH {ℓ} lem using ( SuccCardL; InjL )
import FOL.ZFModel

module SL = hPropStructure 𝒮ʟ
module ModelL = FOL.ZFModel 𝒮ʟ

-- THE QUESTION, TYPE ONLY.  `InjCode : S → S → S → Type (ℓ-suc ℓ)`
-- (src/L/Cardinal.lagda.md:223) and `𝒫 : S → S`
-- (src/FOL/ZFModel.lagda.md:287), both at the SAME `S`, the L-carrier's
-- (src/L/GCH.lagda.md:27 opens `hPropStructure 𝒮ʟ using ( S )`).  So
-- the source slot accepts `𝒫 κ` with no coercion and no side condition.
CodeAtPower : ModelL.isZFModel → Type (ℓ-suc ℓ)
CodeAtPower zf = (κ δ F : SL.S) → InjCode F (𝒫 κ) δ
  where open ModelL.isZFModel zf using ( 𝒫 )

-- AND THE TARGET IT SERVES, TYPE ONLY.  `InjL a b` unfolds to the
-- truncated Σ over `InjCode` (src/L/GCH.lagda.md:38), so the obligation
-- of this task is the truncation of the above at some F.
PowerIntoSucc : ModelL.isZFModel → Type (ℓ-suc ℓ)
PowerIntoSucc zf =
    (κ δ : SL.S) → SuccCardL δ κ → InjL (𝒫 κ) δ
  where open ModelL.isZFModel zf using ( 𝒫 )
