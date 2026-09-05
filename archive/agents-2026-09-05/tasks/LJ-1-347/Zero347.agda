{-# OPTIONS --cubical --safe --guardedness #-}

-- [LJ-1.347] THE CHEAPEST CONTROL FOR THE `m = 0` WALL (C-56).
--
-- `[LJ-1.344]` interrupted FOUR runs on one clause:
--
--   sgl1-not-numeral zero : pair (# 1) (# 1) = # 0 -> bottom
--
-- Route A (`Bisect344A.agda`) transports along `V.Model.empty-spec`,
-- which is an hProp PATH built by `to-path`.  Route D
-- (`Bisect344D.agda`) forces `regularityV (# 1)`, an accessibility
-- proof over the hierarchy HIT.  Both walled.
--
-- THE READING UNDER TEST.  The cost is NOT the numeral `# 0` and it is
-- NOT the subst.  `# zero = empty` is a DEFINING equation of the
-- library's `InfinitySet` module, so `# 0` is the empty set by
-- conversion and costs nothing.  The cost is in the CONSUMER that each
-- route puts after the subst: a path transport in one, an `Acc` in the
-- other.  C-56 says the cost of a walled proof is in the assembly.
--
-- ROUTE E, THE THIRD ROUTE.  The library already exports the refusal as
-- a FUNCTION:
--
--   empty-empty : < for-all b : V l . not (b in-s empty) >
--
-- at the cubical library's `CumulativeHierarchy/Constructions.agda:86`.
-- It is `SetPackage.classification` of the empty package, the SAME
-- constructor `pairing-ax` comes from, and `Bisect344B.agda` already
-- measures `pairing-ax` at 2.01 s through `pair-only`.  So route E
-- leaves the hProp never, transports nothing, and forces no `Acc`.
--
-- THIS FILE IS THE `m = 0` CLAUSE ALONE, with the SMALLEST import set
-- that can state it.  It imports NO Bedrock chapter, so its seconds
-- figure is the clause and not a chapter interface.
--
-- ONE agda process under GHCRTS="-A64m -I0 -M8g".

open import Cubical.Core.Primitives using ( Level; ℓ-suc )
open import Cubical.Foundations.Prelude using ( _≡_; subst; refl; fst; snd )
open import Cubical.Foundations.Structure using ( ⟨_⟩ )
open import Cubical.HITs.CumulativeHierarchy.Base using ( V; _∈_ )
open import Cubical.HITs.CumulativeHierarchy.Constructions
  using ( ⁅_,_⁆; ∅; ∅-empty; pairing-ax ) renaming ( module InfinitySet to Inf )
open Inf using ( #_ )
open import Cubical.HITs.CumulativeHierarchy.Properties using ( ∈∈ₛ )
open import Cubical.Data.Sum using ( inl )
import Cubical.Data.Empty as Empty
import Cubical.HITs.PropositionalTruncation as PT
open PT using ( ∣_∣₁ )

module LJ-1-347.Zero347 {ℓ : Level} where

-- The one ambient fact.  Four lines, copied from
-- agents/tasks/LJ-1-344/Supply344.agda:89-91, which copied them from
-- agents/tasks/LJ-1-302/ProbeLJ1302B.agda:105-108, because
-- src/V/Coding.lagda.md keeps `inl` access private.
x∈pair : (x y : V ℓ) → ⟨ x ∈ ⁅ x , y ⁆ ⟩
x∈pair x y =
  ∈∈ₛ {a = x} {b = ⁅ x , y ⁆} .snd (pairing-ax x y x .snd ∣ inl refl ∣₁)

-- THE CLAUSE THAT WALLED FOUR RUNS.
sgl1-not-zero : ⁅ # 1 , # 1 ⁆ ≡ # 0 → Empty.⊥
sgl1-not-zero q =
  ∅-empty (# 1)
    (∈∈ₛ {a = # 1} {b = ∅} .fst
      (subst (λ s → ⟨ (# 1) ∈ s ⟩) q (x∈pair (# 1) (# 1))))
