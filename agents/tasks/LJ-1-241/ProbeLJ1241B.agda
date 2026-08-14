{-# OPTIONS --cubical --safe --guardedness #-}

-- ProbeLJ1241B: verify the tag-slot trace that ProbeLJ1241A's numeral
-- pinning rests on.  The trace is
--     tag Nk ↦ levelHoodB slot (Nk - 1)
-- (the 28 LevelHood parameters are shifted +5 into DefBodyB, +3 into its
-- isCodeBS context, then back out through nine binders).  With Nk = 5 + k
-- the twelve tags therefore sit at the δ slots 4..15 of the arity-16
-- environment, and ProbeLJ1241A pins slot 4 + k to numeral k.
--
-- This file measures the trace two ways, both by a free-variable walk:
--   1. with N0..N11 = 5..16 and every other parameter zero, the
--      deduplicated free slots are exactly 0..15;
--   2. moving N0 from 5 to 6 drops slot 4 and only slot 4, so N0 is the
--      tag that occupies slot 4 (the order, not only the set).
--
-- ONE agda process under GHCRTS="-A64m -I0 -M8g".

open import Base.Prelude
open import Base.Classical using ( LEM )

module LJ-1-241.ProbeLJ1241B {ℓ : Level} (lem : LEM (ℓ-suc ℓ)) where

open import FOL.ZFStructure using ( module hPropStructure )
open import FOL.Syntax using
  ( Formula; Term; var; con; _∈̇_; _≐_; _∧̇_; _∨̇_; _⇒̇_; ¬̇_; ⊤̇; ⊥̇; ∃̇_; ∀̇_; ∀̇∈; ∃̇∈ )
import FOL.Count
open import L.Constructible {ℓ} using ( 𝒮ʟ )
open import L.BoundedSubset {ℓ} lem using ( module LevelHood )

open import Cubical.Data.Nat using ( ℕ; zero; suc; _+_ )
open import Cubical.Data.Nat.Properties using ( discreteℕ )
open import Cubical.Data.List using ( List; _∷_; [] ; _++_ )
open import Cubical.Data.FinData using ( toℕ )
open import Cubical.Data.Bool using ( Bool; true; false )
open import Cubical.Relation.Nullary using ( yes; no )
import Cubical.Data.Empty as Empty

module CS = hPropStructure 𝒮ʟ
module Cnt = FOL.Count.Count {ℓ = ℓ-suc ℓ} CS.S

fin-suc : (k : ℕ) → Fin (suc k)
fin-suc zero    = zero
fin-suc (suc k) = suc (fin-suc k)

inject+ : {m n : ℕ} → Fin m → Fin (m + n)
inject+ zero    = zero
inject+ (suc i) = suc (inject+ i)

-- N0..N11 = 5..16; t0 = t1 = M0..M11 = s0 = s1 = 0 (the non-N parameters
-- are zeroed so only the twelve tag numerals contribute beyond w v γ K).
module LH = LevelHood {12}
  (inject+ {6} {11} (fin-suc 5))   (inject+ {7} {10} (fin-suc 6))
  (inject+ {8} {9} (fin-suc 7))    (inject+ {9} {8} (fin-suc 8))
  (inject+ {10} {7} (fin-suc 9))   (inject+ {11} {6} (fin-suc 10))
  (inject+ {12} {5} (fin-suc 11))  (inject+ {13} {4} (fin-suc 12))
  (inject+ {14} {3} (fin-suc 13))  (inject+ {15} {2} (fin-suc 14))
  (inject+ {16} {1} (fin-suc 15))  (fin-suc 16)
  zero zero
  zero zero zero zero zero zero zero zero zero zero zero zero zero zero

-- the same, with N0 moved from 5 to 6 (so no tag sits at slot 4).
module LH' = LevelHood {12}
  (inject+ {7} {10} (fin-suc 6))   (inject+ {7} {10} (fin-suc 6))
  (inject+ {8} {9} (fin-suc 7))    (inject+ {9} {8} (fin-suc 8))
  (inject+ {10} {7} (fin-suc 9))   (inject+ {11} {6} (fin-suc 10))
  (inject+ {12} {5} (fin-suc 11))  (inject+ {13} {4} (fin-suc 12))
  (inject+ {14} {3} (fin-suc 13))  (inject+ {15} {2} (fin-suc 14))
  (inject+ {16} {1} (fin-suc 15))  (fin-suc 16)
  zero zero
  zero zero zero zero zero zero zero zero zero zero zero zero zero zero

base : Formula (⊥* {ℓ-suc ℓ}) 16
base = Cnt.erase LH.levelHoodB refl

base' : Formula (⊥* {ℓ-suc ℓ}) 16
base' = Cnt.erase LH'.levelHoodB refl

-- free-variable walk (de Bruijn: under a binder the non-zero slots shift
-- down by one and the zero slot drops).
freeTm : {n : ℕ} → Term (⊥* {ℓ-suc ℓ}) n → List ℕ
freeTm (var i) = toℕ i ∷ []
freeTm (con b) = Empty.rec* b

shift : List ℕ → List ℕ
shift [] = []
shift (0 ∷ xs) = shift xs
shift (suc n ∷ xs) = n ∷ shift xs

freeFo : {n : ℕ} → Formula (⊥* {ℓ-suc ℓ}) n → List ℕ
freeFo (t ∈̇ u)  = freeTm t ++ freeTm u
freeFo (t ≐ u)  = freeTm t ++ freeTm u
freeFo (φ ∧̇ ψ)  = freeFo φ ++ freeFo ψ
freeFo (φ ∨̇ ψ)  = freeFo φ ++ freeFo ψ
freeFo (φ ⇒̇ ψ)  = freeFo φ ++ freeFo ψ
freeFo (¬̇ φ)    = freeFo φ
freeFo ⊤̇        = []
freeFo ⊥̇        = []
freeFo (∃̇ φ)    = shift (freeFo φ)
freeFo (∀̇ φ)    = shift (freeFo φ)
freeFo (∀̇∈ t φ) = freeTm t ++ shift (freeFo φ)
freeFo (∃̇∈ t φ) = freeTm t ++ shift (freeFo φ)

has? : ℕ → List ℕ → Bool
has? n [] = false
has? n (x ∷ xs) with discreteℕ n x
... | yes _ = true
... | no  _ = has? n xs

dedup : List ℕ → List ℕ
dedup [] = []
dedup (x ∷ xs) with has? x xs
... | true  = dedup xs
... | false = x ∷ dedup xs

-- MEASUREMENT 1: with N0..N11 = 5..16 the twelve tags occupy the δ slots
-- 4..15 (and the structural w v γ K are 0..3); every one of 0..15 is free.
free : List ℕ
free = dedup (freeFo base)

freeCheck : free ≡
  (3 ∷ 1 ∷ 2 ∷ 5 ∷ 6 ∷ 7 ∷ 8 ∷ 9 ∷ 10 ∷ 11 ∷ 12 ∷ 13 ∷ 14 ∷ 15 ∷ 4 ∷ 0 ∷ [])
freeCheck = refl

-- MEASUREMENT 2: moving N0 from 5 to 6 drops slot 4 and only slot 4, so
-- N0 is the tag at slot 4 (the order, not only the set).
free' : List ℕ
free' = dedup (freeFo base')

freeCheck' : free' ≡
  (3 ∷ 1 ∷ 2 ∷ 6 ∷ 7 ∷ 8 ∷ 9 ∷ 10 ∷ 11 ∷ 12 ∷ 13 ∷ 14 ∷ 15 ∷ 5 ∷ 0 ∷ [])
freeCheck' = refl
