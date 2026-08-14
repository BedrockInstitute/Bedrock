{-# OPTIONS --cubical --safe --guardedness #-}

-- ProbeLJ1241A: build φ₀ : Formula (⊥*) 2 from erase levelHoodB plus the
-- twelve numeral definitions, and typecheck φ₀ := ⊤̇.
--
--   SECTION 1  the numeral primitives (constant-free, over ⊥*):
--              isZeroAt, sucAt, numAt
--   SECTION 2  erase levelHoodB at a correct n, and the renaming that
--              keeps v and γ and closes everything else
--   SECTION 3  φ₀ (the real formula) and φ₀⊤ (the ⊤̇ inhabitant)
--
-- DD4: the numeral primitives and the closure helper are tower-free; they
-- name no L-tower operation, only the FOL syntax.
--
-- ONE agda process under GHCRTS="-A64m -I0 -M8g".  Tracked, never
-- deleted, and it lives beside its report.

open import Base.Prelude
open import Base.Classical using ( LEM )

module LJ-1-241.ProbeLJ1241A {ℓ : Level} (lem : LEM (ℓ-suc ℓ)) where

open import FOL.ZFStructure using ( module hPropStructure )
open import FOL.Syntax using
  ( Formula; Term; var; _∈̇_; _≐_; _∧̇_; _∨̇_; ⊤̇; ⊥̇; ∃̇_; ∀̇∈ )
open import FOL.Manipulation.Parameters using ( countFo )
open import FOL.Manipulation.Renaming using ( renameFo )
import FOL.Count
open import L.Constructible {ℓ} using ( 𝒮ʟ )
open import L.BoundedSubset {ℓ} lem using ( module LevelHood )

open import Cubical.Data.Nat using ( ℕ; zero; suc; _+_ )

module CS = hPropStructure 𝒮ʟ

module Cnt = FOL.Count.Count {ℓ = ℓ-suc ℓ} CS.S

-- a literal Fin value: k as Fin (suc k).
fin-suc : (k : ℕ) → Fin (suc k)
fin-suc zero    = zero
fin-suc (suc k) = suc (fin-suc k)

-- weaken a Fin by appending n slots.
inject+ : {m n : ℕ} → Fin m → Fin (m + n)
inject+ zero    = zero
inject+ (suc i) = suc (inject+ i)

-- =====================================================================
-- SECTION 1: THE NUMERAL PRIMITIVES.
--
-- The finite ordinal k is pinned inside a constant-free formula: zero is
-- "no members", successor is the two-inclusion atom.  All three are
-- constant-free, so they live over ⊥* and read at any carrier via embed.
-- =====================================================================

-- "slot i has no members" (the ordinal 0).
isZeroAt : {n : ℕ} → Fin n → Formula (⊥* {ℓ-suc ℓ}) n
isZeroAt i = ∀̇∈ (var i) ⊥̇

-- "slot k is the successor of slot a" (k = suc a).
sucAt : {n : ℕ} → Fin n → Fin n → Formula (⊥* {ℓ-suc ℓ}) n
sucAt k a =
    (var a ∈̇ var k)
  ∧̇ (∀̇∈ (var a) (var zero ∈̇ var (suc k)))
  ∧̇ (∀̇∈ (var k) ((var zero ∈̇ var (suc a)) ∨̇ (var zero ≐ var (suc a))))

-- "slot i is the finite ordinal k": nested successors over one witness.
numAt : {n : ℕ} → Fin n → ℕ → Formula (⊥* {ℓ-suc ℓ}) n
numAt i zero    = isZeroAt i
numAt i (suc k) = ∃̇ (sucAt (suc i) zero ∧̇ numAt zero k)

-- =====================================================================
-- SECTION 2: erase levelHoodB at a correct n, and the closure renaming.
--
-- LevelHood is instantiated at n = 12.  The twelve tag numerals N0..N11
-- are the slots 5..16 of Fin (5 + 12); the trace
--   tag Nk ↦ levelHoodB slot (Nk - 1)
-- (the 28 LevelHood parameters are shifted by +5 into DefBodyB, by +3
-- into its isCodeBS context, then back out through nine binders) places
-- them at the δ slots 4..15 of the arity-16 environment.  The remaining
-- parameters (t0, t1, M0..M11, s0, s1) are witnesses and are bound
-- without a numeral pin; pinning them is the fifth step, not this one.
-- =====================================================================

module LH = LevelHood {12}
  (inject+ {6} {11} (fin-suc 5))   (inject+ {7} {10} (fin-suc 6))
  (inject+ {8} {9} (fin-suc 7))    (inject+ {9} {8} (fin-suc 8))
  (inject+ {10} {7} (fin-suc 9))   (inject+ {11} {6} (fin-suc 10))
  (inject+ {12} {5} (fin-suc 11))  (inject+ {13} {4} (fin-suc 12))
  (inject+ {14} {3} (fin-suc 13))  (inject+ {15} {2} (fin-suc 14))
  (inject+ {16} {1} (fin-suc 15))  (fin-suc 16)
  zero zero
  (inject+ {6} {13} (fin-suc 5))   (inject+ {7} {12} (fin-suc 6))
  (inject+ {8} {11} (fin-suc 7))   (inject+ {9} {10} (fin-suc 8))
  (inject+ {10} {9} (fin-suc 9))   (inject+ {11} {8} (fin-suc 10))
  (inject+ {12} {7} (fin-suc 11))  (inject+ {13} {6} (fin-suc 12))
  (inject+ {14} {5} (fin-suc 13))  (inject+ {15} {4} (fin-suc 14))
  (inject+ {16} {3} (fin-suc 15))  (inject+ {17} {2} (fin-suc 16))
  zero zero

-- the constant-free matrix, arity 4 + 12 = 16 (erase preserves arity).
base : Formula (⊥* {ℓ-suc ℓ}) 16
base = Cnt.erase LH.levelHoodB refl

-- the closure renaming: w ↦ 0, K ↦ 1, δᵢ ↦ 2 + i, then v ↦ 14, γ ↦ 15.
ρ : Fin 16 → Fin 16
ρ zero                      = zero
ρ (suc zero)                = inject+ {15} {1} (fin-suc 14)   -- v → 14
ρ (suc (suc zero))          = fin-suc 15                       -- γ → 15
ρ (suc (suc (suc zero)))    = suc zero                         -- K → 1
ρ (suc (suc (suc (suc i)))) = inject+ {14} {2} (suc (suc i))   -- δᵢ → 2 + i

renamed : Formula (⊥* {ℓ-suc ℓ}) 16
renamed = renameFo ρ base

-- =====================================================================
-- SECTION 3: φ₀.
--
-- The twelve tags δ₀..δ₁₁ (renamed slots 2..13) are pinned to the twelve
-- numerals 0..11, and the head 14 slots (w, K, and the twelve δ's) are
-- existentially closed, leaving v and γ free.
-- =====================================================================

pins : Formula (⊥* {ℓ-suc ℓ}) 16
pins =
    numAt (inject+ {3} {13} (fin-suc 2)) 0
  ∧̇ numAt (inject+ {4} {12} (fin-suc 3)) 1
  ∧̇ numAt (inject+ {5} {11} (fin-suc 4)) 2
  ∧̇ numAt (inject+ {6} {10} (fin-suc 5)) 3
  ∧̇ numAt (inject+ {7} {9} (fin-suc 6)) 4
  ∧̇ numAt (inject+ {8} {8} (fin-suc 7)) 5
  ∧̇ numAt (inject+ {9} {7} (fin-suc 8)) 6
  ∧̇ numAt (inject+ {10} {6} (fin-suc 9)) 7
  ∧̇ numAt (inject+ {11} {5} (fin-suc 10)) 8
  ∧̇ numAt (inject+ {12} {4} (fin-suc 11)) 9
  ∧̇ numAt (inject+ {13} {3} (fin-suc 12)) 10
  ∧̇ numAt (inject+ {14} {2} (fin-suc 13)) 11

-- close the head k slots by k nested existentials.
closeN : {n : ℕ} → (k : ℕ) → Formula (⊥* {ℓ-suc ℓ}) (k + n) → Formula (⊥* {ℓ-suc ℓ}) n
closeN zero    φ = φ
closeN (suc k) φ = closeN k (∃̇ φ)

-- THE REAL φ₀, arity two.
φ₀ : Formula (⊥* {ℓ-suc ℓ}) 2
φ₀ = closeN 14 (pins ∧̇ renamed)

-- The ⊤̇ inhabitant of the same type (φ₀ := ⊤̇), the second deliverable.
φ₀⊤ : Formula (⊥* {ℓ-suc ℓ}) 2
φ₀⊤ = ⊤̇
