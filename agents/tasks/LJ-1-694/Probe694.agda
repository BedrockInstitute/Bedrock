{-# OPTIONS --cubical --safe --guardedness #-}

-- [LJ-1.694] PROBE.  Is PowIter's finite iterate served by the
-- Describes families already paid.
-- It runs in agents/tasks/LJ-1-694/ and lands nothing in src/.
--
-- THE OBLIGATION the brief names is iterate-from-families: either
-- PowIter from the four paid families, or the name of the family
-- that is missing.  This file does NOT close PowIter.  It NAMES the
-- missing family: the three-element ordinal sucV³ ∅, which the
-- finite iterate from ∅ reaches at Lset (sucV⁴ ∅), and which is
-- not empty, not a singleton and not a pair.
--
-- WHAT IS SETTLED.
--   1. not-sgl (W2): a set with two distinct members is not a
--      singleton.
--   2. not-pair (W2): a set with three distinct members is not a
--      pair.  The pigeonhole is the eight cases of three bits.
--   3. n3 = sucV³ ∅ has three distinct members ∅, sucV ∅ and
--      sucV² ∅.
--   4. n3 ∈ Lset (sucV n3), by the tree's ord∈Lset-suc
--      (src/L/Ordinal/Stages.lagda.md:434).  Not rewritten (W2).
--   5. iterate-from-families: those three facts, as one term.
--
-- WHAT IS NOT SETTLED.
--   Describes at n3.  PowIter as a closed term.  The n-element
--   family for n ≥ 4.  Infinite members (a later stage than the
--   finite iterate from ∅).  A Formula Code 1 for 𝒟ₒ.
--
-- Nothing is postulated.  Nothing is holed.  Nothing lands in src/.
-- ONE Agda process per run, GHCRTS="-A64m -I0 -M2g", the wide caliber,
-- set on the pane by the program and untouched here.

open import Base.Prelude
open import Base.Truth
open import Base.Classical using ( LEM )

module LJ-1-694.Probe694 {ℓ : Level} (lem : LEM (ℓ-suc ℓ)) where

open import FOL.ZFStructure using ( module hPropStructure )
open import V.Hierarchy {ℓ} using ( 𝒮ᵥ )
open import V.Model {ℓ} using ( ∈sucV-elim; self∈sucV; ∈sucV-inl )
open import L.Constructible {ℓ} using ( Lset; IsOrd )
open import L.Ordinal {ℓ} using ( ∅-ord; suc-ord )
open import L.Ordinal.Stages {ℓ} lem using ( ord∈Lset-suc )

open import Cubical.Data.Sigma using ( _×_; _,_ )
open import Cubical.Data.Sum using ( _⊎_; inl; inr )
import Cubical.Data.Empty as Empty
import Cubical.HITs.PropositionalTruncation as PT
open PT using ( ∥_∥₁ )
open import Cubical.HITs.CumulativeHierarchy.Base using ( setIsSet )
open import Cubical.HITs.CumulativeHierarchy.Properties
  using ( _∈ₛ_; ∈∈ₛ )
open import Cubical.HITs.CumulativeHierarchy.Constructions
  using ( ∅; ∅-empty; ⁅_,_⁆; ⁅_⁆s; pairing-ax
        ; SingletonPackage; SetPackage  -- lint-agda: keep (SetPackage via record projection)
        ; module InfinitySet )
open InfinitySet using ( sucV )

open TruthAlgebra (hPropAlgebra (ℓ-suc ℓ))
open hPropStructure 𝒮ᵥ

-- =====================================================================
-- D-10.  THE THREE-ELEMENT FAMILY.
--
-- The four paid families cover a stage, a singleton and a pair.
-- A set with three distinct members is none of those.  The finite
-- iterate from ∅ reaches such a set: the ordinal sucV³ ∅ sits in
-- the stage after itself.
-- =====================================================================

∈sgl : {a z : S} → ⟨ z ∈ˢ ⁅ a ⁆s ⟩ → z ≡ a
∈sgl {a} {z} h =
  SetPackage.classification (SingletonPackage a) z .fst
    (∈∈ₛ {a = z} {b = ⁅ a ⁆s} .fst h)

-- W2: two distinct members kill the singleton family.
not-sgl :
    (y a b : S)
  → ⟨ a ∈ˢ y ⟩ → ⟨ b ∈ˢ y ⟩
  → (a ≡ b → Empty.⊥)
  → (u : S) → y ≡ ⁅ u ⁆s → Empty.⊥
not-sgl y a b a∈ b∈ a≢b u e =
  a≢b (a≡u ∙ sym b≡u)
  where
  a≡u : a ≡ u
  a≡u = ∈sgl (subst (λ w → ⟨ a ∈ˢ w ⟩) e a∈)
  b≡u : b ≡ u
  b≡u = ∈sgl (subst (λ w → ⟨ b ∈ˢ w ⟩) e b∈)

pair-mem : (u v z : S) → ⟨ z ∈ˢ ⁅ u , v ⁆ ⟩ → ∥ (z ≡ u) ⊎ (z ≡ v) ∥₁
pair-mem u v z h = pairing-ax u v z .fst
  (∈∈ₛ {a = z} {b = ⁅ u , v ⁆} .fst h)

-- W2: three distinct members kill the pair family.  Every assignment
-- of three bits to two holes collides.
not-pair :
    (y a b c : S)
  → ⟨ a ∈ˢ y ⟩ → ⟨ b ∈ˢ y ⟩ → ⟨ c ∈ˢ y ⟩
  → (a ≡ b → Empty.⊥) → (a ≡ c → Empty.⊥) → (b ≡ c → Empty.⊥)
  → (u v : S) → y ≡ ⁅ u , v ⁆ → Empty.⊥
not-pair y a b c a∈ b∈ c∈ a≢b a≢c b≢c u v e =
  PT.rec Empty.isProp⊥ (λ da →
    PT.rec Empty.isProp⊥ (λ db →
      PT.rec Empty.isProp⊥ (λ dc → clash da db dc)
        (pair-mem u v c (subst (λ w → ⟨ c ∈ˢ w ⟩) e c∈)))
      (pair-mem u v b (subst (λ w → ⟨ b ∈ˢ w ⟩) e b∈)))
    (pair-mem u v a (subst (λ w → ⟨ a ∈ˢ w ⟩) e a∈))
  where
  clash : (a ≡ u) ⊎ (a ≡ v)
        → (b ≡ u) ⊎ (b ≡ v)
        → (c ≡ u) ⊎ (c ≡ v)
        → Empty.⊥
  clash (inl au) (inl bu) _       = a≢b (au ∙ sym bu)
  clash (inr av) (inr bv) _       = a≢b (av ∙ sym bv)
  clash (inl au) (inr _)  (inl cu) = a≢c (au ∙ sym cu)
  clash (inr av) (inl _)  (inr cv) = a≢c (av ∙ sym cv)
  clash (inl _)  (inr bv) (inr cv) = b≢c (bv ∙ sym cv)
  clash (inr _)  (inl bu) (inl cu) = b≢c (bu ∙ sym cu)

-- The witness.  Named first so the obligation type does not mention
-- a nested sucV chain (P-l).
n0 n1 n2 n3 : S
n0 = ∅
n1 = sucV n0
n2 = sucV n1
n3 = sucV n2

n3-ord : IsOrd n3
n3-ord = suc-ord (suc-ord (suc-ord ∅-ord))

n0∈n1 : ⟨ n0 ∈ˢ n1 ⟩
n0∈n1 = self∈sucV n0

n0∈n2 : ⟨ n0 ∈ˢ n2 ⟩
n0∈n2 = ∈sucV-inl n0∈n1

n0∈n3 : ⟨ n0 ∈ˢ n3 ⟩
n0∈n3 = ∈sucV-inl n0∈n2

n1∈n2 : ⟨ n1 ∈ˢ n2 ⟩
n1∈n2 = self∈sucV n1

n1∈n3 : ⟨ n1 ∈ˢ n3 ⟩
n1∈n3 = ∈sucV-inl n1∈n2

n2∈n3 : ⟨ n2 ∈ˢ n3 ⟩
n2∈n3 = self∈sucV n2

n0≢n1 : n0 ≡ n1 → Empty.⊥
n0≢n1 e = ∅-empty n0
  (∈∈ₛ {a = n0} {b = n0} .fst
    (subst (λ w → ⟨ n0 ∈ˢ w ⟩) (sym e) n0∈n1))

n0≢n2 : n0 ≡ n2 → Empty.⊥
n0≢n2 e = ∅-empty n0
  (∈∈ₛ {a = n0} {b = n0} .fst
    (subst (λ w → ⟨ n0 ∈ˢ w ⟩) (sym e) n0∈n2))

n1≢n2 : n1 ≡ n2 → Empty.⊥
n1≢n2 e = n0≢n1 (sym n1≡n0)
  where
  n1∈n1 : ⟨ n1 ∈ˢ n1 ⟩
  n1∈n1 = subst (λ w → ⟨ n1 ∈ˢ w ⟩) (sym e) n1∈n2
  n1≡n0 : n1 ≡ n0
  n1≡n0 = ∈sucV-elim (setIsSet n1 n0) n1∈n1
    (λ n1∈n0 → Empty.rec (∅-empty n1 (∈∈ₛ {a = n1} {b = n0} .fst n1∈n0)))
    (λ p → p)

-- THE OBLIGATION.  The missing family, named: a three-element
-- member the finite iterate reaches, which is not a singleton and
-- not a pair.  Describes at this member is not inhabited here.
iterate-from-families :
    ⟨ n3 ∈ˢ Lset (sucV n3) ⟩
  × ((u : S) → n3 ≡ ⁅ u ⁆s → Empty.⊥)
  × ((u v : S) → n3 ≡ ⁅ u , v ⁆ → Empty.⊥)
iterate-from-families =
    ord∈Lset-suc n3 n3-ord
  , not-sgl n3 n0 n1 n0∈n3 n1∈n3 n0≢n1
  , not-pair n3 n0 n1 n2 n0∈n3 n1∈n3 n2∈n3 n0≢n1 n0≢n2 n1≢n2
