{-# OPTIONS --cubical --safe --guardedness #-}

-- [LJ-1.732] runs/Num.  The frame-free facts of the empty-instance
-- probe, checked as their own module so each Agda process on this
-- pane stays under the watchdog's window (see lj-1.732-report.md,
-- section 4).  The content is the probe's own: the von Neumann
-- numerals as sucV-iterates, the transitive bound n 12 and its
-- members, the no-members fact for Lset of the empty ordinal, and
-- the successor-pin shape.  Nothing is postulated.

open import Base.Prelude
open import Base.Truth
open import Base.Classical using ( LEM )

module LJ-1-732.runs.Num {ℓ : Level} (lem : LEM (ℓ-suc ℓ)) where

open import FOL.ZFStructure using ( module hPropStructure )
open import V.Hierarchy {ℓ} using ( 𝒮ᵥ )
open import L.Constructible {ℓ} using ( IsOrd; Lset; Lset-out )
open import L.Ordinal {ℓ} using ( ∅-ord; suc-ord )
open import L.Ordinal.Stages {ℓ} lem using ( Lset-cumul; ord∈Lset-suc )
open import Cubical.Data.Nat using ( ℕ; _+_ )
open import Cubical.Data.Sum using ( _⊎_; inl; inr )
import Cubical.Data.Empty as Empty
import Cubical.HITs.PropositionalTruncation as PT
open PT using ( ∥_∥₁; ∣_∣₁; squash₁ )
open import Cubical.Data.Sigma using ( _×_ )
open import Cubical.HITs.CumulativeHierarchy.Constructions
  using ( ∅; ∅-empty; module InfinitySet )
open InfinitySet using ( sucV )
open import Cubical.HITs.CumulativeHierarchy.Properties
  using ( extensionality; ∈∈ₛ )
open import V.Model {ℓ} using ( empty-spec; self∈sucV; ∈sucV-inl; ∈sucV-elim )

open TruthAlgebra (hPropAlgebra (ℓ-suc ℓ))
open hPropStructure 𝒮ᵥ

-- =====================================================================
-- THE FINITE BOUND.  n k is the k-th von Neumann numeral written as a
-- pure sucV-iterate, so every successor equation is definitional and
-- no library numeral bridge is needed.  Z := n 12 is the witness
-- bound: transitive, carrying the twelve numerals, and a member of
-- every stage this frame names.
-- =====================================================================

n : ℕ → S
n zero    = ∅
n (suc k) = sucV (n k)

ordn : (k : ℕ) → IsOrd (n k)
ordn zero    = ∅-ord
ordn (suc k) = suc-ord (ordn k)

trZ : ∀ {x y : S} → y ∈ᵗ x → x ∈ᵗ n 12 → y ∈ᵗ n 12
trZ = fst (ordn 12)

nin : (d k : ℕ) → ⟨ n k ∈ˢ n (suc (d + k)) ⟩
nin zero    k = self∈sucV (n k)
nin (suc d) k = ∈sucV-inl (nin d k)

-- the twelve tag witnesses, all members of Z
mem11 : ⟨ n 11 ∈ˢ n 12 ⟩
mem11 = nin 0 11
mem10 : ⟨ n 10 ∈ˢ n 12 ⟩
mem10 = nin 1 10
mem9 : ⟨ n 9 ∈ˢ n 12 ⟩
mem9 = nin 2 9
mem8 : ⟨ n 8 ∈ˢ n 12 ⟩
mem8 = nin 3 8
mem7 : ⟨ n 7 ∈ˢ n 12 ⟩
mem7 = nin 4 7
mem6 : ⟨ n 6 ∈ˢ n 12 ⟩
mem6 = nin 5 6
mem5 : ⟨ n 5 ∈ˢ n 12 ⟩
mem5 = nin 6 5
mem4 : ⟨ n 4 ∈ˢ n 12 ⟩
mem4 = nin 7 4
mem3 : ⟨ n 3 ∈ˢ n 12 ⟩
mem3 = nin 8 3
mem2 : ⟨ n 2 ∈ˢ n 12 ⟩
mem2 = nin 9 2
mem1 : ⟨ n 1 ∈ˢ n 12 ⟩
mem1 = nin 10 1
mem0 : ⟨ n 0 ∈ˢ n 12 ⟩
mem0 = nin 11 0

-- Lset of the empty ordinal has no members: a member would cost an
-- index inside the empty ordinal.
Lset∅-empty : (x : S) → ⟨ x ∈ˢ Lset ∅ ⟩ → Empty.⊥* {ℓ-suc ℓ}
Lset∅-empty x h =
  PT.rec Empty.isProp⊥*
    (λ { (δ , δ∈∅ , _) → subst ⟨_⟩ (empty-spec δ) δ∈∅ })
    (Lset-out ∅ x h)

∅≡Lset∅ : ∅ ≡ Lset ∅
∅≡Lset∅ =
  extensionality ∅ (Lset ∅)
    ( (λ z h → Empty.rec (∅-empty z h))
    , (λ z h → Empty.rec* (Lset∅-empty z (∈∈ₛ {a = z} {b = Lset ∅} .snd h))) )

-- the successor-pin shape: the reading of one sucAt conjunct at a
-- numeral pair, stated at the carrier level so no erased subformula
-- has to be named
sucPin :
    (a : S)
    → ( ⟨ a ∈ˢ sucV a ⟩
      × ( (x : S) → ⟨ x ∈ˢ a ⟩ → ⟨ x ∈ˢ sucV a ⟩ )
      × ( (x : S) → ⟨ x ∈ˢ sucV a ⟩ → ∥ ⟨ x ∈ˢ a ⟩ ⊎ (x ≡ a) ∥₁ ) )
sucPin a =
    self∈sucV a
  , (λ x h → ∈sucV-inl h)
  , (λ x h → ∈sucV-elim {A = a} {x = x} {P = ∥ ⟨ x ∈ˢ a ⟩ ⊎ (x ≡ a) ∥₁}
        squash₁ h (λ hh → ∣ inl hh ∣₁) (λ q → ∣ inr q ∣₁))
