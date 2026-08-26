{-# OPTIONS --cubical --safe --guardedness #-}

-- [LJ-1.678] W3.  WHETHER A LIMIT ABOVE THE APPROXIMATION CARRIES
-- SUC-CLOSURE.  Probe-local ω-block: same mathematics as
-- src/L/Ordinal/StageArith.lagda.md:34-78, with the out-lemma
-- exported.  The live +ω is sealed and has no out-lemma
-- (StageArith.lagda.md:39-42).  suc∈or≡ is the tree's own
-- successor-inclusion (src/L/Ordinal/Stages.lagda.md:137-144).
--
-- ONE Agda process, GHCRTS from the pane, never set here.

open import Base.Prelude
open import Base.Truth
open import Base.Classical using ( LEM )

module LJ-1-678.runs.W3 {ℓ : Level} (lem : LEM (ℓ-suc ℓ)) where

open import FOL.ZFStructure using ( module hPropStructure )
open import V.Hierarchy {ℓ} using ( 𝒮ᵥ )
open import V.Model {ℓ} using ( ∈sucV-elim; ∈sucV-inl; self∈sucV )
open import L.Constructible {ℓ} using ( IsOrd )
open import L.Ordinal {ℓ} using ( suc-ord; setUnion-ord; mem-ord; ∅-ord )
open import L.Ordinal.Linear {ℓ} lem using ( ord-tri )
open import L.Ordinal.Stages {ℓ} lem using ( suc∈or≡ )
open import L.Ordinal.StageArith {ℓ} lem using ( sucIter )

open import Cubical.Data.Sum as Sum using ( _⊎_; inl; inr )
import Cubical.Data.Empty as Empty
import Cubical.HITs.PropositionalTruncation as PT
open PT using ( ∣_∣₁; ∥_∥₁; squash₁ )
open import Cubical.HITs.CumulativeHierarchy.Base using ( sett; V; _∈_ )
open import Cubical.HITs.CumulativeHierarchy.Properties using ( _∈ₛ_; ∈∈ₛ )
open import Cubical.HITs.CumulativeHierarchy.Constructions
  using ( ∅; ∅-empty; ⋃_; union-ax; module InfinitySet )
open InfinitySet using ( sucV )

open TruthAlgebra (hPropAlgebra (ℓ-suc ℓ))
open hPropStructure 𝒮ᵥ

-- The finite-iterate family whose union is the ω-block.
F : S → Lift {ℓ-zero} {ℓ} ℕ → S
F u m = sucIter (suc (lower m)) u

sucIter-ord : {u : S} → (n : ℕ) → IsOrd u → IsOrd (sucIter n u)
sucIter-ord zero ou = ou
sucIter-ord (suc n) ou = suc-ord (sucIter-ord n ou)

-- Probe-local ω-block.  Sealed at birth, same discipline as +ω
-- (StageArith.lagda.md:39-42), so a consumer's type sees an atom.
opaque
  ωBlock : S → S
  ωBlock u = ⋃ (sett (Lift {ℓ-zero} {ℓ} ℕ) (F u))

opaque
  unfolding ωBlock

  -- One direction: a member of a finite iterate is a member of the block.
  ωBlock-in : (u x : S) → (n : ℕ) → ⟨ x ∈ˢ sucIter (suc n) u ⟩ → ⟨ x ∈ˢ ωBlock u ⟩
  ωBlock-in u x n x∈ = ∈∈ₛ {a = x} {b = ωBlock u} .snd
    (union-ax (sett (Lift {ℓ-zero} {ℓ} ℕ) (F u)) x .snd
      ∣ sucIter (suc n) u , (memb , x∈ₛ) ∣₁)
    where
    memb : ⟨ sucIter (suc n) u ∈ₛ sett (Lift {ℓ-zero} {ℓ} ℕ) (F u) ⟩
    memb = ∈∈ₛ {a = sucIter (suc n) u} {b = sett (Lift {ℓ-zero} {ℓ} ℕ) (F u)} .fst
      ∣ lift n , refl ∣₁
    x∈ₛ : ⟨ x ∈ₛ sucIter (suc n) u ⟩
    x∈ₛ = ∈∈ₛ {a = x} {b = sucIter (suc n) u} .fst x∈

  ωBlock-mem : (u : S) → ⟨ u ∈ˢ ωBlock u ⟩
  ωBlock-mem u = ωBlock-in u u 0 (self∈sucV u)

  ωBlock-iter : (n : ℕ) → (u : S) → ⟨ sucIter n u ∈ˢ ωBlock u ⟩
  ωBlock-iter n u = ωBlock-in u (sucIter n u) n (self∈sucV (sucIter n u))

  ωBlock-ord : (u : S) → IsOrd u → IsOrd (ωBlock u)
  ωBlock-ord u ou = setUnion-ord (Lift {ℓ-zero} {ℓ} ℕ) (F u)
    (λ m → sucIter-ord (suc (lower m)) ou)

  -- The out-lemma the sealed +ω does not export.
  ωBlock-out : (u x : S) → ⟨ x ∈ˢ ωBlock u ⟩
             → ∥ Σ[ n ∈ ℕ ] ⟨ x ∈ˢ sucIter (suc n) u ⟩ ∥₁
  ωBlock-out u x x∈ = PT.rec squash₁
    (λ { (v , (v∈sett , x∈v)) → PT.map
      (λ { (m , e) → lower m
         , ∈∈ₛ {a = x} {b = sucIter (suc (lower m)) u} .snd
             (subst (λ w → ⟨ x ∈ₛ w ⟩) (sym e) x∈v) })
      (∈∈ₛ {a = v} {b = sett (Lift {ℓ-zero} {ℓ} ℕ) (F u)} .snd v∈sett) })
    (union-ax (sett (Lift {ℓ-zero} {ℓ} ℕ) (F u)) x .fst
      (∈∈ₛ {a = x} {b = ωBlock u} .fst x∈))

  -- W3.  A member's successor stays in the block.
  ωBlock-succ : (u : S) → IsOrd u
              → (d : S) → ⟨ d ∈ˢ ωBlock u ⟩ → ⟨ sucV d ∈ˢ ωBlock u ⟩
  ωBlock-succ u ou d d∈ = PT.rec (snd (sucV d ∈ˢ ωBlock u)) step (ωBlock-out u d d∈)
    where
    step : Σ[ n ∈ ℕ ] ⟨ d ∈ˢ sucIter (suc n) u ⟩ → ⟨ sucV d ∈ˢ ωBlock u ⟩
    step (n , d∈sn) = ∈sucV-elim (snd (sucV d ∈ˢ ωBlock u)) d∈sn from-below from-eq
      where
      from-eq : d ≡ sucIter n u → ⟨ sucV d ∈ˢ ωBlock u ⟩
      from-eq e = subst (λ w → ⟨ sucV w ∈ˢ ωBlock u ⟩) (sym e)
        (ωBlock-iter (suc n) u)
      from-below : ⟨ d ∈ˢ sucIter n u ⟩ → ⟨ sucV d ∈ˢ ωBlock u ⟩
      from-below d∈n = Sum.rec
        (λ s∈n → ωBlock-in u (sucV d) n (∈sucV-inl s∈n))
        (λ s≡n → subst (λ w → ⟨ w ∈ˢ ωBlock u ⟩) (sym s≡n) (ωBlock-iter n u))
        (suc∈or≡ d (sucIter n u)
          (mem-ord {A = sucIter n u} (sucIter-ord n ou) d d∈n)
          (sucIter-ord n ou) d∈n)

  -- Empty set is in the block: trichotomy against the base ordinal.
  ωBlock-∅ : (u : S) → IsOrd u → ⟨ ∅ ∈ˢ ωBlock u ⟩
  ωBlock-∅ u ou = go (ord-tri ∅ ∅-ord u ou)
    where
    go : ⟨ ∅ ∈ˢ u ⟩ ⊎ ((∅ ≡ u) ⊎ ⟨ u ∈ˢ ∅ ⟩) → ⟨ ∅ ∈ˢ ωBlock u ⟩
    go (inl ∅∈u)       = ωBlock-in u ∅ 0 (∈sucV-inl ∅∈u)
    go (inr (inl e))   = subst (λ w → ⟨ w ∈ˢ ωBlock u ⟩) (sym e) (ωBlock-mem u)
    go (inr (inr u∈∅)) =
      Empty.rec (∅-empty u (∈∈ₛ {a = u} {b = ∅} .fst u∈∅))

-- The KValue telescope, at the ω-block above a generic ordinal.
-- W2: written once here, instantiated by the obligation.
module Block (u : V ℓ) (ou : IsOrd u) where
  lam : V ℓ
  lam = ωBlock u
  ordλ : IsOrd lam
  ordλ = ωBlock-ord u ou
  succλ : (d : V ℓ) → ⟨ d ∈ lam ⟩ → ⟨ sucV d ∈ lam ⟩
  succλ = ωBlock-succ u ou
  ∅∈λ : ⟨ ∅ ∈ lam ⟩
  ∅∈λ = ωBlock-∅ u ou
  γ∈λ : ⟨ u ∈ lam ⟩
  γ∈λ = ωBlock-mem u
