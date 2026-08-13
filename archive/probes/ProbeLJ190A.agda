{-# OPTIONS --cubical --safe --guardedness #-}

-- [LJ-1.90] probe A: the first concrete supply site for
-- BoundedSubsetAt (src/L/BoundedSubset.lagda.md:1396-1402).
--
-- The dispatch asks two things.  First, can the consumer that names the
-- limit stage lam produce the frame hypothesis AllCodes A ∈ Lset lam
-- that [LJ-1.89]'s witK needs?  Second, how far does the supply of the
-- BoundedSubsetAt telescope reach, hypothesis by hypothesis?
--
-- THE ANSWER MACHINE-CHECKED HERE.  The consumer can produce it: the
-- code set's OWN stage is δ₀ = stage (fst (AllCodes A)); the consumer
-- names lam as the omega-limit above the merge of the generator stage α
-- and δ₀; then stage-mem plus Lset-mono put AllCodes A in Lset lam.
-- The price is that lam is not arbitrary: it must be chosen with room
-- above the code set's stage.  The telescope permits that choice.
--
-- THE TELESCOPE SUPPLY.  Everything except cardκ receives a value in
-- module Site below (generic in the stage, P-h), and the concrete site
-- is A = LsetS ω, α = ω, x = ∅.  The first hypothesis nothing can
-- supply is cardκ : IsCardinal κ at the concrete κ = sucV ω: no
-- delivered term proves IsCardinal at any ordinal the tree can name
-- beyond ω (search-verified; no cardinal chapter, dev/PLAN.md LJ-1.46).
--
-- Untracked probe; one Agda process under GHCRTS="-A64m -I0 -M8g";
-- never committed.

open import Base.Prelude
open import Base.Truth
open import Base.Classical using ( LEM )

module ProbeLJ190A {ℓ : Level} (lem : LEM (ℓ-suc ℓ)) where

open import FOL.ZFStructure using ( ZFStructure; module hPropStructure )
open import V.Hierarchy {ℓ} using ( 𝒮ᵥ; ∈-irrefl )
open import L.Constructible {ℓ}
  using ( 𝒮ʟ; isL; IsOrd; Lset; Lset-mono )
open import L.Ordinal {ℓ}
  using ( ω-ord; #∈ω; suc-ord; boundingOrd; bound2; mem-ord )
open import L.Ordinal.Linear {ℓ} lem using ( ord-tri )
open import L.Ordinal.Stages {ℓ} lem using ( suc∈or≡ )
open import L.Stage {ℓ} lem using ( stage; stage-ord; stage-mem )
open import L.Axioms.Basic {ℓ} using ( LsetS; Lset-suc; ∅∈𝒟ₒ )
open import L.Coding.CodeSet {ℓ} lem using ( AllCodes )
open import V.Model {ℓ} using ( ∈sucV-elim; self∈sucV )
open import Cubical.HITs.CumulativeHierarchy.Base using ( V; sett )
open import Cubical.HITs.CumulativeHierarchy.Properties
  using ( _∈ₛ_; ∈∈ₛ; ix∈ₛ )
open import Cubical.HITs.CumulativeHierarchy.Constructions
  using ( ∅; ∅-empty; ⋃_; union-ax; module InfinitySet )
open InfinitySet using ( ω; sucV; #_ )
open import Cubical.Data.Nat using ( ℕ; zero; suc )
open import Cubical.Data.Sum using ( _⊎_; inl; inr )
import Cubical.Data.Sum as Sum
open import Cubical.Foundations.Prelude using ( sym; subst; cong )
import Cubical.Data.Empty as Empty
import Cubical.HITs.PropositionalTruncation as PT
open PT using ( ∣_∣₁; ∥_∥₁ )

open TruthAlgebra (hPropAlgebra (ℓ-suc ℓ))
open hPropStructure 𝒮ᵥ

Sʟ : Type (ℓ-suc ℓ)
Sʟ = ZFStructure.S 𝒮ʟ

-- =====================================================================
-- THE GENERIC SITE (P-h: module-parameterized, generic in the stage).
-- Given a carrier A, an infinite ordinal stage α, and α∉ω, everything
-- the dispatch asks the consumer to supply is built here as a VALUE:
-- lam, ordλ, succλ, α∈λ, x ∈ Lset lam, and the frame hypothesis
-- AllCodes A ∈ Lset lam.  The concrete site at the bottom instantiates
-- A = LsetS ω, α = ω.
-- =====================================================================
module Site (A : Sʟ) (α : S) (ordα : IsOrd α)
            (α∉ω : ⟨ α ∈ˢ ω ⟩ → Empty.⊥) where

  -- The code set's own stage: the ordinal that contains AllCodes A.
  δ₀ : S
  δ₀ = stage (fst (AllCodes A)) ((AllCodes A) .snd)

  ordδ : IsOrd δ₀
  ordδ = stage-ord (fst (AllCodes A)) ((AllCodes A) .snd)

  AC∈Lδ₀ : ⟨ fst (AllCodes A) ∈ˢ Lset δ₀ ⟩
  AC∈Lδ₀ = stage-mem (fst (AllCodes A)) ((AllCodes A) .snd)

  -- The merge of α and δ₀, and the omega-limit above it: lam.
  γ-info : Σ[ β ∈ S ] (IsOrd β × ⟨ α ∈ˢ β ⟩ × ⟨ δ₀ ∈ˢ β ⟩)
  γ-info = bound2 α δ₀ ordα ordδ

  γ : S
  γ = γ-info .fst

  ordγ : IsOrd γ
  ordγ = γ-info .snd .fst

  α∈γ : ⟨ α ∈ˢ γ ⟩
  α∈γ = γ-info .snd .snd .fst

  δ∈γ : ⟨ δ₀ ∈ˢ γ ⟩
  δ∈γ = γ-info .snd .snd .snd

  iter : ℕ → S → S
  iter zero x = x
  iter (suc n) x = sucV (iter n x)

  iter-ord : (n : ℕ) → IsOrd (iter n γ)
  iter-ord zero = ordγ
  iter-ord (suc n) = suc-ord (iter-ord n)

  X : Type ℓ
  X = Lift {ℓ-zero} {ℓ} ℕ

  lam-info : Σ[ β ∈ S ] (IsOrd β × ((n : X) → ⟨ iter (lower n) γ ∈ˢ β ⟩))
  lam-info = boundingOrd X (λ n → iter (lower n) γ)
    (λ n → iter-ord (lower n))

  lam : S
  lam = lam-info .fst

  ordλ : IsOrd lam
  ordλ = lam-info .snd .fst

  γ∈λ : ⟨ γ ∈ˢ lam ⟩
  γ∈λ = lam-info .snd .snd (lift zero)

  α∈λ : ⟨ α ∈ˢ lam ⟩
  α∈λ = ordλ .fst α∈γ γ∈λ

  δ∈λ : ⟨ δ₀ ∈ˢ lam ⟩
  δ∈λ = ordλ .fst δ∈γ γ∈λ

  -- The successor closure of lam: lam is a limit ordinal.
  g : X → S
  g n = sucV (iter (lower n) γ)

  gn∈lam : (n : X) → ⟨ g n ∈ˢ lam ⟩
  gn∈lam n = lam-info .snd .snd (lift (suc (lower n)))

  succλ : (d : S) → ⟨ d ∈ˢ lam ⟩ → ⟨ sucV d ∈ˢ lam ⟩
  succλ d d∈lam = PT.rec (snd (sucV d ∈ˢ lam)) go
    (union-ax (sett X g) d .fst (∈∈ₛ {a = d} {b = lam} .fst d∈lam))
    where
    go : Σ[ w ∈ S ] (⟨ w ∈ₛ sett X g ⟩ × ⟨ d ∈ₛ w ⟩)
       → ⟨ sucV d ∈ˢ lam ⟩
    go (w , w∈ₛsett , d∈ₛw) = PT.rec (snd (sucV d ∈ˢ lam)) go₂
      (∈∈ₛ {a = w} {b = sett X g} .snd w∈ₛsett)
      where
      go₂ : Σ[ n ∈ X ] (g n ≡ w) → ⟨ sucV d ∈ˢ lam ⟩
      go₂ (n , e) = ∈sucV-elim {A = iter (lower n) γ} {x = d}
          (snd (sucV d ∈ˢ lam)) dn
          (λ d∈it → via-iter n (suc∈or≡ d (iter (lower n) γ)
            (mem-ord {A = lam} ordλ d d∈lam) (iter-ord (lower n)) d∈it))
          (λ d≡it → subst (λ w → ⟨ w ∈ˢ lam ⟩)
            (sym (cong sucV d≡it)) (gn∈lam n))
        where
        dn : ⟨ d ∈ˢ g n ⟩
        dn = subst (λ w → ⟨ d ∈ˢ w ⟩) (sym e)
          (∈∈ₛ {a = d} {b = w} .snd d∈ₛw)

        via-iter : (n : X)
                 → (⟨ sucV d ∈ˢ iter (lower n) γ ⟩ ⊎ (sucV d ≡ iter (lower n) γ))
                 → ⟨ sucV d ∈ˢ lam ⟩
        via-iter n (inl h) = ordλ .fst h (lam-info .snd .snd n)
        via-iter n (inr h) = subst (λ w → ⟨ w ∈ˢ lam ⟩) (sym h)
          (lam-info .snd .snd n)

  -- The bounded set x = ∅, at the generator stage and at the limit.
  x : S
  x = ∅

  x⊆Lα : (z : S) → ⟨ z ∈ˢ x ⟩ → ⟨ z ∈ˢ Lset α ⟩
  x⊆Lα z z∈∅ = Empty.rec (∅-empty z (∈∈ₛ {a = z} {b = ∅} .fst z∈∅))

  one∈α : ⟨ sucV ∅ ∈ˢ α ⟩
  one∈α = Sum.rec
    (λ α∈ω → Empty.rec (α∉ω α∈ω))
    (Sum.rec (λ α≡ω → subst (λ w → ⟨ sucV ∅ ∈ˢ w ⟩) (sym α≡ω) (#∈ω 1))
             (λ ω∈α → ordα .fst (#∈ω 1) ω∈α))
    (ord-tri α ordα ω ω-ord)

  one∈lam : ⟨ sucV ∅ ∈ˢ lam ⟩
  one∈lam = ordλ .fst one∈α α∈λ

  ∅∈Lset1 : ⟨ ∅ ∈ˢ Lset (sucV ∅) ⟩
  ∅∈Lset1 = subst (λ w → ⟨ ∅ ∈ˢ w ⟩) (sym (Lset-suc ∅)) (∅∈𝒟ₒ ∅)

  x∈Lλ : ⟨ x ∈ˢ Lset lam ⟩
  x∈Lλ = Lset-mono {α = lam} {β = sucV ∅} one∈lam ∅∈Lset1

  -- THE DISPATCH'S NAMED HYPOTHESIS, SUPPLIED: the consumer that names
  -- lam produces AllCodes A ∈ Lset lam.
  AllCodes∈Lλ : ⟨ fst (AllCodes A) ∈ˢ Lset lam ⟩
  AllCodes∈Lλ = Lset-mono {α = lam} {β = δ₀} δ∈λ AC∈Lδ₀

-- =====================================================================
-- THE CONCRETE SITE: A = LsetS ω, α = ω, x = ∅.
-- =====================================================================
module Site0 = Site (LsetS ω ω-ord) ω ω-ord (∈-irrefl ω)

-- The concrete cardinal slot.  The value κ = sucV ω and its ordinality
-- are supplied; cardκ : IsCardinal κ is the first hypothesis nothing
-- can supply (no term; written in _build/lj-1.90-report.md section 1).
κ : S
κ = sucV ω

ordκ : IsOrd κ
ordκ = suc-ord ω-ord

α∈κ : ⟨ ω ∈ˢ κ ⟩
α∈κ = self∈sucV ω
