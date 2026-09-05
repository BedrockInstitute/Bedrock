{-# OPTIONS --cubical --safe --guardedness #-}

-- [LJ-1.735] PROBE.  envSet-in-carrier-lim:  the environment set over a
-- carrier sits in the carrier's own stage, under closedomega gamma.
-- Lands nothing in src/.
--
--   DELIVERED   envSet-in-carrier-lim, INHABITED.  The route is the
--               landed supply-side bound envSetNumeral∈
--               (src/L/Coding/Key.lagda.md, the lemma placing
--               envSet B n at Lset (sucIter 4 sigma) from omega in
--               sigma and fst B in Lset sigma), fed a merged stage
--               m in gamma that holds both omega and the carrier:
--               Lset-out hands back a delta in gamma with
--               fst A in 𝒟ₒ (Lset delta), hence in Lset (sucV delta);
--               ord-tri merges delta with omega into m in gamma;
--               the bound lands at sucIter 4 (+omega m), two closure
--               steps put +omega (+omega m) inside gamma, and two
--               Lset-mono links close.
--   NOT HERE    envSet-in-carrier-stage (the 730 name).  It is not
--               stated, not inhabited, and no postulate stands under
--               it.  Its refutation is LJ-1.730's, not this file's.
--
-- ONE Agda process per run, GHCRTS wide caliber, set on the pane by
-- the program and never touched here.

open import Base.Prelude
open import Base.Truth
open import Base.Classical using ( LEM )

module LJ-1-735.Probe735 {ℓ : Level} (lem : LEM (ℓ-suc ℓ)) where

open import FOL.ZFStructure using ( module hPropStructure )
open import Cubical.Data.Sum as Sum using ( _⊎_; inl; inr )
import Cubical.HITs.PropositionalTruncation as PT
open PT using ( ∣_∣₁; ∥_∥₁; squash₁ )
open import Cubical.HITs.CumulativeHierarchy.Base using ( V; _∈_ )
open import Cubical.HITs.CumulativeHierarchy.Constructions
  using ( module InfinitySet )
open InfinitySet using ( ω; sucV )
open import V.Hierarchy {ℓ} using ( 𝒮ᵥ )
open import L.Constructible {ℓ}
  using ( 𝒮ʟ; IsOrd; Lset; Lset-mono; Lset-out; 𝒟ₒ )
open import L.Ordinal {ℓ} using ( ω-ord; mem-ord )
open import L.Ordinal.Linear {ℓ} lem using ( Tri; ord-tri )
open import L.Ordinal.Stages {ℓ} lem using ( suc∈or≡ )
open import L.Ordinal.StageArith {ℓ} lem
  using ( sucIter; +ω; +ω-mem; +ω-iter; +ω-sup; +ω-ord; closedω )
open import L.Axioms.Basic {ℓ} using ( LsetS; Lset-suc )
open import L.Coding.EnvSet {ℓ} lem using ( envSet )
open import L.Coding.Key {ℓ} lem using ( envSetNumeral∈ )

open TruthAlgebra (hPropAlgebra (ℓ-suc ℓ))
-- The brief's hypothesis glyph `omega in^s gamma` reads at the V
-- structure (gamma : V), so it is renamed here;  the conclusion's
-- glyph is the L structure's and stays unrenamed.  𝒮ʟ's membership
-- is `fst a ∈ˢᵥ fst b`, so facts cross between the two without a
-- conversion step.
open hPropStructure 𝒮ᵥ using () renaming ( _∈ˢ_ to _∈ˢᵥ_ )
open hPropStructure 𝒮ʟ

-- =====================================================================
-- THE OBLIGATION, INHABITED.
-- =====================================================================

envSet-in-carrier-lim :
    (γ : V ℓ) (oγ : IsOrd γ) (clγ : closedω γ)
    → ⟨ ω ∈ˢᵥ γ ⟩
    → (A : S) → ⟨ fst A ∈ Lset γ ⟩
    → (n : ℕ)
    → ⟨ envSet A n ∈ˢ LsetS γ oγ ⟩
envSet-in-carrier-lim γ oγ clγ ω∈γ A hA n =
  PT.rec (snd (envSet A n ∈ˢ LsetS γ oγ)) step (Lset-out γ (fst A) hA)
  where
  step : Σ[ δ ∈ V ℓ ] (⟨ δ ∈ˢᵥ γ ⟩ × ⟨ fst A ∈ˢᵥ 𝒟ₒ (Lset δ) ⟩)
       → ⟨ envSet A n ∈ˢ LsetS γ oγ ⟩
  step (δ , δ∈γ , A∈𝒟) = resolve (ord-tri ω ω-ord δ oδ)
    where
    oδ : IsOrd δ
    oδ = mem-ord {A = γ} oγ δ δ∈γ

    -- The carrier, one successor above its own bounding stage.
    A∈sucδ : ⟨ fst A ∈ Lset (sucV δ) ⟩
    A∈sucδ = subst (λ w → ⟨ fst A ∈ w ⟩) (sym (Lset-suc δ)) A∈𝒟

    -- THE CLOSE, WRITTEN ONCE (W2).  Any stage m inside gamma that
    -- carries both omega and the carrier's one-up stage feeds the
    -- landed envSetNumeral∈ at +omega m, and two closure links put
    -- sucIter 4 (+omega m) inside gamma:  the iterate into the first
    -- +omega block, the block into the second by closedomega.
    close : (m : V ℓ) (om : IsOrd m) → ⟨ m ∈ˢᵥ γ ⟩
          → ⟨ ω ∈ˢᵥ +ω m ⟩ → ⟨ sucV δ ∈ˢᵥ +ω m ⟩
          → ⟨ envSet A n ∈ˢ LsetS γ oγ ⟩
    close m om m∈γ ω∈+ωm sucδ∈+ωm =
      Lset-mono {α = γ} {β = +ω (+ω m)} (clγ (+ω m) (clγ m m∈γ))
        (Lset-mono {α = +ω (+ω m)} {β = sucIter 4 (+ω m)}
          (+ω-iter 4 (+ω m))
          (envSetNumeral∈ (+ω m) (+ω-ord m om) ω∈+ωm A n
            (Lset-mono {α = +ω m} {β = sucV δ} sucδ∈+ωm A∈sucδ)))

    -- omega at or below the carrier's stage:  m is delta itself.
    below : ⟨ ω ∈ˢᵥ δ ⟩ → ⟨ envSet A n ∈ˢ LsetS γ oγ ⟩
    below ω∈δ = close δ oδ δ∈γ
      ((+ω-ord δ oδ) .fst ω∈δ (+ω-mem δ))
      (+ω-iter 1 δ)

    -- omega equal to or above it:  m is omega, and the carrier's
    -- one-up stage still sits in +omega omega, by equality in the
    -- first subcase and by the sup law in the second.
    eq-case : ω ≡ δ → ⟨ sucV δ ∈ˢᵥ +ω ω ⟩
    eq-case ω≡δ = subst (λ w → ⟨ sucV w ∈ˢᵥ +ω ω ⟩) ω≡δ (+ω-iter 1 ω)

    gt-case : ⟨ δ ∈ˢᵥ ω ⟩ → ⟨ sucV δ ∈ˢᵥ +ω ω ⟩
    gt-case δ∈ω = Sum.rec
      (λ sucδ∈ω → +ω-sup ω (sucV δ) sucδ∈ω)
      (λ sucδ≡ω → subst (λ w → ⟨ w ∈ˢᵥ +ω ω ⟩) (sym sucδ≡ω) (+ω-mem ω))
      (suc∈or≡ δ ω oδ ω-ord δ∈ω)

    atω : (ω ≡ δ) ⊎ ⟨ δ ∈ˢᵥ ω ⟩ → ⟨ envSet A n ∈ˢ LsetS γ oγ ⟩
    atω (inl ω≡δ) = close ω ω-ord ω∈γ (+ω-mem ω) (eq-case ω≡δ)
    atω (inr δ∈ω) = close ω ω-ord ω∈γ (+ω-mem ω) (gt-case δ∈ω)

    resolve : Tri ω δ → ⟨ envSet A n ∈ˢ LsetS γ oγ ⟩
    resolve (inl ω∈δ)  = below ω∈δ
    resolve (inr triω) = atω triω
