{-# OPTIONS --cubical --safe --guardedness #-}

-- [LJ-1.734] PROBE.  keyS-in-carrier-lim, the INHABITED name the
-- meter reads ([LJ-1.729] delivered this term;  the 729 meter closed
-- on the FALSE neighbour name keyS-in-carrier-stage).  Lands nothing
-- in src/.
--
--   OBLIGATION  keyS-in-carrier-lim, the 729-inhabited term
--               (Probe729.agda:202-208) transcribed into a fresh
--               file at its own top-level name, so the live meter's
--               obligation has a supply.  W3 asks whether the
--               transcription still converts outside the file whose
--               nesting carried it.
--   ABSENT      keyS-in-carrier-stage.  That type is FALSE at
--               omega in^sv gamma (review-of-keyS-in-carrier-stage.md
--               beside the 729 report);  this file neither states it
--               nor inhabits it, and no postulate stands anywhere.
--
-- ONE Agda process per run, GHCRTS wide caliber, set on the pane by
-- the program and untouched here.

open import Base.Prelude
open import Base.Truth
open import Base.Classical using ( LEM )

module LJ-1-734.Probe734 {ℓ : Level} (lem : LEM (ℓ-suc ℓ)) where

open import FOL.ZFStructure using ( module hPropStructure )
open import FOL.Syntax
  using ( Formula; Term; var; con; _∈̇_; _≐_; _∧̇_; _∨̇_; _⇒̇_; ¬̇_; ⊤̇; ⊥̇
        ; ∃̇_; ∀̇_; ∀̇∈; ∃̇∈ )
open import FOL.Manipulation.Relabelling using ( mapTm; mapFo )
open import Cubical.Data.FinData using ( toℕ )
open import Cubical.Data.Nat using ( _+_ )
open import Cubical.Data.Nat.Properties using ( +-comm )
open import Cubical.Data.Sum using ( _⊎_; inl; inr )
import Cubical.HITs.PropositionalTruncation as PT
open import Cubical.HITs.CumulativeHierarchy.Base using ( V; _∈_ )
open import Cubical.HITs.CumulativeHierarchy.Properties
  using ( ⟪_⟫; ⟪_⟫↪; ∈∈ₛ; ∈ₛ⟪_⟫↪_ )
open import Cubical.HITs.CumulativeHierarchy.Constructions
  using ( module InfinitySet )
open InfinitySet using ( #_; ω; sucV )
open import V.Hierarchy {ℓ} using ( 𝒮ᵥ )
open import V.Coding {ℓ} using ( pr; module VCode )
open import V.Model {ℓ} using ( self∈sucV )
open import L.Constructible {ℓ}
  using ( 𝒮ʟ; isL; isL-trans; IsOrd; Lset; Lset-mono; Lset-out; Lset→isL
        ; 𝒟ₒ; 𝒟ₒ∋⊆ )
open import L.Ordinal {ℓ} using ( mem-ord; ω-ord )
open import L.Ordinal.Linear {ℓ} lem using ( Tri; ord-tri )
open import L.Ordinal.StageArith {ℓ} lem
  using ( sucIter; +ω; +ω-iter; closedω )
open import L.Choice.Name {ℓ} lem using ( numeral∈limit )
open import L.Axioms.Basic {ℓ} using ( LsetS; pr∈Lset-suc )
open import L.Coding.CodeSet {ℓ} lem using ( keyS )

open TruthAlgebra (hPropAlgebra (ℓ-suc ℓ))
-- The hypothesis glyph `omega in^sv gamma` is the V structure's
-- membership (gamma : V), so it is renamed here;  the conclusion's
-- glyph `keyS A phi in^s LsetS gamma ogamma` is the L structure's and
-- stays unrenamed below.
open hPropStructure 𝒮ᵥ using () renaming ( _∈ˢ_ to _∈ˢᵥ_ )
open hPropStructure 𝒮ʟ

-- =====================================================================
-- SECTION 1.  The finite-iterate shift.  sucIter commutes with sucV,
-- sucIter (a + b) u is sucIter b above sucIter a u, and the two sums
-- jb + suc ja and suc (ja + jb) name the same iterate.  This is what
-- lets the climb pair two pieces at ONE common stage and carry ONE
-- existential iterate instead of a weight function and a max.
-- =====================================================================

sucIter-sucV : (X : V ℓ) (b : ℕ) → sucV (sucIter b X) ≡ sucIter b (sucV X)
sucIter-sucV X zero    = refl
sucIter-sucV X (suc b) = cong sucV (sucIter-sucV X b)

sucIter-shift : (u : V ℓ) (a b : ℕ) → sucIter (a + b) u ≡ sucIter b (sucIter a u)
sucIter-shift u zero    b = refl
sucIter-shift u (suc a) b =
  cong sucV (sucIter-shift u a b) ∙ sucIter-sucV (sucIter a u) b

-- b iterates above any stage W.  The zero case is definitional.
iter-up : (W : V ℓ) (b : ℕ) (x : V ℓ)
        → ⟨ x ∈ˢᵥ Lset W ⟩ → ⟨ x ∈ˢᵥ Lset (sucIter b W) ⟩
iter-up W zero    x h = h
iter-up W (suc b) x h =
  Lset-mono {α = sucV (sucIter b W)} {β = sucIter b W}
    (self∈sucV (sucIter b W)) (iter-up W b x h)

-- =====================================================================
-- SECTION 2.  The Kuratowski step.  Two pieces, each possibly at a
-- DIFFERENT finite iterate of sigma, pair at one common stage:  the
-- sum of the iterates, once raised, plus the fixed +2 that
-- pr∈Lset-suc charges.  This is the one place the climb spends stage
-- height, and the spend is the size of the formula, which is exactly
-- what a successor gamma cannot absorb.
-- =====================================================================

pr∈iter : (σ : V ℓ) (ja jb : ℕ) (x y : V ℓ)
        → ⟨ x ∈ˢᵥ Lset (sucIter ja σ) ⟩ → ⟨ y ∈ˢᵥ Lset (sucIter jb σ) ⟩
        → ⟨ pr x y ∈ˢᵥ Lset (sucIter (suc (suc (ja + jb))) σ) ⟩
pr∈iter σ ja jb x y hx hy =
  pr∈Lset-suc (sucIter (ja + jb) σ) x y
    (subst (λ W → ⟨ x ∈ˢᵥ Lset W ⟩) (sym (sucIter-shift σ ja jb))
      (iter-up (sucIter ja σ) jb x hx))
    (subst (λ W → ⟨ y ∈ˢᵥ Lset W ⟩) (cong (λ W → sucIter W σ) (+-comm jb ja))
      (subst (λ W → ⟨ y ∈ˢᵥ Lset W ⟩) (sym (sucIter-shift σ jb ja))
        (iter-up (sucIter jb σ) ja y hy)))

-- =====================================================================
-- SECTION 3.  The climb.  For a formula over ANY small alphabet, the
-- code of its mapFo image sits at SOME finite iterate of the stage
-- that holds the alphabet's values and the numerals.  Twelve
-- constructors, one line each;  the iterate is EXISTENTIAL, so no
-- weight function and no max is ever built.
-- =====================================================================

module Climb (σ : V ℓ) {K : Type ℓ} (f : K → V ℓ)
             (hf : (k : K) → ⟨ f k ∈ˢᵥ Lset σ ⟩)
             (hnum : (k : ℕ) → ⟨ (# k) ∈ˢᵥ Lset σ ⟩) where

  -- A numeral tagged onto a pair of pieces.  The pieces may sit at
  -- DIFFERENT iterates;  the tag sits at the sum raised by the fixed
  -- +4 (the inner pair's +2 and the outer tag's +2).
  pairStep : (k ja jb : ℕ) (x y : V ℓ)
           → ⟨ x ∈ˢᵥ Lset (sucIter ja σ) ⟩ → ⟨ y ∈ˢᵥ Lset (sucIter jb σ) ⟩
           → Σ[ j ∈ ℕ ] ⟨ pr (# k) (pr x y) ∈ˢᵥ Lset (sucIter j σ) ⟩
  pairStep k ja jb x y hx hy =
    suc (suc (suc (suc (ja + jb))))
    , pr∈iter σ 0 (suc (suc (ja + jb))) (# k) (pr x y)
        (hnum k) (pr∈iter σ ja jb x y hx hy)

  -- A numeral tagged onto a single piece.
  tagStep : (k jb : ℕ) (y : V ℓ)
          → ⟨ y ∈ˢᵥ Lset (sucIter jb σ) ⟩
          → Σ[ j ∈ ℕ ] ⟨ pr (# k) y ∈ˢᵥ Lset (sucIter j σ) ⟩
  tagStep k jb y hy =
    suc (suc jb) , pr∈iter σ 0 jb (# k) y (hnum k) hy

  codeTm∈iter : ∀ {n} (t : Term K n)
              → Σ[ j ∈ ℕ ] ⟨ VCode.⌜ mapTm f t ⌝ᵗ ∈ˢᵥ Lset (sucIter j σ) ⟩
  codeTm∈iter (con c) = tagStep 0 0 (f c) (hf c)
  codeTm∈iter (var i) = tagStep 1 0 (# (toℕ i)) (hnum (toℕ i))

  code∈iter : ∀ {n} (φ : Formula K n)
            → Σ[ j ∈ ℕ ] ⟨ VCode.⌜ mapFo f φ ⌝ ∈ˢᵥ Lset (sucIter j σ) ⟩
  code∈iter (t ∈̇ u) =
    pairStep 0 (fst (codeTm∈iter t)) (fst (codeTm∈iter u))
      VCode.⌜ mapTm f t ⌝ᵗ VCode.⌜ mapTm f u ⌝ᵗ
      (snd (codeTm∈iter t)) (snd (codeTm∈iter u))
  code∈iter (t ≐ u) =
    pairStep 1 (fst (codeTm∈iter t)) (fst (codeTm∈iter u))
      VCode.⌜ mapTm f t ⌝ᵗ VCode.⌜ mapTm f u ⌝ᵗ
      (snd (codeTm∈iter t)) (snd (codeTm∈iter u))
  code∈iter (a ∧̇ b) =
    pairStep 2 (fst (code∈iter a)) (fst (code∈iter b))
      VCode.⌜ mapFo f a ⌝ VCode.⌜ mapFo f b ⌝
      (snd (code∈iter a)) (snd (code∈iter b))
  code∈iter (a ∨̇ b) =
    pairStep 3 (fst (code∈iter a)) (fst (code∈iter b))
      VCode.⌜ mapFo f a ⌝ VCode.⌜ mapFo f b ⌝
      (snd (code∈iter a)) (snd (code∈iter b))
  code∈iter (a ⇒̇ b) =
    pairStep 4 (fst (code∈iter a)) (fst (code∈iter b))
      VCode.⌜ mapFo f a ⌝ VCode.⌜ mapFo f b ⌝
      (snd (code∈iter a)) (snd (code∈iter b))
  code∈iter (¬̇ a) = tagStep 5 (fst (code∈iter a)) (VCode.⌜ mapFo f a ⌝) (snd (code∈iter a))
  code∈iter ⊤̇    = tagStep 6 0 (# 0) (hnum 0)
  code∈iter ⊥̇    = tagStep 7 0 (# 0) (hnum 0)
  code∈iter (∃̇ a) = tagStep 8 (fst (code∈iter a)) (VCode.⌜ mapFo f a ⌝) (snd (code∈iter a))
  code∈iter (∀̇ a) = tagStep 9 (fst (code∈iter a)) (VCode.⌜ mapFo f a ⌝) (snd (code∈iter a))
  code∈iter (∀̇∈ t a) =
    pairStep 10 (fst (codeTm∈iter t)) (fst (code∈iter a))
      VCode.⌜ mapTm f t ⌝ᵗ VCode.⌜ mapFo f a ⌝
      (snd (codeTm∈iter t)) (snd (code∈iter a))
  code∈iter (∃̇∈ t a) =
    pairStep 11 (fst (codeTm∈iter t)) (fst (code∈iter a))
      VCode.⌜ mapTm f t ⌝ᵗ VCode.⌜ mapFo f a ⌝
      (snd (codeTm∈iter t)) (snd (code∈iter a))

-- =====================================================================
-- SECTION 4.  THE OBLIGATION, INHABITED.  The 729 term, verbatim.
-- The carrier's stage witness delta comes out of Lset-out;  ord-tri
-- puts omega below, equal to, or above it, and in each case the climb
-- runs at a common sigma inside gamma and the +omega block absorbs
-- every finite iterate.  At gamma = sucV (sucV omega) closedomega
-- FAILS, which is why the neighbour name keyS-in-carrier-stage is
-- false and lives in no line of this file.
-- =====================================================================

keyS-in-carrier-lim :
    (γ : V ℓ) (oγ : IsOrd γ) (clγ : closedω γ)
    (ω∈γ : ⟨ ω ∈ˢᵥ γ ⟩)
    (A : S) (hA : ⟨ fst A ∈ Lset γ ⟩)
    {n : ℕ} (φ : Formula ⟪ fst A ⟫ n)
  → ⟨ keyS A φ ∈ˢ LsetS γ oγ ⟩
keyS-in-carrier-lim γ oγ clγ ω∈γ A hA {n} φ =
  PT.rec (snd (keyS A φ ∈ˢ LsetS γ oγ)) step (Lset-out γ (fst A) hA)
  where
  ι : ⟪ fst A ⟫ → V ℓ
  ι = ⟪ fst A ⟫↪

  ι∈ : (m : ⟪ fst A ⟫) → ⟨ ι m ∈ˢᵥ fst A ⟩
  ι∈ m = ∈∈ₛ {a = ι m} {b = fst A} .snd (∈ₛ⟪ fst A ⟫↪ m)

  hL : ⟨ isL (fst A) ⟩
  hL = Lset→isL γ oγ (fst A) hA

  ιL : (m : ⟪ fst A ⟫) → ⟨ isL (ι m) ⟩
  ιL m = isL-trans {x = fst A} {y = ι m} (ι∈ m) hL

  𝒟𝒟 : (δ : V ℓ) → ⟨ fst A ∈ˢᵥ 𝒟ₒ (Lset δ) ⟩
     → (m : ⟪ fst A ⟫) → ⟨ ι m ∈ˢᵥ Lset δ ⟩
  𝒟𝒟 δ A∈𝒟 m = 𝒟ₒ∋⊆ (Lset δ) (fst A) A∈𝒟 (ι m) (ι∈ m)

  close : (σ : V ℓ) → ⟨ σ ∈ˢᵥ γ ⟩
        → ((k : ℕ) → ⟨ (# k) ∈ˢᵥ Lset σ ⟩)
        → ((m : ⟪ fst A ⟫) → ⟨ ι m ∈ˢᵥ Lset σ ⟩)
        → ⟨ keyS A φ ∈ˢ LsetS γ oγ ⟩
  close σ σ∈γ hnum' hfc =
    Lset-mono {α = γ} {β = +ω σ} (clγ σ σ∈γ)
      (Lset-mono {α = +ω σ} {β = sucIter (suc (suc (fst Cj))) σ}
        (+ω-iter (suc (suc (fst Cj))) σ)
        (pr∈iter σ 0 (fst Cj) (# n) (VCode.⌜ mapFo ι φ ⌝)
          (hnum' n) (snd Cj)))
    where
    module C = Climb σ ι hfc hnum'
    Cj = C.code∈iter φ

  step : Σ[ δ ∈ V ℓ ] (⟨ δ ∈ˢᵥ γ ⟩ × ⟨ fst A ∈ˢᵥ 𝒟ₒ (Lset δ) ⟩)
       → ⟨ keyS A φ ∈ˢ LsetS γ oγ ⟩
  step (δ , δ∈γ , A∈𝒟) = helper (ord-tri ω ω-ord δ oδ)
    where
    oδ : IsOrd δ
    oδ = mem-ord {A = γ} oγ δ δ∈γ

    hfcδ : (m : ⟪ fst A ⟫) → ⟨ ι m ∈ˢᵥ Lset δ ⟩
    hfcδ m = 𝒟𝒟 δ A∈𝒟 m

    helper : Tri ω δ → ⟨ keyS A φ ∈ˢ LsetS γ oγ ⟩
    helper (inl ω∈δ) =
      close δ δ∈γ (λ k → Lset-mono {α = δ} {β = ω} ω∈δ (numeral∈limit k)) hfcδ
    helper (inr (inl ω≡δ)) =
      close δ δ∈γ
        (λ k → subst (λ W → ⟨ (# k) ∈ˢᵥ Lset W ⟩) ω≡δ (numeral∈limit k)) hfcδ
    helper (inr (inr δ∈ω)) =
      close ω ω∈γ numeral∈limit (λ m → Lset-mono {α = ω} {β = δ} δ∈ω (hfcδ m))
