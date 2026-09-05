{-# OPTIONS --cubical --safe --guardedness #-}

-- [LJ-1.85] probe A: the repaired premise excludes the refuting witness.
--
-- The repaired witK adds the premise that the witness w is BOUNDED by the
-- code set of the carrier: every member of w is a key of a formula over
-- the carrier at some arity, i.e. w ⊆ AllCodes A
-- (L.Coding.CodeSet.lagda.md:434-461).
--
-- The LJ-1.84 refuting witness is w = D ∪ {c₀}, where
--     c₀ = pr K₀ (pr (#6) (numeralL 0))
-- has the stage bound itself as its arity slot.  This probe machine-checks
-- that at the chain's stages the junk member is NOT a member of AllCodes A:
-- a member of AllCodes is a key of a formula, so its arity slot is a
-- numeral; the junk member's arity slot is Lset lam, and Lset lam is not a
-- numeral, because Lset lam ∈ ω would put Lset lam inside the stage by
-- transitivity, refuting regularity.  Hence the extended witness fails the
-- new premise, and the LJ-1.84 refutation cannot be assembled against the
-- repaired statement.
--
-- Untracked probe; one Agda process under GHCRTS="-A64m -I0 -M8g";
-- never committed.

open import Base.Prelude
open import Base.Truth
open import Base.Classical using ( LEM )

module ProbeLJ185A {ℓ : Level} (lem : LEM (ℓ-suc ℓ)) where

open import FOL.ZFStructure using ( ZFStructure; module hPropStructure )
open import FOL.Syntax using ( Formula )
open import V.Hierarchy {ℓ} using ( 𝒮ᵥ; ∈-irrefl )
open import L.Constructible {ℓ}
  using ( 𝒮ʟ; isL; IsOrd; Lset; layer-trans; Lset-layer )
open import L.Coding.Model {ℓ} using ( prʟ; prʟ-fst )
open import L.Coding.CodeSet {ℓ} lem using ( AllCodes; AllCodes-out; keyS )
open import L.Axioms.Numerals {ℓ} using ( numeralL; numeralL-fst )
open import L.Axioms.Basic {ℓ} using ( LsetS )
open import L.Ordinal {ℓ} using ( ω-ord; #∈ω )
open import L.Ordinal.Stages {ℓ} lem using ( ord∈Lset-suc; Lset-cumul )
open import L.Ordinal.Linear {ℓ} lem using ( ord-tri )
open import V.Coding {ℓ} using ( pr; pr-inj )
open import Cubical.HITs.CumulativeHierarchy.Base using ( V; _∈_ )
open import Cubical.HITs.CumulativeHierarchy.Properties using ( ⟪_⟫ )
open import Cubical.HITs.CumulativeHierarchy.Constructions using ( module InfinitySet )
open InfinitySet using ( ω; sucV; #_ )
import Cubical.HITs.PropositionalTruncation as PT
open PT using ( ∥_∥₁; ∣_∣₁; squash₁ )
import Cubical.Data.Empty as Empty
open import Cubical.Data.Nat using ( ℕ )
open import Cubical.Data.Sum as Sum using ( _⊎_; inl; inr )

open TruthAlgebra (hPropAlgebra (ℓ-suc ℓ))
open hPropStructure 𝒮ᵥ

Sʟ : Type (ℓ-suc ℓ)
Sʟ = ZFStructure.S 𝒮ʟ

-- =====================================================================
-- AT THE CHAIN'S STAGE.  lam is a limit ordinal above alpha, alpha is not
-- a member of omega (the LJ-1.80 parameters).  K₀ = LsetS lam ordλ is the
-- bound; the junk member's arity slot is fst K₀ = Lset lam.
-- =====================================================================
module Stage (lam : V ℓ) (ordλ : IsOrd lam)
  (α : V ℓ) (ordα : IsOrd α) (α∈λ : ⟨ α ∈ˢ lam ⟩)
  (α∉ω : ⟨ α ∈ˢ ω ⟩ → Empty.⊥) where

  K₀ : Sʟ
  K₀ = LsetS lam ordλ

  A₀ : Sʟ
  A₀ = LsetS α ordα

  -- omega lies in lam, exactly as in ProbeLJ180A.
  ω∈lam : ⟨ ω ∈ˢ lam ⟩
  ω∈lam = Sum.rec
    (λ lam∈ω → Empty.rec (α∉ω (ω-ord .fst {x = lam} {y = α} α∈λ lam∈ω)))
    (Sum.rec (λ lam≡ω → Empty.rec (α∉ω (subst (λ w → ⟨ α ∈ˢ w ⟩) lam≡ω α∈λ)))
             (λ h → h))
    (ord-tri lam ordλ ω ω-ord)

  -- omega is a member of the stage Lset lam: every ordinal below lam
  -- appears at the stage.
  ω∈Lsetlam : ⟨ ω ∈ˢ Lset lam ⟩
  ω∈Lsetlam = Lset-cumul ω lam ω-ord ordλ ω∈lam (ord∈Lset-suc ω ω-ord)

  -- The stage bound is not a numeral.  If Lset lam = # n then Lset lam ∈ ω,
  -- and transitivity of the stage puts Lset lam inside itself.
  notNumeral : (n : ℕ) → Lset lam ≡ # n → Empty.⊥
  notNumeral n p =
    Empty.rec (∈-irrefl (Lset lam)
      (layer-trans (Lset-layer lam) (subst (λ w → ⟨ w ∈ˢ ω ⟩) (sym p) (#∈ω n)) ω∈Lsetlam))

  -- THE JUNK MEMBER of the LJ-1.84 refutation.
  c₀ : Sʟ
  c₀ = prʟ K₀ (prʟ (numeralL 6) (numeralL 0))

  fstC₀ : fst c₀ ≡ pr (fst K₀) (pr (# 6) (fst (numeralL 0)))
  fstC₀ = prʟ-fst K₀ (prʟ (numeralL 6) (numeralL 0))
        ∙ cong (pr (fst K₀))
            (prʟ-fst (numeralL 6) (numeralL 0)
              ∙ cong (λ q → pr q (fst (numeralL 0))) (numeralL-fst 6))

  -- THE REPAIRED PREMISE EXCLUDES THE JUNK MEMBER.  A member of AllCodes A₀
  -- is a key of a formula over the carrier, so its arity slot is a numeral;
  -- the junk member's arity slot is the stage bound, which is not a numeral.
  c₀∉All : ⟨ fst c₀ ∈ˢ fst (AllCodes A₀) ⟩ → Empty.⊥
  c₀∉All h = PT.rec Empty.isProp⊥ go (AllCodes-out A₀ c₀ h)
    where
    go : Σ[ n ∈ ℕ ] Σ[ ψ ∈ Formula ⟪ fst A₀ ⟫ n ]
           (fst c₀ ≡ fst (keyS A₀ ψ)) → Empty.⊥
    go (n , ψ , q) = notNumeral n (pr-inj (sym fstC₀ ∙ q) .fst)
