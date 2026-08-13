{-# OPTIONS --cubical --safe --guardedness #-}

open import Base.Prelude
open import Base.Truth
open import Base.Classical using ( LEM )
open import Cubical.HITs.CumulativeHierarchy.Base using ( V; sett )

module ProbeT211 {ℓ : Level} (lem : LEM (ℓ-suc ℓ)) (A : V ℓ) where

open import FOL.ZFStructure using ( module hPropStructure )
open import FOL.Syntax
  using ( Term; con; var; Formula
        ; _∈̇_; _≐_; _∧̇_; _∨̇_; _⇒̇_; ¬̇_; ⊤̇; ⊥̇; ∃̇_; ∀̇_; ∀̇∈; ∃̇∈ )
open import FOL.Manipulation.Relabelling using ( mapFo; mapTm )
open import V.Hierarchy {ℓ} using ( 𝒮ᵥ )
open import V.Coding {ℓ} using ( pr; module VCode )
open import L.Constructible {ℓ} using ( IsOrd; Lset )
open import L.Definability {ℓ} using ( module DefOf )
open import L.Rud.Step {ℓ} lem A
  using ( f0; f5; f9; Fof; Fof-f0; Fof-f5; Fof-f9; singl≡pair
        ; Sset; Sset-trans; Sset-mem; Jset-rud )
open import L.Rud.OrdArith {ℓ} lem using ( isLimit )
open import L.Rud.OrdBlocks {ℓ} lem using ( +ω; +ω-limit; +ω-mem )
open import L.Rud.StepGraph {ℓ} lem A using ( defSet⊥≡∅ )
open import L.Rud.SatSets {ℓ} lem A using ( module LimitFullSwitch )
open import Cubical.Data.FinData using ( toℕ )
open import Cubical.HITs.CumulativeHierarchy.Properties
  using ( ⟪_⟫; ⟪_⟫↪; ∈∈ₛ; ∈ₛ⟪_⟫↪_ )
open import Cubical.HITs.CumulativeHierarchy.Constructions
  using ( ∅; ⁅_,_⁆; ⁅_⁆s; ⋃_; module InfinitySet )
open InfinitySet using ( sucV; #_ )
import Cubical.HITs.PropositionalTruncation as PT
open PT using ( ∥_∥₁; ∣_∣₁ )

open TruthAlgebra (hPropAlgebra (ℓ-suc ℓ))
open hPropStructure 𝒮ᵥ

-- The gate's own telescope: δ a limit holding C, γ = +ω δ.
module PartI (ζ δ : S) (ordδ : IsOrd δ) (limδ : ⟨ isLimit δ ⟩)
             (L∈ : ⟨ Lset ζ ∈ˢ Sset δ ⟩) where

  C : S
  C = Lset ζ

  γ : S
  γ = +ω δ

  limγ : ⟨ isLimit γ ⟩
  limγ = +ω-limit δ ordδ

  δ∈γ : ⟨ δ ∈ˢ γ ⟩
  δ∈γ = +ω-mem δ

  C∈γ : ⟨ C ∈ˢ Sset γ ⟩
  C∈γ = Sset-trans γ {x = Sset δ} {y = C} L∈ (Sset-mem {α = γ} {β = δ} δ∈γ)

  -- 1. The code map and the arity-one family.
  ι : ⟪ C ⟫ → S
  ι = ⟪ C ⟫↪

  codeTm : ∀ {n} → Term ⟪ C ⟫ n → S
  codeTm t = VCode.⌜ mapTm ι t ⌝ᵗ

  code : ∀ {n} → Formula ⟪ C ⟫ n → S
  code φ = VCode.⌜ mapFo ι φ ⌝

  opaque
    codeSet : ℕ → S
    codeSet k = sett (Formula ⟪ C ⟫ k) code

    code∈codeSet : (k : ℕ) (φ : Formula ⟪ C ⟫ k) → ⟨ code φ ∈ˢ codeSet k ⟩
    code∈codeSet k φ = ∣ φ , refl ∣₁

    codeSet-out : (k : ℕ) (x : S) → ⟨ x ∈ˢ codeSet k ⟩
                → ∥ Σ[ φ ∈ Formula ⟪ C ⟫ k ] (code φ ≡ x) ∥₁
    codeSet-out k x h = h

  -- 2. The discharge engine at (δ, +ω δ): the full switch.
  module LFS = LimitFullSwitch γ limγ δ limδ δ∈γ

  defSet∈γ : (Φ : Formula ⟪ Sset δ ⟫ 1)
           → ⟨ DefOf.defSet (Sset δ) Φ ∈ˢ Sset γ ⟩
  defSet∈γ Φ = LFS.full-switch-⊇ Φ

  ∅∈γ : ⟨ ∅ ∈ˢ Sset γ ⟩
  ∅∈γ = subst (λ w → ⟨ w ∈ˢ Sset γ ⟩) (defSet⊥≡∅ (Sset δ))
    (LFS.full-switch-⊇ ⊥̇)

  -- 3. Level arithmetic at the fixed pair.
  singleton-rud : (x : S) → Fof f0 x x ≡ ⁅ x ⁆s
  singleton-rud x = Fof-f0 x x ∙ sym (singl≡pair x)

  sucV-rud : (x : S) → Fof f5 (Fof f0 x (Fof f0 x x)) x ≡ sucV x
  sucV-rud x = Fof-f5 (Fof f0 x (Fof f0 x x)) x
    ∙ cong ⋃_ (Fof-f0 x (Fof f0 x x)
               ∙ cong (λ w → ⁅ x , w ⁆) (singleton-rud x))

  InJ : S → Type (ℓ-suc ℓ)
  InJ x = ⟨ x ∈ˢ Sset γ ⟩

  pr∈J : (a b : S) → InJ a → InJ b → InJ (pr a b)
  pr∈J a b ha hb = subst (λ w → ⟨ w ∈ˢ Sset γ ⟩) (Fof-f9 a b)
    (Jset-rud γ limγ f9 a b ha hb)

  ∅∈J : (a : S) → InJ a → InJ ∅
  ∅∈J a ha = ∅∈γ

  sucV∈J : (x : S) → InJ x → InJ (sucV x)
  sucV∈J x hx = subst (λ w → ⟨ w ∈ˢ Sset γ ⟩) (sucV-rud x)
    (Jset-rud γ limγ f5 (Fof f0 x (Fof f0 x x)) x
      (Jset-rud γ limγ f0 x (Fof f0 x x) hx
        (Jset-rud γ limγ f0 x x hx hx))
      hx)

  numeral∈J : (a : S) → InJ a → (k : ℕ) → InJ (# k)
  numeral∈J a ha zero    = ∅∈J a ha
  numeral∈J a ha (suc k) = sucV∈J (# k) (numeral∈J a ha k)

  -- 4. The containment half: every code is a member of the level.
  member∈J : (m : ⟪ C ⟫) → InJ (ι m)
  member∈J m = Sset-trans γ {x = C} {y = ι m}
    (∈∈ₛ {a = ι m} {b = C} .snd (∈ₛ⟪ C ⟫↪ m)) C∈γ

  numeralJ : (k : ℕ) → InJ (# k)
  numeralJ = numeral∈J C C∈γ

  mkTag∈J : (k : ℕ) (x : S) → InJ x → InJ (VCode.mkTag k x)
  mkTag∈J k x hx = pr∈J (# k) x (numeralJ k) hx

  codeTm∈J : ∀ {n} (t : Term ⟪ C ⟫ n) → InJ (codeTm t)
  codeTm∈J (con m) = mkTag∈J 0 (ι m) (member∈J m)
  codeTm∈J (var i) = mkTag∈J 1 (# (toℕ i)) (numeralJ (toℕ i))

  code∈J : ∀ {n} (φ : Formula ⟪ C ⟫ n) → InJ (code φ)
  code∈J (t ∈̇ u) = mkTag∈J 0 (pr (codeTm t) (codeTm u))
    (pr∈J (codeTm t) (codeTm u) (codeTm∈J t) (codeTm∈J u))
  code∈J (t ≐ u) = mkTag∈J 1 (pr (codeTm t) (codeTm u))
    (pr∈J (codeTm t) (codeTm u) (codeTm∈J t) (codeTm∈J u))
  code∈J (φ ∧̇ ψ) = mkTag∈J 2 (pr (code φ) (code ψ))
    (pr∈J (code φ) (code ψ) (code∈J φ) (code∈J ψ))
  code∈J (φ ∨̇ ψ) = mkTag∈J 3 (pr (code φ) (code ψ))
    (pr∈J (code φ) (code ψ) (code∈J φ) (code∈J ψ))
  code∈J (φ ⇒̇ ψ) = mkTag∈J 4 (pr (code φ) (code ψ))
    (pr∈J (code φ) (code ψ) (code∈J φ) (code∈J ψ))
  code∈J (¬̇ φ)    = mkTag∈J 5 (code φ) (code∈J φ)
  code∈J ⊤̇        = mkTag∈J 6 (# 0) (numeralJ 0)
  code∈J ⊥̇        = mkTag∈J 7 (# 0) (numeralJ 0)
  code∈J (∃̇ φ)    = mkTag∈J 8 (code φ) (code∈J φ)
  code∈J (∀̇ φ)    = mkTag∈J 9 (code φ) (code∈J φ)
  code∈J (∀̇∈ t φ) = mkTag∈J 10 (pr (codeTm t) (code φ))
    (pr∈J (codeTm t) (code φ) (codeTm∈J t) (code∈J φ))
  code∈J (∃̇∈ t φ) = mkTag∈J 11 (pr (codeTm t) (code φ))
    (pr∈J (codeTm t) (code φ) (codeTm∈J t) (code∈J φ))

  codeSet⊆J : (k : ℕ) (x : S) → ⟨ x ∈ˢ codeSet k ⟩ → InJ x
  codeSet⊆J k x h = PT.rec (snd (x ∈ˢ Sset γ))
    (λ { (φ , q) → subst (λ w → ⟨ w ∈ˢ Sset γ ⟩) q (code∈J φ) })
    (codeSet-out k x h)
