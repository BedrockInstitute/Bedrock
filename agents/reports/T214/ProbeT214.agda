{-# OPTIONS --cubical --safe --guardedness #-}

open import Base.Prelude
open import Base.Truth
open import Base.Classical using ( LEM )
open import Cubical.HITs.CumulativeHierarchy.Base using ( V; sett; setIsSet )

module ProbeT214 {ℓ : Level} (lem : LEM (ℓ-suc ℓ)) (A : V ℓ) where

open import FOL.ZFStructure using ( module hPropStructure )
open import FOL.Syntax
  using ( Term; con; var; Formula
        ; _∈̇_; _≐_; _∧̇_; _∨̇_; _⇒̇_; ¬̇_; ⊤̇; ⊥̇; ∃̇_; ∀̇_; ∀̇∈; ∃̇∈ )
open import FOL.Manipulation.Relabelling using ( mapFo; mapTm )
open import V.Hierarchy {ℓ} using ( 𝒮ᵥ )
open import V.Coding {ℓ} using ( pr; pr-inj; module VCode )
open import L.Constructible {ℓ} using ( IsOrd; Lset; Lset-layer; layer-trans )
open import L.Definability {ℓ} using ( module DefOf )
open import L.Rud.Step {ℓ} lem A
  using ( f0; f5; f9; Fof; Fof-f0; Fof-f5; Fof-f9; singl≡pair
        ; Sset; Sset-trans; Sset-mem; Jset-rud )
open import L.Rud.OrdArith {ℓ} lem using ( isLimit )
open import L.Rud.OrdBlocks {ℓ} lem using ( +ω; +ω-limit; +ω-mem )
open import L.Rud.Ops {ℓ} using ( F0; F0-spec; F2; F2-read; F2-write )
open import L.Rud.StepGraph {ℓ} lem A using ( defSet⊥≡∅ )
open import L.Rud.SatSets {ℓ} lem A using ( module Sat; module LimitFullSwitch )
open import Cubical.Data.FinData using ( toℕ )
open import Cubical.Data.Sum using ( _⊎_; inl; inr )
open import Cubical.HITs.CumulativeHierarchy.Properties
  using ( ⟪_⟫; ⟪_⟫↪; ∈∈ₛ; ∈ₛ⟪_⟫↪_ )
open import Cubical.HITs.CumulativeHierarchy.Constructions
  using ( ∅; ⁅_,_⁆; ⁅_⁆s; ⋃_; module InfinitySet )
open InfinitySet using ( sucV; #_ )
import Cubical.HITs.PropositionalTruncation as PT
open PT using ( ∥_∥₁; ∣_∣₁ )

open TruthAlgebra (hPropAlgebra (ℓ-suc ℓ))
open hPropStructure 𝒮ᵥ

-- The gate's own telescope: δ a limit holding the stage C, block γ = +ω δ.
module Probe (ζ δ : S) (ordδ : IsOrd δ) (limδ : ⟨ isLimit δ ⟩)
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
  C∈γ = Sset-trans γ {x = Sset δ} {y = C} L∈
    (Sset-mem {α = γ} {β = δ} δ∈γ)

  InJ : S → Type (ℓ-suc ℓ)
  InJ x = ⟨ x ∈ˢ Sset γ ⟩

  open DefOf C using ( SM; _⊨ᵐ_ )

  -- Block-level rud closures (D-22: one line per operation).
  pr∈J : (a b : S) → InJ a → InJ b → InJ (pr a b)
  pr∈J a b ha hb = subst (λ w → ⟨ w ∈ˢ Sset γ ⟩) (Fof-f9 a b)
    (Jset-rud γ limγ f9 a b ha hb)

  module LFS = LimitFullSwitch γ limγ δ limδ δ∈γ

  ∅∈γ : ⟨ ∅ ∈ˢ Sset γ ⟩
  ∅∈γ = subst (λ w → ⟨ w ∈ˢ Sset γ ⟩) (defSet⊥≡∅ (Sset δ))
    (LFS.full-switch-⊇ ⊥̇)

  singleton-rud : (x : S) → Fof f0 x x ≡ ⁅ x ⁆s
  singleton-rud x = Fof-f0 x x ∙ sym (singl≡pair x)

  sucV-rud : (x : S) → Fof f5 (Fof f0 x (Fof f0 x x)) x ≡ sucV x
  sucV-rud x = Fof-f5 (Fof f0 x (Fof f0 x x)) x
    ∙ cong ⋃_ (Fof-f0 x (Fof f0 x x)
               ∙ cong (λ w → ⁅ x , w ⁆) (singleton-rud x))

  sucV∈J : (x : S) → InJ x → InJ (sucV x)
  sucV∈J x hx = subst (λ w → ⟨ w ∈ˢ Sset γ ⟩) (sucV-rud x)
    (Jset-rud γ limγ f5 (Fof f0 x (Fof f0 x x)) x
      (Jset-rud γ limγ f0 x (Fof f0 x x) hx
        (Jset-rud γ limγ f0 x x hx hx))
      hx)

  numeral∈J : (a : S) → InJ a → (k : ℕ) → InJ (# k)
  numeral∈J a ha zero    = ∅∈γ
  numeral∈J a ha (suc k) = sucV∈J (# k) (numeral∈J a ha k)

  sgl : S → V ℓ
  sgl x = F0 x x

  hSgl : (x : S) → InJ x → InJ (sgl x)
  hSgl x hx = subst (λ w → ⟨ w ∈ˢ Sset γ ⟩) (Fof-f0 x x)
    (Jset-rud γ limγ f0 x x hx hx)

  sgl-in : (x t : V ℓ) → ⟨ t ∈ˢ sgl x ⟩ → t ≡ x
  sgl-in x t h = PT.rec (setIsSet t x) go (F0-spec x x t .fst h)
    where
    go : (t ≡ x) ⊎ (t ≡ x) → t ≡ x
    go (inl p) = p
    go (inr p) = p

  sgl-out : (x t : V ℓ) → t ≡ x → ⟨ t ∈ˢ sgl x ⟩
  sgl-out x t p = F0-spec x x t .snd ∣ inl p ∣₁

  -- The delivered Sat engine over the stage, closure the block.
  module S = Sat C
    (λ x y x∈y y∈C → layer-trans (Lset-layer ζ) {x = y} {y = x} x∈y y∈C)
    InJ
    (λ a b hb a∈b → Sset-trans γ {x = b} {y = a} a∈b hb)
    (Jset-rud γ limγ)
    C∈γ

  -- The delivered code map over the stage.
  ι : ⟪ C ⟫ → S
  ι = ⟪ C ⟫↪

  codeTm : ∀ {n} → Term ⟪ C ⟫ n → S
  codeTm t = VCode.⌜ mapTm ι t ⌝ᵗ

  code : ∀ {n} → Formula ⟪ C ⟫ n → S
  code φ = VCode.⌜ mapFo ι φ ⌝

  -- Containment half at the block: every code is a member of Sset γ.
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

  -- The code fragment: one atom, one binary connective, one quantifier.
  data Code : ℕ → Type where
    at  : {n : ℕ} → (i j : Fin (suc n)) → Code n
    bin : {n : ℕ} → Code n → Code n → Code n
    qu  : {n : ℕ} → Code (suc n) → Code n

  dec : {n : ℕ} → Code n → Formula ⟪ C ⟫ (suc n)
  dec (at i j) = var i ∈̇ var j
  dec (bin c d) = dec c ∧̇ dec d
  dec (qu c) = ∃̇ dec c

  -- The satisfaction-as-member clauses: pairs (code c, tuple) satisfied.
  R : {n : ℕ} → Code n → V ℓ
  R (at i j) = F2 (sgl (code (var i ∈̇ var j))) (S.T _ (var i ∈̇ var j))
  R (bin c d) = F2 (sgl (code (dec (bin c d)))) (S.T _ (dec (bin c d)))
  R (qu c) = F2 (sgl (code (dec (qu c)))) (S.T _ (dec (qu c)))

  -- Code membership follows the code recursion.
  code∈Jf : {n : ℕ} (c : Code n) → InJ (code (dec c))
  code∈Jf (at i j) = mkTag∈J 0 (pr (codeTm (var i)) (codeTm (var j)))
    (pr∈J (codeTm (var i)) (codeTm (var j))
      (codeTm∈J (var i)) (codeTm∈J (var j)))
  code∈Jf (bin c d) = mkTag∈J 2 (pr (code (dec c)) (code (dec d)))
    (pr∈J (code (dec c)) (code (dec d)) (code∈Jf c) (code∈Jf d))
  code∈Jf (qu c) = mkTag∈J 8 (code (dec c)) (code∈Jf c)

  -- The Sat member: each pair-set is a member of the block.
  hR : {n : ℕ} (c : Code n) → InJ (R c)
  hR (at i j) = S.JF2 (sgl (code (var i ∈̇ var j))) (S.T _ (var i ∈̇ var j))
    (hSgl (code (var i ∈̇ var j)) (code∈Jf (at i j)))
    (S.hT _ (var i ∈̇ var j))
  hR (bin c d) = S.JF2 (sgl (code (dec (bin c d)))) (S.T _ (dec (bin c d)))
    (hSgl (code (dec (bin c d))) (code∈Jf (bin c d)))
    (S.hT _ (dec (bin c d)))
  hR (qu c) = S.JF2 (sgl (code (dec (qu c)))) (S.T _ (dec (qu c)))
    (hSgl (code (dec (qu c))) (code∈Jf (qu c)))
    (S.hT _ (dec (qu c)))

  -- The pair glue, once: read and write a pair (k, t) in F2 (sgl k) X.
  pair-out : (k X t : V ℓ) → ⟨ pr k t ∈ˢ F2 (sgl k) X ⟩ → ⟨ t ∈ˢ X ⟩
  pair-out k X t h = PT.rec (snd (t ∈ˢ X)) go (F2-read (sgl k) X (pr k t) h)
    where
    go : Σ[ p ∈ V ℓ ] Σ[ q ∈ V ℓ ]
           (⟨ p ∈ˢ sgl k ⟩ × ⟨ q ∈ˢ X ⟩ × (pr k t ≡ pr p q))
       → ⟨ t ∈ˢ X ⟩
    go (p , q , hp , hq , eq) = subst (λ w → ⟨ w ∈ˢ X ⟩) (sym (pr-inj eq .snd)) hq

  pair-in : (k X t : V ℓ) → ⟨ t ∈ˢ X ⟩ → ⟨ pr k t ∈ˢ F2 (sgl k) X ⟩
  pair-in k X t h = F2-write (sgl k) X (pr k t)
    ∣ k , t , (sgl-out k k refl , h , refl) ∣₁

  -- Both decode directions, at a tuple (D-11: never at a member).
  R-out : {n : ℕ} (c : Code n) (δ : Vec SM (suc n))
        → ⟨ pr (code (dec c)) (S.Tup _ δ) ∈ˢ R c ⟩ → ⟨ δ ⊨ᵐ dec c ⟩
  R-out (at i j) δ h =
    S.adeq-mem _ (var i ∈̇ var j) δ
      (pair-out (code (var i ∈̇ var j)) (S.T _ (var i ∈̇ var j))
        (S.Tup _ δ) h)
  R-out (bin c d) δ h =
    S.adeq-mem _ (dec c ∧̇ dec d) δ
      (pair-out (code (dec (bin c d))) (S.T _ (dec (bin c d)))
        (S.Tup _ δ) h)
  R-out (qu c) δ h =
    S.adeq-mem _ (∃̇ dec c) δ
      (pair-out (code (dec (qu c))) (S.T _ (dec (qu c)))
        (S.Tup _ δ) h)

  R-in : {n : ℕ} (c : Code n) (δ : Vec SM (suc n))
       → ⟨ δ ⊨ᵐ dec c ⟩ → ⟨ pr (code (dec c)) (S.Tup _ δ) ∈ˢ R c ⟩
  R-in (at i j) δ h =
    pair-in (code (var i ∈̇ var j)) (S.T _ (var i ∈̇ var j)) (S.Tup _ δ)
      (S.adeq-set _ (var i ∈̇ var j) δ h)
  R-in (bin c d) δ h =
    pair-in (code (dec (bin c d))) (S.T _ (dec (bin c d))) (S.Tup _ δ)
      (S.adeq-set _ (dec (bin c d)) δ h)
  R-in (qu c) δ h =
    pair-in (code (dec (qu c))) (S.T _ (dec (qu c))) (S.Tup _ δ)
      (S.adeq-set _ (dec (qu c)) δ h)

  -- Satisfaction-as-member at a pair, both directions.
  R-iff : {n : ℕ} (c : Code n) (δ : Vec SM (suc n))
        → (⟨ pr (code (dec c)) (S.Tup _ δ) ∈ˢ R c ⟩ → ⟨ δ ⊨ᵐ dec c ⟩)
        × (⟨ δ ⊨ᵐ dec c ⟩ → ⟨ pr (code (dec c)) (S.Tup _ δ) ∈ˢ R c ⟩)
  R-iff c δ = R-out c δ , R-in c δ
