{-# OPTIONS --cubical --safe --guardedness #-}

-- [L3.31-IF-Gp] The b4e D-1 gate, arms 1-3, exactly per
-- _build/b4e-feasibility-recon.md:47-53.  A scratch region in the Closure
-- import context (src/L/Godel/Closure.lagda.md's own imports), the seek
-- machinery restated verbatim from Closure's private block (it is not
-- exported).  Only ONE arm is active per cold check; the others are
-- commented out, because a walling arm would block the whole file.

open import Base.Prelude

module ProbeB4eGate {ℓ : Level} where

open import Base.Truth using ( hPropAlgebra )
import FOL.Semantics
open import FOL.Syntax
  using ( Formula; Term; var; con
        ; _∈̇_; _≐_; _∧̇_; _∨̇_; _⇒̇_; ∃̇_; ∀̇∈; ∃̇∈ )
open import FOL.Manipulation.Relabelling using ( mapFo )
open import V.Hierarchy {ℓ} using ( 𝒮ᵥ )
open import V.Coding {ℓ} using ( pr )
open import V.Model {ℓ} using ( self∈sucV )
open import L.Coding.Environment {ℓ} using ( sucAt-adequate )
open import L.Definability {ℓ} using ( module DefOf )
open import L.Constructible {ℓ} using ( Lset )
open import L.Coding.Base {ℓ}
  using ( prAt-adequate; ∈pair-introL; ∈pair-introR; ∈pair-elim )
open import L.Godel.Operations {ℓ} using ( singleton-self )
open import Cubical.Data.FinData using ( Fin; zero; suc )
open import Cubical.HITs.CumulativeHierarchy.Base using ( V; _∈_ )
open import Cubical.HITs.CumulativeHierarchy.Properties using ( ⟪_⟫; ⟪_⟫↪ )
import Cubical.HITs.PropositionalTruncation as PT
open PT using ( ∣_∣₁; ∥_∥₁; squash₁ )
open import Cubical.HITs.CumulativeHierarchy.Constructions
  using ( ∅; ⁅_,_⁆; ⁅_⁆s; module InfinitySet )
module IS = InfinitySet {ℓ}
open IS using ( sucV )

module SemV = FOL.Semantics (hPropAlgebra (ℓ-suc ℓ)) 𝒮ᵥ
open SemV.At (V ℓ) id renaming ( _⊨_ to _⊨v_ )

-- The shift's seek machinery, restated verbatim from Closure's private
-- block (Closure.lagda.md:2356-2443): the successor atom, the pair readers,
-- and the seek sentence with its six-deep chain.
private
  f1 : {n : ℕ} → Fin (suc (suc n))
  f1 = suc zero
  f2 : {n : ℕ} → Fin (suc (suc (suc n)))
  f2 = suc f1
  f3 : {n : ℕ} → Fin (suc (suc (suc (suc n))))
  f3 = suc f2
  f4 : {n : ℕ} → Fin (suc (suc (suc (suc (suc n)))))
  f4 = suc f3
  f5 : {n : ℕ} → Fin (suc (suc (suc (suc (suc (suc n))))))
  f5 = suc f4
  f6 : {n : ℕ} → Fin (suc (suc (suc (suc (suc (suc (suc n)))))))
  f6 = suc f5
  f7 : {n : ℕ} → Fin (suc (suc (suc (suc (suc (suc (suc (suc n))))))))
  f7 = suc f6

  sglAt′ : {ℓ' : Level} {K : Type ℓ'} {n : ℕ} → Fin n → Fin n → Formula K n
  sglAt′ k i = (var i ∈̇ var k) ∧̇ (∀̇∈ (var k) (var zero ≐ var (suc i)))

  pairAt′ : {ℓ' : Level} {K : Type ℓ'} {n : ℕ} → Fin n → Fin n → Fin n → Formula K n
  pairAt′ k i j = (var i ∈̇ var k) ∧̇ ((var j ∈̇ var k)
              ∧̇ (∀̇∈ (var k) ((var zero ≐ var (suc i)) ∨̇ (var zero ≐ var (suc j)))))

  prAt′ : {ℓ' : Level} {K : Type ℓ'} {n : ℕ} → Fin n → Fin n → Fin n → Formula K n
  prAt′ q u v = (∃̇∈ (var q) (sglAt′ zero (suc u)))
             ∧̇ ((∃̇∈ (var q) (pairAt′ zero (suc u) (suc v)))
             ∧̇ (∀̇∈ (var q) (sglAt′ zero (suc u) ∨̇ pairAt′ zero (suc u) (suc v))))

  sucAt′ : {ℓ' : Level} {K : Type ℓ'} {n : ℕ} → Fin n → Fin n → Formula K n
  sucAt′ i j = (var i ∈̇ var j)
            ∧̇ ((∀̇∈ (var i) (var zero ∈̇ var (suc j)))
            ∧̇ (∀̇∈ (var j) ((var zero ∈̇ var (suc i)) ∨̇ (var zero ≐ var (suc i)))))

  tailBody : {ℓ' : Level} {K : Type ℓ'} {m : ℕ}
           → Formula K (suc (suc (suc (suc (suc (suc (suc m)))))))
  tailBody = prAt′ f5 f3 f1 ∧̇ (sucAt′ zero f3 ∧̇ prAt′ f6 zero f1)

  tailSeek : {ℓ' : Level} {K : Type ℓ'} {m : ℕ} → Term K (suc m) → Formula K (suc m)
  tailSeek B = ∃̇∈ B (∃̇∈ (var zero) (∃̇∈ (var zero)
                 (∃̇∈ (var f2) (∃̇∈ (var zero) (∃̇∈ (var f2) tailBody)))))

-- ==== Arm 1 INACTIVE (result: green 51 s / 48 s confirm, no wall) ====
-- module Arm1 (τ : V ℓ) (mX m' : ⟪ Lset (sucV (sucV (sucV (sucV τ)))) ⟫) where
--   module DefA = DefOf (Lset (sucV (sucV (sucV (sucV τ)))))
--   E : ⟪ Lset (sucV (sucV (sucV (sucV τ)))) ⟫ → V ℓ
--   E m = ⟪ Lset (sucV (sucV (sucV (sucV τ)))) ⟫↪ m
--
--   Φ : Formula ⟪ Lset (sucV (sucV (sucV (sucV τ)))) ⟫ 1
--   Φ = ∃̇∈ (con mX)
--         ( (∀̇∈ (var f1) (tailSeek (var f1)))
--         ∧̇ (∀̇∈ (var zero) (∀̇∈ (var zero) (∀̇∈ (var zero)
--              (∀̇∈ (var f2) (∀̇∈ (var zero) (∀̇∈ (var f2)
--                ((prAt′ f5 f3 f1 ∧̇ sucAt′ zero f3)
--                  ⇒̇ ∃̇∈ (var f7) (prAt′ zero f1 f2)))))))) )
--
--   arm1 : ⟨ (E m' ∷ []) ⊨v mapFo fst (mapFo DefA.ι Φ) ⟩
--   arm1 = {!!}

-- ==== Arm 2 INACTIVE (result: green 26 s) ====
-- module Arm2 (τ : V ℓ) where
--   module DefA = DefOf (Lset (sucV (sucV (sucV (sucV τ)))))
--
--   arm2 : (Φ : Formula ⟪ Lset (sucV (sucV (sucV (sucV τ)))) ⟫ 1) (z : V ℓ)
--        → ⟨ (z ∷ []) ⊨v mapFo fst (mapFo DefA.ι Φ) ⟩
--   arm2 Φ z = {!!}

-- ==== Arm 3 ACTIVE ====
-- Arm 3 (restricted carrier, r3a, abort 120 s): the seek sentence's
-- membership shape at the restricted carrier SM₄ = Σ[ v ∈ V ℓ ] ⟨ v ∈
-- Lset (sucV⁴ τ) ⟩, endpoint fst x (certificate carried by the index, no
-- eliminator application in any type), the satisfaction written by the
-- delivered seekIn and read by the delivered seekOut with its six
-- truncation branches written (I-5), at sucV⁴.  Result: green 2 s.
module Arm3 (τ : V ℓ) where
  SM₄ : Type (ℓ-suc ℓ)
  SM₄ = Σ[ v ∈ V ℓ ] ⟨ v ∈ Lset (sucV (sucV (sucV (sucV τ)))) ⟩

  memShape-in : (B : Term (V ℓ) 1) (x : SM₄) (a v : V ℓ)
              → ⟦ var zero ⟧ (fst x ∷ []) ≡ pr a v
              → ⟨ pr (sucV a) v ∈ ⟦ B ⟧ (fst x ∷ []) ⟩
              → ⟨ (fst x ∷ []) ⊨v tailSeek B ⟩
  memShape-in B x a v e h = seekIn B (fst x ∷ []) a v e h
    where
    seekIn : {n : ℕ} (B : Term (V ℓ) (suc n)) (δ : (V ℓ) SemV.^ (suc n)) (a v : V ℓ)
           → ⟦ var zero ⟧ δ ≡ pr a v → ⟨ pr (sucV a) v ∈ ⟦ B ⟧ δ ⟩
           → ⟨ δ ⊨v tailSeek B ⟩
    seekIn B δ a v e h =
      ∣ pr (sucV a) v , h
      , ∣ ⁅ sucV a ⁆s , ∈pair-introL refl
      , ∣ sucV a , singleton-self (sucV a)
      , ∣ ⁅ sucV a , v ⁆ , ∈pair-introR refl
      , ∣ v , ∈pair-introR refl
      , ∣ a , self∈sucV a
      , ( subst ⟨_⟩ (sym (prAt-adequate f5 f3 f1 env′)) refl
        , subst ⟨_⟩ (sym (sucAt-adequate zero f3 env′)) refl
        , subst ⟨_⟩ (sym (prAt-adequate f6 zero f1 env′)) e )
      ∣₁ ∣₁ ∣₁ ∣₁ ∣₁ ∣₁
      where
      env′ : (V ℓ) SemV.^ (suc (suc (suc (suc (suc (suc (suc _)))))))
      env′ = a ∷ v ∷ ⁅ sucV a , v ⁆ ∷ sucV a ∷ ⁅ sucV a ⁆s ∷ pr (sucV a) v ∷ δ

  memShape-out : (B : Term (V ℓ) 1) (x : SM₄)
               → ⟨ (fst x ∷ []) ⊨v tailSeek B ⟩
               → ∥ Σ[ a ∈ V ℓ ] Σ[ v ∈ V ℓ ]
                    ((⟦ var zero ⟧ (fst x ∷ []) ≡ pr a v)
                     × ⟨ pr (sucV a) v ∈ ⟦ B ⟧ (fst x ∷ []) ⟩) ∥₁
  memShape-out B x h = out₁ B (fst x ∷ []) h
    where
    motive : (B : Term (V ℓ) 1) (δ : (V ℓ) SemV.^ 1) → Type (ℓ-suc ℓ)
    motive B δ = ∥ Σ[ a ∈ V ℓ ] Σ[ v ∈ V ℓ ]
                   ((⟦ var zero ⟧ δ ≡ pr a v) × ⟨ pr (sucV a) v ∈ ⟦ B ⟧ δ ⟩) ∥₁

    mutual
      out₁ : (B : Term (V ℓ) 1) (δ : (V ℓ) SemV.^ 1)
           → ⟨ δ ⊨v tailSeek B ⟩ → motive B δ
      out₁ B δ = PT.rec PT.squash₁ (λ { (p , hp , w₁) → out₂ B δ p hp w₁ })

      out₂ : (B : Term (V ℓ) 1) (δ : (V ℓ) SemV.^ 1) (p : V ℓ)
           → ⟨ p ∈ ⟦ B ⟧ δ ⟩
           → ⟨ (p ∷ δ) ⊨v ∃̇∈ (var zero) (∃̇∈ (var zero)
                 (∃̇∈ (var f2) (∃̇∈ (var zero) (∃̇∈ (var f2) tailBody)))) ⟩
           → motive B δ
      out₂ B δ p hp = PT.rec PT.squash₁ (λ { (d₁ , hd₁ , w₂) → out₃ B δ p d₁ hp hd₁ w₂ })

      out₃ : (B : Term (V ℓ) 1) (δ : (V ℓ) SemV.^ 1) (p d₁ : V ℓ)
           → ⟨ p ∈ ⟦ B ⟧ δ ⟩ → ⟨ d₁ ∈ ⟦ var zero ⟧ (p ∷ δ) ⟩
           → ⟨ (d₁ ∷ p ∷ δ) ⊨v ∃̇∈ (var zero)
                 (∃̇∈ (var f2) (∃̇∈ (var zero) (∃̇∈ (var f2) tailBody))) ⟩
           → motive B δ
      out₃ B δ p d₁ hp hd₁ = PT.rec PT.squash₁ (λ { (s , hs , w₃) → out₄ B δ p d₁ s hp hd₁ hs w₃ })

      out₄ : (B : Term (V ℓ) 1) (δ : (V ℓ) SemV.^ 1) (p d₁ s : V ℓ)
           → ⟨ p ∈ ⟦ B ⟧ δ ⟩ → ⟨ d₁ ∈ ⟦ var zero ⟧ (p ∷ δ) ⟩ → ⟨ s ∈ ⟦ var zero ⟧ (d₁ ∷ p ∷ δ) ⟩
           → ⟨ (s ∷ d₁ ∷ p ∷ δ) ⊨v ∃̇∈ (var f2)
                 (∃̇∈ (var zero) (∃̇∈ (var f2) tailBody)) ⟩
           → motive B δ
      out₄ B δ p d₁ s hp hd₁ hs = PT.rec PT.squash₁ (λ { (d₂ , hd₂ , w₄) → out₅ B δ p d₁ s d₂ hp hd₁ hs hd₂ w₄ })

      out₅ : (B : Term (V ℓ) 1) (δ : (V ℓ) SemV.^ 1) (p d₁ s d₂ : V ℓ)
           → ⟨ p ∈ ⟦ B ⟧ δ ⟩ → ⟨ d₁ ∈ ⟦ var zero ⟧ (p ∷ δ) ⟩ → ⟨ s ∈ ⟦ var zero ⟧ (d₁ ∷ p ∷ δ) ⟩
           → ⟨ d₂ ∈ ⟦ var f2 ⟧ (s ∷ d₁ ∷ p ∷ δ) ⟩
           → ⟨ (d₂ ∷ s ∷ d₁ ∷ p ∷ δ) ⊨v ∃̇∈ (var zero) (∃̇∈ (var f2) tailBody) ⟩
           → motive B δ
      out₅ B δ p d₁ s d₂ hp hd₁ hs hd₂ = PT.rec PT.squash₁ (λ { (v , hv , w₅) → out₆ B δ p d₁ s d₂ v hp hd₁ hs hd₂ hv w₅ })

      out₆ : (B : Term (V ℓ) 1) (δ : (V ℓ) SemV.^ 1) (p d₁ s d₂ v : V ℓ)
           → ⟨ p ∈ ⟦ B ⟧ δ ⟩ → ⟨ d₁ ∈ ⟦ var zero ⟧ (p ∷ δ) ⟩ → ⟨ s ∈ ⟦ var zero ⟧ (d₁ ∷ p ∷ δ) ⟩
           → ⟨ d₂ ∈ ⟦ var f2 ⟧ (s ∷ d₁ ∷ p ∷ δ) ⟩ → ⟨ v ∈ ⟦ var zero ⟧ (d₂ ∷ s ∷ d₁ ∷ p ∷ δ) ⟩
           → ⟨ (v ∷ d₂ ∷ s ∷ d₁ ∷ p ∷ δ) ⊨v ∃̇∈ (var f2) tailBody ⟩
           → motive B δ
      out₆ B δ p d₁ s d₂ v hp hd₁ hs hd₂ hv = PT.rec PT.squash₁ (λ { (a , ha , w₆) → out₇ B δ p d₁ s d₂ v a hp hd₁ hs hd₂ hv ha w₆ })

      out₇ : (B : Term (V ℓ) 1) (δ : (V ℓ) SemV.^ 1) (p d₁ s d₂ v a : V ℓ)
           → ⟨ p ∈ ⟦ B ⟧ δ ⟩ → ⟨ d₁ ∈ ⟦ var zero ⟧ (p ∷ δ) ⟩ → ⟨ s ∈ ⟦ var zero ⟧ (d₁ ∷ p ∷ δ) ⟩
           → ⟨ d₂ ∈ ⟦ var f2 ⟧ (s ∷ d₁ ∷ p ∷ δ) ⟩ → ⟨ v ∈ ⟦ var zero ⟧ (d₂ ∷ s ∷ d₁ ∷ p ∷ δ) ⟩
           → ⟨ a ∈ ⟦ var f2 ⟧ (v ∷ d₂ ∷ s ∷ d₁ ∷ p ∷ δ) ⟩
           → ⟨ (a ∷ v ∷ d₂ ∷ s ∷ d₁ ∷ p ∷ δ) ⊨v tailBody ⟩
           → motive B δ
      out₇ B δ p d₁ s d₂ v a hp hd₁ hs hd₂ hv ha (e₁ , e₂ , e₃) =
        ∣ a , v
        , subst ⟨_⟩ (prAt-adequate f6 zero f1 (a ∷ v ∷ d₂ ∷ s ∷ d₁ ∷ p ∷ δ)) e₃
        , subst (λ w → ⟨ w ∈ ⟦ B ⟧ δ ⟩)
            (subst ⟨_⟩ (prAt-adequate f5 f3 f1 (a ∷ v ∷ d₂ ∷ s ∷ d₁ ∷ p ∷ δ)) e₁
             ∙ cong (λ w → pr w v)
                 (subst ⟨_⟩ (sucAt-adequate zero f3 (a ∷ v ∷ d₂ ∷ s ∷ d₁ ∷ p ∷ δ)) e₂))
            hp ∣₁
