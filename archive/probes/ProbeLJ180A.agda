{-# OPTIONS --cubical --safe --guardedness #-}

open import Base.Prelude
open import Base.Truth
open import Base.Classical using ( LEM )

module ProbeLJ180A {ℓ : Level} (lem : LEM (ℓ-suc ℓ)) where

open import FOL.ZFStructure using ( ZFStructure; module hPropStructure )
open import V.Hierarchy {ℓ} using ( 𝒮ᵥ )
open import L.Constructible {ℓ}
  using ( 𝒮ʟ; isL; isL-trans; IsOrd; Lset; 𝒟ₒ; Lset-out; Lset-mono; layer-trans; Lset-layer )
open import L.Condensation {ℓ} lem using ( module KFactsNS )
open import L.Axioms.Numerals {ℓ} using ( numeralL; numeralL-fst )
open import L.Coding.Model {ℓ} using ( prʟ; prʟ-fst )
open import L.Axioms.Basic {ℓ} using ( LsetS; Lset-suc; pr∈Lset-suc )
open import L.Ordinal {ℓ} using ( ω-ord; #∈ω; ∅-ord; numeral-ord; mem-ord )
open import L.Ordinal.Stages {ℓ} lem using ( suc∈or≡; ord∈Lset-suc )
open import L.Ordinal.Linear {ℓ} lem using ( ord-tri; Tri )
open import V.Coding {ℓ} using ( pr )
open import V.Model {ℓ} using ( ∈sucV-inl; self∈sucV )
open import Cubical.Data.Vec using ( Vec; lookup; _∷_; [] )
open import Cubical.Data.FinData using ( toℕ )
open import Cubical.Data.Nat using ( _+_; +-suc; +-zero )
import FOL.Absoluteness
import Cubical.Data.Empty as Empty
import Cubical.Data.Sum as Sum
open import Cubical.Data.Sum using ( _⊎_; inl; inr )
import Cubical.HITs.PropositionalTruncation as PT
open PT using ( ∥_∥₁ )
open import Cubical.HITs.CumulativeHierarchy.Constructions using ( module InfinitySet )
open InfinitySet using ( ω; sucV; #_ )

open TruthAlgebra (hPropAlgebra (ℓ-suc ℓ))
open hPropStructure 𝒮ᵥ

module AbsL = FOL.Absoluteness.Single 𝒮ᵥ isL isL-trans
open AbsL using ( _^_ )

Sʟ : Type (ℓ-suc ℓ)
Sʟ = ZFStructure.S 𝒮ʟ

-- The KFacts value at the limit stage: K = Lset lam, A = Lset alpha.
-- Every closure property is the stage's own, delivered by the tower.
module StageKFacts
  (lam : S) (ordλ : IsOrd lam)
  (succλ : (d : S) → ⟨ d ∈ˢ lam ⟩ → ⟨ sucV d ∈ˢ lam ⟩)
  (α : S) (ordα : IsOrd α) (α∈λ : ⟨ α ∈ˢ lam ⟩)
  (α∉ω : ⟨ α ∈ˢ ω ⟩ → Empty.⊥)
  where

  -- The two constructible slot values.
  K : Sʟ
  K = LsetS lam ordλ

  A : Sʟ
  A = LsetS α ordα

  -- The numeral vector: the m entries numeralL j, numeralL (j+1), ...
  numFrom : (j : ℕ) → (m : ℕ) → Sʟ ^ m
  numFrom j zero = []
  numFrom j (suc m) = numeralL j ∷ numFrom (suc j) m

  numFrom-spec : (j m : ℕ) (k : Fin m) → lookup k (numFrom j m) ≡ numeralL (j + toℕ k)
  numFrom-spec j zero ()
  numFrom-spec j (suc m) zero = cong numeralL (sym (+-zero j))
  numFrom-spec j (suc m) (suc k) =
    numFrom-spec (suc j) m k ∙ sym (cong numeralL (+-suc j (toℕ k)))

  -- The environment: A, K, then the twelve numerals.
  γ : Sʟ ^ 14
  γ = A ∷ K ∷ numFrom 0 12

  A₀ : Fin 14
  A₀ = zero

  K₀ : Fin 14
  K₀ = suc zero

  Nk : Fin 12 → Fin 14
  Nk k = suc (suc k)

  -- omega lies in lam: lam is infinite because alpha is infinite and
  -- alpha lies in lam.
  ω∈lam : ⟨ ω ∈ˢ lam ⟩
  ω∈lam = Sum.rec
    (λ lam∈ω → Empty.rec (α∉ω (ω-ord .fst {x = lam} {y = α} α∈λ lam∈ω)))
    (Sum.rec (λ lam≡ω → Empty.rec (α∉ω (subst (λ w → ⟨ α ∈ˢ w ⟩) lam≡ω α∈λ)))
             (λ h → h))
    (ord-tri lam ordλ ω ω-ord)

  -- Each numeral lies in lam.
  #-in-lam : (j : ℕ) → ⟨ (# j) ∈ˢ lam ⟩
  #-in-lam j = ordλ .fst {x = ω} {y = # j} (#∈ω j) ω∈lam

  -- Each numeral lies in the stage below its successor index: # (suc j)
  -- is definitionally sucV (# j).
  numeral-in-stage : (j : ℕ) → ⟨ (# j) ∈ˢ Lset (# (suc j)) ⟩
  numeral-in-stage j = ord∈Lset-suc (# j) (numeral-ord j)

  -- Each numeral lies in Lset lam.
  numeral-in-lam : (k : ℕ) → ⟨ fst (numeralL k) ∈ˢ Lset lam ⟩
  numeral-in-lam k = subst (λ w → ⟨ w ∈ˢ Lset lam ⟩) (sym (numeralL-fst k))
    (Lset-mono {α = lam} {β = # (suc k)} (#-in-lam (suc k))
      (numeral-in-stage k))

  -- The stage is closed under the ordered pair: from x y in Lset lam,
  -- lift both to one successor stage below lam (trichotomy on their
  -- stage indices), form the pair two stages above it, and close lam
  -- under successors.
  pair-in-lam : (x y : S) → ⟨ x ∈ˢ Lset lam ⟩ → ⟨ y ∈ˢ Lset lam ⟩
              → ⟨ pr x y ∈ˢ Lset lam ⟩
  pair-in-lam x y x∈ y∈ = PT.rec (snd (pr x y ∈ˢ Lset lam)) gox (Lset-out lam x x∈)
    where
    gox : Σ[ δx ∈ S ] (⟨ δx ∈ˢ lam ⟩ × ⟨ x ∈ˢ 𝒟ₒ (Lset δx) ⟩)
        → ⟨ pr x y ∈ˢ Lset lam ⟩
    gox (δx , δx∈ , x∈𝒟ₒδx) =
      PT.rec (snd (pr x y ∈ˢ Lset lam)) goy (Lset-out lam y y∈)
      where
      x∈Lsx : ⟨ x ∈ˢ Lset (sucV δx) ⟩
      x∈Lsx = subst (λ w → ⟨ x ∈ˢ w ⟩) (sym (Lset-suc δx)) x∈𝒟ₒδx
      goy : Σ[ δy ∈ S ] (⟨ δy ∈ˢ lam ⟩ × ⟨ y ∈ˢ 𝒟ₒ (Lset δy) ⟩)
          → ⟨ pr x y ∈ˢ Lset lam ⟩
      goy (δy , δy∈ , y∈𝒟ₒδy) = tri (ord-tri δx oδx δy oδy)
        where
        oδx : IsOrd δx
        oδx = mem-ord {A = lam} ordλ δx δx∈
        oδy : IsOrd δy
        oδy = mem-ord {A = lam} ordλ δy δy∈
        y∈Lsy : ⟨ y ∈ˢ Lset (sucV δy) ⟩
        y∈Lsy = subst (λ w → ⟨ y ∈ˢ w ⟩) (sym (Lset-suc δy)) y∈𝒟ₒδy
        liftPair : (δ : S) → ⟨ δ ∈ˢ lam ⟩
                 → ⟨ x ∈ˢ Lset (sucV δ) ⟩ → ⟨ y ∈ˢ Lset (sucV δ) ⟩
                 → ⟨ pr x y ∈ˢ Lset lam ⟩
        liftPair δ δ∈ hx hy =
          Lset-mono {α = lam} {β = sucV (sucV (sucV δ))}
            (succλ (sucV (sucV δ)) (succλ (sucV δ) (succλ δ δ∈)))
            (pr∈Lset-suc (sucV δ) x y hx hy)
        tri : Tri δx δy → ⟨ pr x y ∈ˢ Lset lam ⟩
        tri (inl δx∈δy) = liftPair δy δy∈
          (Lset-mono {α = sucV δy} {β = sucV δx}
            (Sum.rec (λ (h : ⟨ sucV δx ∈ˢ δy ⟩) → ∈sucV-inl {A = δy} {x = sucV δx} h)
                     (λ (h : sucV δx ≡ δy) →
                        subst (λ w → ⟨ w ∈ˢ sucV δy ⟩) (sym h) (self∈sucV δy))
                     (suc∈or≡ δx δy oδx oδy δx∈δy))
            x∈Lsx)
          y∈Lsy
        tri (inr (inl eq)) = liftPair δx δx∈ x∈Lsx
          (subst (λ w → ⟨ y ∈ˢ Lset (sucV w) ⟩) (sym eq) y∈Lsy)
        tri (inr (inr δy∈δx)) = liftPair δx δx∈ x∈Lsx
          (Lset-mono {α = sucV δx} {β = sucV δy}
            (Sum.rec (λ (h : ⟨ sucV δy ∈ˢ δx ⟩) → ∈sucV-inl {A = δx} {x = sucV δy} h)
                     (λ (h : sucV δy ≡ δx) →
                        subst (λ w → ⟨ w ∈ˢ sucV δx ⟩) (sym h) (self∈sucV δx))
                     (suc∈or≡ δy δx oδy oδx δy∈δx))
            y∈Lsy)

  pair-closed : (a b : Sʟ) → ⟨ fst a ∈ˢ fst K ⟩ → ⟨ fst b ∈ˢ fst K ⟩
              → ⟨ fst (prʟ a b) ∈ˢ fst K ⟩
  pair-closed a b ha hb = subst (λ w → ⟨ w ∈ˢ fst K ⟩) (sym (prʟ-fst a b))
    (pair-in-lam (fst a) (fst b) ha hb)

  numK : (k : Fin 12) → ⟨ fst (numeralL (toℕ k)) ∈ˢ fst (lookup (suc zero) γ) ⟩
  numK k = numeral-in-lam (toℕ k)

  tagEq : (k : Fin 12) → fst (lookup (Nk k) γ) ≡ fst (numeralL (toℕ k))
  tagEq k = cong fst (numFrom-spec 0 12 k)

  carrierK : (v : Sʟ) → ⟨ fst v ∈ˢ fst (lookup zero γ) ⟩
           → ⟨ fst v ∈ˢ fst (lookup (suc zero) γ) ⟩
  carrierK v hv = Lset-mono {α = lam} {β = α} α∈λ hv

  arityK : (N v : Sʟ) → ⟨ fst v ∈ˢ fst N ⟩ → ⟨ fst N ∈ˢ fst (lookup (suc zero) γ) ⟩
         → ⟨ fst v ∈ˢ fst (lookup (suc zero) γ) ⟩
  arityK N v hv hN = layer-trans (Lset-layer lam) {x = fst N} {y = fst v} hv hN

  innerK : (k : ℕ) (a : Sʟ) → ⟨ fst a ∈ˢ fst K ⟩
         → ⟨ fst (prʟ (numeralL k) a) ∈ˢ fst K ⟩
  innerK k a ha = pair-closed (numeralL k) a (numeral-in-lam k) ha

  innerPairK : (k : ℕ) (a b : Sʟ) → ⟨ fst a ∈ˢ fst K ⟩ → ⟨ fst b ∈ˢ fst K ⟩
             → ⟨ fst (prʟ (numeralL k) (prʟ a b)) ∈ˢ fst K ⟩
  innerPairK k a b ha hb =
    pair-closed (numeralL k) (prʟ a b) (numeral-in-lam k) (pair-closed a b ha hb)

  kfacts : KFactsNS.KFacts {14} A₀ K₀
    (Nk zero) (Nk (suc zero)) (Nk (suc (suc zero)))
    (Nk (suc (suc (suc zero)))) (Nk (suc (suc (suc (suc zero)))))
    (Nk (suc (suc (suc (suc (suc zero))))))
    (Nk (suc (suc (suc (suc (suc (suc zero)))))))
    (Nk (suc (suc (suc (suc (suc (suc (suc zero))))))))
    (Nk (suc (suc (suc (suc (suc (suc (suc (suc zero)))))))))
    (Nk (suc (suc (suc (suc (suc (suc (suc (suc (suc zero))))))))))
    (Nk (suc (suc (suc (suc (suc (suc (suc (suc (suc (suc zero)))))))))))
    (Nk (suc (suc (suc (suc (suc (suc (suc (suc (suc (suc (suc zero))))))))))))
    γ
  kfacts = record
    { tagEq0 = tagEq zero
    ; tagEq1 = tagEq (suc zero)
    ; tagEq2 = tagEq (suc (suc zero))
    ; tagEq3 = tagEq (suc (suc (suc zero)))
    ; tagEq4 = tagEq (suc (suc (suc (suc zero))))
    ; tagEq5 = tagEq (suc (suc (suc (suc (suc zero)))))
    ; tagEq6 = tagEq (suc (suc (suc (suc (suc (suc zero))))))
    ; tagEq7 = tagEq (suc (suc (suc (suc (suc (suc (suc zero)))))))
    ; tagEq8 = tagEq (suc (suc (suc (suc (suc (suc (suc (suc zero))))))))
    ; tagEq9 = tagEq (suc (suc (suc (suc (suc (suc (suc (suc (suc zero)))))))))
    ; tagEq10 = tagEq (suc (suc (suc (suc (suc (suc (suc (suc (suc (suc zero))))))))))
    ; tagEq11 = tagEq (suc (suc (suc (suc (suc (suc (suc (suc (suc (suc (suc zero)))))))))))
    ; numK0 = numK zero
    ; numK1 = numK (suc zero)
    ; numK2 = numK (suc (suc zero))
    ; numK3 = numK (suc (suc (suc zero)))
    ; numK4 = numK (suc (suc (suc (suc zero))))
    ; numK5 = numK (suc (suc (suc (suc (suc zero)))))
    ; numK6 = numK (suc (suc (suc (suc (suc (suc zero))))))
    ; numK7 = numK (suc (suc (suc (suc (suc (suc (suc zero)))))))
    ; numK8 = numK (suc (suc (suc (suc (suc (suc (suc (suc zero))))))))
    ; numK9 = numK (suc (suc (suc (suc (suc (suc (suc (suc (suc zero)))))))))
    ; numK10 = numK (suc (suc (suc (suc (suc (suc (suc (suc (suc (suc zero))))))))))
    ; numK11 = numK (suc (suc (suc (suc (suc (suc (suc (suc (suc (suc (suc zero)))))))))))
    ; innerK = innerK
    ; innerPairK = innerPairK
    ; pairK = pair-closed
    ; carrierK = carrierK
    ; arityK = arityK }
