# The twelve-row agreement

<!--en-->
The twelve-row agreement conjoins the lower and upper agreements at the
full sixty-nine-fact frame. It applies the two partials' already-proved
`out` and `back`; it does not re-apply the twelve rows.
<!--zh-->
十二行一致在完整的六十九个事实框架上合取下位一致与上位一致。它应用两个偏模块已经证明的 `out` 与 `back`，并不重新应用那十二行。
<!--/-->

```agda
{-# OPTIONS --cubical --safe --guardedness #-}

open import Base.Prelude
open import Base.Truth
open import Base.Classical using ( LEM )

module L.Condensation.TwelveAgree {ℓ : Level} (lem : LEM (ℓ-suc ℓ)) where

open import FOL.ZFStructure using ( module hPropStructure )
open import FOL.Syntax using ( Formula; var; _∈̇_; _∧̇_ )
import FOL.Absoluteness
open import V.Hierarchy {ℓ} using ( 𝒮ᵥ )
open import V.Coding {ℓ} using ( pr )
open import L.Constructible {ℓ} using ( 𝒮ʟ; isL; isL-trans )
open import L.Axioms.Numerals {ℓ} using ( numeralL )
open import L.Coding.Model {ℓ}
  using ( prʟ; envSetAt; envOverAt; tmValAt; subValAt; subValSuccAt; consAtL )
open import L.Coding.EnvSet {ℓ} lem using ( module Generic )
open import L.Coding.Graph {ℓ} lem using ( twelveAt )
open import L.Condensation {ℓ} lem using ( succU; keyU )
open import L.Condensation.LowerAgree {ℓ} lem using
  ( module LowerAgree; module KeyNegTies; someEnvDef )
open import L.Condensation.UpperAgree {ℓ} lem using
  ( module UpperAgree; module SuccKeyTies )
open import Cubical.Data.Nat using ( _+_ )
open import Cubical.HITs.CumulativeHierarchy.Base using ( _∈_ )
open import Cubical.HITs.CumulativeHierarchy.Constructions using ( module InfinitySet )
open InfinitySet using ( #_; sucV )

open TruthAlgebra (hPropAlgebra (ℓ-suc ℓ))
open hPropStructure 𝒮ʟ

module AbsL = FOL.Absoluteness.Single 𝒮ᵥ isL isL-trans
open AbsL renaming ( _⊨ᵐ_ to _⊨_ )

module AbstractFrame {n : ℕ}
  (N0 N1 N2 N3 N4 N5 N6 N7 N8 N9 N10 N11 t0 t1 K : Fin (5 + n))
  (γ' : S ^ (11 + n))
  (tagEq0 : fst (lookup (suc (suc (suc (suc (suc (suc N0)))))) γ') ≡ fst (numeralL 0))
  (tagEq1 : fst (lookup (suc (suc (suc (suc (suc (suc N1)))))) γ') ≡ fst (numeralL 1))
  (tagEq2 : fst (lookup (suc (suc (suc (suc (suc (suc N2)))))) γ') ≡ fst (numeralL 2))
  (tagEq3 : fst (lookup (suc (suc (suc (suc (suc (suc N3)))))) γ') ≡ fst (numeralL 3))
  (tagEq4 : fst (lookup (suc (suc (suc (suc (suc (suc N4)))))) γ') ≡ fst (numeralL 4))
  (tagEq5 : fst (lookup (suc (suc (suc (suc (suc (suc N5)))))) γ') ≡ fst (numeralL 5))
  (tagEq6 : fst (lookup (suc (suc (suc (suc (suc (suc N6)))))) γ') ≡ fst (numeralL 6))
  (tagEq7 : fst (lookup (suc (suc (suc (suc (suc (suc N7)))))) γ') ≡ fst (numeralL 7))
  (tagEq8 : fst (lookup (suc (suc (suc (suc (suc (suc N8)))))) γ') ≡ fst (numeralL 8))
  (tagEq9 : fst (lookup (suc (suc (suc (suc (suc (suc N9)))))) γ') ≡ fst (numeralL 9))
  (tagEq10 : fst (lookup (suc (suc (suc (suc (suc (suc N10)))))) γ') ≡ fst (numeralL 10))
  (tagEq11 : fst (lookup (suc (suc (suc (suc (suc (suc N11)))))) γ') ≡ fst (numeralL 11))
  (numK0 : ⟨ fst (numeralL 0) ∈ fst (lookup (suc (suc (suc (suc (suc (suc K)))))) γ') ⟩)
  (numK1 : ⟨ fst (numeralL 1) ∈ fst (lookup (suc (suc (suc (suc (suc (suc K)))))) γ') ⟩)
  (numK2 : ⟨ fst (numeralL 2) ∈ fst (lookup (suc (suc (suc (suc (suc (suc K)))))) γ') ⟩)
  (numK3 : ⟨ fst (numeralL 3) ∈ fst (lookup (suc (suc (suc (suc (suc (suc K)))))) γ') ⟩)
  (numK4 : ⟨ fst (numeralL 4) ∈ fst (lookup (suc (suc (suc (suc (suc (suc K)))))) γ') ⟩)
  (numK5 : ⟨ fst (numeralL 5) ∈ fst (lookup (suc (suc (suc (suc (suc (suc K)))))) γ') ⟩)
  (numK6 : ⟨ fst (numeralL 6) ∈ fst (lookup (suc (suc (suc (suc (suc (suc K)))))) γ') ⟩)
  (numK7 : ⟨ fst (numeralL 7) ∈ fst (lookup (suc (suc (suc (suc (suc (suc K)))))) γ') ⟩)
  (numK8 : ⟨ fst (numeralL 8) ∈ fst (lookup (suc (suc (suc (suc (suc (suc K)))))) γ') ⟩)
  (numK9 : ⟨ fst (numeralL 9) ∈ fst (lookup (suc (suc (suc (suc (suc (suc K)))))) γ') ⟩)
  (numK10 : ⟨ fst (numeralL 10) ∈ fst (lookup (suc (suc (suc (suc (suc (suc K)))))) γ') ⟩)
  (numK11 : ⟨ fst (numeralL 11) ∈ fst (lookup (suc (suc (suc (suc (suc (suc K)))))) γ') ⟩)
  (innerK : (k : ℕ) (p : S) → ⟨ fst p ∈ fst (lookup (suc (suc (suc (suc (suc (suc K)))))) γ') ⟩
             → ⟨ fst (prʟ (numeralL k) p) ∈ fst (lookup (suc (suc (suc (suc (suc (suc K)))))) γ') ⟩)
  (pairK : (a b : S) → ⟨ fst a ∈ fst (lookup (suc (suc (suc (suc (suc (suc K)))))) γ') ⟩
             → ⟨ fst b ∈ fst (lookup (suc (suc (suc (suc (suc (suc K)))))) γ') ⟩
             → ⟨ fst (prʟ a b) ∈ fst (lookup (suc (suc (suc (suc (suc (suc K)))))) γ') ⟩)
  (codesK : (k : ℕ) (c ar a b : S) → ⟨ fst c ∈ fst (lookup (suc (suc zero)) γ') ⟩
            → fst c ≡ pr (fst ar) (pr (# k) (pr (fst a) (fst b)))
            → ⟨ fst ar ∈ fst (lookup (suc (suc (suc (suc (suc (suc K)))))) γ') ⟩
              × ⟨ fst a ∈ fst (lookup (suc (suc (suc (suc (suc (suc K)))))) γ') ⟩
              × ⟨ fst b ∈ fst (lookup (suc (suc (suc (suc (suc (suc K)))))) γ') ⟩)
  (codesK-un : (k : ℕ) (c ar a : S) → ⟨ fst c ∈ fst (lookup (suc (suc zero)) γ') ⟩
               → fst c ≡ pr (fst ar) (pr (# k) (fst a))
               → ⟨ fst ar ∈ fst (lookup (suc (suc (suc (suc (suc (suc K)))))) γ') ⟩
                 × ⟨ fst a ∈ fst (lookup (suc (suc (suc (suc (suc (suc K)))))) γ') ⟩)
  (valK : (k : ℕ) (c ar a b yc : S) → ⟨ fst c ∈ fst (lookup (suc (suc zero)) γ') ⟩
          → fst c ≡ pr (fst ar) (pr (# k) (pr (fst a) (fst b)))
          → ⟨ fst yc ∈ fst (lookup (suc (suc (suc (suc (suc (suc K)))))) γ') ⟩)
  (valK-un : (k : ℕ) (c ar a yc : S) → ⟨ fst c ∈ fst (lookup (suc (suc zero)) γ') ⟩
             → fst c ≡ pr (fst ar) (pr (# k) (fst a))
             → ⟨ fst yc ∈ fst (lookup (suc (suc (suc (suc (suc (suc K)))))) γ') ⟩)
  (t0eq : fst (lookup (suc (suc (suc (suc (suc (suc t0)))))) γ') ≡ fst (numeralL 0))
  (t1eq : fst (lookup (suc (suc (suc (suc (suc (suc t1)))))) γ') ≡ fst (numeralL 1))
  (t0K : ⟨ fst (lookup (suc (suc (suc (suc (suc (suc t0)))))) γ')
           ∈ fst (lookup (suc (suc (suc (suc (suc (suc K)))))) γ') ⟩)
  (num1K : ⟨ fst (numeralL 1) ∈ fst (lookup (suc (suc (suc (suc (suc (suc K)))))) γ') ⟩)
  (envK-mem : (yc b a ar c E : S) → ⟨ (E ∷ yc ∷ b ∷ a ∷ ar ∷ c ∷ γ') ⊨
                envSetAt zero (suc (suc (suc (suc zero))))
                          (suc (suc (suc (suc (suc (suc zero)))))) ⟩
             → ⟨ fst E ∈ fst (lookup (suc (suc (suc (suc (suc (suc K)))))) γ') ⟩)
  (envK-neg : (ya yc a ar c E : S) → ⟨ (E ∷ ya ∷ yc ∷ a ∷ ar ∷ c ∷ γ') ⊨
                envSetAt zero (suc (suc (suc (suc zero))))
                          (suc (suc (suc (suc (suc (suc zero)))))) ⟩
             → ⟨ fst E ∈ fst (lookup (suc (suc (suc (suc (suc (suc K)))))) γ') ⟩)
  (envK-top : (yc a ar c E : S) → ⟨ (E ∷ yc ∷ a ∷ ar ∷ c ∷ γ') ⊨
                envSetAt zero (suc (suc (suc zero)))
                          (suc (suc (suc (suc (suc zero))))) ⟩
             → ⟨ fst E ∈ fst (lookup (suc (suc (suc (suc (suc (suc K)))))) γ') ⟩)
  (envK-imp : (E yb ya yc b a ar c : S) → ⟨ (E ∷ yb ∷ ya ∷ yc ∷ b ∷ a ∷ ar ∷ c ∷ γ') ⊨
                envSetAt zero (suc (suc (suc (suc (suc (suc zero))))))
                          (suc (suc (suc (suc (suc (suc (suc (suc zero)))))))) ⟩
             → ⟨ fst E ∈ fst (lookup (suc (suc (suc (suc (suc (suc K)))))) γ') ⟩)
  (envK-allin : (E ya yc b a ar c : S) → ⟨ (E ∷ ya ∷ yc ∷ b ∷ a ∷ ar ∷ c ∷ γ') ⊨
                  envSetAt zero (suc (suc (suc (suc (suc zero)))))
                            (suc (suc (suc (suc (suc (suc (suc zero))))))) ⟩
               → ⟨ fst E ∈ fst (lookup (suc (suc (suc (suc (suc (suc K)))))) γ') ⟩)
  (envInK-mem : (yc b a ar c E z : S) → ⟨ (z ∷ E ∷ yc ∷ b ∷ a ∷ ar ∷ c ∷ γ') ⊨
                  envOverAt zero (suc (suc (suc (suc (suc zero)))))
                              (suc (suc (suc (suc (suc (suc (suc zero))))))) ⟩
               → ⟨ fst z ∈ fst (lookup (suc (suc (suc (suc (suc (suc K)))))) γ') ⟩)
  (envInK-neg : (ya yc a ar c E z : S) → ⟨ (z ∷ E ∷ ya ∷ yc ∷ a ∷ ar ∷ c ∷ γ') ⊨
                  envOverAt zero (suc (suc (suc (suc (suc zero)))))
                              (suc (suc (suc (suc (suc (suc (suc zero))))))) ⟩
               → ⟨ fst z ∈ fst (lookup (suc (suc (suc (suc (suc (suc K)))))) γ') ⟩)
  (envInK-top : (yc a ar c E z : S) → ⟨ (z ∷ E ∷ yc ∷ a ∷ ar ∷ c ∷ γ') ⊨
                  envOverAt zero (suc (suc (suc (suc zero))))
                              (suc (suc (suc (suc (suc (suc zero)))))) ⟩
               → ⟨ fst z ∈ fst (lookup (suc (suc (suc (suc (suc (suc K)))))) γ') ⟩)
  (envInK-imp : (E ya yc b a ar c z : S) → ⟨ (z ∷ E ∷ ya ∷ yc ∷ b ∷ a ∷ ar ∷ c ∷ γ') ⊨
                  envOverAt zero (suc (suc (suc (suc (suc (suc zero))))))
                              (suc (suc (suc (suc (suc (suc (suc (suc zero)))))))) ⟩
               → ⟨ fst z ∈ fst (lookup (suc (suc (suc (suc (suc (suc K)))))) γ') ⟩)
  (valV : (E yc b a ar c z v w : S) → ⟨ (w ∷ v ∷ z ∷ E ∷ yc ∷ b ∷ a ∷ ar ∷ c ∷ γ') ⊨
             tmValAt (suc (suc (suc (suc (suc (suc zero))))))
                     (suc (suc zero))
                     (suc zero) ⟩
           → ⟨ fst v ∈ fst (lookup (suc (suc (suc (suc (suc (suc (suc (suc (suc (suc (suc (suc (suc K)))))))))))))
                             (z ∷ E ∷ yc ∷ b ∷ a ∷ ar ∷ c ∷ γ')) ⟩)
  (valW : (E yc b a ar c z v w : S) → ⟨ (w ∷ v ∷ z ∷ E ∷ yc ∷ b ∷ a ∷ ar ∷ c ∷ γ') ⊨
             tmValAt (suc (suc (suc (suc (suc zero)))))
                     (suc (suc zero))
                     zero ⟩
           → ⟨ fst w ∈ fst (lookup (suc (suc (suc (suc (suc (suc (suc (suc (suc (suc (suc (suc (suc (suc K))))))))))))))
                             (v ∷ z ∷ E ∷ yc ∷ b ∷ a ∷ ar ∷ c ∷ γ')) ⟩)
  (wKfact : (E ya yc b a ar c z w : S) → ⟨ (w ∷ z ∷ E ∷ ya ∷ yc ∷ b ∷ a ∷ ar ∷ c ∷ γ') ⊨
              tmValAt (suc (suc (suc (suc (suc (suc zero))))))
                      (suc zero)
                      zero ⟩
            → ⟨ fst w ∈ fst (lookup (suc (suc (suc (suc (suc (suc (suc (suc (suc (suc (suc (suc (suc (suc K))))))))))))))
                              (z ∷ E ∷ ya ∷ yc ∷ b ∷ a ∷ ar ∷ c ∷ γ')) ⟩)
  (transK : (x a : S) → ⟨ fst x ∈ fst a ⟩
            → ⟨ fst a ∈ fst (lookup (suc (suc (suc (suc (suc (suc K)))))) γ') ⟩
            → ⟨ fst x ∈ fst (lookup (suc (suc (suc (suc (suc (suc K)))))) γ') ⟩)
  (subK₁-and : (x y yc b a ar c : S) → ⟨ (x ∷ y ∷ yc ∷ b ∷ a ∷ ar ∷ c ∷ γ') ⊨
                 subValAt {7 + (11 + n)} (suc (suc (suc (suc (suc (suc (suc (suc zero))))))))
                          (suc (suc (suc (suc (suc zero)))))
                          (suc (suc (suc (suc zero))))
                          (suc zero) ⟩
               → ⟨ fst y ∈ fst (lookup (suc (suc (suc (suc (suc (suc K)))))) γ') ⟩)
  (subK₀-and : (y ya yc b a ar c : S) → ⟨ (y ∷ ya ∷ yc ∷ b ∷ a ∷ ar ∷ c ∷ γ') ⊨
                 subValAt {7 + (11 + n)} (suc (suc (suc (suc (suc (suc (suc (suc zero))))))))
                          (suc (suc (suc (suc (suc zero)))))
                          (suc (suc (suc zero)))
                          zero ⟩
               → ⟨ fst y ∈ fst (lookup (suc (suc (suc (suc (suc (suc K)))))) γ') ⟩)
  (subK₁-imp : (E yb ya yc b a ar c : S) → ⟨ (E ∷ yb ∷ ya ∷ yc ∷ b ∷ a ∷ ar ∷ c ∷ γ') ⊨
                 subValAt (suc (suc (suc (suc (suc (suc (suc (suc (suc zero)))))))))
                          (suc (suc (suc (suc (suc (suc zero))))))
                          (suc (suc (suc (suc (suc zero)))))
                          (suc (suc zero)) ⟩
               → ⟨ fst ya ∈ fst (lookup (suc (suc (suc (suc (suc (suc K)))))) γ') ⟩)
  (subK₀-imp : (E yb ya yc b a ar c : S) → ⟨ (E ∷ yb ∷ ya ∷ yc ∷ b ∷ a ∷ ar ∷ c ∷ γ') ⊨
                 subValAt (suc (suc (suc (suc (suc (suc (suc (suc (suc zero)))))))))
                          (suc (suc (suc (suc (suc (suc zero))))))
                          (suc (suc (suc (suc zero))))
                          (suc zero) ⟩
               → ⟨ fst yb ∈ fst (lookup (suc (suc (suc (suc (suc (suc K)))))) γ') ⟩)
  (someEnv : someEnvDef {n} K γ')
  (subK-neg : (ya yc a ar c E : S) → ⟨ (E ∷ ya ∷ yc ∷ a ∷ ar ∷ c ∷ γ') ⊨
                subValAt (suc (suc (suc (suc (suc (suc (suc zero)))))))
                         (suc (suc (suc (suc zero))))
                         (suc (suc (suc zero)))
                         (suc zero) ⟩
              → ⟨ fst ya ∈ fst (lookup (suc (suc (suc (suc (suc (suc K)))))) γ') ⟩)
  (sucK : (a : S) → ⟨ fst a ∈ fst (lookup (suc (suc (suc (suc (suc (suc K)))))) γ') ⟩
          → ⟨ sucV (fst a) ∈ fst (lookup (suc (suc (suc (suc (suc (suc K)))))) γ') ⟩)
  (envSetK : (B ar : S)
           → ⟨ fst B ∈ fst (lookup (suc (suc (suc (suc (suc (suc K)))))) γ') ⟩
           → ⟨ fst ar ∈ fst (lookup (suc (suc (suc (suc (suc (suc K)))))) γ') ⟩
           → ⟨ fst (Generic.envSetGen B ar)
                ∈ fst (lookup (suc (suc (suc (suc (suc (suc K)))))) γ') ⟩)
  (subK-un : (ya yc a ar c E : S) → ⟨ (E ∷ ya ∷ yc ∷ a ∷ ar ∷ c ∷ γ') ⊨
               subValSuccAt (suc (suc (suc (suc (suc (suc (suc zero)))))))
                            (suc (suc (suc (suc zero))))
                            (suc (suc (suc zero)))
                            (suc zero) ⟩
             → ⟨ fst ya ∈ fst (lookup (suc (suc (suc (suc (suc (suc K)))))) γ') ⟩)
  (consK-exist : (ya yc a ar c E z x e' : S) → ⟨ (e' ∷ x ∷ z ∷ E ∷ ya ∷ yc ∷ a ∷ ar ∷ c ∷ γ') ⊨
                   consAtL zero (suc zero) (suc (suc zero))
                   ∧̇ (var zero ∈̇ var (suc (suc (suc (suc zero))))) ⟩
                 → ⟨ fst e' ∈ fst (lookup (suc (suc (suc (suc (suc (suc (suc (suc (suc (suc (suc (suc (suc (suc K))))))))))))))
                                   (x ∷ z ∷ E ∷ ya ∷ yc ∷ a ∷ ar ∷ c ∷ γ')) ⟩)
  (consK-forall : (ya yc a ar c E z x e' : S) → ⟨ (e' ∷ x ∷ z ∷ E ∷ ya ∷ yc ∷ a ∷ ar ∷ c ∷ γ') ⊨
                    consAtL zero (suc zero) (suc (suc zero)) ⟩
                  → ⟨ fst e' ∈ fst (lookup (suc (suc (suc (suc (suc (suc (suc (suc (suc (suc (suc (suc (suc (suc K))))))))))))))
                                    (x ∷ z ∷ E ∷ ya ∷ yc ∷ a ∷ ar ∷ c ∷ γ')) ⟩)
  (subK-allin : (E ya yc b a ar c : S) → ⟨ (E ∷ ya ∷ yc ∷ b ∷ a ∷ ar ∷ c ∷ γ') ⊨
                  subValSuccAt (suc (suc (suc (suc (suc (suc (suc (suc zero))))))))
                               (suc (suc (suc (suc (suc zero)))))
                               (suc (suc (suc zero)))
                               (suc zero) ⟩
                → ⟨ fst ya ∈ fst (lookup (suc (suc (suc (suc (suc (suc K)))))) γ') ⟩)
  (consK-allin : (E ya yc b a ar c z w x e' : S) → ⟨ (e' ∷ x ∷ w ∷ z ∷ E ∷ ya ∷ yc ∷ b ∷ a ∷ ar ∷ c ∷ γ') ⊨
                   consAtL zero (suc zero) (suc (suc (suc zero))) ⟩
                 → ⟨ fst e' ∈ fst (lookup (suc (suc (suc (suc (suc (suc (suc (suc (suc (suc (suc (suc (suc (suc (suc (suc K))))))))))))))))
                                   (x ∷ w ∷ z ∷ E ∷ ya ∷ yc ∷ b ∷ a ∷ ar ∷ c ∷ γ')) ⟩)
  where

  -- The rows' arityK is the frame's transK with the binder roles
  -- swapped: transK x a closes x ∈ a, the row's arityK N v closes
  -- v ∈ N.  One derivation, reused at every application ([LJ-1.93]).
  arityK : (N v : S) → ⟨ fst v ∈ fst N ⟩
         → ⟨ fst N ∈ fst (lookup (suc (suc (suc (suc (suc (suc K)))))) γ') ⟩
         → ⟨ fst v ∈ fst (lookup (suc (suc (suc (suc (suc (suc K)))))) γ') ⟩
  arityK N v hv hNK = transK v N hv hNK

  -- The five tied key facts, derived once from sucK and pairK
  -- ([LJ-1.109] TiesSupplied).  The site memberships (arK, aK, bK)
  -- are the rows' binders; the facts are derivations, not hypotheses
  -- (C-38).
  module KN = KeyNegTies {11 + n} (suc (suc (suc (suc (suc (suc K)))))) γ' pairK
  module KT = SuccKeyTies {11 + n} (suc (suc (suc (suc (suc (suc K)))))) γ' sucK pairK

  keyK-neg-tied : (E ya yc a ar c : S)
                → ⟨ fst ar ∈ fst (lookup (suc (suc (suc (suc (suc (suc K)))))) γ') ⟩
                → ⟨ fst a ∈ fst (lookup (suc (suc (suc (suc (suc (suc K)))))) γ') ⟩
                → ⟨ pr (fst ar) (fst a)
                     ∈ fst (lookup (suc (suc (suc (suc (suc (suc K)))))) γ') ⟩
  keyK-neg-tied E ya yc a ar c arK aK = KN.key-neg-tied ar a arK aK

  succK-tied : (N : Fin (11 + n)) (E ya yc a ar c : S)
             → ⟨ fst ar ∈ fst (lookup (suc (suc (suc (suc (suc (suc K)))))) γ') ⟩
             → succU {11 + n} (suc (suc zero)) (suc zero) zero N
                      (suc (suc (suc (suc (suc (suc K)))))) γ' E ya yc a ar c
  succK-tied N E ya yc a ar c arK = KT.succ-tied ar arK

  keyK-un-tied : (N : Fin (11 + n)) (E ya yc a ar c : S)
               → ⟨ fst ar ∈ fst (lookup (suc (suc (suc (suc (suc (suc K)))))) γ') ⟩
               → ⟨ fst a ∈ fst (lookup (suc (suc (suc (suc (suc (suc K)))))) γ') ⟩
               → keyU {11 + n} (suc (suc zero)) (suc zero) zero N
                        (suc (suc (suc (suc (suc (suc K)))))) γ' E ya yc a ar c
  keyK-un-tied N E ya yc a ar c arK aK = KT.key-un-tied ar a arK aK

  succK-allin-tied : (E ya yc b a ar c : S)
                   → ⟨ fst ar ∈ fst (lookup (suc (suc (suc (suc (suc (suc K)))))) γ') ⟩
                   → ⟨ sucV (fst ar)
                        ∈ fst (lookup (suc (suc (suc (suc (suc (suc K)))))) γ') ⟩
  succK-allin-tied E ya yc b a ar c arK = KT.succ-tied ar arK

  keyK-allin-tied : (E ya yc b a ar c : S)
                  → ⟨ fst ar ∈ fst (lookup (suc (suc (suc (suc (suc (suc K)))))) γ') ⟩
                  → ⟨ fst b ∈ fst (lookup (suc (suc (suc (suc (suc (suc K)))))) γ') ⟩
                  → ⟨ pr (sucV (fst ar)) (fst b)
                       ∈ fst (lookup (suc (suc (suc (suc (suc (suc K)))))) γ') ⟩
  keyK-allin-tied E ya yc b a ar c arK bK = KT.key-un-tied ar b arK bK

  p0b : Formula S (11 + n)
  p0b = LowerAgree.sixB {n} N0 N1 N2 N3 N4 N5 N6 N7 N8 N9 N10 N11 t0 t1 K γ'
        tagEq0 tagEq1 tagEq2 tagEq3 tagEq4 tagEq5
        numK0 numK1 numK2 numK3 numK4 numK5
        innerK pairK codesK codesK-un valK valK-un
        t0eq t1eq t0K num1K
        envK-mem envK-neg envK-imp
        envInK-mem envInK-neg envInK-imp valV valW
        transK subK₁-and subK₀-and subK₁-imp subK₀-imp
        someEnv subK-neg

  p1b : Formula S (11 + n)
  p1b = UpperAgree.sixB {n} N0 N1 N2 N3 N4 N5 N6 N7 N8 N9 N10 N11 t0 t1 K γ'
        tagEq6 tagEq7 tagEq8 tagEq9 tagEq10 tagEq11
        numK6 numK7 numK8 numK9 numK10 numK11
        innerK pairK arityK codesK codesK-un valK valK-un
        t0eq t1eq t0K num1K
        envK-neg envK-top envK-allin
        envInK-neg envInK-top envInK-imp wKfact
        sucK subK-un consK-exist consK-forall
        subK-allin consK-allin

  twelveB : Formula S (11 + n)
  twelveB = p0b ∧̇ p1b

  out : ⟨ γ' ⊨ twelveAt (suc (suc zero)) (suc zero) zero ⟩ → ⟨ γ' ⊨ twelveB ⟩
  out h =
    ( LowerAgree.out {n} N0 N1 N2 N3 N4 N5 N6 N7 N8 N9 N10 N11 t0 t1 K γ'
        tagEq0 tagEq1 tagEq2 tagEq3 tagEq4 tagEq5
        numK0 numK1 numK2 numK3 numK4 numK5
        innerK pairK codesK codesK-un valK valK-un
        t0eq t1eq t0K num1K
        envK-mem envK-neg envK-imp
        envInK-mem envInK-neg envInK-imp valV valW
        transK subK₁-and subK₀-and subK₁-imp subK₀-imp
        someEnv subK-neg h
    , UpperAgree.out {n} N0 N1 N2 N3 N4 N5 N6 N7 N8 N9 N10 N11 t0 t1 K γ'
        tagEq6 tagEq7 tagEq8 tagEq9 tagEq10 tagEq11
        numK6 numK7 numK8 numK9 numK10 numK11
        innerK pairK arityK codesK codesK-un valK valK-un
        t0eq t1eq t0K num1K
        envK-neg envK-top envK-allin
        envInK-neg envInK-top envInK-imp wKfact
        sucK subK-un consK-exist consK-forall
        subK-allin consK-allin h )

  back : ⟨ γ' ⊨ twelveB ⟩ → ⟨ γ' ⊨ twelveAt (suc (suc zero)) (suc zero) zero ⟩
  back h =
    let a = LowerAgree.back {n} N0 N1 N2 N3 N4 N5 N6 N7 N8 N9 N10 N11 t0 t1 K γ'
              tagEq0 tagEq1 tagEq2 tagEq3 tagEq4 tagEq5
              numK0 numK1 numK2 numK3 numK4 numK5
              innerK pairK codesK codesK-un valK valK-un
              t0eq t1eq t0K num1K
              envK-mem envK-neg envK-imp
              envInK-mem envInK-neg envInK-imp valV valW
              transK subK₁-and subK₀-and subK₁-imp subK₀-imp
              someEnv subK-neg (h .fst)
        b = UpperAgree.back {n} N0 N1 N2 N3 N4 N5 N6 N7 N8 N9 N10 N11 t0 t1 K γ'
              tagEq6 tagEq7 tagEq8 tagEq9 tagEq10 tagEq11
              numK6 numK7 numK8 numK9 numK10 numK11
              innerK pairK arityK codesK codesK-un valK valK-un
              t0eq t1eq t0K num1K
              envK-neg envK-top envK-allin
              envInK-neg envInK-top envInK-imp wKfact
              sucK subK-un consK-exist consK-forall
              subK-allin consK-allin (h .snd)
    in ( a .fst , ( a .snd .fst , ( a .snd .snd .fst , ( a .snd .snd .snd .fst
       , ( a .snd .snd .snd .snd .fst , ( a .snd .snd .snd .snd .snd
       , ( b .fst , ( b .snd .fst , ( b .snd .snd .fst , ( b .snd .snd .snd .fst
       , ( b .snd .snd .snd .snd .fst , b .snd .snd .snd .snd .snd )))))))))))
```
