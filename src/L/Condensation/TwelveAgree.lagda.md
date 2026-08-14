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
open import L.Condensation {ℓ} lem using ( succU; keyU; module SatGraphB )
open import L.Condensation.LowerAgree {ℓ} lem using
  ( module LowerAgree; module KeyNegTies; someEnvDef; LFacts )
open import L.Condensation.UpperAgree {ℓ} lem using
  ( module UpperAgree; module SuccKeyTies; UFacts )
open import Cubical.Data.Nat using ( _+_ )
open import Cubical.HITs.PropositionalTruncation using ( ∥_∥₁ )
open import Cubical.HITs.CumulativeHierarchy.Base using ( _∈_ )
open import Cubical.HITs.CumulativeHierarchy.Constructions using ( module InfinitySet )
open InfinitySet using ( #_; sucV )

open TruthAlgebra (hPropAlgebra (ℓ-suc ℓ))
open hPropStructure 𝒮ʟ

module AbsL = FOL.Absoluteness.Single 𝒮ᵥ isL isL-trans
open AbsL renaming ( _⊨ᵐ_ to _⊨_ )

-- =====================================================================
-- THE GENERIC SIX-AND-SIX RE-ASSOCIATION.
--
-- The composer's `twelveB` (:307) is `p0b ∧̇ p1b`, and each half is a
-- six-fold conjunction.  The consumer's `SatGraphB.twelveB`
-- (src/L/Condensation.lagda.md:2236-2257) is ONE right-nested chain of
-- twelve.  `∧̇` is a `Formula` constructor, so the two terms are
-- different and no `refl` connects them.  dev/PLAN.md:548 records that
-- and it is true.
--
-- It is also not a blocker.  The consumer states its two hypotheses at
-- SATISFACTION, not at equality.  `γ ⊨ (φ ∧̇ ψ)` is definitionally
-- `(γ ⊨ φ) ⊓ (γ ⊨ ψ)`, and `⟨ P ⊓ Q ⟩` is definitionally `⟨ P ⟩ × ⟨ Q ⟩`
-- in the hProp algebra.  So the two satisfactions differ by product
-- ASSOCIATION only, and the bridge is twelve projections and eleven
-- pairings.
--
-- The two functions name no formula, no environment and no carrier:
-- they are product re-association and nothing else, so every future
-- twelve-row consumer on either tower shares this one copy (DD4).
--
-- THEY SIT AT THE TOP LEVEL ON PURPOSE, and P-w is the reason.  A
-- module application COPIES its body.  Written inside `AbstractFrame`
-- these 28 lines would be copied at every instantiation of the frame.
-- Here the frame copies two applications instead ([LJ-1.144] section
-- 5.3, which measured the shape before it measured the price).
-- =====================================================================

module _ {ℓ' : Level}
  {A0 A1 A2 A3 A4 A5 A6 A7 A8 A9 A10 A11 : Type ℓ'} where

  sixes→twelve : (A0 × A1 × A2 × A3 × A4 × A5)
                 × (A6 × A7 × A8 × A9 × A10 × A11)
               → A0 × A1 × A2 × A3 × A4 × A5
                 × A6 × A7 × A8 × A9 × A10 × A11
  sixes→twelve h =
    ( h .fst .fst
    , ( h .fst .snd .fst
      , ( h .fst .snd .snd .fst
        , ( h .fst .snd .snd .snd .fst
          , ( h .fst .snd .snd .snd .snd .fst
            , ( h .fst .snd .snd .snd .snd .snd
              , ( h .snd .fst
                , ( h .snd .snd .fst
                  , ( h .snd .snd .snd .fst
                    , ( h .snd .snd .snd .snd .fst
                      , ( h .snd .snd .snd .snd .snd .fst
                        , h .snd .snd .snd .snd .snd .snd )))))))))))

  twelve→sixes : A0 × A1 × A2 × A3 × A4 × A5
                 × A6 × A7 × A8 × A9 × A10 × A11
               → (A0 × A1 × A2 × A3 × A4 × A5)
                 × (A6 × A7 × A8 × A9 × A10 × A11)
  twelve→sixes h =
    ( ( h .fst
      , ( h .snd .fst
        , ( h .snd .snd .fst
          , ( h .snd .snd .snd .fst
            , ( h .snd .snd .snd .snd .fst
              , h .snd .snd .snd .snd .snd .fst )))))
    , ( h .snd .snd .snd .snd .snd .snd .fst
      , ( h .snd .snd .snd .snd .snd .snd .snd .fst
        , ( h .snd .snd .snd .snd .snd .snd .snd .snd .fst
          , ( h .snd .snd .snd .snd .snd .snd .snd .snd .snd .fst
            , ( h .snd .snd .snd .snd .snd .snd .snd .snd .snd .snd .fst
              , h .snd .snd .snd .snd .snd .snd .snd .snd .snd .snd .snd ))))))

-- THE FRAME'S FACT BLOCK, as ONE record rather than 60 telescope
-- hypotheses.  `[LJ-1.62]` states the reason at `src/L/Condensation.lagda.md`
-- :5990-5994, and these masters never got it: a module telescope is prepended
-- to the STORED TYPE of every definition inside the module, and Agda's
-- `DeadCode.DeadCodeReachable` pass then walks those stored types once per
-- definition.
--
-- MEASURED by `[LJ-1.158]`, a controlled pair of probes over THIS telescope,
-- two runs each side: `DeadCode` 13,018 ms to 95 ms and the probe file
-- 20,958 ms to 6,421, minus 69 percent (probes T1 and T2).
--
-- `sucK` STAYS A TELESCOPE HYPOTHESIS and is never a field.  `[LJ-1.155]`
-- measured `sucV` in a record field type at an 8 GB heap wall, and the same
-- field at 2.02 s with that one token removed (P-x).
record TFacts {n : ℕ}
  (N0 N1 N2 N3 N4 N5 N6 N7 N8 N9 N10 N11 t0 t1 K : Fin (5 + n))
  (γ' : S ^ (11 + n)) : Type (ℓ-suc ℓ) where
  field
    tagEq0 : fst (lookup (suc (suc (suc (suc (suc (suc N0)))))) γ') ≡ fst (numeralL 0)
    tagEq1 : fst (lookup (suc (suc (suc (suc (suc (suc N1)))))) γ') ≡ fst (numeralL 1)
    tagEq2 : fst (lookup (suc (suc (suc (suc (suc (suc N2)))))) γ') ≡ fst (numeralL 2)
    tagEq3 : fst (lookup (suc (suc (suc (suc (suc (suc N3)))))) γ') ≡ fst (numeralL 3)
    tagEq4 : fst (lookup (suc (suc (suc (suc (suc (suc N4)))))) γ') ≡ fst (numeralL 4)
    tagEq5 : fst (lookup (suc (suc (suc (suc (suc (suc N5)))))) γ') ≡ fst (numeralL 5)
    tagEq6 : fst (lookup (suc (suc (suc (suc (suc (suc N6)))))) γ') ≡ fst (numeralL 6)
    tagEq7 : fst (lookup (suc (suc (suc (suc (suc (suc N7)))))) γ') ≡ fst (numeralL 7)
    tagEq8 : fst (lookup (suc (suc (suc (suc (suc (suc N8)))))) γ') ≡ fst (numeralL 8)
    tagEq9 : fst (lookup (suc (suc (suc (suc (suc (suc N9)))))) γ') ≡ fst (numeralL 9)
    tagEq10 : fst (lookup (suc (suc (suc (suc (suc (suc N10)))))) γ') ≡ fst (numeralL 10)
    tagEq11 : fst (lookup (suc (suc (suc (suc (suc (suc N11)))))) γ') ≡ fst (numeralL 11)
    numK0 : ⟨ fst (numeralL 0) ∈ fst (lookup (suc (suc (suc (suc (suc (suc K)))))) γ') ⟩
    numK1 : ⟨ fst (numeralL 1) ∈ fst (lookup (suc (suc (suc (suc (suc (suc K)))))) γ') ⟩
    numK2 : ⟨ fst (numeralL 2) ∈ fst (lookup (suc (suc (suc (suc (suc (suc K)))))) γ') ⟩
    numK3 : ⟨ fst (numeralL 3) ∈ fst (lookup (suc (suc (suc (suc (suc (suc K)))))) γ') ⟩
    numK4 : ⟨ fst (numeralL 4) ∈ fst (lookup (suc (suc (suc (suc (suc (suc K)))))) γ') ⟩
    numK5 : ⟨ fst (numeralL 5) ∈ fst (lookup (suc (suc (suc (suc (suc (suc K)))))) γ') ⟩
    numK6 : ⟨ fst (numeralL 6) ∈ fst (lookup (suc (suc (suc (suc (suc (suc K)))))) γ') ⟩
    numK7 : ⟨ fst (numeralL 7) ∈ fst (lookup (suc (suc (suc (suc (suc (suc K)))))) γ') ⟩
    numK8 : ⟨ fst (numeralL 8) ∈ fst (lookup (suc (suc (suc (suc (suc (suc K)))))) γ') ⟩
    numK9 : ⟨ fst (numeralL 9) ∈ fst (lookup (suc (suc (suc (suc (suc (suc K)))))) γ') ⟩
    numK10 : ⟨ fst (numeralL 10) ∈ fst (lookup (suc (suc (suc (suc (suc (suc K)))))) γ') ⟩
    numK11 : ⟨ fst (numeralL 11) ∈ fst (lookup (suc (suc (suc (suc (suc (suc K)))))) γ') ⟩
    innerK : (k : ℕ) (p : S) → ⟨ fst p ∈ fst (lookup (suc (suc (suc (suc (suc (suc K)))))) γ') ⟩
              → ⟨ fst (prʟ (numeralL k) p) ∈ fst (lookup (suc (suc (suc (suc (suc (suc K)))))) γ') ⟩
    pairK : (a b : S) → ⟨ fst a ∈ fst (lookup (suc (suc (suc (suc (suc (suc K)))))) γ') ⟩
              → ⟨ fst b ∈ fst (lookup (suc (suc (suc (suc (suc (suc K)))))) γ') ⟩
              → ⟨ fst (prʟ a b) ∈ fst (lookup (suc (suc (suc (suc (suc (suc K)))))) γ') ⟩
    codesK : (k : ℕ) (c ar a b : S) → ⟨ fst c ∈ fst (lookup (suc (suc zero)) γ') ⟩
             → fst c ≡ pr (fst ar) (pr (# k) (pr (fst a) (fst b)))
             → ⟨ fst ar ∈ fst (lookup (suc (suc (suc (suc (suc (suc K)))))) γ') ⟩
               × ⟨ fst a ∈ fst (lookup (suc (suc (suc (suc (suc (suc K)))))) γ') ⟩
               × ⟨ fst b ∈ fst (lookup (suc (suc (suc (suc (suc (suc K)))))) γ') ⟩
                 × ∥ Σ[ n ∈ ℕ ] (fst ar ≡ # n) ∥₁
    codesK-un : (k : ℕ) (c ar a : S) → ⟨ fst c ∈ fst (lookup (suc (suc zero)) γ') ⟩
                → fst c ≡ pr (fst ar) (pr (# k) (fst a))
                → ⟨ fst ar ∈ fst (lookup (suc (suc (suc (suc (suc (suc K)))))) γ') ⟩
                  × ⟨ fst a ∈ fst (lookup (suc (suc (suc (suc (suc (suc K)))))) γ') ⟩
                 × ∥ Σ[ n ∈ ℕ ] (fst ar ≡ # n) ∥₁
    valK : (k : ℕ) (c ar a b yc : S) → ⟨ fst c ∈ fst (lookup (suc (suc zero)) γ') ⟩
           → fst c ≡ pr (fst ar) (pr (# k) (pr (fst a) (fst b)))
           → ⟨ pr (fst c) (fst yc) ∈ fst (lookup (suc zero) γ') ⟩
           → ⟨ fst yc ∈ fst (lookup (suc (suc (suc (suc (suc (suc K)))))) γ') ⟩
    valK-un : (k : ℕ) (c ar a yc : S) → ⟨ fst c ∈ fst (lookup (suc (suc zero)) γ') ⟩
              → fst c ≡ pr (fst ar) (pr (# k) (fst a))
              → ⟨ pr (fst c) (fst yc) ∈ fst (lookup (suc zero) γ') ⟩
              → ⟨ fst yc ∈ fst (lookup (suc (suc (suc (suc (suc (suc K)))))) γ') ⟩
    t0eq : fst (lookup (suc (suc (suc (suc (suc (suc t0)))))) γ') ≡ fst (numeralL 0)
    t1eq : fst (lookup (suc (suc (suc (suc (suc (suc t1)))))) γ') ≡ fst (numeralL 1)
    t0K : ⟨ fst (lookup (suc (suc (suc (suc (suc (suc t0)))))) γ')
            ∈ fst (lookup (suc (suc (suc (suc (suc (suc K)))))) γ') ⟩
    num1K : ⟨ fst (numeralL 1) ∈ fst (lookup (suc (suc (suc (suc (suc (suc K)))))) γ') ⟩
    envK-mem : (yc b a ar c E : S)
               → ∥ Σ[ n ∈ ℕ ] (fst ar ≡ # n) ∥₁
               → ⟨ (E ∷ yc ∷ b ∷ a ∷ ar ∷ c ∷ γ') ⊨
                 envSetAt zero (suc (suc (suc (suc zero))))
                           (suc (suc (suc (suc (suc (suc zero)))))) ⟩
              → ⟨ fst E ∈ fst (lookup (suc (suc (suc (suc (suc (suc K)))))) γ') ⟩
    envK-neg : (ya yc a ar c E : S)
               → ∥ Σ[ n ∈ ℕ ] (fst ar ≡ # n) ∥₁
               → ⟨ (E ∷ ya ∷ yc ∷ a ∷ ar ∷ c ∷ γ') ⊨
                 envSetAt zero (suc (suc (suc (suc zero))))
                           (suc (suc (suc (suc (suc (suc zero)))))) ⟩
              → ⟨ fst E ∈ fst (lookup (suc (suc (suc (suc (suc (suc K)))))) γ') ⟩
    envK-top : (yc a ar c E : S)
               → ∥ Σ[ n ∈ ℕ ] (fst ar ≡ # n) ∥₁
               → ⟨ (E ∷ yc ∷ a ∷ ar ∷ c ∷ γ') ⊨
                 envSetAt zero (suc (suc (suc zero)))
                           (suc (suc (suc (suc (suc zero))))) ⟩
              → ⟨ fst E ∈ fst (lookup (suc (suc (suc (suc (suc (suc K)))))) γ') ⟩
    envK-imp : (E yb ya yc b a ar c : S)
               → ∥ Σ[ n ∈ ℕ ] (fst ar ≡ # n) ∥₁
               → ⟨ (E ∷ yb ∷ ya ∷ yc ∷ b ∷ a ∷ ar ∷ c ∷ γ') ⊨
                 envSetAt zero (suc (suc (suc (suc (suc (suc zero))))))
                           (suc (suc (suc (suc (suc (suc (suc (suc zero)))))))) ⟩
              → ⟨ fst E ∈ fst (lookup (suc (suc (suc (suc (suc (suc K)))))) γ') ⟩
    envK-allin : (E ya yc b a ar c : S)
               → ∥ Σ[ n ∈ ℕ ] (fst ar ≡ # n) ∥₁
               → ⟨ (E ∷ ya ∷ yc ∷ b ∷ a ∷ ar ∷ c ∷ γ') ⊨
                   envSetAt zero (suc (suc (suc (suc (suc zero)))))
                             (suc (suc (suc (suc (suc (suc (suc zero))))))) ⟩
                → ⟨ fst E ∈ fst (lookup (suc (suc (suc (suc (suc (suc K)))))) γ') ⟩
    envInK-mem : (yc b a ar c E : S)
               → ⟨ fst ar ∈ fst (lookup (suc (suc (suc (suc (suc (suc K)))))) γ') ⟩
               → ∥ Σ[ n ∈ ℕ ] (fst ar ≡ # n) ∥₁
               → (z : S) → ⟨ (z ∷ E ∷ yc ∷ b ∷ a ∷ ar ∷ c ∷ γ') ⊨
                   envOverAt zero (suc (suc (suc (suc (suc zero)))))
                               (suc (suc (suc (suc (suc (suc (suc zero))))))) ⟩
                → ⟨ fst z ∈ fst (lookup (suc (suc (suc (suc (suc (suc K)))))) γ') ⟩
    envInK-neg : (ya yc a ar c E : S)
               → ⟨ fst ar ∈ fst (lookup (suc (suc (suc (suc (suc (suc K)))))) γ') ⟩
               → ∥ Σ[ n ∈ ℕ ] (fst ar ≡ # n) ∥₁
               → (z : S) → ⟨ (z ∷ E ∷ ya ∷ yc ∷ a ∷ ar ∷ c ∷ γ') ⊨
                   envOverAt zero (suc (suc (suc (suc (suc zero)))))
                               (suc (suc (suc (suc (suc (suc (suc zero))))))) ⟩
                → ⟨ fst z ∈ fst (lookup (suc (suc (suc (suc (suc (suc K)))))) γ') ⟩
    envInK-top : (yc a ar c E : S)
               → ⟨ fst ar ∈ fst (lookup (suc (suc (suc (suc (suc (suc K)))))) γ') ⟩
               → ∥ Σ[ n ∈ ℕ ] (fst ar ≡ # n) ∥₁
               → (z : S) → ⟨ (z ∷ E ∷ yc ∷ a ∷ ar ∷ c ∷ γ') ⊨
                   envOverAt zero (suc (suc (suc (suc zero))))
                               (suc (suc (suc (suc (suc (suc zero)))))) ⟩
                → ⟨ fst z ∈ fst (lookup (suc (suc (suc (suc (suc (suc K)))))) γ') ⟩
    envInK-imp : (E ya yc b a ar c : S)
               → ⟨ fst ar ∈ fst (lookup (suc (suc (suc (suc (suc (suc K)))))) γ') ⟩
               → ∥ Σ[ n ∈ ℕ ] (fst ar ≡ # n) ∥₁
               → (z : S) → ⟨ (z ∷ E ∷ ya ∷ yc ∷ b ∷ a ∷ ar ∷ c ∷ γ') ⊨
                   envOverAt zero (suc (suc (suc (suc (suc (suc zero))))))
                               (suc (suc (suc (suc (suc (suc (suc (suc zero)))))))) ⟩
                → ⟨ fst z ∈ fst (lookup (suc (suc (suc (suc (suc (suc K)))))) γ') ⟩
    valV : (E yc b a ar c z v w : S) → ⟨ (w ∷ v ∷ z ∷ E ∷ yc ∷ b ∷ a ∷ ar ∷ c ∷ γ') ⊨
              tmValAt (suc (suc (suc (suc (suc (suc zero))))))
                      (suc (suc zero))
                      (suc zero) ⟩
            → ⟨ fst v ∈ fst (lookup (suc (suc (suc (suc (suc (suc (suc (suc (suc (suc (suc (suc (suc K)))))))))))))
                              (z ∷ E ∷ yc ∷ b ∷ a ∷ ar ∷ c ∷ γ')) ⟩
    valW : (E yc b a ar c z v w : S) → ⟨ (w ∷ v ∷ z ∷ E ∷ yc ∷ b ∷ a ∷ ar ∷ c ∷ γ') ⊨
              tmValAt (suc (suc (suc (suc (suc zero)))))
                      (suc (suc zero))
                      zero ⟩
            → ⟨ fst w ∈ fst (lookup (suc (suc (suc (suc (suc (suc (suc (suc (suc (suc (suc (suc (suc (suc K))))))))))))))
                              (v ∷ z ∷ E ∷ yc ∷ b ∷ a ∷ ar ∷ c ∷ γ')) ⟩
    wKfact : (E ya yc b a ar c z w : S) → ⟨ (w ∷ z ∷ E ∷ ya ∷ yc ∷ b ∷ a ∷ ar ∷ c ∷ γ') ⊨
               tmValAt (suc (suc (suc (suc (suc (suc zero))))))
                       (suc zero)
                       zero ⟩
             → ⟨ fst w ∈ fst (lookup (suc (suc (suc (suc (suc (suc (suc (suc (suc (suc (suc (suc (suc (suc K))))))))))))))
                               (z ∷ E ∷ ya ∷ yc ∷ b ∷ a ∷ ar ∷ c ∷ γ')) ⟩
    transK : (x a : S) → ⟨ fst x ∈ fst a ⟩
             → ⟨ fst a ∈ fst (lookup (suc (suc (suc (suc (suc (suc K)))))) γ') ⟩
             → ⟨ fst x ∈ fst (lookup (suc (suc (suc (suc (suc (suc K)))))) γ') ⟩
    subK₁-and : (x y yc b a ar c : S) → ⟨ (x ∷ y ∷ yc ∷ b ∷ a ∷ ar ∷ c ∷ γ') ⊨
                  subValAt {7 + (11 + n)} (suc (suc (suc (suc (suc (suc (suc (suc zero))))))))
                           (suc (suc (suc (suc (suc zero)))))
                           (suc (suc (suc (suc zero))))
                           (suc zero) ⟩
                → ⟨ fst y ∈ fst (lookup (suc (suc (suc (suc (suc (suc K)))))) γ') ⟩
    subK₀-and : (y ya yc b a ar c : S) → ⟨ (y ∷ ya ∷ yc ∷ b ∷ a ∷ ar ∷ c ∷ γ') ⊨
                  subValAt {7 + (11 + n)} (suc (suc (suc (suc (suc (suc (suc (suc zero))))))))
                           (suc (suc (suc (suc (suc zero)))))
                           (suc (suc (suc zero)))
                           zero ⟩
                → ⟨ fst y ∈ fst (lookup (suc (suc (suc (suc (suc (suc K)))))) γ') ⟩
    subK₁-imp : (E yb ya yc b a ar c : S) → ⟨ (E ∷ yb ∷ ya ∷ yc ∷ b ∷ a ∷ ar ∷ c ∷ γ') ⊨
                  subValAt (suc (suc (suc (suc (suc (suc (suc (suc (suc zero)))))))))
                           (suc (suc (suc (suc (suc (suc zero))))))
                           (suc (suc (suc (suc (suc zero)))))
                           (suc (suc zero)) ⟩
                → ⟨ fst ya ∈ fst (lookup (suc (suc (suc (suc (suc (suc K)))))) γ') ⟩
    subK₀-imp : (E yb ya yc b a ar c : S) → ⟨ (E ∷ yb ∷ ya ∷ yc ∷ b ∷ a ∷ ar ∷ c ∷ γ') ⊨
                  subValAt (suc (suc (suc (suc (suc (suc (suc (suc (suc zero)))))))))
                           (suc (suc (suc (suc (suc (suc zero))))))
                           (suc (suc (suc (suc zero))))
                           (suc zero) ⟩
                → ⟨ fst yb ∈ fst (lookup (suc (suc (suc (suc (suc (suc K)))))) γ') ⟩
    someEnv : someEnvDef {n} K γ'
    subK-neg : (ya yc a ar c E : S) → ⟨ (E ∷ ya ∷ yc ∷ a ∷ ar ∷ c ∷ γ') ⊨
                 subValAt (suc (suc (suc (suc (suc (suc (suc zero)))))))
                          (suc (suc (suc (suc zero))))
                          (suc (suc (suc zero)))
                          (suc zero) ⟩
               → ⟨ fst ya ∈ fst (lookup (suc (suc (suc (suc (suc (suc K)))))) γ') ⟩
    -- RESTRICTED to a NUMERAL arity by [LJ-1.173].  At an unrestricted
    -- `ar` this field asks a LEVEL to hold the full constructible
    -- function space, and a successor-closed limit does not, so the
    -- general form is FALSE at the bound `HullStage` gives ([LJ-1.172]).
    -- The numeral case is TRUE and [LJ-1.173] closes it: the set lands
    -- at a FIXED iterate above the stage that holds `B`, uniform in `n`.
    -- The restriction costs the consumers nothing, because the arity at
    -- every consuming site IS a numeral: `codesK` gives the code's
    -- shape, `arityNumAtL` (L.Coding.CodeSet) says its arity component
    -- is a numeral, and `pr-inj` closes both into `fst ar ≡ # n`.
    envSetK : (B ar : S) (n : ℕ) → fst ar ≡ # n
            → ⟨ fst B ∈ fst (lookup (suc (suc (suc (suc (suc (suc K)))))) γ') ⟩
            → ⟨ fst ar ∈ fst (lookup (suc (suc (suc (suc (suc (suc K)))))) γ') ⟩
            → ⟨ fst (Generic.envSetGen B ar)
                 ∈ fst (lookup (suc (suc (suc (suc (suc (suc K)))))) γ') ⟩
    subK-un : (ya yc a ar c E : S) → ⟨ (E ∷ ya ∷ yc ∷ a ∷ ar ∷ c ∷ γ') ⊨
                subValSuccAt (suc (suc (suc (suc (suc (suc (suc zero)))))))
                             (suc (suc (suc (suc zero))))
                             (suc (suc (suc zero)))
                             (suc zero) ⟩
              → ⟨ fst ya ∈ fst (lookup (suc (suc (suc (suc (suc (suc K)))))) γ') ⟩
    consK-exist : (ya yc a ar c E z x e' : S) → ⟨ (e' ∷ x ∷ z ∷ E ∷ ya ∷ yc ∷ a ∷ ar ∷ c ∷ γ') ⊨
                    consAtL zero (suc zero) (suc (suc zero))
                    ∧̇ (var zero ∈̇ var (suc (suc (suc (suc zero))))) ⟩
                  → ⟨ fst e' ∈ fst (lookup (suc (suc (suc (suc (suc (suc (suc (suc (suc (suc (suc (suc (suc (suc K))))))))))))))
                                    (x ∷ z ∷ E ∷ ya ∷ yc ∷ a ∷ ar ∷ c ∷ γ')) ⟩
    consK-forall : (ya yc a ar c E z x e' : S) → ⟨ (e' ∷ x ∷ z ∷ E ∷ ya ∷ yc ∷ a ∷ ar ∷ c ∷ γ') ⊨
                     consAtL zero (suc zero) (suc (suc zero)) ⟩
                   → ⟨ fst e' ∈ fst (lookup (suc (suc (suc (suc (suc (suc (suc (suc (suc (suc (suc (suc (suc (suc K))))))))))))))
                                     (x ∷ z ∷ E ∷ ya ∷ yc ∷ a ∷ ar ∷ c ∷ γ')) ⟩
    subK-allin : (E ya yc b a ar c : S) → ⟨ (E ∷ ya ∷ yc ∷ b ∷ a ∷ ar ∷ c ∷ γ') ⊨
                   subValSuccAt (suc (suc (suc (suc (suc (suc (suc (suc zero))))))))
                                (suc (suc (suc (suc (suc zero)))))
                                (suc (suc (suc zero)))
                                (suc zero) ⟩
                 → ⟨ fst ya ∈ fst (lookup (suc (suc (suc (suc (suc (suc K)))))) γ') ⟩
    consK-allin : (E ya yc b a ar c z w x e' : S) → ⟨ (e' ∷ x ∷ w ∷ z ∷ E ∷ ya ∷ yc ∷ b ∷ a ∷ ar ∷ c ∷ γ') ⊨
                    consAtL zero (suc zero) (suc (suc (suc zero))) ⟩
                  → ⟨ fst e' ∈ fst (lookup (suc (suc (suc (suc (suc (suc (suc (suc (suc (suc (suc (suc (suc (suc (suc (suc K))))))))))))))))
                                    (x ∷ w ∷ z ∷ E ∷ ya ∷ yc ∷ b ∷ a ∷ ar ∷ c ∷ γ')) ⟩

module AbstractFrame {n : ℕ}
  (N0 N1 N2 N3 N4 N5 N6 N7 N8 N9 N10 N11 t0 t1 K : Fin (5 + n))
  (γ' : S ^ (11 + n))
  (sucK : (a : S) → ⟨ fst a ∈ fst (lookup (suc (suc (suc (suc (suc (suc K)))))) γ') ⟩
          → ⟨ sucV (fst a) ∈ fst (lookup (suc (suc (suc (suc (suc (suc K)))))) γ') ⟩)
  (tf : TFacts N0 N1 N2 N3 N4 N5 N6 N7 N8 N9 N10 N11 t0 t1 K γ')
  where

  open TFacts tf

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

  -- THE TWO PARTIALS' FACT BLOCKS, built ONCE from this frame's own record.
  -- Before `[LJ-1.158]` the six call sites below listed every hypothesis by
  -- name, so the same 37 and 35 arguments were written six times.  The
  -- archived `asRecursion`
  -- (archive/src/2026-08-09-rud-route/L/Recursion.lagda.md:320) is the same
  -- move: one record built from another record's fields.
  --
  -- `arityK` is DERIVED here from `transK` and is a HYPOTHESIS of
  -- `UpperAgree`, so `uf` supplies the derivation.  That is what the
  -- positional call sites did before, and it discharges nothing (C-38).
  lf : LFacts {n} N0 N1 N2 N3 N4 N5 N6 N7 N8 N9 N10 N11 t0 t1 K γ'
  lf = record
    { tagEq0 = tagEq0
    ; tagEq1 = tagEq1
    ; tagEq2 = tagEq2
    ; tagEq3 = tagEq3
    ; tagEq4 = tagEq4
    ; tagEq5 = tagEq5
    ; numK0 = numK0
    ; numK1 = numK1
    ; numK2 = numK2
    ; numK3 = numK3
    ; numK4 = numK4
    ; numK5 = numK5
    ; innerK = innerK
    ; pairK = pairK
    ; codesK = codesK
    ; codesK-un = codesK-un
    ; valK = valK
    ; valK-un = valK-un
    ; t0eq = t0eq
    ; t1eq = t1eq
    ; t0K = t0K
    ; num1K = num1K
    ; envK-mem = envK-mem
    ; envK-neg = envK-neg
    ; envK-imp = envK-imp
    ; envInK-mem = envInK-mem
    ; envInK-neg = envInK-neg
    ; envInK-imp = envInK-imp
    ; valV = valV
    ; valW = valW
    ; transK = transK
    ; subK₁-and = subK₁-and
    ; subK₀-and = subK₀-and
    ; subK₁-imp = subK₁-imp
    ; subK₀-imp = subK₀-imp
    ; someEnv = someEnv
    ; subK-neg = subK-neg }

  uf : UFacts {n} N0 N1 N2 N3 N4 N5 N6 N7 N8 N9 N10 N11 t0 t1 K γ'
  uf = record
    { tagEq6 = tagEq6
    ; tagEq7 = tagEq7
    ; tagEq8 = tagEq8
    ; tagEq9 = tagEq9
    ; tagEq10 = tagEq10
    ; tagEq11 = tagEq11
    ; numK6 = numK6
    ; numK7 = numK7
    ; numK8 = numK8
    ; numK9 = numK9
    ; numK10 = numK10
    ; numK11 = numK11
    ; innerK = innerK
    ; pairK = pairK
    ; arityK = arityK
    ; codesK = codesK
    ; codesK-un = codesK-un
    ; valK = valK
    ; valK-un = valK-un
    ; t0eq = t0eq
    ; t1eq = t1eq
    ; t0K = t0K
    ; num1K = num1K
    ; envK-neg = envK-neg
    ; envK-top = envK-top
    ; envK-allin = envK-allin
    ; envInK-neg = envInK-neg
    ; envInK-top = envInK-top
    ; envInK-imp = envInK-imp
    ; wKfact = wKfact
    ; subK-un = subK-un
    ; consK-exist = consK-exist
    ; consK-forall = consK-forall
    ; subK-allin = subK-allin
    ; consK-allin = consK-allin }

  p0b : Formula S (11 + n)
  p0b = LowerAgree.sixB {n} N0 N1 N2 N3 N4 N5 N6 N7 N8 N9 N10 N11 t0 t1 K γ'
        lf

  p1b : Formula S (11 + n)
  p1b = UpperAgree.sixB {n} N0 N1 N2 N3 N4 N5 N6 N7 N8 N9 N10 N11 t0 t1 K γ'
        sucK uf

  twelveB : Formula S (11 + n)
  twelveB = p0b ∧̇ p1b

  out : ⟨ γ' ⊨ twelveAt (suc (suc zero)) (suc zero) zero ⟩ → ⟨ γ' ⊨ twelveB ⟩
  out h =
    ( LowerAgree.out {n} N0 N1 N2 N3 N4 N5 N6 N7 N8 N9 N10 N11 t0 t1 K γ'
        lf h
    , UpperAgree.out {n} N0 N1 N2 N3 N4 N5 N6 N7 N8 N9 N10 N11 t0 t1 K γ'
        sucK uf h )

  back : ⟨ γ' ⊨ twelveB ⟩ → ⟨ γ' ⊨ twelveAt (suc (suc zero)) (suc zero) zero ⟩
  back h =
    let a = LowerAgree.back {n} N0 N1 N2 N3 N4 N5 N6 N7 N8 N9 N10 N11 t0 t1 K γ'
              lf (h .fst)
        b = UpperAgree.back {n} N0 N1 N2 N3 N4 N5 N6 N7 N8 N9 N10 N11 t0 t1 K γ'
              sucK uf (h .snd)
    in ( a .fst , ( a .snd .fst , ( a .snd .snd .fst , ( a .snd .snd .snd .fst
       , ( a .snd .snd .snd .snd .fst , ( a .snd .snd .snd .snd .snd
       , ( b .fst , ( b .snd .fst , ( b .snd .snd .fst , ( b .snd .snd .snd .fst
       , ( b .snd .snd .snd .snd .fst , b .snd .snd .snd .snd .snd )))))))))))

  -- The consumer's two hypotheses, in the types it states them.
  -- src/L/Condensation.lagda.md:6692-6697 declares `twelve-out` and
  -- `twelve-back` as unsupplied parameters of `SatGraphAgree`, over
  -- `(d e f : S)` at the environment `f ∷ e ∷ d ∷ γ`.  Here `γ'` IS
  -- that environment, so the two below are the consumer's parameters
  -- with the prefix already applied.
  --
  -- `w` is a function argument, not a frame parameter: `twelveB` does
  -- not read it, and a telescope slot would be copied at every
  -- instantiation while an argument is not (P-w).
  --
  -- THIS DISCHARGES NOTHING (C-38).  It exports the consumer's type
  -- and shortens the chain by one link.  Supplying `SatGraphAgree`
  -- still needs the frame INSTANTIATED at a real `K`, which is
  -- [LJ-1.113]'s 28 pieces of new content.
  twelve-out : (w : Fin (5 + n))
             → ⟨ γ' ⊨ twelveAt (suc (suc zero)) (suc zero) zero ⟩
             → ⟨ γ' ⊨ SatGraphB.twelveB {n} w K N0 N1 N2 N3 N4 N5
                                        N6 N7 N8 N9 N10 N11 t0 t1 ⟩
  twelve-out w h = sixes→twelve (out h)

  twelve-back : (w : Fin (5 + n))
              → ⟨ γ' ⊨ SatGraphB.twelveB {n} w K N0 N1 N2 N3 N4 N5
                                         N6 N7 N8 N9 N10 N11 t0 t1 ⟩
              → ⟨ γ' ⊨ twelveAt (suc (suc zero)) (suc zero) zero ⟩
  twelve-back w h = back (twelve→sixes h)
```
