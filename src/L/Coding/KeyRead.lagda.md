# The split key, read in the object language

```agda
{-# OPTIONS --cubical --safe --guardedness #-}

open import Base.Prelude
open import Base.Truth
open import Base.Classical using ( LEM )

module L.Coding.KeyRead {ℓ : Level} (lem : LEM (ℓ-suc ℓ)) where

open import FOL.ZFStructure using ( module hPropStructure )
open import FOL.Syntax using ( Formula; var; con; _∈̇_; _∧̇_; ∃̇_ )
open import FOL.Manipulation.Relabelling using ( embed )
import FOL.Absoluteness
open import V.Hierarchy {ℓ} using ( 𝒮ᵥ )
open import V.Coding {ℓ} using ( pr; module VCode )
open import L.Constructible {ℓ} using ( 𝒮ʟ; isL; isL-trans )
open import L.Axioms.Numerals {ℓ} using ( numeralL; numeralL-fst )
open import L.Axioms.Infinity {ℓ} lem using ( ωʟ; ω-specL )
open import L.Coding.Model {ℓ}
  using ( prAtL; prAtL-adequate; prʟ; prʟ-fst; numL; closedAt
        ; envOverAt; envOverAt-transport )
open import L.Coding.Shape {ℓ} using ( Onto; shapedAt )
open import L.Coding.Recover {ℓ} using ( module Decode )
import L.Coding.EnvSet

import Cubical.Data.Empty as Empty
open import Cubical.HITs.CumulativeHierarchy.Base using ( _∈_ )
open import Cubical.HITs.CumulativeHierarchy.Properties using ( ∈∈ₛ )
open import Cubical.HITs.CumulativeHierarchy.Constructions
  using ( ∅; ∅-empty; module InfinitySet )
open InfinitySet using ( #_ )
import Cubical.HITs.PropositionalTruncation as PT
open PT using ( ∥_∥₁; ∣_∣₁; squash₁ )

open TruthAlgebra (hPropAlgebra (ℓ-suc ℓ))
open hPropStructure 𝒮ʟ

module AbsL = FOL.Absoluteness.Single 𝒮ᵥ isL isL-trans
open AbsL renaming ( _⊨ᵐ_ to _⊨_ )

module EnvS = L.Coding.EnvSet {ℓ} lem

-- The conjunct, and its two directions.  Five binders: the arity, the
-- payload, the code, the parameter environment, and the environment's
-- length, which is pinned in `ωʟ` exactly as the arity is.
lift5 : ∀ {n} → Fin n → Fin (suc (suc (suc (suc (suc n)))))
lift5 i = suc (suc (suc (suc (suc i))))

-- The carrier is a SLOT and not a constant: the internal hierarchy speaks
-- under its own binder, so a conjunct that names its carrier cannot be said.
paramSetAtL : ∀ {n} → Fin n → Fin n → Formula S n
paramSetAtL b c = ∃̇ (∃̇ (∃̇ (∃̇ (∃̇
  ( prAtL (lift5 c) (suc (suc (suc (suc zero)))) (suc (suc (suc zero)))
  ∧̇ ( prAtL (suc (suc (suc zero))) (suc (suc zero)) (suc zero)
    ∧̇ ( (var zero ∈̇ con ωʟ)
      ∧̇ envOverAt (suc zero) zero (lift5 b) ) ) ) ))))

module _ (B : S) where
  -- What the reading returns: the parameter VECTOR, which is the thing a
  -- finite set cannot give and which the code set's elimination consumes.
  Split : ∀ {n} → Fin n → S ^ n → Type (ℓ-suc ℓ)
  Split c γ = Σ[ ar ∈ S ] Σ[ cd ∈ S ] Σ[ k ∈ ℕ ] Σ[ g ∈ EnvS.Ix B k ]
    (fst (lookup c γ) ≡ pr (fst ar) (pr (fst cd) (fst (EnvS.envS B g))))

  paramSetAtL-out : ∀ {n} (b c : Fin n) (γ : S ^ n)
                  → fst (lookup b γ) ≡ fst B
                  → ⟨ γ ⊨ paramSetAtL b c ⟩ → ∥ Split c γ ∥₁
  paramSetAtL-out b c γ qb = PT.rec squash₁ (λ { (ar , h1) →
    PT.rec squash₁ (λ { (z , h2) → PT.rec squash₁ (λ { (cd , h3) →
    PT.rec squash₁ (λ { (p , h4) →
    PT.rec squash₁ (λ { (d , (hp , (hq , (hω , hov)))) → PT.map
      (λ { (m , qm) → ar , cd , lower m
         , EnvS.Recover.g B (lower m) (d ∷ p ∷ cd ∷ z ∷ ar ∷ γ)
             (suc zero) zero (lift5 b)
             (qm ∙ numeralL-fst (lower m)) qb hov
         , ( subst ⟨_⟩ (prAtL-adequate (lift5 c)
               (suc (suc (suc (suc zero)))) (suc (suc (suc zero)))
               (d ∷ p ∷ cd ∷ z ∷ ar ∷ γ)) hp
           ∙ cong (pr (fst ar))
               ( subst ⟨_⟩ (prAtL-adequate (suc (suc (suc zero)))
                   (suc (suc zero)) (suc zero)
                   (d ∷ p ∷ cd ∷ z ∷ ar ∷ γ)) hq
               ∙ cong (pr (fst cd))
                   (EnvS.Recover.recovers B (lower m)
                     (d ∷ p ∷ cd ∷ z ∷ ar ∷ γ) (suc zero) zero (lift5 b)
                     (qm ∙ numeralL-fst (lower m)) qb hov) ) ) })
      (subst ⟨_⟩ (ω-specL d) hω) }) h4 }) h3 }) h2 }) h1 })

  paramSetAtL-in : ∀ {n} (b c : Fin n) (γ : S ^ n)
                 → fst (lookup b γ) ≡ fst B
                 → (ar cd : S) {k : ℕ} (g : EnvS.Ix B k)
                 → fst (lookup c γ)
                   ≡ pr (fst ar) (pr (fst cd) (fst (EnvS.envS B g)))
                 → ⟨ γ ⊨ paramSetAtL b c ⟩
  paramSetAtL-in {n} b c γ qb ar cd {k} g e =
    ∣ ar , ∣ prʟ cd (EnvS.envS B g) , ∣ cd , ∣ EnvS.envS B g , ∣ numeralL k
    , ( subst ⟨_⟩ (sym (prAtL-adequate (lift5 c)
          (suc (suc (suc (suc zero)))) (suc (suc (suc zero))) δ))
          (e ∙ cong (pr (fst ar)) (sym (prʟ-fst cd (EnvS.envS B g))))
      , ( subst ⟨_⟩ (sym (prAtL-adequate (suc (suc (suc zero)))
            (suc (suc zero)) (suc zero) δ)) (prʟ-fst cd (EnvS.envS B g))
        , ( subst ⟨_⟩ (sym (ω-specL (numeralL k))) ∣ lift k , refl ∣₁
          , envOverAt-transport (B ∷ ((# k) , numL k) ∷ EnvS.envS B g ∷ [])
              δ (suc (suc zero)) (suc zero) zero (suc zero) zero (lift5 b)
              refl (sym (numeralL-fst k)) (sym qb)
              (EnvS.envOver B g) ) ) ) ∣₁ ∣₁ ∣₁ ∣₁ ∣₁
    where
    δ : S ^ suc (suc (suc (suc (suc n))))
    δ = numeralL k ∷ EnvS.envS B g ∷ cd ∷ prʟ cd (EnvS.envS B g) ∷ ar ∷ γ
```

```agda
-- =====================================================================
-- THE CODE HALF, at the EMPTY alphabet.
--
-- Under the re-key the code component is the code of a PARAMETER-FREE
-- formula, so the decoder must run at `K = ⊥*`, where the delivered call
-- site runs it at the carrier's own alphabet.  `Onto` at the empty
-- alphabet says the carrier slot has no member at all, so the whole
-- instantiation is that one observation.
-- =====================================================================
emptyOnto : ∀ {m} (A : Fin m) (γ : S ^ m) → fst (lookup A γ) ≡ ∅
          → Onto {K = ⊥* {ℓ}} Empty.rec* A γ
emptyOnto A γ q y y∈ = Empty.rec
  (∅-empty y (∈∈ₛ {a = y} {b = ∅} .fst (subst (λ w → ⟨ y ∈ w ⟩) q y∈)))

module EmptyDecode {m : ℕ} (C A : Fin m) (γ : S ^ m)
  (q : fst (lookup A γ) ≡ ∅)
  (hcl : ⟨ γ ⊨ closedAt C ⟩) (hsh : ⟨ γ ⊨ shapedAt C A ⟩) where

  open Decode {K = ⊥* {ℓ}} Empty.rec* C A γ (emptyOnto A γ q) hcl hsh public

  -- What it returns: the PARAMETER-FREE formula whose code the key
  -- carries, which is the form `code∈limit` and `splitKey` consume.
  recoverEmpty : (n : ℕ) (x : S) → Wf n x
               → ∥ Σ[ χ ∈ Formula (⊥* {ℓ}) n ] (VCode.⌜ embed χ ⌝ ≡ fst x) ∥₁
  recoverEmpty = recover
```
