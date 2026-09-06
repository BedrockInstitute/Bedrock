# The environment tower

```agda
{-# OPTIONS --cubical --safe --guardedness #-}

open import Base.Prelude
open import Base.Truth
open import Base.Classical using ( LEM )

module L.Coding.Tower {ℓ : Level} (lem : LEM (ℓ-suc ℓ)) where

open import FOL.ZFStructure using ( module hPropStructure )
open import FOL.Syntax using
  ( Formula; Term; var; con; _∈̇_; _≐_; _∧̇_; ∃̇_ )
import FOL.Absoluteness
open import V.Hierarchy {ℓ} using ( 𝒮ᵥ; extensionalV )
open import V.Coding {ℓ} using ( pr )
open import L.Constructible {ℓ} using ( 𝒮ʟ; isL; isL-trans )
open import L.Coding.Model {ℓ} using
  ( prAtL; prAtL-adequate; envSetAt; prʟ; prʟ-fst )
open import L.Coding.EnvSet {ℓ} lem using ( envSet )
open import L.Coding.Sound {ℓ} lem using ( module Ambient; module AmbientHolds )
open import L.Recursion {ℓ} lem using ( smallDom )
open import L.Axioms.Full {ℓ} lem using ( hasSeparationL )
open import L.Axioms.Numerals {ℓ} using ( numeralL; numeralL-fst )
open import L.Axioms.Infinity {ℓ} lem using ( ωʟ; ω-specL )

open import Cubical.Data.Nat using ( _+_ )
open import Cubical.Data.Vec using ( _∷_; []; lookup )
open import Cubical.Functions.Logic using ( ⇔toPath )
import Cubical.HITs.PropositionalTruncation as PT
open PT using ( ∥_∥₁; ∣_∣₁; squash₁ )
open import Cubical.HITs.CumulativeHierarchy.Base using ( V; _∈_ )
open import Cubical.HITs.CumulativeHierarchy.Constructions using ( module InfinitySet )
open InfinitySet {ℓ} using ( #_ )

open TruthAlgebra (hPropAlgebra (ℓ-suc ℓ)) using ( _⊓_ )
open hPropStructure 𝒮ʟ using ( S )

module AbsL = FOL.Absoluteness.Single 𝒮ᵥ isL isL-trans using ( _^_; _⊨ᵐ_ )
open AbsL using ( _^_ ) renaming ( _⊨ᵐ_ to _⊨_ )
```

The slot arithmetic this chapter needs, at the four innermost slots.

```agda
i0 : ∀ {j} → Fin (suc j)
i0 = zero
i1 : ∀ {j} → Fin (2 + j)
i1 = suc i0
i2 : ∀ {j} → Fin (3 + j)
i2 = suc i1
i3 : ∀ {j} → Fin (4 + j)
i3 = suc i2

pr-out : ∀ {m} (q u v : Fin m) (γ : S ^ m) → ⟨ γ ⊨ prAtL q u v ⟩
       → fst (lookup q γ) ≡ pr (fst (lookup u γ)) (fst (lookup v γ))
pr-out q u v γ h = subst ⟨_⟩ (prAtL-adequate q u v γ) h

pr-in : ∀ {m} (q u v : Fin m) (γ : S ^ m)
      → fst (lookup q γ) ≡ pr (fst (lookup u γ)) (fst (lookup v γ))
      → ⟨ γ ⊨ prAtL q u v ⟩
pr-in q u v γ e = subst ⟨_⟩ (sym (prAtL-adequate q u v γ)) e

down : (x : S) (y : V ℓ) → ⟨ y ∈ fst x ⟩ → S
down x y h = y , isL-trans {x = fst x} {y = y} h (snd x)
```

THE TOWER SET.  The pairs (n, Eₙ), cut by separation out of a stage
that holds every entry.  The cutting formula is not Δ₀ and need not
be: it builds the set, and only its two readers leave this section.

```agda
module Tower (W : S) where
  entry : ℕ → S
  entry n = prʟ (numeralL n) (envSet W n)

  private
    dom : Σ[ d ∈ S ] ((k : Lift {ℓ-zero} {ℓ} ℕ) → ⟨ fst (entry (lower k)) ∈ fst d ⟩)
    dom = smallDom (Lift {ℓ-zero} {ℓ} ℕ) (λ k → entry (lower k))

    -- At F ∷ n ∷ b ∷ z ∷ []: b = W, z = (n, F), n ∈ ω, F the environment
    -- set of arity n over b.
    towerFo : Formula S 1
    towerFo = ∃̇ (∃̇ (∃̇ ( (var i2 ≐ con W)
                      ∧̇ ( prAtL i3 i1 i0
                      ∧̇ ( (var i1 ∈̇ con ωʟ)
                      ∧̇ envSetAt i0 i1 i2 )))))

  opaque
    tower : S
    tower = hasSeparationL (dom .fst) towerFo .fst .fst

    tower-mem : (x : S)
              → (fst x ∈ fst tower) ≡ ((fst x ∈ fst (dom .fst)) ⊓ ((x ∷ []) ⊨ towerFo))
    tower-mem = hasSeparationL (dom .fst) towerFo .fst .snd

  private
    holdsAt : (n : ℕ) → ⟨ (envSet W n ∷ numeralL n ∷ W ∷ entry n ∷ []) ⊨ envSetAt i0 i1 i2 ⟩
    holdsAt n = AmbientHolds.holds W (envSet W n ∷ numeralL n ∷ W ∷ entry n ∷ [])
                  i0 i1 i2 n refl (numeralL-fst n) refl

    tower-in : (n : ℕ) → ⟨ fst (entry n) ∈ fst tower ⟩
    tower-in n = subst ⟨_⟩ (sym (tower-mem (entry n)))
      ( dom .snd (lift n)
      , ∣ W , ∣ numeralL n , ∣ envSet W n
        , ( refl
          , ( pr-in i3 i1 i0 (envSet W n ∷ numeralL n ∷ W ∷ entry n ∷ [])
                (prʟ-fst (numeralL n) (envSet W n))
            , ( subst ⟨_⟩ (sym (ω-specL (numeralL n))) ∣ lift n , refl ∣₁
              , holdsAt n ))) ∣₁ ∣₁ ∣₁ )

  tower-in′ : (n : ℕ) → ⟨ pr (# n) (fst (envSet W n)) ∈ fst tower ⟩
  tower-in′ n = subst (λ u → ⟨ u ∈ fst tower ⟩)
    (prʟ-fst (numeralL n) (envSet W n) ∙ cong (λ u → pr u (fst (envSet W n))) (numeralL-fst n))
    (tower-in n)

  tower-out : (x : S) → ⟨ fst x ∈ fst tower ⟩
            → ∥ Σ[ n ∈ ℕ ] (fst x ≡ pr (# n) (fst (envSet W n))) ∥₁
  tower-out x hx = PT.rec squash₁ byB (subst ⟨_⟩ (tower-mem x) hx .snd)
    where
    Goal : Type (ℓ-suc ℓ)
    Goal = ∥ Σ[ n ∈ ℕ ] (fst x ≡ pr (# n) (fst (envSet W n))) ∥₁

    byB : Σ[ b ∈ S ] ⟨ (b ∷ x ∷ []) ⊨ ∃̇ (∃̇ ( (var i2 ≐ con W)
                    ∧̇ ( prAtL i3 i1 i0
                    ∧̇ ( (var i1 ∈̇ con ωʟ)
                    ∧̇ envSetAt i0 i1 i2 )))) ⟩ → Goal
    byB (b , hb) = PT.rec squash₁ byN hb
      where
      byN : Σ[ n ∈ S ] ⟨ (n ∷ b ∷ x ∷ []) ⊨ ∃̇ ( (var i2 ≐ con W)
                    ∧̇ ( prAtL i3 i1 i0
                    ∧̇ ( (var i1 ∈̇ con ωʟ)
                    ∧̇ envSetAt i0 i1 i2 ))) ⟩ → Goal
      byN (n , hn) = PT.rec squash₁ byE hn
        where
        byE : Σ[ F ∈ S ] ⟨ (F ∷ n ∷ b ∷ x ∷ []) ⊨ ( (var i2 ≐ con W)
                    ∧̇ ( prAtL i3 i1 i0
                    ∧̇ ( (var i1 ∈̇ con ωʟ)
                    ∧̇ envSetAt i0 i1 i2 ))) ⟩ → Goal
        byE (F , (qb , (hp , (hω , hE)))) = PT.rec squash₁ byK (subst ⟨_⟩ (ω-specL n) hω)
          where
          xq : fst x ≡ pr (fst n) (fst F)
          xq = pr-out i3 i1 i0 (F ∷ n ∷ b ∷ x ∷ []) hp

          byK : Σ[ k ∈ Lift {ℓ-zero} {ℓ-suc ℓ} ℕ ] (fst n ≡ fst (numeralL (lower k))) → Goal
          byK (k , qn) = ∣ lower k , xq ∙ cong₂ pr (qn ∙ numeralL-fst (lower k)) Eq ∣₁
            where
            module Am = Ambient W (F ∷ n ∷ b ∷ x ∷ []) i0 i1 i2 (lower k)
                          (qn ∙ numeralL-fst (lower k)) qb hE using (into; outof)
            Eq : fst F ≡ fst (envSet W (lower k))
            Eq = extensionalV {a = fst F} {b = fst (envSet W (lower k))}
              (λ z → ⇔toPath
                (λ z∈ → Am.into (down F z z∈) z∈)
                (λ z∈ → Am.outof (down (envSet W (lower k)) z z∈) z∈))
```
