# Cantor-Schroeder-Bernstein, at the index types

```agda
{-# OPTIONS --cubical --safe --guardedness #-}

open import Base.Prelude
open import Base.Classical using ( LEM )

module V.CantorBernstein {ℓ : Level} (lem : LEM ℓ) where

open import Cubical.Functions.Embedding using ( Embedding-into-isSet→isSet )
import Cubical.Data.Sum as Sum
open Sum using ( _⊎_; inl; inr )
import Cubical.Data.Empty as Empty
open import Cubical.Data.Empty.Properties using ( isProp⊥ )
import Cubical.HITs.PropositionalTruncation as PT
open PT using ( ∣_∣₁; ∥_∥₁; squash₁ )
open import Cubical.Data.Sigma using ( Σ≡Prop )
open import Cubical.HITs.CumulativeHierarchy.Base using ( V; setIsSet )
open import Cubical.HITs.CumulativeHierarchy.Properties
  using ( ⟪_⟫; ⟪_⟫↪; isEmb⟪_⟫↪ )
```

```agda
-- Two injections, one each way, give one bijection.  The installed
-- library does not ship it, and both target theorems want it as a
-- reading, so it is proved once here at two ARBITRARY types under one
-- set-ness hypothesis.  The construction names no tower, no stage and
-- no satisfaction relation.
--
-- The proof runs on the index level, which is why it transfers cheaply.
-- The BAD elements of `A` are those reachable by a finite alternating
-- preimage chain starting outside the image of `g`; `ĥ` sends a bad
-- element through `f` and a good one back along `g⁻¹`.  The chain is the
-- small predicate family `Cₙ`, and the one structural fact needed is
-- that `x ↦ g (f x)` closes the bad set.  Excluded middle enters TWICE:
-- to decide the bad set, and to extract `g⁻¹` from the truncated image
-- statement.  The dose is taken at the level of the types themselves, so
-- a chapter holding `LEM (ℓ-suc ℓ)` redeems it through `lowerLEM`.
module Bernstein {A B : Type ℓ} (setA : isSet A)
                 (f : A → B) (fi : (x y : A) → f x ≡ f y → x ≡ y)
                 (g : B → A) (gi : (x y : B) → g x ≡ g y → x ≡ y) where

  imG : A → hProp ℓ
  imG x = (∥ Σ[ y ∈ B ] (g y ≡ x) ∥₁ , squash₁)

  C₀ : A → hProp ℓ
  C₀ x = ((⟨ imG x ⟩ → Empty.⊥) , isPropΠ (λ _ → isProp⊥))

  C₊ : (A → hProp ℓ) → A → hProp ℓ
  C₊ C x = (∥ Σ[ y ∈ B ] Σ[ z ∈ A ] ((g y ≡ x) × ((f z ≡ y) × ⟨ C z ⟩)) ∥₁ , squash₁)

  Cₙ : ℕ → A → hProp ℓ
  Cₙ zero = C₀
  Cₙ (suc n) = C₊ (Cₙ n)

  C : A → hProp ℓ
  C x = (∥ Σ[ n ∈ ℕ ] ⟨ Cₙ n x ⟩ ∥₁ , squash₁)

  c-in : {x : A} {n : ℕ} → ⟨ Cₙ n x ⟩ → ⟨ C x ⟩
  c-in {x} {n} h = ∣ n , h ∣₁

  gf-closed : {x : A} → ⟨ C x ⟩ → ⟨ C (g (f x)) ⟩
  gf-closed {x} = PT.rec (snd (C (g (f x)))) go
    where
    go : Σ[ n ∈ ℕ ] ⟨ Cₙ n x ⟩ → ⟨ C (g (f x)) ⟩
    go (n , cx) = c-in {x = g (f x)} {n = suc n} ∣ f x , x , (refl , (refl , cx)) ∣₁

  C-view : {x : A} → ⟨ C x ⟩
         → ∥ (⟨ C₀ x ⟩ ⊎ (Σ[ z ∈ A ] ((g (f z) ≡ x) × ⟨ C z ⟩))) ∥₁
  C-view {x} = PT.rec squash₁ go
    where
    go : Σ[ n ∈ ℕ ] ⟨ Cₙ n x ⟩ → ∥ (⟨ C₀ x ⟩ ⊎ (Σ[ z ∈ A ] ((g (f z) ≡ x) × ⟨ C z ⟩))) ∥₁
    go (zero , c0) = ∣ inl c0 ∣₁
    go (suc n , cs) = PT.map inr (PT.map (λ { (y , z , gy , fz , cz) →
        z , ((cong g fz ∙ gy) , c-in {x = z} {n = n} cz) }) cs)

  notC→imG : {x : A} → (⟨ C x ⟩ → Empty.⊥) → ⟨ imG x ⟩
  notC→imG {x} nC = Sum.rec {A = ⟨ imG x ⟩} {B = ⟨ imG x ⟩ → Empty.⊥} {C = ⟨ imG x ⟩}
    (λ h → h) (λ nC₀ → Empty.rec (nC (c-in {n = zero} nC₀)))
    (lem (imG x))

  fiberG-prop : (x : A) → isProp (Σ[ y ∈ B ] (g y ≡ x))
  fiberG-prop x (y , p) (y' , p') = Σ≡Prop {A = B} {B = λ y → g y ≡ x}
    (λ y → setA (g y) x) (gi y y' (p ∙ sym p'))

  fiberG : (x : A) → ⟨ imG x ⟩ → Σ[ y ∈ B ] (g y ≡ x)
  fiberG x = PT.rec (fiberG-prop x) (λ w → w)

  ginv : {x : A} → (⟨ C x ⟩ → Empty.⊥) → B
  ginv {x} nC = fiberG x (notC→imG nC) .fst

  ginv-spec : {x : A} (nC : ⟨ C x ⟩ → Empty.⊥) → g (ginv nC) ≡ x
  ginv-spec {x} nC = fiberG x (notC→imG nC) .snd

  h : (x : A) → ⟨ C x ⟩ ⊎ (⟨ C x ⟩ → Empty.⊥) → B
  h x (inl _) = f x
  h x (inr nC) = ginv nC

  h-inj : (x x' : A) (dx : ⟨ C x ⟩ ⊎ (⟨ C x ⟩ → Empty.⊥)) (dx' : ⟨ C x' ⟩ ⊎ (⟨ C x' ⟩ → Empty.⊥))
        → h x dx ≡ h x' dx' → x ≡ x'
  h-inj x x' (inl cx) (inl cx') e = fi x x' e
  h-inj x x' (inl cx) (inr nCx') e =
    Empty.rec (nCx' (subst (λ w → ⟨ C w ⟩) (cong g e ∙ ginv-spec nCx') (gf-closed {x = x} cx)))
  h-inj x x' (inr nCx) (inl cx') e =
    Empty.rec (nCx (subst (λ w → ⟨ C w ⟩) (sym (cong g e) ∙ ginv-spec nCx) (gf-closed {x = x'} cx')))
  h-inj x x' (inr nCx) (inr nCx') e = sym (ginv-spec nCx) ∙ cong g e ∙ ginv-spec nCx'

  h-surj : (y : B) (d : ⟨ C (g y) ⟩ ⊎ (⟨ C (g y) ⟩ → Empty.⊥))
         → ∥ Σ[ x ∈ A ] Σ[ dx ∈ ⟨ C x ⟩ ⊎ (⟨ C x ⟩ → Empty.⊥) ] (h x dx ≡ y) ∥₁
  h-surj y (inr nCgy) = ∣ g y , inr nCgy , gi (ginv nCgy) y (ginv-spec nCgy) ∣₁
  h-surj y (inl cgy) = PT.rec squash₁
    (λ { (inl c0) → Empty.rec (c0 ∣ y , refl ∣₁) ; (inr (z , gfy , cz)) → ∣ z , inl cz , gi (f z) y gfy ∣₁ })
    (C-view {x = g y} cgy)

  h-cons : (x : A) (dx dx' : ⟨ C x ⟩ ⊎ (⟨ C x ⟩ → Empty.⊥)) → h x dx ≡ h x dx'
  h-cons x (inl cx) (inl cx') = refl
  h-cons x (inl cx) (inr nCx') = Empty.rec (nCx' cx)
  h-cons x (inr nCx) (inl cx) = Empty.rec (nCx cx)
  h-cons x (inr nCx) (inr nCx') = cong fst (fiberG-prop x (fiberG x (notC→imG nCx)) (fiberG x (notC→imG nCx')))

  ĥ : A → B
  ĥ x = h x (lem (C x))

  ĥ-inj : (x x' : A) → ĥ x ≡ ĥ x' → x ≡ x'
  ĥ-inj x x' e = h-inj x x' (lem (C x)) (lem (C x')) e

  ĥ-surj : (y : B) → ∥ Σ[ x ∈ A ] (ĥ x ≡ y) ∥₁
  ĥ-surj y = PT.map (λ { (x , dx , e) → x , sym (h-cons x dx (lem (C x))) ∙ e })
    (h-surj y (lem (C (g y))))
```

```agda
-- The set form, at a small carrier: a `V`'s member type embeds into a
-- set, so it is one.
small-set : (a : V ℓ) → isSet (⟪ a ⟫)
small-set a = Embedding-into-isSet→isSet (⟪ a ⟫↪ , isEmb⟪ a ⟫↪) setIsSet

cantor-bernstein : (a b : V ℓ) (f : ⟪ a ⟫ → ⟪ b ⟫)
    → ((x y : ⟪ a ⟫) → f x ≡ f y → x ≡ y)
    → (g : ⟪ b ⟫ → ⟪ a ⟫) → ((x y : ⟪ b ⟫) → g x ≡ g y → x ≡ y)
    → Σ[ h ∈ (⟪ a ⟫ → ⟪ b ⟫) ]
        (((x y : ⟪ a ⟫) → h x ≡ h y → x ≡ y)
      × ((y : ⟪ b ⟫) → ∥ Σ[ x ∈ ⟪ a ⟫ ] (h x ≡ y) ∥₁))
cantor-bernstein a b f fi g gi = M.ĥ , ( M.ĥ-inj , M.ĥ-surj )
  where
  module M = Bernstein {A = ⟪ a ⟫} {B = ⟪ b ⟫} (small-set a) f fi g gi
```

```agda
-- The corollary, generic in the carrier `C`, the small-type assignment
-- `P` and the code notion.  A consumer supplies set-ness and a readback
-- from a code to an honest injection, and reads back a bijection from a
-- pair of codes.  `∃bijection` takes the pair truncated; `mutual→bijection`
-- takes it as data.
module MutualInj {ℓ₁ ℓ₂ : Level} (C : Type ℓ₁) (P : C → Type ℓ)
    (R : (a b : C) → Type ℓ₂)
    (setP : (a : C) → isSet (P a))
    (read : (a b : C) → R a b
          → Σ[ f ∈ (P a → P b) ] ((x y : P a) → f x ≡ f y → x ≡ y)) where

  mutual→bijection : (a b : C) → R a b → R b a
    → Σ[ h ∈ (P a → P b) ]
        (((x y : P a) → h x ≡ h y → x ≡ y)
      × ((y : P b) → ∥ Σ[ x ∈ P a ] (h x ≡ y) ∥₁))
  mutual→bijection a b fwd bwd = M.ĥ , ( M.ĥ-inj , M.ĥ-surj )
    where
    module M = Bernstein {A = P a} {B = P b} (setP a)
      (read a b fwd .fst) (read a b fwd .snd)
      (read b a bwd .fst) (read b a bwd .snd)

  ∃bijection : (a b : C) → ∥ R a b ∥₁ → ∥ R b a ∥₁
    → ∥ Σ[ h ∈ (P a → P b) ]
        (((x y : P a) → h x ≡ h y → x ≡ y)
      × ((y : P b) → ∥ Σ[ x ∈ P a ] (h x ≡ y) ∥₁)) ∥₁
  ∃bijection a b fwd bwd = PT.rec squash₁
    (λ w → PT.rec squash₁ (λ w' → ∣ mutual→bijection a b w w' ∣₁) bwd)
    fwd
```
