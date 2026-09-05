{-# OPTIONS --cubical --safe --guardedness #-}

-- [LJ-1.353] MINIATURE.  Does the retired route's ambient
-- Cantor-Schroeder-Bernstein transfer to the live tree unchanged?
--
-- WHAT THIS FILE DECIDES.  The archived block
-- archive/src/2026-08-09-rud-route/L/Cardinal.lagda.md:89-190 proves
-- `csb` at the index types of two carriers.  This file is that block
-- verbatim, with two edits: the carrier is restated as `V ℓ` (the
-- archived file carried it as `S` of the retired structure, and `S`
-- appears in the two signatures only), and the imports are the live
-- tree's.  Exit 0 means the ambient port is a mechanical import
-- rewiring, priced at the archived line count.
--
-- The proof needs no choice.  The inverse of `g` is extracted by
-- `fiberG` from the propositionality of the fiber, which follows from
-- `gi`.  Excluded middle enters through `lowerLEM`, already a module
-- parameter of every L chapter.

open import Base.Prelude
open import Base.Truth
open import Base.Classical using ( LEM; lowerLEM )

module LJ-1-353.AmbCsb {ℓ : Level} (lem : LEM (ℓ-suc ℓ)) where

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

module CSB (a b : V ℓ) (f : ⟪ a ⟫ → ⟪ b ⟫) (fi : (x y : ⟪ a ⟫) → f x ≡ f y → x ≡ y)
           (g : ⟪ b ⟫ → ⟪ a ⟫) (gi : (x y : ⟪ b ⟫) → g x ≡ g y → x ≡ y) where

  isSetA : isSet (⟪ a ⟫)
  isSetA = Embedding-into-isSet→isSet (⟪ a ⟫↪ , isEmb⟪ a ⟫↪) setIsSet

  imG : ⟪ a ⟫ → hProp ℓ
  imG x = (∥ Σ[ y ∈ ⟪ b ⟫ ] (g y ≡ x) ∥₁ , squash₁)

  C₀ : ⟪ a ⟫ → hProp ℓ
  C₀ x = ((⟨ imG x ⟩ → Empty.⊥) , isPropΠ (λ _ → isProp⊥))

  C₊ : (⟪ a ⟫ → hProp ℓ) → ⟪ a ⟫ → hProp ℓ
  C₊ C x = (∥ Σ[ y ∈ ⟪ b ⟫ ] Σ[ z ∈ ⟪ a ⟫ ] ((g y ≡ x) × ((f z ≡ y) × ⟨ C z ⟩)) ∥₁ , squash₁)

  Cₙ : ℕ → ⟪ a ⟫ → hProp ℓ
  Cₙ zero = C₀
  Cₙ (suc n) = C₊ (Cₙ n)

  C : ⟪ a ⟫ → hProp ℓ
  C x = (∥ Σ[ n ∈ ℕ ] ⟨ Cₙ n x ⟩ ∥₁ , squash₁)

  c-in : {x : ⟪ a ⟫} {n : ℕ} → ⟨ Cₙ n x ⟩ → ⟨ C x ⟩
  c-in {x} {n} h = ∣ n , h ∣₁

  gf-closed : {x : ⟪ a ⟫} → ⟨ C x ⟩ → ⟨ C (g (f x)) ⟩
  gf-closed {x} = PT.rec (snd (C (g (f x)))) go
    where
    go : Σ[ n ∈ ℕ ] ⟨ Cₙ n x ⟩ → ⟨ C (g (f x)) ⟩
    go (n , cx) = c-in {x = g (f x)} {n = suc n} ∣ f x , x , (refl , (refl , cx)) ∣₁

  C-view : {x : ⟪ a ⟫} → ⟨ C x ⟩
         → ∥ (⟨ C₀ x ⟩ ⊎ (Σ[ z ∈ ⟪ a ⟫ ] ((g (f z) ≡ x) × ⟨ C z ⟩))) ∥₁
  C-view {x} = PT.rec squash₁ go
    where
    go : Σ[ n ∈ ℕ ] ⟨ Cₙ n x ⟩ → ∥ (⟨ C₀ x ⟩ ⊎ (Σ[ z ∈ ⟪ a ⟫ ] ((g (f z) ≡ x) × ⟨ C z ⟩))) ∥₁
    go (zero , c0) = ∣ inl c0 ∣₁
    go (suc n , cs) = PT.map inr (PT.map (λ { (y , z , gy , fz , cz) →
        z , ((cong g fz ∙ gy) , c-in {x = z} {n = n} cz) }) cs)

  notC→imG : {x : ⟪ a ⟫} → (⟨ C x ⟩ → Empty.⊥) → ⟨ imG x ⟩
  notC→imG {x} nC = Sum.rec {A = ⟨ imG x ⟩} {B = ⟨ imG x ⟩ → Empty.⊥} {C = ⟨ imG x ⟩}
    (λ h → h) (λ nC₀ → Empty.rec (nC (c-in {n = zero} nC₀)))
    (lowerLEM lem (imG x))

  fiberG-prop : (x : ⟪ a ⟫) → isProp (Σ[ y ∈ ⟪ b ⟫ ] (g y ≡ x))
  fiberG-prop x (y , p) (y' , p') = Σ≡Prop {A = ⟪ b ⟫} {B = λ y → g y ≡ x}
    (λ y → isSetA (g y) x) (gi y y' (p ∙ sym p'))

  fiberG : (x : ⟪ a ⟫) → ⟨ imG x ⟩ → Σ[ y ∈ ⟪ b ⟫ ] (g y ≡ x)
  fiberG x = PT.rec (fiberG-prop x) (λ w → w)

  ginv : {x : ⟪ a ⟫} → (⟨ C x ⟩ → Empty.⊥) → ⟪ b ⟫
  ginv {x} nC = fiberG x (notC→imG nC) .fst

  ginv-spec : {x : ⟪ a ⟫} (nC : ⟨ C x ⟩ → Empty.⊥) → g (ginv nC) ≡ x
  ginv-spec {x} nC = fiberG x (notC→imG nC) .snd

  h : (x : ⟪ a ⟫) → ⟨ C x ⟩ ⊎ (⟨ C x ⟩ → Empty.⊥) → ⟪ b ⟫
  h x (inl _) = f x
  h x (inr nC) = ginv nC

  h-inj : (x x' : ⟪ a ⟫) (dx : ⟨ C x ⟩ ⊎ (⟨ C x ⟩ → Empty.⊥)) (dx' : ⟨ C x' ⟩ ⊎ (⟨ C x' ⟩ → Empty.⊥))
        → h x dx ≡ h x' dx' → x ≡ x'
  h-inj x x' (inl cx) (inl cx') e = fi x x' e
  h-inj x x' (inl cx) (inr nCx') e =
    Empty.rec (nCx' (subst (λ w → ⟨ C w ⟩) (cong g e ∙ ginv-spec nCx') (gf-closed {x = x} cx)))
  h-inj x x' (inr nCx) (inl cx') e =
    Empty.rec (nCx (subst (λ w → ⟨ C w ⟩) (sym (cong g e) ∙ ginv-spec nCx) (gf-closed {x = x'} cx')))
  h-inj x x' (inr nCx) (inr nCx') e = sym (ginv-spec nCx) ∙ cong g e ∙ ginv-spec nCx'

  h-surj : (y : ⟪ b ⟫) (d : ⟨ C (g y) ⟩ ⊎ (⟨ C (g y) ⟩ → Empty.⊥))
         → ∥ Σ[ x ∈ ⟪ a ⟫ ] Σ[ dx ∈ ⟨ C x ⟩ ⊎ (⟨ C x ⟩ → Empty.⊥) ] (h x dx ≡ y) ∥₁
  h-surj y (inr nCgy) = ∣ g y , inr nCgy , gi (ginv nCgy) y (ginv-spec nCgy) ∣₁
  h-surj y (inl cgy) = PT.rec squash₁
    (λ { (inl c0) → Empty.rec (c0 ∣ y , refl ∣₁) ; (inr (z , gfy , cz)) → ∣ z , inl cz , gi (f z) y gfy ∣₁ })
    (C-view {x = g y} cgy)

  h-cons : (x : ⟪ a ⟫) (dx dx' : ⟨ C x ⟩ ⊎ (⟨ C x ⟩ → Empty.⊥)) → h x dx ≡ h x dx'
  h-cons x (inl cx) (inl cx') = refl
  h-cons x (inl cx) (inr nCx') = Empty.rec (nCx' cx)
  h-cons x (inr nCx) (inl cx) = Empty.rec (nCx cx)
  h-cons x (inr nCx) (inr nCx') = cong fst (fiberG-prop x (fiberG x (notC→imG nCx)) (fiberG x (notC→imG nCx')))

  ĥ : ⟪ a ⟫ → ⟪ b ⟫
  ĥ x = h x (lowerLEM lem (C x))

  ĥ-inj : (x x' : ⟪ a ⟫) → ĥ x ≡ ĥ x' → x ≡ x'
  ĥ-inj x x' e = h-inj x x' (lowerLEM lem (C x)) (lowerLEM lem (C x')) e

  ĥ-surj : (y : ⟪ b ⟫) → ∥ Σ[ x ∈ ⟪ a ⟫ ] (ĥ x ≡ y) ∥₁
  ĥ-surj y = PT.map (λ { (x , dx , e) → x , sym (h-cons x dx (lowerLEM lem (C x))) ∙ e })
    (h-surj y (lowerLEM lem (C (g y))))

csb : (a b : V ℓ) (f : ⟪ a ⟫ → ⟪ b ⟫) → ((x y : ⟪ a ⟫) → f x ≡ f y → x ≡ y)
    → (g : ⟪ b ⟫ → ⟪ a ⟫) → ((x y : ⟪ b ⟫) → g x ≡ g y → x ≡ y)
    → Σ[ h ∈ (⟪ a ⟫ → ⟪ b ⟫) ] (((x y : ⟪ a ⟫) → h x ≡ h y → x ≡ y) × ((y : ⟪ b ⟫) → ∥ Σ[ x ∈ ⟪ a ⟫ ] (h x ≡ y) ∥₁))
csb a b f fi g gi = h , (h-inj , h-surj)
  where
  module M = CSB a b f fi g gi
  h : ⟪ a ⟫ → ⟪ b ⟫
  h = M.ĥ
  h-inj = M.ĥ-inj
  h-surj = M.ĥ-surj
