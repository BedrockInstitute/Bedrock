{-# OPTIONS --cubical --safe --guardedness #-}

open import Base.Prelude
open import Base.Truth
open import Base.Classical using ( LEM )

-- [L3.32-T132] One DefAt adequacy arm, measured in the ideal form's home.
--
-- The measured arm is the description-level, two-directional adequacy of the
-- definable-powerset formula `DefAt` against the surviving `L.Definability`
-- interface (`defSet`, whose carrier-level recognition is `𝒟ₒ-intro`/`𝒟ₒ-inv`).
-- The object formula text (`CP.DefAt`, `CP.DefBody`, `CP.isCodeAt`,
-- `CP.DefinesAt`, `CP.envOneAt`, `CP.satGraphAt`) and the per-conjunct
-- sub-readings (`CP.codeAt-in/out`, `CP.graphAt-holds/unique`,
-- `CP.DefinesAt-in/out/both`, `CP.envOneAt-in/out`, `CP.keyS`, `CP.Sat`,
-- `CP.defSet-Sat`, `CP.keyBridge`) are imported from the retiring cone as the
-- counted frame; the assembly theorems below are re-derived in this fresh
-- module, which is the measurement.

module ProbeT132 {ℓ : Level} (lem : LEM (ℓ-suc ℓ)) where

import L.Coding.Powerset {ℓ} lem as CP
import L.Coding.Sat {ℓ} lem as SAT
import L.Coding.Bridge {ℓ} lem as BR
import L.Coding.Uniform {ℓ} lem as UN
import L.Coding.CodeSet {ℓ} lem as CS
import L.Coding.Graph {ℓ} lem as GR

open import FOL.ZFStructure using ( module hPropStructure )
open import FOL.Syntax using ( Formula; var; _∈̇_; _∧̇_; ∃̇_ )
open import FOL.Manipulation.Relabelling using ( mapFo )
import FOL.Absoluteness
open import V.Hierarchy {ℓ} using ( 𝒮ᵥ )
open import L.Constructible {ℓ}
  using ( 𝒮ʟ; isL; isL-trans; 𝒟ₒ; 𝒟ₒ-intro; 𝒟ₒ-inv )
open import L.Definability {ℓ} using ( module DefOf )
open import L.Coding.Model {ℓ}
  using ( extAt; extAt-out; extAt-in; extAt-in-both )
open import L.Coding.Environment {ℓ} using ( env )

open import Cubical.Data.FinData using ( Fin; zero; suc )
open import Cubical.Data.Vec using ( lookup )
open import Cubical.Foundations.HLevels using ( isProp× )
open import Cubical.Functions.Logic using ( ⇔toPath )
import Cubical.HITs.PropositionalTruncation as PT
open PT using ( ∥_∥₁; ∣_∣₁; squash₁ )
open import Cubical.HITs.CumulativeHierarchy.Base using ( V; _∈_ )
open import Cubical.HITs.CumulativeHierarchy.Properties
  using ( ⟪_⟫; ⟪_⟫↪; ∈∈ₛ; ∈ₛ⟪_⟫↪_; ∈-asFiber; _⊆_; extensionality )

open TruthAlgebra (hPropAlgebra (ℓ-suc ℓ))
open hPropStructure 𝒮ʟ

module AbsL = FOL.Absoluteness.Single 𝒮ᵥ isL isL-trans
open AbsL renaming ( _⊨ᵐ_ to _⊨_ )

private
  sh3 : ∀ {n} → Fin n → Fin (suc (suc (suc n)))
  sh3 i = suc (suc (suc i))

-- The one arm, in both directions, against `defSet`/`𝒟ₒ`.
module _ (A : S) where
  module DA = DefOf (fst A)

  envOne : V ℓ → V ℓ
  envOne y = env {1} (λ _ → y)

  toS : Formula ⟪ fst A ⟫ 1 → Formula S 1
  toS ψ = mapFo (BR.asConst A) ψ

  ιA : ⟪ fst A ⟫ → V ℓ
  ιA = ⟪ fst A ⟫↪

  ιA∈ : (m : ⟪ fst A ⟫) → ⟨ ιA m ∈ fst A ⟩
  ιA∈ m = ∈∈ₛ {a = ιA m} {b = fst A} .snd (∈ₛ⟪ fst A ⟫↪ m)

  Fibre : Formula ⟪ fst A ⟫ 1 → V ℓ → Type (ℓ-suc ℓ)
  Fibre ψ y = Σ[ p ∈ Σ[ m ∈ ⟪ fst A ⟫ ] ⟨ DA.smallSat ψ m ⟩ ]
                (ιA (p .fst) ≡ y)

  inSat : (ψ : Formula ⟪ fst A ⟫ 1) (m : ⟪ fst A ⟫)
        → ⟨ ιA m ∈ DA.defSet ψ ⟩
        → ⟨ envOne (ιA m) ∈ fst (SAT.Sat A (toS ψ)) ⟩
  inSat ψ m h = subst ⟨_⟩ (BR.defSet-Sat A ψ m) h

  outSat : (ψ : Formula ⟪ fst A ⟫ 1) (m : ⟪ fst A ⟫)
         → ⟨ envOne (ιA m) ∈ fst (SAT.Sat A (toS ψ)) ⟩
         → ⟨ ιA m ∈ DA.defSet ψ ⟩
  outSat ψ m h = subst ⟨_⟩ (sym (BR.defSet-Sat A ψ m)) h

  -- In direction, at the description level: a `defSet ψ`-named member z makes
  -- the object description hold, with the value taken to be the internalized
  -- satisfaction at the code.
  fill : ∀ {n} (w : Fin n) (γ : S ^ n) → fst (lookup w γ) ≡ fst A
       → (z : S) (ψ : Formula ⟪ fst A ⟫ 1) → DA.defSet ψ ≡ fst z
       → ⟨ (SAT.Sat A (toS ψ) ∷ CS.keyS A ψ ∷ z ∷ γ) ⊨ CP.DefBody w ⟩
  fill {n} w γ qw z ψ qz = hcode , (hgraph , hdef)
    where
    δ : S ^ (suc (suc (suc n)))
    δ = SAT.Sat A (toS ψ) ∷ CS.keyS A ψ ∷ z ∷ γ

    hcode : ⟨ δ ⊨ CP.isCodeAt (suc zero) (sh3 w) ⟩
    hcode = CP.codeAt-in A (suc zero) (sh3 w) δ qw ψ refl

    hgraph : ⟨ δ ⊨ GR.satGraphAt (sh3 w) (suc zero) zero ⟩
    hgraph = CP.graphAt-holds A (toS ψ) (sh3 w) (suc zero) zero δ qw
               (UN.keyBridge A ψ) refl

    Holds : S → Type (ℓ-suc ℓ)
    Holds y = ⟨ fst y ∈ fst (lookup w γ) ⟩
              × ⟨ envOne (fst y) ∈ fst (SAT.Sat A (toS ψ)) ⟩

    into : (y : S) → ⟨ fst y ∈ fst z ⟩ → Holds y
    into y y∈ = PT.rec
      (isProp× (snd (fst y ∈ fst (lookup w γ)))
               (snd (envOne (fst y) ∈ fst (SAT.Sat A (toS ψ)))))
      step (subst (λ X → ⟨ fst y ∈ X ⟩) (sym qz) y∈)
      where
      step : Fibre ψ (fst y) → Holds y
      step ((m , hm) , qm) =
          subst (λ u → ⟨ u ∈ fst (lookup w γ) ⟩) qm
            (subst (λ X → ⟨ ιA m ∈ X ⟩) (sym qw) (ιA∈ m))
        , subst (λ u → ⟨ envOne u ∈ fst (SAT.Sat A (toS ψ)) ⟩) qm
            (inSat ψ m ∣ (m , hm) , refl ∣₁)

    back : (y : S) → Holds y → ⟨ fst y ∈ fst z ⟩
    back y (yw , ys) = subst (λ X → ⟨ fst y ∈ X ⟩) qz
      (subst (λ u → ⟨ u ∈ DA.defSet ψ ⟩) (fib .snd)
        (outSat ψ (fib .fst)
          (subst (λ u → ⟨ envOne u ∈ fst (SAT.Sat A (toS ψ)) ⟩)
            (sym (fib .snd)) ys)))
      where
      fib : Σ[ m ∈ ⟪ fst A ⟫ ] (ιA m ≡ fst y)
      fib = ∈-asFiber {a = fst y} {b = fst A}
        (subst (λ X → ⟨ fst y ∈ X ⟩) qw yw)

    hdef : ⟨ δ ⊨ CP.DefinesAt (suc (suc zero)) (sh3 w) zero ⟩
    hdef = CP.DefinesAt-both (suc (suc zero)) (sh3 w) zero δ into back

  -- Out direction, at the description level: satisfaction of the description
  -- names a formula ψ and the extensional identity `defSet ψ ≡ z`.
  read : ∀ {n} (w : Fin n) (γ : S ^ n) → fst (lookup w γ) ≡ fst A
       → (z c v : S) → ⟨ (v ∷ c ∷ z ∷ γ) ⊨ CP.DefBody w ⟩
       → ∥ (Σ[ ψ ∈ Formula ⟪ fst A ⟫ 1 ] (DA.defSet ψ ≡ fst z)) ∥₁
  read {n} w γ qw z c v (hcode , (hgraph , hdef)) =
    PT.rec squash₁ step (CP.codeAt-out A (suc zero) (sh3 w) δ qw hcode)
    where
    δ : S ^ (suc (suc (suc n)))
    δ = v ∷ c ∷ z ∷ γ

    step : Σ[ ψ ∈ Formula ⟪ fst A ⟫ 1 ] (fst c ≡ fst (CS.keyS A ψ))
         → ∥ (Σ[ ψ ∈ Formula ⟪ fst A ⟫ 1 ] (DA.defSet ψ ≡ fst z)) ∥₁
    step (ψ , qc) = ∣ ψ , extensionality (DA.defSet ψ) (fst z) (sub₁ , sub₂) ∣₁
      where
      qv : fst v ≡ fst (SAT.Sat A (toS ψ))
      qv = CP.graphAt-unique A (toS ψ) (sh3 w) (suc zero) zero δ qw
             (qc ∙ UN.keyBridge A ψ) hgraph

      sub₁ : ⟨ DA.defSet ψ ⊆ fst z ⟩
      sub₁ y y∈ₛ = ∈∈ₛ {a = y} {b = fst z} .fst
        (PT.rec (snd (y ∈ fst z)) place
          (∈∈ₛ {a = y} {b = DA.defSet ψ} .snd y∈ₛ))
        where
        place : Fibre ψ y → ⟨ y ∈ fst z ⟩
        place ((m , hm) , qm) =
          CP.DefinesAt-in (suc (suc zero)) (sh3 w) zero δ hdef
            (y , isL-trans {x = fst A} {y = y}
                   (subst (λ u → ⟨ u ∈ fst A ⟩) qm (ιA∈ m)) (snd A))
            ( subst (λ X → ⟨ y ∈ X ⟩) (sym qw)
                (subst (λ u → ⟨ u ∈ fst A ⟩) qm (ιA∈ m))
            , subst (λ X → ⟨ envOne y ∈ X ⟩) (sym qv)
                (subst (λ u → ⟨ envOne u ∈ fst (SAT.Sat A (toS ψ)) ⟩) qm
                  (inSat ψ m ∣ (m , hm) , refl ∣₁)) )

      sub₂ : ⟨ fst z ⊆ DA.defSet ψ ⟩
      sub₂ y y∈ₛ = ∈∈ₛ {a = y} {b = DA.defSet ψ} .fst
        (subst (λ u → ⟨ u ∈ DA.defSet ψ ⟩) (fib .snd)
          (outSat ψ (fib .fst)
            (subst (λ u → ⟨ envOne u ∈ fst (SAT.Sat A (toS ψ)) ⟩) (sym (fib .snd))
              (subst (λ X → ⟨ envOne y ∈ X ⟩) qv (cond .snd)))))
        where
        y∈ : ⟨ y ∈ fst z ⟩
        y∈ = ∈∈ₛ {a = y} {b = fst z} .snd y∈ₛ

        yS : S
        yS = y , isL-trans {x = fst z} {y = y} y∈ (snd z)

        cond : ⟨ y ∈ fst (lookup w γ) ⟩ × ⟨ envOne y ∈ fst v ⟩
        cond = CP.DefinesAt-out (suc (suc zero)) (sh3 w) zero δ hdef yS y∈

        fib : Σ[ m ∈ ⟪ fst A ⟫ ] (ιA m ≡ y)
        fib = ∈-asFiber {a = y} {b = fst A}
          (subst (λ X → ⟨ y ∈ X ⟩) qw (cond .fst))

  describe : ∀ {n} (w : Fin n) (γ : S ^ n) → fst (lookup w γ) ≡ fst A
           → (z : S) → ⟨ (z ∷ γ) ⊨ ∃̇ (∃̇ (CP.DefBody w)) ⟩
           → ∥ (Σ[ ψ ∈ Formula ⟪ fst A ⟫ 1 ] (DA.defSet ψ ≡ fst z)) ∥₁
  describe w γ qw z = PT.rec squash₁ viaCode
    where
    Target : Type (ℓ-suc ℓ)
    Target = ∥ (Σ[ ψ ∈ Formula ⟪ fst A ⟫ 1 ] (DA.defSet ψ ≡ fst z)) ∥₁

    viaValue : (c : S)
             → Σ[ v ∈ S ] ⟨ (v ∷ c ∷ z ∷ γ) ⊨ CP.DefBody w ⟩ → Target
    viaValue c (v , hv) = read w γ qw z c v hv

    viaCode : Σ[ c ∈ S ] ⟨ (c ∷ z ∷ γ) ⊨ ∃̇ (CP.DefBody w) ⟩ → Target
    viaCode (c , hc) = PT.rec squash₁ (viaValue c) hc

  assemble : ∀ {n} (w : Fin n) (γ : S ^ n) → fst (lookup w γ) ≡ fst A
           → (z : S)
           → ∥ (Σ[ ψ ∈ Formula ⟪ fst A ⟫ 1 ] (DA.defSet ψ ≡ fst z)) ∥₁
           → ⟨ (z ∷ γ) ⊨ ∃̇ (∃̇ (CP.DefBody w)) ⟩
  assemble w γ qw z = PT.rec (snd ((z ∷ γ) ⊨ ∃̇ (∃̇ (CP.DefBody w)))) step
    where
    step : Σ[ ψ ∈ Formula ⟪ fst A ⟫ 1 ] (DA.defSet ψ ≡ fst z)
         → ⟨ (z ∷ γ) ⊨ ∃̇ (∃̇ (CP.DefBody w)) ⟩
    step (ψ , qψ) = ∣ CS.keyS A ψ , ∣ SAT.Sat A (toS ψ) , fill w γ qw z ψ qψ ∣₁ ∣₁

  -- The arm's carrier-level closure, both directions, against `𝒟ₒ` (whose
  -- membership is definitionally the `defSet` recognition).
  DefAt-in : ∀ {n} (u w : Fin n) (γ : S ^ n)
           → fst (lookup w γ) ≡ fst A
           → fst (lookup u γ) ≡ 𝒟ₒ (fst A)
           → ⟨ γ ⊨ CP.DefAt u w ⟩
  DefAt-in {n} u w γ qw qu = extAt-in-both u Φ γ f g
    where
    Φ : Formula S (suc n)
    Φ = ∃̇ (∃̇ (CP.DefBody w))

    f : (z : S) → ⟨ fst z ∈ fst (lookup u γ) ⟩ → ⟨ (z ∷ γ) ⊨ Φ ⟩
    f z z∈ = assemble w γ qw z
      (𝒟ₒ-inv (fst A) (fst z) (subst (λ X → ⟨ fst z ∈ X ⟩) qu z∈))

    g : (z : S) → ⟨ (z ∷ γ) ⊨ Φ ⟩ → ⟨ fst z ∈ fst (lookup u γ) ⟩
    g z hz = subst (λ X → ⟨ fst z ∈ X ⟩) (sym qu)
      (𝒟ₒ-intro (fst A) (fst z) (describe w γ qw z hz))

  DefAt-out : ∀ {n} (u w : Fin n) (γ : S ^ n) → CP.DefOK A
            → fst (lookup w γ) ≡ fst A
            → ⟨ γ ⊨ CP.DefAt u w ⟩
            → fst (lookup u γ) ≡ 𝒟ₒ (fst A)
  DefAt-out {n} u w γ ok qw h =
    extensionality (fst (lookup u γ)) (𝒟ₒ (fst A)) (sub₁ , sub₂)
    where
    Φ : Formula S (suc n)
    Φ = ∃̇ (∃̇ (CP.DefBody w))

    sub₁ : ⟨ fst (lookup u γ) ⊆ 𝒟ₒ (fst A) ⟩
    sub₁ y y∈ₛ = ∈∈ₛ {a = y} {b = 𝒟ₒ (fst A)} .fst
      (𝒟ₒ-intro (fst A) y (describe w γ qw yS (extAt-out u Φ γ h yS y∈)))
      where
      y∈ : ⟨ y ∈ fst (lookup u γ) ⟩
      y∈ = ∈∈ₛ {a = y} {b = fst (lookup u γ)} .snd y∈ₛ

      yS : S
      yS = y , isL-trans {x = fst (lookup u γ)} {y = y} y∈ (snd (lookup u γ))

    sub₂ : ⟨ 𝒟ₒ (fst A) ⊆ fst (lookup u γ) ⟩
    sub₂ y y∈ₛ = ∈∈ₛ {a = y} {b = fst (lookup u γ)} .fst
      (extAt-in u Φ γ h yS
        (assemble w γ qw yS (𝒟ₒ-inv (fst A) y y∈)))
      where
      y∈ : ⟨ y ∈ 𝒟ₒ (fst A) ⟩
      y∈ = ∈∈ₛ {a = y} {b = 𝒟ₒ (fst A)} .snd y∈ₛ

      yS : S
      yS = y , ok y y∈
