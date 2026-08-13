{-# OPTIONS --cubical --safe --guardedness #-}

-- [LJ-1.120] probe A: generic environment-set over an arbitrary arity.
-- The construction is the missing half of someEnv. The machine builds
-- over a numeral only (src/L/Coding/EnvSet.lagda.md:183). Here the
-- arity is an arbitrary S, and the ambient values are an arbitrary S.
-- The set is separated from the power set of a stage that bounds every
-- pair of an arity member and an ambient member. No master is edited.

open import Base.Prelude
open import Base.Truth
open import Base.Classical using ( LEM )

module ProbeLJ1120A {ℓ : Level} (lem : LEM (ℓ-suc ℓ)) where

open import FOL.ZFStructure using ( module hPropStructure )
open import FOL.Syntax using ( Formula; var; con; _≐_; _∧̇_; ∃̇_ )
import FOL.Absoluteness
import FOL.ZFModel
open import V.Hierarchy {ℓ} using ( 𝒮ᵥ )
open import V.Coding {ℓ} using ( pr )
open import L.Constructible {ℓ}
  using ( 𝒮ʟ; isL; isL-trans; IsOrd; Lset; Lset-mono )
open import L.Ordinal {ℓ} using ( boundingOrd )
open import L.Stage {ℓ} lem using ( stage; stage-ord; stage-mem )
open import L.Axioms.Basic {ℓ} using ( LsetS )
open import L.Axioms.Full {ℓ} lem using ( hasSeparationL )
open import L.Axioms.Power {ℓ} lem using ( hasPowerL )
open import L.Coding.Model {ℓ}
  using ( prʟ; prʟ-fst; envSetAt; envOverAt
        ; envOverAt-transport; envOver-pairs; extAt-in-both
        ; pairsIn-out )

open import Cubical.HITs.CumulativeHierarchy.Base using ( V; _∈_ )
open import Cubical.HITs.CumulativeHierarchy.Properties
  using ( ∈∈ₛ; ∈-asFiber; ⟪_⟫; ⟪_⟫↪; ∈ₛ⟪_⟫↪_ )
import Cubical.HITs.PropositionalTruncation as PT
open PT using ( ∣_∣₁; ∥_∥₁; squash₁ )

open TruthAlgebra (hPropAlgebra (ℓ-suc ℓ))
open hPropStructure 𝒮ʟ

module ModelL = FOL.ZFModel 𝒮ʟ
open ModelL using ( _⊆ˢ_ )

module AbsL = FOL.Absoluteness.Single 𝒮ᵥ isL isL-trans
open AbsL renaming ( _⊨ᵐ_ to _⊨_ )

private
  stageFor : (X : Type ℓ) (f : X → S)
           → Σ[ β ∈ V ℓ ] (IsOrd β × ((x : X) → ⟨ fst (f x) ∈ Lset β ⟩))
  stageFor X f = β , (oβ , mem)
    where
    b = boundingOrd X (λ x → stage (fst (f x)) (f x .snd))
          (λ x → stage-ord (fst (f x)) (f x .snd))
    β = b .fst
    oβ : IsOrd β
    oβ = b .snd .fst
    mem : (x : X) → ⟨ fst (f x) ∈ Lset β ⟩
    mem x = Lset-mono {α = β} {β = stage (fst (f x)) (f x .snd)}
              (b .snd .snd x)
              (stage-mem (fst (f x)) (f x .snd))

module Generic (B ar : S) where
  private
    ixA : ⟪ fst ar ⟫ → S
    ixA m = ⟪ fst ar ⟫↪ m
          , isL-trans {x = fst ar} {y = ⟪ fst ar ⟫↪ m}
              (∈∈ₛ {a = ⟪ fst ar ⟫↪ m} {b = fst ar} .snd
                (∈ₛ⟪ fst ar ⟫↪ m))
              (snd ar)

    ixB : ⟪ fst B ⟫ → S
    ixB m = ⟪ fst B ⟫↪ m
          , isL-trans {x = fst B} {y = ⟪ fst B ⟫↪ m}
              (∈∈ₛ {a = ⟪ fst B ⟫↪ m} {b = fst B} .snd
                (∈ₛ⟪ fst B ⟫↪ m))
              (snd B)

    PairX : Type ℓ
    PairX = ⟪ fst ar ⟫ × ⟪ fst B ⟫

    pairS : PairX → S
    pairS p = prʟ (ixA (p .fst)) (ixB (p .snd))

    pairBound : Σ[ β ∈ V ℓ ] (IsOrd β ×
      ((p : PairX) → ⟨ fst (pairS p) ∈ Lset β ⟩))
    pairBound = stageFor PairX pairS

  amb : S
  amb = LsetS (pairBound .fst) (pairBound .snd .fst)

  pair∈amb : (u v : S) → ⟨ fst u ∈ fst ar ⟩ → ⟨ fst v ∈ fst B ⟩
           → ⟨ pr (fst u) (fst v) ∈ fst amb ⟩
  pair∈amb u v u∈ v∈ =
    subst (λ w → ⟨ w ∈ fst amb ⟩) (sym pairEq) (pairBound .snd .snd (m , n))
    where
    m : ⟪ fst ar ⟫
    m = ∈-asFiber {a = fst u} {b = fst ar} u∈ .fst
    em : ⟪ fst ar ⟫↪ m ≡ fst u
    em = ∈-asFiber {a = fst u} {b = fst ar} u∈ .snd
    n : ⟪ fst B ⟫
    n = ∈-asFiber {a = fst v} {b = fst B} v∈ .fst
    en : ⟪ fst B ⟫↪ n ≡ fst v
    en = ∈-asFiber {a = fst v} {b = fst B} v∈ .snd
    pairEq : pr (fst u) (fst v) ≡ fst (pairS (m , n))
    pairEq = cong₂ pr (sym em) (sym en) ∙ sym (prʟ-fst (ixA m) (ixB n))

  powamb : S
  powamb = hasPowerL amb .fst .fst

  powamb-spec : (x : S) → (x ∈ˢ powamb) ≡ (x ⊆ˢ amb)
  powamb-spec = hasPowerL amb .fst .snd

  powamb-in : (x : S) → ⟨ x ⊆ˢ amb ⟩ → ⟨ x ∈ˢ powamb ⟩
  powamb-in x h = subst ⟨_⟩ (sym (powamb-spec x)) h

  envFo : Formula S 1
  envFo = ∃̇ (∃̇ ( (var (suc zero) ≐ con ar)
                ∧̇ ((var zero ≐ con B)
                ∧̇ envOverAt (suc (suc zero)) (suc zero) zero) ))

  envSetGen : S
  envSetGen = hasSeparationL powamb envFo .fst .fst

  envSetGen-spec : (x : S) → (x ∈ˢ envSetGen)
                 ≡ ((x ∈ˢ powamb) ⊓ ((x ∷ []) ⊨ envFo))
  envSetGen-spec = hasSeparationL powamb envFo .fst .snd

  envSetGen-in : (x : S) → ⟨ x ∈ˢ powamb ⟩ → ⟨ (x ∷ []) ⊨ envFo ⟩
               → ⟨ x ∈ˢ envSetGen ⟩
  envSetGen-in x hx hφ =
    subst ⟨_⟩ (sym (envSetGen-spec x)) (hx , hφ)

  envSetGen-out : (x : S) → ⟨ x ∈ˢ envSetGen ⟩
                → ⟨ (x ∷ []) ⊨ envFo ⟩
  envSetGen-out x hx = (subst ⟨_⟩ (envSetGen-spec x) hx) .snd

  -- An environment is a member of the power set: every member of it
  -- is one of the bounded pairs, hence lies in amb.
  envSubset : {k : ℕ} (γ : S ^ k) (di bi : Fin k)
            → fst (lookup di γ) ≡ fst ar
            → fst (lookup bi γ) ≡ fst B
            → (z : S)
            → ⟨ (z ∷ γ) ⊨ envOverAt zero (suc di) (suc bi) ⟩
            → ⟨ z ⊆ˢ amb ⟩
  envSubset γ di bi qd qb z h w w∈ =
    PT.rec (snd (w ∈ˢ amb))
      (λ { (u , (v , (u∈ , (v∈ , eq)))) →
        subst (λ s → ⟨ s ∈ fst amb ⟩) (sym eq)
          (pair∈amb u v
            (subst (λ t → ⟨ fst u ∈ t ⟩) qd u∈)
            (subst (λ t → ⟨ fst v ∈ t ⟩) qb v∈)) })
      (pairsIn-out zero (suc di) (suc bi) (z ∷ γ)
        (envOver-pairs zero (suc di) (suc bi) (z ∷ γ) h) w w∈)

  -- The object-level description, read at a one-slot frame.
  foSat : {k : ℕ} (γ : S ^ k) (di bi : Fin k)
        → fst (lookup di γ) ≡ fst ar
        → fst (lookup bi γ) ≡ fst B
        → (z : S)
        → ⟨ (z ∷ []) ⊨ envFo ⟩
        → ⟨ (z ∷ γ) ⊨ envOverAt zero (suc di) (suc bi) ⟩
  foSat γ di bi qd qb z h =
    PT.rec (snd ((z ∷ γ) ⊨ envOverAt zero (suc di) (suc bi)))
      (λ { (d , hd) → PT.rec (snd ((z ∷ γ) ⊨ envOverAt zero (suc di) (suc bi)))
        (λ { (b , (deq , (beq , ov))) →
          envOverAt-transport (b ∷ d ∷ z ∷ []) (z ∷ γ)
            (suc (suc zero)) (suc zero) zero zero (suc di) (suc bi)
            refl (deq ∙ sym qd) (beq ∙ sym qb) ov })
        hd })
      h

  backToFo : {k : ℕ} (γ : S ^ k) (di bi : Fin k)
           → fst (lookup di γ) ≡ fst ar
           → fst (lookup bi γ) ≡ fst B
           → (z : S)
           → ⟨ (z ∷ γ) ⊨ envOverAt zero (suc di) (suc bi) ⟩
           → ⟨ (z ∷ []) ⊨ envFo ⟩
  backToFo γ di bi qd qb z h =
    ∣ ar , ∣ B ,
      ( refl
      , ( refl
        , envOverAt-transport (z ∷ γ) (B ∷ ar ∷ z ∷ [])
            zero (suc di) (suc bi) (suc (suc zero)) (suc zero) zero
            refl qd qb h ) ) ∣₁ ∣₁

  module Holds {k : ℕ} (γ : S ^ k) (Ei di bi : Fin k)
    (qE : fst (lookup Ei γ) ≡ fst envSetGen)
    (qd : fst (lookup di γ) ≡ fst ar)
    (qb : fst (lookup bi γ) ≡ fst B) where

    fwd : (z : S) → ⟨ fst z ∈ fst (lookup Ei γ) ⟩
        → ⟨ (z ∷ γ) ⊨ envOverAt zero (suc di) (suc bi) ⟩
    fwd z hz =
      foSat γ di bi qd qb z
        (envSetGen-out z (subst (λ w → ⟨ fst z ∈ w ⟩) qE hz))

    bwd : (z : S) → ⟨ (z ∷ γ) ⊨ envOverAt zero (suc di) (suc bi) ⟩
        → ⟨ fst z ∈ fst (lookup Ei γ) ⟩
    bwd z h =
      subst (λ w → ⟨ fst z ∈ w ⟩) (sym qE)
        (envSetGen-in z
          (powamb-in z (envSubset γ di bi qd qb z h))
          (backToFo γ di bi qd qb z h))

    holds : ⟨ γ ⊨ envSetAt Ei di bi ⟩
    holds = extAt-in-both Ei (envOverAt zero (suc di) (suc bi)) γ fwd bwd
