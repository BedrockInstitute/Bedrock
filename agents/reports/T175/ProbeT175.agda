{-# OPTIONS --cubical --safe --guardedness #-}

------------------------------------------------------------------------
-- [L3.32-T175] D22 gate: one arm's defSet equation from StepGraph's
-- memOf decodes (find F2).  Untracked probe, never committed (D-1).
-- Protocol: GHCRTS=-M8g, one Agda process, stop-line 150 non-blank
-- lines, no postulate, no hole, no TERMINATING.  The pin frame is
-- generic over Op16; the measured arm is F1 (op1).  Report:
-- _build/l3.32-t175-report.md (written incrementally, C-22).
------------------------------------------------------------------------

open import Base.Prelude
open import Base.Truth
open import Base.Classical using ( LEM )
open import Cubical.HITs.CumulativeHierarchy.Base using ( V; setIsSet )

module ProbeT175 {ℓ : Level} (lem : LEM (ℓ-suc ℓ)) (A : V ℓ) where

open import FOL.Syntax using
  ( Formula; var; con; _∈̇_; _≐_; _∧̇_; _∨̇_; ¬̇_; ∃̇_ )
open import FOL.ZFStructure using ( module hPropStructure )
open import V.Hierarchy {ℓ} using ( 𝒮ᵥ )
open import L.Constructible {ℓ} using ( isTransV )
open import L.Rud.StepGraph {ℓ} lem A using ( module Desc; module Layer )
open import L.Rud.Step {ℓ} lem A using ( Op16; op1; Fof; Fof-f1 )
open import L.Rud.Ops {ℓ} using ( F1; F1-spec )
open import Cubical.Data.FinData.Base using ( Fin; zero; suc )
open import Cubical.Functions.Logic using ( ∃[]-syntax )
import Cubical.HITs.PropositionalTruncation as PT
open PT using ( ∣_∣₁; ∥_∥₁ )
open import Cubical.HITs.CumulativeHierarchy.Properties
  using ( _∈ₛ_; ∈∈ₛ; ⟪_⟫; ⟪_⟫↪; ∈-asFiber )
open import Cubical.HITs.CumulativeHierarchy.Constructions
  using ( ∅ )

open TruthAlgebra (hPropAlgebra (ℓ-suc ℓ))
open hPropStructure 𝒮ᵥ

private
  f0 : {n : ℕ} → Fin (suc n)
  f0 = zero
  f1 : {n : ℕ} → Fin (suc (suc n))
  f1 = suc f0
  f2 : {n : ℕ} → Fin (suc (suc (suc n)))
  f2 = suc f1
  f3 : {n : ℕ} → Fin (suc (suc (suc (suc n))))
  f3 = suc f2

-- The pin frame, module-parameterized (P-h).  memOf i reads the
-- environment (z, b, a, y): the member at f0, the second argument at
-- f1, the first argument at f2, the value slot at f3.  Three
-- existentials bind the member and the two argument slots; the pins
-- force the argument slots to the constants and re-pin the member
-- slot to the free tail variable.  The frame is generic in i; the
-- arguments are module parameters, so the walk stays abstract.
module PinFrame (C : S) (Ctr : isTransV C)
  (mA : ⟪ C ⟫) (qA : ⟪ C ⟫↪ mA ≡ A) (∅∈C : ⟨ ∅ ∈ˢ C ⟩)
  (a b : S) (a∈ : ⟨ a ∈ˢ C ⟩) (b∈ : ⟨ b ∈ˢ C ⟩) where

  module L = Layer C Ctr mA qA ∅∈C
  module D = Desc C Ctr
  open L public

  mₐ : ⟪ C ⟫
  mₐ = ∈-asFiber {a = a} {b = C} a∈ .fst
  qₐ : ⟪ C ⟫↪ mₐ ≡ a
  qₐ = ∈-asFiber {a = a} {b = C} a∈ .snd
  m_b : ⟪ C ⟫
  m_b = ∈-asFiber {a = b} {b = C} b∈ .fst
  q_b : ⟪ C ⟫↪ m_b ≡ b
  q_b = ∈-asFiber {a = b} {b = C} b∈ .snd

  body : (i : Op16) → Formula ⟪ C ⟫ 4
  body i = (var f0 ≐ var f3) ∧̇
    ((var f1 ≐ con m_b) ∧̇ ((var f2 ≐ con mₐ) ∧̇ L.memOf i))

  pinned : (i : Op16) → Formula ⟪ C ⟫ 1
  pinned i = ∃̇ (∃̇ (∃̇ body i))

  pinned-out : (i : Op16) (v : S) (v∈ : ⟨ v ∈ˢ C ⟩)
             → ⟨ (PK.pt v v∈ ∷ []) ⊨ᵐ pinned i ⟩ → ⟨ v ∈ˢ Fof i a b ⟩
  pinned-out i v v∈ h = PT.rec (snd (v ∈ˢ Fof i a b)) k2 h
    where
    k2 : Σ[ x₂ ∈ SM ] ⟨ (x₂ ∷ PK.pt v v∈ ∷ []) ⊨ᵐ (∃̇ (∃̇ body i)) ⟩
       → ⟨ v ∈ˢ Fof i a b ⟩
    k2 (x₂ , h₂) = PT.rec (snd (v ∈ˢ Fof i a b)) k1 h₂
      where
      k1 : Σ[ x₁ ∈ SM ] ⟨ (x₁ ∷ x₂ ∷ PK.pt v v∈ ∷ []) ⊨ᵐ (∃̇ body i) ⟩
         → ⟨ v ∈ˢ Fof i a b ⟩
      k1 (x₁ , h₁) = PT.rec (snd (v ∈ˢ Fof i a b)) k0 h₁
        where
        k0 : Σ[ x₀ ∈ SM ] ⟨ (x₀ ∷ x₁ ∷ x₂ ∷ PK.pt v v∈ ∷ []) ⊨ᵐ body i ⟩
           → ⟨ v ∈ˢ Fof i a b ⟩
        k0 (x₀ , h₀) = subst (λ w → ⟨ w ∈ˢ Fof i a b ⟩) p0
          (subst (λ t → ⟨ fst x₀ ∈ˢ Fof i a t ⟩) (p1 ∙ q_b)
            (subst (λ t → ⟨ fst x₀ ∈ˢ Fof i t (fst x₁) ⟩) (p2 ∙ qₐ) z∈F))
          where
          p0 : fst x₀ ≡ v
          p0 = h₀ .fst
          p1 : fst x₁ ≡ ⟪ C ⟫↪ m_b
          p1 = h₀ .snd .fst
          p2 : fst x₂ ≡ ⟪ C ⟫↪ mₐ
          p2 = h₀ .snd .snd .fst
          ms : ⟨ (x₀ ∷ x₁ ∷ x₂ ∷ PK.pt v v∈ ∷ []) ⊨ᵐ L.memOf i ⟩
          ms = h₀ .snd .snd .snd
          z∈F : ⟨ fst x₀ ∈ˢ Fof i (fst x₂) (fst x₁) ⟩
          z∈F = L.memOut i (fst x₀) (fst x₁) (fst x₂) v
            (snd x₀) (snd x₁) (snd x₂) v∈ ms

  pinned-in : (i : Op16) (v : S) (v∈ : ⟨ v ∈ˢ C ⟩)
            → ⟨ v ∈ˢ Fof i a b ⟩ → ⟨ (PK.pt v v∈ ∷ []) ⊨ᵐ pinned i ⟩
  pinned-in i v v∈ h =
    ∣ PK.pt a a∈ , (∣ PK.pt b b∈ , (∣ PK.pt v v∈ , (pin₀ , (pin₁ , (pin₂ , ms))) ∣₁) ∣₁) ∣₁
    where
    pin₀ : ⟨ (PK.pt v v∈ ∷ PK.pt b b∈ ∷ PK.pt a a∈ ∷ PK.pt v v∈ ∷ [])
             ⊨ᵐ (var f0 ≐ var f3) ⟩
    pin₀ = refl
    pin₁ : ⟨ (PK.pt v v∈ ∷ PK.pt b b∈ ∷ PK.pt a a∈ ∷ PK.pt v v∈ ∷ [])
             ⊨ᵐ (var f1 ≐ con m_b) ⟩
    pin₁ = sym q_b
    pin₂ : ⟨ (PK.pt v v∈ ∷ PK.pt b b∈ ∷ PK.pt a a∈ ∷ PK.pt v v∈ ∷ [])
             ⊨ᵐ (var f2 ≐ con mₐ) ⟩
    pin₂ = sym qₐ
    ms : ⟨ (PK.pt v v∈ ∷ PK.pt b b∈ ∷ PK.pt a a∈ ∷ PK.pt v v∈ ∷ [])
           ⊨ᵐ L.memOf i ⟩
    ms = L.memIn i v b a v v∈ b∈ a∈ v∈ h

  -- The per-arm equation, in Bridge's Arm shape: the caller's subset
  -- certificate is the wsub input, so no per-op membership analysis
  -- enters the frame.  This is the whole Arms rebuild contract.
  Fof-defSet≡ : (i : Op16) (sub : (v : S) → ⟨ v ∈ˢ Fof i a b ⟩ → ⟨ v ∈ˢ C ⟩)
              → L.defSet (pinned i) ≡ Fof i a b
  Fof-defSet≡ i sub = D.described (pinned i) (Fof i a b) sub
    (λ v v∈ h → pinned-in i v v∈ h)
    (λ v v∈ h → pinned-out i v v∈ h)

  -- The F1 arm: mirror Describe.F1-defSet≡
  -- (src/L/Rud/Describe.lagda.md:461-524) from mem1 plus its decodes.
  F1-defSet≡ : L.defSet (pinned op1) ≡ F1 a b
  F1-defSet≡ = Fof-defSet≡ op1 wsub' ∙ Fof-f1 a b
    where
    wsub : (v : S) → ⟨ v ∈ˢ F1 a b ⟩ → ⟨ v ∈ˢ C ⟩
    wsub v h = Ctr {x = a} {y = v} v∈a a∈
      where
      v∈a : ⟨ v ∈ˢ a ⟩
      v∈a = F1-spec a b v .fst h .fst
    wsub' : (v : S) → ⟨ v ∈ˢ Fof op1 a b ⟩ → ⟨ v ∈ˢ C ⟩
    wsub' v h = wsub v (subst (λ w → ⟨ v ∈ˢ w ⟩) (Fof-f1 a b) h)
