{-# OPTIONS --cubical --safe --guardedness #-}

-- [LJ-1.493] Repair B at the real :3509 frame. W3 is
-- frame-reachable: c∈ from the back binder, shEq from shD.
-- Obligation someEnv-inlined opens SupplyEnv at KValue plus
-- ⟨ ω ∈ sucV gam ⟩ and does not call the someEnv field.
-- C stays a parameter. This is NOT Probe483's dummy-C pad.
--
-- ONE Agda process per run, GHCRTS="-A64m -I0 -M8g", the wide
-- caliber, set on the pane by the program and untouched here.
-- Nothing lands in src/. Do not import a probe.

open import Base.Prelude
open import Base.Truth
open import Base.Classical using ( LEM )

module LJ-1-493.Probe493 {ℓ : Level} (lem : LEM (ℓ-suc ℓ)) where

open import FOL.ZFStructure using ( module hPropStructure )
import FOL.Absoluteness
open import V.Hierarchy {ℓ} using ( 𝒮ᵥ )
open import V.Coding {ℓ} using ( pr )
open import L.Constructible {ℓ} using ( 𝒮ʟ; isL; isL-trans; IsOrd )
open import L.Coding.Model {ℓ}
  using ( arityTagPairAtL; arityTagPairAtL-adequate; appAt; subValAt )
open import L.Condensation {ℓ} lem
  using ( module KValue; envHypB2; module EnvSet; module GraphEntry )
open import L.Coding.EnvSupply {ℓ} lem using ( module SupplyEnv )
open import L.Coding.EnvSet {ℓ} lem using ( module Generic )
open import Cubical.Data.Nat using ( ℕ; _+_ )
open import Cubical.HITs.CumulativeHierarchy.Base using ( V; _∈_ )
open import Cubical.HITs.CumulativeHierarchy.Constructions
  using ( module InfinitySet; ∅ )
open InfinitySet {ℓ} using ( #_; sucV; ω )
import Cubical.HITs.PropositionalTruncation as PT
open PT using ( ∥_∥₁ )

open TruthAlgebra (hPropAlgebra (ℓ-suc ℓ))
open hPropStructure 𝒮ʟ
module AbsL = FOL.Absoluteness.Single 𝒮ᵥ isL isL-trans
open AbsL renaming ( _⊨ᵐ_ to _⊨_ )

-- =====================================================================
-- D-10.  codesK at PropAgree.back :3509.
--   Two inputs: c∈ from the :3505 lambda, shEq from :3506-3508.
--   Both are in scope at the landed proof.  Probe483 emptied C.
--   This frame leaves C a parameter.
-- =====================================================================

-- =====================================================================
-- W3.  frame-reachable, obligation omitted.
--   The pair (c∈, shEq) at the frame codesK is applied in.
--   arNum-at-frame is the fourth component.  No postulate.
-- =====================================================================

module W3 {m : ℕ} (C K : Fin m) (γ : S ^ m) (k : ℕ)
  (codesK : (c ar a b : S)
          → ⟨ fst c ∈ fst (lookup C γ) ⟩
          → fst c ≡ pr (fst ar) (pr (# k) (pr (fst a) (fst b)))
          → ⟨ fst ar ∈ fst (lookup K γ) ⟩
            × ⟨ fst a ∈ fst (lookup K γ) ⟩
            × ⟨ fst b ∈ fst (lookup K γ) ⟩
            × ∥ Σ[ n ∈ ℕ ] (fst ar ≡ # n) ∥₁)
  where

  frame-reachable :
      (c : S)
      (c∈ : ⟨ fst c ∈ fst (lookup C γ) ⟩)
      (ar a b yc : S)
      (shD : ⟨ (yc ∷ b ∷ a ∷ ar ∷ c ∷ γ) ⊨
                arityTagPairAtL
                  (suc (suc (suc (suc zero))))
                  (suc (suc (suc zero))) k
                  (suc (suc zero)) (suc zero) ⟩)
    → ⟨ fst c ∈ fst (lookup C γ) ⟩
      × (fst c ≡ pr (fst ar) (pr (# k) (pr (fst a) (fst b))))
  frame-reachable c c∈ ar a b yc shD =
    c∈ ,
    transport (cong fst (arityTagPairAtL-adequate
      (suc (suc (suc (suc zero)))) (suc (suc (suc zero))) k
      (suc (suc zero)) (suc zero) (yc ∷ b ∷ a ∷ ar ∷ c ∷ γ))) shD

  arNum-at-frame :
      (c : S)
      (c∈ : ⟨ fst c ∈ fst (lookup C γ) ⟩)
      (ar a b yc : S)
      (shD : ⟨ (yc ∷ b ∷ a ∷ ar ∷ c ∷ γ) ⊨
                arityTagPairAtL
                  (suc (suc (suc (suc zero))))
                  (suc (suc (suc zero))) k
                  (suc (suc zero)) (suc zero) ⟩)
    → ∥ Σ[ n ∈ ℕ ] (fst ar ≡ # n) ∥₁
  arNum-at-frame c c∈ ar a b yc shD =
    let (c∈' , shEq) = frame-reachable c c∈ ar a b yc shD
    in  codesK c ar a b c∈' shEq .snd .snd .snd

-- =====================================================================
-- THE OBLIGATION.  Open SupplyEnv at the KValue telescope plus the
-- gate EnvSupply.lagda.md:111.  Inline someEnv at the :3515 call.
-- Do not call the someEnv field.  B = iA, K = iK, γ = Kenv so the
-- memberships match Lset lam.  C and T stay parameters.
-- =====================================================================

module Frame
  (lam : V ℓ) (ordλ : IsOrd lam)
  (succλ : (d : V ℓ) → ⟨ d ∈ lam ⟩ → ⟨ sucV d ∈ lam ⟩)
  (∅∈λ : ⟨ ∅ ∈ lam ⟩)
  (gam : V ℓ) (ordγ : IsOrd gam) (γ∈λ : ⟨ gam ∈ lam ⟩)
  (ω∈γ : ⟨ ω ∈ sucV gam ⟩) where

  open KValue lam ordλ succλ ∅∈λ gam ordγ γ∈λ
  module SE = SupplyEnv lam ordλ succλ ∅∈λ gam ordγ γ∈λ ω∈γ

  module At (C T : Fin 14) (k : ℕ)
    (codesK : (c ar a b : S)
            → ⟨ fst c ∈ fst (lookup C Kenv) ⟩
            → fst c ≡ pr (fst ar) (pr (# k) (pr (fst a) (fst b)))
            → ⟨ fst ar ∈ fst (lookup iK Kenv) ⟩
              × ⟨ fst a ∈ fst (lookup iK Kenv) ⟩
              × ⟨ fst b ∈ fst (lookup iK Kenv) ⟩
              × ∥ Σ[ n ∈ ℕ ] (fst ar ≡ # n) ∥₁)
    (valK : (c ar a b yc : S)
          → ⟨ fst c ∈ fst (lookup C Kenv) ⟩
          → fst c ≡ pr (fst ar) (pr (# k) (pr (fst a) (fst b)))
          → ⟨ pr (fst c) (fst yc) ∈ fst (lookup T Kenv) ⟩
          → ⟨ fst yc ∈ fst (lookup iK Kenv) ⟩)
    (subK₁ : (x y yc b a ar c : S)
           → ⟨ (x ∷ y ∷ yc ∷ b ∷ a ∷ ar ∷ c ∷ Kenv) ⊨
                subValAt {7 + 14}
                  (suc (suc (suc (suc (suc (suc (suc T)))))))
                  (suc (suc (suc (suc (suc zero)))))
                  (suc (suc (suc (suc zero))))
                  (suc zero) ⟩
           → ⟨ fst y ∈ fst (lookup iK Kenv) ⟩)
    where

    module GE = GraphEntry {14} T Kenv

    someEnv-inlined :
        (c : S)
        (c∈ : ⟨ fst c ∈ fst (lookup C Kenv) ⟩)
        (ar a b yc : S)
        (shD : ⟨ (yc ∷ b ∷ a ∷ ar ∷ c ∷ Kenv) ⊨
                  arityTagPairAtL
                    (suc (suc (suc (suc zero))))
                    (suc (suc (suc zero))) k
                    (suc (suc zero)) (suc zero) ⟩)
        (hc : ⟨ (yc ∷ b ∷ a ∷ ar ∷ c ∷ Kenv) ⊨
                 appAt (suc (suc (suc (suc (suc T)))))
                       (suc (suc (suc (suc zero)))) zero ⟩)
        (ya yb : S)
        (hya : ⟨ (yb ∷ ya ∷ yc ∷ b ∷ a ∷ ar ∷ c ∷ Kenv) ⊨
                  subValAt {7 + 14}
                    (suc (suc (suc (suc (suc (suc (suc T)))))))
                    (suc (suc (suc (suc (suc zero)))))
                    (suc (suc (suc (suc zero))))
                    (suc zero) ⟩)
      → Σ S (λ E → ⟨ fst E ∈ fst (lookup iK Kenv) ⟩
          × ⟨ (E ∷ ya ∷ yc ∷ b ∷ a ∷ ar ∷ c ∷ Kenv) ⊨
                envHypB2 {14} iA iK ⟩)
    someEnv-inlined c c∈ ar a b yc shD hc ya yb hya =
      let shEq = transport (cong fst (arityTagPairAtL-adequate
                   (suc (suc (suc (suc zero)))) (suc (suc (suc zero))) k
                   (suc (suc zero)) (suc zero)
                   (yc ∷ b ∷ a ∷ ar ∷ c ∷ Kenv))) shD
          (arK , (_ , (_ , arNum))) = codesK c ar a b c∈ shEq
          ycK = valK c ar a b yc c∈ shEq (GE.bin c ar a b yc hc)
          yaK = subK₁ yb ya yc b a ar c hya
          (E , (EK , _)) = SE.someEnv ya yc b a ar c arNum yaK ycK arK
          module G = Generic SE.B₀ ar
          γ21 = E ∷ ya ∷ yc ∷ b ∷ a ∷ ar ∷ c ∷ Kenv
          iAr = suc (suc (suc (suc (suc zero))))
          iB  = suc (suc (suc (suc (suc (suc (suc iA))))))
          iK21 = suc (suc (suc (suc (suc (suc (suc iK))))))
          arityK21 : (N v : S)
                   → ⟨ fst v ∈ fst N ⟩
                   → ⟨ fst N ∈ fst (lookup iK21 γ21) ⟩
                   → ⟨ fst v ∈ fst (lookup iK21 γ21) ⟩
          arityK21 N v hv hNK = SE.transK v N hv hNK
          envInK21 z hz = SE.envInK-gen γ21 iAr iB refl arNum arK z hz
          module ES = EnvSet {7 + 14} zero iAr iB iK21 γ21
                        arityK21 EK arK envInK21
          module H = G.Holds {7 + 14} γ21 zero iAr iB refl refl refl
      in  E , (EK , ES.back H.holds)

someEnv-inlined = Frame.At.someEnv-inlined
