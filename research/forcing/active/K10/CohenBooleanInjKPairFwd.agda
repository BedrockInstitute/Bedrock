{-# OPTIONS --cubical --safe --guardedness #-}

open import Base.Prelude
open import Base.Truth
open import Base.Classical using ( LEM )
open import FOL.ZFStructure using ( ZFStructure )
import NameKernel
import OrdinaryProfile
import CardinalBridge
import Cubical.HITs.PropositionalTruncation as PT
import K4.Algebra
import K4.Implication
import K9.BooleanAtomic
import K9.NameGround
import K10.CohenBooleanInjSglCong

-- Forward half of PairφK at check names: membership in check(p) is below
-- the singleton-or-pair disjunct. Load is InjSglCong only.

module K10.CohenBooleanInjKPairFwd
  {ℓ} (𝒮 : ZFStructure (hPropAlgebra ℓ))
  (families : NameKernel.Families 𝒮)
  (accessible : NameKernel.Accessibility 𝒮)
  (images : NameKernel.MemberImage 𝒮)
  (pow : OrdinaryProfile.PowerSet 𝒮)
  (κ w : ZFStructure.S 𝒮)
  (lem : LEM ℓ)
  (paths : (x y : ZFStructure.S 𝒮)
         → (ZFStructure._≈ˢ_ 𝒮 x y) ≡ ((x ≡ y) , ZFStructure.isSetS 𝒮 x y))
  where

open import FOL.ZFStructure using ( module hPropStructure )
open import FOL.Syntax using ( var ; _∈̇_ ; _≐_ ; _∧̇_ ; _∨̇_ ; ∀̇∈ )
open import Cubical.Data.Sum using ( _⊎_ ; inl ; inr )
import CardinalBridge

open TruthAlgebra (hPropAlgebra ℓ)
open hPropStructure 𝒮

module NG = K9.NameGround 𝒮 families accessible images pow κ w
  using ( extensional ; ≈ˢ-paths )
module BAT = K9.BooleanAtomic 𝒮 families accessible images pow κ w lem
  using ( B ; module Atomic ; module IC ; module Laws )
open K4.Algebra 𝒮 using ( _≤ᴮ_ ; ≤ᴮ-refl ; ⊆ˢ-trans )
open K4.Algebra.Lattice BAT.IC.codedLattice
  using ( _⊓ᴮ_ ; _⊔ᴮ_ ; ⊤ᴮ ; ⊔-ub₁ ; ⊔-ub₂ ; ⊓-lb₁ ; ⊓-lb₂ ; ⊓-glb )
open K4.Implication 𝒮 NG.extensional NG.≈ˢ-paths BAT.B
  BAT.IC.codedLattice BAT.IC.codedComplement
  using ( ≤ᴮ-antisym ; ⊤-greatest ; _⇒ᴮ_ ; ⇒ᴮ-curry ; ⇒ᴮ-uncurry ; ⊓-⊤ )
module Cong = K10.CohenBooleanInjSglCong 𝒮 families accessible images pow κ w lem paths
module CB = CardinalBridge 𝒮
open BAT.Atomic using () renaming ( _∈ᴮ_ to mem ; _≈ᴮ_ to eq )

open Cong using ( sgl-from-eq ; pair-from-eq )
open Cong.Sgl using ( checkNm ; sglSrc ; pairSrc
                    ; sglMemberφ ; sglOnlyφ
                    ; pairLeftφ ; pairRightφ ; pairOnlyφ
                    ; eq-from-check )
open Cong.Sgl.BNG.Checked using ( check )
open Cong.Sgl.VS using ( Src ; Nameᴮ ; Envᴮ ; val
                       ; law-∈ ; law-≐ ; law-∧ ; law-∨
                       ; law-∀∈-lb ; law-∀∈-glb )

kpairSglφ : Src 4
kpairSglφ =
  (var (suc (suc zero)) ∈̇ var zero)
  ∧̇ (∀̇∈ (var zero) (var zero ≐ var (suc (suc (suc zero)))))

kpairPairφ : Src 4
kpairPairφ =
  (var (suc (suc zero)) ∈̇ var zero)
  ∧̇ ((var (suc (suc (suc zero))) ∈̇ var zero)
  ∧̇ (∀̇∈ (var zero)
       ((var zero ≐ var (suc (suc (suc zero))))
        ∨̇ (var zero ≐ var (suc (suc (suc (suc zero))))))))

kpairDisjφ : Src 4
kpairDisjφ = kpairSglφ ∨̇ kpairPairφ

env4 : Nameᴮ → S → S → S → Envᴮ 4
env4 σ p x y = σ ∷ checkNm p ∷ checkNm x ∷ checkNm y ∷ []

env2 : Nameᴮ → S → Envᴮ 2
env2 σ x = σ ∷ checkNm x ∷ []

env3 : Nameᴮ → S → S → Envᴮ 3
env3 σ x y = σ ∷ checkNm x ∷ checkNm y ∷ []

sgl-only-eq : (σ : Nameᴮ) (p x y : S)
  → val (∀̇∈ (var zero) (var zero ≐ var (suc (suc (suc zero))))) (env4 σ p x y)
    ≡ val sglOnlyφ (env2 σ x)
sgl-only-eq σ p x y = ≤ᴮ-antisym le ge
  where
  body4 = var zero ≐ var (suc (suc (suc zero)))
  body2 = var zero ≐ var (suc (suc zero))
  ν4 = env4 σ p x y
  ν2 = env2 σ x
  body4-eq : (ρ : Nameᴮ) → val body4 (ρ ∷ ν4) ≡ eq (fst ρ) (check x)
  body4-eq ρ = law-≐ zero (suc (suc (suc zero))) (ρ ∷ ν4)
  body2-eq : (ρ : Nameᴮ) → val body2 (ρ ∷ ν2) ≡ eq (fst ρ) (check x)
  body2-eq ρ = law-≐ zero (suc (suc zero)) (ρ ∷ ν2)
  le = law-∀∈-glb zero body2 ν2 (val (∀̇∈ (var zero) body4) ν4) λ ρ →
    subst (λ b → ⟨ val (∀̇∈ (var zero) body4) ν4
                  ≤ᴮ (mem (fst ρ) (fst σ) ⇒ᴮ b) ⟩)
      (body4-eq ρ ∙ sym (body2-eq ρ))
      (law-∀∈-lb zero body4 ν4 ρ)
  ge = law-∀∈-glb zero body4 ν4 (val sglOnlyφ ν2) λ ρ →
    subst (λ b → ⟨ val sglOnlyφ ν2
                  ≤ᴮ (mem (fst ρ) (fst σ) ⇒ᴮ b) ⟩)
      (body2-eq ρ ∙ sym (body4-eq ρ))
      (law-∀∈-lb zero body2 ν2 ρ)

sgl-match : (σ : Nameᴮ) (p x y : S)
  → val kpairSglφ (env4 σ p x y) ≡ val sglSrc (env2 σ x)
sgl-match σ p x y =
  law-∧ (var (suc (suc zero)) ∈̇ var zero)
    (∀̇∈ (var zero) (var zero ≐ var (suc (suc (suc zero))))) (env4 σ p x y)
  ∙ cong₂ _⊓ᴮ_
      (law-∈ (suc (suc zero)) zero (env4 σ p x y)
        ∙ sym (law-∈ (suc zero) zero (env2 σ x)))
      (sgl-only-eq σ p x y)
  ∙ sym (law-∧ sglMemberφ sglOnlyφ (env2 σ x))

pair-only-eq : (σ : Nameᴮ) (p x y : S)
  → val (∀̇∈ (var zero)
      ((var zero ≐ var (suc (suc (suc zero))))
        ∨̇ (var zero ≐ var (suc (suc (suc (suc zero))))))) (env4 σ p x y)
    ≡ val pairOnlyφ (env3 σ x y)
pair-only-eq σ p x y = ≤ᴮ-antisym le ge
  where
  body4 = (var zero ≐ var (suc (suc (suc zero))))
        ∨̇ (var zero ≐ var (suc (suc (suc (suc zero)))))
  body3 = (var zero ≐ var (suc (suc zero)))
        ∨̇ (var zero ≐ var (suc (suc (suc zero))))
  ν4 = env4 σ p x y
  ν3 = env3 σ x y
  body4-eq : (ρ : Nameᴮ)
    → val body4 (ρ ∷ ν4)
      ≡ (eq (fst ρ) (check x) ⊔ᴮ eq (fst ρ) (check y))
  body4-eq ρ =
    law-∨ (var zero ≐ var (suc (suc (suc zero))))
      (var zero ≐ var (suc (suc (suc (suc zero))))) (ρ ∷ ν4)
    ∙ cong₂ _⊔ᴮ_
        (law-≐ zero (suc (suc (suc zero))) (ρ ∷ ν4))
        (law-≐ zero (suc (suc (suc (suc zero)))) (ρ ∷ ν4))
  body3-eq : (ρ : Nameᴮ)
    → val body3 (ρ ∷ ν3)
      ≡ (eq (fst ρ) (check x) ⊔ᴮ eq (fst ρ) (check y))
  body3-eq ρ =
    law-∨ (var zero ≐ var (suc (suc zero)))
      (var zero ≐ var (suc (suc (suc zero)))) (ρ ∷ ν3)
    ∙ cong₂ _⊔ᴮ_
        (law-≐ zero (suc (suc zero)) (ρ ∷ ν3))
        (law-≐ zero (suc (suc (suc zero))) (ρ ∷ ν3))
  le = law-∀∈-glb zero body3 ν3 (val (∀̇∈ (var zero) body4) ν4) λ ρ →
    subst (λ b → ⟨ val (∀̇∈ (var zero) body4) ν4
                  ≤ᴮ (mem (fst ρ) (fst σ) ⇒ᴮ b) ⟩)
      (body4-eq ρ ∙ sym (body3-eq ρ))
      (law-∀∈-lb zero body4 ν4 ρ)
  ge = law-∀∈-glb zero body4 ν4 (val pairOnlyφ ν3) λ ρ →
    subst (λ b → ⟨ val pairOnlyφ ν3
                  ≤ᴮ (mem (fst ρ) (fst σ) ⇒ᴮ b) ⟩)
      (body3-eq ρ ∙ sym (body4-eq ρ))
      (law-∀∈-lb zero body3 ν3 ρ)

pair-match : (σ : Nameᴮ) (p x y : S)
  → val kpairPairφ (env4 σ p x y) ≡ val pairSrc (env3 σ x y)
pair-match σ p x y =
  law-∧ (var (suc (suc zero)) ∈̇ var zero)
    ((var (suc (suc (suc zero))) ∈̇ var zero)
      ∧̇ (∀̇∈ (var zero)
           ((var zero ≐ var (suc (suc (suc zero))))
            ∨̇ (var zero ≐ var (suc (suc (suc (suc zero))))))))
    (env4 σ p x y)
  ∙ cong₂ _⊓ᴮ_
      (law-∈ (suc (suc zero)) zero (env4 σ p x y)
        ∙ sym (law-∈ (suc zero) zero (env3 σ x y)))
      (law-∧ (var (suc (suc (suc zero))) ∈̇ var zero)
        (∀̇∈ (var zero)
          ((var zero ≐ var (suc (suc (suc zero))))
            ∨̇ (var zero ≐ var (suc (suc (suc (suc zero)))))))
        (env4 σ p x y)
      ∙ cong₂ _⊓ᴮ_
          (law-∈ (suc (suc (suc zero))) zero (env4 σ p x y)
            ∙ sym (law-∈ (suc (suc zero)) zero (env3 σ x y)))
          (pair-only-eq σ p x y)
      ∙ sym (law-∧ pairRightφ pairOnlyφ (env3 σ x y)))
  ∙ sym (law-∧ pairLeftφ (pairRightφ ∧̇ pairOnlyφ) (env3 σ x y))

kpair-fwd : (σ : Nameᴮ) (p x y : S) → ⟨ CB.isKPair p x y ⟩
  → ⟨ mem (fst σ) (check p) ≤ᴮ val kpairDisjφ (env4 σ p x y) ⟩
kpair-fwd σ p x y hp =
  Cong.Sgl.CM.check-∈-lub p (fst σ) (val kpairDisjφ (env4 σ p x y))
    (λ t ht → PT.rec
      (snd (eq (fst σ) (check t) ≤ᴮ val kpairDisjφ (env4 σ p x y)))
      (choose t)
      (hp t .fst ht))
  where
  disj = val kpairDisjφ (env4 σ p x y)
  choose : (t : S)
    → ⟨ CB.isSingleton t x ⟩ ⊎ ⟨ CB.isPair t x y ⟩
    → ⟨ eq (fst σ) (check t) ≤ᴮ disj ⟩
  choose t (inl hs) = ⊆ˢ-trans (sgl-from-eq t x σ hs)
    (subst (λ z → ⟨ z ≤ᴮ disj ⟩) (sgl-match σ p x y)
      (subst (λ z → ⟨ val kpairSglφ (env4 σ p x y) ≤ᴮ z ⟩)
        (sym (law-∨ kpairSglφ kpairPairφ (env4 σ p x y)))
        (⊔-ub₁ (val kpairSglφ (env4 σ p x y))
          (val kpairPairφ (env4 σ p x y)))))
  choose t (inr hr) = ⊆ˢ-trans (pair-from-eq t x y σ hr)
    (subst (λ z → ⟨ z ≤ᴮ disj ⟩) (pair-match σ p x y)
      (subst (λ z → ⟨ val kpairPairφ (env4 σ p x y) ≤ᴮ z ⟩)
        (sym (law-∨ kpairSglφ kpairPairφ (env4 σ p x y)))
        (⊔-ub₂ (val kpairSglφ (env4 σ p x y))
          (val kpairPairφ (env4 σ p x y)))))

weight-le : (n x : S) → ⟨ x ∈ˢ Cong.Sgl.BNG.BSupport.support n ⟩
  → ⟨ Cong.Sgl.BNG.weight n x ≤ᴮ mem x n ⟩
weight-le n x h =
  ⊆ˢ-trans into (BAT.Atomic.∈ᴮ-ub x n x h)
  where
  into : ⟨ Cong.Sgl.BNG.weight n x
           ≤ᴮ (Cong.Sgl.BNG.weight n x ⊓ᴮ eq x x) ⟩
  into = ⊓-glb (Cong.Sgl.BNG.weight n x) (eq x x) (Cong.Sgl.BNG.weight n x)
           (≤ᴮ-refl (Cong.Sgl.BNG.weight n x))
           (subst (λ z → ⟨ Cong.Sgl.BNG.weight n x ≤ᴮ z ⟩)
             (sym (BAT.Laws.≈ᴮ-refl x))
             (⊤-greatest (Cong.Sgl.BNG.weight n x)))

pack : (σ : Nameᴮ) (z : S) → ⟨ z ∈ˢ Cong.Sgl.BNG.BSupport.support (fst σ) ⟩
     → Nameᴮ
pack σ z hz = z , Cong.Sgl.BNG.BSupport.K.child-is-name (fst σ) (snd σ) z
  (Cong.Sgl.BNG.BSupport.support-out (fst σ) z hz)

sgl-unique : (s x : S) (σ : Nameᴮ) → ⟨ CB.isSingleton s x ⟩
  → ⟨ val sglSrc (σ ∷ checkNm x ∷ []) ≤ᴮ eq (fst σ) (check s) ⟩
sgl-unique s x σ (hin , honly) =
  subst (λ z → ⟨ z ≤ᴮ eq (fst σ) (check s) ⟩) (sym sg-path)
    (BAT.Atomic.≈ᴮ-glb (fst σ) (check s) sg left right)
  where
  ν = σ ∷ checkNm x ∷ []
  sg = mem (check x) (fst σ) ⊓ᴮ val sglOnlyφ ν
  sg-path : val sglSrc ν ≡ sg
  sg-path =
    law-∧ sglMemberφ sglOnlyφ ν
    ∙ cong₂ _⊓ᴮ_ (law-∈ (suc zero) zero ν) refl

  only-lb : (ρ : Nameᴮ)
    → ⟨ val sglOnlyφ ν
        ≤ᴮ (mem (fst ρ) (fst σ) ⇒ᴮ eq (fst ρ) (check x)) ⟩
  only-lb ρ =
    subst (λ b → ⟨ val sglOnlyφ ν
                  ≤ᴮ (mem (fst ρ) (fst σ) ⇒ᴮ b) ⟩)
      (law-≐ zero (suc (suc zero)) (ρ ∷ ν))
      (law-∀∈-lb zero (var zero ≐ var (suc (suc zero))) ν ρ)

  left : (z : S) → ⟨ z ∈ˢ Cong.Sgl.BNG.BSupport.support (fst σ) ⟩
       → ⟨ sg ≤ᴮ (Cong.Sgl.BNG.weight (fst σ) z ⇒ᴮ mem z (check s)) ⟩
  left z hz = ⇒ᴮ-curry sg (Cong.Sgl.BNG.weight (fst σ) z) (mem z (check s))
    (⊆ˢ-trans meet-mem (⊆ˢ-trans only-to-eq to-mem))
    where
    meet-mem : ⟨ (sg ⊓ᴮ Cong.Sgl.BNG.weight (fst σ) z)
                 ≤ᴮ (sg ⊓ᴮ mem z (fst σ)) ⟩
    meet-mem = ⊓-glb sg (mem z (fst σ)) (sg ⊓ᴮ Cong.Sgl.BNG.weight (fst σ) z)
      (⊓-lb₁ sg (Cong.Sgl.BNG.weight (fst σ) z))
      (⊆ˢ-trans (⊓-lb₂ sg (Cong.Sgl.BNG.weight (fst σ) z))
        (weight-le (fst σ) z hz))
    only-to-eq : ⟨ (sg ⊓ᴮ mem z (fst σ)) ≤ᴮ eq z (check x) ⟩
    only-to-eq = ⇒ᴮ-uncurry sg (mem z (fst σ)) (eq z (check x))
      (⊆ˢ-trans (⊓-lb₂ (mem (check x) (fst σ)) (val sglOnlyφ ν))
        (only-lb (pack σ z hz)))
    to-mem : ⟨ eq z (check x) ≤ᴮ mem z (check s) ⟩
    to-mem = Cong.Sgl.CM.check-∈-ub s x z hin

  right : (z : S) → ⟨ z ∈ˢ Cong.Sgl.BNG.BSupport.support (check s) ⟩
        → ⟨ sg ≤ᴮ (Cong.Sgl.BNG.weight (check s) z ⇒ᴮ mem z (fst σ)) ⟩
  right z hz = ⇒ᴮ-curry sg (Cong.Sgl.BNG.weight (check s) z) (mem z (fst σ))
    (⊆ˢ-trans meet-mem (⊆ˢ-trans into-eq to-mem))
    where
    meet-mem : ⟨ (sg ⊓ᴮ Cong.Sgl.BNG.weight (check s) z)
                 ≤ᴮ (sg ⊓ᴮ mem z (check s)) ⟩
    meet-mem = ⊓-glb sg (mem z (check s)) (sg ⊓ᴮ Cong.Sgl.BNG.weight (check s) z)
      (⊓-lb₁ sg (Cong.Sgl.BNG.weight (check s) z))
      (⊆ˢ-trans (⊓-lb₂ sg (Cong.Sgl.BNG.weight (check s) z))
        (weight-le (check s) z hz))
    into-eq : ⟨ (sg ⊓ᴮ mem z (check s))
                ≤ᴮ (eq (check x) z ⊓ᴮ mem (check x) (fst σ)) ⟩
    into-eq = ⊓-glb (eq (check x) z) (mem (check x) (fst σ))
      (sg ⊓ᴮ mem z (check s))
      (⊆ˢ-trans (⊓-lb₂ sg (mem z (check s)))
        (subst (λ e → ⟨ mem z (check s) ≤ᴮ e ⟩)
          (BAT.Atomic.≈ᴮ-sym z (check x))
          (Cong.Sgl.CM.check-∈-lub s z (eq z (check x))
            (λ a ha → eq-from-check (pack (checkNm s) z hz) a x (honly a ha)))))
      (⊆ˢ-trans (⊓-lb₁ sg (mem z (check s)))
        (⊓-lb₁ (mem (check x) (fst σ)) (val sglOnlyφ ν)))
    to-mem : ⟨ (eq (check x) z ⊓ᴮ mem (check x) (fst σ))
               ≤ᴮ mem z (fst σ) ⟩
    to-mem = BAT.Laws.∈ᴮ-congˡ (check x) z (fst σ)

kpair-sgl-rev : (σ : Nameᴮ) (p x y s : S)
  → ⟨ CB.isSingleton s x ⟩ → ⟨ s ∈ˢ p ⟩
  → ⟨ val kpairSglφ (env4 σ p x y) ≤ᴮ mem (fst σ) (check p) ⟩
kpair-sgl-rev σ p x y s hs hin =
  ⊆ˢ-trans from-sgl from-eq
  where
  from-sgl : ⟨ val kpairSglφ (env4 σ p x y) ≤ᴮ eq (fst σ) (check s) ⟩
  from-sgl = subst (λ z → ⟨ z ≤ᴮ eq (fst σ) (check s) ⟩)
    (sym (sgl-match σ p x y)) (sgl-unique s x σ hs)

  from-eq : ⟨ eq (fst σ) (check s) ≤ᴮ mem (fst σ) (check p) ⟩
  from-eq = subst (λ e → ⟨ e ≤ᴮ mem (fst σ) (check p) ⟩)
    (cong (eq (check s) (fst σ) ⊓ᴮ_)
      (Cong.Sgl.CM.check-∈-top s p hin)
      ∙ ⊓-⊤ (eq (check s) (fst σ))
      ∙ BAT.Atomic.≈ᴮ-sym (check s) (fst σ))
    (BAT.Laws.∈ᴮ-congˡ (check s) (fst σ) (check p))
