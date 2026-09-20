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
import K10.CohenValSeam
import K10.CohenBooleanPowerSrc
import K10.CohenBooleanSubset
import K10.CohenBooleanSubsetVal
import K10.CohenBooleanCands
import K10.CohenBooleanPower

module K10.CohenBooleanPowerSub
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
open import FOL.Syntax using ( var ; ∀̇_ ; _∈̇_ ; _⇒̇_ )
open PT using ( ∣_∣₁ )

open TruthAlgebra (hPropAlgebra ℓ)
open hPropStructure 𝒮
open NameKernel.MemberImage images using ( image ; image-spec )

module NG = K9.NameGround 𝒮 families accessible images pow κ w
  using ( extensional ; ≈ˢ-paths )
module BAT = K9.BooleanAtomic 𝒮 families accessible images pow κ w lem
  using ( B ; module Atomic ; module IC ; module Laws ; module BK
        ; module BSupport ; weight ; weight-upper ; weight-least
        ; source-child-name )
open K4.Algebra 𝒮 using ( Pt ; _≤ᴮ_ ; ⊆ˢ-trans ; ≤ᴮ-refl ; Pt≡ )
open K4.Algebra.Lattice BAT.IC.codedLattice
  using ( _⊓ᴮ_ ; ⊤ᴮ ; ⊓-lb₁ ; ⊓-lb₂ ; ⊓-glb )
open K4.Implication 𝒮 NG.extensional NG.≈ˢ-paths BAT.B
  BAT.IC.codedLattice BAT.IC.codedComplement
  using ( _⇒ᴮ_ ; ⇒ᴮ-curry ; ⇒ᴮ-uncurry ; ⊓-comm ; ≤ᴮ-antisym ; ⊤-greatest ; ⊓-⊤ )
module VS = K10.CohenValSeam 𝒮 families accessible images pow κ w lem paths
module PS = K10.CohenBooleanPowerSrc 𝒮
module Sub = K10.CohenBooleanSubset 𝒮 families accessible images pow κ w lem
module SV = K10.CohenBooleanSubsetVal 𝒮 families accessible images pow κ w lem
module Cands = K10.CohenBooleanCands 𝒮 families accessible images pow κ w
module Power = K10.CohenBooleanPower 𝒮 families accessible images pow κ w lem

open VS using ( Src ; Nameᴮ ; Envᴮ ; val )
open BAT.Atomic using () renaming ( _∈ᴮ_ to mem ; _≈ᴮ_ to eq )
open Sub.BNG using ( module Translation )

emptyEnv : Envᴮ 0
emptyEnv = []

omegaNm : Nameᴮ
omegaNm = Sub.omegaNm

body : Src 3
body = (var zero ∈̇ var (suc zero)) ⇒̇ (var zero ∈̇ var (suc (suc zero)))

subset-shape : PS.subsetSrc ≡ ∀̇ body
subset-shape = refl

subsetVal≤body : (τ σ : Nameᴮ)
  → ⟨ Sub.subsetVal (fst τ)
      ≤ᴮ (mem (fst σ) (fst τ) ⇒ᴮ mem (fst σ) (fst omegaNm)) ⟩
subsetVal≤body τ σ = ⇒ᴮ-curry
  (Sub.subsetVal (fst τ)) (mem (fst σ) (fst τ)) (mem (fst σ) (fst omegaNm))
  (subst (λ z → ⟨ z ≤ᴮ mem (fst σ) (fst omegaNm) ⟩)
    (⊓-comm (mem (fst σ) (fst τ)) (Sub.subsetVal (fst τ)))
    (⇒ᴮ-uncurry (mem (fst σ) (fst τ)) (Sub.subsetVal (fst τ))
      (mem (fst σ) (fst omegaNm))
      (BAT.Atomic.∈ᴮ-lub (fst σ) (fst τ)
        (Sub.subsetVal (fst τ) ⇒ᴮ mem (fst σ) (fst omegaNm))
        λ x hx → from-x x hx)))
  where
  from-x : (x : S) → ⟨ x ∈ˢ BAT.BSupport.support (fst τ) ⟩
    → ⟨ (BAT.weight (fst τ) x ⊓ᴮ eq (fst σ) x)
        ≤ᴮ (Sub.subsetVal (fst τ) ⇒ᴮ mem (fst σ) (fst omegaNm)) ⟩
  from-x x hx = ⇒ᴮ-curry (BAT.weight (fst τ) x ⊓ᴮ eq (fst σ) x)
    (Sub.subsetVal (fst τ)) (mem (fst σ) (fst omegaNm))
    (subst (λ z → ⟨ z ≤ᴮ mem (fst σ) (fst omegaNm) ⟩)
      (⊓-comm (Sub.subsetVal (fst τ))
        (BAT.weight (fst τ) x ⊓ᴮ eq (fst σ) x))
      (⊆ˢ-trans meet (cong-mem x hx)))
    where
    wt : ⟨ (Sub.subsetVal (fst τ) ⊓ᴮ BAT.weight (fst τ) x)
           ≤ᴮ mem x (fst omegaNm) ⟩
    wt = ⇒ᴮ-uncurry (Sub.subsetVal (fst τ))
      (BAT.weight (fst τ) x) (mem x (fst omegaNm))
      (SV.subset-lb (fst τ) x hx)
    meet : ⟨ (Sub.subsetVal (fst τ)
               ⊓ᴮ (BAT.weight (fst τ) x ⊓ᴮ eq (fst σ) x))
             ≤ᴮ (mem x (fst omegaNm) ⊓ᴮ eq (fst σ) x) ⟩
    meet = ⊓-glb (mem x (fst omegaNm)) (eq (fst σ) x)
      (Sub.subsetVal (fst τ) ⊓ᴮ (BAT.weight (fst τ) x ⊓ᴮ eq (fst σ) x))
      (⊆ˢ-trans
        (⊓-glb (BAT.weight (fst τ) x) (Sub.subsetVal (fst τ))
          (Sub.subsetVal (fst τ)
            ⊓ᴮ (BAT.weight (fst τ) x ⊓ᴮ eq (fst σ) x))
          (⊆ˢ-trans
            (⊓-lb₂ (Sub.subsetVal (fst τ))
              (BAT.weight (fst τ) x ⊓ᴮ eq (fst σ) x))
            (⊓-lb₁ (BAT.weight (fst τ) x) (eq (fst σ) x)))
          (⊓-lb₁ (Sub.subsetVal (fst τ))
            (BAT.weight (fst τ) x ⊓ᴮ eq (fst σ) x)))
        (subst (λ z → ⟨ z ≤ᴮ mem x (fst omegaNm) ⟩)
          (⊓-comm (Sub.subsetVal (fst τ)) (BAT.weight (fst τ) x)) wt))
      (⊆ˢ-trans
        (⊓-lb₂ (Sub.subsetVal (fst τ))
          (BAT.weight (fst τ) x ⊓ᴮ eq (fst σ) x))
        (⊓-lb₂ (BAT.weight (fst τ) x) (eq (fst σ) x)))
    cong-mem : (x : S) → ⟨ x ∈ˢ BAT.BSupport.support (fst τ) ⟩
      → ⟨ (mem x (fst omegaNm) ⊓ᴮ eq (fst σ) x)
          ≤ᴮ mem (fst σ) (fst omegaNm) ⟩
    cong-mem x hx =
      subst (λ e → ⟨ (mem x (fst omegaNm) ⊓ᴮ e)
                    ≤ᴮ mem (fst σ) (fst omegaNm) ⟩)
        (sym (BAT.Atomic.≈ᴮ-sym (fst σ) x))
        (subst (λ z → ⟨ z ≤ᴮ mem (fst σ) (fst omegaNm) ⟩)
          (⊓-comm (eq x (fst σ)) (mem x (fst omegaNm)))
          (BAT.Laws.∈ᴮ-congˡ x (fst σ) (fst omegaNm)))

opaque
  subsetVal≤compiled : (τ : Nameᴮ)
    → ⟨ Sub.subsetVal (fst τ) ≤ᴮ val PS.subsetSrc (τ ∷ omegaNm ∷ emptyEnv) ⟩
  subsetVal≤compiled τ =
    subst (λ φ → ⟨ Sub.subsetVal (fst τ) ≤ᴮ val φ (τ ∷ omegaNm ∷ emptyEnv) ⟩)
      (sym subset-shape)
      (VS.law-∀-glb body (τ ∷ omegaNm ∷ emptyEnv) (Sub.subsetVal (fst τ)) λ σ →
        subst (λ z → ⟨ Sub.subsetVal (fst τ) ≤ᴮ z ⟩)
          (sym (VS.law-⇒ (var zero ∈̇ var (suc zero))
            (var zero ∈̇ var (suc (suc zero)))
            (σ ∷ τ ∷ omegaNm ∷ emptyEnv)
            ∙ cong₂ _⇒ᴮ_
                (VS.law-∈ zero (suc zero) (σ ∷ τ ∷ omegaNm ∷ emptyEnv))
                (VS.law-∈ zero (suc (suc zero)) (σ ∷ τ ∷ omegaNm ∷ emptyEnv))))
          (subsetVal≤body τ σ))

body-val : (x σ : Nameᴮ)
  → val body (x ∷ σ ∷ omegaNm ∷ emptyEnv)
    ≡ (mem (fst x) (fst σ) ⇒ᴮ mem (fst x) (fst omegaNm))
body-val x σ =
  VS.law-⇒ (var zero ∈̇ var (suc zero))
    (var zero ∈̇ var (suc (suc zero)))
    (x ∷ σ ∷ omegaNm ∷ emptyEnv)
  ∙ cong₂ _⇒ᴮ_
      (VS.law-∈ zero (suc zero) (x ∷ σ ∷ omegaNm ∷ emptyEnv))
      (VS.law-∈ zero (suc (suc zero)) (x ∷ σ ∷ omegaNm ∷ emptyEnv))

body-subst : (x σ τ : Nameᴮ)
  → ⟨ (eq (fst σ) (fst τ) ⊓ᴮ val body (x ∷ σ ∷ omegaNm ∷ emptyEnv))
      ≤ᴮ val body (x ∷ τ ∷ omegaNm ∷ emptyEnv) ⟩
body-subst x σ τ =
  subst (λ z → ⟨ (eq (fst σ) (fst τ) ⊓ᴮ z)
                  ≤ᴮ val body (x ∷ τ ∷ omegaNm ∷ emptyEnv) ⟩)
    (sym (body-val x σ))
    (subst (λ z → ⟨ (eq (fst σ) (fst τ)
                      ⊓ᴮ (mem (fst x) (fst σ) ⇒ᴮ mem (fst x) (fst omegaNm)))
                    ≤ᴮ z ⟩)
      (sym (body-val x τ))
      (⇒ᴮ-curry (eq (fst σ) (fst τ)
                  ⊓ᴮ (mem (fst x) (fst σ) ⇒ᴮ mem (fst x) (fst omegaNm)))
        (mem (fst x) (fst τ)) (mem (fst x) (fst omegaNm))
        (⊆ˢ-trans meet (⇒ᴮ-uncurry (mem (fst x) (fst σ) ⇒ᴮ mem (fst x) (fst omegaNm))
          (mem (fst x) (fst σ)) (mem (fst x) (fst omegaNm))
          (≤ᴮ-refl (mem (fst x) (fst σ) ⇒ᴮ mem (fst x) (fst omegaNm))))))
      )
  where
  meet : ⟨ ((eq (fst σ) (fst τ)
              ⊓ᴮ (mem (fst x) (fst σ) ⇒ᴮ mem (fst x) (fst omegaNm)))
            ⊓ᴮ mem (fst x) (fst τ))
           ≤ᴮ ((mem (fst x) (fst σ) ⇒ᴮ mem (fst x) (fst omegaNm))
                ⊓ᴮ mem (fst x) (fst σ)) ⟩
  meet = ⊓-glb (mem (fst x) (fst σ) ⇒ᴮ mem (fst x) (fst omegaNm))
    (mem (fst x) (fst σ))
    ((eq (fst σ) (fst τ)
      ⊓ᴮ (mem (fst x) (fst σ) ⇒ᴮ mem (fst x) (fst omegaNm)))
      ⊓ᴮ mem (fst x) (fst τ))
    (⊆ˢ-trans
      (⊓-lb₁ (eq (fst σ) (fst τ)
        ⊓ᴮ (mem (fst x) (fst σ) ⇒ᴮ mem (fst x) (fst omegaNm)))
        (mem (fst x) (fst τ)))
      (⊓-lb₂ (eq (fst σ) (fst τ))
        (mem (fst x) (fst σ) ⇒ᴮ mem (fst x) (fst omegaNm))))
    (⊆ˢ-trans
      (⊓-glb (eq (fst σ) (fst τ)) (mem (fst x) (fst τ))
        ((eq (fst σ) (fst τ)
          ⊓ᴮ (mem (fst x) (fst σ) ⇒ᴮ mem (fst x) (fst omegaNm)))
          ⊓ᴮ mem (fst x) (fst τ))
        (⊆ˢ-trans
          (⊓-lb₁ (eq (fst σ) (fst τ)
            ⊓ᴮ (mem (fst x) (fst σ) ⇒ᴮ mem (fst x) (fst omegaNm)))
            (mem (fst x) (fst τ)))
          (⊓-lb₁ (eq (fst σ) (fst τ))
            (mem (fst x) (fst σ) ⇒ᴮ mem (fst x) (fst omegaNm))))
        (⊓-lb₂ (eq (fst σ) (fst τ)
          ⊓ᴮ (mem (fst x) (fst σ) ⇒ᴮ mem (fst x) (fst omegaNm)))
          (mem (fst x) (fst τ))))
      (subst (λ e → ⟨ (e ⊓ᴮ mem (fst x) (fst τ))
                      ≤ᴮ mem (fst x) (fst σ) ⟩)
        (BAT.Atomic.≈ᴮ-sym (fst τ) (fst σ))
        (BAT.Laws.∈ᴮ-congʳ (fst x) (fst τ) (fst σ))))

opaque
  subset-subst : (σ τ : Nameᴮ)
    → ⟨ (eq (fst σ) (fst τ) ⊓ᴮ val PS.subsetSrc (σ ∷ omegaNm ∷ emptyEnv))
        ≤ᴮ val PS.subsetSrc (τ ∷ omegaNm ∷ emptyEnv) ⟩
  subset-subst σ τ =
    subst (λ φ → ⟨ (eq (fst σ) (fst τ) ⊓ᴮ val φ (σ ∷ omegaNm ∷ emptyEnv))
                    ≤ᴮ val φ (τ ∷ omegaNm ∷ emptyEnv) ⟩)
      (sym subset-shape)
      (VS.law-∀-glb body (τ ∷ omegaNm ∷ emptyEnv)
        (eq (fst σ) (fst τ) ⊓ᴮ val (∀̇ body) (σ ∷ omegaNm ∷ emptyEnv))
        λ x → ⊆ˢ-trans
          (⊓-glb (eq (fst σ) (fst τ))
            (val body (x ∷ σ ∷ omegaNm ∷ emptyEnv))
            (eq (fst σ) (fst τ) ⊓ᴮ val (∀̇ body) (σ ∷ omegaNm ∷ emptyEnv))
            (⊓-lb₁ (eq (fst σ) (fst τ))
              (val (∀̇ body) (σ ∷ omegaNm ∷ emptyEnv)))
            (⊆ˢ-trans
              (⊓-lb₂ (eq (fst σ) (fst τ))
                (val (∀̇ body) (σ ∷ omegaNm ∷ emptyEnv)))
              (VS.law-∀-lb body (σ ∷ omegaNm ∷ emptyEnv) x)))
          (body-subst x σ τ))

≈→≡ : {a b : S} → ⟨ a ≈ˢ b ⟩ → a ≡ b
≈→≡ {a} {b} = subst ⟨_⟩ (NG.≈ˢ-paths a b)

≈-refl : (a : S) → ⟨ a ≈ˢ a ⟩
≈-refl a = subst ⟨_⟩ (sym (NG.≈ˢ-paths a a)) refl

cand-in-power : (σ : S) → ⟨ σ ∈ˢ Cands.cands ⟩
  → ⟨ Sub.candEntry σ ∈ˢ Power.powerB ⟩
cand-in-power σ hσ = subst ⟨_⟩ (sym (Power.powerB-spec (Sub.candEntry σ)))
  ∣ σ , ∣ hσ , ≈-refl (Sub.candEntry σ) ∣₁ ∣₁

entry-in-power : (σ : S) → ⟨ σ ∈ˢ Cands.cands ⟩
  → ⟨ BAT.BK.entry (Translation.trᴮ σ) (Sub.candWeight σ) ∈ˢ Power.powerB ⟩
entry-in-power σ hσ =
  subst (λ e → ⟨ e ∈ˢ Power.powerB ⟩) (Sub.candEntry-weight σ)
    (cand-in-power σ hσ)

weight-ge : (σ : S) → ⟨ σ ∈ˢ Cands.cands ⟩
  → ⟨ Sub.subsetVal (Translation.trᴮ σ) ≤ᴮ BAT.weight Power.powerB (Translation.trᴮ σ) ⟩
weight-ge σ hσ = subst
  (λ b → ⟨ b ≤ᴮ BAT.weight Power.powerB (Translation.trᴮ σ) ⟩)
  (sym (Sub.candWeight-pt σ))
  (BAT.weight-upper Power.powerB (Translation.trᴮ σ)
    (Sub.candWeight σ , Sub.candWeight-inB σ) (entry-in-power σ hσ))

entry-from-power : (x : S) (b : Pt BAT.B)
  → ⟨ BAT.BK.entry x (fst b) ∈ˢ Power.powerB ⟩
  → PT.∥ (Σ[ σ ∈ S ] (⟨ σ ∈ˢ Cands.cands ⟩
      × ((x ≡ Translation.trᴮ σ) × (fst b ≡ Sub.candWeight σ)))) ∥₁
entry-from-power x b he = PT.rec PT.squash₁ from-spec
  (subst ⟨_⟩ (Power.powerB-spec (BAT.BK.entry x (fst b))) he)
  where
  from-spec : Σ[ σ ∈ S ] ⟨ ⋁ ⟨ σ ∈ˢ Cands.cands ⟩
                (λ _ → BAT.BK.entry x (fst b) ≈ˢ Sub.candEntry σ) ⟩
    → PT.∥ (Σ[ σ ∈ S ] (⟨ σ ∈ˢ Cands.cands ⟩
        × ((x ≡ Translation.trᴮ σ) × (fst b ≡ Sub.candWeight σ)))) ∥₁
  from-spec (σ , inner) = PT.map from-eq inner
    where
    from-eq : ⟨ σ ∈ˢ Cands.cands ⟩ × ⟨ BAT.BK.entry x (fst b) ≈ˢ Sub.candEntry σ ⟩
      → Σ[ σ ∈ S ] (⟨ σ ∈ˢ Cands.cands ⟩
          × ((x ≡ Translation.trᴮ σ) × (fst b ≡ Sub.candWeight σ)))
    from-eq (hσ , heq) =
      σ , hσ
      , ( fst (BAT.BK.entry-inj (≈→≡ heq ∙ Sub.candEntry-weight σ))
        , snd (BAT.BK.entry-inj (≈→≡ heq ∙ Sub.candEntry-weight σ)) )

weight-le : (σ : S) → ⟨ σ ∈ˢ Cands.cands ⟩
  → ⟨ BAT.weight Power.powerB (Translation.trᴮ σ)
      ≤ᴮ Sub.subsetVal (Translation.trᴮ σ) ⟩
weight-le σ hσ = BAT.weight-least Power.powerB (Translation.trᴮ σ)
  (Sub.subsetVal (Translation.trᴮ σ)) λ b he →
    PT.rec (snd (b ≤ᴮ Sub.subsetVal (Translation.trᴮ σ)))
      (from-entry b he) (entry-from-power (Translation.trᴮ σ) b he)
  where
  from-entry : (b : Pt BAT.B)
    → ⟨ BAT.BK.entry (Translation.trᴮ σ) (fst b) ∈ˢ Power.powerB ⟩
    → Σ[ τ ∈ S ] (⟨ τ ∈ˢ Cands.cands ⟩
        × ((Translation.trᴮ σ ≡ Translation.trᴮ τ)
          × (fst b ≡ Sub.candWeight τ)))
    → ⟨ b ≤ᴮ Sub.subsetVal (Translation.trᴮ σ) ⟩
  from-entry b he (τ , hτ , xpath , bpath) =
    subst (λ z → ⟨ b ≤ᴮ z ⟩)
      (Pt≡ {BAT.B} {b} {Sub.candWeight τ , Sub.candWeight-inB τ} bpath
        ∙ sym (Sub.candWeight-pt τ)
        ∙ cong Sub.subsetVal (sym xpath))
      (≤ᴮ-refl b)

opaque
  weight-eq : (σ : S) → ⟨ σ ∈ˢ Cands.cands ⟩
    → BAT.weight Power.powerB (Translation.trᴮ σ)
      ≡ Sub.subsetVal (Translation.trᴮ σ)
  weight-eq σ hσ = ≤ᴮ-antisym (weight-le σ hσ) (weight-ge σ hσ)

member-lub : (τ : S) (c : Pt BAT.B)
  → ((σ : S) → ⟨ σ ∈ˢ Cands.cands ⟩
      → ⟨ (Sub.subsetVal (Translation.trᴮ σ)
            ⊓ᴮ eq τ (Translation.trᴮ σ)) ≤ᴮ c ⟩)
  → ⟨ mem τ Power.powerB ≤ᴮ c ⟩
member-lub τ c hyp = BAT.Atomic.∈ᴮ-lub τ Power.powerB c λ x hx →
  PT.rec (snd ((BAT.weight Power.powerB x ⊓ᴮ eq τ x) ≤ᴮ c))
    (from-support x hx) (BAT.BSupport.entry-out Power.powerB x hx)
  where
  from-support : (x : S) → ⟨ x ∈ˢ BAT.BSupport.support Power.powerB ⟩
    → Σ[ b ∈ S ] (⟨ b ∈ˢ BAT.B ⟩ × ⟨ BAT.BK.entry x b ∈ˢ Power.powerB ⟩)
    → ⟨ (BAT.weight Power.powerB x ⊓ᴮ eq τ x) ≤ᴮ c ⟩
  from-support x hx (b , hb , he) = PT.rec
    (snd ((BAT.weight Power.powerB x ⊓ᴮ eq τ x) ≤ᴮ c))
    (from-cand x b hb he) (entry-from-power x (b , hb) he)
    where
    from-cand : (x b : S) (hb : ⟨ b ∈ˢ BAT.B ⟩)
      → ⟨ BAT.BK.entry x b ∈ˢ Power.powerB ⟩
      → Σ[ σ ∈ S ] (⟨ σ ∈ˢ Cands.cands ⟩
          × ((x ≡ Translation.trᴮ σ) × (b ≡ Sub.candWeight σ)))
      → ⟨ (BAT.weight Power.powerB x ⊓ᴮ eq τ x) ≤ᴮ c ⟩
    from-cand x b hb he (σ , hσ , xpath , bpath) =
      subst (λ z → ⟨ (z ⊓ᴮ eq τ x) ≤ᴮ c ⟩)
        (sym (cong (BAT.weight Power.powerB) xpath ∙ weight-eq σ hσ))
        (subst (λ y → ⟨ (Sub.subsetVal (Translation.trᴮ σ)
                          ⊓ᴮ eq τ y) ≤ᴮ c ⟩) (sym xpath)
          (hyp σ hσ))

⊓-monoˡ : (u u' v : Pt BAT.B) → ⟨ u ≤ᴮ u' ⟩ → ⟨ (u ⊓ᴮ v) ≤ᴮ (u' ⊓ᴮ v) ⟩
⊓-monoˡ u u' v h = ⊓-glb u' v (u ⊓ᴮ v)
  (⊆ˢ-trans (⊓-lb₁ u v) h) (⊓-lb₂ u v)

trNm : (σ : S) → ⟨ σ ∈ˢ Cands.cands ⟩ → Nameᴮ
trNm σ hσ = Translation.trᴮ σ
  , Translation.trᴮ-name σ (Cands.cands-name σ hσ)

cand-le : (τ : Nameᴮ) (σ : S) (hσ : ⟨ σ ∈ˢ Cands.cands ⟩)
  → ⟨ (Sub.subsetVal (Translation.trᴮ σ)
        ⊓ᴮ eq (fst τ) (Translation.trᴮ σ))
      ≤ᴮ val PS.subsetSrc (τ ∷ omegaNm ∷ emptyEnv) ⟩
cand-le τ σ hσ = ⊆ˢ-trans
  (⊓-monoˡ (Sub.subsetVal (Translation.trᴮ σ))
    (val PS.subsetSrc (trNm σ hσ ∷ omegaNm ∷ emptyEnv))
    (eq (fst τ) (Translation.trᴮ σ))
    (subsetVal≤compiled (trNm σ hσ)))
  (subst (λ e → ⟨ (val PS.subsetSrc (trNm σ hσ ∷ omegaNm ∷ emptyEnv) ⊓ᴮ e)
                  ≤ᴮ val PS.subsetSrc (τ ∷ omegaNm ∷ emptyEnv) ⟩)
    (BAT.Atomic.≈ᴮ-sym (fst (trNm σ hσ)) (fst τ))
    (subst (λ z → ⟨ z ≤ᴮ val PS.subsetSrc (τ ∷ omegaNm ∷ emptyEnv) ⟩)
      (⊓-comm (eq (fst (trNm σ hσ)) (fst τ))
        (val PS.subsetSrc (trNm σ hσ ∷ omegaNm ∷ emptyEnv)))
      (subset-subst (trNm σ hσ) τ)))

opaque
  member≤subset : (τ : Nameᴮ)
    → ⟨ mem (fst τ) Power.powerB
        ≤ᴮ val PS.subsetSrc (τ ∷ omegaNm ∷ emptyEnv) ⟩
  member≤subset τ = member-lub (fst τ)
    (val PS.subsetSrc (τ ∷ omegaNm ∷ emptyEnv))
    (λ σ hσ → cand-le τ σ hσ)

cand-support : (σ : S) → ⟨ σ ∈ˢ Cands.cands ⟩
  → ⟨ Translation.trᴮ σ ∈ˢ BAT.BSupport.support Power.powerB ⟩
cand-support σ hσ = BAT.BSupport.entry-in Power.powerB (Translation.trᴮ σ)
  (Sub.candWeight σ) (Sub.candWeight-inB σ) (entry-in-power σ hσ)

opaque
  member-ub : (τ σ : S) → ⟨ σ ∈ˢ Cands.cands ⟩
    → ⟨ (Sub.subsetVal (Translation.trᴮ σ) ⊓ᴮ eq τ (Translation.trᴮ σ))
        ≤ᴮ mem τ Power.powerB ⟩
  member-ub τ σ hσ = subst
    (λ b → ⟨ (b ⊓ᴮ eq τ (Translation.trᴮ σ)) ≤ᴮ mem τ Power.powerB ⟩)
    (sym (Sub.candWeight-pt σ))
    (⊆ˢ-trans
      (⊓-monoˡ (Sub.candWeight σ , Sub.candWeight-inB σ)
        (BAT.weight Power.powerB (Translation.trᴮ σ))
        (eq τ (Translation.trᴮ σ))
        (BAT.weight-upper Power.powerB (Translation.trᴮ σ)
          (Sub.candWeight σ , Sub.candWeight-inB σ)
          (entry-in-power σ hσ)))
      (BAT.Atomic.∈ᴮ-ub τ Power.powerB (Translation.trᴮ σ)
        (cand-support σ hσ)))

⇒-antiˡ : (a a' b : Pt BAT.B) → ⟨ a' ≤ᴮ a ⟩
  → ⟨ (a ⇒ᴮ b) ≤ᴮ (a' ⇒ᴮ b) ⟩
⇒-antiˡ a a' b h = ⇒ᴮ-curry (a ⇒ᴮ b) a' b
  (⊆ˢ-trans
    (⊓-glb (a ⇒ᴮ b) a ((a ⇒ᴮ b) ⊓ᴮ a')
      (⊓-lb₁ (a ⇒ᴮ b) a')
      (⊆ˢ-trans (⊓-lb₂ (a ⇒ᴮ b) a') h))
    (⇒ᴮ-uncurry (a ⇒ᴮ b) a b (≤ᴮ-refl (a ⇒ᴮ b))))

weight≤mem : (χ x : S) → ⟨ x ∈ˢ BAT.BSupport.support χ ⟩
  → ⟨ BAT.weight χ x ≤ᴮ mem x χ ⟩
weight≤mem χ x hx =
  subst (λ z → ⟨ z ≤ᴮ mem x χ ⟩) (⊓-⊤ (BAT.weight χ x))
    (subst (λ z → ⟨ (BAT.weight χ x ⊓ᴮ z) ≤ᴮ mem x χ ⟩)
      (BAT.Laws.≈ᴮ-refl x)
      (BAT.Atomic.∈ᴮ-ub x χ x hx))

supportNm : (τ : Nameᴮ) (x : S) → ⟨ x ∈ˢ BAT.BSupport.support (fst τ) ⟩
  → Nameᴮ
supportNm τ x hx = x ,
  BAT.BSupport.K.child-is-name (fst τ) (snd τ) x
    (PT.map (λ { (b , hb , he) → b , he })
      (BAT.BSupport.entry-out (fst τ) x hx))

opaque
  compiled≤subsetVal : (τ : Nameᴮ)
    → ⟨ val PS.subsetSrc (τ ∷ omegaNm ∷ emptyEnv)
        ≤ᴮ Sub.subsetVal (fst τ) ⟩
  compiled≤subsetVal τ =
    subst (λ φ → ⟨ val φ (τ ∷ omegaNm ∷ emptyEnv)
                    ≤ᴮ Sub.subsetVal (fst τ) ⟩)
      (sym subset-shape)
      (SV.subset-glb (fst τ) (val (∀̇ body) (τ ∷ omegaNm ∷ emptyEnv))
        λ x hx → ⊆ˢ-trans
          (VS.law-∀-lb body (τ ∷ omegaNm ∷ emptyEnv) (supportNm τ x hx))
          (subst (λ z → ⟨ z ≤ᴮ Sub.subsetFam (fst τ) (x , hx) ⟩)
            (sym (body-val (supportNm τ x hx) τ))
            (⇒-antiˡ (mem x (fst τ)) (BAT.weight (fst τ) x)
              (mem x (fst omegaNm)) (weight≤mem (fst τ) x hx))))

opaque
  subsetVal≡compiled : (τ : Nameᴮ)
    → Sub.subsetVal (fst τ) ≡ val PS.subsetSrc (τ ∷ omegaNm ∷ emptyEnv)
  subsetVal≡compiled τ = ≤ᴮ-antisym (subsetVal≤compiled τ) (compiled≤subsetVal τ)

