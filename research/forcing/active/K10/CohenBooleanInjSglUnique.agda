{-# OPTIONS --cubical --safe --guardedness #-}

open import Base.Prelude
open import Base.Truth
open import Base.Classical using ( LEM )
open import FOL.ZFStructure using ( ZFStructure )
import NameKernel
import OrdinaryProfile
import CardinalBridge
import K4.Algebra
import K4.Implication
import K9.BooleanAtomic
import K9.NameGround
import K10.CohenBooleanInjSgl

-- Boolean uniqueness of singletons: a name that is a singleton of check(x)
-- is ≈ᴮ the check of a ground singleton of x. No Subst, CCC, Force, or OmegaTop.

module K10.CohenBooleanInjSglUnique
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
open import FOL.Syntax using ( var ; _≐_ ; ∀̇∈ )

open TruthAlgebra (hPropAlgebra ℓ)
open hPropStructure 𝒮

module NG = K9.NameGround 𝒮 families accessible images pow κ w
  using ( extensional ; ≈ˢ-paths )
module BAT = K9.BooleanAtomic 𝒮 families accessible images pow κ w lem
  using ( B ; module Atomic ; module IC ; module Laws )
open K4.Algebra 𝒮 using ( _≤ᴮ_ ; ≤ᴮ-refl ; ⊆ˢ-trans )
open K4.Algebra.Lattice BAT.IC.codedLattice
  using ( _⊓ᴮ_ ; ⊤ᴮ ; ⊓-lb₁ ; ⊓-lb₂ ; ⊓-glb )
open K4.Implication 𝒮 NG.extensional NG.≈ˢ-paths BAT.B
  BAT.IC.codedLattice BAT.IC.codedComplement
  using ( ⊤-greatest ; _⇒ᴮ_ ; ⇒ᴮ-curry ; ⇒ᴮ-uncurry )
module Sgl = K10.CohenBooleanInjSgl 𝒮 families accessible images pow κ w lem paths
module CB = CardinalBridge 𝒮
open BAT.Atomic using () renaming ( _∈ᴮ_ to mem ; _≈ᴮ_ to eq )

open Sgl using ( checkNm ; sglSrc ; sglMemberφ ; sglOnlyφ ; eq-from-check )
open Sgl.BNG.Checked using ( check )
open Sgl.VS using ( Nameᴮ ; val ; law-∈ ; law-≐ ; law-∧ ; law-∀∈-lb )

weight-le : (n x : S) → ⟨ x ∈ˢ Sgl.BNG.BSupport.support n ⟩
  → ⟨ Sgl.BNG.weight n x ≤ᴮ mem x n ⟩
weight-le n x h =
  ⊆ˢ-trans into (BAT.Atomic.∈ᴮ-ub x n x h)
  where
  into : ⟨ Sgl.BNG.weight n x
           ≤ᴮ (Sgl.BNG.weight n x ⊓ᴮ eq x x) ⟩
  into = ⊓-glb (Sgl.BNG.weight n x) (eq x x) (Sgl.BNG.weight n x)
           (≤ᴮ-refl (Sgl.BNG.weight n x))
           (subst (λ z → ⟨ Sgl.BNG.weight n x ≤ᴮ z ⟩)
             (sym (BAT.Laws.≈ᴮ-refl x))
             (⊤-greatest (Sgl.BNG.weight n x)))

pack : (σ : Nameᴮ) (z : S) → ⟨ z ∈ˢ Sgl.BNG.BSupport.support (fst σ) ⟩
     → Nameᴮ
pack σ z hz = z , Sgl.BNG.BSupport.K.child-is-name (fst σ) (snd σ) z
  (Sgl.BNG.BSupport.support-out (fst σ) z hz)

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

  left : (z : S) → ⟨ z ∈ˢ Sgl.BNG.BSupport.support (fst σ) ⟩
       → ⟨ sg ≤ᴮ (Sgl.BNG.weight (fst σ) z ⇒ᴮ mem z (check s)) ⟩
  left z hz = ⇒ᴮ-curry sg (Sgl.BNG.weight (fst σ) z) (mem z (check s))
    (⊆ˢ-trans meet-mem (⊆ˢ-trans only-to-eq to-mem))
    where
    meet-mem : ⟨ (sg ⊓ᴮ Sgl.BNG.weight (fst σ) z) ≤ᴮ (sg ⊓ᴮ mem z (fst σ)) ⟩
    meet-mem = ⊓-glb sg (mem z (fst σ)) (sg ⊓ᴮ Sgl.BNG.weight (fst σ) z)
      (⊓-lb₁ sg (Sgl.BNG.weight (fst σ) z))
      (⊆ˢ-trans (⊓-lb₂ sg (Sgl.BNG.weight (fst σ) z))
        (weight-le (fst σ) z hz))
    only-to-eq : ⟨ (sg ⊓ᴮ mem z (fst σ)) ≤ᴮ eq z (check x) ⟩
    only-to-eq = ⇒ᴮ-uncurry sg (mem z (fst σ)) (eq z (check x))
      (⊆ˢ-trans (⊓-lb₂ (mem (check x) (fst σ)) (val sglOnlyφ ν))
        (only-lb (pack σ z hz)))
    to-mem : ⟨ eq z (check x) ≤ᴮ mem z (check s) ⟩
    to-mem = Sgl.CM.check-∈-ub s x z hin

  right : (z : S) → ⟨ z ∈ˢ Sgl.BNG.BSupport.support (check s) ⟩
        → ⟨ sg ≤ᴮ (Sgl.BNG.weight (check s) z ⇒ᴮ mem z (fst σ)) ⟩
  right z hz = ⇒ᴮ-curry sg (Sgl.BNG.weight (check s) z) (mem z (fst σ))
    (⊆ˢ-trans meet-mem (⊆ˢ-trans into-eq to-mem))
    where
    meet-mem : ⟨ (sg ⊓ᴮ Sgl.BNG.weight (check s) z)
                 ≤ᴮ (sg ⊓ᴮ mem z (check s)) ⟩
    meet-mem = ⊓-glb sg (mem z (check s)) (sg ⊓ᴮ Sgl.BNG.weight (check s) z)
      (⊓-lb₁ sg (Sgl.BNG.weight (check s) z))
      (⊆ˢ-trans (⊓-lb₂ sg (Sgl.BNG.weight (check s) z))
        (weight-le (check s) z hz))
    into-eq : ⟨ (sg ⊓ᴮ mem z (check s))
                ≤ᴮ (eq (check x) z ⊓ᴮ mem (check x) (fst σ)) ⟩
    into-eq = ⊓-glb (eq (check x) z) (mem (check x) (fst σ))
      (sg ⊓ᴮ mem z (check s))
      (⊆ˢ-trans (⊓-lb₂ sg (mem z (check s)))
        (subst (λ e → ⟨ mem z (check s) ≤ᴮ e ⟩)
          (BAT.Atomic.≈ᴮ-sym z (check x))
          (Sgl.CM.check-∈-lub s z (eq z (check x))
            (λ a ha → eq-from-check (pack (checkNm s) z hz) a x (honly a ha)))))
      (⊆ˢ-trans (⊓-lb₁ sg (mem z (check s)))
        (⊓-lb₁ (mem (check x) (fst σ)) (val sglOnlyφ ν)))
    to-mem : ⟨ (eq (check x) z ⊓ᴮ mem (check x) (fst σ))
               ≤ᴮ mem z (fst σ) ⟩
    to-mem = BAT.Laws.∈ᴮ-congˡ (check x) z (fst σ)
