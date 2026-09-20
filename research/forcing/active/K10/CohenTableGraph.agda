{-# OPTIONS --cubical --safe --guardedness #-}

open import Base.Prelude
open import Base.Truth
open import Base.Classical using ( LEM )
open import FOL.ZFStructure using ( ZFStructure )
import NameKernel
import OrdinaryProfile
import K9.NameGround
import K9.BooleanNameGround

module K10.CohenTableGraph
  {ℓ} (𝒮 : ZFStructure (hPropAlgebra ℓ))
  (families : NameKernel.Families 𝒮)
  (accessible : NameKernel.Accessibility 𝒮)
  (images : NameKernel.MemberImage 𝒮)
  (pow : OrdinaryProfile.PowerSet 𝒮)
  (κ w : ZFStructure.S 𝒮)
  (lem : LEM ℓ)
  where

open import FOL.ZFStructure using ( module hPropStructure )
import Cubical.HITs.PropositionalTruncation as PT
open PT using ( ∣_∣₁ ; ∥_∥₁ ; squash₁ )

open TruthAlgebra (hPropAlgebra ℓ)
open hPropStructure 𝒮

module NG = K9.NameGround 𝒮 families accessible images pow κ w
  using ( extensional ; ≈ˢ-paths ; module Union )
module BG = K9.BooleanNameGround 𝒮 families accessible images pow κ w lem
  using ( B ; module BK )

≈→≡ : {x y : S} → ⟨ x ≈ˢ y ⟩ → x ≡ y
≈→≡ {x} {y} h = subst ⟨_⟩ (NG.≈ˢ-paths x y) h

≡→≈ : {x y : S} → x ≡ y → ⟨ x ≈ˢ y ⟩
≡→≈ {x} {y} e = subst ⟨_⟩ (sym (NG.≈ˢ-paths x y)) e

module Graph (C : S) (f : S → S → S) where

  innerH : S → S
  innerH x = NameKernel.MemberImage.image images C
    (λ qy → BG.BK.entry (BG.BK.entry x (fst qy)) (f x (fst qy)))

  graphH : S
  graphH = NG.Union.bigUnion
    (NameKernel.MemberImage.image images C (λ qx → innerH (fst qx)))

  OUTER : S
  OUTER = NameKernel.MemberImage.image images C (λ qx → innerH (fst qx))

  OUTER-spec : (u : S)
    → (u ∈ˢ OUTER)
      ≡ ⋁ S (λ x → ⋁ ⟨ x ∈ˢ C ⟩ (λ hx → u ≈ˢ innerH x))
  OUTER-spec u =
    NameKernel.MemberImage.image-spec images C (λ qx → innerH (fst qx)) u

  innerH-spec : (x u : S)
    → (u ∈ˢ innerH x)
      ≡ ⋁ S (λ y → ⋁ ⟨ y ∈ˢ C ⟩ (λ hy →
          u ≈ˢ BG.BK.entry (BG.BK.entry x y) (f x y)))
  innerH-spec x u =
    NameKernel.MemberImage.image-spec images C
      (λ qy → BG.BK.entry (BG.BK.entry x (fst qy)) (f x (fst qy))) u

  graphH-out : (q : S) (hq∈ : ⟨ q ∈ˢ graphH ⟩)
    → ∥ Σ[ x ∈ S ] Σ[ hx ∈ ⟨ x ∈ˢ C ⟩ ]
        Σ[ y ∈ S ] Σ[ hy ∈ ⟨ y ∈ˢ C ⟩ ]
          q ≡ BG.BK.entry (BG.BK.entry x y) (f x y) ∥₁
  graphH-out q hq∈ =
    PT.rec squash₁
      (λ { (u , hu∈ , hqu) →
        PT.rec squash₁
          (λ { (x , htrunc₁) →
            PT.rec squash₁
              (λ { (hx , hu≈) →
                PT.rec squash₁
                  (λ { (y , htrunc₂) →
                    PT.rec squash₁
                      (λ { (hy , hq≈) →
                        ∣ x , hx , y , hy , ≈→≡ hq≈ ∣₁ })
                      htrunc₂ })
                  (subst ⟨_⟩ (innerH-spec x q)
                    (subst (λ w → ⟨ q ∈ˢ w ⟩) (≈→≡ hu≈) hqu)) })
            htrunc₁ })
          (subst ⟨_⟩ (OUTER-spec u) hu∈) })
      (subst ⟨_⟩ (NG.Union.bigUnion-spec OUTER q) hq∈)

  graphH-in : (q x y : S) → ⟨ x ∈ˢ C ⟩ → ⟨ y ∈ˢ C ⟩
    → q ≡ BG.BK.entry (BG.BK.entry x y) (f x y)
    → ⟨ q ∈ˢ graphH ⟩
  graphH-in q x y hx hy hq =
    subst ⟨_⟩ (sym (NG.Union.bigUnion-spec OUTER q))
      ∣ innerH x , (inner∈outer , q∈inner) ∣₁
    where
    inner∈outer : ⟨ innerH x ∈ˢ OUTER ⟩
    inner∈outer =
      subst ⟨_⟩ (sym (OUTER-spec (innerH x)))
        ∣ x , ∣ hx , ≡→≈ refl ∣₁ ∣₁
    q∈inner : ⟨ q ∈ˢ innerH x ⟩
    q∈inner =
      subst ⟨_⟩ (sym (innerH-spec x q))
        ∣ y , ∣ hy , ≡→≈ hq ∣₁ ∣₁
