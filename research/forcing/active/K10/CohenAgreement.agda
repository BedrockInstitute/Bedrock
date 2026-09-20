{-# OPTIONS --cubical --safe --guardedness #-}

open import Base.Prelude
open import Base.Truth
open import Base.Classical using ( LEM )
open import FOL.ZFStructure using ( ZFStructure )
import NameKernel
import OrdinaryProfile
import GroundDescription
import CodedVocabulary
import K5.Frame
import K5.Generic
import K5.Agreement
import K9.NameGround
import K9.BooleanNameGround

module K10.CohenAgreement
  {ℓ} (𝒮 : ZFStructure (hPropAlgebra ℓ))
  (families : NameKernel.Families 𝒮)
  (accessible : NameKernel.Accessibility 𝒮)
  (images : NameKernel.MemberImage 𝒮)
  (pow : OrdinaryProfile.PowerSet 𝒮)
  (κ w : ZFStructure.S 𝒮)
  (lem : LEM ℓ)
  where

open import FOL.ZFStructure using ( module hPropStructure )
open import FOL.Syntax using ( Formula ; _∨̇_ ; ¬̇_ )
open import FOL.Semantics (hPropAlgebra ℓ) 𝒮 using ( module At )
open import FOL.ZFModel 𝒮 using ( _⊆ˢ_ )
open import CodedVocabulary 𝒮
  using ( orderAtˢ ; orderAtˢ-reading ; compatAtˢ ; compatAtˢ-reading
        ; sepAt ; sepAt-reading ; denseΔ ; refinesΔ ; compatibleΔ )
import Cubical.Data.Empty as Empty
open import Cubical.Data.Sum using ( _⊎_ ; inl ; inr )
import Cubical.HITs.PropositionalTruncation as PT
open PT using ( ∣_∣₁ )

open TruthAlgebra (hPropAlgebra ℓ)
open hPropStructure 𝒮
open At S id using ( _⊨_ )

module NG = K9.NameGround 𝒮 families accessible images pow κ w
  using ( extensional ; ≈ˢ-paths ; hasSeparation
        ; module C ; module K ; module GS ; empty-spec )
module BG = K9.BooleanNameGround 𝒮 families accessible images pow κ w lem
  using ( B ; entry-agrees ; module Base ; module IC ; module Translation )
module GD = GroundDescription 𝒮 NG.extensional NG.≈ˢ-paths
  using ( separateOf ; separateOf-spec )
module Frame = K5.Frame.Poset 𝒮 NG.C.carrier NG.C.order
  using ( _≼ᶜ_ ; compatᶜ ; ForcingBase )
open Frame using ( _≼ᶜ_ ; compatᶜ )
module FB = Frame.ForcingBase (BG.Base.codedBase lem)
  using ( ≼-refl ; i )
module GP = K5.Generic.Poset 𝒮 NG.C.carrier NG.C.order
module GI = GP.Image NG.extensional NG.≈ˢ-paths BG.B BG.IC.codedLattice
  BG.IC.codedComplement BG.IC.codedComplete (BG.Base.codedBase lem)
  using ( Uof ; module FS ; module Laws )
open GI.FS using ( Sub ; Cond ; _∈ᴾ_ ; isFilter )
module KF = K5.Agreement.Poset.Kernel.Frame 𝒮 NG.C.carrier NG.C.order
  NG.K.entry NG.K.entry-inj NG.K.Child NG.K.isPropChild
  (λ x b n h → ∣ b , h ∣₁) NG.K.child-wf NG.GS.empty NG.empty-spec
  NG.≈ˢ-paths BG.B BG.IC.codedLattice BG.IC.codedComplement
  (BG.Base.codedBase lem)

trᴮ-entries-NG : (n e : S) → (e ∈ˢ BG.Translation.trᴮ n)
  ≡ ⋁ S (λ x → ⋁ S (λ p → ⋁ ⟨ p ∈ˢ NG.C.carrier ⟩ (λ hp →
      (NG.K.entry x p ∈ˢ n)
      ⊓ (e ≈ˢ NG.K.entry (BG.Translation.trᴮ x) (fst (BG.Base.iᴷ (p , hp)))))))
trᴮ-entries-NG n e =
  BG.Translation.trᴮ-entries n e
    ∙ cong (⋁ S)
        (funExt (λ x →
          cong (⋁ S)
            (funExt (λ p →
              cong (⋁ ⟨ p ∈ˢ NG.C.carrier ⟩)
                (funExt (λ hp →
                  cong₂ _⊓_
                    (cong (_∈ˢ n) (BG.entry-agrees x p))
                    (cong (e ≈ˢ_)
                      (BG.entry-agrees (BG.Translation.trᴮ x)
                        (fst (BG.Base.iᴷ (p , hp)))))))))))

module FromGeneric (G : Sub) (fil : isFilter G)
  (meets : (d : S) → ⟨ d ⊆ˢ NG.C.carrier ⟩
         → ⟨ denseΔ NG.C.carrier NG.C.order d ⟩
         → ⟨ ⋁ Cond (λ q → (q ∈ᴾ G) ⊓ (fst q ∈ˢ d)) ⟩)
  where

  module GL = GI.Laws G using ( generic-forward ; generic-reflect-from )

  coneOrApartφ : S → Formula S 1
  coneOrApartφ p =
    sepAt (orderAtˢ (suc zero) zero (suc (suc zero))) (NG.C.order ∷ p ∷ [])
    ∨̇ ¬̇ (sepAt (compatAtˢ (suc zero) (suc (suc zero)) zero
                       (suc (suc (suc zero))))
                (NG.C.carrier ∷ NG.C.order ∷ p ∷ []))

  read₁≡ : (x p̂ : S)
    → ((x ∷ []) ⊨ sepAt (orderAtˢ (suc zero) zero (suc (suc zero)))
                        (NG.C.order ∷ p̂ ∷ []))
      ≡ refinesΔ NG.C.order x p̂
  read₁≡ x p̂ =
    sepAt-reading (orderAtˢ (suc zero) zero (suc (suc zero)))
      (NG.C.order ∷ p̂ ∷ []) x
      ∙ orderAtˢ-reading (suc zero) zero (suc (suc zero))
          (x ∷ NG.C.order ∷ p̂ ∷ [])

  read₂≡ : (x p̂ : S)
    → ((x ∷ []) ⊨ sepAt (compatAtˢ (suc zero) (suc (suc zero)) zero
                          (suc (suc (suc zero))))
                         (NG.C.carrier ∷ NG.C.order ∷ p̂ ∷ []))
      ≡ compatibleΔ NG.C.carrier NG.C.order x p̂
  read₂≡ x p̂ =
    sepAt-reading (compatAtˢ (suc zero) (suc (suc zero)) zero
      (suc (suc (suc zero)))) (NG.C.carrier ∷ NG.C.order ∷ p̂ ∷ []) x
      ∙ compatAtˢ-reading (suc zero) (suc (suc zero)) zero
          (suc (suc (suc zero)))
          (x ∷ NG.C.carrier ∷ NG.C.order ∷ p̂ ∷ [])

  coneOrApart : Cond → S
  coneOrApart p = GD.separateOf NG.hasSeparation NG.C.carrier (coneOrApartφ (fst p))

  coneOrApart-in : (p : Cond) (s : S) → ⟨ s ∈ˢ NG.C.carrier ⟩
    → (⟨ refinesΔ NG.C.order s (fst p) ⟩
       ⊎ (⟨ compatibleΔ NG.C.carrier NG.C.order s (fst p) ⟩ → ⊥* {ℓ}))
    → ⟨ s ∈ˢ coneOrApart p ⟩
  coneOrApart-in p s hcar (inl h) =
    subst ⟨_⟩ (sym (GD.separateOf-spec NG.hasSeparation NG.C.carrier
                      (coneOrApartφ (fst p)) s))
      (hcar , ∣ inl (subst ⟨_⟩ (sym (read₁≡ s (fst p))) h) ∣₁)
  coneOrApart-in p s hcar (inr h) =
    subst ⟨_⟩ (sym (GD.separateOf-spec NG.hasSeparation NG.C.carrier
                      (coneOrApartφ (fst p)) s))
      (hcar , ∣ inr (λ hc → h (subst ⟨_⟩ (read₂≡ s (fst p)) hc)) ∣₁)

  coneOrApart-sub : (p : Cond) → ⟨ coneOrApart p ⊆ˢ NG.C.carrier ⟩
  coneOrApart-sub p x hx =
    fst (subst ⟨_⟩
      (GD.separateOf-spec NG.hasSeparation NG.C.carrier (coneOrApartφ (fst p)) x) hx)

  coneOrApart-spec : (p q : Cond) → ⟨ fst q ∈ˢ coneOrApart p ⟩
    → ⟨ (fst q ≼ᶜ fst p) ⊔ (compatᶜ q p ⇒ ⊥) ⟩
  coneOrApart-spec p q h = PT.rec (snd target) atDisj sat
    where
    d₁ : Formula S 1
    d₁ = sepAt (orderAtˢ (suc zero) zero (suc (suc zero)))
               (NG.C.order ∷ fst p ∷ [])
    d₂ : Formula S 1
    d₂ = sepAt (compatAtˢ (suc zero) (suc (suc zero)) zero (suc (suc (suc zero))))
               (NG.C.carrier ∷ NG.C.order ∷ fst p ∷ [])
    pair : ⟨ fst q ∈ˢ NG.C.carrier ⟩ × ⟨ (fst q ∷ []) ⊨ coneOrApartφ (fst p) ⟩
    pair = subst ⟨_⟩
      (GD.separateOf-spec NG.hasSeparation NG.C.carrier (coneOrApartφ (fst p)) (fst q)) h
    sat : ⟨ (fst q ∷ []) ⊨ coneOrApartφ (fst p) ⟩
    sat = snd pair
    target : Ω
    target = (fst q ≼ᶜ fst p) ⊔ (compatᶜ q p ⇒ ⊥)
    atDisj : (⟨ (fst q ∷ []) ⊨ d₁ ⟩
              ⊎ ⟨ (fst q ∷ []) ⊨ ¬̇ d₂ ⟩)
            → ⟨ target ⟩
    atDisj (inl hd) = ∣ inl (subst ⟨_⟩ (read₁≡ (fst q) (fst p)) hd) ∣₁
    atDisj (inr hd) =
      ∣ inr (λ hc → hd (subst ⟨_⟩ (sym (read₂≡ (fst q) (fst p))) hc)) ∣₁

  coneOrApart-dense : (p : Cond)
    → ⟨ denseΔ NG.C.carrier NG.C.order (coneOrApart p) ⟩
  coneOrApart-dense p q hq =
    decide (lem (compatibleΔ NG.C.carrier NG.C.order q (fst p)))
    where
    decide : (⟨ compatibleΔ NG.C.carrier NG.C.order q (fst p) ⟩
              ⊎ (⟨ compatibleΔ NG.C.carrier NG.C.order q (fst p) ⟩ → Empty.⊥))
           → ⟨ ⋁ S (λ r → (r ∈ˢ coneOrApart p) ⊓ refinesΔ NG.C.order r q) ⟩
    decide (inl hcompat) =
      PT.rec (snd (⋁ S (λ r → (r ∈ˢ coneOrApart p) ⊓ refinesΔ NG.C.order r q)))
        (λ { (r , hrc , hrq , hrp) →
              ∣ r , coneOrApart-in p r hrc (inl hrp) , hrq ∣₁ })
        hcompat
    decide (inr hnc) =
      ∣ q , coneOrApart-in p q hq (inr (λ hc → lift (hnc hc))) , FB.≼-refl q hq ∣₁

  generic-reflect : (p : Cond) → ⟨ GI.Uof G (FB.i p) ⟩ → ⟨ p ∈ᴾ G ⟩
  generic-reflect p hu =
    GL.generic-reflect-from fil p
      (PT.map (λ { (s , hsG , hs∈) → s , hsG , coneOrApart-spec p s hs∈ })
        (meets (coneOrApart p) (coneOrApart-sub p) (coneOrApart-dense p)))
      hu

  module KT = KF.Translation BG.Translation.trᴮ trᴮ-entries-NG
  module AG = KT.Agree G (GI.Uof G) GL.generic-forward generic-reflect
  open AG using ( _≈[G]_ ; _∈[G]_ ; _≈[U]_ ; _∈[U]_ )

  ≈-agree : (m n : S)
    → (m ≈[G] n) ≡ (BG.Translation.trᴮ m ≈[U] BG.Translation.trᴮ n)
  ≈-agree = AG.≈-agree

  ∈-agree : (m n : S)
    → (m ∈[G] n) ≡ (BG.Translation.trᴮ m ∈[U] BG.Translation.trᴮ n)
  ∈-agree = AG.∈-agree
