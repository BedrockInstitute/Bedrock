{-# OPTIONS --cubical --safe --guardedness #-}

open import Base.Prelude
open import Base.Truth
open import FOL.ZFStructure using ( ZFStructure )
import OrdinaryProfile

module K8.CodedCCCTransfer
  {ℓ} (𝒮 : ZFStructure (hPropAlgebra ℓ))
  (ext : OrdinaryProfile.Extensionality 𝒮)
  (paths : (x y : ZFStructure.S 𝒮)
    → ZFStructure._≈ˢ_ 𝒮 x y ≡ ((x ≡ y) , ZFStructure.isSetS 𝒮 x y))
  (pair : OrdinaryProfile.Pairing 𝒮)
  (un : OrdinaryProfile.Union 𝒮)
  (pow : OrdinaryProfile.PowerSet 𝒮)
  (sep : OrdinaryProfile.Separation 𝒮)
  (coll : OrdinaryProfile.Collection 𝒮)
  (find : OrdinaryProfile.FoundationInduction 𝒮)
  (seed : ZFStructure.S 𝒮)
  where

open import FOL.ZFStructure using ( module hPropStructure )
open import FOL.Syntax
  using ( Formula; Term; var; con; _∈̇_; _∧̇_; _⇒̇_; ∀̇_ )
open import FOL.Semantics (hPropAlgebra ℓ) 𝒮 using ( module At )
open import CodedVocabulary 𝒮
  using ( subsetΔ; refinesΔ; coneΔ; coneAtˢ
        ; positiveAtˢ; positiveAtˢ-reading; positiveΔ-simp
        ; sepAt; sepAt-reading )
open import OrdinaryProfile 𝒮 using ( ChoiceSet )
open import Cubical.Functions.Logic using ( ⇔toPath )
import Cubical.HITs.PropositionalTruncation as PT
open PT using ( ∣_∣₁ )
import CodedCompletion
import CodedVocabulary
import K7.ChainConditions
import K8.CCCTransfer
import K8.GroundSets
import K8.SubsetOrder

open TruthAlgebra (hPropAlgebra ℓ)
open hPropStructure 𝒮
open At S id using ( _⊨_ )

module GS = K8.GroundSets.Ground 𝒮 ext paths pair un pow sep seed
module SO = K8.SubsetOrder 𝒮 ext paths pair un pow sep seed
module CC = CodedCompletion 𝒮
module CH = K7.ChainConditions 𝒮 ext paths
module TR = K8.CCCTransfer 𝒮 ext paths pair un pow sep coll find seed
module CV = CodedVocabulary 𝒮

module AtPresentation
  (choice : ChoiceSet)
  (𝔓 : CC.Presentation)
  (laws : CC.Coded.ForcingLaws 𝔓)
  (w : S)
  where

  module P = CC.Coded 𝔓
  module R = CC.Core ext pow sep paths 𝔓 laws

  positiveFormula : Formula S 1
  positiveFormula = positiveAtˢ zero

  positive-reading : (u : S)
    → ((u ∷ []) ⊨ positiveFormula) ≡ ⋁ S (λ q → q ∈ˢ u)
  positive-reading u = positiveAtˢ-reading zero (u ∷ []) ∙ positiveΔ-simp u

  opaque
    B⁺set : S
    B⁺set = GS.separator R.B positiveFormula

    B⁺-spec : (u : S) → (u ∈ˢ B⁺set)
      ≡ ((u ∈ˢ R.B) ⊓ ⋁ S (λ q → q ∈ˢ u))
    B⁺-spec u = GS.separator-spec R.B positiveFormula u
      ∙ cong ((u ∈ˢ R.B) ⊓_) (positive-reading u)

  order⁺ : S
  order⁺ = SO.order B⁺set

  img : S → S
  img = R.iSet

  img-in : (p : S) → ⟨ p ∈ˢ P.carrier ⟩ → ⟨ img p ∈ˢ B⁺set ⟩
  img-in p hp = subst ⟨_⟩ (sym (B⁺-spec (img p)))
    (R.iSet-inB p , R.i-pos (p , hp))

  img-mono : (r p : S) → ⟨ r ∈ˢ P.carrier ⟩ → ⟨ p ∈ˢ P.carrier ⟩
    → ⟨ refinesΔ P.order r p ⟩ → ⟨ refinesΔ order⁺ (img r) (img p) ⟩
  img-mono r p hr hp h = SO.refines-backward B⁺set (img r) (img p)
    (img-in r hr) (img-in p hp) (R.i-mono (p , hp) (r , hr) h)

  coneFo : Formula S 3
  coneFo = CV.instFo emb
    (coneAtˢ zero (suc zero) (suc (suc zero)) (suc (suc (suc zero))))
    where
    emb : Fin 4 → Term S 3
    emb zero = con P.carrier
    emb (suc zero) = con P.order
    emb (suc (suc zero)) = var (suc zero)
    emb (suc (suc (suc zero))) = var zero

  coneFo-reading : (x p u : S) → ((x ∷ p ∷ u ∷ []) ⊨ coneFo)
    ≡ coneΔ P.carrier P.order p x
  coneFo-reading x p u = CV.⊨-inst emb
    (coneAtˢ zero (suc zero) (suc (suc zero)) (suc (suc (suc zero))))
    (x ∷ p ∷ u ∷ []) (P.carrier ∷ P.order ∷ p ∷ x ∷ []) fits
    where
    emb : Fin 4 → Term S 3
    emb zero = con P.carrier
    emb (suc zero) = con P.order
    emb (suc (suc zero)) = var (suc zero)
    emb (suc (suc (suc zero))) = var zero
    fits : CV.Fits emb (x ∷ p ∷ u ∷ []) (P.carrier ∷ P.order ∷ p ∷ x ∷ [])
    fits zero = refl
    fits (suc zero) = refl
    fits (suc (suc zero)) = refl
    fits (suc (suc (suc zero))) = refl

  belowBody : Formula S 3
  belowBody = ((var zero ∈̇ con P.carrier)
    ∧̇ coneFo)
    ⇒̇ (var zero ∈̇ var (suc (suc zero)))

  subsetFo : Formula S 2
  subsetFo = ∀̇ belowBody

  subsetFo-reading : (u p : S) → ((p ∷ u ∷ []) ⊨ subsetFo)
    ≡ subsetΔ (img p) u
  subsetFo-reading u p = cong (⋀ S) (funExt λ x →
    cong (λ z → z ⇒ (x ∈ˢ u))
      (cong ((x ∈ˢ P.carrier) ⊓_) (coneFo-reading x p u)
        ∙ sym (R.iSet-mem p x)))

  belowFo : Formula S 2
  belowFo = (var zero ∈̇ con P.carrier)
    ∧̇ ((var (suc zero) ∈̇ con B⁺set) ∧̇ subsetFo)

  belowFormula : S → Formula S 1
  belowFormula u = sepAt belowFo (u ∷ [])

  opaque
    below : S → S
    below u = GS.separator P.carrier (belowFormula u)

    below-spec : (u p : S) → (p ∈ˢ below u)
      ≡ ((p ∈ˢ P.carrier) ⊓
          ((p ∈ˢ P.carrier) ⊓ ((u ∈ˢ B⁺set) ⊓ subsetΔ (img p) u)))
    below-spec u p = GS.separator-spec P.carrier (belowFormula u) p
      ∙ cong ((p ∈ˢ P.carrier) ⊓_) (sepAt-reading belowFo (u ∷ []) p)
      ∙ cong ((p ∈ˢ P.carrier) ⊓_)
          (cong ((p ∈ˢ P.carrier) ⊓_)
            (cong ((u ∈ˢ B⁺set) ⊓_) (subsetFo-reading u p)))

  belowFo-reading : (u p : S) → ((p ∷ u ∷ []) ⊨ belowFo) ≡ (p ∈ˢ below u)
  belowFo-reading u p = ⇔toPath
    (λ h → subst ⟨_⟩ (sym (below-spec u p))
      (h .fst , h .fst , h .snd .fst ,
        subst ⟨_⟩ (subsetFo-reading u p) (h .snd .snd)))
    (λ h → let parts = subst ⟨_⟩ (below-spec u p) h in
      parts .snd .fst , parts .snd .snd .fst ,
        subst ⟨_⟩ (sym (subsetFo-reading u p)) (parts .snd .snd .snd))

  below-sub : (u p : S) → ⟨ p ∈ˢ below u ⟩ → ⟨ p ∈ˢ P.carrier ⟩
  below-sub u p h = subst ⟨_⟩ (below-spec u p) h .fst

  below-refines : (u p : S) → ⟨ p ∈ˢ below u ⟩
    → ⟨ refinesΔ order⁺ (img p) u ⟩
  below-refines u p h = SO.refines-backward B⁺set (img p) u
    (img-in p hp) hu sub
    where
    parts : ⟨ (p ∈ˢ P.carrier) ⊓
      ((p ∈ˢ P.carrier) ⊓ ((u ∈ˢ B⁺set) ⊓ subsetΔ (img p) u)) ⟩
    parts = subst ⟨_⟩ (below-spec u p) h
    hp = parts .fst
    sub = parts .snd .snd .snd
    hu : ⟨ u ∈ˢ B⁺set ⟩
    hu = parts .snd .snd .fst

  endpoints : (u v : S) → ⟨ refinesΔ order⁺ u v ⟩
    → ⟨ (u ∈ˢ B⁺set) ⊓ (v ∈ˢ B⁺set) ⟩
  endpoints u v = PT.rec (snd ((u ∈ˢ B⁺set) ⊓ (v ∈ˢ B⁺set))) λ
    { (z , hz , kp) → PT.rec (snd ((u ∈ˢ B⁺set) ⊓ (v ∈ˢ B⁺set)))
      (λ { (u' , v' , hu' , hv' , kp' , _) →
        let eq = GS.ordered-components z u v u' v' kp kp' in
        subst (λ t → ⟨ t ∈ˢ B⁺set ⟩) (sym (fst eq)) hu' ,
        subst (λ t → ⟨ t ∈ˢ B⁺set ⟩) (sym (snd eq)) hv' })
      (SO.order-out B⁺set z hz) }

  refines⁺-trans : (u v z : S) → ⟨ refinesΔ order⁺ u v ⟩
    → ⟨ refinesΔ order⁺ v z ⟩ → ⟨ refinesΔ order⁺ u z ⟩
  refines⁺-trans u v z huv hvz = SO.refines-backward B⁺set u z hu hz
    (λ x hx → svz x (suv x hx))
    where
    hu : ⟨ u ∈ˢ B⁺set ⟩
    hu = endpoints u v huv .fst
    hz : ⟨ z ∈ˢ B⁺set ⟩
    hz = endpoints v z hvz .snd
    suv : ⟨ subsetΔ u v ⟩
    suv = SO.refines-forward B⁺set u v hu (endpoints u v huv .snd) huv
    svz : ⟨ subsetΔ v z ⟩
    svz = SO.refines-forward B⁺set v z (endpoints v z hvz .fst) hz hvz

  dense : (u : S) → ⟨ u ∈ˢ B⁺set ⟩
    → ⟨ ⋁ S (λ p → (p ∈ˢ P.carrier) ⊓ ((p ∷ u ∷ []) ⊨ belowFo)) ⟩
  dense u hu = PT.map
    (λ { ((p , hp) , sub) → p , hp ,
      subst ⟨_⟩ (sym (belowFo-reading u p))
        (subst ⟨_⟩ (sym (below-spec u p)) (hp , hp , hu , sub)) })
    (R.i-dense (u , bu) pos)
    where
    parts = subst ⟨_⟩ (B⁺-spec u) hu
    bu = parts .fst
    pos = parts .snd

  transfer : ⟨ CH.CCC₂ᴵ P.carrier P.order w ⟩
    → ⟨ CH.CCC₂ᴵ B⁺set order⁺ w ⟩
  transfer = T.ccc-transfer
    where
    module T = TR.Transfer choice P.carrier P.order B⁺set order⁺ w
      img img-in img-mono below below-sub below-refines refines⁺-trans
      belowFo belowFo-reading dense
