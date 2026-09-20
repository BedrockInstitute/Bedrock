{-# OPTIONS --cubical --safe --guardedness #-}

open import Base.Prelude
open import Base.Truth
open import Base.Classical using ( LEM )
open import FOL.ZFStructure using ( ZFStructure )
import OrdinaryProfile
import CardinalBridge

module K8.DistinctDense
  {ℓ} (𝒮 : ZFStructure (hPropAlgebra ℓ))
  (ext : OrdinaryProfile.Extensionality 𝒮)
  (paths : (x y : ZFStructure.S 𝒮)
    → ZFStructure._≈ˢ_ 𝒮 x y ≡ ((x ≡ y) , ZFStructure.isSetS 𝒮 x y))
  (pair : OrdinaryProfile.Pairing 𝒮)
  (un : OrdinaryProfile.Union 𝒮)
  (pow : OrdinaryProfile.PowerSet 𝒮)
  (sep : OrdinaryProfile.Separation 𝒮)
  (find : OrdinaryProfile.FoundationInduction 𝒮)
  (κ w : ZFStructure.S 𝒮)
  (hw : ⟨ CardinalBridge.isOmega 𝒮 w ⟩)
  where

open import FOL.ZFStructure using ( module hPropStructure )
open import FOL.Syntax
  using ( Formula; var; _∈̇_; _≐_; _∧̇_; ¬̇_; ∃̇∈ )
open import FOL.Semantics (hPropAlgebra ℓ) 𝒮 using ( module At )
open import FOL.LevyHierarchy using ( Δ₀; checkΔ₀ )
open import Cubical.Data.Unit using ( tt )
open import CodedVocabulary 𝒮
  using ( isKPairΔ; prAtˢ; refinesΔ; orderAtˢ; denseΔ; subsetΔ
        ; sepAt; sepAt-reading; Δ₀-sepAt )
import K8.Cohen
import K8.GroundSets
import K8.PartialMaps
import K8.MapOperations
import K8.DomainFinite
import K8.RangeFinite
import K8.OmegaFinite
import K8.FiniteVocabulary
import K8.MapVocabulary
open import Cubical.Data.Sum using ( _⊎_ ) renaming ( inl to inl⊎; inr to inr⊎ )
import Cubical.Data.Empty as Empty
import Cubical.HITs.PropositionalTruncation as PT
open PT using ( ∥_∥₁; ∣_∣₁ )

open TruthAlgebra (hPropAlgebra ℓ)
open hPropStructure 𝒮
open At S id using ( _⊨_ )

module C = K8.Cohen 𝒮 ext paths pair un pow sep κ w
module GS = K8.GroundSets.Ground 𝒮 ext paths pair un pow sep κ
module PM = K8.PartialMaps.Maps 𝒮 ext paths pair un pow sep κ C.coordinates C.two
module MO = K8.MapOperations.Operations 𝒮 ext paths pair un pow sep κ C.coordinates C.two
module DF = K8.DomainFinite 𝒮 ext paths pair un pow sep κ C.coordinates C.two
module RF = K8.RangeFinite 𝒮 ext paths pair un pow sep κ κ w
module OF = K8.OmegaFinite 𝒮 ext paths pair un pow sep find κ

unequalPred : S → S → S → Ω
unequalPred α β p = ⋁ S (λ n → (n ∈ˢ w) ⊓
  ⋁ S (λ u → (u ∈ˢ C.coordinates) ⊓
  ⋁ S (λ v → (v ∈ˢ C.coordinates) ⊓
    (isKPairΔ u α n ⊓ (isKPairΔ v β n ⊓
      ⋁ S (λ b → (b ∈ˢ C.two) ⊓
      ⋁ S (λ c → (c ∈ˢ C.two) ⊓
        (refinesΔ p u b ⊓ (refinesΔ p v c ⊓ ((b ≈ˢ c) ⇒ ⊥))))))))))

valuesBody : Formula S 11
valuesBody =
  (orderAtˢ (suc (suc (suc (suc (suc zero)))))
    (suc (suc (suc zero))) (suc zero)) ∧̇
  ((orderAtˢ (suc (suc (suc (suc (suc zero)))))
    (suc (suc zero)) zero) ∧̇ ¬̇ (var (suc zero) ≐ var zero))

valuesAt : Formula S 9
valuesAt =
  ∃̇∈ (var (suc (suc (suc (suc (suc (suc (suc (suc zero)))))))))
    (∃̇∈ (var (suc (suc (suc (suc (suc (suc (suc (suc (suc zero))))))))))
      valuesBody)

unequalAt : Formula S 6
unequalAt =
  ∃̇∈ (var (suc (suc (suc zero))))
    (∃̇∈ (var (suc (suc (suc (suc (suc zero))))))
      (∃̇∈ (var (suc (suc (suc (suc (suc (suc zero)))))))
        ((prAtˢ (suc zero) (suc (suc (suc (suc zero)))) (suc (suc zero))) ∧̇
         ((prAtˢ zero (suc (suc (suc (suc (suc zero))))) (suc (suc zero))) ∧̇
          valuesAt))))

unequal-bounded : Δ₀ unequalAt
unequal-bounded = checkΔ₀ unequalAt tt

EFormula : S → S → Formula S 1
EFormula α β = sepAt unequalAt (α ∷ β ∷ w ∷ C.coordinates ∷ C.two ∷ [])

EFormula-bounded : (α β : S) → Δ₀ (EFormula α β)
EFormula-bounded α β = Δ₀-sepAt unequal-bounded
  (α ∷ β ∷ w ∷ C.coordinates ∷ C.two ∷ [])

EFormula-reading : (α β p : S)
  → ((p ∷ []) ⊨ EFormula α β) ≡ unequalPred α β p
EFormula-reading α β p = sepAt-reading unequalAt
  (α ∷ β ∷ w ∷ C.coordinates ∷ C.two ∷ []) p

opaque
  E : S → S → S
  E α β = GS.separator C.carrier (EFormula α β)

  E-spec : (α β p : S)
    → (p ∈ˢ E α β) ≡ ((p ∈ˢ C.carrier) ⊓ unequalPred α β p)
  E-spec α β p = GS.separator-spec C.carrier (EFormula α β) p
    ∙ cong ((p ∈ˢ C.carrier) ⊓_) (EFormula-reading α β p)

E-dense : LEM ℓ → (α β : S) → ⟨ α ∈ˢ κ ⟩ → ⟨ β ∈ˢ κ ⟩
  → (⟨ α ≈ˢ β ⟩ → ⟨ ⊥ ⟩) → ⟨ denseΔ C.carrier C.order (E α β) ⟩
E-dense lem α β hα hβ α≠β p hp = PT.rec (snd goal) build omitted
  where
  goal : Ω
  goal = ⋁ S (λ q → (q ∈ˢ E α β) ⊓ refinesΔ C.order q p)

  pFinite : ⟨ K8.FiniteVocabulary.finiteIn 𝒮 PM.W p ⟩
  pFinite = fst (subst ⟨_⟩ (PM.carrier-spec p) hp)

  domainFinite : ⟨ K8.FiniteVocabulary.finiteIn 𝒮 C.coordinates (PM.domain p) ⟩
  domainFinite = DF.domain-finite p pFinite

  naturalFinite : ⟨ K8.FiniteVocabulary.finiteIn 𝒮 w (RF.range (PM.domain p)) ⟩
  naturalFinite = RF.range-finite (PM.domain p) domainFinite

  omitted : ∥ Σ[ n ∈ S ] (⟨ n ∈ˢ w ⟩ ×
    (⟨ n ∈ˢ RF.range (PM.domain p) ⟩ → Empty.⊥)) ∥₁
  omitted = OF.finite-omits lem w hw (RF.range (PM.domain p)) naturalFinite

  build : Σ[ n ∈ S ] (⟨ n ∈ˢ w ⟩ ×
    (⟨ n ∈ˢ RF.range (PM.domain p) ⟩ → Empty.⊥)) → ⟨ goal ⟩
  build (n , hn , nFresh) = ∣ q , qE , q≤p ∣₁
    where
    u v : S
    u = C.coordinate α n
    v = C.coordinate β n

    hu : ⟨ u ∈ˢ C.coordinates ⟩
    hu = C.coordinate-in α n hα hn
    hv : ⟨ v ∈ˢ C.coordinates ⟩
    hv = C.coordinate-in β n hβ hn

    freshP : (z γ : S) → ⟨ γ ∈ˢ κ ⟩ → ⟨ isKPairΔ z γ n ⟩
      → ⟨ z ∈ˢ PM.domain p ⟩ → Empty.⊥
    freshP z γ hγ kp hz = nFresh
      (RF.range-in (PM.domain p) γ n hγ hn ∣ z , hz , kp ∣₁)

    uFresh : ⟨ u ∈ˢ PM.domain p ⟩ → ⟨ ⊥ ⟩
    uFresh h = Empty.rec (freshP u α hα (GS.ordered-witness α n) h)

    vFreshP : ⟨ v ∈ˢ PM.domain p ⟩ → Empty.⊥
    vFreshP = freshP v β hβ (GS.ordered-witness β n)

    r : S
    r = MO.insert p u C.bit₀

    hr : ⟨ r ∈ˢ C.carrier ⟩
    hr = MO.insert-in-carrier p u C.bit₀ hp hu C.bit₀-in uFresh

    u≠v : u ≡ v → Empty.⊥
    u≠v eq = Empty.rec* (α≠β (subst ⟨_⟩ (sym (paths α β))
      (fst (GS.ordered-components v α n β n
        (subst (λ z → ⟨ isKPairΔ z α n ⟩) eq (GS.ordered-witness α n))
        (GS.ordered-witness β n)))))

    vFreshR : ⟨ v ∈ˢ PM.domain r ⟩ → ⟨ ⊥ ⟩
    vFreshR h = Empty.rec (PT.rec Empty.isProp⊥ atBit (snd data'))
      where
      data' : ⟨ (v ∈ˢ C.coordinates) ⊓ K8.MapVocabulary.domainPred 𝒮 C.two r v ⟩
      data' = subst ⟨_⟩ (PM.domain-spec r v) h

      atBit : Σ[ b ∈ S ] (⟨ b ∈ˢ C.two ⟩ × ⟨ refinesΔ r v b ⟩) → Empty.⊥
      atBit (b , hb , ev) = PT.rec Empty.isProp⊥ branch
        (subst ⟨_⟩ (MO.join-refines p (MO.point u C.bit₀) v b) ev)
        where
        branch : ⟨ refinesΔ p v b ⟩ ⊎ ⟨ refinesΔ (MO.point u C.bit₀) v b ⟩
          → Empty.⊥
        branch (inl⊎ old) = vFreshP (PM.domain-in p v b hv hb old)
        branch (inr⊎ new) = u≠v (sym (fst (MO.point-components u C.bit₀ v b new)))

    q : S
    q = MO.insert r v C.bit₁

    hq : ⟨ q ∈ˢ C.carrier ⟩
    hq = MO.insert-in-carrier r v C.bit₁ hr hv C.bit₁-in vFreshR

    evalU : ⟨ refinesΔ q u C.bit₀ ⟩
    evalU = MO.refines-mono r q u C.bit₀ (MO.insert-extends r v C.bit₁)
      (MO.insert-evaluates p u C.bit₀)

    evalV : ⟨ refinesΔ q v C.bit₁ ⟩
    evalV = MO.insert-evaluates r v C.bit₁

    witness : ⟨ unequalPred α β q ⟩
    witness = ∣ n , hn , ∣ u , hu , ∣ v , hv ,
      GS.ordered-witness α n , GS.ordered-witness β n ,
      ∣ C.bit₀ , C.bit₀-in , ∣ C.bit₁ , C.bit₁-in ,
        evalU , evalV , C.bits-distinct ∣₁ ∣₁ ∣₁ ∣₁ ∣₁

    qE : ⟨ q ∈ˢ E α β ⟩
    qE = subst ⟨_⟩ (sym (E-spec α β q)) (hq , witness)

    p⊆q : ⟨ subsetΔ p q ⟩
    p⊆q z hz = MO.insert-extends r v C.bit₁ z (MO.insert-extends p u C.bit₀ z hz)

    q≤p : ⟨ refinesΔ C.order q p ⟩
    q≤p = subst ⟨_⟩ (sym (C.PC.refines-spec q p hq hp)) p⊆q
