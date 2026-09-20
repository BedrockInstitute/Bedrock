{-# OPTIONS --cubical --safe --guardedness #-}

open import Base.Prelude
open import Base.Truth
open import FOL.ZFStructure using ( ZFStructure )
open import Cubical.Induction.WellFounded using ( Acc; acc )
import OrdinaryProfile

module CheckRecursion
  {ℓ} (𝒮 : ZFStructure (hPropAlgebra ℓ))
  (ext : OrdinaryProfile.Extensionality 𝒮)
  (paths : (x y : ZFStructure.S 𝒮)
    → ZFStructure._≈ˢ_ 𝒮 x y ≡ ((x ≡ y) , ZFStructure.isSetS 𝒮 x y))
  (wf : (x : ZFStructure.S 𝒮) →
    let open ZFStructure 𝒮 in
    Acc (λ y z → ⟨ y ∈ˢ z ⟩) x)
  (w : ZFStructure.S 𝒮)
  where

open import FOL.ZFStructure using ( module hPropStructure )
open import FOL.Syntax using
  ( Formula; var; con; _∈̇_; _∧̇_; _⇒̇_; ∀̇_; ∀̇∈; ∃̇_; ∃̇∈ )
open import FOL.Semantics (hPropAlgebra ℓ) 𝒮 using ( module At; _^_ )
open import CodedVocabulary 𝒮 using ( isKPairΔ; prAtˢ; refinesΔ; orderAtˢ )
open import OrdinaryProfile 𝒮 using ( iff )
open import Cubical.Functions.Logic using ( ⇔toPath )
import Cubical.HITs.PropositionalTruncation as PT
open PT using ( ∣_∣₁ )
open import GroundDescription 𝒮 ext paths using ( ext-path )

open TruthAlgebra (hPropAlgebra ℓ)
open hPropStructure 𝒮
open At S id using ( _⊨_ )

Ref : S → S → S → Ω
Ref = refinesΔ

Weighted : S → S → S → Ω
Weighted F x z = ⋁ S (λ u → (u ∈ˢ x) ⊓
  ⋁ S (λ t → Ref F u t ⊓ isKPairΔ z t w))

Local : S → S → S → Ω
Local F x v =
  (⋀ S (λ u → (u ∈ˢ x) ⇒ ⋁ S (λ t → Ref F u t))) ⊓
  (⋀ S (λ z → iff (z ∈ˢ v) (Weighted F x z)))

Good : S → Ω
Good F = ⋀ S (λ x → ⋀ S (λ v → Ref F x v ⇒ Local F x v))

weightedFo : ∀ {n} → Fin n → Fin n → Fin n → Fin n → Formula S n
weightedFo F x z b = ∃̇∈ (var x) (∃̇
  (orderAtˢ (suc (suc F)) (suc zero) zero ∧̇
   prAtˢ (suc (suc z)) zero (suc (suc b))))

localFo : ∀ {n} → Fin n → Fin n → Fin n → Fin n → Formula S n
localFo F x v b =
  (∀̇∈ (var x) (∃̇ (orderAtˢ (suc (suc F)) (suc zero) zero))) ∧̇
  (∀̇ (((var zero ∈̇ var (suc v)) ⇒̇
          weightedFo (suc F) (suc x) zero (suc b)) ∧̇
       (weightedFo (suc F) (suc x) zero (suc b) ⇒̇
          (var zero ∈̇ var (suc v)))))

goodFo : ∀ {n} → Fin n → Fin n → Formula S n
goodFo F b = ∀̇ (∀̇
  (orderAtˢ (suc (suc F)) (suc zero) zero ⇒̇
   localFo (suc (suc F)) (suc zero) zero (suc (suc b))))

good-reading : ∀ {n} (F b : Fin n) (γ : S ^ n)
  → lookup b γ ≡ w → (γ ⊨ goodFo F b) ≡ Good (lookup F γ)
good-reading F b γ e = cong
  (λ weight → ⋀ S (λ x → ⋀ S (λ v → Ref (lookup F γ) x v ⇒
    ((⋀ S (λ u → (u ∈ˢ x) ⇒ ⋁ S (λ t → Ref (lookup F γ) u t))) ⊓
     (⋀ S (λ z → iff (z ∈ˢ v)
       (⋁ S (λ u → (u ∈ˢ x) ⊓ ⋁ S (λ t →
         Ref (lookup F γ) u t ⊓ isKPairΔ z t weight))))))))) e

local-unique : (F x v t : S) → ⟨ Local F x v ⟩ → ⟨ Local F x t ⟩ → v ≡ t
local-unique F x v t lv lt = ext-path λ z →
  ⇔toPath (λ h → lt .snd z .snd (lv .snd z .fst h))
          (λ h → lv .snd z .snd (lt .snd z .fst h))

agree-acc : (x : S) → Acc (λ y z → ⟨ y ∈ˢ z ⟩) x
  → (F G v t : S) → ⟨ Good F ⟩ → ⟨ Good G ⟩
  → ⟨ Ref F x v ⟩ → ⟨ Ref G x t ⟩ → v ≡ t
agree-acc x (acc below) F G v t gf gg fv gt = ext-path λ z →
  ⇔toPath (transfer F G v t gf gg fv gt z) (transfer G F t v gg gf gt fv z)
  where
  transfer : (A B r s : S) → ⟨ Good A ⟩ → ⟨ Good B ⟩
    → ⟨ Ref A x r ⟩ → ⟨ Ref B x s ⟩
    → (z : S) → ⟨ z ∈ˢ r ⟩ → ⟨ z ∈ˢ s ⟩
  transfer A B r s ga gb ar bs z hz = gb x s bs .snd z .snd
    (PT.rec (snd (Weighted B x z))
      (λ { (u , hu , rest) → PT.rec (snd (Weighted B x z))
        (λ { (q , aq , kp) → PT.rec (snd (Weighted B x z))
          (λ { (q' , bq) → ∣ u , hu , ∣ q' , bq ,
            subst (λ j → ⟨ isKPairΔ z j w ⟩)
              (agree-acc u (below u hu) A B q q' ga gb aq bq) kp ∣₁ ∣₁ })
          (gb x s bs .fst u hu) }) rest })
      (ga x r ar .snd z .fst hz))

agree : (F G x v t : S) → ⟨ Good F ⟩ → ⟨ Good G ⟩
  → ⟨ Ref F x v ⟩ → ⟨ Ref G x t ⟩ → v ≡ t
agree F G x = agree-acc x (wf x) F G

local-transport : (F G x v : S)
  → ((u t : S) → ⟨ u ∈ˢ x ⟩ → ⟨ Ref F u t ⟩ → ⟨ Ref G u t ⟩)
  → ((u t : S) → ⟨ u ∈ˢ x ⟩ → ⟨ Ref G u t ⟩ → ⟨ Ref F u t ⟩)
  → ⟨ Local F x v ⟩ → ⟨ Local G x v ⟩
local-transport F G x v forward backward local =
  (λ u hu → PT.map (λ { (t , ft) → t , forward u t hu ft }) (local .fst u hu)) ,
  λ z → (λ h → map-weighted F G forward z (local .snd z .fst h)) ,
        (λ h → local .snd z .snd (map-weighted G F backward z h))
  where
  map-weighted : (A B : S)
    → ((u t : S) → ⟨ u ∈ˢ x ⟩ → ⟨ Ref A u t ⟩ → ⟨ Ref B u t ⟩)
    → (z : S) → ⟨ Weighted A x z ⟩ → ⟨ Weighted B x z ⟩
  map-weighted A B inc z = PT.map λ { (u , hu , rest) →
    u , hu , PT.map (λ { (t , ht , kp) → t , inc u t hu ht , kp }) rest }

module Unions (un : OrdinaryProfile.Union 𝒮) where

  open import GroundDescription 𝒮 ext paths using ( the; the-spec )

  unionClass : S → S → Ω
  unionClass B e = ⋁ S (λ F → (F ∈ˢ B) ⊓ (e ∈ˢ F))

  union : S → S
  union B = the (unionClass B) (un B)

  union-spec : (B e : S) → (e ∈ˢ union B) ≡ unionClass B e
  union-spec B = the-spec (unionClass B) (un B)

  ref-in : (B F x v : S) → ⟨ F ∈ˢ B ⟩ → ⟨ Ref F x v ⟩ → ⟨ Ref (union B) x v ⟩
  ref-in B F x v hF = PT.map λ { (e , he , kp) → e ,
    subst ⟨_⟩ (sym (union-spec B e)) ∣ F , hF , he ∣₁ , kp }

  ref-out : (B x v : S) → ⟨ Ref (union B) x v ⟩
    → ⟨ ⋁ S (λ F → (F ∈ˢ B) ⊓ Ref F x v) ⟩
  ref-out B x v = PT.rec PT.squash₁ λ { (e , he , kp) →
    PT.map (λ { (F , hF , heF) → F , hF , ∣ e , heF , kp ∣₁ })
      (subst ⟨_⟩ (union-spec B e) he) }

  good-union : (B : S) → ((F : S) → ⟨ F ∈ˢ B ⟩ → ⟨ Good F ⟩) → ⟨ Good (union B) ⟩
  good-union B good x v ref = PT.rec (snd (Local (union B) x v))
    (λ { (F , hF , fx) → local-transport F (union B) x v
      (λ u t hu → ref-in B F u t hF)
      (back F hF fx) (good F hF x v fx) }) (ref-out B x v ref)
    where
    back : (F : S) → ⟨ F ∈ˢ B ⟩ → ⟨ Ref F x v ⟩
      → (u t : S) → ⟨ u ∈ˢ x ⟩ → ⟨ Ref (union B) u t ⟩ → ⟨ Ref F u t ⟩
    back F hF fx u t hu ut = PT.rec (snd (Ref F u t))
      (λ { (r , fr) → PT.rec (snd (Ref F u t))
        (λ { (G , hG , gt) → subst (λ z → ⟨ Ref F u z ⟩)
          (agree F G u r t (good F hF) (good G hG) fr gt) fr })
        (ref-out B u t ut) }) (good F hF x v fx .fst u hu)

Witness : S → S → Ω
Witness F x = Good F ⊓ ⋁ S (λ v → Ref F x v)

open import NameImage 𝒮 ext paths using ( colAt; colAt-reading )
open import CodedVocabulary 𝒮 using ( sepAt; sepAt-reading )

witnessFo : Formula S 3
witnessFo = goodFo zero (suc (suc zero)) ∧̇
  ∃̇ (orderAtˢ (suc zero) (suc (suc zero)) zero)

witnessAt : Formula S 2
witnessAt = colAt witnessFo (w ∷ [])

witness-reading : (F x : S) → ((F ∷ x ∷ []) ⊨ witnessAt) ≡ Witness F x
witness-reading F x = colAt-reading witnessFo (w ∷ []) F x
  ∙ cong (_⊓ (⋁ S (λ v → Ref F x v)))
    (good-reading zero (suc (suc zero)) (F ∷ x ∷ w ∷ []) refl)

goodAt : Formula S 1
goodAt = sepAt (goodFo zero (suc zero)) (w ∷ [])

goodAt-reading : (F : S) → ((F ∷ []) ⊨ goodAt) ≡ Good F
goodAt-reading F = sepAt-reading (goodFo zero (suc zero)) (w ∷ []) F
  ∙ good-reading zero (suc zero) (F ∷ w ∷ []) refl

module Collect
  (un : OrdinaryProfile.Union 𝒮)
  (sep : OrdinaryProfile.Separation 𝒮)
  (coll : OrdinaryProfile.Collection 𝒮)
  where

  open Unions un
  open import GroundDescription 𝒮 ext paths using ( separateOf; separateOf-spec )

  Covered : S → S → Ω
  Covered F a = Good F ⊓ ⋀ S (λ u → (u ∈ˢ a) ⇒ ⋁ S (λ t → Ref F u t))

  collect-tables : (a : S)
    → ((u : S) → ⟨ u ∈ˢ a ⟩ → ⟨ ⋁ S (λ F → Witness F u) ⟩)
    → ⟨ ⋁ S (λ F → Covered F a) ⟩
  collect-tables a ih = PT.rec PT.squash₁ assemble
    (coll a witnessAt (λ u hu → PT.map (λ { (F , hF) →
      F , subst ⟨_⟩ (sym (witness-reading F u)) hF }) (ih u hu)))
    where
    assemble : Σ[ B ∈ S ] ((u : S) → ⟨ u ∈ˢ a ⟩
      → ⟨ ⋁ S (λ F → (F ∈ˢ B) ⊓ ((F ∷ u ∷ []) ⊨ witnessAt)) ⟩)
      → ⟨ ⋁ S (λ F → Covered F a) ⟩
    assemble (B , bound) = ∣ union C , good-union C all-good , covered ∣₁
      where
      C : S
      C = separateOf sep B goodAt

      all-good : (F : S) → ⟨ F ∈ˢ C ⟩ → ⟨ Good F ⟩
      all-good F hF = subst ⟨_⟩ (goodAt-reading F)
        (subst ⟨_⟩ (separateOf-spec sep B goodAt F) hF .snd)

      covered : (u : S) → ⟨ u ∈ˢ a ⟩ → ⟨ ⋁ S (λ t → Ref (union C) u t) ⟩
      covered u hu = PT.rec PT.squash₁
        (λ { (F , hB , sat) → let h = subst ⟨_⟩ (witness-reading F u) sat in
          PT.map (λ { (t , ft) → t , ref-in C F u t
            (subst ⟨_⟩ (sym (separateOf-spec sep B goodAt F))
              (hB , subst ⟨_⟩ (sym (goodAt-reading F)) (h .fst))) ft }) (h .snd) })
        (bound u hu)

module Construct
  (pair : OrdinaryProfile.Pairing 𝒮)
  (un : OrdinaryProfile.Union 𝒮)
  (pow : OrdinaryProfile.PowerSet 𝒮)
  (sep : OrdinaryProfile.Separation 𝒮)
  (coll : OrdinaryProfile.Collection 𝒮)
  (seed : S)
  where

  import K8.GroundSets
  import NameImage
  module GS = K8.GroundSets.Ground 𝒮 ext paths pair un pow sep seed
    using ( ordered; ordered-witness; ordered-unique; ordered-components;
            join; join-spec; singleton; singleton-witness; ≈→≡ )
  module CD = NameImage.CheckDischarge 𝒮 ext paths
    GS.ordered GS.ordered-witness GS.ordered-unique w
    using ( checkAtˢ; checkAtˢ-reading; CheckΔ )
  open Collect un sep coll
  open import GroundDescription 𝒮 ext paths using ( hasImage′ )
  open import Cubical.Data.Sigma using ( Σ≡Prop )
  open import Cubical.Foundations.Prelude using ( isPropIsContr )
  open import Cubical.Data.Sum using ( inl; inr )

  stage : (F a : S) → ⟨ Covered F a ⟩ → ⟨ ⋁ S (λ v → Local F a v) ⟩
  stage F a covered = PT.map (λ { (v , spec) → v , covered .snd ,
    λ z → (λ h → subst ⟨_⟩ (reading z) (spec z .fst h)) ,
          (λ h → spec z .snd (subst ⟨_⟩ (sym (reading z)) h)) })
    (hasImage′ sep coll a (CD.checkAtˢ F) functional)
    where
    reading : (z : S) →
      (⋁ S (λ u → (u ∈ˢ a) ⊓ ((z ∷ u ∷ []) ⊨ CD.checkAtˢ F))) ≡ Weighted F a z
    reading z = cong (⋁ S) (funExt λ u →
      cong ((u ∈ˢ a) ⊓_) (CD.checkAtˢ-reading F z u))

    functional : (u : S) → ⟨ u ∈ˢ a ⟩
      → isContr (Σ[ z ∈ S ] ⟨ (z ∷ u ∷ []) ⊨ CD.checkAtˢ F ⟩)
    functional u hu = PT.rec isPropIsContr make (covered .snd u hu)
      where
      make : Σ[ t ∈ S ] ⟨ Ref F u t ⟩
        → isContr (Σ[ z ∈ S ] ⟨ (z ∷ u ∷ []) ⊨ CD.checkAtˢ F ⟩)
      make (t , ft) =
        (GS.ordered t w , subst ⟨_⟩ (sym (CD.checkAtˢ-reading F (GS.ordered t w) u))
          ∣ t , ft , GS.ordered-witness t w ∣₁) ,
        λ { (z , hz) → Σ≡Prop (λ j → snd ((j ∷ u ∷ []) ⊨ CD.checkAtˢ F))
          (sym (PT.rec (isSetS z (GS.ordered t w))
            (λ { (r , fr , kp) → GS.ordered-unique z r w kp ∙
              cong (λ j → GS.ordered j w) (agree F F u r t
                (covered .fst) (covered .fst) fr ft) })
            (subst ⟨_⟩ (CD.checkAtˢ-reading F z u) hz))) }

  extend : S → S → S → S
  extend F a v = GS.join F (GS.singleton (GS.ordered a v))

  extend-in : (F a v x t : S) → ⟨ Ref F x t ⟩ → ⟨ Ref (extend F a v) x t ⟩
  extend-in F a v x t = PT.map λ { (e , he , kp) → e ,
    subst ⟨_⟩ (sym (GS.join-spec F (GS.singleton (GS.ordered a v)) e)) ∣ inl he ∣₁ , kp }

  extend-root : (F a v : S) → ⟨ Ref (extend F a v) a v ⟩
  extend-root F a v = ∣ GS.ordered a v ,
    subst ⟨_⟩ (sym (GS.join-spec F (GS.singleton (GS.ordered a v)) (GS.ordered a v)))
      ∣ inr (GS.singleton-witness (GS.ordered a v) .fst) ∣₁ , GS.ordered-witness a v ∣₁

  extend-out : (F a v x t : S) → ⟨ Ref (extend F a v) x t ⟩
    → ⟨ Ref F x t ⊔ ((x ≈ˢ a) ⊓ (t ≈ˢ v)) ⟩
  extend-out F a v x t = PT.rec PT.squash₁ λ { (e , he , kp) →
    PT.rec PT.squash₁
      (λ { (inl hf) → ∣ inl ∣ e , hf , kp ∣₁ ∣₁
         ; (inr hs) → let eq = GS.ordered-components (GS.ordered a v) x t a v
                            (subst (λ j → ⟨ isKPairΔ j x t ⟩)
                              (GS.≈→≡ (GS.singleton-witness (GS.ordered a v) .snd e hs)) kp)
                            (GS.ordered-witness a v)
                     in ∣ inr (subst ⟨_⟩ (sym (paths x a)) (eq .fst) ,
                                subst ⟨_⟩ (sym (paths t v)) (eq .snd)) ∣₁ })
      (subst ⟨_⟩ (GS.join-spec F (GS.singleton (GS.ordered a v)) e) he) }

  good-extend : (F a v : S) → ⟨ Good F ⟩ → ⟨ Local F a v ⟩ → ⟨ Good (extend F a v) ⟩
  good-extend F a v gf local x t ref = PT.rec (snd (Local (extend F a v) x t))
    (λ { (inl ft) → transfer x t (gf x t ft)
       ; (inr eq) → subst (λ j → ⟨ Local (extend F a v) x j ⟩) (sym (GS.≈→≡ (eq .snd)))
         (subst (λ j → ⟨ Local (extend F a v) j v ⟩) (sym (GS.≈→≡ (eq .fst)))
           (transfer a v local)) }) (extend-out F a v x t ref)
    where
    transfer : (x t : S) → ⟨ Local F x t ⟩ → ⟨ Local (extend F a v) x t ⟩
    transfer x t lx = local-transport F (extend F a v) x t
      (λ u r hu → extend-in F a v u r) back lx
      where
      back : (u r : S) → ⟨ u ∈ˢ x ⟩ → ⟨ Ref (extend F a v) u r ⟩ → ⟨ Ref F u r ⟩
      back u r hu ur = PT.rec (snd (Ref F u r))
        (λ { (inl fr) → fr
           ; (inr eq) → PT.rec (snd (Ref F u r))
             (λ { (s , fs) → let
                 as = subst (λ j → ⟨ Ref F j s ⟩) (GS.≈→≡ (eq .fst)) fs
                 sv = local-unique F a s v (gf a s as) local
               in subst (λ j → ⟨ Ref F u j ⟩) (sv ∙ sym (GS.≈→≡ (eq .snd))) fs })
             (lx .fst u hu) }) (extend-out F a v u r ur)

  total-acc : (a : S) → Acc (λ y z → ⟨ y ∈ˢ z ⟩) a
    → ⟨ ⋁ S (λ F → Witness F a) ⟩
  total-acc a (acc below) = PT.rec PT.squash₁
    (λ { (F , covered) → PT.map (λ { (v , local) →
      extend F a v , good-extend F a v (covered .fst) local , ∣ v , extend-root F a v ∣₁ })
      (stage F a covered) })
    (collect-tables a (λ u hu → total-acc u (below u hu)))

  total : (a : S) → ⟨ ⋁ S (λ F → Witness F a) ⟩
  total a = total-acc a (wf a)

  Value : S → S → Ω
  Value v a = ⋁ S (λ F → Good F ⊓ Ref F a v)

  valueFo : Formula S 3
  valueFo = ∃̇ (goodFo zero (suc (suc (suc zero))) ∧̇
    orderAtˢ zero (suc (suc zero)) (suc zero))

  valueAt : Formula S 2
  valueAt = colAt valueFo (w ∷ [])

  value-reading : (v a : S) → ((v ∷ a ∷ []) ⊨ valueAt) ≡ Value v a
  value-reading v a = colAt-reading valueFo (w ∷ []) v a ∙
    cong (⋁ S) (funExt λ F → cong (_⊓ Ref F a v)
      (good-reading zero (suc (suc (suc zero))) (F ∷ v ∷ a ∷ w ∷ []) refl))

  value-total : (a : S) → ⟨ ⋁ S (λ v → Value v a) ⟩
  value-total a = PT.rec PT.squash₁
    (λ { (F , gf , rest) → PT.map (λ { (v , fv) → v , ∣ F , gf , fv ∣₁ }) rest }) (total a)

  value-single : (a v t : S) → ⟨ Value v a ⟩ → ⟨ Value t a ⟩ → v ≡ t
  value-single a v t hv ht = PT.rec (isSetS v t)
    (λ { (F , gf , fv) → PT.rec (isSetS v t)
      (λ { (G , gg , gt) → agree F G a v t gf gg fv gt }) ht }) hv

  value-contr : (a : S) → isContr (Σ[ v ∈ S ] ⟨ Value v a ⟩)
  value-contr a = PT.rec isPropIsContr
    (λ { (v , hv) → (v , hv) , λ { (t , ht) →
      Σ≡Prop (λ j → snd (Value j a)) (value-single a v t hv ht) } }) (value-total a)

  opaque
    chk : S → S
    chk a = value-contr a .fst .fst

    chk-value : (a : S) → ⟨ Value (chk a) a ⟩
    chk-value a = value-contr a .fst .snd

  module NI = NameImage 𝒮 ext paths
    using ( DefinableGraph; ImageClass; InternalImage; graph→internal )

  check-graph : NI.DefinableGraph chk
  check-graph = record
    { graph = valueAt
    ; defines = λ a → subst ⟨_⟩ (sym (value-reading (chk a) a)) (chk-value a)
    ; only = λ a v hv → value-single a v (chk a)
        (subst ⟨_⟩ (value-reading v a) hv) (chk-value a)
    }

  check-image : NI.InternalImage chk
  check-image = NI.graph→internal coll sep chk check-graph

  ref-check : (F x v : S) → ⟨ Good F ⟩ → ⟨ Ref F x v ⟩ → v ≡ chk x
  ref-check F x v gf fv = value-single x v (chk x) ∣ F , gf , fv ∣₁ (chk-value x)

  chk-spec : (a z : S) → (z ∈ˢ chk a) ≡ NI.ImageClass (λ u → GS.ordered (chk u) w) a z
  chk-spec a z = ⇔toPath forward backward
    where
    forward : ⟨ z ∈ˢ chk a ⟩ → ⟨ NI.ImageClass (λ u → GS.ordered (chk u) w) a z ⟩
    forward hz = PT.rec PT.squash₁ (λ { (F , gf , fa) →
      PT.rec PT.squash₁ (λ { (u , hu , rest) → PT.map
        (λ { (t , ft , kp) → u , hu , subst ⟨_⟩ (sym (paths z (GS.ordered (chk u) w)))
          (GS.ordered-unique z t w kp ∙ cong (λ j → GS.ordered j w) (ref-check F u t gf ft)) })
        rest }) (gf a (chk a) fa .snd z .fst hz) }) (chk-value a)

    backward : ⟨ NI.ImageClass (λ u → GS.ordered (chk u) w) a z ⟩ → ⟨ z ∈ˢ chk a ⟩
    backward hz = PT.rec (snd (z ∈ˢ chk a)) (λ { (F , gf , fa) →
      gf a (chk a) fa .snd z .snd (PT.rec PT.squash₁
        (λ { (u , hu , eq) → PT.map (λ { (t , ft) → u , hu , ∣ t , ft ,
          subst (λ j → ⟨ isKPairΔ j t w ⟩)
            (sym (GS.≈→≡ eq ∙ cong (λ j → GS.ordered j w) (sym (ref-check F u t gf ft))))
            (GS.ordered-witness t w) ∣₁ }) (gf a (chk a) fa .fst u hu) }) hz) }) (chk-value a)

  check-internal : NI.InternalImage (λ u → GS.ordered (chk u) w)
  check-internal = record { img = chk ; img-spec = chk-spec }

  valueSlots : ∀ {n} → Fin n → Fin n → Fin n → Formula S n
  valueSlots v a b = ∃̇ (goodFo zero (suc b) ∧̇ orderAtˢ zero (suc a) (suc v))

  valueSlots-reading : ∀ {n} (v a b : Fin n) (γ : S ^ n)
    → lookup b γ ≡ w → (γ ⊨ valueSlots v a b) ≡ Value (lookup v γ) (lookup a γ)
  valueSlots-reading v a b γ e = cong (⋁ S) (funExt λ F →
    cong (_⊓ Ref F (lookup a γ) (lookup v γ)) (good-reading zero (suc b) (F ∷ γ) e))

  tableFo : Formula S 3
  tableFo = ∃̇ (valueSlots zero (suc (suc zero)) (suc (suc (suc zero))) ∧̇
    prAtˢ (suc zero) (suc (suc zero)) zero)

  tableAt : Formula S 2
  tableAt = colAt tableFo (w ∷ [])

  table-reading : (e x : S) → ((e ∷ x ∷ []) ⊨ tableAt) ≡
    ⋁ S (λ v → Value v x ⊓ isKPairΔ e x v)
  table-reading e x = colAt-reading tableFo (w ∷ []) e x ∙
    cong (⋁ S) (funExt λ v → cong (_⊓ isKPairΔ e x v)
      (valueSlots-reading zero (suc (suc zero)) (suc (suc (suc zero)))
        (v ∷ e ∷ x ∷ w ∷ []) refl))

  table-graph : NI.DefinableGraph (λ x → GS.ordered x (chk x))
  table-graph = record
    { graph = tableAt
    ; defines = λ x → subst ⟨_⟩ (sym (table-reading (GS.ordered x (chk x)) x))
        ∣ chk x , chk-value x , GS.ordered-witness x (chk x) ∣₁
    ; only = λ x e he → PT.rec (isSetS e (GS.ordered x (chk x)))
        (λ { (v , hv , kp) → GS.ordered-unique e x v kp ∙
          cong (GS.ordered x) (value-single x v (chk x) hv (chk-value x)) })
        (subst ⟨_⟩ (table-reading e x) he)
    }

  table-image : NI.InternalImage (λ x → GS.ordered x (chk x))
  table-image = NI.graph→internal coll sep (λ x → GS.ordered x (chk x)) table-graph

  table : S → S
  table = NI.InternalImage.img table-image

  table-mem : (a x : S) → ⟨ x ∈ˢ a ⟩ → ⟨ GS.ordered x (chk x) ∈ˢ table a ⟩
  table-mem a x hx = subst ⟨_⟩ (sym (NI.InternalImage.img-spec table-image a (GS.ordered x (chk x))))
    ∣ x , hx , subst ⟨_⟩ (sym (paths (GS.ordered x (chk x)) (GS.ordered x (chk x)))) refl ∣₁

  table-only : (a e u v : S) → ⟨ u ∈ˢ a ⟩ → ⟨ e ∈ˢ table a ⟩
    → ⟨ isKPairΔ e u v ⟩ → v ≡ chk u
  table-only a e u v hu he kp = PT.rec (isSetS v (chk u))
    (λ { (x , hx , eq) → let
        components = GS.ordered-components (GS.ordered x (chk x)) u v x (chk x)
          (subst (λ j → ⟨ isKPairΔ j u v ⟩) (GS.≈→≡ eq) kp) (GS.ordered-witness x (chk x))
      in components .snd ∙ cong chk (sym (components .fst)) })
    (subst ⟨_⟩ (NI.InternalImage.img-spec table-image a e) he)

  module Discharged (a : S) = NameImage.CheckDischarge.Stage 𝒮 ext paths
    GS.ordered GS.ordered-witness GS.ordered-unique w a (table a) chk
    (table-mem a) (table-only a)
