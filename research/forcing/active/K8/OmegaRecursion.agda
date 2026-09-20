{-# OPTIONS --cubical --safe --guardedness #-}

open import Base.Prelude
open import Base.Truth
open import Base.Classical using ( LEM )
open import FOL.ZFStructure using ( ZFStructure )
import OrdinaryProfile

module K8.OmegaRecursion
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
  using ( Formula; Term; var; con; _∈̇_; _≐_; _∧̇_; _∨̇_; _⇒̇_; ∀̇_; ∀̇∈; ∃̇_; ∃̇∈ )
open import FOL.Semantics (hPropAlgebra ℓ) 𝒮 using ( module At; _^_ )
open import FOL.Manipulation.Renaming using ( renameFo; module Sat )
open import CodedVocabulary 𝒮 using ( refinesΔ; isKPairΔ; subsetΔ; orderAtˢ; instFo )
open import K8.FiniteVocabulary 𝒮 using ( emptyPred; adjoinPred; adjoinAt )
open import K8.MapVocabulary 𝒮 using ( domainPred )
open import OrdinaryProfile 𝒮 using ( iff )
open import Cubical.Data.Sum using ( _⊎_; inl; inr )
open import Cubical.Functions.Logic using ( ⇔toPath )
import Cubical.Data.Empty as Empty
import Cubical.HITs.PropositionalTruncation as PT
open PT using ( ∣_∣₁ )
import GroundDescription
import CardinalBridge
import K7.CardinalOrder
import K8.GroundSets
import K8.OmegaSuccessor
import K8.OmegaInduction
import K8.PartialMaps
import K8.MapOperations
import K8.DomainExtension
import K8.CountableUnion
import K8.FinitePigeonhole

open TruthAlgebra (hPropAlgebra ℓ)
open hPropStructure 𝒮
open At S id using ( _⊨_ )

module CB = CardinalBridge 𝒮
module GS = K8.GroundSets.Ground 𝒮 ext paths pair un pow sep seed
module GD = GroundDescription 𝒮 ext paths
module OS = K8.OmegaSuccessor 𝒮 ext paths pair un pow sep find seed
module OI = K8.OmegaInduction 𝒮 ext paths pair un pow sep seed
module CU = K8.CountableUnion 𝒮 ext paths pair un pow sep coll find seed
module FP = K8.FinitePigeonhole 𝒮 ext paths pair un pow sep coll find seed
module CO = K7.CardinalOrder.Order 𝒮 ext
  (λ x y z h → cong (_∈ˢ z) (GS.≈→≡ h))
  (λ x y z h → cong (x ∈ˢ_) (GS.≈→≡ h))
module Ren = Sat (hPropAlgebra ℓ) 𝒮 id
open CB using ( _↔̇_ )
open CU using ( Ref )

delta-ref : (f x y : S) → ⟨ Ref f x y ⟩ → ⟨ refinesΔ f x y ⟩
delta-ref f x y = PT.map λ { (p , hp , kp) → p , hp , CU.kpair-delta p x y kp }

coded-ref : (f x y : S) → ⟨ refinesΔ f x y ⟩ → ⟨ Ref f x y ⟩
coded-ref f x y = PT.map λ { (p , hp , kp) → p , hp ,
  subst (λ z → ⟨ CB.isKPair z x y ⟩) (sym (GS.ordered-unique p x y kp))
    (CU.ordered-kpair x y) }

deltaAt : ∀ {n} → Term S n → Term S n → Term S n → Formula S n
deltaAt f x y = instFo emb (orderAtˢ zero (suc zero) (suc (suc zero)))
  where
  emb : Fin 3 → _
  emb zero = f
  emb (suc zero) = x
  emb (suc (suc zero)) = y

module AtOmega (lem : LEM ℓ) (w : S) (hw : ⟨ CB.isOmega w ⟩)
  (Y t a : S) (ha : ⟨ a ∈ˢ Y ⟩)
  (tf : ⟨ CB.isFunction t ⟩)
  (tt : (u : S) → ⟨ u ∈ˢ Y ⟩ → ⟨ ⋁ S (λ v → (v ∈ˢ Y) ⊓ Ref t u v) ⟩)
  where

  module PM = K8.PartialMaps.Maps 𝒮 ext paths pair un pow sep seed w Y
  module MO = K8.MapOperations.Operations 𝒮 ext paths pair un pow sep seed w Y
  module DE = K8.DomainExtension 𝒮 ext paths pair un pow sep seed w Y

  Local : S → S → S → Ω
  Local p k v = ((k ≈ˢ OS.zeroSet) ⇒ (v ≈ˢ a)) ⊓
    (⋀ S (λ m → (m ∈ˢ w) ⇒ (CB.isSuccOf k m ⇒
      ⋁ S (λ u → (u ∈ˢ Y) ⊓ (refinesΔ p m u ⊓ refinesΔ t u v)))))

  Good : S → Ω
  Good p = ⋀ S (λ k → (k ∈ˢ w) ⇒
    ⋀ S (λ v → (v ∈ˢ Y) ⇒ (refinesΔ p k v ⇒ Local p k v)))

  goodFormula : Formula S 1
  goodFormula = ∀̇∈ (con w) (∀̇∈ (con Y)
    (orderAtˢ (suc (suc zero)) (suc zero) zero ⇒̇
      (((var (suc zero) ≐ con OS.zeroSet) ⇒̇ (var zero ≐ con a)) ∧̇
        ∀̇∈ (con w) (adjoinAt (suc (suc zero)) zero zero ⇒̇
          ∃̇∈ (con Y) (orderAtˢ (suc (suc (suc (suc zero)))) (suc zero) zero ∧̇
            deltaAt (con t) (var zero) (var (suc (suc zero))))))))

  good-reading : (p : S) → ((p ∷ []) ⊨ goodFormula) ≡ Good p
  good-reading p = refl

  goodAt : ∀ {n} → Fin n → Formula S n
  goodAt p = renameFo (λ _ → p) goodFormula

  goodAt-reading : ∀ {n} (p : Fin n) (γ : S ^ n)
    → (γ ⊨ goodAt p) ≡ Good (lookup p γ)
  goodAt-reading p γ = Ren.⊨-rename (λ _ → p) goodFormula γ (lookup p γ ∷ [])
    (λ { zero → refl }) ∙ good-reading (lookup p γ)

  Through : S → S → Ω
  Through n p = ⋀ S (λ k → iff ((k ∈ˢ n) ⊔ (k ≈ˢ n))
    ((k ∈ˢ w) ⊓ domainPred Y p k))

  throughFormula : Formula S 2
  throughFormula = ∀̇ (((var zero ∈̇ var (suc (suc zero))) ∨̇
    (var zero ≐ var (suc (suc zero)))) ↔̇
    ((var zero ∈̇ con w) ∧̇ ∃̇∈ (con Y)
      (orderAtˢ (suc (suc zero)) (suc zero) zero)))

  through-reading : (p n : S) → ((p ∷ n ∷ []) ⊨ throughFormula) ≡ Through n p
  through-reading p n = refl

  Seq : S → S → Ω
  Seq n p = (p ∈ˢ PM.carrier) ⊓ (Through n p ⊓ Good p)

  seqFormula : Formula S 2
  seqFormula = (var zero ∈̇ con PM.carrier) ∧̇ (throughFormula ∧̇ goodAt zero)

  seq-reading : (p n : S) → ((p ∷ n ∷ []) ⊨ seqFormula) ≡ Seq n p
  seq-reading p n = cong ((p ∈ˢ PM.carrier) ⊓_)
    (cong₂ _⊓_ (through-reading p n) (goodAt-reading zero (p ∷ n ∷ [])))

  successor-members : (n k : S)
    → (k ∈ˢ OS.successor n) ≡ ((k ∈ˢ n) ⊔ (k ≈ˢ n))
  successor-members n k = ⇔toPath (OS.successor-spec n .snd .snd k)
    (PT.rec (snd (k ∈ˢ OS.successor n))
      (λ { (inl kn) → OS.successor-spec n .snd .fst k kn
         ; (inr eq) → subst (λ z → ⟨ z ∈ˢ OS.successor n ⟩)
             (sym (GS.≈→≡ eq)) (OS.successor-spec n .fst) }))

  through-equality : (n p : S) → ⟨ Through n p ⟩ → PM.domain p ≡ OS.successor n
  through-equality n p h = GD.ext-path λ k → PM.domain-spec p k
    ∙ sym (⇔toPath (h k .fst) (h k .snd)) ∙ sym (successor-members n k)

  equality-through : (n p : S) → PM.domain p ≡ OS.successor n → ⟨ Through n p ⟩
  equality-through n p eq k = subst ⟨_⟩ (sym path) , subst ⟨_⟩ path
    where
    path : ((k ∈ˢ w) ⊓ domainPred Y p k) ≡ ((k ∈ˢ n) ⊔ (k ≈ˢ n))
    path = sym (PM.domain-spec p k) ∙ cong (k ∈ˢ_) eq ∙ successor-members n k

  local-monotone : (p q k v : S) → ⟨ subsetΔ p q ⟩ → ⟨ Local p k v ⟩ → ⟨ Local q k v ⟩
  local-monotone p q k v sub h = h .fst , λ m hm km → PT.map
    (λ { (u , hu , pu , tv) → u , hu , MO.refines-mono p q m u sub pu , tv })
    (h .snd m hm km)

  insert-good : (p n v : S) → ⟨ Good p ⟩ → ⟨ Local p n v ⟩ → ⟨ Good (MO.insert p n v) ⟩
  insert-good p n v gp lv k hk y hy r = PT.rec (snd (Local (MO.insert p n v) k y))
    (λ { (inl old) → local-monotone p (MO.insert p n v) k y (MO.insert-extends p n v)
        (gp k hk y hy old)
       ; (inr new) → local-monotone p (MO.insert p n v) k y (MO.insert-extends p n v)
         (subst (λ z → ⟨ Local p k z ⟩) (sym (MO.point-components n v k y new .snd))
           (subst (λ z → ⟨ Local p z v ⟩) (sym (MO.point-components n v k y new .fst)) lv)) })
    (subst ⟨_⟩ (MO.join-refines p (MO.point n v) k y) r)

  empty-domain : PM.domain GS.empty ≡ OS.zeroSet
  empty-domain = OS.empty-unique (PM.domain GS.empty) λ k hk → PT.rec (snd ⊥)
    (λ { (v , hv , r) → PT.rec (snd ⊥) (λ { (p , hp , _) → GS.empty-out p hp }) r })
    (subst ⟨_⟩ (PM.domain-spec GS.empty k) hk .snd)

  empty-good : ⟨ Good GS.empty ⟩
  empty-good k hk v hv = PT.rec (snd (Local GS.empty k v))
    (λ { (p , hp , _) → Empty.rec* (GS.empty-out p hp) })

  base-local : ⟨ Local GS.empty OS.zeroSet a ⟩
  base-local = (λ _ → CO.≈-refl a) , λ m hm sm → Empty.rec
    (OS.successor-not-zero m (sym (OS.successor-unique OS.zeroSet m sm)))

  base-sequence : ⟨ Seq OS.zeroSet (MO.insert GS.empty OS.zeroSet a) ⟩
  base-sequence = MO.insert-in-carrier GS.empty OS.zeroSet a PM.empty-in-carrier
    (OS.zero-in w hw) ha
    (λ h → GS.empty-out OS.zeroSet (subst (λ z → ⟨ OS.zeroSet ∈ˢ z ⟩) empty-domain h))
    , equality-through OS.zeroSet (MO.insert GS.empty OS.zeroSet a)
      (OS.successor-unique (PM.domain (MO.insert GS.empty OS.zeroSet a)) OS.zeroSet
        (subst (λ d → ⟨ adjoinPred (PM.domain (MO.insert GS.empty OS.zeroSet a)) d OS.zeroSet ⟩)
          empty-domain (DE.domain-insert GS.empty OS.zeroSet a (OS.zero-in w hw) ha)))
    , insert-good GS.empty OS.zeroSet a empty-good base-local

  extend-sequence : (n s p : S) → ⟨ n ∈ˢ w ⟩ → ⟨ s ∈ˢ w ⟩ → ⟨ CB.isSuccOf s n ⟩
    → ⟨ Seq n p ⟩ → ⟨ ⋁ S (Seq s) ⟩
  extend-sequence n s p hn hs sn hp = PT.rec (snd (⋁ S (Seq s)))
    (λ { (u , hu , pu) → PT.map (finish u hu pu) (tt u hu) })
    (hp .snd .fst n .fst ∣ inr (CO.≈-refl n) ∣₁ .snd)
    where
    domain-eq : PM.domain p ≡ s
    domain-eq = through-equality n p (hp .snd .fst) ∙ sym (OS.successor-unique s n sn)

    finish : (u : S) → ⟨ u ∈ˢ Y ⟩ → ⟨ refinesΔ p n u ⟩
      → Σ[ v ∈ S ] ⟨ (v ∈ˢ Y) ⊓ Ref t u v ⟩ → Σ[ q ∈ S ] ⟨ Seq s q ⟩
    finish u hu pu (v , hv , tv) = MO.insert p s v ,
      MO.insert-in-carrier p s v (hp .fst) hs hv
        (λ h → Empty.rec (CO.no-self find s (subst (λ z → ⟨ s ∈ˢ z ⟩) domain-eq h)))
      , equality-through s (MO.insert p s v)
        (OS.successor-unique (PM.domain (MO.insert p s v)) s
          (subst (λ d → ⟨ adjoinPred (PM.domain (MO.insert p s v)) d s ⟩)
            domain-eq (DE.domain-insert p s v hs hv)))
      , insert-good p s v (hp .snd .snd) local
      where
      local : ⟨ Local p s v ⟩
      local = (λ sz → Empty.rec (OS.successor-not-zero n
        (sym (OS.successor-unique s n sn) ∙ GS.≈→≡ sz)))
        , λ m hm sm → ∣ u , hu ,
          subst (λ k → ⟨ refinesΔ p k u ⟩)
            (OS.successor-injective lem w hw n m hn hm
              (sym (OS.successor-unique s n sn) ∙ OS.successor-unique s m sm)) pu
          , delta-ref t u v tv ∣₁

  sequence-exists : (n : S) → ⟨ n ∈ˢ w ⟩ → ⟨ ⋁ S (Seq n) ⟩
  sequence-exists n hn = subst ⟨_⟩ (reading n)
    (OI.omega-induction w hw (∃̇ seqFormula) base step n hn)
    where
    reading : (n : S) → ((n ∷ []) ⊨ ∃̇ seqFormula) ≡ (⋁ S (Seq n))
    reading n = cong (⋁ S) (funExt (λ p → seq-reading p n))

    base : (e : S) → ⟨ e ∈ˢ w ⟩ → ⟨ emptyPred e ⟩ → ⟨ (e ∷ []) ⊨ ∃̇ seqFormula ⟩
    base e he ee = subst ⟨_⟩ (sym (reading e))
      (subst (λ k → ⟨ ⋁ S (Seq k) ⟩) (sym (OS.empty-unique e ee))
        ∣ MO.insert GS.empty OS.zeroSet a , base-sequence ∣₁)

    step : (n s : S) → ⟨ n ∈ˢ w ⟩ → ⟨ (n ∷ []) ⊨ ∃̇ seqFormula ⟩
      → ⟨ s ∈ˢ w ⟩ → ⟨ CB.isSuccOf s n ⟩ → ⟨ (s ∷ []) ⊨ ∃̇ seqFormula ⟩
    step n s hn ih hs sn = subst ⟨_⟩ (sym (reading s))
      (PT.rec (snd (⋁ S (Seq s)))
        (λ { (p , hp) → extend-sequence n s p hn hs sn hp }) (subst ⟨_⟩ (reading n) ih))

  Unique : S → Ω
  Unique k = ⋀ S (λ p → Good p ⇒ ⋀ S (λ q → Good q ⇒
    ⋀ S (λ y → (y ∈ˢ Y) ⇒ ⋀ S (λ z → (z ∈ˢ Y) ⇒
      ((refinesΔ p k y) ⊓ (refinesΔ q k z)) ⇒ (y ≈ˢ z)))))

  uniqueFormula : Formula S 1
  uniqueFormula = ∀̇ (goodAt zero ⇒̇ ∀̇ (goodAt zero ⇒̇
    ∀̇∈ (con Y) (∀̇∈ (con Y)
      ((orderAtˢ (suc (suc (suc zero))) (suc (suc (suc (suc zero)))) (suc zero)
        ∧̇ orderAtˢ (suc (suc zero)) (suc (suc (suc (suc zero)))) zero)
        ⇒̇ (var (suc zero) ≐ var zero)))))

  unique-reading : (k : S) → ((k ∷ []) ⊨ uniqueFormula) ≡ Unique k
  unique-reading k = cong (⋀ S) (funExt (λ p → cong₂ _⇒_
    (goodAt-reading zero (p ∷ k ∷ []))
    (cong (⋀ S) (funExt (λ q → cong
      (_⇒ (⋀ S (λ y → (y ∈ˢ Y) ⇒ ⋀ S (λ z → (z ∈ˢ Y) ⇒
        ((refinesΔ p k y) ⊓ (refinesΔ q k z)) ⇒ (y ≈ˢ z)))))
      (goodAt-reading zero (q ∷ p ∷ k ∷ [])))))))

  unique-zero : ⟨ Unique OS.zeroSet ⟩
  unique-zero p gp q gq y hy z hz (py , qz) = CO.≈-trans y a z
    (gp OS.zeroSet (OS.zero-in w hw) y hy py .fst (CO.≈-refl OS.zeroSet))
    (CO.≈-sym z a (gq OS.zeroSet (OS.zero-in w hw) z hz qz .fst (CO.≈-refl OS.zeroSet)))

  unique-step : (n s : S) → ⟨ n ∈ˢ w ⟩ → ⟨ s ∈ˢ w ⟩ → ⟨ CB.isSuccOf s n ⟩
    → ⟨ Unique n ⟩ → ⟨ Unique s ⟩
  unique-step n s hn hs sn ih p gp q gq y hy z hz (py , qz) = PT.rec (snd (y ≈ˢ z))
    (λ { (u , hu , pu , uy) → PT.rec (snd (y ≈ˢ z))
      (λ { (v , hv , qv , vz) → CU.ref-single t u y z tf (coded-ref t u y uy)
        (coded-ref t u z (subst (λ k → ⟨ refinesΔ t k z ⟩)
          (sym (GS.≈→≡ (ih p gp q gq u hu v hv (pu , qv)))) vz)) })
      (gq s hs z hz qz .snd n hn sn) })
    (gp s hs y hy py .snd n hn sn)

  values-unique : (k : S) → ⟨ k ∈ˢ w ⟩ → ⟨ Unique k ⟩
  values-unique k hk = subst ⟨_⟩ (unique-reading k)
    (OI.omega-induction w hw uniqueFormula
      (λ e he ee → subst ⟨_⟩ (sym (unique-reading e))
        (subst (λ z → ⟨ Unique z ⟩) (sym (OS.empty-unique e ee)) unique-zero))
      (λ n s hn ih hs sn → subst ⟨_⟩ (sym (unique-reading s))
        (unique-step n s hn hs sn (subst ⟨_⟩ (unique-reading n) ih))) k hk)

  Value : S → S → Ω
  Value y k = (k ∈ˢ w) ⊓ ((y ∈ˢ Y) ⊓
    (⋁ S (λ p → (p ∈ˢ PM.carrier) ⊓ (Good p ⊓ refinesΔ p k y))))

  valueFormula : Formula S 2
  valueFormula = (var (suc zero) ∈̇ con w) ∧̇ ((var zero ∈̇ con Y) ∧̇
    ∃̇∈ (con PM.carrier) (goodAt zero ∧̇ orderAtˢ zero (suc (suc zero)) (suc zero)))

  value-reading : (y k : S) → ((y ∷ k ∷ []) ⊨ valueFormula) ≡ Value y k
  value-reading y k = cong ((k ∈ˢ w) ⊓_) (cong ((y ∈ˢ Y) ⊓_)
    (cong (⋁ S) (funExt (λ p → cong ((p ∈ˢ PM.carrier) ⊓_)
      (cong (_⊓ refinesΔ p k y) (goodAt-reading zero (p ∷ y ∷ k ∷ [])))))))

  value-total : (k : S) → ⟨ k ∈ˢ w ⟩ → ⟨ ⋁ S (λ y → (y ∈ˢ Y) ⊓ Value y k) ⟩
  value-total k hk = PT.rec (snd (⋁ S (λ y → (y ∈ˢ Y) ⊓ Value y k)))
    (λ { (p , hp , dom , gp) → PT.map (λ { (y , hy , py) →
      y , hy , hk , hy , ∣ p , hp , gp , py ∣₁ })
      (dom k .fst ∣ inr (CO.≈-refl k) ∣₁ .snd) }) (sequence-exists k hk)

  value-single : (k y z : S) → ⟨ Value y k ⟩ → ⟨ Value z k ⟩ → ⟨ y ≈ˢ z ⟩
  value-single k y z hy hz = PT.rec (snd (y ≈ˢ z))
    (λ { (p , hp , gp , py) → PT.rec (snd (y ≈ˢ z))
      (λ { (q , hq , gq , qz) → values-unique k (hy .fst) p gp q gq
        y (hy .snd .fst) z (hz .snd .fst) (py , qz) }) (hz .snd .snd) }) (hy .snd .snd)

  module G = FP.Graph w Y valueFormula

  recursion : S
  recursion = G.graph

  opaque
    recursion-value : (k y : S) → ⟨ Ref recursion k y ⟩ → ⟨ Value y k ⟩
    recursion-value k y r = subst ⟨_⟩ (value-reading y k) (G.ref-entry k y r .snd .snd)

    recursion-function : ⟨ CB.isFunction recursion ⟩
    recursion-function = G.relation , λ p hp q hq k y z (kp , kq) → value-single k y z
      (subst ⟨_⟩ (value-reading y k) (G.entry p hp k y kp .snd .snd))
      (subst ⟨_⟩ (value-reading z k) (G.entry q hq k z kq .snd .snd))

    recursion-total : (k : S) → ⟨ k ∈ˢ w ⟩ → ⟨ ⋁ S (λ y → (y ∈ˢ Y) ⊓ Ref recursion k y) ⟩
    recursion-total k hk = PT.map (λ { (y , hy , val) → y , hy ,
      G.ref-in k y hk hy (subst ⟨_⟩ (sym (value-reading y k)) val) }) (value-total k hk)

    recursion-typed : (k y : S) → ⟨ Ref recursion k y ⟩ → ⟨ (k ∈ˢ w) ⊓ (y ∈ˢ Y) ⟩
    recursion-typed k y r = recursion-value k y r .fst , recursion-value k y r .snd .fst

    recursion-zero : ⟨ Ref recursion OS.zeroSet a ⟩
    recursion-zero = G.ref-in OS.zeroSet a (OS.zero-in w hw) ha
      (subst ⟨_⟩ (sym (value-reading a OS.zeroSet))
        (OS.zero-in w hw , ha , ∣ MO.insert GS.empty OS.zeroSet a , base-sequence .fst ,
          base-sequence .snd .snd , MO.insert-evaluates GS.empty OS.zeroSet a ∣₁))

    recursion-step : (n u v : S) → ⟨ n ∈ˢ w ⟩
      → ⟨ Ref recursion n u ⟩ → ⟨ Ref recursion (OS.successor n) v ⟩ → ⟨ Ref t u v ⟩
    recursion-step n u v hn nu sv = PT.rec (snd (Ref t u v))
      (λ { (p , hp , gp , pv) → PT.rec (snd (Ref t u v))
        (λ { (y , hy , py , yv) → coded-ref t u v
          (subst (λ z → ⟨ refinesΔ t z v ⟩)
            (sym (GS.≈→≡ (value-single n u y (recursion-value n u nu)
              (hn , hy , ∣ p , hp , gp , py ∣₁)))) yv) })
        (gp (OS.successor n) (OS.successor-in w hw n hn) v (recursion-value (OS.successor n) v sv .snd .fst)
          pv .snd n hn (OS.successor-spec n)) })
      (recursion-value (OS.successor n) v sv .snd .snd)

    recursion-next : (n u : S) → ⟨ n ∈ˢ w ⟩ → ⟨ Ref recursion n u ⟩
      → ⟨ ⋁ S (λ v → (v ∈ˢ Y) ⊓ (Ref recursion (OS.successor n) v ⊓ Ref t u v)) ⟩
    recursion-next n u hn nu = PT.map (λ { (v , hv , sv) → v , hv , sv , recursion-step n u v hn nu sv })
      (recursion-total (OS.successor n) (OS.successor-in w hw n hn))
