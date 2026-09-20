{-# OPTIONS --cubical --safe --guardedness #-}

open import Base.Prelude
open import Base.Truth
open import Base.Classical using ( LEM )
open import FOL.ZFStructure using ( ZFStructure )
import OrdinaryProfile

module K8.FinitePigeonhole
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
  using ( Formula; var; con; _≐_; _∧̇_; _∨̇_; ¬̇_; ∃̇∈ )
open import FOL.Semantics (hPropAlgebra ℓ) 𝒮 using ( module At )
open import FOL.Manipulation.Renaming using ( renameFo; module Sat )
open import Cubical.Data.Sum using ( _⊎_; inl; inr )
import Cubical.Data.Empty as Empty
import Cubical.HITs.PropositionalTruncation as PT
open PT using ( ∣_∣₁ )
import K8.GroundSets
import K8.FiniteEnumeration
import K8.CountableUnion
import K8.OmegaInduction
import K7.CardinalOrder
import CardinalBridge

open TruthAlgebra (hPropAlgebra ℓ)
open hPropStructure 𝒮
open At S id using ( _⊨_ )

module CB = CardinalBridge 𝒮
module GS = K8.GroundSets.Ground 𝒮 ext paths pair un pow sep seed
module CU = K8.CountableUnion 𝒮 ext paths pair un pow sep coll find seed
module FE = K8.FiniteEnumeration 𝒮 ext paths pair un pow sep find seed
module CO = K7.CardinalOrder.Order 𝒮 ext
  (λ x y z h → cong (_∈ˢ z) (GS.≈→≡ h))
  (λ x y z h → cong (x ∈ˢ_) (GS.≈→≡ h))
module Ren = Sat (hPropAlgebra ℓ) 𝒮 id
module OI = K8.OmegaInduction 𝒮 ext paths pair un pow sep seed
open CU using ( Ref; refAt; refAt-reading; ref-single; ref-injective; ref-range; ordered-kpair )
open FE using ( pairAt; pairAt-reading )

module Graph (A B : S) (φ : Formula S 2) where

  R : S → S → Ω
  R v u = (v ∷ u ∷ []) ⊨ φ

  liftR : Fin 2 → Fin 3
  liftR zero = zero
  liftR (suc zero) = suc zero

  body : Formula S 1
  body = ∃̇∈ (con A) (∃̇∈ (con B)
    (pairAt (suc (suc zero)) (suc zero) zero ∧̇ renameFo liftR φ))

  Entries : S → Ω
  Entries p = ⋁ S (λ u → (u ∈ˢ A) ⊓
    ⋁ S (λ v → (v ∈ˢ B) ⊓ (CB.isKPair p u v ⊓ R v u)))

  body-reading : (p : S) → ((p ∷ []) ⊨ body) ≡ Entries p
  body-reading p = cong (⋁ S) (funExt (λ u → cong ((u ∈ˢ A) ⊓_)
    (cong (⋁ S) (funExt (λ v → cong ((v ∈ˢ B) ⊓_)
      (cong₂ _⊓_ (pairAt-reading (suc (suc zero)) (suc zero) zero (v ∷ u ∷ p ∷ []))
        (Ren.⊨-rename liftR φ (v ∷ u ∷ p ∷ []) (v ∷ u ∷ []) (agrees v u))))))))
    where
    agrees : (v u : S) → Ren.Agrees liftR (v ∷ u ∷ p ∷ []) (v ∷ u ∷ [])
    agrees v u zero = refl
    agrees v u (suc zero) = refl

  opaque
    graph : S
    graph = GS.separator (GS.product A B) body

    graph-spec : (p : S) → (p ∈ˢ graph) ≡ ((p ∈ˢ GS.product A B) ⊓ Entries p)
    graph-spec p = GS.separator-spec (GS.product A B) body p
      ∙ cong ((p ∈ˢ GS.product A B) ⊓_) (body-reading p)

  entry : (p : S) → ⟨ p ∈ˢ graph ⟩ → (x y : S) → ⟨ CB.isKPair p x y ⟩
    → ⟨ (x ∈ˢ A) ⊓ ((y ∈ˢ B) ⊓ R y x) ⟩
  entry p hp x y kp = PT.rec (snd ((x ∈ˢ A) ⊓ ((y ∈ˢ B) ⊓ R y x)))
    (λ { (u , hu , vs) → PT.rec (snd ((x ∈ˢ A) ⊓ ((y ∈ˢ B) ⊓ R y x)))
      (λ { (v , hv , kq , hR) →
        subst (λ z → ⟨ z ∈ˢ A ⟩) (sym (eqs u v kq .fst)) hu
        , subst (λ z → ⟨ z ∈ˢ B ⟩) (sym (eqs u v kq .snd)) hv
        , subst (λ z → ⟨ R z x ⟩) (sym (eqs u v kq .snd))
          (subst (λ z → ⟨ R v z ⟩) (sym (eqs u v kq .fst)) hR) }) vs })
    (subst ⟨_⟩ (graph-spec p) hp .snd)
    where
    eqs : (u v : S) → ⟨ CB.isKPair p u v ⟩ → (x ≡ u) × (y ≡ v)
    eqs u v kq = GS.≈→≡ (CO.kpair-components pair p x y u v kp kq .fst)
      , GS.≈→≡ (CO.kpair-components pair p x y u v kp kq .snd)

  ref-entry : (x y : S) → ⟨ Ref graph x y ⟩ → ⟨ (x ∈ˢ A) ⊓ ((y ∈ˢ B) ⊓ R y x) ⟩
  ref-entry x y = PT.rec (snd ((x ∈ˢ A) ⊓ ((y ∈ˢ B) ⊓ R y x)))
    (λ { (p , hp , kp) → entry p hp x y kp })

  ref-in : (x y : S) → ⟨ x ∈ˢ A ⟩ → ⟨ y ∈ˢ B ⟩ → ⟨ R y x ⟩ → ⟨ Ref graph x y ⟩
  ref-in x y hx hy hR = ∣ GS.ordered x y ,
    subst ⟨_⟩ (sym (graph-spec (GS.ordered x y)))
      (GS.product-in A B x y hx hy , ∣ x , hx , ∣ y , hy , ordered-kpair x y , hR ∣₁ ∣₁)
    , ordered-kpair x y ∣₁

  relation : ⟨ CB.isRelation graph ⟩
  relation p hp = PT.rec (snd (⋁ S (λ x → ⋁ S (λ y → CB.isKPair p x y))))
    (λ { (x , hx , vs) → PT.map (λ { (y , hy , kp , _) → x , ∣ y , kp ∣₁ }) vs })
    (subst ⟨_⟩ (graph-spec p) hp .snd)

  injection : ((x : S) → ⟨ x ∈ˢ A ⟩ → ⟨ ⋁ S (λ y → (y ∈ˢ B) ⊓ R y x) ⟩)
    → ((x y z : S) → ⟨ R y x ⟩ → ⟨ R z x ⟩ → ⟨ y ≈ˢ z ⟩)
    → ((x y z : S) → ⟨ R y x ⟩ → ⟨ R y z ⟩ → ⟨ x ≈ˢ z ⟩)
    → ⟨ CB.isInjection graph A B ⟩
  injection total single injective =
    (relation , λ p hp q hq x y z (kp , kq) → single x y z
      (entry p hp x y kp .snd .snd) (entry q hq x z kq .snd .snd))
    , (λ x hx → PT.map (λ { (y , hy , hR) → y , ref-in x y hx hy hR }) (total x hx))
    , (λ p hp x y kp → entry p hp x y kp .snd .fst)
    , (λ p hp q hq x y z (kp , kq) → injective x y z
        (entry p hp x y kp .snd .snd) (entry q hq z y kq .snd .snd))

module Compress (lem : LEM ℓ) (A n s f y : S)
  (ns : ⟨ CB.isSuccOf s n ⟩)
  (hf : ⟨ CB.isInjection f A s ⟩)
  (hy : ⟨ y ∈ˢ s ⟩)
  (omitted : (u : S) → ⟨ Ref f u y ⟩ → Empty.⊥)
  where

  R : S → S → Ω
  R v u = (Ref f u v ⊓ ((v ≈ˢ n) ⇒ ⊥)) ⊔ (Ref f u n ⊓ (v ≈ˢ y))

  formula : Formula S 2
  formula = (refAt (con f) (var (suc zero)) (var zero) ∧̇ ¬̇ (var zero ≐ con n))
    ∨̇ (refAt (con f) (var (suc zero)) (con n) ∧̇ (var zero ≐ con y))

  reading : (v u : S) → ((v ∷ u ∷ []) ⊨ formula) ≡ R v u
  reading v u = cong₂ _⊔_
    (cong (_⊓ ((v ≈ˢ n) ⇒ ⊥)) (refAt-reading (con f) (var (suc zero)) (var zero) (v ∷ u ∷ [])))
    (cong (_⊓ (v ≈ˢ y)) (refAt-reading (con f) (var (suc zero)) (con n) (v ∷ u ∷ [])))

  module G = Graph A n formula

  below : (v : S) → ⟨ v ∈ˢ s ⟩ → (⟨ v ≈ˢ n ⟩ → Empty.⊥) → ⟨ v ∈ˢ n ⟩
  below v hv neq = PT.rec (snd (v ∈ˢ n))
    (λ { (inl vn) → vn ; (inr eq) → Empty.rec (neq eq) }) (ns .snd .snd v hv)

  total : (u : S) → ⟨ u ∈ˢ A ⟩ → ⟨ ⋁ S (λ v → (v ∈ˢ n) ⊓ R v u) ⟩
  total u hu = PT.rec (snd (⋁ S (λ v → (v ∈ˢ n) ⊓ R v u)))
    (λ { (v , rv) → choose v rv (lem (v ≈ˢ n)) }) (hf .snd .fst u hu)
    where
    choose : (v : S) → ⟨ Ref f u v ⟩ → ⟨ v ≈ˢ n ⟩ ⊎ (⟨ v ≈ˢ n ⟩ → Empty.⊥)
      → ⟨ ⋁ S (λ v' → (v' ∈ˢ n) ⊓ R v' u) ⟩
    choose v rv (inl eq) = ∣ y , below y hy notyn , ∣ inr (rn , CO.≈-refl y) ∣₁ ∣₁
      where
      rn : ⟨ Ref f u n ⟩
      rn = subst (λ z → ⟨ Ref f u z ⟩) (GS.≈→≡ eq) rv
      notyn : ⟨ y ≈ˢ n ⟩ → Empty.⊥
      notyn e = omitted u (subst (λ z → ⟨ Ref f u z ⟩) (sym (GS.≈→≡ e)) rn)
    choose v rv (inr neq) = ∣ v , below v (ref-range f A s u v hf rv) neq
      , ∣ inl (rv , λ eq → Empty.rec (neq eq)) ∣₁ ∣₁

  single : (u v z : S) → ⟨ R v u ⟩ → ⟨ R z u ⟩ → ⟨ v ≈ˢ z ⟩
  single u v z = PT.rec (isPropΠ (λ _ → snd (v ≈ˢ z))) first
    where
    first : ⟨ Ref f u v ⊓ ((v ≈ˢ n) ⇒ ⊥) ⟩ ⊎ ⟨ Ref f u n ⊓ (v ≈ˢ y) ⟩
      → ⟨ R z u ⟩ → ⟨ v ≈ˢ z ⟩
    first (inl (rv , vn)) = PT.rec (snd (v ≈ˢ z)) λ
      { (inl (rz , _)) → ref-single f u v z (hf .fst) rv rz
      ; (inr (rn , _)) → Empty.rec* (vn (ref-single f u v n (hf .fst) rv rn)) }
    first (inr (rn , vy)) = PT.rec (snd (v ≈ˢ z)) λ
      { (inl (rz , zn)) → Empty.rec* (zn (ref-single f u z n (hf .fst) rz rn))
      ; (inr (_ , zy)) → CO.≈-trans v y z vy (CO.≈-sym z y zy) }

  injective : (u v z : S) → ⟨ R v u ⟩ → ⟨ R v z ⟩ → ⟨ u ≈ˢ z ⟩
  injective u v z = PT.rec (isPropΠ (λ _ → snd (u ≈ˢ z))) first
    where
    first : ⟨ Ref f u v ⊓ ((v ≈ˢ n) ⇒ ⊥) ⟩ ⊎ ⟨ Ref f u n ⊓ (v ≈ˢ y) ⟩
      → ⟨ R v z ⟩ → ⟨ u ≈ˢ z ⟩
    first (inl (rv , _)) = PT.rec (snd (u ≈ˢ z)) λ
      { (inl (rz , _)) → ref-injective f A s u v z hf rv rz
      ; (inr (_ , vy)) → Empty.rec (omitted u
          (subst (λ t → ⟨ Ref f u t ⟩) (GS.≈→≡ vy) rv)) }
    first (inr (rn , vy)) = PT.rec (snd (u ≈ˢ z)) λ
      { (inl (rz , _)) → Empty.rec (omitted z
          (subst (λ t → ⟨ Ref f z t ⟩) (GS.≈→≡ vy) rz))
      ; (inr (rn' , _)) → ref-injective f A s u n z hf rn rn' }

  compressed : ⟨ CB.injectable A n ⟩
  compressed = ∣ G.graph , G.injection
    (λ u hu → PT.map (λ { (v , hv , hR) → v , hv , subst ⟨_⟩ (sym (reading v u)) hR }) (total u hu))
    (λ u v z h h' → single u v z (subst ⟨_⟩ (reading v u) h) (subst ⟨_⟩ (reading z u) h'))
    (λ u v z h h' → injective u v z (subst ⟨_⟩ (reading v u) h) (subst ⟨_⟩ (reading v z) h')) ∣₁

compress-omitted : LEM ℓ → (A n s f y : S)
  → ⟨ CB.isSuccOf s n ⟩ → ⟨ CB.isInjection f A s ⟩ → ⟨ y ∈ˢ s ⟩
  → ((u : S) → ⟨ Ref f u y ⟩ → Empty.⊥)
  → ⟨ CB.injectable A n ⟩
compress-omitted = Compress.compressed

MinimumBound : S → S → Ω
MinimumBound A n = CB.injectable A n ⊓
  (⋀ S (λ m → (m ∈ˢ n) ⇒ (CB.injectable A m ⇒ ⊥)))

module Restrict (A B n f : S)
  (sub : (u : S) → ⟨ u ∈ˢ A ⟩ → ⟨ u ∈ˢ B ⟩)
  (hf : ⟨ CB.isInjection f B n ⟩)
  where

  formula : Formula S 2
  formula = refAt (con f) (var (suc zero)) (var zero)

  module G = Graph A n formula

  reading : (v u : S) → ((v ∷ u ∷ []) ⊨ formula) ≡ Ref f u v
  reading v u = refAt-reading (con f) (var (suc zero)) (var zero) (v ∷ u ∷ [])

  restriction : ⟨ CB.isInjection G.graph A n ⟩
  restriction = G.injection
    (λ u hu → PT.map (λ { (v , rv) → v , ref-range f B n u v hf rv
      , subst ⟨_⟩ (sym (reading v u)) rv }) (hf .snd .fst u (sub u hu)))
    (λ u v z h h' → ref-single f u v z (hf .fst)
      (subst ⟨_⟩ (reading v u) h) (subst ⟨_⟩ (reading z u) h'))
    (λ u v z h h' → ref-injective f B n u v z hf
      (subst ⟨_⟩ (reading v u) h) (subst ⟨_⟩ (reading v z) h'))

  restricted-entry : (u v : S) → ⟨ Ref G.graph u v ⟩ → ⟨ (u ∈ˢ A) ⊓ Ref f u v ⟩
  restricted-entry u v h = G.ref-entry u v h .fst
    , subst ⟨_⟩ (reading v u) (G.ref-entry u v h .snd .snd)

strict-bound : LEM ℓ → (w : S) → ⟨ CB.isOmega w ⟩
  → (A B n p : S) → ⟨ n ∈ˢ w ⟩ → ⟨ MinimumBound A n ⟩ → ⟨ CB.injectable B n ⟩
  → ((u : S) → ⟨ u ∈ˢ A ⟩ → ⟨ u ∈ˢ B ⟩)
  → ⟨ p ∈ˢ B ⟩ → (⟨ p ∈ˢ A ⟩ → Empty.⊥) → Empty.⊥
strict-bound lem w hw A B n p hn minimum inj sub hp notp =
  PT.rec Empty.isProp⊥ atInjection inj
  where
  atInjection : Σ[ f ∈ S ] ⟨ CB.isInjection f B n ⟩ → Empty.⊥
  atInjection (f , hf) = PT.rec Empty.isProp⊥ atValue (hf .snd .fst p hp)
    where
    module Res = Restrict A B n f sub hf

    atValue : Σ[ y ∈ S ] ⟨ Ref f p y ⟩ → Empty.⊥
    atValue (y , ry) = atPredecessor (OI.omega-predecessor w hw n hn)
      where
      hy : ⟨ y ∈ˢ n ⟩
      hy = ref-range f B n p y hf ry

      omitted : (u : S) → ⟨ Ref Res.G.graph u y ⟩ → Empty.⊥
      omitted u ru = notp (subst (λ z → ⟨ z ∈ˢ A ⟩)
        (GS.≈→≡ (ref-injective f B n u y p hf (Res.restricted-entry u y ru .snd) ry))
        (Res.restricted-entry u y ru .fst))

      atPredecessor : ⟨ OI.predecessorPred w n ⟩ → Empty.⊥
      atPredecessor = PT.rec Empty.isProp⊥ λ
        { (inl empty) → Empty.rec* (empty y hy)
        ; (inr some) → PT.rec Empty.isProp⊥
            (λ { (m , hm , nm) → Empty.rec* (minimum .snd m (nm .fst)
              (compress-omitted lem A m n Res.G.graph y nm Res.restriction hy omitted)) }) some }

proper-subset-bound : LEM ℓ → (A B n s p : S)
  → ⟨ CB.isSuccOf s n ⟩ → ⟨ CB.injectable B s ⟩
  → ((u : S) → ⟨ u ∈ˢ A ⟩ → ⟨ u ∈ˢ B ⟩)
  → ⟨ p ∈ˢ B ⟩ → (⟨ p ∈ˢ A ⟩ → Empty.⊥)
  → ⟨ CB.injectable A n ⟩
proper-subset-bound lem A B n s p ns inj sub hp notp =
  PT.rec (snd (CB.injectable A n)) atInjection inj
  where
  atInjection : Σ[ f ∈ S ] ⟨ CB.isInjection f B s ⟩ → ⟨ CB.injectable A n ⟩
  atInjection (f , hf) = PT.rec (snd (CB.injectable A n)) atValue (hf .snd .fst p hp)
    where
    module Res = Restrict A B s f sub hf

    atValue : Σ[ y ∈ S ] ⟨ Ref f p y ⟩ → ⟨ CB.injectable A n ⟩
    atValue (y , ry) = compress-omitted lem A n s Res.G.graph y ns Res.restriction
      (ref-range f B s p y hf ry) omitted
      where
      omitted : (u : S) → ⟨ Ref Res.G.graph u y ⟩ → Empty.⊥
      omitted u ru = notp (subst (λ z → ⟨ z ∈ˢ A ⟩)
        (GS.≈→≡ (ref-injective f B s u y p hf (Res.restricted-entry u y ru .snd) ry))
        (Res.restricted-entry u y ru .fst))
