{-# OPTIONS --cubical --safe --guardedness #-}

open import Base.Prelude
open import Base.Truth
open import Base.Classical using ( LEM )
open import FOL.ZFStructure using ( ZFStructure )
import OrdinaryProfile

module K8.FiniteEnumeration
  {ℓ} (𝒮 : ZFStructure (hPropAlgebra ℓ))
  (ext : OrdinaryProfile.Extensionality 𝒮)
  (paths : (x y : ZFStructure.S 𝒮)
    → ZFStructure._≈ˢ_ 𝒮 x y ≡ ((x ≡ y) , ZFStructure.isSetS 𝒮 x y))
  (pair : OrdinaryProfile.Pairing 𝒮)
  (un : OrdinaryProfile.Union 𝒮)
  (pow : OrdinaryProfile.PowerSet 𝒮)
  (sep : OrdinaryProfile.Separation 𝒮)
  (find : OrdinaryProfile.FoundationInduction 𝒮)
  (seed : ZFStructure.S 𝒮)
  where

open import FOL.ZFStructure using ( module hPropStructure )
open import FOL.Syntax
  using ( Formula; var; con; _≐_; _⇒̇_; ⊥̇; ∀̇_; ∃̇∈ )
open import FOL.Semantics (hPropAlgebra ℓ) 𝒮 using ( module At; _^_ )
open import FOL.Manipulation.Renaming using ( renameFo; module Sat )
open import K8.FiniteVocabulary 𝒮 using ( finiteIn; emptyPred; adjoinPred )
open import K8.FiniteSets 𝒮 ext paths pow sep using ( finite-induction )
import K8.GroundSets
import K7.CardinalOrder
import CardinalBridge
open import Cubical.Data.Sum using ( _⊎_; inl; inr )
import Cubical.Data.Empty as Empty
import Cubical.HITs.PropositionalTruncation as PT
open PT using ( ∣_∣₁ )

open TruthAlgebra (hPropAlgebra ℓ)
open hPropStructure 𝒮
open At S id using ( _⊨_ )

module CB = CardinalBridge 𝒮
module GS = K8.GroundSets.Ground 𝒮 ext paths pair un pow sep seed
module CO = K7.CardinalOrder.Order 𝒮 ext
  (λ x y z e → cong (_∈ˢ z) (GS.≈→≡ e))
  (λ x y z e → cong (x ∈ˢ_) (GS.≈→≡ e))
module Ren = Sat (hPropAlgebra ℓ) 𝒮 id

pairAt : ∀ {n} → Fin n → Fin n → Fin n → Formula S n
pairAt p x y = renameFo emb CB.PairφK
  where
  emb : Fin 3 → _
  emb zero = p
  emb (suc zero) = x
  emb (suc (suc zero)) = y

pairAt-reading : ∀ {n} (p x y : Fin n) (γ : S ^ n)
  → (γ ⊨ pairAt p x y) ≡ CB.isKPair (lookup p γ) (lookup x γ) (lookup y γ)
pairAt-reading p x y γ =
  Ren.⊨-rename emb CB.PairφK γ (lookup p γ ∷ lookup x γ ∷ lookup y γ ∷ []) agrees
  ∙ CB.PairφK-bridge (lookup p γ) (lookup x γ) (lookup y γ)
  where
  emb : Fin 3 → _
  emb zero = p
  emb (suc zero) = x
  emb (suc (suc zero)) = y
  agrees : Ren.Agrees emb γ (lookup p γ ∷ lookup x γ ∷ lookup y γ ∷ [])
  agrees zero = refl
  agrees (suc zero) = refl
  agrees (suc (suc zero)) = refl

notAt : S → S → Ω
notAt x p = ⋀ S (λ u → ⋀ S (λ v →
  CB.isKPair p u v ⇒ ((u ≈ˢ x) ⇒ ⊥)))

notAtFormula : S → Formula S 1
notAtFormula x = ∀̇ (∀̇
  (pairAt (suc (suc zero)) (suc zero) zero
    ⇒̇ ((var (suc zero) ≐ con x) ⇒̇ ⊥̇)))

notAt-reading : (x p : S) → ((p ∷ []) ⊨ notAtFormula x) ≡ notAt x p
notAt-reading x p = cong (⋀ S) (funExt (λ u → cong (⋀ S) (funExt (λ v →
  cong (_⇒ ((u ≈ˢ x) ⇒ ⊥))
    (pairAt-reading (suc (suc zero)) (suc zero) zero (v ∷ u ∷ p ∷ []))))))

module Extend (lem : LEM ℓ) (a b x n s f t : S)
  (ad : ⟨ adjoinPred b a x ⟩)
  (ns : ⟨ CB.isSuccOf s n ⟩)
  (hf : ⟨ CB.isInjection f a n ⟩)
  (ht : ⟨ CB.isKPair t x n ⟩)
  where

  cut : S
  cut = GS.separator f (notAtFormula x)

  cut-spec : (p : S) → (p ∈ˢ cut) ≡ ((p ∈ˢ f) ⊓ notAt x p)
  cut-spec p = GS.separator-spec f (notAtFormula x) p
    ∙ cong ((p ∈ˢ f) ⊓_) (notAt-reading x p)

  graph : S
  graph = GS.join cut (GS.singleton t)

  graph-out : (p : S) → ⟨ p ∈ˢ graph ⟩
    → ⟨ ((p ∈ˢ f) ⊓ notAt x p) ⊔ (p ≈ˢ t) ⟩
  graph-out p hp = PT.map
    (λ { (inl h) → inl (subst ⟨_⟩ (cut-spec p) h)
       ; (inr h) → inr (GS.singleton-witness t .snd p h) })
    (subst ⟨_⟩ (GS.join-spec cut (GS.singleton t) p) hp)

  old-in : (p : S) → ⟨ p ∈ˢ f ⟩ → ⟨ notAt x p ⟩ → ⟨ p ∈ˢ graph ⟩
  old-in p hp keep = subst ⟨_⟩ (sym (GS.join-spec cut (GS.singleton t) p))
    ∣ inl (subst ⟨_⟩ (sym (cut-spec p)) (hp , keep)) ∣₁

  new-in : ⟨ t ∈ˢ graph ⟩
  new-in = subst ⟨_⟩ (sym (GS.join-spec cut (GS.singleton t) t))
    ∣ inr (GS.singleton-witness t .fst) ∣₁

  Old : S → S → Ω
  Old u v = ⋁ S (λ p → (p ∈ˢ f) ⊓ CB.isKPair p u v)

  Entry : S → S → Ω
  Entry u v = ((u ≈ˢ x) ⊓ (v ≈ˢ n)) ⊔ (Old u v ⊓ ((u ≈ˢ x) ⇒ ⊥))

  entry : (p : S) → ⟨ p ∈ˢ graph ⟩ → (u v : S)
    → ⟨ CB.isKPair p u v ⟩ → ⟨ Entry u v ⟩
  entry p hp u v kp = PT.map
    (λ { (inl (pf , keep)) → inr (∣ p , pf , kp ∣₁ , keep u v kp)
       ; (inr eq) → inl (CO.kpair-components pair p u v x n kp
           (subst (λ z → ⟨ CB.isKPair z x n ⟩) (sym (GS.≈→≡ eq)) ht)) })
    (graph-out p hp)

  old-single : (u v z : S) → ⟨ Old u v ⟩ → ⟨ Old u z ⟩ → ⟨ v ≈ˢ z ⟩
  old-single u v z = PT.rec (isPropΠ (λ _ → snd (v ≈ˢ z)))
    (λ { (p , hp , kp) → PT.rec (snd (v ≈ˢ z))
      (λ { (q , hq , kq) → hf .fst .snd p hp q hq u v z (kp , kq) }) })

  old-injective : (u v z : S) → ⟨ Old u v ⟩ → ⟨ Old z v ⟩ → ⟨ u ≈ˢ z ⟩
  old-injective u v z = PT.rec (isPropΠ (λ _ → snd (u ≈ˢ z)))
    (λ { (p , hp , kp) → PT.rec (snd (u ≈ˢ z))
      (λ { (q , hq , kq) → hf .snd .snd .snd p hp q hq u v z (kp , kq) }) })

  old-range : (u v : S) → ⟨ Old u v ⟩ → ⟨ v ∈ˢ n ⟩
  old-range u v = PT.rec (snd (v ∈ˢ n))
    (λ { (p , hp , kp) → hf .snd .snd .fst p hp u v kp })

  fresh : (u v : S) → ⟨ Old u v ⟩ → ⟨ v ≈ˢ n ⟩ → Empty.⊥
  fresh u v old eq = CO.no-self find n
    (subst (λ z → ⟨ z ∈ˢ n ⟩) (GS.≈→≡ eq) (old-range u v old))

  entry-single : (u v z : S) → ⟨ Entry u v ⟩ → ⟨ Entry u z ⟩ → ⟨ v ≈ˢ z ⟩
  entry-single u v z = PT.rec (isPropΠ (λ _ → snd (v ≈ˢ z))) first
    where
    first : (⟨ (u ≈ˢ x) ⊓ (v ≈ˢ n) ⟩ ⊎ ⟨ Old u v ⊓ ((u ≈ˢ x) ⇒ ⊥) ⟩)
      → ⟨ Entry u z ⟩ → ⟨ v ≈ˢ z ⟩
    first (inl (ux , vn)) = PT.rec (snd (v ≈ˢ z)) λ
      { (inl (_ , zn)) → CO.≈-trans v n z vn (CO.≈-sym z n zn)
      ; (inr (_ , no)) → Empty.rec* (no ux) }
    first (inr (old , no)) = PT.rec (snd (v ≈ˢ z)) λ
      { (inl (ux , _)) → Empty.rec* (no ux)
      ; (inr (old' , _)) → old-single u v z old old' }

  entry-injective : (u v z : S) → ⟨ Entry u v ⟩ → ⟨ Entry z v ⟩ → ⟨ u ≈ˢ z ⟩
  entry-injective u v z = PT.rec (isPropΠ (λ _ → snd (u ≈ˢ z))) first
    where
    first : (⟨ (u ≈ˢ x) ⊓ (v ≈ˢ n) ⟩ ⊎ ⟨ Old u v ⊓ ((u ≈ˢ x) ⇒ ⊥) ⟩)
      → ⟨ Entry z v ⟩ → ⟨ u ≈ˢ z ⟩
    first (inl (ux , vn)) = PT.rec (snd (u ≈ˢ z)) λ
      { (inl (zx , _)) → CO.≈-trans u x z ux (CO.≈-sym z x zx)
      ; (inr (old , _)) → Empty.rec (fresh z v old vn) }
    first (inr (old , _)) = PT.rec (snd (u ≈ˢ z)) λ
      { (inl (_ , vn)) → Empty.rec (fresh u v old vn)
      ; (inr (old' , _)) → old-injective u v z old old' }

  entry-range : (u v : S) → ⟨ Entry u v ⟩ → ⟨ v ∈ˢ s ⟩
  entry-range u v = PT.rec (snd (v ∈ˢ s)) λ
    { (inl (_ , vn)) → subst (λ z → ⟨ z ∈ˢ s ⟩) (sym (GS.≈→≡ vn)) (ns .fst)
    ; (inr (old , _)) → ns .snd .fst v (old-range u v old) }

  relation : ⟨ CB.isRelation graph ⟩
  relation p hp = PT.rec (snd (⋁ S (λ u → ⋁ S (λ v → CB.isKPair p u v))))
    (λ { (inl (pf , _)) → hf .fst .fst p pf
       ; (inr eq) → ∣ x , ∣ n ,
           subst (λ z → ⟨ CB.isKPair z x n ⟩) (sym (GS.≈→≡ eq)) ht ∣₁ ∣₁ })
    (graph-out p hp)

  domain : (u : S) → ⟨ u ∈ˢ b ⟩
    → ⟨ ⋁ S (λ v → ⋁ S (λ p → (p ∈ˢ graph) ⊓ CB.isKPair p u v)) ⟩
  domain u hu = decide (lem (u ≈ˢ x))
    where
    target : Ω
    target = ⋁ S (λ v → ⋁ S (λ p → (p ∈ˢ graph) ⊓ CB.isKPair p u v))

    decide : ⟨ u ≈ˢ x ⟩ ⊎ (⟨ u ≈ˢ x ⟩ → Empty.⊥) → ⟨ target ⟩
    decide (inl eq) = ∣ n , ∣ t , new-in ,
      subst (λ z → ⟨ CB.isKPair t z n ⟩) (sym (GS.≈→≡ eq)) ht ∣₁ ∣₁
    decide (inr neq) = PT.rec (snd target) fromA (ad .snd .snd u hu)
      where
      fromA : ⟨ u ∈ˢ a ⟩ ⊎ ⟨ u ≈ˢ x ⟩ → ⟨ target ⟩
      fromA (inr eq) = Empty.rec (neq eq)
      fromA (inl ua) = PT.rec (snd target)
        (λ { (v , some) → PT.rec (snd target)
          (λ { (p , pf , kp) → ∣ v , ∣ p , old-in p pf (keep p v kp) , kp ∣₁ ∣₁ }) some })
        (hf .snd .fst u ua)
        where
        keep : (p v : S) → ⟨ CB.isKPair p u v ⟩ → ⟨ notAt x p ⟩
        keep p v kp u' v' kp' eq = Empty.rec (neq
          (CO.≈-trans u u' x (CO.kpair-components pair p u v u' v' kp kp' .fst) eq))

  graph-injection : ⟨ CB.isInjection graph b s ⟩
  graph-injection =
    ( relation
    , λ p hp q hq u v z ks → entry-single u v z
        (entry p hp u v (ks .fst)) (entry q hq u z (ks .snd)) )
    , domain
    , (λ p hp u v kp → entry-range u v (entry p hp u v kp))
    , λ p hp q hq u v z ks → entry-injective u v z
        (entry p hp u v (ks .fst)) (entry q hq z v (ks .snd))

injectable-adjoin : LEM ℓ → (a b x n s : S)
  → ⟨ adjoinPred b a x ⟩ → ⟨ CB.isSuccOf s n ⟩
  → ⟨ CB.injectable a n ⟩ → ⟨ CB.injectable b s ⟩
injectable-adjoin lem a b x n s ad ns = PT.rec (snd (CB.injectable b s))
  (λ { (f , hf) → PT.rec (snd (CB.injectable b s))
    (λ { (t , ht) → ∣ Extend.graph lem a b x n s f t ad ns hf ht
      , Extend.graph-injection lem a b x n s f t ad ns hf ht ∣₁ })
    (CO.kpairOf pair x n) })

finiteBound : S → S → Ω
finiteBound w a = ⋁ S (λ n → (n ∈ˢ w) ⊓ CB.injectable a n)

finiteBoundFormula : S → Formula S 1
finiteBoundFormula w = ∃̇∈ (con w) (renameFo swap CB.Injectableφ)
  where
  swap : Fin 2 → Fin 2
  swap zero = suc zero
  swap (suc zero) = zero

finiteBound-reading : (w a : S)
  → ((a ∷ []) ⊨ finiteBoundFormula w) ≡ finiteBound w a
finiteBound-reading w a = cong (⋁ S) (funExt (λ n → cong ((n ∈ˢ w) ⊓_)
  (Ren.⊨-rename swap CB.Injectableφ (n ∷ a ∷ []) (a ∷ n ∷ []) (agrees n)
    ∙ CB.Injectable-bridge a n)))
  where
  swap : Fin 2 → Fin 2
  swap zero = suc zero
  swap (suc zero) = zero
  agrees : (n : S) → Ren.Agrees swap (n ∷ a ∷ []) (a ∷ n ∷ [])
  agrees n zero = refl
  agrees n (suc zero) = refl

empty-injectable : (e n : S) → ⟨ emptyPred e ⟩ → ⟨ CB.injectable e n ⟩
empty-injectable e n he = ∣ GS.empty ,
  ( (λ p hp → Empty.rec* (GS.empty-out p hp))
  , (λ p hp q hq u v z ks → Empty.rec* (GS.empty-out p hp)) )
  , (λ u hu → Empty.rec* (he u hu))
  , (λ p hp u v kp → Empty.rec* (GS.empty-out p hp))
  , (λ p hp q hq u v z ks → Empty.rec* (GS.empty-out p hp)) ∣₁

finite-size-bound : LEM ℓ → (w : S) → ⟨ CB.isOmega w ⟩
  → (X a : S) → ⟨ finiteIn X a ⟩ → ⟨ finiteBound w a ⟩
finite-size-bound lem w hw X a ha = subst ⟨_⟩ (finiteBound-reading w a)
  (finite-induction X (finiteBoundFormula w) base step a ha)
  where
  base : (e : S) → ⟨ emptyPred e ⟩ → ⟨ (e ∷ []) ⊨ finiteBoundFormula w ⟩
  base e he = subst ⟨_⟩ (sym (finiteBound-reading w e))
    (PT.map (λ { (n , nw , _) → n , nw , empty-injectable e n he }) (hw .fst .fst))

  step : (a' b x : S) → ⟨ finiteIn X a' ⟩
    → ⟨ (a' ∷ []) ⊨ finiteBoundFormula w ⟩
    → ⟨ x ∈ˢ X ⟩ → ⟨ adjoinPred b a' x ⟩
    → ⟨ (b ∷ []) ⊨ finiteBoundFormula w ⟩
  step a' b x ha' ih hx ad = subst ⟨_⟩ (sym (finiteBound-reading w b))
    (PT.rec (snd (finiteBound w b))
      (λ { (n , nw , inj) → PT.map
        (λ { (s , sw , ns) → s , sw , injectable-adjoin lem a' b x n s ad ns inj })
        (hw .fst .snd n nw) })
      (subst ⟨_⟩ (finiteBound-reading w a') ih))
