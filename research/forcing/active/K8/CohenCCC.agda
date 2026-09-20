{-# OPTIONS --cubical --safe --guardedness #-}

open import Base.Prelude
open import Base.Truth
open import Base.Classical using ( LEM )
open import FOL.ZFStructure using ( ZFStructure )
import OrdinaryProfile

module K8.CohenCCC
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
  (κ w : ZFStructure.S 𝒮) where

open import FOL.ZFStructure using ( module hPropStructure )
open import FOL.Syntax using ( Formula; var; con; _∈̇_; _≐_; _∧̇_; ∀̇_; ∃̇∈ )
open import FOL.Semantics (hPropAlgebra ℓ) 𝒮 using ( module At; _^_ )
open import FOL.Manipulation.Renaming using ( renameFo; module Sat )
open import CodedVocabulary 𝒮 using ( subsetΔ; prAtˢ )
open import K8.FiniteVocabulary 𝒮 using ( finiteIn )
open import OrdinaryProfile 𝒮 using ( ChoiceSet )
open import Cubical.Functions.Logic using ( ⇔toPath )
open import Cubical.Data.Sum using ( _⊎_; inl; inr )
import Cubical.Data.Empty as Empty
import Cubical.HITs.PropositionalTruncation as PT
open PT using ( ∣_∣₁ )
import K8.DomainFamilies
import K8.RootCompatibility
import K8.DeltaSystem
import K8.FullDeltaSystem
import K8.OmegaSuccessor
import K7.ChainConditions
import K8.Cohen
import K8.CohenFibers
import CardinalBridge
import GroundDescription
import K8.FiniteCountable
import K8.FiniteSubsets
import K8.CountableUnion
import K8.Uncountability

open TruthAlgebra (hPropAlgebra ℓ)
open hPropStructure 𝒮
open At S id using ( _⊨_ )
module D = K8.DomainFamilies 𝒮 ext paths pair un pow sep coll find κ w
  using ( toEq; domainFo-out; domainFo-in; domainAt; domainAt-reading; module Family )
module C = K8.Cohen 𝒮 ext paths pair un pow sep κ w
module PM = C.PM
module GS = C.GS
module CF = K8.CohenFibers 𝒮 ext paths pair un pow sep κ w
module CB = CardinalBridge 𝒮
module GD = GroundDescription 𝒮 ext paths
module FC = K8.FiniteCountable 𝒮 ext paths pair un pow sep find κ
module FS = K8.FiniteSubsets 𝒮 ext paths pow sep
module CU = K8.CountableUnion 𝒮 ext paths pair un pow sep coll find κ
module UC = K8.Uncountability 𝒮 ext paths pair un pow sep coll find κ
module RC = K8.RootCompatibility 𝒮 ext paths pair un pow sep κ C.coordinates C.two
module R = RC.R
module CH = K7.ChainConditions 𝒮 ext paths
module OS = K8.OmegaSuccessor 𝒮 ext paths pair un pow sep find κ
module Ren = Sat (hPropAlgebra ℓ) 𝒮 id
open CB using ( _↔̇_ )
open D using ( toEq )

restrictionFo : S → Formula S 2
restrictionFo r = ∀̇ ((var zero ∈̇ var (suc zero)) ↔̇
  ((var zero ∈̇ var (suc (suc zero))) ∧̇ ∃̇∈ (con r) (∃̇∈ (con C.two)
    (prAtˢ (suc (suc zero)) (suc zero) zero))))

restrictionFo-out : (r s p : S) → ⟨ (s ∷ p ∷ []) ⊨ restrictionFo r ⟩
  → s ≡ R.restrict p r
restrictionFo-out r s p h = GD.ext-path λ e →
  ⇔toPath (h e .fst) (h e .snd) ∙ sym (R.restrict-spec p r e)

restrictionFo-in : (r s p : S) → s ≡ R.restrict p r
  → ⟨ (s ∷ p ∷ []) ⊨ restrictionFo r ⟩
restrictionFo-in r s p eq e = subst ⟨_⟩ path , subst ⟨_⟩ (sym path)
  where path = cong (e ∈ˢ_) eq ∙ R.restrict-spec p r e

restrictionAt : ∀ {n} → S → Fin n → Fin n → Formula S n
restrictionAt r s p = renameFo (λ { zero → s ; (suc zero) → p }) (restrictionFo r)

restrictionAt-reading : ∀ {n} (r : S) (s p : Fin n) (γ : S ^ n)
  → (γ ⊨ restrictionAt r s p) ≡ ((lookup s γ ∷ lookup p γ ∷ []) ⊨ restrictionFo r)
restrictionAt-reading r s p γ = Ren.⊨-rename
  (λ { zero → s ; (suc zero) → p }) (restrictionFo r) γ
  (lookup s γ ∷ lookup p γ ∷ []) (λ { zero → refl ; (suc zero) → refl })

rootRelationFo : S → S → Formula S 2
rootRelationFo d r = ∃̇∈ (con d)
  (D.domainAt (suc zero) zero ∧̇ restrictionAt r (suc (suc zero)) zero)

rootRelation : S → S → S → S → Ω
rootRelation d r a s = ⋁ S (λ p → (p ∈ˢ d) ⊓
  ((a ≈ˢ PM.domain p) ⊓ (s ≈ˢ R.restrict p r)))

rootRelation-out : (d r a s : S) → ⟨ (a ∷ s ∷ []) ⊨ rootRelationFo d r ⟩
  → ⟨ rootRelation d r a s ⟩
rootRelation-out d r a s = PT.map λ { (p , hp , da , rs) → p , hp ,
  toEq (D.domainFo-out a p (subst ⟨_⟩ (D.domainAt-reading (suc zero) zero (p ∷ a ∷ s ∷ [])) da)) ,
  toEq (restrictionFo-out r s p
    (subst ⟨_⟩ (restrictionAt-reading r (suc (suc zero)) zero (p ∷ a ∷ s ∷ [])) rs)) }

rootRelation-in : (d r a s p : S) → ⟨ p ∈ˢ d ⟩
  → a ≡ PM.domain p → s ≡ R.restrict p r
  → ⟨ (a ∷ s ∷ []) ⊨ rootRelationFo d r ⟩
rootRelation-in d r a s p hp da rs = ∣ p , hp ,
  subst ⟨_⟩ (sym (D.domainAt-reading (suc zero) zero (p ∷ a ∷ s ∷ []))) (D.domainFo-in a p da) ,
  subst ⟨_⟩ (sym (restrictionAt-reading r (suc (suc zero)) zero (p ∷ a ∷ s ∷ [])))
    (restrictionFo-in r s p rs) ∣₁

module AtOmega (lem : LEM ℓ) (choice : ChoiceSet) (hw : ⟨ CB.isOmega w ⟩) where
  module Delta = K8.DeltaSystem.AtOmega 𝒮 ext paths pair un pow sep coll find κ lem choice w hw
    using ( Delta; Result )

  restriction-in-fiber : (p r : S) → ⟨ p ∈ˢ C.carrier ⟩
    → ⟨ R.restrict p r ∈ˢ CF.F.fiber r ⟩
  restriction-in-fiber p r hp = CF.F.fiber-in r (R.restrict p r)
    (R.restrict-in-carrier lem p r hp)
    (λ x hx → PT.rec (snd (x ∈ˢ r))
      (λ { (y , hy , lookup) → R.lookup-restrict-out p r x y lookup .snd })
      (subst ⟨_⟩ (PM.domain-spec (R.restrict p r) x) hx .snd))

  two-members : (B : S) → ⟨ UC.uncountable w B ⟩
    → ⟨ ⋁ S (λ a → (a ∈ˢ B) ⊓ ⋁ S (λ b → (b ∈ˢ B) ⊓ ((a ≈ˢ b) ⇒ ⊥))) ⟩
  two-members B unB = decide (lem target)
    where
    target : Ω
    target = ⋁ S (λ a → (a ∈ˢ B) ⊓ ⋁ S (λ b → (b ∈ˢ B) ⊓ ((a ≈ˢ b) ⇒ ⊥)))
    decide : ⟨ target ⟩ ⊎ (⟨ target ⟩ → Empty.⊥) → ⟨ target ⟩
    decide (inl yes) = yes
    decide (inr no) = Empty.rec* (unB (CU.choice-injection choice B w
      (var zero ≐ con OS.zeroSet)
      (λ a ha → ∣ OS.zeroSet , OS.zero-in w hw , toEq refl ∣₁)
      (λ a b z ha hb hz sa sb → equal a b ha hb)))
      where
      equal : (a b : S) → ⟨ a ∈ˢ B ⟩ → ⟨ b ∈ˢ B ⟩ → ⟨ a ≈ˢ b ⟩
      equal a b ha hb = eqcase (lem (a ≈ˢ b))
        where
        eqcase : ⟨ a ≈ˢ b ⟩ ⊎ (⟨ a ≈ˢ b ⟩ → Empty.⊥) → ⟨ a ≈ˢ b ⟩
        eqcase (inl eq) = eq
        eqcase (inr neq) = Empty.rec (no ∣ a , ha , ∣ b , hb , (λ eq → Empty.rec (neq eq)) ∣₁ ∣₁)

  module Antichain (d : S) (sub : ⟨ subsetΔ d C.carrier ⟩)
    (anti : ⟨ CH.antichainΔ C.carrier C.order d ⟩) where
    module Dom = D.Family d sub

    module Root (B r : S) (subB : ⟨ subsetΔ B Dom.D ⟩)
      (delta : ⟨ Delta.Delta B r ⟩) where

      relation-single : (s a b : S) → ⟨ a ∈ˢ B ⟩ → ⟨ b ∈ˢ B ⟩
        → ⟨ rootRelation d r a s ⟩ → ⟨ rootRelation d r b s ⟩ → ⟨ a ≈ˢ b ⟩
      relation-single s a b ha hb pa pb = decide (lem (a ≈ˢ b))
        where
        decide : ⟨ a ≈ˢ b ⟩ ⊎ (⟨ a ≈ˢ b ⟩ → Empty.⊥) → ⟨ a ≈ˢ b ⟩
        decide (inl eq) = eq
        decide (inr neq) = PT.rec (snd (a ≈ˢ b))
          (λ { (p , hp , ea , es) → PT.rec (snd (a ≈ˢ b))
            (λ { (q , hq , eb , et) → toEq
              (GS.≈→≡ ea ∙ cong PM.domain (GS.≈→≡
                (RC.antichain-root-injective d p q r anti (sub p hp) hp (sub q hq) hq
                  (λ x ov → delta a ha b hb (λ eq → Empty.rec (neq eq)) x .fst
                    (subst (λ z → ⟨ x ∈ˢ z ⟩) (sym (GS.≈→≡ ea)) (ov .fst) ,
                     subst (λ z → ⟨ x ∈ˢ z ⟩) (sym (GS.≈→≡ eb)) (ov .snd)))
                  (toEq (sym (GS.≈→≡ es) ∙ GS.≈→≡ et)))) ∙ sym (GS.≈→≡ eb)) }) pb }) pa

      root-counts-domains : ⟨ finiteIn C.coordinates r ⟩ → ⟨ CB.injectable B w ⟩
      root-counts-domains finiteR = UC.countable-image choice (CF.F.fiber r) B w
        (rootRelationFo d r) onto
        (λ s a b hs ha hb ea eb → relation-single s a b ha hb
          (rootRelation-out d r a s ea) (rootRelation-out d r b s eb))
        (FC.finite-countable lem w hw C.carrier (CF.F.fiber r)
          (CF.F.finite-fiber lem r finiteR CF.two-finite))
        where
        onto : (a : S) → ⟨ a ∈ˢ B ⟩ → ⟨ ⋁ S (λ s →
          (s ∈ˢ CF.F.fiber r) ⊓ ((a ∷ s ∷ []) ⊨ rootRelationFo d r)) ⟩
        onto a ha = PT.map (λ { (p , hp , ea) → R.restrict p r ,
          restriction-in-fiber p r (sub p hp) ,
          rootRelation-in d r a (R.restrict p r) p hp (GS.≈→≡ ea) refl })
          (Dom.D-out a (subB a ha))

      impossible : ⟨ UC.uncountable w B ⟩ → ⟨ ⊥ ⟩
      impossible unB = PT.rec (snd ⊥)
        (λ { (a , ha , others) → PT.rec (snd ⊥)
          (λ { (b , hb , neq) → unB (root-counts-domains
            (FS.finite-subset lem C.coordinates a r (Dom.D-finite a (subB a ha))
              (λ x hx → delta a ha b hb neq x .snd hx .fst))) }) others }) (two-members B unB)

    delta-impossible : ⟨ Delta.Result Dom.D ⟩ → ⟨ ⊥ ⟩
    delta-impossible = PT.rec (snd ⊥) λ { (B , subB , unB , roots) →
      PT.rec (snd ⊥) (λ { (r , delta) → Root.impossible B r subB delta unB }) roots }

  module FromDelta
    (finite-delta : (X F : S)
      → ((a : S) → ⟨ a ∈ˢ F ⟩ → ⟨ finiteIn X a ⟩)
      → ⟨ UC.uncountable w F ⟩ → ⟨ Delta.Result F ⟩) where

    ccc : ⟨ CH.CCC₂ᴵ C.carrier C.order w ⟩
    ccc d data' = decide (lem (CB.injectable d w))
      where
      module A = Antichain d (data' .fst) (data' .snd)
      decide : ⟨ CB.injectable d w ⟩ ⊎ (⟨ CB.injectable d w ⟩ → Empty.⊥)
        → ⟨ CB.injectable d w ⟩
      decide (inl count) = count
      decide (inr uncount) = Empty.rec* (A.delta-impossible
        (finite-delta C.coordinates A.Dom.D A.Dom.D-finite
          (λ countD → Empty.rec (uncount (A.Dom.conditions-countable lem choice hw countD)))))

  ccc : ⟨ CH.CCC₂ᴵ C.carrier C.order w ⟩
  ccc = FromDelta.ccc Full.finite-delta
    where
    module Full = K8.FullDeltaSystem.AtOmega 𝒮 ext paths pair un pow sep coll find κ
      lem choice w hw using ( finite-delta )
