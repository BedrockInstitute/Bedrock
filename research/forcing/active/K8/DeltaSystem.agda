{-# OPTIONS --cubical --safe --guardedness #-}

open import Base.Prelude
open import Base.Truth
open import Base.Classical using ( LEM )
open import FOL.ZFStructure using ( ZFStructure )
import OrdinaryProfile

module K8.DeltaSystem
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
  using ( Formula; var; con; _∈̇_; _≐_; _∧̇_; _⇒̇_; ¬̇_; ∀̇_; ∀̇∈; ∃̇_ )
open import FOL.Semantics (hPropAlgebra ℓ) 𝒮 using ( module At; _^_ )
open import FOL.Manipulation.Renaming using ( renameFo; module Sat )
open import CodedVocabulary 𝒮 using ( subsetΔ; subsetAtˢ; sepAt; sepAt-reading )
open import K8.FiniteVocabulary 𝒮 using ( finiteIn; emptyPred )
open import K8.FiniteSubsets 𝒮 ext paths pow sep using ( finite-subset )
open import OrdinaryProfile 𝒮 using ( ChoiceSet )
open import Cubical.Data.Sum using ( _⊎_; inl; inr )
import Cubical.Data.Empty as Empty
import Cubical.HITs.PropositionalTruncation as PT
open PT using ( ∣_∣₁ )
import CardinalBridge
import K8.GroundSets
import K8.FiniteSets
import K8.CountableUnion
import K8.Uncountability
import K8.OmegaPairing
import K8.OmegaInduction
import K8.OmegaSuccessor
import K8.CountableStars
import K8.DeleteFamilies
import K8.DisjointFamilies
import K8.LayerFamilies

open TruthAlgebra (hPropAlgebra ℓ)
open hPropStructure 𝒮
open At S id using ( _⊨_ )
module CB = CardinalBridge 𝒮
module GS = K8.GroundSets.Ground 𝒮 ext paths pair un pow sep seed
module FS = K8.FiniteSets 𝒮 ext paths pow sep
module CU = K8.CountableUnion 𝒮 ext paths pair un pow sep coll find seed
module UC = K8.Uncountability 𝒮 ext paths pair un pow sep coll find seed
module OP = K8.OmegaPairing 𝒮 ext paths pair un pow sep coll find seed
module OI = K8.OmegaInduction 𝒮 ext paths pair un pow sep seed
module OS = K8.OmegaSuccessor 𝒮 ext paths pair un pow sep find seed
module CS = K8.CountableStars 𝒮 ext paths pair un pow sep coll find seed
module DJ = K8.DisjointFamilies 𝒮 ext paths pair un pow sep seed
module LF = K8.LayerFamilies 𝒮 ext paths pair un pow sep coll find seed
module Ren = Sat (hPropAlgebra ℓ) 𝒮 id
open CB using ( _↔̇_ )

module AtOmega (lem : LEM ℓ) (choice : ChoiceSet) (w : S) (hw : ⟨ CB.isOmega w ⟩) where
  module DF = K8.DeleteFamilies 𝒮 ext paths pair un pow sep coll find seed lem

  Delta : S → S → Ω
  Delta B r = ⋀ S (λ a → (a ∈ˢ B) ⇒ ⋀ S (λ b → (b ∈ˢ B) ⇒
    (((a ≈ˢ b) ⇒ ⊥) ⇒ DF.Intersection a b r)))

  deltaAt : ∀ {n} → Fin n → Fin n → Formula S n
  deltaAt B r = ∀̇∈ (var B) (∀̇∈ (var (suc B))
    (¬̇ (var (suc zero) ≐ var zero) ⇒̇ ∀̇
      (((var zero ∈̇ var (suc (suc zero))) ∧̇ (var zero ∈̇ var (suc zero))) ↔̇
        (var zero ∈̇ var (suc (suc (suc r)))))))

  delta-reading : ∀ {n} (B r : Fin n) (γ : S ^ n)
    → (γ ⊨ deltaAt B r) ≡ Delta (lookup B γ) (lookup r γ)
  delta-reading B r γ = refl

  uncountableFormula : Formula S 1
  uncountableFormula = ¬̇ (sepAt (OP.injectableAt zero (suc zero)) (w ∷ []))

  uncountable-reading : (F : S) → ((F ∷ []) ⊨ uncountableFormula) ≡ UC.uncountable w F
  uncountable-reading F = cong (_⇒ ⊥)
    (sepAt-reading (OP.injectableAt zero (suc zero)) (w ∷ []) F
      ∙ OP.injectableAt-reading zero (suc zero) (F ∷ w ∷ []))

  uncountableAt : ∀ {n} → Fin n → Formula S n
  uncountableAt F = renameFo (λ _ → F) uncountableFormula

  uncountableAt-reading : ∀ {n} (F : Fin n) (γ : S ^ n)
    → (γ ⊨ uncountableAt F) ≡ UC.uncountable w (lookup F γ)
  uncountableAt-reading F γ = Ren.⊨-rename (λ _ → F) uncountableFormula γ (lookup F γ ∷ [])
    (λ { zero → refl }) ∙ uncountable-reading (lookup F γ)

  Result : S → Ω
  Result F = ⋁ S (λ B → subsetΔ B F ⊓ (UC.uncountable w B ⊓ ⋁ S (Delta B)))

  resultFormula : Formula S 1
  resultFormula = ∃̇ (subsetAtˢ zero (suc zero) ∧̇
    (uncountableAt zero ∧̇ ∃̇ (deltaAt (suc zero) zero)))

  result-reading : (F : S) → ((F ∷ []) ⊨ resultFormula) ≡ Result F
  result-reading F = cong (⋁ S) (funExt (λ B → cong (subsetΔ B F ⊓_)
    (cong₂ _⊓_ (uncountableAt-reading zero (B ∷ F ∷ []))
      (cong (⋁ S) (funExt (λ r → delta-reading (suc zero) zero (r ∷ B ∷ F ∷ [])))))))

  resultAt : ∀ {n} → Fin n → Formula S n
  resultAt F = renameFo (λ _ → F) resultFormula

  resultAt-reading : ∀ {n} (F : Fin n) (γ : S ^ n)
    → (γ ⊨ resultAt F) ≡ Result (lookup F γ)
  resultAt-reading F γ = Ren.⊨-rename (λ _ → F) resultFormula γ (lookup F γ ∷ [])
    (λ { zero → refl }) ∙ result-reading (lookup F γ)

  result-upward : (E F : S) → ⟨ subsetΔ E F ⟩ → ⟨ Result E ⟩ → ⟨ Result F ⟩
  result-upward E F sub = PT.map λ { (B , be , unB , root) →
    B , (λ a ha → sub a (be a ha)) , unB , root }

  disjoint-result : (F B : S) → ⟨ subsetΔ B F ⟩ → ⟨ UC.uncountable w B ⟩
    → ⟨ DJ.pairwiseDisjoint B ⟩ → ⟨ Result F ⟩
  disjoint-result F B sub unB dj = ∣ B , sub , unB , ∣ GS.empty ,
    (λ a ha b hb neq z → (λ { (za , zb) → Empty.rec* (dj a ha b hb neq z za zb) })
      , (λ ze → Empty.rec* (GS.empty-out z ze))) ∣₁ ∣₁

  uncountable-distinct : (B a : S) → ⟨ UC.uncountable w B ⟩
    → ⟨ ⋁ S (λ b → (b ∈ˢ B) ⊓ ((b ≈ˢ a) ⇒ ⊥)) ⟩
  uncountable-distinct B a unB = decide (lem target)
    where
    target : Ω
    target = ⋁ S (λ b → (b ∈ˢ B) ⊓ ((b ≈ˢ a) ⇒ ⊥))

    decide : ⟨ target ⟩ ⊎ (⟨ target ⟩ → Empty.⊥) → ⟨ target ⟩
    decide (inl some) = some
    decide (inr absent) = Empty.rec* (unB countB)
      where
      equal : (b : S) → ⟨ b ∈ˢ B ⟩ → ⟨ b ≈ˢ a ⟩
      equal b hb = choose (lem (b ≈ˢ a))
        where
        choose : ⟨ b ≈ˢ a ⟩ ⊎ (⟨ b ≈ˢ a ⟩ → Empty.⊥) → ⟨ b ≈ˢ a ⟩
        choose (inl same) = same
        choose (inr neq) = Empty.rec (absent ∣ b , hb , (λ eq → Empty.rec (neq eq)) ∣₁)

      countB : ⟨ CB.injectable B w ⟩
      countB = CU.choice-injection choice B w (var zero ≐ con OS.zeroSet)
        (λ b hb → ∣ OS.zeroSet , OS.zero-in w hw , OP.CO.≈-refl OS.zeroSet ∣₁)
        (λ b c y hb hc hy sb sc → OP.CO.≈-trans b a c (equal b hb)
          (OP.CO.≈-sym c a (equal c hc)))

  root-subset-member : (B r a : S) → ⟨ a ∈ˢ B ⟩ → ⟨ UC.uncountable w B ⟩
    → ⟨ Delta B r ⟩ → ⟨ subsetΔ r a ⟩
  root-subset-member B r a ha unB delta z zr = PT.rec (snd (z ∈ˢ a))
    (λ { (b , hb , neq) → delta a ha b hb
      (λ eq → neq (OP.CO.≈-sym a b eq)) z .snd zr .fst }) (uncountable-distinct B a unB)

  root-finite : (X B r : S)
    → ((a : S) → ⟨ a ∈ˢ B ⟩ → ⟨ finiteIn X a ⟩)
    → ⟨ UC.uncountable w B ⟩ → ⟨ Delta B r ⟩ → ⟨ finiteIn X r ⟩
  root-finite X B r each unB delta = PT.rec (snd (finiteIn X r))
    (λ { (a , ha , _) → finite-subset lem X a r (each a ha)
      (root-subset-member B r a ha unB delta) }) (uncountable-distinct B OS.zeroSet unB)

  module WithDisjoint
    (disjoint-case : (F X : S)
      → ((a : S) → ⟨ a ∈ˢ F ⟩ → ⟨ finiteIn X a ⟩)
      → ⟨ UC.uncountable w F ⟩
      → ((x : S) → ⟨ x ∈ˢ X ⟩ → ⟨ CB.injectable (CS.Family.star F X x) w ⟩)
      → ⟨ ⋁ S (λ B → subsetΔ B F ⊓ (UC.uncountable w B ⊓ DJ.pairwiseDisjoint B)) ⟩)
    (X : S)
    where

    Uniform : S → Ω
    Uniform n = ⋀ S (λ F → subsetΔ F (FS.finiteSubsets X) ⇒
      ((⋀ S (λ a → (a ∈ˢ F) ⇒ CB.injectable a n)) ⇒
        (UC.uncountable w F ⇒ Result F)))

    uniformFormula : Formula S 1
    uniformFormula = ∀̇ ((∀̇∈ (var zero) (var zero ∈̇ con (FS.finiteSubsets X))) ⇒̇
      ((∀̇∈ (var zero) (OP.injectableAt zero (suc (suc zero)))) ⇒̇
        (uncountableAt zero ⇒̇ resultAt zero)))

    uniform-reading : (n : S) → ((n ∷ []) ⊨ uniformFormula) ≡ Uniform n
    uniform-reading n = cong (⋀ S) (funExt (λ F → cong (subsetΔ F (FS.finiteSubsets X) ⇒_)
      (cong₂ _⇒_
        (cong (⋀ S) (funExt (λ a → cong ((a ∈ˢ F) ⇒_)
          (OP.injectableAt-reading zero (suc (suc zero)) (a ∷ F ∷ n ∷ [])))))
        (cong₂ _⇒_ (uncountableAt-reading zero (F ∷ n ∷ []))
          (resultAt-reading zero (F ∷ n ∷ []))))))

    empty-bound : (a e : S) → ⟨ emptyPred e ⟩ → ⟨ CB.injectable a e ⟩ → ⟨ emptyPred a ⟩
    empty-bound a e he bound x hx = PT.rec (snd ⊥)
      (λ { (f , hf) → PT.rec (snd ⊥)
        (λ { (y , fy) → he y (CU.ref-range f a e x y hf fy) }) (hf .snd .fst x hx) }) bound

    uniform-empty : (e : S) → ⟨ emptyPred e ⟩ → ⟨ Uniform e ⟩
    uniform-empty e he F finite bound unF = Empty.rec* (unF countF)
      where
      countF : ⟨ CB.injectable F w ⟩
      countF = CU.choice-injection choice F w (var zero ≐ con OS.zeroSet)
        (λ a ha → ∣ OS.zeroSet , OS.zero-in w hw , OP.CO.≈-refl OS.zeroSet ∣₁)
        (λ a b y ha hb hy sa sb → subst ⟨_⟩ (sym (paths a b))
          (OS.empty-unique a (empty-bound a e he (bound a ha))
            ∙ sym (OS.empty-unique b (empty-bound b e he (bound b hb)))))

    module Step (n s : S) (hn : ⟨ n ∈ˢ w ⟩) (sn : ⟨ CB.isSuccOf s n ⟩)
      (ih : ⟨ Uniform n ⟩) (F : S)
      (finite : ⟨ subsetΔ F (FS.finiteSubsets X) ⟩)
      (bound : (a : S) → ⟨ a ∈ˢ F ⟩ → ⟨ CB.injectable a s ⟩)
      (unF : ⟨ UC.uncountable w F ⟩) where

      module Stars = CS.Family F X

      each : (a : S) → ⟨ a ∈ˢ F ⟩ → ⟨ finiteIn X a ⟩
      each a ha = subst ⟨_⟩ (FS.finiteSubsets-spec X a) (finite a ha)

      largeStar : Ω
      largeStar = ⋁ S (λ x → (x ∈ˢ X) ⊓ UC.uncountable w (Stars.star x))

      star-case : (x : S) → ⟨ x ∈ˢ X ⟩ → ⟨ UC.uncountable w (Stars.star x) ⟩ → ⟨ Result F ⟩
      star-case x hx unStar = PT.rec (snd (Result F)) pull
        (ih D.D
          (λ d hd → subst ⟨_⟩ (sym (FS.finiteSubsets-spec X d))
            (D.D-finite (λ a ha → each a (Stars.star-sub x a ha)) d hd))
          (D.D-bound n s sn (λ a ha → bound a (Stars.star-sub x a ha)))
          (D.D-uncountable w unStar))
        where
        module D = DF.Family X (Stars.star x) x
          (λ a ha → subst ⟨_⟩ (sym (GS.power-spec X a))
            (each a (Stars.star-sub x a ha) .fst))
          (λ a ha → subst ⟨_⟩ (Stars.star-spec x a) ha .snd)

        pull : Σ[ E ∈ S ] ⟨ subsetΔ E D.D ⊓ (UC.uncountable w E ⊓ ⋁ S (Delta E)) ⟩
          → ⟨ Result F ⟩
        pull (E , sub , unE , roots) = ∣ B.B , (λ a ha → Stars.star-sub x a (B.B-sub a ha))
          , B.B-uncountable w unE , PT.map (λ { (r , dr) →
            GS.join r (GS.singleton x) ,
            (λ a ha b hb → B.root-pullback r (λ d e hd he → dr d hd e he) a b ha hb) }) roots ∣₁
          where
          module B = D.Pullback E sub

      small-stars : (⟨ largeStar ⟩ → Empty.⊥)
        → (x : S) → ⟨ x ∈ˢ X ⟩ → ⟨ CB.injectable (Stars.star x) w ⟩
      small-stars absent x hx = decide (lem (CB.injectable (Stars.star x) w))
        where
        decide : ⟨ CB.injectable (Stars.star x) w ⟩ ⊎ (⟨ CB.injectable (Stars.star x) w ⟩ → Empty.⊥)
          → ⟨ CB.injectable (Stars.star x) w ⟩
        decide (inl count) = count
        decide (inr uncount) = Empty.rec (absent ∣ x , hx , (λ c → Empty.rec (uncount c)) ∣₁)

      conclusion : ⟨ Result F ⟩
      conclusion = decide (lem largeStar)
        where
        decide : ⟨ largeStar ⟩ ⊎ (⟨ largeStar ⟩ → Empty.⊥) → ⟨ Result F ⟩
        decide (inl some) = PT.rec (snd (Result F)) (λ { (x , hx , unStar) → star-case x hx unStar }) some
        decide (inr absent) = PT.rec (snd (Result F))
          (λ { (B , sub , unB , dj) → disjoint-result F B sub unB dj })
          (disjoint-case F X each unF (small-stars absent))

    uniform-delta : (n : S) → ⟨ n ∈ˢ w ⟩ → ⟨ Uniform n ⟩
    uniform-delta n hn = subst ⟨_⟩ (uniform-reading n)
      (OI.omega-induction w hw uniformFormula
        (λ e he ee → subst ⟨_⟩ (sym (uniform-reading e)) (uniform-empty e ee))
        (λ n s hn ih hs sn → subst ⟨_⟩ (sym (uniform-reading s))
          (Step.conclusion n s hn sn (subst ⟨_⟩ (uniform-reading n) ih))) n hn)

    finite-delta : (F : S)
      → ((a : S) → ⟨ a ∈ˢ F ⟩ → ⟨ finiteIn X a ⟩)
      → ⟨ UC.uncountable w F ⟩ → ⟨ Result F ⟩
    finite-delta F each unF = PT.rec (snd (Result F))
      (λ { (n , hn , unLayer) → result-upward (Layers.layer n) F (Layers.layer-sub n)
        (uniform-delta n hn (Layers.layer n)
          (λ a ha → subst ⟨_⟩ (sym (FS.finiteSubsets-spec X a))
            (each a (Layers.layer-sub n a ha))) (Layers.layer-bound n) unLayer) })
      (NaturalLayers.uncountable-layer X each unF)
      where
      module Layers = LF.Family F
      module NaturalLayers = Layers.AtOmega lem choice w hw

    finite-delta-with-root : (F : S)
      → ((a : S) → ⟨ a ∈ˢ F ⟩ → ⟨ finiteIn X a ⟩)
      → ⟨ UC.uncountable w F ⟩
      → ⟨ ⋁ S (λ B → subsetΔ B F ⊓ (UC.uncountable w B ⊓
          ⋁ S (λ r → finiteIn X r ⊓ Delta B r))) ⟩
    finite-delta-with-root F each unF = PT.map (λ { (B , sub , unB , roots) → B , sub , unB ,
      PT.map (λ { (r , delta) → r , root-finite X B r (λ a ha → each a (sub a ha)) unB delta , delta }) roots })
      (finite-delta F each unF)
