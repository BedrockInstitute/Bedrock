{-# OPTIONS --cubical --safe --guardedness #-}

open import Base.Prelude
open import Base.Truth

open import FOL.ZFStructure using ( module hPropStructure; Transitive; _↾_ )
open import V.Hierarchy using ( 𝒮ᵥ )
open import Cubical.HITs.CumulativeHierarchy.Base using ( V )
open import Cubical.HITs.CumulativeHierarchy.Constructions
  using ( ⁅_,_⁆ ) renaming ( module InfinitySet to Inf )
open Inf using ( #_; sucV )

module LJ-1-210.GenModel {ℓ : Level}
  (M : V ℓ → hProp (ℓ-suc ℓ))
  (M-trans : Transitive (𝒮ᵥ {ℓ}) M)
  (numeralL : ℕ → Σ[ x ∈ V ℓ ] ⟨ M x ⟩)
  (numeralL-fst : (k : ℕ) → fst (numeralL k) ≡ # k)
  (pairʟ : (a b : Σ[ x ∈ V ℓ ] ⟨ M x ⟩) → Σ[ x ∈ V ℓ ] ⟨ M x ⟩)
  (pairʟ-fst : (a b : Σ[ x ∈ V ℓ ] ⟨ M x ⟩)
             → fst (pairʟ a b) ≡ ⁅ fst a , fst b ⁆)
  (sucʟ : Σ[ x ∈ V ℓ ] ⟨ M x ⟩ → Σ[ x ∈ V ℓ ] ⟨ M x ⟩)
  (sucʟ-fst : (a : Σ[ x ∈ V ℓ ] ⟨ M x ⟩) → fst (sucʟ a) ≡ sucV (fst a))
  where

open import FOL.Syntax
  using ( Term; Formula; var; con; _∈̇_; _≐_; _∧̇_; _∨̇_; _⇒̇_; ¬̇_; ⊤̇; ⊥̇
        ; ∀̇_; ∀̇∈; ∃̇_; ∃̇∈ )
open import FOL.Manipulation.Relabelling using ( mapTm; mapFo; ⊨-map )
open import FOL.LevyHierarchy using ( Δ₀ )
import FOL.Absoluteness
import FOL.Semantics
import FOL.Coding
open import V.Coding {ℓ} using ( pr; pr-inj; #-inj′; module VCode )
open import V.Model {ℓ} using ( pair-singleton )
open import FOL.Manipulation.Bounding using ( BoundedFo; module Relabel )
open import L.Coding.Base {ℓ}
  using ( prAt; Δ₀-prAt; prAt-adequate )
open import L.Coding.Environment {ℓ}
  using ( sucAt; Δ₀-sucAt; sucAt-adequate; consAt; Δ₀-consAt; consAt-adequate
        ; env; cons; shiftPairAt; sgl0At; pair0At; tag0At )
open import Cubical.Data.Sigma using ( Σ≡Prop )
open import Cubical.Foundations.Prelude using ( subst2 )
open import Cubical.Data.Vec using ( map )
open import Cubical.Data.Nat using ( _+_ )
open import Cubical.Data.FinData using ( toℕ )
open import Cubical.Functions.Logic using ( ⇔toPath; ∃[∶]-syntax )
open import Cubical.Data.Sum using ( _⊎_; inl; inr )
import Cubical.HITs.PropositionalTruncation as PT
open PT using ( ∣_∣₁; ∥_∥₁; squash₁ )
open import Cubical.HITs.CumulativeHierarchy.Base using ( V; setIsSet; _∈_ )
open import Cubical.HITs.CumulativeHierarchy.Constructions using ( ⁅_,_⁆ )
open import Cubical.HITs.CumulativeHierarchy.Constructions using ( module InfinitySet )
open InfinitySet using ( #_; sucV )

open TruthAlgebra (hPropAlgebra (ℓ-suc ℓ))
open hPropStructure (𝒮ᵥ {ℓ} ↾ M) using ( S )

module AbsL = FOL.Absoluteness.Single (𝒮ᵥ {ℓ}) M M-trans
open AbsL using ( _^_ ) renaming ( _⊨ᵐ_ to _⊨_ )

module SemV = FOL.Semantics (hPropAlgebra (ℓ-suc ℓ)) (𝒮ᵥ {ℓ})
open SemV.At (V ℓ) id using () renaming ( _⊨_ to _⊨v_ )

InL : V ℓ → Type (ℓ-suc ℓ)
InL c = ⟨ M c ⟩

module ToL = Relabel {K = V ℓ} {K' = S} {W = V ℓ}
  id fst InL (λ c p → c , p) (λ c p → refl)

open ToL using ( liftFo; Δ₀-liftFo )

transferFo : ∀ {n} (φ : Formula (V ℓ) n) (h : BoundedFo InL φ) → Δ₀ φ
           → (γ : S ^ n) → (γ ⊨ liftFo φ h) ≡ ((map fst γ) ⊨v φ)
transferFo φ h dφ γ =
    AbsL.abs₀ (Δ₀-liftFo h dφ) γ
  ∙ sym (⊨-map (hPropAlgebra (ℓ-suc ℓ)) (𝒮ᵥ {ℓ}) fst id (liftFo φ h) (map fst γ))
  ∙ cong (λ ψ → (map fst γ) ⊨v ψ) (ToL.liftFo-correct φ h)
  ∙ ⊨-map (hPropAlgebra (ℓ-suc ℓ)) (𝒮ᵥ {ℓ}) id id φ (map fst γ)

lookup-fst : ∀ {n} (i : Fin n) (γ : S ^ n)
           → lookup i (map fst γ) ≡ fst (lookup i γ)
lookup-fst zero    (x ∷ γ) = refl
lookup-fst (suc i) (x ∷ γ) = lookup-fst i γ
private
  PairIs : V ℓ → V ℓ → Ω
  PairIs a p = (a ≡ p) , setIsSet a p

prAtL : ∀ {n} → Fin n → Fin n → Fin n → Formula S n
prAtL q u v = liftFo (prAt q u v) _

prAtL-adequate : ∀ {n} (q u v : Fin n) (γ : S ^ n)
  → (γ ⊨ prAtL q u v)
  ≡ PairIs (fst (lookup q γ)) (pr (fst (lookup u γ)) (fst (lookup v γ)))
prAtL-adequate q u v γ =
    transferFo (prAt q u v) _ (Δ₀-prAt q u v) γ
  ∙ prAt-adequate q u v (map fst γ)
  ∙ cong₂ PairIs (lookup-fst q γ)
      (cong₂ pr (lookup-fst u γ) (lookup-fst v γ))
appAt : ∀ {n} → Fin n → Fin n → Fin n → Formula S n
appAt f x y = ∃̇∈ (var f) (prAtL zero (suc x) (suc y))

appAt-adequate : ∀ {n} (f x y : Fin n) (γ : S ^ n)
  → (γ ⊨ appAt f x y)
  ≡ (pr (fst (lookup x γ)) (fst (lookup y γ)) ∈ fst (lookup f γ))
appAt-adequate f x y γ = ⇔toPath fwd bwd
  where
  a = fst (lookup x γ)
  b = fst (lookup y γ)
  F = lookup f γ

  read : (z : S) → ⟨ (z ∷ γ) ⊨ prAtL zero (suc x) (suc y) ⟩ → fst z ≡ pr a b
  read z h = subst ⟨_⟩ (prAtL-adequate zero (suc x) (suc y) (z ∷ γ)) h

  fwd : ⟨ γ ⊨ appAt f x y ⟩ → ⟨ pr a b ∈ fst F ⟩
  fwd = PT.rec (snd (pr a b ∈ fst F))
    (λ { (z , (z∈F , h)) → subst (λ w → ⟨ w ∈ fst F ⟩) (read z h) z∈F })

  bwd : ⟨ pr a b ∈ fst F ⟩ → ⟨ γ ⊨ appAt f x y ⟩
  bwd h = ∣ zS , (h , subst ⟨_⟩
      (sym (prAtL-adequate zero (suc x) (suc y) (zS ∷ γ))) refl) ∣₁
    where
    zS : S
    zS = pr a b , M-trans {x = fst F} {y = pr a b} h (F .snd)
svAt : ∀ {n} → Fin n → Formula S n
svAt f = ∀̇ (∀̇ (∀̇ (
      appAt (suc (suc (suc f))) (suc (suc zero)) (suc zero)
  ⇒̇ (appAt (suc (suc (suc f))) (suc (suc zero)) zero
  ⇒̇ (var (suc zero) ≐ var zero)))))

module _ {n : ℕ} (f : Fin n) (γ : S ^ n) where
  private
    Holds : S → S → Type (ℓ-suc ℓ)
    Holds x y = ⟨ pr (fst x) (fst y) ∈ fst (lookup f γ) ⟩

    at : (x y y' : S)
       → ((y' ∷ y ∷ x ∷ γ) ⊨ appAt (suc (suc (suc f))) (suc (suc zero)) (suc zero))
       ≡ (pr (fst x) (fst y) ∈ fst (lookup f γ))
    at x y y' = appAt-adequate (suc (suc (suc f))) (suc (suc zero)) (suc zero)
                  (y' ∷ y ∷ x ∷ γ)

    at' : (x y y' : S)
        → ((y' ∷ y ∷ x ∷ γ) ⊨ appAt (suc (suc (suc f))) (suc (suc zero)) zero)
        ≡ (pr (fst x) (fst y') ∈ fst (lookup f γ))
    at' x y y' = appAt-adequate (suc (suc (suc f))) (suc (suc zero)) zero
                   (y' ∷ y ∷ x ∷ γ)

  svAt-out : ⟨ γ ⊨ svAt f ⟩
           → (x y y' : S) → Holds x y → Holds x y' → fst y ≡ fst y'
  svAt-out h x y y' p q = h x y y'
    (subst ⟨_⟩ (sym (at x y y')) p) (subst ⟨_⟩ (sym (at' x y y')) q)

  svAt-in : ((x y y' : S) → Holds x y → Holds x y' → fst y ≡ fst y')
          → ⟨ γ ⊨ svAt f ⟩
  svAt-in h x y y' p q = h x y y'
    (subst ⟨_⟩ (at x y y') p) (subst ⟨_⟩ (at' x y y') q)
inDomAt : ∀ {n} → Fin n → Fin n → Formula S n
inDomAt f x = ∃̇ (appAt (suc f) (suc x) zero)

inDomAt-adequate : ∀ {n} (f x : Fin n) (γ : S ^ n)
  → (γ ⊨ inDomAt f x)
  ≡ (∃[ y ∶ S ] (pr (fst (lookup x γ)) (fst y) ∈ fst (lookup f γ)))
inDomAt-adequate f x γ =
  cong (⋁ S) (funExt (λ y → appAt-adequate (suc f) (suc x) zero (y ∷ γ)))

domAt : ∀ {n} → Fin n → Fin n → Formula S n
domAt f d = ∀̇ ( (inDomAt (suc f) zero ⇒̇ (var zero ∈̇ var (suc d)))
             ∧̇ ((var zero ∈̇ var (suc d)) ⇒̇ inDomAt (suc f) zero) )

module _ {n : ℕ} (f d : Fin n) (γ : S ^ n) where
  private
    step : (x : S)
         → ((x ∷ γ) ⊨ inDomAt (suc f) zero)
         ≡ (∃[ y ∶ S ] (pr (fst x) (fst y) ∈ fst (lookup f γ)))
    step x = inDomAt-adequate (suc f) zero (x ∷ γ)

  domAt-out : ⟨ γ ⊨ domAt f d ⟩ → (x y : S)
            → ⟨ pr (fst x) (fst y) ∈ fst (lookup f γ) ⟩
            → ⟨ fst x ∈ fst (lookup d γ) ⟩
  domAt-out h x y p = h x .fst (subst ⟨_⟩ (sym (step x)) ∣ y , p ∣₁)

  domAt-in : ⟨ γ ⊨ domAt f d ⟩ → (x : S) → ⟨ fst x ∈ fst (lookup d γ) ⟩
           → ∥ (Σ[ y ∈ S ] ⟨ pr (fst x) (fst y) ∈ fst (lookup f γ) ⟩) ∥₁
  domAt-in h x m = subst ⟨_⟩ (step x) (h x .snd m)

  domAt-intro : ((x : S)
                 → (⟨ ∃[ y ∶ S ] (pr (fst x) (fst y) ∈ fst (lookup f γ)) ⟩
                    → ⟨ fst x ∈ fst (lookup d γ) ⟩)
                 × (⟨ fst x ∈ fst (lookup d γ) ⟩
                    → ⟨ ∃[ y ∶ S ] (pr (fst x) (fst y) ∈ fst (lookup f γ)) ⟩))
              → ⟨ γ ⊨ domAt f d ⟩
  domAt-intro g x = (λ h → g x .fst (subst ⟨_⟩ (step x) h))
                  , (λ m → subst ⟨_⟩ (sym (step x)) (g x .snd m))
prʟ : S → S → S
prʟ a b = pairʟ (pairʟ a a) (pairʟ a b)

prʟ-fst : (a b : S) → fst (prʟ a b) ≡ pr (fst a) (fst b)
prʟ-fst a b =
    pairʟ-fst (pairʟ a a) (pairʟ a b)
  ∙ cong₂ ⁅_,_⁆ (pairʟ-fst a a ∙ pair-singleton (fst a)) (pairʟ-fst a b)
prʟ-inj : {a b c d : S} → prʟ a b ≡ prʟ c d → (a ≡ c) × (b ≡ d)
prʟ-inj {a} {b} {c} {d} e =
    Σ≡Prop (λ v → snd (M v)) (pr-inj q .fst)
  , Σ≡Prop (λ v → snd (M v)) (pr-inj q .snd)
  where
  q : pr (fst a) (fst b) ≡ pr (fst c) (fst d)
  q = sym (prʟ-fst a b) ∙ cong fst e ∙ prʟ-fst c d

numeralL-inj : {j k : ℕ} → numeralL j ≡ numeralL k → j ≡ k
numeralL-inj {j} {k} e =
  #-inj′ (sym (numeralL-fst j) ∙ cong fst e ∙ numeralL-fst k)

module LCode = FOL.Coding {ℓ-suc ℓ} (𝒮ᵥ {ℓ} ↾ M) prʟ prʟ-inj numeralL numeralL-inj

tagBridge : (k : ℕ) (x : S) → fst (LCode.mkTag k x) ≡ VCode.mkTag k (fst x)
tagBridge k x = prʟ-fst (numeralL k) x ∙ cong₂ pr (numeralL-fst k) refl

codeBridgeTm : ∀ {n} (t : Term S n) → fst LCode.⌜ t ⌝ᵗ ≡ VCode.⌜ mapTm fst t ⌝ᵗ
codeBridgeTm (con c) = tagBridge 0 c
codeBridgeTm (var i) =
  tagBridge 1 (numeralL (toℕ i)) ∙ cong (VCode.mkTag 1) (numeralL-fst (toℕ i))

codeBridge : ∀ {n} (φ : Formula S n) → fst LCode.⌜ φ ⌝ ≡ VCode.⌜ mapFo fst φ ⌝
codeBridge (t ∈̇ u) = tagBridge 0 _ ∙ cong (VCode.mkTag 0)
  (prʟ-fst _ _ ∙ cong₂ pr (codeBridgeTm t) (codeBridgeTm u))
codeBridge (t ≐ u) = tagBridge 1 _ ∙ cong (VCode.mkTag 1)
  (prʟ-fst _ _ ∙ cong₂ pr (codeBridgeTm t) (codeBridgeTm u))
codeBridge (a ∧̇ b) = tagBridge 2 _ ∙ cong (VCode.mkTag 2)
  (prʟ-fst _ _ ∙ cong₂ pr (codeBridge a) (codeBridge b))
codeBridge (a ∨̇ b) = tagBridge 3 _ ∙ cong (VCode.mkTag 3)
  (prʟ-fst _ _ ∙ cong₂ pr (codeBridge a) (codeBridge b))
codeBridge (a ⇒̇ b) = tagBridge 4 _ ∙ cong (VCode.mkTag 4)
  (prʟ-fst _ _ ∙ cong₂ pr (codeBridge a) (codeBridge b))
codeBridge (¬̇ a)   = tagBridge 5 _ ∙ cong (VCode.mkTag 5) (codeBridge a)
codeBridge ⊤̇       = tagBridge 6 _ ∙ cong (VCode.mkTag 6) (numeralL-fst 0)
codeBridge ⊥̇       = tagBridge 7 _ ∙ cong (VCode.mkTag 7) (numeralL-fst 0)
codeBridge (∃̇ a)   = tagBridge 8 _ ∙ cong (VCode.mkTag 8) (codeBridge a)
codeBridge (∀̇ a)   = tagBridge 9 _ ∙ cong (VCode.mkTag 9) (codeBridge a)
codeBridge (∀̇∈ t a) = tagBridge 10 _ ∙ cong (VCode.mkTag 10)
  (prʟ-fst _ _ ∙ cong₂ pr (codeBridgeTm t) (codeBridge a))
codeBridge (∃̇∈ t a) = tagBridge 11 _ ∙ cong (VCode.mkTag 11)
  (prʟ-fst _ _ ∙ cong₂ pr (codeBridgeTm t) (codeBridge a))



valuesInAt : ∀ {n} → Fin n → Fin n → Formula S n
valuesInAt f B = ∀̇ (∀̇ ( appAt (suc (suc f)) (suc zero) zero
                     ⇒̇ (var zero ∈̇ var (suc (suc B))) ))

valuesInAt-out : ∀ {n} (f B : Fin n) (γ : S ^ n)
               → ⟨ γ ⊨ valuesInAt f B ⟩ → (x y : S)
               → ⟨ pr (fst x) (fst y) ∈ fst (lookup f γ) ⟩
               → ⟨ fst y ∈ fst (lookup B γ) ⟩
valuesInAt-out f B γ h x y p = h x y
  (subst ⟨_⟩ (sym (appAt-adequate (suc (suc f)) (suc zero) zero (y ∷ x ∷ γ))) p)

pairsInAt : ∀ {n} → Fin n → Fin n → Fin n → Formula S n
pairsInAt e d B =
  ∀̇∈ (var e) (∃̇∈ (var (suc d)) (∃̇∈ (var (suc (suc B)))
    (prAtL (suc (suc zero)) (suc zero) zero)))

pairsIn-out : ∀ {n} (e d B : Fin n) (γ : S ^ n) → ⟨ γ ⊨ pairsInAt e d B ⟩
            → (s : S) → ⟨ fst s ∈ fst (lookup e γ) ⟩
            → ∥ (Σ[ u ∈ S ] (Σ[ v ∈ S ]
                  (⟨ fst u ∈ fst (lookup d γ) ⟩
                   × (⟨ fst v ∈ fst (lookup B γ) ⟩
                      × (fst s ≡ pr (fst u) (fst v)))))) ∥₁
pairsIn-out e d B γ h s s∈ = PT.rec squash₁
  (λ { (u , (u∈ , hv)) → PT.map
    (λ { (v , (v∈ , hp)) → u , (v , (u∈ , (v∈ , subst ⟨_⟩
      (prAtL-adequate (suc (suc zero)) (suc zero) zero (v ∷ u ∷ s ∷ γ)) hp))) })
    hv })
  (h s s∈)

pairsIn-in : ∀ {n} (e d B : Fin n) (γ : S ^ n)
           → ((s : S) → ⟨ fst s ∈ fst (lookup e γ) ⟩
              → ∥ (Σ[ u ∈ S ] (Σ[ v ∈ S ]
                    (⟨ fst u ∈ fst (lookup d γ) ⟩
                     × (⟨ fst v ∈ fst (lookup B γ) ⟩
                        × (fst s ≡ pr (fst u) (fst v)))))) ∥₁)
           → ⟨ γ ⊨ pairsInAt e d B ⟩
pairsIn-in e d B γ k s s∈ = PT.map
  (λ { (u , (v , (u∈ , (v∈ , eq)))) → u , (u∈ , ∣ v , (v∈ , subst ⟨_⟩
    (sym (prAtL-adequate (suc (suc zero)) (suc zero) zero (v ∷ u ∷ s ∷ γ))) eq) ∣₁) })
  (k s s∈)

envOverAt : ∀ {n} → Fin n → Fin n → Fin n → Formula S n
envOverAt e d B =
  svAt e ∧̇ (domAt e d ∧̇ (valuesInAt e B ∧̇ pairsInAt e d B))

module _ {n : ℕ} (e d B : Fin n) (γ : S ^ n) (h : ⟨ γ ⊨ envOverAt e d B ⟩) where
  envOver-sv     : ⟨ γ ⊨ svAt e ⟩
  envOver-sv     = h .fst
  envOver-dom    : ⟨ γ ⊨ domAt e d ⟩
  envOver-dom    = h .snd .fst
  envOver-values : ⟨ γ ⊨ valuesInAt e B ⟩
  envOver-values = h .snd .snd .fst
  envOver-pairs  : ⟨ γ ⊨ pairsInAt e d B ⟩
  envOver-pairs  = h .snd .snd .snd
valuesInAt-in : ∀ {n} (f B : Fin n) (γ : S ^ n)
              → ((x y : S) → ⟨ pr (fst x) (fst y) ∈ fst (lookup f γ) ⟩
                 → ⟨ fst y ∈ fst (lookup B γ) ⟩)
              → ⟨ γ ⊨ valuesInAt f B ⟩
valuesInAt-in f B γ k x y hp = k x y
  (subst ⟨_⟩ (appAt-adequate (suc (suc f)) (suc zero) zero (y ∷ x ∷ γ)) hp)

envOverAt-transport : ∀ {n n'} (γ : S ^ n) (γ' : S ^ n')
                      (e d B : Fin n) (e' d' B' : Fin n')
                    → fst (lookup e γ) ≡ fst (lookup e' γ')
                    → fst (lookup d γ) ≡ fst (lookup d' γ')
                    → fst (lookup B γ) ≡ fst (lookup B' γ')
                    → ⟨ γ ⊨ envOverAt e d B ⟩ → ⟨ γ' ⊨ envOverAt e' d' B' ⟩
envOverAt-transport γ γ' e d B e' d' B' qe qd qb h =
    svAt-in e' γ' (λ x y y' p q →
      svAt-out e γ (envOver-sv e d B γ h) x y y'
        (subst ⟨_⟩ (sym (at x y)) p) (subst ⟨_⟩ (sym (at x y')) q))
  , ( domAt-intro e' d' γ'
      (λ x → (λ m → subst (λ w → ⟨ fst x ∈ w ⟩) qd
                (PT.rec (snd (fst x ∈ fst (lookup d γ)))
                  (λ { (y , p) → domAt-out e d γ (envOver-dom e d B γ h) x y
                         (subst ⟨_⟩ (sym (at x y)) p) })
                  m))
            , (λ hx → PT.map (λ { (y , p) → y , subst ⟨_⟩ (at x y) p })
                (domAt-in e d γ (envOver-dom e d B γ h) x
                  (subst (λ w → ⟨ fst x ∈ w ⟩) (sym qd) hx))))
    , ( valuesInAt-in e' B' γ'
        (λ x y p → subst (λ w → ⟨ fst y ∈ w ⟩) qb
          (valuesInAt-out e B γ (envOver-values e d B γ h) x y
            (subst ⟨_⟩ (sym (at x y)) p)))
      , pairsIn-in e' d' B' γ'
        (λ s s∈ → PT.map
          (λ { (u , (v , (u∈ , (v∈ , eq)))) →
            u , (v , ( subst (λ w → ⟨ fst u ∈ w ⟩) qd u∈
                     , ( subst (λ w → ⟨ fst v ∈ w ⟩) qb v∈ , eq ) )) })
          (pairsIn-out e d B γ (envOver-pairs e d B γ h) s
            (subst (λ w → ⟨ fst s ∈ w ⟩) (sym qe) s∈))) ) )
  where
  at : (x y : S) → (pr (fst x) (fst y) ∈ fst (lookup e γ))
                 ≡ (pr (fst x) (fst y) ∈ fst (lookup e' γ'))
  at x y = cong (λ w → pr (fst x) (fst y) ∈ w) qe
tagAtL : ∀ {n} → Fin n → ℕ → Fin n → Formula S n
tagAtL s k x = ∃̇ ((var zero ≐ con (numeralL k)) ∧̇ prAtL (suc s) zero (suc x))

tagAtL-adequate : ∀ {n} (s : Fin n) (k : ℕ) (x : Fin n) (γ : S ^ n)
  → (γ ⊨ tagAtL s k x)
  ≡ PairIs (fst (lookup s γ)) (pr (# k) (fst (lookup x γ)))
tagAtL-adequate s k x γ = ⇔toPath fwd bwd
  where
  target = PairIs (fst (lookup s γ)) (pr (# k) (fst (lookup x γ)))

  fwd : ⟨ γ ⊨ tagAtL s k x ⟩ → ⟨ target ⟩
  fwd = PT.rec (snd target)
    (λ { (z , (e , p)) →
      subst ⟨_⟩ (prAtL-adequate (suc s) zero (suc x) (z ∷ γ)) p
      ∙ cong (λ w → pr w (fst (lookup x γ))) (e ∙ numeralL-fst k) })

  bwd : ⟨ target ⟩ → ⟨ γ ⊨ tagAtL s k x ⟩
  bwd q = ∣ numeralL k , (refl , subst ⟨_⟩
      (sym (prAtL-adequate (suc s) zero (suc x) (numeralL k ∷ γ)))
      (q ∙ cong (λ w → pr w (fst (lookup x γ))) (sym (numeralL-fst k)))) ∣₁

tagPairAtL : ∀ {n} → Fin n → ℕ → Fin n → Fin n → Formula S n
tagPairAtL s k a b =
  ∃̇ (prAtL zero (suc a) (suc b) ∧̇ tagAtL (suc s) k zero)

tagPairAtL-adequate : ∀ {n} (s : Fin n) (k : ℕ) (a b : Fin n) (γ : S ^ n)
  → (γ ⊨ tagPairAtL s k a b)
  ≡ PairIs (fst (lookup s γ))
      (pr (# k) (pr (fst (lookup a γ)) (fst (lookup b γ))))
tagPairAtL-adequate s k a b γ = ⇔toPath fwd bwd
  where
  A = fst (lookup a γ)
  B = fst (lookup b γ)
  target = PairIs (fst (lookup s γ)) (pr (# k) (pr A B))

  fwd : ⟨ γ ⊨ tagPairAtL s k a b ⟩ → ⟨ target ⟩
  fwd = PT.rec (snd target)
    (λ { (z , (p , t)) →
      subst ⟨_⟩ (tagAtL-adequate (suc s) k zero (z ∷ γ)) t
      ∙ cong (pr (# k))
          (subst ⟨_⟩ (prAtL-adequate zero (suc a) (suc b) (z ∷ γ)) p) })

  bwd : ⟨ target ⟩ → ⟨ γ ⊨ tagPairAtL s k a b ⟩
  bwd q = ∣ zS
    , ( subst ⟨_⟩ (sym (prAtL-adequate zero (suc a) (suc b) (zS ∷ γ))) e
      , subst ⟨_⟩ (sym (tagAtL-adequate (suc s) k zero (zS ∷ γ)))
          (q ∙ cong (pr (# k)) (sym e)) ) ∣₁
    where
    zS : S
    zS = prʟ (lookup a γ) (lookup b γ)
    e : fst zS ≡ pr A B
    e = prʟ-fst (lookup a γ) (lookup b γ)
extAt : ∀ {n} → Fin n → Formula S (suc n) → Formula S n
extAt y φ = ∀̇ ((var zero ∈̇ var (suc y)) ⇒̇ φ)
         ∧̇ ∀̇ (φ ⇒̇ (var zero ∈̇ var (suc y)))

module _ {n : ℕ} (y : Fin n) (φ : Formula S (suc n)) (γ : S ^ n) where
  extAt-out : ⟨ γ ⊨ extAt y φ ⟩ → (z : S)
            → ⟨ fst z ∈ fst (lookup y γ) ⟩ → ⟨ (z ∷ γ) ⊨ φ ⟩
  extAt-out h = h .fst

  extAt-in : ⟨ γ ⊨ extAt y φ ⟩ → (z : S)
           → ⟨ (z ∷ γ) ⊨ φ ⟩ → ⟨ fst z ∈ fst (lookup y γ) ⟩
  extAt-in h = h .snd

  extAt-in-both : ((z : S) → ⟨ fst z ∈ fst (lookup y γ) ⟩ → ⟨ (z ∷ γ) ⊨ φ ⟩)
                → ((z : S) → ⟨ (z ∷ γ) ⊨ φ ⟩ → ⟨ fst z ∈ fst (lookup y γ) ⟩)
                → ⟨ γ ⊨ extAt y φ ⟩
  extAt-in-both f g = f , g

private
  memb : ∀ {n} → Fin n → Formula S (suc n)
  memb a = var zero ∈̇ var (suc a)

interAt : ∀ {n} → Fin n → Fin n → Fin n → Formula S n
interAt y a b = extAt y (memb a ∧̇ memb b)

unionAt : ∀ {n} → Fin n → Fin n → Fin n → Formula S n
unionAt y a b = extAt y (memb a ∨̇ memb b)

diffAt : ∀ {n} → Fin n → Fin n → Fin n → Formula S n
diffAt y a b = extAt y (memb a ∧̇ ¬̇ memb b)

sameAt : ∀ {n} → Fin n → Fin n → Formula S n
sameAt y a = extAt y (memb a)

emptyAt : ∀ {n} → Fin n → Formula S n
emptyAt y = extAt y ⊥̇

implAt : ∀ {n} → Fin n → Fin n → Fin n → Fin n → Formula S n
implAt y e a b = extAt y (memb e ∧̇ (memb a ⇒̇ memb b))
arityTagPairAtL : ∀ {n} → Fin n → Fin n → ℕ → Fin n → Fin n → Formula S n
arityTagPairAtL c ar k a b =
  ∃̇ (prAtL (suc c) (suc ar) zero ∧̇ tagPairAtL zero k (suc a) (suc b))

arityTagPairAtL-adequate : ∀ {n} (c ar : Fin n) (k : ℕ) (a b : Fin n) (γ : S ^ n)
  → (γ ⊨ arityTagPairAtL c ar k a b)
  ≡ PairIs (fst (lookup c γ))
      (pr (fst (lookup ar γ))
        (pr (# k) (pr (fst (lookup a γ)) (fst (lookup b γ)))))
arityTagPairAtL-adequate c ar k a b γ = ⇔toPath fwd bwd
  where
  N = fst (lookup ar γ)
  P = pr (fst (lookup a γ)) (fst (lookup b γ))
  target = PairIs (fst (lookup c γ)) (pr N (pr (# k) P))

  fwd : ⟨ γ ⊨ arityTagPairAtL c ar k a b ⟩ → ⟨ target ⟩
  fwd = PT.rec (snd target)
    (λ { (z , (p , t)) →
      subst ⟨_⟩ (prAtL-adequate (suc c) (suc ar) zero (z ∷ γ)) p
      ∙ cong (pr N) (subst ⟨_⟩ (tagPairAtL-adequate zero k (suc a) (suc b) (z ∷ γ)) t) })

  bwd : ⟨ target ⟩ → ⟨ γ ⊨ arityTagPairAtL c ar k a b ⟩
  bwd q = ∣ zS
    , ( subst ⟨_⟩ (sym (prAtL-adequate (suc c) (suc ar) zero (zS ∷ γ)))
          (q ∙ cong (pr N) (sym e))
      , subst ⟨_⟩ (sym (tagPairAtL-adequate zero k (suc a) (suc b) (zS ∷ γ))) e ) ∣₁
    where
    zS : S
    zS = prʟ (numeralL k) (prʟ (lookup a γ) (lookup b γ))
    e : fst zS ≡ pr (# k) P
    e = prʟ-fst (numeralL k) (prʟ (lookup a γ) (lookup b γ))
      ∙ cong₂ pr (numeralL-fst k) (prʟ-fst (lookup a γ) (lookup b γ))

arityTagAtL : ∀ {n} → Fin n → Fin n → ℕ → Fin n → Formula S n
arityTagAtL c ar k a =
  ∃̇ (prAtL (suc c) (suc ar) zero ∧̇ tagAtL zero k (suc a))

arityTagAtL-adequate : ∀ {n} (c ar : Fin n) (k : ℕ) (a : Fin n) (γ : S ^ n)
  → (γ ⊨ arityTagAtL c ar k a)
  ≡ PairIs (fst (lookup c γ))
      (pr (fst (lookup ar γ)) (pr (# k) (fst (lookup a γ))))
arityTagAtL-adequate c ar k a γ = ⇔toPath fwd bwd
  where
  N = fst (lookup ar γ)
  A = fst (lookup a γ)
  target = PairIs (fst (lookup c γ)) (pr N (pr (# k) A))

  fwd : ⟨ γ ⊨ arityTagAtL c ar k a ⟩ → ⟨ target ⟩
  fwd = PT.rec (snd target)
    (λ { (z , (p , t)) →
      subst ⟨_⟩ (prAtL-adequate (suc c) (suc ar) zero (z ∷ γ)) p
      ∙ cong (pr N) (subst ⟨_⟩ (tagAtL-adequate zero k (suc a) (z ∷ γ)) t) })

  bwd : ⟨ target ⟩ → ⟨ γ ⊨ arityTagAtL c ar k a ⟩
  bwd q = ∣ zS
    , ( subst ⟨_⟩ (sym (prAtL-adequate (suc c) (suc ar) zero (zS ∷ γ)))
          (q ∙ cong (pr N) (sym e))
      , subst ⟨_⟩ (sym (tagAtL-adequate zero k (suc a) (zS ∷ γ))) e ) ∣₁
    where
    zS : S
    zS = prʟ (numeralL k) (lookup a γ)
    e : fst zS ≡ pr (# k) A
    e = prʟ-fst (numeralL k) (lookup a γ) ∙ cong₂ pr (numeralL-fst k) refl
subValAt : ∀ {n} → Fin n → Fin n → Fin n → Fin n → Formula S n
subValAt T ar a y =
  ∃̇ (prAtL zero (suc ar) (suc a) ∧̇ appAt (suc T) zero (suc y))

subValAt-adequate : ∀ {n} (T ar a y : Fin n) (γ : S ^ n)
  → (γ ⊨ subValAt T ar a y)
  ≡ (pr (pr (fst (lookup ar γ)) (fst (lookup a γ))) (fst (lookup y γ))
      ∈ fst (lookup T γ))
subValAt-adequate T ar a y γ = ⇔toPath fwd bwd
  where
  K = pr (fst (lookup ar γ)) (fst (lookup a γ))
  target = pr K (fst (lookup y γ)) ∈ fst (lookup T γ)

  fwd : ⟨ γ ⊨ subValAt T ar a y ⟩ → ⟨ target ⟩
  fwd = PT.rec (snd target)
    (λ { (z , (p , q)) →
      subst (λ w → ⟨ pr w (fst (lookup y γ)) ∈ fst (lookup T γ) ⟩)
        (subst ⟨_⟩ (prAtL-adequate zero (suc ar) (suc a) (z ∷ γ)) p)
        (subst ⟨_⟩ (appAt-adequate (suc T) zero (suc y) (z ∷ γ)) q) })

  bwd : ⟨ target ⟩ → ⟨ γ ⊨ subValAt T ar a y ⟩
  bwd h = ∣ zS
    , ( subst ⟨_⟩ (sym (prAtL-adequate zero (suc ar) (suc a) (zS ∷ γ))) e
      , subst ⟨_⟩ (sym (appAt-adequate (suc T) zero (suc y) (zS ∷ γ)))
          (subst (λ w → ⟨ pr w (fst (lookup y γ)) ∈ fst (lookup T γ) ⟩) (sym e) h) ) ∣₁
    where
    zS : S
    zS = prʟ (lookup ar γ) (lookup a γ)
    e : fst zS ≡ K
    e = prʟ-fst (lookup ar γ) (lookup a γ)
module _ {n : ℕ} where
  private
    sh5 : Fin n → Fin (5 + n)
    sh5 i = suc (suc (suc (suc (suc i))))

    c5 n5 a5 b5 yc5 : Fin (5 + n)
    c5  = suc (suc (suc (suc zero)))
    n5  = suc (suc (suc zero))
    a5  = suc (suc zero)
    b5  = suc zero
    yc5 = zero

  binClauseAt : Fin n → Fin n → ℕ → Formula S (5 + n) → Formula S n
  binClauseAt C T k rel =
    ∀̇∈ (var C) (∀̇ (∀̇ (∀̇ (∀̇
      ( arityTagPairAtL c5 n5 k a5 b5
      ⇒̇ ( appAt (sh5 T) c5 yc5
      ⇒̇ rel ))))))

  binClause-out : (C T : Fin n) (k : ℕ) (rel : Formula S (5 + n)) (γ : S ^ n)
    → ⟨ γ ⊨ binClauseAt C T k rel ⟩
    → (c ar a b yc : S)
    → ⟨ fst c ∈ fst (lookup C γ) ⟩
    → fst c ≡ pr (fst ar) (pr (# k) (pr (fst a) (fst b)))
    → ⟨ pr (fst c) (fst yc) ∈ fst (lookup T γ) ⟩
    → ⟨ (yc ∷ b ∷ a ∷ ar ∷ c ∷ γ) ⊨ rel ⟩
  binClause-out C T k rel γ h c ar a b yc c∈ shape hc =
    h c c∈ ar a b yc
      (subst ⟨_⟩ (sym (arityTagPairAtL-adequate c5 n5 k a5 b5 δ)) shape)
      (subst ⟨_⟩ (sym (appAt-adequate (sh5 T) c5 yc5 δ)) hc)
    where
    δ : S ^ (5 + n)
    δ = yc ∷ b ∷ a ∷ ar ∷ c ∷ γ
  binClause-in : (C T : Fin n) (k : ℕ) (rel : Formula S (5 + n)) (γ : S ^ n)
    → ((c ar a b yc : S)
       → ⟨ fst c ∈ fst (lookup C γ) ⟩
       → fst c ≡ pr (fst ar) (pr (# k) (pr (fst a) (fst b)))
       → ⟨ pr (fst c) (fst yc) ∈ fst (lookup T γ) ⟩
       → ⟨ (yc ∷ b ∷ a ∷ ar ∷ c ∷ γ) ⊨ rel ⟩)
    → ⟨ γ ⊨ binClauseAt C T k rel ⟩
  binClause-in C T k rel γ g c c∈ ar a b yc sh hc =
    g c ar a b yc c∈
      (subst ⟨_⟩ (arityTagPairAtL-adequate c5 n5 k a5 b5 δ) sh)
      (subst ⟨_⟩ (appAt-adequate (sh5 T) c5 yc5 δ) hc)
    where
    δ : S ^ (5 + n)
    δ = yc ∷ b ∷ a ∷ ar ∷ c ∷ γ
  private
    sh4 : Fin n → Fin (4 + n)
    sh4 i = suc (suc (suc (suc i)))

    c4 n4 a4 yc4 : Fin (4 + n)
    c4  = suc (suc (suc zero))
    n4  = suc (suc zero)
    a4  = suc zero
    yc4 = zero

  unClauseAt : Fin n → Fin n → ℕ → Formula S (4 + n) → Formula S n
  unClauseAt C T k rel =
    ∀̇∈ (var C) (∀̇ (∀̇ (∀̇
      ( arityTagAtL c4 n4 k a4
      ⇒̇ ( appAt (sh4 T) c4 yc4
      ⇒̇ rel )))))

  unClause-out : (C T : Fin n) (k : ℕ) (rel : Formula S (4 + n)) (γ : S ^ n)
    → ⟨ γ ⊨ unClauseAt C T k rel ⟩
    → (c ar a yc : S)
    → ⟨ fst c ∈ fst (lookup C γ) ⟩
    → fst c ≡ pr (fst ar) (pr (# k) (fst a))
    → ⟨ pr (fst c) (fst yc) ∈ fst (lookup T γ) ⟩
    → ⟨ (yc ∷ a ∷ ar ∷ c ∷ γ) ⊨ rel ⟩
  unClause-out C T k rel γ h c ar a yc c∈ shape hc =
    h c c∈ ar a yc
      (subst ⟨_⟩ (sym (arityTagAtL-adequate c4 n4 k a4 δ)) shape)
      (subst ⟨_⟩ (sym (appAt-adequate (sh4 T) c4 yc4 δ)) hc)
    where
    δ : S ^ (4 + n)
    δ = yc ∷ a ∷ ar ∷ c ∷ γ
  unClause-in : (C T : Fin n) (k : ℕ) (rel : Formula S (4 + n)) (γ : S ^ n)
    → ((c ar a yc : S)
       → ⟨ fst c ∈ fst (lookup C γ) ⟩
       → fst c ≡ pr (fst ar) (pr (# k) (fst a))
       → ⟨ pr (fst c) (fst yc) ∈ fst (lookup T γ) ⟩
       → ⟨ (yc ∷ a ∷ ar ∷ c ∷ γ) ⊨ rel ⟩)
    → ⟨ γ ⊨ unClauseAt C T k rel ⟩
  unClause-in C T k rel γ g c c∈ ar a yc sh hc =
    g c ar a yc c∈
      (subst ⟨_⟩ (arityTagAtL-adequate c4 n4 k a4 δ) sh)
      (subst ⟨_⟩ (appAt-adequate (sh4 T) c4 yc4 δ) hc)
    where
    δ : S ^ (4 + n)
    δ = yc ∷ a ∷ ar ∷ c ∷ γ
module _ {n : ℕ} where
  private
    sh7 : Fin n → Fin (7 + n)
    sh7 i = suc (suc (suc (suc (suc (suc (suc i))))))

  c7 ar7 a7 b7 yc7 ya7 yb7 : Fin (7 + n)
  c7  = suc (suc (suc (suc (suc (suc zero)))))
  ar7 = suc (suc (suc (suc (suc zero))))
  a7  = suc (suc (suc (suc zero)))
  b7  = suc (suc (suc zero))
  yc7 = suc (suc zero)
  ya7 = suc zero
  yb7 = zero

  propRel : Fin n → Formula S (7 + n) → Formula S (5 + n)
  propRel T op =
    ∀̇ (∀̇ ( subValAt (sh7 T) ar7 a7 ya7
         ⇒̇ ( subValAt (sh7 T) ar7 b7 yb7
         ⇒̇ op )))

  propClauseAt : Fin n → Fin n → ℕ → Formula S (7 + n) → Formula S n
  propClauseAt C T k op = binClauseAt C T k (propRel T op)

  propClause-out : (C T : Fin n) (k : ℕ) (op : Formula S (7 + n)) (γ : S ^ n)
    → ⟨ γ ⊨ propClauseAt C T k op ⟩
    → (c ar a b yc ya yb : S)
    → ⟨ fst c ∈ fst (lookup C γ) ⟩
    → fst c ≡ pr (fst ar) (pr (# k) (pr (fst a) (fst b)))
    → ⟨ pr (fst c) (fst yc) ∈ fst (lookup T γ) ⟩
    → ⟨ pr (pr (fst ar) (fst a)) (fst ya) ∈ fst (lookup T γ) ⟩
    → ⟨ pr (pr (fst ar) (fst b)) (fst yb) ∈ fst (lookup T γ) ⟩
    → ⟨ (yb ∷ ya ∷ yc ∷ b ∷ a ∷ ar ∷ c ∷ γ) ⊨ op ⟩
  propClause-out C T k op γ h c ar a b yc ya yb c∈ shape hc ha hb =
    binClause-out C T k (propRel T op) γ h c ar a b yc c∈ shape hc ya yb
      (subst ⟨_⟩ (sym (subValAt-adequate (sh7 T) ar7 a7 ya7 δ)) ha)
      (subst ⟨_⟩ (sym (subValAt-adequate (sh7 T) ar7 b7 yb7 δ)) hb)
    where
    δ : S ^ (7 + n)
    δ = yb ∷ ya ∷ yc ∷ b ∷ a ∷ ar ∷ c ∷ γ

  propClause-in : (C T : Fin n) (k : ℕ) (op : Formula S (7 + n)) (γ : S ^ n)
    → ((c ar a b yc ya yb : S)
       → ⟨ fst c ∈ fst (lookup C γ) ⟩
       → fst c ≡ pr (fst ar) (pr (# k) (pr (fst a) (fst b)))
       → ⟨ pr (fst c) (fst yc) ∈ fst (lookup T γ) ⟩
       → ⟨ pr (pr (fst ar) (fst a)) (fst ya) ∈ fst (lookup T γ) ⟩
       → ⟨ pr (pr (fst ar) (fst b)) (fst yb) ∈ fst (lookup T γ) ⟩
       → ⟨ (yb ∷ ya ∷ yc ∷ b ∷ a ∷ ar ∷ c ∷ γ) ⊨ op ⟩)
    → ⟨ γ ⊨ propClauseAt C T k op ⟩
  propClause-in C T k op γ g =
    binClause-in C T k (propRel T op) γ
      (λ c ar a b yc c∈ sh hc ya yb ha hb →
        g c ar a b yc ya yb c∈ sh hc
          (subst ⟨_⟩
            (subValAt-adequate (sh7 T) ar7 a7 ya7 (yb ∷ ya ∷ yc ∷ b ∷ a ∷ ar ∷ c ∷ γ)) ha)
          (subst ⟨_⟩
            (subValAt-adequate (sh7 T) ar7 b7 yb7 (yb ∷ ya ∷ yc ∷ b ∷ a ∷ ar ∷ c ∷ γ)) hb))

  andClauseAt : Fin n → Fin n → Formula S n
  andClauseAt C T = propClauseAt C T 2 (interAt yc7 ya7 yb7)

  orClauseAt : Fin n → Fin n → Formula S n
  orClauseAt C T = propClauseAt C T 3 (unionAt yc7 ya7 yb7)
envSetAt : ∀ {n} → Fin n → Fin n → Fin n → Formula S n
envSetAt E ar B = extAt E (envOverAt zero (suc ar) (suc B))

module _ {n : ℕ} where
  private
    sh6 : Fin n → Fin (6 + n)
    sh6 i = suc (suc (suc (suc (suc (suc i)))))

    c6 ar6 a6 yc6 ya6 E6 : Fin (6 + n)
    c6  = suc (suc (suc (suc (suc zero))))
    ar6 = suc (suc (suc (suc zero)))
    a6  = suc (suc (suc zero))
    yc6 = suc (suc zero)
    ya6 = suc zero
    E6  = zero

    negRel : Fin n → Fin n → Formula S (4 + n)
    negRel T B =
      ∀̇ (∀̇ ( subValAt (sh6 T) ar6 a6 ya6
           ⇒̇ ( envSetAt E6 ar6 (sh6 B)
           ⇒̇ diffAt yc6 E6 ya6 )))

  negClauseAt : Fin n → Fin n → Fin n → Formula S n
  negClauseAt C T B = unClauseAt C T 5 (negRel T B)

  negClause-out : (C T B : Fin n) (γ : S ^ n)
    → ⟨ γ ⊨ negClauseAt C T B ⟩
    → (c ar a yc ya E : S)
    → ⟨ fst c ∈ fst (lookup C γ) ⟩
    → fst c ≡ pr (fst ar) (pr (# 5) (fst a))
    → ⟨ pr (fst c) (fst yc) ∈ fst (lookup T γ) ⟩
    → ⟨ pr (pr (fst ar) (fst a)) (fst ya) ∈ fst (lookup T γ) ⟩
    → ⟨ (E ∷ ya ∷ yc ∷ a ∷ ar ∷ c ∷ γ) ⊨ envSetAt E6 ar6 (sh6 B) ⟩
    → ⟨ (E ∷ ya ∷ yc ∷ a ∷ ar ∷ c ∷ γ) ⊨ diffAt yc6 E6 ya6 ⟩
  negClause-out C T B γ h c ar a yc ya E c∈ shape hc ha hE =
    unClause-out C T 5 (negRel T B) γ h c ar a yc c∈ shape hc ya E
      (subst ⟨_⟩ (sym (subValAt-adequate (sh6 T) ar6 a6 ya6 δ)) ha) hE
    where
    δ : S ^ (6 + n)
    δ = E ∷ ya ∷ yc ∷ a ∷ ar ∷ c ∷ γ
  negClause-in : (C T B : Fin n) (γ : S ^ n)
    → ((c ar a yc ya E : S)
       → ⟨ fst c ∈ fst (lookup C γ) ⟩
       → fst c ≡ pr (fst ar) (pr (# 5) (fst a))
       → ⟨ pr (fst c) (fst yc) ∈ fst (lookup T γ) ⟩
       → ⟨ pr (pr (fst ar) (fst a)) (fst ya) ∈ fst (lookup T γ) ⟩
       → ⟨ (E ∷ ya ∷ yc ∷ a ∷ ar ∷ c ∷ γ) ⊨ envSetAt E6 ar6 (sh6 B) ⟩
       → ⟨ (E ∷ ya ∷ yc ∷ a ∷ ar ∷ c ∷ γ) ⊨ diffAt yc6 E6 ya6 ⟩)
    → ⟨ γ ⊨ negClauseAt C T B ⟩
  negClause-in C T B γ g = unClause-in C T 5 (negRel T B) γ
    (λ c ar a yc c∈ sh hc ya E ha hE →
      g c ar a yc ya E c∈ sh hc
        (subst ⟨_⟩ (subValAt-adequate (sh6 T) ar6 a6 ya6
          (E ∷ ya ∷ yc ∷ a ∷ ar ∷ c ∷ γ)) ha) hE)
module _ {n : ℕ} where
  private
    sh8 : Fin n → Fin (8 + n)
    sh8 i = suc (suc (suc (suc (suc (suc (suc (suc i)))))))

    ar8 a8 b8 yc8 ya8 yb8 E8 : Fin (8 + n)
    ar8 = suc (suc (suc (suc (suc (suc zero)))))
    a8  = suc (suc (suc (suc (suc zero))))
    b8  = suc (suc (suc (suc zero)))
    yc8 = suc (suc (suc zero))
    ya8 = suc (suc zero)
    yb8 = suc zero
    E8  = zero

    impRel : Fin n → Fin n → Formula S (5 + n)
    impRel T B =
      ∀̇ (∀̇ (∀̇ ( subValAt (sh8 T) ar8 a8 ya8
              ⇒̇ ( subValAt (sh8 T) ar8 b8 yb8
              ⇒̇ ( envSetAt E8 ar8 (sh8 B)
              ⇒̇ implAt yc8 E8 ya8 yb8 )))))

    sh5 : Fin n → Fin (5 + n)
    sh5 i = suc (suc (suc (suc (suc i))))

    ar5 yc5 E5 : Fin (5 + n)
    ar5 = suc (suc (suc zero))
    yc5 = suc zero
    E5  = zero

    topRel : Fin n → Formula S (4 + n)
    topRel B = ∀̇ ( envSetAt E5 ar5 (sh5 B) ⇒̇ sameAt yc5 E5 )

  impClauseAt : Fin n → Fin n → Fin n → Formula S n
  impClauseAt C T B = binClauseAt C T 4 (impRel T B)

  topClauseAt : Fin n → Fin n → Fin n → Formula S n
  topClauseAt C T B = unClauseAt C T 6 (topRel B)

  botClauseAt : Fin n → Fin n → Formula S n
  botClauseAt C T = unClauseAt C T 7 (emptyAt zero)
  impClause-out : (C T B : Fin n) (γ : S ^ n)
    → ⟨ γ ⊨ impClauseAt C T B ⟩
    → (c ar a b yc ya yb E : S)
    → ⟨ fst c ∈ fst (lookup C γ) ⟩
    → fst c ≡ pr (fst ar) (pr (# 4) (pr (fst a) (fst b)))
    → ⟨ pr (fst c) (fst yc) ∈ fst (lookup T γ) ⟩
    → ⟨ pr (pr (fst ar) (fst a)) (fst ya) ∈ fst (lookup T γ) ⟩
    → ⟨ pr (pr (fst ar) (fst b)) (fst yb) ∈ fst (lookup T γ) ⟩
    → ⟨ (E ∷ yb ∷ ya ∷ yc ∷ b ∷ a ∷ ar ∷ c ∷ γ) ⊨ envSetAt E8 ar8 (sh8 B) ⟩
    → ⟨ (E ∷ yb ∷ ya ∷ yc ∷ b ∷ a ∷ ar ∷ c ∷ γ) ⊨ implAt yc8 E8 ya8 yb8 ⟩
  impClause-out C T B γ h c ar a b yc ya yb E c∈ shape hc ha hb hE =
    binClause-out C T 4 (impRel T B) γ h c ar a b yc c∈ shape hc ya yb E
      (subst ⟨_⟩ (sym (subValAt-adequate (sh8 T) ar8 a8 ya8 δ)) ha)
      (subst ⟨_⟩ (sym (subValAt-adequate (sh8 T) ar8 b8 yb8 δ)) hb) hE
    where
    δ : S ^ (8 + n)
    δ = E ∷ yb ∷ ya ∷ yc ∷ b ∷ a ∷ ar ∷ c ∷ γ

  impClause-in : (C T B : Fin n) (γ : S ^ n)
    → ((c ar a b yc ya yb E : S)
       → ⟨ fst c ∈ fst (lookup C γ) ⟩
       → fst c ≡ pr (fst ar) (pr (# 4) (pr (fst a) (fst b)))
       → ⟨ pr (fst c) (fst yc) ∈ fst (lookup T γ) ⟩
       → ⟨ pr (pr (fst ar) (fst a)) (fst ya) ∈ fst (lookup T γ) ⟩
       → ⟨ pr (pr (fst ar) (fst b)) (fst yb) ∈ fst (lookup T γ) ⟩
       → ⟨ (E ∷ yb ∷ ya ∷ yc ∷ b ∷ a ∷ ar ∷ c ∷ γ) ⊨ envSetAt E8 ar8 (sh8 B) ⟩
       → ⟨ (E ∷ yb ∷ ya ∷ yc ∷ b ∷ a ∷ ar ∷ c ∷ γ) ⊨ implAt yc8 E8 ya8 yb8 ⟩)
    → ⟨ γ ⊨ impClauseAt C T B ⟩
  impClause-in C T B γ g = binClause-in C T 4 (impRel T B) γ
    (λ c ar a b yc c∈ sh hc ya yb E ha hb hE →
      g c ar a b yc ya yb E c∈ sh hc
        (subst ⟨_⟩ (subValAt-adequate (sh8 T) ar8 a8 ya8
          (E ∷ yb ∷ ya ∷ yc ∷ b ∷ a ∷ ar ∷ c ∷ γ)) ha)
        (subst ⟨_⟩ (subValAt-adequate (sh8 T) ar8 b8 yb8
          (E ∷ yb ∷ ya ∷ yc ∷ b ∷ a ∷ ar ∷ c ∷ γ)) hb) hE)

  topClause-out : (C T B : Fin n) (γ : S ^ n)
    → ⟨ γ ⊨ topClauseAt C T B ⟩
    → (c ar a yc E : S)
    → ⟨ fst c ∈ fst (lookup C γ) ⟩
    → fst c ≡ pr (fst ar) (pr (# 6) (fst a))
    → ⟨ pr (fst c) (fst yc) ∈ fst (lookup T γ) ⟩
    → ⟨ (E ∷ yc ∷ a ∷ ar ∷ c ∷ γ) ⊨ envSetAt E5 ar5 (sh5 B) ⟩
    → ⟨ (E ∷ yc ∷ a ∷ ar ∷ c ∷ γ) ⊨ sameAt yc5 E5 ⟩
  topClause-out C T B γ h c ar a yc E c∈ shape hc hE =
    unClause-out C T 6 (topRel B) γ h c ar a yc c∈ shape hc E hE

  topClause-in : (C T B : Fin n) (γ : S ^ n)
    → ((c ar a yc E : S)
       → ⟨ fst c ∈ fst (lookup C γ) ⟩
       → fst c ≡ pr (fst ar) (pr (# 6) (fst a))
       → ⟨ pr (fst c) (fst yc) ∈ fst (lookup T γ) ⟩
       → ⟨ (E ∷ yc ∷ a ∷ ar ∷ c ∷ γ) ⊨ envSetAt E5 ar5 (sh5 B) ⟩
       → ⟨ (E ∷ yc ∷ a ∷ ar ∷ c ∷ γ) ⊨ sameAt yc5 E5 ⟩)
    → ⟨ γ ⊨ topClauseAt C T B ⟩
  topClause-in C T B γ g = unClause-in C T 6 (topRel B) γ
    (λ c ar a yc c∈ sh hc E hE → g c ar a yc E c∈ sh hc hE)

  botClause-out : (C T : Fin n) (γ : S ^ n)
    → ⟨ γ ⊨ botClauseAt C T ⟩
    → (c ar a yc : S)
    → ⟨ fst c ∈ fst (lookup C γ) ⟩
    → fst c ≡ pr (fst ar) (pr (# 7) (fst a))
    → ⟨ pr (fst c) (fst yc) ∈ fst (lookup T γ) ⟩
    → ⟨ (yc ∷ a ∷ ar ∷ c ∷ γ) ⊨ emptyAt zero ⟩
  botClause-out C T γ h = unClause-out C T 7 (emptyAt zero) γ h

  botClause-in : (C T : Fin n) (γ : S ^ n)
    → ((c ar a yc : S)
       → ⟨ fst c ∈ fst (lookup C γ) ⟩
       → fst c ≡ pr (fst ar) (pr (# 7) (fst a))
       → ⟨ pr (fst c) (fst yc) ∈ fst (lookup T γ) ⟩
       → ⟨ (yc ∷ a ∷ ar ∷ c ∷ γ) ⊨ emptyAt zero ⟩)
    → ⟨ γ ⊨ botClauseAt C T ⟩
  botClause-in C T γ = unClause-in C T 7 (emptyAt zero) γ
sucAtL : ∀ {n} → Fin n → Fin n → Formula S n
sucAtL i j = liftFo (sucAt i j) _

sucAtL-adequate : ∀ {n} (i j : Fin n) (γ : S ^ n)
  → (γ ⊨ sucAtL i j) ≡ PairIs (fst (lookup j γ)) (sucV (fst (lookup i γ)))
sucAtL-adequate i j γ =
    transferFo (sucAt i j) _ (Δ₀-sucAt i j) γ
  ∙ sucAt-adequate i j (map fst γ)
  ∙ cong₂ PairIs (lookup-fst j γ) (cong sucV (lookup-fst i γ))

subValSuccAt : ∀ {n} → Fin n → Fin n → Fin n → Fin n → Formula S n
subValSuccAt T ar a y =
  ∃̇ (sucAtL (suc ar) zero ∧̇ subValAt (suc T) zero (suc a) (suc y))

subValSuccAt-adequate : ∀ {n} (T ar a y : Fin n) (γ : S ^ n)
  → (γ ⊨ subValSuccAt T ar a y)
  ≡ (pr (pr (sucV (fst (lookup ar γ))) (fst (lookup a γ))) (fst (lookup y γ))
      ∈ fst (lookup T γ))
subValSuccAt-adequate T ar a y γ = ⇔toPath fwd bwd
  where
  key : V ℓ → V ℓ
  key w = pr (pr w (fst (lookup a γ))) (fst (lookup y γ))
  target = key (sucV (fst (lookup ar γ))) ∈ fst (lookup T γ)

  fwd : ⟨ γ ⊨ subValSuccAt T ar a y ⟩ → ⟨ target ⟩
  fwd = PT.rec (snd target)
    (λ { (z , (sz , v)) →
      subst (λ w → ⟨ key w ∈ fst (lookup T γ) ⟩)
        (subst ⟨_⟩ (sucAtL-adequate (suc ar) zero (z ∷ γ)) sz)
        (subst ⟨_⟩ (subValAt-adequate (suc T) zero (suc a) (suc y) (z ∷ γ)) v) })

  bwd : ⟨ target ⟩ → ⟨ γ ⊨ subValSuccAt T ar a y ⟩
  bwd h = ∣ zS
    , ( subst ⟨_⟩ (sym (sucAtL-adequate (suc ar) zero (zS ∷ γ))) e
      , subst ⟨_⟩ (sym (subValAt-adequate (suc T) zero (suc a) (suc y) (zS ∷ γ)))
          (subst (λ w → ⟨ key w ∈ fst (lookup T γ) ⟩) (sym e) h) ) ∣₁
    where
    zS : S
    zS = sucʟ (lookup ar γ)
    e : fst zS ≡ sucV (fst (lookup ar γ))
    e = sucʟ-fst (lookup ar γ)
numL : (k : ℕ) → InL (# k)
numL k = subst (λ w → ⟨ M w ⟩) (numeralL-fst k) (numeralL k .snd)

private
  bddSgl0 : ∀ {n} (k : Fin n) → BoundedFo InL (sgl0At k)
  bddSgl0 k = (_ , (_ , _)) , (_ , (_ , _))

  bddPair0 : ∀ {n} (k j : Fin n) → BoundedFo InL (pair0At k j)
  bddPair0 k j = (_ , (_ , _)) , ((_ , _) , (_ , ((_ , _) , (_ , _))))

  bddTag0 : ∀ {n} (s x : Fin n) → BoundedFo InL (tag0At s x)
  bddTag0 {n} s x =
      (_ , bddSgl0 {suc n} zero)
    , ( (_ , bddPair0 {suc n} zero (suc x))
      , (_ , (bddSgl0 {suc n} zero , bddPair0 {suc n} zero (suc x))) )

  bddShift : ∀ {n} (p' p : Fin n) → BoundedFo InL (shiftPairAt p' p)
  bddShift p' p = _

  bddCons : ∀ {n} (e' m e : Fin n) → BoundedFo InL (consAt e' m e)
  bddCons {n} e' m e =
      (_ , bddTag0 {suc n} zero (suc m))
    , ( (_ , (_ , bddShift {suc (suc n)} zero (suc zero)))
      , (_ , ( bddTag0 {suc n} zero (suc m)
             , (_ , bddShift {suc (suc n)} (suc zero) zero) )) )

consAtL : ∀ {n} → Fin n → Fin n → Fin n → Formula S n
consAtL e' m e = liftFo (consAt e' m e) (bddCons e' m e)

consAtL-adequate : ∀ {n} (e' m e : Fin n) (γ : S ^ n)
  {k : ℕ} (g : Fin k → V ℓ)
  → fst (lookup e γ) ≡ env g
  → (γ ⊨ consAtL e' m e)
  ≡ PairIs (fst (lookup e' γ)) (env (cons (fst (lookup m γ)) g))
consAtL-adequate e' m e γ g hE =
    transferFo (consAt e' m e) (bddCons e' m e) (Δ₀-consAt e' m e) γ
  ∙ consAt-adequate e' m e (map fst γ) g
      (lookup-fst e γ ∙ hE)
  ∙ cong₂ PairIs (lookup-fst e' γ)
      (cong (λ w → env (cons w g)) (lookup-fst m γ))

consAtL-transport : ∀ {n n'} (γ : S ^ n) (γ' : S ^ n')
                    (e₁ m₁ d₁ : Fin n) (e₂ m₂ d₂ : Fin n')
                    {k : ℕ} (g : Fin k → V ℓ)
                  → fst (lookup d₁ γ) ≡ env g
                  → fst (lookup e₁ γ) ≡ fst (lookup e₂ γ')
                  → fst (lookup m₁ γ) ≡ fst (lookup m₂ γ')
                  → fst (lookup d₁ γ) ≡ fst (lookup d₂ γ')
                  → ⟨ γ ⊨ consAtL e₁ m₁ d₁ ⟩ → ⟨ γ' ⊨ consAtL e₂ m₂ d₂ ⟩
consAtL-transport γ γ' e₁ m₁ d₁ e₂ m₂ d₂ g hE qe qm qd h =
  subst ⟨_⟩ (sym (consAtL-adequate e₂ m₂ d₂ γ' g (sym qd ∙ hE)))
    (subst2 (λ p q → ⟨ PairIs p (env (cons q g)) ⟩) qe qm
      (subst ⟨_⟩ (consAtL-adequate e₁ m₁ d₁ γ g hE) h))
module _ {n : ℕ} where
  private
    sh6' : Fin n → Fin (6 + n)
    sh6' i = suc (suc (suc (suc (suc (suc i)))))

    sh7' : Fin n → Fin (7 + n)
    sh7' i = suc (suc (suc (suc (suc (suc (suc i))))))

    ar6' a6' yc6' ya6' E6' : Fin (6 + n)
    ar6' = suc (suc (suc (suc zero)))
    a6'  = suc (suc (suc zero))
    yc6' = suc (suc zero)
    ya6' = suc zero
    E6'  = zero

    -- at the innermost point: e' = 0, m = 1, e = 2, E = 3, ya = 4
  body∃ body∀ : Fin n → Formula S (7 + n)
  body∃ B = (var zero ∈̇ var (suc zero))
            ∧̇ ∃̇∈ (var (sh7' B)) (∃̇
                ( consAtL zero (suc zero) (suc (suc zero))
                ∧̇ (var zero ∈̇ var (suc (suc (suc (suc zero))))) ))
  body∀ B = (var zero ∈̇ var (suc zero))
            ∧̇ ∀̇∈ (var (sh7' B)) (∀̇
                ( consAtL zero (suc zero) (suc (suc zero))
                ⇒̇ (var zero ∈̇ var (suc (suc (suc (suc zero))))) ))

  QuantWit : Fin n → S ^ (7 + n) → Type (ℓ-suc ℓ)
  QuantWit B γ = Σ[ x ∈ S ] (⟨ fst x ∈ fst (lookup (sh7' B) γ) ⟩
    × (Σ[ e' ∈ S ] (⟨ (e' ∷ x ∷ γ) ⊨ consAtL zero (suc zero) (suc (suc zero)) ⟩
                    × ⟨ fst e' ∈ fst (lookup (suc (suc zero)) γ) ⟩)))

  body∃-in : (B : Fin n) (γ : S ^ (7 + n))
           → ⟨ fst (lookup zero γ) ∈ fst (lookup (suc zero) γ) ⟩
           → ∥ QuantWit B γ ∥₁ → ⟨ γ ⊨ body∃ B ⟩
  body∃-in B γ h k =
    h , PT.map (λ { (x , (x∈ , (e' , r))) → x , (x∈ , ∣ e' , r ∣₁) }) k

  body∃-out : (B : Fin n) (γ : S ^ (7 + n)) → ⟨ γ ⊨ body∃ B ⟩
            → ⟨ fst (lookup zero γ) ∈ fst (lookup (suc zero) γ) ⟩
            × ∥ QuantWit B γ ∥₁
  body∃-out B γ h = h .fst , PT.rec squash₁
    (λ { (x , (x∈ , hv)) → PT.map (λ { (e' , r) → x , (x∈ , (e' , r)) }) hv })
    (h .snd)

  body∀-in : (B : Fin n) (γ : S ^ (7 + n))
           → ⟨ fst (lookup zero γ) ∈ fst (lookup (suc zero) γ) ⟩
           → ((x e' : S) → ⟨ fst x ∈ fst (lookup (sh7' B) γ) ⟩
              → ⟨ (e' ∷ x ∷ γ) ⊨ consAtL zero (suc zero) (suc (suc zero)) ⟩
              → ⟨ fst e' ∈ fst (lookup (suc (suc zero)) γ) ⟩)
           → ⟨ γ ⊨ body∀ B ⟩
  body∀-in B γ h k = h , (λ x x∈ e' hc → k x e' x∈ hc)

  body∀-out : (B : Fin n) (γ : S ^ (7 + n)) → ⟨ γ ⊨ body∀ B ⟩
            → ⟨ fst (lookup zero γ) ∈ fst (lookup (suc zero) γ) ⟩
            × ((x e' : S) → ⟨ fst x ∈ fst (lookup (sh7' B) γ) ⟩
               → ⟨ (e' ∷ x ∷ γ) ⊨ consAtL zero (suc zero) (suc (suc zero)) ⟩
               → ⟨ fst e' ∈ fst (lookup (suc (suc zero)) γ) ⟩)
  body∀-out B γ h = h .fst , (λ x e' x∈ hc → h .snd x x∈ e' hc)

  quantRel : Fin n → Fin n → Formula S (7 + n) → Formula S (4 + n)
  quantRel T B body =
      ∀̇ (∀̇ ( subValSuccAt (sh6' T) ar6' a6' ya6'
           ⇒̇ ( envSetAt E6' ar6' (sh6' B)
           ⇒̇ extAt yc6' body )))

  existClauseAt : Fin n → Fin n → Fin n → Formula S n
  existClauseAt C T B = unClauseAt C T 8 (quantRel T B (body∃ B))

  forallClauseAt : Fin n → Fin n → Fin n → Formula S n
  forallClauseAt C T B = unClauseAt C T 9 (quantRel T B (body∀ B))
  quantClause-out : (C T B : Fin n) (k : ℕ) (body : Formula S (7 + n)) (γ : S ^ n)
    → ⟨ γ ⊨ unClauseAt C T k (quantRel T B body) ⟩
    → (c ar a yc ya E : S)
    → ⟨ fst c ∈ fst (lookup C γ) ⟩
    → fst c ≡ pr (fst ar) (pr (# k) (fst a))
    → ⟨ pr (fst c) (fst yc) ∈ fst (lookup T γ) ⟩
    → ⟨ pr (pr (sucV (fst ar)) (fst a)) (fst ya) ∈ fst (lookup T γ) ⟩
    → ⟨ (E ∷ ya ∷ yc ∷ a ∷ ar ∷ c ∷ γ) ⊨ envSetAt E6' ar6' (sh6' B) ⟩
    → ⟨ (E ∷ ya ∷ yc ∷ a ∷ ar ∷ c ∷ γ) ⊨ extAt yc6' body ⟩
  quantClause-out C T B k body γ h c ar a yc ya E c∈ sh hc ha hE =
    unClause-out C T k (quantRel T B body) γ h c ar a yc c∈ sh hc ya E
      (subst ⟨_⟩ (sym (subValSuccAt-adequate (sh6' T) ar6' a6' ya6' δ)) ha) hE
    where
    δ : S ^ (6 + n)
    δ = E ∷ ya ∷ yc ∷ a ∷ ar ∷ c ∷ γ

  quantClause-in : (C T B : Fin n) (k : ℕ) (body : Formula S (7 + n)) (γ : S ^ n)
    → ((c ar a yc ya E : S)
       → ⟨ fst c ∈ fst (lookup C γ) ⟩
       → fst c ≡ pr (fst ar) (pr (# k) (fst a))
       → ⟨ pr (fst c) (fst yc) ∈ fst (lookup T γ) ⟩
       → ⟨ pr (pr (sucV (fst ar)) (fst a)) (fst ya) ∈ fst (lookup T γ) ⟩
       → ⟨ (E ∷ ya ∷ yc ∷ a ∷ ar ∷ c ∷ γ) ⊨ envSetAt E6' ar6' (sh6' B) ⟩
       → ⟨ (E ∷ ya ∷ yc ∷ a ∷ ar ∷ c ∷ γ) ⊨ extAt yc6' body ⟩)
    → ⟨ γ ⊨ unClauseAt C T k (quantRel T B body) ⟩
  quantClause-in C T B k body γ g = unClause-in C T k (quantRel T B body) γ
    (λ c ar a yc c∈ sh hc ya E ha hE →
      g c ar a yc ya E c∈ sh hc
        (subst ⟨_⟩ (subValSuccAt-adequate (sh6' T) ar6' a6' ya6'
          (E ∷ ya ∷ yc ∷ a ∷ ar ∷ c ∷ γ)) ha) hE)
tmValAt : ∀ {n} → Fin n → Fin n → Fin n → Formula S n
tmValAt t e v = ∃̇ (tagAtL (suc t) 1 zero ∧̇ appAt (suc e) zero (suc v))
              ∨̇ tagAtL t 0 v

module _ {n : ℕ} (t e v : Fin n) (γ : S ^ n) where
  private
    T = fst (lookup t γ)
    Val = fst (lookup v γ)
    Env = fst (lookup e γ)

    Var : Type (ℓ-suc ℓ)
    Var = Σ[ k ∈ S ] ((T ≡ pr (# 1) (fst k)) × ⟨ pr (fst k) Val ∈ Env ⟩)

    Con : Type (ℓ-suc ℓ)
    Con = T ≡ pr (# 0) Val

  tmValAt-var : (k : S) → T ≡ pr (# 1) (fst k) → ⟨ pr (fst k) Val ∈ Env ⟩
              → ⟨ γ ⊨ tmValAt t e v ⟩
  tmValAt-var k q m = ∣ inl ∣ k
    , ( subst ⟨_⟩ (sym (tagAtL-adequate (suc t) 1 zero (k ∷ γ))) q
      , subst ⟨_⟩ (sym (appAt-adequate (suc e) zero (suc v) (k ∷ γ))) m ) ∣₁ ∣₁

  tmValAt-con : T ≡ pr (# 0) Val → ⟨ γ ⊨ tmValAt t e v ⟩
  tmValAt-con q = ∣ inr (subst ⟨_⟩ (sym (tagAtL-adequate t 0 v γ)) q) ∣₁

  tmValAt-out : ⟨ γ ⊨ tmValAt t e v ⟩ → ∥ (Var ⊎ Con) ∥₁
  tmValAt-out = PT.rec squash₁
    (λ { (inl h) → PT.map
           (λ { (k , (ht , hm)) → inl (k
             , ( subst ⟨_⟩ (tagAtL-adequate (suc t) 1 zero (k ∷ γ)) ht
               , subst ⟨_⟩ (appAt-adequate (suc e) zero (suc v) (k ∷ γ)) hm )) })
           h
       ; (inr h) → ∣ inr (subst ⟨_⟩ (tagAtL-adequate t 0 v γ) h) ∣₁ })

module _ {n : ℕ} where
  private
    sh6″ : Fin n → Fin (6 + n)
    sh6″ i = suc (suc (suc (suc (suc (suc i)))))

    ar6″ yc6″ E6″ : Fin (6 + n)
    ar6″ = suc (suc (suc (suc zero)))
    yc6″ = suc zero
    E6″  = zero

    -- at the innermost point: w = 0, v = 1, e = 2, E = 3, yc = 4, b = 5, a = 6
    a9″ b9″ e9″ v9″ w9″ : Fin (9 + n)
    a9″ = suc (suc (suc (suc (suc (suc zero)))))
    b9″ = suc (suc (suc (suc (suc zero))))
    e9″ = suc (suc zero)
    v9″ = suc zero
    w9″ = zero

  atomBody : Formula S (9 + n) → Formula S (7 + n)
  atomBody cmp =
      (var zero ∈̇ var (suc zero))
      ∧̇ ∃̇ (∃̇ ( tmValAt a9″ e9″ v9″
             ∧̇ ( tmValAt b9″ e9″ w9″
             ∧̇ cmp )))

  atomRel : Fin n → Formula S (9 + n) → Formula S (5 + n)
  atomRel B cmp =
      ∀̇ ( envSetAt E6″ ar6″ (sh6″ B) ⇒̇ extAt yc6″ (atomBody cmp) )

  AtomWit : Formula S (9 + n) → S ^ (7 + n) → Type (ℓ-suc ℓ)
  AtomWit cmp γ = Σ[ v ∈ S ] (Σ[ w ∈ S ]
    (⟨ (w ∷ v ∷ γ) ⊨ tmValAt a9″ e9″ v9″ ⟩
     × (⟨ (w ∷ v ∷ γ) ⊨ tmValAt b9″ e9″ w9″ ⟩ × ⟨ (w ∷ v ∷ γ) ⊨ cmp ⟩)))

  atomBody-in : (cmp : Formula S (9 + n)) (γ : S ^ (7 + n))
              → ⟨ fst (lookup zero γ) ∈ fst (lookup (suc zero) γ) ⟩
              → ∥ AtomWit cmp γ ∥₁ → ⟨ γ ⊨ atomBody cmp ⟩
  atomBody-in cmp γ h k =
    h , PT.map (λ { (v , (w , r)) → v , ∣ w , r ∣₁ }) k

  atomBody-out : (cmp : Formula S (9 + n)) (γ : S ^ (7 + n))
               → ⟨ γ ⊨ atomBody cmp ⟩
               → ⟨ fst (lookup zero γ) ∈ fst (lookup (suc zero) γ) ⟩
               × ∥ AtomWit cmp γ ∥₁
  atomBody-out cmp γ h =
    h .fst , PT.rec squash₁ (λ { (v , hv) →
      PT.map (λ { (w , r) → v , (w , r) }) hv }) (h .snd)

  memRel eqRel : Formula S (9 + n)
  memRel = var v9″ ∈̇ var w9″
  eqRel  = var v9″ ≐ var w9″

  memClauseAt : Fin n → Fin n → Fin n → Formula S n
  memClauseAt C T B = binClauseAt C T 0 (atomRel B memRel)

  eqClauseAt : Fin n → Fin n → Fin n → Formula S n
  eqClauseAt C T B = binClauseAt C T 1 (atomRel B eqRel)
  atomClause-out : (C T B : Fin n) (k : ℕ) (cmp : Formula S (9 + n)) (γ : S ^ n)
    → ⟨ γ ⊨ binClauseAt C T k (atomRel B cmp) ⟩
    → (c ar a b yc E : S)
    → ⟨ fst c ∈ fst (lookup C γ) ⟩
    → fst c ≡ pr (fst ar) (pr (# k) (pr (fst a) (fst b)))
    → ⟨ pr (fst c) (fst yc) ∈ fst (lookup T γ) ⟩
    → ⟨ (E ∷ yc ∷ b ∷ a ∷ ar ∷ c ∷ γ) ⊨ envSetAt E6″ ar6″ (sh6″ B) ⟩
    → ⟨ (E ∷ yc ∷ b ∷ a ∷ ar ∷ c ∷ γ) ⊨ extAt yc6″ (atomBody cmp) ⟩
  atomClause-out C T B k cmp γ h c ar a b yc E c∈ sh hc hE =
    binClause-out C T k (atomRel B cmp) γ h c ar a b yc c∈ sh hc E hE

  atomClause-in : (C T B : Fin n) (k : ℕ) (cmp : Formula S (9 + n)) (γ : S ^ n)
    → ((c ar a b yc E : S)
       → ⟨ fst c ∈ fst (lookup C γ) ⟩
       → fst c ≡ pr (fst ar) (pr (# k) (pr (fst a) (fst b)))
       → ⟨ pr (fst c) (fst yc) ∈ fst (lookup T γ) ⟩
       → ⟨ (E ∷ yc ∷ b ∷ a ∷ ar ∷ c ∷ γ) ⊨ envSetAt E6″ ar6″ (sh6″ B) ⟩
       → ⟨ (E ∷ yc ∷ b ∷ a ∷ ar ∷ c ∷ γ) ⊨ extAt yc6″ (atomBody cmp) ⟩)
    → ⟨ γ ⊨ binClauseAt C T k (atomRel B cmp) ⟩
  atomClause-in C T B k cmp γ g = binClause-in C T k (atomRel B cmp) γ
    (λ c ar a b yc c∈ sh hc E hE → g c ar a b yc E c∈ sh hc hE)
module _ {n : ℕ} where
  private
    sh7B : Fin n → Fin (7 + n)
    sh7B i = suc (suc (suc (suc (suc (suc (suc i))))))

    -- at depth 7: E = 0, yb = 1, yc = 2, b = 3, a = 4, ar = 5, c = 6
    ar7B b7B yc7B yb7B E7B : Fin (7 + n)
    ar7B = suc (suc (suc (suc (suc zero))))
    b7B  = suc (suc (suc zero))
    yc7B = suc (suc zero)
    yb7B = suc zero
    E7B  = zero

    -- at depth 9: w = 0, e = 1, a = 6
    a9B e9B w9B : Fin (9 + n)
    a9B = suc (suc (suc (suc (suc (suc zero)))))
    e9B = suc zero
    w9B = zero

    -- at depth 11: e' = 0, m = 1, e = 3, yb = 5
    e'11 m11 e11 yb11 : Fin (11 + n)
    e'11 = zero
    m11  = suc zero
    e11  = suc (suc (suc zero))
    yb11 = suc (suc (suc (suc (suc zero))))

    sh9B : Fin n → Fin (9 + n)
    sh9B i = suc (suc (suc (suc (suc (suc (suc (suc (suc i))))))))

    -- inside the bound's quantifier, at depth 10: m = 0, w = 1
  bodyAll bodyEx : Fin n → Formula S (8 + n)
  bodyAll B = (var zero ∈̇ var (suc zero))
              ∧̇ ∀̇ ( tmValAt a9B e9B w9B
                  ⇒̇ ∀̇∈ (var (sh9B B))
                      ( (var zero ∈̇ var (suc zero))
                      ⇒̇ ∀̇ ( consAtL e'11 m11 e11
                          ⇒̇ (var e'11 ∈̇ var yb11) )))
  bodyEx  B = (var zero ∈̇ var (suc zero))
              ∧̇ ∃̇ ( tmValAt a9B e9B w9B
                  ∧̇ ∃̇∈ (var (sh9B B))
                      ( (var zero ∈̇ var (suc zero))
                      ∧̇ ∃̇ ( consAtL e'11 m11 e11
                          ∧̇ (var e'11 ∈̇ var yb11) )))

  BndWit : Fin n → S ^ (8 + n) → S → Type (ℓ-suc ℓ)
  BndWit B γ w = Σ[ x ∈ S ] ((⟨ fst x ∈ fst (lookup (sh9B B) (w ∷ γ)) ⟩
    × ⟨ fst x ∈ fst w ⟩)
    × (Σ[ e' ∈ S ] (⟨ (e' ∷ x ∷ w ∷ γ) ⊨ consAtL e'11 m11 e11 ⟩
                    × ⟨ fst e' ∈ fst (lookup (suc (suc zero)) γ) ⟩)))

  bodyEx-in : (B : Fin n) (γ : S ^ (8 + n))
            → ⟨ fst (lookup zero γ) ∈ fst (lookup (suc zero) γ) ⟩
            → ∥ (Σ[ w ∈ S ] (⟨ (w ∷ γ) ⊨ tmValAt a9B e9B w9B ⟩
                             × ∥ BndWit B γ w ∥₁)) ∥₁
            → ⟨ γ ⊨ bodyEx B ⟩
  bodyEx-in B γ h k = h , PT.map
    (λ { (w , (hw , hx)) → w , (hw , PT.map
      (λ { (x , ((x∈B , x∈w) , (e' , r))) → x , (x∈B , (x∈w , ∣ e' , r ∣₁)) })
      hx) }) k

  bodyEx-out : (B : Fin n) (γ : S ^ (8 + n)) → ⟨ γ ⊨ bodyEx B ⟩
             → ⟨ fst (lookup zero γ) ∈ fst (lookup (suc zero) γ) ⟩
             × ∥ (Σ[ w ∈ S ] (⟨ (w ∷ γ) ⊨ tmValAt a9B e9B w9B ⟩
                              × ∥ BndWit B γ w ∥₁)) ∥₁
  bodyEx-out B γ h = h .fst , PT.map
    (λ { (w , (hw , hx)) → w , (hw , PT.rec squash₁
      (λ { (x , (x∈B , (x∈w , hv))) → PT.map
        (λ { (e' , r) → x , ((x∈B , x∈w) , (e' , r)) }) hv })
      hx) }) (h .snd)

  bodyAll-in : (B : Fin n) (γ : S ^ (8 + n))
             → ⟨ fst (lookup zero γ) ∈ fst (lookup (suc zero) γ) ⟩
             → ((w : S) → ⟨ (w ∷ γ) ⊨ tmValAt a9B e9B w9B ⟩
                → (x e' : S) → ⟨ fst x ∈ fst (lookup (sh9B B) (w ∷ γ)) ⟩
                → ⟨ fst x ∈ fst w ⟩
                → ⟨ (e' ∷ x ∷ w ∷ γ) ⊨ consAtL e'11 m11 e11 ⟩
                → ⟨ fst e' ∈ fst (lookup (suc (suc zero)) γ) ⟩)
             → ⟨ γ ⊨ bodyAll B ⟩
  bodyAll-in B γ h k =
    h , (λ w hw x x∈B x∈w e' hc → k w hw x e' x∈B x∈w hc)

  bodyAll-out : (B : Fin n) (γ : S ^ (8 + n)) → ⟨ γ ⊨ bodyAll B ⟩
              → ⟨ fst (lookup zero γ) ∈ fst (lookup (suc zero) γ) ⟩
              × ((w : S) → ⟨ (w ∷ γ) ⊨ tmValAt a9B e9B w9B ⟩
                 → (x e' : S) → ⟨ fst x ∈ fst (lookup (sh9B B) (w ∷ γ)) ⟩
                 → ⟨ fst x ∈ fst w ⟩
                 → ⟨ (e' ∷ x ∷ w ∷ γ) ⊨ consAtL e'11 m11 e11 ⟩
                 → ⟨ fst e' ∈ fst (lookup (suc (suc zero)) γ) ⟩)
  bodyAll-out B γ h =
    h .fst , (λ w hw x e' x∈B x∈w hc → h .snd w hw x x∈B x∈w e' hc)

  bndRel : Fin n → Fin n → Formula S (8 + n) → Formula S (5 + n)
  bndRel T B body =
      ∀̇ (∀̇ ( subValSuccAt (sh7B T) ar7B b7B yb7B
           ⇒̇ ( envSetAt E7B ar7B (sh7B B)
           ⇒̇ extAt yc7B body )))

  allInClauseAt : Fin n → Fin n → Fin n → Formula S n
  allInClauseAt C T B = binClauseAt C T 10 (bndRel T B (bodyAll B))

  exInClauseAt : Fin n → Fin n → Fin n → Formula S n
  exInClauseAt C T B = binClauseAt C T 11 (bndRel T B (bodyEx B))
  bndClause-out : (C T B : Fin n) (k : ℕ) (body : Formula S (8 + n)) (γ : S ^ n)
    → ⟨ γ ⊨ binClauseAt C T k (bndRel T B body) ⟩
    → (c ar a b yc yb E : S)
    → ⟨ fst c ∈ fst (lookup C γ) ⟩
    → fst c ≡ pr (fst ar) (pr (# k) (pr (fst a) (fst b)))
    → ⟨ pr (fst c) (fst yc) ∈ fst (lookup T γ) ⟩
    → ⟨ pr (pr (sucV (fst ar)) (fst b)) (fst yb) ∈ fst (lookup T γ) ⟩
    → ⟨ (E ∷ yb ∷ yc ∷ b ∷ a ∷ ar ∷ c ∷ γ) ⊨ envSetAt E7B ar7B (sh7B B) ⟩
    → ⟨ (E ∷ yb ∷ yc ∷ b ∷ a ∷ ar ∷ c ∷ γ) ⊨ extAt yc7B body ⟩
  bndClause-out C T B k body γ h c ar a b yc yb E c∈ sh hc hb hE =
    binClause-out C T k (bndRel T B body) γ h c ar a b yc c∈ sh hc yb E
      (subst ⟨_⟩ (sym (subValSuccAt-adequate (sh7B T) ar7B b7B yb7B δ)) hb) hE
    where
    δ : S ^ (7 + n)
    δ = E ∷ yb ∷ yc ∷ b ∷ a ∷ ar ∷ c ∷ γ

  bndClause-in : (C T B : Fin n) (k : ℕ) (body : Formula S (8 + n)) (γ : S ^ n)
    → ((c ar a b yc yb E : S)
       → ⟨ fst c ∈ fst (lookup C γ) ⟩
       → fst c ≡ pr (fst ar) (pr (# k) (pr (fst a) (fst b)))
       → ⟨ pr (fst c) (fst yc) ∈ fst (lookup T γ) ⟩
       → ⟨ pr (pr (sucV (fst ar)) (fst b)) (fst yb) ∈ fst (lookup T γ) ⟩
       → ⟨ (E ∷ yb ∷ yc ∷ b ∷ a ∷ ar ∷ c ∷ γ) ⊨ envSetAt E7B ar7B (sh7B B) ⟩
       → ⟨ (E ∷ yb ∷ yc ∷ b ∷ a ∷ ar ∷ c ∷ γ) ⊨ extAt yc7B body ⟩)
    → ⟨ γ ⊨ binClauseAt C T k (bndRel T B body) ⟩
  bndClause-in C T B k body γ g = binClause-in C T k (bndRel T B body) γ
    (λ c ar a b yc c∈ sh hc yb E hb hE →
      g c ar a b yc yb E c∈ sh hc
        (subst ⟨_⟩ (subValSuccAt-adequate (sh7B T) ar7B b7B yb7B
          (E ∷ yb ∷ yc ∷ b ∷ a ∷ ar ∷ c ∷ γ)) hb) hE)
module _ {n : ℕ} where
  private
    sh4 : Fin n → Fin (4 + n)
    sh4 i = suc (suc (suc (suc i)))

    c4 n4 a4 b4 : Fin (4 + n)
    c4 = suc (suc (suc zero))
    n4 = suc (suc zero)
    a4 = suc zero
    b4 = zero

    sh3 : Fin n → Fin (3 + n)
    sh3 i = suc (suc (suc i))

    c3 n3 a3 : Fin (3 + n)
    c3 = suc (suc zero)
    n3 = suc zero
    a3 = zero

  binShapeAt : Fin n → ℕ → Formula S (4 + n) → Formula S n
  binShapeAt C k rel =
    ∀̇∈ (var C) (∀̇ (∀̇ (∀̇ ( arityTagPairAtL c4 n4 k a4 b4 ⇒̇ rel))))

  unShapeAt : Fin n → ℕ → Formula S (3 + n) → Formula S n
  unShapeAt C k rel =
    ∀̇∈ (var C) (∀̇ (∀̇ ( arityTagAtL c3 n3 k a3 ⇒̇ rel)))

  binShape-out : (C : Fin n) (k : ℕ) (rel : Formula S (4 + n)) (γ : S ^ n)
    → ⟨ γ ⊨ binShapeAt C k rel ⟩
    → (c ar a b : S)
    → ⟨ fst c ∈ fst (lookup C γ) ⟩
    → fst c ≡ pr (fst ar) (pr (# k) (pr (fst a) (fst b)))
    → ⟨ (b ∷ a ∷ ar ∷ c ∷ γ) ⊨ rel ⟩
  binShape-out C k rel γ h c ar a b c∈ shape =
    h c c∈ ar a b
      (subst ⟨_⟩ (sym (arityTagPairAtL-adequate c4 n4 k a4 b4 (b ∷ a ∷ ar ∷ c ∷ γ)))
        shape)

  unShape-out : (C : Fin n) (k : ℕ) (rel : Formula S (3 + n)) (γ : S ^ n)
    → ⟨ γ ⊨ unShapeAt C k rel ⟩
    → (c ar a : S)
    → ⟨ fst c ∈ fst (lookup C γ) ⟩
    → fst c ≡ pr (fst ar) (pr (# k) (fst a))
    → ⟨ (a ∷ ar ∷ c ∷ γ) ⊨ rel ⟩
  unShape-out C k rel γ h c ar a c∈ shape =
    h c c∈ ar a
      (subst ⟨_⟩ (sym (arityTagAtL-adequate c3 n3 k a3 (a ∷ ar ∷ c ∷ γ))) shape)
  bothSameAt : Fin n → Formula S (4 + n)
  bothSameAt C = appAt (sh4 C) n4 a4 ∧̇ appAt (sh4 C) n4 b4

  oneSameAt : Fin n → Formula S (3 + n)
  oneSameAt C = appAt (sh3 C) n3 a3

  oneSuccAt : Fin n → Formula S (3 + n)
  oneSuccAt C = ∃̇ (sucAtL (suc n3) zero ∧̇ appAt (suc (sh3 C)) zero (suc a3))

  succSndAt : Fin n → Formula S (4 + n)
  succSndAt C = ∃̇ (sucAtL (suc n4) zero ∧̇ appAt (suc (sh4 C)) zero (suc b4))
  binSameClosed-out : (C : Fin n) (k : ℕ) (γ : S ^ n)
    → ⟨ γ ⊨ binShapeAt C k (bothSameAt C) ⟩
    → (c ar a b : S)
    → ⟨ fst c ∈ fst (lookup C γ) ⟩
    → fst c ≡ pr (fst ar) (pr (# k) (pr (fst a) (fst b)))
    → ⟨ pr (fst ar) (fst a) ∈ fst (lookup C γ) ⟩
    × ⟨ pr (fst ar) (fst b) ∈ fst (lookup C γ) ⟩
  binSameClosed-out C k γ h c ar a b c∈ shape =
      subst ⟨_⟩ (appAt-adequate (sh4 C) n4 a4 δ) (r .fst)
    , subst ⟨_⟩ (appAt-adequate (sh4 C) n4 b4 δ) (r .snd)
    where
    δ : S ^ (4 + n)
    δ = b ∷ a ∷ ar ∷ c ∷ γ
    r = binShape-out C k (bothSameAt C) γ h c ar a b c∈ shape

  unSameClosed-out : (C : Fin n) (k : ℕ) (γ : S ^ n)
    → ⟨ γ ⊨ unShapeAt C k (oneSameAt C) ⟩
    → (c ar a : S)
    → ⟨ fst c ∈ fst (lookup C γ) ⟩
    → fst c ≡ pr (fst ar) (pr (# k) (fst a))
    → ⟨ pr (fst ar) (fst a) ∈ fst (lookup C γ) ⟩
  unSameClosed-out C k γ h c ar a c∈ shape =
    subst ⟨_⟩ (appAt-adequate (sh3 C) n3 a3 (a ∷ ar ∷ c ∷ γ))
      (unShape-out C k (oneSameAt C) γ h c ar a c∈ shape)

  unSuccClosed-out : (C : Fin n) (k : ℕ) (γ : S ^ n)
    → ⟨ γ ⊨ unShapeAt C k (oneSuccAt C) ⟩
    → (c ar a : S)
    → ⟨ fst c ∈ fst (lookup C γ) ⟩
    → fst c ≡ pr (fst ar) (pr (# k) (fst a))
    → ⟨ pr (sucV (fst ar)) (fst a) ∈ fst (lookup C γ) ⟩
  unSuccClosed-out C k γ h c ar a c∈ shape =
    PT.rec (snd target)
      (λ { (z , (sz , ap)) →
        subst (λ w → ⟨ pr w (fst a) ∈ fst (lookup C γ) ⟩)
          (subst ⟨_⟩ (sucAtL-adequate (suc n3) zero (z ∷ δ)) sz)
          (subst ⟨_⟩ (appAt-adequate (suc (sh3 C)) zero (suc a3) (z ∷ δ)) ap) })
      (unShape-out C k (oneSuccAt C) γ h c ar a c∈ shape)
    where
    δ : S ^ (3 + n)
    δ = a ∷ ar ∷ c ∷ γ
    target = pr (sucV (fst ar)) (fst a) ∈ fst (lookup C γ)

  binSuccClosed-out : (C : Fin n) (k : ℕ) (γ : S ^ n)
    → ⟨ γ ⊨ binShapeAt C k (succSndAt C) ⟩
    → (c ar a b : S)
    → ⟨ fst c ∈ fst (lookup C γ) ⟩
    → fst c ≡ pr (fst ar) (pr (# k) (pr (fst a) (fst b)))
    → ⟨ pr (sucV (fst ar)) (fst b) ∈ fst (lookup C γ) ⟩
  binSuccClosed-out C k γ h c ar a b c∈ shape =
    PT.rec (snd target)
      (λ { (z , (sz , ap)) →
        subst (λ w → ⟨ pr w (fst b) ∈ fst (lookup C γ) ⟩)
          (subst ⟨_⟩ (sucAtL-adequate (suc n4) zero (z ∷ δ)) sz)
          (subst ⟨_⟩ (appAt-adequate (suc (sh4 C)) zero (suc b4) (z ∷ δ)) ap) })
      (binShape-out C k (succSndAt C) γ h c ar a b c∈ shape)
    where
    δ : S ^ (4 + n)
    δ = b ∷ a ∷ ar ∷ c ∷ γ
    target = pr (sucV (fst ar)) (fst b) ∈ fst (lookup C γ)
  andClosedAt orClosedAt impClosedAt negClosedAt : Fin n → Formula S n
  existClosedAt forallClosedAt allInClosedAt exInClosedAt : Fin n → Formula S n

  andClosedAt    C = binShapeAt C 2 (bothSameAt C)
  orClosedAt     C = binShapeAt C 3 (bothSameAt C)
  impClosedAt    C = binShapeAt C 4 (bothSameAt C)
  negClosedAt    C = unShapeAt  C 5 (oneSameAt C)
  existClosedAt  C = unShapeAt  C 8 (oneSuccAt C)
  forallClosedAt C = unShapeAt  C 9 (oneSuccAt C)
  allInClosedAt  C = binShapeAt C 10 (succSndAt C)
  exInClosedAt   C = binShapeAt C 11 (succSndAt C)

  closedAt : Fin n → Formula S n
  closedAt C =
    andClosedAt C ∧̇ (orClosedAt C ∧̇ (impClosedAt C ∧̇ (negClosedAt C
      ∧̇ (existClosedAt C ∧̇ (forallClosedAt C
      ∧̇ (allInClosedAt C ∧̇ exInClosedAt C))))))
  binShape-in : (C : Fin n) (k : ℕ) (rel : Formula S (4 + n)) (γ : S ^ n)
    → ((c ar a b : S)
       → ⟨ fst c ∈ fst (lookup C γ) ⟩
       → fst c ≡ pr (fst ar) (pr (# k) (pr (fst a) (fst b)))
       → ⟨ (b ∷ a ∷ ar ∷ c ∷ γ) ⊨ rel ⟩)
    → ⟨ γ ⊨ binShapeAt C k rel ⟩
  binShape-in C k rel γ g c c∈ ar a b sh =
    g c ar a b c∈
      (subst ⟨_⟩ (arityTagPairAtL-adequate c4 n4 k a4 b4 (b ∷ a ∷ ar ∷ c ∷ γ)) sh)

  unShape-in : (C : Fin n) (k : ℕ) (rel : Formula S (3 + n)) (γ : S ^ n)
    → ((c ar a : S)
       → ⟨ fst c ∈ fst (lookup C γ) ⟩
       → fst c ≡ pr (fst ar) (pr (# k) (fst a))
       → ⟨ (a ∷ ar ∷ c ∷ γ) ⊨ rel ⟩)
    → ⟨ γ ⊨ unShapeAt C k rel ⟩
  unShape-in C k rel γ g c c∈ ar a sh =
    g c ar a c∈
      (subst ⟨_⟩ (arityTagAtL-adequate c3 n3 k a3 (a ∷ ar ∷ c ∷ γ)) sh)

  binSameClosed-in : (C : Fin n) (k : ℕ) (γ : S ^ n)
    → ((c ar a b : S)
       → ⟨ fst c ∈ fst (lookup C γ) ⟩
       → fst c ≡ pr (fst ar) (pr (# k) (pr (fst a) (fst b)))
       → ⟨ pr (fst ar) (fst a) ∈ fst (lookup C γ) ⟩
       × ⟨ pr (fst ar) (fst b) ∈ fst (lookup C γ) ⟩)
    → ⟨ γ ⊨ binShapeAt C k (bothSameAt C) ⟩
  binSameClosed-in C k γ g = binShape-in C k (bothSameAt C) γ
    (λ c ar a b c∈ sh →
        subst ⟨_⟩ (sym (appAt-adequate (sh4 C) n4 a4 (b ∷ a ∷ ar ∷ c ∷ γ)))
          (g c ar a b c∈ sh .fst)
      , subst ⟨_⟩ (sym (appAt-adequate (sh4 C) n4 b4 (b ∷ a ∷ ar ∷ c ∷ γ)))
          (g c ar a b c∈ sh .snd))

  unSameClosed-in : (C : Fin n) (k : ℕ) (γ : S ^ n)
    → ((c ar a : S)
       → ⟨ fst c ∈ fst (lookup C γ) ⟩
       → fst c ≡ pr (fst ar) (pr (# k) (fst a))
       → ⟨ pr (fst ar) (fst a) ∈ fst (lookup C γ) ⟩)
    → ⟨ γ ⊨ unShapeAt C k (oneSameAt C) ⟩
  unSameClosed-in C k γ g = unShape-in C k (oneSameAt C) γ
    (λ c ar a c∈ sh →
      subst ⟨_⟩ (sym (appAt-adequate (sh3 C) n3 a3 (a ∷ ar ∷ c ∷ γ)))
        (g c ar a c∈ sh))

  unSuccClosed-in : (C : Fin n) (k : ℕ) (γ : S ^ n)
    → ((c ar a : S)
       → ⟨ fst c ∈ fst (lookup C γ) ⟩
       → fst c ≡ pr (fst ar) (pr (# k) (fst a))
       → ⟨ pr (sucV (fst ar)) (fst a) ∈ fst (lookup C γ) ⟩)
    → ⟨ γ ⊨ unShapeAt C k (oneSuccAt C) ⟩
  unSuccClosed-in C k γ g = unShape-in C k (oneSuccAt C) γ
    (λ c ar a c∈ sh → ∣ sucʟ ar
      , ( subst ⟨_⟩ (sym (sucAtL-adequate (suc n3) zero
            (sucʟ ar ∷ a ∷ ar ∷ c ∷ γ))) (sucʟ-fst ar)
        , subst ⟨_⟩ (sym (appAt-adequate (suc (sh3 C)) zero (suc a3)
            (sucʟ ar ∷ a ∷ ar ∷ c ∷ γ)))
            (subst (λ w → ⟨ pr w (fst a) ∈ fst (lookup C γ) ⟩)
              (sym (sucʟ-fst ar)) (g c ar a c∈ sh)) ) ∣₁)

  binSuccClosed-in : (C : Fin n) (k : ℕ) (γ : S ^ n)
    → ((c ar a b : S)
       → ⟨ fst c ∈ fst (lookup C γ) ⟩
       → fst c ≡ pr (fst ar) (pr (# k) (pr (fst a) (fst b)))
       → ⟨ pr (sucV (fst ar)) (fst b) ∈ fst (lookup C γ) ⟩)
    → ⟨ γ ⊨ binShapeAt C k (succSndAt C) ⟩
  binSuccClosed-in C k γ g = binShape-in C k (succSndAt C) γ
    (λ c ar a b c∈ sh → ∣ sucʟ ar
      , ( subst ⟨_⟩ (sym (sucAtL-adequate (suc n4) zero
            (sucʟ ar ∷ b ∷ a ∷ ar ∷ c ∷ γ))) (sucʟ-fst ar)
        , subst ⟨_⟩ (sym (appAt-adequate (suc (sh4 C)) zero (suc b4)
            (sucʟ ar ∷ b ∷ a ∷ ar ∷ c ∷ γ)))
            (subst (λ w → ⟨ pr w (fst b) ∈ fst (lookup C γ) ⟩)
              (sym (sucʟ-fst ar)) (g c ar a b c∈ sh)) ) ∣₁)
