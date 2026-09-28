{-# OPTIONS --cubical --safe --guardedness #-}
module RelationalLargeFunctions where

open import Cubical.Foundations.Prelude
open import Cubical.Foundations.HLevels
open import Cubical.Data.Sigma using (_×_)
open import ModalTrees using (NN; unitNN; mapNN; bindNN; propNN; stableNN)
open import StableRelations

open Object
open Map

product : ∀ {a e b d} → Object a e → Object b d
  → Object (ℓ-max a b) (ℓ-max e d)
Carrier (product A B) = Carrier A × Carrier B
Equal (product A B) x y = Equal A (x .fst) (y .fst) × Equal B (x .snd) (y .snd)
equal-prop (product A B) x y = isProp× (equal-prop A _ _) (equal-prop B _ _)
equal-stable (product A B) x y n =
  equal-stable A _ _ (mapNN fst n) , equal-stable B _ _ (mapNN snd n)
equal-refl (product A B) x = equal-refl A _ , equal-refl B _
equal-sym (product A B) x y e = equal-sym A _ _ (e .fst) , equal-sym B _ _ (e .snd)
equal-trans (product A B) x y z e f =
  equal-trans A _ _ _ (e .fst) (f .fst) , equal-trans B _ _ _ (e .snd) (f .snd)

module _ {ℓ : Level} (A B : Object ℓ ℓ) where
  Functions : Object (ℓ-suc ℓ) ℓ
  Carrier Functions = Map A B ℓ
  Equal Functions = MapEq
  equal-prop Functions F G = isPropΠ2 λ x y → isProp×
    (isPropΠ λ _ → graph-prop G x y) (isPropΠ λ _ → graph-prop F x y)
  equal-stable Functions F G n x y =
    (λ p → graph-stable G x y (mapNN (λ e → e x y .fst p) n)) ,
    (λ p → graph-stable F x y (mapNN (λ e → e x y .snd p) n))
  equal-refl Functions = map-eq-refl
  equal-sym Functions F G e x y = e x y .snd , e x y .fst
  equal-trans Functions F G H e f x y =
    (λ p → f x y .fst (e x y .fst p)) , (λ p → e x y .snd (f x y .snd p))

  evaluate : Map (product Functions A) B ℓ
  graph evaluate (F , x) y = graph F x y
  graph-prop evaluate (F , x) y = graph-prop F x y
  graph-stable evaluate (F , x) y = graph-stable F x y
  respect evaluate (F , x) (G , x') y y' (fg , xx') yy' p =
    respect G x x' y y' xx' yy' (fg x y .fst p)
  total evaluate (F , x) = total F x
  unique evaluate (F , x) = unique F x

  module _ {Γ : Object ℓ ℓ} where
    row : Map (product Γ A) B ℓ → Carrier Γ → Map A B ℓ
    graph (row F γ) x y = graph F (γ , x) y
    graph-prop (row F γ) x y = graph-prop F (γ , x) y
    graph-stable (row F γ) x y = graph-stable F (γ , x) y
    respect (row F γ) x x' y y' xx' yy' =
      respect F (γ , x) (γ , x') y y' (equal-refl Γ γ , xx') yy'
    total (row F γ) x = total F (γ , x)
    unique (row F γ) x = unique F (γ , x)

    row-respect : (F : Map (product Γ A) B ℓ) (γ δ : Carrier Γ)
      → Equal Γ γ δ → MapEq (row F γ) (row F δ)
    row-respect F γ δ e x y =
      respect F (γ , x) (δ , x) y y (e , equal-refl A x) (equal-refl B y) ,
      respect F (δ , x) (γ , x) y y
        (equal-sym Γ γ δ e , equal-refl A x) (equal-refl B y)

    curry : Map (product Γ A) B ℓ → Map Γ Functions ℓ
    graph (curry F) γ R = MapEq (row F γ) R
    graph-prop (curry F) γ R = equal-prop Functions (row F γ) R
    graph-stable (curry F) γ R = equal-stable Functions (row F γ) R
    respect (curry F) γ δ R S e rs fr x y =
      (λ p → rs x y .fst (fr x y .fst (row-respect F γ δ e x y .snd p))) ,
      (λ p → row-respect F γ δ e x y .fst (fr x y .snd (rs x y .snd p)))
    total (curry F) γ = unitNN (row F γ , map-eq-refl (row F γ))
    unique (curry F) γ R S fr fs x y =
      (λ p → fs x y .fst (fr x y .snd p)) ,
      (λ p → fr x y .fst (fs x y .snd p))

    uncurry : ∀ {s} → Map Γ Functions s
      → Map (product Γ A) B (ℓ-max (ℓ-suc ℓ) s)
    graph (uncurry K) (γ , x) y =
      NN (Σ[ R ∈ Map A B ℓ ] (graph K γ R × graph R x y))
    graph-prop (uncurry K) z y = propNN
    graph-stable (uncurry K) z y = stableNN
    respect (uncurry K) (γ , x) (δ , x') y y' (e , xx') yy' = mapNN
      λ { (R , kr , rxy) → R ,
        respect K γ δ R R e (map-eq-refl R) kr ,
        respect R x x' y y' xx' yy' rxy }
    total (uncurry K) (γ , x) = bindNN (total K γ) λ { (R , kr) →
      mapNN (λ { (y , rxy) → y , unitNN (R , kr , rxy) }) (total R x) }
    unique (uncurry K) (γ , x) y y' n m = equal-stable B y y'
      (bindNN n λ { (R , kr , rxy) → mapNN
        (λ { (S , ks , sxy') → unique S x y y'
          (unique K γ R S kr ks x y .fst rxy) sxy' }) m })

    beta : (F : Map (product Γ A) B ℓ) → MapEq (uncurry (curry F)) F
    beta F (γ , x) y =
      (λ n → graph-stable F (γ , x) y
        (mapNN (λ { (R , fr , rxy) → fr x y .snd rxy }) n)) ,
      (λ fxy → unitNN (row F γ , map-eq-refl (row F γ) , fxy))

    realizes-to-curry : ∀ {s} (K : Map Γ Functions s)
      (F : Map (product Γ A) B ℓ) → MapEq (uncurry K) F
      → (γ : Carrier Γ) (R : Map A B ℓ) → graph K γ R → graph (curry F) γ R
    realizes-to-curry K F realizes γ R kr x y =
      (λ fxy → graph-stable R x y (mapNN
        (λ { (S , ks , sxy) → unique K γ S R ks kr x y .fst sxy })
        (realizes (γ , x) y .snd fxy))) ,
      (λ rxy → realizes (γ , x) y .fst (unitNN (R , kr , rxy)))

    eta : ∀ {s} (K : Map Γ Functions s) (F : Map (product Γ A) B ℓ)
      → MapEq (uncurry K) F → MapEq K (curry F)
    eta K F realizes γ R = realizes-to-curry K F realizes γ R ,
      (λ fr → graph-stable K γ R (mapNN
        (λ { (S , ks) → respect K γ γ S R (equal-refl Γ γ)
          (λ x y →
            (λ sxy → fr x y .fst (realizes-to-curry K F realizes γ S ks x y .snd sxy)) ,
            (λ rxy → realizes-to-curry K F realizes γ S ks x y .fst (fr x y .snd rxy))) ks })
        (total K γ)))

module _ {ℓ : Level} (A B : Object ℓ ℓ) {Γ Δ : Object ℓ ℓ}
  (σ : Map Δ Γ ℓ) where
  extend-context : Map (product Δ A) (product Γ A) ℓ
  graph extend-context (δ , x) (γ , x') = graph σ δ γ × Equal A x x'
  graph-prop extend-context (δ , x) (γ , x') =
    isProp× (graph-prop σ δ γ) (equal-prop A x x')
  graph-stable extend-context (δ , x) (γ , x') n =
    graph-stable σ δ γ (mapNN fst n) , equal-stable A x x' (mapNN snd n)
  respect extend-context (δ , x) (δ' , z) (γ , x') (γ' , z') (dd , xz) (gg , x'z') (sg , xx') =
    respect σ δ δ' γ γ' dd gg sg ,
    equal-trans A z x z' (equal-sym A x z xz) (equal-trans A x x' z' xx' x'z')
  total extend-context (δ , x) = mapNN
    (λ { (γ , sg) → (γ , x) , sg , equal-refl A x }) (total σ δ)
  unique extend-context (δ , x) (γ , y) (γ' , y') (sg , xy) (sg' , xy') =
    unique σ δ γ γ' sg sg' , equal-trans A y x y' (equal-sym A x y xy) xy'

  substitution-realizes : (F : Map (product Γ A) B ℓ)
    → MapEq (uncurry A B (compose (curry A B F) σ)) (compose F extend-context)
  substitution-realizes F (δ , x) y =
    (λ n → bindNN n λ { (R , kr , rxy) → mapNN
      (λ { (γ , sg , fr) → (γ , x) , (sg , equal-refl A x) , fr x y .snd rxy }) kr }) ,
    (λ n → mapNN (λ { ((γ , x') , (sg , xx') , fxy) →
      row A B {Γ = Γ} F γ , unitNN (γ , sg , map-eq-refl (row A B {Γ = Γ} F γ)) ,
      respect F (γ , x') (γ , x) y y
        (equal-refl Γ γ , equal-sym A x x' xx') (equal-refl B y) fxy }) n)

  curry-substitution : (F : Map (product Γ A) B ℓ)
    → MapEq (compose (curry A B F) σ) (curry A B (compose F extend-context))
  curry-substitution F = eta A B (compose (curry A B F) σ) (compose F extend-context)
    (substitution-realizes F)
