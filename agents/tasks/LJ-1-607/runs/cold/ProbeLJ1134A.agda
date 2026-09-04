{-# OPTIONS --cubical --safe --guardedness #-}

-- [LJ-1.134] probe A: the section 4 probe of agents/reports/lj-1.131-report.md.
--
-- Block A2 of Route A' turns an L-element graph into an honest Agda
-- function.  Every part is delivered; nobody ran the assembly.  This
-- probe runs it.
--
--   Part A. From (svAt f) and (domAt f d), extract the value through
--           the fibre and get toFun with toFun-inj.
--   Part B. Compose with leastOf (orderAt beta) at a bound stage.
--   Part C. One concrete non-degenerate graph, so Part A is not vacuous.
--
-- Untracked probe; ONE agda process under GHCRTS="-A64m -I0 -M8g";
-- never committed.

open import Base.Prelude
open import Base.Truth
open import Base.Classical using ( LEM )

module ProbeLJ1134A {ℓ : Level} (lem : LEM (ℓ-suc ℓ)) where

open import FOL.ZFStructure using ( module hPropStructure )
open import FOL.Syntax using ( Formula; var; _≐_; _⇒̇_; ∀̇_ )
import FOL.Absoluteness
open import V.Hierarchy {ℓ} using ( 𝒮ᵥ )
open import V.Coding {ℓ} using ( pr; pr-inj )
open import L.Constructible {ℓ}
  using ( 𝒮ʟ; isL; isL-trans; Lset; Lset→isL; IsOrd; isPropIsOrd )
open import L.Choice.Step {ℓ} lem using ( Mem; orderAt )
open import L.WellOrder.Base {ℓ-suc ℓ} using ( SWO; IsLeast; leastOf )
open import L.Coding.Model {ℓ}
  using ( appAt; appAt-adequate; svAt; svAt-out; svAt-in
        ; domAt; domAt-in; domAt-out; domAt-intro
        ; prʟ; prʟ-fst )

open import L.Axioms.Numerals {ℓ} using ( pairʟ; pairʟ-fst; numeralL )
open import V.Model {ℓ} using ( pair-spec )
open import V.Presentation {ℓ} using ( member; fiber; ↪-inj )
open import Cubical.HITs.CumulativeHierarchy.Properties using ( ⟪_⟫; ⟪_⟫↪ )

open import Cubical.Data.Sigma using ( Σ≡Prop )
open import Cubical.Data.Sum using ( inl; inr )
open import Cubical.Functions.Logic using ( ∃[∶]-syntax )
open import Cubical.HITs.CumulativeHierarchy.Base using ( V; _∈_; setIsSet )
open import Cubical.HITs.CumulativeHierarchy.Constructions using ( ⁅_,_⁆ )
import Cubical.HITs.PropositionalTruncation as PT
open PT using ( ∣_∣₁; ∥_∥₁ )

open TruthAlgebra (hPropAlgebra (ℓ-suc ℓ))
open hPropStructure 𝒮ʟ using ( S )

module AbsL = FOL.Absoluteness.Single 𝒮ᵥ isL isL-trans
open AbsL using ( _^_ ) renaming ( _⊨ᵐ_ to _⊨_ )

-- ---------------------------------------------------------------------
-- Injectivity of a graph, in the object language.
-- The mirror of svAt: the second component determines the first.
-- ---------------------------------------------------------------------

injAt : ∀ {n} → Fin n → Formula S n
injAt f = ∀̇ (∀̇ (∀̇ (
      appAt (suc (suc (suc f))) (suc zero) (suc (suc zero))
  ⇒̇ (appAt (suc (suc (suc f))) zero (suc (suc zero))
  ⇒̇ (var (suc zero) ≐ var zero)))))

-- The two directions, in the shape L.Coding.Model gives svAt.
module _ {n : ℕ} (f : Fin n) (γ : S ^ n) where
  private
    Holds₀ : S → S → Type (ℓ-suc ℓ)
    Holds₀ x y = ⟨ pr (fst x) (fst y) ∈ fst (lookup f γ) ⟩

    at₁ : (y x x' : S)
        → ((x' ∷ x ∷ y ∷ γ) ⊨ appAt (suc (suc (suc f))) (suc zero) (suc (suc zero)))
        ≡ (pr (fst x) (fst y) ∈ fst (lookup f γ))
    at₁ y x x' = appAt-adequate (suc (suc (suc f))) (suc zero) (suc (suc zero))
                   (x' ∷ x ∷ y ∷ γ)

    at₂ : (y x x' : S)
        → ((x' ∷ x ∷ y ∷ γ) ⊨ appAt (suc (suc (suc f))) zero (suc (suc zero)))
        ≡ (pr (fst x') (fst y) ∈ fst (lookup f γ))
    at₂ y x x' = appAt-adequate (suc (suc (suc f))) zero (suc (suc zero))
                   (x' ∷ x ∷ y ∷ γ)

  injAt-out : ⟨ γ ⊨ injAt f ⟩
            → (y x x' : S) → Holds₀ x y → Holds₀ x' y → fst x ≡ fst x'
  injAt-out h y x x' p q = h y x x'
    (subst ⟨_⟩ (sym (at₁ y x x')) p) (subst ⟨_⟩ (sym (at₂ y x x')) q)

  injAt-in : ((y x x' : S) → Holds₀ x y → Holds₀ x' y → fst x ≡ fst x')
           → ⟨ γ ⊨ injAt f ⟩
  injAt-in h y x x' p q = h y x x'
    (subst ⟨_⟩ (at₁ y x x') p) (subst ⟨_⟩ (at₂ y x x') q)

-- ---------------------------------------------------------------------
-- Part A. The fibre extraction.
-- ---------------------------------------------------------------------

module Extract (F D : S)
               (sv : ⟨ (F ∷ D ∷ []) ⊨ svAt zero ⟩)
               (dm : ⟨ (F ∷ D ∷ []) ⊨ domAt zero (suc zero) ⟩) where

  γ : S ^ 2
  γ = F ∷ D ∷ []

  Holds : S → S → Type (ℓ-suc ℓ)
  Holds x y = ⟨ pr (fst x) (fst y) ∈ fst F ⟩

  Fib : S → Type (ℓ-suc ℓ)
  Fib x = Σ[ y ∈ S ] Holds x y

  -- Single-valuedness makes the fibre a proposition.
  isPropFib : (x : S) → isProp (Fib x)
  isPropFib x (y , p) (y' , q) =
    Σ≡Prop (λ w → snd (pr (fst x) (fst w) ∈ fst F))
      (Σ≡Prop (λ z → snd (isL z)) (svAt-out zero γ sv x y y' p q))

  -- The extraction itself: a proposition plus an inhabitant.
  toVal : (x : S) → ∥ Fib x ∥₁ → Fib x
  toVal x = PT.rec (isPropFib x) (λ z → z)

  Dom : Type (ℓ-suc ℓ)
  Dom = Σ[ x ∈ S ] ⟨ fst x ∈ fst D ⟩

  fib : (u : Dom) → Fib (fst u)
  fib (x , m) = toVal x (domAt-in zero (suc zero) γ dm x m)

  toFun : Dom → S
  toFun u = fst (fib u)

  toFun-graph : (u : Dom) → Holds (fst u) (toFun u)
  toFun-graph u = snd (fib u)

  module _ (ij : ⟨ γ ⊨ injAt zero ⟩) where

    toFun-inj : (u v : Dom) → fst (toFun u) ≡ fst (toFun v)
              → fst (fst u) ≡ fst (fst v)
    toFun-inj u v e = injAt-out zero γ ij (toFun v) (fst u) (fst v)
      (subst (λ w → ⟨ pr (fst (fst u)) w ∈ fst F ⟩) e (toFun-graph u))
      (toFun-graph v)

-- ---------------------------------------------------------------------
-- Part B. The composite: pick the <_L-least graph at a bound stage,
-- then run Part A on it.
-- ---------------------------------------------------------------------

module Least (β : V ℓ) (oβ : IsOrd β) (D : S) where

  -- The crossing.  L.Choice.Step works over the AMBIENT carrier, so a
  -- member of a stage is not yet an element of the model.
  up : Mem (Lset β) → S
  up (x , m) = x , Lset→isL β oβ x m

  Good : Mem (Lset β) → Ω
  Good A = ((up A ∷ D ∷ []) ⊨ svAt zero)
         ⊓ (((up A ∷ D ∷ []) ⊨ domAt zero (suc zero))
         ⊓  ((up A ∷ D ∷ []) ⊨ injAt zero))

  module _ (h : ∥ Σ[ A ∈ Mem (Lset β) ] ⟨ Good A ⟩ ∥₁) where

    chosen : Σ[ A ∈ Mem (Lset β) ] IsLeast (orderAt β oβ) Good A
    chosen = leastOf (orderAt β oβ) lem Good h

    F₀ : S
    F₀ = up (fst chosen)

    good : ⟨ Good (fst chosen) ⟩
    good = fst (snd chosen)

    module E = Extract F₀ D (fst good) (fst (snd good))

    DomOf : Type (ℓ-suc ℓ)
    DomOf = E.Dom

    -- The deliverable: an honest function out of the domain, and it is
    -- injective, built from the <_L-least graph.
    leastFun : DomOf → S
    leastFun = E.toFun

    leastFun-inj : (u v : DomOf) → fst (leastFun u) ≡ fst (leastFun v)
                 → fst (fst u) ≡ fst (fst v)
    leastFun-inj = E.toFun-inj (snd (snd good))

-- ---------------------------------------------------------------------
-- Part C. One concrete graph, so Part A and Part B are not vacuous.
-- The graph is the singleton {<a,a>} and the domain is {a}; both are
-- elements of L by construction, through pairʟ.
-- ---------------------------------------------------------------------

module Concrete (a : S) where

  G : S
  G = pairʟ (prʟ a a) (prʟ a a)

  Dm : S
  Dm = pairʟ a a

  p₀ : V ℓ
  p₀ = pr (fst a) (fst a)

  G-fst : fst G ≡ ⁅ p₀ , p₀ ⁆
  G-fst = pairʟ-fst (prʟ a a) (prʟ a a)
        ∙ cong₂ ⁅_,_⁆ (prʟ-fst a a) (prʟ-fst a a)

  D-fst : fst Dm ≡ ⁅ fst a , fst a ⁆
  D-fst = pairʟ-fst a a

  memG : (z : V ℓ) → ⟨ z ∈ fst G ⟩ → z ≡ p₀
  memG z h = PT.rec (setIsSet z p₀) (λ { (inl e) → e ; (inr e) → e })
    (subst ⟨_⟩ (pair-spec p₀ p₀ z) (subst (λ w → ⟨ z ∈ w ⟩) G-fst h))

  inG : ⟨ p₀ ∈ fst G ⟩
  inG = subst (λ w → ⟨ p₀ ∈ w ⟩) (sym G-fst)
          (subst ⟨_⟩ (sym (pair-spec p₀ p₀ p₀)) ∣ inl refl ∣₁)

  memD : (z : V ℓ) → ⟨ z ∈ fst Dm ⟩ → z ≡ fst a
  memD z h = PT.rec (setIsSet z (fst a)) (λ { (inl e) → e ; (inr e) → e })
    (subst ⟨_⟩ (pair-spec (fst a) (fst a) z) (subst (λ w → ⟨ z ∈ w ⟩) D-fst h))

  inD : ⟨ fst a ∈ fst Dm ⟩
  inD = subst (λ w → ⟨ fst a ∈ w ⟩) (sym D-fst)
          (subst ⟨_⟩ (sym (pair-spec (fst a) (fst a) (fst a))) ∣ inl refl ∣₁)

  γ : S ^ 2
  γ = G ∷ Dm ∷ []

  split : (x y : S) → ⟨ pr (fst x) (fst y) ∈ fst G ⟩
        → (fst x ≡ fst a) × (fst y ≡ fst a)
  split x y h = pr-inj (memG (pr (fst x) (fst y)) h)

  sv : ⟨ γ ⊨ svAt zero ⟩
  sv = svAt-in zero γ
    (λ x y y' p q → snd (split x y p) ∙ sym (snd (split x y' q)))

  ij : ⟨ γ ⊨ injAt zero ⟩
  ij = injAt-in zero γ
    (λ y x x' p q → fst (split x y p) ∙ sym (fst (split x' y q)))

  dm : ⟨ γ ⊨ domAt zero (suc zero) ⟩
  dm = domAt-intro zero (suc zero) γ (λ x → fwd x , bwd x)
    where
    fwd : (x : S) → ⟨ ∃[ y ∶ S ] (pr (fst x) (fst y) ∈ fst G) ⟩
        → ⟨ fst x ∈ fst Dm ⟩
    fwd x = PT.rec (snd (fst x ∈ fst Dm))
      (λ { (y , p) →
        subst (λ w → ⟨ w ∈ fst Dm ⟩) (sym (fst (split x y p))) inD })

    bwd : (x : S) → ⟨ fst x ∈ fst Dm ⟩
        → ⟨ ∃[ y ∶ S ] (pr (fst x) (fst y) ∈ fst G) ⟩
    bwd x m = ∣ a , subst (λ w → ⟨ pr w (fst a) ∈ fst G ⟩)
                     (sym (memD (fst x) m)) inG ∣₁

  module C = Extract G Dm sv dm

  concreteFun : C.Dom → S
  concreteFun = C.toFun

  concreteFun-inj : (u v : C.Dom) → fst (concreteFun u) ≡ fst (concreteFun v)
                  → fst (fst u) ≡ fst (fst v)
  concreteFun-inj = C.toFun-inj ij

  -- The function is not a placeholder: it returns a at a.
  concreteFun-value : (m : ⟨ fst a ∈ fst Dm ⟩)
                    → fst (concreteFun (a , m)) ≡ fst a
  concreteFun-value m =
    snd (split a (concreteFun (a , m)) (C.toFun-graph (a , m)))

  -- Part C feeds Part B: at any stage that holds the graph, the
  -- selection predicate is satisfied, so leastOf has an input.
  goodAt : (β : V ℓ) (oβ : IsOrd β) (m : ⟨ fst G ∈ Lset β ⟩)
         → ⟨ Least.Good β oβ Dm (fst G , m) ⟩
  goodAt β oβ m =
    subst (λ w → ⟨ ((w ∷ Dm ∷ []) ⊨ svAt zero)
                ⊓ (((w ∷ Dm ∷ []) ⊨ domAt zero (suc zero))
                ⊓  ((w ∷ Dm ∷ []) ⊨ injAt zero)) ⟩)
          (sym eq) (sv , (dm , ij))
    where
    eq : Least.up β oβ Dm (fst G , m) ≡ G
    eq = Σ≡Prop (λ z → snd (isL z)) refl

  hGood : (β : V ℓ) (oβ : IsOrd β) (m : ⟨ fst G ∈ Lset β ⟩)
        → ∥ Σ[ A ∈ Mem (Lset β) ] ⟨ Least.Good β oβ Dm A ⟩ ∥₁
  hGood β oβ m = ∣ (fst G , m) , goodAt β oβ m ∣₁

  -- The whole composite, forced to elaborate.
  composite : (β : V ℓ) (oβ : IsOrd β) (m : ⟨ fst G ∈ Lset β ⟩)
            → Least.DomOf β oβ Dm (hGood β oβ m) → S
  composite β oβ m = Least.leastFun β oβ Dm (hGood β oβ m)

-- A fully concrete instance: the graph {<0,0>} over the empty set.
module Zero = Concrete (numeralL 0)

-- ---------------------------------------------------------------------
-- Part D. The shape the square-law chain consumes.  [LJ-1.107] and
-- [LJ-1.114] state their injections between the SMALL index types,
-- not between Dom and S.  This part converts.
-- ---------------------------------------------------------------------

module Small (F D C : S)
             (sv : ⟨ (F ∷ D ∷ []) ⊨ svAt zero ⟩)
             (dm : ⟨ (F ∷ D ∷ []) ⊨ domAt zero (suc zero) ⟩)
             (ij : ⟨ (F ∷ D ∷ []) ⊨ injAt zero ⟩)
             (ran : (x y : S) → ⟨ pr (fst x) (fst y) ∈ fst F ⟩
                  → ⟨ fst y ∈ fst C ⟩) where

  module E = Extract F D sv dm

  toS : ⟪ fst D ⟫ → S
  toS m = ⟪ fst D ⟫↪ m
        , isL-trans {x = fst D} {y = ⟪ fst D ⟫↪ m} (member (fst D) m) (snd D)

  at : ⟪ fst D ⟫ → E.Dom
  at m = toS m , member (fst D) m

  fib : (m : ⟪ fst D ⟫)
      → Σ[ k ∈ ⟪ fst C ⟫ ] (⟪ fst C ⟫↪ k ≡ fst (E.toFun (at m)))
  fib m = fiber (fst C)
    (ran (toS m) (E.toFun (at m)) (E.toFun-graph (at m)))

  -- The honest injection, between the small index types.
  small : ⟪ fst D ⟫ → ⟪ fst C ⟫
  small m = fst (fib m)

  small-inj : (m n : ⟪ fst D ⟫) → small m ≡ small n → m ≡ n
  -- ⟪ a ⟫ does not determine a by unification, so the set is named.
  small-inj m n e = ↪-inj {a = fst D} {m = m} {n = n}
    (E.toFun-inj ij (at m) (at n)
      (sym (snd (fib m)) ∙ cong ⟪ fst C ⟫↪ e ∙ snd (fib n)))
