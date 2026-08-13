{-# OPTIONS --cubical --safe --guardedness #-}

open import Base.Prelude
open import Base.Truth
open import Base.Classical using ( LEM )

module ProbeLJ147SquareLawViaCol {ℓ : Level} (lem : LEM (ℓ-suc ℓ)) where

open import FOL.ZFStructure using ( module hPropStructure )
open import V.Hierarchy {ℓ} using ( 𝒮ᵥ; ∈-irrefl )
open import V.Model {ℓ}
  using ( ∈sucV-elim; ∈sucV-inl; self∈sucV; ω-specV; numeralV; numeralV≡# )
open import V.Presentation {ℓ} using ( member; fiber; ↪-inj )
open import L.Constructible {ℓ} using ( IsOrd )
open import L.Ordinal {ℓ}
  using ( mem-ord; suc-ord; ω-ord; #∈ω; ∈#-elim )
open import V.Coding {ℓ} using ( #-inj′; #mono )
open import L.Ordinal.Linear {ℓ} lem using ( ord-tri )
open import ProbeLJ147Collapse {ℓ} lem
  using ( ordSWO; _≺₁_; _≤₁_; maxOrd; max-spec; Pair; _≺_; tri≺; wf≺
        ; trans₁; godSWO; ≺-dec; colPick; colStep; col; col-compute; col-ord
        ; col-mono; col-inj; col-img )
open import L.WellOrder.Base {ℓₚ = ℓ-suc ℓ}
  using ( SWO; Tri; lt; eq; gt; IsLeast; leastOf; module SWO )
open import ProbeLJ117Combinators {ℓₚ = ℓ-suc ℓ}
  using ( natSWO )

import Cubical.Data.Empty as Empty
import Cubical.HITs.PropositionalTruncation as PT
open PT using ( ∣_∣₁; ∥_∥₁; squash₁ )
open import Cubical.Data.Sum using ( _⊎_; inl; inr )
open import Cubical.Data.Sigma using ( Σ≡Prop; ΣPathP )
open import Cubical.Data.Nat using ( _·_; snotz; znots; injSuc )
import Cubical.Data.Fin.Base as FB
open import Cubical.Data.Fin.Properties using ( factorEquiv; pigeonhole )
open import Cubical.Data.Nat.Order using ( _<_; isProp≤; ≤-refl )
open import Cubical.Foundations.Equiv
  using ( equivFun; invEq; retEq; idEquiv; _≃_ )
open import Cubical.Foundations.Univalence using ( pathToEquiv )
open import Cubical.Foundations.HLevels using ( isProp× )
open import Cubical.HITs.CumulativeHierarchy.Base using ( sett )
open import Cubical.HITs.CumulativeHierarchy.Properties
  using ( _∈ₛ_; ∈∈ₛ; ⟪_⟫; ⟪_⟫↪; ∈ₛ⟪_⟫↪_ )
open import Cubical.HITs.CumulativeHierarchy.Constructions
  using ( ⋃_; union-ax; ∅; ∅-empty; module InfinitySet )
open InfinitySet using ( sucV; #_; ω )
open import Cubical.Induction.WellFounded using ( WellFounded; module WFI )

open TruthAlgebra (hPropAlgebra (ℓ-suc ℓ))
open hPropStructure 𝒮ᵥ
module AbstractH₀ (A : Type ℓ)
                  (↪A : A → S)
                  (↪A-inj : {m n : A} → ↪A m ≡ ↪A n → m ≡ n)
                  (prec : A × A → A × A → Type (ℓ-suc ℓ))
                  (γp : A × A → S)
                  (F : S → Type ℓ)
                  (↪F : (a : S) → F a → S)
                  (fiberF : (a : S) {x : S} → ⟨ x ∈ˢ a ⟩ → Σ[ m ∈ F a ] (↪F a m ≡ x))
                  (fst∈sucmaxF : {p q : A × A} → prec p q → ⟨ ↪A (fst p) ∈ˢ sucV (γp q) ⟩)
                  (snd∈sucmaxF : {p q : A × A} → prec p q → ⟨ ↪A (snd p) ∈ˢ sucV (γp q) ⟩) where

  h₀ : (p : A × A) → (r : A × A) → prec r p → F (sucV (γp p)) × F (sucV (γp p))
  h₀ p r pr = (fiberF (sucV (γp p)) (fst∈sucmaxF {r} {p} pr) .fst
             , fiberF (sucV (γp p)) (snd∈sucmaxF {r} {p} pr) .fst)

  h₀-inj : (p : A × A) {r r' : A × A} (pr : prec r p) (pr' : prec r' p)
         → h₀ p r pr ≡ h₀ p r' pr' → r ≡ r'
  h₀-inj p {a , b} {a' , b'} pr pr' e = cong₂ _,_ ea eb
    where
    β : S
    β = sucV (γp p)
    ea : a ≡ a'
    ea = ↪A-inj (sym (fiberF β (fst∈sucmaxF {a , b} {p} pr) .snd)
      ∙ cong (↪F β) (cong fst e)
      ∙ fiberF β (fst∈sucmaxF {a' , b'} {p} pr') .snd)
    eb : b ≡ b'
    eb = ↪A-inj (sym (fiberF β (snd∈sucmaxF {a , b} {p} pr) .snd)
      ∙ cong (↪F β) (cong snd e)
      ∙ fiberF β (snd∈sucmaxF {a' , b'} {p} pr') .snd)
module FiniteBase where

  P : (n : ℕ) (m : ⟪ # n ⟫) → ℕ → hProp (ℓ-suc ℓ)
  P n m k = ((k < n) × (⟪ # n ⟫↪ m ≡ # k))
          , isProp× isProp≤ (isSetS (⟪ # n ⟫↪ m) (# k))

  ω-mem→numeral : (β : S) → ⟨ β ∈ˢ ω ⟩ → ∥ Σ[ n ∈ ℕ ] (β ≡ # n) ∥₁
  ω-mem→numeral β β∈ω = PT.map hit (subst ⟨_⟩ (ω-specV β) β∈ω)
    where
    hit : Σ[ n ∈ Lift {ℓ-zero} {ℓ-suc ℓ} ℕ ] ⟨ β ≈ˢ numeralV (lower n) ⟩
        → Σ[ n ∈ ℕ ] (β ≡ # n)
    hit (n , p) = lower n , p ∙ numeralV≡# (lower n)

  toFin : (n : ℕ) → ⟪ # n ⟫ → FB.Fin n
  toFin n m = k , k<n
    where
    s = leastOf natSWO lem (P n m) (∈#-elim n (⟪ # n ⟫↪ m) (member (# n) m))
    k : ℕ
    k = fst s
    k<n : k < n
    k<n = fst (fst (snd s))

  toFin-spec : (n : ℕ) (m : ⟪ # n ⟫) → ⟪ # n ⟫↪ m ≡ # (fst (toFin n m))
  toFin-spec n m = snd (fst (snd s))
    where
    s = leastOf natSWO lem (P n m) (∈#-elim n (⟪ # n ⟫↪ m) (member (# n) m))

  toFin-inj : (n : ℕ) (m₁ m₂ : ⟪ # n ⟫) → toFin n m₁ ≡ toFin n m₂ → m₁ ≡ m₂
  toFin-inj n m₁ m₂ e = ↪-inj {a = # n}
    (toFin-spec n m₁ ∙ cong (λ k → # k) (cong fst e) ∙ sym (toFin-spec n m₂))

  fromFin : (n : ℕ) → FB.Fin n → ⟪ # n ⟫
  fromFin n (k , k<n) = fiber (# n) (#mono k n k<n) .fst

  fromFin-spec : (n : ℕ) (i : FB.Fin n) → ⟪ # n ⟫↪ (fromFin n i) ≡ # (fst i)
  fromFin-spec n (k , k<n) = fiber (# n) (#mono k n k<n) .snd

  fromFin-inj : (n : ℕ) (i₁ i₂ : FB.Fin n) → fromFin n i₁ ≡ fromFin n i₂ → i₁ ≡ i₂
  fromFin-inj n i₁ i₂ e = Σ≡Prop (λ _ → isProp≤)
    (#-inj′ (sym (fromFin-spec n i₁) ∙ cong (⟪ # n ⟫↪) e ∙ fromFin-spec n i₂))

  factor : (n : ℕ) → FB.Fin n × FB.Fin n → FB.Fin (n · n)
  factor n = equivFun (factorEquiv {n = n} {m = n})

  factor-inj : (n : ℕ) (x y : FB.Fin n × FB.Fin n)
             → factor n x ≡ factor n y → x ≡ y
  factor-inj n x y e =
    sym (retEq (factorEquiv {n = n} {m = n}) x)
      ∙ cong (invEq (factorEquiv {n = n} {m = n})) e
      ∙ retEq (factorEquiv {n = n} {m = n}) y

  no-inj-Fin : (n : ℕ) → (f : FB.Fin (suc n) → FB.Fin n)
             → ((x y : FB.Fin (suc n)) → f x ≡ f y → x ≡ y) → Empty.⊥
  no-inj-Fin n f finj = i#j (finj i j feq)
    where
    i = fst (pigeonhole (≤-refl {m = suc n}) f)
    j = fst (snd (pigeonhole (≤-refl {m = suc n}) f))
    prf = snd (snd (pigeonhole (≤-refl {m = suc n}) f))
    i#j = fst prf
    feq : f i ≡ f j
    feq = snd prf

  module AbstractChase (E : ℕ → Type ℓ)
                       (toFinE : (n : ℕ) → E n → FB.Fin n)
                       (toFinE-inj : (n : ℕ) (m₁ m₂ : E n) → toFinE n m₁ ≡ toFinE n m₂ → m₁ ≡ m₂)
                       (fromFinE : (n : ℕ) → FB.Fin n → E n)
                       (fromFinE-inj : (n : ℕ) (i₁ i₂ : FB.Fin n) → fromFinE n i₁ ≡ fromFinE n i₂ → i₁ ≡ i₂) where

    module NoInj (A : Type ℓ) (into : (m : ℕ) → E m → A)
                 (into-inj : (m : ℕ) (i₁ i₂ : E m) → into m i₁ ≡ into m i₂ → i₁ ≡ i₂) where

      no-inj : (n : ℕ) → (f : A → E n × E n)
             → ((x y : A) → f x ≡ f y → x ≡ y) → Empty.⊥
      no-inj n f finj = no-inj-Fin (n · n) g g-inj
        where
        g : FB.Fin (suc (n · n)) → FB.Fin (n · n)
        g i = factor n ( toFinE n (fst (f (into (suc (n · n)) (fromFinE (suc (n · n)) i))))
                       , toFinE n (snd (f (into (suc (n · n)) (fromFinE (suc (n · n)) i)))))
        g-inj : (x y : FB.Fin (suc (n · n))) → g x ≡ g y → x ≡ y
        g-inj x y e = fromFinE-inj (suc (n · n)) x y
          (into-inj (suc (n · n))
            (fromFinE (suc (n · n)) x) (fromFinE (suc (n · n)) y)
            (finj Xx Xy pair-eq))
          where
          Xx : A
          Xx = into (suc (n · n)) (fromFinE (suc (n · n)) x)
          Xy : A
          Xy = into (suc (n · n)) (fromFinE (suc (n · n)) y)
          p-eq : (toFinE n (fst (f Xx)) , toFinE n (snd (f Xx)))
               ≡ (toFinE n (fst (f Xy)) , toFinE n (snd (f Xy)))
          p-eq = factor-inj n
                   (toFinE n (fst (f Xx)) , toFinE n (snd (f Xx)))
                   (toFinE n (fst (f Xy)) , toFinE n (snd (f Xy))) e
          fst-eq : toFinE n (fst (f Xx)) ≡ toFinE n (fst (f Xy))
          fst-eq = cong fst p-eq
          snd-eq : toFinE n (snd (f Xx)) ≡ toFinE n (snd (f Xy))
          snd-eq = cong snd p-eq
          fst-eq′ : fst (f Xx) ≡ fst (f Xy)
          fst-eq′ = toFinE-inj n (fst (f Xx)) (fst (f Xy)) fst-eq
          snd-eq′ : snd (f Xx) ≡ snd (f Xy)
          snd-eq′ = toFinE-inj n (snd (f Xx)) (snd (f Xy)) snd-eq
          pair-eq : f Xx ≡ f Xy
          pair-eq = ΣPathP (fst-eq′ , snd-eq′)
  module _ (α : S) (oα : IsOrd α) (ω∈α : ⟨ ω ∈ˢ α ⟩) where

    numeral-in-α : (m : ℕ) → ⟨ (# m) ∈ˢ α ⟩
    numeral-in-α m = oα .fst (#∈ω m) ω∈α

    numeral-into-α : (m : ℕ) → ⟪ # m ⟫ → ⟪ α ⟫
    numeral-into-α m i = fiber α (oα .fst (member (# m) i) (numeral-in-α m)) .fst

    numeral-into-α-inj : (m : ℕ) (i₁ i₂ : ⟪ # m ⟫)
                       → numeral-into-α m i₁ ≡ numeral-into-α m i₂ → i₁ ≡ i₂
    numeral-into-α-inj m i₁ i₂ e = ↪-inj {a = # m}
      (sym (fiber α (oα .fst (member (# m) i₁) (numeral-in-α m)) .snd)
       ∙ cong (⟪ α ⟫↪) e
       ∙ fiber α (oα .fst (member (# m) i₂) (numeral-in-α m)) .snd)

    no-inj-finite : (n : ℕ) → (f : ⟪ α ⟫ → ⟪ # n ⟫ × ⟪ # n ⟫)
                  → ((x y : ⟪ α ⟫) → f x ≡ f y → x ≡ y) → Empty.⊥
    no-inj-finite n f finj =
      AbstractChase.NoInj.no-inj
        (λ n → ⟪ # n ⟫)
        toFin toFin-inj
        fromFin fromFin-inj
        (⟪ α ⟫)
        (numeral-into-α)
        (numeral-into-α-inj)
        n f finj

  finite-excl : (α : S) (oα : IsOrd α) (ω∈α : ⟨ ω ∈ˢ α ⟩)
              → (β : S) → IsOrd β → ⟨ β ∈ˢ ω ⟩
              → (f : ⟪ α ⟫ → ⟪ β ⟫ × ⟪ β ⟫)
              → ((x y : ⟪ α ⟫) → f x ≡ f y → x ≡ y) → Empty.⊥
  finite-excl α oα ω∈α β oβ β∈ω f finj =
    PT.rec Empty.isProp⊥ go (ω-mem→numeral β β∈ω)
    where
    go : Σ[ n ∈ ℕ ] (β ≡ # n) → Empty.⊥
    go (n , p) = no-inj-finite α oα ω∈α n f' finj'
      where
      e : ⟪ β ⟫ × ⟪ β ⟫ ≃ ⟪ # n ⟫ × ⟪ # n ⟫
      e = pathToEquiv (cong (λ w → ⟪ w ⟫ × ⟪ w ⟫) p)
      f' : ⟪ α ⟫ → ⟪ # n ⟫ × ⟪ # n ⟫
      f' x = equivFun e (f x)
      finj' : (x y : ⟪ α ⟫) → f' x ≡ f' y → x ≡ y
      finj' x y e' = finj x y
        (sym (retEq e (f x)) ∙ cong (invEq e) e' ∙ retEq e (f y))

open FiniteBase
-- The square law, and its truncated form.
sq : S → Type ℓ
sq α = Σ[ f ∈ (⟪ α ⟫ × ⟪ α ⟫ → ⟪ α ⟫) ]
         ((x y : ⟪ α ⟫ × ⟪ α ⟫) → f x ≡ f y → x ≡ y)

-- An ordinal is initial in this chapter: it has omega as a member (so omega
-- itself is not initial), is closed under successors, and its index injects
-- into no infinite member's square.
Init : S → Type (ℓ-suc ℓ)
Init α = IsOrd α
       × ⟨ ω ∈ˢ α ⟩
       × ((γ : S) → ⟨ γ ∈ˢ α ⟩ → ⟨ sucV γ ∈ˢ α ⟩)
       × ((β : S) → IsOrd β → ⟨ β ∈ˢ α ⟩ → ⟨ ω ∈ˢ β ⟩
          → (f : ⟪ α ⟫ → ⟪ β ⟫ × ⟪ β ⟫)
          → ((m n : ⟪ α ⟫) → f m ≡ f n → m ≡ n) → Empty.⊥)

-- The order core with the no-injection hypothesis in its square form: the
-- law at members is never needed, since the exclusion case refutes an
-- injection of the index into the square of a member directly.
module InitialCore (α : S) (oα : IsOrd α)
  (α-limit : (γ : S) → ⟨ γ ∈ˢ α ⟩ → ⟨ sucV γ ∈ˢ α ⟩)
  (noinj² : (β : S) → IsOrd β → ⟨ β ∈ˢ α ⟩ → ⟨ ω ∈ˢ β ⟩
          → (f : ⟪ α ⟫ → ⟪ β ⟫ × ⟪ β ⟫)
          → ((m n : ⟪ α ⟫) → f m ≡ f n → m ≡ n) → Empty.⊥)
  (finite-excl : (β : S) → IsOrd β → ⟨ β ∈ˢ ω ⟩
               → (f : ⟪ α ⟫ → ⟪ β ⟫ × ⟪ β ⟫)
               → ((m n : ⟪ α ⟫) → f m ≡ f n → m ≡ n) → Empty.⊥) where

  PairA : Type ℓ
  PairA = Pair α oα

  colA : PairA → S
  colA = col α oα

  _≺'_ : PairA → PairA → Type (ℓ-suc ℓ)
  _≺'_ = _≺_ α oα

  prec1 : ⟪ α ⟫ → ⟪ α ⟫ → Type (ℓ-suc ℓ)
  prec1 = _≺₁_ α oα

  leq : ⟪ α ⟫ → ⟪ α ⟫ → Type (ℓ-suc ℓ)
  leq = _≤₁_ α oα

  max' : ⟪ α ⟫ → ⟪ α ⟫ → ⟪ α ⟫
  max' = maxOrd α oα

  trans1 : (m n k : ⟪ α ⟫) → prec1 m n → prec1 n k → prec1 m k
  trans1 = trans₁ α oα

  tri' : (p q : PairA) → Tri (p ≺' q) (p ≡ q) (q ≺' p)
  tri' = tri≺ α oα

  cm : {p q : PairA} → p ≺' q → ⟨ colA p ∈ˢ colA q ⟩
  cm = col-mono α oα

  ci : {p q : PairA} → colA p ≡ colA q → p ≡ q
  ci = col-inj α oα

  cimg : (q : PairA) (b : S) → ⟨ b ∈ˢ colA q ⟩
       → ∥ Σ[ r ∈ PairA ] (colA r ≡ b) ∥₁
  cimg = col-img α oα

  colo : (p : PairA) → IsOrd (colA p)
  colo = col-ord α oα

  cc : (p : PairA) → colA p ≡ colStep α oα p (λ r _ → colA r)
  cc = col-compute α oα

  wf : WellFounded _≺'_
  wf = wf≺ α oα

  god : SWO PairA
  god = godSWO α oα

  ≺dec : (p q : PairA) → (p ≺' q) ⊎ ((p ≺' q) → Empty.⊥)
  ≺dec = ≺-dec α oα


  ≤₁→≺₁ : (m n k : ⟪ α ⟫) → leq m n → prec1 n k → prec1 m k
  ≤₁→≺₁ m n k (inl h) h' = trans1 m n k h h'
  ≤₁→≺₁ m n k (inr e) h' = subst (λ w → prec1 w k) (sym e) h'

  ≤₁-subst : (m n n' : ⟪ α ⟫) → leq m n → n ≡ n' → leq m n'
  ≤₁-subst m n n' (inl h) e = inl (subst (λ w → prec1 m w) e h)
  ≤₁-subst m n n' (inr q) e = inr (q ∙ e)

  ≤₁-into-suc : (m n : ⟪ α ⟫) → leq m n → ⟨ ⟪ α ⟫↪ m ∈ˢ sucV (⟪ α ⟫↪ n) ⟩
  ≤₁-into-suc m n (inl h) = ∈sucV-inl h
  ≤₁-into-suc m n (inr e) =
    subst (λ w → ⟨ ⟪ α ⟫↪ w ∈ˢ sucV (⟪ α ⟫↪ n) ⟩) (sym e) (self∈sucV (⟪ α ⟫↪ n))

  fst∈sucmax : {p q : PairA} → p ≺' q
             → ⟨ ⟪ α ⟫↪ (fst p) ∈ˢ sucV (⟪ α ⟫↪ (max' (fst q) (snd q))) ⟩
  fst∈sucmax {a , b} {c , d} (inl h) =
    ∈sucV-inl (≤₁→≺₁ a (max' a b) (max' c d) (max-spec α oα a b .fst) h)
  fst∈sucmax {a , b} {c , d} (inr (e , _)) =
    ≤₁-into-suc a (max' c d)
      (≤₁-subst a (max' a b) (max' c d) (max-spec α oα a b .fst) e)

  snd∈sucmax : {p q : PairA} → p ≺' q
             → ⟨ ⟪ α ⟫↪ (snd p) ∈ˢ sucV (⟪ α ⟫↪ (max' (fst q) (snd q))) ⟩
  snd∈sucmax {a , b} {c , d} (inl h) =
    ∈sucV-inl (≤₁→≺₁ b (max' a b) (max' c d) (max-spec α oα a b .snd) h)
  snd∈sucmax {a , b} {c , d} (inr (e , _)) =
    ≤₁-into-suc b (max' c d)
      (≤₁-subst b (max' a b) (max' c d) (max-spec α oα a b .snd) e)

  Pb : (b : S) → PairA → hProp (ℓ-suc ℓ)
  Pb b r = (colA r ≡ b) , isSetS (colA r) b

  colr≺ : {p : PairA} (b : S) → ⟨ b ∈ˢ colA p ⟩ → (r : PairA)
        → colA r ≡ b → r ≺' p
  colr≺ {p} b b∈ r e = go (tri' r p)
    where
    go : Tri (r ≺' p) (r ≡ p) (p ≺' r) → r ≺' p
    go (lt h) = h
    go (eq q) = Empty.rec
      (∈-irrefl (colA p)
        (subst (λ w → ⟨ w ∈ˢ colA p ⟩) (sym (cong colA (sym q) ∙ e)) b∈))
    go (gt h) = Empty.rec
      (∈-irrefl (colA p)
        (colo p .fst (cm h) (subst (λ w → ⟨ w ∈ˢ colA p ⟩) (sym e) b∈)))

  module WF = WFI wf

  opaque
    descent : (p : PairA) (b : S) → ⟨ b ∈ˢ colA p ⟩
            → Σ[ r ∈ PairA ] ((r ≺' p) × (colA r ≡ b))
    descent p b b∈ = fst s , (colr≺ b b∈ (fst s) (fst (snd s)) , fst (snd s))
      where
      s : Σ[ m ∈ PairA ] IsLeast god (Pb b) m
      s = leastOf god lem (Pb b) (cimg p b b∈)

    g : (p : PairA) (b : S) → ⟨ b ∈ˢ colA p ⟩ → PairA
    g p b b∈ = fst (descent p b b∈)

    g-inj : (p : PairA) {b b' : S} (hb : ⟨ b ∈ˢ colA p ⟩) (hb' : ⟨ b' ∈ˢ colA p ⟩)
          → g p b hb ≡ g p b' hb' → b ≡ b'
    g-inj p {b} {b'} hb hb' e =
      sym (snd (descent p b hb) .snd) ∙ cong colA e ∙ snd (descent p b' hb') .snd

    γp : PairA → S
    γp p = ⟪ α ⟫↪ (max' (fst p) (snd p))

    h₀ : (p : PairA) → (r : PairA) → r ≺' p → ⟪ sucV (γp p) ⟫ × ⟪ sucV (γp p) ⟫
    h₀ = AbstractH₀.h₀ (⟪ α ⟫) (⟪ α ⟫↪) (↪-inj {a = α}) _≺'_ γp (⟪_⟫) (⟪_⟫↪) fiber fst∈sucmax snd∈sucmax

    h₀-inj : (p : PairA) {r r' : PairA} (pr : r ≺' p) (pr' : r' ≺' p)
           → h₀ p r pr ≡ h₀ p r' pr' → r ≡ r'
    h₀-inj = AbstractH₀.h₀-inj (⟪ α ⟫) (⟪ α ⟫↪) (↪-inj {a = α}) _≺'_ γp (⟪_⟫) (⟪_⟫↪) fiber fst∈sucmax snd∈sucmax

    comp₀ : (p : PairA) (e : colA p ≡ α) → ⟪ α ⟫ → ⟪ sucV (γp p) ⟫ × ⟪ sucV (γp p) ⟫
    comp₀ p e m = h₀ p (g p (⟪ α ⟫↪ m) (b∈ m))
                      (snd (descent p (⟪ α ⟫↪ m) (b∈ m)) .fst)
      where
      b∈ : (m : ⟪ α ⟫) → ⟨ ⟪ α ⟫↪ m ∈ˢ colA p ⟩
      b∈ m = subst (λ w → ⟨ ⟪ α ⟫↪ m ∈ˢ w ⟩) (sym e)
        (∈∈ₛ {a = ⟪ α ⟫↪ m} {b = α} .snd (∈ₛ⟪ α ⟫↪ m))

    comp₀-inj : (p : PairA) (e : colA p ≡ α) (m n : ⟪ α ⟫)
              → comp₀ p e m ≡ comp₀ p e n → m ≡ n
    comp₀-inj p e m n e' = ↪-inj {a = α}
      (g-inj p (b∈ m) (b∈ n)
        (h₀-inj p (snd (descent p (⟪ α ⟫↪ m) (b∈ m)) .fst)
                  (snd (descent p (⟪ α ⟫↪ n) (b∈ n)) .fst) e'))
      where
      b∈ : (m : ⟪ α ⟫) → ⟨ ⟪ α ⟫↪ m ∈ˢ colA p ⟩
      b∈ m = subst (λ w → ⟨ ⟪ α ⟫↪ m ∈ˢ w ⟩) (sym e)
        (∈∈ₛ {a = ⟪ α ⟫↪ m} {b = α} .snd (∈ₛ⟪ α ⟫↪ m))

    β≠ω : (p : PairA) → sucV (γp p) ≡ ω → Empty.⊥
    β≠ω p e = PT.rec Empty.isProp⊥ go (ω-mem→numeral (γp p) γp∈ω)
      where
      γp∈ω : ⟨ γp p ∈ˢ ω ⟩
      γp∈ω = subst (λ w → ⟨ γp p ∈ˢ w ⟩) e (self∈sucV (γp p))
      go : Σ[ n ∈ ℕ ] (γp p ≡ # n) → Empty.⊥
      go (n , q) = ∈-irrefl ω
        (subst (λ w → ⟨ w ∈ˢ ω ⟩) (sym (cong sucV q) ∙ e) (#∈ω (suc n)))

    exclude : (p : PairA) → colA p ≡ α → Empty.⊥
    exclude p e = go (ord-tri β ordβ ω ω-ord)
      where
      γp∈α : ⟨ γp p ∈ˢ α ⟩
      γp∈α = ∈∈ₛ {a = γp p} {b = α} .snd (∈ₛ⟪ α ⟫↪ (max' (fst p) (snd p)))
      β : S
      β = sucV (γp p)
      ordβ : IsOrd β
      ordβ = suc-ord (mem-ord {A = α} oα (γp p) γp∈α)
      β∈α : ⟨ β ∈ˢ α ⟩
      β∈α = α-limit (γp p) γp∈α
      go : (⟨ β ∈ˢ ω ⟩ ⊎ ((β ≡ ω) ⊎ ⟨ ω ∈ˢ β ⟩)) → Empty.⊥
      go (inl β∈ω) = finite-excl β ordβ β∈ω (comp₀ p e) (comp₀-inj p e)
      go (inr (inl β≡ω)) = β≠ω p β≡ω
      go (inr (inr ω∈β)) = noinj² β ordβ β∈α ω∈β (comp₀ p e) (comp₀-inj p e)

    gₚ : (p : PairA) → PairA → S
    gₚ p r = colPick α oα p (λ r _ → colA r) r (≺dec r p)

    gₚ-inl : (p r : PairA) → (rp : r ≺' p) → gₚ p r ≡ sucV (colA r)
    gₚ-inl p r rp = go (≺dec r p)
      where
      go : (d : (r ≺' p) ⊎ ((r ≺' p) → Empty.⊥))
         → colPick α oα p (λ r _ → colA r) r d ≡ sucV (colA r)
      go (inl _) = refl
      go (inr ¬rp) = Empty.rec (¬rp rp)

    gₚ-inr : (p r : PairA) → ((r ≺' p) → Empty.⊥) → gₚ p r ≡ ∅
    gₚ-inr p r ¬rp = go (≺dec r p)
      where
      go : (d : (r ≺' p) ⊎ ((r ≺' p) → Empty.⊥))
         → colPick α oα p (λ r _ → colA r) r d ≡ ∅
      go (inl rp) = Empty.rec (¬rp rp)
      go (inr _) = refl

    colp⊆α : (p : PairA) → ((r : PairA) → r ≺' p → ⟨ colA r ∈ˢ α ⟩)
           → (x : S) → ⟨ x ∈ˢ colA p ⟩ → ⟨ x ∈ˢ α ⟩
    colp⊆α p rec x x∈ = PT.rec (snd (x ∈ˢ α)) viaUnion
      (union-ax (sett PairA (gₚ p)) x .fst
        (∈∈ₛ {a = x} {b = ⋃ (sett PairA (gₚ p))} .fst
          (subst (λ w → ⟨ x ∈ˢ w ⟩) (cc p) x∈)))
      where
      viaUnion : Σ[ v ∈ S ] (⟨ v ∈ₛ sett PairA (gₚ p) ⟩ × ⟨ x ∈ₛ v ⟩) → ⟨ x ∈ˢ α ⟩
      viaUnion (v , (v∈ₛsett , x∈ₛv)) = PT.rec (snd (x ∈ˢ α)) viaFiber
        (∈∈ₛ {a = v} {b = sett PairA (gₚ p)} .snd v∈ₛsett)
        where
        viaFiber : Σ[ r ∈ PairA ] (gₚ p r ≡ v) → ⟨ x ∈ˢ α ⟩
        viaFiber (r , gr≡v) = decide (≺dec r p)
          where
          x∈gr : ⟨ x ∈ₛ gₚ p r ⟩
          x∈gr = subst (λ w → ⟨ x ∈ₛ w ⟩) (sym gr≡v) x∈ₛv
          decide : (r ≺' p) ⊎ ((r ≺' p) → Empty.⊥) → ⟨ x ∈ˢ α ⟩
          decide (inl rp) = ∈sucV-elim {A = colA r} {x = x} (snd (x ∈ˢ α))
            (∈∈ₛ {a = x} {b = sucV (colA r)} .snd
              (subst (λ w → ⟨ x ∈ₛ w ⟩) (gₚ-inl p r rp) x∈gr))
            (λ x∈r → oα .fst x∈r (rec r rp))
            (λ x≡r → subst (λ w → ⟨ w ∈ˢ α ⟩) (sym x≡r) (rec r rp))
          decide (inr ¬rp) = Empty.rec
            (∅-empty x (subst (λ w → ⟨ x ∈ₛ w ⟩) (gₚ-inr p r ¬rp) x∈gr))

    col≤α : (p : PairA) → ((r : PairA) → r ≺' p → ⟨ colA r ∈ˢ α ⟩)
          → ⟨ colA p ∈ˢ α ⟩
    col≤α p rec = go (ord-tri (colA p) (colo p) α oα)
      where
      go : (⟨ colA p ∈ˢ α ⟩ ⊎ ((colA p ≡ α) ⊎ ⟨ α ∈ˢ colA p ⟩)) → ⟨ colA p ∈ˢ α ⟩
      go (inl h) = h
      go (inr (inl e)) = Empty.rec (exclude p e)
      go (inr (inr h)) = Empty.rec (∈-irrefl α (colp⊆α p rec α h))

    col∈α : (p : PairA) → ⟨ colA p ∈ˢ α ⟩
    col∈α = WF.induction {P = λ p → ⟨ colA p ∈ˢ α ⟩} step
      where
      step : (p : PairA) → ((r : PairA) → r ≺' p → ⟨ colA r ∈ˢ α ⟩)
           → ⟨ colA p ∈ˢ α ⟩
      step p rec = col≤α p (λ r rp → rec r rp)

module Initial (α : S) (iα : Init α) where
  module IC = InitialCore α (iα .fst) (iα .snd .snd .fst) (iα .snd .snd .snd)
                 (FiniteBase.finite-excl α (iα .fst) (iα .snd .fst))

  open IC

  pair : ⟪ α ⟫ × ⟪ α ⟫ → ⟪ α ⟫
  pair p = fiber α {x = colA p} (col∈α p) .fst

  pair-inj : (p q : ⟪ α ⟫ × ⟪ α ⟫) → pair p ≡ pair q → p ≡ q
  pair-inj p q e = col-inj α (iα .fst) {p = p} {q = q}
    (sym (fiber α {x = colA p} (col∈α p) .snd)
     ∙ cong (⟪ α ⟫↪) e
     ∙ fiber α {x = colA q} (col∈α q) .snd)

  square : sq α
  square = pair , pair-inj

  truncated : ∥ sq α ∥₁
  truncated = ∣ square ∣₁

opaque
  via-col-square : (α : S) → Init α → sq α
  via-col-square α iα = Initial.square α iα

  via-col-truncated : (α : S) → Init α → ∥ sq α ∥₁
  via-col-truncated α iα = Initial.truncated α iα
