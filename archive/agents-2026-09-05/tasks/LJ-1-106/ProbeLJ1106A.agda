{-# OPTIONS --cubical --safe --guardedness #-}

-- [LJ-1.106] probe A: build Init SiteAt.κ with no hypothesis left.
--
-- The [LJ-1.101] assembly (src/ProbeLJ1101A.agda:105-109) checks
-- Init SiteAt.κ under exactly two hypotheses: the square pairing
-- ⟪ ω ⟫ × ⟪ ω ⟫ ↪ ⟪ ω ⟫ and the successor closure of κ.  This probe
-- supplies both, so Init SiteAt.κ holds outright.
--
-- Piece 1: the pairing.  The tree delivers the ℕ-level square pairing
-- with injectivity (src/FOL/Count.lagda.md:29-30, :59-60) and the
-- injective numerals (src/V/Coding.lagda.md:114-115).  The one
-- unmeasured step is the presentation bijection ⟪ ω ⟫ ≃ ℕ:  ℕ → ⟪ ω ⟫
-- by the numerals, and ⟪ ω ⟫ → ℕ from the delivered
-- FiniteBase.ω-mem→numeral (src/L/Ordinal/SquareLaw.lagda.md:539-542),
-- eliminating the truncation because the numeral fiber is a
-- proposition.  No LEM and no choice.
--
-- Piece 2: the successor closure.  For wo with ot wo = γ, the order
-- type of sucV γ is realized on a subset of ω by pulling the ∈-order
-- on sucV γ back along the countability injection of its presentation
-- (the delivered countAt, src/ProbeLJ194A.agda:555-556).  The
-- pullback well-order is a generic module over an ordinal α and an
-- injection ⟪ α ⟫ ↪ ⟪ ω ⟫; the successor closure instantiates it at
-- α = sucV γ.  This is the [LJ-1.94] Pullback shape
-- (src/ProbeLJ194A.agda:937-1107) with the carrier left generic.
--
-- Untracked probe; ONE agda process under GHCRTS="-A64m -I0 -M8g";
-- never committed.

open import Base.Prelude
open import Base.Truth
open import Base.Classical using ( LEM )

module ProbeLJ1106A {ℓ : Level} (lem : LEM (ℓ-suc ℓ)) where

import ProbeLJ194A {ℓ} lem as P194
open P194 using ( module SmallWO; module Hartogs; module SiteAt
                ; module OrdSWO; module OrdinalSelf; countAt; isSet⟪⟫
                ; enc; dec; decEnc; encDec; dec∘enc )
import ProbeLJ192A {ℓ} as P192
open P192 using ( module OrderType; module Unique )
import L.Ordinal.SquareLaw {ℓ} lem as SQ
open SQ using ( module FiniteBase )
import FOL.Count {ℓ} as Count
open import V.Coding {ℓ} using ( #-inj′ )
open import V.Hierarchy {ℓ} using ( 𝒮ᵥ; ∈-irrefl )
open import V.Presentation {ℓ} using ( fiber )
open import V.Model {ℓ} using ( ∈sucV-elim; ∈sucV-inl; self∈sucV )
open import L.Constructible {ℓ} using ( IsOrd )
open import L.Ordinal {ℓ} using ( #∈ω; suc-ord )
open import FOL.ZFStructure using ( module hPropStructure )
open import Cubical.HITs.CumulativeHierarchy.Properties
  using ( _∈ₛ_; ∈∈ₛ; ⟪_⟫; ⟪_⟫↪; isEmb⟪_⟫↪; ∈ₛ⟪_⟫↪_ )
open import Cubical.HITs.CumulativeHierarchy.Constructions
  using ( module InfinitySet )
open InfinitySet {ℓ} using ( ω; sucV; #_ )
open import Cubical.Foundations.Isomorphism using ( iso; isoToEquiv )
open import Cubical.Foundations.Equiv using ( _≃_ )
open import Cubical.Functions.Embedding using ( isEmbedding→hasPropFibers )
open import Cubical.Data.Sigma using ( ΣPathP; Σ≡Prop )
open import Cubical.Foundations.HLevels using ( isProp× )
open import Cubical.Foundations.Transport using ( transportTransport⁻ )
open import Cubical.Induction.WellFounded using ( Acc; acc )
open import L.WellOrder.Base {ℓₚ = ℓ-suc ℓ} using ( SWO; Tri; lt; eq; gt )
open import Cubical.Data.Nat using ( ℕ )
open import Cubical.Data.Nat.Properties using ( injSuc; znots )
open import Cubical.Data.Sum using ( _⊎_; inl; inr )
open import Cubical.Data.Sum.Properties using ( isProp⊎ )
open import Cubical.Data.Unit using ( Unit; tt )
import Cubical.Data.Empty as Empty
import Cubical.HITs.PropositionalTruncation as PT
open PT using ( ∣_∣₁; ∥_∥₁; squash₁ )

open hPropStructure 𝒮ᵥ

-- =====================================================================
-- PIECE 1: the pairing, and the presentation bijection inside it.
--
-- The numerals give an injection ℕ → ⟪ ω ⟫.  Its inverse reads the
-- numeral of a presented element: every element of ⟪ ω ⟫ is a numeral
-- (FiniteBase.ω-mem→numeral), and the numeral fiber is a proposition
-- because the numerals are injective, so the truncation eliminates
-- without LEM.  The two directions prove the bijection.
-- =====================================================================
module NumeralPresentation where

  open FiniteBase

  numeralω : ℕ → ⟪ ω ⟫
  numeralω k = fiber ω {x = # k} (#∈ω k) .fst

  numeralω-inj : (k k' : ℕ) → numeralω k ≡ numeralω k' → k ≡ k'
  numeralω-inj k k' e = #-inj′ (sym (fiber ω {x = # k} (#∈ω k) .snd)
    ∙ cong (⟪ ω ⟫↪) e ∙ fiber ω {x = # k'} (#∈ω k') .snd)

  isPropNumeralWit : (δ : S) → isProp (Σ[ n ∈ ℕ ] (# n ≡ δ))
  isPropNumeralWit δ (n , p) (n' , p') =
    Σ≡Prop (λ k → isSetS (# k) δ) (#-inj′ (p ∙ sym p'))

  to-wit : (m : ⟪ ω ⟫) → Σ[ n ∈ ℕ ] (# n ≡ ⟪ ω ⟫↪ m)
  to-wit m = PT.rec (isPropNumeralWit (⟪ ω ⟫↪ m)) hit
    (ω-mem→numeral (⟪ ω ⟫↪ m)
      (∈∈ₛ {a = ⟪ ω ⟫↪ m} {b = ω} .snd (∈ₛ⟪ ω ⟫↪ m)))
    where
    hit : Σ[ n ∈ ℕ ] (⟪ ω ⟫↪ m ≡ # n) → Σ[ n ∈ ℕ ] (# n ≡ ⟪ ω ⟫↪ m)
    hit (n , p) = n , sym p

  to : ⟪ ω ⟫ → ℕ
  to m = to-wit m .fst

  to∘numeralω : (k : ℕ) → to (numeralω k) ≡ k
  to∘numeralω k = #-inj′ (to-wit (numeralω k) .snd
    ∙ fiber ω {x = # k} (#∈ω k) .snd)

  numeralω∘to : (m : ⟪ ω ⟫) → numeralω (to m) ≡ m
  numeralω∘to m = cong fst (isEmbedding→hasPropFibers isEmb⟪ ω ⟫↪ (⟪ ω ⟫↪ m)
    (numeralω (to m) , fiber ω {x = # (to m)} (#∈ω (to m)) .snd ∙ to-wit m .snd)
    (m , refl))

  to-inj : (m n : ⟪ ω ⟫) → to m ≡ to n → m ≡ n
  to-inj m n e = sym (numeralω∘to m) ∙ cong numeralω e ∙ numeralω∘to n

  ω≃ℕ : ⟪ ω ⟫ ≃ ℕ
  ω≃ℕ = isoToEquiv (iso to numeralω to∘numeralω numeralω∘to)

  pairω : ⟪ ω ⟫ × ⟪ ω ⟫ → ⟪ ω ⟫
  pairω (m , n) = numeralω (Count.pair (to m) (to n))

  pairω-inj : (x y : ⟪ ω ⟫ × ⟪ ω ⟫) → pairω x ≡ pairω y → x ≡ y
  pairω-inj (m , n) (m' , n') e =
    ΣPathP ( to-inj m m' (fst (Count.pair-inj (to m) (to n) (to m') (to n') nm))
           , to-inj n n' (snd (Count.pair-inj (to m) (to n) (to m') (to n') nm)) )
    where
    nm : Count.pair (to m) (to n) ≡ Count.pair (to m') (to n')
    nm = numeralω-inj (Count.pair (to m) (to n)) (Count.pair (to m') (to n')) e

-- =====================================================================
-- PIECE 2, the generic half: the pullback well-order.
--
-- For an ordinal α and an injection of its presentation into ⟪ ω ⟫,
-- the image of the injection is the field of a well-order on a subset
-- of ω whose order type is α.  The order is the ∈-order on α pulled
-- back along the injection.  The order-type equality is the Unique
-- module of ProbeLJ192A plus the ordinal-self collapse of ProbeLJ194A.
-- The [LJ-1.94] Pullback (src/ProbeLJ194A.agda:937-1107) is this
-- module at α = κ; the successor closure instantiates it at the
-- successor of an order type.
-- =====================================================================
module PullbackAt (α : S) (oα : IsOrd α) (g : P194._↪_ ⟪ α ⟫ ⟪ ω ⟫) where

  open SmallWO
  module OS = OrdSWO α oα
  module OSα = OrdinalSelf α oα

  f : ⟪ α ⟫ → ⟪ ω ⟫
  f = g .fst

  f-inj : (x y : ⟪ α ⟫) → f x ≡ f y → x ≡ y
  f-inj = g .snd

  Q : ⟪ ω ⟫ → hProp ℓ
  Q m = (Σ[ k ∈ ⟪ α ⟫ ] (f k ≡ m)) , isPropQ m
    where
    isPropQ : (m : ⟪ ω ⟫) → isProp (Σ[ k ∈ ⟪ α ⟫ ] (f k ≡ m))
    isPropQ m (k , p) (k' , p') = Σ≡Prop {B = λ x → f x ≡ m}
      (λ x → isSet⟪⟫ ω (f x) m) (f-inj k k' (p ∙ sym p'))

  A' : Sub
  A' m = enc (Q m)

  P-body : ⟪ ω ⟫ → ⟪ ω ⟫ → Type ℓ
  P-body m n = Σ[ k ∈ ⟪ α ⟫ ] Σ[ k' ∈ ⟪ α ⟫ ]
    ((f k ≡ m) × ((f k' ≡ n) × ⟨ ⟪ α ⟫↪ k ∈ₛ ⟪ α ⟫↪ k' ⟩))

  P : ⟪ ω ⟫ → ⟪ ω ⟫ → hProp ℓ
  P m n = (P-body m n , isPropP m n)
    where
    isPropP : (m n : ⟪ ω ⟫)
            → isProp (Σ[ k ∈ ⟪ α ⟫ ] Σ[ k' ∈ ⟪ α ⟫ ]
              ((f k ≡ m) × ((f k' ≡ n) × ⟨ ⟪ α ⟫↪ k ∈ₛ ⟪ α ⟫↪ k' ⟩)))
    isPropP m n (k , w) (k' , w') =
      Σ≡Prop {B = λ x → Σ[ k₂ ∈ ⟪ α ⟫ ]
                ((f x ≡ m) × ((f k₂ ≡ n) × ⟨ ⟪ α ⟫↪ x ∈ₛ ⟪ α ⟫↪ k₂ ⟩))}
        (λ x → isPropRest x)
        (f-inj k k' (w .snd .fst ∙ sym (w' .snd .fst)))
      where
      isPropRest : (x : ⟪ α ⟫)
                 → isProp (Σ[ k₂ ∈ ⟪ α ⟫ ]
                     ((f x ≡ m) × ((f k₂ ≡ n) × ⟨ ⟪ α ⟫↪ x ∈ₛ ⟪ α ⟫↪ k₂ ⟩)))
      isPropRest x (k₂ , u) (k₂' , u') =
        Σ≡Prop {B = λ y → (f x ≡ m) × ((f y ≡ n) × ⟨ ⟪ α ⟫↪ x ∈ₛ ⟪ α ⟫↪ y ⟩)}
          (λ y → isProp× (isSet⟪⟫ ω (f x) m)
            (isProp× (isSet⟪⟫ ω (f y) n)
              (snd (⟪ α ⟫↪ x ∈ₛ ⟪ α ⟫↪ y))))
          (f-inj k₂ k₂' (u .snd .fst ∙ sym (u' .snd .fst)))

  R' : Rel
  R' m n = enc (P m n)

  irr' : Irr R'
  irr' m h = ∈-irrefl (⟪ α ⟫↪ k)
    (subst (λ z → ⟨ ⟪ α ⟫↪ k ∈ˢ z ⟩)
      (sym (cong (⟪ α ⟫↪) (f-inj k k' (p ∙ sym p'))))
      (∈∈ₛ {a = ⟪ α ⟫↪ k} {b = ⟪ α ⟫↪ k'} .snd h₁))
    where
    w = decEnc (P m m) h
    k : ⟪ α ⟫
    k = w .fst
    k' : ⟪ α ⟫
    k' = w .snd .fst
    p : f k ≡ m
    p = w .snd .snd .fst
    p' : f k' ≡ m
    p' = w .snd .snd .snd .fst
    h₁ : ⟨ ⟪ α ⟫↪ k ∈ₛ ⟪ α ⟫↪ k' ⟩
    h₁ = w .snd .snd .snd .snd

  trans' : Trans R'
  trans' m n k h h' =
    encDec (P m k) ( k₁ , k₃ , p₁ , p₃ , trans₁' h₁ h₂' )
    where
    w = decEnc (P m n) h
    w' = decEnc (P n k) h'
    k₁ : ⟪ α ⟫
    k₁ = w .fst
    k₂ : ⟪ α ⟫
    k₂ = w .snd .fst
    k₂' : ⟪ α ⟫
    k₂' = w' .fst
    k₃ : ⟪ α ⟫
    k₃ = w' .snd .fst
    p₁ : f k₁ ≡ m
    p₁ = w .snd .snd .fst
    p₂ : f k₂ ≡ n
    p₂ = w .snd .snd .snd .fst
    p₂' : f k₂' ≡ n
    p₂' = w' .snd .snd .fst
    p₃ : f k₃ ≡ k
    p₃ = w' .snd .snd .snd .fst
    h₁ : ⟨ ⟪ α ⟫↪ k₁ ∈ₛ ⟪ α ⟫↪ k₂ ⟩
    h₁ = w .snd .snd .snd .snd
    h₂ : ⟨ ⟪ α ⟫↪ k₂' ∈ₛ ⟪ α ⟫↪ k₃ ⟩
    h₂ = w' .snd .snd .snd .snd
    k₂≡k₂' : k₂ ≡ k₂'
    k₂≡k₂' = f-inj k₂ k₂' (p₂ ∙ sym p₂')
    h₂' : ⟨ ⟪ α ⟫↪ k₂ ∈ₛ ⟪ α ⟫↪ k₃ ⟩
    h₂' = subst (λ z → ⟨ ⟪ α ⟫↪ z ∈ₛ ⟪ α ⟫↪ k₃ ⟩) (sym k₂≡k₂') h₂
    trans₁' : ⟨ ⟪ α ⟫↪ k₁ ∈ₛ ⟪ α ⟫↪ k₂ ⟩
            → ⟨ ⟪ α ⟫↪ k₂ ∈ₛ ⟪ α ⟫↪ k₃ ⟩
            → ⟨ ⟪ α ⟫↪ k₁ ∈ₛ ⟪ α ⟫↪ k₃ ⟩
    trans₁' a b = ∈∈ₛ {a = ⟪ α ⟫↪ k₁} {b = ⟪ α ⟫↪ k₃} .fst
      (OS.trans₁ k₁ k₂ k₃
        (∈∈ₛ {a = ⟪ α ⟫↪ k₁} {b = ⟪ α ⟫↪ k₂} .snd a)
        (∈∈ₛ {a = ⟪ α ⟫↪ k₂} {b = ⟪ α ⟫↪ k₃} .snd b))

  wf' : Wf R'
  wf' m = acc (λ n h → step n h)
    where
    acc-map : (y : ⟪ α ⟫) → Acc OS._≺_ y → Acc (λ m n → ⟨ dec (R' m n) ⟩) (f y)
    acc-map y (acc rs) = acc (λ n h → step₂ n h)
      where
      step₂ : (n : ⟪ ω ⟫) → ⟨ dec (R' n (f y)) ⟩
            → Acc (λ m n → ⟨ dec (R' m n) ⟩) n
      step₂ n h = subst (λ z → Acc (λ m n → ⟨ dec (R' m n) ⟩) z)
        p₂ (acc-map k₂ (rs k₂ h₂'))
        where
        w = decEnc (P n (f y)) h
        k₂ : ⟪ α ⟫
        k₂ = w .fst
        k₃ : ⟪ α ⟫
        k₃ = w .snd .fst
        p₂ : f k₂ ≡ n
        p₂ = w .snd .snd .fst
        p₃ : f k₃ ≡ f y
        p₃ = w .snd .snd .snd .fst
        h₂ : ⟨ ⟪ α ⟫↪ k₂ ∈ₛ ⟪ α ⟫↪ k₃ ⟩
        h₂ = w .snd .snd .snd .snd
        h₂' : k₂ OS.≺ y
        h₂' = ∈∈ₛ {a = ⟪ α ⟫↪ k₂} {b = ⟪ α ⟫↪ y} .snd
          (subst (λ z → ⟨ ⟪ α ⟫↪ k₂ ∈ₛ ⟪ α ⟫↪ z ⟩) (f-inj k₃ y p₃) h₂)
    step : (n : ⟪ ω ⟫) → ⟨ dec (R' n m) ⟩ → Acc (λ m n → ⟨ dec (R' m n) ⟩) n
    step n h = subst (λ z → Acc (λ m n → ⟨ dec (R' m n) ⟩) z)
      p₂ (acc-map k₂ (OS.wf₁ k₂))
      where
      w = decEnc (P n m) h
      k₂ : ⟪ α ⟫
      k₂ = w .fst
      p₂ : f k₂ ≡ n
      p₂ = w .snd .snd .fst

  total' : Total A' R'
  total' m n a b = go (unwrap (OS.tri₁ k k'))
    where
    w = decEnc (Q m) a
    w' = decEnc (Q n) b
    k : ⟪ α ⟫
    k = w .fst
    k' : ⟪ α ⟫
    k' = w' .fst
    p : f k ≡ m
    p = w .snd
    p' : f k' ≡ n
    p' = w' .snd
    unwrap : (t : Tri (k OS.≺ k') (k ≡ k') (k' OS.≺ k))
           → (⟨ ⟪ α ⟫↪ k ∈ˢ ⟪ α ⟫↪ k' ⟩ ⊎ ((k ≡ k') ⊎ ⟨ ⟪ α ⟫↪ k' ∈ˢ ⟪ α ⟫↪ k ⟩))
    unwrap (lt h) = inl h
    unwrap (eq e) = inr (inl e)
    unwrap (gt h) = inr (inr h)
    go : (⟨ ⟪ α ⟫↪ k ∈ˢ ⟪ α ⟫↪ k' ⟩
          ⊎ ((k ≡ k') ⊎ ⟨ ⟪ α ⟫↪ k' ∈ˢ ⟪ α ⟫↪ k ⟩))
         → (⟨ dec (R' m n) ⟩ ⊎ ((m ≡ n) ⊎ ⟨ dec (R' n m) ⟩))
    go (inl h) = inl (encDec (P m n)
      (k , k' , p , p' , ∈∈ₛ {a = ⟪ α ⟫↪ k} {b = ⟪ α ⟫↪ k'} .fst h))
    go (inr (inl e)) = inr (inl
      (subst (λ z → z ≡ n) p (cong (f) e ∙ p')))
    go (inr (inr h)) = inr (inr (encDec (P n m)
      (k' , k , p' , p , ∈∈ₛ {a = ⟪ α ⟫↪ k'} {b = ⟪ α ⟫↪ k} .fst h)))

  wo' : WO
  wo' = A' , R' , irr' , trans' , wf' , total'

  module D' = Decode wo'
  module U' = Unique (car A') (⟪ α ⟫) (D'.swo) (OS.ordSWO)

  g-fwd : car A' → ⟪ α ⟫
  g-fwd (m , a) = decEnc (Q m) a .fst

  g-bwd : ⟪ α ⟫ → car A'
  g-bwd k = (f k , encDec (Q (f k)) (k , refl))

  opaque
    g-mono : {x y : car A'} → x D'.≺ y → g-fwd x OS.≺ g-fwd y
    g-mono {m , a} {n , b} (lift h) = go (decEnc (P m n) h)
      where
      go : Σ[ k ∈ ⟪ α ⟫ ] Σ[ k' ∈ ⟪ α ⟫ ]
             ((f k ≡ m) × ((f k' ≡ n) × ⟨ ⟪ α ⟫↪ k ∈ₛ ⟪ α ⟫↪ k' ⟩))
         → ⟨ ⟪ α ⟫↪ (g-fwd (m , a)) ∈ˢ ⟪ α ⟫↪ (g-fwd (n , b)) ⟩
      go (k , k' , p₁ , p₂ , h₀) =
        ∈∈ₛ {a = ⟪ α ⟫↪ (g-fwd (m , a))} {b = ⟪ α ⟫↪ (g-fwd (n , b))} .snd
          (subst (λ z → ⟨ ⟪ α ⟫↪ (g-fwd (m , a)) ∈ₛ ⟪ α ⟫↪ z ⟩) (k'≡g' k' p₂)
            (subst (λ z → ⟨ ⟪ α ⟫↪ z ∈ₛ ⟪ α ⟫↪ k' ⟩) (k≡g k p₁) h₀))
        where
        k≡g : (k : ⟪ α ⟫) → f k ≡ m → k ≡ g-fwd (m , a)
        k≡g k p = f-inj k (g-fwd (m , a)) (p ∙ sym (decEnc (Q m) a .snd))
        k'≡g' : (k' : ⟪ α ⟫) → f k' ≡ n → k' ≡ g-fwd (n , b)
        k'≡g' k' p = f-inj k' (g-fwd (n , b)) (p ∙ sym (decEnc (Q n) b .snd))

    g-mono-bwd : {x y : car A'} → g-fwd x OS.≺ g-fwd y → x D'.≺ y
    g-mono-bwd {m , a} {n , b} h = lift (encDec (P m n)
      ( g-fwd (m , a)
      , ( g-fwd (n , b)
        , ( decEnc (Q m) a .snd
          , ( decEnc (Q n) b .snd
            , ∈∈ₛ {a = ⟪ α ⟫↪ (g-fwd (m , a))} {b = ⟪ α ⟫↪ (g-fwd (n , b))} .fst h )))))

    g-surj : (y : ⟪ α ⟫) → ∥ Σ[ x ∈ car A' ] (g-fwd x ≡ y) ∥₁
    g-surj y = ∣ g-bwd y , cong fst rt ∣₁
      where
      rt : decEnc (Q (f y)) (encDec (Q (f y)) (y , refl)) ≡ (y , refl)
      rt = transportTransport⁻ (cong ⟨_⟩ (dec∘enc (Q (f y)))) (y , refl)

  iso' : U'.OrderIso
  iso' = record
    { f          = g-fwd
    ; f-mono     = g-mono
    ; f-mono-bwd = g-mono-bwd
    ; f-surj     = g-surj }

  module UU' = U'.Uniq iso'

  ot'≡α : ot wo' ≡ α
  ot'≡α = UU'.τ-eq ∙ OSα.ot-self

-- =====================================================================
-- PIECE 2, the countability of a successor.
--
-- The presentation of sucV A splits into the presentation of A plus
-- the top element A itself.  The split is a proposition: a set never
-- equals one of its own members (∈-irrefl).  Then, for a well-order
-- wo with order type γ, the successor's presentation injects into
-- ⟪ ω ⟫:  the member part embeds by the countability of wo shifted
-- past zero, and the top maps to the numeral zero.
-- =====================================================================
module SucPresentation (A : S) where

  Split : (v : S) → Type (ℓ-suc ℓ)
  Split v = (Σ[ u ∈ ⟪ A ⟫ ] (⟪ A ⟫↪ u ≡ v)) ⊎ (v ≡ A)

  disj : (v : S) → (Σ[ u ∈ ⟪ A ⟫ ] (⟪ A ⟫↪ u ≡ v)) → (v ≡ A) → Empty.⊥
  disj v (u , p) q = ∈-irrefl A
    (∈∈ₛ {a = A} {b = A} .snd
      (subst (λ w → ⟨ w ∈ₛ A ⟩) (p ∙ q) (∈ₛ⟪ A ⟫↪ u)))

  isPropSplit : (v : S) → isProp (Split v)
  isPropSplit v = isProp⊎
    (isEmbedding→hasPropFibers isEmb⟪ A ⟫↪ v)
    (isSetS v A)
    (disj v)

  toSplit : (m : ⟪ sucV A ⟫) → Split (⟪ sucV A ⟫↪ m)
  toSplit m = ∈sucV-elim {A = A} {x = ⟪ sucV A ⟫↪ m} (isPropSplit (⟪ sucV A ⟫↪ m))
    (∈∈ₛ {a = ⟪ sucV A ⟫↪ m} {b = sucV A} .snd (∈ₛ⟪ sucV A ⟫↪ m))
    (λ v∈A → inl (fiber A {x = ⟪ sucV A ⟫↪ m} v∈A))
    (λ v≡A → inr v≡A)

  to : ⟪ sucV A ⟫ → ⟪ A ⟫ ⊎ Unit
  to m = go (toSplit m)
    where
    go : Split (⟪ sucV A ⟫↪ m) → ⟪ A ⟫ ⊎ Unit
    go (inl (u , _)) = inl u
    go (inr _) = inr tt

-- =====================================================================
-- PIECE 2, the instantiation: the successor closure of κ.
--
-- For wo with ot wo = γ, the successor sucV γ is an order type on a
-- subset of ω:  the successor's presentation injects into ⟪ ω ⟫ by
-- SuccCount, and PullbackAt turns that injection into a well-order
-- whose order type is the successor.  This module is one
-- instantiation of the generic half.
-- =====================================================================
module SuccCount (wo : SmallWO.WO) where

  open SmallWO
  module O = OT wo
  module SP = SucPresentation (O.τ)

  γ : S
  γ = O.τ

  countγ : P194._↪_ ⟪ γ ⟫ ⟪ ω ⟫
  countγ = P194.Count.count wo

  shift : ⟪ ω ⟫ → ⟪ ω ⟫
  shift m = NumeralPresentation.numeralω (suc (NumeralPresentation.to m))

  shift-inj : (m n : ⟪ ω ⟫) → shift m ≡ shift n → m ≡ n
  shift-inj m n e = NumeralPresentation.to-inj m n
    (injSuc (NumeralPresentation.numeralω-inj
      (suc (NumeralPresentation.to m)) (suc (NumeralPresentation.to n)) e))

  shift-ne : (m : ⟪ ω ⟫) → (shift m ≡ NumeralPresentation.numeralω 0) → Empty.⊥
  shift-ne m e = znots
    (sym (NumeralPresentation.numeralω-inj
      (suc (NumeralPresentation.to m)) 0 e))

  emb' : (m : ⟪ sucV γ ⟫) → SP.Split (⟪ sucV γ ⟫↪ m) → ⟪ ω ⟫
  emb' m (inl (u , _)) = shift (countγ .fst u)
  emb' m (inr _) = NumeralPresentation.numeralω 0

  emb : ⟪ sucV γ ⟫ → ⟪ ω ⟫
  emb m = emb' m (SP.toSplit m)

  emb'-inl : (m : ⟪ sucV γ ⟫) (u : ⟪ γ ⟫)
           → (⟪ γ ⟫↪ u ≡ ⟪ sucV γ ⟫↪ m)
           → (s : SP.Split (⟪ sucV γ ⟫↪ m))
           → emb' m s ≡ shift (countγ .fst u)
  emb'-inl m u p (inl (u' , p')) = cong (λ w → shift (countγ .fst w)) u≡u'
    where
    u≡u' : u' ≡ u
    u≡u' = cong fst (isEmbedding→hasPropFibers isEmb⟪ γ ⟫↪ (⟪ γ ⟫↪ u)
      (u' , p' ∙ sym p) (u , refl))
  emb'-inl m u p (inr q) = Empty.rec (∈-irrefl γ
    (∈∈ₛ {a = γ} {b = γ} .snd
      (subst (λ w → ⟨ w ∈ₛ γ ⟩) (p ∙ q) (∈ₛ⟪ γ ⟫↪ u))))

  emb-inl : (m : ⟪ sucV γ ⟫) (u : ⟪ γ ⟫)
          → (⟪ γ ⟫↪ u ≡ ⟪ sucV γ ⟫↪ m) → emb m ≡ shift (countγ .fst u)
  emb-inl m u p = emb'-inl m u p (SP.toSplit m)

  emb'-top : (m : ⟪ sucV γ ⟫) (q : ⟪ sucV γ ⟫↪ m ≡ γ)
           → (s : SP.Split (⟪ sucV γ ⟫↪ m))
           → emb' m s ≡ NumeralPresentation.numeralω 0
  emb'-top m q (inl (u , p)) = Empty.rec (∈-irrefl γ
    (∈∈ₛ {a = γ} {b = γ} .snd
      (subst (λ w → ⟨ w ∈ₛ γ ⟩) (p ∙ q) (∈ₛ⟪ γ ⟫↪ u))))
  emb'-top m q (inr _) = refl

  emb-top : (m : ⟪ sucV γ ⟫) (q : ⟪ sucV γ ⟫↪ m ≡ γ)
          → emb m ≡ NumeralPresentation.numeralω 0
  emb-top m q = emb'-top m q (SP.toSplit m)

  emb-inj : (m n : ⟪ sucV γ ⟫) → emb m ≡ emb n → m ≡ n
  emb-inj m n e = go (SP.toSplit m) (SP.toSplit n) e
    where
    fiber-eq : (a b : ⟪ sucV γ ⟫)
             → (⟪ sucV γ ⟫↪ a ≡ ⟪ sucV γ ⟫↪ b) → a ≡ b
    fiber-eq a b p = cong fst
      (isEmbedding→hasPropFibers isEmb⟪ sucV γ ⟫↪ (⟪ sucV γ ⟫↪ a)
        (a , refl) (b , sym p))
    go : SP.Split (⟪ sucV γ ⟫↪ m) → SP.Split (⟪ sucV γ ⟫↪ n)
       → emb m ≡ emb n → m ≡ n
    go (inl (u , p)) (inl (u' , p')) e =
      fiber-eq m n
        (sym p ∙ cong (⟪ γ ⟫↪) (countγ .snd u u'
          (shift-inj (countγ .fst u) (countγ .fst u')
            (sym (emb-inl m u p) ∙ e ∙ emb-inl n u' p'))) ∙ p')
    go (inl (u , p)) (inr q) e =
      Empty.rec (shift-ne (countγ .fst u)
        (sym (emb-inl m u p) ∙ e ∙ emb-top n q))
    go (inr q) (inl (u' , p')) e =
      Empty.rec (shift-ne (countγ .fst u')
        (sym (emb-inl n u' p') ∙ sym e ∙ emb-top m q))
    go (inr q) (inr q') e = fiber-eq m n (q ∙ sym q')

  succ-inj : P194._↪_ ⟪ sucV γ ⟫ ⟪ ω ⟫
  succ-inj = emb , emb-inj

module SuccClosure where

  open SmallWO

  succWO : (wo : WO) → Σ[ wo' ∈ WO ] (ot wo' ≡ sucV (ot wo))
  succWO wo = PB.wo' , PB.ot'≡α
    where
    module O = OT wo
    module SC = SuccCount wo
    δ : S
    δ = sucV (O.τ)
    ordδ : IsOrd δ
    ordδ = suc-ord (ot-ord wo)
    module PB = PullbackAt δ ordδ SC.succ-inj

  succκ : (γ : S) → ⟨ γ ∈ˢ Hartogs.κ ⟩ → ⟨ sucV γ ∈ˢ Hartogs.κ ⟩
  succκ γ γ∈κ = PT.rec (snd (sucV γ ∈ˢ Hartogs.κ)) go (Hartogs.κ-mem γ γ∈κ)
    where
    go : Σ[ wo ∈ WO ] (ot wo ≡ γ) → ⟨ sucV γ ∈ˢ Hartogs.κ ⟩
    go (wo , e) = ∣ succWO wo .fst , succWO wo .snd ∙ cong sucV e ∣₁

-- =====================================================================
-- THE ASSEMBLY: Init SiteAt.κ with no hypothesis left.
--
-- The square clause is the [LJ-1.101] bridge
-- (src/ProbeLJ1101A.agda:78-103), restated here because the original
-- probe imports L.BoundedSubset, which imports the sibling's open
-- file L.Condensation (src/L/BoundedSubset.lagda.md:29).  The restated
-- content is the same delivered bridge with both hypotheses supplied.
-- =====================================================================
module InitBridge
  (pairω : ⟪ ω ⟫ × ⟪ ω ⟫ → ⟪ ω ⟫)
  (pairω-inj : (m n : ⟪ ω ⟫ × ⟪ ω ⟫) → pairω m ≡ pairω n → m ≡ n)
  where

  square-clause : (β : S) → IsOrd β → ⟨ β ∈ˢ SiteAt.κ ⟩ → ⟨ ω ∈ˢ β ⟩
                → (f : ⟪ SiteAt.κ ⟫ → ⟪ β ⟫ × ⟪ β ⟫)
                → ((m n : ⟪ SiteAt.κ ⟫) → f m ≡ f n → m ≡ n) → Empty.⊥
  square-clause β oβ β∈κ ω∈β f f-inj =
    PT.rec Empty.isProp⊥ go (P194.Hartogs.κ-mem β β∈κ)
    where
    go : Σ[ wo ∈ P194.SmallWO.WO ] (P194.SmallWO.ot wo ≡ β) → Empty.⊥
    go (wo , e) = P194.Hartogs.cardκ ω SiteAt.α∈κ g
      where
      i : (P194._↪_) ⟪ β ⟫ ⟪ ω ⟫
      i = P194.countAt wo β e
      g0 : ⟪ SiteAt.κ ⟫ → ⟪ ω ⟫
      g0 m = pairω (i .fst (fst (f m)) , i .fst (snd (f m)))
      g-inj : (m n : ⟪ SiteAt.κ ⟫) → g0 m ≡ g0 n → m ≡ n
      g-inj m n h = f-inj m n (ΣPathP (i .snd (fst (f m)) (fst (f n)) (cong fst h')
                                    , i .snd (snd (f m)) (snd (f n)) (cong snd h')))
        where
        h' : (i .fst (fst (f m)) , i .fst (snd (f m)))
           ≡ (i .fst (fst (f n)) , i .fst (snd (f n)))
        h' = pairω-inj (i .fst (fst (f m)) , i .fst (snd (f m)))
                       (i .fst (fst (f n)) , i .fst (snd (f n))) h
      g : (P194._↪_) ⟪ SiteAt.κ ⟫ ⟪ ω ⟫
      g = g0 , g-inj

module InitAtSiteFull where

  module B = InitBridge NumeralPresentation.pairω NumeralPresentation.pairω-inj

  initκ : SQ.Init SiteAt.κ
  initκ = SiteAt.ordκ , SiteAt.α∈κ , SuccClosure.succκ , B.square-clause

  -- the delivered consumer (src/L/Ordinal/SquareLaw.lagda.md:960-961)
  -- now receives a value at κ.
  sqκ : SQ.sq SiteAt.κ
  sqκ = SQ.via-col-square SiteAt.κ initκ
