{-# OPTIONS --cubical --safe --guardedness #-}

-- K5 Track J, file 2: the designer's proposed refuting notion, and why it is
-- not one.
--
-- One designer proposed a TWO ELEMENT ANTICHAIN as the negative control that
-- refutes the naive disjunction clause. The architecture corrected this at its
-- part 6.6 and T-J1. This file settles the correction by proof rather than by
-- assertion: at the two element antichain BOTH naive clauses HOLD, so no
-- instantiation of that notion can refute either of them.
--
-- The mechanism, and it is the whole content of the correction: in this poset
-- the only refinement of a condition is that condition itself, so the
-- pseudocomplement of a subset at p is just "p is not in it", and the double
-- pseudocomplement of a union is, at p, the double negation of "p is in one of
-- the two". Excluded middle strips the double negation and hands back a
-- disjunct. In the three element V of K5/RefutedClauses.agda the top has two
-- PROPER refinements, the double negation cannot be stripped at the top
-- because the witnesses live strictly below it, and the clause fails.
--
-- LEM ℓ is an explicit first argument of the two theorems that spend it and
-- appears nowhere else. It is genuinely spent: this file proves the naive
-- clauses, and the double negation above is not removable without it.

open import Base.Prelude
open import Base.Truth

module K5.AntichainControl {ℓ : Level} where

open import Base.Classical using ( LEM )
open import Cubical.Data.Bool using ( Bool; true; false; isSetBool )
open import Cubical.Data.Sum using ( _⊎_; inl; inr )
open import Cubical.Data.Unit using ( tt* )
open import Cubical.Foundations.HLevels using ( isOfHLevelRetract )
import Cubical.Data.Empty as Empty
import Cubical.Functions.Logic as Logic
import Cubical.HITs.PropositionalTruncation as PT
open PT using ( ∥_∥₁; ∣_∣₁ )

import HostRegularOpen

open TruthAlgebra (hPropAlgebra ℓ)

--------------------------------------------------------------------------------
-- 1. The two element antichain
--------------------------------------------------------------------------------

data A2 : Type ℓ where
  pa pb : A2

bit : A2 → Bool
bit pa = true
bit pb = false

unbit : Bool → A2
unbit true  = pa
unbit false = pb

bit-retract : (p : A2) → unbit (bit p) ≡ p
bit-retract pa = refl
bit-retract pb = refl

isSetA2 : isSet A2
isSetA2 = isOfHLevelRetract 2 bit unbit bit-retract isSetBool

ord2 : A2 → A2 → Ω
ord2 pa pa = ⊤
ord2 pa pb = ⊥
ord2 pb pa = ⊥
ord2 pb pb = ⊤

ord2-refl : (p : A2) → ⟨ ord2 p p ⟩
ord2-refl pa = tt*
ord2-refl pb = tt*

ord2-trans : {p q r : A2} → ⟨ ord2 p q ⟩ → ⟨ ord2 q r ⟩ → ⟨ ord2 p r ⟩
ord2-trans {pa} {pa} {pa} _  _  = tt*
ord2-trans {pa} {pa} {pb} _  h₂ = Empty.rec* h₂
ord2-trans {pa} {pb} {_}  h₁ _  = Empty.rec* h₁
ord2-trans {pb} {pa} {_}  h₁ _  = Empty.rec* h₁
ord2-trans {pb} {pb} {pa} _  h₂ = Empty.rec* h₂
ord2-trans {pb} {pb} {pb} _  _  = tt*

--------------------------------------------------------------------------------
-- 2. The algebra, and the one fact that makes this notion harmless
--------------------------------------------------------------------------------

module R2 = HostRegularOpen A2 isSetA2 ord2 ord2-refl
              (λ {p} {q} {r} → ord2-trans {p} {q} {r})

open R2 using ( Sub; Reg; _⊑_; isProp⊑; _⋆; _∪_; ⋃; _⊔ᴮ_; ⋁ᴮ )

_⊩²_ : A2 → Reg → Ω
p ⊩² U = (fst (R2.i p) ⊑ fst U) , isProp⊑ (fst (R2.i p)) (fst U)

-- THE FACT. The only refinement of a condition is itself, so a condition lies
-- in the pseudocomplement of U as soon as it is not in U. This is what the
-- three element V denies: there, vtop is not in the pseudocomplement of the
-- union of the two atoms even though vtop is in neither atom's image.

⋆-at : (p : A2) (U : Sub) → (⟨ U p ⟩ → ⟨ ⊥ ⟩) → ⟨ (U ⋆) p ⟩
⋆-at pa U n pa _ u = n u
⋆-at pa U n pb h u = Empty.rec* h
⋆-at pb U n pa h u = Empty.rec* h
⋆-at pb U n pb _ u = n u

--------------------------------------------------------------------------------
-- 3. The naive disjunction clause HOLDS at the antichain
--------------------------------------------------------------------------------

NaiveDisjunctionA2 : Type (ℓ-suc ℓ)
NaiveDisjunctionA2 = (p : A2) (U V : Reg)
                   → ⟨ p ⊩² (U ⊔ᴮ V) ⟩ → ⟨ (p ⊩² U) ⊔ (p ⊩² V) ⟩

antichain-naive-disjunction : LEM ℓ → NaiveDisjunctionA2
antichain-naive-disjunction lem p U V h = go (lem ((fst U p) ⊔ (fst V p)))
  where
  goal : Ω
  goal = (p ⊩² U) ⊔ (p ⊩² V)

  branch : ⟨ fst U p ⟩ ⊎ ⟨ fst V p ⟩ → ⟨ goal ⟩
  branch (inl x) = Logic.inl (R2.i-below p U x)
  branch (inr y) = Logic.inr (R2.i-below p V y)

  go : ⟨ (fst U p) ⊔ (fst V p) ⟩ ⊎ (⟨ (fst U p) ⊔ (fst V p) ⟩ → Empty.⊥)
     → ⟨ goal ⟩
  go (inl z) = PT.rec (snd goal) branch z
  go (inr n) = Empty.rec*
    (h p (R2.i-self p) p (ord2-refl p)
       (⋆-at p ((fst U) ∪ (fst V)) (λ z → Empty.rec (n z))))

--------------------------------------------------------------------------------
-- 4. The naive existential clause HOLDS at the antichain too
--------------------------------------------------------------------------------

NaiveExistentialA2 : Type (ℓ-suc ℓ)
NaiveExistentialA2 = (p : A2) (A : Type ℓ) (f : A → Reg)
                   → ⟨ p ⊩² (⋁ᴮ A f) ⟩ → ⟨ ⋁ A (λ a → p ⊩² f a) ⟩

antichain-naive-existential : LEM ℓ → NaiveExistentialA2
antichain-naive-existential lem p A f h = go (lem (⋁ A (λ a → fst (f a) p)))
  where
  goal : Ω
  goal = ⋁ A (λ a → p ⊩² f a)

  branch : Σ[ a ∈ A ] ⟨ fst (f a) p ⟩ → Σ[ a ∈ A ] ⟨ p ⊩² f a ⟩
  branch (a , x) = a , R2.i-below p (f a) x

  go : ⟨ ⋁ A (λ a → fst (f a) p) ⟩ ⊎ (⟨ ⋁ A (λ a → fst (f a) p) ⟩ → Empty.⊥)
     → ⟨ goal ⟩
  go (inl z) = PT.map branch z
  go (inr n) = Empty.rec*
    (h p (R2.i-self p) p (ord2-refl p)
       (⋆-at p (⋃ A (λ a → fst (f a))) (λ z → Empty.rec (n z))))

--------------------------------------------------------------------------------
-- 5. The correction, as one statement
--------------------------------------------------------------------------------

-- Both naive clauses hold at the two element antichain, so that notion refutes
-- neither of them and the designer's proposed negative control is not one.
-- The refuting notion is the three element V, and it is built and used in
-- K5/RefutedClauses.agda.

antichain-refutes-nothing : LEM ℓ → NaiveDisjunctionA2 × NaiveExistentialA2
antichain-refutes-nothing lem =
  antichain-naive-disjunction lem , antichain-naive-existential lem
