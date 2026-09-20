{-# OPTIONS --cubical --safe --guardedness #-}

-- K2 Track I, second file: the three acceptance instances against the host
-- regular-open algebra of Track C.
--
-- Instances.agda says what each presentation does to ANY completion map
-- satisfying the kernel law. This file says what Track C's actual completion
-- does to them, and states the theorems Track C's own sanity file did not:
-- the exact size of the algebra, the image of each condition in it, failure of
-- order reflection for the module's own Boolean order, and the concrete
-- collapse on the K0 four-condition example that shows the antisymmetry
-- hypothesis of i-injective is not droppable.
--
-- Nothing here re-derives Track C. HostRegularOpen is applied to the fields of
-- an Instances notion, which is the entry point REPORT-C section 7 names, with
-- the transitivity field's three implicit arguments bound by a lambda as that
-- report measured to be necessary.
--
-- LEM ℓ appears as the first explicit argument of exactly one theorem per
-- instance, the two-element classification, and nowhere else. Every other
-- result below is constructive.

open import Base.Prelude
open import Base.Truth

module InstancesCompletion {ℓ : Level} where

open import Base.Classical using ( LEM )
open import Cubical.Data.Sum using ( _⊎_; inl; inr )
open import Cubical.Data.Unit using ( tt*; isSetUnit* )
import Cubical.Data.Empty as Empty
import Instances
import HostRegularOpen

open TruthAlgebra (hPropAlgebra ℓ)

--------------------------------------------------------------------------------
-- 0. Presentations with a least condition
--------------------------------------------------------------------------------

-- Instances 1 and 3 both have a condition below every condition, and that one
-- fact settles their whole algebra: the pseudocomplement of anything is
-- decided at the least condition. The argument is written once here and used
-- twice.

module Bottomed (Cond : Type ℓ) (isSetC : isSet Cond)
  (_≼_ : Cond → Cond → Ω)
  (≼-refl : (p : Cond) → ⟨ p ≼ p ⟩)
  (≼-trans : {p q r : Cond} → ⟨ p ≼ q ⟩ → ⟨ q ≼ r ⟩ → ⟨ p ≼ r ⟩)
  (bot : Cond) (bot-least : (p : Cond) → ⟨ bot ≼ p ⟩) where

  module R = HostRegularOpen Cond isSetC _≼_ ≼-refl
               (λ {p} {q} {r} → ≼-trans {p} {q} {r})

  -- Every condition lands on the top of the algebra, because the cone of any
  -- condition contains the least condition, and so no condition at all lies in
  -- the pseudocomplement of that cone.

  i-top : (p : Cond) → R.i p ≡ R.⊤ᴮ
  i-top p = R.Reg≡ (R.i p) R.⊤ᴮ (λ q _ → tt*)
    (λ q _ r r≼q y → y bot (bot-least r) (bot-least p))

  -- The algebra has exactly two elements. This is where LEM is spent, and the
  -- reason is visible: a regular subset is determined by its truth value at
  -- the least condition, and only excluded middle turns that truth value into
  -- one of two cases.

  two-valued : LEM ℓ → (U : R.Reg) → (U ≡ R.⊥ᴮ) ⊎ (U ≡ R.⊤ᴮ)
  two-valued lem U = decide (lem (fst U bot))
    where
    decide : ⟨ fst U bot ⟩ ⊎ (⟨ fst U bot ⟩ → Empty.⊥)
           → (U ≡ R.⊥ᴮ) ⊎ (U ≡ R.⊤ᴮ)
    decide (inl h) = inr (R.Reg≡ U R.⊤ᴮ (λ q _ → tt*)
      (λ q _ → R.regular-⊒ (fst U) (snd U) q
                 (λ r r≼q y → y bot (bot-least r) h)))
    decide (inr nh) = inl (R.Reg≡ U R.⊥ᴮ
      (λ q hq → Empty.rec (nh (R.regDown U q bot (bot-least q) hq)))
      (λ q x → Empty.rec* x))

  -- And the two are distinct, so the algebra is exactly two-valued and not
  -- one-valued.

  nondegenerate : R.⊥ᴮ ≡ R.⊤ᴮ → ⟨ ⊥ ⟩
  nondegenerate e = R.Reg⊑ R.⊤ᴮ R.⊥ᴮ (sym e) bot tt*

--------------------------------------------------------------------------------
-- 1. The non-refined presentation
--------------------------------------------------------------------------------

module NR = Instances.NonRefined {ℓ}

module NRB = Bottomed NR.Two NR.isSetTwo NR.ord NR.ord-refl
               (λ {p} {q} {r} → NR.ord-trans {p} {q} {r})
               NR.low NR.low-below

module RO = NRB.R

-- Track C's kernel law is the weak one, so this is the module Instances.agda
-- built for it. Everything below RO.i is a theorem about the real completion.

module NRC = NR.AnyCompletionWeak RO.Reg RO.i RO.i-kernel←

-- The algebra of the two-condition non-refined poset.

RO-two-valued : LEM ℓ → (U : RO.Reg) → (U ≡ RO.⊥ᴮ) ⊎ (U ≡ RO.⊤ᴮ)
RO-two-valued = NRB.two-valued

RO-nondegenerate : RO.⊥ᴮ ≡ RO.⊤ᴮ → ⟨ ⊥ ⟩
RO-nondegenerate = NRB.nondegenerate

-- Both conditions map to the top, so the embedding is not injective, at a pair
-- that is not order equivalent: NR.not-above says one does not refine low.

i-one-top : RO.i NR.one ≡ RO.⊤ᴮ
i-one-top = NRB.i-top NR.one

i-low-top : RO.i NR.low ≡ RO.⊤ᴮ
i-low-top = NRB.i-top NR.low

i-collapses : RO.i NR.one ≡ RO.i NR.low
i-collapses = NRC.i-collapses

i-not-injective : (RO.i NR.one ≡ RO.i NR.low) × ((NR.one ≡ NR.low) → ⟨ ⊥ ⟩)
i-not-injective = NRC.i-not-injective

-- Order reflection fails for the module's own Boolean order. So Track C's
-- separative→reflect cannot drop its separativity hypothesis: this
-- presentation is a partial order, and is the pair of theorems
-- NR.antisym and NR.not-separative away from satisfying it.

no-order-reflection :
  ({p q : NR.Two} → RO.i q RO.≤ᴮ RO.i p → ⟨ NR.ord q p ⟩) → ⟨ ⊥ ⟩
no-order-reflection =
  NRC.no-order-reflection RO._≤ᴮ_ (λ U → RO.≤ᴮ-from U U (λ q x → x))

-- The full statement of instance 1, in the algebra rather than under a
-- hypothesis: a two-element algebra, two conditions at its top, one strictly
-- below the other, and the presentation a partial order throughout.

instance-1 : LEM ℓ
  → (((U : RO.Reg) → (U ≡ RO.⊥ᴮ) ⊎ (U ≡ RO.⊤ᴮ)) × ((RO.⊥ᴮ ≡ RO.⊤ᴮ) → ⟨ ⊥ ⟩))
  × (((RO.i NR.one ≡ RO.⊤ᴮ) × (RO.i NR.low ≡ RO.⊤ᴮ))
      × (NR.antisymmetric × ((NR.separative → ⟨ ⊥ ⟩) × (⟨ NR.ord NR.one NR.low ⟩ → ⟨ ⊥ ⟩))))
instance-1 lem =
    (RO-two-valued lem , RO-nondegenerate)
  , ((i-one-top , i-low-top)
  , (NR.antisym , NR.not-separative , NR.not-above))

--------------------------------------------------------------------------------
-- 2. The K0 four-condition example
--------------------------------------------------------------------------------

module K4 = Instances.K0Four {ℓ}

module RO4 = HostRegularOpen K4.Four K4.isSetFour K4.ord K4.ord-refl
               (λ {p} {q} {r} → K4.ord-trans {p} {q} {r})

module K4C = K4.AnyCompletionWeak RO4.Reg RO4.i RO4.i-kernel←

-- The real completion identifies the two left conditions, which are distinct.
-- Since this presentation IS separative, the separativity hypothesis of Track
-- C's i-injective cannot be the only one: antisymmetry is doing work.

k0-i-collapses : RO4.i K4.k-left₀ ≡ RO4.i K4.k-left₁
k0-i-collapses = K4C.i-collapses

k0-antisymmetry-is-needed :
  K4.separative
  × ((RO4.i K4.k-left₀ ≡ RO4.i K4.k-left₁) × ((K4.k-left₀ ≡ K4.k-left₁) → ⟨ ⊥ ⟩))
k0-antisymmetry-is-needed = K4C.separativity-is-not-enough

-- Unlike instance 1, here the collapsed pair IS order equivalent, which is
-- exactly why this example cannot serve as the non-refined witness.

k0-collapsed-pair-is-order-equivalent :
  ⟨ K4.ord K4.k-left₀ K4.k-left₁ ⟩ × ⟨ K4.ord K4.k-left₁ K4.k-left₀ ⟩
k0-collapsed-pair-is-order-equivalent = K4.left₀≼left₁ , K4.left₁≼left₀

--------------------------------------------------------------------------------
-- 3. Trivial forcing
--------------------------------------------------------------------------------

module TR = Instances.Trivial {ℓ}

module TRB = Bottomed TR.Point isSetUnit* TR.ord (λ _ → tt*)
               (λ {_} {_} {_} _ _ → tt*) tt* (λ _ → tt*)

module ROT = TRB.R

module TRC = TR.AnyCompletion ROT.Reg ROT.i

trivial-two-valued : LEM ℓ → (U : ROT.Reg) → (U ≡ ROT.⊥ᴮ) ⊎ (U ≡ ROT.⊤ᴮ)
trivial-two-valued = TRB.two-valued

trivial-nondegenerate : ROT.⊥ᴮ ≡ ROT.⊤ᴮ → ⟨ ⊥ ⟩
trivial-nondegenerate = TRB.nondegenerate

trivial-i-constant : (p q : TR.Point) → ROT.i p ≡ ROT.i q
trivial-i-constant = TRC.i-constant

trivial-i-top : (p : TR.Point) → ROT.i p ≡ ROT.⊤ᴮ
trivial-i-top = TRB.i-top

-- Trivial forcing, preserved: two elements in the algebra, the embedding
-- constant, and the presentation still a separative partial order.

instance-3 : LEM ℓ
  → (((U : ROT.Reg) → (U ≡ ROT.⊥ᴮ) ⊎ (U ≡ ROT.⊤ᴮ)) × ((ROT.⊥ᴮ ≡ ROT.⊤ᴮ) → ⟨ ⊥ ⟩))
  × (((p q : TR.Point) → ROT.i p ≡ ROT.i q) × (TR.separative × TR.antisymmetric))
instance-3 lem =
    (trivial-two-valued lem , trivial-nondegenerate)
  , (trivial-i-constant , (TR.sep , TR.antisym))
