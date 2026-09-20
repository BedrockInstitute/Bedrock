{-# OPTIONS --cubical --safe --guardedness #-}

-- K2 Track I: acceptance instances for the host structural layer.
--
-- Three presentations, each with the theorems that say what it witnesses. An
-- inhabitant of ForcingNotion witnesses nothing by itself; the content of this
-- file is the named theorems beside each instance.
--
--  1. NonRefined. Two conditions, one strictly below the other, both pairwise
--     compatible. It is a partial order (antisym), so the failure is a failure
--     of Bell's refinement condition and not an artefact of the preorder
--     (not-separative). The two conditions are separatively equal while being
--     neither equal nor order equivalent, so the kernel of any completion map
--     fires at a pair no order relation identifies, and order reflection fails
--     for every completion. This is the witness that roadmap:251 and
--     geology:204 ask for and that the tree did not have.
--
--  2. K0Four. The four-condition example of
--     dev/literature/k0-probe-evidence-2026-09.md:455-635, relabelled. Its
--     file name there, NonseparativeCompletion.agda, is the source of a
--     standing error: the example is SEPARATIVE (sep) and fails ANTISYMMETRY
--     (not-antisymmetric), exactly as architecture section 5, N5 records. Its
--     compatibility relation is re-expressed through the truncated form of
--     Track A; the untruncated sigma form is not a truth value, and
--     Sigma-form-not-prop proves that it is not, at this very instance.
--
--  3. Trivial. One condition. Every completion map out of it is constant. It
--     also carries a filter that is host generic (atomless-not-removable),
--     which shows that the atomlessness hypothesis of Track A's
--     no-host-generic cannot be dropped.
--
-- Hypotheses: none. No LEM anywhere in this file, at any level, and no module
-- takes a structure, a model or a ground. Every theorem below is constructive.
--
-- Track C is NOT imported. Everything this file says about a completion map is
-- said through an explicit module parameter (AnyCompletion), so the statements
-- hold for any map satisfying the kernel law and do not wait on, or break
-- with, the regular-open construction. The kernel law is taken in the
-- separativelyEqual form, which is the weaker demand: a module delivering it
-- in the weaklyEqual form supplies this one by composing with
-- separativelyEqual-to-weaklyEqual below.
--
-- Notation rules of K2 section 1.0 are respected: _∈ᶜ_ never appears, every
-- negation is _ ⇒ ⊥ with the algebra's own bottom, and compatibility inside
-- any ⋀ or ⋁ is the truncated ⋁-form.

open import Base.Prelude
open import Base.Truth

module Instances {ℓ : Level} where

open import ForcingNotion using ( ForcingNotion; module Structure )

open import Cubical.Data.Bool using ( Bool; true; false; isSetBool; true≢false; false≢true )
open import Cubical.Data.Unit using ( Unit*; tt*; isSetUnit* )
open import Cubical.Foundations.HLevels using ( isOfHLevelRetract; isSet× )
import Cubical.Data.Empty as Empty
import Cubical.HITs.PropositionalTruncation as PT
open PT using ( ∥_∥₁; ∣_∣₁ )

open TruthAlgebra (hPropAlgebra ℓ)

--------------------------------------------------------------------------------
-- 0. Two kernel forms, and the passage between them
--------------------------------------------------------------------------------

-- The architecture states the kernel law of a completion map with Bell's
-- separative equality (Problem 2.4(i), fulltext:3538-3539). Track C measured
-- that the constructive kernel is the incompatibility form instead, and calls
-- it weaklyEqual. The implication that always holds is recorded here, so that
-- an instance proved for the compatibility form can feed a law stated for
-- either one.

module KernelForms (𝔓 : ForcingNotion {ℓ}) where
  open Structure 𝔓

  weaklyEqual : Cond → Cond → Ω
  weaklyEqual p q = ⋀ Cond (λ r →
    (incompatible r p ⇒ incompatible r q) ⊓ (incompatible r q ⇒ incompatible r p))

  -- Order equivalent conditions are separatively equal. This is the only
  -- route instance 2 needs, and it is constructive.

  order-equiv-separativelyEqual : (p q : Cond) → ⟨ p ≼ q ⟩ → ⟨ q ≼ p ⟩
                                → ⟨ separativelyEqual p q ⟩
  order-equiv-separativelyEqual p q p≼q q≼p r =
    compatible-mono (≼-refl r) p≼q , compatible-mono (≼-refl r) q≼p

  separativelyEqual-to-weaklyEqual : (p q : Cond) → ⟨ separativelyEqual p q ⟩
                                   → ⟨ weaklyEqual p q ⟩
  separativelyEqual-to-weaklyEqual p q se r =
    (λ inc c → inc (snd (se r) c)) , (λ inc c → inc (fst (se r) c))

--------------------------------------------------------------------------------
-- 1. The non-refined presentation
--------------------------------------------------------------------------------

module NonRefined where

  -- Two conditions. The carrier is declared at the level of the enclosing
  -- module, so that the instance exists at every level and so that the names
  -- of its two points carry no implicit level argument. Its h-set structure
  -- and the distinctness of its points come from Bool by a retraction, rather
  -- than from a hand written code family.

  data Two : Type ℓ where
    one low : Two

  bit : Two → Bool
  bit one = true
  bit low = false

  unbit : Bool → Two
  unbit true  = one
  unbit false = low

  bit-retract : (p : Two) → unbit (bit p) ≡ p
  bit-retract one = refl
  bit-retract low = refl

  -- The order. Written by matching on the RIGHT argument only, which is what
  -- makes transitivity four clauses instead of sixty-four: ord p one reduces
  -- to ⊤ with p still a variable.

  isLow : Two → Ω
  isLow low = ⊤
  isLow _   = ⊥

  ord : Two → Two → Ω
  ord _ one = ⊤
  ord p low = isLow p

  ord-refl : (p : Two) → ⟨ ord p p ⟩
  ord-refl one = tt*
  ord-refl low = tt*

  low-refines : (p q : Two) → ⟨ ord p q ⟩ → ⟨ isLow q ⟩ → ⟨ isLow p ⟩
  low-refines p one _ h = Empty.rec* h
  low-refines p low h _ = h

  ord-trans : {p q r : Two} → ⟨ ord p q ⟩ → ⟨ ord q r ⟩ → ⟨ ord p r ⟩
  ord-trans {p} {q} {one} _  _  = tt*
  ord-trans {p} {q} {low} h₁ h₂ = low-refines p q h₁ h₂

  isSetTwo : isSet Two
  isSetTwo = isOfHLevelRetract 2 bit unbit bit-retract isSetBool

  notion : ForcingNotion {ℓ}
  notion = record
    { Cond     = Two
    ; isSetC   = isSetTwo
    ; _≼_      = ord
    ; ≼-refl   = ord-refl
    ; ≼-trans  = λ {p} {q} {r} → ord-trans {p} {q} {r}
    ; nonempty = ∣ one ∣₁ }

  open Structure notion public
  open KernelForms notion public

  -- The two conditions are distinct, and low is STRICTLY below one: the pair
  -- is not order equivalent. This is the difference between this instance and
  -- instance 2, and it is what makes the collapse below a genuine failure of
  -- injectivity rather than a quotient by an order equivalence.

  distinct : one ≡ low → ⟨ ⊥ ⟩
  distinct e = Empty.rec (true≢false (cong bit e))

  strictly-below : ⟨ low ≼ one ⟩
  strictly-below = tt*

  not-above : ⟨ one ≼ low ⟩ → ⟨ ⊥ ⟩
  not-above x = x

  antisym : antisymmetric
  antisym one one _ _ = refl
  antisym one low h _ = Empty.rec* h
  antisym low one _ h = Empty.rec* h
  antisym low low _ _ = refl

  -- Every condition is above low, so every two conditions are compatible.

  low-below : (p : Two) → ⟨ low ≼ p ⟩
  low-below one = tt*
  low-below low = tt*

  all-compatible : (p q : Cond) → ⟨ compatible p q ⟩
  all-compatible p q = ∣ low , low-below p , low-below q ∣₁

  -- Bell's refinement condition fails, and it fails at the one pair where it
  -- could: one does not refine low, yet nothing below one is incompatible
  -- with low, because nothing at all is incompatible with anything.

  not-separative : separative → ⟨ ⊥ ⟩
  not-separative sep = PT.rec (⊥ .snd) step (sep low one not-above)
    where
    step : Σ[ r ∈ Cond ] (⟨ r ≼ one ⟩ × ⟨ incompatible r low ⟩) → ⟨ ⊥ ⟩
    step (r , _ , inc) = inc (all-compatible r low)

  -- The kernel of any completion fires here: the two conditions are
  -- compatible with exactly the same conditions, namely with all of them.

  separatively-equal : ⟨ separativelyEqual one low ⟩
  separatively-equal r = (λ _ → all-compatible r low) , (λ _ → all-compatible r one)

  weakly-equal : ⟨ weaklyEqual one low ⟩
  weakly-equal = separativelyEqual-to-weaklyEqual one low separatively-equal

  -- The whole witness in one statement: a separatively equal pair that is
  -- neither equal nor order equivalent.

  kernel-nontrivial :
    Σ[ p ∈ Cond ] Σ[ q ∈ Cond ]
      (⟨ separativelyEqual p q ⟩ × (((p ≡ q) → ⟨ ⊥ ⟩) × ((⟨ p ≼ q ⟩ → ⟨ ⊥ ⟩))))
  kernel-nontrivial = one , low , separatively-equal , distinct , not-above

  -- What any completion map must do here. B, i and the kernel law are
  -- parameters, so these are theorems about every completion of this poset
  -- rather than about one construction.

  module AnyCompletion {ℓᴮ : Level} (B : Type ℓᴮ) (i : Cond → B)
    (i-kernel : (p q : Cond) → ⟨ separativelyEqual p q ⟩ → i p ≡ i q) where

    i-collapses : i one ≡ i low
    i-collapses = i-kernel one low separatively-equal

    i-not-injective : (i one ≡ i low) × ((one ≡ low) → ⟨ ⊥ ⟩)
    i-not-injective = i-collapses , distinct

    -- Order reflection fails for ANY relation on B that is reflexive, so in
    -- particular for the order of any Boolean algebra. No property of _⊴_
    -- beyond reflexivity is used.

    no-order-reflection : {ℓ⊴ : Level} (_⊴_ : B → B → Type ℓ⊴)
                        → ((b : B) → b ⊴ b)
                        → ({p q : Cond} → i q ⊴ i p → ⟨ q ≼ p ⟩)
                        → ⟨ ⊥ ⟩
    no-order-reflection _⊴_ ⊴-refl reflect =
      reflect {low} {one} (subst (λ b → i one ⊴ b) i-collapses (⊴-refl (i one)))

  -- The same, for a kernel law delivered in the weaklyEqual form. Track C
  -- proves that form, so this is the module to instantiate there.

  module AnyCompletionWeak {ℓᴮ : Level} (B : Type ℓᴮ) (i : Cond → B)
    (i-kernel : (p q : Cond) → ⟨ weaklyEqual p q ⟩ → i p ≡ i q) where

    open AnyCompletion B i
      (λ p q se → i-kernel p q (separativelyEqual-to-weaklyEqual p q se)) public

--------------------------------------------------------------------------------
-- 2. The K0 four-condition example
--------------------------------------------------------------------------------

module K0Four where

  -- k0-probe-evidence-2026-09.md:545-560 builds four conditions and orders
  -- them by the image of an embedding into a four element Boolean algebra,
  -- with embed left₀ = embed left₁ = left. Here the same order is written
  -- directly. k-top is the K0 file's `top`, k-left₀ and k-left₁ are its
  -- `left₀` and `left₁`, k-right is its `right₀`.

  data Four : Type ℓ where
    k-top k-left₀ k-left₁ k-right : Four

  tag : Four → Bool × Bool
  tag k-top   = false , false
  tag k-left₀ = true  , false
  tag k-left₁ = true  , true
  tag k-right = false , true

  untag : Bool × Bool → Four
  untag (false , false) = k-top
  untag (true  , false) = k-left₀
  untag (true  , true)  = k-left₁
  untag (false , true)  = k-right

  tag-retract : (p : Four) → untag (tag p) ≡ p
  tag-retract k-top   = refl
  tag-retract k-left₀ = refl
  tag-retract k-left₁ = refl
  tag-retract k-right = refl

  isLeft : Four → Ω
  isLeft k-left₀ = ⊤
  isLeft k-left₁ = ⊤
  isLeft _       = ⊥

  isRight : Four → Ω
  isRight k-right = ⊤
  isRight _       = ⊥

  -- p refines q when the image of p is below the image of q. Everything
  -- refines the top; the two left conditions refine each other and nothing
  -- else refines them; the right condition refines only itself and the top.

  ord : Four → Four → Ω
  ord _ k-top   = ⊤
  ord p k-left₀ = isLeft p
  ord p k-left₁ = isLeft p
  ord p k-right = isRight p

  ord-refl : (p : Four) → ⟨ ord p p ⟩
  ord-refl k-top   = tt*
  ord-refl k-left₀ = tt*
  ord-refl k-left₁ = tt*
  ord-refl k-right = tt*

  left-refines : (p q : Four) → ⟨ ord p q ⟩ → ⟨ isLeft q ⟩ → ⟨ isLeft p ⟩
  left-refines p k-top   _ h = Empty.rec* h
  left-refines p k-left₀ h _ = h
  left-refines p k-left₁ h _ = h
  left-refines p k-right _ h = Empty.rec* h

  right-refines : (p q : Four) → ⟨ ord p q ⟩ → ⟨ isRight q ⟩ → ⟨ isRight p ⟩
  right-refines p k-top   _ h = Empty.rec* h
  right-refines p k-left₀ _ h = Empty.rec* h
  right-refines p k-left₁ _ h = Empty.rec* h
  right-refines p k-right h _ = h

  ord-trans : {p q r : Four} → ⟨ ord p q ⟩ → ⟨ ord q r ⟩ → ⟨ ord p r ⟩
  ord-trans {p} {q} {k-top}   _  _  = tt*
  ord-trans {p} {q} {k-left₀} h₁ h₂ = left-refines p q h₁ h₂
  ord-trans {p} {q} {k-left₁} h₁ h₂ = left-refines p q h₁ h₂
  ord-trans {p} {q} {k-right} h₁ h₂ = right-refines p q h₁ h₂

  left-not-right : (r : Four) → ⟨ isLeft r ⟩ → ⟨ isRight r ⟩ → ⟨ ⊥ ⟩
  left-not-right k-top   h _ = Empty.rec* h
  left-not-right k-left₀ _ h = Empty.rec* h
  left-not-right k-left₁ _ h = Empty.rec* h
  left-not-right k-right h _ = Empty.rec* h

  isSetFour : isSet Four
  isSetFour =
    isOfHLevelRetract 2 tag untag tag-retract (isSet× isSetBool isSetBool)

  notion : ForcingNotion {ℓ}
  notion = record
    { Cond     = Four
    ; isSetC   = isSetFour
    ; _≼_      = ord
    ; ≼-refl   = ord-refl
    ; ≼-trans  = λ {p} {q} {r} → ord-trans {p} {q} {r}
    ; nonempty = ∣ k-top ∣₁ }

  open Structure notion public
  open KernelForms notion public

  -- Incompatibility of a left condition with the right condition. A common
  -- refinement would be both a left and a right condition.

  left-right-incompatible : (a b : Four) → ⟨ isLeft a ⟩ → ⟨ isRight b ⟩
                          → ⟨ incompatible a b ⟩
  left-right-incompatible a b la rb = PT.rec (⊥ .snd) step
    where
    step : compatibleData a b → ⟨ ⊥ ⟩
    step (r , ra , rb') =
      left-not-right r (left-refines r a ra la) (right-refines r b rb' rb)

  right-left-incompatible : (a b : Four) → ⟨ isRight a ⟩ → ⟨ isLeft b ⟩
                          → ⟨ incompatible a b ⟩
  right-left-incompatible a b ra lb = PT.rec (⊥ .snd) step
    where
    step : compatibleData a b → ⟨ ⊥ ⟩
    step (r , rr , rl) =
      left-not-right r (left-refines r b rl lb) (right-refines r a rr ra)

  inc-left₀-right : ⟨ incompatible k-left₀ k-right ⟩
  inc-left₀-right = left-right-incompatible k-left₀ k-right tt* tt*

  inc-left₁-right : ⟨ incompatible k-left₁ k-right ⟩
  inc-left₁-right = left-right-incompatible k-left₁ k-right tt* tt*

  inc-right-left₀ : ⟨ incompatible k-right k-left₀ ⟩
  inc-right-left₀ = right-left-incompatible k-right k-left₀ tt* tt*

  inc-right-left₁ : ⟨ incompatible k-right k-left₁ ⟩
  inc-right-left₁ = right-left-incompatible k-right k-left₁ tt* tt*

  -- The two left conditions refine each other and are distinct, so
  -- antisymmetry fails. This is the property the K0 file actually exhibits.

  left₀≼left₁ : ⟨ k-left₀ ≼ k-left₁ ⟩
  left₀≼left₁ = tt*

  left₁≼left₀ : ⟨ k-left₁ ≼ k-left₀ ⟩
  left₁≼left₀ = tt*

  lefts-distinct : k-left₀ ≡ k-left₁ → ⟨ ⊥ ⟩
  lefts-distinct e = Empty.rec (false≢true (cong (λ x → snd (tag x)) e))

  not-antisymmetric : antisymmetric → ⟨ ⊥ ⟩
  not-antisymmetric anti = lefts-distinct (anti k-left₀ k-left₁ left₀≼left₁ left₁≼left₀)

  -- Bell's refinement condition HOLDS, at every pair where it has content.
  -- Below the top a witness has to be chosen on the other side; everywhere
  -- else the condition q is itself incompatible with p.

  sep : separative
  sep k-top   k-top   h = Empty.rec* (h tt*)
  sep k-left₀ k-top   _ = ∣ k-right , tt* , inc-right-left₀ ∣₁
  sep k-left₁ k-top   _ = ∣ k-right , tt* , inc-right-left₁ ∣₁
  sep k-right k-top   _ = ∣ k-left₀ , tt* , inc-left₀-right ∣₁
  sep k-top   k-left₀ h = Empty.rec* (h tt*)
  sep k-left₀ k-left₀ h = Empty.rec* (h tt*)
  sep k-left₁ k-left₀ h = Empty.rec* (h tt*)
  sep k-right k-left₀ _ = ∣ k-left₀ , tt* , inc-left₀-right ∣₁
  sep k-top   k-left₁ h = Empty.rec* (h tt*)
  sep k-left₀ k-left₁ h = Empty.rec* (h tt*)
  sep k-left₁ k-left₁ h = Empty.rec* (h tt*)
  sep k-right k-left₁ _ = ∣ k-left₁ , tt* , inc-left₁-right ∣₁
  sep k-top   k-right h = Empty.rec* (h tt*)
  sep k-left₀ k-right _ = ∣ k-right , tt* , inc-right-left₀ ∣₁
  sep k-left₁ k-right _ = ∣ k-right , tt* , inc-right-left₁ ∣₁
  sep k-right k-right h = Empty.rec* (h tt*)

  -- The pair on which every completion collapses.

  lefts-separatively-equal : ⟨ separativelyEqual k-left₀ k-left₁ ⟩
  lefts-separatively-equal =
    order-equiv-separativelyEqual k-left₀ k-left₁ left₀≼left₁ left₁≼left₀

  -- The port of the K0 file's compatibility relation. Its ConditionCompatible
  -- (k0-probe-evidence:566-568) is Track A's compatibleData, on the nose, and
  -- the only form that can appear inside ⋀ or ⋁ is the truncation of it.

  k0-Σ-form : Cond → Cond → Type ℓ
  k0-Σ-form p q = Σ[ r ∈ Cond ] (⟨ r ≼ p ⟩ × ⟨ r ≼ q ⟩)

  k0-Σ-form-is-compatibleData : (p q : Cond) → k0-Σ-form p q ≡ compatibleData p q
  k0-Σ-form-is-compatibleData p q = refl

  k0-to-truth-value : (p q : Cond) → k0-Σ-form p q → ⟨ compatible p q ⟩
  k0-to-truth-value p q = witness {p} {q}

  -- And the truncation is not a formality here: the sigma form has two
  -- distinct inhabitants already at the pair (k-top , k-top), so it is not a
  -- proposition and cannot be the value of a formula.

  top-left₀-distinct : k-top ≡ k-left₀ → ⟨ ⊥ ⟩
  top-left₀-distinct e = Empty.rec (false≢true (cong (λ x → fst (tag x)) e))

  Σ-form-not-prop : isProp (k0-Σ-form k-top k-top) → ⟨ ⊥ ⟩
  Σ-form-not-prop ip =
    top-left₀-distinct (cong fst (ip (k-top , tt* , tt*) (k-left₀ , tt* , tt*)))

  -- The K0 file's SameSeparativeSemantics (k0-probe-evidence:618-620), stated
  -- in its own sigma form and proved, so that the port is exhibited rather
  -- than asserted. The truncated statement is lefts-separatively-equal above.

  k0-same-separative-semantics : (r : Cond)
    → (k0-Σ-form r k-left₀ → k0-Σ-form r k-left₁)
    × (k0-Σ-form r k-left₁ → k0-Σ-form r k-left₀)
  k0-same-separative-semantics r = fwd , bwd
    where
    fwd : k0-Σ-form r k-left₀ → k0-Σ-form r k-left₁
    fwd (s , s≼r , s≼l₀) = s , s≼r , ≼-trans {s} {k-left₀} {k-left₁} s≼l₀ left₀≼left₁
    bwd : k0-Σ-form r k-left₁ → k0-Σ-form r k-left₀
    bwd (s , s≼r , s≼l₁) = s , s≼r , ≼-trans {s} {k-left₁} {k-left₀} s≼l₁ left₁≼left₀

  -- Separativity alone does not make a completion map injective. This
  -- instance is separative, and every completion of it identifies the two
  -- left conditions.

  module AnyCompletion {ℓᴮ : Level} (B : Type ℓᴮ) (i : Cond → B)
    (i-kernel : (p q : Cond) → ⟨ separativelyEqual p q ⟩ → i p ≡ i q) where

    i-collapses : i k-left₀ ≡ i k-left₁
    i-collapses = i-kernel k-left₀ k-left₁ lefts-separatively-equal

    separativity-is-not-enough :
      separative × ((i k-left₀ ≡ i k-left₁) × ((k-left₀ ≡ k-left₁) → ⟨ ⊥ ⟩))
    separativity-is-not-enough = sep , i-collapses , lefts-distinct

  module AnyCompletionWeak {ℓᴮ : Level} (B : Type ℓᴮ) (i : Cond → B)
    (i-kernel : (p q : Cond) → ⟨ weaklyEqual p q ⟩ → i p ≡ i q) where

    open AnyCompletion B i
      (λ p q se → i-kernel p q (separativelyEqual-to-weaklyEqual p q se)) public

--------------------------------------------------------------------------------
-- 3. Trivial forcing
--------------------------------------------------------------------------------

module Trivial where

  Point : Type ℓ
  Point = Unit*

  ord : Point → Point → Ω
  ord _ _ = ⊤

  notion : ForcingNotion {ℓ}
  notion = record
    { Cond     = Point
    ; isSetC   = isSetUnit*
    ; _≼_      = ord
    ; ≼-refl   = λ _ → tt*
    ; ≼-trans  = λ {_} {_} {_} _ _ → tt*
    ; nonempty = ∣ tt* ∣₁ }

  open Structure notion public

  one-point : (p q : Cond) → p ≡ q
  one-point p q = refl

  all-compatible : (p q : Cond) → ⟨ compatible p q ⟩
  all-compatible p q = ∣ tt* , tt* , tt* ∣₁

  antisym : antisymmetric
  antisym p q _ _ = refl

  -- Vacuously separative: nothing fails to refine anything.

  sep : separative
  sep p q h = Empty.rec* (h tt*)

  not-atomless : atomless → ⟨ ⊥ ⟩
  not-atomless atl = PT.rec (⊥ .snd) outer (atl tt*)
    where
    inner : (q : Cond)
          → Σ[ r ∈ Cond ] (⟨ q ≼ tt* ⟩ × (⟨ r ≼ tt* ⟩ × ⟨ incompatible q r ⟩))
          → ⟨ ⊥ ⟩
    inner q (r , _ , _ , inc) = inc (all-compatible q r)
    outer : Σ[ q ∈ Cond ]
              ⟨ ⋁ Cond (λ r → (q ≼ tt*) ⊓ ((r ≼ tt*) ⊓ incompatible q r)) ⟩
          → ⟨ ⊥ ⟩
    outer (q , h) = PT.rec (⊥ .snd) (inner q) h

  -- Every completion map out of one condition is constant, whatever the
  -- target and whatever the map.

  module AnyCompletion {ℓᴮ : Level} (B : Type ℓᴮ) (i : Cond → B) where

    i-constant : (p q : Cond) → i p ≡ i q
    i-constant p q = cong i (one-point p q)

  -- The whole poset is a filter, and it is host generic, because a dense set
  -- meets it at whatever condition density supplies. So the atomlessness
  -- hypothesis of Track A's no-host-generic is not removable: without it the
  -- theorem is false at this instance, and no LEM is involved either way.

  everything : Sub
  everything = λ _ → ⊤

  everything-filter : isFilter everything
  everything-filter = record
    { inhabited = ∣ tt* , tt* ∣₁
    ; upward    = λ _ _ _ _ → tt*
    ; directed  = λ _ _ _ _ → ∣ tt* , tt* , tt* , tt* ∣₁ }

  everything-hostGeneric : hostGeneric everything
  everything-hostGeneric D dns = PT.map step (dns tt*)
    where
    step : Σ[ p ∈ Cond ] (⟨ p ∈ᴾ D ⟩ × ⟨ p ≼ tt* ⟩)
         → Σ[ p ∈ Cond ] (⟨ p ∈ᴾ everything ⟩ × ⟨ p ∈ᴾ D ⟩)
    step (p , hp , _) = p , tt* , hp

  atomless-not-removable : Σ[ G ∈ Sub ] (isFilter G × hostGeneric G)
  atomless-not-removable = everything , everything-filter , everything-hostGeneric

--------------------------------------------------------------------------------
-- 4. What the two instances say together
--------------------------------------------------------------------------------

-- Architecture section 5, N5, as one checked statement: separativity and
-- antisymmetry are independent, so injectivity of a completion map needs both
-- and the K0 example is a witness for the second only. The K0 file's name,
-- NonseparativeCompletion.agda, names the property its example HAS.

adapters-independent :
    (Σ[ 𝔓 ∈ ForcingNotion {ℓ} ]
       (Structure.separative 𝔓 × (Structure.antisymmetric 𝔓 → ⟨ ⊥ ⟩)))
  × (Σ[ 𝔔 ∈ ForcingNotion {ℓ} ]
       (Structure.antisymmetric 𝔔 × (Structure.separative 𝔔 → ⟨ ⊥ ⟩)))
adapters-independent =
    (K0Four.notion , K0Four.sep , K0Four.not-antisymmetric)
  , (NonRefined.notion , NonRefined.antisym , NonRefined.not-separative)
