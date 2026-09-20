{-# OPTIONS --cubical --safe --guardedness #-}

-- K2 module M4 (Track C): the host regular-open algebra of a forcing notion.
--
-- Parameterized by the FIELDS of a ForcingNotion rather than by the record, so
-- that this module does not wait on M1 and so that a consumer can instantiate
-- it either from the record or from raw data. The sixth field of M1's record,
-- mere inhabitation of Cond, is deliberately absent: nothing in the algebra,
-- its laws or its completeness needs it. Nondegeneracy is the one statement
-- that does, and it is delivered as a function of a condition.
--
-- The primitive notion of regularity is the REGULAR ELEMENT one, U = U ⋆ ⋆,
-- and not Bell's displayed dense-below formula (bell-2005-boolean-valued-
-- models.fulltext.md:3446). The reason is the one Bell himself gives at
-- printed p. 8 (fulltext:1260-1268): the regular elements of a Heyting algebra
-- form a Boolean algebra, and if the Heyting algebra is complete so is the
-- Boolean one, and that argument is constructive. The consequence is that
-- everything from `_⋆` through `roLaws` and `roComplete` is LEM free; the
-- classical cost is isolated in sections 9 and 10.
--
-- THE TRAP, and it decides whether this file is correct at all: the completion
-- map of a condition is the DOUBLE PSEUDOCOMPLEMENT of its cone,
-- i p = ((↓ᶜ p) ⋆) ⋆, never the cone ↓ᶜ p itself. Bell's Lemma 2.1(i)
-- (fulltext:3441) says O_p is regular open for every p if and only if the
-- presentation is refined, and K2 must accept presentations that are not, so
-- the naive map is not even well defined there.
--
-- Notation rules inherited from K2 section 1.0 and respected throughout. The
-- cubical powerset membership _∈ᶜ_ never appears, not even in type position;
-- host subsets of conditions are read through _∈ᴾ_ and ⟨_⟩. Every negation is
-- spelled _ ⇒ ⊥ with the algebra's own bottom; the ¬_ that comes into scope
-- with the hProp algebra is never used, and the pseudocomplement of this
-- module is the separate symbol ¬ᴮ_. Compatibility inside any ⋀ or ⋁ is the
-- truncated ⋁-form.
--
-- Two facts about `_⋆` that the design depends on and that are easy to get
-- wrong. It is the pseudocomplement of the DOWNSET algebra, not of the
-- powerset: for a subset that is not downward closed, U ⊑ U ⋆ ⋆ fails and so
-- does U ⋆ ⋆ ⋆ ⊑ U ⋆. Concretely, on the two-condition poset {a, b} with
-- b ≼ a and a ⋠ b, the singleton {a} has {a} ⋆ = {b} and {a} ⋆ ⋆ = ∅, so the
-- first inclusion fails at a, and {b} ⋆ ⋆ = {a, b} witnesses the second
-- failing. So every lemma below that needs one of those two inclusions carries
-- `Down U` as an explicit hypothesis, and the regularity predicate is the
-- two-sided biconditional, which SUPPLIES downward closure rather than
-- assuming it.
--
-- Every theorem takes its Reg and Cond arguments EXPLICITLY. This is not
-- style: Reg is a Σ-type and _⊓ᴮ_ builds a pair, so an implicit argument
-- standing in an order statement is not recoverable by unification from the
-- goal. Track B measured the same wall one level down (REPORT-B section 7).

open import Base.Prelude
open import Base.Truth

module HostRegularOpen {ℓ : Level}
  (Cond : Type ℓ) (isSetC : isSet Cond)
  (_≼_ : Cond → Cond → hProp ℓ)
  (≼-refl : (p : Cond) → ⟨ p ≼ p ⟩)
  (≼-trans : {p q r : Cond} → ⟨ p ≼ q ⟩ → ⟨ q ≼ r ⟩ → ⟨ p ≼ r ⟩)
  where

open import Algebra
open import Base.Classical using ( LEM )

open import Cubical.Data.Sum using ( _⊎_; inl; inr )
open import Cubical.Data.Unit using ( tt* )
open import Cubical.Data.Sigma using ( Σ≡Prop )
open import Cubical.Foundations.Equiv using ( _≃_; propBiimpl→Equiv )
open import Cubical.Foundations.HLevels using ( isSetΠ; isSetΣSndProp )
open import Cubical.Functions.Logic using ( ⇔toPath )
import Cubical.Data.Empty as Empty
import Cubical.Functions.Logic as Logic
import Cubical.HITs.PropositionalTruncation as PT
open PT using ( ∥_∥₁; ∣_∣₁ )

open TruthAlgebra (hPropAlgebra ℓ)

--------------------------------------------------------------------------------
-- 1. Host subsets of conditions, entailment, downward closure
--------------------------------------------------------------------------------

-- A host subset of conditions is an Ω-valued predicate. It is large: Ω is
-- hProp ℓ, so Sub lands in Type (ℓ-suc ℓ), and so does Reg below.

Sub : Type (ℓ-suc ℓ)
Sub = Cond → Ω

_∈ᴾ_ : Cond → Sub → Ω
p ∈ᴾ D = D p

-- Entailment between subsets is a host TYPE, not a truth value, and it is
-- SMALL: Cond and every ⟨ U q ⟩ live in Type ℓ. This is what lets a family of
-- entailments be indexed by ⋁ Cond in i-dense, where the Boolean order, which
-- lives in Type (ℓ-suc ℓ), cannot go.

_⊑_ : Sub → Sub → Type ℓ
U ⊑ V = (q : Cond) → ⟨ U q ⟩ → ⟨ V q ⟩

isProp⊑ : (U V : Sub) → isProp (U ⊑ V)
isProp⊑ U V = isPropΠ (λ q → isPropΠ (λ _ → snd (V q)))

⊑-refl : (U : Sub) → U ⊑ U
⊑-refl U q x = x

⊑-trans : (U V W : Sub) → U ⊑ V → V ⊑ W → U ⊑ W
⊑-trans U V W h k q x = k q (h q x)

-- Downward closure: an open subset in the Alexandrov sense.

Down : Sub → Type ℓ
Down U = (q r : Cond) → ⟨ r ≼ q ⟩ → ⟨ U q ⟩ → ⟨ U r ⟩

-- The pointwise operations on subsets. They are named at the level of Sub, and
-- not inlined inside the Reg operations, so that every later conversion step
-- unfolds one definition rather than a where-lifted auxiliary.

_∩_ : Sub → Sub → Sub
U ∩ V = λ q → (U q) ⊓ (V q)

_∪_ : Sub → Sub → Sub
U ∪ V = λ q → (U q) ⊔ (V q)

⋂ : (A : Type ℓ) → (A → Sub) → Sub
⋂ A f = λ q → ⋀ A (λ a → f a q)

⋃ : (A : Type ℓ) → (A → Sub) → Sub
⋃ A f = λ q → ⋁ A (λ a → f a q)

-- The Heyting implication of subsets: everything refining q that lies in U
-- lies in V.

_↝_ : Sub → Sub → Sub
U ↝ V = λ q → ⋀ Cond (λ r → (r ≼ q) ⇒ ((U r) ⇒ (V r)))

--------------------------------------------------------------------------------
-- 2. The poset vocabulary this module needs
--------------------------------------------------------------------------------

-- These repeat M1's definitions verbatim rather than importing them, because
-- M1's Structure module is parameterized by the whole record while this module
-- is parameterized by five of its fields. Repeating the definition keeps the
-- two definitionally equal at any instantiation, which is what a consumer
-- needs when it passes a ForcingNotion's fields in here.

compatible : Cond → Cond → Ω
compatible p q = ⋁ Cond (λ r → (r ≼ p) ⊓ (r ≼ q))

incompatible : Cond → Cond → Ω
incompatible p q = compatible p q ⇒ ⊥

compatible-sym : (p q : Cond) → ⟨ compatible p q ⟩ → ⟨ compatible q p ⟩
compatible-sym p q = PT.map swap
  where
  swap : Σ[ r ∈ Cond ] (⟨ r ≼ p ⟩ × ⟨ r ≼ q ⟩)
       → Σ[ r ∈ Cond ] (⟨ r ≼ q ⟩ × ⟨ r ≼ p ⟩)
  swap (r , r≼p , r≼q) = r , r≼q , r≼p

-- Bell's O_p, the principal cone of a condition (fulltext:3433-3434).

↓ᶜ_ : Cond → Sub
↓ᶜ p = λ q → q ≼ p

↓ᶜ-down : (p : Cond) → Down (↓ᶜ p)
↓ᶜ-down p q r r≼q q≼p = ≼-trans r≼q q≼p

denseBelow : Cond → Sub → Ω
denseBelow r D = ⋀ Cond (λ q → (q ≼ r) ⇒ ⋁ Cond (λ p → (p ∈ᴾ D) ⊓ (p ≼ q)))

-- Additional data, never fields, exactly as in M1.

separative : Type ℓ
separative = (p q : Cond) → (⟨ q ≼ p ⟩ → ⟨ ⊥ ⟩)
           → ⟨ ⋁ Cond (λ r → (r ≼ q) ⊓ incompatible r p) ⟩

antisymmetric : Type ℓ
antisymmetric = (p q : Cond) → ⟨ p ≼ q ⟩ → ⟨ q ≼ p ⟩ → p ≡ q

-- Bell Problem 2.4(i) (fulltext:3538-3539): p and q are compatible with
-- exactly the same conditions.

separativelyEqual : Cond → Cond → Ω
separativelyEqual p q = ⋀ Cond (λ r →
  (compatible r p ⇒ compatible r q) ⊓ (compatible r q ⇒ compatible r p))

-- The CONSTRUCTIVE kernel of the completion map is the incompatibility form,
-- not the compatibility form. See i-kernel, and section 9 for the measurement
-- of the gap between the two.

weaklyEqual : Cond → Cond → Ω
weaklyEqual p q = ⋀ Cond (λ r →
  (incompatible r p ⇒ incompatible r q) ⊓ (incompatible r q ⇒ incompatible r p))

--------------------------------------------------------------------------------
-- 3. The pseudocomplement and its calculus
--------------------------------------------------------------------------------

-- q lies in U ⋆ when no refinement of q lies in U. Unfolded, ⟨ (U ⋆) q ⟩ is
-- (r : Cond) → ⟨ r ≼ q ⟩ → ⟨ U r ⟩ → ⟨ ⊥ ⟩, and every proof below writes it
-- that way rather than through an introduction rule.

_⋆ : Sub → Sub
U ⋆ = λ q → ⋀ Cond (λ r → (r ≼ q) ⇒ ((U r) ⇒ ⊥))

-- A pseudocomplement is downward closed whatever U is. This is the reason
-- openness is not a separate conjunct of regularity.

⋆-down : (U : Sub) → Down (U ⋆)
⋆-down U q r r≼q x = λ s s≼r u → x s (≼-trans s≼r r≼q) u

⋆-anti : (U V : Sub) → U ⊑ V → (V ⋆) ⊑ (U ⋆)
⋆-anti U V h q x = λ r r≼q u → x r r≼q (h r u)

-- The unit of the double pseudocomplement. Downward closure is REQUIRED here,
-- and is the whole reason Down exists in this file: for U that is not downward
-- closed the inclusion is false, see the header.

⋆⋆-unit : (U : Sub) → Down U → U ⊑ ((U ⋆) ⋆)
⋆⋆-unit U dn q u = λ r r≼q y → y r (≼-refl r) (dn q r r≼q u)

⋆⋆-mono : (U V : Sub) → U ⊑ V → ((U ⋆) ⋆) ⊑ ((V ⋆) ⋆)
⋆⋆-mono U V h = ⋆-anti (V ⋆) (U ⋆) (⋆-anti U V h)

⋆⋆-down : (U : Sub) → Down ((U ⋆) ⋆)
⋆⋆-down U = ⋆-down (U ⋆)

iff : Ω → Ω → Ω
iff a b = (a ⇒ b) ⊓ (b ⇒ a)

isRegular : Sub → Ω
isRegular U = ⋀ Cond (λ q → iff (U q) (((U ⋆) ⋆) q))

regular-⊑ : (U : Sub) → ⟨ isRegular U ⟩ → U ⊑ ((U ⋆) ⋆)
regular-⊑ U reg q = fst (reg q)

regular-⊒ : (U : Sub) → ⟨ isRegular U ⟩ → ((U ⋆) ⋆) ⊑ U
regular-⊒ U reg q = snd (reg q)

-- Downward closure is a CONSEQUENCE of regularity, transported across the
-- biconditional from the double pseudocomplement, which has it for free.

regular-down : (U : Sub) → ⟨ isRegular U ⟩ → Down U
regular-down U reg q r r≼q u =
  regular-⊒ U reg r (⋆⋆-down U q r r≼q (regular-⊑ U reg q u))

-- Every pseudocomplement of an open subset is regular. This is the engine: it
-- is what makes ¬ᴮ, ⊔ᴮ and ⋁ᴮ land in Reg with no classical step anywhere.

⋆-regular : (U : Sub) → Down U → ⟨ isRegular (U ⋆) ⟩
⋆-regular U dn q =
    ⋆⋆-unit (U ⋆) (⋆-down U) q
  , ⋆-anti U ((U ⋆) ⋆) (⋆⋆-unit U dn) q

-- Saturation: the double pseudocomplement of W is the least regular subset
-- above W. With ⋆⋆-unit and ⋆⋆-mono this proves every join law below.

⋆⋆-least : (W R : Sub) → ⟨ isRegular R ⟩ → W ⊑ R → ((W ⋆) ⋆) ⊑ R
⋆⋆-least W R reg h =
  ⊑-trans ((W ⋆) ⋆) ((R ⋆) ⋆) R (⋆⋆-mono W R h) (regular-⊒ R reg)

--------------------------------------------------------------------------------
-- 4. The carrier, its set-ness, and its equality principle
--------------------------------------------------------------------------------

Reg : Type (ℓ-suc ℓ)
Reg = Σ[ U ∈ Sub ] ⟨ isRegular U ⟩

isSetSub : isSet Sub
isSetSub = isSetΠ (λ _ → isSetHProp)

isSetReg : isSet Reg
isSetReg = isSetΣSndProp isSetSub (λ U → snd (isRegular U))

-- THE EQUALITY PRINCIPLE, proved before any law and used by every one of them.
-- Two regular subsets are equal in Reg as soon as they entail each other: the
-- regularity component is a proposition, so Σ≡Prop discards it, and the subset
-- component is a function into hProp, so pointwise biimplication is pointwise
-- equality. K1 measured what happens without such a principle: nine unsolved
-- metas from cong₂ over Σ-building operations (k1-ordinary-profile-cardinal-
-- bridges-2026-09.md:59), and Reg is a Σ-type whose second component is a
-- proof, so the hazard is strictly larger here.

Reg≡ : (U V : Reg) → fst U ⊑ fst V → fst V ⊑ fst U → U ≡ V
Reg≡ U V h k =
  Σ≡Prop (λ W → snd (isRegular W)) (funExt (λ q → ⇔toPath (h q) (k q)))

Reg⊑ : (U V : Reg) → U ≡ V → fst U ⊑ fst V
Reg⊑ U V e q x = subst (λ W → ⟨ fst W q ⟩) e x

regDown : (U : Reg) → Down (fst U)
regDown U = regular-down (fst U) (snd U)

--------------------------------------------------------------------------------
-- 5. The eight operations
--------------------------------------------------------------------------------

⊤ᴮ : Reg
⊤ᴮ = (λ _ → ⊤) , reg
  where
  reg : ⟨ isRegular (λ _ → ⊤) ⟩
  reg q = (λ _ r r≼q y → y r (≼-refl r) tt*) , (λ _ → tt*)

⊥ᴮ : Reg
⊥ᴮ = (λ _ → ⊥) , reg
  where
  reg : ⟨ isRegular (λ _ → ⊥) ⟩
  reg q = (λ x → Empty.rec* x) , (λ x → x q (≼-refl q) (λ s _ z → z))

_⊓ᴮ_ : Reg → Reg → Reg
U ⊓ᴮ V = ((fst U) ∩ (fst V)) , reg
  where
  dn : Down ((fst U) ∩ (fst V))
  dn q r r≼q z = regDown U q r r≼q (fst z) , regDown V q r r≼q (snd z)
  reg : ⟨ isRegular ((fst U) ∩ (fst V)) ⟩
  reg q = ⋆⋆-unit ((fst U) ∩ (fst V)) dn q
        , λ x → regular-⊒ (fst U) (snd U) q
                  (⋆⋆-mono ((fst U) ∩ (fst V)) (fst U) (λ s z → fst z) q x)
              , regular-⊒ (fst V) (snd V) q
                  (⋆⋆-mono ((fst U) ∩ (fst V)) (fst V) (λ s z → snd z) q x)

¬ᴮ_ : Reg → Reg
¬ᴮ U = ((fst U) ⋆) , ⋆-regular (fst U) (regDown U)

_⊔ᴮ_ : Reg → Reg → Reg
U ⊔ᴮ V = ((((fst U) ∪ (fst V)) ⋆) ⋆)
       , ⋆-regular (((fst U) ∪ (fst V)) ⋆) (⋆-down ((fst U) ∪ (fst V)))

-- Implication is the HEYTING implication, not the derived (¬ᴮ U) ⊔ᴮ V. The two
-- agree in the Boolean algebra, and Track B's BooleanTheory.⇒-def proves it
-- from the laws, but the adjunction fields ⇒-curry and ⇒-uncurry are one line
-- each in this spelling and would be an argument in the other.

_⇒ᴮ_ : Reg → Reg → Reg
U ⇒ᴮ V = ((fst U) ↝ (fst V)) , reg
  where
  dn : Down ((fst U) ↝ (fst V))
  dn q r r≼q x = λ s s≼r us → x s (≼-trans s≼r r≼q) us
  out : ((((fst U) ↝ (fst V)) ⋆) ⋆) ⊑ ((fst U) ↝ (fst V))
  out q x r r≼q ur = regular-⊒ (fst V) (snd V) r inner
    where
    inner : ⟨ (((fst V) ⋆) ⋆) r ⟩
    inner s s≼r y = xs s (≼-refl s) sH
      where
      xs : ⟨ ((((fst U) ↝ (fst V)) ⋆) ⋆) s ⟩
      xs = ⋆⋆-down ((fst U) ↝ (fst V)) q s (≼-trans s≼r r≼q) x
      sH : ⟨ (((fst U) ↝ (fst V)) ⋆) s ⟩
      sH t t≼s ht =
        y t t≼s (ht t (≼-refl t) (regDown U r t (≼-trans t≼s s≼r) ur))
  reg : ⟨ isRegular ((fst U) ↝ (fst V)) ⟩
  reg q = ⋆⋆-unit ((fst U) ↝ (fst V)) dn q , out q

⋀ᴮ : (A : Type ℓ) → (A → Reg) → Reg
⋀ᴮ A f = (⋂ A (λ a → fst (f a))) , reg
  where
  dn : Down (⋂ A (λ a → fst (f a)))
  dn q r r≼q x = λ a → regDown (f a) q r r≼q (x a)
  reg : ⟨ isRegular (⋂ A (λ a → fst (f a))) ⟩
  reg q = ⋆⋆-unit (⋂ A (λ a → fst (f a))) dn q
        , λ x a → regular-⊒ (fst (f a)) (snd (f a)) q
                    (⋆⋆-mono (⋂ A (λ a → fst (f a))) (fst (f a))
                      (λ s z → z a) q x)

⋁ᴮ : (A : Type ℓ) → (A → Reg) → Reg
⋁ᴮ A f = (((⋃ A (λ a → fst (f a))) ⋆) ⋆)
       , ⋆-regular ((⋃ A (λ a → fst (f a))) ⋆) (⋆-down (⋃ A (λ a → fst (f a))))

--------------------------------------------------------------------------------
-- 6. The lattice characterizations, at the level of entailment
--------------------------------------------------------------------------------

⊓ᴮ-fst : (U V : Reg) → fst (U ⊓ᴮ V) ⊑ fst U
⊓ᴮ-fst U V q z = fst z

⊓ᴮ-snd : (U V : Reg) → fst (U ⊓ᴮ V) ⊑ fst V
⊓ᴮ-snd U V q z = snd z

⊓ᴮ-greatest : (U V W : Reg) → fst W ⊑ fst U → fst W ⊑ fst V
            → fst W ⊑ fst (U ⊓ᴮ V)
⊓ᴮ-greatest U V W h k q x = h q x , k q x

⊔ᴮ-inl : (U V : Reg) → fst U ⊑ fst (U ⊔ᴮ V)
⊔ᴮ-inl U V = ⊑-trans (fst U) (((fst U) ⋆) ⋆) (fst (U ⊔ᴮ V))
  (regular-⊑ (fst U) (snd U))
  (⋆⋆-mono (fst U) ((fst U) ∪ (fst V)) (λ q x → Logic.inl x))

⊔ᴮ-inr : (U V : Reg) → fst V ⊑ fst (U ⊔ᴮ V)
⊔ᴮ-inr U V = ⊑-trans (fst V) (((fst V) ⋆) ⋆) (fst (U ⊔ᴮ V))
  (regular-⊑ (fst V) (snd V))
  (⋆⋆-mono (fst V) ((fst U) ∪ (fst V)) (λ q x → Logic.inr x))

⊔ᴮ-least : (U V W : Reg) → fst U ⊑ fst W → fst V ⊑ fst W
         → fst (U ⊔ᴮ V) ⊑ fst W
⊔ᴮ-least U V W h k =
  ⋆⋆-least ((fst U) ∪ (fst V)) (fst W) (snd W) step
  where
  branch : (q : Cond) → ⟨ fst U q ⟩ ⊎ ⟨ fst V q ⟩ → ⟨ fst W q ⟩
  branch q (inl x) = h q x
  branch q (inr y) = k q y
  step : ((fst U) ∪ (fst V)) ⊑ fst W
  step q z = PT.rec (snd (fst W q)) (branch q) z

⋀ᴮ-lb : (A : Type ℓ) (f : A → Reg) (a : A) → fst (⋀ᴮ A f) ⊑ fst (f a)
⋀ᴮ-lb A f a q x = x a

⋀ᴮ-greatest : (A : Type ℓ) (f : A → Reg) (W : Reg)
            → ((a : A) → fst W ⊑ fst (f a)) → fst W ⊑ fst (⋀ᴮ A f)
⋀ᴮ-greatest A f W h q x = λ a → h a q x

⋁ᴮ-ub : (A : Type ℓ) (f : A → Reg) (a : A) → fst (f a) ⊑ fst (⋁ᴮ A f)
⋁ᴮ-ub A f a = ⊑-trans (fst (f a)) (((fst (f a)) ⋆) ⋆) (fst (⋁ᴮ A f))
  (regular-⊑ (fst (f a)) (snd (f a)))
  (⋆⋆-mono (fst (f a)) (⋃ A (λ b → fst (f b))) (λ q x → ∣ a , x ∣₁))

⋁ᴮ-least : (A : Type ℓ) (f : A → Reg) (W : Reg)
         → ((a : A) → fst (f a) ⊑ fst W) → fst (⋁ᴮ A f) ⊑ fst W
⋁ᴮ-least A f W h =
  ⋆⋆-least (⋃ A (λ a → fst (f a))) (fst W) (snd W) step
  where
  step : (⋃ A (λ a → fst (f a))) ⊑ fst W
  step q z = PT.rec (snd (fst W q)) (λ y → h (fst y) q (snd y)) z

-- Distributivity of a meet over a saturation. This single lemma is the whole
-- content of the finite distributive law, and through Track B's CompleteTheory
-- of infinite distributivity as well. It is constructive, and it is where
-- downward closure of the left factor is spent.

⊓-⋆⋆-dist : (U : Sub) → Down U → (W : Sub)
          → (U ∩ ((W ⋆) ⋆)) ⊑ (((U ∩ W) ⋆) ⋆)
⊓-⋆⋆-dist U dn W q z = step
  where
  step : (r : Cond) → ⟨ r ≼ q ⟩
       → ((s : Cond) → ⟨ s ≼ r ⟩ → (⟨ U s ⟩ × ⟨ W s ⟩) → ⟨ ⊥ ⟩) → ⟨ ⊥ ⟩
  step r r≼q y =
    ⋆⋆-down W q r r≼q (snd z) r (≼-refl r)
      (λ s s≼r w → y s s≼r (dn r s s≼r (dn q r r≼q (fst z)) , w))

--------------------------------------------------------------------------------
-- 7. The truth algebra, the Boolean laws, and host completeness
--------------------------------------------------------------------------------

-- This fills the seat reserved at src/Base/Truth.lagda.md:161-166 for "the
-- regular-open Boolean completion of a forcing poset, with Ω a complete
-- Boolean algebra", and the record carries it unchanged. The level arithmetic
-- closes with no resizing: Reg is Type (ℓ-suc ℓ) and the index type of ⋀ᴮ and
-- ⋁ᴮ is Type ℓ, exactly the shape of hPropAlgebra ℓ.

roAlgebra : TruthAlgebra ℓ (ℓ-suc ℓ)
roAlgebra = record
  { Ω      = Reg
  ; isSetΩ = isSetReg
  ; _⊓_    = _⊓ᴮ_
  ; _⊔_    = _⊔ᴮ_
  ; _⇒_    = _⇒ᴮ_
  ; ¬_     = ¬ᴮ_
  ; ⊤      = ⊤ᴮ
  ; ⊥      = ⊥ᴮ
  ; ⋀      = ⋀ᴮ
  ; ⋁      = ⋁ᴮ }

-- Only the order and the record types are taken from Track B's interface.
-- Opening BooleanAlgebra wholesale would re-export a second Ω, ⊓, ⊔, ⇒, ¬, ⊤,
-- ⊥, ⋀ and ⋁ on top of the hProp algebra's, and every connective in this file
-- would become ambiguous.

-- The open is public, because the statements of i-mono, i-below≤ and
-- separative→reflect below mention _≤ᴮ_, so a consumer of this module needs
-- the name without having to reconstruct it as
-- Algebra.BooleanAlgebra._≤_ (roAlgebra ...).

open BooleanAlgebra roAlgebra public
  using ( BooleanLaws ; CompleteHost ; Nondegenerate
        ; IsUpper ; IsLower ; IsSup ; IsInf )
  renaming ( _≤_ to _≤ᴮ_ ; isProp≤ to isProp≤ᴮ )

-- The bridge between the Boolean order and entailment of subsets. Every law is
-- proved as an entailment and shipped as an order fact through this pair.

≤ᴮ-from : (U V : Reg) → fst U ⊑ fst V → U ≤ᴮ V
≤ᴮ-from U V h = Reg≡ (U ⊓ᴮ V) U (λ q z → fst z) (λ q x → x , h q x)

≤ᴮ-to : (U V : Reg) → U ≤ᴮ V → fst U ⊑ fst V
≤ᴮ-to U V e q x = snd (Reg⊑ U (U ⊓ᴮ V) (sym e) q x)

⊓ᴮ-comm : (U V : Reg) → (U ⊓ᴮ V) ≡ (V ⊓ᴮ U)
⊓ᴮ-comm U V = Reg≡ (U ⊓ᴮ V) (V ⊓ᴮ U)
  (λ q z → snd z , fst z) (λ q z → snd z , fst z)

⊓ᴮ-assoc : (U V W : Reg) → ((U ⊓ᴮ V) ⊓ᴮ W) ≡ (U ⊓ᴮ (V ⊓ᴮ W))
⊓ᴮ-assoc U V W = Reg≡ ((U ⊓ᴮ V) ⊓ᴮ W) (U ⊓ᴮ (V ⊓ᴮ W))
  (λ q z → fst (fst z) , (snd (fst z) , snd z))
  (λ q z → (fst z , fst (snd z)) , snd (snd z))

⊓ᴮ-idem : (U : Reg) → (U ⊓ᴮ U) ≡ U
⊓ᴮ-idem U = Reg≡ (U ⊓ᴮ U) U (λ q z → fst z) (λ q x → x , x)

⊔ᴮ-comm : (U V : Reg) → (U ⊔ᴮ V) ≡ (V ⊔ᴮ U)
⊔ᴮ-comm U V = Reg≡ (U ⊔ᴮ V) (V ⊔ᴮ U)
  (⊔ᴮ-least U V (V ⊔ᴮ U) (⊔ᴮ-inr V U) (⊔ᴮ-inl V U))
  (⊔ᴮ-least V U (U ⊔ᴮ V) (⊔ᴮ-inr U V) (⊔ᴮ-inl U V))

⊔ᴮ-assoc : (U V W : Reg) → ((U ⊔ᴮ V) ⊔ᴮ W) ≡ (U ⊔ᴮ (V ⊔ᴮ W))
⊔ᴮ-assoc U V W = Reg≡ ((U ⊔ᴮ V) ⊔ᴮ W) (U ⊔ᴮ (V ⊔ᴮ W)) fwd bwd
  where
  fwd : fst ((U ⊔ᴮ V) ⊔ᴮ W) ⊑ fst (U ⊔ᴮ (V ⊔ᴮ W))
  fwd = ⊔ᴮ-least (U ⊔ᴮ V) W (U ⊔ᴮ (V ⊔ᴮ W))
    (⊔ᴮ-least U V (U ⊔ᴮ (V ⊔ᴮ W))
      (⊔ᴮ-inl U (V ⊔ᴮ W))
      (⊑-trans (fst V) (fst (V ⊔ᴮ W)) (fst (U ⊔ᴮ (V ⊔ᴮ W)))
        (⊔ᴮ-inl V W) (⊔ᴮ-inr U (V ⊔ᴮ W))))
    (⊑-trans (fst W) (fst (V ⊔ᴮ W)) (fst (U ⊔ᴮ (V ⊔ᴮ W)))
      (⊔ᴮ-inr V W) (⊔ᴮ-inr U (V ⊔ᴮ W)))
  bwd : fst (U ⊔ᴮ (V ⊔ᴮ W)) ⊑ fst ((U ⊔ᴮ V) ⊔ᴮ W)
  bwd = ⊔ᴮ-least U (V ⊔ᴮ W) ((U ⊔ᴮ V) ⊔ᴮ W)
    (⊑-trans (fst U) (fst (U ⊔ᴮ V)) (fst ((U ⊔ᴮ V) ⊔ᴮ W))
      (⊔ᴮ-inl U V) (⊔ᴮ-inl (U ⊔ᴮ V) W))
    (⊔ᴮ-least V W ((U ⊔ᴮ V) ⊔ᴮ W)
      (⊑-trans (fst V) (fst (U ⊔ᴮ V)) (fst ((U ⊔ᴮ V) ⊔ᴮ W))
        (⊔ᴮ-inr U V) (⊔ᴮ-inl (U ⊔ᴮ V) W))
      (⊔ᴮ-inr (U ⊔ᴮ V) W))

⊔ᴮ-idem : (U : Reg) → (U ⊔ᴮ U) ≡ U
⊔ᴮ-idem U = Reg≡ (U ⊔ᴮ U) U
  (⊔ᴮ-least U U U (⊑-refl (fst U)) (⊑-refl (fst U))) (⊔ᴮ-inl U U)

⊓ᴮ-absorb : (U V : Reg) → (U ⊓ᴮ (U ⊔ᴮ V)) ≡ U
⊓ᴮ-absorb U V = Reg≡ (U ⊓ᴮ (U ⊔ᴮ V)) U
  (λ q z → fst z) (λ q x → x , ⊔ᴮ-inl U V q x)

⊔ᴮ-absorb : (U V : Reg) → (U ⊔ᴮ (U ⊓ᴮ V)) ≡ U
⊔ᴮ-absorb U V = Reg≡ (U ⊔ᴮ (U ⊓ᴮ V)) U
  (⊔ᴮ-least U (U ⊓ᴮ V) U (⊑-refl (fst U)) (⊓ᴮ-fst U V))
  (⊔ᴮ-inl U (U ⊓ᴮ V))

⊓ᴮ-⊔ᴮ-dist : (U V W : Reg) → (U ⊓ᴮ (V ⊔ᴮ W)) ≡ ((U ⊓ᴮ V) ⊔ᴮ (U ⊓ᴮ W))
⊓ᴮ-⊔ᴮ-dist U V W = Reg≡ (U ⊓ᴮ (V ⊔ᴮ W)) ((U ⊓ᴮ V) ⊔ᴮ (U ⊓ᴮ W)) fwd bwd
  where
  target : Reg
  target = (U ⊓ᴮ V) ⊔ᴮ (U ⊓ᴮ W)
  branch : (q : Cond) → ⟨ fst U q ⟩ → ⟨ fst V q ⟩ ⊎ ⟨ fst W q ⟩
         → ⟨ fst target q ⟩
  branch q x (inl y) = ⊔ᴮ-inl (U ⊓ᴮ V) (U ⊓ᴮ W) q (x , y)
  branch q x (inr y) = ⊔ᴮ-inr (U ⊓ᴮ V) (U ⊓ᴮ W) q (x , y)
  step : ((fst U) ∩ ((fst V) ∪ (fst W))) ⊑ fst target
  step q z = PT.rec (snd (fst target q)) (branch q (fst z)) (snd z)
  fwd : fst (U ⊓ᴮ (V ⊔ᴮ W)) ⊑ fst target
  fwd = ⊑-trans ((fst U) ∩ ((((fst V) ∪ (fst W)) ⋆) ⋆))
                ((((fst U) ∩ ((fst V) ∪ (fst W))) ⋆) ⋆)
                (fst target)
    (⊓-⋆⋆-dist (fst U) (regDown U) ((fst V) ∪ (fst W)))
    (⋆⋆-least ((fst U) ∩ ((fst V) ∪ (fst W))) (fst target) (snd target) step)
  bwd : fst target ⊑ fst (U ⊓ᴮ (V ⊔ᴮ W))
  bwd = ⊔ᴮ-least (U ⊓ᴮ V) (U ⊓ᴮ W) (U ⊓ᴮ (V ⊔ᴮ W))
    (⊓ᴮ-greatest U (V ⊔ᴮ W) (U ⊓ᴮ V) (⊓ᴮ-fst U V)
      (⊑-trans (fst (U ⊓ᴮ V)) (fst V) (fst (V ⊔ᴮ W))
        (⊓ᴮ-snd U V) (⊔ᴮ-inl V W)))
    (⊓ᴮ-greatest U (V ⊔ᴮ W) (U ⊓ᴮ W) (⊓ᴮ-fst U W)
      (⊑-trans (fst (U ⊓ᴮ W)) (fst W) (fst (V ⊔ᴮ W))
        (⊓ᴮ-snd U W) (⊔ᴮ-inr V W)))

⊤ᴮ-unit : (U : Reg) → (U ⊓ᴮ ⊤ᴮ) ≡ U
⊤ᴮ-unit U = Reg≡ (U ⊓ᴮ ⊤ᴮ) U (λ q z → fst z) (λ q x → x , tt*)

⊥ᴮ-unit : (U : Reg) → (U ⊔ᴮ ⊥ᴮ) ≡ U
⊥ᴮ-unit U = Reg≡ (U ⊔ᴮ ⊥ᴮ) U
  (⊔ᴮ-least U ⊥ᴮ U (⊑-refl (fst U)) (λ q x → Empty.rec* x))
  (⊔ᴮ-inl U ⊥ᴮ)

-- A regular subset is disjoint from its own pseudocomplement: a condition in
-- both refutes itself at the refinement q ≼ q.

¬ᴮ-⊓ᴮ : (U : Reg) → (U ⊓ᴮ (¬ᴮ U)) ≡ ⊥ᴮ
¬ᴮ-⊓ᴮ U = Reg≡ (U ⊓ᴮ (¬ᴮ U)) ⊥ᴮ
  (λ q z → snd z q (≼-refl q) (fst z)) (λ q x → Empty.rec* x)

-- Excluded middle holds IN the algebra without holding in the metatheory. This
-- is the whole point of the regular-element definition. A condition refuting
-- the saturated join of U and its pseudocomplement refutes itself, because
-- anything refuting every refinement inside U IS a member of U ⋆.

¬ᴮ-⊔ᴮ : (U : Reg) → (U ⊔ᴮ (¬ᴮ U)) ≡ ⊤ᴮ
¬ᴮ-⊔ᴮ U = Reg≡ (U ⊔ᴮ (¬ᴮ U)) ⊤ᴮ (λ q _ → tt*) (λ q _ → excl q)
  where
  excl : (q : Cond) → ⟨ fst (U ⊔ᴮ (¬ᴮ U)) q ⟩
  excl q = λ r r≼q y →
    y r (≼-refl r) (Logic.inr (λ s s≼r us → y s s≼r (Logic.inl us)))

⇒ᴮ-curry : (U V W : Reg) → (U ⊓ᴮ V) ≤ᴮ W → U ≤ᴮ (V ⇒ᴮ W)
⇒ᴮ-curry U V W h = ≤ᴮ-from U (V ⇒ᴮ W)
  (λ q x r r≼q v → ≤ᴮ-to (U ⊓ᴮ V) W h r (regDown U q r r≼q x , v))

⇒ᴮ-uncurry : (U V W : Reg) → U ≤ᴮ (V ⇒ᴮ W) → (U ⊓ᴮ V) ≤ᴮ W
⇒ᴮ-uncurry U V W h = ≤ᴮ-from (U ⊓ᴮ V) W
  (λ q z → ≤ᴮ-to U (V ⇒ᴮ W) h q (fst z) q (≼-refl q) (snd z))

roLaws : BooleanLaws
roLaws = record
  { ⊓-comm    = ⊓ᴮ-comm
  ; ⊓-assoc   = ⊓ᴮ-assoc
  ; ⊓-idem    = ⊓ᴮ-idem
  ; ⊔-comm    = ⊔ᴮ-comm
  ; ⊔-assoc   = ⊔ᴮ-assoc
  ; ⊔-idem    = ⊔ᴮ-idem
  ; ⊓-absorb  = ⊓ᴮ-absorb
  ; ⊔-absorb  = ⊔ᴮ-absorb
  ; ⊓-⊔-dist  = ⊓ᴮ-⊔ᴮ-dist
  ; ⊤-unit    = ⊤ᴮ-unit
  ; ⊥-unit    = ⊥ᴮ-unit
  ; ¬-⊓       = ¬ᴮ-⊓ᴮ
  ; ¬-⊔       = ¬ᴮ-⊔ᴮ
  ; ⇒-curry   = ⇒ᴮ-curry
  ; ⇒-uncurry = ⇒ᴮ-uncurry }

-- Completeness for HOST families, which this algebra genuinely has and which
-- the model-internal algebra of M8 genuinely does not. Never transport this
-- record along any map into a coded algebra.

roComplete : CompleteHost
roComplete = record { ⋁-sup = sup ; ⋀-inf = inf }
  where
  sup : (A : Type ℓ) (f : A → Reg) → IsSup f (⋁ᴮ A f)
  sup A f = (λ a → ≤ᴮ-from (f a) (⋁ᴮ A f) (⋁ᴮ-ub A f a))
          , (λ W ub → ≤ᴮ-from (⋁ᴮ A f) W
              (⋁ᴮ-least A f W (λ a → ≤ᴮ-to (f a) W (ub a))))
  inf : (A : Type ℓ) (f : A → Reg) → IsInf f (⋀ᴮ A f)
  inf A f = (λ a → ≤ᴮ-from (⋀ᴮ A f) (f a) (⋀ᴮ-lb A f a))
          , (λ W lb → ≤ᴮ-from W (⋀ᴮ A f)
              (⋀ᴮ-greatest A f W (λ a → ≤ᴮ-to W (f a) (lb a))))

-- Nondegeneracy is NOT free: it fails for the empty forcing notion, where Reg
-- has exactly one element. It is delivered as a function of a condition rather
-- than as a theorem, which is why mere inhabitation of Cond is not a parameter
-- of this module: nothing else in it needs one.

roNondegenerate : Cond → Nondegenerate
roNondegenerate p =
  record { ⊥≢⊤ = λ e → Empty.rec* (Reg⊑ ⊤ᴮ ⊥ᴮ (sym e) p tt*) }

--------------------------------------------------------------------------------
-- 8. The completion map and its constructive laws
--------------------------------------------------------------------------------

-- THE trap of this module. i p is the double pseudocomplement of the cone of
-- p, never the cone itself; see the header and architecture section 5, N8.

i : Cond → Reg
i p = (((↓ᶜ p) ⋆) ⋆) , ⋆-regular ((↓ᶜ p) ⋆) (⋆-down (↓ᶜ p))

i-cone : (p : Cond) → (↓ᶜ p) ⊑ fst (i p)
i-cone p = ⋆⋆-unit (↓ᶜ p) (↓ᶜ-down p)

i-self : (p : Cond) → ⟨ fst (i p) p ⟩
i-self p = i-cone p p (≼-refl p)

-- The pseudocomplement of a cone IS incompatibility with its condition, in
-- both directions and constructively. Every theorem below goes through this
-- pair rather than unfolding a regular-open membership by hand.

cone⋆ : (p r : Cond) → ⟨ ((↓ᶜ p) ⋆) r ⟩ → ⟨ incompatible r p ⟩
cone⋆ p r y = PT.rec isProp⊥* (λ z → y (fst z) (fst (snd z)) (snd (snd z)))

⋆cone : (p r : Cond) → ⟨ incompatible r p ⟩ → ⟨ ((↓ᶜ p) ⋆) r ⟩
⋆cone p r n = λ s s≼r s≼p → n ∣ s , s≼r , s≼p ∣₁

i-mono⊑ : (p q : Cond) → ⟨ q ≼ p ⟩ → fst (i q) ⊑ fst (i p)
i-mono⊑ p q q≼p = ⋆⋆-mono (↓ᶜ q) (↓ᶜ p) (λ r r≼q → ≼-trans r≼q q≼p)

i-mono : (p q : Cond) → ⟨ q ≼ p ⟩ → i q ≤ᴮ i p
i-mono p q q≼p = ≤ᴮ-from (i q) (i p) (i-mono⊑ p q q≼p)

positiveᴮ : Reg → Ω
positiveᴮ U = ⋁ Cond (λ q → fst U q)

i-pos : (p : Cond) → ⟨ positiveᴮ (i p) ⟩
i-pos p = ∣ p , i-self p ∣₁

i-compat→ : (p q : Cond) → ⟨ compatible p q ⟩ → ⟨ positiveᴮ (i p ⊓ᴮ i q) ⟩
i-compat→ p q = PT.map step
  where
  step : Σ[ r ∈ Cond ] (⟨ r ≼ p ⟩ × ⟨ r ≼ q ⟩)
       → Σ[ r ∈ Cond ] (⟨ fst (i p) r ⟩ × ⟨ fst (i q) r ⟩)
  step (r , r≼p , r≼q) = r , i-cone p r r≼p , i-cone q r r≼q

-- Density of the image of i, in the form Bell's Lemma 2.3 proof consumes. The
-- content is the first lemma: a condition inside a regular U drags the whole
-- regularized cone of that condition inside U.

i-below : (p : Cond) (U : Reg) → ⟨ fst U p ⟩ → fst (i p) ⊑ fst U
i-below p U h = ⋆⋆-least (↓ᶜ p) (fst U) (snd U)
  (λ r r≼p → regDown U p r r≼p h)

i-below≤ : (p : Cond) (U : Reg) → ⟨ fst U p ⟩ → i p ≤ᴮ U
i-below≤ p U h = ≤ᴮ-from (i p) U (i-below p U h)

-- The index of this ⋁ is the SMALL entailment, not the Boolean order: the
-- Boolean order lives in Type (ℓ-suc ℓ) and cannot be the carrier of an
-- hProp ℓ. See the report, architecture correction B.

i-dense : (U : Reg) → ⟨ positiveᴮ U ⟩
        → ⟨ ⋁ Cond (λ p → (fst (i p) ⊑ fst U) , isProp⊑ (fst (i p)) (fst U)) ⟩
i-dense U = PT.map step
  where
  step : Σ[ p ∈ Cond ] ⟨ fst U p ⟩ → Σ[ p ∈ Cond ] (fst (i p) ⊑ fst U)
  step (p , h) = p , i-below p U h

-- The kernel. Constructively it is equality of the two INCOMPATIBILITY
-- relations, which is what the ⋆-calculus computes; Bell's separative equality
-- is the classical reading of the same fact and is delivered under LEM in
-- section 9.

i-kernel→ : (p q : Cond) → i p ≡ i q → ⟨ weaklyEqual p q ⟩
i-kernel→ p q e r = to , from
  where
  to : ⟨ incompatible r p ⟩ → ⟨ incompatible r q ⟩
  to n = cone⋆ q r
    (snd (⋆-regular (↓ᶜ q) (↓ᶜ-down q) r)
      (⋆-anti (fst (i q)) (fst (i p)) (Reg⊑ (i q) (i p) (sym e)) r
        (⋆⋆-unit ((↓ᶜ p) ⋆) (⋆-down (↓ᶜ p)) r (⋆cone p r n))))
  from : ⟨ incompatible r q ⟩ → ⟨ incompatible r p ⟩
  from n = cone⋆ p r
    (snd (⋆-regular (↓ᶜ p) (↓ᶜ-down p) r)
      (⋆-anti (fst (i p)) (fst (i q)) (Reg⊑ (i p) (i q) e) r
        (⋆⋆-unit ((↓ᶜ q) ⋆) (⋆-down (↓ᶜ q)) r (⋆cone q r n))))

i-kernel← : (p q : Cond) → ⟨ weaklyEqual p q ⟩ → i p ≡ i q
i-kernel← p q h = Reg≡ (i p) (i q)
  (⋆-anti ((↓ᶜ q) ⋆) ((↓ᶜ p) ⋆)
    (λ r y → ⋆cone p r (snd (h r) (cone⋆ q r y))))
  (⋆-anti ((↓ᶜ p) ⋆) ((↓ᶜ q) ⋆)
    (λ r y → ⋆cone q r (fst (h r) (cone⋆ p r y))))

-- The two sides sit at different universe levels, ℓ-suc ℓ on the left and ℓ
-- on the right. That is not an obstruction: the library's propBiimpl→Equiv is
-- level polymorphic in both arguments, measured, see the report.

i-kernel : (p q : Cond) → (i p ≡ i q) ≃ ⟨ weaklyEqual p q ⟩
i-kernel p q = propBiimpl→Equiv (isSetReg (i p) (i q)) (snd (weaklyEqual p q))
  (i-kernel→ p q) (i-kernel← p q)

--------------------------------------------------------------------------------
-- 9. The classical theorems
--------------------------------------------------------------------------------

-- MEASURED CORRECTION. The architecture charges LEM ℓ for this theorem. It
-- does not need it: the backward direction builds a member of U ⋆ ⋆ directly
-- out of the density hypothesis and then spends regularity, and the forward
-- direction is downward closure plus ≼-refl. A dead hypothesis would make the
-- ledger lie, so it is not taken.

regular-denseBelow : (U : Sub) → ⟨ isRegular U ⟩ → (q : Cond)
                   → U q ≡ denseBelow q U
regular-denseBelow U reg q = ⇔toPath fwd bwd
  where
  fwd : ⟨ U q ⟩ → ⟨ denseBelow q U ⟩
  fwd u s s≼q = ∣ s , regular-down U reg q s s≼q u , ≼-refl s ∣₁
  bwd : ⟨ denseBelow q U ⟩ → ⟨ U q ⟩
  bwd d = regular-⊒ U reg q
    (λ r r≼q y → PT.rec isProp⊥*
      (λ z → y (fst z) (snd (snd z)) (fst (snd z))) (d r r≼q))

regular-denseBelow-carrier : (U : Sub) → ⟨ isRegular U ⟩ → (q : Cond)
                           → ⟨ U q ⟩ ≡ ⟨ denseBelow q U ⟩
regular-denseBelow-carrier U reg q =
  cong (λ P → ⟨ P ⟩) (regular-denseBelow U reg q)

-- Bell's displayed formula (1) at fulltext:3456-3457, and the form K5 and K8
-- consume so that no application proof unfolds a regular-open membership. LEM
-- is genuinely spent here, and only in the forward direction: the ⋆-calculus
-- computes a DOUBLE NEGATION of compatibility, and nothing weaker than
-- excluded middle removes it.

i-bell→ : LEM ℓ → (p q : Cond) → ⟨ fst (i p) q ⟩
        → (r : Cond) → ⟨ r ≼ q ⟩ → ⟨ compatible p r ⟩
i-bell→ lem p q x r r≼q = go (lem (compatible p r))
  where
  go : ⟨ compatible p r ⟩ ⊎ (⟨ compatible p r ⟩ → Empty.⊥)
     → ⟨ compatible p r ⟩
  go (inl c) = c
  go (inr n) =
    Empty.rec* (x r r≼q (λ s s≼r s≼p → Empty.rec (n ∣ s , s≼p , s≼r ∣₁)))

i-bell← : (p q : Cond) → ((r : Cond) → ⟨ r ≼ q ⟩ → ⟨ compatible p r ⟩)
        → ⟨ fst (i p) q ⟩
i-bell← p q h = λ r r≼q y →
  PT.rec isProp⊥* (λ z → y (fst z) (snd (snd z)) (fst (snd z))) (h r r≼q)

i-as-Bell : LEM ℓ → (p q : Cond)
          → fst (i p) q ≡ ⋀ Cond (λ r → (r ≼ q) ⇒ compatible p r)
i-as-Bell lem p q = ⇔toPath (i-bell→ lem p q) (i-bell← p q)

i-as-Bell-carrier : LEM ℓ → (p q : Cond)
                  → ⟨ fst (i p) q ⟩
                  ≡ ⟨ ⋀ Cond (λ r → (r ≼ q) ⇒ compatible p r) ⟩
i-as-Bell-carrier lem p q = cong (λ P → ⟨ P ⟩) (i-as-Bell lem p q)

-- The converse of i-compat→. This is the half of Bell's Problem 2.4(iii)
-- contract that costs LEM, and it is why M9's certificate carries i-compat←
-- as a field rather than deriving it.

i-compat← : LEM ℓ → (p q : Cond) → ⟨ positiveᴮ (i p ⊓ᴮ i q) ⟩
          → ⟨ compatible p q ⟩
i-compat← lem p q = PT.rec (snd (compatible p q)) outer
  where
  outer : Σ[ r ∈ Cond ] (⟨ fst (i p) r ⟩ × ⟨ fst (i q) r ⟩)
        → ⟨ compatible p q ⟩
  outer (r , xp , xq) =
    PT.rec (snd (compatible p q)) middle (i-bell→ lem p r xp r (≼-refl r))
    where
    middle : Σ[ t ∈ Cond ] (⟨ t ≼ p ⟩ × ⟨ t ≼ r ⟩) → ⟨ compatible p q ⟩
    middle (t , t≼p , t≼r) =
      PT.rec (snd (compatible p q)) inner (i-bell→ lem q r xq t t≼r)
      where
      inner : Σ[ w ∈ Cond ] (⟨ w ≼ q ⟩ × ⟨ w ≼ t ⟩) → ⟨ compatible p q ⟩
      inner (w , w≼q , w≼t) = ∣ w , ≼-trans w≼t t≼p , w≼q ∣₁

-- positive is primitive and nonzero is the derived classical notion. Only the
-- backward direction costs LEM.

positive→nonzero : (U : Reg) → ⟨ positiveᴮ U ⟩ → (U ≡ ⊥ᴮ) → Empty.⊥
positive→nonzero U pos e =
  PT.rec Empty.isProp⊥ (λ z → Empty.rec* (Reg⊑ U ⊥ᴮ e (fst z) (snd z))) pos

nonzero→positive : LEM ℓ → (U : Reg) → ((U ≡ ⊥ᴮ) → Empty.⊥)
                 → ⟨ positiveᴮ U ⟩
nonzero→positive lem U nz = go (lem (positiveᴮ U))
  where
  go : ⟨ positiveᴮ U ⟩ ⊎ (⟨ positiveᴮ U ⟩ → Empty.⊥) → ⟨ positiveᴮ U ⟩
  go (inl x) = x
  go (inr n) = Empty.rec (nz (Reg≡ U ⊥ᴮ
    (λ q x → Empty.rec (n ∣ q , x ∣₁)) (λ q x → Empty.rec* x)))

positive↔nonzero : LEM ℓ → (U : Reg)
                 → ⟨ positiveᴮ U ⟩ ≃ ((U ≡ ⊥ᴮ) → Empty.⊥)
positive↔nonzero lem U = propBiimpl→Equiv
  (snd (positiveᴮ U)) (isPropΠ (λ _ → Empty.isProp⊥))
  (positive→nonzero U) (nonzero→positive lem U)

-- The classical reading of the kernel. Under LEM the incompatibility form of
-- section 8 is Bell's separative equality; constructively it is strictly
-- weaker, and that gap is a measured correction to the architecture.

separative→weak : (p q : Cond) → ⟨ separativelyEqual p q ⟩
                → ⟨ weaklyEqual p q ⟩
separative→weak p q h r =
    (λ n c → n (snd (h r) c))
  , (λ n c → n (fst (h r) c))

weak→separative : LEM ℓ → (p q : Cond) → ⟨ weaklyEqual p q ⟩
                → ⟨ separativelyEqual p q ⟩
weak→separative lem p q h r = to , from
  where
  to : ⟨ compatible r p ⟩ → ⟨ compatible r q ⟩
  to c = go (lem (compatible r q))
    where
    go : ⟨ compatible r q ⟩ ⊎ (⟨ compatible r q ⟩ → Empty.⊥)
       → ⟨ compatible r q ⟩
    go (inl d) = d
    go (inr n) = Empty.rec* (snd (h r) (λ d → Empty.rec (n d)) c)
  from : ⟨ compatible r q ⟩ → ⟨ compatible r p ⟩
  from c = go (lem (compatible r p))
    where
    go : ⟨ compatible r p ⟩ ⊎ (⟨ compatible r p ⟩ → Empty.⊥)
       → ⟨ compatible r p ⟩
    go (inl d) = d
    go (inr n) = Empty.rec* (fst (h r) (λ d → Empty.rec (n d)) c)

i-kernel-separative : LEM ℓ → (p q : Cond)
                    → (i p ≡ i q) ≃ ⟨ separativelyEqual p q ⟩
i-kernel-separative lem p q = propBiimpl→Equiv
  (isSetReg (i p) (i q)) (snd (separativelyEqual p q))
  (λ e → weak→separative lem p q (i-kernel→ p q e))
  (λ h → i-kernel← p q (separative→weak p q h))

--------------------------------------------------------------------------------
-- 10. The three adapters
--------------------------------------------------------------------------------

-- On a separative (Bell: refined) presentation the regularized cone collapses
-- to the bare cone, which is Bell's Lemma 2.1(i) read in this direction. The
-- forward map is the adapter that the other two use.

i-bare→ : LEM ℓ → separative → (p q : Cond) → ⟨ fst (i p) q ⟩ → ⟨ q ≼ p ⟩
i-bare→ lem sep p q x = go (lem (q ≼ p))
  where
  step : Σ[ r ∈ Cond ] (⟨ r ≼ q ⟩ × ⟨ incompatible r p ⟩) → ⟨ ⊥ ⟩
  step (r , r≼q , inc) = x r r≼q (⋆cone p r inc)
  go : ⟨ q ≼ p ⟩ ⊎ (⟨ q ≼ p ⟩ → Empty.⊥) → ⟨ q ≼ p ⟩
  go (inl h) = h
  go (inr n) =
    Empty.rec* (PT.rec isProp⊥* step (sep p q (λ h → Empty.rec (n h))))

separative→i-bare : LEM ℓ → separative → (p q : Cond)
                  → fst (i p) q ≡ (q ≼ p)
separative→i-bare lem sep p q = ⇔toPath (i-bare→ lem sep p q) (i-cone p q)

separative→i-bare-carrier : LEM ℓ → separative → (p q : Cond)
                          → ⟨ fst (i p) q ⟩ ≡ ⟨ q ≼ p ⟩
separative→i-bare-carrier lem sep p q =
  cong (λ P → ⟨ P ⟩) (separative→i-bare lem sep p q)

separative→reflect : LEM ℓ → separative → (p q : Cond)
                   → i q ≤ᴮ i p → ⟨ q ≼ p ⟩
separative→reflect lem sep p q h =
  i-bare→ lem sep p q (≤ᴮ-to (i q) (i p) h q (i-self q))

-- Injectivity needs separativity AND antisymmetry. Neither implies the other,
-- and the K0 four-condition example fails antisymmetry while satisfying
-- refinement (architecture section 5, N5).

i-injective : LEM ℓ → separative → antisymmetric → (p q : Cond)
            → i p ≡ i q → p ≡ q
i-injective lem sep anti p q e =
  anti p q (i-bare→ lem sep q p (Reg⊑ (i p) (i q) e p (i-self p)))
           (i-bare→ lem sep p q (Reg⊑ (i q) (i p) (sym e) q (i-self q)))
