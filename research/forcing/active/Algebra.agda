{-# OPTIONS --cubical --safe --guardedness #-}

-- K2 Track B: the law-bearing Boolean interface.
--
-- The audit's constraint 1 is that TruthAlgebra stays the evaluator signature
-- and does not change: FOL.Semantics and FOL.ZFStructure take it as a module
-- parameter (src/FOL/Semantics.lagda.md:34, src/FOL/ZFStructure.lagda.md:61)
-- and the whole existing development is written against it. So the Boolean
-- laws live in a SEPARATE record, parameterized by a TruthAlgebra value and
-- never containing one. The tree's precedent for a law record over a data
-- record is FOL.ZFModel (src/FOL/ZFModel.lagda.md:38).
--
-- Three design points, each of which was a named trap.
--
-- 1. The order is DERIVED, a ≤ b = a ⊓ b ≡ a, and is not a field. isSetΩ is
--    already a field of TruthAlgebra (src/Base/Truth.lagda.md:76), so the
--    derived order is automatically a proposition and there is nothing to
--    state about its coherence with the meet. The K0 probe's shape, where
--    _≤ᴮ_ was an inductive family with no proved link to _∧ᴮ_
--    (dev/literature/k0-probe-evidence-2026-09.md:473-479), is what this
--    avoids.
-- 2. Nothing here imports Cubical.Algebra.*. The library's only Boolean
--    algebra is inside Cubical/Algebra/BooleanRing/, where join and meet come
--    from ring operations and there is no order and no infinitary join, and
--    Cubical/Algebra/Lattice/Base.agda:34-35 is single level and finite.
--    The lattice vocabulary below is therefore the tree's first.
-- 3. CompleteHost is for the two algebras that genuinely have host-indexed
--    suprema: hPropAlgebra and the host regular-open algebra of M4. It must
--    NEVER be applied to the model-internal coded algebra of M8, whose
--    suprema exist only for coded families; completeness over arbitrary host
--    families is exactly what the project has ruled out.
--
-- Hypotheses: the records and module BooleanTheory take none. LEM ℓ appears
-- once, as an explicit argument of the hProp instance's complement law, and
-- nowhere else.

module Algebra where

open import Base.Prelude
open import Base.Truth using ( TruthAlgebra; hPropAlgebra )
open import Base.Classical using ( LEM )

open import Cubical.Data.Sum using ( _⊎_ ) renaming ( inl to inl⊎ ; inr to inr⊎ )
open import Cubical.Data.Unit using ( tt* )
import Cubical.Data.Empty as Empty
import Cubical.Functions.Logic as Logic
import Cubical.HITs.PropositionalTruncation as PT
open PT using ( ∣_∣₁ )

-- The interface, over an arbitrary evaluator signature.

module BooleanAlgebra {ℓ ℓ'} (𝕋 : TruthAlgebra ℓ ℓ') where
  open TruthAlgebra 𝕋 public

  infix 4 _≤_

  -- The order and its propositionality. isSetΩ is the whole proof.

  _≤_ : Ω → Ω → Type ℓ'
  a ≤ b = a ⊓ b ≡ a

  isProp≤ : (a b : Ω) → isProp (a ≤ b)
  isProp≤ a b = isSetΩ (a ⊓ b) a

  -- Fifteen fields and no more. ⇒-def, ¬-invol, both De Morgan laws,
  -- antisymmetry, monotonicity and ¬-as-⇒⊥ are theorems below, not fields.
  -- The two implication fields are the adjunction (_ ⊓ b) ⊣ (b ⇒ _), which is
  -- what the evaluator's implication clause actually needs; the equation
  -- a ⇒ b ≡ ¬ a ⊔ b is then forced.

  record BooleanLaws : Type ℓ' where
    field
      ⊓-comm    : (a b : Ω) → (a ⊓ b) ≡ (b ⊓ a)
      ⊓-assoc   : (a b c : Ω) → ((a ⊓ b) ⊓ c) ≡ (a ⊓ (b ⊓ c))
      ⊓-idem    : (a : Ω) → (a ⊓ a) ≡ a
      ⊔-comm    : (a b : Ω) → (a ⊔ b) ≡ (b ⊔ a)
      ⊔-assoc   : (a b c : Ω) → ((a ⊔ b) ⊔ c) ≡ (a ⊔ (b ⊔ c))
      ⊔-idem    : (a : Ω) → (a ⊔ a) ≡ a
      ⊓-absorb  : (a b : Ω) → (a ⊓ (a ⊔ b)) ≡ a
      ⊔-absorb  : (a b : Ω) → (a ⊔ (a ⊓ b)) ≡ a
      ⊓-⊔-dist  : (a b c : Ω) → (a ⊓ (b ⊔ c)) ≡ ((a ⊓ b) ⊔ (a ⊓ c))
      ⊤-unit    : (a : Ω) → (a ⊓ ⊤) ≡ a
      ⊥-unit    : (a : Ω) → (a ⊔ ⊥) ≡ a
      ¬-⊓       : (a : Ω) → (a ⊓ (¬ a)) ≡ ⊥
      ¬-⊔       : (a : Ω) → (a ⊔ (¬ a)) ≡ ⊤
      ⇒-curry   : (a b c : Ω) → (a ⊓ b) ≤ c → a ≤ (b ⇒ c)
      ⇒-uncurry : (a b c : Ω) → a ≤ (b ⇒ c) → (a ⊓ b) ≤ c

  -- The degenerate one-element algebra is excluded, the two-element one kept.
  -- The host empty type is the target because Ω is an arbitrary Type ℓ' here
  -- and carries no ⟨_⟩; and the algebra's own ¬_ is not used, because a
  -- refutation of a host path is not a truth value of the algebra.

  record Nondegenerate : Type ℓ' where
    field
      ⊥≢⊤ : ⊥ ≡ ⊤ → Empty.⊥

  -- Bounds for a family. The index type is a Type ℓ, matching the index of
  -- the algebra's own ⋀ and ⋁ (src/Base/Truth.lagda.md:91).

  IsUpper : {A : Type ℓ} → (A → Ω) → Ω → Type (ℓ-max ℓ ℓ')
  IsUpper {A = A} f a = (x : A) → f x ≤ a

  IsLower : {A : Type ℓ} → (A → Ω) → Ω → Type (ℓ-max ℓ ℓ')
  IsLower {A = A} f a = (x : A) → a ≤ f x

  IsSup : {A : Type ℓ} → (A → Ω) → Ω → Type (ℓ-max ℓ ℓ')
  IsSup f a = IsUpper f a × ((b : Ω) → IsUpper f b → a ≤ b)

  IsInf : {A : Type ℓ} → (A → Ω) → Ω → Type (ℓ-max ℓ ℓ')
  IsInf f a = IsLower f a × ((b : Ω) → IsLower f b → b ≤ a)

  -- Host completeness: the algebra's own ⋁ and ⋀ really are the supremum and
  -- infimum of every host family. Never assert this of a coded algebra.

  record CompleteHost : Type (ℓ-max (ℓ-suc ℓ) ℓ') where
    field
      ⋁-sup : (A : Type ℓ) (f : A → Ω) → IsSup f (⋁ A f)
      ⋀-inf : (A : Type ℓ) (f : A → Ω) → IsInf f (⋀ A f)

  -- Everything the laws force.

  module BooleanTheory (bl : BooleanLaws) where
    open BooleanLaws bl public

    -- The derived order is a partial order.

    ≤-refl : (a : Ω) → a ≤ a
    ≤-refl = ⊓-idem

    ≤-trans : (a b c : Ω) → a ≤ b → b ≤ c → a ≤ c
    ≤-trans a b c p q =
      cong (_⊓ c) (sym p) ∙ ⊓-assoc a b c ∙ cong (a ⊓_) q ∙ p

    ≤-antisym : (a b : Ω) → a ≤ b → b ≤ a → a ≡ b
    ≤-antisym a b p q = sym p ∙ ⊓-comm a b ∙ q

    -- Meet is the greatest lower bound, join the least upper bound.

    ⊓-≤-l : (a b : Ω) → (a ⊓ b) ≤ a
    ⊓-≤-l a b =
      ⊓-assoc a b a ∙ cong (a ⊓_) (⊓-comm b a) ∙ sym (⊓-assoc a a b)
        ∙ cong (_⊓ b) (⊓-idem a)

    ⊓-≤-r : (a b : Ω) → (a ⊓ b) ≤ b
    ⊓-≤-r a b = ⊓-assoc a b b ∙ cong (a ⊓_) (⊓-idem b)

    ⊓-greatest : (a b c : Ω) → c ≤ a → c ≤ b → c ≤ (a ⊓ b)
    ⊓-greatest a b c p q = sym (⊓-assoc c a b) ∙ cong (_⊓ b) p ∙ q

    ≤-⊔-l : (a b : Ω) → a ≤ (a ⊔ b)
    ≤-⊔-l = ⊓-absorb

    ≤-⊔-r : (a b : Ω) → b ≤ (a ⊔ b)
    ≤-⊔-r a b = cong (b ⊓_) (⊔-comm a b) ∙ ⊓-absorb b a

    ⊔-least : (a b c : Ω) → a ≤ c → b ≤ c → (a ⊔ b) ≤ c
    ⊔-least a b c p q =
      ⊓-comm (a ⊔ b) c ∙ ⊓-⊔-dist c a b
        ∙ cong₂ _⊔_ (⊓-comm c a ∙ p) (⊓-comm c b ∙ q)

    ⊓-mono : (a b c d : Ω) → a ≤ c → b ≤ d → (a ⊓ b) ≤ (c ⊓ d)
    ⊓-mono a b c d p q =
      ⊓-greatest c d (a ⊓ b)
        (≤-trans (a ⊓ b) a c (⊓-≤-l a b) p)
        (≤-trans (a ⊓ b) b d (⊓-≤-r a b) q)

    ⊔-mono : (a b c d : Ω) → a ≤ c → b ≤ d → (a ⊔ b) ≤ (c ⊔ d)
    ⊔-mono a b c d p q =
      ⊔-least a b (c ⊔ d)
        (≤-trans a c (c ⊔ d) p (≤-⊔-l c d))
        (≤-trans b d (c ⊔ d) q (≤-⊔-r c d))

    -- The two constants, on both sides, as units and as annihilators.

    ⊥-unitˡ : (a : Ω) → (⊥ ⊔ a) ≡ a
    ⊥-unitˡ a = ⊔-comm ⊥ a ∙ ⊥-unit a

    ⊤-unitˡ : (a : Ω) → (⊤ ⊓ a) ≡ a
    ⊤-unitˡ a = ⊓-comm ⊤ a ∙ ⊤-unit a

    ⊥-annihilˡ : (a : Ω) → (⊥ ⊓ a) ≡ ⊥
    ⊥-annihilˡ a = cong (⊥ ⊓_) (sym (⊥-unitˡ a)) ∙ ⊓-absorb ⊥ a

    ⊥-annihil : (a : Ω) → (a ⊓ ⊥) ≡ ⊥
    ⊥-annihil a = ⊓-comm a ⊥ ∙ ⊥-annihilˡ a

    ⊤-annihilˡ : (a : Ω) → (⊤ ⊔ a) ≡ ⊤
    ⊤-annihilˡ a = cong (⊤ ⊔_) (sym (⊤-unitˡ a)) ∙ ⊔-absorb ⊤ a

    ⊤-annihil : (a : Ω) → (a ⊔ ⊤) ≡ ⊤
    ⊤-annihil a = ⊔-comm a ⊤ ∙ ⊤-annihilˡ a

    ⊥-least : (a : Ω) → ⊥ ≤ a
    ⊥-least = ⊥-annihilˡ

    ⊤-greatest : (a : Ω) → a ≤ ⊤
    ⊤-greatest = ⊤-unit

    ≤⊥→≡⊥ : (a : Ω) → a ≤ ⊥ → a ≡ ⊥
    ≤⊥→≡⊥ a p = sym p ∙ ⊥-annihil a

    -- One distributive law forces the other, as in any lattice.

    ⊔-⊓-dist : (a b c : Ω) → (a ⊔ (b ⊓ c)) ≡ ((a ⊔ b) ⊓ (a ⊔ c))
    ⊔-⊓-dist a b c = sym
      ( ⊓-⊔-dist (a ⊔ b) a c
      ∙ cong (_⊔ ((a ⊔ b) ⊓ c)) (⊓-comm (a ⊔ b) a ∙ ⊓-absorb a b)
      ∙ cong (a ⊔_) (⊓-comm (a ⊔ b) c ∙ ⊓-⊔-dist c a b)
      ∙ sym (⊔-assoc a (c ⊓ a) (c ⊓ b))
      ∙ cong (_⊔ (c ⊓ b)) (cong (a ⊔_) (⊓-comm c a) ∙ ⊔-absorb a c)
      ∙ cong (a ⊔_) (⊓-comm c b) )

    -- Complements are unique, which is what makes ¬_ determined rather than
    -- merely constrained, and is the engine of everything below.

    complement-unique : (a x y : Ω)
      → (a ⊓ x) ≡ ⊥ → (a ⊔ x) ≡ ⊤ → (a ⊓ y) ≡ ⊥ → (a ⊔ y) ≡ ⊤ → x ≡ y
    complement-unique a x y ax₀ ax₁ ay₀ ay₁ = xy ∙ sym (yx ∙ ⊓-comm y x)
      where
        xy : x ≡ (x ⊓ y)
        xy = sym (⊤-unit x) ∙ cong (x ⊓_) (sym ay₁) ∙ ⊓-⊔-dist x a y
           ∙ cong (_⊔ (x ⊓ y)) (⊓-comm x a ∙ ax₀) ∙ ⊥-unitˡ (x ⊓ y)
        yx : y ≡ (y ⊓ x)
        yx = sym (⊤-unit y) ∙ cong (y ⊓_) (sym ax₁) ∙ ⊓-⊔-dist y a x
           ∙ cong (_⊔ (y ⊓ x)) (⊓-comm y a ∙ ay₀) ∙ ⊥-unitˡ (y ⊓ x)

    ¬-invol : (a : Ω) → (¬ (¬ a)) ≡ a
    ¬-invol a = complement-unique (¬ a) (¬ (¬ a)) a
      (¬-⊓ (¬ a)) (¬-⊔ (¬ a)) (⊓-comm (¬ a) a ∙ ¬-⊓ a) (⊔-comm (¬ a) a ∙ ¬-⊔ a)

    -- De Morgan, in both directions.

    ¬-⊓-dist : (a b : Ω) → (¬ (a ⊓ b)) ≡ ((¬ a) ⊔ (¬ b))
    ¬-⊓-dist a b = complement-unique (a ⊓ b) (¬ (a ⊓ b)) ((¬ a) ⊔ (¬ b))
      (¬-⊓ (a ⊓ b)) (¬-⊔ (a ⊓ b)) meet join
      where
        meet : ((a ⊓ b) ⊓ ((¬ a) ⊔ (¬ b))) ≡ ⊥
        meet = ⊓-⊔-dist (a ⊓ b) (¬ a) (¬ b) ∙ cong₂ _⊔_ l r ∙ ⊔-idem ⊥
          where
            l : ((a ⊓ b) ⊓ (¬ a)) ≡ ⊥
            l = cong (_⊓ (¬ a)) (⊓-comm a b) ∙ ⊓-assoc b a (¬ a)
              ∙ cong (b ⊓_) (¬-⊓ a) ∙ ⊥-annihil b
            r : ((a ⊓ b) ⊓ (¬ b)) ≡ ⊥
            r = ⊓-assoc a b (¬ b) ∙ cong (a ⊓_) (¬-⊓ b) ∙ ⊥-annihil a
        join : ((a ⊓ b) ⊔ ((¬ a) ⊔ (¬ b))) ≡ ⊤
        join = ⊔-comm (a ⊓ b) ((¬ a) ⊔ (¬ b))
             ∙ ⊔-⊓-dist ((¬ a) ⊔ (¬ b)) a b ∙ cong₂ _⊓_ l r ∙ ⊓-idem ⊤
          where
            l : (((¬ a) ⊔ (¬ b)) ⊔ a) ≡ ⊤
            l = ⊔-comm ((¬ a) ⊔ (¬ b)) a ∙ sym (⊔-assoc a (¬ a) (¬ b))
              ∙ cong (_⊔ (¬ b)) (¬-⊔ a) ∙ ⊤-annihilˡ (¬ b)
            r : (((¬ a) ⊔ (¬ b)) ⊔ b) ≡ ⊤
            r = ⊔-assoc (¬ a) (¬ b) b
              ∙ cong ((¬ a) ⊔_) (⊔-comm (¬ b) b ∙ ¬-⊔ b) ∙ ⊤-annihil (¬ a)

    ¬-⊔-dist : (a b : Ω) → (¬ (a ⊔ b)) ≡ ((¬ a) ⊓ (¬ b))
    ¬-⊔-dist a b = complement-unique (a ⊔ b) (¬ (a ⊔ b)) ((¬ a) ⊓ (¬ b))
      (¬-⊓ (a ⊔ b)) (¬-⊔ (a ⊔ b)) meet join
      where
        meet : ((a ⊔ b) ⊓ ((¬ a) ⊓ (¬ b))) ≡ ⊥
        meet = ⊓-comm (a ⊔ b) ((¬ a) ⊓ (¬ b))
             ∙ ⊓-⊔-dist ((¬ a) ⊓ (¬ b)) a b ∙ cong₂ _⊔_ l r ∙ ⊔-idem ⊥
          where
            l : (((¬ a) ⊓ (¬ b)) ⊓ a) ≡ ⊥
            l = ⊓-assoc (¬ a) (¬ b) a ∙ cong ((¬ a) ⊓_) (⊓-comm (¬ b) a)
              ∙ sym (⊓-assoc (¬ a) a (¬ b))
              ∙ cong (_⊓ (¬ b)) (⊓-comm (¬ a) a ∙ ¬-⊓ a) ∙ ⊥-annihilˡ (¬ b)
            r : (((¬ a) ⊓ (¬ b)) ⊓ b) ≡ ⊥
            r = ⊓-assoc (¬ a) (¬ b) b
              ∙ cong ((¬ a) ⊓_) (⊓-comm (¬ b) b ∙ ¬-⊓ b) ∙ ⊥-annihil (¬ a)
        join : ((a ⊔ b) ⊔ ((¬ a) ⊓ (¬ b))) ≡ ⊤
        join = ⊔-⊓-dist (a ⊔ b) (¬ a) (¬ b) ∙ cong₂ _⊓_ l r ∙ ⊓-idem ⊤
          where
            l : ((a ⊔ b) ⊔ (¬ a)) ≡ ⊤
            l = cong (_⊔ (¬ a)) (⊔-comm a b) ∙ ⊔-assoc b a (¬ a)
              ∙ cong (b ⊔_) (¬-⊔ a) ∙ ⊤-annihil b
            r : ((a ⊔ b) ⊔ (¬ b)) ≡ ⊤
            r = ⊔-assoc a b (¬ b) ∙ cong (a ⊔_) (¬-⊔ b) ∙ ⊤-annihil a

    -- The implication adjunction pins implication to its Boolean value.

    ⇒-def : (a b : Ω) → (a ⇒ b) ≡ ((¬ a) ⊔ b)
    ⇒-def a b = ≤-antisym (a ⇒ b) ((¬ a) ⊔ b) forward backward
      where
        du : ((a ⇒ b) ⊓ a) ≤ b
        du = ⇒-uncurry (a ⇒ b) a b (≤-refl (a ⇒ b))
        decomp : (a ⇒ b) ≡ (((a ⇒ b) ⊓ a) ⊔ ((a ⇒ b) ⊓ (¬ a)))
        decomp = sym (⊤-unit (a ⇒ b)) ∙ cong ((a ⇒ b) ⊓_) (sym (¬-⊔ a))
               ∙ ⊓-⊔-dist (a ⇒ b) a (¬ a)
        forward : (a ⇒ b) ≤ ((¬ a) ⊔ b)
        forward = subst (λ z → z ≤ ((¬ a) ⊔ b)) (sym decomp)
          (⊔-least ((a ⇒ b) ⊓ a) ((a ⇒ b) ⊓ (¬ a)) ((¬ a) ⊔ b)
            (≤-trans ((a ⇒ b) ⊓ a) b ((¬ a) ⊔ b) du (≤-⊔-r (¬ a) b))
            (≤-trans ((a ⇒ b) ⊓ (¬ a)) (¬ a) ((¬ a) ⊔ b)
              (⊓-≤-r (a ⇒ b) (¬ a)) (≤-⊔-l (¬ a) b)))
        cancel : (((¬ a) ⊔ b) ⊓ a) ≡ (a ⊓ b)
        cancel = ⊓-comm ((¬ a) ⊔ b) a ∙ ⊓-⊔-dist a (¬ a) b
               ∙ cong (_⊔ (a ⊓ b)) (¬-⊓ a) ∙ ⊥-unitˡ (a ⊓ b)
        backward : ((¬ a) ⊔ b) ≤ (a ⇒ b)
        backward = ⇒-curry ((¬ a) ⊔ b) a b
          (subst (λ z → z ≤ b) (sym cancel) (⊓-≤-r a b))

    -- The evaluator produces _⇒ ⊥ and never ¬_, because the syntax expands
    -- ¬̇ φ to φ ⇒̇ ⊥̇ (src/FOL/Syntax.lagda.md:108-109) and the semantics
    -- follows it (src/FOL/Semantics.lagda.md:118-119). Every K2 negation is
    -- therefore written _ ⇒ ⊥, and this is the bridge to the algebra's own
    -- complement. It is a theorem here, not a transported lemma: K1's
    -- ¬-as-⇒⊥ (CardinalBridge.agda:55-56) is the hProp-specific statement and
    -- lives inside a module parameterized by a ZFStructure, which this file
    -- has none of and must not acquire.

    ¬-as-⇒⊥ : (a : Ω) → (¬ a) ≡ (a ⇒ ⊥)
    ¬-as-⇒⊥ a = sym (⇒-def a ⊥ ∙ ⊥-unit (¬ a))

    -- Refinement read as disjointness from the complement. This is the form
    -- in which the forcing layer meets the order: p forces φ exactly when p
    -- is incompatible with the value of ¬̇ φ.

    ≤-as-⊥ : (a b : Ω) → a ≤ b → (a ⊓ (b ⇒ ⊥)) ≡ ⊥
    ≤-as-⊥ a b p = cong (a ⊓_) (sym (¬-as-⇒⊥ b)) ∙ cong (_⊓ (¬ b)) (sym p)
                 ∙ ⊓-assoc a b (¬ b) ∙ cong (a ⊓_) (¬-⊓ b) ∙ ⊥-annihil a

    ⊥-as-≤ : (a b : Ω) → (a ⊓ (b ⇒ ⊥)) ≡ ⊥ → a ≤ b
    ⊥-as-≤ a b h = sym
      ( sym (⊤-unit a) ∙ cong (a ⊓_) (sym (¬-⊔ b)) ∙ ⊓-⊔-dist a b (¬ b)
      ∙ cong ((a ⊓ b) ⊔_) (cong (a ⊓_) (¬-as-⇒⊥ b) ∙ h) ∙ ⊥-unit (a ⊓ b) )

  -- Infinite distributivity is a theorem of a COMPLETE Boolean algebra and
  -- not of the laws alone, so it cannot sit in BooleanTheory: it needs a
  -- supremum to distribute over. It holds in every complete Boolean algebra,
  -- with no chain condition and no choice, and the forcing layer uses it
  -- whenever it pushes a meet with a condition inside a join over witnesses.

  module CompleteTheory (bl : BooleanLaws) (ch : CompleteHost) where
    open BooleanTheory bl public
    open CompleteHost ch public

    ⋁-dist : (a : Ω) (A : Type ℓ) (f : A → Ω)
      → (a ⊓ (⋁ A f)) ≡ (⋁ A (λ x → a ⊓ f x))
    ⋁-dist a A f = ≤-antisym (a ⊓ (⋁ A f)) (⋁ A g) forward backward
      where
        g : A → Ω
        g x = a ⊓ f x
        c : Ω
        c = ⋁ A g
        backward : (⋁ A g) ≤ (a ⊓ (⋁ A f))
        backward = snd (⋁-sup A g) (a ⊓ (⋁ A f))
          (λ x → ⊓-mono a (f x) a (⋁ A f) (≤-refl a) (fst (⋁-sup A f) x))
        step : (x : A) → (f x) ≤ (c ⊔ (¬ a))
        step x = subst (λ z → z ≤ (c ⊔ (¬ a))) (sym decomp)
          (⊔-least ((f x) ⊓ a) ((f x) ⊓ (¬ a)) (c ⊔ (¬ a)) lft rgt)
          where
            decomp : (f x) ≡ (((f x) ⊓ a) ⊔ ((f x) ⊓ (¬ a)))
            decomp = sym (⊤-unit (f x)) ∙ cong ((f x) ⊓_) (sym (¬-⊔ a))
                   ∙ ⊓-⊔-dist (f x) a (¬ a)
            lft : ((f x) ⊓ a) ≤ (c ⊔ (¬ a))
            lft = ≤-trans ((f x) ⊓ a) c (c ⊔ (¬ a))
              (subst (λ z → z ≤ c) (⊓-comm a (f x)) (fst (⋁-sup A g) x))
              (≤-⊔-l c (¬ a))
            rgt : ((f x) ⊓ (¬ a)) ≤ (c ⊔ (¬ a))
            rgt = ≤-trans ((f x) ⊓ (¬ a)) (¬ a) (c ⊔ (¬ a))
              (⊓-≤-r (f x) (¬ a)) (≤-⊔-r c (¬ a))
        cancel : (a ⊓ (c ⊔ (¬ a))) ≡ (a ⊓ c)
        cancel = ⊓-⊔-dist a c (¬ a) ∙ cong ((a ⊓ c) ⊔_) (¬-⊓ a) ∙ ⊥-unit (a ⊓ c)
        forward : (a ⊓ (⋁ A f)) ≤ (⋁ A g)
        forward = ≤-trans (a ⊓ (⋁ A f)) (a ⊓ (c ⊔ (¬ a))) c
          (⊓-mono a (⋁ A f) a (c ⊔ (¬ a)) (≤-refl a)
            (snd (⋁-sup A f) (c ⊔ (¬ a)) step))
          (subst (λ z → z ≤ c) (sym cancel) (⊓-≤-r a c))

-- The acceptance instances.
--
-- READ THIS BEFORE USING THEM. hPropAlgebra is a Boolean algebra only with
-- LEM, and with LEM it is the classical host truth-value algebra. It is a
-- TEST INSTANCE: it checks that the records are inhabitable and that their
-- fields are the ones a real algebra supplies, and it must never carry a
-- final result. The roadmap already warns that a host Boolean countermodel
-- is available (cohen-implementation-roadmap-2026-09.md:64): forcing over
-- the host truth values proves nothing about the model, because the generic
-- filter is not there. A T3 theorem routed through hPropBooleanLaws or
-- hPropCompleteHost is not a theorem about a forcing extension.

module HProp {ℓ : Level} where
  open BooleanAlgebra (hPropAlgebra ℓ)

  -- At hProp the derived order is entailment, in both directions.

  ⊆→≤ : (a b : Ω) → (⟨ a ⟩ → ⟨ b ⟩) → a ≤ b
  ⊆→≤ a b f = Logic.⇔toPath fst (λ p → p , f p)

  ≤→⊆ : (a b : Ω) → a ≤ b → ⟨ a ⟩ → ⟨ b ⟩
  ≤→⊆ a b p x = snd (Logic.pathTo⇐ p x)

  -- The laws the library does not already carry. Absorption is absent from
  -- Cubical.Functions.Logic; the two ⊥ laws cannot be reused from it either,
  -- because the algebra's ⊥ is the LIFTED empty type ⊥* (Base/Truth:152)
  -- while the library's ⊥ is the unlifted one at level zero.

  private
    absorbM : (a b : Ω) → (a ⊓ (a ⊔ b)) ≡ a
    absorbM a b = Logic.⇔toPath fst (λ p → p , Logic.inl p)

    absorbJ : (a b : Ω) → (a ⊔ (a ⊓ b)) ≡ a
    absorbJ a b =
      Logic.⇔toPath (Logic.⊔-elim a (a ⊓ b) (λ _ → a) (λ x → x) fst) Logic.inl

    botUnit : (a : Ω) → (a ⊔ ⊥) ≡ a
    botUnit a =
      Logic.⇔toPath (Logic.⊔-elim a ⊥ (λ _ → a) (λ x → x) Empty.rec*) Logic.inl

    negMeet : (a : Ω) → (a ⊓ (¬ a)) ≡ ⊥
    negMeet a = Logic.⇔toPath (λ p → Empty.rec (snd p (fst p))) Empty.rec*

    -- The only use of LEM in this file, and it is an argument of exactly the
    -- law that needs it. Everything else above is constructive.

    negJoin : LEM ℓ → (a : Ω) → (a ⊔ (¬ a)) ≡ ⊤
    negJoin lem a = Logic.⇔toPath (λ _ → tt*) (λ _ → dec (lem a))
      where
        dec : ⟨ a ⟩ ⊎ (⟨ a ⟩ → Empty.⊥) → ⟨ a ⊔ (¬ a) ⟩
        dec (inl⊎ p) = Logic.inl p
        dec (inr⊎ n) = Logic.inr n

    curryH : (a b c : Ω) → (a ⊓ b) ≤ c → a ≤ (b ⇒ c)
    curryH a b c h = ⊆→≤ a (b ⇒ c) (λ p q → ≤→⊆ (a ⊓ b) c h (p , q))

    uncurryH : (a b c : Ω) → a ≤ (b ⇒ c) → (a ⊓ b) ≤ c
    uncurryH a b c h = ⊆→≤ (a ⊓ b) c (λ p → ≤→⊆ a (b ⇒ c) h (fst p) (snd p))

  open BooleanLaws
  open CompleteHost
  open Nondegenerate

  laws : LEM ℓ → BooleanLaws
  laws lem = record
    { ⊓-comm    = Logic.⊓-comm
    ; ⊓-assoc   = λ a b c → sym (Logic.⊓-assoc a b c)
    ; ⊓-idem    = Logic.⊓-idem
    ; ⊔-comm    = Logic.⊔-comm
    ; ⊔-assoc   = λ a b c → sym (Logic.⊔-assoc a b c)
    ; ⊔-idem    = Logic.⊔-idem
    ; ⊓-absorb  = absorbM
    ; ⊔-absorb  = absorbJ
    ; ⊓-⊔-dist  = Logic.⊓-⊔-distribˡ
    ; ⊤-unit    = Logic.⊓-identityʳ
    ; ⊥-unit    = botUnit
    ; ¬-⊓       = negMeet
    ; ¬-⊔       = negJoin lem
    ; ⇒-curry   = curryH
    ; ⇒-uncurry = uncurryH
    }

  -- Completeness is free and constructive: the algebra's ⋁ is the truncated
  -- Σ and its ⋀ is the dependent function type, and those are the supremum
  -- and infimum of a host family on the nose.

  complete : CompleteHost
  complete = record { ⋁-sup = sup ; ⋀-inf = inf }
    where
      sup : (A : Type ℓ) (f : A → Ω) → IsSup f (⋁ A f)
      sup A f = (λ x → ⊆→≤ (f x) (⋁ A f) (λ p → ∣ x , p ∣₁))
              , (λ b ub → ⊆→≤ (⋁ A f) b
                  (PT.rec (snd b) (λ q → ≤→⊆ (f (fst q)) b (ub (fst q)) (snd q))))
      inf : (A : Type ℓ) (f : A → Ω) → IsInf f (⋀ A f)
      inf A f = (λ x → ⊆→≤ (⋀ A f) (f x) (λ h → h x))
              , (λ b lb → ⊆→≤ b (⋀ A f) (λ p x → ≤→⊆ b (f x) (lb x) p))

  -- Nondegeneracy is constructive here, and the instance is what shows the
  -- record is inhabitable rather than vacuously demanding.

  nondeg : Nondegenerate
  nondeg = record { ⊥≢⊤ = λ p → Empty.rec* (Logic.pathTo⇐ p tt*) }

hPropBooleanLaws : ∀ {ℓ} → LEM ℓ → BooleanAlgebra.BooleanLaws (hPropAlgebra ℓ)
hPropBooleanLaws {ℓ} = HProp.laws {ℓ}

hPropCompleteHost : ∀ {ℓ} → BooleanAlgebra.CompleteHost (hPropAlgebra ℓ)
hPropCompleteHost {ℓ} = HProp.complete {ℓ}

hPropNondegenerate : ∀ {ℓ} → BooleanAlgebra.Nondegenerate (hPropAlgebra ℓ)
hPropNondegenerate {ℓ} = HProp.nondeg {ℓ}
