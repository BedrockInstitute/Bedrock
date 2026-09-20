{-# OPTIONS --cubical --safe --guardedness #-}

-- K1-b probe B1: the object-language cardinal vocabulary and its semantic
-- bridges, structure-polymorphic over any 𝒮 : ZFStructure (hPropAlgebra ℓ).
-- No import below begins with L. or V.; that is checked by grep in the report.
--
-- The syntax has no function symbols, so every operation is a defined FORMULA
-- relating its arguments: "p is an ordered pair of x and y", never "the pair".
-- Each bridge lemma is a path of hProps between the evaluator's reading of the
-- formula and a host predicate written with _∈ˢ_, _≈ˢ_ and the hProp
-- algebra's own ⋀ and ⋁, so the host side carries exactly the truncation the
-- evaluator uses and never mentions host path equality where the formula says
-- _≐_.
--
-- Variable juggling inside larger formulas is done by FOL.Manipulation.Renaming
-- (renameFo with the correctness theorem Sat.⊨-rename), reusing the same
-- device K1-a used for a transposition.

open import Base.Prelude
open import Base.Truth
open import FOL.ZFStructure using ( ZFStructure )

module CardinalBridge {ℓ} (𝒮 : ZFStructure (hPropAlgebra ℓ)) where

open import FOL.ZFStructure using ( module hPropStructure )
open import FOL.Syntax
  using ( Formula; var; _∈̇_; _≐_; _∧̇_; _∨̇_; _⇒̇_; ⊥̇; ¬̇_; ∃̇_; ∀̇_
        ; ∀̇∈; ∃̇∈ )
open import FOL.Semantics (hPropAlgebra ℓ) 𝒮 using ( module At )
open import FOL.Manipulation.Renaming using ( renameFo; module Sat )
open import OrdinaryProfile 𝒮 using ( iff )
open import Cubical.Data.Sum using ( _⊎_; inl; inr )
open import Cubical.Functions.Logic using ( ⇔toPath )
import Cubical.Data.Empty as Empty

open TruthAlgebra (hPropAlgebra ℓ)
open hPropStructure 𝒮
open At S id using ( _⊨_ )

module Ren = Sat (hPropAlgebra ℓ) 𝒮 id
open Ren using ( Agrees; ⊨-rename )

infixr 11 _↔̇_

-- The object-language biconditional, spelled from the primitive connectives.

_↔̇_ : ∀ {K : Type ℓ} {n : ℕ} → Formula K n → Formula K n → Formula K n
φ ↔̇ ψ = (φ ⇒̇ ψ) ∧̇ (ψ ⇒̇ φ)

-- Two bottoms meet whenever a bridge passes through a negated subformula. The
-- syntax expands ¬̇ φ to φ ⇒̇ ⊥̇ and the evaluator sends ⊥̇ to the algebra's
-- ⊥, which is ⊥* = Lift ⊥, while the algebra's ¬_ is the library's, built on
-- the unlifted ⊥. They are logically equivalent and not definitionally equal.

¬-as-⇒⊥ : (P : Ω) → (¬ P) ≡ (P ⇒ ⊥)
¬-as-⇒⊥ P = ⇔toPath (λ f p → Empty.rec (f p)) (λ g p → Empty.rec* (g p))

-- A bare refl inside cong₂ over an hProp operation leaves the isProp component
-- of its endpoint undetermined: _⊓_ and _⇒_ build a Σ-pair, so matching the
-- goal fixes the carrier and not the proof of propositionality. Naming the
-- endpoint pins it. Every unchanged component below goes through this.

same : (P : Ω) → P ≡ P
same _ = refl

-- Subset. Env (x ∷ y ∷ []), reading "x ⊆ y".

Subsetφ : Formula S 2
Subsetφ =
  ∀̇ ((var zero ∈̇ var (suc zero)) ⇒̇ (var zero ∈̇ var (suc (suc zero))))

isSubset : S → S → Ω
isSubset x y = ⋀ S (λ z → (z ∈ˢ x) ⇒ (z ∈ˢ y))

Subset-bridge : (x y : S) → ((x ∷ y ∷ []) ⊨ Subsetφ) ≡ (isSubset x y)
Subset-bridge x y = refl

-- Singleton and unordered pair, used inside the Kuratowski pair. Envs
-- (t ∷ x ∷ []) and (t ∷ x ∷ y ∷ []), readings "t = {x}" and "t = {x, y}".

IsSingletonφ : Formula S 2
IsSingletonφ =
  (var (suc zero) ∈̇ var zero)
  ∧̇ (∀̇∈ (var zero) (var zero ≐ var (suc (suc zero))))

isSingleton : S → S → Ω
isSingleton t x =
  (x ∈ˢ t) ⊓ (⋀ S (λ u → (u ∈ˢ t) ⇒ (u ≈ˢ x)))

IsSingleton-bridge : (t x : S)
  → ((t ∷ x ∷ []) ⊨ IsSingletonφ) ≡ (isSingleton t x)
IsSingleton-bridge t x = refl

IsPairφ : Formula S 3
IsPairφ =
  (var (suc zero) ∈̇ var zero)
  ∧̇ ((var (suc (suc zero)) ∈̇ var zero)
  ∧̇ (∀̇∈ (var zero)
       ((var zero ≐ var (suc (suc zero)))
        ∨̇ (var zero ≐ var (suc (suc (suc zero)))))))

isPair : S → S → S → Ω
isPair t x y =
  (x ∈ˢ t) ⊓ ((y ∈ˢ t)
  ⊓ (⋀ S (λ u → (u ∈ˢ t) ⇒ ((u ≈ˢ x) ⊔ (u ≈ˢ y)))))

IsPair-bridge : (t x y : S)
  → ((t ∷ x ∷ y ∷ []) ⊨ IsPairφ) ≡ (isPair t x y)
IsPair-bridge t x y = refl

-- The Kuratowski ordered pair. Env (p ∷ x ∷ y ∷ []), reading
-- "p = {{x}, {x, y}}": every member of p is either the singleton of x or the
-- pair of x and y, and conversely.

PairφK : Formula S 3
PairφK =
  ∀̇ ((var zero ∈̇ var (suc zero))
    ↔̇ (((var (suc (suc zero)) ∈̇ var zero)
        ∧̇ (∀̇∈ (var zero) (var zero ≐ var (suc (suc (suc zero))))))
     ∨̇ ((var (suc (suc zero)) ∈̇ var zero)
        ∧̇ ((var (suc (suc (suc zero))) ∈̇ var zero)
        ∧̇ (∀̇∈ (var zero)
             ((var zero ≐ var (suc (suc (suc zero))))
              ∨̇ (var zero ≐ var (suc (suc (suc (suc zero)))))))))))

isKPair : S → S → S → Ω
isKPair p x y =
  ⋀ S (λ t → iff (t ∈ˢ p) ((isSingleton t x) ⊔ (isPair t x y)))

PairφK-bridge : (p x y : S)
  → ((p ∷ x ∷ y ∷ []) ⊨ PairφK) ≡ (isKPair p x y)
PairφK-bridge p x y = refl

-- Relation. Env (r ∷ []), reading "every member of r is an ordered pair of
-- some two sets". The pair formula is embedded by renaming: inside the two
-- existentials, positions 2, 1, 0 hold p, x, y.

rel-emb : Fin 3 → Fin 4
rel-emb zero              = suc (suc zero)
rel-emb (suc zero)        = suc zero
rel-emb (suc (suc zero))  = zero

IsRelationφ : Formula S 1
IsRelationφ = ∀̇∈ (var zero) (∃̇ (∃̇ (renameFo rel-emb PairφK)))

isRelation : S → Ω
isRelation r =
  ⋀ S (λ p → (p ∈ˢ r) ⇒ (⋁ S (λ x → ⋁ S (λ y → isKPair p x y))))

rel-emb-agrees : (p x y r : S)
  → Ren.Agrees rel-emb (y ∷ x ∷ p ∷ r ∷ []) (p ∷ x ∷ y ∷ [])
rel-emb-agrees p x y r zero              = refl
rel-emb-agrees p x y r (suc zero)        = refl
rel-emb-agrees p x y r (suc (suc zero))  = refl

IsRelation-bridge : (r : S) → ((r ∷ []) ⊨ IsRelationφ) ≡ (isRelation r)
IsRelation-bridge r =
  cong (⋀ S) (funExt (λ p → cong ((p ∈ˢ r) ⇒_) (cong (⋁ S) (funExt (λ x →
    cong (⋁ S) (funExt (λ y →
      ⊨-rename rel-emb PairφK (y ∷ x ∷ p ∷ r ∷ []) (p ∷ x ∷ y ∷ [])
        (rel-emb-agrees p x y r))))))))

-- Function. Env (f ∷ []), reading "f is a relation and single-valued: two
-- pairs of f with the same first component have the same second component".

fn-pair₁ : Fin 3 → Fin 6
fn-pair₁ zero              = suc (suc (suc (suc zero)))
fn-pair₁ (suc zero)        = suc (suc zero)
fn-pair₁ (suc (suc zero))  = suc zero

fn-pair₂ : Fin 3 → Fin 6
fn-pair₂ zero              = suc (suc (suc zero))
fn-pair₂ (suc zero)        = suc (suc zero)
fn-pair₂ (suc (suc zero))  = zero

IsFunctionφ : Formula S 1
IsFunctionφ =
  IsRelationφ
  ∧̇ (∀̇∈ (var zero)
      (∀̇∈ (var (suc zero))
        (∀̇ (∀̇ (∀̇
          (((renameFo fn-pair₁ PairφK) ∧̇ (renameFo fn-pair₂ PairφK))
            ⇒̇ (var (suc zero) ≐ var zero)))))))

isFunction : S → Ω
isFunction f =
  (isRelation f)
  ⊓ (⋀ S (λ p → (p ∈ˢ f) ⇒ (⋀ S (λ q → (q ∈ˢ f) ⇒
       (⋀ S (λ x → ⋀ S (λ y → ⋀ S (λ z →
         ((isKPair p x y) ⊓ (isKPair q x z)) ⇒ (y ≈ˢ z)))))))))

fn-pair₁-agrees : (p q x y z f : S)
  → Ren.Agrees fn-pair₁ (z ∷ y ∷ x ∷ q ∷ p ∷ f ∷ []) (p ∷ x ∷ y ∷ [])
fn-pair₁-agrees p q x y z f zero              = refl
fn-pair₁-agrees p q x y z f (suc zero)        = refl
fn-pair₁-agrees p q x y z f (suc (suc zero))  = refl

fn-pair₂-agrees : (p q x y z f : S)
  → Ren.Agrees fn-pair₂ (z ∷ y ∷ x ∷ q ∷ p ∷ f ∷ []) (q ∷ x ∷ z ∷ [])
fn-pair₂-agrees p q x y z f zero              = refl
fn-pair₂-agrees p q x y z f (suc zero)        = refl
fn-pair₂-agrees p q x y z f (suc (suc zero))  = refl

IsFunction-bridge : (f : S) → ((f ∷ []) ⊨ IsFunctionφ) ≡ (isFunction f)
IsFunction-bridge f =
  cong₂ _⊓_ (IsRelation-bridge f) (cong (⋀ S) (funExt (λ p →
    cong ((p ∈ˢ f) ⇒_) (cong (⋀ S) (funExt (λ q →
      cong ((q ∈ˢ f) ⇒_) (cong (⋀ S) (funExt (λ x →
        cong (⋀ S) (funExt (λ y →
          cong (⋀ S) (funExt (λ z →
            cong₂ _⇒_
              (cong₂ _⊓_
                (⊨-rename fn-pair₁ PairφK (z ∷ y ∷ x ∷ q ∷ p ∷ f ∷ [])
                  (p ∷ x ∷ y ∷ []) (fn-pair₁-agrees p q x y z f))
                (⊨-rename fn-pair₂ PairφK (z ∷ y ∷ x ∷ q ∷ p ∷ f ∷ [])
                  (q ∷ x ∷ z ∷ []) (fn-pair₂-agrees p q x y z f)))
              (same (y ≈ˢ z)))))))))))))))

-- Injection. Env (f ∷ a ∷ b ∷ []), reading "f is an injective function, TOTAL
-- ON a, with values in b": a function, defined at every member of a, every
-- value of which lies in b, and two pairs with the same second component have
-- the same first component.
--
-- The domain clause is ONE implication, not a biconditional, so the domain may
-- be larger than a. That is deliberate but it is weaker than the usual reading
-- of "injection from a into b", and the distinction is load bearing: the L
-- development's InjCode uses domAt, which IS a biconditional, so the two are
-- NOT equivalent per graph. The counterexample is a = empty, b = {empty},
-- F = {pr empty empty}, which satisfies this predicate and refutes InjCode.
-- Nothing downstream is harmed, because injectable quantifies the graph
-- existentially and a graph can always be cut down to the pairs whose first
-- component lies in a. The comparison track discharges exactly that repair.

inj-fun : Fin 1 → Fin 3
inj-fun zero = zero

inj-dom : Fin 3 → Fin 6
inj-dom zero              = zero
inj-dom (suc zero)        = suc (suc zero)
inj-dom (suc (suc zero))  = suc zero

inj-ran : Fin 3 → Fin 6
inj-ran zero              = suc (suc zero)
inj-ran (suc zero)        = suc zero
inj-ran (suc (suc zero))  = zero

inj-pair₁ : Fin 3 → Fin 8
inj-pair₁ zero              = suc (suc (suc (suc zero)))
inj-pair₁ (suc zero)        = suc (suc zero)
inj-pair₁ (suc (suc zero))  = suc zero

inj-pair₂ : Fin 3 → Fin 8
inj-pair₂ zero              = suc (suc (suc zero))
inj-pair₂ (suc zero)        = zero
inj-pair₂ (suc (suc zero))  = suc zero

InjDomφ : Formula S 3
InjDomφ =
  ∀̇∈ (var (suc zero))
       (∃̇ (∃̇ ((var zero ∈̇ var (suc (suc (suc zero))))
            ∧̇ (renameFo inj-dom PairφK))))

InjRanφ : Formula S 3
InjRanφ =
  ∀̇∈ (var zero)
       (∀̇ (∀̇ ((renameFo inj-ran PairφK)
            ⇒̇ (var zero ∈̇ var (suc (suc (suc (suc (suc zero)))))))))

InjPairφ : Formula S 3
InjPairφ =
  ∀̇∈ (var zero)
       (∀̇∈ (var (suc zero))
         (∀̇ (∀̇ (∀̇ (((renameFo inj-pair₁ PairφK) ∧̇ (renameFo inj-pair₂ PairφK))
                  ⇒̇ (var (suc (suc zero)) ≐ var zero))))))

IsInjectionφ : Formula S 3
IsInjectionφ =
  (renameFo inj-fun IsFunctionφ)
  ∧̇ (InjDomφ
  ∧̇ (InjRanφ
  ∧̇ InjPairφ))

isInjection : S → S → S → Ω
isInjection f a b =
  (isFunction f)
  ⊓ ((⋀ S (λ x → (x ∈ˢ a) ⇒ (⋁ S (λ y → ⋁ S (λ p →
       (p ∈ˢ f) ⊓ (isKPair p x y))))))
  ⊓ ((⋀ S (λ p → (p ∈ˢ f) ⇒ (⋀ S (λ x → ⋀ S (λ y →
       (isKPair p x y) ⇒ (y ∈ˢ b))))))
  ⊓ (⋀ S (λ p → (p ∈ˢ f) ⇒ (⋀ S (λ q → (q ∈ˢ f) ⇒
       (⋀ S (λ x → ⋀ S (λ y → ⋀ S (λ z →
         ((isKPair p x y) ⊓ (isKPair q z y)) ⇒ (x ≈ˢ z)))))))))))

inj-fun-agrees : (f a b : S)
  → Ren.Agrees inj-fun (f ∷ a ∷ b ∷ []) (f ∷ [])
inj-fun-agrees f a b zero = refl

inj-dom-agrees : (p x y f a b : S)
  → Ren.Agrees inj-dom (p ∷ y ∷ x ∷ f ∷ a ∷ b ∷ []) (p ∷ x ∷ y ∷ [])
inj-dom-agrees p x y f a b zero              = refl
inj-dom-agrees p x y f a b (suc zero)        = refl
inj-dom-agrees p x y f a b (suc (suc zero))  = refl

inj-ran-agrees : (p x y f a b : S)
  → Ren.Agrees inj-ran (y ∷ x ∷ p ∷ f ∷ a ∷ b ∷ []) (p ∷ x ∷ y ∷ [])
inj-ran-agrees p x y f a b zero              = refl
inj-ran-agrees p x y f a b (suc zero)        = refl
inj-ran-agrees p x y f a b (suc (suc zero))  = refl

inj-pair₁-agrees : (p q x y z f a b : S)
  → Ren.Agrees inj-pair₁ (z ∷ y ∷ x ∷ q ∷ p ∷ f ∷ a ∷ b ∷ [])
                     (p ∷ x ∷ y ∷ [])
inj-pair₁-agrees p q x y z f a b zero              = refl
inj-pair₁-agrees p q x y z f a b (suc zero)        = refl
inj-pair₁-agrees p q x y z f a b (suc (suc zero))  = refl

inj-pair₂-agrees : (p q x y z f a b : S)
  → Ren.Agrees inj-pair₂ (z ∷ y ∷ x ∷ q ∷ p ∷ f ∷ a ∷ b ∷ [])
                     (q ∷ z ∷ y ∷ [])
inj-pair₂-agrees p q x y z f a b zero              = refl
inj-pair₂-agrees p q x y z f a b (suc zero)        = refl
inj-pair₂-agrees p q x y z f a b (suc (suc zero))  = refl

InjDom-bridge : (f a b : S)
  → ((f ∷ a ∷ b ∷ []) ⊨ InjDomφ)
    ≡ (⋀ S (λ x → (x ∈ˢ a) ⇒ (⋁ S (λ y → ⋁ S (λ p →
         (p ∈ˢ f) ⊓ (isKPair p x y))))))
InjDom-bridge f a b =
  cong (⋀ S) (funExt (λ x → cong ((x ∈ˢ a) ⇒_) (cong (⋁ S) (funExt (λ y →
    cong (⋁ S) (funExt (λ p → cong₂ _⊓_ (same (p ∈ˢ f))
      (⊨-rename inj-dom PairφK (p ∷ y ∷ x ∷ f ∷ a ∷ b ∷ [])
        (p ∷ x ∷ y ∷ []) (inj-dom-agrees p x y f a b)))))))))

InjRan-bridge : (f a b : S)
  → ((f ∷ a ∷ b ∷ []) ⊨ InjRanφ)
    ≡ (⋀ S (λ p → (p ∈ˢ f) ⇒ (⋀ S (λ x → ⋀ S (λ y →
         (isKPair p x y) ⇒ (y ∈ˢ b))))))
InjRan-bridge f a b =
  cong (⋀ S) (funExt (λ p → cong ((p ∈ˢ f) ⇒_) (cong (⋀ S) (funExt (λ x →
    cong (⋀ S) (funExt (λ y → cong₂ _⇒_
      (⊨-rename inj-ran PairφK (y ∷ x ∷ p ∷ f ∷ a ∷ b ∷ [])
        (p ∷ x ∷ y ∷ []) (inj-ran-agrees p x y f a b))
      (same (y ∈ˢ b)))))))))

InjPair-bridge : (f a b : S)
  → ((f ∷ a ∷ b ∷ []) ⊨ InjPairφ)
    ≡ (⋀ S (λ p → (p ∈ˢ f) ⇒ (⋀ S (λ q → (q ∈ˢ f) ⇒
         (⋀ S (λ x → ⋀ S (λ y → ⋀ S (λ z →
           ((isKPair p x y) ⊓ (isKPair q z y)) ⇒ (x ≈ˢ z)))))))))
InjPair-bridge f a b =
  cong (⋀ S) (funExt (λ p → cong ((p ∈ˢ f) ⇒_) (cong (⋀ S) (funExt (λ q →
    cong ((q ∈ˢ f) ⇒_) (cong (⋀ S) (funExt (λ x →
      cong (⋀ S) (funExt (λ y → cong (⋀ S) (funExt (λ z → cong₂ _⇒_
        (cong₂ _⊓_
          (⊨-rename inj-pair₁ PairφK (z ∷ y ∷ x ∷ q ∷ p ∷ f ∷ a ∷ b ∷ [])
            (p ∷ x ∷ y ∷ []) (inj-pair₁-agrees p q x y z f a b))
          (⊨-rename inj-pair₂ PairφK (z ∷ y ∷ x ∷ q ∷ p ∷ f ∷ a ∷ b ∷ [])
            (q ∷ z ∷ y ∷ []) (inj-pair₂-agrees p q x y z f a b)))
        (same (x ≈ˢ z))))))))))))))

InjFun-bridge : (f a b : S)
  → ((f ∷ a ∷ b ∷ []) ⊨ (renameFo inj-fun IsFunctionφ)) ≡ (isFunction f)
InjFun-bridge f a b =
  ⊨-rename inj-fun IsFunctionφ (f ∷ a ∷ b ∷ []) (f ∷ [])
    (inj-fun-agrees f a b)
  ∙ IsFunction-bridge f

IsInjection-bridge : (f a b : S)
  → ((f ∷ a ∷ b ∷ []) ⊨ IsInjectionφ) ≡ (isInjection f a b)
IsInjection-bridge f a b =
  cong₂ _⊓_ (InjFun-bridge f a b)
    (cong₂ _⊓_ (InjDom-bridge f a b)
      (cong₂ _⊓_ (InjRan-bridge f a b) (InjPair-bridge f a b)))

-- Injectable, the internal cardinal comparison. Env (x ∷ y ∷ []), reading
-- "some injection carries x into y". The bound variable sits at position 0
-- with x and y at 1 and 2, so the injection formula applies unrenamed.

Injectableφ : Formula S 2
Injectableφ = ∃̇ IsInjectionφ

injectable : S → S → Ω
injectable x y = ⋁ S (λ f → isInjection f x y)

Injectable-bridge : (x y : S)
  → ((x ∷ y ∷ []) ⊨ Injectableφ) ≡ (injectable x y)
Injectable-bridge x y =
  cong (⋁ S) (funExt (λ f → IsInjection-bridge f x y))

-- Successor of a set. Env (y ∷ x ∷ []), reading "y = x ∪ {x}".

IsSuccOfφ : Formula S 2
IsSuccOfφ =
  (var (suc zero) ∈̇ var zero)
  ∧̇ ((∀̇∈ (var (suc zero)) (var zero ∈̇ var (suc zero)))
  ∧̇ (∀̇∈ (var zero)
       ((var zero ∈̇ var (suc (suc zero)))
        ∨̇ (var zero ≐ var (suc (suc zero))))))

isSuccOf : S → S → Ω
isSuccOf y x =
  (x ∈ˢ y)
  ⊓ ((⋀ S (λ z → (z ∈ˢ x) ⇒ (z ∈ˢ y)))
  ⊓ (⋀ S (λ z → (z ∈ˢ y) ⇒ ((z ∈ˢ x) ⊔ (z ≈ˢ x)))))

IsSuccOf-bridge : (y x : S)
  → ((y ∷ x ∷ []) ⊨ IsSuccOfφ) ≡ (isSuccOf y x)
IsSuccOf-bridge y x = refl

-- Inductive. Env (u ∷ []). The closure is by the SUCCESSOR operation, not
-- Bell's "every member has a member above it": a Bell-inductive set need not
-- contain any numeral beyond the empty set, since u = {∅} together with an
-- ascending chain of pairs {{∅, junk}, ...} is Bell-inductive while missing
-- {∅}. Under successor closure the least inductive set exists and behaves,
-- which is what IsOmegaφ below needs.

wk2 : Fin 2 → Fin 3
wk2 zero       = zero
wk2 (suc zero) = suc zero

wk2-agrees : (y x u : S)
  → Ren.Agrees wk2 (y ∷ x ∷ u ∷ []) (y ∷ x ∷ [])
wk2-agrees y x u zero       = refl
wk2-agrees y x u (suc zero) = refl

IsInductiveφ : Formula S 1
IsInductiveφ =
  (∃̇∈ (var zero) (∀̇∈ (var zero) ⊥̇))
  ∧̇ (∀̇∈ (var zero) (∃̇∈ (var (suc zero)) (renameFo wk2 IsSuccOfφ)))

isInductive : S → Ω
isInductive u =
  (⋁ S (λ e → (e ∈ˢ u) ⊓ (⋀ S (λ w → (w ∈ˢ e) ⇒ ⊥))))
  ⊓ (⋀ S (λ x → (x ∈ˢ u) ⇒ (⋁ S (λ y → (y ∈ˢ u) ⊓ (isSuccOf y x)))))

IsInductive-bridge : (u : S) → ((u ∷ []) ⊨ IsInductiveφ) ≡ (isInductive u)
IsInductive-bridge u =
  cong₂ _⊓_ (same (⋁ S (λ e → (e ∈ˢ u) ⊓ (⋀ S (λ w → (w ∈ˢ e) ⇒ ⊥)))))
    (cong (⋀ S) (funExt (λ x → cong ((x ∈ˢ u) ⇒_) (cong (⋁ S) (funExt (λ y →
      cong₂ _⊓_ (same (y ∈ˢ u))
        (⊨-rename wk2 IsSuccOfφ (y ∷ x ∷ u ∷ []) (y ∷ x ∷ [])
          (wk2-agrees y x u))))))))

-- Omega. Env (w ∷ []), reading "w is inductive and every member of w belongs
-- to every inductive set".

wk1 : Fin 1 → Fin 2
wk1 zero = zero

wk1-agrees : (i w : S) → Ren.Agrees wk1 (i ∷ w ∷ []) (i ∷ [])
wk1-agrees i w zero = refl

IsOmegaφ : Formula S 1
IsOmegaφ =
  IsInductiveφ
  ∧̇ (∀̇ ((renameFo wk1 IsInductiveφ)
        ⇒̇ (∀̇∈ (var (suc zero)) ((var zero) ∈̇ (var (suc zero))))))

isOmega : S → Ω
isOmega w =
  (isInductive w)
  ⊓ (⋀ S (λ i → (isInductive i) ⇒ (⋀ S (λ v → (v ∈ˢ w) ⇒ (v ∈ˢ i)))))

IsOmega-bridge : (w : S) → ((w ∷ []) ⊨ IsOmegaφ) ≡ (isOmega w)
IsOmega-bridge w =
  cong₂ _⊓_ (same (isInductive w))
    (cong (⋀ S) (funExt (λ i → cong₂ _⇒_
      (⊨-rename wk1 IsInductiveφ (i ∷ w ∷ []) (i ∷ []) (wk1-agrees i w))
      (same (⋀ S (λ v → (v ∈ˢ w) ⇒ (v ∈ˢ i)))))))

-- Power set. Env (p ∷ a ∷ []), reading "the members of p are exactly the
-- subsets of a".

pow-emb : Fin 2 → Fin 3
pow-emb zero       = zero
pow-emb (suc zero) = suc (suc zero)

IsPowerSetφ : Formula S 2
IsPowerSetφ =
  ∀̇ ((var zero ∈̇ var (suc zero)) ↔̇ (renameFo pow-emb Subsetφ))

isPowerSet : S → S → Ω
isPowerSet p a = ⋀ S (λ x → iff (x ∈ˢ p) (isSubset x a))

pow-emb-agrees : (x p a : S)
  → Ren.Agrees pow-emb (x ∷ p ∷ a ∷ []) (x ∷ a ∷ [])
pow-emb-agrees x p a zero       = refl
pow-emb-agrees x p a (suc zero) = refl

IsPowerSet-bridge : (p a : S)
  → ((p ∷ a ∷ []) ⊨ IsPowerSetφ) ≡ (isPowerSet p a)
IsPowerSet-bridge p a =
  cong (⋀ S) (funExt (λ x →
    cong₂ _⊓_
      (cong₂ _⇒_ (same (x ∈ˢ p))
        (⊨-rename pow-emb Subsetφ (x ∷ p ∷ a ∷ []) (x ∷ a ∷ [])
          (pow-emb-agrees x p a)))
      (cong₂ _⇒_
        (⊨-rename pow-emb Subsetφ (x ∷ p ∷ a ∷ []) (x ∷ a ∷ [])
          (pow-emb-agrees x p a))
        (same (x ∈ˢ p)))))

-- Transitive set. Env (a ∷ []).

IsTransitiveφ : Formula S 1
IsTransitiveφ =
  ∀̇∈ (var zero) (∀̇∈ (var zero) ((var zero) ∈̇ (var (suc (suc zero)))))

isTransitiveSet : S → Ω
isTransitiveSet a =
  ⋀ S (λ x → (x ∈ˢ a) ⇒ (⋀ S (λ y → (y ∈ˢ x) ⇒ (y ∈ˢ a))))

IsTransitive-bridge : (a : S)
  → ((a ∷ []) ⊨ IsTransitiveφ) ≡ (isTransitiveSet a)
IsTransitive-bridge a = refl

-- Ordinal. Env (α ∷ []), reading "α is transitive and membership linearly
-- orders α". No well-foundedness: the only well-foundedness the ordinary
-- profile has is the induction form Foundation field, and a Cohen quotient has
-- nothing else.

IsOrdinalφ : Formula S 1
IsOrdinalφ =
  IsTransitiveφ
  ∧̇ (∀̇∈ (var zero)
       (∀̇∈ (var (suc zero))
         (((var (suc zero)) ∈̇ (var zero))
          ∨̇ (((var (suc zero)) ≐ (var zero))
           ∨̇ ((var zero) ∈̇ (var (suc zero)))))))

isOrdinal : S → Ω
isOrdinal α =
  (isTransitiveSet α)
  ⊓ (⋀ S (λ x → (x ∈ˢ α) ⇒ (⋀ S (λ y → (y ∈ˢ α) ⇒
       ((x ∈ˢ y) ⊔ ((x ≈ˢ y) ⊔ (y ∈ˢ x)))))))

IsOrdinal-bridge : (α : S)
  → ((α ∷ []) ⊨ IsOrdinalφ) ≡ (isOrdinal α)
IsOrdinal-bridge α = refl

-- Cardinal. Env (κ ∷ []), reading "κ is an ordinal that does not inject into
-- any strictly smaller ordinal". Smaller is membership, the von Neumann order.

swap21 : Fin 2 → Fin 2
swap21 zero       = suc zero
swap21 (suc zero) = zero

IsCardinalφ : Formula S 1
IsCardinalφ =
  IsOrdinalφ
  ∧̇ (∀̇∈ (var zero) (¬̇ (renameFo swap21 Injectableφ)))

isCardinal : S → Ω
isCardinal κ =
  (isOrdinal κ)
  ⊓ (⋀ S (λ β → (β ∈ˢ κ) ⇒ ¬ (injectable κ β)))

swap21-agrees : (κ β : S)
  → Ren.Agrees swap21 (β ∷ κ ∷ []) (κ ∷ β ∷ [])
swap21-agrees κ β zero       = refl
swap21-agrees κ β (suc zero) = refl

IsCardinal-bridge : (κ : S)
  → ((κ ∷ []) ⊨ IsCardinalφ) ≡ (isCardinal κ)
IsCardinal-bridge κ =
  cong₂ _⊓_ (IsOrdinal-bridge κ)
    (cong (⋀ S) (funExt (λ β → cong ((β ∈ˢ κ) ⇒_)
      (cong (_⇒ ⊥)
        (⊨-rename swap21 Injectableφ (β ∷ κ ∷ []) (κ ∷ β ∷ [])
          (swap21-agrees κ β)
         ∙ Injectable-bridge κ β)
       ∙ sym (¬-as-⇒⊥ (injectable κ β))))))

-- Successor cardinal. Env (δ ∷ κ ∷ []), reading "δ is a cardinal strictly
-- above κ and below-or-equal to every cardinal strictly above κ".

sc-emb : Fin 1 → Fin 2
sc-emb zero = zero

sc-emb-mu : Fin 1 → Fin 3
sc-emb-mu zero = zero

IsSuccCardinalφ : Formula S 2
IsSuccCardinalφ =
  (renameFo sc-emb IsCardinalφ)
  ∧̇ ((var (suc zero) ∈̇ var zero)
  ∧̇ (∀̇ (((renameFo sc-emb-mu IsCardinalφ)
        ∧̇ ((var (suc (suc zero))) ∈̇ (var zero)))
       ⇒̇ (((var (suc zero)) ≐ (var zero))
        ∨̇ ((var (suc zero)) ∈̇ (var zero))))))

isSuccCardinal : S → S → Ω
isSuccCardinal δ κ =
  (isCardinal δ)
  ⊓ ((κ ∈ˢ δ)
  ⊓ (⋀ S (λ μ → ((isCardinal μ) ⊓ (κ ∈ˢ μ))
       ⇒ ((δ ≈ˢ μ) ⊔ (δ ∈ˢ μ)))))

sc-emb-agrees : (δ κ : S) → Ren.Agrees sc-emb (δ ∷ κ ∷ []) (δ ∷ [])
sc-emb-agrees δ κ zero = refl

sc-emb-mu-agrees : (μ δ κ : S)
  → Ren.Agrees sc-emb-mu (μ ∷ δ ∷ κ ∷ []) (μ ∷ [])
sc-emb-mu-agrees μ δ κ zero = refl

IsSuccCardinal-bridge : (δ κ : S)
  → ((δ ∷ κ ∷ []) ⊨ IsSuccCardinalφ) ≡ (isSuccCardinal δ κ)
IsSuccCardinal-bridge δ κ =
  cong₂ _⊓_
    (⊨-rename sc-emb IsCardinalφ (δ ∷ κ ∷ []) (δ ∷ []) (sc-emb-agrees δ κ)
     ∙ IsCardinal-bridge δ)
    (cong₂ _⊓_ (same (κ ∈ˢ δ))
      (cong (⋀ S) (funExt (λ μ → cong₂ _⇒_
        (cong₂ _⊓_
          (⊨-rename sc-emb-mu IsCardinalφ (μ ∷ δ ∷ κ ∷ []) (μ ∷ [])
            (sc-emb-mu-agrees μ δ κ)
           ∙ IsCardinal-bridge μ)
          (same (κ ∈ˢ μ)))
        (same ((δ ≈ˢ μ) ⊔ (δ ∈ˢ μ)))))))
