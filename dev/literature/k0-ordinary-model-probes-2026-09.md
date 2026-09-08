# K0 ordinary-model realization probes

Date: 2026-09-08. Baseline: `f61112d4`. Status: in progress; neither K0 nor trophy 3 is complete. This batch investigates the ordinary two-valued model endpoint introduced in K12-K15 of the [Cohen roadmap](cohen-implementation-roadmap-2026-09.md). It complements the [earlier probe ledger](k0-probe-evidence-2026-09.md). All new Agda files and dependency caches remain under `/tmp/bedrock-k0-probes`; no repository source modules are modified.

## Checked restriction equality adapter

`RestrictedEquality.agda` generalizes the earlier singleton equality example to every proposition-valued restriction of any coherent ordinary structure. It uses the actual repository `_↾_` and `↾-reflects`, and instantiates the result on HIT-V and every proposition-valued subclass of it. Transitivity is not needed for this equality fact. In particular, the abstract class parameter can later be instantiated with L without supplying a fresh equality axiom.

The coordinator ran the following command from `/tmp/bedrock-k0-probes/model`; it exited 0 without warnings:

```text
GHCRTS="-A64m -I0 -M8g" agda -l cubical -i /tmp/bedrock-k0-probes/model -i /tmp/bedrock-k0-probes/model/deps/src /tmp/bedrock-k0-probes/model/RestrictedEquality.agda
```

The probe uses neither LEM nor host/internal Choice, resizing, genericity or ultrafilters. It proves equality coherence only: it does not prove that an arbitrary subclass is transitive or satisfies ZFC, and it does not instantiate a fully implemented ordinary-model axiom profile. The V dependency was checked in the copied dependency tree.

### model/RestrictedEquality.agda

SHA-256: `69d91fbee9adbe3fbaba003cf372d038b5fd1e62bb3f867a25bf9b263304cc57`

```text
{-# OPTIONS --cubical --safe --guardedness #-}

module RestrictedEquality where

open import Base.Prelude
open import Base.Truth using ( hPropAlgebra )
open import FOL.ZFStructure using ( ZFStructure; _↾_; ↾-reflects )
open import EqualityCoherence using ( EqualityCoherence )
open import V.Hierarchy using ( 𝒮ᵥ )

restricted-coherence : ∀ {ℓ} (𝒮 : ZFStructure (hPropAlgebra ℓ))
  → EqualityCoherence 𝒮
  → (M : ZFStructure.S 𝒮 → hProp ℓ)
  → EqualityCoherence (𝒮 ↾ M)
restricted-coherence 𝒮 e M = record
  { ≈-sound = λ p → ↾-reflects {𝒮 = 𝒮} {M = M}
      (EqualityCoherence.≈-sound e p)
  ; ≈-complete = λ p → EqualityCoherence.≈-complete e (cong fst p)
  }

hierarchy-coherence : ∀ {ℓ} → EqualityCoherence (𝒮ᵥ {ℓ})
hierarchy-coherence = record
  { ≈-sound = λ p → p
  ; ≈-complete = λ p → p
  }

hierarchy-restriction-coherence : ∀ {ℓ}
  → (M : ZFStructure.S (𝒮ᵥ {ℓ}) → hProp (ℓ-suc ℓ))
  → EqualityCoherence (𝒮ᵥ ↾ M)
hierarchy-restriction-coherence M =
  restricted-coherence 𝒮ᵥ hierarchy-coherence M
```

## Checked ordinary quotient and existential boundary

The agent's final serial check from `/tmp/bedrock-k0-probes/quotient` exited 0, rechecking both `Quotient.agda` and `Finite.agda`:

```text
GHCRTS="-A64m -I0 -M8g" agda -i /tmp/bedrock-k0-probes/quotient -l cubical /tmp/bedrock-k0-probes/quotient/Finite.agda
```

The coordinator reviewed both sources. `Descent` consumes small types A/B, a proposition-valued predicate U, B-valued equality/membership, an equivalence-relation certificate for U-valued equality, and congruence after applying U. It constructs the actual Cubical set quotient, descends membership and proves both directions of quotient equality on representatives using effectiveness. It does not derive these hypotheses from a packaged Boolean model, nor assume Boolean/filter laws in the generic lemma.

The existential step consumes a predicate descending to the quotient, a candidate value s, the U-level upper implication, and truncated fullness `∥ Σ x, P x = s ∥`. It proves both directions between U(s) and truncated existential satisfaction on the quotient, eliminating truncation only into propositions. It does not select representatives, need LEM/Choice, or assume genericity. This is atomic/existential boundary evidence, not a recursive all-formula truth theorem. Universes are fixed to Type₀/hProp₀; production universe polymorphism remains open.

The finite instance discharges those assumptions using Bool × Bool truth values and names. U tests the first coordinate. It proves top membership, properness, meet/upward closure and complement decision. Two distinct names become equal in the quotient, while a third gives a distinct class; membership and inhabitation are nontrivial. For a specific predicate, its existential value is the partial value `(true,false)`, with checked upper/least laws and an explicit fullness witness. The ordinary existential theorem actually calls the generic transfer. The instance is not a ZFC model, not a generic-extension example and not a packaged complete Boolean algebra.

## Checked integration with the existing structure interface

The coordinator then ran the following command from `/tmp/bedrock-k0-probes/model`; it exited 0 without warnings:

```text
GHCRTS="-A64m -I0 -M8g" agda -l cubical -i /tmp/bedrock-k0-probes/model -i /tmp/bedrock-k0-probes/quotient -i /tmp/bedrock-k0-probes/model/deps/src /tmp/bedrock-k0-probes/model/QuotientStructure.agda
```

`QuotientStructure.Adapter` packages the actual quotient into the repository's `ZFStructure (hPropAlgebra ℓ-zero)` and proves its path-equality coherence. Thus the existing formula evaluator has a compatible ordinary structure to consume; this is more than an unrelated quotient type. No ZFC axiom profile, external well-foundedness or complete formula truth theorem is claimed. No generated dependency cache was written into repository source.

## Additional checked source snapshots

### quotient/Quotient.agda

SHA-256: `386953241f0159bc37c8ccc4202326eba54a00165f7c32172155545c65225698`

```text
{-# OPTIONS --cubical --safe --guardedness #-}
module Quotient where

open import Cubical.Foundations.Prelude using (Type; _≡_; refl; sym; cong₂; subst; ℓ-zero)
open import Cubical.Foundations.HLevels using (hProp; isSetHProp; isPropΠ)
open import Cubical.Data.Sigma using (Σ; _,_; fst; snd)
open import Cubical.Relation.Binary using (module BinaryRelation)
open BinaryRelation using (isEquivRel)
import Cubical.HITs.SetQuotients as Quotient
import Cubical.HITs.PropositionalTruncation as Truncation
open import Cubical.HITs.PropositionalTruncation using (∥_∥₁; ∣_∣₁; squash₁)

module Descent (A B : Type₀) (U : B → hProp ℓ-zero)
  (E M : A → A → B)
  (e : isEquivRel (λ x y → fst (U (E x y))))
  (l : (x y z : A) → fst (U (E x y)) → U (M x z) ≡ U (M y z))
  (r : (x y z : A) → fst (U (E y z)) → U (M x y) ≡ U (M x z)) where

  _≈_ : A → A → Type₀
  x ≈ y = fst (U (E x y))

  N : Type₀
  N = A Quotient./ _≈_

  [_] : A → N
  [_] = Quotient.[_]

  _∈ˢ_ : N → N → hProp ℓ-zero
  _∈ˢ_ = Quotient.rec2 isSetHProp (λ x y → U (M x y)) l r

  equality-to-ordinary : (x y : A) → x ≈ y → [ x ] ≡ [ y ]
  equality-to-ordinary = Quotient.eq/

  equality-from-ordinary : (x y : A) → [ x ] ≡ [ y ] → x ≈ y
  equality-from-ordinary = Quotient.effective (λ x y → snd (U (E x y))) e

  membership-at-names : (x y : A) → [ x ] ∈ˢ [ y ] ≡ U (M x y)
  membership-at-names x y = refl

  ordinary-membership-coherent : (x y z w : N) → x ≡ y → z ≡ w → x ∈ˢ z ≡ y ∈ˢ w
  ordinary-membership-coherent x y z w p q = cong₂ _∈ˢ_ p q

  module Existential (P : A → B) (s : B)
    (c : (x y : A) → x ≈ y → U (P x) ≡ U (P y))
    (u : (x : A) → fst (U (P x)) → fst (U s)) where

    predicate : N → hProp ℓ-zero
    predicate = Quotient.rec isSetHProp (λ x → U (P x)) c

    Fullness : Type₀
    Fullness = ∥ Σ A (λ x → P x ≡ s) ∥₁

    ordinaryExistence : Type₀
    ordinaryExistence = ∥ Σ N (λ x → fst (predicate x)) ∥₁

    truth-to-existence : Fullness → fst (U s) → ordinaryExistence
    truth-to-existence f h = Truncation.rec squash₁
      (λ { (x , p) → ∣ [ x ] , subst (λ b → fst (U b)) (sym p) h ∣₁ }) f

    existence-to-truth : ordinaryExistence → fst (U s)
    existence-to-truth = Truncation.rec (snd (U s))
      (λ { (x , h) → Quotient.elimProp {P = λ y → fst (predicate y) → fst (U s)}
        (λ y → isPropΠ (λ _ → snd (U s))) u x h })
```

### quotient/Finite.agda

SHA-256: `c1a0d7dcfb962e926950e79642ed60795014bac2b431a3dbf400d560a9cb0d05`

```text
{-# OPTIONS --cubical --safe --guardedness #-}
module Finite where

open import Cubical.Foundations.Prelude using (Type; _≡_; refl; sym; cong; cong₂; _∙_; subst; ℓ-zero)
open import Cubical.Foundations.HLevels using (hProp)
open import Cubical.Data.Bool using (Bool; false; true; not; _and_; isSetBool; false≢true)
open import Cubical.Data.Empty using (⊥; rec)
open import Cubical.Data.Sigma using (_×_; _,_; fst; snd)
open import Cubical.HITs.PropositionalTruncation using (∣_∣₁)
open import Quotient using (module Descent)

B Name : Type₀
B = Bool × Bool
Name = Bool × Bool

U : B → hProp ℓ-zero
U b = (fst b ≡ true) , isSetBool (fst b) true

_≈₂_ : Bool → Bool → Bool
false ≈₂ y = not y
true ≈₂ y = y

code-to-path : (x y : Bool) → x ≈₂ y ≡ true → x ≡ y
code-to-path false false p = refl
code-to-path false true p = rec (false≢true p)
code-to-path true false p = rec (false≢true p)
code-to-path true true p = refl

code-reflexive : (x : Bool) → x ≈₂ x ≡ true
code-reflexive false = refl
code-reflexive true = refl

path-to-code : (x y : Bool) → x ≡ y → x ≈₂ y ≡ true
path-to-code x y p = subst (λ z → x ≈₂ z ≡ true) p (code-reflexive x)

_≈ᴮ_ _∈ᴮ_ : Name → Name → B
x ≈ᴮ y = (fst x ≈₂ fst y) , (snd x ≈₂ snd y)
x ∈ᴮ y = (not (fst x) and fst y) , (not (snd x) and snd y)

left-coherence : (x y z : Name) → fst (U (x ≈ᴮ y)) → U (x ∈ᴮ z) ≡ U (y ∈ᴮ z)
left-coherence x y z p = cong
  (λ t → U ((not t and fst z) , false))
  (code-to-path (fst x) (fst y) p)

right-coherence : (x y z : Name) → fst (U (y ≈ᴮ z)) → U (x ∈ᴮ y) ≡ U (x ∈ᴮ z)
right-coherence x y z p = cong
  (λ t → U ((not (fst x) and t) , false))
  (code-to-path (fst y) (fst z) p)

module Ordinary = Descent Name B U _≈ᴮ_ _∈ᴮ_
  (record
    { reflexive = λ x → code-reflexive (fst x)
    ; symmetric = λ x y p → path-to-code (fst y) (fst x) (sym (code-to-path (fst x) (fst y) p))
    ; transitive = λ x y z p q → path-to-code (fst x) (fst z)
      (code-to-path (fst x) (fst y) p ∙ code-to-path (fst y) (fst z) q)
    }) left-coherence right-coherence

x y z : Name
x = false , true
y = false , false
z = true , true

names-distinct : x ≡ y → ⊥
names-distinct p = false≢true (sym (cong snd p))

names-identified : Ordinary.[ x ] ≡ Ordinary.[ y ]
names-identified = Ordinary.equality-to-ordinary x y refl

classes-distinct : Ordinary.[ x ] ≡ Ordinary.[ z ] → ⊥
classes-distinct p = false≢true (Ordinary.equality-from-ordinary x z p)

ordinary-member : fst (Ordinary.[ x ] Ordinary.∈ˢ Ordinary.[ z ])
ordinary-member = refl

P : Name → B
P t = x ∈ᴮ t

s : B
s = true , false

_≤₂_ : Bool → Bool → Type₀
b ≤₂ c = b and c ≡ b

_≤ᴮ_ : B → B → Type₀
b ≤ᴮ c = (fst b ≤₂ fst c) × (snd b ≤₂ snd c)

and-true : (b : Bool) → b and true ≡ b
and-true false = refl
and-true true = refl

join-upper : (t : Name) → P t ≤ᴮ s
join-upper t = and-true (fst t) , refl

join-least : (b : B) → ((t : Name) → P t ≤ᴮ b) → s ≤ᴮ b
join-least b h = h z

module Witness = Ordinary.Existential P s
  (λ a b p → right-coherence x a b p)
  (λ _ _ → refl)

fullness : Witness.Fullness
fullness = ∣ z , refl ∣₁

ordinary-existence : Witness.ordinaryExistence
ordinary-existence = Witness.truth-to-existence fullness refl

existence-reflects-truth : Witness.ordinaryExistence → fst (U s)
existence-reflects-truth = Witness.existence-to-truth

open import Cubical.Data.Sum using (_⊎_; inl; inr)

⊤ᴮ ⊥ᴮ : B
⊤ᴮ = true , true
⊥ᴮ = false , false

_⊓_ : B → B → B
b ⊓ c = (fst b and fst c) , (snd b and snd c)

¬ᴮ_ : B → B
¬ᴮ b = not (fst b) , not (snd b)

filter-top : fst (U ⊤ᴮ)
filter-top = refl

filter-proper : fst (U ⊥ᴮ) → ⊥
filter-proper = false≢true

filter-meet : (b c : B) → fst (U b) → fst (U c) → fst (U (b ⊓ c))
filter-meet b c p q = cong₂ _and_ p q

filter-upward : (b c : B) → b ≤ᴮ c → fst (U b) → fst (U c)
filter-upward b c p q = cong (λ t → t and fst c) (sym q) ∙ fst p ∙ q

filter-decides : (b : B) → fst (U b) ⊎ fst (U (¬ᴮ b))
filter-decides (false , c) = inr refl
filter-decides (true , c) = inl refl

ordinary-inhabitant : Ordinary.N
ordinary-inhabitant = Ordinary.[ y ]
```

### model/QuotientStructure.agda

SHA-256: `8be3a14e87ef4e6f0b1214bbacb5a1998a11c7c522f9d29d99faa6e0d29c4499`

```text
{-# OPTIONS --cubical --safe --guardedness #-}

module QuotientStructure where

open import Base.Prelude
open import Base.Truth using ( hPropAlgebra )
open import FOL.ZFStructure using ( ZFStructure )
open import EqualityCoherence using ( EqualityCoherence )
open import Cubical.Relation.Binary using ( module BinaryRelation )
open BinaryRelation using ( isEquivRel )
import Cubical.HITs.SetQuotients as SQ
import Quotient

module Adapter (A B : Type ℓ-zero) (U : B → hProp ℓ-zero)
  (E M : A → A → B)
  (e : isEquivRel (λ x y → fst (U (E x y))))
  (l : (x y z : A) → fst (U (E x y)) → U (M x z) ≡ U (M y z))
  (r : (x y z : A) → fst (U (E y z)) → U (M x y) ≡ U (M x z)) where

  module Q = Quotient.Descent A B U E M e l r

  structure : ZFStructure (hPropAlgebra ℓ-zero)
  structure = record
    { S = Q.N
    ; isSetS = SQ.squash/
    ; _≈ˢ_ = λ x y → (x ≡ y) , SQ.squash/ x y
    ; _∈ˢ_ = Q._∈ˢ_
    }

  coherence : EqualityCoherence structure
  coherence = record
    { ≈-sound = λ p → p
    ; ≈-complete = λ p → p
    }
```


## Internal ultrafilter extraction: audited next obligation

The [bounded extraction audit](k0-ultrafilter-extraction-audit-2026-09.md) locates existing `hasPowerL`, `stageBound`, stage `orderAt`, `Bound (fst PB) (snd PB)`, `leastOf` and uniqueness. The root checked the crucial signatures. This is source evidence, not a newly typechecked construction.

The candidate U must belong to the L-internal power set PB of B. Its underlying ambient V set can be embedded into a sufficiently large constructible stage, whose existing strict well-order supports least-element selection. The candidate predicate lifts stage members back to the restricted L carrier and requires membership in PB plus the internal ultrafilter clauses. Subtype equality handles the projection/lifting proof terms. This avoids a presumed global well-order of L and avoids eliminating a mere existence directly into arbitrary host data.

Remaining work, in dependency order:

1. Check this stage-bounded extraction against an abstract proposition-valued candidate predicate and its precise truncated existence premise, including the successor universe and LEM budget.
2. Prove ordinary ultrafilter existence inside the selected ground profile for an internally coded nontrivial Boolean algebra. Completeness is not a prerequisite of that existence theorem. Existing `L⊨ZFC` is a source of axioms, not an implementation of all their consequences.
3. Prove the Boolean carrier/operation decoding and the ordinary ultrafilter laws after interpretation.
4. Derive the generic descent assumptions from Boolean equality/congruence and ultrafilter laws, then prove recursive all-formula quotient truth over the shared syntax. Fullness must be constructed for the intended internal names; the finite witness does not supply it.
5. Validate universe-polymorphic quotient realization and the actual ordinary ZFC profile, before instantiating the Cohen application. K0 remains open; this batch implements neither K12 in full nor trophy 3.
