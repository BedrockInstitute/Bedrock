# K0 final representation decision

Date: 2026-09-09. Source baseline: `0504fe27`. Status: **K0 complete at the six-item representation gate**. This accepts the implementation architecture, not the full forcing theorems or T3. All proof work remains temporary; production implementation starts with K1. The [exit checklist](k0-exit-checklist-2026-09.md) defines the unchanged acceptance scope.

## Selected representation and component boundaries

Use actual material ground codes, with the host language handling dependent interfaces and safe recursion. In the L backend let k = ℓ-suc ℓ and S be the actual L carrier. Select `Name B = Σ n : S. ⟨ IsName B n ⟩`, an h-set at level k. A weighted entry is an actual internal ordered pair. Multiple weights for one child are permitted; do not normalize these entries into a host function. Raw equality and Boolean equality remain distinct, as the checked zero-weight example demonstrates.

Ground realization and ordinary model satisfaction are separate interfaces. A transitive ground realization supplies faithful equality/membership decoding, internal set constructors, the relevant axiom profile, and external accessibility. Transitive restriction inherits accessibility from HIT-V; ordinary first-order Foundation does not supply it. The L instance supplies actual decoding and existing axioms under its existing LEM assumption. An arbitrary transitive class does not automatically satisfy ZF. The final quotient only needs the ordinary first-order profile, not the strong existing model record or external well-foundedness.

Internal supports, closed name families, operation graphs and admitted index families must be actual ground sets. The checked L name-recognition, omega closure and pair-recursion path settle this representation. A generic ground adapter must prove the corresponding closure and decoding laws; it may not receive unrestricted host-family closure as an implicit convenience.

Keep both public forcing interfaces. The poset interface owns conditions, dense sets, generic filters, presentation-sensitive combinatorics and future iteration/support descriptions. The Boolean interface owns shared atomic/formula values, admitted joins, mixing and ordinary-ultrafilter quotient semantics. The certified converter constructs model-relative completion and proves map, density and semantic transport. It is a mathematical constructor with correctness certificates, not an unchecked compiler. Nonseparative conditions may have identical images. General regular-open completion and its laws remain K2; the finite internally coded test is its representation evidence. Bridges must state local theory and model-relative completeness assumptions explicitly. They do not identify every Boolean-valued model with a generic extension or preserve every raw presentation property.

## Universe and assumption ledger

| Object or operation | Selected level / requirement | Evidence or implementation owner |
|---|---|---|
| L carrier S and material names | Type k, h-sets; k = ℓ-suc ℓ | Actual name and closure probes |
| Carrier of an internal Boolean set B | Σ b : S. b ∈ B, at Type k | Ground coding and powerset probes |
| Boolean equality/membership values | Functions into that carrier | Atomic table route; full laws K4 |
| Interpreted ultrafilter | B-carrier → hProp k, from internal membership | Fixed-witness extraction below; UF laws K13 |
| Ordinary quotient N | Type k, h-set | `UniverseQuotient`, including successor-level instance |
| Ordinary membership | N → N → hProp k | Checked quotient descent |
| Fullness and ordinary existential | Propositional truncations at Type k | Checked existential transfer |
| hProp k and structure packaging | May live at a successor level as types of structures | Does not require LEM at that successor level or resizing |
| L selection/classical backend | Existing LEM k | Existing stage well-order and bounded extraction |
| Host AC, CC, DC, Zorn, BPI, new resizing axioms | Forbidden | No such assumption in the two new probe interfaces |
| Internal AC | Object-theory axiom/theorem, discharged for L | Later internal Collection/mixing/ultrafilter proofs |
| Supplied generic filter | Permitted in general extension theorem | Must not remain a premise of the final T3 constructor |

The quotient probe is universe-polymorphic with A and B at the same level. This includes the actual intended level k; it does not assert arbitrary mixed-level resizing. Its equivalence and compatibility arguments are proof obligations, not theorems about arbitrary operations E and M.

## Quantifiers and ordinary-model extraction contract

Preserve this proof order: material-name recognition → fixed atomic graph and exact reading → Separation of attained values inside B → admitted supremum and upper-bound transfer → formula induction with fixed-formula compilation → ground Collection/rank bounds and mixing → fullness and extension axiom transfer. Never use extension Replacement to construct its own forcing semantics. Collecting values does not choose a name per value. The [actual value-set test](k0-atomic-value-set-2026-09.md) checks this distinction.

For each fixed formula φ and parameters a, the later fullness theorem must supply `∥ Σ τ : Name B. value(φ(τ,a)) ≡ value(∃x φ(x,a)) ∥₁`. It must derive the required internally coded bounded witness family, rank bounds and mixing from the ground theory and prove value correctness. No internal global truth predicate or host selection across all formulas is assumed. Fullness is eliminated only into ordinary truncated existence or a proposition U(s). The checked quotient existential transfer never returns a chosen raw name or quotient section.

For the final L instance, construct a nontrivial internal Boolean algebra B with operation/carrier correctness. In L, prove the fixed first-order ultrafilter theorem to obtain `∥ Σ U : S. U ∈ 𝒫(B) × UF_B(U) ∥₁`. Here UF_B must be a specific formula with exact reading into properness, upward closure, finite-meet closure and complement decisions for the coded operations. Its existence proof must use L's internal ZFC; it remains K13, not a new hypothesis of T3.

The checked extraction path uses bound 𝒫(B), its existing L stage, the proved stage well-order and the unique least satisfying witness. `BoundedExtraction` eliminates into the proposition of being that least witness before projecting actual data. This is justified bounded selection in L, not choice on arbitrary host types. The new `InternalWitnessExtraction` composes that result with a fixed formula and reading theorem: from truncated bounded satisfaction it returns an actual U, its decoded specification and the interpreted predicate b ∈ U, proved contained in B. Different proofs of existence give equal chosen outputs. This probe does not instantiate UF_B or prove existence.

After interpreting this actual U, derive the quotient equivalence, membership compatibility, formula congruence and ultrafilter truth laws. `UniverseQuotient` already checks effective equality, binary membership descent, ordinary `ZFStructure` packaging and the existential transfer at level k. Full all-formula truth and every ZFC schema remain K12-K14. Their contracts expose the missing mathematical proofs without leaving a choice or universe operation unexplained. Neither ordinary model existence nor the exact final T3 assumption theorem is claimed proved by this audit.

## Acceptance and next work

| Item | Decision / checked evidence | Status |
|---|---|---|
| E1 | [Transitive ground and L axiom/code instance](k0-ground-completion-adapters-2026-09.md); keep ordinary and transitive profiles separate | Passed |
| E2 | Material h-set names, actual supports, recognition and external safe recursion; levels selected above; [name evidence](k0-internal-names-probes-2026-09.md) | Passed |
| E3 | [Actual weighted membership, equality and representative substitution](k0-material-atomic-example-2026-09.md) | Passed at representative boundary |
| E4 | [Internally attained atomic values and admitted join](k0-atomic-value-set-2026-09.md), with noncircular quantifier order | Passed at instance boundary |
| E5 | [Actual L finite completion carriers and maps](k0-ground-completion-adapters-2026-09.md), including dense noninjective map | Passed at presentation boundary |
| E6 | Integrated contracts above plus the two checked sources below and [bounded extraction](k0-bounded-extraction-probes-2026-09.md) | Passed |

K0 is closed. The next bounded task is K1: implement shared ordinary ZFC/CH/GCH interpretations and equality coherence, separate the transitive realization contract, then adapt existing L results without changing their statements or LEM budget. Production placement must be coordinated with the separate teaching work before source changes. K2 completion, K3 names and K4 shared semantics follow their dependency order. Do not promote every exploratory probe as a production module or duplicate proofs across the two interfaces.

T1 and T2 remain proved. General forcing, T3's actual ordinary non-CH model, its combination with L as semantic CH independence, and T4 ground definability remain unproved. K0 closure is not evidence that every future theorem fits the target assumptions. If implementation exposes a stronger requirement, revise or prove the missing construction explicitly; never silently introduce host choice, higher LEM or a supplied ultrafilter into the final constructor.

## Validation

Both Agda checks exited 0. Scoped prose and glossary gates on all eight changed notes exited 0; `git diff --check` passed. Both archived sources match the checked files byte-for-byte with verified SHA-256, safe headers and no forbidden proof markers. All 123 tracked production source files and their temporary baseline copies match `0504fe27`; 133 relative documentation links resolve. No whole-tree build was run for this probe/document-only change.

## Reproducible final probes

Both new files checked with exit 0 in the common temporary compile root using `GHCRTS="-A64m -I0 -M8g" agda src/FILE.agda`. At most two Agda processes were permitted. The witness probe imports the previously archived `BoundedExtraction` and `InternalPowersetSupremum`; the quotient uses the repository foundations and Cubical set quotients. Safe checking does not mean their explicit mathematical inputs have been discharged. Snapshots below preserve the exact checked sources.

### UniverseQuotient.agda

SHA-256: `645bcdfef066c2f9c0738743754462e0b7fd2bee71f33861ce5c3466168fa175`.

```text
{-# OPTIONS --cubical --safe --guardedness #-}

module UniverseQuotient where

open import Base.Prelude
open import Base.Truth using ( hPropAlgebra )
open import FOL.ZFStructure using ( ZFStructure )
open import Cubical.Foundations.HLevels using ( hProp; isSetHProp; isPropΠ )
open import Cubical.Foundations.Univalence using ( hPropExt )
open import Cubical.Relation.Binary using ( module BinaryRelation )
open BinaryRelation using ( isEquivRel )
import Cubical.HITs.SetQuotients as Quotient
import Cubical.HITs.PropositionalTruncation as Truncation
open Truncation using ( ∥_∥₁; ∣_∣₁; squash₁ )

module Descent {ℓ : Level} (A B : Type ℓ) (U : B → hProp ℓ)
  (E M : A → A → B)
  (equivalence : isEquivRel (λ x y → fst (U (E x y))))
  (left-compatible : (x y z : A) → fst (U (E x y))
    → U (M x z) ≡ U (M y z))
  (right-compatible : (x y z : A) → fst (U (E y z))
    → U (M x y) ≡ U (M x z)) where

  _≈_ : A → A → Type ℓ
  x ≈ y = fst (U (E x y))

  N : Type ℓ
  N = A Quotient./ _≈_

  [_] : A → N
  [_] = Quotient.[_]

  _∈ˢ_ : N → N → hProp ℓ
  _∈ˢ_ = Quotient.rec2 isSetHProp
    (λ x y → U (M x y)) left-compatible right-compatible

  equality-to-ordinary : (x y : A) → x ≈ y → [ x ] ≡ [ y ]
  equality-to-ordinary = Quotient.eq/

  equality-from-ordinary : (x y : A) → [ x ] ≡ [ y ] → x ≈ y
  equality-from-ordinary =
    Quotient.effective (λ x y → snd (U (E x y))) equivalence

  equality-effective : (x y : A) → ([ x ] ≡ [ y ]) ≡ (x ≈ y)
  equality-effective x y = hPropExt
    (Quotient.squash/ ([ x ]) ([ y ]))
    (snd (U (E x y)))
    (equality-from-ordinary x y)
    (equality-to-ordinary x y)

  membership-at-names : (x y : A) → [ x ] ∈ˢ [ y ] ≡ U (M x y)
  membership-at-names x y = refl

  membership-coherent : (x y z w : N) → x ≡ y → z ≡ w
    → x ∈ˢ z ≡ y ∈ˢ w
  membership-coherent x y z w p q = cong₂ _∈ˢ_ p q

  structure : ZFStructure (hPropAlgebra ℓ)
  structure = record
    { S = N
    ; isSetS = Quotient.squash/
    ; _≈ˢ_ = λ x y → (x ≡ y) , Quotient.squash/ x y
    ; _∈ˢ_ = _∈ˢ_
    }

  module Existential (P : A → B) (s : B)
    (compatible : (x y : A) → x ≈ y → U (P x) ≡ U (P y))
    (upper : (x : A) → fst (U (P x)) → fst (U s)) where

    predicate : N → hProp ℓ
    predicate = Quotient.rec isSetHProp (λ x → U (P x)) compatible

    Fullness : Type ℓ
    Fullness = ∥ Σ A (λ x → P x ≡ s) ∥₁

    ordinaryExistence : Type ℓ
    ordinaryExistence = ∥ Σ N (λ x → fst (predicate x)) ∥₁

    truth-to-existence : Fullness → fst (U s) → ordinaryExistence
    truth-to-existence fullness truth = Truncation.rec squash₁
      (λ { (x , p) →
        ∣ [ x ] , subst (λ b → fst (U b)) (sym p) truth ∣₁ }) fullness

    existence-to-truth : ordinaryExistence → fst (U s)
    existence-to-truth = Truncation.rec (snd (U s))
      (λ { (x , truth) →
        Quotient.elimProp {P = λ y → fst (predicate y) → fst (U s)}
          (λ y → isPropΠ (λ _ → snd (U s))) upper x truth })

module SuccessorLevel {k : Level}
  (A B : Type (ℓ-suc k)) (U : B → hProp (ℓ-suc k))
  (E M : A → A → B)
  (equivalence : isEquivRel (λ x y → fst (U (E x y))))
  (left-compatible : (x y z : A) → fst (U (E x y))
    → U (M x z) ≡ U (M y z))
  (right-compatible : (x y z : A) → fst (U (E y z))
    → U (M x y) ≡ U (M x z))
  = Descent A B U E M equivalence left-compatible right-compatible
```

### InternalWitnessExtraction.agda

SHA-256: `4e113e49fc6d7aaf9dbe7771f70614341e419935a709af3daf7438e6243b2e97`.

```text
{-# OPTIONS --cubical --safe --guardedness #-}

open import Base.Prelude
open import Base.Truth
open import Base.Classical using ( LEM )

module InternalWitnessExtraction {ℓ : Level} (lem : LEM (ℓ-suc ℓ)) where

open import FOL.ZFStructure using ( module hPropStructure )
open import FOL.Syntax using ( Formula )
open import L.Constructible {ℓ} using ( 𝒮ʟ )
open import FOL.Semantics (hPropAlgebra (ℓ-suc ℓ)) 𝒮ʟ using ( module At )
import FOL.ZFModel as Model
import InternalPowersetSupremum
import BoundedExtraction
import Cubical.HITs.PropositionalTruncation as PT
open PT using ( ∥_∥₁ )

open hPropStructure 𝒮ʟ using ( S; _∈ˢ_ )
open At S id using ( _⊨_ )

module For (B : S) (formula : Formula S 1)
  (Decoded : S → hProp (ℓ-suc ℓ))
  (reading : ∀ U → ((U ∷ []) ⊨ formula) ≡ Decoded U) where

  module Ground = InternalPowersetSupremum.Ground lem using ( 𝒫; hasPower )

  bound : S
  bound = Ground.𝒫 B

  Internal : S → hProp (ℓ-suc ℓ)
  Internal U = (U ∷ []) ⊨ formula

  Candidate : Type (ℓ-suc ℓ)
  Candidate = Σ[ U ∈ S ] ⟨ U ∈ˢ bound ⟩ × ⟨ Internal U ⟩

  DecodedCandidate : Type (ℓ-suc ℓ)
  DecodedCandidate = Σ[ U ∈ S ] ⟨ U ∈ˢ bound ⟩ × ⟨ Decoded U ⟩

  module Selection = BoundedExtraction lem
    using ( extract; extract-independent )

  decode : Candidate → DecodedCandidate
  decode (U , bounded , holds) = U , bounded , subst ⟨_⟩ (reading U) holds

  choose : ∥ Candidate ∥₁ → DecodedCandidate
  choose exists = decode (Selection.extract bound Internal exists)

  independent : ∀ e f → choose e ≡ choose f
  independent e f = cong decode (Selection.extract-independent bound Internal e f)

  module Chosen (exists : ∥ Candidate ∥₁) where

    U : S
    U = fst (choose exists)

    predicate : S → hProp (ℓ-suc ℓ)
    predicate b = b ∈ˢ U

    specification : ⟨ Decoded U ⟩
    specification = snd (snd (choose exists))

    contained : ∀ b → ⟨ predicate b ⟩ → ⟨ b ∈ˢ B ⟩
    contained = subst ⟨_⟩ (Model.℩-spec 𝒮ʟ (Ground.hasPower B) U)
      (fst (snd (choose exists)))
```

