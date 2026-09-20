# K0 actual powerset recursion tables

Date: 2026-09-09. Source baseline: `82e0dd98`. Four safe temporary probes checked. This continues the [finite Step and locality probes](k0-powerset-step-formula-2026-09.md). K0 remains open.

## From coordinates to encoded keys

`PowersetPairStep.For X.WithDomain C` fixes the actual powerset bound and coordinate domain. Its semantic Step(H,p,b) says merely that there are x,y in C with p = pair(x,y) and the previously checked raw-coordinate Step(C,x,y,H,b). Its three-variable finite formula has an exact reading theorem at every environment, including raw p not known to lie in the product. Domain membership is part of the formula, not a premise silently required by the reading theorem.

The formula uses bounded coordinate quantifiers and the existing pair formula, then specializes the domain parameter using the shared substitution theorem. `pair-in` inserts any typed coordinate witness. `pair-out` uses ordered-pair injectivity to identify arbitrary existential coordinates with the requested pair, eliminating truncation only into the raw Step proposition. No representative choice is needed.

## Opaque packaging of the existing recursion result

`BoundedTableRealization` packages the existing generic engine result as a record containing the table, typed values, graph membership, equations, goodness and boundedness. Its opaque `realize` theorem constructs this record solely from the already proved engine projections. It adds neither a recursion proof nor a choice principle.

This is a proof abstraction boundary: clients use checked record fields instead of repeatedly exposing the implementation of the candidate union and well-founded readout. The concrete adapter supplies every required law. Production integration should make this cohesive result interface part of the generic kernel rather than preserve a second proof implementation or re-export its internal module tree.

## Actual bounded recursion for any internal C

`PowersetAtomicTable.For X C` constructs D = C × C and instantiates the existing bounded recursion engine. It supplies all previously open instance arguments:

- The actual name-pair dependency relation, its finite formula and reading theorem.
- The encoded-key Step formula and exact reading theorem.
- Step uniqueness, transported through the existing unique product decoder.
- Step locality, obtained by transporting predecessor relations along the decoded pair equality and reusing raw-coordinate locality.
- Step admission, using the actual raw output and typed pair insertion.
- Restricted well-foundedness from `NamePairDependency.Domain C.wf`.

The module calls the packaged `realize` theorem with the proved `unique`, `locality`, `Keys.wf` and `admit` arguments. None of those laws, a good union table, candidate compatibility, a recursive graph or a well-foundedness certificate remains an input to this actual instance. The existing kernel supplies the internal candidate family, compatible union, goodness, totality and readout; no recursion proof is duplicated here.

The result includes an actual internal table, a value in B at every key in D, the encoded Step equation, and the raw coordinate equation at each pair(x,y) with x,y in C. It also exposes graph membership and table functionality directly. The underlying kernel proves the candidate union good and bounded, and supplies total readout; the concrete adapter avoids re-exporting its entire internal namespace.

This construction is valid for arbitrary actual C: it solves the recursion restricted to C × C, and the image expressions retain their C bounds. It does not assert that such C contains all genuine children of an arbitrary name. That closure requirement belongs to the next adapter and to the later domain-independence/adequacy proof.

## Actual table at a pair of valid names

`PowersetNameTable.For X.AtPair x y validX validY` uses the previously proved name-closure construction to obtain a child-closed actual `closedSet` containing x and y. It instantiates `PowersetAtomicTable` on that set and returns:

- the actual internal `table`;
- the initial pair's value and its B-membership proof;
- membership of pair(pair(x,y),value) in the table;
- the raw expanded coordinate equation at x,y.

Only X, the names and their validity proofs are supplied, in addition to the existing LEM parameter. The domain, closure, dependency well-foundedness and all Step laws are built or proved. Because the chosen coordinate domain is child-closed, relevant predecessor pairs of its valid names remain in its product.

The construction order matters: first choose C, then instantiate the C-dependent Step and recursion engine. The earlier `NamePairRecursion` probe accepts a Step before choosing its name domain; its conditional wrapper is not an additional proof home. This concrete adapter reuses the closure and dependency components and the underlying solved bounded engine directly, avoiding a second closure construction or a duplicated recursion proof. Production interfaces should preserve that dependency order.

Subsequent evidence: the [closed-domain independence probes](k0-closed-domain-independence-2026-09.md) implement the proposed common-domain restriction route and prove equality of the constructed powerset table values at shared coordinates. The remaining-work list below records this earlier checkpoint; its domain-independence item is now discharged. Global atomic formula adequacy and semantic laws remain open.

## Current boundary and next work

This closes the actual powerset-instance recursion-table check, including a pair of genuine valid names. The resulting theorem is a local internal-table theorem for the expanded equations. It is not yet a global Boolean-valued equality definition, a forcing theorem, a Cohen algebra construction, or a non-CH model.

A scoped design audit identified a route to domain independence that preserves the existing comparison proof home. Form E = C ∩ C′ internally, restrict both tables by finite Separation to E × E keys, and use support-sensitive image congruence to prove their Step equations survive restriction. Then apply the existing same-domain compatibility theorem at E. The restrictions, cross-domain support transport and preserved-goodness proofs remain to be implemented; there is no need to introduce a second comparison induction merely because the initial domains differ.

Next work:

1. Prove closed-domain independence: tables constructed over different adequate closed coordinate domains must give the same value at shared name pairs. This requires the relevant image/domain comparison, not merely same-domain table uniqueness.
2. Package a single fixed atomic equality formula quantifying a suitable domain and table; prove its soundness, completeness and unique-value reading. Do the analogous membership image construction.
3. Prove the required atomic semantic laws and continue the general Boolean/regular-open realization. The powerset instance does not replace the Cohen completion or the general forcing interfaces.
4. Continue the quantifier, Collection/fullness, ordinary-model extraction and geology obligations under the no-host-choice audit.

The final K0 architecture gate and the endpoint LEM-only budget are still open. No host choice or resizing principle was added; T3 and T4 remain unchanged.

## Verification and source snapshots

From `/tmp/bedrock-k0-probes/extraction/compile-root`:

```sh
GHCRTS="-A64m -I0 -M8g" agda src/BoundedTableRealization.agda
GHCRTS="-A64m -I0 -M8g" agda src/PowersetPairStep.agda
GHCRTS="-A64m -I0 -M8g" agda src/PowersetAtomicTable.agda
GHCRTS="-A64m -I0 -M8g" agda src/PowersetNameTable.agda
```

All exited 0 and retain `--safe`. The complete table instance is substantially heavier to check than the formula-only probes; it was checked under the same 8 GB per-process cap. Temporary prefix checks were used to isolate interface elaboration, and the final source uses explicit admission/output types rather than relying on inference for the largest expressions. One transparent full check was stopped after about eight minutes with roughly 3.7 GB resident memory; this was an interrupted diagnostic, not a mathematical counterexample or a completed check. The final implementation uses the opaque generic result record for its public table/readout interface and passed its own full scoped check.

Scoped prose/glossary gates, snapshot/hash and local-link checks, and `git diff --check` passed. All 123 tracked production source files and copied probe-baseline versions match `82e0dd98` byte-for-byte. No production source changed. Whole-tree and chapter gates were not run for this temporary-probe/documentation change.

### BoundedTableRealization.agda

SHA-256: `efb5204fafebdfbb5994c824bafb16b9b61527e8848310a1913b6fc658f4c123`.

```text
{-# OPTIONS --cubical --safe --guardedness #-}

open import Base.Prelude
open import Base.Truth
open import Base.Classical using ( LEM )

module BoundedTableRealization {ℓ : Level} (lem : LEM (ℓ-suc ℓ)) where

open import FOL.ZFStructure using ( module hPropStructure )
open import L.Constructible {ℓ} using ( 𝒮ʟ )
open import FOL.Syntax using ( Formula )
open import FOL.Semantics (hPropAlgebra (ℓ-suc ℓ)) 𝒮ʟ using ( module At )
open import L.Coding.Model {ℓ} using ( prʟ )
import BoundedTableRecursion
open import Cubical.Induction.WellFounded using ( WellFounded )
import Cubical.HITs.PropositionalTruncation as PT
open PT using ( ∥_∥₁ )

open hPropStructure 𝒮ʟ using ( S; _∈ˢ_ )
open At S id using ( _⊨_ )

module WithStep
  (R : S → S → hProp (ℓ-suc ℓ))
  (rAt : ∀ {n} → Fin n → Fin n → Formula S n)
  (rAt-reading : ∀ {n} (y x : Fin n) (γ : Vec S n)
    → (γ ⊨ rAt y x) ≡ R (lookup y γ) (lookup x γ))
  (Step : S → S → S → hProp (ℓ-suc ℓ))
  (stepAt : ∀ {n} → Fin n → Fin n → Fin n → Formula S n)
  (stepAt-reading : ∀ {n} (h x b : Fin n) (γ : Vec S n)
    → (γ ⊨ stepAt h x b) ≡ Step (lookup h γ) (lookup x γ) (lookup b γ)) where

  module Engine = BoundedTableRecursion.WithStep lem R rAt rAt-reading
    Step stepAt stepAt-reading

  module Construction (D B : S) where

    module Recursor = Engine.Construction D B
    open Recursor.Base.Laws using ( Bounded; Covers; Agree )
    open Recursor.Base.Good.Functionality using ( Functional )

    record Realization : Type (ℓ-suc ℓ) where
      field
        table         : S
        value         : ∀ p → ⟨ p ∈ˢ D ⟩ → S
        value-in-B    : ∀ p pD → ⟨ value p pD ∈ˢ B ⟩
        graph         : ∀ p pD → ⟨ prʟ p (value p pD) ∈ˢ table ⟩
        equation      : ∀ p pD → ⟨ Step table p (value p pD) ⟩
        table-good    : Recursor.Base.Good.Good table
        table-bounded : Recursor.Base.Laws.Bounded table

    opaque
      realize :
        (unique : ∀ H p c d → Bounded H → Functional H → ⟨ p ∈ˢ D ⟩
          → ⟨ c ∈ˢ B ⟩ → ⟨ d ∈ˢ B ⟩ → Covers H p
          → ⟨ Step H p c ⟩ → ⟨ Step H p d ⟩ → c ≡ d)
        (locality : ∀ H K p c → Bounded H → Bounded K → Functional H → Functional K
          → ⟨ p ∈ˢ D ⟩ → ⟨ c ∈ˢ B ⟩ → Covers H p → Covers K p → Agree H K p
          → ⟨ Step H p c ⟩ → ⟨ Step K p c ⟩)
        (wf : WellFounded Recursor.Compatibility.Dependency)
        (admit : ∀ H p → Bounded H → Functional H → ⟨ p ∈ˢ D ⟩ → Covers H p
          → ∥ Σ[ b ∈ S ] (⟨ b ∈ˢ B ⟩ × ⟨ Step H p b ⟩) ∥₁)
        → Realization
      realize unique locality wf admit = record
        { table = Recursor.Solve.table unique locality wf admit
        ; value = Recursor.Solve.value unique locality wf admit
        ; value-in-B = Recursor.Solve.value-in-B unique locality wf admit
        ; graph = Recursor.Solve.value-in-table unique locality wf admit
        ; equation = Recursor.Solve.equation unique locality wf admit
        ; table-good = Recursor.Solve.table-good unique locality wf admit
        ; table-bounded = Recursor.Solve.table-bounded unique locality wf admit
        }
```

### PowersetPairStep.agda

SHA-256: `b02713661915ab4f6e5d53974cf7f275b8054c3a64c05b2280ac9979bd56ea5f`.

```text
{-# OPTIONS --cubical --safe --guardedness #-}

open import Base.Prelude
open import Base.Truth
open import Base.Classical using ( LEM )

module PowersetPairStep {ℓ : Level} (lem : LEM (ℓ-suc ℓ)) where

open import FOL.ZFStructure using ( module hPropStructure )
open import FOL.Syntax using ( Formula; var; _∧̇_; ∃̇∈ )
open import L.Constructible {ℓ} using ( 𝒮ʟ )
open import FOL.Semantics (hPropAlgebra (ℓ-suc ℓ)) 𝒮ʟ using ( module At )
open import L.Coding.Model {ℓ} using ( prʟ; prAtL; prʟ-inj )
open import PairFormulaReading {ℓ} using ( reading )
open import FormulaParameters (hPropAlgebra (ℓ-suc ℓ)) 𝒮ʟ
  using ( instantiate; instantiate-reading )
import PowersetStepFormula {ℓ} lem as Powerset
open import Cubical.Functions.Logic using ( ⇔toPath )
open import Cubical.Foundations.Prelude using ( subst2 )
import Cubical.HITs.PropositionalTruncation as PT
open PT using ( ∥_∥₁; ∣_∣₁ )

open hPropStructure 𝒮ʟ using ( S; _∈ˢ_; isSetS )
open At S id using ( _⊨_ )

module For (X : S) where

  module Raw = Powerset.For X

  module WithDomain (C : S) where

    Step : S → S → S → hProp (ℓ-suc ℓ)
    Step H p b = (∥ Σ[ x ∈ S ] Σ[ y ∈ S ]
      ⟨ x ∈ˢ C ⟩ × ⟨ y ∈ˢ C ⟩ × (p ≡ prʟ x y) × ⟨ Raw.Step C x y H b ⟩ ∥₁) ,
      PT.squash₁

    shiftThree : ∀ {n} → Fin n → Fin (suc (suc (suc n)))
    shiftThree i = suc (suc (suc i))

    parameterized : ∀ {n} → Fin n → Fin n → Fin n → Formula S (suc n)
    parameterized H p b = ∃̇∈ (var zero) (∃̇∈ (var (suc zero))
      (prAtL (shiftThree p) (suc zero) zero
      ∧̇ Raw.stepAt (suc (suc zero)) (suc zero) zero
        (shiftThree H) (shiftThree b)))

    stepAt : ∀ {n} → Fin n → Fin n → Fin n → Formula S n
    stepAt H p b = instantiate (C ∷ []) (parameterized H p b)

    module Reading {n : ℕ} (H p b : Fin n) (γ : Vec S n) where

      specialization = instantiate-reading (C ∷ []) (parameterized H p b) γ

      forward : ⟨ γ ⊨ stepAt H p b ⟩
        → ⟨ Step (lookup H γ) (lookup p γ) (lookup b γ) ⟩
      forward holds = PT.rec PT.squash₁
        (λ { (x , xC , ys) → PT.map
          (λ { (y , yC , pair , raw) → x , y , xC , yC ,
            subst ⟨_⟩
              (reading (shiftThree p) (suc zero) zero (y ∷ x ∷ C ∷ γ)) pair ,
            subst ⟨_⟩
              (Raw.step-reading (suc (suc zero)) (suc zero) zero
                (shiftThree H) (shiftThree b) (y ∷ x ∷ C ∷ γ)) raw }) ys })
        (subst ⟨_⟩ specialization holds)

      backward : ⟨ Step (lookup H γ) (lookup p γ) (lookup b γ) ⟩
        → ⟨ γ ⊨ stepAt H p b ⟩
      backward = PT.rec (snd (γ ⊨ stepAt H p b))
        (λ { (x , y , xC , yC , pair , raw) → subst ⟨_⟩ (sym specialization)
          ∣ x , xC , ∣ y , yC ,
            subst ⟨_⟩
              (sym (reading (shiftThree p) (suc zero) zero (y ∷ x ∷ C ∷ γ))) pair ,
            subst ⟨_⟩
              (sym (Raw.step-reading (suc (suc zero)) (suc zero) zero
                (shiftThree H) (shiftThree b) (y ∷ x ∷ C ∷ γ))) raw ∣₁ ∣₁ })

      exact : (γ ⊨ stepAt H p b)
        ≡ Step (lookup H γ) (lookup p γ) (lookup b γ)
      exact = ⇔toPath forward backward

    step-reading : ∀ {n} (H p b : Fin n) (γ : Vec S n)
      → (γ ⊨ stepAt H p b)
        ≡ Step (lookup H γ) (lookup p γ) (lookup b γ)
    step-reading = Reading.exact

    pair-out : ∀ H x y b → ⟨ Step H (prʟ x y) b ⟩ → ⟨ Raw.Step C x y H b ⟩
    pair-out H x y b = PT.rec (snd (Raw.Step C x y H b))
      λ { (u , v , uC , vC , pair , raw) →
        subst2 (λ a c → ⟨ Raw.Step C a c H b ⟩)
          (sym (fst (prʟ-inj pair))) (sym (snd (prʟ-inj pair))) raw }

    pair-in : ∀ H x y b → ⟨ x ∈ˢ C ⟩ → ⟨ y ∈ˢ C ⟩
      → ⟨ Raw.Step C x y H b ⟩ → ⟨ Step H (prʟ x y) b ⟩
    pair-in H x y b xC yC raw = ∣ x , y , xC , yC , refl , raw ∣₁
```

### PowersetAtomicTable.agda

SHA-256: `dcd0d5fa416296bcbc67b60ce8a958a3716601f6ec1d0eeb9f1b72b3fa3c2a72`.

```text
{-# OPTIONS --cubical --safe --guardedness #-}

open import Base.Prelude
open import Base.Truth
open import Base.Classical using ( LEM )

module PowersetAtomicTable {ℓ : Level} (lem : LEM (ℓ-suc ℓ)) where

open import FOL.ZFStructure using ( module hPropStructure )
open import L.Constructible {ℓ} using ( 𝒮ʟ )
open import L.Coding.Model {ℓ} using ( prʟ )
import PowersetPairStep {ℓ} lem as PairSteps
import PowersetStepFormula {ℓ} lem as RawSteps
import InternalPowersetSupremum {ℓ} lem as Powersets
import NamePairDependency {ℓ} lem as Dependency
import BoundedTableRealization {ℓ} lem as Recursion
import Cubical.HITs.PropositionalTruncation as PT
open PT using ( ∥_∥₁; ∣_∣₁ )

open hPropStructure 𝒮ʟ using ( S; _∈ˢ_ )

module For (X C : S) where

  module Pair = PairSteps.For.WithDomain X C
  module Raw = RawSteps.For X
  module Algebra = Powersets.For X
  module Keys = Dependency.Domain C
  open Algebra using ( B )

  D : S
  D = Keys.Product.product

  module Engine = Recursion.WithStep Dependency.R Dependency.relationAt Dependency.relation-reading
    Pair.Step Pair.stepAt Pair.step-reading
  module Package = Engine.Construction D B
  module Recursor = Package.Recursor
  open Recursor.Base.Laws using ( Bounded; Covers; Agree )
  open Recursor.Base.Good.Functionality using ( Functional )

  module AtKey (p : S) (pD : ⟨ p ∈ˢ D ⟩) where

    decoded : Keys.Decoded p
    decoded = Keys.decode p pD

    x y : S
    x = fst (fst decoded)
    y = snd (fst decoded)

    xC : ⟨ x ∈ˢ C ⟩
    xC = fst (snd decoded)

    yC : ⟨ y ∈ˢ C ⟩
    yC = fst (snd (snd decoded))

    represents : p ≡ prʟ x y
    represents = snd (snd (snd decoded))

    out : ∀ H b → ⟨ Pair.Step H p b ⟩ → ⟨ Raw.Step C x y H b ⟩
    out H b holds = Pair.pair-out H x y b
      (subst (λ q → ⟨ Pair.Step H q b ⟩) represents holds)

    into : ∀ H b → ⟨ Raw.Step C x y H b ⟩ → ⟨ Pair.Step H p b ⟩
    into H b holds = subst (λ q → ⟨ Pair.Step H q b ⟩) (sym represents)
      (Pair.pair-in H x y b xC yC holds)

    relation-back : ∀ q → Dependency.Relation q (prʟ x y) → Dependency.Relation q p
    relation-back q = subst (Dependency.Relation q) (sym represents)

  unique : ∀ H p c d → Bounded H → Functional H → ⟨ p ∈ˢ D ⟩
    → ⟨ c ∈ˢ B ⟩ → ⟨ d ∈ˢ B ⟩ → Covers H p
    → ⟨ Pair.Step H p c ⟩ → ⟨ Pair.Step H p d ⟩ → c ≡ d
  unique H p c d bound functional pD cB dB covers pc pd =
    Raw.unique C Key.x Key.y H c d (Key.out H c pc) (Key.out H d pd)
    where
    module Key = AtKey p pD

  locality : ∀ H K p c → Bounded H → Bounded K → Functional H → Functional K
    → ⟨ p ∈ˢ D ⟩ → ⟨ c ∈ˢ B ⟩ → Covers H p → Covers K p → Agree H K p
    → ⟨ Pair.Step H p c ⟩ → ⟨ Pair.Step K p c ⟩
  locality H K p c boundH boundK functionalH functionalK pD cB coversH coversK agrees holds =
    Key.into K c (Transfer.transfer c (Key.out H c holds))
    where
    module Key = AtKey p pD
    module Tables = Raw.Tables C H K Key.x Key.y Key.xC Key.yC

    left-cover : Tables.Values.Previous.Covers H
    left-cover q qD edge = coversH q qD (Key.relation-back q edge)

    right-cover : Tables.Values.Previous.Covers K
    right-cover q qD edge = coversK q qD (Key.relation-back q edge)

    same : Tables.Values.Previous.Same
    same q b d qD edge bB dB graphH graphK =
      agrees q b d qD (Key.relation-back q edge) bB dB graphH graphK

    module Transfer = Tables.Agreement left-cover right-cover same

  admit : ∀ H p → Bounded H → Functional H → ⟨ p ∈ˢ D ⟩ → Covers H p
    → ∥ Σ[ b ∈ S ] (⟨ b ∈ˢ B ⟩ × ⟨ Pair.Step H p b ⟩) ∥₁
  admit H p bound functional pD covers =
    ∣ fst result , fst (snd result) , Key.into H (fst result) (snd (snd result)) ∣₁
    where
    module Key = AtKey p pD
    result : Σ[ b ∈ S ] (⟨ b ∈ˢ B ⟩ × ⟨ Raw.Step C Key.x Key.y H b ⟩)
    result = Raw.admit C Key.x Key.y H

  solution : Package.Realization
  solution = Package.realize unique locality Keys.wf admit

  table : S
  table = Package.Realization.table solution

  value : ∀ p → ⟨ p ∈ˢ D ⟩ → S
  value = Package.Realization.value solution

  value-in-B : ∀ p pD → ⟨ value p pD ∈ˢ B ⟩
  value-in-B = Package.Realization.value-in-B solution

  equation : ∀ p pD → ⟨ Pair.Step table p (value p pD) ⟩
  equation = Package.Realization.equation solution

  coordinate-equation : ∀ x y → (xC : ⟨ x ∈ˢ C ⟩) → (yC : ⟨ y ∈ˢ C ⟩)
    → ⟨ Raw.Step C x y table (value (prʟ x y) (Keys.Product.pair-in x y xC yC)) ⟩
  coordinate-equation x y xC yC = Pair.pair-out table x y
    (value (prʟ x y) (Keys.Product.pair-in x y xC yC))
    (equation (prʟ x y) (Keys.Product.pair-in x y xC yC))

  graph : ∀ p pD → ⟨ prʟ p (value p pD) ∈ˢ table ⟩
  graph = Package.Realization.graph solution

  functional : Functional table
  functional = fst (Package.Realization.table-good solution)
```

### PowersetNameTable.agda

SHA-256: `a851a8a7ba906f9e6522f99c7f2386ffd6dbbad46e0e2f27b1ddbf6d49de8019`.

```text
{-# OPTIONS --cubical --safe --guardedness #-}

open import Base.Prelude
open import Base.Truth
open import Base.Classical using ( LEM )

module PowersetNameTable {ℓ : Level} (lem : LEM (ℓ-suc ℓ)) where

open import FOL.ZFStructure using ( module hPropStructure )
open import L.Constructible {ℓ} using ( 𝒮ʟ )
open import L.Coding.Model {ℓ} using ( prʟ )
import ClosedNamePairDomain
import InternalPowersetSupremum
import PowersetAtomicTable

open hPropStructure 𝒮ʟ using ( S; _∈ˢ_ )

module For (X : S) where

  module Algebra = InternalPowersetSupremum.For lem X
  module Closed = ClosedNamePairDomain.For lem Algebra.B

  module AtPair (x y : S)
    (validX : ⟨ Closed.Names.IsName x ⟩)
    (validY : ⟨ Closed.Names.IsName y ⟩) where

    module Domain = Closed.PairOf x y validX validY

    closedSet : S
    closedSet = Domain.C

    module Atomic = PowersetAtomicTable.For lem X closedSet

    table : S
    table = Atomic.table

    value : S
    value = Atomic.value (prʟ x y) (snd Domain.initial)

    value-in-B : ⟨ value ∈ˢ Algebra.B ⟩
    value-in-B = Atomic.value-in-B (prʟ x y) (snd Domain.initial)

    graph : ⟨ prʟ (prʟ x y) value ∈ˢ table ⟩
    graph = Atomic.graph (prʟ x y) (snd Domain.initial)

    coordinate-equation :
      ⟨ Atomic.Raw.Step closedSet x y table value ⟩
    coordinate-equation =
      Atomic.coordinate-equation x y Domain.contains-x Domain.contains-y
```
