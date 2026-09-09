# K0 arbitrary good tables and a unique semantic value relation

Date: 2026-09-09. Source baseline: `3c5a78bf`. This extends the [closed-domain independence probes](k0-closed-domain-independence-2026-09.md). Three safe temporary probes are archived below. K0 remains open; production `src` is unchanged.

## Arbitrary good source tables

`PowersetTableRestriction.For X C E subset closed.WithTable H goodH` now handles any actual L set H satisfying the existing good-table condition for the C-indexed powerset step. The target E must be child-closed and contained in C. The source C need not be child-closed for this restriction theorem.

The exact source contract is weaker than initially planned: no source boundedness or totality argument is required. Goodness comprises functionality, predecessor downward closure and obedience on typed keys and values. Entries outside the relevant key/value product have no effect on the result. Restriction by internal Separation produces its own bound, and the existing generic preservation theorem supplies restricted goodness after the powerset expression transport proves Step preservation.

For any p in E × E and any b in B with pair(p,b) in H, `compare-value` proves b equal to the canonical table's value at p over E. The theorem concerns existing typed entries; it does not claim every good partial table contains every key. The original `For.value-equal` is the canonical-source specialization of this theorem. Its proof is shared, and the previous closed-domain independence client still checks.

## One semantic witness relation

For fixed X and B = P(X), `PowersetAtomicGraph.For X` defines the host proposition:

```text
Graph(x,y,b) = merely there exist actual L sets C and H such that
  C is child-closed,
  x and y belong to C,
  H is good for the C-indexed powerset step,
  b belongs to B,
  pair(pair(x,y),b) belongs to H.
```

`Good` reuses the recursion kernel's existing definition. `introduce` constructs this witness relation from the stated data. Comparing two witnesses restricts their tables to the common closed domain, applies the generalized `compare-value` twice, and uses equality transitivity. `unique` eliminates the two truncated witnesses only into equality of elements of the h-set S. Thus any two witnessed outputs agree, even if their source domains and source tables differ. There is no new comparison induction and no selection of a contributing table.

This is a globally quantified host relation over actual model elements. It is not yet represented by one fixed first-order formula, nor collected as an internal set of all atomic pairs. Its characterization below concerns the constructed expanded recursion values. Atomic Boolean equality/membership laws and agreement with a full forcing semantics remain separate obligations.

## General existence before the valid-name instance

`AtClosed C closed x y xC yC` first proves the general result for any supplied child-closed actual C containing x and y. It returns the existing canonical recursion value, proves it belongs to B, inserts the already constructed canonical good table as a Graph witness, and proves both directions:

```text
Graph(x,y,b) implies b = value
b = value implies Graph(x,y,b).
```

`exact` packages these directions as equality of h-propositions. The explicit `graph-prop : S → S → S → hProp` interface fixes the proposition type of that statement.

`AtNames x y validX validY` then uses the existing material-name closure theorem to provide C, its child closure and both memberships. It reuses the general `AtClosed` value, membership, existence and exact characterization. It does not assume a source table or choose a closed domain from a merely inhabited family. The checked instance gives existence for valid material names; no claim of totality for arbitrary raw x,y without a suitable closed container is made.

## A finite formula for the closure premise

`ClosedDomainFormula.closedAt C` is uniformly indexed by a formula variable C. Its all-environment reading is exactly the existing child-closure predicate:

```text
for every n in C, every z and every weight b,
  if pair(z,b) belongs to n, then z belongs to C.
```

The forward reading eliminates the merely existing child weight into the proposition z in C. The reverse reading supplies the given weight as a truncated witness. `closed-is-prop`, `out`, `into` and `closed-reading` are all checked. This discharges one component of the eventual fixed graph formula, without claiming that the whole graph formula is already available.

## Exact next syntax gate

Successor: the [fixed atomic graph formula probes](k0-fixed-atomic-graph-formula-2026-09.md) complete the four syntax APIs listed below. This section records the preceding batch's planned gate.

The next fixed-formula implementation has four explicit steps. These are planned APIs, not checked declarations in this batch.

| API | Required role | Existing proof to reuse |
|---|---|---|
| `productAt C D p` | Uniform membership predicate for the variable product domain | Actual product coding, pair reading and product membership specification |
| `pairStepAt C H p b` | Encoded-pair Step with C as a genuine formula variable | Existing parameterized pair-step template and uniform raw `stepAt` |
| `goodAt C H` | Uniform functionality, downward closure and obedience with the variable key domain | The existing three Good clauses, through a shared parameterized syntax interface |
| `graphAt x y b` | Bind C, H and a temporary pair code, then combine all readings | `closedAt`, `goodAt`, pair coding and table-entry syntax |

The source audit finds the pair-step template at `PowersetPairStep.agda:40-44`, its fixed-C specialization at lines 46-47, and the uniform raw Step at `PowersetStepFormula.agda:139-143`. Product construction currently inserts fixed bounds with constants in `ProductSet.agda:77-78`. The Good formula currently fixes D and B in `CodedGoodTables.agda:35`, uses constant D in lines 58-66, and exports its fixed-domain reading at lines 138-139. These locations refer to the unchanged temporary dependency sources recorded in the preceding probe ledgers.

The syntax must treat C, H, x, y, b and the temporary pair code as variables. X and its derived B may remain fixed parameters of this instance. A host expression such as the product of C with itself cannot be inserted as a constant under an object-language existential binder for C. Prove each reading for every environment, then compose the final fixed formula with the already checked semantic witness relation. Refine the existing generic Good syntax and derive fixed-domain clients through specialization; preserve one proof of each clause and the existing comparison kernel.

After fixed-formula reading, prove the membership image and the atomic semantic laws. General-ground adapters, the general Boolean/regular-open compiler, quantified value bounds, Collection/fullness and ordinary-model extraction remain open. T3 is still an actual ordinary non-CH model after the general forcing results; T4 remains ground definability.

## Assumptions and verification

This batch introduces no host AC, countable/dependent choice, BPI, ultrafilter selector, resizing or additional LEM level. The actual L constructions retain the existing `LEM (ℓ-suc ℓ)` parameter. Generic source-goodness and closed-container premises are stated explicitly, and the canonical-table/name instances discharge the relevant premises. Propositional truncation is eliminated into propositions in the witness-comparison and closure-reading proofs. This local audit does not certify the complete eventual T3 assumption budget.

From `/tmp/bedrock-k0-probes/extraction/compile-root`, all final commands exited 0:

```sh
GHCRTS="-A64m -I0 -M8g" agda src/PowersetTableRestriction.agda
GHCRTS="-A64m -I0 -M8g" agda src/PowersetClosedDomainIndependence.agda
GHCRTS="-A64m -I0 -M8g" agda src/ClosedDomainFormula.agda
GHCRTS="-A64m -I0 -M8g" agda src/PowersetAtomicGraph.agda
```

The coordinator checked the final semantic relation and reviewed the delegated restriction/closure results. At most two Agda processes ran concurrently, with the prescribed heap cap. The unchanged closed-domain independence client was checked as the relevant regression client.

One earlier complete graph check exhausted the 8 GB heap, exiting 251. Intermediate diagnostic checks were interrupted without completion. Prefix checks separately established comparison/uniqueness, the canonical value and its bound, canonical goodness, existence, and both implications. The remaining stalled declaration wrote both sides of an h-proposition equality as unannotated pairs. Giving `graph-prop` an explicit hProp return type made the final complete module check successfully. Explicit instance parameters, the shared Good definition and direct/scoped references remain in the final source; the trial opaque extensionality wrapper was removed. The final theorem still uses the library's ordinary proposition-extensionality proof. These diagnostic results identify an elaboration boundary, not a mathematical obstruction or a need for an extra axiom.

Scoped prose/glossary gates, exact snapshot/hash and local-link checks, and `git diff --check` passed. All 123 tracked production source files and their copied probe-baseline versions match `3c5a78bf` byte-for-byte. Whole-tree and trilingual chapter gates were not run for this temporary-probe/documentation change.

## Source snapshots

### PowersetTableRestriction.agda

SHA-256: `ddff7f5ade34b1459a4feaa42f1bde880accad424431d8dfa9f32076ac999c78`.

```text
{-# OPTIONS --cubical --safe --guardedness #-}

open import Base.Prelude
open import Base.Truth
open import Base.Classical using ( LEM )

module PowersetTableRestriction {ℓ : Level} (lem : LEM (ℓ-suc ℓ)) where

open import FOL.ZFStructure using ( module hPropStructure )
open import L.Constructible {ℓ} using ( 𝒮ʟ )
open import L.Coding.Model {ℓ} using ( prʟ )
import ClosedCoordinateDomain
import PowersetAtomicTable
import PowersetDomainTransport
import CodedTableRestriction
import NamePairDependency

open hPropStructure 𝒮ʟ using ( S; _∈ˢ_ )

module For (X C E : S)
  (subset : ClosedCoordinateDomain.Subset lem E C)
  (closed : ClosedCoordinateDomain.Closed lem E) where

  module Large = PowersetAtomicTable.For lem X C
    using ( D; table; value; value-in-B; graph; solution
          ; module Algebra; module Pair; module Raw; module Package; module Recursor )
  module Small = PowersetAtomicTable.For lem X E
    using ( D; value; solution; module Algebra; module Pair; module AtKey
          ; module Keys; module Package; module Recursor )
  module Keys = ClosedCoordinateDomain.Inclusion lem C E subset using ( keys )
  module DomainTransport = PowersetDomainTransport.For lem X using ( module Transport )

  module WithTable (H : S) (goodH : Large.Recursor.Base.Good.Good H) where

    module Restriction = CodedTableRestriction.Construction lem Small.D Large.Algebra.B H

    agrees : ∀ u v d → ⟨ u ∈ˢ E ⟩ → ⟨ v ∈ˢ E ⟩ → ⟨ d ∈ˢ Large.Algebra.B ⟩
      → (⟨ prʟ (prʟ u v) d ∈ˢ H ⟩
        → ⟨ prʟ (prʟ u v) d ∈ˢ Restriction.restricted ⟩)
        × (⟨ prʟ (prʟ u v) d ∈ˢ Restriction.restricted ⟩
        → ⟨ prʟ (prʟ u v) d ∈ˢ H ⟩)
    agrees u v d uE vE dB =
      Restriction.graph-in (prʟ u v) d (Small.Keys.Product.pair-in u v uE vE) dB ,
      λ graph → snd (snd (Restriction.graph-out (prʟ u v) d graph))

    step-transfer : ∀ p b → ⟨ p ∈ˢ Small.D ⟩ → ⟨ b ∈ˢ Large.Algebra.B ⟩
      → ⟨ prʟ p b ∈ˢ H ⟩ → ⟨ Large.Pair.Step H p b ⟩
      → ⟨ Small.Pair.Step Restriction.restricted p b ⟩
    step-transfer p b pE bB graph step = Key.into Restriction.restricted b
      (Transfer.transfer b source)
      where
      module Key = Small.AtKey p pE

      source : ⟨ Large.Raw.Step C Key.x Key.y H b ⟩
      source = Large.Pair.pair-out H Key.x Key.y b
        (subst (λ q → ⟨ Large.Pair.Step H q b ⟩) Key.represents step)

      module Transfer = DomainTransport.Transport C E Key.x Key.y
        H Restriction.restricted subset closed Key.xC Key.yC agrees

    module Preserved = CodedTableRestriction.Preservation lem
      Large.D Small.D Large.Algebra.B (NamePairDependency.R lem)
      Large.Pair.Step Small.Pair.Step Keys.keys H goodH step-transfer

    restricted-good : Small.Recursor.Base.Good.Good Restriction.restricted
    restricted-good = Preserved.good

    restricted-bounded : Small.Recursor.Base.Laws.Bounded Restriction.restricted
    restricted-bounded = Restriction.bounded

    compare-value : ∀ p pE b → ⟨ b ∈ˢ Large.Algebra.B ⟩
      → ⟨ prʟ p b ∈ˢ H ⟩ → b ≡ Small.value p pE
    compare-value p pE b bB graph =
      Small.Package.Realization.partial-agreement Small.solution
        Restriction.restricted restricted-bounded restricted-good p pE b bB
        (Restriction.graph-in p b pE bB graph)

  module Canonical = WithTable Large.table
    (Large.Package.Realization.table-good Large.solution) using ( compare-value )

  value-equal : ∀ p pE pC → Large.value p pC ≡ Small.value p pE
  value-equal p pE pC = Canonical.compare-value p pE (Large.value p pC)
    (Large.value-in-B p pC) (Large.graph p pC)
```

### ClosedDomainFormula.agda

SHA-256: `5d96a0d4adb1e01a5a5dac7ffec7376a56ea25a11fa8e208bfec516f1bfad8c9`.

```text
{-# OPTIONS --cubical --safe --guardedness #-}

open import Base.Prelude
open import Base.Truth
open import Base.Classical using ( LEM )

module ClosedDomainFormula {ℓ : Level} (lem : LEM (ℓ-suc ℓ)) where

open import FOL.ZFStructure using ( module hPropStructure )
open import FOL.Syntax using ( Formula; var; _∈̇_; _⇒̇_; ∀̇_; ∀̇∈ )
open import L.Constructible {ℓ} using ( 𝒮ʟ )
open import FOL.Semantics (hPropAlgebra (ℓ-suc ℓ)) 𝒮ʟ using ( module At )
open import CodedTableFunctionality {ℓ} using ( entryAt; entry-reading )
import ClosedCoordinateDomain {ℓ} lem as Domain
open import Cubical.Functions.Logic using ( ⇔toPath )
import Cubical.HITs.PropositionalTruncation as PT

open hPropStructure 𝒮ʟ using ( S; _∈ˢ_ )
open At S id using ( _⊨_ )

closedAt : ∀ {n} → Fin n → Formula S n
closedAt C = ∀̇∈ (var C) (∀̇ (∀̇
  (entryAt (suc (suc zero)) (suc zero) zero
    ⇒̇ (var (suc zero) ∈̇ var (suc (suc (suc C)))))))

closed-is-prop : ∀ C → isProp (Domain.Closed C)
closed-is-prop C = isPropΠ (λ n → isPropΠ (λ nC → isPropΠ (λ z →
  isPropΠ (λ edge → snd (z ∈ˢ C)))))

out : ∀ {n} (C : Fin n) (γ : Vec S n) → ⟨ γ ⊨ closedAt C ⟩
  → Domain.Closed (lookup C γ)
out C γ holds n nC z edge = PT.rec (snd (z ∈ˢ lookup C γ))
  (λ { (b , entry) → holds n nC z b
    (subst ⟨_⟩
      (sym (entry-reading (suc (suc zero)) (suc zero) zero (b ∷ z ∷ n ∷ γ)))
      entry) }) edge

into : ∀ {n} (C : Fin n) (γ : Vec S n) → Domain.Closed (lookup C γ)
  → ⟨ γ ⊨ closedAt C ⟩
into C γ closed n nC z b entry = closed n nC z
  (PT.∣ b , subst ⟨_⟩
    (entry-reading (suc (suc zero)) (suc zero) zero (b ∷ z ∷ n ∷ γ)) entry ∣₁)

closed-reading : ∀ {n} (C : Fin n) (γ : Vec S n)
  → (γ ⊨ closedAt C)
    ≡ (Domain.Closed (lookup C γ) , closed-is-prop (lookup C γ))
closed-reading C γ = ⇔toPath (out C γ) (into C γ)
```

### PowersetAtomicGraph.agda

SHA-256: `4dcf16adb6c5c6a3cefd5931a7ccd2e9e82b395640d30d9dc3e0ffacde771268`.

```text
{-# OPTIONS --cubical --safe --guardedness #-}

open import Base.Prelude
open import Base.Truth
open import Base.Classical using ( LEM )

module PowersetAtomicGraph {ℓ : Level} (lem : LEM (ℓ-suc ℓ)) where

open import FOL.ZFStructure using ( module hPropStructure )
open import L.Constructible {ℓ} using ( 𝒮ʟ )
open import L.Coding.Model {ℓ} using ( prʟ )
import ClosedCoordinateDomain
import ClosedNamePairDomain
import NamePairDependency
import PowersetAtomicTable
import PowersetTableRestriction
import InternalPowersetSupremum
open import Cubical.Functions.Logic using ( ⇔toPath )
import Cubical.HITs.PropositionalTruncation as PT
open PT using ( ∥_∥₁; ∣_∣₁ )

open hPropStructure 𝒮ʟ using ( S; _∈ˢ_; isSetS )

module For (X : S) where

  module Algebra = InternalPowersetSupremum.For lem X using ( B )

  Good : S → S → Type (ℓ-suc ℓ)
  Good C H = PowersetAtomicTable.For.Recursor.Base.Good.Good lem X C H

  Witness : S → S → S → Type (ℓ-suc ℓ)
  Witness x y b = Σ[ C ∈ S ] Σ[ H ∈ S ]
    ClosedCoordinateDomain.Closed lem C × ⟨ x ∈ˢ C ⟩ × ⟨ y ∈ˢ C ⟩ ×
    Good C H × ⟨ b ∈ˢ Algebra.B ⟩ × ⟨ prʟ (prʟ x y) b ∈ˢ H ⟩

  Graph : S → S → S → Type (ℓ-suc ℓ)
  Graph x y b = ∥ Witness x y b ∥₁

  graph-prop : S → S → S → hProp (ℓ-suc ℓ)
  graph-prop x y b = Graph x y b , PT.squash₁

  introduce : ∀ C H x y b → ClosedCoordinateDomain.Closed lem C
    → ⟨ x ∈ˢ C ⟩ → ⟨ y ∈ˢ C ⟩ → Good C H → ⟨ b ∈ˢ Algebra.B ⟩
    → ⟨ prʟ (prʟ x y) b ∈ˢ H ⟩ → Graph x y b
  introduce C H x y b closed xC yC good bB entry =
    ∣ C , H , closed , xC , yC , good , bB , entry ∣₁

  module Compare (C D H K : S)
    (closedC : ClosedCoordinateDomain.Closed lem C)
    (closedD : ClosedCoordinateDomain.Closed lem D)
    (goodH : Good C H) (goodK : Good D K) where

    module Common = ClosedCoordinateDomain.Common lem C D closedC closedD
      using ( E; left; right; closed; into )
    module Keys = NamePairDependency.Domain lem Common.E using ( module Product )
    module Left = PowersetTableRestriction.For.WithTable lem X C Common.E
      Common.left Common.closed H goodH using ( compare-value )
    module Right = PowersetTableRestriction.For.WithTable lem X D Common.E
      Common.right Common.closed K goodK using ( compare-value )

    equal : ∀ x y b c → ⟨ x ∈ˢ C ⟩ → ⟨ y ∈ˢ C ⟩
      → ⟨ x ∈ˢ D ⟩ → ⟨ y ∈ˢ D ⟩ → ⟨ b ∈ˢ Algebra.B ⟩ → ⟨ c ∈ˢ Algebra.B ⟩
      → ⟨ prʟ (prʟ x y) b ∈ˢ H ⟩ → ⟨ prʟ (prʟ x y) c ∈ˢ K ⟩ → b ≡ c
    equal x y b c xC yC xD yD bB cB hb kc =
      Left.compare-value (prʟ x y) key b bB hb ∙
      sym (Right.compare-value (prʟ x y) key c cB kc)
      where
      key : ⟨ prʟ x y ∈ˢ Keys.Product.product ⟩
      key = Keys.Product.pair-in x y (Common.into x xC xD) (Common.into y yC yD)

  witness-unique : ∀ x y b c → Witness x y b → Witness x y c → b ≡ c
  witness-unique x y b c (C , H , closedC , xC , yC , goodH , bB , hb)
    (D , K , closedD , xD , yD , goodK , cB , kc) =
    Compare.equal C D H K closedC closedD goodH goodK x y b c xC yC xD yD bB cB hb kc

  unique : ∀ x y b c → Graph x y b → Graph x y c → b ≡ c
  unique x y b c left right = PT.rec (isSetS b c)
    (λ w → PT.rec (isSetS b c) (witness-unique x y b c w) right) left

  module AtClosed (C : S) (closed : ClosedCoordinateDomain.Closed lem C)
    (x y : S) (xC : ⟨ x ∈ˢ C ⟩) (yC : ⟨ y ∈ˢ C ⟩) where

    key : ⟨ prʟ x y ∈ˢ NamePairDependency.Domain.Product.product lem C ⟩
    key = NamePairDependency.Domain.Product.pair-in lem C x y xC yC

    value : S
    value = PowersetAtomicTable.For.value lem X C (prʟ x y) key

    value-in-B : ⟨ value ∈ˢ Algebra.B ⟩
    value-in-B = PowersetAtomicTable.For.value-in-B lem X C (prʟ x y) key

    table-good : Good C (PowersetAtomicTable.For.table lem X C)
    table-good = PowersetAtomicTable.For.Package.Realization.table-good {lem = lem} {X = X} {C = C}
      (PowersetAtomicTable.For.solution lem X C)

    exists : Graph x y value
    exists = introduce C (PowersetAtomicTable.For.table lem X C) x y value
      closed xC yC table-good value-in-B (PowersetAtomicTable.For.graph lem X C (prʟ x y) key)

    agrees-with-value : ∀ b → Graph x y b → b ≡ value
    agrees-with-value b holds = unique x y b value holds exists

    from-value : ∀ b → b ≡ value → Graph x y b
    from-value b eq = subst (Graph x y) (sym eq) exists

    exact : ∀ b → graph-prop x y b ≡ ((b ≡ value) , isSetS b value)
    exact b = ⇔toPath {P = graph-prop x y b}
      {Q = ((b ≡ value) , isSetS b value)} (agrees-with-value b) (from-value b)

  module AtNames (x y : S)
    (validX : ⟨ ClosedNamePairDomain.For.Names.IsName lem Algebra.B x ⟩)
    (validY : ⟨ ClosedNamePairDomain.For.Names.IsName lem Algebra.B y ⟩) where

    module Domain = ClosedNamePairDomain.For.PairOf lem Algebra.B x y validX validY
      using ( C; contains-x; contains-y; child-closed )
    value : S
    value = AtClosed.value Domain.C Domain.child-closed x y Domain.contains-x Domain.contains-y

    value-in-B : ⟨ value ∈ˢ Algebra.B ⟩
    value-in-B = AtClosed.value-in-B Domain.C Domain.child-closed x y Domain.contains-x Domain.contains-y

    exists : Graph x y value
    exists = AtClosed.exists Domain.C Domain.child-closed x y Domain.contains-x Domain.contains-y

    exact : ∀ b → graph-prop x y b ≡ ((b ≡ value) , isSetS b value)
    exact = AtClosed.exact Domain.C Domain.child-closed x y Domain.contains-x Domain.contains-y
```
