# K0 bounded internal table recursion

Date: 2026-09-08. Repository source baseline: `54bf77f4`. Status: five safe probe modules checked. The parameterized L bounded-table recursion construction now proves compatibility, internal union goodness and totality together. This closes the previous `Good(T)` premise in the [extension probes](k0-good-table-extension-2026-09.md). It does not close K0: the actual Boolean atomic step, its internal images, closed-name-domain adapters and general-ground portability remain open.

## The checked constructor

`BoundedTableRecursion.WithStep.Construction.Solve` returns an actual internal table in L, its Good proof and product bound, a total data-valued readout on D, membership of every value in B, graph membership and the local step equation. It also proves the exact value/graph correspondence on typed keys and values, and agreement with every bounded Good partial table on the same domain. The table is the already defined union of the internally separated candidate family, not a code for an assumed host recursion.

The final Solve interface has these explicit inputs:

| Input | Exact scope |
|---|---|
| LEM | Existing `LEM (ℓ-suc ℓ)` for the proved L ground; no new host choice |
| D and B | Supplied internal sets of keys and possible values |
| Dependency syntax | A relation R on L codes, finite syntax constructors and reading proofs at arbitrary environments |
| Step syntax | Step(H,x,b), finite syntax constructors and corresponding reading proofs |
| Step uniqueness | For a bounded internal functional H covering x's predecessors, two typed step outputs are equal |
| Step locality | Two bounded internal functional tables covering x and agreeing on predecessor values preserve a step output |
| Well-foundedness | R restricted to the actual member subtype of D |
| Internal admission | Such an internal H merely admits some b ∈ B satisfying its step formula |

There is NO supplied compatibility theorem, Good(T) proof, total recursive table, host graph-closure function, host-complete Boolean algebra or choice operator in Solve. Internal admission is still a real mathematical obligation for each step instance. It does not assert that arbitrary host predecessor functions admit outputs or internally represented images.

No hypothesis says D is externally countable, and no enumeration, ordinal rank recursion or proof system is needed for this bounded construction. The fixed output bound B is essential: it lets the candidate family be constructed before the well-founded induction. This is not an arbitrary unbounded set-valued recursion theorem.

## Proof decomposition and ownership

`CodedTableCompatibility` owns the well-founded compatibility induction. Keys are members of arbitrary internal D, so this interface can later accept encoded pairs of names. At a key shared by two Good tables, downward closure supplies predecessor coverage. The induction hypothesis identifies their predecessor graph values. Locality transfers the first table's step to the second table, where step uniqueness identifies their outputs. All existence eliminations remain propositional; no table readout is selected merely to run this comparison.

`CodedGoodUnion` owns internal union goodness. Its reusable lemma takes compatibility and locality, and constructs Good(T) from actual CandidateFamily membership laws. Two contributing candidate witnesses and compatibility prove the union functional. Downward closure transports predecessor entries from a contributing candidate into T. Locality then transfers the candidate's step equation to T using the already proved union functionality and closure. Totality is not used in this proof. The module also proves T itself belongs to the original candidate family.

`BoundedTableRecursion` composes these results with the previous finite extension and WFI totality driver. Its compatibility and Good(T) arguments are proved internally in the composition. It then invokes the already checked unique readout rather than a host selector. The partial-agreement result is a direct consumer of the one compatibility proof.

Architecture refinement: use coded compatibility as the single intended production proof home. The older two-coordinate `PartialAtomicTables` remains historical exploratory evidence, not a second production recursion to port alongside it. The direct coded formulation handles general dependency keys and avoids an extra existential semantic-step wrapper in the construction of the internal table. Future semantic presentations obtain their comparison laws through proved code/readout adapters. This replaces the earlier preference for reusing that exploratory semantic kernel; it does not authorize duplicate compatibility proofs or weaken either the poset or Boolean public interface.

Host language use remains substantial: dependency induction, value functions, uniqueness and propositional reasoning use Agda directly. Actual internal sets and syntax are introduced where internal collection and relative Boolean completeness require them. There is no deduction-system implementation hidden in these probes.

## Actual constant-step instance

`ConstantTableStep` supplies concrete dependency/step formulas, their reading proofs, uniqueness, locality, restricted well-foundedness and internal admission for the rule that always returns a supplied b₀ ∈ B. The dependency relation is empty. Its only logical input is the existing LEM; no step-law records are left unconstructed in this instance.

`ConstantTableRecursion` runs the complete constructor for arbitrary internal D and B with b₀ ∈ B. It proves the output value is b₀ and that pair(x,b) belongs to the constructed table exactly when x ∈ D and b = b₀. The table comes through the candidate-union/WFI construction, rather than being supplied as a constant-function graph. D need not be finite or externally enumerable.

This is an integration instance for the general contracts. The file does not explicitly select a nonempty D; if D is inhabited, the checked entry-in theorem immediately supplies an entry. Since dependencies are empty, the instance does not test the actual weighted Boolean recursion or constitute a Cohen theorem. The general compatibility and totality proofs themselves are genuinely parameterized by arbitrary supplied well-founded dependencies.

## Remaining K0 work

1. Adapt a closed internal family of valid names to the internal key domain C × C, with the concrete dependency formula and its restricted well-foundedness. Preserve entry weights and the existing coordinate coding.
2. Construct the weighted inner and outer Boolean images from supplied internal tables. Supply internally represented Boolean operations and relative suprema, and prove the actual expanded atomic step's syntax, reading, admission, uniqueness and locality.
3. Instantiate bounded recursion with that step. Prove independence of the chosen closed name domain and fixed equality/membership formula adequacy; derive the semantic computation laws and the required standard-clause results.
4. Generalize the L-specific ground adapters with the same explicit internal set and accessibility requirements. Preserve the shared compiler, two public forcing interfaces and their certified bridge.

Collection/fullness, actual internal ultrafilter existence and the later ordinary-model quotient remain separate obligations. The completed parameterized kernel does not certify the entire T3 assumption budget. T3 remains an actual ordinary non-CH model after the mandatory general forcing results; T4 remains ground definability.

## Verification and reproduction

The five final source snapshots below checked with exit 0 under `--cubical --safe --guardedness` and `GHCRTS="-A64m -I0 -M8g"`. Root entry points ran in `/tmp/bedrock-k0-probes/extraction/compile-root`; the union agent checked from that tree's src directory. The final BoundedTableRecursion and ConstantTableRecursion commands check the complete final composition using the final dependencies. Baseline caches were reused; no whole-tree build is claimed.

The constant-step draft initially used a nonexistent empty-type eliminator name; replacing it with the library's `Empty.rec*` closed the check. Only final checked sources are archived. The scoped mathematical audit is appended to `/tmp/bedrock-k0-probes/table-totality-design/REPORT.md`; it confirms the absence of hidden Good(T)/compatibility assumptions in Solve and distinguishes the constant instance from the pending Boolean instance.

Scoped prose/glossary gates and `git diff --check` exited 0. All tracked source and copied baseline files were checked byte-for-byte against `54bf77f4`, and source snapshots match their SHA-256 values. No repository src, landmark, glossary or teaching files changed. Chapter-framework and whole-tree gates were not run for this temporary-probe/document-only change.

### CodedTableCompatibility.agda

SHA-256: `1f5f70265cd462c28059db2e66a112afb75fe5a4349e601435b138989828afbd`.

```text
{-# OPTIONS --cubical --safe --guardedness #-}

open import Base.Prelude
open import Base.Truth
open import Base.Classical using ( LEM )

module CodedTableCompatibility {ℓ : Level} (lem : LEM (ℓ-suc ℓ)) where

open import FOL.ZFStructure using ( module hPropStructure )
open import L.Constructible {ℓ} using ( 𝒮ʟ )
import CodedStepExtension
import CodedTableFunctionality
open import Cubical.Induction.WellFounded using ( WellFounded; module WFI )
import Cubical.HITs.PropositionalTruncation as PT
open PT using ( ∣_∣₁ )

open hPropStructure 𝒮ʟ using ( S; _∈ˢ_ )

module Construction (D B : S) (R : S → S → hProp (ℓ-suc ℓ))
  (Step : S → S → S → hProp (ℓ-suc ℓ)) where

  module Laws = CodedStepExtension.Laws lem D B R Step
  open Laws using ( Bounded; Covers; Agree; Graph; Downward; Obeys )
  open CodedTableFunctionality.Construction D B using ( Functional )

  Good : S → Type (ℓ-suc ℓ)
  Good H = Functional H × Downward H × Obeys H

  Key : Type (ℓ-suc ℓ)
  Key = Σ[ x ∈ S ] ⟨ x ∈ˢ D ⟩

  Dependency : Key → Key → Type (ℓ-suc ℓ)
  Dependency y x = ⟨ R (fst y) (fst x) ⟩

  module Proof
    (unique : ∀ H x c d → Bounded H → Functional H → ⟨ x ∈ˢ D ⟩
      → ⟨ c ∈ˢ B ⟩ → ⟨ d ∈ˢ B ⟩ → Covers H x
      → ⟨ Step H x c ⟩ → ⟨ Step H x d ⟩ → c ≡ d)
    (locality : ∀ H K x c → Bounded H → Bounded K → Functional H → Functional K
      → ⟨ x ∈ˢ D ⟩ → ⟨ c ∈ˢ B ⟩ → Covers H x → Covers K x → Agree H K x
      → ⟨ Step H x c ⟩ → ⟨ Step K x c ⟩)
    (wf : WellFounded Dependency) where

    AtKey : Key → Type (ℓ-suc ℓ)
    AtKey x = (H K : S) → Bounded H → Bounded K → Good H → Good K
      → (b c : S) → ⟨ b ∈ˢ B ⟩ → ⟨ c ∈ˢ B ⟩
      → Graph H (fst x) b → Graph K (fst x) c → b ≡ c

    at-key : (x : Key) → AtKey x
    at-key = WFI.induction wf advance
      where
      advance : (x : Key) → ((y : Key) → Dependency y x → AtKey y) → AtKey x
      advance (x , xD) below H K boundH boundK goodH goodK b c bB cB xb xc =
        unique K x b c boundK (fst goodK) xD bB cB coverK
          (locality H K x b boundH boundK (fst goodH) (fst goodK) xD bB coverH coverK
            agreement (snd (snd goodH) x b xD bB xb))
          (snd (snd goodK) x c xD cB xc)
        where
        coverH : Covers H x
        coverH y yD relation = fst (snd goodH) x y xD yD ∣ b , bB , xb ∣₁ relation

        coverK : Covers K x
        coverK y yD relation = fst (snd goodK) x y xD yD ∣ c , cB , xc ∣₁ relation

        agreement : Agree H K x
        agreement y d e yD relation dB eB yd ye =
          below (y , yD) relation H K boundH boundK goodH goodK d e dB eB yd ye

    compatible : ∀ H K → Bounded H → Bounded K → Good H → Good K
      → ∀ x b c → ⟨ x ∈ˢ D ⟩ → ⟨ b ∈ˢ B ⟩ → ⟨ c ∈ˢ B ⟩
      → Graph H x b → Graph K x c → b ≡ c
    compatible H K boundH boundK goodH goodK x b c xD bB cB xb xc =
      at-key (x , xD) H K boundH boundK goodH goodK b c bB cB xb xc
```

### CodedGoodUnion.agda

SHA-256: `acdf162695c4ba3f4dbd161df11c045b85e64de9e60251136c25775624751405`.

```text
{-# OPTIONS --cubical --safe --guardedness #-}

open import Base.Prelude
open import Base.Truth
open import Base.Classical using ( LEM )

module CodedGoodUnion {ℓ : Level} (lem : LEM (ℓ-suc ℓ)) where

open import FOL.ZFStructure using ( module hPropStructure )
open import FOL.Syntax using ( Formula )
open import L.Constructible {ℓ} using ( 𝒮ʟ )
open import FOL.Semantics (hPropAlgebra (ℓ-suc ℓ)) 𝒮ʟ using ( module At )
open import L.Coding.Model {ℓ} using ( prʟ )
import GoodTableExtension
import Cubical.HITs.PropositionalTruncation as PT

open hPropStructure 𝒮ʟ using ( S; _∈ˢ_; isSetS )
open At S id using ( _⊨_ )

module WithStep
  (R : S → S → hProp (ℓ-suc ℓ))
  (rAt : ∀ {n} → Fin n → Fin n → Formula S n)
  (rAt-adequate : ∀ {n} (y x : Fin n) (γ : Vec S n)
    → (γ ⊨ rAt y x) ≡ R (lookup y γ) (lookup x γ))
  (Step : S → S → S → hProp (ℓ-suc ℓ))
  (stepAt : ∀ {n} → Fin n → Fin n → Fin n → Formula S n)
  (stepAt-adequate : ∀ {n} (h x b : Fin n) (γ : Vec S n)
    → (γ ⊨ stepAt h x b) ≡ Step (lookup h γ) (lookup x γ) (lookup b γ)) where

  module Extension = GoodTableExtension.WithStep lem R rAt rAt-adequate
    Step stepAt stepAt-adequate

  module Construction (D B : S) where

    module Base = Extension.Construction D B
    module Family = Base.Family
    module Good = Base.Good
    module Laws = Base.Laws
    open Laws using ( Bounded; Covers; Agree; Graph )

    Compatible : Type (ℓ-suc ℓ)
    Compatible = ∀ H K → Bounded H → Bounded K
      → Good.Good H → Good.Good K → ∀ x b c → ⟨ x ∈ˢ D ⟩
      → ⟨ b ∈ˢ B ⟩ → ⟨ c ∈ˢ B ⟩
      → Graph H x b → Graph K x c → b ≡ c

    Locality : Type (ℓ-suc ℓ)
    Locality = ∀ H K x c → Bounded H → Bounded K
      → Good.Functionality.Functional H → Good.Functionality.Functional K
      → ⟨ x ∈ˢ D ⟩ → ⟨ c ∈ˢ B ⟩ → Covers H x → Covers K x
      → Agree H K x → ⟨ Step H x c ⟩ → ⟨ Step K x c ⟩

    union-good-core : Compatible → Locality → Good.Good Family.T
    union-good-core compatible locality = functional , downward , obeys
      where
      functional : Good.Functionality.Functional Family.T
      functional x b c xD bB cB xb xc = PT.rec (isSetS b c)
        (λ { (H , Hbound , Hgood , Hxb) → PT.rec (isSetS b c)
          (λ { (K , Kbound , Kgood , Kxc) → compatible H K
            Hbound Kbound (Good.formula-out H Hgood) (Good.formula-out K Kgood)
            x b c xD bB cB Hxb Kxc }) (Family.T-out (prʟ x c) xc) })
        (Family.T-out (prʟ x b) xb)

      downward : Good.Downward Family.T
      downward x y xD yD domain relation = PT.rec PT.squash₁
        (λ { (b , bB , xb) → PT.rec PT.squash₁
          (λ { (H , Hbound , Hgood , Hxb) →
            let good : Good.Good H
                good = Good.formula-out H Hgood
            in PT.map (λ { (c , cB , Hyc) → c , cB ,
              Family.good-subset⊆T H Hbound Hgood (prʟ y c) Hyc })
              (fst (snd good) x y xD yD PT.∣ b , bB , Hxb ∣₁ relation)
          }) (Family.T-out (prʟ x b) xb) }) domain

      agrees : ∀ H → Bounded H → Family.Good H → ∀ x → Agree H Family.T x
      agrees H Hbound Hgood x y b c yD relation bB cB Hyb Tyc =
        functional y b c yD bB cB
          (Family.good-subset⊆T H Hbound Hgood (prʟ y b) Hyb) Tyc

      obeys : Good.Obeys Family.T
      obeys x b xD bB xb = PT.rec (snd (Step Family.T x b))
        (λ { (H , Hbound , Hgood , Hxb) →
          let good : Good.Good H
              good = Good.formula-out H Hgood
          in locality H Family.T x b Hbound Family.T⊆W (fst good) functional xD bB
            (λ y yD relation → fst (snd good) x y xD yD
              PT.∣ b , bB , Hxb ∣₁ relation)
            (λ y yD relation → downward x y xD yD
              PT.∣ b , bB , xb ∣₁ relation)
            (agrees H Hbound Hgood x) (snd (snd good) x b xD bB Hxb)
        }) (Family.T-out (prʟ x b) xb)

    module Union (compatible : Compatible) (locality : Locality) where

      union-good : Good.Good Family.T
      union-good = union-good-core compatible locality

      union-candidate : ⟨ Family.T ∈ˢ Family.K ⟩
      union-candidate = Family.K-in Family.T Family.T⊆W
        (Good.formula-in Family.T union-good)
```

### BoundedTableRecursion.agda

SHA-256: `f478905f9ed0dc694147189a9d12318771630a19b94b6f94918a19293594fe8c`.

```text
{-# OPTIONS --cubical --safe --guardedness #-}

open import Base.Prelude
open import Base.Truth
open import Base.Classical using ( LEM )

module BoundedTableRecursion {ℓ : Level} (lem : LEM (ℓ-suc ℓ)) where

open import FOL.ZFStructure using ( module hPropStructure )
open import L.Constructible {ℓ} using ( 𝒮ʟ )
open import FOL.Syntax using ( Formula )
open import FOL.Semantics (hPropAlgebra (ℓ-suc ℓ)) 𝒮ʟ using ( module At )
open import L.Coding.Model {ℓ} using ( prʟ )
import GoodTableExtension
import CodedTableCompatibility
import CodedGoodUnion
import CodedTableReadout
open import Cubical.Induction.WellFounded using ( WellFounded )
open import Cubical.Functions.Logic using ( ⇔toPath )
import Cubical.HITs.PropositionalTruncation as PT
open PT using ( ∥_∥₁ )

open hPropStructure 𝒮ʟ using ( S; _∈ˢ_; isSetS )
open At S id using ( _⊨_ )

module WithStep
  (R : S → S → hProp (ℓ-suc ℓ))
  (rAt : ∀ {n} → Fin n → Fin n → Formula S n)
  (rAt-adequate : ∀ {n} (y x : Fin n) (γ : Vec S n)
    → (γ ⊨ rAt y x) ≡ R (lookup y γ) (lookup x γ))
  (Step : S → S → S → hProp (ℓ-suc ℓ))
  (stepAt : ∀ {n} → Fin n → Fin n → Fin n → Formula S n)
  (stepAt-adequate : ∀ {n} (h x b : Fin n) (γ : Vec S n)
    → (γ ⊨ stepAt h x b) ≡ Step (lookup h γ) (lookup x γ) (lookup b γ)) where

  module Extension = GoodTableExtension.WithStep lem R rAt rAt-adequate Step stepAt stepAt-adequate
  module Unions = CodedGoodUnion.WithStep lem R rAt rAt-adequate Step stepAt stepAt-adequate

  module Construction (D B : S) where

    module Base = Extension.Construction D B
    module Candidates = Unions.Construction D B
    module Compatibility = CodedTableCompatibility.Construction lem D B R Step
    open Base.Laws using ( Bounded; Covers; Agree )
    open Base.Good.Functionality using ( Functional )

    module Solve
      (unique : ∀ H x c d → Bounded H → Functional H → ⟨ x ∈ˢ D ⟩
        → ⟨ c ∈ˢ B ⟩ → ⟨ d ∈ˢ B ⟩ → Covers H x
        → ⟨ Step H x c ⟩ → ⟨ Step H x d ⟩ → c ≡ d)
      (locality : ∀ H K x c → Bounded H → Bounded K → Functional H → Functional K
        → ⟨ x ∈ˢ D ⟩ → ⟨ c ∈ˢ B ⟩ → Covers H x → Covers K x → Agree H K x
        → ⟨ Step H x c ⟩ → ⟨ Step K x c ⟩)
      (wf : WellFounded Compatibility.Dependency)
      (admit : ∀ H x → Bounded H → Functional H → ⟨ x ∈ˢ D ⟩ → Covers H x
        → ∥ Σ[ b ∈ S ] (⟨ b ∈ˢ B ⟩ × ⟨ Step H x b ⟩) ∥₁) where

      module Comparison = Compatibility.Proof unique locality wf
      module Union = Candidates.Union Comparison.compatible locality
      module Preserve = Base.Preservation unique locality
      module Total = Preserve.Totality wf Union.union-good admit

      table : S
      table = Base.Family.T

      table-good : Base.Good.Good table
      table-good = Union.union-good

      table-bounded : Bounded table
      table-bounded = Base.Family.T⊆W

      module Read = CodedTableReadout.Readout D B table (fst table-good)

      total : ∀ x → ⟨ x ∈ˢ D ⟩ → Read.Domain x
      total x xD = Total.total (x , xD)

      value : ∀ x → ⟨ x ∈ˢ D ⟩ → S
      value x xD = Read.value x xD (total x xD)

      value-in-B : ∀ x xD → ⟨ value x xD ∈ˢ B ⟩
      value-in-B x xD = Read.value-in-B x xD (total x xD)

      value-in-table : ∀ x xD → ⟨ prʟ x (value x xD) ∈ˢ table ⟩
      value-in-table x xD = Read.value-in-H x xD (total x xD)

      equation : ∀ x xD → ⟨ Step table x (value x xD) ⟩
      equation x xD = snd (snd table-good) x (value x xD) xD
        (value-in-B x xD) (value-in-table x xD)

      graph-reading : ∀ x xD b → ⟨ b ∈ˢ B ⟩
        → (prʟ x b ∈ˢ table) ≡ ((b ≡ value x xD) , isSetS b (value x xD))
      graph-reading x xD b bB = ⇔toPath
        (λ graph → sym (Read.value-agrees x xD (total x xD) b (bB , graph)))
        (λ eq → subst (λ c → ⟨ prʟ x c ∈ˢ table ⟩) (sym eq) (value-in-table x xD))

      partial-agreement : ∀ H → Bounded H → Base.Good.Good H
        → ∀ x xD b → ⟨ b ∈ˢ B ⟩ → ⟨ prʟ x b ∈ˢ H ⟩ → b ≡ value x xD
      partial-agreement H bounded good x xD b bB graph =
        Comparison.compatible H table bounded table-bounded good table-good
          x b (value x xD) xD bB (value-in-B x xD) graph (value-in-table x xD)
```

### ConstantTableStep.agda

SHA-256: `cd8a8dbfb05f1b7e9fc57d867c7e126354dcc3aa90b4edfcb633c9d5563bb375`.

```text
{-# OPTIONS --cubical --safe --guardedness #-}

open import Base.Prelude
open import Base.Truth
open import Base.Classical using ( LEM )

module ConstantTableStep {ℓ : Level} (lem : LEM (ℓ-suc ℓ)) where

open import FOL.ZFStructure using ( module hPropStructure )
open import L.Constructible {ℓ} using ( 𝒮ʟ )
open import FOL.Syntax using ( Formula; var; con; _≐_; ⊥̇ )
open import FOL.Semantics (hPropAlgebra (ℓ-suc ℓ)) 𝒮ʟ using ( module At )
import GoodTableExtension
import CodedTableFunctionality
open import ProductSet lem using ( S≡ )
open import Cubical.Functions.Logic using ( ⇔toPath )
open import Cubical.Induction.WellFounded using ( WellFounded; acc )
import Cubical.Data.Empty as Empty
import Cubical.HITs.PropositionalTruncation as PT
open PT using ( ∥_∥₁; ∣_∣₁ )

open hPropStructure 𝒮ʟ using ( S; _∈ˢ_; isSetS )
open At S id using ( _⊨_ )

module Construction (D B b₀ : S) (b₀B : ⟨ b₀ ∈ˢ B ⟩) where

  R : S → S → hProp (ℓ-suc ℓ)
  R x y = ⊥* , isProp⊥*

  rAt : ∀ {n} → Fin n → Fin n → Formula S n
  rAt y x = ⊥̇

  relation-reading : ∀ {n} (y x : Fin n) (γ : Vec S n)
    → (γ ⊨ rAt y x) ≡ R (lookup y γ) (lookup x γ)
  relation-reading y x γ = refl

  Step : S → S → S → hProp (ℓ-suc ℓ)
  Step H x b = (b ≡ b₀) , isSetS b b₀

  stepAt : ∀ {n} → Fin n → Fin n → Fin n → Formula S n
  stepAt h x b = var b ≐ con b₀

  step-reading : ∀ {n} (h x b : Fin n) (γ : Vec S n)
    → (γ ⊨ stepAt h x b) ≡ Step (lookup h γ) (lookup x γ) (lookup b γ)
  step-reading h x b γ = ⇔toPath S≡ (cong fst)

  module Framework = GoodTableExtension.WithStep lem R rAt relation-reading Step stepAt step-reading
  module Base = Framework.Construction D B
  open Base.Laws using ( Bounded; Covers; Agree )
  open CodedTableFunctionality.Construction D B using ( Functional )

  unique : ∀ H x c d → Bounded H → Functional H → ⟨ x ∈ˢ D ⟩
    → ⟨ c ∈ˢ B ⟩ → ⟨ d ∈ˢ B ⟩ → Covers H x
    → ⟨ Step H x c ⟩ → ⟨ Step H x d ⟩ → c ≡ d
  unique H x c d bounded functional xD cB dB covers hc hd = hc ∙ sym hd

  locality : ∀ H K x c → Bounded H → Bounded K → Functional H → Functional K
    → ⟨ x ∈ˢ D ⟩ → ⟨ c ∈ˢ B ⟩ → Covers H x → Covers K x → Agree H K x
    → ⟨ Step H x c ⟩ → ⟨ Step K x c ⟩
  locality H K x c boundedH boundedK functionalH functionalK xD cB coversH coversK agree step = step

  module Preserve = Base.Preservation unique locality

  wf : WellFounded Preserve.Dependency
  wf x = acc (λ y relation → Empty.rec* relation)

  admit : ∀ H x → Bounded H → Functional H → ⟨ x ∈ˢ D ⟩ → Covers H x
    → ∥ Σ[ b ∈ S ] (⟨ b ∈ˢ B ⟩ × ⟨ Step H x b ⟩) ∥₁
  admit H x bounded functional xD covers = ∣ b₀ , b₀B , refl ∣₁
```

### ConstantTableRecursion.agda

SHA-256: `07540a091dbbea6e4d5b39d9f84e9c850c95e96894fbae4e8e0d5bbac3684322`.

```text
{-# OPTIONS --cubical --safe --guardedness #-}

open import Base.Prelude
open import Base.Truth
open import Base.Classical using ( LEM )

module ConstantTableRecursion {ℓ : Level} (lem : LEM (ℓ-suc ℓ)) where

open import FOL.ZFStructure using ( module hPropStructure )
open import L.Constructible {ℓ} using ( 𝒮ʟ )
open import L.Coding.Model {ℓ} using ( prʟ )
import ConstantTableStep
import BoundedTableRecursion
open import Cubical.Functions.Logic using ( ⇔toPath )
open import Cubical.Foundations.HLevels using ( isProp× )

open hPropStructure 𝒮ʟ using ( S; _∈ˢ_; isSetS )

module Construction (D B b₀ : S) (b₀B : ⟨ b₀ ∈ˢ B ⟩) where

  module Constant = ConstantTableStep.Construction lem D B b₀ b₀B
  module Recursor = BoundedTableRecursion.WithStep lem Constant.R Constant.rAt
    Constant.relation-reading Constant.Step Constant.stepAt Constant.step-reading
  module Result = Recursor.Construction.Solve D B Constant.unique Constant.locality Constant.wf Constant.admit

  table : S
  table = Result.table

  constant-value : ∀ x xD → Result.value x xD ≡ b₀
  constant-value = Result.equation

  entry-in : ∀ x → ⟨ x ∈ˢ D ⟩ → ⟨ prʟ x b₀ ∈ˢ table ⟩
  entry-in x xD = subst (λ b → ⟨ prʟ x b ∈ˢ table ⟩)
    (constant-value x xD) (Result.value-in-table x xD)

  entry-out : ∀ x b → ⟨ prʟ x b ∈ˢ table ⟩ → ⟨ x ∈ˢ D ⟩ × (b ≡ b₀)
  entry-out x b graph = xD , snd (snd Result.table-good) x b xD bB graph
    where
    typed = Constant.Base.Laws.Product.pair-out x b (Result.table-bounded (prʟ x b) graph)
    xD : ⟨ x ∈ˢ D ⟩
    xD = fst typed
    bB : ⟨ b ∈ˢ B ⟩
    bB = snd typed

  entry-reading : ∀ x b → (prʟ x b ∈ˢ table)
    ≡ ((⟨ x ∈ˢ D ⟩ × (b ≡ b₀)) , isProp× (snd (x ∈ˢ D)) (isSetS b b₀))
  entry-reading x b = ⇔toPath (entry-out x b)
    (λ { (xD , eq) → subst (λ c → ⟨ prʟ x c ∈ˢ table ⟩) (sym eq) (entry-in x xD) })
```
