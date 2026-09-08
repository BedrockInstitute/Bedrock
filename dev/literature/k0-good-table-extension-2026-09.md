# K0 coded Good formulas and one-entry preservation

Date: 2026-09-08. Repository source baseline: `0c0bd900`. Status: checked temporary probes, not production forcing. This follows the [internal candidate-table probes](k0-internal-candidate-tables-2026-09.md). K0 remains open at recursive candidate compatibility/internal union goodness, totality, the actual Boolean step and general-ground portability.

## Internal one-entry extension

`CodedTableExtension` constructs the actual L set H⁺ = H ∪ {pair(p,b)} for p ∈ D and b ∈ B. It proves the exact graph law: an entry belongs to H⁺ precisely when it belonged to H or its key/value equal p/b. It proves product boundedness, inclusion of the old domain, and that any new domain point was already present or equals p.

The functional preservation lemma takes functionality of H and the explicitly local consistency condition that every existing B-valued entry at p equals b. It proves H⁺ functional and proves old values agree with all extended values. The downward-closure lemma takes downward closure of H and coverage in H of p's relevant predecessors. It then proves H⁺ downward closed. These are conditional finite-set lemmas, not a generic step-existence assumption or a well-founded recursion theorem.

`CodedStepExtension` discharges that consistency condition from the old table's equations and uniqueness of the step output. It then proves that all old and new entries obey their equations in H⁺. Its result packages actual product boundedness, functionality, downward closure and equations for the actual extended set.

Its two step laws are nonrecursive and explicit. Uniqueness compares two outputs for a supplied bounded internal functional table covering the key's predecessors. Locality transfers a step between two such internal tables whose predecessor graph values agree. Neither law gives an output for an arbitrary host function. Neither presupposes that H⁺ is good. The proof supplies its functionality and coverage before applying locality to it.

For an old entry, downward closure supplies predecessor coverage in H, and the checked old-value agreement supplies the premise of locality. For the new entry, the supplied coverage and step witness at p are transferred to H⁺ and then transported along key/value equality. No excluded-middle split on whether p already has a value is needed. This finite preservation theorem needs neither well-foundedness nor a separate no-self-predecessor hypothesis.

## Fixed Good syntax

`CodedGoodTables` builds actual finite syntax for functionality, downward-closed domain and local entry equations. Relation and step syntax come with explicit adequacy proofs for their semantic predicates. The module proves the domain formula's reading at arbitrary environments and proves both directions of the complete Good reading theorem. Good is therefore no longer an unexplained predicate offered to Separation.

The table bound remains the separate CandidateFamily restriction H ⊆ D × B. Functionality, downward closure and entry equations range only over keys in D and values in B, matching that bound. The step and dependency syntax are still supplied parameters. This result does not construct the expanded Boolean step or prove its admission, uniqueness or locality. Those obligations cannot be replaced by an arbitrary host predicate.

## Composition and conditional totality

`GoodTableExtension` composes the actual fixed Good formula, internal candidate family and proved finite-step preservation. A one-entry extension of a bounded Good table with an admitted output is proved to be a member of the original internal K. Its new entry therefore belongs to the already constructed union T. This uses the checked Good reading in the reverse direction; candidate admission is proved, not assumed.

The same module checks a conditional WFI totality driver for this actual T. Its explicit remaining inputs are well-foundedness of the dependency relation on members of D, a proof Good(T), and internal step admission for bounded functional tables covering the relevant predecessors. The induction hypothesis gives coverage in T; truncated step existence is eliminated into the proposition that the current key is in T's domain. The constructed one-entry candidate then supplies its value. No induction-result graph is collected externally.

Good(T) is an explicit premise of this reusable lemma and remains unproved for the intended recursive family. The conditional result must not be reported as a completed bounded recursion theorem. It isolates the exact remaining union-goodness dependency; it is not an extra axiom authorized for the eventual trophy.

## Proof ownership and remaining work

The finite extension layer owns set membership, bounding and functional preservation. The step extension layer owns consistency derived from step uniqueness and equation transfer by locality. Good syntax owns definability/reading. The internal candidate family owns collection and union membership; the shared well-founded compatibility kernel owns uniqueness across recursive partial tables. Compose these interfaces rather than reproving their mathematics on the poset side or in the Cohen instance.

The next bridge must decode bounded Good candidates to the shared partial-table semantics through internally witnessed steps, and identify the semantic union graph with the already constructed internal union. Locality must then establish the internal union's equations. Good(T) is still a theorem to prove, not a permissible replacement assumption for claiming atomic graph existence.

After Good(T), WFI supplies predecessor coverage at each key. The actual Boolean step must supply a merely existing output for that INTERNAL T. The now checked finite extension machinery is intended to make the resulting one-entry extension a candidate in the original family, whose checked inclusion then places the entry in T. The conditional totality composition is now checked, but its Good(T) and actual step-admission premises remain to be discharged. Uniqueness can then extract actual values without host choice.

The existing no-host-choice restriction is unchanged. Finite internal constructions use the proved L ground under `LEM (ℓ-suc ℓ)`; the Good syntax/reading proof itself has no LEM parameter. The actual ordinary non-CH model remains T3, with the general forcing theorems and both interfaces mandatory before acceptance; ground definability remains T4.

## Verification

Final source snapshots below retain `--cubical --safe --guardedness` and checked with exit 0 in `/tmp/bedrock-k0-probes/extraction/compile-root`, using the required `GHCRTS="-A64m -I0 -M8g"` limit. No production source, landmark or teaching file was changed. The temporary tree reuses the preceding checked probes and baseline dependencies; no whole-tree compilation is claimed.

The initial finite-extension check reported two unresolved implicit endpoints of the L-code equality adapter. Explicit endpoints closed both goals and the final source checked. Only final sources are archived as evidence. The scoped read-only review in `/tmp/bedrock-k0-probes/table-totality-design/REPORT.md` confirms that preservation is noncircular and contains no host-choice or host-wide step-totality assumption; it is not a proof of the pending union/Boolean instance.

Scoped prose and glossary checks and `git diff --check` exited 0. Source baselines and snapshot hashes were checked. Chapter-framework and whole-tree gates were not run for this temporary-probe/document change.

### CodedTableExtension.agda

Command: `GHCRTS="-A64m -I0 -M8g" agda src/CodedTableExtension.agda`, exit 0.

SHA-256: `737a2f3c5804417d84e36dbf4a6d6dc54e915ac8bdf4c9df05f5502bcfdb53d2`.

```text
{-# OPTIONS --cubical --safe --guardedness #-}

open import Base.Prelude
open import Base.Truth
open import Base.Classical using ( LEM )

module CodedTableExtension {ℓ : Level} (lem : LEM (ℓ-suc ℓ)) where

open import FOL.ZFStructure using ( module hPropStructure )
open import L.Constructible {ℓ} using ( 𝒮ʟ )
open import L.Coding.Model {ℓ} using ( prʟ; prʟ-inj )
import FOL.ZFModel as Model
import ProductSet
import CodedTableFunctionality
open import Cubical.Data.Sum using ( _⊎_; inl; inr )
open import Cubical.Functions.Logic using ( ⇔toPath )
import Cubical.HITs.PropositionalTruncation as PT
open PT using ( ∥_∥₁; ∣_∣₁ )

open hPropStructure 𝒮ʟ using ( S; _∈ˢ_; isSetS )
module Ground = ProductSet.Ground lem
open ProductSet lem using ( S≡ )

module Extension (D B H p b : S) (pD : ⟨ p ∈ˢ D ⟩) (bB : ⟨ b ∈ˢ B ⟩) where

  module Product = ProductSet.Construction lem D B
  module Functionality = CodedTableFunctionality.Construction D B

  entry : S
  entry = prʟ p b

  singleton : S
  singleton = Ground.pair entry entry

  extended : S
  extended = Ground._∪_ H singleton

  member-cases : ∀ z → ⟨ z ∈ˢ extended ⟩ → ∥ (⟨ z ∈ˢ H ⟩ ⊎ (z ≡ entry)) ∥₁
  member-cases z member = PT.rec PT.squash₁
    (λ { (A , pair , inA) → PT.rec PT.squash₁
      (λ { (inl q) → ∣ inl (subst (λ w → ⟨ z ∈ˢ w ⟩) (S≡ {x = A} {y = H} q) inA) ∣₁
         ; (inr q) → PT.map
           (λ { (inl e) → inr (S≡ e) ; (inr e) → inr (S≡ e) })
           (subst ⟨_⟩ (Ground.pair-spec entry entry z)
             (subst (λ w → ⟨ z ∈ˢ w ⟩) (S≡ {x = A} {y = singleton} q) inA)) })
      (subst ⟨_⟩ (Ground.pair-spec H singleton A) pair) })
    (subst ⟨_⟩ (Model.℩-spec 𝒮ʟ (Ground.hasUnion (Ground.pair H singleton)) z) member)

  old-in : ∀ z → ⟨ z ∈ˢ H ⟩ → ⟨ z ∈ˢ extended ⟩
  old-in z member = subst ⟨_⟩
    (sym (Model.℩-spec 𝒮ʟ (Ground.hasUnion (Ground.pair H singleton)) z))
    ∣ H , subst ⟨_⟩ (sym (Ground.pair-spec H singleton H)) ∣ inl refl ∣₁ , member ∣₁

  new-in : ⟨ entry ∈ˢ extended ⟩
  new-in = subst ⟨_⟩
    (sym (Model.℩-spec 𝒮ʟ (Ground.hasUnion (Ground.pair H singleton)) entry))
    ∣ singleton , subst ⟨_⟩ (sym (Ground.pair-spec H singleton singleton)) ∣ inr refl ∣₁ ,
      subst ⟨_⟩ (sym (Ground.pair-spec entry entry entry)) ∣ inl refl ∣₁ ∣₁

  Graph : S → S → S → Type (ℓ-suc ℓ)
  Graph T x c = ⟨ prʟ x c ∈ˢ T ⟩

  Domain : S → S → Type (ℓ-suc ℓ)
  Domain T x = ∥ Σ[ c ∈ S ] (⟨ c ∈ˢ B ⟩ × Graph T x c) ∥₁

  graph-cases : ∀ x c → Graph extended x c
    → ∥ (Graph H x c ⊎ ((x ≡ p) × (c ≡ b))) ∥₁
  graph-cases x c member = PT.map
    (λ { (inl old) → inl old ; (inr eq) → inr (prʟ-inj eq) })
    (member-cases (prʟ x c) member)

  graph-in : ∀ x c → ∥ (Graph H x c ⊎ ((x ≡ p) × (c ≡ b))) ∥₁
    → Graph extended x c
  graph-in x c = PT.rec (snd (prʟ x c ∈ˢ extended))
    (λ { (inl old) → old-in (prʟ x c) old
       ; (inr (xp , cb)) → subst (λ z → ⟨ z ∈ˢ extended ⟩)
          (sym (cong₂ prʟ xp cb)) new-in })

  graph-reading : ∀ x c → (prʟ x c ∈ˢ extended)
    ≡ (∥ (Graph H x c ⊎ ((x ≡ p) × (c ≡ b))) ∥₁ , PT.squash₁)
  graph-reading x c = ⇔toPath (graph-cases x c) (graph-in x c)

  bounded : ((z : S) → ⟨ z ∈ˢ H ⟩ → ⟨ z ∈ˢ Product.product ⟩)
    → (z : S) → ⟨ z ∈ˢ extended ⟩ → ⟨ z ∈ˢ Product.product ⟩
  bounded bound z member = PT.rec (snd (z ∈ˢ Product.product))
    (λ { (inl old) → bound z old
       ; (inr eq) → subst (λ w → ⟨ w ∈ˢ Product.product ⟩)
         (sym eq) (Product.pair-in p b pD bB) }) (member-cases z member)

  domain-in : ∀ x → Domain H x → Domain extended x
  domain-in x = PT.map (λ { (c , cB , graph) → c , cB , old-in (prʟ x c) graph })

  domain-cases : ∀ x → Domain extended x → ∥ (Domain H x ⊎ (x ≡ p)) ∥₁
  domain-cases x = PT.rec PT.squash₁ (λ { (c , cB , graph) → PT.map
    (λ { (inl old) → inl ∣ c , cB , old ∣₁ ; (inr (xp , cb)) → inr xp })
    (graph-cases x c graph) })

  module Consistent
    (functional : Functionality.Functional H)
    (consistent : ∀ c → ⟨ c ∈ˢ B ⟩ → Graph H p c → c ≡ b) where

    old-agrees : ∀ x c d → ⟨ x ∈ˢ D ⟩ → ⟨ c ∈ˢ B ⟩ → ⟨ d ∈ˢ B ⟩
      → Graph H x c → Graph extended x d → c ≡ d
    old-agrees x c d xD cB dB old extendedGraph = PT.rec (isSetS c d)
      (λ { (inl other) → functional x c d xD cB dB old other
         ; (inr (xp , db)) → consistent c cB
           (subst (λ z → Graph H z c) xp old) ∙ sym db })
      (graph-cases x d extendedGraph)

    extended-functional : Functionality.Functional extended
    extended-functional x c d xD cB dB xc xd = PT.rec (isSetS c d)
      (λ { (inl old) → old-agrees x c d xD cB dB old xd
         ; (inr (xp , cb)) → PT.rec (isSetS c d)
           (λ { (inl old) → sym (old-agrees x d c xD dB cB old xc)
              ; (inr (yp , db)) → cb ∙ sym db })
           (graph-cases x d xd) }) (graph-cases x c xc)

  module Closure (R : S → S → hProp (ℓ-suc ℓ))
    (down : ∀ x y → ⟨ x ∈ˢ D ⟩ → ⟨ y ∈ˢ D ⟩ → Domain H x → ⟨ R y x ⟩ → Domain H y)
    (covers : ∀ y → ⟨ y ∈ˢ D ⟩ → ⟨ R y p ⟩ → Domain H y) where

    extended-down : ∀ x y → ⟨ x ∈ˢ D ⟩ → ⟨ y ∈ˢ D ⟩
      → Domain extended x → ⟨ R y x ⟩ → Domain extended y
    extended-down x y xD yD domain relation = PT.rec PT.squash₁
      (λ { (inl old) → domain-in y (down x y xD yD old relation)
         ; (inr xp) → domain-in y (covers y yD (subst (λ z → ⟨ R y z ⟩) xp relation)) })
      (domain-cases x domain)
```

### CodedStepExtension.agda

Command: `GHCRTS="-A64m -I0 -M8g" agda src/CodedStepExtension.agda`, exit 0.

SHA-256: `9d34a178f3004f043fdc33023f7b0e314197ee0802a25459dbde0ce4fb4e85de`.

```text
{-# OPTIONS --cubical --safe --guardedness #-}

open import Base.Prelude
open import Base.Truth
open import Base.Classical using ( LEM )

module CodedStepExtension {ℓ : Level} (lem : LEM (ℓ-suc ℓ)) where

open import FOL.ZFStructure using ( module hPropStructure )
open import L.Constructible {ℓ} using ( 𝒮ʟ )
open import L.Coding.Model {ℓ} using ( prʟ )
import ProductSet
import CodedTableFunctionality
import CodedTableExtension
open import Cubical.Data.Sum using ( inl; inr )
import Cubical.HITs.PropositionalTruncation as PT
open PT using ( ∥_∥₁ )

open hPropStructure 𝒮ʟ using ( S; _∈ˢ_ )

module Laws (D B : S) (R : S → S → hProp (ℓ-suc ℓ))
  (Step : S → S → S → hProp (ℓ-suc ℓ)) where

  module Product = ProductSet.Construction lem D B
  open CodedTableFunctionality.Construction D B using ( Functional )

  Bounded : S → Type (ℓ-suc ℓ)
  Bounded H = ∀ z → ⟨ z ∈ˢ H ⟩ → ⟨ z ∈ˢ Product.product ⟩

  Graph : S → S → S → Type (ℓ-suc ℓ)
  Graph H x c = ⟨ prʟ x c ∈ˢ H ⟩

  Domain : S → S → Type (ℓ-suc ℓ)
  Domain H x = ∥ Σ[ c ∈ S ] (⟨ c ∈ˢ B ⟩ × Graph H x c) ∥₁

  Covers : S → S → Type (ℓ-suc ℓ)
  Covers H x = ∀ y → ⟨ y ∈ˢ D ⟩ → ⟨ R y x ⟩ → Domain H y

  Downward : S → Type (ℓ-suc ℓ)
  Downward H = ∀ x y → ⟨ x ∈ˢ D ⟩ → ⟨ y ∈ˢ D ⟩
    → Domain H x → ⟨ R y x ⟩ → Domain H y

  Obeys : S → Type (ℓ-suc ℓ)
  Obeys H = ∀ x c → ⟨ x ∈ˢ D ⟩ → ⟨ c ∈ˢ B ⟩ → Graph H x c → ⟨ Step H x c ⟩

  Agree : S → S → S → Type (ℓ-suc ℓ)
  Agree H K x = ∀ y c d → ⟨ y ∈ˢ D ⟩ → ⟨ R y x ⟩
    → ⟨ c ∈ˢ B ⟩ → ⟨ d ∈ˢ B ⟩ → Graph H y c → Graph K y d → c ≡ d

  module Preservation
    (unique : ∀ H x c d → Bounded H → Functional H → ⟨ x ∈ˢ D ⟩
      → ⟨ c ∈ˢ B ⟩ → ⟨ d ∈ˢ B ⟩ → Covers H x
      → ⟨ Step H x c ⟩ → ⟨ Step H x d ⟩ → c ≡ d)
    (locality : ∀ H K x c → Bounded H → Bounded K → Functional H → Functional K
      → ⟨ x ∈ˢ D ⟩ → ⟨ c ∈ˢ B ⟩ → Covers H x → Covers K x → Agree H K x
      → ⟨ Step H x c ⟩ → ⟨ Step K x c ⟩) where

    module Extend (H p b : S) (pD : ⟨ p ∈ˢ D ⟩) (bB : ⟨ b ∈ˢ B ⟩)
      (bound : Bounded H) (functional : Functional H) (down : Downward H)
      (obeys : Obeys H) (covers : Covers H p) (step : ⟨ Step H p b ⟩) where

      module Addition = CodedTableExtension.Extension lem D B H p b pD bB
      open Addition using ( extended )

      consistent : ∀ c → ⟨ c ∈ˢ B ⟩ → Graph H p c → c ≡ b
      consistent c cB graph = unique H p c b bound functional pD cB bB covers
        (obeys p c pD cB graph) step

      module Consistency = Addition.Consistent functional consistent
      module Closure = Addition.Closure R down covers

      extended-bounded : Bounded extended
      extended-bounded = Addition.bounded bound

      extended-functional : Functional extended
      extended-functional = Consistency.extended-functional

      extended-downward : Downward extended
      extended-downward = Closure.extended-down

      extended-covers : ∀ x → Covers H x → Covers extended x
      extended-covers x coverage y yD relation = Addition.domain-in y (coverage y yD relation)

      agrees : ∀ x → Agree H extended x
      agrees x y c d yD relation cB dB old graph =
        Consistency.old-agrees y c d yD cB dB old graph

      transfer : ∀ x c → ⟨ x ∈ˢ D ⟩ → ⟨ c ∈ˢ B ⟩ → Covers H x
        → ⟨ Step H x c ⟩ → ⟨ Step extended x c ⟩
      transfer x c xD cB coverage = locality H extended x c bound extended-bounded
        functional extended-functional xD cB coverage (extended-covers x coverage) (agrees x)

      extended-obeys : Obeys extended
      extended-obeys x c xD cB graph = PT.rec (snd (Step extended x c))
        (λ { (inl old) → transfer x c xD cB
          (λ y yD relation → down x y xD yD PT.∣ c , cB , old ∣₁ relation)
          (obeys x c xD cB old)
           ; (inr (xp , cb)) → subst ⟨_⟩
             (cong₂ (Step extended) (sym xp) (sym cb))
             (transfer p b pD bB covers step) }) (Addition.graph-cases x c graph)

      preserved : Bounded extended × Functional extended × Downward extended × Obeys extended
      preserved = extended-bounded , extended-functional , extended-downward , extended-obeys
```

### CodedGoodTables.agda

Command: `GHCRTS="-A64m -I0 -M8g" agda src/CodedGoodTables.agda`, exit 0.

SHA-256: `a6323cb4de87c32a04ecf3a17a11e0e367ee25bdbab574d7555d46c12330154e`.

```text
{-# OPTIONS --cubical --safe --guardedness #-}

open import Base.Prelude

module CodedGoodTables {ℓ : Level} where

open import Base.Truth using ( hPropAlgebra )
open import FOL.ZFStructure using ( module hPropStructure )
open import FOL.Syntax using ( Formula; con; _∧̇_; _⇒̇_; ∃̇∈; ∀̇∈ )
open import L.Constructible {ℓ} using ( 𝒮ʟ )
open hPropStructure 𝒮ʟ using ( S; _∈ˢ_ )
open import FOL.Semantics (hPropAlgebra (ℓ-suc ℓ)) 𝒮ʟ using ( module At )
open import L.Coding.Model {ℓ} using ( prʟ )
open import CodedTableFunctionality {ℓ} using ( entryAt; entry-reading )
import CodedTableFunctionality
import CodedTableReadout
open import Cubical.Foundations.HLevels using ( isProp× )
open import Cubical.Functions.Logic using ( ⇔toPath )
import Cubical.HITs.PropositionalTruncation as PT
open PT using ( ∥_∥₁ )

open At S id using ( _⊨_ )

module WithStep
  (R : S → S → hProp (ℓ-suc ℓ))
  (rAt : ∀ {n} → Fin n → Fin n → Formula S n)
  (rAt-adequate : ∀ {n} (y x : Fin n) (γ : Vec S n)
    → (γ ⊨ rAt y x) ≡ R (lookup y γ) (lookup x γ))
  (Step : S → S → S → hProp (ℓ-suc ℓ))
  (stepAt : ∀ {n} → Fin n → Fin n → Fin n → Formula S n)
  (stepAt-adequate : ∀ {n} (h x b : Fin n) (γ : Vec S n)
    → (γ ⊨ stepAt h x b) ≡ Step (lookup h γ) (lookup x γ) (lookup b γ))
  where

  module Construction (D B : S) where

    module Functionality = CodedTableFunctionality.Construction D B

    Domain : S → S → Type (ℓ-suc ℓ)
    Domain H x = ∥ Σ[ b ∈ S ] ⟨ b ∈ˢ B ⟩ × ⟨ prʟ x b ∈ˢ H ⟩ ∥₁

    domain-is-prop : ∀ H x → isProp (Domain H x)
    domain-is-prop H x = PT.squash₁

    domainAt : ∀ {n} → Fin n → Fin n → Formula S n
    domainAt h x = ∃̇∈ (con B) (entryAt (suc h) (suc x) zero)

    domain-reading : ∀ {n} (h x : Fin n) (γ : Vec S n)
      → (γ ⊨ domainAt h x)
        ≡ (Domain (lookup h γ) (lookup x γ) ,
           domain-is-prop (lookup h γ) (lookup x γ))
    domain-reading h x γ = ⇔toPath
      (PT.map (λ { (b , bB , entry) → b , bB , subst ⟨_⟩
        (entry-reading (suc h) (suc x) zero (b ∷ γ)) entry }))
      (PT.map (λ { (b , bB , entry) → b , bB , subst ⟨_⟩
        (sym (entry-reading (suc h) (suc x) zero (b ∷ γ))) entry }))

    downwardFormula : Formula S 1
    downwardFormula = ∀̇∈ (con D) (∀̇∈ (con D)
      ((domainAt (suc (suc zero)) (suc zero) ∧̇ rAt zero (suc zero))
        ⇒̇ domainAt (suc (suc zero)) zero))

    stepFormula : Formula S 1
    stepFormula = ∀̇∈ (con D) (∀̇∈ (con B)
      (entryAt (suc (suc zero)) (suc zero) zero
        ⇒̇ stepAt (suc (suc zero)) (suc zero) zero))

    formula : Formula S 1
    formula = Functionality.formula ∧̇ (downwardFormula ∧̇ stepFormula)

    Downward : S → Type (ℓ-suc ℓ)
    Downward H = (x y : S) → ⟨ x ∈ˢ D ⟩ → ⟨ y ∈ˢ D ⟩
      → Domain H x → ⟨ R y x ⟩ → Domain H y

    Obeys : S → Type (ℓ-suc ℓ)
    Obeys H = (x b : S) → ⟨ x ∈ˢ D ⟩ → ⟨ b ∈ˢ B ⟩
      → ⟨ prʟ x b ∈ˢ H ⟩ → ⟨ Step H x b ⟩

    Good : S → Type (ℓ-suc ℓ)
    Good H = Functionality.Functional H × Downward H × Obeys H

    downward-is-prop : ∀ H → isProp (Downward H)
    downward-is-prop H = isPropΠ (λ x → isPropΠ (λ y →
      isPropΠ (λ _ → isPropΠ (λ _ → isPropΠ (λ _ → isPropΠ (λ _ → PT.squash₁))))))

    obeys-is-prop : ∀ H → isProp (Obeys H)
    obeys-is-prop H = isPropΠ (λ x → isPropΠ (λ b → isPropΠ (λ _ →
      isPropΠ (λ _ → isPropΠ (λ _ → snd (Step H x b))))))

    good-is-prop : ∀ H → isProp (Good H)
    good-is-prop H = isProp× (Functionality.functional-is-prop H)
      (isProp× (downward-is-prop H) (obeys-is-prop H))

    domain-readout : ∀ H (functional : Functionality.Functional H) x
      → Domain H x ≡ CodedTableReadout.Readout.Domain D B H functional x
    domain-readout H functional x = refl

    formula-out : ∀ H → ⟨ (H ∷ []) ⊨ formula ⟩ → Good H
    formula-out H holds = Functionality.formula-out H (fst holds) , downward , obeys
      where
      downward : Downward H
      downward x y xD yD domain relation = subst ⟨_⟩
        (domain-reading (suc (suc zero)) zero (y ∷ x ∷ H ∷ []))
        (fst (snd holds) x xD y yD
          (subst ⟨_⟩ (sym (domain-reading (suc (suc zero)) (suc zero)
            (y ∷ x ∷ H ∷ []))) domain ,
           subst ⟨_⟩ (sym (rAt-adequate zero (suc zero)
            (y ∷ x ∷ H ∷ []))) relation))

      obeys : Obeys H
      obeys x b xD bB entry = subst ⟨_⟩
        (stepAt-adequate (suc (suc zero)) (suc zero) zero (b ∷ x ∷ H ∷ []))
        (snd (snd holds) x xD b bB
          (subst ⟨_⟩ (sym (entry-reading (suc (suc zero)) (suc zero) zero
            (b ∷ x ∷ H ∷ []))) entry))

    formula-in : ∀ H → Good H → ⟨ (H ∷ []) ⊨ formula ⟩
    formula-in H (functional , downward , obeys) =
      Functionality.formula-in H functional , downward-in , obeys-in
      where
      downward-in : ⟨ (H ∷ []) ⊨ downwardFormula ⟩
      downward-in x xD y yD premise = subst ⟨_⟩
        (sym (domain-reading (suc (suc zero)) zero (y ∷ x ∷ H ∷ [])))
        (downward x y xD yD
          (subst ⟨_⟩ (domain-reading (suc (suc zero)) (suc zero)
            (y ∷ x ∷ H ∷ [])) (fst premise))
          (subst ⟨_⟩ (rAt-adequate zero (suc zero) (y ∷ x ∷ H ∷ []))
            (snd premise)))

      obeys-in : ⟨ (H ∷ []) ⊨ stepFormula ⟩
      obeys-in x xD b bB entry = subst ⟨_⟩
        (sym (stepAt-adequate (suc (suc zero)) (suc zero) zero
          (b ∷ x ∷ H ∷ [])))
        (obeys x b xD bB
          (subst ⟨_⟩ (entry-reading (suc (suc zero)) (suc zero) zero
            (b ∷ x ∷ H ∷ [])) entry))

    formula-reading : ∀ H → ((H ∷ []) ⊨ formula) ≡ (Good H , good-is-prop H)
    formula-reading H = ⇔toPath (formula-out H) (formula-in H)
```

### GoodTableExtension.agda

Command: `GHCRTS="-A64m -I0 -M8g" agda src/GoodTableExtension.agda`, exit 0.

SHA-256: `0651816b95a7d4c06266b317fe6a1601523c7d744f4e849810e19700774a10fa`.

```text
{-# OPTIONS --cubical --safe --guardedness #-}

open import Base.Prelude
open import Base.Truth
open import Base.Classical using ( LEM )

module GoodTableExtension {ℓ : Level} (lem : LEM (ℓ-suc ℓ)) where

open import FOL.ZFStructure using ( module hPropStructure )
open import L.Constructible {ℓ} using ( 𝒮ʟ )
open import FOL.Syntax using ( Formula )
open import FOL.Semantics (hPropAlgebra (ℓ-suc ℓ)) 𝒮ʟ using ( module At )
open import L.Coding.Model {ℓ} using ( prʟ )
import CodedGoodTables
import CodedStepExtension
import CodedTableFunctionality
import CandidateFamily
open import Cubical.Induction.WellFounded using ( WellFounded; module WFI )
import Cubical.HITs.PropositionalTruncation as PT
open PT using ( ∥_∥₁; ∣_∣₁ )

open hPropStructure 𝒮ʟ using ( S; _∈ˢ_ )
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

  module Syntax = CodedGoodTables.WithStep R rAt rAt-adequate Step stepAt stepAt-adequate

  module Construction (D B : S) where

    module Good = Syntax.Construction D B
    module Laws = CodedStepExtension.Laws lem D B R Step
    open Laws using ( Bounded; Covers; Agree )
    open CodedTableFunctionality.Construction D B using ( Functional )
    module Family = CandidateFamily.Construction lem Laws.Product.product Good.formula

    module Preservation
      (unique : ∀ H x c d → Bounded H → Functional H → ⟨ x ∈ˢ D ⟩
        → ⟨ c ∈ˢ B ⟩ → ⟨ d ∈ˢ B ⟩ → Covers H x
        → ⟨ Step H x c ⟩ → ⟨ Step H x d ⟩ → c ≡ d)
      (locality : ∀ H K x c → Bounded H → Bounded K → Functional H → Functional K
        → ⟨ x ∈ˢ D ⟩ → ⟨ c ∈ˢ B ⟩ → Covers H x → Covers K x → Agree H K x
        → ⟨ Step H x c ⟩ → ⟨ Step K x c ⟩) where

      module Keep = Laws.Preservation unique locality

      module Extend (H p b : S) (pD : ⟨ p ∈ˢ D ⟩) (bB : ⟨ b ∈ˢ B ⟩)
        (bound : Bounded H) (good : Good.Good H)
        (covers : Covers H p) (step : ⟨ Step H p b ⟩) where

        module Added = Keep.Extend H p b pD bB bound (fst good)
          (fst (snd good)) (snd (snd good)) covers step

        extended-good : Good.Good Added.Addition.extended
        extended-good = Added.extended-functional , Added.extended-downward , Added.extended-obeys

        extension-candidate : ⟨ Added.Addition.extended ∈ˢ Family.K ⟩
        extension-candidate = Family.K-in Added.Addition.extended Added.extended-bounded
          (Good.formula-in Added.Addition.extended extended-good)

        entry-in-union : ⟨ prʟ p b ∈ˢ Family.T ⟩
        entry-in-union = Family.good-subset⊆T Added.Addition.extended Added.extended-bounded
          (Good.formula-in Added.Addition.extended extended-good) (prʟ p b) Added.Addition.new-in

      Key : Type (ℓ-suc ℓ)
      Key = Σ[ x ∈ S ] ⟨ x ∈ˢ D ⟩

      Dependency : Key → Key → Type (ℓ-suc ℓ)
      Dependency y x = ⟨ R (fst y) (fst x) ⟩

      module Totality
        (wf : WellFounded Dependency)
        (union-good : Good.Good Family.T)
        (admit : ∀ H x → Bounded H → Functional H → ⟨ x ∈ˢ D ⟩ → Covers H x
          → ∥ Σ[ b ∈ S ] (⟨ b ∈ˢ B ⟩ × ⟨ Step H x b ⟩) ∥₁) where

        total : (x : Key) → Good.Domain Family.T (fst x)
        total = WFI.induction wf advance
          where
          advance : (x : Key)
            → ((y : Key) → Dependency y x → Good.Domain Family.T (fst y))
            → Good.Domain Family.T (fst x)
          advance (p , pD) below = PT.rec PT.squash₁ consume
            (admit Family.T p Family.T⊆W (fst union-good) pD covers)
            where
            covers : Covers Family.T p
            covers y yD relation = below (y , yD) relation

            consume : Σ[ b ∈ S ] (⟨ b ∈ˢ B ⟩ × ⟨ Step Family.T p b ⟩)
              → Good.Domain Family.T p
            consume (b , bB , step) = ∣ b , bB , Extension.entry-in-union ∣₁
              where
              module Extension = Extend Family.T p b pD bB Family.T⊆W union-good covers step
```
