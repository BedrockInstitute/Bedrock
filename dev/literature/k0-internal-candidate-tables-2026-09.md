# K0 internal candidate families and functional table codes

Date: 2026-09-08. Repository source baseline: `f239d101`. Status: five safe probes checked. This follows the [partial atomic table probes](k0-partial-atomic-tables-2026-09.md). K0 remains open: the complete recursive Good formula, coded-step bridge and totality theorem are not yet implemented.

## Actual internal constructions

`ProductSet` constructs D × B in actual L. Its bound is P(P(D ∪ B)); a fixed formula separates exactly the existing Kuratowski pair codes. The probe proves both membership directions, pair inclusion and recovery of both coordinate membership proofs using the existing ordered-pair injectivity theorem. D and B are arbitrary internal sets. The construction returns an internal set without assuming a host family has an image in L. Products can be nested to obtain (C × C) × B; no different pair representation is introduced.

`CandidateFamily` constructs K = { H ∈ P(W) | good(H) } and T = ⋃K for arbitrary internal W and an actual supplied finite formula good. Exact membership laws prove that K contains precisely the internal bounded candidates satisfying that formula, T consists precisely of their entries, T ⊆ W, and every admitted candidate is a subset of T. These are actual constructions under the existing successor-level LEM, not fields assuming a candidate-family code. The formula is still an input: this theorem alone supplies no recursive Good definition or compatibility.

`CodedTableFunctionality` supplies a concrete part of Good. Its reusable `entryAt` formula expresses ordered-pair membership in a table at arbitrary environment indices, with a checked reading theorem. The concrete functionality formula says that entries with the same key in D and values in B have equal values. The reading theorem connects object equality to equality of L codes in both directions. Functionality is only required on D and B; bounding the entire table by D × B supplies the separate typing guard. This module requires no LEM.

`CodedTableReadout` assumes exactly that functionality theorem for a supplied internal H. For x ∈ D, the type of a value b ∈ B together with pair(x,b) ∈ H is a proposition. Hence its propositional truncation can be eliminated to the actual unique value. The result includes membership in B, graph membership in H and agreement with every other graph value. It chooses neither a table nor a representative among multiple values. This module requires no LEM, and its domain is still partial.

`FunctionalCandidates` composes all four modules in actual L. Its candidate formula is the concrete functionality formula, with actual product bound. Membership in the resulting internal family supplies a readout module without an extra functionality argument. Every singleton containing an entry from the product is constructed internally and proved to belong to this family.

## A checked boundary: functionality alone is insufficient

The composition proves `union-is-product`: the union of all bounded functional partial tables equals D × B. Each product entry lies in its own singleton functional table, and every candidate is bounded by the product.

Thus the construction of a bounded candidate family must not be confused with the compatibility theorem for recursive candidates. When D is inhabited and B has two distinct values, this union cannot be functional. That consequence is a direct mathematical inference from the checked equality; no separate concrete two-value counterexample is claimed compiled here. The proper recursive Good formula must add downward closure and local equations before invoking the previously checked compatibility kernel.

This is a deliberate integration check, not the atomic recursion instance. Do not replace Good by functionality or assume that every collection of partial functions has a functional union.

Subsequent evidence: the [Good-formula and extension probes](k0-good-table-extension-2026-09.md) implement parameterized complete Good reading and the finite extension below, and check a conditional totality driver. The internal/semantic union correspondence, Good(T) and actual Boolean step remain unproved. The proof-plan sections below are historical dependencies refined by that follow-up.

## Remaining bridge, with precise admission boundary

The following is a source/mathematical audit and proof plan, not checked code. Retain the existing semantic partial-table kernel and instantiate its step relation through internally coded witnesses:

    StepSem(p,f,b) holds merely when there is an internal bounded functional H
    covering every predecessor of p, whose unique predecessor readouts equal f,
    and whose fixed StepCode(p,b,H) formula holds.

Here p represents a pair of names for the existing two-coordinate kernel. For arbitrary uncoded host f, StepSem may have no witness. Internal locality plus uniqueness should prove determinacy. This avoids both an assumed host-complete Boolean algebra and a demand that every host function have a graph in L.

The actual StepCode needs internal admission, uniqueness and locality. Admission applies to any internal functional table covering the relevant predecessors, not merely to an already total recursive solution. Boolean operations and the images used by the step must have fixed codes/formulas and proved adequacy. Relative completeness applies only to internal subsets of B.

Extend the checked functionality formula to one fixed Good formula and prove both directions of its reading theorem:

    Good(H) iff H is functional, its domain is downward closed,
    and each entry satisfies StepCode with H as table parameter.

CandidateFamily already imposes H ⊆ W outside that formula. Decode each such candidate using the checked unique readout, prove its semantic local equations, and use the existing compatibility theorem. Prove that internal T membership agrees with the semantic union graph. This yields functionality and downward closure of actual T; use internal locality to transfer each contributing candidate's step equation to T. Only then is Good(T) established.

Avoid proving compatibility twice for two presentations. The coded-witness relation permits reuse of the existing semantic proof. A direct coded implementation is an alternative only if it replaces that proof ownership rather than adding a parallel development.

## Totality after internal union goodness

For H already good, prove that H ∪ {pair(p,b)} stays good whenever H covers p's predecessors and StepCode(p,b,H) holds. Any old value at p equals b by step uniqueness. Consequently old readouts are unchanged; locality preserves their equations, and transfers the new equation to the extended table. The extension lemma needs no case split on domain membership and no additional choice. It also needs no separate assumption that p is not its own predecessor; coverage and unchanged readouts suffice for this local argument.

With actual T fixed before induction and Good(T) proved, well-founded induction supplies predecessor coverage at p. Internal admission supplies merely a step output. Eliminate this existence into the proposition that p belongs to the domain of T. The internal one-entry extension is a candidate in the original K, so CandidateFamily's checked candidate-inclusion law places its new entry in T. Unique readout then yields a total external value function with an actual internal graph.

The missing proof work is the full Good reading, coded local-step bridge, internal-union goodness, extension and totality, followed by the actual weighted Boolean step and atomic formula adequacy. Neither these five probes nor the audited argument closes those obligations. General-ground portability, Collection/fullness and internal ultrafilter existence also remain open. The T3 actual-model target, general forcing APIs and certified bridge, and T4 ground definability are unchanged.

## Verification and reproduction

All five final modules retain `--cubical --safe --guardedness` and checked with exit 0 in `/tmp/bedrock-k0-probes/extraction/compile-root`:

```text
GHCRTS="-A64m -I0 -M8g" agda src/ProductSet.agda
GHCRTS="-A64m -I0 -M8g" agda src/CandidateFamily.agda
GHCRTS="-A64m -I0 -M8g" agda src/CodedTableFunctionality.agda
GHCRTS="-A64m -I0 -M8g" agda src/CodedTableReadout.agda
GHCRTS="-A64m -I0 -M8g" agda src/FunctionalCandidates.agda
```

CandidateFamily was checked by the scoped agent and again through the coordinator's composed consumer. The final composition uses the final source versions below. The temporary tree reuses repository dependency caches and the earlier PairFormulaReading probe. No production source, landmark, glossary or teaching file was edited, and no whole-tree build is claimed.

An initial CandidateFamily tuple grouped its bound and formula proofs incorrectly and was corrected. Prolonged elaboration persisted: isolated prefix checks located the remaining bottleneck at K-out with-abstraction. Replacing that clause with an explicitly typed local separation result and projections checked successfully, and the final file uses that form. Slow drafts and a redundant consumer check were interrupted; they are not successful verification runs. The memory cap was not increased. ProductSet's initial missing imports were corrected before its successful check. Failed drafts are not evidence of a completed theorem.

The read-only audit is `/tmp/bedrock-k0-probes/table-totality-design/REPORT.md`; its contracts and proof argument are preserved above. Scoped prose/glossary gates and `git diff --check` exited 0. Source snapshots and SHA-256 values below match the compiled files; tracked source and copied baseline dependencies were checked against `f239d101`. Chapter-framework and whole-tree checks were not run for this temporary-probe/document change.

### ProductSet.agda

SHA-256: `bf34989ba2ddb991d69211c448fca6570ca9a8421a5304c76448cea7257f58c6`.

```text
{-# OPTIONS --cubical --safe --guardedness #-}

open import Base.Prelude
open import Base.Truth
open import Base.Classical using ( LEM )

module ProductSet {ℓ : Level} (lem : LEM (ℓ-suc ℓ)) where

open import FOL.ZFStructure using ( module hPropStructure )
open import FOL.Syntax using ( Formula; con; ∃̇∈ )
open import L.Constructible {ℓ} using ( 𝒮ʟ; isL )
open import FOL.Semantics (hPropAlgebra (ℓ-suc ℓ)) 𝒮ʟ using ( module At )
import FOL.ZFModel as Model
open import L.Model {ℓ} lem using ( L⊨ZF )
open import L.Coding.Model {ℓ} using ( prʟ; prAtL; prʟ-inj )
open import L.Axioms.Numerals {ℓ} using ( pairʟ; pairʟ-fst )
open import V.Model {ℓ} using ( pair-spec )
open import Cubical.HITs.CumulativeHierarchy.Base using () renaming ( _∈_ to _∈ᵛ_ )
open import PairFormulaReading {ℓ} using ( reading )
open import Cubical.Data.Sigma using ( Σ≡Prop )
open import Cubical.Foundations.HLevels using ( isProp× )
open import Cubical.Data.Sum using ( inl; inr )
open import Cubical.Functions.Logic using ( ⇔toPath )
import Cubical.HITs.PropositionalTruncation as PT
open PT using ( ∥_∥₁; ∣_∣₁ )

open TruthAlgebra (hPropAlgebra (ℓ-suc ℓ))
open hPropStructure 𝒮ʟ using ( S; _∈ˢ_ )
open At S id using ( _⊨_ )

opaque
  actualL : Model.isZFModel 𝒮ʟ
  actualL = L⊨ZF

module Ground = Model.isZFModel actualL

S≡ : {x y : S} → fst x ≡ fst y → x ≡ y
S≡ = Σ≡Prop (λ v → snd (isL v))

power-in : ∀ A X → ((z : S) → ⟨ z ∈ˢ X ⟩ → ⟨ z ∈ˢ A ⟩)
  → ⟨ X ∈ˢ Ground.𝒫 A ⟩
power-in A X subset = subst ⟨_⟩
  (sym (Model.℩-spec 𝒮ʟ (Ground.hasPower A) X)) subset

pair-contained : ∀ A x y → ⟨ x ∈ˢ A ⟩ → ⟨ y ∈ˢ A ⟩
  → (z : S) → ⟨ z ∈ˢ pairʟ x y ⟩ → ⟨ z ∈ˢ A ⟩
pair-contained A x y xA yA z member = PT.rec (snd (z ∈ˢ A))
  (λ { (inl p) → subst (λ w → ⟨ w ∈ˢ A ⟩) (sym (S≡ {x = z} {y = x} p)) xA
     ; (inr p) → subst (λ w → ⟨ w ∈ˢ A ⟩) (sym (S≡ {x = z} {y = y} p)) yA })
  (subst ⟨_⟩ (pair-spec (fst x) (fst y) (fst z))
    (subst (λ w → ⟨ fst z ∈ᵛ w ⟩) (pairʟ-fst x y) member))

module Construction (D B : S) where

  base : S
  base = Ground._∪_ D B

  left : ∀ x → ⟨ x ∈ˢ D ⟩ → ⟨ x ∈ˢ base ⟩
  left x xD = subst ⟨_⟩
    (sym (Model.℩-spec 𝒮ʟ (Ground.hasUnion (Ground.pair D B)) x))
    ∣ D , subst ⟨_⟩ (sym (Ground.pair-spec D B D)) ∣ inl refl ∣₁ , xD ∣₁

  right : ∀ y → ⟨ y ∈ˢ B ⟩ → ⟨ y ∈ˢ base ⟩
  right y yB = subst ⟨_⟩
    (sym (Model.℩-spec 𝒮ʟ (Ground.hasUnion (Ground.pair D B)) y))
    ∣ B , subst ⟨_⟩ (sym (Ground.pair-spec D B B)) ∣ inr refl ∣₁ , yB ∣₁

  bound : S
  bound = Ground.𝒫 (Ground.𝒫 base)

  pair-bounded : ∀ x y → ⟨ x ∈ˢ D ⟩ → ⟨ y ∈ˢ B ⟩ → ⟨ prʟ x y ∈ˢ bound ⟩
  pair-bounded x y xD yB = power-in (Ground.𝒫 base) (prʟ x y)
    (pair-contained (Ground.𝒫 base) (pairʟ x x) (pairʟ x y)
      (power-in base (pairʟ x x) (pair-contained base x x (left x xD) (left x xD)))
      (power-in base (pairʟ x y) (pair-contained base x y (left x xD) (right y yB))))

  formula : Formula S 1
  formula = ∃̇∈ (con D) (∃̇∈ (con B) (prAtL (suc (suc zero)) (suc zero) zero))

  product : S
  product = Ground.separate bound formula

  Encoded : S → Type (ℓ-suc ℓ)
  Encoded p = ∥ Σ[ x ∈ S ] Σ[ y ∈ S ]
    (⟨ x ∈ˢ D ⟩ × ⟨ y ∈ˢ B ⟩ × (p ≡ prʟ x y)) ∥₁

  formula-out : ∀ p → ⟨ (p ∷ []) ⊨ formula ⟩ → Encoded p
  formula-out p = PT.rec PT.squash₁ (λ { (x , xD , ys) → PT.map
    (λ { (y , yB , pair) → x , y , xD , yB , subst ⟨_⟩
      (reading (suc (suc zero)) (suc zero) zero (y ∷ x ∷ p ∷ [])) pair }) ys })

  formula-in : ∀ p → Encoded p → ⟨ (p ∷ []) ⊨ formula ⟩
  formula-in p = PT.map (λ { (x , y , xD , yB , pair) →
    x , xD , ∣ y , yB , subst ⟨_⟩
      (sym (reading (suc (suc zero)) (suc zero) zero (y ∷ x ∷ p ∷ []))) pair ∣₁ })

  product-out : ∀ p → ⟨ p ∈ˢ product ⟩ → Encoded p
  product-out p member = formula-out p (snd (subst ⟨_⟩ (Ground.separate-spec bound formula p) member))

  product-in : ∀ p → Encoded p → ⟨ p ∈ˢ product ⟩
  product-in p = PT.rec (snd (p ∈ˢ product))
    (λ { (x , y , xD , yB , pair) → subst ⟨_⟩
      (sym (Ground.separate-spec bound formula p))
      (subst (λ z → ⟨ z ∈ˢ bound ⟩) (sym pair) (pair-bounded x y xD yB) ,
        formula-in p ∣ x , y , xD , yB , pair ∣₁) })

  product-membership : ∀ p → (p ∈ˢ product) ≡ (Encoded p , PT.squash₁)
  product-membership p = ⇔toPath (product-out p) (product-in p)

  pair-in : ∀ x y → ⟨ x ∈ˢ D ⟩ → ⟨ y ∈ˢ B ⟩ → ⟨ prʟ x y ∈ˢ product ⟩
  pair-in x y xD yB = product-in (prʟ x y) ∣ x , y , xD , yB , refl ∣₁

  pair-out : ∀ x y → ⟨ prʟ x y ∈ˢ product ⟩ → ⟨ x ∈ˢ D ⟩ × ⟨ y ∈ˢ B ⟩
  pair-out x y member = PT.rec (isProp× (snd (x ∈ˢ D)) (snd (y ∈ˢ B)))
    (λ { (u , v , uD , vB , pair) →
      subst (λ z → ⟨ z ∈ˢ D ⟩) (sym (fst (prʟ-inj pair))) uD ,
      subst (λ z → ⟨ z ∈ˢ B ⟩) (sym (snd (prʟ-inj pair))) vB })
    (product-out (prʟ x y) member)
```

### CandidateFamily.agda

SHA-256: `06116c120ce9ec599f15e8d09d8a32451d2bb7551f5ebcb7f36045243c591071`.

```text
{-# OPTIONS --cubical --safe --guardedness #-}

open import Base.Prelude
open import Base.Truth
open import Base.Classical using ( LEM )

module CandidateFamily {ℓ : Level} (lem : LEM (ℓ-suc ℓ)) where

open import FOL.ZFStructure using ( module hPropStructure )
open import FOL.Syntax using ( Formula )
open import L.Constructible {ℓ} using ( 𝒮ʟ )
open import FOL.Semantics (hPropAlgebra (ℓ-suc ℓ)) 𝒮ʟ using ( module At )
open import FOL.ZFModel 𝒮ʟ using ( isZFModel; ℩-spec; _⊆ˢ_ )
open import L.Model {ℓ} lem using ( L⊨ZF )
open import Cubical.Functions.Logic using ( ⇔toPath )
import Cubical.HITs.PropositionalTruncation as PT
open PT using ( ∥_∥₁; ∣_∣₁ )

open TruthAlgebra (hPropAlgebra (ℓ-suc ℓ))
open hPropStructure 𝒮ʟ using ( S; _∈ˢ_ )
open At S id using ( _⊨_ )

opaque
  actualL : isZFModel
  actualL = L⊨ZF

module Construction (W : S) (good : Formula S 1) where

  open isZFModel actualL using ( separate; separate-spec; 𝒫; ⋃; hasPower; hasUnion )

  K : S
  K = separate (𝒫 W) good

  T : S
  T = ⋃ K

  Good : S → Type (ℓ-suc ℓ)
  Good H = ⟨ (H ∷ []) ⊨ good ⟩

  Subset : S → S → Type (ℓ-suc ℓ)
  Subset H A = (x : S) → ⟨ x ∈ˢ H ⟩ → ⟨ x ∈ˢ A ⟩

  K-out : ∀ H → ⟨ H ∈ˢ K ⟩ → Subset H W × Good H
  K-out H member =
    (λ x hx → subst ⟨_⟩ (℩-spec (hasPower W) H) (fst separated) x hx) , snd separated
    where
    separated : ⟨ H ∈ˢ 𝒫 W ⟩ × Good H
    separated = subst ⟨_⟩ (separate-spec (𝒫 W) good H) member

  K-in : ∀ H → Subset H W → Good H → ⟨ H ∈ˢ K ⟩
  K-in H subset satisfies = subst ⟨_⟩
    (sym (separate-spec (𝒫 W) good H))
    (subst ⟨_⟩ (sym (℩-spec (hasPower W) H)) subset , satisfies)

  K-membership : ∀ H
    → (H ∈ˢ K) ≡ ((H ⊆ˢ W) ⊓ ((H ∷ []) ⊨ good))
  K-membership H = ⇔toPath (K-out H)
    (λ { (subset , satisfies) → K-in H subset satisfies })

  Contains : S → Type (ℓ-suc ℓ)
  Contains x = ∥ Σ[ H ∈ S ]
    (Subset H W × Good H × ⟨ x ∈ˢ H ⟩) ∥₁

  T-out : ∀ x → ⟨ x ∈ˢ T ⟩ → Contains x
  T-out x member = PT.map
    (λ { (H , (inK , inH)) →
      let evidence = K-out H inK
      in H , fst evidence , snd evidence , inH })
    (subst ⟨_⟩ (℩-spec (hasUnion K) x) member)

  T-in : ∀ x → Contains x → ⟨ x ∈ˢ T ⟩
  T-in x contains = subst ⟨_⟩ (sym (℩-spec (hasUnion K) x))
    (PT.map
      (λ { (H , (subset , satisfies , inH)) →
        H , K-in H subset satisfies , inH })
      contains)

  T-membership : ∀ x
    → (x ∈ˢ T) ≡ (Contains x , PT.squash₁)
  T-membership x = ⇔toPath (T-out x) (T-in x)

  T⊆W : Subset T W
  T⊆W x member = PT.rec (snd (x ∈ˢ W))
    (λ { (H , (subset , satisfies , inH)) → subset x inH })
    (T-out x member)

  good-subset⊆T : ∀ H → Subset H W → Good H → Subset H T
  good-subset⊆T H subset satisfies x inH =
    T-in x ∣ H , subset , satisfies , inH ∣₁
```

### CodedTableFunctionality.agda

SHA-256: `7cd1385503bd3703c19aaaf10dba54d7d3608e080c48c681d90b4da0d0e8ebbe`.

```text
{-# OPTIONS --cubical --safe --guardedness #-}

open import Base.Prelude

module CodedTableFunctionality {ℓ : Level} where

open import Base.Truth
open import FOL.ZFStructure using ( module hPropStructure )
open import FOL.Syntax using ( Formula; var; con; _∧̇_; _⇒̇_; _≐_; ∃̇∈; ∀̇∈ )
open import L.Constructible {ℓ} using ( 𝒮ʟ; isL )
open import FOL.Semantics (hPropAlgebra (ℓ-suc ℓ)) 𝒮ʟ using ( module At )
open import L.Coding.Model {ℓ} using ( prAtL; prʟ )
open import PairFormulaReading {ℓ} using ( reading )
open import Cubical.Data.Sigma using ( Σ≡Prop )
open import Cubical.Functions.Logic using ( ⇔toPath )
import Cubical.HITs.PropositionalTruncation as PT
open PT using ( ∣_∣₁ )

open hPropStructure 𝒮ʟ using ( S; _∈ˢ_; isSetS )
open At S id using ( _⊨_ )

entryAt : ∀ {n} → Fin n → Fin n → Fin n → Formula S n
entryAt h x b = ∃̇∈ (var h) (prAtL zero (suc x) (suc b))

entry-reading : ∀ {n} (h x b : Fin n) (γ : Vec S n)
  → (γ ⊨ entryAt h x b) ≡ (prʟ (lookup x γ) (lookup b γ) ∈ˢ lookup h γ)
entry-reading h x b γ = ⇔toPath
  (PT.rec (snd (prʟ (lookup x γ) (lookup b γ) ∈ˢ lookup h γ))
    (λ { (p , member , pair) → subst (λ z → ⟨ z ∈ˢ lookup h γ ⟩)
      (subst ⟨_⟩ (reading zero (suc x) (suc b) (p ∷ γ)) pair) member }))
  (λ member → ∣ prʟ (lookup x γ) (lookup b γ) , member , subst ⟨_⟩
    (sym (reading zero (suc x) (suc b) (prʟ (lookup x γ) (lookup b γ) ∷ γ))) refl ∣₁)

module Construction (D B : S) where

  formula : Formula S 1
  formula = ∀̇∈ (con D) (∀̇∈ (con B) (∀̇∈ (con B)
    ((entryAt (suc (suc (suc zero))) (suc (suc zero)) (suc zero)
      ∧̇ entryAt (suc (suc (suc zero))) (suc (suc zero)) zero)
      ⇒̇ (var (suc zero) ≐ var zero))))

  Functional : S → Type (ℓ-suc ℓ)
  Functional H = (x b c : S) → ⟨ x ∈ˢ D ⟩ → ⟨ b ∈ˢ B ⟩ → ⟨ c ∈ˢ B ⟩
    → ⟨ prʟ x b ∈ˢ H ⟩ → ⟨ prʟ x c ∈ˢ H ⟩ → b ≡ c

  functional-is-prop : ∀ H → isProp (Functional H)
  functional-is-prop H = isPropΠ (λ x → isPropΠ (λ b → isPropΠ (λ c →
    isPropΠ (λ _ → isPropΠ (λ _ → isPropΠ (λ _ →
      isPropΠ (λ _ → isPropΠ (λ _ → isSetS b c))))))))

  formula-out : ∀ H → ⟨ (H ∷ []) ⊨ formula ⟩ → Functional H
  formula-out H holds x b c xD bB cB xb xc = Σ≡Prop (λ v → snd (isL v))
    (holds x xD b bB c cB
      (subst ⟨_⟩ (sym (entry-reading (suc (suc (suc zero))) (suc (suc zero))
        (suc zero) (c ∷ b ∷ x ∷ H ∷ []))) xb ,
       subst ⟨_⟩ (sym (entry-reading (suc (suc (suc zero))) (suc (suc zero))
        zero (c ∷ b ∷ x ∷ H ∷ []))) xc))

  formula-in : ∀ H → Functional H → ⟨ (H ∷ []) ⊨ formula ⟩
  formula-in H functional x xD b bB c cB entries = cong fst
    (functional x b c xD bB cB
      (subst ⟨_⟩ (entry-reading (suc (suc (suc zero))) (suc (suc zero))
        (suc zero) (c ∷ b ∷ x ∷ H ∷ [])) (fst entries))
      (subst ⟨_⟩ (entry-reading (suc (suc (suc zero))) (suc (suc zero))
        zero (c ∷ b ∷ x ∷ H ∷ [])) (snd entries)))

  formula-reading : ∀ H → ((H ∷ []) ⊨ formula) ≡ (Functional H , functional-is-prop H)
  formula-reading H = ⇔toPath (formula-out H) (formula-in H)
```

### CodedTableReadout.agda

SHA-256: `792bfe8b1c570050d6dc4af2b8a0c8b5a4d001c07755194616a0429a1daa8b91`.

```text
{-# OPTIONS --cubical --safe --guardedness #-}

open import Base.Prelude

module CodedTableReadout {ℓ : Level} where

open import Base.Truth using ( hPropAlgebra )
open import FOL.ZFStructure using ( module hPropStructure )
open import L.Constructible {ℓ} using ( 𝒮ʟ )
open import L.Coding.Model {ℓ} using ( prʟ )
open import CodedTableFunctionality {ℓ} using ( module Construction )
open import Cubical.Data.Sigma using ( Σ≡Prop )
open import Cubical.Foundations.HLevels using ( isProp× )
import Cubical.HITs.PropositionalTruncation as PT
open PT using ( ∥_∥₁; ∣_∣₁ )

open hPropStructure 𝒮ʟ using ( S; _∈ˢ_ )

module Readout (D B H : S) (functional : Construction.Functional D B H) where

  Graph : S → S → Type (ℓ-suc ℓ)
  Graph x b = ⟨ b ∈ˢ B ⟩ × ⟨ prʟ x b ∈ˢ H ⟩

  Read : S → Type (ℓ-suc ℓ)
  Read x = Σ[ b ∈ S ] Graph x b

  Domain : S → Type (ℓ-suc ℓ)
  Domain x = ∥ Read x ∥₁

  read-is-prop : ∀ x → ⟨ x ∈ˢ D ⟩ → isProp (Read x)
  read-is-prop x xD (b , bB , xb) (c , cB , xc) =
    Σ≡Prop (λ v → isProp× (snd (v ∈ˢ B)) (snd (prʟ x v ∈ˢ H)))
      (functional x b c xD bB cB xb xc)

  read : ∀ x → ⟨ x ∈ˢ D ⟩ → Domain x → Read x
  read x xD = PT.rec (read-is-prop x xD) id

  value : ∀ x → ⟨ x ∈ˢ D ⟩ → Domain x → S
  value x xD member = fst (read x xD member)

  value-in-B : ∀ x xD member → ⟨ value x xD member ∈ˢ B ⟩
  value-in-B x xD member = fst (snd (read x xD member))

  value-in-H : ∀ x xD member → ⟨ prʟ x (value x xD member) ∈ˢ H ⟩
  value-in-H x xD member = snd (snd (read x xD member))

  value-agrees : ∀ x xD member b → Graph x b → value x xD member ≡ b
  value-agrees x xD member b (bB , xb) = functional x _ b xD
    (value-in-B x xD member) bB (value-in-H x xD member) xb

  graph-domain : ∀ x b → Graph x b → Domain x
  graph-domain x b graph = ∣ b , graph ∣₁
```

### FunctionalCandidates.agda

SHA-256: `ee098b89f67bdfbb1d1c0dcb64644e1b60c12f513fa50e3cadfad089e8855358`.

```text
{-# OPTIONS --cubical --safe --guardedness #-}

open import Base.Prelude
open import Base.Truth
open import Base.Classical using ( LEM )

module FunctionalCandidates {ℓ : Level} (lem : LEM (ℓ-suc ℓ)) where

open import FOL.ZFStructure using ( module hPropStructure )
open import L.Constructible {ℓ} using ( 𝒮ʟ )
open import L.Coding.Model {ℓ} using ( prʟ; prʟ-inj )
import ProductSet
import CandidateFamily
import CodedTableFunctionality
import CodedTableReadout
open import Cubical.Data.Sum using ( inl; inr )
open import Cubical.Functions.Logic using ( ⇔toPath )
import Cubical.HITs.PropositionalTruncation as PT
open PT using ( ∣_∣₁ )

open hPropStructure 𝒮ʟ using ( S; _∈ˢ_; isSetS )
module Ground = ProductSet.Ground lem
open ProductSet lem using ( S≡ )

module Construction (D B : S) where

  module Product = ProductSet.Construction lem D B
  module Functionality = CodedTableFunctionality.Construction D B
  module Family = CandidateFamily.Construction lem Product.product Functionality.formula

  candidate-in : ∀ H → Family.Subset H Product.product → Functionality.Functional H
    → ⟨ H ∈ˢ Family.K ⟩
  candidate-in H bounded functional = Family.K-in H bounded (Functionality.formula-in H functional)

  candidate-functional : ∀ H → ⟨ H ∈ˢ Family.K ⟩ → Functionality.Functional H
  candidate-functional H member = Functionality.formula-out H (snd (Family.K-out H member))

  module Read (H : S) (member : ⟨ H ∈ˢ Family.K ⟩) =
    CodedTableReadout.Readout D B H (candidate-functional H member)

  singleton : S → S
  singleton p = Ground.pair p p

  singleton-in : ∀ p → ⟨ p ∈ˢ singleton p ⟩
  singleton-in p = subst ⟨_⟩ (sym (Ground.pair-spec p p p)) ∣ inl refl ∣₁

  singleton-out : ∀ p z → ⟨ z ∈ˢ singleton p ⟩ → z ≡ p
  singleton-out p z member = PT.rec (isSetS z p)
    (λ { (inl q) → S≡ q ; (inr q) → S≡ q })
    (subst ⟨_⟩ (Ground.pair-spec p p z) member)

  singleton-bounded : ∀ p → ⟨ p ∈ˢ Product.product ⟩ → Family.Subset (singleton p) Product.product
  singleton-bounded p member z hz = subst (λ q → ⟨ q ∈ˢ Product.product ⟩)
    (sym (singleton-out p z hz)) member

  singleton-functional : ∀ p → Functionality.Functional (singleton p)
  singleton-functional p x b c xD bB cB xb xc = snd (prʟ-inj
    (singleton-out p (prʟ x b) xb ∙ sym (singleton-out p (prʟ x c) xc)))

  singleton-candidate : ∀ p → ⟨ p ∈ˢ Product.product ⟩ → ⟨ singleton p ∈ˢ Family.K ⟩
  singleton-candidate p member = candidate-in (singleton p)
    (singleton-bounded p member) (singleton-functional p)

  product⊆union : Family.Subset Product.product Family.T
  product⊆union p member = Family.good-subset⊆T (singleton p)
    (singleton-bounded p member) (Functionality.formula-in (singleton p) (singleton-functional p))
    p (singleton-in p)

  union-is-product : Family.T ≡ Product.product
  union-is-product = Ground.extensional
    (λ p → ⇔toPath (Family.T⊆W p) (product⊆union p))
```
