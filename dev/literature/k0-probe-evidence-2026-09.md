# K0 probe evidence and remaining obligations

Date: 2026-09-08. Source baseline: `db40669b5787a5a38e0f0b1c3caa867fcee6784b`. Status: K0 in progress, not complete. The owner selected semantic forcing, model extensions and geology; no deduction system or PRA development is part of these probes. All authored Agda files and dependency caches are under `/tmp/bedrock-k0-probes`; no repository `src` file was changed. Snapshots below preserve the checked probe text for later reproduction, not as production modules.

## Checked first batch

The dispatched agents ran the following checks with `GHCRTS="-A64m -I0 -M8g"`; the coordinator assigned compilation slots after checking machine process counts. Every probe has `--safe`; the installed checker reports Agda 2.8.0 and uses the project's cubical dependency. The root reviewed the source and reports; it has not rerun every check independently.

| Probe | Checked result | What it does not establish |
|---|---|---|
| EqualityCoherence.agda | Exit 0; explicit equality/path adapter and membership substitution | No full ZFC model adapter; singleton example is not a ZF model |
| FixedFormulaCompiler.agda | Exit 0; actual library relativization of a quantified formula, bounded syntax and semantic correctness | Not a forcing-formula compiler; no internal global truth predicate |
| Names.agda | Exit 0, warning-free; finite weighted equality/membership, admitted existential LUB, raw-name obstruction and coded-carrier h-set result | No general forcing semantics or model-internal name universe |
| NonseparativeCompletion.agda | Exit 0; density, compatibility correspondence and distinct raw conditions with identical separative behavior | Not the general RO construction or a fully packaged internally complete algebra; indexed-match warnings remain |
| VCodeWitness.agda | Exit 0, warning-free; distinct V codes for the four condition tags | Does not collect those codes/order graph into sets of an arbitrary ground |

The completion warnings are Agda's unsupported indexed matches at the order-transitivity and density clauses. They are recorded rather than silently suppressed; this finite probe is not a production representation selection.

## Design consequences

1. A raw name constructor accepting arbitrary host types exposes a retract of the host universe. The checked `raw-not-set` theorem refutes `isSet Raw` under Cubical univalence. This specific raw carrier cannot be inserted unchanged into `ZFStructure.isSetS`. It is a measured negative, not a failure of forcing or host-language constructions.
2. A W-name carrier over an h-set of codes has a checked h-set theorem. This is a candidate direction, not proof that its codes represent every required ground set or that all operations stay internal.
3. Boolean equality genuinely differs from raw path equality: checked examples have partial truth values, and distinct zero-weight/empty names can be equal with top truth value. Keep semantic equality separate from raw names and ordinary model equality.
4. The tested existential join is top although neither listed witness has top value. This is not a counterexample to the maximum principle in a full Boolean universe: the witness family is restricted. It prevents incorrectly obtaining a witness selector merely from a LUB operation.
5. Bare structural equality needs an explicit coherence contract for ordinary first-order interpretation. The model record has external well-foundedness and strong numeral assumptions; no literal transitive realization is built by the record itself. The probe is a positive adapter example, not a formal impossibility theorem about all existing model fields.
6. Completion certificates must accept noninjective maps on nonseparative presentations. Ground-set coding, full algebra laws, completeness and property transfer remain separately checked obligations.

## Remaining K0 obligations and next probes

The finite first batch does not settle the model-relative universe architecture. Do not declare K0 complete merely because the examples typecheck.

- The finite material-set/order-graph example now passes. Still derive its finite closure capabilities from an actual ground profile; ambient V existence alone does not imply membership in an arbitrary ground M.
- The range-bound follow-up checks exhaustive coded coverage and independence of sufficient bounds. Still specify the internal Separation/Collection theorem and admissible-family contract for genuine all-name quantification; finite exhaustive coverage is not the general production interface.
- Specify the actual transitive-ground realization and equality adapter for the intended general model profile. A singleton structure and an external V code are not substitutes.
- Select a name coding representation only after proving the required ground-code closure and universe bounds. General RO-in-M remains a K2 construction, but its input/output coding contract must survive K0.
- Check the dependency order of fixed-formula definitions, value-set existence, rank bounds and extension axiom transfer. No step may use an extension axiom to justify the ground-side construction establishing that axiom.

The material coding and range-bound follow-ups have passed their corrected statements, as recorded below. Neither discharges the general ground-model closure requirements. The remaining items are explicit acceptance requirements for the representation decision, not promises of completed code.

## Representation decisions after review

These are design contracts inferred from the checked probes and mathematical review. The general contracts in this section have not yet been implemented in Agda.

**Names.** Prefer investigating material name codes inside the supplied ground, with a host recursive presentation and a proved adapter. A possible carrier is the subtype of ground elements satisfying an internal name predicate. Its h-set property follows if the ground carrier is an h-set and that predicate is proposition-valued, but the predicate, recursion and closure still need construction. A code-indexed W carrier is another useful representation; its h-set theorem does not make arbitrary host branch or weight functions internal to M. A production adapter must certify the domain, subname relation and weight graph as actual ground sets.

Track the universe levels of ground elements, codes, decoded index types, Boolean values and name predicates separately. Do not assume resizing, or a small carrier for all names of a proper-class ground. Internal Foundation in an arbitrary first-order model does not alone supply external well-founded recursion. The transitive-ground realization must provide the latter explicitly. Raw paths, material graph equality and Boolean-valued equality have different purposes; no quotient is justified without proving the relevant semantics descends to it.

**Quantifiers.** The public interface should consume a ground-admitted family and a certificate that it has the same upper bounds as the full target domain. For a family `f : I -> S` and an already defined fixed-subformula value `φ`, a sufficient interface is:

```text
admitted LUB of the internally coded family i |-> φ(f(i))
upper-bound transfer:
  for every c, (for every i, φ(f(i)) ≤ c) implies (for every x, φ(x) ≤ c)
```

Its LUB is then an upper bound of all target values and is least among their upper bounds. Two such certificates give equal values by antisymmetry. Exact value coverage, as checked in `Bounds.agda`, is a stronger sufficient certificate. Pointwise cofinal coverage is another sufficient certificate. Neither needs to be the only public representation. A value-set backend may instead give an internally coded set of attained values, with the corresponding upper-bound equivalence, without selecting one name per value.

The finite probe grammar does not even include an empty index code. Production admitted families must support empty and infinite ground sets. The concrete rank-one bound is not a universal rank bound for arbitrary formulas. Ground Separation/Collection can be investigated once the fixed subformula's internal value relation is defined and proved correct: form its attained values inside B, collect a set of name witnesses when needed, and bound their ranks. That argument must not assume a host choice function or the extension's Replacement. General mixing and maximum principles are separate consumers.

**Completion.** Keep carrier/order codes, dense-map and compatibility laws, full Boolean laws, internal completeness, semantic transport and property transfer as separate certificates. The finite nonseparative example checks only named slices. A typecheck under an excessive closure assumption cannot replace the ground adapter.

**Next source briefs.** Resolve the actual transitive-ground decoding adapter, then the internal name predicate/support operations and universe ledger, then a fixed-formula internal value-set/bound construction. These are the unresolved prerequisites for committing to production K1/K3/K4 interfaces. They do not require completing general RO-in-M during K0 or adding a proof system.

## Existing transitive realization: source audit

A follow-up read-only audit located real reusable interfaces beyond the singleton probe. The coordinator inspected the definitions below in the isolated baseline. This audit did not run a new Agda check or implement the proposed adapter.

| Existing component | Reusable fact | Boundary |
|---|---|---|
| [V.Hierarchy](../../src/V/Hierarchy.lagda.md), lines 88-93 | `𝒮ᵥ` uses V as carrier and path equality as structural equality | Not a proof that an arbitrary subclass is a ground |
| [FOL.ZFStructure](../../src/FOL/ZFStructure.lagda.md), lines 173-197 | `_↾_` constructs the actual subtype structure; `↾-reflects` lifts equality of projections | Transitivity and axioms are separate data |
| [FOL.Absoluteness](../../src/FOL/Absoluteness.lagda.md), `Single`, lines 75-182 | Inner/outer semantics and bounded absoluteness for a transitive class | No unrestricted elementarity |
| [L.Constructible](../../src/L/Constructible.lagda.md), lines 380-415 | `isL-trans` and `𝒮ʟ = 𝒮ᵥ ↾ isL` give an actual nontrivial instance | Neither a countable ground nor an ambient L-generic |
| [L.Coding.Model](../../src/L/Coding/Model.lagda.md), lines 390-429 | Inner pair/numeral injectivity, `LCode`, and `codeBridge` already connect material syntax codes to V codes | Closure constructions are currently specialized to L |

For a restriction of `𝒮ᵥ`, structural equality is equality of first projections. Its soundness for subtype paths follows from `↾-reflects`; completeness follows from `cong fst`. Thus this realization does not need a new equality axiom. The general bare `ZFStructure` still needs its own coherence argument.

The next adapter should reuse this restriction/absoluteness layer, separate a ground axiom profile, and certify pair/numeral coding and projection agreement. Pair and numeral injectivity can then be derived from the ambient injectivity theorems instead of being new assumptions. A further internal-code-domain capability must state a set-sized parameter domain or use parameter-free syntax with separate assignments. It must not demand one ground set containing formula codes with arbitrary constants from all of M. A host type of syntax is not evidence that its entire image forms a set inside M, especially for a proper-class realization.

A generic internal decoder remains to be constructed for its stated code domain. This is distinct from a host compiler on an individual formula and from an internal truth predicate. Existing L coding is a source of reusable mathematics; extracting it requires a later source brief coordinated with the teaching work. This research task changes none of those source modules.

## Exact first-batch commands

From `/tmp/bedrock-k0-probes/model`, with the copied source tree and explicit cubical dependency:

```text
GHCRTS="-A64m -I0 -M8g" agda -l cubical -i /tmp/bedrock-k0-probes/model -i /tmp/bedrock-k0-probes/model/deps/src /tmp/bedrock-k0-probes/model/EqualityCoherence.agda
GHCRTS="-A64m -I0 -M8g" agda -l cubical -i /tmp/bedrock-k0-probes/model -i /tmp/bedrock-k0-probes/model/deps/src /tmp/bedrock-k0-probes/model/FixedFormulaCompiler.agda
```

From `/tmp/bedrock-k0-probes/names` with its local library file:

```text
GHCRTS="-A64m -I0 -M8g" agda Names.agda
```

From `/tmp/bedrock-k0-probes/completion/compile-root` with its copied source tree:

```text
GHCRTS="-A64m -I0 -M8g" agda -i /tmp/bedrock-k0-probes/completion -i src /tmp/bedrock-k0-probes/completion/NonseparativeCompletion.agda
GHCRTS="-A64m -I0 -M8g" agda -i /tmp/bedrock-k0-probes/completion -i src /tmp/bedrock-k0-probes/completion/VCodeWitness.agda
```

See the agent reports in `/tmp/bedrock-k0-probes/{model,names,completion}/report.md` for setup diagnostics and source dependencies. The code snapshots and hashes below are durable; temporary cache/log locations are not guaranteed to persist.

## First-batch source snapshots

These text fences are archival probe sources. They are deliberately not imported into the production tree or treated as checked by a Markdown gate.

### model/EqualityCoherence.agda

SHA-256: `b871f1e6bc1762caf8963613e42a6040e786cc82ab28bf1434092922fd42085d`

```text
{-# OPTIONS --cubical --safe --guardedness #-}

module EqualityCoherence where

open import Base.Prelude
open import Base.Truth
open import FOL.ZFStructure using ( ZFStructure; module hPropStructure )
open import Cubical.Data.Unit using ( Unit*; tt*; isPropUnit* )

record EqualityCoherence {ℓ} (𝒮 : ZFStructure (hPropAlgebra ℓ))
                         : Type (ℓ-suc ℓ) where
  open hPropStructure 𝒮
  field
    ≈-sound    : {x y : S} → ⟨ x ≈ˢ y ⟩ → x ≡ y
    ≈-complete : {x y : S} → x ≡ y → ⟨ x ≈ˢ y ⟩

  ≈-refl : (x : S) → ⟨ x ≈ˢ x ⟩
  ≈-refl x = ≈-complete refl

  ∈-respects-left : {x y z : S} → ⟨ x ≈ˢ y ⟩ → (x ∈ˢ z) ≡ (y ∈ˢ z)
  ∈-respects-left p = cong (_∈ˢ _) (≈-sound p)

  ∈-respects-right : {x y z : S} → ⟨ y ≈ˢ z ⟩ → (x ∈ˢ y) ≡ (x ∈ˢ z)
  ∈-respects-right {x = x} p = cong (x ∈ˢ_) (≈-sound p)

unitStructure : ZFStructure (hPropAlgebra ℓ-zero)
unitStructure = record
  { S      = Unit*
  ; isSetS = isProp→isSet isPropUnit*
  ; _≈ˢ_   = λ x y → (x ≡ y) , isProp→isSet isPropUnit* x y
  ; _∈ˢ_   = λ _ _ → Unit* , isPropUnit* }

unitEqualityCoherence : EqualityCoherence unitStructure
unitEqualityCoherence = record
  { ≈-sound    = λ p → p
  ; ≈-complete = λ p → p }

unit-membership-substitution : let open hPropStructure unitStructure
                               in {x y z : S} → ⟨ x ≈ˢ y ⟩
                                  → (x ∈ˢ z) ≡ (y ∈ˢ z)
unit-membership-substitution =
  EqualityCoherence.∈-respects-left unitEqualityCoherence
```

### model/FixedFormulaCompiler.agda

SHA-256: `1da2e722d9f9f1d55a73d728177563cf986225f3d0b240ab2bf2e6d86b96ca20`

```text
{-# OPTIONS --cubical --safe --guardedness #-}

module FixedFormulaCompiler where

open import Base.Prelude
open import Base.Truth
open import FOL.Syntax using ( Formula; con; var; _≐_; ∀̇_; ∀̇∈ )
open import EqualityCoherence using ( unitStructure )
open import FOL.Semantics (hPropAlgebra ℓ-zero) EqualityCoherence.unitStructure
  using ( module At )
open import FOL.Manipulation.Relativization using
  ( relativize; module Correct )
open import Cubical.Data.Unit using ( Unit*; tt* )

K : Type ℓ-zero
K = Unit* {ℓ-zero}

bound : K
bound = tt*

open At K (λ _ → bound) using ( _⊨_ )
module Rel = Correct (hPropAlgebra ℓ-zero) unitStructure (λ _ → bound) bound

reflexiveSentence : Formula K 0
reflexiveSentence = ∀̇ (var zero ≐ var zero)

compiler-shape : relativize bound reflexiveSentence
               ≡ ∀̇∈ (con bound) (var zero ≐ var zero)
compiler-shape = refl

fixed-formula-correct : ([] ⊨ relativize bound reflexiveSentence)
                      ≡ ([] Rel.⊨ᴬ reflexiveSentence)
fixed-formula-correct = Rel.relativize-correct reflexiveSentence []

compiled-formula-valid : ⟨ [] ⊨ relativize bound reflexiveSentence ⟩
compiled-formula-valid = λ x _ → refl
```

### names/Names.agda

SHA-256: `dfb66f04d15fe20658daf395b49305ac3a9fa71cece2788f817218208cf9735c`

```text
{-# OPTIONS --cubical --safe --guardedness #-}
module Names where

open import Cubical.Foundations.Prelude using (Type; _≡_; refl; cong; sym; _∙_; transport; transportRefl; isSet)
open import Cubical.Foundations.HLevels using (isSetRetract)
open import Cubical.Foundations.Univalence using (ua; uaβ)
open import Cubical.Data.Bool using (Bool; false; true; _and_; _or_; not; _≟_; notEquiv; false≢true; true≢false)
open import Cubical.Data.Empty using (⊥)
open import Cubical.Data.Sigma using (_×_; _,_; fst; snd; discreteΣ)
open import Cubical.Relation.Nullary using (Discrete; yes; no; Discrete→isSet)

B : Type₀
B = Bool × Bool

⊤ᴮ ⊥ᴮ a b : B
⊤ᴮ = true , true
⊥ᴮ = false , false
a = true , false
b = false , true

infixr 6 _⊓_
infixr 5 _⊔_
infixr 4 _⇒_

_⊓_ _⊔_ _⇒_ : B → B → B
(x , y) ⊓ (z , w) = (x and z) , (y and w)
(x , y) ⊔ (z , w) = (x or z) , (y or w)
(x , y) ⇒ (z , w) = (not x or z) , (not y or w)

data Name : Type₀ where
  empty : Name
  pair : B → Name → B → Name → Name

_≈ᴮ_ : Name → Name → B
empty ≈ᴮ empty = ⊤ᴮ
empty ≈ᴮ pair c x d y = (c ⇒ ⊥ᴮ) ⊓ (d ⇒ ⊥ᴮ)
pair c x d y ≈ᴮ empty = (c ⇒ ⊥ᴮ) ⊓ (d ⇒ ⊥ᴮ)
pair c x d y ≈ᴮ pair e z f w =
  (c ⇒ ((e ⊓ (x ≈ᴮ z)) ⊔ (f ⊓ (x ≈ᴮ w)))) ⊓
  (d ⇒ ((e ⊓ (y ≈ᴮ z)) ⊔ (f ⊓ (y ≈ᴮ w)))) ⊓
  (e ⇒ ((c ⊓ (z ≈ᴮ x)) ⊔ (d ⊓ (z ≈ᴮ y)))) ⊓
  (f ⇒ ((c ⊓ (w ≈ᴮ x)) ⊔ (d ⊓ (w ≈ᴮ y))))

_∈ᴮ_ : Name → Name → B
x ∈ᴮ empty = ⊥ᴮ
x ∈ᴮ pair c y d z = (c ⊓ (x ≈ᴮ y)) ⊔ (d ⊓ (x ≈ᴮ z))

leftName rightName zeroName : Name
leftName = pair a empty ⊥ᴮ empty
rightName = pair b empty ⊥ᴮ empty
zeroName = pair ⊥ᴮ empty ⊥ᴮ empty

membership-left : empty ∈ᴮ leftName ≡ a
membership-left = refl

equality-partial : empty ≈ᴮ leftName ≡ b
equality-partial = refl

equality-zero : empty ≈ᴮ zeroName ≡ ⊤ᴮ
equality-zero = refl

membership-congruence-example : zeroName ∈ᴮ leftName ≡ empty ∈ᴮ leftName
membership-congruence-example = refl

tag : Name → Bool
tag empty = false
tag (pair _ _ _ _) = true

zero-distinct : empty ≡ zeroName → ⊥
zero-distinct p = false≢true (cong tag p)

weightLeft weightRight : Name → B
weightLeft empty = ⊥ᴮ
weightLeft (pair c _ _ _) = c
weightRight empty = ⊥ᴮ
weightRight (pair _ _ d _) = d

childLeft childRight : Name → Name
childLeft empty = empty
childLeft (pair _ x _ _) = x
childRight empty = empty
childRight (pair _ _ _ y) = y

name-discrete : Discrete Name
name-discrete empty empty = yes refl
name-discrete empty (pair _ _ _ _) = no (λ p → false≢true (cong tag p))
name-discrete (pair _ _ _ _) empty = no (λ p → true≢false (cong tag p))
name-discrete (pair c x d y) (pair e z f w)
  with discreteΣ _≟_ (λ _ → _≟_) c e | name-discrete x z | discreteΣ _≟_ (λ _ → _≟_) d f | name-discrete y w
... | no p | _ | _ | _ = no (λ q → p (cong weightLeft q))
... | yes p | no q | _ | _ = no (λ r → q (cong childLeft r))
... | yes p | yes q | no r | _ = no (λ s → r (cong weightRight s))
... | yes p | yes q | yes r | no s = no (λ t → s (cong childRight t))
... | yes p | yes q | yes r | yes s = yes (λ i → pair (p i) (q i) (r i) (s i))

name-is-set : isSet Name
name-is-set = Discrete→isSet name-discrete

_≤₂_ : Bool → Bool → Type₀
x ≤₂ y = x and y ≡ x

_≤ᴮ_ : B → B → Type₀
(x , y) ≤ᴮ (z , w) = (x ≤₂ z) × (y ≤₂ w)

join-left : (x y : Bool) → x ≤₂ (x or y)
join-left false y = refl
join-left true y = refl

join-right : (x y : Bool) → y ≤₂ (x or y)
join-right false y with y
... | false = refl
... | true = refl
join-right true false = refl
join-right true true = refl

join-least : (x y z : Bool) → x ≤₂ z → y ≤₂ z → (x or y) ≤₂ z
join-least false y z p q = q
join-least true y z p q = p

⋁₂ : (Bool → B) → B
⋁₂ f = f false ⊔ f true

join-upper : (f : Bool → B) (i : Bool) → f i ≤ᴮ ⋁₂ f
join-upper f false = join-left (fst (f false)) (fst (f true)) , join-left (snd (f false)) (snd (f true))
join-upper f true = join-right (fst (f false)) (fst (f true)) , join-right (snd (f false)) (snd (f true))

join-least-upper : (f : Bool → B) (c : B) → ((i : Bool) → f i ≤ᴮ c) → ⋁₂ f ≤ᴮ c
join-least-upper f c h =
  join-least (fst (f false)) (fst (f true)) (fst c) (fst (h false)) (fst (h true)) ,
  join-least (snd (f false)) (snd (f true)) (snd c) (snd (h false)) (snd (h true))

family : Bool → Name
family false = leftName
family true = rightName

existential : B
existential = ⋁₂ (λ i → empty ∈ᴮ family i)

existential-top : existential ≡ ⊤ᴮ
existential-top = refl

no-listed-full-witness : (i : Bool) → (empty ∈ᴮ family i) ≡ ⊤ᴮ → ⊥
no-listed-full-witness false p = false≢true (cong snd p)
no-listed-full-witness true p = false≢true (cong fst p)

data Raw : Type₁ where
  sup : (A : Type₀) → (A → Raw) → (A → B) → Raw

rawEmpty : Raw
rawEmpty = sup ⊥ (λ ()) (λ ())

shape : Raw → Type₀
shape (sup A _ _) = A

section : Type₀ → Raw
section A = sup A (λ _ → rawEmpty) (λ _ → ⊤ᴮ)

raw-set-implies-universe-set : isSet Raw → isSet Type₀
raw-set-implies-universe-set = isSetRetract section shape (λ _ → refl)

universe-not-set : isSet Type₀ → ⊥
universe-not-set h = false≢true
  (sym (uaβ notEquiv true) ∙
   cong (λ p → transport p true) (h Bool Bool (ua notEquiv) refl) ∙
   transportRefl true)

raw-not-set : isSet Raw → ⊥
raw-not-set h = universe-not-set (raw-set-implies-universe-set h)

open import Cubical.Data.W.Indexed using (IW; isOfHLevelSuc-IW)
open import Cubical.Data.Unit using (Unit; tt)
open import Cubical.Data.Sigma using (Σ)
open import Cubical.Foundations.HLevels using (isSetΣ; isSetΠ)
open import Cubical.Data.Bool using (isSetBool)
open import Cubical.Data.Nat using (zero; suc)

module Coded (C : Type₀) (E : C → Type₀) (h : isSet C) where
  Shape : Unit → Type₀
  Shape _ = Σ C (λ c → E c → B)

  Branch : (u : Unit) → Shape u → Type₀
  Branch _ s = E (fst s)

  CodedName : Type₀
  CodedName = IW Shape Branch (λ _ _ _ → tt) tt

  coded-name-is-set : isSet CodedName
  coded-name-is-set = isOfHLevelSuc-IW (suc zero)
    (λ _ → isSetΣ h (λ _ → isSetΠ (λ _ → isSetΣ isSetBool (λ _ → isSetBool)))) tt

finiteBranch : Bool → Type₀
finiteBranch false = ⊥
finiteBranch true = Bool

finite-coded-name-is-set : isSet (Coded.CodedName Bool finiteBranch isSetBool)
finite-coded-name-is-set = Coded.coded-name-is-set Bool finiteBranch isSetBool
```

### names/names.agda-lib

SHA-256: `78f3a50e5d0bd3cf404394d5cb823b7d8e69b3a6ac6f8713e1d122d6f3c91e0e`

```text
name: names-probe
include: .
depend: cubical
```

### completion/NonseparativeCompletion.agda

SHA-256: `61a8c840abf196861a5fdfcd95daff33143232bd98ec78e1e26dca0d52fd4975`

```text
{-# OPTIONS --cubical --safe --guardedness #-}

module NonseparativeCompletion where

open import Cubical.Foundations.Prelude
  using ( Type; _≡_; refl; Σ; _,_; fst; snd; subst )
open import Cubical.Data.Sigma using ( _×_ )
open import Cubical.Data.Empty using ( ⊥ )
open import Cubical.Data.Unit using ( Unit; tt )

data Boolean : Type where
  zero left right one : Boolean

data _≤ᴮ_ : Boolean → Boolean → Type where
  zero≤      : {b : Boolean} → zero ≤ᴮ b
  left≤left  : left ≤ᴮ left
  left≤one   : left ≤ᴮ one
  right≤right : right ≤ᴮ right
  right≤one  : right ≤ᴮ one
  one≤one    : one ≤ᴮ one

infix 20 _≤ᴮ_

≤ᴮ-refl : (b : Boolean) → b ≤ᴮ b
≤ᴮ-refl zero  = zero≤
≤ᴮ-refl left  = left≤left
≤ᴮ-refl right = right≤right
≤ᴮ-refl one   = one≤one

≤ᴮ-trans : {a b c : Boolean} → a ≤ᴮ b → b ≤ᴮ c → a ≤ᴮ c
≤ᴮ-trans zero≤ q = zero≤
≤ᴮ-trans left≤left q = q
≤ᴮ-trans left≤one one≤one = left≤one
≤ᴮ-trans right≤right q = q
≤ᴮ-trans right≤one one≤one = right≤one
≤ᴮ-trans one≤one one≤one = one≤one

_∧ᴮ_ : Boolean → Boolean → Boolean
zero  ∧ᴮ b     = zero
left  ∧ᴮ zero  = zero
left  ∧ᴮ left  = left
left  ∧ᴮ right = zero
left  ∧ᴮ one   = left
right ∧ᴮ zero  = zero
right ∧ᴮ left  = zero
right ∧ᴮ right = right
right ∧ᴮ one   = right
one   ∧ᴮ b     = b

_∨ᴮ_ : Boolean → Boolean → Boolean
zero  ∨ᴮ b     = b
left  ∨ᴮ zero  = left
left  ∨ᴮ left  = left
left  ∨ᴮ right = one
left  ∨ᴮ one   = one
right ∨ᴮ zero  = right
right ∨ᴮ left  = one
right ∨ᴮ right = right
right ∨ᴮ one   = one
one   ∨ᴮ b     = one

¬ᴮ_ : Boolean → Boolean
¬ᴮ zero  = one
¬ᴮ left  = right
¬ᴮ right = left
¬ᴮ one   = zero

infixr 22 _∧ᴮ_
infixr 21 _∨ᴮ_
infix 23 ¬ᴮ_

complement-meet : (b : Boolean) → b ∧ᴮ (¬ᴮ b) ≡ zero
complement-meet zero  = refl
complement-meet left  = refl
complement-meet right = refl
complement-meet one   = refl

complement-join : (b : Boolean) → b ∨ᴮ (¬ᴮ b) ≡ one
complement-join zero  = refl
complement-join left  = refl
complement-join right = refl
complement-join one   = refl

data Nonzero : Boolean → Type where
  left+  : Nonzero left
  right+ : Nonzero right
  one+   : Nonzero one

BooleanCompatible : Boolean → Boolean → Type
BooleanCompatible b c =
  Σ Boolean (λ d → Nonzero d × ((d ≤ᴮ b) × (d ≤ᴮ c)))

data Condition : Type where
  top left₀ left₁ right₀ : Condition

embed : Condition → Boolean
embed top    = one
embed left₀  = left
embed left₁  = left
embed right₀ = right

_≤ᴾ_ : Condition → Condition → Type
p ≤ᴾ q = embed p ≤ᴮ embed q

infix 20 _≤ᴾ_

ConditionCompatible : Condition → Condition → Type
ConditionCompatible p q =
  Σ Condition (λ r → (r ≤ᴾ p) × (r ≤ᴾ q))

dense : (b : Boolean) → Nonzero b
      → Σ Condition (λ p → embed p ≤ᴮ b)
dense left  left+  = left₀ , left≤left
dense right right+ = right₀ , right≤right
dense one   one+   = top , one≤one

compatibility-preserved : {p q : Condition}
                        → ConditionCompatible p q
                        → BooleanCompatible (embed p) (embed q)
compatibility-preserved (top , r≤p , r≤q) =
  one , one+ , r≤p , r≤q
compatibility-preserved (left₀ , r≤p , r≤q) =
  left , left+ , r≤p , r≤q
compatibility-preserved (left₁ , r≤p , r≤q) =
  left , left+ , r≤p , r≤q
compatibility-preserved (right₀ , r≤p , r≤q) =
  right , right+ , r≤p , r≤q

compatibility-reflected : {p q : Condition}
                        → BooleanCompatible (embed p) (embed q)
                        → ConditionCompatible p q
compatibility-reflected (b , b+ , b≤p , b≤q) =
  fst (dense b b+) ,
  ≤ᴮ-trans (snd (dense b b+)) b≤p ,
  ≤ᴮ-trans (snd (dense b b+)) b≤q

left-duplicates : embed left₀ ≡ embed left₁
left-duplicates = refl

DistinguishLeft : Condition → Type
DistinguishLeft left₀ = Unit
DistinguishLeft left₁ = ⊥
DistinguishLeft _     = Unit

left-distinct : left₀ ≡ left₁ → ⊥
left-distinct e = subst DistinguishLeft e tt

SameSeparativeSemantics : Condition → Condition → Type
SameSeparativeSemantics p q =
  (r : Condition) →
  (ConditionCompatible r p → ConditionCompatible r q) ×
  (ConditionCompatible r q → ConditionCompatible r p)

left-same-separative-semantics : SameSeparativeSemantics left₀ left₁
left-same-separative-semantics r =
  (λ c → compatibility-reflected {p = r} {q = left₁}
    (subst-compatible
      (compatibility-preserved {p = r} {q = left₀} c)
      left-duplicates)) ,
  (λ c → compatibility-reflected {p = r} {q = left₀}
    (subst-compatible-back
      (compatibility-preserved {p = r} {q = left₁} c)
      left-duplicates))
  where
  subst-compatible : BooleanCompatible (embed r) (embed left₀)
                   → embed left₀ ≡ embed left₁
                   → BooleanCompatible (embed r) (embed left₁)
  subst-compatible c refl = c

  subst-compatible-back : BooleanCompatible (embed r) (embed left₁)
                        → embed left₀ ≡ embed left₁
                        → BooleanCompatible (embed r) (embed left₀)
  subst-compatible-back c refl = c
```

### completion/VCodeWitness.agda

SHA-256: `628f980d3c8ae3fe5527a12bb28d2ec670acbab5e53d6e98c490a465b6e4e9d0`

```text
{-# OPTIONS --cubical --safe --guardedness #-}

module VCodeWitness where

open import Base.Prelude using ( ℓ-zero; ℕ; _≡_ )
open import V.Coding {ℓ-zero} using ( #-inj )
open import Cubical.HITs.CumulativeHierarchy.Base using ( V )
open import Cubical.HITs.CumulativeHierarchy.Constructions
  using ( module InfinitySet )
open InfinitySet using ( #_ )

conditionCode : ℕ → V ℓ-zero
conditionCode = #_

conditionCode-inj : (m n : ℕ)
                  → conditionCode m ≡ conditionCode n
                  → m ≡ n
conditionCode-inj = #-inj
```

## Checked range-bound follow-up

`GHCRTS="-A64m -I0 -M8g" agda Bounds.agda`, from `/tmp/bedrock-k0-probes/names`, exited 0 without warnings. The proof uses a finite code grammar and a truncated exhaustive truth-value range certificate. LUB laws and order antisymmetry prove bound independence, eliminating truncation only into the order proposition. The concrete predicate ranges over the entire infinite carrier of finite binary names, but its values are covered by two or four names of rank at most one. Both presentations give the same partial Boolean value.

This strengthens the first two-instance existential check. It does not establish Separation/Collection in a material ground or bound arbitrary formulas over the full name universe. `RangeBound` is a sufficient certificate, obtained here by finite Boolean calculations. Its exact-value coverage and finite code grammar are probe choices, not mandatory production restrictions; the general interface may instead certify a ground-admitted family with the same upper bounds. No host choice or maximum principle is used.

### names/Bounds.agda

SHA-256: `4a5f48e5c2d1d6c1532ccdbdd53d7eff7a645420905c24d2400f76e9209ac7af`

```text
{-# OPTIONS --cubical --safe --guardedness #-}
module Bounds where

open import Names using (B; Name; empty; pair; a; ⊥ᴮ; _∈ᴮ_; _⊓_; _≤₂_; _≤ᴮ_; ⋁₂; join-upper; join-least-upper)
open import Cubical.Foundations.Prelude using (Type; _≡_; refl; cong; sym; subst; isProp)
open import Cubical.Foundations.HLevels using (isPropΣ)
open import Cubical.Data.Bool using (Bool; false; true; _and_; isSetBool; false≢true; true≢false)
open import Cubical.Data.Sigma using (Σ; _×_; _,_; fst; snd)
open import Cubical.Data.Unit using (Unit; tt)
open import Cubical.Data.Empty using () renaming (rec to absurd)
open import Cubical.HITs.PropositionalTruncation using (∥_∥₁; ∣_∣₁; rec)

bit-reflexive : (x : Bool) → x ≤₂ x
bit-reflexive false = refl
bit-reflexive true = refl

bit-transitive : (x y z : Bool) → x ≤₂ y → y ≤₂ z → x ≤₂ z
bit-transitive false y z p q = refl
bit-transitive true false z p q = absurd (false≢true p)
bit-transitive true true z p q = q

bit-antisymmetric : (x y : Bool) → x ≤₂ y → y ≤₂ x → x ≡ y
bit-antisymmetric false false p q = refl
bit-antisymmetric false true p q = absurd (false≢true q)
bit-antisymmetric true false p q = absurd (false≢true p)
bit-antisymmetric true true p q = refl

order-reflexive : (c : B) → c ≤ᴮ c
order-reflexive (x , y) = bit-reflexive x , bit-reflexive y

order-transitive : (c d e : B) → c ≤ᴮ d → d ≤ᴮ e → c ≤ᴮ e
order-transitive (x , y) (z , w) (u , v) p q =
  bit-transitive x z u (fst p) (fst q) , bit-transitive y w v (snd p) (snd q)

order-antisymmetric : (c d : B) → c ≤ᴮ d → d ≤ᴮ c → c ≡ d
order-antisymmetric (x , y) (z , w) p q i =
  bit-antisymmetric x z (fst p) (fst q) i , bit-antisymmetric y w (snd p) (snd q) i

order-is-prop : (c d : B) → isProp (c ≤ᴮ d)
order-is-prop (x , y) (z , w) =
  isPropΣ (isSetBool (x and z) x) (λ _ → isSetBool (y and w) y)

record Admitted {I : Type₀} (f : I → B) : Type₀ where
  field
    value : B
    upper : (i : I) → f i ≤ᴮ value
    least : (c : B) → ((i : I) → f i ≤ᴮ c) → value ≤ᴮ c

open Admitted

product-admitted : {I J : Type₀} (f : I × J → B)
  (p : (i : I) → Admitted (λ j → f (i , j)))
  → Admitted (λ i → value (p i)) → Admitted f
product-admitted f p q .value = value q
product-admitted f p q .upper (i , j) =
  order-transitive (f (i , j)) (value (p i)) (value q) (upper (p i) j) (upper q i)
product-admitted f p q .least c h = least q c (λ i → least (p i) c (λ j → h (i , j)))

data FiniteCode : Type₀ where
  unitCode boolCode : FiniteCode
  productCode : FiniteCode → FiniteCode → FiniteCode

El : FiniteCode → Type₀
El unitCode = Unit
El boolCode = Bool
El (productCode c d) = El c × El d

finite-admitted : (c : FiniteCode) (f : El c → B) → Admitted f
finite-admitted unitCode f .value = f tt
finite-admitted unitCode f .upper tt = order-reflexive (f tt)
finite-admitted unitCode f .least c h = h tt
finite-admitted boolCode f .value = ⋁₂ f
finite-admitted boolCode f .upper = join-upper f
finite-admitted boolCode f .least = join-least-upper f
finite-admitted (productCode c d) f = product-admitted f
  (λ i → finite-admitted d (λ j → f (i , j)))
  (finite-admitted c (λ i → value (finite-admitted d (λ j → f (i , j)))))

record RangeBound (S : Type₀) (φ : S → B) : Type₀ where
  field
    code : FiniteCode
    enumerate : El code → S
    covers : (x : S) → ∥ Σ (El code) (λ i → φ x ≡ φ (enumerate i)) ∥₁

open RangeBound

existentialValue : {S : Type₀} {φ : S → B} → RangeBound S φ → B
existentialValue {φ = φ} c = value (finite-admitted (code c) (λ i → φ (enumerate c i)))

bound-upper : {S : Type₀} {φ : S → B} (c : RangeBound S φ)
  → (x : S) → φ x ≤ᴮ existentialValue c
bound-upper {φ = φ} c x = rec (order-is-prop (φ x) (existentialValue c))
  (λ p → subst (λ b → b ≤ᴮ existentialValue c) (sym (snd p))
    (upper (finite-admitted (code c) (λ i → φ (enumerate c i))) (fst p)))
  (covers c x)

bound-least : {S : Type₀} {φ : S → B} (c : RangeBound S φ)
  → (b : B) → ((x : S) → φ x ≤ᴮ b) → existentialValue c ≤ᴮ b
bound-least {φ = φ} c b h =
  least (finite-admitted (code c) (λ i → φ (enumerate c i))) b (λ i → h (enumerate c i))

bound-independent : {S : Type₀} {φ : S → B} (c d : RangeBound S φ)
  → existentialValue c ≡ existentialValue d
bound-independent c d = order-antisymmetric (existentialValue c) (existentialValue d)
  (bound-least c (existentialValue d) (bound-upper d))
  (bound-least d (existentialValue c) (bound-upper c))

singleton : B → Name
singleton c = pair c empty ⊥ᴮ empty

singleton-value : (c : B) → empty ∈ᴮ singleton c ≡ c
singleton-value (false , false) = refl
singleton-value (false , true) = refl
singleton-value (true , false) = refl
singleton-value (true , true) = refl

φ : Name → B
φ x = a ⊓ (empty ∈ᴮ x)

fourBound : RangeBound Name φ
fourBound .code = productCode boolCode boolCode
fourBound .enumerate = singleton
fourBound .covers x = ∣ (empty ∈ᴮ x) , sym (cong (λ c → a ⊓ c) (singleton-value (empty ∈ᴮ x))) ∣₁

chooseName : Bool → Name
chooseName false = singleton ⊥ᴮ
chooseName true = singleton a

restricted-range : (c : B) → a ⊓ c ≡ φ (chooseName (fst c))
restricted-range (false , false) = refl
restricted-range (false , true) = refl
restricted-range (true , false) = refl
restricted-range (true , true) = refl

twoBound : RangeBound Name φ
twoBound .code = boolCode
twoBound .enumerate = chooseName
twoBound .covers x = ∣ fst (empty ∈ᴮ x) , restricted-range (empty ∈ᴮ x) ∣₁

existential-partial : existentialValue twoBound ≡ a
existential-partial = refl

presentation-independent : existentialValue fourBound ≡ existentialValue twoBound
presentation-independent = bound-independent fourBound twoBound

all-names-upper : (x : Name) → φ x ≤ᴮ a
all-names-upper = bound-upper twoBound

all-names-least : (c : B) → ((x : Name) → φ x ≤ᴮ c) → a ≤ᴮ c
all-names-least = bound-least twoBound

data RankAtMostOne : Name → Type₀ where
  empty-bound : RankAtMostOne empty
  pair-bound : (c d : B) → RankAtMostOne (pair c empty d empty)

four-rank-bound : (i : El (code fourBound)) → RankAtMostOne (enumerate fourBound i)
four-rank-bound i = pair-bound i ⊥ᴮ

two-rank-bound : (i : El (code twoBound)) → RankAtMostOne (enumerate twoBound i)
two-rank-bound false = pair-bound ⊥ᴮ ⊥ᴮ
two-rank-bound true = pair-bound a ⊥ᴮ
```

## Checked material-coding follow-up and specification correction

The following command, from `/tmp/bedrock-k0-probes/completion/compile-root`, exited 0:

```text
GHCRTS="-A64m -I0 -M8g" agda -i /tmp/bedrock-k0-probes/completion -i /tmp/bedrock-k0-probes/completion/compile-root/src /tmp/bedrock-k0-probes/completion/GroundCodes.agda
```

There are unsupported indexed-match warnings for the inherited order-transitivity/density definitions and `edge-complete`. The agent reports no holes, unsolved metas or constraints. The root reviewed the corrected source, including the assumptions and the material decoding directions.

An earlier version also typechecked, but its `contains-image` field quantified over arbitrary `A : Type` while the report described finite closure. That specification was rejected during root review. The archived revision restricts the image fields to the explicitly enumerated four-condition type and nine-edge type. These remain explicit closure assumptions, together with numeral and ordered-pair closure; no theorem deriving them from `isZFCModel` has been checked.

The source constructs actual ambient V sets for the carrier and graph. It proves code injectivity, edge soundness and completeness, and material graph membership implies the propositional truncation of the actual order. Conversely an actual order proof gives graph membership. It does not silently eliminate truncation into an arbitrary type. The conditional `GroundPresentation` theorem establishes membership of the two codes in M only from its stated finite closure contract. This is not a packaged ground-complete Boolean algebra or the general RO-in-M construction.

### completion/GroundCodes.agda

SHA-256: `753967e19087a0ffd9906a982a9766e989bd5d1c99800fa864afbce8130dec67`

```text
{-# OPTIONS --cubical --safe --guardedness #-}

module GroundCodes where

open import Base.Prelude
  using ( Type; ℓ-zero; ℓ-suc; ℕ; zero; suc; _≡_; refl; sym; _∙_; cong; cong₂; subst
        ; Σ; Σ-syntax; _,_; fst; snd; ⟨_⟩ )
open import Cubical.Data.Sigma using ( _×_ )
open import NonseparativeCompletion
  using ( Condition; top; left₀; left₁; right₀; _≤ᴾ_
        ; one≤one; left≤left; left≤one; right≤right; right≤one )
open import V.Coding {ℓ-zero} using ( pr; pr-inj; #-inj )
open import Cubical.HITs.CumulativeHierarchy.Base using ( V; sett; _∈_ )
open import Cubical.HITs.PropositionalTruncation using ( ∥_∥₁; ∣_∣₁ )
import Cubical.HITs.PropositionalTruncation as PT
open import Cubical.HITs.CumulativeHierarchy.Constructions
  using ( module InfinitySet )
open InfinitySet using ( #_ )

conditionTag : Condition → ℕ
conditionTag top    = zero
conditionTag left₀  = suc zero
conditionTag left₁  = suc (suc zero)
conditionTag right₀ = suc (suc (suc zero))

conditionCode : Condition → V ℓ-zero
conditionCode p = # conditionTag p

decodeTag : ℕ → Condition
decodeTag zero                         = top
decodeTag (suc zero)                   = left₀
decodeTag (suc (suc zero))             = left₁
decodeTag (suc (suc (suc zero)))       = right₀
decodeTag (suc (suc (suc (suc n))))   = right₀

decode-conditionTag : (p : Condition) → decodeTag (conditionTag p) ≡ p
decode-conditionTag top    = refl
decode-conditionTag left₀  = refl
decode-conditionTag left₁  = refl
decode-conditionTag right₀ = refl

conditionCode-inj : {p q : Condition}
  → conditionCode p ≡ conditionCode q → p ≡ q
conditionCode-inj {p} {q} e =
  sym (decode-conditionTag p) ∙
  cong decodeTag (#-inj (conditionTag p) (conditionTag q) e) ∙
  decode-conditionTag q

conditionCodes : V ℓ-zero
conditionCodes = sett Condition conditionCode

conditionCodes-spec : (x : V ℓ-zero)
  → ⟨ x ∈ conditionCodes ⟩
  ≡ ∥ Σ[ p ∈ Condition ] (conditionCode p ≡ x) ∥₁
conditionCodes-spec x = refl

data OrderEdge : Type where
  top-top         : OrderEdge
  left₀-left₀    : OrderEdge
  left₀-left₁    : OrderEdge
  left₀-top      : OrderEdge
  left₁-left₀    : OrderEdge
  left₁-left₁    : OrderEdge
  left₁-top      : OrderEdge
  right₀-right₀  : OrderEdge
  right₀-top     : OrderEdge

stronger : OrderEdge → Condition
stronger top-top        = top
stronger left₀-left₀   = left₀
stronger left₀-left₁   = left₀
stronger left₀-top     = left₀
stronger left₁-left₀   = left₁
stronger left₁-left₁   = left₁
stronger left₁-top     = left₁
stronger right₀-right₀ = right₀
stronger right₀-top    = right₀

weaker : OrderEdge → Condition
weaker top-top        = top
weaker left₀-left₀   = left₀
weaker left₀-left₁   = left₁
weaker left₀-top     = top
weaker left₁-left₀   = left₀
weaker left₁-left₁   = left₁
weaker left₁-top     = top
weaker right₀-right₀ = right₀
weaker right₀-top    = top

edgeCode : OrderEdge → V ℓ-zero
edgeCode e = pr (conditionCode (stronger e)) (conditionCode (weaker e))

orderGraph : V ℓ-zero
orderGraph = sett OrderEdge edgeCode

orderGraph-spec : (x : V ℓ-zero)
  → ⟨ x ∈ orderGraph ⟩
  ≡ ∥ Σ[ e ∈ OrderEdge ] (edgeCode e ≡ x) ∥₁
orderGraph-spec x = refl

edge-sound : (e : OrderEdge) → stronger e ≤ᴾ weaker e
edge-sound top-top        = one≤one
edge-sound left₀-left₀   = left≤left
edge-sound left₀-left₁   = left≤left
edge-sound left₀-top     = left≤one
edge-sound left₁-left₀   = left≤left
edge-sound left₁-left₁   = left≤left
edge-sound left₁-top     = left≤one
edge-sound right₀-right₀ = right≤right
edge-sound right₀-top    = right≤one

EdgeAt : Condition → Condition → Type
EdgeAt p q = Σ OrderEdge (λ e → (stronger e ≡ p) × (weaker e ≡ q))

edge-complete : (p q : Condition) → p ≤ᴾ q → EdgeAt p q
edge-complete top top one≤one = top-top , refl , refl
edge-complete top left₀ ()
edge-complete top left₁ ()
edge-complete top right₀ ()
edge-complete left₀ top left≤one = left₀-top , refl , refl
edge-complete left₀ left₀ left≤left = left₀-left₀ , refl , refl
edge-complete left₀ left₁ left≤left = left₀-left₁ , refl , refl
edge-complete left₀ right₀ ()
edge-complete left₁ top left≤one = left₁-top , refl , refl
edge-complete left₁ left₀ left≤left = left₁-left₀ , refl , refl
edge-complete left₁ left₁ left≤left = left₁-left₁ , refl , refl
edge-complete left₁ right₀ ()
edge-complete right₀ top right≤one = right₀-top , refl , refl
edge-complete right₀ left₀ ()
edge-complete right₀ left₁ ()
edge-complete right₀ right₀ right≤right = right₀-right₀ , refl , refl

edge-enumeration : (p q : Condition)
  → (EdgeAt p q → p ≤ᴾ q) × (p ≤ᴾ q → EdgeAt p q)
edge-enumeration p q = from-edge , edge-complete p q
  where
  from-edge : EdgeAt p q → p ≤ᴾ q
  from-edge (e , s , w) =
    subst (λ x → x ≤ᴾ q) s
      (subst (λ x → stronger e ≤ᴾ x) w (edge-sound e))

orderedPairCode : Condition → Condition → V ℓ-zero
orderedPairCode p q = pr (conditionCode p) (conditionCode q)

material-order-sound : (p q : Condition)
  → ⟨ orderedPairCode p q ∈ orderGraph ⟩ → ∥ p ≤ᴾ q ∥₁
material-order-sound p q = PT.map read
  where
  read : Σ[ e ∈ OrderEdge ] (edgeCode e ≡ orderedPairCode p q) → p ≤ᴾ q
  read (e , code-equality) = edge-enumeration p q .fst
    (e
    , conditionCode-inj (pr-inj code-equality .fst)
    , conditionCode-inj (pr-inj code-equality .snd))

material-order-complete : (p q : Condition)
  → p ≤ᴾ q → ⟨ orderedPairCode p q ∈ orderGraph ⟩
material-order-complete p q p≤q with edge-complete p q p≤q
... | e , s , w = ∣ e , cong₂ pr (cong conditionCode s) (cong conditionCode w) ∣₁

record FiniteGroundClosure (M : V ℓ-zero → Type) : Type (ℓ-suc ℓ-zero) where
  field
    contains-numeral : (n : ℕ) → M (# n)
    contains-pair    : {a b : V ℓ-zero} → M a → M b → M (pr a b)
    contains-four-image : (f : Condition → V ℓ-zero)
                        → ((p : Condition) → M (f p)) → M (sett Condition f)
    contains-nine-image : (f : OrderEdge → V ℓ-zero)
                        → ((e : OrderEdge) → M (f e)) → M (sett OrderEdge f)

record GroundPresentation (M : V ℓ-zero → Type) : Type where
  field
    carrier-in-ground : M conditionCodes
    order-in-ground   : M orderGraph

from-finite-ground-closure : {M : V ℓ-zero → Type}
  → FiniteGroundClosure M → GroundPresentation M
from-finite-ground-closure {M = M} c = record
  { carrier-in-ground = C.contains-four-image conditionCode condition-in
  ; order-in-ground = C.contains-nine-image edgeCode edge-in }
  where
  module C = FiniteGroundClosure c

  condition-in : (p : Condition) → M (conditionCode p)
  condition-in p = C.contains-numeral (conditionTag p)

  edge-in : (e : OrderEdge) → M (edgeCode e)
  edge-in e = C.contains-pair
    (condition-in (stronger e))
    (condition-in (weaker e))
```
