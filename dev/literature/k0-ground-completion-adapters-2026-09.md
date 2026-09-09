# K0 transitive realization and finite internal completion presentation

Date: 2026-09-09. Baseline: `287b6098`. This batch addresses E1 and E5 of the [exit checklist](k0-exit-checklist-2026-09.md). It builds on the existing actual L coding and the original finite nonseparative example. Production `src` is unchanged.

## A real restriction adapter with a separate axiom profile

`TransitiveGroundAdapter.Restriction M transitive` uses the existing restriction of HIT-V to a proposition-valued class M. Its carrier is the actual subtype, with first projection into V. Equality of projections reflects to subtype equality, membership projects definitionally, and the ambient accessibility proof restricts to the subtype to give external well-foundedness. Bounded formula absoluteness reuses the existing transitive-class theorem, with an explicit atomic-membership specialization.

These facts do not say that every transitive class satisfies ZF. The ground axiom profile remains separate; transitivity is needed by bounded absoluteness, and no ZFC inheritance theorem is asserted. External accessibility is obtained from this particular ambient HIT-V realization. An arbitrary first-order model's Foundation does not supply that accessibility. Numeral coding and injectivity also do not prove Infinity: the existing `isZFModel` uses a stronger standard-numeral interface, while this restriction adapter does not assume every transitive class contains the natural-number set. K1 must keep those profile distinctions explicit.

The L specialization identifies this actual restriction with the existing `𝒮ʟ`, exports the concrete pair/numeral coding and projection evidence, and supplies the actual empty set with its empty-membership specification from the proved L ZF model. Thus the adapter is not the old singleton model example, and its axiom evidence is not merely a renamed empty interface.

The generic carrier and predicate levels are explicit at `ℓ-suc ℓ`. No resizing or small set of all M elements is inferred. In particular, individual formula codes and finite assignments do not imply one internal set containing codes with every possible constant from a proper-class ground. Full general decoder/code-domain implementation and the complete ordinary axiom bridge remain K1 work.

## Finite images are proved from actual ground operations

`FiniteGroundImage.Construction` accepts an ordinary structure, its existing ZF model operations and equality coherence. It constructs the image of any supplied `Fin n → S` by finite insertion using empty set, pair and union. It proves introduction, elimination and exact membership:

```text
z belongs to image(f)
  iff merely there is i : Fin n with z = f(i).
```

The zero-length case is supported. Repeated entries are allowed. Neither injectivity nor a choice of image representatives is required. The theorem quantifies over explicitly finite domains; it does not reintroduce the rejected closure under images of arbitrary host types. The input model record is stronger than the three set operations the proof actually uses; that existing record is an adapter input, not a new minimal axiom profile.

This discharges the previous finite-image closure risk constructively. The concrete L instance obtains all elements and resulting image sets from actual L operations. It no longer assumes `FiniteGroundClosure` for four- and nine-element images.

## Four actual L sets and their certified map

`FiniteCompletionInL` reuses the original `NonseparativeCompletion` and the finite edge enumeration in `GroundCodes`. Both legacy files are copied unchanged into the common temporary compile root. The new source enumerates their four conditions and nine order edges with `Fin 4` and `Fin 9`, and uses existing L numerals and ordered pairs to construct:

- the condition carrier;
- the nine-edge order graph;
- the four-element Boolean carrier;
- the four-entry completion-map graph.

All four outputs are actual L sets. The source proves the carrier and map membership descriptions, the two directions between material order-graph membership and the truncated original order, map landing and output uniqueness, and the coded dense-map witness. The map sends two different source condition codes to the same Boolean code, with the original nonseparative semantics supplying the example. No representative of a separative class is selected.

The dense-map certificate retains the original finite Boolean order as an interpreted host relation on the named Boolean codes. This is a finite ground-coded presentation and map test, not a fully packaged internal Boolean algebra with every operation graph and arbitrary coded-family completeness. Those full K2 outputs remain explicit future obligations. The legacy ambient `sett` codes and the new finite L construction need not be definitionally identical; this batch reuses their enumeration/order mathematics and proves the actual L membership interfaces directly.

## Acceptance and remaining boundary

This is the E1/E5 probe evidence required to settle a real transitive realization and a finite internal completion presentation. It does not implement general regular-open completion, a generic filter, general axiom transfer or Cohen forcing. E1 and E5 pass at these adapter/presentation boundaries. The final acceptance decision must preserve the explicit axiom and code-domain contracts and the limitations of the legacy finite certificate.

E2 and E6 still require the consolidated representation and assumption audit, including the ordinary quotient/fullness/ultrafilter extraction interfaces. The existing bounded L extraction theorem is relevant evidence for that audit, not an internal ultrafilter existence theorem. K0 remains open until that final decision is complete.

## Verification and assumptions

The final sources passed safe Agda checking with `GHCRTS="-A64m -I0 -M8g"`, at most two checks concurrently, in the common temporary compile root. The final finite-completion check returned no warnings. The original ledger records indexed-match warnings from the earlier standalone probe run; this batch does not change either legacy source or suppress warnings.

The generic restriction adapter has no LEM parameter; only its Constructible specialization takes the existing successor-level LEM. No host Choice, BPI, Zorn, resizing or genericity premise is introduced. The generic finite-image construction has no LEM parameter. The actual L instance uses the existing `LEM (ℓ-suc ℓ)`. Existential image witnesses are eliminated only into propositions. Each finite enumeration and the original dense witness are supplied by explicit finite functions.

Scoped prose/glossary gates, source snapshot hashes and exact bytes, local links and `git diff --check` passed. All 123 tracked production files and copied probe-baseline files match `287b6098` byte-for-byte. Whole-tree and trilingual chapter gates were not run for this temporary-probe/documentation change.

The initial transitive-adapter version exhausted the fixed 8 GB heap while exposing the full L model. The final interface refers narrowly to the existing concrete empty-set and coding theorems and passes. An explicit restriction parameter resolved an equality-reflection meta. The finite completion instance corrected an initially wrong import home for `numeralL` and the orientation of the map-uniqueness equality chain before its final successful check.

Final commands from the common temporary compile root:

```sh
GHCRTS="-A64m -I0 -M8g" agda src/FiniteGroundImage.agda
GHCRTS="-A64m -I0 -M8g" agda src/TransitiveGroundAdapter.agda
GHCRTS="-A64m -I0 -M8g" agda src/FiniteCompletionInL.agda
```

## Source snapshots

### FiniteGroundImage.agda

SHA-256: `3d5d26f78c997c0f0c42865406f6a2c8c749e2f60827e3d8a66adc1088ed011c`.

```text
{-# OPTIONS --cubical --safe --guardedness #-}

open import Base.Prelude
open import Base.Truth
open import FOL.ZFStructure using ( ZFStructure; module hPropStructure )

module FiniteGroundImage {ℓ : Level} (𝒮 : ZFStructure (hPropAlgebra ℓ)) where

open hPropStructure 𝒮
import FOL.ZFModel as Model
open import Cubical.Data.Sum using ( _⊎_; inl; inr )
import Cubical.Data.Empty as Empty
open import Cubical.Functions.Logic using ( ⇔toPath )
import Cubical.HITs.PropositionalTruncation as PT
open PT using ( ∥_∥₁; ∣_∣₁ )

module Construction (ground : Model.isZFModel 𝒮)
  (reflects : ∀ {x y} → ⟨ x ≈ˢ y ⟩ → x ≡ y)
  (reflexive : ∀ x → ⟨ x ≈ˢ x ⟩) where

  module Ground = Model.isZFModel ground
    using ( ∅; hasEmpty; pair; pair-spec; ⋃; hasUnion )

  insert : S → S → S
  insert a D = Ground.⋃ (Ground.pair (Ground.pair a a) D)

  insert-out : ∀ z a D → ⟨ z ∈ˢ insert a D ⟩ → ∥ (z ≡ a) ⊎ ⟨ z ∈ˢ D ⟩ ∥₁
  insert-out z a D member = PT.rec PT.squash₁
    (λ { (u , uPair , zu) → PT.rec PT.squash₁
      (λ { (inl eq) → PT.map (λ { (inl same) → inl (reflects same)
                                  ; (inr same) → inl (reflects same) })
             (subst ⟨_⟩ (Ground.pair-spec a a z)
               (subst (λ v → ⟨ z ∈ˢ v ⟩) (reflects eq) zu))
         ; (inr eq) → ∣ inr (subst (λ v → ⟨ z ∈ˢ v ⟩) (reflects eq) zu) ∣₁ })
      (subst ⟨_⟩ (Ground.pair-spec (Ground.pair a a) D u) uPair) })
    (subst ⟨_⟩ (Model.℩-spec 𝒮 (Ground.hasUnion (Ground.pair (Ground.pair a a) D)) z) member)

  insert-head : ∀ a D → ⟨ a ∈ˢ insert a D ⟩
  insert-head a D = subst ⟨_⟩
    (sym (Model.℩-spec 𝒮 (Ground.hasUnion (Ground.pair (Ground.pair a a) D)) a))
    ∣ Ground.pair a a ,
      subst ⟨_⟩ (sym (Ground.pair-spec (Ground.pair a a) D (Ground.pair a a)))
        ∣ inl (reflexive (Ground.pair a a)) ∣₁ ,
      subst ⟨_⟩ (sym (Ground.pair-spec a a a)) ∣ inl (reflexive a) ∣₁ ∣₁

  insert-tail : ∀ z a D → ⟨ z ∈ˢ D ⟩ → ⟨ z ∈ˢ insert a D ⟩
  insert-tail z a D member = subst ⟨_⟩
    (sym (Model.℩-spec 𝒮 (Ground.hasUnion (Ground.pair (Ground.pair a a) D)) z))
    ∣ D , subst ⟨_⟩ (sym (Ground.pair-spec (Ground.pair a a) D D))
      ∣ inr (reflexive D) ∣₁ , member ∣₁

  image : ∀ {n} → (Fin n → S) → S
  image {zero} f = Ground.∅
  image {suc n} f = insert (f zero) (image (λ i → f (suc i)))

  image-out : ∀ {n} (f : Fin n → S) z → ⟨ z ∈ˢ image f ⟩
    → ∥ Σ[ i ∈ Fin n ] z ≡ f i ∥₁
  image-out {zero} f z member = Empty.rec*
    (subst ⟨_⟩ (Ground.hasEmpty .fst .snd z) member)
  image-out {suc n} f z member = PT.rec PT.squash₁
    (λ { (inl eq) → ∣ zero , eq ∣₁
       ; (inr old) → PT.map (λ { (i , eq) → suc i , eq })
         (image-out (λ i → f (suc i)) z old) })
    (insert-out z (f zero) (image (λ i → f (suc i))) member)

  image-entry : ∀ {n} (f : Fin n → S) i → ⟨ f i ∈ˢ image f ⟩
  image-entry {suc n} f zero = insert-head (f zero) (image (λ i → f (suc i)))
  image-entry {suc n} f (suc i) = insert-tail (f (suc i)) (f zero)
    (image (λ j → f (suc j))) (image-entry (λ j → f (suc j)) i)

  image-in : ∀ {n} (f : Fin n → S) z → ∥ Σ[ i ∈ Fin n ] z ≡ f i ∥₁
    → ⟨ z ∈ˢ image f ⟩
  image-in f z = PT.rec (snd (z ∈ˢ image f))
    (λ { (i , eq) → subst (λ v → ⟨ v ∈ˢ image f ⟩) (sym eq) (image-entry f i) })

  image-reading : ∀ {n} (f : Fin n → S) z
    → (z ∈ˢ image f) ≡ (∥ Σ[ i ∈ Fin n ] z ≡ f i ∥₁ , PT.squash₁)
  image-reading f z = ⇔toPath (image-out f z) (image-in f z)
```

### TransitiveGroundAdapter.agda

SHA-256: `52c7dbe8477973817a33c0c6833d9c460cce8a11e4e8bd5840243bf20be607c7`.

```text
{-# OPTIONS --cubical --safe --guardedness #-}

open import Base.Prelude
open import Base.Truth
open import Base.Classical using ( LEM )

module TransitiveGroundAdapter {ℓ : Level} where

open import FOL.ZFStructure using
  ( ZFStructure; Transitive; _↾_; ↾-reflects; module hPropStructure )
open import FOL.Syntax using ( Term; Formula )
open import FOL.LevyHierarchy using ( Δ₀; δ-∈ )
import FOL.Absoluteness
open import V.Hierarchy {ℓ} using ( 𝒮ᵥ; regularityV )
open import L.Constructible {ℓ} using ( 𝒮ʟ; isL; isL-trans )
import CoordinateDecoder
open import L.Axioms.Basic {ℓ} using ( ∅ʟ; hasEmptyL )
open import L.Coding.Model {ℓ}
  using ( prʟ; prʟ-fst; prʟ-inj; numeralL-inj )
open import L.Axioms.Numerals {ℓ} using ( numeralL; numeralL-fst )
open import Cubical.Data.Vec using ( map )
open import Cubical.Induction.WellFounded using ( Acc; acc; WellFounded )

open TruthAlgebra (hPropAlgebra (ℓ-suc ℓ))

module Restriction
  (M : ZFStructure.S 𝒮ᵥ → hProp (ℓ-suc ℓ))
  (transitive : Transitive 𝒮ᵥ M) where

  structure : ZFStructure (hPropAlgebra (ℓ-suc ℓ))
  structure = 𝒮ᵥ ↾ M

  module Ambient = hPropStructure 𝒮ᵥ
  module Inner = hPropStructure structure
  module Absolute = FOL.Absoluteness.Single 𝒮ᵥ M transitive

  Carrier : Type (ℓ-suc ℓ)
  Carrier = Inner.S

  project : Carrier → Ambient.S
  project = fst

  equality-reflect : ∀ {a b : Carrier} → project a ≡ project b → a ≡ b
  equality-reflect = ↾-reflects {𝒮 = 𝒮ᵥ} {M = M}

  membership-projection : ∀ a b → (a Inner.∈ˢ b) ≡ (project a Ambient.∈ˢ project b)
  membership-projection a b = refl

  restrict-accessible : ∀ a → Acc Ambient._∈ᵗ_ (project a) → Acc Inner._∈ᵗ_ a
  restrict-accessible a (acc below) = acc λ b member →
    restrict-accessible b (below (project b) member)

  externalWF : WellFounded Inner._∈ᵗ_
  externalWF a = restrict-accessible a (regularityV (project a))

  bounded-absolute : ∀ {n} {φ : Formula Carrier n} → Δ₀ φ
    → (δ : Absolute._^_ Carrier n)
    → Absolute._⊨ᵐ_ δ φ ≡ Absolute._⊨ᵛ_ (map project δ) φ
  bounded-absolute = Absolute.abs₀

  membership-absolute : ∀ {n} (t u : Term Carrier n)
    (δ : Absolute._^_ Carrier n)
    → Absolute._⊨ᵐ_ δ (FOL.Syntax._∈̇_ t u)
      ≡ Absolute._⊨ᵛ_ (map project δ) (FOL.Syntax._∈̇_ t u)
  membership-absolute t u = bounded-absolute (δ-∈ {t = t} {u = u})

module Constructible (lem : LEM (ℓ-suc ℓ)) where

  module Adapter = Restriction isL isL-trans
  module LStructure = hPropStructure 𝒮ʟ

  structure-is-L : Adapter.structure ≡ 𝒮ʟ
  structure-is-L = refl

  externalWF : WellFounded LStructure._∈ᵗ_
  externalWF = Adapter.externalWF

  ordered-pair-code : ∀ x b →
    CoordinateDecoder.WithLEM.Names.orderedPairName lem x b ≡ prʟ x b
  ordered-pair-code = CoordinateDecoder.WithLEM.orderedPairName-bridge lem

  pair-projection = prʟ-fst
  pair-injective = prʟ-inj
  numeral-projection = numeralL-fst
  numeral-injective = numeralL-inj

  empty : LStructure.S
  empty = ∅ʟ

  empty-membership : ∀ x → (x LStructure.∈ˢ empty) ≡ ⊥
  empty-membership = hasEmptyL .fst .snd
```

### NonseparativeCompletion.agda

SHA-256: `61a8c840abf196861a5fdfcd95daff33143232bd98ec78e1e26dca0d52fd4975`.

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

### GroundCodes.agda

SHA-256: `753967e19087a0ffd9906a982a9766e989bd5d1c99800fa864afbce8130dec67`.

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

### FiniteCompletionInL.agda

SHA-256: `2b030d110d5b9705c6d6771a5d1e226de9c24267f13e018eaa7123233799b43f`.

```text
{-# OPTIONS --cubical --safe --guardedness #-}

open import Base.Prelude
  using ( Level; ℓ-suc; ℕ; zero; suc; Fin; _≡_; refl; sym; _∙_; cong; cong₂
        ; subst; Σ; Σ-syntax; _,_; fst; snd; ⟨_⟩ )
open import Base.Classical using ( LEM )
open import Cubical.Data.Sigma using ( _×_ )
open import Cubical.Data.Empty using ( ⊥ )
open import Cubical.Functions.Logic using ( ⇔toPath )
open import Cubical.HITs.PropositionalTruncation using ( ∥_∥₁; ∣_∣₁ )
import Cubical.HITs.PropositionalTruncation as PT
open import FOL.ZFStructure using ( ↾-reflects; module hPropStructure )
open import L.Constructible using ( 𝒮ʟ; isL )
open import V.Hierarchy using ( 𝒮ᵥ )
open import L.Axioms.Numerals using ( numeralL )
open import L.Coding.Model using ( numeralL-inj; prʟ; prʟ-inj )
open import MaterialNameL using ( ground )
open import NonseparativeCompletion
  using ( Boolean; zero; left; right; one; Nonzero; Condition; top; left₀; left₁
        ; right₀; embed; _≤ᴮ_; _≤ᴾ_; dense; left-duplicates; left-distinct )
open import GroundCodes
  using ( conditionTag; decodeTag; decode-conditionTag; OrderEdge; top-top
        ; left₀-left₀; left₀-left₁; left₀-top; left₁-left₀; left₁-left₁
        ; left₁-top; right₀-right₀; right₀-top; stronger; weaker
        ; edge-sound; edge-complete )
open import FiniteGroundImage

module FiniteCompletionInL {ℓ : Level} (lem : LEM (ℓ-suc ℓ)) where

open hPropStructure (𝒮ʟ {ℓ}) using ( S; _∈ˢ_; _≈ˢ_; isSetS )

module Images = FiniteGroundImage (𝒮ʟ {ℓ})
module Finite = Images.Construction (ground {ℓ} lem)
  (λ p → ↾-reflects {𝒮 = 𝒮ᵥ {ℓ}} {M = isL} p) (λ _ → refl)

conditionAt : Fin 4 → Condition
conditionAt zero = top
conditionAt (suc zero) = left₀
conditionAt (suc (suc zero)) = left₁
conditionAt (suc (suc (suc zero))) = right₀

conditionIndex : Condition → Fin 4
conditionIndex top = zero
conditionIndex left₀ = suc zero
conditionIndex left₁ = suc (suc zero)
conditionIndex right₀ = suc (suc (suc zero))

condition-cover : (p : Condition) → conditionAt (conditionIndex p) ≡ p
condition-cover top = refl
condition-cover left₀ = refl
condition-cover left₁ = refl
condition-cover right₀ = refl

booleanAt : Fin 4 → Boolean
booleanAt zero = zero
booleanAt (suc zero) = left
booleanAt (suc (suc zero)) = right
booleanAt (suc (suc (suc zero))) = one

booleanIndex : Boolean → Fin 4
booleanIndex zero = zero
booleanIndex left = suc zero
booleanIndex right = suc (suc zero)
booleanIndex one = suc (suc (suc zero))

boolean-cover : (b : Boolean) → booleanAt (booleanIndex b) ≡ b
boolean-cover zero = refl
boolean-cover left = refl
boolean-cover right = refl
boolean-cover one = refl

edgeAt : Fin 9 → OrderEdge
edgeAt zero = top-top
edgeAt (suc zero) = left₀-left₀
edgeAt (suc (suc zero)) = left₀-left₁
edgeAt (suc (suc (suc zero))) = left₀-top
edgeAt (suc (suc (suc (suc zero)))) = left₁-left₀
edgeAt (suc (suc (suc (suc (suc zero))))) = left₁-left₁
edgeAt (suc (suc (suc (suc (suc (suc zero)))))) = left₁-top
edgeAt (suc (suc (suc (suc (suc (suc (suc zero))))))) = right₀-right₀
edgeAt (suc (suc (suc (suc (suc (suc (suc (suc zero)))))))) = right₀-top

edgeIndex : OrderEdge → Fin 9
edgeIndex top-top = zero
edgeIndex left₀-left₀ = suc zero
edgeIndex left₀-left₁ = suc (suc zero)
edgeIndex left₀-top = suc (suc (suc zero))
edgeIndex left₁-left₀ = suc (suc (suc (suc zero)))
edgeIndex left₁-left₁ = suc (suc (suc (suc (suc zero))))
edgeIndex left₁-top = suc (suc (suc (suc (suc (suc zero)))))
edgeIndex right₀-right₀ = suc (suc (suc (suc (suc (suc (suc zero))))))
edgeIndex right₀-top = suc (suc (suc (suc (suc (suc (suc (suc zero)))))))

edge-cover : (e : OrderEdge) → edgeAt (edgeIndex e) ≡ e
edge-cover top-top = refl
edge-cover left₀-left₀ = refl
edge-cover left₀-left₁ = refl
edge-cover left₀-top = refl
edge-cover left₁-left₀ = refl
edge-cover left₁-left₁ = refl
edge-cover left₁-top = refl
edge-cover right₀-right₀ = refl
edge-cover right₀-top = refl

conditionCodeL : Condition → S
conditionCodeL p = numeralL (conditionTag p)

conditionCodeL-inj : ∀ {p q} → conditionCodeL p ≡ conditionCodeL q → p ≡ q
conditionCodeL-inj {p} {q} eq =
  sym (decode-conditionTag p) ∙
  cong decodeTag (numeralL-inj eq) ∙ decode-conditionTag q

booleanTag : Boolean → ℕ
booleanTag zero = zero
booleanTag left = suc zero
booleanTag right = suc (suc zero)
booleanTag one = suc (suc (suc zero))

booleanCodeL : Boolean → S
booleanCodeL b = numeralL (booleanTag b)

edgeCodeL : OrderEdge → S
edgeCodeL e = prʟ (conditionCodeL (stronger e)) (conditionCodeL (weaker e))

mapCodeL : Condition → S
mapCodeL p = prʟ (conditionCodeL p) (booleanCodeL (embed p))

carrier booleanCarrier orderGraph mapGraph : S
carrier = Finite.image (λ i → conditionCodeL (conditionAt i))
booleanCarrier = Finite.image (λ i → booleanCodeL (booleanAt i))
orderGraph = Finite.image (λ i → edgeCodeL (edgeAt i))
mapGraph = Finite.image (λ i → mapCodeL (conditionAt i))

condition-in : (p : Condition) → ⟨ conditionCodeL p ∈ˢ carrier ⟩
condition-in p = subst (λ z → ⟨ z ∈ˢ carrier ⟩) (cong conditionCodeL (condition-cover p))
  (Finite.image-entry (λ i → conditionCodeL (conditionAt i)) (conditionIndex p))

boolean-in : (b : Boolean) → ⟨ booleanCodeL b ∈ˢ booleanCarrier ⟩
boolean-in b = subst (λ z → ⟨ z ∈ˢ booleanCarrier ⟩) (cong booleanCodeL (boolean-cover b))
  (Finite.image-entry (λ i → booleanCodeL (booleanAt i)) (booleanIndex b))

map-in : (p : Condition) → ⟨ mapCodeL p ∈ˢ mapGraph ⟩
map-in p = subst (λ z → ⟨ z ∈ˢ mapGraph ⟩) (cong mapCodeL (condition-cover p))
  (Finite.image-entry (λ i → mapCodeL (conditionAt i)) (conditionIndex p))

carrier-out : ∀ z → ⟨ z ∈ˢ carrier ⟩ → ∥ Σ[ p ∈ Condition ] z ≡ conditionCodeL p ∥₁
carrier-out z member = PT.map (λ { (i , eq) → conditionAt i , eq })
  (Finite.image-out (λ i → conditionCodeL (conditionAt i)) z member)

map-out : ∀ z → ⟨ z ∈ˢ mapGraph ⟩ → ∥ Σ[ p ∈ Condition ] z ≡ mapCodeL p ∥₁
map-out z member = PT.map (λ { (i , eq) → conditionAt i , eq })
  (Finite.image-out (λ i → mapCodeL (conditionAt i)) z member)

carrier-reading : ∀ z → (z ∈ˢ carrier) ≡
  (∥ Σ[ p ∈ Condition ] z ≡ conditionCodeL p ∥₁ , PT.squash₁)
carrier-reading z = ⇔toPath (carrier-out z) (PT.rec (snd (z ∈ˢ carrier))
  (λ { (p , eq) → subst (λ v → ⟨ v ∈ˢ carrier ⟩) (sym eq) (condition-in p) }))

boolean-out : ∀ z → ⟨ z ∈ˢ booleanCarrier ⟩
  → ∥ Σ[ b ∈ Boolean ] z ≡ booleanCodeL b ∥₁
boolean-out z member = PT.map (λ { (i , eq) → booleanAt i , eq })
  (Finite.image-out (λ i → booleanCodeL (booleanAt i)) z member)

boolean-reading : ∀ z → (z ∈ˢ booleanCarrier) ≡
  (∥ Σ[ b ∈ Boolean ] z ≡ booleanCodeL b ∥₁ , PT.squash₁)
boolean-reading z = ⇔toPath (boolean-out z) (PT.rec (snd (z ∈ˢ booleanCarrier))
  (λ { (b , eq) → subst (λ v → ⟨ v ∈ˢ booleanCarrier ⟩) (sym eq) (boolean-in b) }))

map-reading : ∀ z → (z ∈ˢ mapGraph) ≡
  (∥ Σ[ p ∈ Condition ] z ≡ mapCodeL p ∥₁ , PT.squash₁)
map-reading z = ⇔toPath (map-out z) (PT.rec (snd (z ∈ˢ mapGraph))
  (λ { (p , eq) → subst (λ v → ⟨ v ∈ˢ mapGraph ⟩) (sym eq) (map-in p) }))

material-order-sound : (p q : Condition)
  → ⟨ prʟ (conditionCodeL p) (conditionCodeL q) ∈ˢ orderGraph ⟩
  → ∥ p ≤ᴾ q ∥₁
material-order-sound p q member = PT.map read
  (Finite.image-out (λ i → edgeCodeL (edgeAt i)) _ member)
  where
  read : Σ[ i ∈ Fin 9 ] prʟ (conditionCodeL p) (conditionCodeL q) ≡ edgeCodeL (edgeAt i)
    → p ≤ᴾ q
  read (i , eq) = subst (λ a → a ≤ᴾ q) (sym (conditionCodeL-inj (fst (prʟ-inj eq))))
    (subst (λ b → stronger (edgeAt i) ≤ᴾ b)
      (sym (conditionCodeL-inj (snd (prʟ-inj eq)))) (edge-sound (edgeAt i)))

material-order-complete : (p q : Condition) → p ≤ᴾ q
  → ⟨ prʟ (conditionCodeL p) (conditionCodeL q) ∈ˢ orderGraph ⟩
material-order-complete p q p≤q with edge-complete p q p≤q
... | e , se , we = subst (λ z → ⟨ z ∈ˢ orderGraph ⟩)
  (cong₂ prʟ (cong conditionCodeL se) (cong conditionCodeL we))
  (subst (λ z → ⟨ edgeCodeL z ∈ˢ orderGraph ⟩) (edge-cover e)
    (Finite.image-entry (λ i → edgeCodeL (edgeAt i)) (edgeIndex e)))

map-output-unique : ∀ p b c
  → ⟨ prʟ (conditionCodeL p) b ∈ˢ mapGraph ⟩
  → ⟨ prʟ (conditionCodeL p) c ∈ˢ mapGraph ⟩ → b ≡ c
map-output-unique p b c pb pc = PT.rec (isSetS b c)
  (λ { (q , eq) → PT.rec (isSetS b c)
    (λ { (r , eq') →
      snd (prʟ-inj eq) ∙
      cong (λ x → booleanCodeL (embed x))
        (conditionCodeL-inj (sym (fst (prʟ-inj eq)) ∙ fst (prʟ-inj eq'))) ∙
      sym (snd (prʟ-inj eq')) }) (map-out _ pc) }) (map-out _ pb)

coded-dense : (b : Boolean) → Nonzero b
  → Σ[ p ∈ Condition ]
      (⟨ conditionCodeL p ∈ˢ carrier ⟩ ×
       (⟨ mapCodeL p ∈ˢ mapGraph ⟩ ×
        (⟨ booleanCodeL (embed p) ∈ˢ booleanCarrier ⟩ × (embed p ≤ᴮ b))))
coded-dense b b+ with dense b b+
... | p , p≤b = p , condition-in p , map-in p , boolean-in (embed p) , p≤b

map-identifies-left : booleanCodeL (embed left₀) ≡ booleanCodeL (embed left₁)
map-identifies-left = cong booleanCodeL left-duplicates

source-left-distinct : conditionCodeL left₀ ≡ conditionCodeL left₁ → ⊥
source-left-distinct eq = left-distinct (conditionCodeL-inj eq)
```
