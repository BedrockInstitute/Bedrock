# K0 actual powerset weighted joins

Date: 2026-09-09. Source baseline: `995598f8`. Four safe temporary probes checked. This follows [uniform internal weighted images](k0-uniform-internal-images-2026-09.md). K0 remains open.

## Concrete internal operations and relative suprema

`InternalPowersetSupremum.For X` takes any actual L set X and constructs B = P(X) with actual internal subset order. Its variable-indexed order formula has an arbitrary-environment reading theorem. For every actual internal set A with A ⊆ B, the actual set union(A) is proved to belong to B, bound all elements of A, and lie below every competing upper bound in B. This is the complete relative-supremum specification from `IndexedSupremum`, not a presumed completeness field.

The proof covers empty A without a nonemptiness premise. It only eliminates the merely existing contributing member of a union into a membership proposition. The input is an actual internal family A with its bound; this does not assert completeness for arbitrary host-indexed families or collect host functions into L.

`InternalIntersection` constructs c ∩ d by L Separation and proves exact membership. Its finite `meetAt c d z` formula describes z = c ∩ d at arbitrary environments. It also proves closure in internal powersets. These are actual model operations under exactly `LEM (ℓ-suc ℓ)`; no host choice principle is used.

## Composed image/supremum formula

`WeightedImageSupremum` is independent of the powerset example. It composes the already checked key/operation image template with an arbitrary supplied order formula and its reading theorem:

    resultAt(C,B,parent,H,f,b) says:
      there is an internal A whose image-set description holds,
      and b is the B-relative supremum of A.

`Reading.exact` proves this formula means precisely that b is a relative supremum of the actual image constructed by `UniformWeightedImage`. The soundness proof identifies the quantified A with that actual image by extensionality, then transports the supremum specification. The converse inserts the actual image. The existential over A is object-language syntax, not a host selection operation. Truncation is eliminated only into the propositional supremum specification.

This theorem alone does not construct a supremum for an arbitrary supplied order. It isolates finite syntax composition from the independent existence obligation.

## Actual weighted values in both orientations

`PowersetWeightedSupremum.For X` instantiates the composition with actual intersection and subset order. For arbitrary actual C, parent, H and fixed coordinate f, it constructs the image I ⊆ B and returns union(I), proves that value belongs to B, proves the full relative-supremum specification, and proves satisfaction of the composed finite formula. No caller-supplied operation, supremum, selector or recursive atomic table is required by this concrete instance.

One shared construction has these two interfaces:

| Interface | Enumerated entry | Key used in H | Image value |
| --- | --- | --- | --- |
| Forward, fixed u | pair(v,c) in y | pair(u,v) | c ∩ d |
| Reverse, fixed v | pair(u,a) in x | pair(u,v) | a ∩ d |

The image's B-membership guard cannot silently discard genuine operation results: `meet-bounded` proves c ∩ d ∈ B whenever c ∈ B, and `entry-value-in-image` inserts the result for every relevant original weighted entry and table value. The proof bridges the separate opaque ground instances through exact membership and the powerset specification, without assuming their operations are definitionally identical.

`Congruence.value-equal` transports actual image equality through internal union. Thus relevant graph agreement yields equal actual weighted suprema in both orientations. It reuses the common image congruence proof; it does not repeat a supremum uniqueness or choice proof.

## Scope and production direction

This is an actual internally relatively complete powerset-order instance with meet, not merely the earlier finite carrier example. It validates that the image and supremum contracts can be realized under the existing LEM budget. It does not yet package all Boolean laws, complement, implication or infima. It is not the Cohen algebra, a regular-open completion compiler or a proof of the full atomic Step. General regular-open completion remains a separate construction obligation; the powerset example cannot replace it.

The production proof homes remain: generic syntax operations, indexed image/supremum formulas, internal image realization, and independent concrete algebra instances. Avoid baking the union implementation into the generic semantic interface. In particular, the concrete congruence proof through union is specific to this example; general instances must use their own proved supremum contract. The current repeated opaque L adapters are temporary isolation boundaries, not a decision to duplicate the production ground adapter.

Next work is to supply implication and infimum operations with their finite readings, compose the outer weighted images, and prove actual Step admissibility, uniqueness and locality. Full Boolean instance validation, general RO-in-ground construction, domain independence and atomic adequacy remain open. The general forcing route and the T3 ordinary non-CH model / T4 ground-definability targets are unchanged.

## Verification and source snapshots

In `/tmp/bedrock-k0-probes/extraction/compile-root`, each command exited 0:

```sh
GHCRTS="-A64m -I0 -M8g" agda src/InternalPowersetSupremum.agda
GHCRTS="-A64m -I0 -M8g" agda src/InternalIntersection.agda
GHCRTS="-A64m -I0 -M8g" agda src/WeightedImageSupremum.agda
GHCRTS="-A64m -I0 -M8g" agda src/PowersetWeightedSupremum.agda
```

All four retain `--safe`; no production source changed. Scoped prose/glossary gates, snapshot/hash checks, local-link checks and `git diff --check` passed. All 123 tracked source files and their copied probe-baseline versions match the baseline byte-for-byte. Whole-tree and chapter gates were not run for this temporary-probe/documentation change.

### InternalPowersetSupremum.agda

SHA-256: `00dcea6d4277df4c9f1a87250db52db92c955ce97f5193c506cd4f2e36b583bd`.

```text
{-# OPTIONS --cubical --safe --guardedness #-}

open import Base.Prelude
open import Base.Truth
open import Base.Classical using ( LEM )

module InternalPowersetSupremum {ℓ : Level} (lem : LEM (ℓ-suc ℓ)) where

open import FOL.ZFStructure using ( module hPropStructure )
open import FOL.Syntax using ( Formula; var; _∈̇_; ∀̇∈ )
open import L.Constructible {ℓ} using ( 𝒮ʟ )
open import FOL.Semantics (hPropAlgebra (ℓ-suc ℓ)) 𝒮ʟ using ( module At )
import FOL.ZFModel as Model
open import L.Model {ℓ} lem using ( L⊨ZF )
import IndexedSupremum {ℓ} as Indexed
import Cubical.HITs.PropositionalTruncation as PT
open PT using ( ∣_∣₁ )

open TruthAlgebra (hPropAlgebra (ℓ-suc ℓ))
open hPropStructure 𝒮ʟ using ( S; _∈ˢ_ )
open At S id using ( _⊨_ )

opaque
  actualL : Model.isZFModel 𝒮ʟ
  actualL = L⊨ZF

module Ground = Model.isZFModel actualL

module For (X : S) where

  B : S
  B = Ground.𝒫 X

  Order : S → S → hProp (ℓ-suc ℓ)
  Order A C = Model._⊆ˢ_ 𝒮ʟ A C

  orderAt : ∀ {n} → Fin n → Fin n → Formula S n
  orderAt A C = ∀̇∈ (var A) (var zero ∈̇ var (suc C))

  order-reading : ∀ {n} (A C : Fin n) (γ : Vec S n)
    → (γ ⊨ orderAt A C) ≡ Order (lookup A γ) (lookup C γ)
  order-reading A C γ = refl

  module Supremum = Indexed.WithOrder Order orderAt order-reading

  supremum : (A : S) → ((a : S) → ⟨ a ∈ˢ A ⟩ → ⟨ a ∈ˢ B ⟩) → S
  supremum A bounded = Ground.⋃ A

  supremum-correct : (A : S)
    → (bounded : (a : S) → ⟨ a ∈ˢ A ⟩ → ⟨ a ∈ˢ B ⟩)
    → Supremum.Supremum B A (supremum A bounded)
  supremum-correct A bounded = in-B , upper , least
    where
    union-spec = Model.℩-spec 𝒮ʟ (Ground.hasUnion A)
    power-spec = Model.℩-spec 𝒮ʟ (Ground.hasPower X)

    upper : Supremum.Upper A (Ground.⋃ A)
    upper a aA x xa = subst ⟨_⟩ (sym (union-spec x)) ∣ a , aA , xa ∣₁

    union-subset : (x : S) → ⟨ x ∈ˢ Ground.⋃ A ⟩ → ⟨ x ∈ˢ X ⟩
    union-subset x member = PT.rec (snd (x ∈ˢ X))
      (λ { (a , (aA , xa)) →
        subst ⟨_⟩ (power-spec a) (bounded a aA) x xa })
      (subst ⟨_⟩ (union-spec x) member)

    in-B : ⟨ Ground.⋃ A ∈ˢ B ⟩
    in-B = subst ⟨_⟩ (sym (power-spec (Ground.⋃ A))) union-subset

    least : (C : S) → ⟨ C ∈ˢ B ⟩ → Supremum.Upper A C
      → ⟨ Order (Ground.⋃ A) C ⟩
    least C C-in-B is-upper x member = PT.rec (snd (x ∈ˢ C))
      (λ { (a , (aA , xa)) → is-upper a aA x xa })
      (subst ⟨_⟩ (union-spec x) member)
```

### InternalIntersection.agda

SHA-256: `c124d01797700cfea52eea602b5e4ee5ea039484cdf13e16e65c2ba56e100a4e`.

```text
{-# OPTIONS --cubical --safe --guardedness #-}

open import Base.Prelude
open import Base.Truth
open import Base.Classical using ( LEM )

module InternalIntersection {ℓ : Level} (lem : LEM (ℓ-suc ℓ)) where

open import FOL.ZFStructure using ( module hPropStructure )
open import FOL.Syntax using
  ( Formula; var; _∈̇_; _∧̇_; _⇒̇_; ∀̇_ )
open import L.Constructible {ℓ} using ( 𝒮ʟ )
open import FOL.Semantics (hPropAlgebra (ℓ-suc ℓ)) 𝒮ʟ using ( module At )
import FOL.ZFModel as Model
open import L.Model {ℓ} lem using ( L⊨ZF )
open import Cubical.Functions.Logic using ( ⇔toPath )

open TruthAlgebra (hPropAlgebra (ℓ-suc ℓ))
open hPropStructure 𝒮ʟ using ( S; _∈ˢ_; isSetS )
open At S id using ( _⊨_ )

opaque
  actualL : Model.isZFModel 𝒮ʟ
  actualL = L⊨ZF

module Ground = Model.isZFModel actualL

intersection : S → S → S
intersection c d = Ground.separate c (var zero ∈̇ FOL.Syntax.con d)

intersection-membership : ∀ z c d
  → (z ∈ˢ intersection c d) ≡ ((z ∈ˢ c) ⊓ (z ∈ˢ d))
intersection-membership z c d = Ground.separate-spec c
  (var zero ∈̇ FOL.Syntax.con d) z

intersection-out : ∀ z c d → ⟨ z ∈ˢ intersection c d ⟩
  → ⟨ z ∈ˢ c ⟩ × ⟨ z ∈ˢ d ⟩
intersection-out z c d member = subst ⟨_⟩
  (intersection-membership z c d) member

intersection-in : ∀ z c d → ⟨ z ∈ˢ c ⟩ → ⟨ z ∈ˢ d ⟩
  → ⟨ z ∈ˢ intersection c d ⟩
intersection-in z c d zc zd = subst ⟨_⟩
  (sym (intersection-membership z c d)) (zc , zd)

Op : S → S → S → hProp (ℓ-suc ℓ)
Op c d z = (z ≡ intersection c d) , isSetS z (intersection c d)

meetAt : ∀ {n} → Fin n → Fin n → Fin n → Formula S n
meetAt c d z = ∀̇
  (((var zero ∈̇ var (suc z)) ⇒̇
      ((var zero ∈̇ var (suc c)) ∧̇ (var zero ∈̇ var (suc d)))) ∧̇
   (((var zero ∈̇ var (suc c)) ∧̇ (var zero ∈̇ var (suc d))) ⇒̇
      (var zero ∈̇ var (suc z))))

meet-reading : ∀ {n} (c d z : Fin n) (γ : Vec S n)
  → (γ ⊨ meetAt c d z)
    ≡ Op (lookup c γ) (lookup d γ) (lookup z γ)
meet-reading c d z γ = ⇔toPath out into
  where
  out : ⟨ γ ⊨ meetAt c d z ⟩
    → lookup z γ ≡ intersection (lookup c γ) (lookup d γ)
  out holds = Ground.extensional λ w → ⇔toPath
    (λ member → intersection-in w (lookup c γ) (lookup d γ)
      (fst (fst (holds w) member)) (snd (fst (holds w) member)))
    (λ member → snd (holds w)
      (fst (intersection-out w (lookup c γ) (lookup d γ) member) ,
       snd (intersection-out w (lookup c γ) (lookup d γ) member)))

  into : lookup z γ ≡ intersection (lookup c γ) (lookup d γ)
    → ⟨ γ ⊨ meetAt c d z ⟩
  into eq w =
    (λ member → intersection-out w (lookup c γ) (lookup d γ)
      (subst (λ a → ⟨ w ∈ˢ a ⟩) eq member)) ,
    (λ { (wc , wd) → subst (λ a → ⟨ w ∈ˢ a ⟩) (sym eq)
      (intersection-in w (lookup c γ) (lookup d γ) wc wd) })

intersection-in-power : ∀ X c d → ⟨ c ∈ˢ Ground.𝒫 X ⟩
  → ⟨ d ∈ˢ Ground.𝒫 X ⟩ → ⟨ intersection c d ∈ˢ Ground.𝒫 X ⟩
intersection-in-power X c d cX dX = subst ⟨_⟩
  (sym (Model.℩-spec 𝒮ʟ (Ground.hasPower X) (intersection c d))) subset
  where
  c-subset : ⟨ Model._⊆ˢ_ 𝒮ʟ c X ⟩
  c-subset = subst ⟨_⟩ (Model.℩-spec 𝒮ʟ (Ground.hasPower X) c) cX

  subset : ⟨ Model._⊆ˢ_ 𝒮ʟ (intersection c d) X ⟩
  subset z member = c-subset z (fst (intersection-out z c d member))
```

### WeightedImageSupremum.agda

SHA-256: `e14bbd3f6c51c72954ab6b456970494e4b2a6c8956117102010374e4e6a9680b`.

```text
{-# OPTIONS --cubical --safe --guardedness #-}

open import Base.Prelude
open import Base.Truth
open import Base.Classical using ( LEM )

module WeightedImageSupremum {ℓ : Level} (lem : LEM (ℓ-suc ℓ)) where

open import FOL.ZFStructure using ( module hPropStructure )
open import FOL.Syntax using ( Formula; _∧̇_; ∃̇_ )
open import L.Constructible {ℓ} using ( 𝒮ʟ )
open import FOL.Semantics (hPropAlgebra (ℓ-suc ℓ)) 𝒮ʟ using ( module At )
import UniformWeightedImage {ℓ} lem as Images
import IndexedSupremum {ℓ} as Suprema
open import Cubical.Functions.Logic using ( ⇔toPath )
import Cubical.HITs.PropositionalTruncation as PT
open PT using ( ∣_∣₁ )

open hPropStructure 𝒮ʟ using ( S; _∈ˢ_; isSetS )
open At S id using ( _⊨_ )

module WithKey
  (Key : S → S → S)
  (keyAt : ∀ {n} → Fin n → Fin n → Fin n → Formula S n)
  (key-reading : ∀ {n} (q f v : Fin n) (γ : Vec S n)
    → (γ ⊨ keyAt q f v) ≡ ((lookup q γ ≡ Key (lookup f γ) (lookup v γ)) ,
      isSetS (lookup q γ) (Key (lookup f γ) (lookup v γ)))) where

  module WithOperation
    (Op : S → S → S → hProp (ℓ-suc ℓ))
    (opAt : ∀ {n} → Fin n → Fin n → Fin n → Formula S n)
    (op-reading : ∀ {n} (c d z : Fin n) (γ : Vec S n)
      → (γ ⊨ opAt c d z) ≡ Op (lookup c γ) (lookup d γ) (lookup z γ)) where

    module Image = Images.WithKey.WithOperation Key keyAt key-reading Op opAt op-reading

    module WithOrder
      (Order : S → S → hProp (ℓ-suc ℓ))
      (orderAt : ∀ {n} → Fin n → Fin n → Formula S n)
      (order-reading : ∀ {n} (a b : Fin n) (γ : Vec S n)
        → (γ ⊨ orderAt a b) ≡ Order (lookup a γ) (lookup b γ)) where

      module Sup = Suprema.WithOrder Order orderAt order-reading

      resultAt : ∀ {n} → Fin n → Fin n → Fin n → Fin n → Fin n → Fin n → Formula S n
      resultAt C B parent H f b = ∃̇
        (Image.imageSetAt zero (suc C) (suc B) (suc parent) (suc H) (suc f)
        ∧̇ Sup.supremumAt (suc B) zero (suc b))

      module Reading {n : ℕ} (C B parent H f b : Fin n) (γ : Vec S n) where

        module Actual = Image.Construction (lookup C γ) (lookup B γ) (lookup parent γ)
          (lookup H γ) (lookup f γ)

        Specification : Type (ℓ-suc ℓ)
        Specification = Sup.Supremum (lookup B γ) Actual.image (lookup b γ)

        out : ⟨ γ ⊨ resultAt C B parent H f b ⟩ → Specification
        out = PT.rec (Sup.supremum-is-prop (lookup B γ) Actual.image (lookup b γ))
          λ { (A , description , upper) →
            subst (λ I → Sup.Supremum (lookup B γ) I (lookup b γ))
              (Image.Description.out zero (suc C) (suc B) (suc parent) (suc H) (suc f)
                (A ∷ γ) description)
              (Sup.supremum-out (suc B) zero (suc b) (A ∷ γ) upper) }

        into : Specification → ⟨ γ ⊨ resultAt C B parent H f b ⟩
        into correct = ∣ Actual.image ,
          Image.Description.into zero (suc C) (suc B) (suc parent) (suc H) (suc f)
            (Actual.image ∷ γ) refl ,
          Sup.supremum-in (suc B) zero (suc b) (Actual.image ∷ γ) correct ∣₁

        exact : (γ ⊨ resultAt C B parent H f b)
          ≡ (Specification , Sup.supremum-is-prop (lookup B γ) Actual.image (lookup b γ))
        exact = ⇔toPath out into
```

### PowersetWeightedSupremum.agda

SHA-256: `61080ffffda357be60e81bb6d6c94be6457b3d4783e0829bd1776db57ebb9e4c`.

```text
{-# OPTIONS --cubical --safe --guardedness #-}

open import Base.Prelude
open import Base.Truth
open import Base.Classical using ( LEM )

module PowersetWeightedSupremum {ℓ : Level} (lem : LEM (ℓ-suc ℓ)) where

open import FOL.ZFStructure using ( module hPropStructure )
open import FOL.Syntax using ( Formula )
open import L.Constructible {ℓ} using ( 𝒮ʟ )
open import FOL.Semantics (hPropAlgebra (ℓ-suc ℓ)) 𝒮ʟ using ( module At )
open import L.Coding.Model {ℓ} using ( prʟ; prAtL )
open import PairFormulaReading {ℓ} using ( reading )
import IndexedWeightedImage {ℓ} as Keys
import InternalPowersetSupremum {ℓ} lem as Powersets
import InternalIntersection {ℓ} lem as Intersections
import WeightedImageSupremum {ℓ} lem as Weighted
import FOL.ZFModel as Model
import Cubical.HITs.PropositionalTruncation as PT
open PT using ( ∣_∣₁ )

open hPropStructure 𝒮ʟ using ( S; _∈ˢ_; isSetS )
open At S id using ( _⊨_ )

module For (X : S) where

  module Algebra = Powersets.For X
  open Algebra using ( B )

  meet-bounded : ∀ c d → ⟨ c ∈ˢ B ⟩ → ⟨ Intersections.intersection c d ∈ˢ B ⟩
  meet-bounded c d cB = subst ⟨_⟩
    (sym (Model.℩-spec 𝒮ʟ (Powersets.Ground.hasPower X) (Intersections.intersection c d)))
    (λ z member → subst ⟨_⟩ (Model.℩-spec 𝒮ʟ (Powersets.Ground.hasPower X) c) cB z
      (fst (Intersections.intersection-out z c d member)))

  module WithKey
    (Key : S → S → S)
    (keyAt : ∀ {n} → Fin n → Fin n → Fin n → Formula S n)
    (key-reading : ∀ {n} (q f v : Fin n) (γ : Vec S n)
      → (γ ⊨ keyAt q f v) ≡ ((lookup q γ ≡ Key (lookup f γ) (lookup v γ)) ,
        isSetS (lookup q γ) (Key (lookup f γ) (lookup v γ)))) where

    module Operations = Weighted.WithKey.WithOperation Key keyAt key-reading
      Intersections.Op Intersections.meetAt Intersections.meet-reading
    module Result = Operations.WithOrder Algebra.Order Algebra.orderAt Algebra.order-reading

    module Construction (C parent H f : S) where

      module Image = Operations.Image.Construction C B parent H f

      bounded : ∀ z → ⟨ z ∈ˢ Image.image ⟩ → ⟨ z ∈ˢ B ⟩
      bounded z member = fst (Image.image-out z member)

      value : S
      value = Algebra.supremum Image.image bounded

      correct : Algebra.Supremum.Supremum B Image.image value
      correct = Algebra.supremum-correct Image.image bounded

      value-in-B : ⟨ value ∈ˢ B ⟩
      value-in-B = fst correct

      satisfies : ⟨ (C ∷ B ∷ parent ∷ H ∷ f ∷ value ∷ []) ⊨
        Result.resultAt zero (suc zero) (suc (suc zero)) (suc (suc (suc zero)))
          (suc (suc (suc (suc zero)))) (suc (suc (suc (suc (suc zero))))) ⟩
      satisfies = Result.Reading.into zero (suc zero) (suc (suc zero))
        (suc (suc (suc zero))) (suc (suc (suc (suc zero))))
        (suc (suc (suc (suc (suc zero)))))
        (C ∷ B ∷ parent ∷ H ∷ f ∷ value ∷ []) correct

      entry-value-in-image : ∀ v c d → ⟨ v ∈ˢ C ⟩ → ⟨ c ∈ˢ B ⟩ → ⟨ d ∈ˢ B ⟩
        → ⟨ prʟ v c ∈ˢ parent ⟩ → ⟨ prʟ (Key f v) d ∈ˢ H ⟩
        → ⟨ Intersections.intersection c d ∈ˢ Image.image ⟩
      entry-value-in-image v c d vC cB dB entry graph =
        Image.image-in (Intersections.intersection c d) (meet-bounded c d cB)
          ∣ v , c , d , vC , cB , dB , entry , graph , refl ∣₁

    module Congruence (C parent H K f : S)
      (agrees : ∀ v c d → ⟨ v ∈ˢ C ⟩ → ⟨ c ∈ˢ B ⟩ → ⟨ d ∈ˢ B ⟩
        → ⟨ prʟ v c ∈ˢ parent ⟩
        → (⟨ prʟ (Key f v) d ∈ˢ H ⟩ → ⟨ prʟ (Key f v) d ∈ˢ K ⟩)
          × (⟨ prʟ (Key f v) d ∈ˢ K ⟩ → ⟨ prʟ (Key f v) d ∈ˢ H ⟩)) where

      module Left = Construction C parent H f
      module Right = Construction C parent K f
      module Images = Operations.Image.Congruence C B parent H K f agrees

      value-equal : Left.value ≡ Right.value
      value-equal = cong Powersets.Ground.⋃ Images.image-equal

  module Forward = WithKey prʟ prAtL reading
  module Reverse = WithKey (λ f v → prʟ v f) Keys.reverseKeyAt Keys.reverse-key-reading
```
