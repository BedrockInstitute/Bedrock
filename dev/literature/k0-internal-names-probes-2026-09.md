# K0 internal names, supports and closed families

Date: 2026-09-08. Repository source baseline: `7ab8da41`. Status: eight new safe probe modules checked. The L name-recognition and support branch now has actual internal constructions; K0 as a whole remains open. See the [previous material-name probes](k0-material-names-value-sets-2026-09.md), [Cohen roadmap](cohen-implementation-roadmap-2026-09.md), and [master architecture](forcing-geology-design-2026-09.md).

## 1. Checked outcome

For every weight-carrier code B in L, the existing successor-level LEM now suffices for the following checked statement, schematically:

```text
L satisfies NameFormula(B,t)  iff  IsName(B,t)
```

Here IsName is the previously checked host hereditary predicate on material L codes. NameFormula is an actual finite `Formula S 1`, with B as an L constant. It says:

```text
there exists C such that
  t belongs to C, and
  for every n in C and e in n,
    there exist x in C and b in B with e = Pair(x,b).
```

The backward direction constructs an actual C in L. It does not assume a closed-family witness or a recognition/definability certificate as an extra parameter. The theorem applies to all t in L, not just finite sample names. B need only be an L set for this coding theorem; Boolean laws are additional semantics inputs, not prerequisites of hereditary pair coding.

The same branch also constructs each name's support as an L set, proves its members are exactly the subnames, and decodes each internal entry into an actual name and an actual weight in B. These are ground-coded families with checked host presentations, not arbitrary host branch functions asserted to be internal.

## 2. Probe contracts

| Module | Checked result | Boundary |
|---|---|---|
| PairFormulaReading | Existing pair formula agrees with actual L pair equality at arbitrary variable positions/environments | Constructive; no LEM or Choice |
| NameSupport | Actual Replacement image for first coordinates of any internally paired set, with both membership directions | Takes merely represented entries; functionality is proved by unique coordinate extraction |
| NamedSupport | Discharges entry representation for the exact hereditary-name carrier; support membership iff Child; support members decode to Name | Actual L instance under the original LEM |
| NamedEntries | The internal entry index decodes to a Name and a weight in B, with pairing and descent certificates | Does not assert arbitrary externally supplied graphs are internal or produce Boolean values |
| NameRecognition | Fixed first-order recognition formula; soundness by external well-founded induction; formula satisfaction from a closed internal family | Initial soundness alone was insufficient; NameClosure supplies the missing family |
| NameClosureDown | Total one-step subname expansion on arbitrary L sets, with a triple-union bound and actual Separation | Does not test host IsName inside Separation |
| NameClosureStep | Total growing step, membership laws, a fixed global two-variable graph, and existence/uniqueness adequacy | Suitable actual input to the existing internal omega iterator |
| NameClosure | Actual internal closed family, finite-stage invariant, closure under Child, and full formula/host-predicate equivalence | Uses the proved L iterator, not an assumed generic iteration or choice operator |

Except for the constructive pair-reading helper, these packages instantiate already proved L facts under `LEM (ℓ-suc ℓ)`. No host Choice, countable/dependent choice, BPI, resizing, postulate, supplied ultrafilter or supplied generic is added. The actual Name carrier remains at `Type (ℓ-suc ℓ)`; no smallness of the whole L name class is inferred.

## 3. Support and entry decoding

`NameSupport` uses the fixed formula `there exists b, e = Pair(x,b)` in the output/input order required by `hasReplacement`. Pair injectivity proves the coordinate fiber has a unique result. The earlier coordinate decoder removes truncation only into that proved proposition, providing the contractible satisfying-output type required by the real Replacement field.

The result is an actual L element, with the exact specification:

```text
x belongs to support(n)
  iff merely some e in n and b satisfy e = Pair(x,b).
```

`NamedSupport` uses the host name-shape theorem and the proved bridge between the generic material pair and `prʟ` to discharge the represented-entry premise. It proves the support/Child equivalence and that every support member is again a valid name. `NamedEntries` supplies a second useful presentation: index by the members of n itself, decode each uniquely represented entry, prove its weight belongs to B, and retain the recursive-decrease certificate. Repeated first coordinates with different weights are allowed. There is no normalization to a functional weight map and no choice of one weight per subname.

This validates both useful internal indices: the support set and the entry set. It does not yet prove that an arbitrary family of recursively computed Boolean values has an internal image. That is precisely the pending atomic-table/value-graph obligation.

## 4. A noncircular internal recognizer

The forward implication uses the existing externally well-founded Child relation. A closed family supplies the shape of each member and contains every child; well-founded induction therefore proves hereditary validity. This consumes the strong ground profile, not an invalid inference from mere first-order Foundation in an arbitrary model.

For the converse, define on every L set A:

```text
down(A) = { x in union(union(union(A))) |
              some n in A contains a pair Pair(x,b) }
step(A) = A union down(A)
C = union of the finite step-iterates starting from {t}
```

The three-union bound follows from `x in {x} in Pair(x,b) in n in A`. `down-in` uses only three union introductions; `down-out` discards the bounding conjunction of Separation and reads the defining formula. No reconstruction of arbitrary ambient witnesses is needed.

The generalized `childAt` formula accepts a term for A and a variable position for x, so its adequacy works both in the one-step construction and under the binders of the global step graph. `stepFo` describes membership in the output by equivalence to membership in A or its one-step subnames. `defines` and `only` prove the precise inputs required by [OmegaRecursion.Iterate](../../src/L/GCH/OmegaRecursion.lagda.md). Although this existing module is in the GCH directory, it takes successor-level LEM and does not assume GCH. The probe reuses its proved internal `iterUnion`, `iterUnion-in` and `iterUnion-out`.

The step is total even on malformed codes. Host IsName occurs only in the EXTERNAL proof that every finite iterate consists of valid names when the seed does. It is not a predicate passed to Separation or assumed to have an internal graph. A child of an element at stage k appears at stage k+1, so the internal union is closed. The name-shape theorem then reconstructs the fixed recognition formula, completing both directions without circular definability.

This is actual deterministic, internally coded omega recursion. No host sequence is chosen from pointwise truncated existential steps. The construction does not require a separate general transitive-closure library first; that library may still be useful elsewhere.

Subsequent evidence: the [partial-table and image probes](k0-partial-atomic-tables-2026-09.md) check semantic partial-table union and images of supplied internal tables. They refine the atomic obligation below without closing recursive graph existence.

## 5. Architecture decisions and remaining K0 work

Retain material pair-code subtypes and their checked host entry/support presentations as the shared candidate for poset-weighted and Boolean-weighted names. The weight-carrier parameter is independent of Boolean laws. Reuse the same pair-reading, unique-coordinate and hereditary-recursion mathematics through proved ground adapters. The L implementation demonstrates the representation without licensing arbitrary host families in every ground.

The new recognition theorem closes a previously explicit L-side dependency of the fixed-formula compiler: the name guard has an actual first-order formula and a proved host correspondence. It does not define or internalize Boolean equality/membership. The next K0 work is a local atomic value-table interface: actual internal domains of relevant name pairs, admissible Boolean value images, table existence/uniqueness and agreement with the safe expanded atomic recursion. Only afterwards may the existing attained-value Separation backend consume the subformula graph. Do not substitute an assumed graph-definability field for that proof.

General transitive-ground adapters still require their own proved coordinate, support and internal recursion contracts. The L-specific package must not replace the required general forcing theorem. No claim is made here about the full Boolean compiler, generic truth, fullness, internal ultrafilter existence, Cohen or ground definability. K0 remains open at the general-ground/atomic internalization boundary.

The established opacity boundary around proved ground records remains necessary. These probes reuse that boundary and export specifications rather than normalizing the complete L proof in consumers. Existing source modules, landmarks, glossary and trilingual chapters are unchanged.

## 6. Verification and evidence

All eight final sources below were checked under `--cubical --safe --guardedness`. Commands use the required memory limit. Agent entry points ran in their own copied roots, while coordinator entry points ran in `/tmp/bedrock-k0-probes/extraction/compile-root`:

```text
GHCRTS="-A64m -I0 -M8g" agda src/NameSupport.agda
GHCRTS="-A64m -I0 -M8g" agda src/NameRecognition.agda
GHCRTS="-A64m -I0 -M8g" agda src/NamedSupport.agda
GHCRTS="-A64m -I0 -M8g" agda src/NamedEntries.agda
GHCRTS="-A64m -I0 -M8g" agda src/NameClosureDown.agda
GHCRTS="-A64m -I0 -M8g" agda src/NameClosureStep.agda
GHCRTS="-A64m -I0 -M8g" agda src/NameClosure.agda
```

Every listed final entry-point check exited 0. PairFormulaReading was checked as an imported dependency. The final NameClosure command checked the actual composition, including the copied down/step modules, and its log has no warnings. NamedSupport was rechecked after adding the formula-from-closed direction to NameRecognition. Existing copied baseline caches were reused; no repository source cache or whole-tree check was required for this temporary-code/document-only work. At most two Agda processes were permitted, with compiler slots coordinated explicitly.

The final step proof preserves nested truncations and transports through the formula adequacy theorem instead of assuming those expressions definitionally equal. Only the completed final sources are archived here. Temporary logs remain under `/tmp/bedrock-k0-probes/extraction`, and the read-only mathematical audit is `/tmp/bedrock-k0-probes/name-recursion-audit/REPORT.md`.

A subsequent read-only review of the final composition confirmed that `NameClosure.For.adequate` has no hidden closed-family or graph premise: the only logical parameter is the original LEM. It also confirmed that the remaining semantic image and general-ground obligations are not discharged by this theorem.

## 7. Exact checked source snapshots

### PairFormulaReading.agda

SHA-256: `1554b61471257ccdeafb6695ad140032c58b5528d9644dfd6b6e63dc9b1abda6`

```text
{-# OPTIONS --cubical --safe --guardedness #-}

open import Base.Prelude

module PairFormulaReading {ℓ} where

open import Base.Truth using ( hPropAlgebra )
open import FOL.ZFStructure using ( module hPropStructure )
open import L.Constructible {ℓ} using ( 𝒮ʟ; isL )
open import L.Coding.Model {ℓ} using ( prAtL; prAtL-adequate; prʟ; prʟ-fst )
open import FOL.Semantics (hPropAlgebra (ℓ-suc ℓ)) 𝒮ʟ using ( module At )
open import Cubical.Data.Sigma using ( Σ≡Prop )
open import Cubical.Functions.Logic using ( ⇔toPath )
open hPropStructure 𝒮ʟ using ( S; isSetS )
open At S id using ( _⊨_ )

reading : ∀ {n} (q u v : Fin n) (γ : Vec S n)
  → (γ ⊨ prAtL q u v)
  ≡ ((lookup q γ ≡ prʟ (lookup u γ) (lookup v γ)) ,
     isSetS (lookup q γ) (prʟ (lookup u γ) (lookup v γ)))
reading q u v γ = ⇔toPath forward backward
  where
  adequate = prAtL-adequate q u v γ
  forward : ⟨ γ ⊨ prAtL q u v ⟩ → lookup q γ ≡ prʟ (lookup u γ) (lookup v γ)
  forward h = Σ≡Prop (λ z → snd (isL z))
    (subst ⟨_⟩ adequate h ∙ sym (prʟ-fst (lookup u γ) (lookup v γ)))
  backward : lookup q γ ≡ prʟ (lookup u γ) (lookup v γ) → ⟨ γ ⊨ prAtL q u v ⟩
  backward p = subst ⟨_⟩ (sym adequate)
    (cong fst p ∙ prʟ-fst (lookup u γ) (lookup v γ))
```

### NameSupport.agda

SHA-256: `5bd9c7456ff5f4d6b7f4cd49eabb7b047fd28c74aeb175cabbe11bc04043dd7b`

```text
{-# OPTIONS --cubical --safe --guardedness #-}

open import Base.Prelude
open import Base.Truth
open import Base.Classical using ( LEM )

module NameSupport {ℓ : Level} (lem : LEM (ℓ-suc ℓ)) where

open import FOL.ZFStructure using ( module hPropStructure )
open import FOL.Syntax using ( Formula; ∃̇_ )
import FOL.Absoluteness
import FOL.ZFModel as Model
open import V.Hierarchy {ℓ} using ( 𝒮ᵥ )
open import V.Coding {ℓ} using ( pr )
open import L.Constructible {ℓ} using ( 𝒮ʟ; isL; isL-trans )
open import L.Model {ℓ} lem using ( L⊨ZF )
open import L.Coding.Model {ℓ}
  using ( prAtL; prAtL-adequate; prʟ; prʟ-fst; prʟ-inj )
open import CoordinateDecoder {ℓ}
  using ( Representation; representation-is-prop; decodeCoordinates )
open import Cubical.Data.Sigma using ( Σ≡Prop )
open import Cubical.Functions.Logic using ( ⇔toPath )
open import Cubical.HITs.CumulativeHierarchy.Base using ( setIsSet )
import Cubical.HITs.PropositionalTruncation as PT
open PT using ( ∥_∥₁; ∣_∣₁; squash₁ )

open TruthAlgebra (hPropAlgebra (ℓ-suc ℓ))
open hPropStructure 𝒮ʟ

module AbsL = FOL.Absoluteness.Single 𝒮ᵥ isL isL-trans
open AbsL using ( _^_ ) renaming ( _⊨ᵐ_ to _⊨_ )

opaque
  ground : Model.isZFModel 𝒮ʟ
  ground = L⊨ZF

coordinateFormula : Formula S 2
coordinateFormula = ∃̇ (prAtL (suc (suc zero)) (suc zero) zero)

Coordinates : S → S → hProp (ℓ-suc ℓ)
Coordinates e x =
  (∥ Σ[ b ∈ S ] e ≡ prʟ x b ∥₁)
  , squash₁

coordinateFormula-adequate : (e x : S)
                           → ((x ∷ e ∷ []) ⊨ coordinateFormula)
                           ≡ Coordinates e x
coordinateFormula-adequate e x = ⇔toPath
  (PT.map (λ { (b , h) → b , forward b h }))
  (PT.map (λ { (b , q) → b , backward b q }))
  where
  adequate : (b : S)
           → ((b ∷ x ∷ e ∷ [])
                ⊨ prAtL (suc (suc zero)) (suc zero) zero)
           ≡ ((fst e ≡ pr (fst x) (fst b)) , setIsSet _ _)
  adequate b = prAtL-adequate (suc (suc zero)) (suc zero) zero
    (b ∷ x ∷ e ∷ [])

  forward : (b : S)
          → ⟨ (b ∷ x ∷ e ∷ [])
                ⊨ prAtL (suc (suc zero)) (suc zero) zero ⟩
          → e ≡ prʟ x b
  forward b h = Σ≡Prop (λ v → snd (isL v))
    (subst ⟨_⟩ (adequate b) h ∙ sym (prʟ-fst x b))

  backward : (b : S) → e ≡ prʟ x b
           → ⟨ (b ∷ x ∷ e ∷ [])
                 ⊨ prAtL (suc (suc zero)) (suc zero) zero ⟩
  backward b q = subst ⟨_⟩ (sym (adequate b))
    (cong fst q ∙ prʟ-fst x b)

module Support (n : S)
    (represented : (e : S) → ⟨ e ∈ˢ n ⟩ → ∥ Representation e ∥₁) where

  functional : (e : S) → ⟨ e ∈ˢ n ⟩
             → isContr (Σ[ x ∈ S ] ⟨ (x ∷ e ∷ []) ⊨ coordinateFormula ⟩)
  functional e e∈ = (x , sat) , unique
    where
    decoded : Representation e
    decoded = decodeCoordinates e (represented e e∈)

    x : S
    x = decoded .fst

    b : S
    b = decoded .snd .fst

    q : e ≡ prʟ x b
    q = decoded .snd .snd

    sat : ⟨ (x ∷ e ∷ []) ⊨ coordinateFormula ⟩
    sat = subst ⟨_⟩ (sym (coordinateFormula-adequate e x)) ∣ b , q ∣₁

    coordinate-unique : (y : S) → ⟨ (y ∷ e ∷ []) ⊨ coordinateFormula ⟩ → x ≡ y
    coordinate-unique y h = PT.rec (isSetS x y)
      (λ { (c , r) → prʟ-inj (sym q ∙ r) .fst })
      (subst ⟨_⟩ (coordinateFormula-adequate e y) h)

    unique : (w : Σ[ y ∈ S ] ⟨ (y ∷ e ∷ []) ⊨ coordinateFormula ⟩)
           → (x , sat) ≡ w
    unique (y , h) = Σ≡Prop
      (λ y → snd ((y ∷ e ∷ []) ⊨ coordinateFormula))
      (coordinate-unique y h)

  support : S
  support = Model.℩ 𝒮ʟ
    (Model.isZFModel.hasReplacement ground n coordinateFormula functional)

  SupportWitness : S → Type (ℓ-suc ℓ)
  SupportWitness x =
    Σ[ e ∈ S ] (⟨ e ∈ˢ n ⟩ × (Σ[ b ∈ S ] e ≡ prʟ x b))

  support-in : (x : S) → ∥ SupportWitness x ∥₁ → ⟨ x ∈ˢ support ⟩
  support-in x = PT.rec (snd (x ∈ˢ support)) (λ { (e , e∈ , b , q) →
    subst ⟨_⟩
      (sym (Model.℩-spec 𝒮ʟ
        (Model.isZFModel.hasReplacement ground n coordinateFormula functional) x))
      ∣ e , e∈ , subst ⟨_⟩ (sym (coordinateFormula-adequate e x)) ∣ b , q ∣₁ ∣₁ })

  support-out : (x : S) → ⟨ x ∈ˢ support ⟩ → ∥ SupportWitness x ∥₁
  support-out x x∈ = PT.rec squash₁
    (λ { (e , e∈ , sat) → PT.map
      (λ { (b , q) → e , e∈ , b , q })
      (subst ⟨_⟩ (coordinateFormula-adequate e x) sat) })
    (subst ⟨_⟩
      (Model.℩-spec 𝒮ʟ
        (Model.isZFModel.hasReplacement ground n coordinateFormula functional) x)
      x∈)
```

### NameRecognition.agda

SHA-256: `04845cd3dc06fad94add0c66a23ef043816ea76b89628f287e0a00fa542048dc`

```text
{-# OPTIONS --cubical --safe --guardedness #-}

open import Base.Prelude
open import Base.Classical using ( LEM )

module NameRecognition {ℓ} (lem : LEM (ℓ-suc ℓ)) where

open import Base.Truth using ( hPropAlgebra )
open import FOL.ZFStructure using ( module hPropStructure )
open import L.Constructible {ℓ} using ( 𝒮ʟ )
open import L.Coding.Model {ℓ} using ( prAtL; prʟ; prʟ-inj )
open import FOL.Syntax using ( Formula; var; con; _∈̇_; _∧̇_; ∃̇_; ∀̇∈; ∃̇∈ )
open import FOL.Semantics (hPropAlgebra (ℓ-suc ℓ)) 𝒮ʟ using ( module At )
open import MaterialNameL lem using ( ground )
open import MaterialNamePredicate 𝒮ʟ using ( module Names )
open import GroundClosure 𝒮ʟ using ( module MaterialNames )
open import NameDescent 𝒮ʟ using ( module Descent )
open import CoordinateDecoder {ℓ} using ( module WithLEM )
open WithLEM lem using ( orderedPairName-bridge )
open import PairFormulaReading {ℓ} using ( reading )
import Cubical.HITs.PropositionalTruncation as PT
open PT using ( ∥_∥₁ )
open hPropStructure 𝒮ʟ using ( S; _∈ˢ_ )
open At S id using ( _⊨_ )
open MaterialNames ground using ( weightedEntry )
open Descent ground (λ _ → refl) using ( Child; module Recursion )

opaque
  unfolding ground
  entry-bridge : ∀ x b → weightedEntry x b ≡ prʟ x b
  entry-bridge = orderedPairName-bridge

module Recognition (B : S) where

  open Names ground (λ _ → refl) B using ( IsName; Shape; unfold )

  formula : Formula S 1
  formula = ∃̇ ((var (suc zero) ∈̇ var zero) ∧̇
    ∀̇∈ (var zero) (∀̇∈ (var zero)
      (∃̇∈ (var (suc (suc zero))) (∃̇∈ (con B)
        (prAtL (suc (suc zero)) (suc zero) zero)))))

  Closed : S → Type (ℓ-suc ℓ)
  Closed C = ∀ n → ⟨ n ∈ˢ C ⟩ → ∀ e → ⟨ e ∈ˢ n ⟩ →
    ∥ Σ[ x ∈ S ] ⟨ x ∈ˢ C ⟩ ×
      ∥ Σ[ b ∈ S ] ⟨ b ∈ˢ B ⟩ × (e ≡ prʟ x b) ∥₁ ∥₁

  readClosed : ∀ C t →
    (∀ n → ⟨ n ∈ˢ C ⟩ → ∀ e → ⟨ e ∈ˢ n ⟩ →
      ∥ Σ[ x ∈ S ] ⟨ x ∈ˢ C ⟩ ×
        ∥ Σ[ b ∈ S ] ⟨ b ∈ˢ B ⟩ ×
          ⟨ (b ∷ x ∷ e ∷ n ∷ C ∷ t ∷ []) ⊨
            prAtL (suc (suc zero)) (suc zero) zero ⟩ ∥₁ ∥₁)
    → Closed C
  readClosed C t proof n inC e member = PT.map
    (λ { (x , xC , weights) → x , xC , PT.map
      (λ { (b , bB , h) → b , bB , subst ⟨_⟩
        (reading (suc (suc zero)) (suc zero) zero (b ∷ x ∷ e ∷ n ∷ C ∷ t ∷ [])) h }) weights })
    (proof n inC e member)

  module Family (C : S) (closed : Closed C) where

    shape : ∀ n → ⟨ n ∈ˢ C ⟩ → ⟨ Shape n ⟩
    shape n inC e member = PT.rec PT.squash₁
      (λ { (x , xC , weights) → PT.map
        (λ { (b , bB , eq) → x , b , eq ∙ sym (entry-bridge x b) , bB }) weights })
      (closed n inC e member)

    child-in : ∀ n → ⟨ n ∈ˢ C ⟩ → ∀ x → Child x n → ⟨ x ∈ˢ C ⟩
    child-in n inC x edge = PT.rec (snd (x ∈ˢ C))
      (λ { (b , member) → PT.rec (snd (x ∈ˢ C))
        (λ { (y , yC , weights) → PT.rec (snd (x ∈ˢ C))
          (λ { (c , cB , eq) → subst (λ z → ⟨ z ∈ˢ C ⟩)
            (sym (fst (prʟ-inj {a = x} {b = b} {c = y} {d = c}
              (sym (entry-bridge x b) ∙ eq)))) yC }) weights })
        (closed n inC (weightedEntry x b) member) }) edge

    step : ∀ n → (∀ x → Child x n → (⟨ x ∈ˢ C ⟩ → ⟨ IsName x ⟩))
      → ⟨ n ∈ˢ C ⟩ → ⟨ IsName n ⟩
    step n below inC = subst ⟨_⟩ (sym (unfold n))
      (shape n inC , λ x edge → below x edge (child-in n inC x edge))

    sound : ∀ n → ⟨ n ∈ˢ C ⟩ → ⟨ IsName n ⟩
    sound = Recursion.result (λ n → ⟨ n ∈ˢ C ⟩ → ⟨ IsName n ⟩) step

  formula-sound : ∀ t → ⟨ (t ∷ []) ⊨ formula ⟩ → ⟨ IsName t ⟩
  formula-sound t = PT.rec (snd (IsName t))
    (λ { (C , member , closed) → Family.sound C (readClosed C t closed) t member })

  formula-from-closed : ∀ C t → ⟨ t ∈ˢ C ⟩ → Closed C → ⟨ (t ∷ []) ⊨ formula ⟩
  formula-from-closed C t member closed = PT.∣ C , member ,
    (λ n inC e inN → PT.map
      (λ { (x , xC , weights) → x , xC , PT.map
        (λ { (b , bB , eq) → b , bB , subst ⟨_⟩
          (sym (reading (suc (suc zero)) (suc zero) zero
            (b ∷ x ∷ e ∷ n ∷ C ∷ t ∷ []))) eq }) weights })
      (closed n inC e inN)) ∣₁
```

### NamedSupport.agda

SHA-256: `3948602cfe49d8072592c94b64f2026c2da374c614afbe1aa4eab6b0698ce1df`

```text
{-# OPTIONS --cubical --safe --guardedness #-}

open import Base.Prelude
open import Base.Classical using ( LEM )

module NamedSupport {ℓ} (lem : LEM (ℓ-suc ℓ)) where

open import FOL.ZFStructure using ( module hPropStructure )
open import L.Constructible {ℓ} using ( 𝒮ʟ )
open import CoordinateDecoder {ℓ} using ( Representation )
open import MaterialNameL lem using ( ground; module At )
open import GroundClosure 𝒮ʟ using ( module MaterialNames )
open import NameDescent 𝒮ʟ using ( module Descent )
open import NameRecognition lem using ( entry-bridge )
open import NameSupport lem using ( module Support )
import Cubical.HITs.PropositionalTruncation as PT
open PT using ( ∥_∥₁; ∣_∣₁ )
open hPropStructure 𝒮ʟ using ( S; _∈ˢ_ )
open MaterialNames ground using ( weightedEntry )
open Descent ground (λ _ → refl) using ( Child )

module For (B : S) where
  open At B using ( Name; module Predicate )
  open Predicate using ( name-shape; child-is-name; IsName )

  represented : (n : Name) → ∀ e → ⟨ e ∈ˢ fst n ⟩ → ∥ Representation e ∥₁
  represented n e member = PT.map
    (λ { (x , b , eq , bB) → x , b , eq ∙ entry-bridge x b })
    (name-shape (fst n) (snd n) e member)

  module Of (n : Name) where
    module Internal = Support (fst n) (represented n)
    open Internal public using ( support )

    child-to-member : ∀ x → Child x (fst n) → ⟨ x ∈ˢ support ⟩
    child-to-member x edge = Internal.support-in x (PT.map
      (λ { (b , member) → weightedEntry x b , member , b , entry-bridge x b }) edge)

    member-to-child : ∀ x → ⟨ x ∈ˢ support ⟩ → Child x (fst n)
    member-to-child x member = PT.map
      (λ { (e , inN , b , eq) → b ,
        subst (λ z → ⟨ z ∈ˢ fst n ⟩) (eq ∙ sym (entry-bridge x b)) inN })
      (Internal.support-out x member)

    member-is-name : ∀ x → ⟨ x ∈ˢ support ⟩ → ⟨ IsName x ⟩
    member-is-name x member = child-is-name (fst n) (snd n) x (member-to-child x member)

    decode : Σ[ x ∈ S ] ⟨ x ∈ˢ support ⟩ → Name
    decode (x , member) = x , member-is-name x member
```

### NamedEntries.agda

SHA-256: `0899a79cf03d64d3bab022a120fe84076eb2905dc08d4ec08ddc92a9cf2643fa`

```text
{-# OPTIONS --cubical --safe --guardedness #-}

open import Base.Prelude
open import Base.Classical using ( LEM )

module NamedEntries {ℓ} (lem : LEM (ℓ-suc ℓ)) where

open import FOL.ZFStructure using ( module hPropStructure )
open import L.Constructible {ℓ} using ( 𝒮ʟ )
open import L.Coding.Model {ℓ} using ( prʟ; prʟ-inj )
open import MaterialNameL lem using ( ground; module At )
open import GroundClosure 𝒮ʟ using ( module MaterialNames )
open import NameDescent 𝒮ʟ using ( module Descent )
open import CoordinateDecoder {ℓ} using ( Representation; decodeCoordinates )
open import NameRecognition lem using ( entry-bridge )
import NamedSupport
open import Cubical.Foundations.HLevels using ( isProp× )
import Cubical.HITs.PropositionalTruncation as PT
open PT using ( ∣_∣₁ )
open hPropStructure 𝒮ʟ using ( S; _∈ˢ_ )
open MaterialNames ground using ( weightedEntry )
open Descent ground (λ _ → refl) using ( Child )

module For (B : S) where
  open At B using ( Name; module Predicate )
  open Predicate using ( IsName; name-shape; child-is-name )
  module Support = NamedSupport.For lem B

  module Of (n : Name) where

    Index : Type (ℓ-suc ℓ)
    Index = Σ[ e ∈ S ] ⟨ e ∈ˢ fst n ⟩

    raw : (i : Index) → Representation (fst i)
    raw (e , member) = decodeCoordinates e (Support.represented n e member)

    raw-child : (i : Index) → Child (fst (raw i)) (fst n)
    raw-child (e , member) = ∣ raw (e , member) .snd .fst ,
      subst (λ z → ⟨ z ∈ˢ fst n ⟩)
        (raw (e , member) .snd .snd ∙ sym (entry-bridge (raw (e , member) .fst) (raw (e , member) .snd .fst)))
        member ∣₁

    raw-weight : (i : Index) → ⟨ raw i .snd .fst ∈ˢ B ⟩
    raw-weight (e , member) = PT.rec (snd (raw (e , member) .snd .fst ∈ˢ B))
      (λ { (x , b , eq , bB) → subst (λ z → ⟨ z ∈ˢ B ⟩)
        (sym (snd (prʟ-inj
          {a = raw (e , member) .fst} {b = raw (e , member) .snd .fst} {c = x} {d = b}
          (sym (raw (e , member) .snd .snd) ∙ eq ∙ entry-bridge x b)))) bB })
      (name-shape (fst n) (snd n) e member)

    child : Index → Name
    child i = raw i .fst , child-is-name (fst n) (snd n) (raw i .fst) (raw-child i)

    weight : Index → Σ[ b ∈ S ] ⟨ b ∈ˢ B ⟩
    weight i = raw i .snd .fst , raw-weight i

    represents : (i : Index) → fst i ≡ prʟ (fst (child i)) (fst (weight i))
    represents i = raw i .snd .snd

    decreases : (i : Index) → Child (fst (child i)) (fst n)
    decreases = raw-child
```

### NameClosureDown.agda

SHA-256: `c150436dc5a03143dd666ba88ef2c8120509957cde11dfe088cea5f139cf51d9`

```text
{-# OPTIONS --cubical --safe --guardedness #-}

open import Base.Prelude
open import Base.Truth
open import Base.Classical using ( LEM )

module NameClosureDown {ℓ : Level} (lem : LEM (ℓ-suc ℓ)) where

open import FOL.ZFStructure using ( module hPropStructure )
open import FOL.Syntax using ( Formula; var; con; ∃̇_; ∃̇∈ )
import FOL.Absoluteness
import FOL.ZFModel as Model
open import V.Hierarchy {ℓ} using ( 𝒮ᵥ )
open import L.Constructible {ℓ} using ( 𝒮ʟ; isL; isL-trans )
open import L.Model {ℓ} lem using ( L⊨ZF )
open import L.Axioms.Numerals {ℓ} using ( pairʟ; unionʟ )
open import L.Coding.Model {ℓ} using ( prAtL; prAtL-adequate; prʟ; prʟ-fst )
open import L.GCH.OmegaRecursion {ℓ} lem using ( pairʟ-in; unionʟ-in )
open import NameSupport {ℓ} lem using ( coordinateFormula-adequate )
open import Cubical.Data.Sum using ( inl )
open import Cubical.Data.Sigma using ( Σ≡Prop )
open import Cubical.Functions.Logic using ( ⇔toPath )
open import V.Coding {ℓ} using ( pr )
open import Cubical.HITs.CumulativeHierarchy.Base using ( setIsSet )
import Cubical.HITs.PropositionalTruncation as PT
open PT using ( ∥_∥₁; ∣_∣₁; squash₁ )

open TruthAlgebra (hPropAlgebra (ℓ-suc ℓ))
open hPropStructure 𝒮ʟ

module AbsL = FOL.Absoluteness.Single 𝒮ᵥ isL isL-trans
open AbsL using ( _^_ ) renaming ( _⊨ᵐ_ to _⊨_ )

opaque
  ground : Model.isZFModel 𝒮ʟ
  ground = L⊨ZF

Child : S → S → Type (ℓ-suc ℓ)
Child x n = ∥ Σ[ b ∈ S ] ⟨ prʟ x b ∈ˢ n ⟩ ∥₁

Descendant : S → S → Type (ℓ-suc ℓ)
Descendant A x = ∥ Σ[ n ∈ S ] (⟨ n ∈ˢ A ⟩ × Child x n) ∥₁

childFo : (A : S) → Formula S 1
childFo A = ∃̇∈ (con A)
  (∃̇∈ (var zero)
    (∃̇ (prAtL (suc zero) (suc (suc (suc zero))) zero)))

childFo-adequate : (A x : S)
                 → ((x ∷ []) ⊨ childFo A)
                 ≡ (Descendant A x , squash₁)
childFo-adequate A x = ⇔toPath forward backward
  where
  entry : (n e b : S)
        → ((b ∷ e ∷ n ∷ x ∷ [])
             ⊨ prAtL (suc zero) (suc (suc (suc zero))) zero)
        ≡ ((e ≡ prʟ x b) , isSetS e (prʟ x b))
  entry n e b = ⇔toPath
    (λ h → Σ≡Prop (λ v → snd (isL v))
      (subst ⟨_⟩ adequate h ∙ sym (prʟ-fst x b)))
    (λ q → subst ⟨_⟩ (sym adequate) (cong fst q ∙ prʟ-fst x b))
    where
    adequate = prAtL-adequate (suc zero) (suc (suc (suc zero))) zero
      (b ∷ e ∷ n ∷ x ∷ [])

  forward : ⟨ (x ∷ []) ⊨ childFo A ⟩ → Descendant A x
  forward = PT.map (λ { (n , n∈ , witnesses) → n , n∈ , PT.rec squash₁
    (λ { (e , e∈ , bs) → PT.map
      (λ { (b , h) → b , subst (λ z → ⟨ z ∈ˢ n ⟩)
        (subst ⟨_⟩ (entry n e b) h) e∈ }) bs })
    witnesses })

  backward : Descendant A x → ⟨ (x ∷ []) ⊨ childFo A ⟩
  backward = PT.map (λ { (n , n∈ , children) → n , n∈ , PT.map
    (λ { (b , p) → prʟ x b , p ,
      ∣ b , subst ⟨_⟩ (sym (entry n (prʟ x b) b)) refl ∣₁ })
    children })

tripleUnion : S → S
tripleUnion A = unionʟ (unionʟ (unionʟ A))

down : S → S
down A = Model.℩ 𝒮ʟ
  (Model.isZFModel.hasSeparation ground (tripleUnion A) (childFo A))

down-spec : (A x : S)
          → (x ∈ˢ down A)
          ≡ ((x ∈ˢ tripleUnion A) ⊓ ((x ∷ []) ⊨ childFo A))
down-spec A = Model.℩-spec 𝒮ʟ
  (Model.isZFModel.hasSeparation ground (tripleUnion A) (childFo A))

down-in : (A x : S) → Descendant A x → ⟨ x ∈ˢ down A ⟩
down-in A x = PT.rec (snd (x ∈ˢ down A)) outer
  where
  outer : Σ[ n ∈ S ] (⟨ n ∈ˢ A ⟩ × Child x n) → ⟨ x ∈ˢ down A ⟩
  outer (n , n∈ , children) = PT.rec (snd (x ∈ˢ down A)) inner children
    where
    inner : Σ[ b ∈ S ] ⟨ prʟ x b ∈ˢ n ⟩ → ⟨ x ∈ˢ down A ⟩
    inner (b , e∈) = subst ⟨_⟩ (sym (down-spec A x))
      (x∈bound , subst ⟨_⟩ (sym (childFo-adequate A x))
        ∣ n , n∈ , ∣ b , e∈ ∣₁ ∣₁)
      where
      s : S
      s = pairʟ x x

      x∈s : ⟨ x ∈ˢ s ⟩
      x∈s = pairʟ-in x x x (inl refl)

      s∈e : ⟨ s ∈ˢ prʟ x b ⟩
      s∈e = pairʟ-in s (pairʟ x b) s (inl refl)

      e∈uA : ⟨ prʟ x b ∈ˢ unionʟ A ⟩
      e∈uA = unionʟ-in A (prʟ x b) n n∈ e∈

      s∈uuA : ⟨ s ∈ˢ unionʟ (unionʟ A) ⟩
      s∈uuA = unionʟ-in (unionʟ A) s (prʟ x b) e∈uA s∈e

      x∈bound : ⟨ x ∈ˢ tripleUnion A ⟩
      x∈bound = unionʟ-in (unionʟ (unionʟ A)) x s s∈uuA x∈s

down-out : (A x : S) → ⟨ x ∈ˢ down A ⟩ → Descendant A x
down-out A x x∈ = subst ⟨_⟩ (childFo-adequate A x)
  (subst ⟨_⟩ (down-spec A x) x∈ .snd)
```

### NameClosureStep.agda

SHA-256: `324fbe028c3677398b1354c501a05dd2396667c79c9143ce549127fa1daeab6b`

```text
{-# OPTIONS --cubical --safe --guardedness #-}

open import Base.Prelude
open import Base.Truth
open import Base.Classical using ( LEM )

module NameClosureStep {ℓ : Level} (lem : LEM (ℓ-suc ℓ)) where

open import FOL.ZFStructure using ( module hPropStructure )
open import FOL.Syntax
  using ( Term; Formula; var; _∈̇_; _∧̇_; _∨̇_; _⇒̇_; ∃̇_; ∀̇_; ∃̇∈ )
import FOL.Absoluteness
import FOL.ZFModel as Model
open import V.Hierarchy {ℓ} using ( 𝒮ᵥ )
open import L.Constructible {ℓ} using ( 𝒮ʟ; isL; isL-trans )
open import L.Model {ℓ} lem using ( L⊨ZF )
open import L.Coding.Model {ℓ} using ( prAtL; prʟ )
open import NameClosureDown {ℓ} lem
  using ( Child; Descendant; down; down-in; down-out )
open import PairFormulaReading {ℓ} using ( reading )
open import Cubical.Data.Sigma using ( Σ≡Prop )
open import Cubical.Data.Sum using ( _⊎_; inl; inr )
open import Cubical.Functions.Logic using ( ⇔toPath )
import Cubical.HITs.PropositionalTruncation as PT
open PT using ( ∥_∥₁; ∣_∣₁; squash₁ )

open TruthAlgebra (hPropAlgebra (ℓ-suc ℓ))
open hPropStructure 𝒮ʟ

module AbsL = FOL.Absoluteness.Single 𝒮ᵥ isL isL-trans
open AbsL using ( _^_ ) renaming ( _⊨ᵐ_ to _⊨_; ⟦_⟧ᵐ to ⟦_⟧ )

opaque
  ground : Model.isZFModel 𝒮ʟ
  ground = L⊨ZF

module Ground = Model.isZFModel ground

private
  S≡ : {x y : S} → fst x ≡ fst y → x ≡ y
  S≡ = Σ≡Prop (λ v → snd (isL v))

step : S → S
step A = Ground._∪_ A (down A)

private
  step-spec : (A x : S)
            → (x ∈ˢ step A) ≡ ((x ∈ˢ A) ⊔ (x ∈ˢ down A))
  step-spec A x = Model.℩-spec 𝒮ʟ
      (Ground.hasUnion (Ground.pair A (down A))) x
    ∙ ⇔toPath forward backward
    where
    forward : ∥ Σ[ B ∈ S ]
        (⟨ B ∈ˢ Ground.pair A (down A) ⟩ × ⟨ x ∈ˢ B ⟩) ∥₁
      → ∥ (⟨ x ∈ˢ A ⟩ ⊎ ⟨ x ∈ˢ down A ⟩) ∥₁
    forward = PT.rec squash₁ (λ { (B , B∈ , x∈) → PT.rec squash₁
      (λ { (inl p) → ∣ inl (subst (λ C → ⟨ x ∈ˢ C ⟩)
              (S≡ {x = B} {y = A} p) x∈) ∣₁
         ; (inr p) → ∣ inr (subst (λ C → ⟨ x ∈ˢ C ⟩)
              (S≡ {x = B} {y = down A} p) x∈) ∣₁ })
      (subst ⟨_⟩ (Ground.pair-spec A (down A) B) B∈) })

    backward : ∥ (⟨ x ∈ˢ A ⟩ ⊎ ⟨ x ∈ˢ down A ⟩) ∥₁
      → ∥ Σ[ B ∈ S ]
          (⟨ B ∈ˢ Ground.pair A (down A) ⟩ × ⟨ x ∈ˢ B ⟩) ∥₁
    backward = PT.map
      (λ { (inl p) → A , subst ⟨_⟩
              (sym (Ground.pair-spec A (down A) A)) ∣ inl refl ∣₁ , p
         ; (inr p) → down A , subst ⟨_⟩
              (sym (Ground.pair-spec A (down A) (down A))) ∣ inr refl ∣₁ , p })

step-in-original : ∀ A x → ⟨ x ∈ˢ A ⟩ → ⟨ x ∈ˢ step A ⟩
step-in-original A x x∈ = subst ⟨_⟩ (sym (step-spec A x))
  ∣ inl x∈ ∣₁

step-in-child : ∀ A n x → ⟨ n ∈ˢ A ⟩ → Child x n → ⟨ x ∈ˢ step A ⟩
step-in-child A n x n∈ child = subst ⟨_⟩ (sym (step-spec A x))
  ∣ inr (down-in A x ∣ n , n∈ , child ∣₁) ∣₁

step-out : ∀ A x → ⟨ x ∈ˢ step A ⟩
         → ∥ ((⟨ x ∈ˢ A ⟩) ⊎ (Σ[ n ∈ S ] (⟨ n ∈ˢ A ⟩ × Child x n))) ∥₁
step-out A x x∈ = PT.rec squash₁
  (λ { (inl p) → ∣ inl p ∣₁
     ; (inr p) → PT.map inr (down-out A x p) })
  (subst ⟨_⟩ (step-spec A x) x∈)

childAt : ∀ {k} (a : Term S k) (x : Fin k) → Formula S k
childAt a x = ∃̇∈ a
  (∃̇∈ (var zero)
    (∃̇ (prAtL (suc zero) (suc (suc (suc x))) zero)))

childAt-adequate : ∀ {k} (a : Term S k) (x : Fin k) (γ : S ^ k)
  → (γ ⊨ childAt a x)
  ≡ ((∥ Σ[ n ∈ S ] (⟨ n ∈ˢ ⟦ a ⟧ γ ⟩ × Child (lookup x γ) n) ∥₁) , squash₁)
childAt-adequate a x γ = ⇔toPath forward backward
  where
  forward : ⟨ γ ⊨ childAt a x ⟩
          → ∥ Σ[ n ∈ S ] (⟨ n ∈ˢ ⟦ a ⟧ γ ⟩ × Child (lookup x γ) n) ∥₁
  forward = PT.map (λ { (n , n∈ , es) → n , n∈ , PT.rec squash₁
    (λ { (e , e∈ , bs) → PT.map (λ { (b , p) → b ,
      subst (λ z → ⟨ z ∈ˢ n ⟩) (subst ⟨_⟩
        (reading (suc zero) (suc (suc (suc x))) zero
          (b ∷ e ∷ n ∷ γ)) p) e∈ }) bs }) es })

  backward : ∥ Σ[ n ∈ S ] (⟨ n ∈ˢ ⟦ a ⟧ γ ⟩ × Child (lookup x γ) n) ∥₁
           → ⟨ γ ⊨ childAt a x ⟩
  backward = PT.map (λ { (n , n∈ , bs) → n , n∈ , PT.map
    (λ { (b , e∈) → prʟ (lookup x γ) b , e∈ ,
      ∣ b , subst ⟨_⟩
        (sym (reading (suc zero) (suc (suc (suc x))) zero
          (b ∷ prʟ (lookup x γ) b ∷ n ∷ γ))) refl ∣₁ }) bs })

private
  rhs : Formula S 3
  rhs = (var zero ∈̇ var (suc (suc zero)))
      ∨̇ childAt (var (suc (suc zero))) zero

  rhs-adequate : (A out x : S)
    → ((x ∷ out ∷ A ∷ []) ⊨ rhs) ≡ (x ∈ˢ step A)
  rhs-adequate A out x = cong (λ P → (x ∈ˢ A) ⊔ P)
      (childAt-adequate (var (suc (suc zero))) zero (x ∷ out ∷ A ∷ [])
        ∙ ⇔toPath {P = (Descendant A x , squash₁)} {Q = x ∈ˢ down A}
            (down-in A x) (down-out A x))
    ∙ sym (step-spec A x)

stepFo : Formula S 2
stepFo = ∀̇ (((var zero ∈̇ var (suc zero)) ⇒̇ rhs)
          ∧̇ (rhs ⇒̇ (var zero ∈̇ var (suc zero))))

defines : ∀ A → ⟨ (step A ∷ A ∷ []) ⊨ stepFo ⟩
defines A x =
  (λ x∈ → subst ⟨_⟩ (sym (rhs-adequate A (step A) x)) x∈) ,
  (λ h → subst ⟨_⟩ (rhs-adequate A (step A) x) h)

only : ∀ A out → ⟨ (out ∷ A ∷ []) ⊨ stepFo ⟩ → out ≡ step A
only A out h = Ground.extensional (λ x → ⇔toPath
  (λ x∈ → subst ⟨_⟩ (rhs-adequate A out x) (h x .fst x∈))
  (λ x∈ → h x .snd (subst ⟨_⟩ (sym (rhs-adequate A out x)) x∈)))
```

### NameClosure.agda

SHA-256: `62f39f8124788e7fbd92ca45e712ec43ea0ed7c72b7894e0fa48708ce3346d35`

```text
{-# OPTIONS --cubical --safe --guardedness #-}

open import Base.Prelude
open import Base.Classical using ( LEM )

module NameClosure {ℓ} (lem : LEM (ℓ-suc ℓ)) where

open import Base.Truth using ( hPropAlgebra )
open import FOL.ZFStructure using ( module hPropStructure; ↾-reflects )
open import L.Constructible {ℓ} using ( 𝒮ʟ; isL )
open import V.Hierarchy {ℓ} using ( 𝒮ᵥ )
open import MaterialNameL lem using ( ground )
open import FOL.ZFModel 𝒮ʟ using ( module isZFModel )
open isZFModel ground using ( pair; pair-spec )
open import MaterialNamePredicate 𝒮ʟ using ( module Names )
open import NameRecognition lem using ( entry-bridge; module Recognition )
open import L.Coding.Model {ℓ} using ( prʟ )
open import L.GCH.OmegaRecursion {ℓ} lem using ( module Iterate )
open import NameClosureDown lem using ( Child )
import NameClosureStep
module Step = NameClosureStep lem
open import FOL.Semantics (hPropAlgebra (ℓ-suc ℓ)) 𝒮ʟ using ( module At )
open import Cubical.Data.Sum using ( inl; inr )
open import Cubical.Functions.Logic using ( ⇔toPath )
import Cubical.HITs.PropositionalTruncation as PT
open PT using ( ∥_∥₁; ∣_∣₁ )
open hPropStructure 𝒮ʟ using ( S; _∈ˢ_ )
open At S id using ( _⊨_ )

module For (B : S) where
  open Names ground (λ _ → refl) B using ( IsName; name-shape; child-is-name )
  module Recognizer = Recognition B

  module Witness (t : S) (valid : ⟨ IsName t ⟩) where

    seed : S
    seed = pair t t

    seed-in : ⟨ t ∈ˢ seed ⟩
    seed-in = subst ⟨_⟩ (sym (pair-spec t t t)) ∣ inl refl ∣₁

    seed-valid : ∀ n → ⟨ n ∈ˢ seed ⟩ → ⟨ IsName n ⟩
    seed-valid n member = PT.rec (snd (IsName n))
      (λ { (inl eq) → subst (λ z → ⟨ IsName z ⟩)
           (sym (↾-reflects {𝒮 = 𝒮ᵥ} {M = isL} eq)) valid
         ; (inr eq) → subst (λ z → ⟨ IsName z ⟩)
           (sym (↾-reflects {𝒮 = 𝒮ᵥ} {M = isL} eq)) valid })
      (subst ⟨_⟩ (pair-spec t t n) member)

    module Iteration = Iterate seed Step.stepFo Step.step Step.defines Step.only
      using ( it; iterUnion; iterUnion-in; iterUnion-out )

    stage-valid : ∀ k n → ⟨ n ∈ˢ Iteration.it k ⟩ → ⟨ IsName n ⟩
    stage-valid zero n = seed-valid n
    stage-valid (suc k) n member = PT.rec (snd (IsName n))
      (λ { (inl old) → stage-valid k n old
         ; (inr (parent , parentIn , edge)) → child-is-name parent
           (stage-valid k parent parentIn) n
           (PT.map (λ { (b , member) → b ,
             subst (λ z → ⟨ z ∈ˢ parent ⟩) (sym (entry-bridge n b)) member }) edge) })
      (Step.step-out (Iteration.it k) n member)

    closedSet : S
    closedSet = Iteration.iterUnion

    contains : ⟨ t ∈ˢ closedSet ⟩
    contains = Iteration.iterUnion-in zero t seed-in

    all-valid : ∀ n → ⟨ n ∈ˢ closedSet ⟩ → ⟨ IsName n ⟩
    all-valid n member = PT.rec (snd (IsName n))
      (λ { (k , atStage) → stage-valid k n atStage })
      (Iteration.iterUnion-out n member)

    child-contained : ∀ n → ⟨ n ∈ˢ closedSet ⟩ → ∀ x → Child x n → ⟨ x ∈ˢ closedSet ⟩
    child-contained n member x edge = PT.rec (snd (x ∈ˢ closedSet))
      (λ { (k , atStage) → Iteration.iterUnion-in (suc k) x
        (Step.step-in-child (Iteration.it k) n x atStage edge) })
      (Iteration.iterUnion-out n member)

    closed : Recognizer.Closed closedSet
    closed n member e inN = PT.map
      (λ { (x , b , eq , bB) → x ,
        child-contained n member x ∣ b ,
          subst (λ z → ⟨ z ∈ˢ n ⟩) (eq ∙ entry-bridge x b) inN ∣₁ ,
        ∣ b , bB , eq ∙ entry-bridge x b ∣₁ })
      (name-shape n (all-valid n member) e inN)

    recognized : ⟨ (t ∷ []) ⊨ Recognizer.formula ⟩
    recognized = Recognizer.formula-from-closed closedSet t contains closed

  complete : ∀ t → ⟨ IsName t ⟩ → ⟨ (t ∷ []) ⊨ Recognizer.formula ⟩
  complete t valid = Witness.recognized t valid

  adequate : ∀ t → ((t ∷ []) ⊨ Recognizer.formula) ≡ IsName t
  adequate t = ⇔toPath (Recognizer.formula-sound t) (complete t)
```

