# K0 closed coordinate domain independence

Date: 2026-09-09. Source baseline: `9718c33a`. This continues the [actual powerset recursion tables](k0-powerset-atomic-tables-2026-09.md). K0 remains open. These are temporary safe Agda probes, archived here for reproduction; production `src` is unchanged.

## Statement and scope

Fix an actual L set X and B = P(X). If actual coordinate sets C and D are closed under the material child relation, then their constructed recursion tables give equal values at every ordered pair whose two coordinates belong to both sets. Neither C nor D must contain the other. The theorem concerns the previously constructed powerset expanded equations; it does not yet identify them with a global atomic Boolean equality formula or prove the atomic semantic laws.

The inclusion comparison accepts an arbitrary source-domain membership proof directly. The public shared-coordinate theorem supplies ordinary membership proofs for x,y in each source domain, without converting readout values between generated membership proofs.

The closure premise concerns actual children, independently of name-validity proofs. It is sufficient for this table comparison. Genuine valid names have the previously checked closed-domain constructor; global name semantics still needs its own formula and adequacy interface.

## One comparison proof, reused across domains

The implementation forms E = C ∩ D by internal Separation. An opaque `CommonDomain` result exposes E, its proved equality with the actual intersection, both inclusions, the shared-membership constructor and child closure. Clients use these specifications without repeatedly expanding the intersection construction. E is child-closed. It restricts each actual table to E × E keys while retaining the same B bound. Each restriction is an actual L set with an exact membership specification.

Generic table restriction preserves functionality and downward closure. Preservation of the Step equation is a separate contract: an arbitrary domain-dependent Step need not survive restriction. The powerset adapter proves this contract from the actual expression, so the generic restriction theorem does not assume the desired domain independence.

For this expression, changing a coordinate bound preserves the inner and outer image sets whenever their relevant weighted entries transport between bounds and the corresponding graph or inner-supremum propositions agree. `DomainCongruence` provides that general interface. The old same-domain `Congruence` is now its identity specialization, retaining its public interface and avoiding duplicate witness-mapping proofs.

At a parent in E, child closure proves that every relevant child considered over C lies in E. Inclusion E ⊆ C gives the reverse transport. Inner image equality transports the supremum specification for each candidate value; outer image equality then transports the infimum. Both orientations reuse these components, and equality of the final intersections yields Step transport. This argument requires only E ⊆ C, child closure of E, and parents in E. The source C need not itself be closed for the restriction adapter.

Finally each restricted good table is compared with the canonical recursion table constructed over E, using the existing partial-table agreement theorem. Both values equal that table's value and therefore each other. `BoundedTableRealization` exposes the already proved `partial-agreement` as an opaque result field. No new well-founded comparison induction or second recursion engine is introduced. The final client uses scoped module aliases that expose only the required values, key domains and comparison theorem; it does not re-export both restriction modules' full nested recursion namespaces.

## Choice and abstraction audit

All additional sets are obtained from the existing L operations. Witnesses in image membership and table domains are transported through propositional truncation into propositions or truncated witnesses. The proof does not choose one contributing entry, predecessor value, table or domain from a family. Both source tables and their canonical comparison table are already constructed by the existing bounded engine.

The additional field in the opaque realization record is implemented by the existing engine projection, rather than imposed as a caller premise. The concrete restriction and comparison supply their own graph equivalence and goodness proofs. No host AC, countable/dependent choice, BPI, ultrafilter selector, resizing or additional LEM level is added. This local audit does not establish the eventual T3 constructor's complete assumption budget.

Subsequent evidence: the [arbitrary-good-table and semantic-value probes](k0-good-table-value-relation-2026-09.md) discharge the arbitrary-good-source extension, with no source boundedness premise, and prove unique semantic values with general closed-container existence and a valid-name instance. Closure syntax is checked. The remaining-work list below records this earlier checkpoint; its full fixed graph formula and atomic-law obligations remain open.

## Remaining work

1. Extend the concrete restriction adapter from the constructed source table to an arbitrary bounded good source table, reusing the already generic restriction and expression transport kernels. This is needed to compare arbitrary witnesses of a global graph formula, not only the canonical table constructors. Then define a fixed finite atomic equality formula by quantifying an adequate internal domain and good table. Prove existence, unique-value reading, and agreement with the domain-independent local values. Construct and identify the corresponding membership image.
2. Prove the atomic semantic laws. Domain independence alone does not prove reflexivity, transitivity, substitution or check-name adequacy.
3. Preserve the general admitted-family algebra contracts and instantiate the general Boolean/regular-open framework. The concrete powerset instance is not the Cohen completion.
4. Continue general-ground adapters, quantified value-set bounds, Collection/fullness, ordinary-model extraction and geology. T3 remains an actual ordinary non-CH model after the general forcing results; T4 remains ground definability.

## Verification and source snapshots

From the temporary compile root, each of the following scoped commands exited 0:

```sh
GHCRTS="-A64m -I0 -M8g" agda src/UniformWeightedImage.agda
GHCRTS="-A64m -I0 -M8g" agda src/OuterWeightedImage.agda
GHCRTS="-A64m -I0 -M8g" agda src/ClosedCoordinateDomain.agda
GHCRTS="-A64m -I0 -M8g" agda src/CodedTableRestriction.agda
GHCRTS="-A64m -I0 -M8g" agda src/BoundedTableRealization.agda
GHCRTS="-A64m -I0 -M8g" agda src/PowersetDomainTransport.agda
GHCRTS="-A64m -I0 -M8g" agda src/PowersetTableRestriction.agda
GHCRTS="-A64m -I0 -M8g" agda src/PowersetClosedDomainIndependence.agda
GHCRTS="-A64m -I0 -M8g" agda src/PowersetNameTable.agda
```

The integration checks also rechecked affected imported modules. Coordinator checks covered the closed-coordinate helper, extended generic realization and existing valid-name client; delegated checks covered image generalization, generic restriction and the concrete comparison integration. At most two Agda processes ran concurrently, each with the existing 8 GB heap cap. Two comparison versions with broad module aliases and a prefix diagnostic were interrupted without a result after prolonged elaboration; they are not mathematical counterexamples or completed checks. Packaging the common domain and accepting arbitrary source-key proofs produced a cleaner interface, but the next broad-alias full check still ran for more than eight minutes. A complete `PowersetClosedDomainThin` diagnostic with the same proof and narrowly scoped aliases then exited 0 while that check was still running. The final named probe adopts those scoped aliases and was checked separately, exiting 0 in 5.2 seconds as reported by the checking agent. The strengthened restriction check exited 0 in about four minutes and twenty-five seconds. This preserves the statement and proof while avoiding the large auxiliary namespace exposure. The listed final commands apply to that revised source.

Scoped prose/glossary gates, exact snapshot/hash and relative-link checks, and `git diff --check` passed. All 123 tracked production source files and their probe-baseline copies match `9718c33a` byte-for-byte. Whole-tree and chapter gates were not run for this temporary-probe/documentation change.

### UniformWeightedImage.agda

SHA-256: `cdf471a5ee888dd153ec8ff90059725b4d439fec94aa6156d358c97c8120b30c`.

```text
{-# OPTIONS --cubical --safe --guardedness #-}

open import Base.Prelude
open import Base.Truth
open import Base.Classical using ( LEM )

module UniformWeightedImage {ℓ : Level} (lem : LEM (ℓ-suc ℓ)) where

open import FOL.ZFStructure using ( module hPropStructure )
open import FOL.Syntax using ( Formula; var; _∈̇_; _∧̇_; _⇒̇_; ∀̇_ )
open import L.Constructible {ℓ} using ( 𝒮ʟ )
open import FOL.Semantics (hPropAlgebra (ℓ-suc ℓ)) 𝒮ʟ using ( module At )
import FOL.ZFModel as Model
open import L.Model {ℓ} lem using ( L⊨ZF )
open import L.Coding.Model {ℓ} using ( prʟ; prAtL )
open import PairFormulaReading {ℓ} using ( reading )
import IndexedWeightedImage {ℓ} as Indexed
open import FormulaParameters (hPropAlgebra (ℓ-suc ℓ)) 𝒮ʟ using ( specialize; specialize-reading )
open import Cubical.Functions.Logic using ( ⇔toPath )
import Cubical.HITs.PropositionalTruncation as PT

open hPropStructure 𝒮ʟ using ( S; _∈ˢ_; isSetS )
open At S id using ( _⊨_ )
open TruthAlgebra (hPropAlgebra (ℓ-suc ℓ))

opaque
  actualL : Model.isZFModel 𝒮ʟ
  actualL = L⊨ZF

module Ground = Model.isZFModel actualL

module WithKey
  (Key : S → S → S)
  (keyAt : ∀ {n} → Fin n → Fin n → Fin n → Formula S n)
  (key-reading : ∀ {n} (q f v : Fin n) (γ : Vec S n)
    → (γ ⊨ keyAt q f v)
      ≡ ((lookup q γ ≡ Key (lookup f γ) (lookup v γ)) ,
         isSetS (lookup q γ) (Key (lookup f γ) (lookup v γ)))) where

  module WithOperation
    (Op : S → S → S → hProp (ℓ-suc ℓ))
    (opAt : ∀ {n} → Fin n → Fin n → Fin n → Formula S n)
    (op-reading : ∀ {n} (c d z : Fin n) (γ : Vec S n)
      → (γ ⊨ opAt c d z) ≡ Op (lookup c γ) (lookup d γ) (lookup z γ)) where

    module Syntax = Indexed.WithKey.WithOperation Key keyAt key-reading Op opAt op-reading

    template : Formula S 6
    template = Syntax.imageAt zero (suc zero) (suc (suc zero))
      (suc (suc (suc zero))) (suc (suc (suc (suc zero))))
      (suc (suc (suc (suc (suc zero)))))

    module Construction (C B parent H f : S) where

      parameters : Vec S 5
      parameters = C ∷ B ∷ parent ∷ H ∷ f ∷ []

      formula : Formula S 1
      formula = specialize parameters template

      Witness : S → Type (ℓ-suc ℓ)
      Witness = Syntax.truncatedWitness C B parent H f

      formula-reading : ∀ z → ((z ∷ []) ⊨ formula) ≡ (Witness z , PT.squash₁)
      formula-reading z = specialize-reading parameters template z
        ∙ Syntax.imageAt-reading zero (suc zero) (suc (suc zero))
          (suc (suc (suc zero))) (suc (suc (suc (suc zero))))
          (suc (suc (suc (suc (suc zero)))) )
          (C ∷ B ∷ parent ∷ H ∷ f ∷ z ∷ [])

      image : S
      image = Ground.separate B formula

      separated : ∀ z → ⟨ z ∈ˢ image ⟩
        → ⟨ z ∈ˢ B ⟩ × ⟨ (z ∷ []) ⊨ formula ⟩
      separated z member = subst ⟨_⟩ (Ground.separate-spec B formula z) member

      image-out : ∀ z → ⟨ z ∈ˢ image ⟩ → ⟨ z ∈ˢ B ⟩ × Witness z
      image-out z member = fst (separated z member) ,
        subst ⟨_⟩ (formula-reading z) (snd (separated z member))

      image-in : ∀ z → ⟨ z ∈ˢ B ⟩ → Witness z → ⟨ z ∈ˢ image ⟩
      image-in z zB witness = subst ⟨_⟩ (sym (Ground.separate-spec B formula z))
        (zB , subst ⟨_⟩ (sym (formula-reading z)) witness)

      image-membership : ∀ z → (z ∈ˢ image) ≡ ((z ∈ˢ B) ⊓ (Witness z , PT.squash₁))
      image-membership z = ⇔toPath (image-out z)
        (λ { (zB , witness) → image-in z zB witness })

    imageSetAt : ∀ {n} → Fin n → Fin n → Fin n → Fin n → Fin n → Fin n
      → Formula S n
    imageSetAt I C B parent H f = ∀̇
      (((var zero ∈̇ var (suc I)) ⇒̇
        ((var zero ∈̇ var (suc B)) ∧̇ Syntax.imageAt (suc C) (suc B)
          (suc parent) (suc H) (suc f) zero)) ∧̇
       (((var zero ∈̇ var (suc B)) ∧̇ Syntax.imageAt (suc C) (suc B)
          (suc parent) (suc H) (suc f) zero) ⇒̇ (var zero ∈̇ var (suc I))))

    module Description {n : ℕ} (I C B parent H f : Fin n) (γ : Vec S n) where

      module Actual = Construction (lookup C γ) (lookup B γ) (lookup parent γ)
        (lookup H γ) (lookup f γ)

      out : ⟨ γ ⊨ imageSetAt I C B parent H f ⟩ → lookup I γ ≡ Actual.image
      out holds = Ground.extensional λ z → ⇔toPath
        (λ member → Actual.image-in z (fst (fst (holds z) member))
          (Syntax.imageAt-out (suc C) (suc B) (suc parent) (suc H) (suc f) zero
            (z ∷ γ) (snd (fst (holds z) member))))
        (λ member → snd (holds z) (fst (Actual.image-out z member) ,
          Syntax.imageAt-in (suc C) (suc B) (suc parent) (suc H) (suc f) zero
            (z ∷ γ) (snd (Actual.image-out z member))))

      into : lookup I γ ≡ Actual.image → ⟨ γ ⊨ imageSetAt I C B parent H f ⟩
      into eq z =
        (λ member → fst (Actual.image-out z (subst (λ A → ⟨ z ∈ˢ A ⟩) eq member)) ,
          Syntax.imageAt-in (suc C) (suc B) (suc parent) (suc H) (suc f) zero
            (z ∷ γ) (snd (Actual.image-out z (subst (λ A → ⟨ z ∈ˢ A ⟩) eq member)))) ,
        (λ { (zB , witness) → subst (λ A → ⟨ z ∈ˢ A ⟩) (sym eq)
          (Actual.image-in z zB (Syntax.imageAt-out (suc C) (suc B)
            (suc parent) (suc H) (suc f) zero (z ∷ γ) witness)) })

      exact : (γ ⊨ imageSetAt I C B parent H f)
        ≡ ((lookup I γ ≡ Actual.image) , isSetS (lookup I γ) Actual.image)
      exact = ⇔toPath out into

    module DomainCongruence (C D B parent H K f : S)
      (support-forward : ∀ v c → ⟨ v ∈ˢ C ⟩ → ⟨ c ∈ˢ B ⟩
        → ⟨ prʟ v c ∈ˢ parent ⟩ → ⟨ v ∈ˢ D ⟩)
      (support-backward : ∀ v c → ⟨ v ∈ˢ D ⟩ → ⟨ c ∈ˢ B ⟩
        → ⟨ prʟ v c ∈ˢ parent ⟩ → ⟨ v ∈ˢ C ⟩)
      (agrees : ∀ v c d → ⟨ v ∈ˢ C ⟩ → ⟨ v ∈ˢ D ⟩
        → ⟨ c ∈ˢ B ⟩ → ⟨ d ∈ˢ B ⟩ → ⟨ prʟ v c ∈ˢ parent ⟩
        → (⟨ prʟ (Key f v) d ∈ˢ H ⟩ → ⟨ prʟ (Key f v) d ∈ˢ K ⟩)
          × (⟨ prʟ (Key f v) d ∈ˢ K ⟩ → ⟨ prʟ (Key f v) d ∈ˢ H ⟩)) where

      module Left = Construction C B parent H f
      module Right = Construction D B parent K f

      forward : ∀ z → ⟨ z ∈ˢ Left.image ⟩ → ⟨ z ∈ˢ Right.image ⟩
      forward z member = Right.image-in z (fst (Left.image-out z member))
        (PT.map (λ { (v , c , d , vC , cB , dB , vc , hd , op) →
          let vD = support-forward v c vC cB vc
          in v , c , d , vD , cB , dB , vc ,
            fst (agrees v c d vC vD cB dB vc) hd , op })
          (snd (Left.image-out z member)))

      backward : ∀ z → ⟨ z ∈ˢ Right.image ⟩ → ⟨ z ∈ˢ Left.image ⟩
      backward z member = Left.image-in z (fst (Right.image-out z member))
        (PT.map (λ { (v , c , d , vD , cB , dB , vc , kd , op) →
          let vC = support-backward v c vD cB vc
          in v , c , d , vC , cB , dB , vc ,
            snd (agrees v c d vC vD cB dB vc) kd , op })
          (snd (Right.image-out z member)))

      image-equal : Left.image ≡ Right.image
      image-equal = Ground.extensional (λ z → ⇔toPath (forward z) (backward z))

    module Congruence (C B parent H K f : S)
      (agrees : ∀ v c d → ⟨ v ∈ˢ C ⟩ → ⟨ c ∈ˢ B ⟩ → ⟨ d ∈ˢ B ⟩
        → ⟨ prʟ v c ∈ˢ parent ⟩
        → (⟨ prʟ (Key f v) d ∈ˢ H ⟩ → ⟨ prʟ (Key f v) d ∈ˢ K ⟩)
          × (⟨ prʟ (Key f v) d ∈ˢ K ⟩ → ⟨ prʟ (Key f v) d ∈ˢ H ⟩)) where

      module General = DomainCongruence C C B parent H K f
        (λ v c vC cB vc → vC) (λ v c vC cB vc → vC)
        (λ v c d vC vD cB dB vc → agrees v c d vC cB dB vc)
      module Left = General.Left
      module Right = General.Right
      open General public using ( forward; backward; image-equal )

module ForwardKey = WithKey prʟ prAtL reading
module ReverseKey = WithKey (λ f v → prʟ v f) Indexed.reverseKeyAt Indexed.reverse-key-reading
```

### OuterWeightedImage.agda

SHA-256: `48db0d8f753718ab2454bce883c1a8609241d87edbc48fc3d9c9d01cd5b54be5`.

```text
{-# OPTIONS --cubical --safe --guardedness #-}

open import Base.Prelude
open import Base.Truth
open import Base.Classical using ( LEM )

module OuterWeightedImage {ℓ : Level} (lem : LEM (ℓ-suc ℓ)) where

open import FOL.ZFStructure using ( module hPropStructure )
open import FOL.Syntax using ( Formula; var; _∧̇_; ∃̇∈ )
open import L.Constructible {ℓ} using ( 𝒮ʟ )
open import FOL.Semantics (hPropAlgebra (ℓ-suc ℓ)) 𝒮ʟ using ( module At )
open import L.Coding.Model {ℓ} using ( prʟ )
open import CodedTableFunctionality {ℓ} using ( entryAt; entry-reading )
open import FormulaParameters (hPropAlgebra (ℓ-suc ℓ)) 𝒮ʟ using ( specialize; specialize-reading )
import InternalPowersetSupremum {ℓ} lem as Powersets
open import Cubical.Functions.Logic using ( ⇔toPath )
import Cubical.HITs.PropositionalTruncation as PT
open PT using ( ∥_∥₁; ∣_∣₁ )

open hPropStructure 𝒮ʟ using ( S; _∈ˢ_ )
open At S id using ( _⊨_ )
open TruthAlgebra (hPropAlgebra (ℓ-suc ℓ))
module Ground = Powersets.Ground

shiftThree : ∀ {n} → Fin n → Fin (suc (suc (suc n)))
shiftThree i = suc (suc (suc i))

module WithInner
  (Inner : S → S → S → S → S → S → hProp (ℓ-suc ℓ))
  (innerAt : ∀ {n} → Fin n → Fin n → Fin n → Fin n → Fin n → Fin n → Formula S n)
  (inner-reading : ∀ {n} (C B parent H f j : Fin n) (γ : Vec S n)
    → (γ ⊨ innerAt C B parent H f j)
      ≡ Inner (lookup C γ) (lookup B γ) (lookup parent γ) (lookup H γ) (lookup f γ) (lookup j γ)) where

  module WithOperation
    (Op : S → S → S → S → hProp (ℓ-suc ℓ))
    (opAt : ∀ {n} → Fin n → Fin n → Fin n → Fin n → Formula S n)
    (op-reading : ∀ {n} (X a j z : Fin n) (γ : Vec S n)
      → (γ ⊨ opAt X a j z) ≡ Op (lookup X γ) (lookup a γ) (lookup j γ) (lookup z γ)) where

    imageAt : ∀ {n} → Fin n → Fin n → Fin n → Fin n → Fin n → Fin n → Fin n → Formula S n
    imageAt X C B outer inner H z = ∃̇∈ (var C) (∃̇∈ (var (suc B))
      (∃̇∈ (var (suc (suc B)))
        (entryAt (shiftThree outer) (suc (suc zero)) (suc zero) ∧̇
        (innerAt (shiftThree C) (shiftThree B) (shiftThree inner) (shiftThree H)
          (suc (suc zero)) zero ∧̇ opAt (shiftThree X) (suc zero) zero (shiftThree z)))))

    Witness : S → S → S → S → S → S → S → Type (ℓ-suc ℓ)
    Witness X C B outer inner H z = ∥ Σ[ u ∈ S ] Σ[ a ∈ S ] Σ[ j ∈ S ]
      (⟨ u ∈ˢ C ⟩ × ⟨ a ∈ˢ B ⟩ × ⟨ j ∈ˢ B ⟩ × ⟨ prʟ u a ∈ˢ outer ⟩
        × ⟨ Inner C B inner H u j ⟩ × ⟨ Op X a j z ⟩) ∥₁

    out : ∀ {n} (X C B outer inner H z : Fin n) (γ : Vec S n)
      → ⟨ γ ⊨ imageAt X C B outer inner H z ⟩
      → Witness (lookup X γ) (lookup C γ) (lookup B γ) (lookup outer γ)
          (lookup inner γ) (lookup H γ) (lookup z γ)
    out X C B outer inner H z γ = PT.rec PT.squash₁ λ { (u , uC , rest) →
      PT.rec PT.squash₁ (λ { (a , aB , rest) → PT.map
        (λ { (j , jB , entry , val , op) → u , a , j , uC , aB , jB ,
          subst ⟨_⟩ (entry-reading (shiftThree outer) (suc (suc zero)) (suc zero)
            (j ∷ a ∷ u ∷ γ)) entry ,
          subst ⟨_⟩ (inner-reading (shiftThree C) (shiftThree B) (shiftThree inner)
            (shiftThree H) (suc (suc zero)) zero (j ∷ a ∷ u ∷ γ)) val ,
          subst ⟨_⟩ (op-reading (shiftThree X) (suc zero) zero (shiftThree z)
            (j ∷ a ∷ u ∷ γ)) op }) rest }) rest }

    into : ∀ {n} (X C B outer inner H z : Fin n) (γ : Vec S n)
      → Witness (lookup X γ) (lookup C γ) (lookup B γ) (lookup outer γ)
          (lookup inner γ) (lookup H γ) (lookup z γ)
      → ⟨ γ ⊨ imageAt X C B outer inner H z ⟩
    into X C B outer inner H z γ = PT.map λ { (u , a , j , uC , aB , jB , entry , val , op) →
      u , uC , ∣ a , aB , ∣ j , jB ,
        subst ⟨_⟩ (sym (entry-reading (shiftThree outer) (suc (suc zero)) (suc zero)
          (j ∷ a ∷ u ∷ γ))) entry ,
        subst ⟨_⟩ (sym (inner-reading (shiftThree C) (shiftThree B) (shiftThree inner)
          (shiftThree H) (suc (suc zero)) zero (j ∷ a ∷ u ∷ γ))) val ,
        subst ⟨_⟩ (sym (op-reading (shiftThree X) (suc zero) zero (shiftThree z)
          (j ∷ a ∷ u ∷ γ))) op ∣₁ ∣₁ }

    image-reading : ∀ {n} (X C B outer inner H z : Fin n) (γ : Vec S n)
      → (γ ⊨ imageAt X C B outer inner H z)
        ≡ (Witness (lookup X γ) (lookup C γ) (lookup B γ) (lookup outer γ)
          (lookup inner γ) (lookup H γ) (lookup z γ) , PT.squash₁)
    image-reading X C B outer inner H z γ = ⇔toPath
      (out X C B outer inner H z γ) (into X C B outer inner H z γ)

    template : Formula S 7
    template = imageAt zero (suc zero) (suc (suc zero)) (suc (suc (suc zero)))
      (suc (suc (suc (suc zero)))) (suc (suc (suc (suc (suc zero)))))
      (suc (suc (suc (suc (suc (suc zero))))))

    module Construction (X C B outer inner H : S) where

      parameters : Vec S 6
      parameters = X ∷ C ∷ B ∷ outer ∷ inner ∷ H ∷ []

      formula : Formula S 1
      formula = specialize parameters template

      formula-reading : ∀ z → ((z ∷ []) ⊨ formula)
        ≡ (Witness X C B outer inner H z , PT.squash₁)
      formula-reading z = specialize-reading parameters template z ∙
        image-reading zero (suc zero) (suc (suc zero)) (suc (suc (suc zero)))
          (suc (suc (suc (suc zero)))) (suc (suc (suc (suc (suc zero)))))
          (suc (suc (suc (suc (suc (suc zero))))))
          (X ∷ C ∷ B ∷ outer ∷ inner ∷ H ∷ z ∷ [])

      image : S
      image = Ground.separate B formula

      separated : ∀ z → ⟨ z ∈ˢ image ⟩ → ⟨ z ∈ˢ B ⟩ × ⟨ (z ∷ []) ⊨ formula ⟩
      separated z member = subst ⟨_⟩ (Ground.separate-spec B formula z) member

      image-out : ∀ z → ⟨ z ∈ˢ image ⟩ → ⟨ z ∈ˢ B ⟩ × Witness X C B outer inner H z
      image-out z member = fst (separated z member) ,
        subst ⟨_⟩ (formula-reading z) (snd (separated z member))

      image-in : ∀ z → ⟨ z ∈ˢ B ⟩ → Witness X C B outer inner H z → ⟨ z ∈ˢ image ⟩
      image-in z zB witness = subst ⟨_⟩ (sym (Ground.separate-spec B formula z))
        (zB , subst ⟨_⟩ (sym (formula-reading z)) witness)

    module DomainCongruence (X C D B outer inner H K : S)
      (support-forward : ∀ u a → ⟨ u ∈ˢ C ⟩ → ⟨ a ∈ˢ B ⟩
        → ⟨ prʟ u a ∈ˢ outer ⟩ → ⟨ u ∈ˢ D ⟩)
      (support-backward : ∀ u a → ⟨ u ∈ˢ D ⟩ → ⟨ a ∈ˢ B ⟩
        → ⟨ prʟ u a ∈ˢ outer ⟩ → ⟨ u ∈ˢ C ⟩)
      (agrees : ∀ u a j → ⟨ u ∈ˢ C ⟩ → ⟨ u ∈ˢ D ⟩
        → ⟨ a ∈ˢ B ⟩ → ⟨ j ∈ˢ B ⟩ → ⟨ prʟ u a ∈ˢ outer ⟩
        → (⟨ Inner C B inner H u j ⟩ → ⟨ Inner D B inner K u j ⟩)
          × (⟨ Inner D B inner K u j ⟩ → ⟨ Inner C B inner H u j ⟩)) where

      module Left = Construction X C B outer inner H
      module Right = Construction X D B outer inner K

      forward : ∀ z → ⟨ z ∈ˢ Left.image ⟩ → ⟨ z ∈ˢ Right.image ⟩
      forward z member = Right.image-in z (fst (Left.image-out z member))
        (PT.map (λ { (u , a , j , uC , aB , jB , entry , val , op) →
          let uD = support-forward u a uC aB entry
          in u , a , j , uD , aB , jB , entry ,
            fst (agrees u a j uC uD aB jB entry) val , op })
          (snd (Left.image-out z member)))

      backward : ∀ z → ⟨ z ∈ˢ Right.image ⟩ → ⟨ z ∈ˢ Left.image ⟩
      backward z member = Left.image-in z (fst (Right.image-out z member))
        (PT.map (λ { (u , a , j , uD , aB , jB , entry , val , op) →
          let uC = support-backward u a uD aB entry
          in u , a , j , uC , aB , jB , entry ,
            snd (agrees u a j uC uD aB jB entry) val , op })
          (snd (Right.image-out z member)))

      image-equal : Left.image ≡ Right.image
      image-equal = Ground.extensional (λ z → ⇔toPath (forward z) (backward z))

    module Congruence (X C B outer inner H K : S)
      (agrees : ∀ u a j → ⟨ u ∈ˢ C ⟩ → ⟨ a ∈ˢ B ⟩ → ⟨ j ∈ˢ B ⟩
        → ⟨ prʟ u a ∈ˢ outer ⟩
        → (⟨ Inner C B inner H u j ⟩ → ⟨ Inner C B inner K u j ⟩)
          × (⟨ Inner C B inner K u j ⟩ → ⟨ Inner C B inner H u j ⟩)) where

      module General = DomainCongruence X C C B outer inner H K
        (λ u a uC aB entry → uC) (λ u a uC aB entry → uC)
        (λ u a j uC uD aB jB entry → agrees u a j uC aB jB entry)
      module Left = General.Left
      module Right = General.Right
      open General public using ( forward; backward; image-equal )
```

### ClosedCoordinateDomain.agda

SHA-256: `f85c33e2bd4a857d189c8e6e5d1357a19dece3ac8db35c5f5a9e66b7ab6d4b6f`.

```text
{-# OPTIONS --cubical --safe --guardedness #-}

open import Base.Prelude
open import Base.Truth
open import Base.Classical using ( LEM )

module ClosedCoordinateDomain {ℓ : Level} (lem : LEM (ℓ-suc ℓ)) where

open import FOL.ZFStructure using ( module hPropStructure )
open import L.Constructible {ℓ} using ( 𝒮ʟ )
open import NameClosureDown lem using ( Child )
import NamePairDependency {ℓ} lem as Dependency
import InternalIntersection {ℓ} lem as Intersection
import Cubical.HITs.PropositionalTruncation as PT

open hPropStructure 𝒮ʟ using ( S; _∈ˢ_ )

Subset : S → S → Type (ℓ-suc ℓ)
Subset E C = ∀ z → ⟨ z ∈ˢ E ⟩ → ⟨ z ∈ˢ C ⟩

Closed : S → Type (ℓ-suc ℓ)
Closed C = ∀ n → ⟨ n ∈ˢ C ⟩ → ∀ z → Child z n → ⟨ z ∈ˢ C ⟩

module Inclusion (C E : S) (subset : Subset E C) where

  module Source = Dependency.Domain E
  module Target = Dependency.Domain C

  keys : ∀ p → ⟨ p ∈ˢ Source.Product.product ⟩ → ⟨ p ∈ˢ Target.Product.product ⟩
  keys p member = Target.Product.product-in p
    (PT.map (λ { (x , y , xE , yE , eq) → x , y , subset x xE , subset y yE , eq })
      (Source.Product.product-out p member))

record CommonDomain (C D : S) : Type (ℓ-suc ℓ) where
  field
    E : S
    intersection-equation : E ≡ Intersection.intersection C D
    left : Subset E C
    right : Subset E D
    into : ∀ z → ⟨ z ∈ˢ C ⟩ → ⟨ z ∈ˢ D ⟩ → ⟨ z ∈ˢ E ⟩
    closed : Closed E

opaque
  common : ∀ C D → Closed C → Closed D → CommonDomain C D
  common C D closedC closedD = record
    { E = Intersection.intersection C D
    ; intersection-equation = refl
    ; left = λ z member → fst (Intersection.intersection-out z C D member)
    ; right = λ z member → snd (Intersection.intersection-out z C D member)
    ; into = λ z → Intersection.intersection-in z C D
    ; closed = λ n member z edge → Intersection.intersection-in z C D
        (closedC n (fst (Intersection.intersection-out n C D member)) z edge)
        (closedD n (snd (Intersection.intersection-out n C D member)) z edge)
    }

module Common (C D : S) (closedC : Closed C) (closedD : Closed D) where

  open CommonDomain (common C D closedC closedD) public

  module LeftKeys = Inclusion C E left
  module RightKeys = Inclusion D E right
```

### CodedTableRestriction.agda

SHA-256: `b14394d880f9c661d10f3dcb06ee1224e1b219701eb3b5f63e7305a482a17b59`.

```text
{-# OPTIONS --cubical --safe --guardedness #-}

open import Base.Prelude
open import Base.Truth
open import Base.Classical using ( LEM )

module CodedTableRestriction {ℓ : Level} (lem : LEM (ℓ-suc ℓ)) where

open import FOL.ZFStructure using ( module hPropStructure )
open import FOL.Syntax using ( Formula; var; con; _∈̇_ )
open import L.Constructible {ℓ} using ( 𝒮ʟ )
open import L.Coding.Model {ℓ} using ( prʟ )
import ProductSet
import CodedStepExtension
import CodedTableCompatibility
import CodedTableFunctionality
open import Cubical.Functions.Logic using ( ⇔toPath )
import Cubical.HITs.PropositionalTruncation as PT
open PT using ( ∥_∥₁; ∣_∣₁ )

open TruthAlgebra (hPropAlgebra (ℓ-suc ℓ))
open hPropStructure 𝒮ʟ using ( S; _∈ˢ_ )
module Ground = ProductSet.Ground lem
module Compatibility = CodedTableCompatibility lem
module StepExtension = CodedStepExtension lem

Good : (D B : S) → (S → S → hProp (ℓ-suc ℓ))
  → (S → S → S → hProp (ℓ-suc ℓ)) → S → Type (ℓ-suc ℓ)
Good D B R Step H = Compatibility.Construction.Good D B R Step H

module Construction (E B H : S) where

  module Product = ProductSet.Construction lem E B

  formula : Formula S 1
  formula = var zero ∈̇ con Product.product

  restricted : S
  restricted = Ground.separate H formula

  membership : ∀ e → (e ∈ˢ restricted) ≡ ((e ∈ˢ H) ⊓ (e ∈ˢ Product.product))
  membership e = Ground.separate-spec H formula e

  graph-out : ∀ p b → ⟨ prʟ p b ∈ˢ restricted ⟩
    → ⟨ p ∈ˢ E ⟩ × ⟨ b ∈ˢ B ⟩ × ⟨ prʟ p b ∈ˢ H ⟩
  graph-out p b graph =
    fst (Product.pair-out p b (snd parts)) ,
    snd (Product.pair-out p b (snd parts)) , fst parts
    where
    parts : ⟨ prʟ p b ∈ˢ H ⟩ × ⟨ prʟ p b ∈ˢ Product.product ⟩
    parts = subst ⟨_⟩ (membership (prʟ p b)) graph

  graph-in : ∀ p b → ⟨ p ∈ˢ E ⟩ → ⟨ b ∈ˢ B ⟩ → ⟨ prʟ p b ∈ˢ H ⟩
    → ⟨ prʟ p b ∈ˢ restricted ⟩
  graph-in p b pE bB graph = subst ⟨_⟩
    (sym (membership (prʟ p b))) (graph , Product.pair-in p b pE bB)

  bounded : ∀ e → ⟨ e ∈ˢ restricted ⟩ → ⟨ e ∈ˢ Product.product ⟩
  bounded e member = snd (subst ⟨_⟩ (membership e) member)

module Preservation (D E B : S) (R : S → S → hProp (ℓ-suc ℓ))
  (StepD StepE : S → S → S → hProp (ℓ-suc ℓ))
  (subset : ∀ p → ⟨ p ∈ˢ E ⟩ → ⟨ p ∈ˢ D ⟩)
  (actualH : S)
  (goodH : Good D B R StepD actualH)
  (transport : ∀ p b → ⟨ p ∈ˢ E ⟩ → ⟨ b ∈ˢ B ⟩
    → ⟨ prʟ p b ∈ˢ actualH ⟩ → ⟨ StepD actualH p b ⟩
    → ⟨ StepE (Construction.restricted E B actualH) p b ⟩) where

  module Restriction = Construction E B actualH
  module Source = Compatibility.Construction D B R StepD
  module Target = Compatibility.Construction E B R StepE
  module TargetFunctionality = CodedTableFunctionality.Construction E B
  module SourceLaws = StepExtension.Laws D B R StepD
  module TargetLaws = StepExtension.Laws E B R StepE

  functional : TargetFunctionality.Functional Restriction.restricted
  functional p b c pE bB cB pb pc = fst goodH p b c (subset p pE) bB cB
    (snd (snd (Restriction.graph-out p b pb)))
    (snd (snd (Restriction.graph-out p c pc)))

  downward : TargetLaws.Downward Restriction.restricted
  downward p q pE qE domain relation = PT.rec PT.squash₁ descend domain
    where
    descend : Σ[ b ∈ S ] (⟨ b ∈ˢ B ⟩ × ⟨ prʟ p b ∈ˢ Restriction.restricted ⟩)
      → TargetLaws.Domain Restriction.restricted q
    descend (b , bB , graph) = PT.map
      (λ { (c , cB , sourceGraph) →
        c , cB , Restriction.graph-in q c qE cB sourceGraph })
      (fst (snd goodH) p q (subset p pE) (subset q qE)
        ∣ b , bB , snd (snd (Restriction.graph-out p b graph)) ∣₁ relation)

  obeys : TargetLaws.Obeys Restriction.restricted
  obeys p b pE bB graph = transport p b pE bB sourceGraph
    (snd (snd goodH) p b (subset p pE) bB sourceGraph)
    where
    sourceGraph : ⟨ prʟ p b ∈ˢ actualH ⟩
    sourceGraph = snd (snd (Restriction.graph-out p b graph))

  good : Target.Good Restriction.restricted
  good = functional , downward , obeys
```

### BoundedTableRealization.agda

SHA-256: `88ec07c3f69e66a6f411dfad53915a725f79e1564e161a0909c8a896e5193060`.

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
        partial-agreement : ∀ H → Bounded H → Recursor.Base.Good.Good H
          → ∀ p pD b → ⟨ b ∈ˢ B ⟩ → ⟨ prʟ p b ∈ˢ H ⟩ → b ≡ value p pD

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
        ; partial-agreement = Recursor.Solve.partial-agreement unique locality wf admit
        }
```

### PowersetDomainTransport.agda

SHA-256: `42fca3e9d7caba78a6a10f5feb26e2e598c4241735741cfb37664b67973aacb2`.

```text
{-# OPTIONS --cubical --safe --guardedness #-}

open import Base.Prelude
open import Base.Truth
open import Base.Classical using ( LEM )

module PowersetDomainTransport {ℓ : Level} (lem : LEM (ℓ-suc ℓ)) where

open import FOL.ZFStructure using ( module hPropStructure )
open import FOL.Syntax using ( Formula )
open import L.Constructible {ℓ} using ( 𝒮ʟ )
open import FOL.Semantics (hPropAlgebra (ℓ-suc ℓ)) 𝒮ʟ using ( module At )
open import L.Coding.Model {ℓ} using ( prʟ; prAtL )
open import PairFormulaReading {ℓ} using ( reading )
open import NameClosureDown lem using ( Child )
import ClosedCoordinateDomain {ℓ} lem as Domain
import PowersetStepFormula {ℓ} lem as Steps
import PowersetAtomicExpression {ℓ} lem as Expressions
import IndexedWeightedImage {ℓ} as Keys
import InternalIntersection {ℓ} lem as Intersection
open import Cubical.HITs.PropositionalTruncation using ( ∣_∣₁ )

open hPropStructure 𝒮ʟ using ( S; _∈ˢ_; isSetS )
open At S id using ( _⊨_ )

module For (X : S) where

  module Step = Steps.For X
  module Expression = Expressions.For X
  open Expression.Algebra using ( B )

  module Transport (C E x y H K : S)
    (subset : Domain.Subset E C)
    (closed : Domain.Closed E)
    (xE : ⟨ x ∈ˢ E ⟩)
    (yE : ⟨ y ∈ˢ E ⟩)
    (agrees : ∀ u v d → ⟨ u ∈ˢ E ⟩ → ⟨ v ∈ˢ E ⟩ → ⟨ d ∈ˢ B ⟩
      → (⟨ prʟ (prʟ u v) d ∈ˢ H ⟩ → ⟨ prʟ (prʟ u v) d ∈ˢ K ⟩)
        × (⟨ prʟ (prʟ u v) d ∈ˢ K ⟩ → ⟨ prʟ (prʟ u v) d ∈ˢ H ⟩)) where

    module Branch
      (Key : S → S → S)
      (keyAt : ∀ {n} → Fin n → Fin n → Fin n → Formula S n)
      (key-reading : ∀ {n} (q f v : Fin n) (γ : Vec S n)
        → (γ ⊨ keyAt q f v) ≡ ((lookup q γ ≡ Key (lookup f γ) (lookup v γ)) ,
          isSetS (lookup q γ) (Key (lookup f γ) (lookup v γ))))
      (parent inner : S)
      (parentE : ⟨ parent ∈ˢ E ⟩)
      (innerE : ⟨ inner ∈ˢ E ⟩)
      (key-agrees : ∀ u v d → ⟨ u ∈ˢ E ⟩ → ⟨ v ∈ˢ E ⟩ → ⟨ d ∈ˢ B ⟩
        → (⟨ prʟ (Key u v) d ∈ˢ H ⟩ → ⟨ prʟ (Key u v) d ∈ˢ K ⟩)
          × (⟨ prʟ (Key u v) d ∈ˢ K ⟩ → ⟨ prʟ (Key u v) d ∈ˢ H ⟩)) where

      module Atomic = Expression.WithKey Key keyAt key-reading

      support : ∀ u a → ⟨ u ∈ˢ C ⟩ → ⟨ a ∈ˢ B ⟩
        → ⟨ prʟ u a ∈ˢ parent ⟩ → ⟨ u ∈ˢ E ⟩
      support u a uC aB entry = closed parent parentE u (∣ a , entry ∣₁)

      module InnerEquality (u a : S) (uC : ⟨ u ∈ˢ C ⟩) (uE : ⟨ u ∈ˢ E ⟩)
        (aB : ⟨ a ∈ˢ B ⟩) (entry : ⟨ prʟ u a ∈ˢ parent ⟩) where

        module Equality = Atomic.Values.Operations.Image.DomainCongruence
          C E B inner H K u
          (λ v c vC cB vc → closed inner innerE v (∣ c , vc ∣₁))
          (λ v c vE cB vc → subset v vE)
          (λ v c d vC vE cB dB vc → key-agrees u v d uE vE dB)

        equivalent : ∀ j
          → (⟨ Atomic.Inner C B inner H u j ⟩ → ⟨ Atomic.Inner E B inner K u j ⟩)
          × (⟨ Atomic.Inner E B inner K u j ⟩ → ⟨ Atomic.Inner C B inner H u j ⟩)
        equivalent j =
          subst (λ A → Atomic.Values.Result.Sup.Supremum B A j) Equality.image-equal ,
          subst (λ A → Atomic.Values.Result.Sup.Supremum B A j) (sym Equality.image-equal)

      inner-agreement : ∀ u a j → ⟨ u ∈ˢ C ⟩ → ⟨ u ∈ˢ E ⟩
        → ⟨ a ∈ˢ B ⟩ → ⟨ j ∈ˢ B ⟩ → ⟨ prʟ u a ∈ˢ parent ⟩
        → (⟨ Atomic.Inner C B inner H u j ⟩ → ⟨ Atomic.Inner E B inner K u j ⟩)
          × (⟨ Atomic.Inner E B inner K u j ⟩ → ⟨ Atomic.Inner C B inner H u j ⟩)
      inner-agreement u a j uC uE aB jB entry =
        InnerEquality.equivalent u a uC uE aB entry j

      module ImageEquality = Atomic.Images.DomainCongruence X C E B parent inner H K
        support (λ u a uE aB entry → subset u uE) inner-agreement

      module Left = Atomic.Construction C parent inner H
      module Right = Atomic.Construction E parent inner K

      value-equal : Left.value ≡ Right.value
      value-equal = cong Expression.Bounds.infimum ImageEquality.image-equal

    module ForwardBranch = Branch prʟ prAtL reading x y xE yE agrees
    module ReverseBranch = Branch (λ u v → prʟ v u) Keys.reverseKeyAt Keys.reverse-key-reading
      y x yE xE (λ u v d uE vE dB → agrees v u d vE uE dB)

    forward-value-equal : ForwardBranch.Left.value ≡ ForwardBranch.Right.value
    forward-value-equal = ForwardBranch.value-equal

    reverse-value-equal : ReverseBranch.Left.value ≡ ReverseBranch.Right.value
    reverse-value-equal = ReverseBranch.value-equal

    module Left = Expression.Expression C x y H
    module Right = Expression.Expression E x y K

    expression-equal : Left.value ≡ Right.value
    expression-equal = cong₂ Intersection.intersection forward-value-equal reverse-value-equal

    transfer : ∀ b → ⟨ Step.Step C x y H b ⟩ → ⟨ Step.Step E x y K b ⟩
    transfer b holds = holds ∙ expression-equal
```

### PowersetTableRestriction.agda

SHA-256: `c1d36cf63fb422658f62972092b1899d44b867767b6998bdb0b8839872783737`.

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
  module Small = PowersetAtomicTable.For lem X E
  module Keys = ClosedCoordinateDomain.Inclusion lem C E subset
  module Restriction = CodedTableRestriction.Construction lem Small.D Large.Algebra.B Large.table
  module DomainTransport = PowersetDomainTransport.For lem X

  agrees : ∀ u v d → ⟨ u ∈ˢ E ⟩ → ⟨ v ∈ˢ E ⟩ → ⟨ d ∈ˢ Large.Algebra.B ⟩
    → (⟨ prʟ (prʟ u v) d ∈ˢ Large.table ⟩
      → ⟨ prʟ (prʟ u v) d ∈ˢ Restriction.restricted ⟩)
      × (⟨ prʟ (prʟ u v) d ∈ˢ Restriction.restricted ⟩
      → ⟨ prʟ (prʟ u v) d ∈ˢ Large.table ⟩)
  agrees u v d uE vE dB =
    Restriction.graph-in (prʟ u v) d (Small.Keys.Product.pair-in u v uE vE) dB ,
    λ graph → snd (snd (Restriction.graph-out (prʟ u v) d graph))

  step-transfer : ∀ p b → ⟨ p ∈ˢ Small.D ⟩ → ⟨ b ∈ˢ Large.Algebra.B ⟩
    → ⟨ prʟ p b ∈ˢ Large.table ⟩ → ⟨ Large.Pair.Step Large.table p b ⟩
    → ⟨ Small.Pair.Step Restriction.restricted p b ⟩
  step-transfer p b pE bB graph step = Key.into Restriction.restricted b
    (Transfer.transfer b source)
    where
    module Key = Small.AtKey p pE

    source : ⟨ Large.Raw.Step C Key.x Key.y Large.table b ⟩
    source = Large.Pair.pair-out Large.table Key.x Key.y b
      (subst (λ q → ⟨ Large.Pair.Step Large.table q b ⟩) Key.represents step)

    module Transfer = DomainTransport.Transport C E Key.x Key.y
      Large.table Restriction.restricted subset closed Key.xC Key.yC agrees

  module Preserved = CodedTableRestriction.Preservation lem Large.D Small.D Large.Algebra.B
    (NamePairDependency.R lem) Large.Pair.Step Small.Pair.Step Keys.keys Large.table
    (Large.Package.Realization.table-good Large.solution) step-transfer

  restricted-good : Small.Recursor.Base.Good.Good Restriction.restricted
  restricted-good = Preserved.good

  restricted-bounded : Small.Recursor.Base.Laws.Bounded Restriction.restricted
  restricted-bounded = Restriction.bounded

  value-equal : ∀ p pE pC → Large.value p pC ≡ Small.value p pE
  value-equal p pE pC = Small.Package.Realization.partial-agreement Small.solution
    Restriction.restricted restricted-bounded restricted-good p pE
    (Large.value p pC) (Large.value-in-B p pC)
    (Restriction.graph-in p (Large.value p pC) pE
      (Large.value-in-B p pC) (Large.graph p pC))
```

### PowersetClosedDomainIndependence.agda

SHA-256: `2ef07687dd820cef991e7fd509fd00d65dfb5430e58029f7e911de4a7813a9d2`.

```text
{-# OPTIONS --cubical --safe --guardedness #-}

open import Base.Prelude
open import Base.Truth
open import Base.Classical using ( LEM )

module PowersetClosedDomainIndependence {ℓ : Level} (lem : LEM (ℓ-suc ℓ)) where

open import FOL.ZFStructure using ( module hPropStructure )
open import L.Constructible {ℓ} using ( 𝒮ʟ )
open import L.Coding.Model {ℓ} using ( prʟ )
import ClosedCoordinateDomain
import PowersetAtomicTable
import PowersetTableRestriction

open hPropStructure 𝒮ʟ using ( S; _∈ˢ_ )

module Compare (X C D : S)
  (closedC : ClosedCoordinateDomain.Closed lem C)
  (closedD : ClosedCoordinateDomain.Closed lem D) where

  module Common = ClosedCoordinateDomain.Common lem C D closedC closedD
    using ( E; left; right; closed; into )
  module Left = PowersetTableRestriction.For lem X C Common.E Common.left Common.closed
    using ( value-equal )
  module LeftTable = PowersetAtomicTable.For lem X C using ( value; D; module Keys )
  module Right = PowersetTableRestriction.For lem X D Common.E Common.right Common.closed
    using ( value-equal )
  module RightTable = PowersetAtomicTable.For lem X D using ( value; D; module Keys )
  module Canonical = PowersetAtomicTable.For lem X Common.E using ( value; D; module Keys )

  left-equal : ∀ p pE pC → LeftTable.value p pC ≡ Canonical.value p pE
  left-equal = Left.value-equal

  right-equal : ∀ p pE pD → RightTable.value p pD ≡ Canonical.value p pE
  right-equal = Right.value-equal

  independent : ∀ p → (pE : ⟨ p ∈ˢ Canonical.D ⟩)
    → (pC : ⟨ p ∈ˢ LeftTable.D ⟩) → (pD : ⟨ p ∈ˢ RightTable.D ⟩)
    → LeftTable.value p pC ≡ RightTable.value p pD
  independent p pE pC pD = left-equal p pE pC ∙ sym (right-equal p pE pD)

  coordinate-independent : ∀ x y → (xE : ⟨ x ∈ˢ Common.E ⟩)
    → (yE : ⟨ y ∈ˢ Common.E ⟩)
    → LeftTable.value (prʟ x y)
        (LeftTable.Keys.Product.pair-in x y (Common.left x xE) (Common.left y yE))
      ≡ RightTable.value (prʟ x y)
        (RightTable.Keys.Product.pair-in x y (Common.right x xE) (Common.right y yE))
  coordinate-independent x y xE yE = independent (prʟ x y)
    (Canonical.Keys.Product.pair-in x y xE yE)
    (LeftTable.Keys.Product.pair-in x y (Common.left x xE) (Common.left y yE))
    (RightTable.Keys.Product.pair-in x y (Common.right x xE) (Common.right y yE))

  shared-coordinate : ∀ x y → (xC : ⟨ x ∈ˢ C ⟩) → (yC : ⟨ y ∈ˢ C ⟩)
    → (xD : ⟨ x ∈ˢ D ⟩) → (yD : ⟨ y ∈ˢ D ⟩)
    → LeftTable.value (prʟ x y) (LeftTable.Keys.Product.pair-in x y xC yC)
      ≡ RightTable.value (prʟ x y) (RightTable.Keys.Product.pair-in x y xD yD)
  shared-coordinate x y xC yC xD yD = independent p commonKey leftKey rightKey
    where
    p : S
    p = prʟ x y

    commonKey : ⟨ p ∈ˢ Canonical.D ⟩
    commonKey = Canonical.Keys.Product.pair-in x y
      (Common.into x xC xD) (Common.into y yC yD)

    leftKey : ⟨ p ∈ˢ LeftTable.D ⟩
    leftKey = LeftTable.Keys.Product.pair-in x y xC yC

    rightKey : ⟨ p ∈ˢ RightTable.D ⟩
    rightKey = RightTable.Keys.Product.pair-in x y xD yD
```
