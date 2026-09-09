# K0 real name-pair domains and weighted internal images

Date: 2026-09-08. Repository source baseline: `2c2babef`. Status: four safe temporary probes checked. The [bounded recursion kernel](k0-bounded-table-recursion-2026-09.md) is now connected to actual hereditary names and their internally constructed closed pair domain. The first weighted image has an actual internal set construction. K0 remains open: Boolean operations/relative suprema, the full atomic Step formula and its laws, domain independence and general-ground portability are not yet proved.

## Actual pair dependency and its syntax

`NamePairDependency` uses the existing material Child relation, where a child occurs as the first coordinate of an actual weighted entry. It proves a finite formula for Child and its reading at arbitrary environments. The existing material-name descent proof is transported through the already checked ordered-pair bridge, so the new raw pair convention gets its well-foundedness from the existing L ground.

For raw pair codes q and p, the relation holds when there are coordinates u,v,x,y with

    q = pair(u,v), p = pair(x,y), Child(u,x), Child(v,y).

The four coordinate witnesses are propositionally truncated. A single finite formula with four existential binders has a checked reading theorem. `pair-edge` and `pair-edge-out` give both directions on actual pair constructors, including both child conditions. Nothing assumes symmetry of atomic equality to define this dependency.

For any internal C, the key domain is the actual product C × C. A key's two coordinates and their membership proofs are decoded from its product membership. Ordered-pair injectivity proves the full decoding fiber is a proposition, permitting unique extraction without selecting representatives. Well-foundedness of the restricted pair dependency follows by accessibility recursion on the first decoded coordinate; every dependency decreases that coordinate. The second child condition is still present in the relation and its formula.

This matches the expanded equality clauses in which both halves read H(u,v), with u a child of x and v a child of y. It is not a justification for a recurrence that keeps one coordinate fixed or swaps the table arguments.

## Internal closed domain for two real names

`ClosedNamePairDomain` takes actual valid B-names x and y. It reuses the previously proved internal closure construction for each name, takes the actual L union C of those closures, and proves x,y ∈ C, validity of all C members and closure under Child. D = C × C is an actual internal set, and pair(x,y) is supplied as an actual initial key.

The module proves that decoded key coordinates are valid names. It also proves D is closed under the full raw dependency relation: if p ∈ D and q depends on p, then q ∈ D. The proof uses product membership, coordinate injectivity and the proved closure of C. There is no supplied closed-family witness, assumed coordinate selector or new accessibility axiom.

`NamePairRecursion` composes this domain and the exact dependency syntax/WF with the bounded recursion constructor. Its caller supplies actual names and the proposed step's syntax, reading, internal uniqueness, locality and admission. The caller supplies neither a closed name family, a well-foundedness proof, compatibility nor Good(T). The output includes the value in B, its local equation and membership of pair(pair(x,y),value) in the actual internal table.

This is a checked representation adapter. The step remains parameterized; it is not yet the Boolean equality operation. Equality of values computed using different closed domains also remains to be proved.

## First weighted internal image

`WeightedTableImage` constructs in actual L the set

    { z ∈ B | exists v ∈ C, c ∈ B, d ∈ B:
        pair(v,c) ∈ y and pair(pair(u,v),d) ∈ H and Op(c,d,z) }.

H, y, u, C and B are supplied internal objects. Op has actual finite syntax and a reading theorem. The construction bounds the intermediate key by {u} × C, reusing the checked internal product, and separates the displayed values from B. Both formula directions and exact image membership are proved. This uses the original weighted entries: repeated children with different weights are not collapsed by a chosen representative.

The module requires no functionality/totality of H to construct this set and does not posit a host image-closure operation. Op need not be functional for image construction. A Boolean meet instance would still have to supply its actual code, reading, totality and range laws. The output guard z ∈ B is explicit and must be supplied when introducing a computed value.

Its locality result uses agreement of H and K on exactly those coded entries relevant to u and weighted entries of y. This is a graph-membership condition, not agreement on arbitrary host functions. The image congruence allows the two actual internally constructed image sets to be identified. Deriving this premise from recursive predecessor-value agreement and coverage is a further adapter, not silently assumed completed here.

The present image formula specializes H,y,u as parameters. It does not by itself provide the single variable-indexed atomic Step formula in which the table, parent names and output vary. That uniform syntax and its adequacy still need construction. For the second inner image, preserve H(u,v): simply swapping u and v in this first image would read the wrong table entry before symmetry has been proved. A shared indexed key/operation image interface can factor common proof work, with separately checked adapters for the two orientations.

Subsequent evidence: the [indexed-image and supremum-syntax probes](k0-indexed-images-suprema-2026-09.md) discharge the variable-indexed image template and the two-orientation predecessor-agreement adapter below, including actual left-image equality. They add relative-supremum syntax without proving existence. A shared uniform image-set realization and actual Boolean Step remain pending.

## Next proof work and boundaries

1. Generalize the image template to the required variable-indexed key and operation graphs, preserving the two equality-clause orientations. Prove the predecessor-agreement adapter needed for its locality.
2. Supply actual internally represented Boolean operations and relative supremum/infimum contracts. Construct both weighted inner images and the outer images, including empty families.
3. Build the expanded Step formula and prove internal admission, uniqueness and locality. Then instantiate the checked real-name-pair recursion adapter.
4. Prove independence of the closed name domain, fixed atomic equality/membership formula adequacy, and the semantic computation/standard-clause results. General-ground adapters remain a separate obligation.

The two public forcing interfaces, automatic certified conversion and shared proof ownership remain unchanged. No source theorem, landmark or trilingual content was modified. The only logical parameter used by these L constructions is the existing `LEM (ℓ-suc ℓ)`; no host choice, countable/dependent choice, BPI or resizing was added. This does not certify the final T3 assumption budget or complete K0.

## Verification

The four final snapshots below checked with exit 0 under `--cubical --safe --guardedness` and the required `GHCRTS="-A64m -I0 -M8g"`. Root checks ran in `/tmp/bedrock-k0-probes/extraction/compile-root`. The final NamePairRecursion check rechecked NamePairDependency and ClosedNamePairDomain after the exact pair-edge laws were added, so the complete final adapter was verified. Baseline interfaces were reused; no whole-tree build is claimed.

NamePairDependency's initial missing `subst2` import was corrected before the successful checks. Only final safe sources are evidence. The read-only mathematical audit appended to `/tmp/bedrock-k0-probes/table-totality-design/REPORT.md` confirms the actual relation/closure/WF and the lack of caller-supplied WF or closure in NamePairRecursion, and records the weighted-image orientation/uniform-syntax limitations.

Scoped prose/glossary checks and `git diff --check` exited 0. Tracked and copied baseline source was compared byte-for-byte with `2c2babef`; snapshots match the recorded SHA-256 values. No production source, glossary or teaching file was changed. Chapter-framework and whole-tree checks were not run for this temporary-probe/document-only change.

### NamePairDependency.agda

SHA-256: `214fc49f0a45d829f4ec1eee2acee48968c672abe81a4e8881dc911d43bc6e25`.

```text
{-# OPTIONS --cubical --safe --guardedness #-}

open import Base.Prelude
open import Base.Truth
open import Base.Classical using ( LEM )

module NamePairDependency {ℓ : Level} (lem : LEM (ℓ-suc ℓ)) where

open import FOL.ZFStructure using ( module hPropStructure )
open import L.Constructible {ℓ} using ( 𝒮ʟ )
open import FOL.Syntax using ( Formula; var; _∧̇_; ∃̇_; ∃̇∈ )
open import FOL.Semantics (hPropAlgebra (ℓ-suc ℓ)) 𝒮ʟ using ( module At )
open import L.Coding.Model {ℓ} using ( prʟ; prAtL; prʟ-inj )
open import PairFormulaReading {ℓ} using ( reading )
open import NameClosureDown lem using ( Child )
open import NameRecognition lem using ( entry-bridge )
open import MaterialNameL lem using ( ground )
import NameDescent
import ProductSet
open import Cubical.Foundations.Prelude using ( subst2 )
open import Cubical.Data.Sigma using ( Σ≡Prop )
open import Cubical.Foundations.HLevels using ( isProp× )
open import Cubical.Functions.Logic using ( ⇔toPath )
open import Cubical.Induction.WellFounded using ( Acc; acc; WellFounded )
import Cubical.HITs.PropositionalTruncation as PT
open PT using ( ∥_∥₁; ∣_∣₁ )

open hPropStructure 𝒮ʟ using ( S; _∈ˢ_; isSetS )
open At S id using ( _⊨_ )
module Native = NameDescent.Descent 𝒮ʟ ground (λ _ → refl)

childAt : ∀ {n} → Fin n → Fin n → Formula S n
childAt c p = ∃̇∈ (var p) (∃̇ (prAtL (suc zero) (suc (suc c)) zero))

child-reading : ∀ {n} (c p : Fin n) (γ : Vec S n)
  → (γ ⊨ childAt c p) ≡ (Child (lookup c γ) (lookup p γ) , PT.squash₁)
child-reading c p γ = ⇔toPath
  (PT.rec PT.squash₁ (λ { (e , member , weights) → PT.map
    (λ { (b , eq) → b , subst (λ z → ⟨ z ∈ˢ lookup p γ ⟩)
      (subst ⟨_⟩ (reading (suc zero) (suc (suc c)) zero (b ∷ e ∷ γ)) eq) member }) weights }))
  (PT.map (λ { (b , member) → prʟ (lookup c γ) b , member ,
    ∣ b , subst ⟨_⟩ (sym (reading (suc zero) (suc (suc c)) zero
      (b ∷ prʟ (lookup c γ) b ∷ γ))) refl ∣₁ }))

from-native : ∀ n → Acc Native.Child n → Acc Child n
from-native n (acc below) = acc (λ x edge → from-native x
  (below x (PT.map (λ { (b , member) → b ,
    subst (λ z → ⟨ z ∈ˢ n ⟩) (sym (entry-bridge x b)) member }) edge)))

child-wf : WellFounded Child
child-wf n = from-native n (Native.child-well-founded n)

Relation : S → S → Type (ℓ-suc ℓ)
Relation q p = ∥ Σ[ u ∈ S ] Σ[ v ∈ S ] Σ[ x ∈ S ] Σ[ y ∈ S ]
  (q ≡ prʟ u v) × (p ≡ prʟ x y) × Child u x × Child v y ∥₁

R : S → S → hProp (ℓ-suc ℓ)
R q p = Relation q p , PT.squash₁

pair-edge : ∀ u v x y → Child u x → Child v y → Relation (prʟ u v) (prʟ x y)
pair-edge u v x y left right = ∣ u , v , x , y , refl , refl , left , right ∣₁

pair-edge-out : ∀ u v x y → Relation (prʟ u v) (prʟ x y) → Child u x × Child v y
pair-edge-out u v x y = PT.rec (isProp× PT.squash₁ PT.squash₁)
  (λ { (a , b , c , d , eqQ , eqP , left , right) →
    subst2 Child (sym (fst (prʟ-inj eqQ))) (sym (fst (prʟ-inj eqP))) left ,
    subst2 Child (sym (snd (prʟ-inj eqQ))) (sym (snd (prʟ-inj eqP))) right })

relationAt : ∀ {n} → Fin n → Fin n → Formula S n
relationAt q p = ∃̇ (∃̇ (∃̇ (∃̇
  (prAtL (suc (suc (suc (suc q)))) (suc (suc (suc zero))) (suc (suc zero))
   ∧̇ (prAtL (suc (suc (suc (suc p)))) (suc zero) zero
   ∧̇ (childAt (suc (suc (suc zero))) (suc zero)
   ∧̇ childAt (suc (suc zero)) zero))))))

relation-reading : ∀ {n} (q p : Fin n) (γ : Vec S n)
  → (γ ⊨ relationAt q p) ≡ R (lookup q γ) (lookup p γ)
relation-reading q p γ = ⇔toPath forward backward
  where
  forward : ⟨ γ ⊨ relationAt q p ⟩ → Relation (lookup q γ) (lookup p γ)
  forward = PT.rec PT.squash₁ (λ { (u , vs) → PT.rec PT.squash₁
    (λ { (v , xs) → PT.rec PT.squash₁ (λ { (x , ys) → PT.map
      (λ { (y , eqQ , eqP , left , right) → u , v , x , y ,
        subst ⟨_⟩ (reading (suc (suc (suc (suc q)))) (suc (suc (suc zero)))
          (suc (suc zero)) (y ∷ x ∷ v ∷ u ∷ γ)) eqQ ,
        subst ⟨_⟩ (reading (suc (suc (suc (suc p)))) (suc zero) zero
          (y ∷ x ∷ v ∷ u ∷ γ)) eqP ,
        subst ⟨_⟩ (child-reading (suc (suc (suc zero))) (suc zero)
          (y ∷ x ∷ v ∷ u ∷ γ)) left ,
        subst ⟨_⟩ (child-reading (suc (suc zero)) zero (y ∷ x ∷ v ∷ u ∷ γ)) right }) ys }) xs }) vs })

  backward : Relation (lookup q γ) (lookup p γ) → ⟨ γ ⊨ relationAt q p ⟩
  backward = PT.map (λ { (u , v , x , y , eqQ , eqP , left , right) →
    u , ∣ v , ∣ x , ∣ y ,
      subst ⟨_⟩ (sym (reading (suc (suc (suc (suc q)))) (suc (suc (suc zero)))
        (suc (suc zero)) (y ∷ x ∷ v ∷ u ∷ γ))) eqQ ,
      subst ⟨_⟩ (sym (reading (suc (suc (suc (suc p)))) (suc zero) zero
        (y ∷ x ∷ v ∷ u ∷ γ))) eqP ,
      subst ⟨_⟩ (sym (child-reading (suc (suc (suc zero))) (suc zero)
        (y ∷ x ∷ v ∷ u ∷ γ))) left ,
      subst ⟨_⟩ (sym (child-reading (suc (suc zero)) zero (y ∷ x ∷ v ∷ u ∷ γ))) right ∣₁ ∣₁ ∣₁ })

module Domain (C : S) where

  module Product = ProductSet.Construction lem C C

  Key : Type (ℓ-suc ℓ)
  Key = Σ[ k ∈ S ] ⟨ k ∈ˢ Product.product ⟩

  Decoded : S → Type (ℓ-suc ℓ)
  Decoded k = Σ[ pair ∈ S × S ]
    ⟨ fst pair ∈ˢ C ⟩ × ⟨ snd pair ∈ˢ C ⟩ × (k ≡ prʟ (fst pair) (snd pair))

  decoded-is-prop : ∀ k → isProp (Decoded k)
  decoded-is-prop k ((u , v) , uC , vC , eqQ) ((x , y) , xC , yC , eqP) =
    Σ≡Prop (λ pair → isProp× (snd (fst pair ∈ˢ C))
      (isProp× (snd (snd pair ∈ˢ C)) (isSetS k (prʟ (fst pair) (snd pair)))))
      (cong₂ _,_ (fst coordinates) (snd coordinates))
    where
    coordinates = prʟ-inj (sym eqQ ∙ eqP)

  decode : ∀ k → ⟨ k ∈ˢ Product.product ⟩ → Decoded k
  decode k member = PT.rec (decoded-is-prop k)
    (λ { (x , y , xC , yC , eq) → (x , y) , xC , yC , eq })
    (Product.product-out k member)

  first : Key → S
  first (k , member) = fst (fst (decode k member))

  second : Key → S
  second (k , member) = snd (fst (decode k member))

  represents : ∀ k → fst k ≡ prʟ (first k) (second k)
  represents (k , member) = snd (snd (snd (decode k member)))

  first-decreases : ∀ q p → Relation (fst q) (fst p) → Child (first q) (first p)
  first-decreases q p = PT.rec PT.squash₁
    (λ { (u , v , x , y , eqQ , eqP , left , right) →
      subst2 Child (sym (fst (prʟ-inj (sym (represents q) ∙ eqQ))))
        (sym (fst (prʟ-inj (sym (represents p) ∙ eqP)))) left })

  accessible : ∀ k → Acc Child (first k)
    → Acc (λ q p → Relation (fst q) (fst p)) k
  accessible k (acc below) = acc (λ q edge → accessible q
    (below (first q) (first-decreases q k edge)))

  wf : WellFounded (λ q p → Relation (fst q) (fst p))
  wf k = accessible k (child-wf (first k))
```

### ClosedNamePairDomain.agda

SHA-256: `658df816cb9fccae81cd6e3f629da78763038428accf0d97fd859c5090aeaf9f`.

```text
{-# OPTIONS --cubical --safe --guardedness #-}

open import Base.Prelude
open import Base.Truth
open import Base.Classical using ( LEM )

module ClosedNamePairDomain {ℓ : Level} (lem : LEM (ℓ-suc ℓ)) where

open import FOL.ZFStructure using ( module hPropStructure )
open import L.Constructible {ℓ} using ( 𝒮ʟ )
open import L.Coding.Model {ℓ} using ( prʟ )
open import MaterialNameL lem using ( ground )
import MaterialNamePredicate
import NameClosure
import NamePairDependency
import ProductSet
import FOL.ZFModel as Model
open import NameClosureDown lem using ( Child )
open import Cubical.Data.Sum using ( _⊎_; inl; inr )
import Cubical.HITs.PropositionalTruncation as PT
open PT using ( ∥_∥₁; ∣_∣₁ )

open hPropStructure 𝒮ʟ using ( S; _∈ˢ_ )
module Ground = ProductSet.Ground lem
open ProductSet lem using ( S≡ )

module For (B : S) where

  module Names = MaterialNamePredicate.Names 𝒮ʟ ground (λ _ → refl) B
  module Closure = NameClosure.For lem B

  module PairOf (x y : S) (validX : ⟨ Names.IsName x ⟩) (validY : ⟨ Names.IsName y ⟩) where

    module Left = Closure.Witness x validX
    module Right = Closure.Witness y validY

    C : S
    C = Ground._∪_ Left.closedSet Right.closedSet

    left-in : ∀ z → ⟨ z ∈ˢ Left.closedSet ⟩ → ⟨ z ∈ˢ C ⟩
    left-in z member = subst ⟨_⟩
      (sym (Model.℩-spec 𝒮ʟ (Ground.hasUnion (Ground.pair Left.closedSet Right.closedSet)) z))
      ∣ Left.closedSet , subst ⟨_⟩
        (sym (Ground.pair-spec Left.closedSet Right.closedSet Left.closedSet)) ∣ inl refl ∣₁ , member ∣₁

    right-in : ∀ z → ⟨ z ∈ˢ Right.closedSet ⟩ → ⟨ z ∈ˢ C ⟩
    right-in z member = subst ⟨_⟩
      (sym (Model.℩-spec 𝒮ʟ (Ground.hasUnion (Ground.pair Left.closedSet Right.closedSet)) z))
      ∣ Right.closedSet , subst ⟨_⟩
        (sym (Ground.pair-spec Left.closedSet Right.closedSet Right.closedSet)) ∣ inr refl ∣₁ , member ∣₁

    cases : ∀ z → ⟨ z ∈ˢ C ⟩ → ∥ (⟨ z ∈ˢ Left.closedSet ⟩ ⊎ ⟨ z ∈ˢ Right.closedSet ⟩) ∥₁
    cases z member = PT.rec PT.squash₁
      (λ { (A , pair , inA) → PT.map
        (λ { (inl eq) → inl (subst (λ w → ⟨ z ∈ˢ w ⟩)
          (S≡ {x = A} {y = Left.closedSet} eq) inA)
           ; (inr eq) → inr (subst (λ w → ⟨ z ∈ˢ w ⟩)
          (S≡ {x = A} {y = Right.closedSet} eq) inA) })
        (subst ⟨_⟩ (Ground.pair-spec Left.closedSet Right.closedSet A) pair) })
      (subst ⟨_⟩ (Model.℩-spec 𝒮ʟ (Ground.hasUnion (Ground.pair Left.closedSet Right.closedSet)) z) member)

    contains-x : ⟨ x ∈ˢ C ⟩
    contains-x = left-in x Left.contains

    contains-y : ⟨ y ∈ˢ C ⟩
    contains-y = right-in y Right.contains

    all-valid : ∀ z → ⟨ z ∈ˢ C ⟩ → ⟨ Names.IsName z ⟩
    all-valid z member = PT.rec (snd (Names.IsName z))
      (λ { (inl inLeft) → Left.all-valid z inLeft
         ; (inr inRight) → Right.all-valid z inRight }) (cases z member)

    child-closed : ∀ n → ⟨ n ∈ˢ C ⟩ → ∀ z → Child z n → ⟨ z ∈ˢ C ⟩
    child-closed n member z edge = PT.rec (snd (z ∈ˢ C))
      (λ { (inl inLeft) → left-in z (Left.child-contained n inLeft z edge)
         ; (inr inRight) → right-in z (Right.child-contained n inRight z edge) }) (cases n member)

    module Keys = NamePairDependency.Domain lem C

    D : S
    D = Keys.Product.product

    initial : Keys.Key
    initial = prʟ x y , Keys.Product.pair-in x y contains-x contains-y

    coordinates-valid : ∀ k → ⟨ Names.IsName (Keys.first k) ⟩ × ⟨ Names.IsName (Keys.second k) ⟩
    coordinates-valid (k , member) =
      all-valid _ (fst (snd decoded)) , all-valid _ (fst (snd (snd decoded)))
      where
      decoded = Keys.decode k member

    dependency-closed : ∀ p → ⟨ p ∈ˢ D ⟩ → ∀ q → NamePairDependency.Relation lem q p → ⟨ q ∈ˢ D ⟩
    dependency-closed p pD q = PT.rec (snd (q ∈ˢ D))
      (λ { (u , v , a , b , eqQ , eqP , left , right) →
        subst (λ k → ⟨ k ∈ˢ D ⟩) (sym eqQ)
          (Keys.Product.pair-in u v
            (child-closed a (fst (parents a b eqP)) u left)
            (child-closed b (snd (parents a b eqP)) v right)) })
      where
      parents : ∀ a b → p ≡ prʟ a b → ⟨ a ∈ˢ C ⟩ × ⟨ b ∈ˢ C ⟩
      parents a b eq = Keys.Product.pair-out a b (subst (λ k → ⟨ k ∈ˢ D ⟩) eq pD)
```

### NamePairRecursion.agda

SHA-256: `8e2822e12c5b6e72d9ef90e44908207391aae340d610bb5c9decb53c501d700d`.

```text
{-# OPTIONS --cubical --safe --guardedness #-}

open import Base.Prelude
open import Base.Truth
open import Base.Classical using ( LEM )

module NamePairRecursion {ℓ : Level} (lem : LEM (ℓ-suc ℓ)) where

open import FOL.ZFStructure using ( module hPropStructure )
open import L.Constructible {ℓ} using ( 𝒮ʟ )
open import FOL.Syntax using ( Formula )
open import FOL.Semantics (hPropAlgebra (ℓ-suc ℓ)) 𝒮ʟ using ( module At )
open import L.Coding.Model {ℓ} using ( prʟ )
import ClosedNamePairDomain
import NamePairDependency
import BoundedTableRecursion
open import Cubical.Induction.WellFounded using ( WellFounded )
import Cubical.HITs.PropositionalTruncation as PT
open PT using ( ∥_∥₁ )

open hPropStructure 𝒮ʟ using ( S; _∈ˢ_ )
open At S id using ( _⊨_ )
module Dependency = NamePairDependency lem

module WithStep
  (Step : S → S → S → hProp (ℓ-suc ℓ))
  (stepAt : ∀ {n} → Fin n → Fin n → Fin n → Formula S n)
  (stepAt-adequate : ∀ {n} (h x b : Fin n) (γ : Vec S n)
    → (γ ⊨ stepAt h x b) ≡ Step (lookup h γ) (lookup x γ) (lookup b γ)) where

  module Engine = BoundedTableRecursion.WithStep lem Dependency.R Dependency.relationAt
    Dependency.relation-reading Step stepAt stepAt-adequate

  module Names (B : S) where

    module Closure = ClosedNamePairDomain.For lem B

    module AtPair (x y : S)
      (validX : ⟨ Closure.Names.IsName x ⟩) (validY : ⟨ Closure.Names.IsName y ⟩) where

      module Domain = Closure.PairOf x y validX validY
      module Recursor = Engine.Construction Domain.D B
      open Recursor.Base.Laws using ( Bounded; Covers; Agree )
      open Recursor.Base.Good.Functionality using ( Functional )

      wf : WellFounded Recursor.Compatibility.Dependency
      wf = Domain.Keys.wf

      module Solve
        (unique : ∀ H p c d → Bounded H → Functional H → ⟨ p ∈ˢ Domain.D ⟩
          → ⟨ c ∈ˢ B ⟩ → ⟨ d ∈ˢ B ⟩ → Covers H p
          → ⟨ Step H p c ⟩ → ⟨ Step H p d ⟩ → c ≡ d)
        (locality : ∀ H K p c → Bounded H → Bounded K → Functional H → Functional K
          → ⟨ p ∈ˢ Domain.D ⟩ → ⟨ c ∈ˢ B ⟩ → Covers H p → Covers K p → Agree H K p
          → ⟨ Step H p c ⟩ → ⟨ Step K p c ⟩)
        (admit : ∀ H p → Bounded H → Functional H → ⟨ p ∈ˢ Domain.D ⟩ → Covers H p
          → ∥ Σ[ b ∈ S ] (⟨ b ∈ˢ B ⟩ × ⟨ Step H p b ⟩) ∥₁) where

        module Result = Recursor.Solve unique locality wf admit

        value : S
        value = Result.value (prʟ x y) (snd Domain.initial)

        value-in-B : ⟨ value ∈ˢ B ⟩
        value-in-B = Result.value-in-B (prʟ x y) (snd Domain.initial)

        equation : ⟨ Step Result.table (prʟ x y) value ⟩
        equation = Result.equation (prʟ x y) (snd Domain.initial)

        graph : ⟨ prʟ (prʟ x y) value ∈ˢ Result.table ⟩
        graph = Result.value-in-table (prʟ x y) (snd Domain.initial)
```

### WeightedTableImage.agda

SHA-256: `43651eedff92328d57aa990d1d26d9ea2ce92e28425cc673ee3354307870730b`.

```text
{-# OPTIONS --cubical --safe --guardedness #-}

open import Base.Prelude
open import Base.Truth
open import Base.Classical using ( LEM )

module WeightedTableImage {ℓ : Level} (lem : LEM (ℓ-suc ℓ)) where

open import FOL.ZFStructure using ( module hPropStructure )
open import FOL.Syntax using ( Formula; con; _∧̇_; ∃̇∈ )
open import L.Constructible {ℓ} using ( 𝒮ʟ; isL )
open import FOL.Semantics (hPropAlgebra (ℓ-suc ℓ)) 𝒮ʟ using ( module At )
import FOL.ZFModel as Model
open import L.Model {ℓ} lem using ( L⊨ZF )
open import L.Coding.Model {ℓ} using ( prAtL; prʟ )
open import PairFormulaReading {ℓ} using ( reading )
import ProductSet {ℓ} lem as Products
open import Cubical.Data.Sum using ( inl; inr )
open import Cubical.Data.Sigma using ( Σ≡Prop )
open import Cubical.Functions.Logic using ( ⇔toPath )
import Cubical.HITs.PropositionalTruncation as PT
open PT using ( ∥_∥₁; ∣_∣₁ )

open TruthAlgebra (hPropAlgebra (ℓ-suc ℓ))
open hPropStructure 𝒮ʟ using ( S; _∈ˢ_; isSetS )
open At S id using ( _⊨_ )

opaque
  actualL : Model.isZFModel 𝒮ʟ
  actualL = L⊨ZF

module Ground = Model.isZFModel actualL

S≡ : {x y : S} → fst x ≡ fst y → x ≡ y
S≡ = Σ≡Prop (λ v → snd (isL v))

entryIn : ∀ {n} → S → Fin n → Fin n → Formula S n
entryIn T x b = ∃̇∈ (con T) (prAtL zero (suc x) (suc b))

entryIn-reading : ∀ {n} (T : S) (x b : Fin n) (γ : Vec S n)
  → (γ ⊨ entryIn T x b) ≡ (prʟ (lookup x γ) (lookup b γ) ∈ˢ T)
entryIn-reading T x b γ = ⇔toPath
  (PT.rec (snd (prʟ (lookup x γ) (lookup b γ) ∈ˢ T))
    (λ { (p , pT , pair) → subst (λ z → ⟨ z ∈ˢ T ⟩)
      (subst ⟨_⟩ (reading zero (suc x) (suc b) (p ∷ γ)) pair) pT }))
  (λ member → ∣ prʟ (lookup x γ) (lookup b γ) , member , subst ⟨_⟩
    (sym (reading zero (suc x) (suc b)
      (prʟ (lookup x γ) (lookup b γ) ∷ γ))) refl ∣₁)

module Construction
  (C B y H u : S)
  (Op : S → S → S → hProp (ℓ-suc ℓ))
  (opAt : ∀ {n} → Fin n → Fin n → Fin n → Formula S n)
  (op-reading : ∀ {n} (c d z : Fin n) (γ : Vec S n)
    → (γ ⊨ opAt c d z)
      ≡ Op (lookup c γ) (lookup d γ) (lookup z γ)) where

  singleton : S
  singleton = Ground.pair u u

  singleton-in : ⟨ u ∈ˢ singleton ⟩
  singleton-in = subst ⟨_⟩ (sym (Ground.pair-spec u u u)) ∣ inl refl ∣₁

  singleton-out : ∀ x → ⟨ x ∈ˢ singleton ⟩ → x ≡ u
  singleton-out x member = PT.rec (isSetS x u)
    (λ { (inl p) → S≡ p ; (inr p) → S≡ p })
    (subst ⟨_⟩ (Ground.pair-spec u u x) member)

  module Keys = Products.Construction singleton C

  formula : Formula S 1
  formula = ∃̇∈ (con C) (∃̇∈ (con B) (∃̇∈ (con B)
    (∃̇∈ (con singleton) (∃̇∈ (con Keys.product)
      (entryIn y (suc (suc (suc (suc zero)))) (suc (suc (suc zero)))
      ∧̇ (prAtL zero (suc zero) (suc (suc (suc (suc zero))))
      ∧̇ (entryIn H zero (suc (suc zero))
      ∧̇ opAt (suc (suc (suc zero))) (suc (suc zero))
        (suc (suc (suc (suc (suc zero))))))))))))

  image : S
  image = Ground.separate B formula

  Witness : S → Type (ℓ-suc ℓ)
  Witness z = ∥ Σ[ v ∈ S ] Σ[ c ∈ S ] Σ[ d ∈ S ]
    (⟨ v ∈ˢ C ⟩ × ⟨ c ∈ˢ B ⟩ × ⟨ d ∈ˢ B ⟩
      × ⟨ prʟ v c ∈ˢ y ⟩ × ⟨ prʟ (prʟ u v) d ∈ˢ H ⟩
      × ⟨ Op c d z ⟩) ∥₁

  formula-out : ∀ z → ⟨ (z ∷ []) ⊨ formula ⟩ → Witness z
  formula-out z = PT.rec PT.squash₁ λ { (v , vC , cs) → PT.rec PT.squash₁
    (λ { (c , cB , ds) → PT.rec PT.squash₁ (λ { (d , dB , xs) →
      PT.rec PT.squash₁ (λ { (x , xU , ks) → PT.rec PT.squash₁
        (λ { (k , kK , yc , pair , hd , op) →
          ∣ v , c , d , vC , cB , dB ,
          subst ⟨_⟩
            (entryIn-reading y (suc (suc (suc (suc zero))))
              (suc (suc (suc zero))) (k ∷ x ∷ d ∷ c ∷ v ∷ z ∷ [])) yc ,
          subst (λ q → ⟨ prʟ q d ∈ˢ H ⟩)
            (subst ⟨_⟩
              (reading zero (suc zero) (suc (suc (suc (suc zero))))
                (k ∷ x ∷ d ∷ c ∷ v ∷ z ∷ [])) pair
              ∙ cong (λ q → prʟ q v) (singleton-out x xU))
            (subst ⟨_⟩
              (entryIn-reading H zero (suc (suc zero))
                (k ∷ x ∷ d ∷ c ∷ v ∷ z ∷ [])) hd) ,
          subst ⟨_⟩
            (op-reading (suc (suc (suc zero))) (suc (suc zero))
              (suc (suc (suc (suc (suc zero)))))
              (k ∷ x ∷ d ∷ c ∷ v ∷ z ∷ [])) op ∣₁ }) ks }) xs }) ds }) cs }

  formula-in : ∀ z → Witness z → ⟨ (z ∷ []) ⊨ formula ⟩
  formula-in z = PT.map λ { (v , c , d , vC , cB , dB , vc , hd , op) →
    v , vC , ∣ c , cB , ∣ d , dB , ∣ u , singleton-in ,
      ∣ prʟ u v , Keys.pair-in u v singleton-in vC ,
        subst ⟨_⟩
          (sym (entryIn-reading y (suc (suc (suc (suc zero))))
            (suc (suc (suc zero)))
            (prʟ u v ∷ u ∷ d ∷ c ∷ v ∷ z ∷ []))) vc ,
        subst ⟨_⟩
          (sym (reading zero (suc zero) (suc (suc (suc (suc zero))))
            (prʟ u v ∷ u ∷ d ∷ c ∷ v ∷ z ∷ []))) refl ,
        subst ⟨_⟩
          (sym (entryIn-reading H zero (suc (suc zero))
            (prʟ u v ∷ u ∷ d ∷ c ∷ v ∷ z ∷ []))) hd ,
        subst ⟨_⟩
          (sym (op-reading (suc (suc (suc zero))) (suc (suc zero))
            (suc (suc (suc (suc (suc zero)))))
            (prʟ u v ∷ u ∷ d ∷ c ∷ v ∷ z ∷ []))) op ∣₁ ∣₁ ∣₁ ∣₁ }

  separated : ∀ z → ⟨ z ∈ˢ image ⟩
    → ⟨ z ∈ˢ B ⟩ × ⟨ (z ∷ []) ⊨ formula ⟩
  separated z member = subst ⟨_⟩ (Ground.separate-spec B formula z) member

  image-out : ∀ z → ⟨ z ∈ˢ image ⟩ → ⟨ z ∈ˢ B ⟩ × Witness z
  image-out z member = fst (separated z member) ,
    formula-out z (snd (separated z member))

  image-in : ∀ z → ⟨ z ∈ˢ B ⟩ → Witness z → ⟨ z ∈ˢ image ⟩
  image-in z zB witness = subst ⟨_⟩
    (sym (Ground.separate-spec B formula z)) (zB , formula-in z witness)

  image-membership : ∀ z
    → (z ∈ˢ image) ≡ ((z ∈ˢ B) ⊓ (Witness z , PT.squash₁))
  image-membership z = ⇔toPath (image-out z)
    (λ { (zB , witness) → image-in z zB witness })

  GraphAgreement : S → Type (ℓ-suc ℓ)
  GraphAgreement K = (v c d : S) → ⟨ v ∈ˢ C ⟩ → ⟨ c ∈ˢ B ⟩ → ⟨ d ∈ˢ B ⟩
    → ⟨ prʟ v c ∈ˢ y ⟩
    → (⟨ prʟ (prʟ u v) d ∈ˢ H ⟩ → ⟨ prʟ (prʟ u v) d ∈ˢ K ⟩)
      × (⟨ prʟ (prʟ u v) d ∈ˢ K ⟩ → ⟨ prʟ (prʟ u v) d ∈ˢ H ⟩)

  locality : ∀ K → GraphAgreement K
    → (z : S) → Witness z
    → ∥ Σ[ v ∈ S ] Σ[ c ∈ S ] Σ[ d ∈ S ]
      (⟨ v ∈ˢ C ⟩ × ⟨ c ∈ˢ B ⟩ × ⟨ d ∈ˢ B ⟩
        × ⟨ prʟ v c ∈ˢ y ⟩ × ⟨ prʟ (prʟ u v) d ∈ˢ K ⟩
        × ⟨ Op c d z ⟩) ∥₁
  locality K agrees z = PT.map λ { (v , c , d , vC , cB , dB , vc , hd , op) →
    v , c , d , vC , cB , dB , vc , fst (agrees v c d vC cB dB vc) hd , op }

module Congruence
  (C B y H K u : S)
  (Op : S → S → S → hProp (ℓ-suc ℓ))
  (opAt : ∀ {n} → Fin n → Fin n → Fin n → Formula S n)
  (op-reading : ∀ {n} (c d z : Fin n) (γ : Vec S n)
    → (γ ⊨ opAt c d z)
      ≡ Op (lookup c γ) (lookup d γ) (lookup z γ))
  (agrees : (v c d : S) → ⟨ v ∈ˢ C ⟩ → ⟨ c ∈ˢ B ⟩ → ⟨ d ∈ˢ B ⟩
    → ⟨ prʟ v c ∈ˢ y ⟩
    → (⟨ prʟ (prʟ u v) d ∈ˢ H ⟩ → ⟨ prʟ (prʟ u v) d ∈ˢ K ⟩)
      × (⟨ prʟ (prʟ u v) d ∈ˢ K ⟩ → ⟨ prʟ (prʟ u v) d ∈ˢ H ⟩)) where

  module Left = Construction C B y H u Op opAt op-reading
  module Right = Construction C B y K u Op opAt op-reading

  forward : ∀ z → ⟨ z ∈ˢ Left.image ⟩ → ⟨ z ∈ˢ Right.image ⟩
  forward z member = Right.image-in z (fst (Left.image-out z member))
    (PT.map (λ { (v , c , d , vC , cB , dB , vc , hd , op) →
      v , c , d , vC , cB , dB , vc , fst (agrees v c d vC cB dB vc) hd , op })
      (snd (Left.image-out z member)))

  backward : ∀ z → ⟨ z ∈ˢ Right.image ⟩ → ⟨ z ∈ˢ Left.image ⟩
  backward z member = Left.image-in z (fst (Right.image-out z member))
    (PT.map (λ { (v , c , d , vC , cB , dB , vc , kd , op) →
      v , c , d , vC , cB , dB , vc , snd (agrees v c d vC cB dB vc) kd , op })
      (snd (Right.image-out z member)))

  image-equal : Left.image ≡ Right.image
  image-equal = Ground.extensional (λ z → ⇔toPath (forward z) (backward z))
```
