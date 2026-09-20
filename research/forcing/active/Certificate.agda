{-# OPTIONS --cubical --safe --guardedness #-}

-- K2 module M9 (Track G): certified completions, the nonzero part, the
-- comparison theorem, the dense-map calculus and property transfer.
--
-- What this module is for. A completion request may carry a SEMANTIC
-- certificate, which says that a given coded algebra really is a Boolean
-- completion of a given presentation, and it may carry a PROPERTY
-- certificate, which says that some property of the presentation survives
-- the passage to the algebra. Those are different objects and the types keep
-- them apart: CertifiedCompletion below has no field mentioning a chain
-- condition, countability, closure, a size bound, fullness, a name or a
-- translation, and PropertyTransfer is a separate record whose two property
-- arguments are arbitrary. A transfer package for one chain-condition variant
-- is therefore an inhabitant of a type that mentions that variant and no
-- other, and cannot be coerced into a package for another variant.
--
-- Five structural decisions, each of which is a trap named by the K2
-- architecture.
--
--  1. The specification of the carrier B is NOT a field of
--     CertifiedCompletion. It is a field of Completion, the record for the
--     canonical regular-open construction. Were it a field of the
--     certificate, Extensionality would force any two certificates to have
--     the same B and the comparison theorem would be an identity.
--  2. The nonzero part is total only under nontriviality. That hypothesis is
--     the field `nontrivial`, and B⁺ consumes it to produce the presentation's
--     inhabitation clause; the nonzero part of a degenerate algebra is empty
--     and no presentation exists over it.
--  3. There is no transport of a certificate along a bare monotone map.
--     transport-certificate takes a DenseMap, whose density field is used at
--     exactly one place in the proof of the transported `recover`, and whose
--     compatibility fields run in BOTH directions.
--  4. PropertyTransfer is parameterized by the presentation and by the
--     certificate, so that its `hypotheses` field can mention either.
--  5. CompleteSubalgebra is a definition and nothing else. Bell's Theorem
--     1.20 and Corollary 1.21 quantify over Boolean-valued names, which do
--     not exist at this layer.
--
-- Notation rules of K2 section 1.0 are observed: the cubical powerset
-- membership never appears, and every negation is spelled _ ⇒ ⊥ with the
-- algebra's own bottom. The lattice complement is written ¬ᴮ_ and is a
-- different operator on a different carrier.
--
-- Hypotheses. The module takes the structure, ordinary Extensionality and the
-- path realization of the structure equality; those three are what make the
-- order on elements antisymmetric, which every uniqueness statement below
-- needs. Separation is an argument of exactly the constructions that build a
-- set, and LEM ℓ is an explicit first argument of exactly the lemmas that
-- need it, never a module parameter. The presentation layer is taken as the
-- record Presentation below rather than imported, so that a change in the
-- coded presentation of Track F cannot invalidate this file; the coordinator
-- instantiates it with one record projection.

open import Base.Prelude
open import Base.Truth
open import FOL.ZFStructure using ( ZFStructure )
import OrdinaryProfile
import GroundDescription
import ForcingNotion as FN

module Certificate
  {ℓ} (𝒮 : ZFStructure (hPropAlgebra ℓ))
  (ext : OrdinaryProfile.Extensionality 𝒮)
  (paths : (x y : ZFStructure.S 𝒮)
         → (ZFStructure._≈ˢ_ 𝒮 x y) ≡ ((x ≡ y) , ZFStructure.isSetS 𝒮 x y))
  where

open import FOL.ZFStructure using ( module hPropStructure )
open import FOL.Syntax using ( Formula; con; var; _∈̇_; _≐_; _∧̇_; ¬̇_; ∀̇∈ )
open import FOL.Semantics (hPropAlgebra ℓ) 𝒮 using ( module At )
open import FOL.ZFModel 𝒮 using ( _⊆ˢ_ )
open import Base.Classical using ( LEM )
open import Cubical.Foundations.HLevels using ( isSetΣSndProp )
open import Cubical.Foundations.Equiv using ( _≃_; propBiimpl→Equiv )
open import Cubical.Data.Sigma using ( Σ≡Prop )
open import Cubical.Data.Sum using ( _⊎_; inl; inr )
open import Cubical.Functions.Logic using ( ⇔toPath )
import Cubical.Data.Empty as Empty
import Cubical.HITs.PropositionalTruncation as PT
open PT using ( ∥_∥₁; ∣_∣₁ )

module OP = OrdinaryProfile 𝒮
module GD = GroundDescription 𝒮 ext paths

open TruthAlgebra (hPropAlgebra ℓ)
open hPropStructure 𝒮
open At S id using ( _⊨_ )

open OP using ( iff; Separation )
open OP.PathRealization paths using ( ≈ˢ-to-path; path-to-≈ˢ )
open GD using ( ext-path; separateOf; separateOf-spec )

--------------------------------------------------------------------------------
-- Points of a coded set
--------------------------------------------------------------------------------

-- Every carrier in this file is a set of the ground, and its elements are
-- read as pairs of a code and a membership proof. This is the K0 ledger's
-- representation decision, and it is the same shape for the conditions of a
-- presentation and for the elements of the algebra, which is what lets the
-- nonzero part of an algebra be a presentation with no coercion at all.

Pt : S → Type ℓ
Pt a = Σ[ x ∈ S ] ⟨ x ∈ˢ a ⟩

isSetPt : (a : S) → isSet (Pt a)
isSetPt a = isSetΣSndProp isSetS (λ x → snd (x ∈ˢ a))

-- Membership is a proposition, so two points with the same code are equal.

Pt≡ : {a : S} {u v : Pt a} → fst u ≡ fst v → u ≡ v
Pt≡ {a} = Σ≡Prop (λ x → snd (x ∈ˢ a))

--------------------------------------------------------------------------------
-- The order on elements
--------------------------------------------------------------------------------

-- The order of the algebra is internal inclusion of codes, which is the
-- reading the regular-open construction produces and the only order any
-- coded algebra of K2 carries. It is passed to the lattice and completeness
-- records rather than being a field of either, so that the lattice laws, the
-- join laws and the embedding laws are provably about one relation.

infix 20 _≤ᴮ_
_≤ᴮ_ : {a : S} → Pt a → Pt a → Ω
u ≤ᴮ v = fst u ⊆ˢ fst v

≤ᴮ-refl : {a : S} (u : Pt a) → ⟨ u ≤ᴮ u ⟩
≤ᴮ-refl u x h = h

-- Transitivity is stated on the codes rather than on the points. The point
-- level statement would leave its implicit carrier and both endpoints
-- undetermined at every call site, since the order only ever mentions the
-- first projections, and Agda cannot invert a projection. Measured: a point
-- level version produced an unsolved meta at each of eleven uses.

⊆ˢ-trans : {x y z : S} → ⟨ x ⊆ˢ y ⟩ → ⟨ y ⊆ˢ z ⟩ → ⟨ x ⊆ˢ z ⟩
⊆ˢ-trans h k w m = k w (h w m)

-- Antisymmetry is where the module's two ground hypotheses are spent, and it
-- is spent nowhere else: internal Extensionality turns mutual inclusion into
-- the structure equality, and the path realization turns that into a host
-- path, which the membership proof then rides along.

≤ᴮ-antisym : {a : S} {u v : Pt a} → ⟨ u ≤ᴮ v ⟩ → ⟨ v ≤ᴮ u ⟩ → u ≡ v
≤ᴮ-antisym h k = Pt≡ (ext-path (λ x → ⇔toPath (h x) (k x)))

--------------------------------------------------------------------------------
-- The bounded lattice, in order form
--------------------------------------------------------------------------------

-- The operations are pinned by their universal properties rather than by an
-- equational axiomatisation. Two inhabitants of BoundedLattice over the same
-- carrier therefore have equal operations, which is the property the
-- comparison theorem needs and which an equational presentation with an
-- independent order field would not give.

record BoundedLattice (B : S) : Type ℓ where
  field
    ⊤ᴮ ⊥ᴮ      : Pt B
    _⊓ᴮ_ _⊔ᴮ_  : Pt B → Pt B → Pt B
    ⊓-lb₁      : (u v : Pt B) → ⟨ (u ⊓ᴮ v) ≤ᴮ u ⟩
    ⊓-lb₂      : (u v : Pt B) → ⟨ (u ⊓ᴮ v) ≤ᴮ v ⟩
    ⊓-glb      : (u v w : Pt B) → ⟨ w ≤ᴮ u ⟩ → ⟨ w ≤ᴮ v ⟩ → ⟨ w ≤ᴮ (u ⊓ᴮ v) ⟩
    ⊔-ub₁      : (u v : Pt B) → ⟨ u ≤ᴮ (u ⊔ᴮ v) ⟩
    ⊔-ub₂      : (u v : Pt B) → ⟨ v ≤ᴮ (u ⊔ᴮ v) ⟩
    ⊔-lub      : (u v w : Pt B) → ⟨ u ≤ᴮ w ⟩ → ⟨ v ≤ᴮ w ⟩ → ⟨ (u ⊔ᴮ v) ≤ᴮ w ⟩
    ⊥-least    : (u : Pt B) → ⟨ ⊥ᴮ ≤ᴮ u ⟩
    ⊤-greatest : (u : Pt B) → ⟨ u ≤ᴮ ⊤ᴮ ⟩

  infixr 12 _⊓ᴮ_ _⊔ᴮ_

-- The complement and the one law no order-theoretic characterisation can
-- force. Distributivity is a field because a bounded lattice with
-- complements need not be distributive; the rest of the Boolean theory is
-- derived below.

record IsBoolean (B : S) (L : BoundedLattice B) : Type ℓ where
  open BoundedLattice L
  field
    ¬ᴮ_      : Pt B → Pt B
    ¬-⊓      : (u : Pt B) → (u ⊓ᴮ (¬ᴮ u)) ≡ ⊥ᴮ
    ¬-⊔      : (u : Pt B) → (u ⊔ᴮ (¬ᴮ u)) ≡ ⊤ᴮ
    ⊓-⊔-dist : (u v w : Pt B) → (u ⊓ᴮ (v ⊔ᴮ w)) ≡ ((u ⊓ᴮ v) ⊔ᴮ (u ⊓ᴮ w))

  infix 13 ¬ᴮ_

-- Completeness for the coded families, and for those only. The family is a
-- ground code X together with a proof that it is a subset of the algebra;
-- there is deliberately no host-indexed supremum operator anywhere in K2, and
-- no predicate parameter naming an abstract class of admissible families.

record CompleteForCoded (B : S) : Type ℓ where
  field
    supᴮ    : (X : S) → ⟨ X ⊆ˢ B ⟩ → Pt B
    sup-ub  : (X : S) (h : ⟨ X ⊆ˢ B ⟩) (u : Pt B)
            → ⟨ fst u ∈ˢ X ⟩ → ⟨ u ≤ᴮ supᴮ X h ⟩
    sup-lub : (X : S) (h : ⟨ X ⊆ˢ B ⟩) (v : Pt B)
            → ((u : Pt B) → ⟨ fst u ∈ˢ X ⟩ → ⟨ u ≤ᴮ v ⟩)
            → ⟨ supᴮ X h ≤ᴮ v ⟩
    infᴮ    : (X : S) → ⟨ X ⊆ˢ B ⟩ → Pt B
    inf-lb  : (X : S) (h : ⟨ X ⊆ˢ B ⟩) (u : Pt B)
            → ⟨ fst u ∈ˢ X ⟩ → ⟨ infᴮ X h ≤ᴮ u ⟩
    inf-glb : (X : S) (h : ⟨ X ⊆ˢ B ⟩) (v : Pt B)
            → ((u : Pt B) → ⟨ fst u ∈ˢ X ⟩ → ⟨ v ≤ᴮ u ⟩)
            → ⟨ v ≤ᴮ infᴮ X h ⟩

-- Nondegeneracy, in the form the architecture fixes. It is stated with the
-- algebra's own bottom on the right, never with the host empty type.

Nontrivial : (B : S) → BoundedLattice B → Type ℓ
Nontrivial B L = (BoundedLattice.⊥ᴮ L ≡ BoundedLattice.⊤ᴮ L) → ⟨ ⊥ ⟩

--------------------------------------------------------------------------------
-- What the lattice laws force
--------------------------------------------------------------------------------

module LatticeTheory (B : S) (L : BoundedLattice B) where
  open BoundedLattice L public

  ⊓-idem : (u : Pt B) → (u ⊓ᴮ u) ≡ u
  ⊓-idem u = ≤ᴮ-antisym (⊓-lb₁ u u) (⊓-glb u u u (≤ᴮ-refl u) (≤ᴮ-refl u))

  ⊓-comm : (u v : Pt B) → (u ⊓ᴮ v) ≡ (v ⊓ᴮ u)
  ⊓-comm u v =
    ≤ᴮ-antisym (⊓-glb v u (u ⊓ᴮ v) (⊓-lb₂ u v) (⊓-lb₁ u v))
               (⊓-glb u v (v ⊓ᴮ u) (⊓-lb₂ v u) (⊓-lb₁ v u))

  ⊓-⊤ : (u : Pt B) → (u ⊓ᴮ ⊤ᴮ) ≡ u
  ⊓-⊤ u = ≤ᴮ-antisym (⊓-lb₁ u ⊤ᴮ)
                     (⊓-glb u ⊤ᴮ u (≤ᴮ-refl u) (⊤-greatest u))

  ⊓-⊥ : (u : Pt B) → (u ⊓ᴮ ⊥ᴮ) ≡ ⊥ᴮ
  ⊓-⊥ u = ≤ᴮ-antisym (⊓-lb₂ u ⊥ᴮ) (⊥-least (u ⊓ᴮ ⊥ᴮ))

  ⊔-⊥ : (u : Pt B) → (u ⊔ᴮ ⊥ᴮ) ≡ u
  ⊔-⊥ u = ≤ᴮ-antisym (⊔-lub u ⊥ᴮ u (≤ᴮ-refl u) (⊥-least u)) (⊔-ub₁ u ⊥ᴮ)

  ⊔-⊥ˡ : (u : Pt B) → (⊥ᴮ ⊔ᴮ u) ≡ u
  ⊔-⊥ˡ u = ≤ᴮ-antisym (⊔-lub ⊥ᴮ u u (⊥-least u) (≤ᴮ-refl u)) (⊔-ub₂ ⊥ᴮ u)

  -- Refinement and meet say the same thing, in both directions.

  ≤→⊓ : (u v : Pt B) → ⟨ u ≤ᴮ v ⟩ → (u ⊓ᴮ v) ≡ u
  ≤→⊓ u v h = ≤ᴮ-antisym (⊓-lb₁ u v) (⊓-glb u v u (≤ᴮ-refl u) h)

  ⊓→≤ : (u v : Pt B) → (u ⊓ᴮ v) ≡ u → ⟨ u ≤ᴮ v ⟩
  ⊓→≤ u v p = subst (λ z → ⟨ z ≤ᴮ v ⟩) p (⊓-lb₂ u v)

  ≤⊥→≡⊥ : (u : Pt B) → ⟨ u ≤ᴮ ⊥ᴮ ⟩ → u ≡ ⊥ᴮ
  ≤⊥→≡⊥ u h = ≤ᴮ-antisym h (⊥-least u)

  -- Positivity is nonzeroness, and it is the only reading available at this
  -- layer: an element of an abstract certificate is not known to be a set of
  -- conditions, so "inhabited" is not expressible here. Bell states the
  -- completion contract in exactly this form, j(p) ∧ j(q) ≠ 0
  -- (bell-2005-boolean-valued-models.fulltext.md:3546-3547). The host
  -- regular-open algebra's inhabitedness form agrees with this one under LEM
  -- by its own positive-nonzero theorem, and that theorem is where the
  -- coordinator's instantiation spends its excluded middle.

  positiveᴮ : Pt B → Ω
  positiveᴮ u = ((u ≡ ⊥ᴮ) , isSetPt B u ⊥ᴮ) ⇒ ⊥

  positive-mono : (u v : Pt B) → ⟨ u ≤ᴮ v ⟩ → ⟨ positiveᴮ u ⟩ → ⟨ positiveᴮ v ⟩
  positive-mono u v h pu e =
    pu (≤⊥→≡⊥ u (subst (λ z → ⟨ u ≤ᴮ z ⟩) e h))

  -- The supremum and the infimum are unique, so an algebra cannot carry two
  -- different bounded lattice structures over the same order. This is the
  -- property that makes `lattice` safe to state as a field rather than as a
  -- specification against the carrier.

  ⊓-unique : (L' : BoundedLattice B) (u v : Pt B)
           → (u ⊓ᴮ v) ≡ (BoundedLattice._⊓ᴮ_ L' u v)
  ⊓-unique L' u v = ≤ᴮ-antisym
    (M.⊓-glb u v (u ⊓ᴮ v) (⊓-lb₁ u v) (⊓-lb₂ u v))
    (⊓-glb u v (M._⊓ᴮ_ u v) (M.⊓-lb₁ u v) (M.⊓-lb₂ u v))
    where module M = BoundedLattice L'

module BooleanTheory (B : S) (L : BoundedLattice B) (b : IsBoolean B L) where
  open LatticeTheory B L public
  open IsBoolean b public

  -- The two directions of "refines" read as "disjoint from the complement".
  -- This is the bridge the forcing layer uses, and neither direction needs
  -- involutivity of the complement.

  ≤-as-⊥ : (u v : Pt B) → ⟨ u ≤ᴮ v ⟩ → (u ⊓ᴮ (¬ᴮ v)) ≡ ⊥ᴮ
  ≤-as-⊥ u v h = ≤⊥→≡⊥ (u ⊓ᴮ (¬ᴮ v))
    (subst (λ z → ⟨ (u ⊓ᴮ (¬ᴮ v)) ≤ᴮ z ⟩) (¬-⊓ v)
      (⊓-glb v (¬ᴮ v) (u ⊓ᴮ (¬ᴮ v))
        (⊆ˢ-trans (⊓-lb₁ u (¬ᴮ v)) h) (⊓-lb₂ u (¬ᴮ v))))

  ⊥-as-≤ : (u v : Pt B) → (u ⊓ᴮ (¬ᴮ v)) ≡ ⊥ᴮ → ⟨ u ≤ᴮ v ⟩
  ⊥-as-≤ u v e = ⊓→≤ u v (sym decomp)
    where
      decomp : u ≡ (u ⊓ᴮ v)
      decomp =
          sym (⊓-⊤ u)
        ∙ cong (u ⊓ᴮ_) (sym (¬-⊔ v))
        ∙ ⊓-⊔-dist u v (¬ᴮ v)
        ∙ cong ((u ⊓ᴮ v) ⊔ᴮ_) e
        ∙ ⊔-⊥ (u ⊓ᴮ v)

  -- Disjointness and refinement of the complement, again both ways. The
  -- forward direction is where the decomposition u = (u ⊓ v) ⊔ (u ⊓ ¬v) is
  -- used with the first summand empty.

  ⊓⊥→≤¬ : (u v : Pt B) → (u ⊓ᴮ v) ≡ ⊥ᴮ → ⟨ u ≤ᴮ (¬ᴮ v) ⟩
  ⊓⊥→≤¬ u v e = subst (λ z → ⟨ z ≤ᴮ (¬ᴮ v) ⟩) (sym decomp) (⊓-lb₂ u (¬ᴮ v))
    where
      decomp : u ≡ (u ⊓ᴮ (¬ᴮ v))
      decomp =
          sym (⊓-⊤ u)
        ∙ cong (u ⊓ᴮ_) (sym (¬-⊔ v))
        ∙ ⊓-⊔-dist u v (¬ᴮ v)
        ∙ cong (_⊔ᴮ (u ⊓ᴮ (¬ᴮ v))) e
        ∙ ⊔-⊥ˡ (u ⊓ᴮ (¬ᴮ v))

  ≤¬→⊓⊥ : (u v : Pt B) → ⟨ u ≤ᴮ (¬ᴮ v) ⟩ → (u ⊓ᴮ v) ≡ ⊥ᴮ
  ≤¬→⊓⊥ u v h = ≤⊥→≡⊥ (u ⊓ᴮ v)
    (subst (λ z → ⟨ (u ⊓ᴮ v) ≤ᴮ z ⟩) (⊓-comm (¬ᴮ v) v ∙ ¬-⊓ v)
      (⊓-glb (¬ᴮ v) v (u ⊓ᴮ v)
        (⊆ˢ-trans (⊓-lb₁ u v) h) (⊓-lb₂ u v)))

  -- Two elements lying on opposite sides of a complement are disjoint.

  disjoint-of-≤ : (u v w : Pt B) → ⟨ u ≤ᴮ w ⟩ → ⟨ v ≤ᴮ (¬ᴮ w) ⟩ → (u ⊓ᴮ v) ≡ ⊥ᴮ
  disjoint-of-≤ u v w hu hv = ≤⊥→≡⊥ (u ⊓ᴮ v)
    (subst (λ z → ⟨ (u ⊓ᴮ v) ≤ᴮ z ⟩) (¬-⊓ w)
      (⊓-glb w (¬ᴮ w) (u ⊓ᴮ v)
        (⊆ˢ-trans (⊓-lb₁ u v) hu) (⊆ˢ-trans (⊓-lb₂ u v) hv)))

  -- Complements are unique, which is what pins ¬ᴮ under an isomorphism.

  complement-unique : (u x y : Pt B)
    → (u ⊓ᴮ x) ≡ ⊥ᴮ → (u ⊔ᴮ x) ≡ ⊤ᴮ → (u ⊓ᴮ y) ≡ ⊥ᴮ → (u ⊔ᴮ y) ≡ ⊤ᴮ → x ≡ y
  complement-unique u x y ux uX uy uY = xy ∙ ⊓-comm x y ∙ sym yx
    where
      xy : x ≡ (x ⊓ᴮ y)
      xy = sym (⊓-⊤ x) ∙ cong (x ⊓ᴮ_) (sym uY) ∙ ⊓-⊔-dist x u y
         ∙ cong (_⊔ᴮ (x ⊓ᴮ y)) (⊓-comm x u ∙ ux) ∙ ⊔-⊥ˡ (x ⊓ᴮ y)
      yx : y ≡ (y ⊓ᴮ x)
      yx = sym (⊓-⊤ y) ∙ cong (y ⊓ᴮ_) (sym uX) ∙ ⊓-⊔-dist y u x
         ∙ cong (_⊔ᴮ (y ⊓ᴮ x)) (⊓-comm y u ∙ uy) ∙ ⊔-⊥ˡ (y ⊓ᴮ x)

--------------------------------------------------------------------------------
-- Presentations
--------------------------------------------------------------------------------

-- A presentation is the host reading of a coded forcing notion: a carrier set
-- of the ground, an Ω-valued preorder on its points, and mere inhabitation.
-- This file states it rather than importing it, so that the coded
-- presentation of the model-internal completion can change without touching
-- anything below: its decoded forcing notion has exactly these five
-- components, and the instantiation is one record expression.
--
-- The order is a relation on points rather than a graph set of the ground.
-- Nothing in this module reads the order internally, and the graph is
-- recovered on the producing side; what is lost is recorded in this track's
-- report, since the nonzero part below is therefore delivered as a
-- presentation in this sense and not yet as a coded one.

record Presentation : Type (ℓ-suc ℓ) where
  field
    carrier   : S
    _≼_       : Pt carrier → Pt carrier → Ω
    ≼-refl    : (p : Pt carrier) → ⟨ p ≼ p ⟩
    ≼-trans   : {p q r : Pt carrier} → ⟨ p ≼ q ⟩ → ⟨ q ≼ r ⟩ → ⟨ p ≼ r ⟩
    inhabited : ⟨ ⋁ S (λ x → x ∈ˢ carrier) ⟩

  infix 20 _≼_

-- The host structural vocabulary of Track A is imported through this one
-- adapter, so compatibility, density, antichains, separativity and Bell's
-- separative equality all have their Track A meanings and no second
-- definition of any of them exists in K2.

notion : Presentation → FN.ForcingNotion {ℓ}
notion 𝔓 = record
  { Cond     = Pt carrier
  ; isSetC   = isSetPt carrier
  ; _≼_      = _≼_
  ; ≼-refl   = ≼-refl
  ; ≼-trans  = ≼-trans
  ; nonempty = PT.map (λ { (x , hx) → x , hx }) inhabited }
  where open Presentation 𝔓

--------------------------------------------------------------------------------
-- Certified completions of one presentation
--------------------------------------------------------------------------------

module Over (𝔓 : Presentation) where

  open Presentation 𝔓 public
  open FN.Structure (notion 𝔓) public
    using ( compatible; compatibleData; incompatible; witness
          ; separativelyEqual; separative; antisymmetric; Top
          ; compatible-refl; compatible-sym; ≼-compatible; compatible-mono )

  -- The embedding of the conditions and the two coded operations that make
  -- Bell's density clause statable inside the model. `below b` is Bell's P_x,
  -- the set of conditions whose image refines b (fulltext:3479-3480), and
  -- `iImage` is the coded direct image of a set of conditions under i; the
  -- pair is what turns "the density of e[P] in B implies x = ⋁ e[P_x]" into a
  -- field that mentions no host-indexed supremum.
  --
  -- There is no injectivity field and no order-reflection field: both are
  -- adapters that need separativity, and one of them needs antisymmetry as
  -- well. The kernel theorem below replaces them.

  record Embedding (B : S) (L : BoundedLattice B) (C : CompleteForCoded B)
    : Type (ℓ-suc ℓ) where
    open LatticeTheory B L
    open CompleteForCoded C
    field
      i         : Pt carrier → Pt B
      i-mono    : {p q : Pt carrier} → ⟨ q ≼ p ⟩ → ⟨ i q ≤ᴮ i p ⟩
      i-pos     : (p : Pt carrier) → ⟨ positiveᴮ (i p) ⟩
      i-compat→ : (p q : Pt carrier)
                → ⟨ compatible p q ⟩ → ⟨ positiveᴮ ((i p) ⊓ᴮ (i q)) ⟩
      i-compat← : (p q : Pt carrier)
                → ⟨ positiveᴮ ((i p) ⊓ᴮ (i q)) ⟩ → ⟨ compatible p q ⟩
      below      : Pt B → S
      below-sub  : (b : Pt B) → ⟨ below b ⊆ˢ carrier ⟩
      below-spec : (b : Pt B) (p : Pt carrier) → (fst p ∈ˢ below b) ≡ (i p ≤ᴮ b)
      iImage      : S → S
      iImage-sub  : (d : S) → ⟨ d ⊆ˢ carrier ⟩ → ⟨ iImage d ⊆ˢ B ⟩
      iImage-spec : (d : S) (u : Pt B)
                  → (fst u ∈ˢ iImage d)
                  ≡ ⋁ (Pt carrier) (λ p → (fst p ∈ˢ d) ⊓ (fst u ≈ˢ fst (i p)))
      recover : (b : Pt B)
              → supᴮ (iImage (below b)) (iImage-sub (below b) (below-sub b)) ≡ b

  -- The certificate. Note what is absent: the specification of B, any chain
  -- condition, any countability or closure clause, any size bound, fullness,
  -- names, translations. B is a bare field, and that is what makes the
  -- comparison theorem below say something.

  record CertifiedCompletion : Type (ℓ-suc ℓ) where
    field
      B          : S
      lattice    : BoundedLattice B
      boolean    : IsBoolean B lattice
      complete   : CompleteForCoded B
      nontrivial : Nontrivial B lattice
      embedding  : Embedding B lattice complete

  -- Bell's regular-open condition, read against the presentation's own order.
  -- The right-hand side is the interior of the closure of U at q, Bell's
  -- displayed (X)° = {q : ∀p′ ≤ q ∃r ∈ X, r ≤ p′} (fulltext:3449).

  regularOpenᴾ : S → Ω
  regularOpenᴾ U = ⋀ (Pt carrier) (λ q → iff (fst q ∈ˢ U)
    (⋀ (Pt carrier) (λ r → (r ≼ q) ⇒
      (⋁ (Pt carrier) (λ s → (s ≼ r) ⊓ (fst s ∈ˢ U))))))

  -- The canonical construction's output carries one more field than a
  -- certificate does, and this is the only place it may appear. Were B-spec a
  -- field of CertifiedCompletion, internal Extensionality would identify the
  -- carriers of any two certificates and the comparison theorem would
  -- degenerate to the identity.

  record Completion : Type (ℓ-suc ℓ) where
    field
      certified : CertifiedCompletion
      B-spec    : (U : S) → (U ∈ˢ CertifiedCompletion.B certified)
                ≡ ((U ⊆ˢ carrier) ⊓ regularOpenᴾ U)

  --------------------------------------------------------------------------
  -- What one certificate proves on its own
  --------------------------------------------------------------------------

  module Theory (c : CertifiedCompletion) where
    open CertifiedCompletion c public
    open BooleanTheory B lattice boolean public
    open CompleteForCoded complete public
    open Embedding embedding public

    -- The top of a nondegenerate algebra is nonzero. This is the form the
    -- nonzero part consumes to prove its own inhabitation clause.

    ⊤-positive : ⟨ positiveᴮ ⊤ᴮ ⟩
    ⊤-positive e = nontrivial (sym e)

    -- An element with no condition below it is zero. The proof is the whole
    -- content of the density field: b is the supremum of the coded image of
    -- the conditions below it, and if there are none then that image has no
    -- element of the algebra in it, so every element is vacuously an upper
    -- bound of it and the supremum refines the bottom.

    empty-below : (b : Pt B)
                → (⟨ ⋁ (Pt carrier) (λ p → i p ≤ᴮ b) ⟩ → Empty.⊥)
                → b ≡ ⊥ᴮ
    empty-below b n = sym (recover b) ∙
      ≤⊥→≡⊥ (supᴮ (iImage (below b)) (iImage-sub (below b) (below-sub b)))
            (sup-lub (iImage (below b))
                     (iImage-sub (below b) (below-sub b)) ⊥ᴮ step)
      where
        step : (u : Pt B) → ⟨ fst u ∈ˢ iImage (below b) ⟩ → ⟨ u ≤ᴮ ⊥ᴮ ⟩
        step u hu = Empty.rec
          (n (PT.map pick (subst ⟨_⟩ (iImage-spec (below b) u) hu)))
          where
            pick : Σ[ p ∈ Pt carrier ]
                     (⟨ fst p ∈ˢ below b ⟩ × ⟨ fst u ≈ˢ fst (i p) ⟩)
                 → Σ[ p ∈ Pt carrier ] ⟨ i p ≤ᴮ b ⟩
            pick (p , hp , _) = p , subst ⟨_⟩ (below-spec b p) hp

    -- Bell's dense form: the image of the conditions is dense in the algebra,
    -- where a subset X of a Boolean algebra is dense when 0 is not in X and
    -- every nonzero element has a member of X below it (fulltext:3438-3439).
    -- The first clause is the i-pos field; this is the second. LEM is used
    -- once, to decide the truncated existential, and the false branch is
    -- closed by empty-below.

    dense-form : LEM ℓ → (b : Pt B) → ⟨ positiveᴮ b ⟩
               → ⟨ ⋁ (Pt carrier) (λ p → i p ≤ᴮ b) ⟩
    dense-form lem b pos with lem (⋁ (Pt carrier) (λ p → i p ≤ᴮ b))
    ... | inl h = h
    ... | inr n = Empty.rec* (pos (empty-below b n))

    -- Two consequences of the compatibility fields used throughout.

    i-meet-pos : (p q : Pt carrier) → ⟨ i p ≤ᴮ i q ⟩
               → ⟨ positiveᴮ ((i p) ⊓ᴮ (i q)) ⟩
    i-meet-pos p q h =
      subst (λ z → ⟨ positiveᴮ z ⟩) (sym (≤→⊓ (i p) (i q) h)) (i-pos p)

    ≤→compatible : (p q : Pt carrier) → ⟨ i p ≤ᴮ i q ⟩ → ⟨ compatible p q ⟩
    ≤→compatible p q h = i-compat← p q (i-meet-pos p q h)

    -- The semantic order theorem. The image of q refines the image of p
    -- exactly when every refinement of q is compatible with p, which is
    -- Bell's displayed formula (1) for the regular-open completion
    -- (fulltext:3456-3457) proved here from the certificate alone.
    --
    -- The forward direction is constructive. The backward direction is the
    -- one that carries the package: if the images do not refine, the meet of
    -- i q with the complement of i p is nonzero, density supplies a condition
    -- r whose image lies under it, r is compatible with q because its image
    -- meets the image of q in a nonzero element, a common refinement t of r
    -- and q is compatible with p by hypothesis, and a common refinement u of
    -- t and p refines r as well, so r and p are compatible. But the image of
    -- r is disjoint from the image of p by construction, and that is the
    -- contradiction. Note where the transitivity of ≼ is spent: the step from
    -- u ≼ t ≼ r is what makes the argument go through without any order
    -- reflection property of i, which no certificate has.

    semantic-order : LEM ℓ → (p q : Pt carrier)
      → (i q ≤ᴮ i p) ≡ (⋀ (Pt carrier) (λ r → (r ≼ q) ⇒ compatible r p))
    semantic-order lem p q = ⇔toPath forward backward
      where
        forward : ⟨ i q ≤ᴮ i p ⟩
                → ⟨ ⋀ (Pt carrier) (λ r → (r ≼ q) ⇒ compatible r p) ⟩
        forward le r r≼q = ≤→compatible r p (⊆ˢ-trans (i-mono r≼q) le)

        backward : ⟨ ⋀ (Pt carrier) (λ r → (r ≼ q) ⇒ compatible r p) ⟩
                 → ⟨ i q ≤ᴮ i p ⟩
        backward h with lem ((((i q) ⊓ᴮ (¬ᴮ (i p))) ≡ ⊥ᴮ)
                            , isSetPt B ((i q) ⊓ᴮ (¬ᴮ (i p))) ⊥ᴮ)
        ... | inl e  = ⊥-as-≤ (i q) (i p) e
        ... | inr ne = PT.rec (snd (i q ≤ᴮ i p)) step
                              (dense-form lem ((i q) ⊓ᴮ (¬ᴮ (i p))) posd)
          where
            posd : ⟨ positiveᴮ ((i q) ⊓ᴮ (¬ᴮ (i p))) ⟩
            posd e = Empty.rec (ne e)

            step : Σ[ r ∈ Pt carrier ] ⟨ i r ≤ᴮ ((i q) ⊓ᴮ (¬ᴮ (i p))) ⟩
                 → ⟨ i q ≤ᴮ i p ⟩
            step (r , hr) = Empty.rec* (i-compat→ r p comp-rp disjoint)
              where
                r≤q : ⟨ i r ≤ᴮ i q ⟩
                r≤q = ⊆ˢ-trans hr (⊓-lb₁ (i q) (¬ᴮ (i p)))

                disjoint : ((i r) ⊓ᴮ (i p)) ≡ ⊥ᴮ
                disjoint = ≤¬→⊓⊥ (i r) (i p)
                  (⊆ˢ-trans hr (⊓-lb₂ (i q) (¬ᴮ (i p))))

                inner2 : (t : Pt carrier) → ⟨ t ≼ r ⟩
                       → Σ[ u ∈ Pt carrier ] (⟨ u ≼ t ⟩ × ⟨ u ≼ p ⟩)
                       → ⟨ compatible r p ⟩
                inner2 t t≼r (u , u≼t , u≼p) = ∣ u , ≼-trans u≼t t≼r , u≼p ∣₁

                inner : Σ[ t ∈ Pt carrier ] (⟨ t ≼ r ⟩ × ⟨ t ≼ q ⟩)
                      → ⟨ compatible r p ⟩
                inner (t , t≼r , t≼q) =
                  PT.rec (snd (compatible r p)) (inner2 t t≼r) (h t t≼q)

                comp-rp : ⟨ compatible r p ⟩
                comp-rp = PT.rec (snd (compatible r p)) inner
                                 (≤→compatible r q r≤q)

    -- The kernel of the embedding is Bell's separative equality, Problem
    -- 2.4(i) (fulltext:3538-3539). This is what replaces an injectivity
    -- field: i is injective exactly on the presentations where separative
    -- equality is host equality, and that needs separativity AND
    -- antisymmetry, neither of which a certificate may assume.

    i-kernelᴮ : LEM ℓ → (p q : Pt carrier)
              → (i p ≡ i q) ≃ ⟨ separativelyEqual p q ⟩
    i-kernelᴮ lem p q = propBiimpl→Equiv
      (isSetPt B (i p) (i q)) (snd (separativelyEqual p q)) fwd bwd
      where
        fwd : i p ≡ i q → ⟨ separativelyEqual p q ⟩
        fwd e r =
            (λ crp → i-compat← r q
               (subst (λ z → ⟨ positiveᴮ ((i r) ⊓ᴮ z) ⟩) e (i-compat→ r p crp)))
          , (λ crq → i-compat← r p
               (subst (λ z → ⟨ positiveᴮ ((i r) ⊓ᴮ z) ⟩) (sym e)
                      (i-compat→ r q crq)))

        bwd : ⟨ separativelyEqual p q ⟩ → i p ≡ i q
        bwd se = ≤ᴮ-antisym
          (subst ⟨_⟩ (sym (semantic-order lem q p))
            (λ r r≼p → fst (se r) (≼-compatible r p r≼p)))
          (subst ⟨_⟩ (sym (semantic-order lem p q))
            (λ r r≼q → snd (se r) (≼-compatible r q r≼q)))

  --------------------------------------------------------------------------
  -- Complete subalgebras: a definition, and nothing more
  --------------------------------------------------------------------------

  -- Bell, printed page 33: a complete Boolean algebra B′ is a complete
  -- subalgebra of B when it is a subalgebra and, for any X ⊆ B′, the
  -- supremum and infimum of X formed in B′ are those formed in B
  -- (fulltext:2290-2292). Here the subalgebra is given by its code A, and
  -- the closure clause is stated for the coded families, which is the only
  -- class of families the algebra has suprema for at all.
  --
  -- Bell's Theorem 1.20 and Corollary 1.21 (fulltext:2294-2307) are about
  -- Boolean-valued names and their values, which do not exist at this layer.
  -- They are not promised here and must not be.

  module _ (c : CertifiedCompletion) where
    open Theory c

    record CompleteSubalgebra (A : S) : Type ℓ where
      field
        A-sub   : ⟨ A ⊆ˢ B ⟩
        has-⊤   : ⟨ fst ⊤ᴮ ∈ˢ A ⟩
        has-⊥   : ⟨ fst ⊥ᴮ ∈ˢ A ⟩
        has-⊓   : (u v : Pt B) → ⟨ fst u ∈ˢ A ⟩ → ⟨ fst v ∈ˢ A ⟩
                → ⟨ fst (u ⊓ᴮ v) ∈ˢ A ⟩
        has-⊔   : (u v : Pt B) → ⟨ fst u ∈ˢ A ⟩ → ⟨ fst v ∈ˢ A ⟩
                → ⟨ fst (u ⊔ᴮ v) ∈ˢ A ⟩
        has-¬   : (u : Pt B) → ⟨ fst u ∈ˢ A ⟩ → ⟨ fst (¬ᴮ u) ∈ˢ A ⟩
        has-sup : (X : S) (h : ⟨ X ⊆ˢ B ⟩) → ⟨ X ⊆ˢ A ⟩
                → ⟨ fst (supᴮ X h) ∈ˢ A ⟩
        has-inf : (X : S) (h : ⟨ X ⊆ˢ B ⟩) → ⟨ X ⊆ˢ A ⟩
                → ⟨ fst (infᴮ X h) ∈ˢ A ⟩

  --------------------------------------------------------------------------
  -- The comparison of two certified completions
  --------------------------------------------------------------------------

  -- Bell's Lemma 2.3 (fulltext:3477-3482) in the form his own proof uses:
  -- for x in B put P_x for the conditions whose image refines x; density
  -- gives x = ⋁ e[P_x], and the map sending x to the join of e′[P_x] is the
  -- isomorphism. Here P_x is the certificate's `below` and e′[P_x] is the
  -- other certificate's `iImage` of it, so the map is a composition of two
  -- fields and needs no choice, no host-indexed supremum, and, note, no
  -- excluded middle: LEM enters only in the laws.

  module _ (c c′ : CertifiedCompletion) where
    module C = Theory c
    module D = Theory c′

    compare : Pt C.B → Pt D.B
    compare b = D.supᴮ (D.iImage (C.below b))
                       (D.iImage-sub (C.below b) (C.below-sub b))

    -- The universal property of the comparison map, in two halves. Together
    -- they say that compare b is the least upper bound, in the second
    -- algebra, of the images of the conditions that the first algebra puts
    -- below b. Everything else about compare is derived from these two.

    compare-ub : (b : Pt C.B) (p : Pt carrier)
               → ⟨ C.i p ≤ᴮ b ⟩ → ⟨ D.i p ≤ᴮ compare b ⟩
    compare-ub b p le =
      D.sup-ub (D.iImage (C.below b))
               (D.iImage-sub (C.below b) (C.below-sub b)) (D.i p) mem
      where
        mem : ⟨ fst (D.i p) ∈ˢ D.iImage (C.below b) ⟩
        mem = subst ⟨_⟩ (sym (D.iImage-spec (C.below b) (D.i p)))
          ∣ p , subst ⟨_⟩ (sym (C.below-spec b p)) le
              , path-to-≈ˢ (fst (D.i p)) (fst (D.i p)) refl ∣₁

    compare-lub : (b : Pt C.B) (v : Pt D.B)
                → ((p : Pt carrier) → ⟨ C.i p ≤ᴮ b ⟩ → ⟨ D.i p ≤ᴮ v ⟩)
                → ⟨ compare b ≤ᴮ v ⟩
    compare-lub b v h =
      D.sup-lub (D.iImage (C.below b))
                (D.iImage-sub (C.below b) (C.below-sub b)) v step
      where
        step : (u : Pt D.B) → ⟨ fst u ∈ˢ D.iImage (C.below b) ⟩ → ⟨ u ≤ᴮ v ⟩
        step u hu = PT.rec (snd (u ≤ᴮ v)) pick
          (subst ⟨_⟩ (D.iImage-spec (C.below b) u) hu)
          where
            pick : Σ[ p ∈ Pt carrier ]
                     (⟨ fst p ∈ˢ C.below b ⟩ × ⟨ fst u ≈ˢ fst (D.i p) ⟩)
                 → ⟨ u ≤ᴮ v ⟩
            pick (p , hp , heq) =
              subst (λ z → ⟨ z ⊆ˢ fst v ⟩)
                (sym (≈ˢ-to-path (fst u) (fst (D.i p)) heq))
                (h p (subst ⟨_⟩ (C.below-spec b p) hp))

    compare-mono : (b b' : Pt C.B) → ⟨ b ≤ᴮ b' ⟩ → ⟨ compare b ≤ᴮ compare b' ⟩
    compare-mono b b' le =
      compare-lub b (compare b') (λ p h → compare-ub b' p (⊆ˢ-trans h le))

    -- The refinement relation between images of conditions is the same in
    -- both algebras, because the semantic order theorem characterises it by
    -- a condition on the presentation alone. This single lemma is what makes
    -- the comparison possible at all, and it is the reason every law below
    -- carries LEM while the map itself does not.

    i-transfer : LEM ℓ → (p q : Pt carrier)
               → ⟨ C.i q ≤ᴮ C.i p ⟩ → ⟨ D.i q ≤ᴮ D.i p ⟩
    i-transfer lem p q le =
      subst ⟨_⟩ (sym (D.semantic-order lem p q))
        (subst ⟨_⟩ (C.semantic-order lem p q) le)

    -- The converse of compare-ub, which is the hard half of the comparison.
    -- If the image of p in the second algebra refines compare b, then p was
    -- already below b in the first. The argument runs entirely in the first
    -- algebra until the last step: if p is not below b, density gives a
    -- condition r with image under i p and disjoint from b, hence
    -- incompatible with every condition below b; compatibility transfers, so
    -- the image of r in the second algebra is disjoint from the image of
    -- every condition below b, so compare b refines the complement of that
    -- image; but the image of r refines the image of p, which refines
    -- compare b, so the image of r is zero, and no image is zero.

    compare-below : LEM ℓ → (b : Pt C.B) (p : Pt carrier)
                  → ⟨ D.i p ≤ᴮ compare b ⟩ → ⟨ C.i p ≤ᴮ b ⟩
    compare-below lem b p hp with lem (C.i p ≤ᴮ b)
    ... | inl h = h
    ... | inr n = PT.rec (snd (C.i p ≤ᴮ b)) step
      (C.dense-form lem ((C.i p) C.⊓ᴮ (C.¬ᴮ b)) posd)
      where
        posd : ⟨ C.positiveᴮ ((C.i p) C.⊓ᴮ (C.¬ᴮ b)) ⟩
        posd e = Empty.rec (n (C.⊥-as-≤ (C.i p) b e))

        step : Σ[ r ∈ Pt carrier ] ⟨ C.i r ≤ᴮ ((C.i p) C.⊓ᴮ (C.¬ᴮ b)) ⟩
             → ⟨ C.i p ≤ᴮ b ⟩
        step (r , hr) = Empty.rec* (D.i-pos r rzero)
          where
            r≤p : ⟨ C.i r ≤ᴮ C.i p ⟩
            r≤p = ⊆ˢ-trans hr (C.⊓-lb₁ (C.i p) (C.¬ᴮ b))

            r≤¬b : ⟨ C.i r ≤ᴮ (C.¬ᴮ b) ⟩
            r≤¬b = ⊆ˢ-trans hr (C.⊓-lb₂ (C.i p) (C.¬ᴮ b))

            ncomp : (s : Pt carrier) → ⟨ C.i s ≤ᴮ b ⟩
                  → ⟨ compatible s r ⟩ → Empty.⊥
            ncomp s hs cm = Empty.rec*
              (C.i-compat→ s r cm (C.disjoint-of-≤ (C.i s) (C.i r) b hs r≤¬b))

            sdisj : (s : Pt carrier) → ⟨ C.i s ≤ᴮ b ⟩
                  → ⟨ D.i s ≤ᴮ (D.¬ᴮ (D.i r)) ⟩
            sdisj s hs = D.⊓⊥→≤¬ (D.i s) (D.i r) dis
              where
                dis : ((D.i s) D.⊓ᴮ (D.i r)) ≡ D.⊥ᴮ
                dis with lem ((((D.i s) D.⊓ᴮ (D.i r)) ≡ D.⊥ᴮ)
                             , isSetPt D.B ((D.i s) D.⊓ᴮ (D.i r)) D.⊥ᴮ)
                ... | inl e  = e
                ... | inr nz = Empty.rec
                  (ncomp s hs (D.i-compat← s r (λ e → Empty.rec (nz e))))

            rzero : D.i r ≡ D.⊥ᴮ
            rzero = sym (D.⊓-idem (D.i r)) ∙ D.≤¬→⊓⊥ (D.i r) (D.i r)
              (⊆ˢ-trans (⊆ˢ-trans (i-transfer lem p r r≤p) hp)
                        (compare-lub b (D.¬ᴮ (D.i r)) sdisj))

    -- The comparison map interchanges the two embeddings, which is Bell's
    -- "interchanges e[P] and e′[P]" (fulltext:3478).

    compare-i : LEM ℓ → (p : Pt carrier) → compare (C.i p) ≡ D.i p
    compare-i lem p = ≤ᴮ-antisym
      (compare-lub (C.i p) (D.i p) (λ r h → i-transfer lem p r h))
      (compare-ub (C.i p) p (≤ᴮ-refl (C.i p)))

  -- The comparison of a certificate with itself is the identity, and this is
  -- not a coincidence of the definition: it IS the density field, spelled
  -- out. No hypothesis at all, LEM included.

  compare-id : (c : CertifiedCompletion) (b : Pt (CertifiedCompletion.B c))
             → compare c c b ≡ b
  compare-id c b = Theory.recover c b

  -- Composition. The forward inclusion is immediate from the two universal
  -- properties; the backward one is where compare-below is spent, since it
  -- must recognise the conditions that the middle algebra puts below the
  -- intermediate element as exactly those the first algebra puts below b.

  module _ (c c′ c″ : CertifiedCompletion) where

    compare-comp : LEM ℓ → (b : Pt (CertifiedCompletion.B c))
                 → compare c′ c″ (compare c c′ b) ≡ compare c c″ b
    compare-comp lem b = ≤ᴮ-antisym
      (compare-lub c′ c″ (compare c c′ b) (compare c c″ b)
        (λ p hp → compare-ub c c″ b p (compare-below c c′ lem b p hp)))
      (compare-lub c c″ b (compare c′ c″ (compare c c′ b))
        (λ p hp → compare-ub c′ c″ (compare c c′ b) p (compare-ub c c′ b p hp)))

  -- Composing the two comparisons in either order is the identity, so each
  -- is a bijection. This is the first half of "isomorphism, both directions".

  compare-inv : (c c′ : CertifiedCompletion) → LEM ℓ
              → (b : Pt (CertifiedCompletion.B c))
              → compare c′ c (compare c c′ b) ≡ b
  compare-inv c c′ lem b = compare-comp c c′ c lem b ∙ compare-id c b

  -- Uniqueness. Any order isomorphism commuting with the two embeddings is
  -- the comparison map. Bell asserts existence only; this is the statement
  -- that makes the completion unique rather than merely comparable, and it
  -- needs no excluded middle, because the only property of b it uses is that
  -- b is the least upper bound of the images below it, which is the density
  -- field read through compare-id.

  module _ (c c′ : CertifiedCompletion) where
    module G = Theory c
    module H = Theory c′

    compare-unique :
        (f : Pt G.B → Pt H.B) (g : Pt H.B → Pt G.B)
      → ((u v : Pt G.B) → ⟨ u ≤ᴮ v ⟩ → ⟨ f u ≤ᴮ f v ⟩)
      → ((u v : Pt H.B) → ⟨ u ≤ᴮ v ⟩ → ⟨ g u ≤ᴮ g v ⟩)
      → ((u : Pt G.B) → g (f u) ≡ u)
      → ((v : Pt H.B) → f (g v) ≡ v)
      → ((p : Pt carrier) → f (G.i p) ≡ H.i p)
      → (b : Pt G.B) → f b ≡ compare c c′ b
    compare-unique f g mf mg gf fg fi b = ≤ᴮ-antisym above below
      where
        below : ⟨ compare c c′ b ≤ᴮ f b ⟩
        below = compare-lub c c′ b (f b)
          (λ p hp → subst (λ z → ⟨ z ≤ᴮ f b ⟩) (fi p) (mf (G.i p) b hp))

        below-g : ⟨ b ≤ᴮ g (compare c c′ b) ⟩
        below-g = subst (λ z → ⟨ z ≤ᴮ g (compare c c′ b) ⟩) (compare-id c b)
          (compare-lub c c b (g (compare c c′ b))
            (λ p hp → subst (λ z → ⟨ z ≤ᴮ g (compare c c′ b) ⟩)
              (cong g (sym (fi p)) ∙ gf (G.i p))
              (mg (H.i p) (compare c c′ b) (compare-ub c c′ b p hp))))

        above : ⟨ f b ≤ᴮ compare c c′ b ⟩
        above = subst (λ z → ⟨ f b ≤ᴮ z ⟩) (fg (compare c c′ b))
                      (mf b (g (compare c c′ b)) below-g)

  -- The second half of "isomorphism, both directions": the comparison map is
  -- a homomorphism of the whole Boolean structure. Each law is forced by the
  -- universal property of the operation together with the fact that the
  -- inverse is monotone as well; the complement is forced by uniqueness of
  -- complements.

  module _ (c c′ : CertifiedCompletion) (lem : LEM ℓ) where
    module E = Theory c
    module F = Theory c′

    compare-⊓ : (u v : Pt E.B)
      → compare c c′ (u E.⊓ᴮ v) ≡ ((compare c c′ u) F.⊓ᴮ (compare c c′ v))
    compare-⊓ u v = ≤ᴮ-antisym
      (F.⊓-glb (compare c c′ u) (compare c c′ v) (compare c c′ (u E.⊓ᴮ v))
        (compare-mono c c′ (u E.⊓ᴮ v) u (E.⊓-lb₁ u v))
        (compare-mono c c′ (u E.⊓ᴮ v) v (E.⊓-lb₂ u v)))
      (subst (λ z → ⟨ z ≤ᴮ compare c c′ (u E.⊓ᴮ v) ⟩)
        (compare-inv c′ c lem ((compare c c′ u) F.⊓ᴮ (compare c c′ v)))
        (compare-mono c c′
          (compare c′ c ((compare c c′ u) F.⊓ᴮ (compare c c′ v))) (u E.⊓ᴮ v) gw))
      where
        gw : ⟨ compare c′ c ((compare c c′ u) F.⊓ᴮ (compare c c′ v))
              ≤ᴮ (u E.⊓ᴮ v) ⟩
        gw = E.⊓-glb u v
          (compare c′ c ((compare c c′ u) F.⊓ᴮ (compare c c′ v)))
          (subst (λ z → ⟨ compare c′ c
                            ((compare c c′ u) F.⊓ᴮ (compare c c′ v)) ≤ᴮ z ⟩)
            (compare-inv c c′ lem u)
            (compare-mono c′ c ((compare c c′ u) F.⊓ᴮ (compare c c′ v))
              (compare c c′ u) (F.⊓-lb₁ (compare c c′ u) (compare c c′ v))))
          (subst (λ z → ⟨ compare c′ c
                            ((compare c c′ u) F.⊓ᴮ (compare c c′ v)) ≤ᴮ z ⟩)
            (compare-inv c c′ lem v)
            (compare-mono c′ c ((compare c c′ u) F.⊓ᴮ (compare c c′ v))
              (compare c c′ v) (F.⊓-lb₂ (compare c c′ u) (compare c c′ v))))

    compare-⊔ : (u v : Pt E.B)
      → compare c c′ (u E.⊔ᴮ v) ≡ ((compare c c′ u) F.⊔ᴮ (compare c c′ v))
    compare-⊔ u v = ≤ᴮ-antisym
      (subst (λ z → ⟨ compare c c′ (u E.⊔ᴮ v) ≤ᴮ z ⟩)
        (compare-inv c′ c lem ((compare c c′ u) F.⊔ᴮ (compare c c′ v)))
        (compare-mono c c′ (u E.⊔ᴮ v)
          (compare c′ c ((compare c c′ u) F.⊔ᴮ (compare c c′ v))) gw))
      (F.⊔-lub (compare c c′ u) (compare c c′ v) (compare c c′ (u E.⊔ᴮ v))
        (compare-mono c c′ u (u E.⊔ᴮ v) (E.⊔-ub₁ u v))
        (compare-mono c c′ v (u E.⊔ᴮ v) (E.⊔-ub₂ u v)))
      where
        gw : ⟨ (u E.⊔ᴮ v)
              ≤ᴮ compare c′ c ((compare c c′ u) F.⊔ᴮ (compare c c′ v)) ⟩
        gw = E.⊔-lub u v
          (compare c′ c ((compare c c′ u) F.⊔ᴮ (compare c c′ v)))
          (subst (λ z → ⟨ z ≤ᴮ compare c′ c
                            ((compare c c′ u) F.⊔ᴮ (compare c c′ v)) ⟩)
            (compare-inv c c′ lem u)
            (compare-mono c′ c (compare c c′ u)
              ((compare c c′ u) F.⊔ᴮ (compare c c′ v))
              (F.⊔-ub₁ (compare c c′ u) (compare c c′ v))))
          (subst (λ z → ⟨ z ≤ᴮ compare c′ c
                            ((compare c c′ u) F.⊔ᴮ (compare c c′ v)) ⟩)
            (compare-inv c c′ lem v)
            (compare-mono c′ c (compare c c′ v)
              ((compare c c′ u) F.⊔ᴮ (compare c c′ v))
              (F.⊔-ub₂ (compare c c′ u) (compare c c′ v))))

    compare-⊤ : compare c c′ E.⊤ᴮ ≡ F.⊤ᴮ
    compare-⊤ = ≤ᴮ-antisym (F.⊤-greatest (compare c c′ E.⊤ᴮ))
      (subst (λ z → ⟨ z ≤ᴮ compare c c′ E.⊤ᴮ ⟩) (compare-inv c′ c lem F.⊤ᴮ)
        (compare-mono c c′ (compare c′ c F.⊤ᴮ) E.⊤ᴮ
          (E.⊤-greatest (compare c′ c F.⊤ᴮ))))

    compare-⊥ : compare c c′ E.⊥ᴮ ≡ F.⊥ᴮ
    compare-⊥ = ≤ᴮ-antisym
      (subst (λ z → ⟨ compare c c′ E.⊥ᴮ ≤ᴮ z ⟩) (compare-inv c′ c lem F.⊥ᴮ)
        (compare-mono c c′ E.⊥ᴮ (compare c′ c F.⊥ᴮ)
          (E.⊥-least (compare c′ c F.⊥ᴮ))))
      (F.⊥-least (compare c c′ E.⊥ᴮ))

    compare-¬ : (u : Pt E.B)
      → compare c c′ (E.¬ᴮ u) ≡ (F.¬ᴮ (compare c c′ u))
    compare-¬ u = F.complement-unique (compare c c′ u)
      (compare c c′ (E.¬ᴮ u)) (F.¬ᴮ (compare c c′ u))
      (sym (compare-⊓ u (E.¬ᴮ u)) ∙ cong (compare c c′) (E.¬-⊓ u) ∙ compare-⊥)
      (sym (compare-⊔ u (E.¬ᴮ u)) ∙ cong (compare c c′) (E.¬-⊔ u) ∙ compare-⊤)
      (F.¬-⊓ (compare c c′ u))
      (F.¬-⊔ (compare c c′ u))

--------------------------------------------------------------------------------
-- The nonzero part of a certified algebra
--------------------------------------------------------------------------------

-- Bell, printed page 56: "P is refined iff it is order-isomorphic to a dense
-- subset of a complete Boolean algebra" (fulltext:3466-3467), and the proof of
-- the converse is exactly the argument below. The nonzero part of the algebra
-- is the canonical such dense subset, and it is separative whatever the
-- presentation it came from was, which is what makes B⁺ the adapter that
-- turns an arbitrary presentation into a separative one.
--
-- Totality needs the nontriviality field and nothing else: a presentation
-- must be inhabited, and the only element available to inhabit the nonzero
-- part with is the top, which is nonzero exactly when the algebra is
-- nondegenerate. This is the second trap of the track brief, and it is
-- discharged by making `nontrivial` a field rather than a hypothesis of the
-- construction.

module Nonzero (𝔓 : Presentation) (c : Over.CertifiedCompletion 𝔓)
               (sep : Separation) where

  module P = Over 𝔓
  module C = P.Theory c

  -- The nonzero part is cut out of B by one Separation, using the object
  -- language formula "not equal to the code of the bottom". No PowerSet, no
  -- Pairing, no Union, no LEM.

  botCode : S
  botCode = fst C.⊥ᴮ

  nonzeroFo : Formula S 1
  nonzeroFo = ¬̇ (var zero ≐ con botCode)

  B⁺set : S
  B⁺set = separateOf sep C.B nonzeroFo

  B⁺spec : (x : S) → (x ∈ˢ B⁺set) ≡ ((x ∈ˢ C.B) ⊓ ((x ≈ˢ botCode) ⇒ ⊥))
  B⁺spec = separateOf-spec sep C.B nonzeroFo

  toEl : Pt B⁺set → Pt C.B
  toEl u = fst u , fst (subst ⟨_⟩ (B⁺spec (fst u)) (snd u))

  toEl-pos : (u : Pt B⁺set) → ⟨ C.positiveᴮ (toEl u) ⟩
  toEl-pos u e = snd (subst ⟨_⟩ (B⁺spec (fst u)) (snd u))
                     (path-to-≈ˢ (fst u) botCode (cong fst e))

  fromEl : (u : Pt C.B) → ⟨ C.positiveᴮ u ⟩ → Pt B⁺set
  fromEl u pu = fst u , subst ⟨_⟩ (sym (B⁺spec (fst u)))
    (snd u , λ h → pu (Pt≡ (≈ˢ-to-path (fst u) botCode h)))

  -- The presentation. Its order is the algebra's own order, restricted; that
  -- is Bell's "P will be regarded as a dense subset of B" (fulltext:3486).

  B⁺ : Presentation
  B⁺ = record
    { carrier   = B⁺set
    ; _≼_       = λ u v → fst u ⊆ˢ fst v
    ; ≼-refl    = λ u → ≤ᴮ-refl u
    ; ≼-trans   = ⊆ˢ-trans
    ; inhabited = ∣ fromEl C.⊤ᴮ C.⊤-positive ∣₁ }

  module Q = Over B⁺

  -- Bell's Corollary 2.2, converse direction: given u not refining v, the
  -- element v ⊓ ¬u is nonzero, refines v, and is incompatible with u, since a
  -- common refinement would be below both a thing and its complement.
  -- Constructive, and it uses nothing but the lattice laws.

  B⁺-separative : Q.separative
  B⁺-separative u v nle = ∣ w⁺ , C.⊓-lb₁ (toEl v) (C.¬ᴮ (toEl u)) , winc ∣₁
    where
      w : Pt C.B
      w = (toEl v) C.⊓ᴮ (C.¬ᴮ (toEl u))

      wpos : ⟨ C.positiveᴮ w ⟩
      wpos e = nle (C.⊥-as-≤ (toEl v) (toEl u) e)

      w⁺ : Pt B⁺set
      w⁺ = fromEl w wpos

      winc : ⟨ Q.incompatible w⁺ u ⟩
      winc = PT.rec (snd ⊥) collide
        where
          collide : Σ[ t ∈ Pt B⁺set ]
                      (⟨ fst t ⊆ˢ fst w⁺ ⟩ × ⟨ fst t ⊆ˢ fst u ⟩) → ⟨ ⊥ ⟩
          collide (t , t≼w , t≼u) = toEl-pos t
            (sym (C.≤→⊓ (toEl t) (toEl u) t≼u)
             ∙ C.≤¬→⊓⊥ (toEl t) (toEl u)
                 (⊆ˢ-trans t≼w (C.⊓-lb₂ (toEl v) (C.¬ᴮ (toEl u)))))

  -- The nonzero part has a largest element, namely the top of the algebra.

  B⁺-top : Q.Top
  B⁺-top = fromEl C.⊤ᴮ C.⊤-positive , λ v → C.⊤-greatest (toEl v)

  --------------------------------------------------------------------------
  -- The unit: B certifies its own completion
  --------------------------------------------------------------------------

  -- The same algebra, the same lattice, the same completeness, with the
  -- inclusion of the nonzero part as the embedding. Two Separations build the
  -- two coded operations, and the density field is inherited from the
  -- original certificate rather than reproved: every condition below b in the
  -- original sense is a nonzero element below b, so the two suprema have the
  -- same upper bounds.

  below⁺ : Pt C.B → S
  below⁺ b = separateOf sep B⁺set (∀̇∈ (var zero) (var zero ∈̇ con (fst b)))

  below⁺spec : (b : Pt C.B) (x : S)
             → (x ∈ˢ below⁺ b) ≡ ((x ∈ˢ B⁺set) ⊓ (x ⊆ˢ fst b))
  below⁺spec b = separateOf-spec sep B⁺set
    (∀̇∈ (var zero) (var zero ∈̇ con (fst b)))

  iImage⁺ : S → S
  iImage⁺ d = separateOf sep C.B ((var zero ∈̇ con d) ∧̇ (var zero ∈̇ con B⁺set))

  iImage⁺spec : (d x : S)
              → (x ∈ˢ iImage⁺ d)
              ≡ ((x ∈ˢ C.B) ⊓ ((x ∈ˢ d) ⊓ (x ∈ˢ B⁺set)))
  iImage⁺spec d = separateOf-spec sep C.B
    ((var zero ∈̇ con d) ∧̇ (var zero ∈̇ con B⁺set))

  iImage⁺sub : (d : S) → ⟨ d ⊆ˢ B⁺set ⟩ → ⟨ iImage⁺ d ⊆ˢ C.B ⟩
  iImage⁺sub d _ x h = fst (subst ⟨_⟩ (iImage⁺spec d x) h)

  below⁺sub : (b : Pt C.B) → ⟨ below⁺ b ⊆ˢ B⁺set ⟩
  below⁺sub b x h = fst (subst ⟨_⟩ (below⁺spec b x) h)

  unitEmbedding : Q.Embedding C.B C.lattice C.complete
  unitEmbedding = record
    { i         = toEl
    ; i-mono    = λ h → h
    ; i-pos     = toEl-pos
    ; i-compat→ = compat→
    ; i-compat← = compat←
    ; below      = below⁺
    ; below-sub  = below⁺sub
    ; below-spec = bspec
    ; iImage      = iImage⁺
    ; iImage-sub  = iImage⁺sub
    ; iImage-spec = ispec
    ; recover     = rec }
    where
      compat→ : (u v : Pt B⁺set) → ⟨ Q.compatible u v ⟩
              → ⟨ C.positiveᴮ ((toEl u) C.⊓ᴮ (toEl v)) ⟩
      compat→ u v cm e = PT.rec (snd ⊥) step cm
        where
          step : Σ[ t ∈ Pt B⁺set ]
                   (⟨ fst t ⊆ˢ fst u ⟩ × ⟨ fst t ⊆ˢ fst v ⟩) → ⟨ ⊥ ⟩
          step (t , t≼u , t≼v) = toEl-pos t
            (C.≤⊥→≡⊥ (toEl t)
              (subst (λ z → ⟨ fst (toEl t) ⊆ˢ fst z ⟩) e
                (C.⊓-glb (toEl u) (toEl v) (toEl t) t≼u t≼v)))

      compat← : (u v : Pt B⁺set)
              → ⟨ C.positiveᴮ ((toEl u) C.⊓ᴮ (toEl v)) ⟩ → ⟨ Q.compatible u v ⟩
      compat← u v pos =
        ∣ fromEl ((toEl u) C.⊓ᴮ (toEl v)) pos
        , C.⊓-lb₁ (toEl u) (toEl v)
        , C.⊓-lb₂ (toEl u) (toEl v) ∣₁

      bspec : (b : Pt C.B) (u : Pt B⁺set)
            → (fst u ∈ˢ below⁺ b) ≡ (toEl u ≤ᴮ b)
      bspec b u = below⁺spec b (fst u) ∙ ⇔toPath snd (λ h → snd u , h)

      ispec : (d : S) (u : Pt C.B)
            → (fst u ∈ˢ iImage⁺ d)
            ≡ ⋁ (Pt B⁺set) (λ p → (fst p ∈ˢ d) ⊓ (fst u ≈ˢ fst (toEl p)))
      ispec d u = iImage⁺spec d (fst u) ∙ ⇔toPath fwd bwd
        where
          fwd : ⟨ (fst u ∈ˢ C.B) ⊓ ((fst u ∈ˢ d) ⊓ (fst u ∈ˢ B⁺set)) ⟩
              → ⟨ ⋁ (Pt B⁺set)
                    (λ p → (fst p ∈ˢ d) ⊓ (fst u ≈ˢ fst (toEl p))) ⟩
          fwd (_ , hd , hb) =
            ∣ (fst u , hb) , hd , path-to-≈ˢ (fst u) (fst u) refl ∣₁

          bwd : ⟨ ⋁ (Pt B⁺set)
                    (λ p → (fst p ∈ˢ d) ⊓ (fst u ≈ˢ fst (toEl p))) ⟩
              → ⟨ (fst u ∈ˢ C.B) ⊓ ((fst u ∈ˢ d) ⊓ (fst u ∈ˢ B⁺set)) ⟩
          bwd = PT.rec (snd ((fst u ∈ˢ C.B) ⊓ ((fst u ∈ˢ d) ⊓ (fst u ∈ˢ B⁺set))))
            (λ { (p , hd , heq) →
                 let e = ≈ˢ-to-path (fst u) (fst p) heq in
                 snd u
               , subst (λ z → ⟨ z ∈ˢ d ⟩) (sym e) hd
               , subst (λ z → ⟨ z ∈ˢ B⁺set ⟩) (sym e) (snd p) })

      rec : (b : Pt C.B)
          → C.supᴮ (iImage⁺ (below⁺ b))
                   (iImage⁺sub (below⁺ b) (below⁺sub b)) ≡ b
      rec b = ≤ᴮ-antisym down up
        where
          h⁺ : ⟨ iImage⁺ (below⁺ b) ⊆ˢ C.B ⟩
          h⁺ = iImage⁺sub (below⁺ b) (below⁺sub b)

          down : ⟨ C.supᴮ (iImage⁺ (below⁺ b)) h⁺ ≤ᴮ b ⟩
          down = C.sup-lub (iImage⁺ (below⁺ b)) h⁺ b step
            where
              step : (u : Pt C.B) → ⟨ fst u ∈ˢ iImage⁺ (below⁺ b) ⟩
                   → ⟨ u ≤ᴮ b ⟩
              step u hu =
                snd (subst ⟨_⟩ (below⁺spec b (fst u))
                  (fst (snd (subst ⟨_⟩ (iImage⁺spec (below⁺ b) (fst u)) hu))))

          up : ⟨ b ≤ᴮ C.supᴮ (iImage⁺ (below⁺ b)) h⁺ ⟩
          up = subst (λ z → ⟨ fst z ⊆ˢ fst (C.supᴮ (iImage⁺ (below⁺ b)) h⁺) ⟩)
            (C.recover b)
            (C.sup-lub (C.iImage (C.below b))
              (C.iImage-sub (C.below b) (C.below-sub b))
              (C.supᴮ (iImage⁺ (below⁺ b)) h⁺) step)
            where
              step : (u : Pt C.B) → ⟨ fst u ∈ˢ C.iImage (C.below b) ⟩
                   → ⟨ u ≤ᴮ C.supᴮ (iImage⁺ (below⁺ b)) h⁺ ⟩
              step u hu = PT.rec (snd (u ≤ᴮ C.supᴮ (iImage⁺ (below⁺ b)) h⁺))
                pick (subst ⟨_⟩ (C.iImage-spec (C.below b) u) hu)
                where
                  pick : Σ[ p ∈ Pt P.carrier ]
                           (⟨ fst p ∈ˢ C.below b ⟩ × ⟨ fst u ≈ˢ fst (C.i p) ⟩)
                       → ⟨ u ≤ᴮ C.supᴮ (iImage⁺ (below⁺ b)) h⁺ ⟩
                  pick (p , hp , heq) =
                    subst (λ z → ⟨ z ⊆ˢ fst (C.supᴮ (iImage⁺ (below⁺ b)) h⁺) ⟩)
                      (sym (≈ˢ-to-path (fst u) (fst (C.i p)) heq))
                      (C.sup-ub (iImage⁺ (below⁺ b)) h⁺ (C.i p) mem)
                    where
                      q : Pt B⁺set
                      q = fromEl (C.i p) (C.i-pos p)

                      inbelow : ⟨ fst (C.i p) ∈ˢ below⁺ b ⟩
                      inbelow = subst ⟨_⟩ (sym (below⁺spec b (fst (C.i p))))
                        (snd q , subst ⟨_⟩ (C.below-spec b p) hp)

                      mem : ⟨ fst (C.i p) ∈ˢ iImage⁺ (below⁺ b) ⟩
                      mem = subst ⟨_⟩ (sym (iImage⁺spec (below⁺ b) (fst (C.i p))))
                        (snd (C.i p) , inbelow , snd q)

  unit : Q.CertifiedCompletion
  unit = record
    { B          = C.B
    ; lattice    = C.lattice
    ; boolean    = C.boolean
    ; complete   = C.complete
    ; nontrivial = C.nontrivial
    ; embedding  = unitEmbedding }

--------------------------------------------------------------------------------
-- The dense-map category
--------------------------------------------------------------------------------

-- A dense map is the only kind of map along which a certificate transports.
-- Monotonicity alone is not enough and must not be accepted: the transported
-- density field needs a condition of the source below an arbitrary condition
-- of the target, which is exactly the `dense` field, and the transported
-- compatibility fields need BOTH directions of compat, since the certificate
-- has an equivalence there and not an implication.
--
-- Beside the map itself the record carries its coded direct image and coded
-- inverse image, with their specifications. Those are what the two coded
-- operations of a transported certificate are built from. They are exactly
-- what one Separation against the graph of the map produces, and they are
-- taken as fields rather than constructed here because constructing them
-- needs the ordered-pair fragment, which the core of K2 deliberately does not
-- take; see this track's report.

module Maps (𝔓 𝔔 : Presentation) where

  module P = Over 𝔓
  module Q = Over 𝔔

  record DenseMap : Type (ℓ-suc ℓ) where
    field
      map     : Pt P.carrier → Pt Q.carrier
      mono    : (p q : Pt P.carrier) → ⟨ p P.≼ q ⟩ → ⟨ map p Q.≼ map q ⟩
      compat→ : (p q : Pt P.carrier)
              → ⟨ P.compatible p q ⟩ → ⟨ Q.compatible (map p) (map q) ⟩
      compat← : (p q : Pt P.carrier)
              → ⟨ Q.compatible (map p) (map q) ⟩ → ⟨ P.compatible p q ⟩
      dense   : (q : Pt Q.carrier)
              → ⟨ ⋁ (Pt P.carrier) (λ p → map p Q.≼ q) ⟩
      image      : S → S
      image-sub  : (d : S) → ⟨ d ⊆ˢ P.carrier ⟩ → ⟨ image d ⊆ˢ Q.carrier ⟩
      image-spec : (d : S) (q : Pt Q.carrier)
                 → (fst q ∈ˢ image d)
                 ≡ ⋁ (Pt P.carrier) (λ p → (fst p ∈ˢ d) ⊓ (fst q ≈ˢ fst (map p)))
      preimage      : S → S
      preimage-sub  : (e : S) → ⟨ e ⊆ˢ Q.carrier ⟩
                    → ⟨ preimage e ⊆ˢ P.carrier ⟩
      preimage-spec : (e : S) → ⟨ e ⊆ˢ Q.carrier ⟩ → (p : Pt P.carrier)
                    → (fst p ∈ˢ preimage e) ≡ (fst (map p) ∈ˢ e)

-- The identity is dense, with both coded operations the identity on sets.
-- Note that the inverse image is specified only for subsets of the target
-- carrier, which is what makes the identity's inverse image the set itself:
-- an unrestricted inverse image would have to intersect with the carrier and
-- would need a Separation even here.

id-dense : (𝔓 : Presentation) → Maps.DenseMap 𝔓 𝔓
id-dense 𝔓 = record
  { map     = λ p → p
  ; mono    = λ p q h → h
  ; compat→ = λ p q h → h
  ; compat← = λ p q h → h
  ; dense   = λ q → ∣ q , Over.≼-refl 𝔓 q ∣₁
  ; image         = λ d → d
  ; image-sub     = λ d h → h
  ; image-spec    = ispec
  ; preimage      = λ e → e
  ; preimage-sub  = λ e h → h
  ; preimage-spec = λ e h p → refl }
  where
    open Over 𝔓
    ispec : (d : S) (q : Pt carrier)
          → (fst q ∈ˢ d)
          ≡ ⋁ (Pt carrier) (λ p → (fst p ∈ˢ d) ⊓ (fst q ≈ˢ fst p))
    ispec d q = ⇔toPath
      (λ h → ∣ q , h , path-to-≈ˢ (fst q) (fst q) refl ∣₁)
      (PT.rec (snd (fst q ∈ˢ d))
        (λ { (p , hp , heq) →
             subst (λ z → ⟨ z ∈ˢ d ⟩)
               (sym (≈ˢ-to-path (fst q) (fst p) heq)) hp }))

-- Composition. Both coded operations compose in the evident order, and the
-- density of the composite is where the monotonicity of the second map is
-- spent: a condition below a condition below r is below r.

_∘ᴰ_ : {𝔓 𝔔 ℛ : Presentation}
     → Maps.DenseMap 𝔔 ℛ → Maps.DenseMap 𝔓 𝔔 → Maps.DenseMap 𝔓 ℛ
_∘ᴰ_ {𝔓} {𝔔} {ℛ} g f = record
  { map     = λ p → G.map (F.map p)
  ; mono    = λ p q h → G.mono (F.map p) (F.map q) (F.mono p q h)
  ; compat→ = λ p q h → G.compat→ (F.map p) (F.map q) (F.compat→ p q h)
  ; compat← = λ p q h → F.compat← p q (G.compat← (F.map p) (F.map q) h)
  ; dense   = dns
  ; image         = λ d → G.image (F.image d)
  ; image-sub     = λ d h → G.image-sub (F.image d) (F.image-sub d h)
  ; image-spec    = ispec
  ; preimage      = λ e → F.preimage (G.preimage e)
  ; preimage-sub  = λ e h →
      F.preimage-sub (G.preimage e) (G.preimage-sub e h)
  ; preimage-spec = λ e h p →
      F.preimage-spec (G.preimage e) (G.preimage-sub e h) p
      ∙ G.preimage-spec e h (F.map p) }
  where
    module F = Maps.DenseMap {𝔓} {𝔔} f
    module G = Maps.DenseMap {𝔔} {ℛ} g
    module R = Over ℛ

    dns : (r : Pt (Over.carrier ℛ))
        → ⟨ ⋁ (Pt (Over.carrier 𝔓)) (λ p → G.map (F.map p) R.≼ r) ⟩
    dns r = PT.rec PT.isPropPropTrunc
      (λ { (q , hq) → PT.map
             (λ { (p , hp) →
                  p , R.≼-trans (G.mono (F.map p) q hp) hq })
             (F.dense q) })
      (G.dense r)

    ispec : (d : S) (r : Pt (Over.carrier ℛ))
          → (fst r ∈ˢ G.image (F.image d))
          ≡ ⋁ (Pt (Over.carrier 𝔓))
              (λ p → (fst p ∈ˢ d) ⊓ (fst r ≈ˢ fst (G.map (F.map p))))
    ispec d r = G.image-spec (F.image d) r ∙ ⇔toPath fwd bwd
      where
        target : Ω
        target = ⋁ (Pt (Over.carrier 𝔓))
                   (λ p → (fst p ∈ˢ d) ⊓ (fst r ≈ˢ fst (G.map (F.map p))))

        fwd : ⟨ ⋁ (Pt (Over.carrier 𝔔))
                  (λ q → (fst q ∈ˢ F.image d) ⊓ (fst r ≈ˢ fst (G.map q))) ⟩
            → ⟨ target ⟩
        fwd = PT.rec (snd target)
          (λ { (q , hq , heq) → PT.map
                 (λ { (p , hp , heq') →
                      p , hp , subst (λ z → ⟨ fst r ≈ˢ fst (G.map z) ⟩)
                                 (Pt≡ (≈ˢ-to-path (fst q) (fst (F.map p)) heq'))
                                 heq })
                 (subst ⟨_⟩ (F.image-spec d q) hq) })

        bwd : ⟨ target ⟩
            → ⟨ ⋁ (Pt (Over.carrier 𝔔))
                  (λ q → (fst q ∈ˢ F.image d) ⊓ (fst r ≈ˢ fst (G.map q))) ⟩
        bwd = PT.map
          (λ { (p , hp , heq) →
               F.map p
             , subst ⟨_⟩ (sym (F.image-spec d (F.map p)))
                 ∣ p , hp , path-to-≈ˢ (fst (F.map p)) (fst (F.map p)) refl ∣₁
             , heq })

--------------------------------------------------------------------------------
-- Transport of a certificate along a dense map
--------------------------------------------------------------------------------

-- The same algebra certifies the source presentation, with the embedding
-- composed with the map. Everything except the density field is immediate;
-- the density field is the theorem, and it is where both the `dense` field
-- and the excluded middle are spent. The architecture does not record LEM on
-- this statement; it is needed, and this track's report says where.

module Transport (𝔓 𝔔 : Presentation) (m : Maps.DenseMap 𝔓 𝔔)
                 (c : Over.CertifiedCompletion 𝔔) where

  module P = Over 𝔓
  module Q = Over 𝔔
  module M = Maps.DenseMap {𝔓} {𝔔} m
  module C = Q.Theory c

  private
    imgOf : Pt C.B → S
    imgOf b = M.image (M.preimage (C.below b))

    subOf : (b : Pt C.B) → ⟨ imgOf b ⊆ˢ Q.carrier ⟩
    subOf b = M.image-sub (M.preimage (C.below b))
                (M.preimage-sub (C.below b) (C.below-sub b))

  transported-embedding : LEM ℓ → P.Embedding C.B C.lattice C.complete
  transported-embedding lem = record
    { i         = λ p → C.i (M.map p)
    ; i-mono    = λ {p} {q} h → C.i-mono (M.mono q p h)
    ; i-pos     = λ p → C.i-pos (M.map p)
    ; i-compat→ = λ p q h →
        C.i-compat→ (M.map p) (M.map q) (M.compat→ p q h)
    ; i-compat← = λ p q h →
        M.compat← p q (C.i-compat← (M.map p) (M.map q) h)
    ; below      = λ b → M.preimage (C.below b)
    ; below-sub  = λ b → M.preimage-sub (C.below b) (C.below-sub b)
    ; below-spec = λ b p →
        M.preimage-spec (C.below b) (C.below-sub b) p ∙ C.below-spec b (M.map p)
    ; iImage      = λ d → C.iImage (M.image d)
    ; iImage-sub  = λ d h → C.iImage-sub (M.image d) (M.image-sub d h)
    ; iImage-spec = ispec
    ; recover     = rec }
    where
      ispec : (d : S) (u : Pt C.B)
            → (fst u ∈ˢ C.iImage (M.image d))
            ≡ ⋁ (Pt P.carrier)
                (λ p → (fst p ∈ˢ d) ⊓ (fst u ≈ˢ fst (C.i (M.map p))))
      ispec d u = C.iImage-spec (M.image d) u ∙ ⇔toPath fwd bwd
        where
          target : Ω
          target = ⋁ (Pt P.carrier)
                     (λ p → (fst p ∈ˢ d) ⊓ (fst u ≈ˢ fst (C.i (M.map p))))

          fwd : ⟨ ⋁ (Pt Q.carrier)
                    (λ q → (fst q ∈ˢ M.image d) ⊓ (fst u ≈ˢ fst (C.i q))) ⟩
              → ⟨ target ⟩
          fwd = PT.rec (snd target)
            (λ { (q , hq , heq) → PT.map
                   (λ { (p , hp , heq') →
                        p , hp
                      , subst (λ z → ⟨ fst u ≈ˢ fst (C.i z) ⟩)
                          (Pt≡ (≈ˢ-to-path (fst q) (fst (M.map p)) heq')) heq })
                   (subst ⟨_⟩ (M.image-spec d q) hq) })

          bwd : ⟨ target ⟩
              → ⟨ ⋁ (Pt Q.carrier)
                    (λ q → (fst q ∈ˢ M.image d) ⊓ (fst u ≈ˢ fst (C.i q))) ⟩
          bwd = PT.map
            (λ { (p , hp , heq) →
                 M.map p
               , subst ⟨_⟩ (sym (M.image-spec d (M.map p)))
                   ∣ p , hp , path-to-≈ˢ (fst (M.map p)) (fst (M.map p)) refl ∣₁
               , heq })

      rec : (b : Pt C.B)
          → C.supᴮ (C.iImage (imgOf b))
                   (C.iImage-sub (imgOf b) (subOf b)) ≡ b
      rec b = ≤ᴮ-antisym down up
        where
          hB : ⟨ C.iImage (imgOf b) ⊆ˢ C.B ⟩
          hB = C.iImage-sub (imgOf b) (subOf b)

          sup : Pt C.B
          sup = C.supᴮ (C.iImage (imgOf b)) hB

          down : ⟨ sup ≤ᴮ b ⟩
          down = C.sup-lub (C.iImage (imgOf b)) hB b step
            where
              step : (u : Pt C.B) → ⟨ fst u ∈ˢ C.iImage (imgOf b) ⟩
                   → ⟨ u ≤ᴮ b ⟩
              step u hu = PT.rec (snd (u ≤ᴮ b)) pick
                (subst ⟨_⟩ (ispec (M.preimage (C.below b)) u) hu)
                where
                  pick : Σ[ p ∈ Pt P.carrier ]
                           (⟨ fst p ∈ˢ M.preimage (C.below b) ⟩
                            × ⟨ fst u ≈ˢ fst (C.i (M.map p)) ⟩)
                       → ⟨ u ≤ᴮ b ⟩
                  pick (p , hp , heq) =
                    subst (λ z → ⟨ z ⊆ˢ fst b ⟩)
                      (sym (≈ˢ-to-path (fst u) (fst (C.i (M.map p))) heq))
                      (subst ⟨_⟩ (C.below-spec b (M.map p))
                        (subst ⟨_⟩
                          (M.preimage-spec (C.below b) (C.below-sub b) p) hp))

          -- The image of a condition of the source, when it lies below b,
          -- belongs to the transported family, so the supremum dominates it.

          inSup : (p : Pt P.carrier) → ⟨ C.i (M.map p) ≤ᴮ b ⟩
                → ⟨ C.i (M.map p) ≤ᴮ sup ⟩
          inSup p hle = C.sup-ub (C.iImage (imgOf b)) hB (C.i (M.map p)) mem
            where
              inPre : ⟨ fst p ∈ˢ M.preimage (C.below b) ⟩
              inPre = subst ⟨_⟩
                (sym (M.preimage-spec (C.below b) (C.below-sub b) p))
                (subst ⟨_⟩ (sym (C.below-spec b (M.map p))) hle)

              inImg : ⟨ fst (M.map p) ∈ˢ imgOf b ⟩
              inImg = subst ⟨_⟩
                (sym (M.image-spec (M.preimage (C.below b)) (M.map p)))
                ∣ p , inPre , path-to-≈ˢ (fst (M.map p)) (fst (M.map p)) refl ∣₁

              mem : ⟨ fst (C.i (M.map p)) ∈ˢ C.iImage (imgOf b) ⟩
              mem = subst ⟨_⟩ (sym (C.iImage-spec (imgOf b) (C.i (M.map p))))
                ∣ M.map p , inImg
                , path-to-≈ˢ (fst (C.i (M.map p))) (fst (C.i (M.map p))) refl ∣₁

          -- The density argument. If some image below b escaped the
          -- supremum, a condition of the target would sit under that escape,
          -- the map's density would put a condition of the source under that,
          -- and its image would have to be both inside the supremum and
          -- disjoint from it, hence zero, which no image is.

          dominate : (q : Pt Q.carrier) → ⟨ C.i q ≤ᴮ b ⟩ → ⟨ C.i q ≤ᴮ sup ⟩
          dominate q hq with lem (C.i q ≤ᴮ sup)
          ... | inl h = h
          ... | inr n = PT.rec (snd (C.i q ≤ᴮ sup)) escape
            (C.dense-form lem ((C.i q) C.⊓ᴮ (C.¬ᴮ sup)) posd)
            where
              posd : ⟨ C.positiveᴮ ((C.i q) C.⊓ᴮ (C.¬ᴮ sup)) ⟩
              posd e = Empty.rec (n (C.⊥-as-≤ (C.i q) sup e))

              escape : Σ[ r ∈ Pt Q.carrier ]
                         ⟨ C.i r ≤ᴮ ((C.i q) C.⊓ᴮ (C.¬ᴮ sup)) ⟩
                     → ⟨ C.i q ≤ᴮ sup ⟩
              escape (r , hr) = PT.rec (snd (C.i q ≤ᴮ sup)) below-r (M.dense r)
                where
                  below-r : Σ[ p ∈ Pt P.carrier ] ⟨ M.map p Q.≼ r ⟩
                          → ⟨ C.i q ≤ᴮ sup ⟩
                  below-r (p , hp) = Empty.rec* (C.i-pos (M.map p) zeroed)
                    where
                      ir≤ : ⟨ C.i (M.map p) ≤ᴮ C.i r ⟩
                      ir≤ = C.i-mono hp

                      ≤b : ⟨ C.i (M.map p) ≤ᴮ b ⟩
                      ≤b = ⊆ˢ-trans ir≤
                        (⊆ˢ-trans (⊆ˢ-trans hr
                          (C.⊓-lb₁ (C.i q) (C.¬ᴮ sup))) hq)

                      ≤¬sup : ⟨ C.i (M.map p) ≤ᴮ (C.¬ᴮ sup) ⟩
                      ≤¬sup = ⊆ˢ-trans ir≤
                        (⊆ˢ-trans hr (C.⊓-lb₂ (C.i q) (C.¬ᴮ sup)))

                      zeroed : C.i (M.map p) ≡ C.⊥ᴮ
                      zeroed =
                          sym (C.≤→⊓ (C.i (M.map p)) sup (inSup p ≤b))
                        ∙ C.≤¬→⊓⊥ (C.i (M.map p)) sup ≤¬sup

          up : ⟨ b ≤ᴮ sup ⟩
          up = subst (λ z → ⟨ fst z ⊆ˢ fst sup ⟩) (C.recover b)
            (C.sup-lub (C.iImage (C.below b))
              (C.iImage-sub (C.below b) (C.below-sub b)) sup step)
            where
              step : (u : Pt C.B) → ⟨ fst u ∈ˢ C.iImage (C.below b) ⟩
                   → ⟨ u ≤ᴮ sup ⟩
              step u hu = PT.rec (snd (u ≤ᴮ sup)) pick
                (subst ⟨_⟩ (C.iImage-spec (C.below b) u) hu)
                where
                  pick : Σ[ q ∈ Pt Q.carrier ]
                           (⟨ fst q ∈ˢ C.below b ⟩ × ⟨ fst u ≈ˢ fst (C.i q) ⟩)
                       → ⟨ u ≤ᴮ sup ⟩
                  pick (q , hq , heq) =
                    subst (λ z → ⟨ z ⊆ˢ fst sup ⟩)
                      (sym (≈ˢ-to-path (fst u) (fst (C.i q)) heq))
                      (dominate q (subst ⟨_⟩ (C.below-spec b q) hq))

  transport-certificate : LEM ℓ → P.CertifiedCompletion
  transport-certificate lem = record
    { B          = C.B
    ; lattice    = C.lattice
    ; boolean    = C.boolean
    ; complete   = C.complete
    ; nontrivial = C.nontrivial
    ; embedding  = transported-embedding lem }

--------------------------------------------------------------------------------
-- Property transfer
--------------------------------------------------------------------------------

-- A property certificate is a different object from a completion
-- certificate, and this is the record that keeps them apart. It is
-- parameterized by the presentation and by the certificate, so that its
-- hypotheses field may mention either: "P is the Cohen poset as coded in M"
-- and "the second chain-condition variant holds of P" are both hypotheses of
-- this shape, and neither is expressible without the parameters.
--
-- Φ and Ψ are arbitrary. A package carrying one chain-condition variant is an
-- inhabitant of a type that names that variant twice, in Φ and in Ψ, and
-- there is no operation in this file that turns it into an inhabitant of the
-- type for another variant: nothing here quantifies over Φ or Ψ, and no
-- certificate field mentions a chain condition at all, so the three variants
-- cannot be manufactured from one another at this layer. That is the whole
-- design point of the split, and K2 ships zero nontrivial inhabitants.

module Property (𝔓 : Presentation) (c : Over.CertifiedCompletion 𝔓)
                (sep : Separation) (Φ Ψ : Presentation → Ω) where

  record PropertyTransfer : Type (ℓ-suc ℓ) where
    field
      hypotheses : Type ℓ
      transfer   : hypotheses → ⟨ Φ 𝔓 ⟩ → ⟨ Ψ (Nonzero.B⁺ 𝔓 c sep) ⟩
