{-# OPTIONS --cubical --safe --guardedness #-}

-- K4 Track A, file 1 of 3: the algebra layer.
--
-- What this module is for. K4 states every Boolean fact about the coded
-- algebra against THREE RECORDS declared here, field for field from K2's
-- Certificate.agda:159-172 (BoundedLattice), :179-187 (IsBoolean) and
-- :194-208 (CompleteForCoded). K4 does NOT apply CodedCompletion.Core to get
-- them. Two reasons, both architectural:
--
--  1. Applying Core drags `pow : PowerSet` into the ledger of every K4 module
--     that mentions a value, and no K4 result needs a power set.
--  2. A projection out of a MODULE PARAMETER is a variable, and a variable
--     cannot unfold. That is the tightest seal available (preamble rule R2),
--     and it is what keeps the elaborator from walking into the regular-open
--     construction while checking an atomic value statement.
--
-- The order is NOT a field of any of the three records. It is the top-level
-- `_≤ᴮ_` below, internal inclusion of codes, so that the lattice laws, the
-- complement laws and the completeness laws are provably about one relation.
-- That is K2's own decision (Certificate.agda:119-123) and K4 keeps it.
--
-- Hypotheses. The structure and nothing else. No Extensionality, no path
-- realization, no Separation, no PowerSet, no LEM, no nontriviality. The two
-- ground hypotheses enter one file later, in K4/Implication.agda, and they
-- are spent there on antisymmetry alone.
--
-- Universe ledger. Pt a : Type ℓ, because it is a Σ over S of a membership
-- proposition. Ω = hProp ℓ : Type (ℓ-suc ℓ). All three records are Type ℓ:
-- every field is a function into Pt B, a member of ⟨ _ ⟩ : Type ℓ, or a path
-- in Pt B. Nothing here has a field that is a path in Ω, so nothing here is
-- barred from indexing a ⋁ or a ⋀. The records that ARE barred, Admits and
-- Interp, live in K4.1 and K4.5.

open import Base.Prelude
open import Base.Truth
open import FOL.ZFStructure using ( ZFStructure )

module K4.Algebra {ℓ} (𝒮 : ZFStructure (hPropAlgebra ℓ)) where

open import FOL.ZFStructure using ( module hPropStructure )
open import FOL.ZFModel 𝒮 using ( _⊆ˢ_ )
open import Cubical.Foundations.HLevels using ( isSetΣSndProp )
open import Cubical.Data.Sigma using ( Σ≡Prop )

open TruthAlgebra (hPropAlgebra ℓ)
open hPropStructure 𝒮

--------------------------------------------------------------------------------
-- Points of a coded set
--------------------------------------------------------------------------------

-- An element of a coded algebra is a code together with a proof that it is a
-- member of the carrier set. This is the K0 representation ledger's decision
-- and it is the same shape for the conditions of a presentation and for the
-- elements of the algebra. Certificate.agda:104-108.

Pt : S → Type ℓ
Pt a = Σ[ x ∈ S ] ⟨ x ∈ˢ a ⟩

isSetPt : (a : S) → isSet (Pt a)
isSetPt a = isSetΣSndProp isSetS (λ x → snd (x ∈ˢ a))

-- Membership is a proposition, so two points with the same code are equal.
-- Every value equation in K4 ends here or at ≤ᴮ-antisym.

Pt≡ : {a : S} {u v : Pt a} → fst u ≡ fst v → u ≡ v
Pt≡ {a} = Σ≡Prop (λ x → snd (x ∈ˢ a))

--------------------------------------------------------------------------------
-- The order on elements
--------------------------------------------------------------------------------

infix 20 _≤ᴮ_

_≤ᴮ_ : {a : S} → Pt a → Pt a → Ω
u ≤ᴮ v = fst u ⊆ˢ fst v

≤ᴮ-refl : {a : S} (u : Pt a) → ⟨ u ≤ᴮ u ⟩
≤ᴮ-refl u x h = h

-- Transitivity is stated on the CODES and not on the points, copying
-- Certificate.agda:132-139 and its measured reason: a point level version
-- leaves the implicit carrier and both endpoints undetermined at every call
-- site, since the order only ever mentions the first projections and Agda
-- cannot invert a projection. Eleven unsolved metas were measured there. Every
-- chain of inequalities in K4 composes through this one lemma.

⊆ˢ-trans : {x y z : S} → ⟨ x ⊆ˢ y ⟩ → ⟨ y ⊆ˢ z ⟩ → ⟨ x ⊆ˢ z ⟩
⊆ˢ-trans h k w m = k w (h w m)

--------------------------------------------------------------------------------
-- The bounded lattice
--------------------------------------------------------------------------------

-- Field for field from Certificate.agda:159-172. The operations are pinned by
-- their universal properties and not by an equational axiomatisation, so two
-- inhabitants over the same carrier have equal operations. That is what makes
-- a Lattice safe to carry as a parameter rather than as a specification.

record Lattice (B : S) : Type ℓ where
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

--------------------------------------------------------------------------------
-- The complement
--------------------------------------------------------------------------------

-- Field for field from Certificate.agda:179-187, renamed IsBoolean to
-- Complement. Distributivity is a field because a bounded lattice with
-- complements need not be distributive; the rest of the Boolean theory is a
-- theorem of K4/Implication.agda.
--
-- Named trap, measured. CodedCompletion.Core defines ¬ᴮ_ at :710 and proves
-- NO law about it, and `grep -c "dist" CodedCompletion.agda` returns 0. So
-- these four fields are not projections of any existing K2 structure; the
-- transport instance of Track K must prove them from roLaws through reads-inj,
-- which is exactly the plan CodedCompletion.agda:1185-1188 states in its own
-- words.

record Complement (B : S) (L : Lattice B) : Type ℓ where
  open Lattice L
  field
    ¬ᴮ_      : Pt B → Pt B
    ¬-⊓      : (u : Pt B) → (u ⊓ᴮ (¬ᴮ u)) ≡ ⊥ᴮ
    ¬-⊔      : (u : Pt B) → (u ⊔ᴮ (¬ᴮ u)) ≡ ⊤ᴮ
    ⊓-⊔-dist : (u v w : Pt B) → (u ⊓ᴮ (v ⊔ᴮ w)) ≡ ((u ⊓ᴮ v) ⊔ᴮ (u ⊓ᴮ w))

  infix 13 ¬ᴮ_

--------------------------------------------------------------------------------
-- Completeness, for the coded families and for those only
--------------------------------------------------------------------------------

-- Field for field from Certificate.agda:194-208. The family is a GROUND CODE
-- X together with a proof that it is a subset of the carrier. There is
-- deliberately no host-indexed supremum operator anywhere in K4, and no
-- predicate parameter naming an abstract class of admissible families: a
-- family reaches supᴮ only by being realized as a set, which is what K4.1's
-- ValueSets contract is for.
--
-- The Lattice parameter is not consumed by any field. It is present so that
-- consumers can write the telescope (B : S) (L : Lattice B) (Cm : Complement
-- B L) (Kc : CodedComplete B L) uniformly, as tracks C, F, I and J do.

record CodedComplete (B : S) (L : Lattice B) : Type ℓ where
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
