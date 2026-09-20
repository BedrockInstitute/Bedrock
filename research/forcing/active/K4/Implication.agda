{-# OPTIONS --cubical --safe --guardedness #-}

-- K4 Track A, file 2 of 3: antisymmetry, the finite Boolean theory, and the
-- Boolean implication.
--
-- What this module is for. NEW. The coded carrier has no implication anywhere
-- in the inherited layers. Measured, both searches re-run for this file:
--
--   grep -c "⇒ᴮ" CodedCompletion.agda   = 0
--   grep -c "⇒ᴮ" Certificate.agda       = 0
--
-- The only ⇒ᴮ in the tree is on the HOST regular-open carrier,
-- HostRegularOpen.agda:332, with its adjunction at :586-592, and that is a
-- different operator on a different carrier. The evaluator of K4.5 needs an
-- implication clause and Bell's proofs of 1.15 to 1.18 are written with one,
-- so K4 defines it here, once, as ¬ᴮ u ⊔ᴮ v, and proves the adjunction.
--
-- Why the adjunction and not the equation. Algebra.agda:71-88 says in its own
-- words that the two implication fields of BooleanLaws are the adjunction
-- (_ ⊓ b) ⊣ (b ⇒ _), because that is what an evaluator's implication clause
-- actually needs, and that the equation a ⇒ b ≡ ¬ a ⊔ b is then forced. Here
-- the equation is the DEFINITION and the adjunction is the theorem, which is
-- the same content read in the other direction, and it is the direction that
-- lets ⇒ᴮ-curry and ⇒ᴮ-uncurry carry every residuation step of K4.
--
-- Hypotheses, and this is the whole list: the structure, ordinary
-- Extensionality, the path realization of the structure equality, the carrier
-- code B, a Lattice on it and a Complement of that Lattice. The two ground
-- hypotheses are spent on ≤ᴮ-antisym and nowhere else, exactly as
-- Certificate.agda:141-147 spends them. No Separation, no PowerSet, no
-- Collection, no names, no LEM, no nontriviality.
--
-- Trap, named. `Algebra.agda:435 laws : LEM ℓ → BooleanLaws` would supply the
-- finite theory below for the hProp algebra, but it carries LEM and would put
-- excluded middle under the whole K4 package. `roLaws` is LEM-free
-- (HostRegularOpen.agda:18) but lives on the host carrier. So the finite
-- theory is proved here from the four Complement fields and nothing else, and
-- `grep -c "LEM"` over this file counts only this ledger comment.

open import Base.Prelude
open import Base.Truth
open import FOL.ZFStructure using ( ZFStructure )
import OrdinaryProfile
import GroundDescription
import K4.Algebra

module K4.Implication
  {ℓ} (𝒮 : ZFStructure (hPropAlgebra ℓ))
  (ext : OrdinaryProfile.Extensionality 𝒮)
  (paths : (x y : ZFStructure.S 𝒮)
         → (ZFStructure._≈ˢ_ 𝒮 x y) ≡ ((x ≡ y) , ZFStructure.isSetS 𝒮 x y))
  (B : ZFStructure.S 𝒮)
  (L : K4.Algebra.Lattice 𝒮 B)
  (Cm : K4.Algebra.Complement 𝒮 B L)
  where

open import FOL.ZFStructure using ( module hPropStructure )
open import FOL.ZFModel 𝒮 using ( _⊆ˢ_ )
open import Cubical.Functions.Logic using ( ⇔toPath )

open TruthAlgebra (hPropAlgebra ℓ)
open hPropStructure 𝒮

-- Scope contract, measured. K4.Algebra is opened WITHOUT `public` here, and
-- the record type names Lattice, Complement and CodedComplete are NOT
-- re-exported. Re-exporting a record type name makes its record module
-- reachable by two routes, and a consumer that opens both K4.Algebra and this
-- module then fails with
--
--   error: [AmbiguousModule] Ambiguous module name CodedComplete. It could
--   refer to any one of K4.Infinitary.CodedComplete (record module)
--   K4.Infinitary.CodedComplete (record module)
--
-- even though the two routes name the SAME record. Plain definitions are
-- de-duplicated by Agda and record modules are not. So every consumer opens
-- K4.Algebra itself for the three record types and the point vocabulary, and
-- opens this module for the theory.

open K4.Algebra 𝒮
  using ( Pt; isSetPt; Pt≡; _≤ᴮ_; ≤ᴮ-refl; ⊆ˢ-trans
        ; Lattice; Complement; CodedComplete )

open Lattice L public
open Complement Cm public

module GD = GroundDescription 𝒮 ext paths
open GD using ( ext-path )

--------------------------------------------------------------------------------
-- Antisymmetry
--------------------------------------------------------------------------------

-- Where the module's two ground hypotheses are spent, and the only place.
-- Internal Extensionality turns mutual inclusion into the structure equality,
-- the path realization turns that into a host path, and the membership proof
-- rides along by Pt≡. Certificate.agda:146-147.
--
-- This is also the answer to preamble rule R1 for the whole package: every
-- value equation of K4 is proved by ≤ᴮ-antisym, never by a congruence over
-- ⊓ᴮ, ⊔ᴮ, ¬ᴮ or supᴮ with a bare reflexivity in one argument.

≤ᴮ-antisym : {a : S} {u v : Pt a} → ⟨ u ≤ᴮ v ⟩ → ⟨ v ≤ᴮ u ⟩ → u ≡ v
≤ᴮ-antisym h k = Pt≡ (ext-path (λ x → ⇔toPath (h x) (k x)))

--------------------------------------------------------------------------------
-- What the lattice laws force
--------------------------------------------------------------------------------

-- These are the order-theoretic consequences of the ten Lattice fields, in the
-- shapes the Boolean theory below consumes. They follow Certificate.agda's
-- LatticeTheory (:219-280); ⊔-comm and ⊔-⊤ are added here because the
-- complement theory needs them and K2's module did not.

⊓-idem : (u : Pt B) → (u ⊓ᴮ u) ≡ u
⊓-idem u = ≤ᴮ-antisym (⊓-lb₁ u u) (⊓-glb u u u (≤ᴮ-refl u) (≤ᴮ-refl u))

⊓-comm : (u v : Pt B) → (u ⊓ᴮ v) ≡ (v ⊓ᴮ u)
⊓-comm u v =
  ≤ᴮ-antisym (⊓-glb v u (u ⊓ᴮ v) (⊓-lb₂ u v) (⊓-lb₁ u v))
             (⊓-glb u v (v ⊓ᴮ u) (⊓-lb₂ v u) (⊓-lb₁ v u))

⊔-comm : (u v : Pt B) → (u ⊔ᴮ v) ≡ (v ⊔ᴮ u)
⊔-comm u v =
  ≤ᴮ-antisym (⊔-lub u v (v ⊔ᴮ u) (⊔-ub₂ v u) (⊔-ub₁ v u))
             (⊔-lub v u (u ⊔ᴮ v) (⊔-ub₂ u v) (⊔-ub₁ u v))

⊓-⊤ : (u : Pt B) → (u ⊓ᴮ ⊤ᴮ) ≡ u
⊓-⊤ u = ≤ᴮ-antisym (⊓-lb₁ u ⊤ᴮ) (⊓-glb u ⊤ᴮ u (≤ᴮ-refl u) (⊤-greatest u))

⊓-⊥ : (u : Pt B) → (u ⊓ᴮ ⊥ᴮ) ≡ ⊥ᴮ
⊓-⊥ u = ≤ᴮ-antisym (⊓-lb₂ u ⊥ᴮ) (⊥-least (u ⊓ᴮ ⊥ᴮ))

⊔-⊥ : (u : Pt B) → (u ⊔ᴮ ⊥ᴮ) ≡ u
⊔-⊥ u = ≤ᴮ-antisym (⊔-lub u ⊥ᴮ u (≤ᴮ-refl u) (⊥-least u)) (⊔-ub₁ u ⊥ᴮ)

⊔-⊥ˡ : (u : Pt B) → (⊥ᴮ ⊔ᴮ u) ≡ u
⊔-⊥ˡ u = ≤ᴮ-antisym (⊔-lub ⊥ᴮ u u (⊥-least u) (≤ᴮ-refl u)) (⊔-ub₂ ⊥ᴮ u)

⊔-⊤ : (u : Pt B) → (u ⊔ᴮ ⊤ᴮ) ≡ ⊤ᴮ
⊔-⊤ u = ≤ᴮ-antisym (⊔-lub u ⊤ᴮ ⊤ᴮ (⊤-greatest u) (≤ᴮ-refl ⊤ᴮ)) (⊔-ub₂ u ⊤ᴮ)

-- Refinement and meet say the same thing, in both directions.

≤→⊓ : (u v : Pt B) → ⟨ u ≤ᴮ v ⟩ → (u ⊓ᴮ v) ≡ u
≤→⊓ u v h = ≤ᴮ-antisym (⊓-lb₁ u v) (⊓-glb u v u (≤ᴮ-refl u) h)

⊓→≤ : (u v : Pt B) → (u ⊓ᴮ v) ≡ u → ⟨ u ≤ᴮ v ⟩
⊓→≤ u v p = subst (λ z → ⟨ z ≤ᴮ v ⟩) p (⊓-lb₂ u v)

≤⊥→≡⊥ : (u : Pt B) → ⟨ u ≤ᴮ ⊥ᴮ ⟩ → u ≡ ⊥ᴮ
≤⊥→≡⊥ u h = ≤ᴮ-antisym h (⊥-least u)

-- Monotonicity of the two finite operations. These are the workhorses of every
-- later track: an inequality between two compound values is assembled from the
-- inequalities of its parts and never from a distributive law.

⊓ᴮ-mono : (u u' v v' : Pt B) → ⟨ u ≤ᴮ u' ⟩ → ⟨ v ≤ᴮ v' ⟩
        → ⟨ (u ⊓ᴮ v) ≤ᴮ (u' ⊓ᴮ v') ⟩
⊓ᴮ-mono u u' v v' h k =
  ⊓-glb u' v' (u ⊓ᴮ v) (⊆ˢ-trans (⊓-lb₁ u v) h) (⊆ˢ-trans (⊓-lb₂ u v) k)

⊔ᴮ-mono : (u u' v v' : Pt B) → ⟨ u ≤ᴮ u' ⟩ → ⟨ v ≤ᴮ v' ⟩
        → ⟨ (u ⊔ᴮ v) ≤ᴮ (u' ⊔ᴮ v') ⟩
⊔ᴮ-mono u u' v v' h k =
  ⊔-lub u v (u' ⊔ᴮ v') (⊆ˢ-trans h (⊔-ub₁ u' v')) (⊆ˢ-trans k (⊔-ub₂ u' v'))

--------------------------------------------------------------------------------
-- What the complement laws force
--------------------------------------------------------------------------------

-- The bridge between refinement and disjointness, in all four directions.
-- Certificate.agda:290-329. Neither direction of the first pair needs
-- involutivity, which is why involutivity can be proved from them below rather
-- than assumed.

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

-- An element below both a value and its complement is bottom. This one line
-- replaces every appeal to a distributive law in the De Morgan proofs below:
-- the distribution is used once, to split a meet into two summands, and each
-- summand is killed by this lemma.

≤-both-⊥ : (w v : Pt B) → ⟨ w ≤ᴮ v ⟩ → ⟨ w ≤ᴮ (¬ᴮ v) ⟩ → w ≡ ⊥ᴮ
≤-both-⊥ w v h k = sym (≤→⊓ w v h) ∙ ≤¬→⊓⊥ w v k

-- Complements are unique, which is what pins ¬ᴮ. Certificate.agda:338-347.

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

-- Involution. The proof is uniqueness of complements read at ¬ᴮ u: both u and
-- ¬ᴮ (¬ᴮ u) complement it, so they are equal.

¬ᴮ-invol : (u : Pt B) → (¬ᴮ (¬ᴮ u)) ≡ u
¬ᴮ-invol u = sym (complement-unique (¬ᴮ u) u (¬ᴮ (¬ᴮ u))
  (⊓-comm (¬ᴮ u) u ∙ ¬-⊓ u)
  (⊔-comm (¬ᴮ u) u ∙ ¬-⊔ u)
  (¬-⊓ (¬ᴮ u))
  (¬-⊔ (¬ᴮ u)))

-- The complement reverses the order. Every antitonicity in K4, including the
-- left antitonicity of the implication, factors through this.

¬ᴮ-anti : (u v : Pt B) → ⟨ u ≤ᴮ v ⟩ → ⟨ (¬ᴮ v) ≤ᴮ (¬ᴮ u) ⟩
¬ᴮ-anti u v h = ⊓⊥→≤¬ (¬ᴮ v) u
  (≤-both-⊥ ((¬ᴮ v) ⊓ᴮ u) v
    (⊆ˢ-trans (⊓-lb₂ (¬ᴮ v) u) h)
    (⊓-lb₁ (¬ᴮ v) u))

--------------------------------------------------------------------------------
-- De Morgan
--------------------------------------------------------------------------------

-- The join law first. Refinement of the meet of the two complements is pure
-- order theory through ¬ᴮ-anti; the converse is the single place where the
-- distributive field is spent.

De-Morgan-⊔ : (u v : Pt B) → (¬ᴮ (u ⊔ᴮ v)) ≡ ((¬ᴮ u) ⊓ᴮ (¬ᴮ v))
De-Morgan-⊔ u v = ≤ᴮ-antisym le ge
  where
    w : Pt B
    w = (¬ᴮ u) ⊓ᴮ (¬ᴮ v)
    le : ⟨ (¬ᴮ (u ⊔ᴮ v)) ≤ᴮ w ⟩
    le = ⊓-glb (¬ᴮ u) (¬ᴮ v) (¬ᴮ (u ⊔ᴮ v))
           (¬ᴮ-anti u (u ⊔ᴮ v) (⊔-ub₁ u v))
           (¬ᴮ-anti v (u ⊔ᴮ v) (⊔-ub₂ u v))
    e₁ : (w ⊓ᴮ u) ≡ ⊥ᴮ
    e₁ = ≤-both-⊥ (w ⊓ᴮ u) u (⊓-lb₂ w u)
           (⊆ˢ-trans (⊓-lb₁ w u) (⊓-lb₁ (¬ᴮ u) (¬ᴮ v)))
    e₂ : (w ⊓ᴮ v) ≡ ⊥ᴮ
    e₂ = ≤-both-⊥ (w ⊓ᴮ v) v (⊓-lb₂ w v)
           (⊆ˢ-trans (⊓-lb₁ w v) (⊓-lb₂ (¬ᴮ u) (¬ᴮ v)))
    e : (w ⊓ᴮ (u ⊔ᴮ v)) ≡ ⊥ᴮ
    e = ⊓-⊔-dist w u v
      ∙ cong (_⊔ᴮ (w ⊓ᴮ v)) e₁
      ∙ cong (⊥ᴮ ⊔ᴮ_) e₂
      ∙ ⊔-⊥ ⊥ᴮ
    ge : ⟨ w ≤ᴮ (¬ᴮ (u ⊔ᴮ v)) ⟩
    ge = ⊓⊥→≤¬ w (u ⊔ᴮ v) e

-- The double negation of a join of complements. This is De-Morgan-⊔ read at
-- the complements and then folded by involution, and it is what makes the meet
-- law a corollary rather than a second distributivity argument.

dn-meet : (u v : Pt B) → (¬ᴮ ((¬ᴮ u) ⊔ᴮ (¬ᴮ v))) ≡ (u ⊓ᴮ v)
dn-meet u v =
    De-Morgan-⊔ (¬ᴮ u) (¬ᴮ v)
  ∙ cong (_⊓ᴮ (¬ᴮ (¬ᴮ v))) (¬ᴮ-invol u)
  ∙ cong (u ⊓ᴮ_) (¬ᴮ-invol v)

De-Morgan-⊓ : (u v : Pt B) → (¬ᴮ (u ⊓ᴮ v)) ≡ ((¬ᴮ u) ⊔ᴮ (¬ᴮ v))
De-Morgan-⊓ u v =
  complement-unique (u ⊓ᴮ v) (¬ᴮ (u ⊓ᴮ v)) y
    (¬-⊓ (u ⊓ᴮ v)) (¬-⊔ (u ⊓ᴮ v)) e⊓ e⊔
  where
    y : Pt B
    y = (¬ᴮ u) ⊔ᴮ (¬ᴮ v)
    e⊓ : ((u ⊓ᴮ v) ⊓ᴮ y) ≡ ⊥ᴮ
    e⊓ = subst (λ z → (z ⊓ᴮ y) ≡ ⊥ᴮ) (dn-meet u v) (⊓-comm (¬ᴮ y) y ∙ ¬-⊓ y)
    e⊔ : ((u ⊓ᴮ v) ⊔ᴮ y) ≡ ⊤ᴮ
    e⊔ = subst (λ z → (z ⊔ᴮ y) ≡ ⊤ᴮ) (dn-meet u v) (⊔-comm (¬ᴮ y) y ∙ ¬-⊔ y)

--------------------------------------------------------------------------------
-- The Boolean implication
--------------------------------------------------------------------------------

infixr 10 _⇒ᴮ_

_⇒ᴮ_ : Pt B → Pt B → Pt B
u ⇒ᴮ v = (¬ᴮ u) ⊔ᴮ v

-- The adjunction, both directions. Everything else in K4 that looks like an
-- implication step is one of these two lines.
--
-- Curry decomposes x as (x ⊓ᴮ a) ⊔ᴮ (x ⊓ᴮ ¬ᴮ a), which is the one use of the
-- distributive field here; the first summand is below b by hypothesis and the
-- second is below ¬ᴮ a, so the join is below ¬ᴮ a ⊔ᴮ b.

⇒ᴮ-curry : (x a b : Pt B) → ⟨ (x ⊓ᴮ a) ≤ᴮ b ⟩ → ⟨ x ≤ᴮ (a ⇒ᴮ b) ⟩
⇒ᴮ-curry x a b h = subst (λ z → ⟨ z ≤ᴮ (a ⇒ᴮ b) ⟩) (sym decomp) bound
  where
    decomp : x ≡ ((x ⊓ᴮ a) ⊔ᴮ (x ⊓ᴮ (¬ᴮ a)))
    decomp = sym (⊓-⊤ x) ∙ cong (x ⊓ᴮ_) (sym (¬-⊔ a)) ∙ ⊓-⊔-dist x a (¬ᴮ a)
    bound : ⟨ ((x ⊓ᴮ a) ⊔ᴮ (x ⊓ᴮ (¬ᴮ a))) ≤ᴮ (a ⇒ᴮ b) ⟩
    bound = ⊔-lub (x ⊓ᴮ a) (x ⊓ᴮ (¬ᴮ a)) (a ⇒ᴮ b)
              (⊆ˢ-trans h (⊔-ub₂ (¬ᴮ a) b))
              (⊆ˢ-trans (⊓-lb₂ x (¬ᴮ a)) (⊔-ub₁ (¬ᴮ a) b))

-- Uncurry meets both sides with a and then reduces a ⊓ᴮ (¬ᴮ a ⊔ᴮ b) to
-- a ⊓ᴮ b, the complement summand vanishing.

⇒ᴮ-uncurry : (x a b : Pt B) → ⟨ x ≤ᴮ (a ⇒ᴮ b) ⟩ → ⟨ (x ⊓ᴮ a) ≤ᴮ b ⟩
⇒ᴮ-uncurry x a b h =
  ⊆ˢ-trans (subst (λ z → ⟨ (x ⊓ᴮ a) ≤ᴮ z ⟩) reduce inner) (⊓-lb₂ a b)
  where
    inner : ⟨ (x ⊓ᴮ a) ≤ᴮ (a ⊓ᴮ (a ⇒ᴮ b)) ⟩
    inner = ⊓-glb a (a ⇒ᴮ b) (x ⊓ᴮ a) (⊓-lb₂ x a) (⊆ˢ-trans (⊓-lb₁ x a) h)
    reduce : (a ⊓ᴮ (a ⇒ᴮ b)) ≡ (a ⊓ᴮ b)
    reduce = ⊓-⊔-dist a (¬ᴮ a) b
           ∙ cong (_⊔ᴮ (a ⊓ᴮ b)) (¬-⊓ a)
           ∙ ⊔-⊥ˡ (a ⊓ᴮ b)

⇒ᴮ-mp : (u v : Pt B) → ⟨ ((u ⇒ᴮ v) ⊓ᴮ u) ≤ᴮ v ⟩
⇒ᴮ-mp u v = ⇒ᴮ-uncurry (u ⇒ᴮ v) u v (≤ᴮ-refl (u ⇒ᴮ v))

⇒ᴮ-antitoneˡ : (u u' v : Pt B) → ⟨ u' ≤ᴮ u ⟩ → ⟨ (u ⇒ᴮ v) ≤ᴮ (u' ⇒ᴮ v) ⟩
⇒ᴮ-antitoneˡ u u' v h = ⇒ᴮ-curry (u ⇒ᴮ v) u' v
  (⊆ˢ-trans
    (⊓-glb (u ⇒ᴮ v) u ((u ⇒ᴮ v) ⊓ᴮ u')
      (⊓-lb₁ (u ⇒ᴮ v) u') (⊆ˢ-trans (⊓-lb₂ (u ⇒ᴮ v) u') h))
    (⇒ᴮ-mp u v))

⇒ᴮ-monotoneʳ : (u v v' : Pt B) → ⟨ v ≤ᴮ v' ⟩ → ⟨ (u ⇒ᴮ v) ≤ᴮ (u ⇒ᴮ v') ⟩
⇒ᴮ-monotoneʳ u v v' h = ⇒ᴮ-curry (u ⇒ᴮ v) u v' (⊆ˢ-trans (⇒ᴮ-mp u v) h)

⇒ᴮ-⊤ : (u : Pt B) → (u ⇒ᴮ ⊤ᴮ) ≡ ⊤ᴮ
⇒ᴮ-⊤ u = ≤ᴮ-antisym (⊤-greatest (u ⇒ᴮ ⊤ᴮ))
                    (⇒ᴮ-curry ⊤ᴮ u ⊤ᴮ (⊤-greatest (⊤ᴮ ⊓ᴮ u)))

-- Two further shapes the atomic layer will spend often enough to name here.
-- ⇒ᴮ-⊤ˡ says a hypothesis that always holds can be dropped, and ⇒ᴮ-mono is the
-- two-sided monotonicity assembled from the two one-sided laws.

⇒ᴮ-⊤ˡ : (v : Pt B) → (⊤ᴮ ⇒ᴮ v) ≡ v
⇒ᴮ-⊤ˡ v = ≤ᴮ-antisym
  (subst (λ z → ⟨ z ≤ᴮ v ⟩) (⊓-⊤ (⊤ᴮ ⇒ᴮ v)) (⇒ᴮ-mp ⊤ᴮ v))
  (⇒ᴮ-curry v ⊤ᴮ v (⊓-lb₁ v ⊤ᴮ))

⇒ᴮ-mono : (u u' v v' : Pt B) → ⟨ u' ≤ᴮ u ⟩ → ⟨ v ≤ᴮ v' ⟩
        → ⟨ (u ⇒ᴮ v) ≤ᴮ (u' ⇒ᴮ v') ⟩
⇒ᴮ-mono u u' v v' h k =
  ⊆ˢ-trans (⇒ᴮ-antitoneˡ u u' v h) (⇒ᴮ-monotoneʳ u' v v' k)
