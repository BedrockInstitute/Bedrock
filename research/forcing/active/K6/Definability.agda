{-# OPTIONS --cubical --safe --guardedness #-}

-- K6 Track E1. Definability, the half that costs nothing.
--
-- ARCHITECTURE PART 3.2, THE SPLIT, AND IT IS THE POINT OF THIS FILE. Two
-- lenses disagreed about what forcing definability costs, and both were right
-- about a different half. The ground SET of conditions forcing a given Boolean
-- ELEMENT is FREE: it is the ForcingBase field below (K5/Frame.agda:199-201)
-- and its two entailments ⊩ᴮ-mem and ⊩ᴮ-from (:287-288, :290-291), each one
-- line. No Separation may be spent on it. The Boolean VALUE of a FORMULA is
-- val, and val is unconditionally O1. This file owns the free half ONLY and
-- names no obstruction; K6/ForcesTruth.agda owns val and names O1 in its type.
--
-- THE SECOND HALF OF THIS FILE, and ruling D5. K5's whole value and forcing
-- apparatus is defined on PARAMETER FREE formulas, Src k = Formula (⊥* {ℓ}) k
-- (K5/Clauses.agda:117-118, K5/Truth.agda:107-108). But OrdinaryProfile's
-- Separation takes φ : Formula S 1 and Collection takes φ : Formula S 2, and at
-- the extension structure S is the names, so a constant is an arbitrary NAME.
-- Without a constant elimination the two schemata cannot even be STATED in K5's
-- vocabulary. The bridge exists in the book and no K1 to K5 document names it:
-- absFo at FOL/Manipulation/ParameterAbstraction.lagda.md:103 with ⊨-abs at
-- :261-263 and ⊨-abs₁ at :295-297. Track E owns it so that Tracks F, G and H do
-- not each invent a different one.
--
-- ONE MEASURED DEPARTURE FROM THE ARCHITECTURE'S PRINTED SIGNATURE, and rule 14
-- governs. The architecture prints sat-abs with ⊨₀ on the right, which is
-- satisfaction at the EMPTY constant domain, At (⊥* {ℓ}) Empty.rec*. That form
-- does not compose with K5: ext-⊨ is stated at (ν ⊨ᴾ embed φ) ≡ (envᴮ ν ⊨ᴮ embed φ)
-- (K5/ExtensionSat.agda:219-220), with embed on BOTH sides and the name
-- alphabet on both sides. So the right hand side below is the embed form, which
-- is one application of embed-⊨ (FOL/Manipulation/Relabelling.lagda.md:100-102)
-- away from the architecture's and is the form Tracks E2, F, G and H can chain.
-- The ⊨₀ form is exported beside it as sat-abs₀ so that nothing is lost.

open import Base.Prelude
open import Base.Truth
open import FOL.ZFStructure using ( ZFStructure )
open import FOL.Syntax using ( Formula )
open import FOL.Manipulation.ConstantOccurrences using ( countFo ; constantsFo )
open import FOL.Manipulation.ConstantMapping using ( embed )
open import FOL.Manipulation.ParameterAbstraction using ( absFo ; ⊨-abs )
open import FOL.Manipulation.Relabelling using ( embed-⊨ )
open import Cubical.Data.Nat using ( _+_ )
open import Cubical.Data.Vec using ( _++_ ; map )
import Cubical.Data.Empty as Empty
import FOL.Semantics
import OrdinaryProfile
import K4.Algebra
import K5.Frame

module K6.Definability
  {ℓ} (𝒮 : ZFStructure (hPropAlgebra ℓ))
  (ext : OrdinaryProfile.Extensionality 𝒮)
  (paths : (x y : ZFStructure.S 𝒮)
         → (ZFStructure._≈ˢ_ 𝒮 x y) ≡ ((x ≡ y) , ZFStructure.isSetS 𝒮 x y))
  (carrier order : ZFStructure.S 𝒮)
  (B : ZFStructure.S 𝒮)
  (L : K4.Algebra.Lattice 𝒮 B)
  (Cm : K4.Algebra.Complement 𝒮 B L)
  (Kc : K4.Algebra.CodedComplete 𝒮 B L)
  (fb : K5.Frame.Poset.ForcingBase 𝒮 carrier order B L Cm)
  -- The extension structure, as a variable. Part 4.0's spine: nothing here
  -- applies K5.Structures, and at the instance this is 𝒮ᴾ[ G ]. Because
  -- OrdinaryProfile does `open At S id`, the satisfaction opened below IS the
  -- one appearing inside OrdinaryProfile.Separation 𝒮ᴱ, not a copy of it.
  (𝒮ᴱ : ZFStructure (hPropAlgebra ℓ))
  where

open import FOL.ZFStructure using ( module hPropStructure )
open import FOL.ZFModel 𝒮 using ( _⊆ˢ_ )

open TruthAlgebra (hPropAlgebra ℓ)
open hPropStructure 𝒮

open K4.Algebra 𝒮 using ( Pt )

--------------------------------------------------------------------------------
-- The forced set, free
--------------------------------------------------------------------------------

module FP = K5.Frame.Poset 𝒮 carrier order
module FF = FP.Forcing ext paths B L Cm Kc fb
module FB = K5.Frame.Poset.ForcingBase fb

-- The set of conditions forcing a Boolean element, as a GROUND SET. It is a
-- field and not a construction, so no description operator is formed and rule
-- 2 has no target here.

forcedSet : Pt B → S
forcedSet = FB.below

forcedSet-sub : (b : Pt B) → ⟨ forcedSet b ⊆ˢ carrier ⟩
forcedSet-sub = FB.below-sub

-- The two directions, in the architecture's argument order. K5 states both
-- with the condition first; the flip is written out here rather than left for
-- three tracks to discover.

forcedSet-in : (b : Pt B) (p : FP.Cond)
             → ⟨ FF._⊩ᴮ_ p b ⟩ → ⟨ fst p ∈ˢ forcedSet b ⟩
forcedSet-in b p h = FF.⊩ᴮ-mem p b h

forcedSet-out : (b : Pt B) (p : FP.Cond)
              → ⟨ fst p ∈ˢ forcedSet b ⟩ → ⟨ FF._⊩ᴮ_ p b ⟩
forcedSet-out b p h = FF.⊩ᴮ-from p b h

--------------------------------------------------------------------------------
-- The constant bridge
--------------------------------------------------------------------------------

Nm : Type ℓ
Nm = ZFStructure.S 𝒮ᴱ

private
  module SemE = FOL.Semantics (hPropAlgebra ℓ) 𝒮ᴱ

open SemE.At Nm id public using ( _⊨_ )
open SemE.At (⊥* {ℓ}) (λ b → id (Empty.rec* b)) public using ()
  renaming ( _⊨_ to _⊨₀_ )

Src : ℕ → Type ℓ
Src k = Formula (⊥* {ℓ}) k

-- The parameter free shadow of a formula, and the vector of names it drops.
-- One new variable per constant OCCURRENCE, placed in the block immediately
-- after the original free variables.

srcOf : ∀ {k} (φ : Formula Nm k) → Src (k + countFo φ)
srcOf φ = absFo φ

parsOf : ∀ {k} (φ : Formula Nm k) → Vec Nm (countFo φ)
parsOf φ = constantsFo φ

-- The interpretation of a name is the name, so the book's `map ι` is `map id`
-- here and the vector it produces is the vector itself. That is not
-- definitional: map recurses on the vector and a variable vector does not
-- reduce. One induction, and then parsOf can be the plain constant vector
-- rather than a mapped one.

private
  mapId : ∀ {k} (v : Vec Nm k) → map id v ≡ v
  mapId [] = refl
  mapId (x ∷ v) = cong (x ∷_) (mapId v)

-- ADEQUACY. Satisfaction is unchanged when the constants are moved out of the
-- formula and into the tail of the environment. This is the statement Tracks F,
-- G and H need in order to hand a Separation or Collection instance to the
-- forcing machinery at all.

sat-abs : ∀ {k} (φ : Formula Nm k) (ν : Vec Nm k)
        → (ν ⊨ φ) ≡ ((ν ++ parsOf φ) ⊨ embed (srcOf φ))
sat-abs φ ν =
  ⊨-abs (hPropAlgebra ℓ) 𝒮ᴱ {ℓz = ℓ} id φ ν
  ∙ sym (embed-⊨ (hPropAlgebra ℓ) 𝒮ᴱ id (absFo φ) (ν ++ map id (constantsFo φ)))
  ∙ cong (λ w → (ν ++ w) ⊨ embed (srcOf φ)) (mapId (constantsFo φ))

-- The same statement at the empty constant domain, which is the architecture's
-- printed form. It is kept so that a consumer working in ⊨₀ is not forced
-- through embed, and so that the two forms are visibly one theorem.

sat-abs₀ : ∀ {k} (φ : Formula Nm k) (ν : Vec Nm k)
         → (ν ⊨ φ) ≡ ((ν ++ parsOf φ) ⊨₀ srcOf φ)
sat-abs₀ φ ν =
  ⊨-abs (hPropAlgebra ℓ) 𝒮ᴱ {ℓz = ℓ} id φ ν
  ∙ cong (λ w → (ν ++ w) ⊨₀ srcOf φ) (mapId (constantsFo φ))

-- Arity one, written out because it is the shape Separation and Foundation
-- both present: one member, then the parameters.

sat-abs₁ : (φ : Formula Nm 1) (x : Nm)
         → ((x ∷ []) ⊨ φ) ≡ ((x ∷ parsOf φ) ⊨ embed (srcOf φ))
sat-abs₁ φ x = sat-abs φ (x ∷ [])

-- Arity two, which is what Collection presents.

sat-abs₂ : (φ : Formula Nm 2) (y x : Nm)
         → ((y ∷ x ∷ []) ⊨ φ) ≡ ((y ∷ x ∷ parsOf φ) ⊨ embed (srcOf φ))
sat-abs₂ φ y x = sat-abs φ (y ∷ x ∷ [])
