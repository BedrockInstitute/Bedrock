{-# OPTIONS --cubical --safe --guardedness #-}

-- K4 Track K, file 1 of 4. The adapter: K2's certificate records and K4's
-- three algebra records are the same three records, and this file proves it
-- by exhibiting the translation in both directions.
--
-- WHY A FILE AND NOT A REMARK. Architecture section 1.1 fixes K4's parameter
-- surface as "K4 declares its own three algebra records, field for field from
-- Certificate.agda:159-172, :179-187, :194-209, and takes them as module
-- parameters, rather than applying CodedCompletion.Core". That decision buys
-- every K4 track a telescope with no K2 module application in it, and it
-- costs exactly one obligation: somebody has to check that the copy is
-- faithful. If a field had drifted, every K4 theorem would still typecheck
-- and none of them would apply to a K2 algebra. The check is mechanical and
-- it belongs here, in the instance track, where the two layers first meet.
--
-- WHAT FAITHFUL MEANS, and why the round trips are the real statement. Two
-- record translations that agree on field names prove nothing on their own:
-- a translation could quietly drop to a weaker law and still compile, because
-- Agda checks each field against the TARGET type and a weaker source law
-- would simply fail to typecheck, while a translation built by hand from
-- derived lemmas could reconstruct a field from something else and lose the
-- identity of the operations. The round trips below rule that out. They hold
-- by refl, which says the two records have the same fields at the same types
-- in the same order, and that the translation is the identity on every one of
-- them.
--
-- HYPOTHESES. The three that Certificate takes: the structure, ordinary
-- Extensionality and the path realization. This file spends none of them; it
-- carries them only because Certificate's module telescope demands them
-- before its records can be named. K4.Algebra's own records need only the
-- structure, which is the asymmetry the translation makes harmless.
--
-- NO L AND NO V HERE. This file is generic in the ground. Track K's second
-- and fourth files are the ones that name a hierarchy, and the reason the
-- naming is correct there and would be wrong in Tracks A to J is written at
-- the head of K4/InstanceL.agda.

open import Base.Prelude
open import Base.Truth
open import FOL.ZFStructure using ( ZFStructure )
import OrdinaryProfile
import Certificate
import K4.Algebra

module K4.InstanceAdapter
  {ℓ} (𝒮 : ZFStructure (hPropAlgebra ℓ))
  (ext : OrdinaryProfile.Extensionality 𝒮)
  (paths : (x y : ZFStructure.S 𝒮)
         → (ZFStructure._≈ˢ_ 𝒮 x y) ≡ ((x ≡ y) , ZFStructure.isSetS 𝒮 x y))
  where

open import FOL.ZFStructure using ( module hPropStructure )

open TruthAlgebra (hPropAlgebra ℓ)
open hPropStructure 𝒮

module Cert = Certificate 𝒮 ext paths

open import K4.Algebra 𝒮 using ( Lattice; Complement; CodedComplete )

-- ---------------------------------------------------------------------
-- The bounded lattice
-- ---------------------------------------------------------------------

-- Certificate.BoundedLattice and K4.Algebra.Lattice carry the same ten
-- fields over the same order. The order is the point: both files define
-- u ≤ᴮ v as fst u ⊆ˢ fst v with _⊆ˢ_ from FOL.ZFModel 𝒮, so the two order
-- relations are the same function and not merely provably equivalent ones,
-- and no coercion appears anywhere below.

lattice : (B : S) → Cert.BoundedLattice B → Lattice B
lattice B bl = record
  { ⊤ᴮ         = ⊤ᴮ
  ; ⊥ᴮ         = ⊥ᴮ
  ; _⊓ᴮ_       = _⊓ᴮ_
  ; _⊔ᴮ_       = _⊔ᴮ_
  ; ⊓-lb₁      = ⊓-lb₁
  ; ⊓-lb₂      = ⊓-lb₂
  ; ⊓-glb      = ⊓-glb
  ; ⊔-ub₁      = ⊔-ub₁
  ; ⊔-ub₂      = ⊔-ub₂
  ; ⊔-lub      = ⊔-lub
  ; ⊥-least    = ⊥-least
  ; ⊤-greatest = ⊤-greatest }
  where open Cert.BoundedLattice bl

toBoundedLattice : (B : S) → Lattice B → Cert.BoundedLattice B
toBoundedLattice B L = record
  { ⊤ᴮ         = ⊤ᴮ
  ; ⊥ᴮ         = ⊥ᴮ
  ; _⊓ᴮ_       = _⊓ᴮ_
  ; _⊔ᴮ_       = _⊔ᴮ_
  ; ⊓-lb₁      = ⊓-lb₁
  ; ⊓-lb₂      = ⊓-lb₂
  ; ⊓-glb      = ⊓-glb
  ; ⊔-ub₁      = ⊔-ub₁
  ; ⊔-ub₂      = ⊔-ub₂
  ; ⊔-lub      = ⊔-lub
  ; ⊥-least    = ⊥-least
  ; ⊤-greatest = ⊤-greatest }
  where open Lattice L

-- ---------------------------------------------------------------------
-- The complement
-- ---------------------------------------------------------------------

-- Certificate.IsBoolean is indexed by its bounded lattice and K4.Complement
-- by its lattice, so the translation of the complement has to be stated over
-- the translation of the lattice. That is what makes these two declarations
-- a check rather than a restatement: the three laws mention ⊓ᴮ, ⊔ᴮ, ⊥ᴮ and
-- ⊤ᴮ, and they typecheck at the target only because projecting the record
-- literal above returns the source's own operations.

complement : (B : S) (bl : Cert.BoundedLattice B)
           → Cert.IsBoolean B bl → Complement B (lattice B bl)
complement B bl bo = record
  { ¬ᴮ_      = ¬ᴮ_
  ; ¬-⊓      = ¬-⊓
  ; ¬-⊔      = ¬-⊔
  ; ⊓-⊔-dist = ⊓-⊔-dist }
  where open Cert.IsBoolean bo

toIsBoolean : (B : S) (L : Lattice B)
            → Complement B L → Cert.IsBoolean B (toBoundedLattice B L)
toIsBoolean B L C = record
  { ¬ᴮ_      = ¬ᴮ_
  ; ¬-⊓      = ¬-⊓
  ; ¬-⊔      = ¬-⊔
  ; ⊓-⊔-dist = ⊓-⊔-dist }
  where open Complement C

-- ---------------------------------------------------------------------
-- Completeness for the coded families
-- ---------------------------------------------------------------------

-- K4.CodedComplete carries a lattice index that none of its six fields
-- mentions, so the translation is available at EVERY lattice over the same
-- carrier and the index is free in both directions. That asymmetry is worth
-- stating rather than hiding: a consumer holding a certificate's completeness
-- record may use it at whatever lattice the rest of its telescope fixed, and
-- no compatibility obligation between the two is created by doing so.

codedComplete : (B : S) (L : Lattice B)
              → Cert.CompleteForCoded B → CodedComplete B L
codedComplete B L K = record
  { supᴮ    = supᴮ
  ; sup-ub  = sup-ub
  ; sup-lub = sup-lub
  ; infᴮ    = infᴮ
  ; inf-lb  = inf-lb
  ; inf-glb = inf-glb }
  where open Cert.CompleteForCoded K

toCompleteForCoded : (B : S) (L : Lattice B)
                   → CodedComplete B L → Cert.CompleteForCoded B
toCompleteForCoded B L K = record
  { supᴮ    = supᴮ
  ; sup-ub  = sup-ub
  ; sup-lub = sup-lub
  ; infᴮ    = infᴮ
  ; inf-lb  = inf-lb
  ; inf-glb = inf-glb }
  where open CodedComplete K

-- ---------------------------------------------------------------------
-- The round trips
-- ---------------------------------------------------------------------

-- Each of the six equations below holds by reflexivity. Read that as the
-- theorem it is: the two record declarations have the same fields, at the
-- same types, and the translation is the identity on each field, so nothing
-- is reconstructed, weakened or re-derived in passing between the layers.
-- A drifted field would break the translation itself; a translation that
-- compiled but rebuilt a field from a derived lemma would break these.

lattice-round : (B : S) (L : Lattice B) → lattice B (toBoundedLattice B L) ≡ L
lattice-round B L = refl

boundedLattice-round : (B : S) (bl : Cert.BoundedLattice B)
                     → toBoundedLattice B (lattice B bl) ≡ bl
boundedLattice-round B bl = refl

complement-round : (B : S) (L : Lattice B) (C : Complement B L)
                 → complement B (toBoundedLattice B L) (toIsBoolean B L C) ≡ C
complement-round B L C = refl

isBoolean-round : (B : S) (bl : Cert.BoundedLattice B) (bo : Cert.IsBoolean B bl)
                → toIsBoolean B (lattice B bl) (complement B bl bo) ≡ bo
isBoolean-round B bl bo = refl

codedComplete-round : (B : S) (L : Lattice B) (K : CodedComplete B L)
                    → codedComplete B L (toCompleteForCoded B L K) ≡ K
codedComplete-round B L K = refl

completeForCoded-round : (B : S) (L : Lattice B) (K : Cert.CompleteForCoded B)
                       → toCompleteForCoded B L (codedComplete B L K) ≡ K
completeForCoded-round B L K = refl

-- ---------------------------------------------------------------------
-- Nontriviality
-- ---------------------------------------------------------------------

-- The shared preamble's first banner records that Bell 1.23(ii) is FALSE at
-- an algebra whose top and bottom coincide, that K4 assumes nontriviality
-- nowhere, and that the K4 instance must therefore carry K2's nontriviality
-- explicitly. K2 states it as Certificate.Nontrivial over a BoundedLattice
-- (Certificate.agda:213-214, with the algebra's own bottom on the right and
-- never the host empty type). Stating the K4-side spelling here, and proving
-- the two are the same statement, keeps the hypothesis in one vocabulary.

Nontrivial : (B : S) → Lattice B → Type ℓ
Nontrivial B L = (Lattice.⊥ᴮ L ≡ Lattice.⊤ᴮ L) → ⟨ ⊥ ⟩

nontrivial-agree : (B : S) (L : Lattice B)
                 → Nontrivial B L ≡ Cert.Nontrivial B (toBoundedLattice B L)
nontrivial-agree B L = refl
