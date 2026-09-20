{-# OPTIONS --cubical --safe --guardedness #-}

-- K6 Track J, ruling D8: the one-point CODED presentation, unconditional half.
--
-- Obstruction O4, as the architecture states it and as this session
-- re-verified it by grep: "no inhabitant of the coded Presentation type exists
-- anywhere in the programme". `record Presentation : Type ℓ` is at
-- CodedCompletion.agda:201 with four fields at :202-208. The only
-- `Presentation` inhabitants in the compile root are K2Bridge.agda:65-66 and
-- Certificate.agda:992, and BOTH inhabit the HOST record at
-- Certificate.agda:366, which is a different record at a different level
-- (Type (ℓ-suc ℓ)) with five different fields.
--
-- This file supplies the first inhabitant of the CODED record. What that does
-- and does not buy is stated at the bottom of the file, and the "does not" is
-- the longer list.
--
-- THE LEDGER, and it is the parameter list: ordinary Extensionality, the path
-- realization, ordinary PAIRING, and one set constant p₀. No PowerSet, no
-- Separation, no Union, no Infinity, no Collection, no Foundation, no Choice,
-- no LEM at any level. That is strictly BELOW the floor architecture 6.4
-- measures for anything routed through the coded completion
-- (Extensionality + PowerSet + Separation + paths, CodedCompletion.agda:256-263),
-- because the Presentation record sits OUTSIDE module Core and consumes none
-- of Core's parameters.

open import Base.Prelude
open import Base.Truth
open import FOL.ZFStructure using ( ZFStructure )
import OrdinaryProfile

module K6.OnePoint
  {ℓ} (𝒮 : ZFStructure (hPropAlgebra ℓ))
  (ext   : OrdinaryProfile.Extensionality 𝒮)
  (paths : (x y : ZFStructure.S 𝒮)
         → (ZFStructure._≈ˢ_ 𝒮 x y) ≡ ((x ≡ y) , ZFStructure.isSetS 𝒮 x y))
  (pair  : OrdinaryProfile.Pairing 𝒮)
  (p₀    : ZFStructure.S 𝒮)
  where

open import FOL.ZFStructure using ( module hPropStructure )
open import Cubical.Data.Sigma using ( Σ≡Prop )
open import Cubical.Data.Sum using ( _⊎_ ) renaming ( inl to inl⊎ ; inr to inr⊎ )
open import Cubical.Data.Unit using ( tt* )
import Cubical.Data.Empty as Empty
import Cubical.Functions.Logic as Logic
import Cubical.HITs.PropositionalTruncation as PT
open PT using ( ∥_∥₁; ∣_∣₁ )

import GroundDescription
import CodedVocabulary
import CodedCompletion
import ForcingNotion as FN

open TruthAlgebra (hPropAlgebra ℓ)
open hPropStructure 𝒮

module OP = OrdinaryProfile 𝒮
module GD = GroundDescription 𝒮 ext paths
module CV = CodedVocabulary 𝒮
module CC = CodedCompletion 𝒮

open GD using ( the; the-spec )
open CV using ( isSglΔ; isPairΔ; isKPairΔ; refinesΔ )
open OP.PathRealization paths using ( ≈ˢ-to-path )

≈ˢ-refl : (x : S) → ⟨ x ≈ˢ x ⟩
≈ˢ-refl = OP.≈ˢ-refl ext

--------------------------------------------------------------------------------
-- 1. The singleton, sealed with its spec
--------------------------------------------------------------------------------

-- Pairing at a = b. The class is written out and not left to unification:
-- GroundDescription.agda:113-121 records the measured reason, an element of Ω
-- is a pair and the isProp half of the meta stays blocked otherwise.
--
-- Rule 2: the description term and its spec are sealed together. Everything
-- below reads the singleton only through sgl-spec, sgl-member and sgl-only.

sglClass : S → S → Ω
sglClass a x = (x ≈ˢ a) ⊔ (x ≈ˢ a)

opaque
  sgl : S → S
  sgl a = the (sglClass a) (pair a a)

  sgl-spec : (a x : S) → (x ∈ˢ sgl a) ≡ sglClass a x
  sgl-spec a = the-spec (sglClass a) (pair a a)

sgl-member : (a : S) → ⟨ a ∈ˢ sgl a ⟩
sgl-member a = subst ⟨_⟩ (sym (sgl-spec a a)) (Logic.inl (≈ˢ-refl a))

sgl-≈ : (a x : S) → ⟨ x ∈ˢ sgl a ⟩ → ⟨ x ≈ˢ a ⟩
sgl-≈ a x h = PT.rec (snd (x ≈ˢ a))
  (λ { (inl⊎ e) → e ; (inr⊎ e) → e }) (subst ⟨_⟩ (sgl-spec a x) h)

sgl-only : (a x : S) → ⟨ x ∈ˢ sgl a ⟩ → x ≡ a
sgl-only a x h = ≈ˢ-to-path x a (sgl-≈ a x h)

sgl-of-≈ : (a x : S) → ⟨ x ≈ˢ a ⟩ → ⟨ x ∈ˢ sgl a ⟩
sgl-of-≈ a x h = subst ⟨_⟩ (sym (sgl-spec a x)) (Logic.inl h)

--------------------------------------------------------------------------------
-- 2. The three codes
--------------------------------------------------------------------------------

-- The carrier is {p₀}. The Kuratowski pair ⟨p₀, p₀⟩ is {{p₀},{p₀,p₀}}, which
-- is {{p₀}}, so the order GRAPH is the singleton of that: three nested
-- singletons and nothing else. Two Pairing instances would already do it; the
-- third is spent because the graph is a set of pairs and not a pair.

carrierOP : S
carrierOP = sgl p₀

kpOP : S
kpOP = sgl (sgl p₀)

orderOP : S
orderOP = sgl kpOP

-- kpOP really is the Kuratowski pair of p₀ with itself. This is the one
-- non-formal step in the file, and it is three clauses of CodedVocabulary's
-- isKPairΔ (CodedVocabulary.agda:118-122) read at a singleton.

sglWitness : ⟨ isSglΔ (sgl p₀) p₀ ⟩
sglWitness = sgl-member p₀ , (λ x h → sgl-≈ p₀ x h)

pairWitness : ⟨ isPairΔ (sgl p₀) p₀ p₀ ⟩
pairWitness = sgl-member p₀ , sgl-member p₀
  , (λ x h → subst ⟨_⟩ (sgl-spec p₀ x) h)

kpWitness : ⟨ isKPairΔ kpOP p₀ p₀ ⟩
kpWitness =
    ∣ sgl p₀ , sgl-member (sgl p₀) , sglWitness ∣₁
  , ∣ sgl p₀ , sgl-member (sgl p₀) , pairWitness ∣₁
  , (λ w hw → Logic.inl
      (subst (λ u → ⟨ isSglΔ u p₀ ⟩) (sym (sgl-only (sgl p₀) w hw)) sglWitness))

-- And the graph really does hold that pair, at the two arguments the order
-- laws need. refinesΔ is CodedVocabulary.agda:144-145.

refines-p₀ : ⟨ refinesΔ orderOP p₀ p₀ ⟩
refines-p₀ = ∣ kpOP , sgl-member kpOP , kpWitness ∣₁

--------------------------------------------------------------------------------
-- 3. The presentation, and its forcing laws
--------------------------------------------------------------------------------

order-typed-OP :
  ⟨ ⋀ S (λ z → (z ∈ˢ orderOP) ⇒ ⋁ S (λ p → ⋁ S (λ q →
      (p ∈ˢ carrierOP) ⊓ ((q ∈ˢ carrierOP) ⊓ isKPairΔ z p q)))) ⟩
order-typed-OP z hz =
  ∣ p₀ , ∣ p₀ , sgl-member p₀ , sgl-member p₀
    , subst (λ u → ⟨ isKPairΔ u p₀ p₀ ⟩) (sym (sgl-only kpOP z hz)) kpWitness
    ∣₁ ∣₁

𝔓 : CC.Presentation
𝔓 = record
  { carrier     = carrierOP
  ; order       = orderOP
  ; order-typed = order-typed-OP
  ; inhabited   = ∣ p₀ , sgl-member p₀ ∣₁ }

module C = CC.Coded 𝔓

-- Reflexivity and transitivity collapse to the same one fact, because every
-- condition of this notion IS p₀.

refines-any : (r p : S) → ⟨ r ∈ˢ carrierOP ⟩ → ⟨ p ∈ˢ carrierOP ⟩
            → ⟨ refinesΔ orderOP r p ⟩
refines-any r p hr hp =
  subst (λ u → ⟨ refinesΔ orderOP u p ⟩) (sym (sgl-only p₀ r hr))
    (subst (λ u → ⟨ refinesΔ orderOP p₀ u ⟩) (sym (sgl-only p₀ p hp))
      refines-p₀)

laws : C.ForcingLaws
laws = record
  { ≼ᴵ-refl  = λ p hp → refines-any p p hp hp
  ; ≼ᴵ-trans = λ r q p hr hq hp _ _ → refines-any r p hr hp }

--------------------------------------------------------------------------------
-- 4. That it really is one point
--------------------------------------------------------------------------------

-- Without this the file would only have built A presentation, not THE
-- positive control: the whole value of the exit example is that at one
-- condition the extension IS the ground (K5/Structures.agda:527-531).

carrier-one-point : (x : S) → ⟨ x ∈ˢ carrierOP ⟩ → x ≡ p₀
carrier-one-point = sgl-only p₀

cond-p₀ : C.Cond
cond-p₀ = p₀ , sgl-member p₀

cond-isContr : isContr C.Cond
cond-isContr = cond-p₀ , (λ q → Σ≡Prop (λ x → snd (x ∈ˢ carrierOP))
  (sym (sgl-only p₀ (fst q) (snd q))))

one-point : (p q : C.Cond) → p ≡ q
one-point p q = sym (snd cond-isContr p) ∙ snd cond-isContr q

--------------------------------------------------------------------------------
-- 5. The decoded host notion, and the filter
--------------------------------------------------------------------------------

notionOP : FN.ForcingNotion {ℓ}
notionOP = C.decode laws

module FS = FN.Structure notionOP

-- Every K6 field of the ordinary profile that carries `isFilter G` or
-- ⟨ positive G ⟩ now has a witnessed hypothesis at a CODED notion. Before this
-- file the only witness in the compile root was Instances.agda:544, at the
-- HOST trivial notion whose Cond is Unit* and which no Presentation produces.

everythingOP : FS.Sub
everythingOP = λ _ → ⊤

all-refine : (p q : C.Cond) → ⟨ FS._≼_ p q ⟩
all-refine p q = subst (λ w → ⟨ FS._≼_ p w ⟩) (one-point p q) (FS.≼-refl p)

everything-filter : FS.isFilter everythingOP
everything-filter = record
  { inhabited = ∣ cond-p₀ , tt* ∣₁
  ; upward    = λ _ _ _ _ → tt*
  ; directed  = λ p q _ _ → ∣ p , tt* , FS.≼-refl p , all-refine p q ∣₁ }

everything-positive : ⟨ FS.positive everythingOP ⟩
everything-positive = FS.isFilter.inhabited everything-filter

--------------------------------------------------------------------------------
-- 6. What this notion is NOT, stated so nobody over-reads section 5
--------------------------------------------------------------------------------

-- It is not atomless, so it does not witness the hypothesis of K2's
-- no-host-generic (ForcingNotion.agda:315). K5's Track J built the binary tree
-- for that and this file does not replace it.

all-compatible : (p q : C.Cond) → ⟨ FS.compatible p q ⟩
all-compatible p q = ∣ p , FS.≼-refl p , all-refine p q ∣₁

not-atomless : FS.atomless → ⟨ ⊥ ⟩
not-atomless atl = PT.rec (snd ⊥) outer (atl cond-p₀)
  where
  inner : (q : C.Cond)
        → Σ[ r ∈ C.Cond ] (⟨ FS._≼_ q cond-p₀ ⟩
            × (⟨ FS._≼_ r cond-p₀ ⟩ × ⟨ FS.incompatible q r ⟩))
        → ⟨ ⊥ ⟩
  inner q (r , _ , _ , inc) = inc (all-compatible q r)
  outer : Σ[ q ∈ C.Cond ] ⟨ ⋁ C.Cond (λ r → (FS._≼_ q cond-p₀)
            ⊓ ((FS._≼_ r cond-p₀) ⊓ FS.incompatible q r)) ⟩
        → ⟨ ⊥ ⟩
  outer (q , h) = PT.rec (snd ⊥) (inner q) h

-- It is also not a notion at which any unbounded formula changes truth value,
-- since it has one condition; so it does NOT unblock the refutation of
-- Elementarity (K5/Structures.agda:503-505, NON-CLAIM 2) and it does NOT
-- unblock exit example E5. Those need a notion that ADDS a set, and O4's
-- remaining half, a nontrivial coded presentation, is still K8's.
--
-- And it supplies no AtomicGraph, so O1 is untouched: the four conditional
-- fields of OrdinaryZF at 𝒮ᴾ[ G ] are exactly as conditional as before.
--
-- ONE MORE THING IT IS NOT, because the coordinator's rule 15 message asks it
-- to be exactly this. It does NOT discriminate a `foundation` proof routed
-- through external accessibility of the extension's membership from the direct
-- one. At one condition the extension IS the ground, so every host structural
-- property of the ground, well-foundedness included, transfers; a control that
-- discriminates a hypothesis must be a notion at which that hypothesis is
-- FALSE, and this is the notion at which nothing changes. The discrimination
-- is not needed either way: K6/Refuted.agda section 2g proves the hypothesis
-- is a THEOREM of the spine at 𝒮ᴾ[ G ], whose carrier is Nm and not a
-- quotient.
