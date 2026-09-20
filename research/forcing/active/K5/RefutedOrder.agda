{-# OPTIONS --cubical --safe --guardedness #-}

-- K5 Track J, file 3: order reflection, and the identification of the forward
-- translation of the poset generic name with the Boolean one.
--
-- Both statements are about the same map, the completion embedding, and both
-- say that it does something it does not do: reflect the order, and be onto.
--
-- ITEM 3, ORDER REFLECTION. K5 states ⊩ᴮ-mono, that a refinement forces
-- whatever its coarsening forces. The converse, that forcing the image of p is
-- refining p, is what a reader writes next, because it is TRUE for the bare
-- cone: q ∈ ↓ᶜ p is literally q ≼ p. The completion map is not the bare cone
-- but the double pseudocomplement of it, and on a non-refined presentation the
-- two differ. K2's two condition non-refined instance is the witness, and K2
-- already refutes the statement for an arbitrary reflexive relation on the
-- algebra (InstancesCompletion.agda:131-134). What this file adds is the
-- statement in K5's own vocabulary, the ⊩ spelling, and the converse of
-- ⊩ᴮ-mono, which is the form a clause layer reaches for.
--
-- The boundary is exact and is recorded below: with LEM and separativity the
-- reflection IS available (separative→reflect), and the refuting instance is
-- antisymmetric and NOT separative, so the failure is a failure of Bell's
-- refinement condition and not a preorder artefact.
--
-- ITEM 4, trᴮ Γᴾ ≡ U̇. Γᴾ carries one entry per CONDITION, with the condition
-- as its own weight; U̇ carries one entry per ELEMENT OF THE ALGEBRA, with the
-- element as its own weight (StandardNames.agda:616-644). The forward
-- translation sends the weight p of an entry to the image of p
-- (TranslateForward.agda:441-442). So an entry of trᴮ Γᴾ has a weight in the
-- IMAGE of the embedding, while U̇ has an entry whose weight is the bottom of
-- the algebra, and the bottom is never an image: every image contains its own
-- condition and is therefore positive. That is the whole refutation, and it is
-- unconditional and constructive.
--
-- The coded statement cannot be computed with at all, because no inhabitant of
-- the coded telescope exists anywhere in the programme (architecture part 6.4,
-- O4). So the statement is transcribed host-side, with the two weight facts as
-- explicit module parameters, and the parameters are shown satisfiable so that
-- the refutation is not vacuous.
--
-- WHAT IS NOT REFUTED, and this must not be overread: the two names may still
-- have the same VALUE at a filter, since an entry of weight ⊥ᴮ is never
-- active. Only the identity of the two CODES is refuted, which is exactly the
-- non-claim K3 records at StandardNames.agda:610-615.
--
-- Every theorem in this file is constructive except the two citations of K2's
-- classical lemmas, which carry their LEM explicitly.

open import Base.Prelude
open import Base.Truth

module K5.RefutedOrder {ℓ : Level} where

open import Base.Classical using ( LEM )
import Cubical.Data.Empty as Empty
import Cubical.HITs.PropositionalTruncation as PT
open PT using ( ∥_∥₁; ∣_∣₁ )

import InstancesCompletion

open TruthAlgebra (hPropAlgebra ℓ)

--------------------------------------------------------------------------------
-- 0. K2's non-refined instance and its real regular-open algebra
--------------------------------------------------------------------------------

-- Taken from K2's own acceptance file rather than rebuilt, so that the
-- statements below are about the algebra K2 shipped. No module application
-- happens in this file.

module IC = InstancesCompletion {ℓ}
module NR = IC.NR
module RO = IC.RO

open RO using ( Reg; _⊑_; ⊑-refl; isProp⊑; ⊥ᴮ; ⊤ᴮ; _≤ᴮ_; ≤ᴮ-from; ≤ᴮ-to )

_⊩ᴿ_ : NR.Two → Reg → Ω
p ⊩ᴿ U = (fst (RO.i p) ⊑ fst U) , isProp⊑ (fst (RO.i p)) (fst U)

⊩ᴿ-to-≤ : (p : NR.Two) (U : Reg) → ⟨ p ⊩ᴿ U ⟩ → RO.i p ≤ᴮ U
⊩ᴿ-to-≤ p U h = ≤ᴮ-from (RO.i p) U h

⊩ᴿ-from-≤ : (p : NR.Two) (U : Reg) → RO.i p ≤ᴮ U → ⟨ p ⊩ᴿ U ⟩
⊩ᴿ-from-≤ p U e = ≤ᴮ-to (RO.i p) U e

--------------------------------------------------------------------------------
-- 1. The collapse, and the one condition forcing the image of the other
--------------------------------------------------------------------------------

-- one and low are separatively equal, so every completion identifies them,
-- while low is STRICTLY below one.

collapse : RO.i NR.one ≡ RO.i NR.low
collapse = IC.i-collapses

one-forces-low : ⟨ NR.one ⊩ᴿ RO.i NR.low ⟩
one-forces-low =
  subst (λ U → fst (RO.i NR.one) ⊑ fst U) collapse (⊑-refl (fst (RO.i NR.one)))

--------------------------------------------------------------------------------
-- 2. ORDER REFLECTION, REFUTED
--------------------------------------------------------------------------------

-- The statement in K5's vocabulary: forcing the image of p is refining p.

OrderReflection : Type ℓ
OrderReflection = (p q : NR.Two) → ⟨ q ⊩ᴿ RO.i p ⟩ → ⟨ NR._≼_ q p ⟩

order-reflection-fails : OrderReflection → ⟨ ⊥ ⟩
order-reflection-fails ref = NR.not-above (ref NR.low NR.one one-forces-low)

-- The same in the Boolean order, which is the spelling of the architecture's
-- trap T-A1.

OrderReflection≤ : Type (ℓ-suc ℓ)
OrderReflection≤ = (p q : NR.Two) → RO.i q ≤ᴮ RO.i p → ⟨ NR._≼_ q p ⟩

order-reflection≤-fails : OrderReflection≤ → ⟨ ⊥ ⟩
order-reflection≤-fails ref = order-reflection-fails step
  where
  step : OrderReflection
  step p q h = ref p q (⊩ᴿ-to-≤ q (RO.i p) h)

-- The converse of ⊩ᴮ-mono, which is the form a clause layer reaches for when
-- it wants to compare conditions by what they force. It fails for the same
-- reason and at the same pair.

MonoConverse : Type (ℓ-suc ℓ)
MonoConverse = (p q : NR.Two)
             → ((U : Reg) → ⟨ p ⊩ᴿ U ⟩ → ⟨ q ⊩ᴿ U ⟩) → ⟨ NR._≼_ q p ⟩

mono-converse-fails : MonoConverse → ⟨ ⊥ ⟩
mono-converse-fails mc = NR.not-above (mc NR.low NR.one step)
  where
  step : (U : Reg) → ⟨ NR.low ⊩ᴿ U ⟩ → ⟨ NR.one ⊩ᴿ U ⟩
  step U h = subst (λ W → fst W ⊑ fst U) (sym collapse) h

-- The exact boundary. K2 proves the reflection under LEM and separativity;
-- the refuting instance is antisymmetric and not separative, so separativity
-- is the missing hypothesis and antisymmetry is not.

reflection-under-separativity :
  LEM ℓ → RO.separative → (p q : NR.Two) → RO.i q ≤ᴮ RO.i p → ⟨ NR._≼_ q p ⟩
reflection-under-separativity = RO.separative→reflect

reflection-boundary :
    (NR.antisymmetric × (NR.separative → ⟨ ⊥ ⟩))
  × ((OrderReflection → ⟨ ⊥ ⟩) × (MonoConverse → ⟨ ⊥ ⟩))
reflection-boundary =
    (NR.antisym , NR.not-separative)
  , (order-reflection-fails , mono-converse-fails)

--------------------------------------------------------------------------------
-- 3. The embedding is never onto
--------------------------------------------------------------------------------

-- No image is the bottom of the algebra: the image of p contains p, so it is
-- positive, and a positive element is nonzero constructively.

image-misses-⊥ : (p : NR.Two) → RO.i p ≡ ⊥ᴮ → ⟨ ⊥ ⟩
image-misses-⊥ p e =
  Empty.rec (RO.positive→nonzero (RO.i p) (RO.i-pos p) e)

OntoImage : Type (ℓ-suc ℓ)
OntoImage = (U : Reg) → ∥ Σ[ p ∈ NR.Two ] (RO.i p ≡ U) ∥₁

i-not-onto : OntoImage → ⟨ ⊥ ⟩
i-not-onto onto =
  PT.rec isProp⊥* (λ z → image-misses-⊥ (fst z) (snd z)) (onto ⊥ᴮ)

-- Concretely, at this instance the algebra has exactly two elements and both
-- conditions sit at the top, so the image is the singleton of the top and the
-- element it misses is the bottom.

both-at-top : (RO.i NR.one ≡ ⊤ᴮ) × (RO.i NR.low ≡ ⊤ᴮ)
both-at-top = IC.i-one-top , IC.i-low-top

--------------------------------------------------------------------------------
-- 4. trᴮ Γᴾ ≡ U̇, REFUTED
--------------------------------------------------------------------------------

-- The transcription. Ent stands for the coded entries; entryᴾ p is the entry
-- of trᴮ Γᴾ coming from the condition p, whose weight is the image of p
-- (Γᴾ-spec at StandardNames.agda:619-621, carried across by trᴮ-entries at
-- TranslateForward.agda:441-442); entryᴮ U is the entry of U̇ at the algebra
-- element U, whose weight is U (U̇-spec, StandardNames.agda:637-639).
--
-- The single hypothesis `weights` is exactly the second component of K3's
-- entry injectivity, entry-inj (NameKernel.agda:321), composed with those two
-- specifications: if the two entries are the same entry then their weights are
-- the same weight. Coded equality of entries is ≈ˢ rather than a host path;
-- under the `paths` hypothesis every K5 module carries (architecture section
-- 1.2) the two coincide, which is why the transcription may use ≡.

module GenericName {ℓᴱ : Level} (Ent : Type ℓᴱ)
  (entryᴾ : NR.Two → Ent)
  (entryᴮ : Reg → Ent)
  (weights : (p : NR.Two) (U : Reg) → entryᴾ p ≡ entryᴮ U → RO.i p ≡ U)
  where

  -- "Every entry of U̇ is an entry of trᴮ Γᴾ", which is one half of the
  -- claimed identity of the two codes. Refuting the half refutes the whole.

  SameName : Type (ℓ-max ℓᴱ (ℓ-suc ℓ))
  SameName = (U : Reg) → ∥ Σ[ p ∈ NR.Two ] (entryᴾ p ≡ entryᴮ U) ∥₁

  same-name-fails : SameName → ⟨ ⊥ ⟩
  same-name-fails same = PT.rec isProp⊥* step (same ⊥ᴮ)
    where
    step : Σ[ p ∈ NR.Two ] (entryᴾ p ≡ entryᴮ ⊥ᴮ) → ⟨ ⊥ ⟩
    step (p , e) = image-misses-⊥ p (weights p ⊥ᴮ e)

-- The parameters are satisfiable, so this is not the refutation of an empty
-- hypothesis: entries as name-and-weight pairs satisfy the weight law by
-- congruence.

module Witnessed = GenericName (Reg × Reg)
  (λ p → RO.i p , RO.i p) (λ U → U , U) (λ p U e → cong snd e)

generic-name-identification-fails : Witnessed.SameName → ⟨ ⊥ ⟩
generic-name-identification-fails = Witnessed.same-name-fails
