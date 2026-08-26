{-# OPTIONS --cubical --safe --guardedness #-}

-- [LJ-1.668] PROBE.  Is the limit stage closed under the definable
-- powerset at an arbitrary member.
-- It runs in agents/tasks/LJ-1-668/ and lands nothing in src/.
--
-- THE OBLIGATION the brief names is powiter-status, the limit-stage
-- reading of Bound.PowIter's hypothesis
-- (src/L/Coding/Bound.lagda.md:151-152), i.e. Bound.Iter.pow∈λ at
-- D = 𝒟ₒ (src/L/Coding/Bound.lagda.md:109-110).  This file does NOT
-- inhabit that type as a closed term.  It does not inhabit its
-- negation.  D-10 is the job: price the TARGET's truth at members
-- the frame admits, before anyone prices a proof of the arbitrary
-- case.
--
-- WHAT IS SETTLED.
--   1. A set is a member of its own definable powerset (A∈𝒟ₒ).
--   2. A stage Lset δ is a member of Lset lam whenever δ ∈ lam.
--   3. 𝒟ₒ (Lset δ) is a member of Lset lam whenever sucV δ ∈ lam.
--      So the members the TOWER itself applies 𝒟ₒ to do not refute.
--   4. The empty set is a member of Lset lam, and 𝒟ₒ ∅ ≡ sucV ∅,
--      so 𝒟ₒ ∅ is a member of Lset lam.  The empty set does not
--      refute.
--   5. The consumer Bound.Iter.pow∈λ, generic in the operator, is
--      imported and instantiated at 𝒟ₒ (W2).  It is not rewritten.
--
-- WHAT IS NOT SETTLED.
--   powiter-status at an arbitrary member.  The only route the tree
--   has is 𝒟ₒ-intro at the value 𝒟ₒ y, which is [LJ-1.169]'s
--   Describes (agents/tasks/LJ-1-169/ProbeLJ1169A.agda:80-86).
--   Nothing in src/ supplies Describes.  A Formula Code 1 for 𝒟ₒ
--   is a second debt and the brief forbids funding it here.
--
-- Nothing is postulated.  Nothing is holed.  Nothing lands in src/.
-- ONE Agda process per run, GHCRTS="-A64m -I0 -M2g", the wide caliber,
-- set on the pane by the program and untouched here.

open import Base.Prelude
open import Base.Truth
open import Base.Classical using ( LEM )

module LJ-1-668.Probe668 {ℓ : Level} (lem : LEM (ℓ-suc ℓ)) where

open import FOL.ZFStructure using ( module hPropStructure )
open import FOL.Syntax using ( Formula; ⊤̇ )
open import V.Hierarchy {ℓ} using ( 𝒮ᵥ )
open import V.Model {ℓ} using ( ∈sucV-elim; self∈sucV )
open import L.Definability {ℓ} using ( module DefOf )
open import L.Constructible {ℓ}
  using ( IsOrd; Lset; 𝒟ₒ; 𝒟ₒ-intro; 𝒟ₒ-inv; Lset-in; Lset-mono )
open import L.Axioms.Basic {ℓ} using ( Lset-suc; ∅∈𝒟ₒ )
open import L.Ordinal {ℓ} using ( ∅-ord; suc-ord )
open import L.Ordinal.Stages {ℓ} lem using ( ord∈Lset-suc )
open import L.Ordinal.StageArith {ℓ} lem using ( sucIter )
open import L.Coding.Bound {ℓ} lem using ( module Bound )

open import Cubical.Data.Sigma using ( Σ-syntax; _,_ )
import Cubical.Data.Empty as Empty
import Cubical.HITs.PropositionalTruncation as PT
open PT using ( ∥_∥₁; ∣_∣₁ )
open import Cubical.HITs.CumulativeHierarchy.Properties
  using ( _∈ₛ_; ∈∈ₛ; _⊆_; extensionality )
open import Cubical.HITs.CumulativeHierarchy.Constructions
  using ( ∅; ∅-empty; module InfinitySet )
open InfinitySet using ( sucV )

open TruthAlgebra (hPropAlgebra (ℓ-suc ℓ))
open hPropStructure 𝒮ᵥ

-- =====================================================================
-- D-10, MEMBERS THE FRAME ADMITS.
--
-- 𝒟ₒ-intro at ⊤̇ is DefOf.defSet⊤≡A
-- (src/L/Definability.lagda.md:178-179): the formula "true" carves
-- out the whole of A, so A ∈ 𝒟ₒ A.  The tower never records this
-- as a named lemma.  Every stage-member fact below is one call.
-- =====================================================================

A∈𝒟ₒ : (A : S) → ⟨ A ∈ˢ 𝒟ₒ A ⟩
A∈𝒟ₒ A = 𝒟ₒ-intro A A ∣ ⊤̇ , DefOf.defSet⊤≡A A ∣₁

-- 𝒟ₒ ∅ is the singleton {∅}, which is sucV ∅.  Every definable
-- subset of ∅ is ∅ (defSet φ ⊆ ∅), and ∅ itself is definable
-- (A∈𝒟ₒ).  So the empty set does not refute the target.
dee-empty : 𝒟ₒ ∅ ≡ sucV ∅
dee-empty = extensionality (𝒟ₒ ∅) (sucV ∅) (sub₁ , sub₂)
  where
  sub₁ : ⟨ 𝒟ₒ ∅ ⊆ sucV ∅ ⟩
  sub₁ x x∈ₛ = ∈∈ₛ {a = x} {b = sucV ∅} .fst
    (PT.rec (snd (x ∈ˢ sucV ∅)) from
      (𝒟ₒ-inv ∅ x (∈∈ₛ {a = x} {b = 𝒟ₒ ∅} .snd x∈ₛ)))
    where
    from : Σ[ φ ∈ Formula _ 1 ] (DefOf.defSet ∅ φ ≡ x)
         → ⟨ x ∈ˢ sucV ∅ ⟩
    from (φ , q) = subst (λ w → ⟨ w ∈ˢ sucV ∅ ⟩) q (carve⊆∅ φ)
      where
      carve⊆∅ : (ψ : Formula _ 1) → ⟨ DefOf.defSet ∅ ψ ∈ˢ sucV ∅ ⟩
      carve⊆∅ ψ = subst (λ w → ⟨ w ∈ˢ sucV ∅ ⟩) (sym carve≡∅)
        (self∈sucV ∅)
        where
        carve≡∅ : DefOf.defSet ∅ ψ ≡ ∅
        carve≡∅ = extensionality (DefOf.defSet ∅ ψ) ∅ (c₁ , c₂)
          where
          c₁ : ⟨ DefOf.defSet ∅ ψ ⊆ ∅ ⟩
          c₁ y y∈ₛ = ∈∈ₛ {a = y} {b = ∅} .fst
            (DefOf.defSet⊆A ∅ ψ y
              (∈∈ₛ {a = y} {b = DefOf.defSet ∅ ψ} .snd y∈ₛ))
          c₂ : ⟨ ∅ ⊆ DefOf.defSet ∅ ψ ⟩
          c₂ y y∈ₛ = Empty.rec (∅-empty y y∈ₛ)

  sub₂ : ⟨ sucV ∅ ⊆ 𝒟ₒ ∅ ⟩
  sub₂ x x∈ₛ = ∈∈ₛ {a = x} {b = 𝒟ₒ ∅} .fst
    (∈sucV-elim {A = ∅} {x = x} (snd (x ∈ˢ 𝒟ₒ ∅))
      (∈∈ₛ {a = x} {b = sucV ∅} .snd x∈ₛ)
      (λ x∈∅ → Empty.rec (∅-empty x (∈∈ₛ {a = x} {b = ∅} .fst x∈∅)))
      (λ x≡∅ → subst (λ w → ⟨ w ∈ˢ 𝒟ₒ ∅ ⟩) (sym x≡∅) (A∈𝒟ₒ ∅)))

-- =====================================================================
-- THE TELESCOPE.  Bound's own parameters
-- (src/L/Coding/Bound.lagda.md:130-132): a limit ordinal closed under
-- successor, with ∅ as a member.  P-l: lam is an atom.
-- =====================================================================

module At (lam : S) (ordλ : IsOrd lam)
  (succλ : (d : S) → ⟨ d ∈ˢ lam ⟩ → ⟨ sucV d ∈ˢ lam ⟩)
  (∅∈λ : ⟨ ∅ ∈ˢ lam ⟩) where

  module B = Bound lam ordλ succλ ∅∈λ

  -- A stage is a member of the limit stage: Lset δ ∈ 𝒟ₒ (Lset δ)
  -- by A∈𝒟ₒ, and Lset-in climbs the union.
  lset∈limit : (δ : S) → ⟨ δ ∈ˢ lam ⟩ → ⟨ Lset δ ∈ˢ Lset lam ⟩
  lset∈limit δ δ∈ = Lset-in lam δ (Lset δ) δ∈ (A∈𝒟ₒ (Lset δ))

  -- 𝒟ₒ of a STAGE is the next stage (Lset-suc,
  -- src/L/Axioms/Basic.lagda.md:196).  The next stage is a member of
  -- the limit whenever the limit holds the successor of δ.  These
  -- are the members the tower itself applies 𝒟ₒ to.
  dee-stage∈limit : (δ : S) → ⟨ sucV δ ∈ˢ lam ⟩
                  → ⟨ 𝒟ₒ (Lset δ) ∈ˢ Lset lam ⟩
  dee-stage∈limit δ suc∈ =
    subst (λ w → ⟨ w ∈ˢ Lset lam ⟩) (Lset-suc δ)
      (lset∈limit (sucV δ) suc∈)

  -- The empty set is a member of every nonempty stage
  -- (src/L/Hull.lagda.md:317-318, same two calls).
  empty∈limit : ⟨ ∅ ∈ˢ Lset lam ⟩
  empty∈limit = Lset-in lam ∅ ∅ ∅∈λ (∅∈𝒟ₒ ∅)

  -- 𝒟ₒ ∅ ≡ sucV ∅, and sucV ∅ is an ordinal, so it appears at the
  -- stage after itself.  Two applications of succλ put that stage
  -- below lam.
  dee-empty∈limit : ⟨ 𝒟ₒ ∅ ∈ˢ Lset lam ⟩
  dee-empty∈limit =
    subst (λ w → ⟨ w ∈ˢ Lset lam ⟩) (sym dee-empty)
      (Lset-mono {α = lam} {β = sucV (sucV ∅)}
        (succλ (sucV ∅) (succλ ∅ ∅∈λ))
        (ord∈Lset-suc (sucV ∅) (suc-ord ∅-ord)))

  -- THE HYPOTHESIS, verbatim Bound.PowIter
  -- (src/L/Coding/Bound.lagda.md:151-152).  Named, not inhabited.
  PowIter : Type (ℓ-suc ℓ)
  PowIter = (δ y : S) → ⟨ y ∈ˢ Lset δ ⟩
          → ∥ Σ[ k ∈ ℕ ] ⟨ 𝒟ₒ y ∈ˢ Lset (sucIter k δ) ⟩ ∥₁

  -- THE CONSUMER.  W2: one instance of Bound.Iter.pow∈λ, not a
  -- second proof.  IT IS NOT THE OBLIGATION: the obligation has no
  -- PowIter argument.
  from-iter : PowIter
            → (y : S) → ⟨ y ∈ˢ Lset lam ⟩ → ⟨ 𝒟ₒ y ∈ˢ Lset lam ⟩
  from-iter pi = I.pow∈λ
    where
    module I = B.PowIter pi

  -- The brief's type, named here so the search can point at it, and
  -- NOT lifted to the probe module.  The witness reads
  -- Target.powiter-status at the probe module
  -- (scripts/pod/witness.py:278).  Leaving the name inside At is the
  -- stated NO-GO: the closed term the brief asked for is not built,
  -- and no refutation at a member the frame admits is built either.
  powiter-status : Type (ℓ-suc ℓ)
  powiter-status = (y : S) → ⟨ y ∈ˢ Lset lam ⟩ → ⟨ 𝒟ₒ y ∈ˢ Lset lam ⟩

-- powiter-status is not lifted.  The witness meter reads
-- Target.powiter-status at this module (scripts/pod/witness.py:278)
-- and will not find it.
