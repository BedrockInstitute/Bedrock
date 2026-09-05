# The environment supply at the concrete site

Step 6's environment supply, landed as a new master that imports
`L.Condensation`. The block lives here, not inside the chapter, because the
chapter's own live lines were what made the same content heap-exhaust
(C-49). The env supply proves that an environment and its components stay
inside the level `Lset lam`; the tower-neutral fields and the
finite-supremum merge close the same carrier generically over `(K, Ktr)`.

```agda
{-# OPTIONS --cubical --safe --guardedness #-}

open import Base.Prelude
open import Base.Truth
open import Base.Classical using ( LEM )

module LJ-1-287.Min {ℓ : Level} (lem : LEM (ℓ-suc ℓ)) where
open import FOL.ZFStructure using ( module hPropStructure )
open import FOL.Syntax using ( Formula; var; con; _∈̇_; _∧̇_; ⊤̇; ∃̇∈ )
import FOL.Absoluteness
open import V.Hierarchy {ℓ} using ( 𝒮ᵥ )
open import V.Coding {ℓ} using ( pr )
open import L.Constructible {ℓ} using ( 𝒮ʟ; isL; isL-trans; Lset; IsOrd )
open import L.Axioms.Numerals {ℓ} using ( numeralL-fst )
open import L.Coding.Model {ℓ}
  using ( consAtL; subValAt; subValSuccAt; tmValAt; envSetAt; envOverAt )
open import Cubical.Data.Sum using ( inl; inr )
open import Cubical.HITs.CumulativeHierarchy.Base using ( V; _∈_ )
open import Cubical.HITs.CumulativeHierarchy.Constructions
  using ( ⁅_,_⁆; ⁅_⁆s; pairing-ax; ∅; module InfinitySet )
open import Cubical.HITs.CumulativeHierarchy.Properties using ( ∈∈ₛ )
open InfinitySet using ( #_; sucV )
import Cubical.HITs.PropositionalTruncation as PT
open PT using ( ∣_∣₁; ∥_∥₁ )

open TruthAlgebra (hPropAlgebra (ℓ-suc ℓ))
open hPropStructure 𝒮ʟ

module AbsL = FOL.Absoluteness.Single 𝒮ᵥ isL isL-trans
open AbsL renaming ( _⊨ᵐ_ to _⊨_ )

-- The names the master's own tail block imports, plus the two names that
-- `L.Condensation` DEFINES and this block consumes.
open import L.Constructible {ℓ} using ( Lset-mono )
open import L.Axioms.Basic {ℓ} using ( LsetS )
open import L.Coding.Bound {ℓ} lem using ( module Bound )
open import L.Condensation {ℓ} lem using ( envSetB; module EnvSet )
```

```agda
-- =====================================================================
-- THE ENV SUPPLY, the tower-neutral fields, and the finite-supremum
-- merge.  The master opens hPropStructure 𝒮ʟ, so `S` is the L-carrier
-- and the ambient carrier is V ℓ with Cubical _∈_.
-- =====================================================================

open import V.Hierarchy {ℓ} using ( extensionalV )
open import L.Constructible {ℓ}
  using ( isTransV; Lset-layer; layer-trans; 𝒟ₒ; 𝒟ₒ-intro
        ; ∪-trans; isPropIsTransV )
open import L.Axioms.Basic {ℓ}
  using ( isL-Lset; finSet; Lset-suc; pair∈Lset-suc; sgl∈Lset-suc
        ; module FinOf )
open import L.Coding.Environment {ℓ} using ( env; cons )
open import L.Coding.Model {ℓ}
  using ( tmValAt-out; subValAt-adequate; subValSuccAt-adequate
        ; consAtL-adequate; extAt-out; extAt-in )
open import L.Coding.Bound {ℓ} lem using ( Lset-out′ )
open import L.Coding.Key {ℓ} lem using ( envSetNumeral∈ )
open import L.Coding.Sound {ℓ} lem using ( module NumeralFromGeneric )
open import L.Coding.EnvSet {ℓ} lem using ( envSet; module Generic )
open import L.Definability {ℓ} using ( module DefOf )
open import L.Ordinal {ℓ} using ( suc-ord; mem-ord; ∅-ord )
open import L.Ordinal.Linear {ℓ} lem using ( ord-tri )
open import L.Ordinal.StageArith {ℓ} lem using ( sucIter )
open import V.Model {ℓ} using ( self∈sucV )
open import Cubical.Data.Sigma using ( _,_; Σ≡Prop )
open import Cubical.Functions.Logic using ( ⇔toPath )
open import Cubical.Data.Nat using ( ℕ )
open import Cubical.Data.FinData using ( toℕ )
open import Cubical.Data.FinData.FiniteChoice using ( choice )
open import Cubical.Data.Vec using ( Vec; lookup )
import Cubical.Data.Sum as Sum
open import Cubical.HITs.CumulativeHierarchy.Constructions using ( ⋃_; union-ax; _∪_ )
open InfinitySet using ( ω )
open import Cubical.HITs.CumulativeHierarchy.Properties
  using ( ⟪_⟫; ⟪_⟫↪; ∈-asFiber; extensionality; _⊆_; _∈ₛ_ )

-- Named Fin indices, definitionally the same `suc` chains the field
-- types write.
pattern one   = suc zero
pattern two   = suc one
pattern three = suc two
pattern four  = suc three
pattern five  = suc four
pattern six   = suc five
pattern seven = suc six
pattern eight = suc seven
pattern nine  = suc eight

-- LJ-1.287 MINIMAL REPRODUCER.  The two lines of `sucV∈`, with everything
-- else removed.  The supplier comes from `L.Coding.Key`, which is already
-- compiled, so any cost measured here belongs to the CALL.
open import L.Coding.Key {ℓ} lem using ( union∈Lset-suc )

minSucV∈ : (δ a : V ℓ)
         → ⟨ ⁅ a , ⁅ a ⁆s ⁆ ∈ Lset (sucV (sucV (sucV δ))) ⟩
         → ⟨ sucV a ∈ Lset (sucIter 4 δ) ⟩
minSucV∈ δ a p = union∈Lset-suc (sucV (sucV (sucV δ))) ⁅ a , ⁅ a ⁆s ⁆ p
```
