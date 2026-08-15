# LJ-1.275 CURE A control: the NEW master's imports and nothing else

This file is a PROBE for `[LJ-1.275]`. It carries the SAME env-supply block that
`[LJ-1.266]`'s `CondensationEnv.lagda.md` appended INSIDE `L.Condensation`. Here the
block lives in a new master that IMPORTS `L.Condensation`. The two arms differ only in
that placement.

```agda
{-# OPTIONS --cubical --safe --guardedness #-}

open import Base.Prelude
open import Base.Truth
open import Base.Classical using ( LEM )

module LJ-1-275.SupplyNewControl {ℓ : Level} (lem : LEM (ℓ-suc ℓ)) where
open import FOL.ZFStructure using ( module hPropStructure )
open import FOL.Syntax using
  ( Formula; var; con; _∈̇_; _≐_; _∧̇_; _∨̇_; _⇒̇_; ¬̇_; ⊤̇; ⊥̇
  ; ∃̇_; ∃̇∈; ∀̇∈ )
open import FOL.LevyHierarchy using
  ( Δ₀; δ-∈; δ-≐; δ-∧; δ-∨; δ-⇒; δ-¬; δ-⊤; δ-⊥; δ-∀∈; δ-∃∈; Σ₁; σ-Δ₀; σ-∃ )
open import FOL.Manipulation.Parameters using ( countFo )
open import FOL.Manipulation.Relabelling using ( embed )
import FOL.Count
import FOL.Absoluteness
open import V.Hierarchy {ℓ} using ( 𝒮ᵥ )
open import V.Coding {ℓ} using ( pr )
open import V.Model {ℓ} using ( pair-singleton )
open import L.Constructible {ℓ} using ( 𝒮ʟ; isL; isL-trans; Lset; IsOrd )
open import L.Absoluteness {ℓ} using ( Δ₀-liftFo )
open import L.Coding.Base {ℓ} using ( Δ₀-prAt )
open import L.Coding.Environment {ℓ} using ( Δ₀-consAt; Δ₀-sucAt )
open import L.Axioms.Numerals {ℓ} using ( numeralL; numeralL-fst; pairʟ; pairʟ-fst )
open import L.Coding.Model {ℓ}
  using ( prAtL; appAt; appAt-adequate; consAtL; sucAtL; closedAt; domAt
        ; sucAtL-adequate
        ; extAt; extAt-in-both
        ; interAt; unionAt
        ; arityTagAtL; arityTagPairAtL
        ; arityTagAtL-adequate; arityTagPairAtL-adequate
        ; tagAtL; tagAtL-adequate; tagPairAtL-adequate; prAtL-adequate
        ; prʟ; prʟ-fst
        ; binShapeAt; unShapeAt; bothSameAt; oneSameAt; oneSuccAt; succSndAt
        ; binShape-out; binShape-in; unShape-out; unShape-in
        ; emptyAt; botClauseAt
        ; subValAt; subValSuccAt; binClauseAt; propRel
        ; negClauseAt; topClauseAt; forallClauseAt; existClauseAt
        ; body∀; body∃; bodyAll; bodyEx
        ; tmValAt; envSetAt; envOverAt; envOverAt-transport; implAt
        ; atomBody; memClauseAt; eqClauseAt; impClauseAt
        ; allInClauseAt; exInClauseAt
        ; svAt-in; svAt-out; domAt-intro; domAt-out; domAt-in
        ; valuesInAt-in; valuesInAt-out )
open import L.Hierarchy {ℓ} lem using ( Lset-only; Lset-defines )
open import L.Coding.Sequence {ℓ} lem using ( LsetGraphAt )
open import L.Coding.Shape {ℓ}
  using ( isTmAt; shapes; binForm; unForm; bothTm; fstTm; noneB; noneU; zeroPay
        ; shapedAt )
open import L.Coding.CodeSet {ℓ} lem using ( hasWitnessAt; keyArityAtL )
open import L.Coding.Graph {ℓ} lem using ( satGraphAt; twelveAt )
open import L.Coding.Powerset {ℓ} lem using ( isCodeAt; DefBody; DefinesAt; envOneAt )
open import Cubical.Data.Vec using ( map )
open import Cubical.Data.Nat using ( _+_ )
import Cubical.Data.Empty as Empty
open import Cubical.Data.Sum using ( _⊎_; inl; inr )
open import Cubical.HITs.CumulativeHierarchy.Base using ( V; _∈_; setIsSet )
open import Cubical.HITs.CumulativeHierarchy.Constructions
  using ( ⁅_,_⁆; ⁅_⁆s; pairing-ax; module InfinitySet )
open import Cubical.HITs.CumulativeHierarchy.Properties using ( ∈∈ₛ )
open InfinitySet using ( #_; sucV )
import Cubical.HITs.PropositionalTruncation as PT
open PT using ( ∣_∣₁; squash₁; ∥_∥₁ )

open TruthAlgebra (hPropAlgebra (ℓ-suc ℓ))
open hPropStructure 𝒮ʟ

module AbsL = FOL.Absoluteness.Single 𝒮ᵥ isL isL-trans
open AbsL renaming ( _⊨ᵐ_ to _⊨_ )

module Cnt = FOL.Count.Count {ℓ = ℓ-suc ℓ} S
-- The names the master's own tail block imports, plus the two names that
-- `L.Condensation` DEFINES and this block consumes.
open import L.Constructible {ℓ} using ( Lset-mono )
open import L.Axioms.Basic {ℓ} using ( LsetS )
open import L.Coding.Bound {ℓ} lem using ( module Bound )
open import Cubical.HITs.CumulativeHierarchy.Constructions using ( ∅ )
open import L.Condensation {ℓ} lem using ( envSetB; module EnvSet )
```
