{-# OPTIONS --cubical --safe --guardedness #-}

-- [LJ-1.30] Probe B: the adequacy risk of the constant-free reader.  The
-- rewrite of L.Coding.Environment keeps consAt-adequate's statement, so
-- its proof only swaps tagAt-adequate for tag0At-adequate.  The new
-- lemma is tag0At-adequate: satisfaction of the emptiness readers is the
-- Kuratowski pair pr ∅ W.  This probe builds the meta machinery (a set
-- with no members is ∅; {∅} and {∅, W} are characterized by empty
-- members) and proves tag0At-adequate.  If this typechecks, the rewrite
-- price is supported; if it walls, the cure is dead.
-- Untracked probe; one Agda process under GHCRTS="-A64m -I0 -M8g";
-- never committed.

open import Base.Prelude
open import Base.Truth

module ProbeLJ130B {ℓ : Level} where

open import FOL.ZFStructure using ( module hPropStructure )
open import FOL.Syntax
  using ( Formula; var; con; _∈̇_; _≐_; _∧̇_; _∨̇_; _⇒̇_; ¬̇_; ⊤̇; ⊥̇
        ; ∃̇_; ∀̇_; ∀̇∈; ∃̇∈ )
import FOL.Semantics
open import V.Hierarchy {ℓ} using ( 𝒮ᵥ )
open import V.Coding {ℓ} using ( pr )
open import L.Coding.Base {ℓ} using ( sgl-char; pair-char; prChar-fwd; prChar-bwd )
import Cubical.Data.Sum as Sum
open Sum using ( _⊎_; inl; inr )
import Cubical.HITs.PropositionalTruncation as PT
open PT using ( ∥_∥₁; ∣_∣₁; squash₁ )
open import Cubical.Functions.Logic using ( ⇔toPath )
open import Cubical.Data.Empty as E hiding ( elim )
open import Cubical.HITs.CumulativeHierarchy.Base
  using ( V; sett; setIsSet; _∈_ )
open import Cubical.HITs.CumulativeHierarchy.Properties
  using ( _∈ₛ_; ∈∈ₛ; _⊆_; extensionality )
open import Cubical.HITs.CumulativeHierarchy.Constructions
  using ( ⁅_,_⁆; ⁅_⁆s; ∅; ∅-empty )

open TruthAlgebra (hPropAlgebra (ℓ-suc ℓ))
open hPropStructure 𝒮ᵥ
module Sem = FOL.Semantics (hPropAlgebra (ℓ-suc ℓ)) 𝒮ᵥ
open Sem using ( _^_ )
open Sem.At (V ℓ) id using ( _⊨_; ⟦_⟧ )

-- =====================================================================
-- SECTION 1: EMPTINESS.  A set with no members is ∅, and conversely.
-- The member relations come in two shapes: the satisfaction relation
-- `_∈_` and the set-membership `_∈ₛ_`; ∈∈ₛ bridges them.
-- =====================================================================
Emptyₛ : V ℓ → Type (ℓ-suc ℓ)
Emptyₛ z = (y : V ℓ) → ⟨ y ∈ₛ z ⟩ → E.⊥

∅-uniq : (z : V ℓ) → Emptyₛ z → z ≡ ∅
∅-uniq z hz = extensionality z ∅ (sub₁ , sub₂)
  where
  sub₁ : ⟨ z ⊆ ∅ ⟩
  sub₁ y y∈z = E.rec (hz y y∈z)
  sub₂ : ⟨ ∅ ⊆ z ⟩
  sub₂ y y∈∅ = E.rec (∅-empty y y∈∅)

∅-uniq-sym : (z : V ℓ) → z ≡ ∅ → Emptyₛ z
∅-uniq-sym z e y y∈z = ∅-empty y (subst (λ w → ⟨ y ∈ₛ w ⟩) e y∈z)

-- The emptiness shape the satisfaction of `∀̇∈ (var zero) ⊥̇` gives.
Empty' : V ℓ → Type (ℓ-suc ℓ)
Empty' z = (y : V ℓ) → ⟨ y ∈ z ⟩ → E.⊥* {ℓ-suc ℓ}

empty'→∅ : (z : V ℓ) → Empty' z → z ≡ ∅
empty'→∅ z hz = ∅-uniq z (λ y y∈ₛz → lower (hz y (∈∈ₛ {a = y} {b = z} .snd y∈ₛz)))

∅→empty' : (z : V ℓ) → z ≡ ∅ → Empty' z
∅→empty' z e y y∈z = lift (∅-empty y (∈∈ₛ {a = y} {b = ∅} .fst (subst (λ w → ⟨ y ∈ w ⟩) e y∈z)))

-- =====================================================================
-- SECTION 2: THE EMPTY-READER SHAPES.  A set is {∅} exactly when it has
-- an empty member and every member is empty.  A set is {∅, W} exactly
-- when it has an empty member, W is a member, and every member is empty
-- or W.  These are the shapes sgl0At / pair0At unfold to.
-- =====================================================================
EmptySgl : V ℓ → Type (ℓ-suc ℓ)
EmptySgl w = ∥ Σ[ z ∈ V ℓ ] (⟨ z ∈ w ⟩ × Empty' z) ∥₁
          × ((z : V ℓ) → ⟨ z ∈ w ⟩ → Empty' z)

EmptyPair : V ℓ → V ℓ → Type (ℓ-suc ℓ)
EmptyPair W w = ∥ Σ[ z ∈ V ℓ ] (⟨ z ∈ w ⟩ × Empty' z) ∥₁
             × (⟨ W ∈ w ⟩ × ((z : V ℓ) → ⟨ z ∈ w ⟩ → ∥ Empty' z ⊎ (z ≡ W) ∥₁))

-- The SglOf ∅ / PairOf ∅ shapes prChar-fwd expects, inlined because the
-- originals are private in L.Coding.Base.  The types are definitionally
-- the same.
SglOf∅ : V ℓ → Type (ℓ-suc ℓ)
SglOf∅ w = ⟨ ∅ ∈ w ⟩ × ((z : V ℓ) → ⟨ z ∈ w ⟩ → z ≡ ∅)

PairOf∅ : V ℓ → V ℓ → Type (ℓ-suc ℓ)
PairOf∅ W w = ⟨ ∅ ∈ w ⟩ × (⟨ W ∈ w ⟩ × ((z : V ℓ) → ⟨ z ∈ w ⟩ → ∥ (z ≡ ∅) ⊎ (z ≡ W) ∥₁))

EmptySgl→SglOf∅ : (w : V ℓ) → EmptySgl w → SglOf∅ w
EmptySgl→SglOf∅ w (h₁ , hall) = hu , hall'
  where
  hu : ⟨ ∅ ∈ w ⟩
  hu = PT.rec ((∅ ∈ w) .snd)
    (λ { (z , z∈w , ez) → subst (λ u → ⟨ u ∈ w ⟩) (empty'→∅ z ez) z∈w })
    h₁
  hall' : (z : V ℓ) → ⟨ z ∈ w ⟩ → z ≡ ∅
  hall' z z∈w = empty'→∅ z (hall z z∈w)

EmptyPair→PairOf∅ : (W w : V ℓ) → EmptyPair W w → PairOf∅ W w
EmptyPair→PairOf∅ W w (h₁ , hW , hall) = hu , hW , hall'
  where
  hu : ⟨ ∅ ∈ w ⟩
  hu = PT.rec ((∅ ∈ w) .snd)
    (λ { (z , z∈w , ez) → subst (λ u → ⟨ u ∈ w ⟩) (empty'→∅ z ez) z∈w })
    h₁
  hall' : (z : V ℓ) → ⟨ z ∈ w ⟩ → ∥ (z ≡ ∅) ⊎ (z ≡ W) ∥₁
  hall' z z∈w = PT.map (Sum.rec (λ ez → inl (empty'→∅ z ez)) (λ e → inr e))
    (hall z z∈w)

SglOf∅→EmptySgl : (w : V ℓ) → SglOf∅ w → EmptySgl w
SglOf∅→EmptySgl w (h∅ , hall) =
    (∣ ∅ , (h∅ , ∅→empty' ∅ refl) ∣₁)
  , (λ z z∈w → ∅→empty' z (hall z z∈w))

PairOf∅→EmptyPair : (W w : V ℓ) → PairOf∅ W w → EmptyPair W w
PairOf∅→EmptyPair W w (h∅ , hW , hall) =
    (∣ ∅ , (h∅ , ∅→empty' ∅ refl) ∣₁)
  , (hW , λ z z∈w → PT.map (Sum.rec (λ e → inl (∅→empty' z e)) (λ e → inr e))
      (hall z z∈w))

-- =====================================================================
-- SECTION 3: prChar∅.  The same characterization as prChar-fwd / bwd,
-- with U fixed to ∅ and the shapes written through empty members.
-- =====================================================================
prChar∅-fwd : (Q W : V ℓ)
  → ∥ Σ[ w ∈ V ℓ ] (⟨ w ∈ Q ⟩ × EmptySgl w) ∥₁
  → ∥ Σ[ w ∈ V ℓ ] (⟨ w ∈ Q ⟩ × EmptyPair W w) ∥₁
  → ((y : V ℓ) → ⟨ y ∈ Q ⟩ → ∥ EmptySgl y ⊎ EmptyPair W y ∥₁)
  → Q ≡ pr ∅ W
prChar∅-fwd Q W h₁ h₂ h₃ =
  prChar-fwd Q ∅ W
    (PT.map (λ { (w , w∈Q , s) → w , w∈Q , EmptySgl→SglOf∅ w s }) h₁)
    (PT.map (λ { (w , w∈Q , p) → w , w∈Q , EmptyPair→PairOf∅ W w p }) h₂)
    (λ y y∈Q → PT.map (Sum.rec (λ s → inl (EmptySgl→SglOf∅ y s))
                               (λ p → inr (EmptyPair→PairOf∅ W y p)))
      (h₃ y y∈Q))

prChar∅-bwd : (Q W : V ℓ) → Q ≡ pr ∅ W
  → ∥ Σ[ w ∈ V ℓ ] (⟨ w ∈ Q ⟩ × EmptySgl w) ∥₁
  × (∥ Σ[ w ∈ V ℓ ] (⟨ w ∈ Q ⟩ × EmptyPair W w) ∥₁
  × ((y : V ℓ) → ⟨ y ∈ Q ⟩ → ∥ EmptySgl y ⊎ EmptyPair W y ∥₁))
prChar∅-bwd Q W e = h₁' , (h₂' , h₃')
  where
  h : ∥ Σ[ w ∈ V ℓ ] (⟨ w ∈ Q ⟩ × SglOf∅ w) ∥₁
    × (∥ Σ[ w ∈ V ℓ ] (⟨ w ∈ Q ⟩ × PairOf∅ W w) ∥₁
    × ((y : V ℓ) → ⟨ y ∈ Q ⟩ → ∥ SglOf∅ y ⊎ PairOf∅ W y ∥₁))
  h = prChar-bwd Q ∅ W e
  h₁' : ∥ Σ[ w ∈ V ℓ ] (⟨ w ∈ Q ⟩ × EmptySgl w) ∥₁
  h₁' = PT.map (λ { (w , w∈Q , s) → w , w∈Q , SglOf∅→EmptySgl w s }) (fst h)
  h₂' : ∥ Σ[ w ∈ V ℓ ] (⟨ w ∈ Q ⟩ × EmptyPair W w) ∥₁
  h₂' = PT.map (λ { (w , w∈Q , p) → w , w∈Q , PairOf∅→EmptyPair W w p }) (fst (snd h))
  h₃' : (y : V ℓ) → ⟨ y ∈ Q ⟩ → ∥ EmptySgl y ⊎ EmptyPair W y ∥₁
  h₃' y y∈Q = PT.map (Sum.rec (λ s → inl (SglOf∅→EmptySgl y s))
                              (λ p → inr (PairOf∅→EmptyPair W y p)))
    (snd (snd h) y y∈Q)

-- =====================================================================
-- SECTION 4: THE READER AND ITS ADEQUACY.  tag0At s x reads "the set at
-- s is the pair pr ∅ (the set at x)".  With # 0 ≡ ∅ definitionally, this
-- is tagAt s 0 x with the constant removed.
-- =====================================================================
sgl0At : ∀ {n} → Fin n → Formula (V ℓ) n
sgl0At k = (∃̇∈ (var k) (∀̇∈ (var zero) ⊥̇))
        ∧̇ (∀̇∈ (var k) (∀̇∈ (var zero) ⊥̇))

pair0At : ∀ {n} → Fin n → Fin n → Formula (V ℓ) n
pair0At k j = (∃̇∈ (var k) (∀̇∈ (var zero) ⊥̇))
           ∧̇ ((var j ∈̇ var k)
           ∧̇ (∀̇∈ (var k) ((∀̇∈ (var zero) ⊥̇) ∨̇ (var zero ≐ var (suc j)))))

tag0At : ∀ {n} → Fin n → Fin n → Formula (V ℓ) n
tag0At s x = (∃̇∈ (var s) (sgl0At zero))
          ∧̇ ((∃̇∈ (var s) (pair0At zero (suc x)))
          ∧̇ (∀̇∈ (var s) (sgl0At zero ∨̇ pair0At zero (suc x))))

tag0At-adequate : ∀ {n} (s x : Fin n) (γ : (V ℓ) ^ n)
                → (γ ⊨ tag0At s x) ≡ ((⟦ var s ⟧ γ ≡ pr ∅ (⟦ var x ⟧ γ)) , setIsSet _ _)
tag0At-adequate s x γ = ⇔toPath
  (λ { (h₁ , h₂ , h₃) → prChar∅-fwd _ _ h₁ h₂ h₃ })
  (λ e → prChar∅-bwd _ _ e)
