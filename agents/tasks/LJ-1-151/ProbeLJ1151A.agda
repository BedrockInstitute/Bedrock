{-# OPTIONS --cubical --safe --guardedness #-}

-- [LJ-1.151] probe A: ONE member of the 25-fact satisfier-in-K family,
-- supplied at a CONCRETE K.
--
-- The member is `valK`, the brief's candidate
-- (src/L/Condensation/TwelveAgree.lagda.md:155-157).  The row's `back`
-- binds the graph membership `hc : pr c yc ∈ T` at the use site
-- (binClause-out, src/L/Coding/Model.lagda.md:904-917), so the honest
-- obligation carries that premise.  The frame's own statement omits it;
-- `check-unbound-hyp.py` flags exactly that, and probe B measures it.
--
-- The concrete K is the constructibility level `Lset α` as an element of
-- L (src/L/Constructible.lagda.md:222, src/L/Axioms/Basic.lagda.md:156).
-- Its transitivity is delivered: `layer-trans (Lset-layer α)`
-- (:183, :246).  Nothing about K stays a slot or a hypothesis.
--
-- THE FACT'S PRICE IS THE `Fact` MODULE PLUS `levelK` AND `AtLevel`.
-- The imports, the module header, this comment and the blank lines are
-- NOT the fact.  The report gives the file total separately.

open import Base.Prelude
open import Base.Truth

module LJ-1-151.ProbeLJ1151A {ℓ : Level} where

open import FOL.ZFStructure using ( module hPropStructure )
open import V.Hierarchy {ℓ} using ( 𝒮ᵥ )
open import V.Coding {ℓ} using ( pr )
open import L.Constructible {ℓ}
  using ( 𝒮ʟ; isL; isL-trans; IsOrd; isTransV; Lset; Lset-layer; layer-trans )
import FOL.Absoluteness
open import L.Axioms.Basic {ℓ} using ( isL-Lset )

open import Cubical.HITs.CumulativeHierarchy.Base using ( V; _∈_ )
open import Cubical.HITs.CumulativeHierarchy.Properties using ( ∈∈ₛ )
open import Cubical.HITs.CumulativeHierarchy.Constructions
  using ( ⁅_,_⁆; ⁅_⁆s; pairing-ax; module InfinitySet )
open InfinitySet using ( #_ )
import Cubical.HITs.PropositionalTruncation as PT
open PT using ( ∣_∣₁ )
import Cubical.Data.Sum as Sum
open Sum using ( inl; inr )

open TruthAlgebra (hPropAlgebra (ℓ-suc ℓ))
open hPropStructure 𝒮ʟ

module AbsL = FOL.Absoluteness.Single 𝒮ᵥ isL isL-trans
open AbsL using ( _^_ )

-- ===================================================================
-- THE ONE FACT.  Every non-blank, non-comment line below is counted.
-- ===================================================================

module Fact (K : S) (Ktr : isTransV (fst K)) where

  -- A transitive set absorbs both components of a Kuratowski pair it
  -- contains.  Generic: the only premise is transitivity, so a J level
  -- instantiates the same lemma unchanged (DD4).
  prK : (x y : V ℓ) → ⟨ pr x y ∈ fst K ⟩ → ⟨ x ∈ fst K ⟩ × ⟨ y ∈ fst K ⟩
  prK x y h = Ktr (mem x (inl refl)) two , Ktr (mem y (inr refl)) two
    where
    two : ⟨ ⁅ x , y ⁆ ∈ fst K ⟩
    two = Ktr (∈∈ₛ {a = ⁅ x , y ⁆} {b = pr x y} .snd
                (pairing-ax ⁅ x ⁆s ⁅ x , y ⁆ ⁅ x , y ⁆ .snd ∣ inr refl ∣₁)) h
    mem : (z : V ℓ) → (z ≡ x) Sum.⊎ (z ≡ y) → ⟨ z ∈ ⁅ x , y ⁆ ⟩
    mem z e = ∈∈ₛ {a = z} {b = ⁅ x , y ⁆} .snd (pairing-ax x y z .snd ∣ e ∣₁)

  -- The obligation, written at the frame's own type
  -- (TwelveAgree.lagda.md:155-157) with three changes and no others: the
  -- K slot is the concrete set, the C slot is the clause set it denotes,
  -- and the graph membership the row binds is a premise.
  -- `TK` is the site fact the stage holds for the graph slot.
  valK : (C T : S) → ⟨ fst T ∈ fst K ⟩
       → (k : ℕ) (c ar a b yc : S)
       → ⟨ fst c ∈ fst C ⟩
       → fst c ≡ pr (fst ar) (pr (# k) (pr (fst a) (fst b)))
       → ⟨ pr (fst c) (fst yc) ∈ fst T ⟩
       → ⟨ fst yc ∈ fst K ⟩
  valK C T TK k c ar a b yc c∈ shape hc =
    prK (fst c) (fst yc) (Ktr hc TK) .snd

-- The level as an element of L, so K is a value and not a slot.
levelK : (α : V ℓ) → IsOrd α → S
levelK α o = Lset α , isL-Lset α o

-- The concrete instance.  Nothing is left abstract but the ordinal.
module AtLevel (α : V ℓ) (o : IsOrd α) =
  Fact (levelK α o) (layer-trans (Lset-layer α))

-- ===================================================================
-- THE SLOT MATCH.  The frame writes its facts at slots of an
-- environment, so this block re-states `valK` in the frame's own
-- notation and discharges it from the block above.  It exists so the
-- match is machine-checked and not read off the source.
-- ===================================================================

module Slots {n : ℕ} (γ' : S ^ n) (Cs T K : Fin n)
  (α : V ℓ) (o : IsOrd α)
  (Kis : lookup K γ' ≡ levelK α o)
  (TK : ⟨ fst (lookup T γ') ∈ fst (lookup K γ') ⟩) where

  frame-valK : (k : ℕ) (c ar a b yc : S)
             → ⟨ fst c ∈ fst (lookup Cs γ') ⟩
             → fst c ≡ pr (fst ar) (pr (# k) (pr (fst a) (fst b)))
             → ⟨ pr (fst c) (fst yc) ∈ fst (lookup T γ') ⟩
             → ⟨ fst yc ∈ fst (lookup K γ') ⟩
  frame-valK k c ar a b yc c∈ shape hc =
    subst (λ z → ⟨ fst yc ∈ fst z ⟩) (sym Kis)
      (AtLevel.valK α o (lookup Cs γ') (lookup T γ')
        (subst (λ z → ⟨ fst (lookup T γ') ∈ fst z ⟩) Kis TK)
        k c ar a b yc c∈ shape hc)
