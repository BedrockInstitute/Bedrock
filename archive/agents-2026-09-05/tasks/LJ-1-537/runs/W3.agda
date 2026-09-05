{-# OPTIONS --cubical --safe --guardedness #-}

-- [LJ-1.537]  W3, THE WIDEST UNMEASURED TERM, WRITTEN FIRST AND ALONE.
--
-- The brief names it: "the Formula that carves the graph of `swo-rank′`
-- over preds", and orders the stop if the rank's recursion cannot be
-- said in the object language at this arity.
--
-- IT CAN, AND THE RECURSION IS NEVER SAID.  D-10 answered first: at an
-- ORDINAL site the rank IS the member.  `swo-rank′ w k` is
-- `⋃ { sucV (swo-rank′ w j) : j ≺ k }` (Probe521.agda:237-244 with
-- bnd-out/bnd-in at :290-313), and at `w = OrdSWO∈ₛ.w α oα` the order
-- `≺` is ∈, so the recursion is `x ↦ ⋃ { sucV y : y ∈ x }`, which is
-- the identity on every transitive set.  The graph of the rank over the
-- ∈-predecessors of `m` is therefore the IDENTITY graph on `m`, and the
-- formula that carves it names no rank and no recursion:
--
--   Cond = ∃̇ ( prAtL (suc zero) zero zero ∧̇ (var zero ∈̇ con m) )
--
-- "z is the pair of some x with itself, and that x is a member of m."
-- One existential, two conjuncts, and `con m` is the only constant.
--
-- THE GENERATOR IS `hasSeparationL` (src/L/Axioms/Full.lagda.md:144-146)
-- out of a `smallDom` bound (src/L/Recursion.lagda.md:133), which is
-- [LJ-1.521]'s `Witness` pattern (Probe521.agda:1046-1059) at one
-- component instead of two.
--
-- This file carries the formula and the carve, with the three
-- satisfaction properties OMITTED, exactly as the brief ordered.  The
-- identity lemma itself is NOT here: it is not the formula.  Nothing
-- lands in src/.  Does not postulate.

open import Base.Prelude
open import Base.Truth
open import Base.Classical using ( LEM )

module LJ-1-537.runs.W3 {ℓ : Level} (lem : LEM (ℓ-suc ℓ)) where

open import FOL.ZFStructure using ( module hPropStructure )
open import FOL.Syntax using ( Formula; var; con; _∈̇_; _∧̇_; ∃̇_ )
import FOL.Absoluteness
open import V.Hierarchy {ℓ} using ( 𝒮ᵥ )
open import V.Coding {ℓ} using ( pr; pr-inj )
open import V.Presentation {ℓ} using ( member; fiber )
open import L.Constructible {ℓ} using ( 𝒮ʟ; isL; isL-trans )
open import L.Recursion {ℓ} lem using ( smallDom )
open import L.Axioms.Full {ℓ} lem using ( hasSeparationL )
open import L.Coding.Model {ℓ}
  using ( prAtL; prAtL-adequate; prʟ; prʟ-fst )
open import Cubical.Data.FinData using ( Fin; zero; suc )
open import Cubical.Foundations.HLevels using ( isProp× )
open import Cubical.HITs.CumulativeHierarchy.Base
  using ( V; _∈_; setIsSet )
open import Cubical.HITs.CumulativeHierarchy.Properties
  using ( ⟪_⟫; ⟪_⟫↪; ∈∈ₛ )
import Cubical.HITs.PropositionalTruncation as PT

open TruthAlgebra (hPropAlgebra (ℓ-suc ℓ))
open hPropStructure 𝒮ʟ using ( S; _∈ˢ_ )

module AbsL = FOL.Absoluteness.Single 𝒮ᵥ isL isL-trans
open AbsL renaming ( _⊨ᵐ_ to _⊨_ )

-- =====================================================================
-- THE CARVE.  One parameter: the member whose ∈-predecessors carry the
-- graph.
-- =====================================================================

module Carve (m : S) where

  μ : V ℓ
  μ = fst m

  -- A member of `m` is an element of the model.  [LJ-1.521]'s
  -- `Site.memS` (Probe521.agda:129-130) at `m` instead of at `a`.
  memS : ⟪ μ ⟫ → S
  memS k = ⟪ μ ⟫↪ k , isL-trans {x = μ} {y = ⟪ μ ⟫↪ k} (member μ k) (snd m)

  ix : (x : S) → ⟨ fst x ∈ μ ⟩ → ⟪ μ ⟫
  ix x h = fiber μ h .fst

  ix-val : (x : S) (h : ⟨ fst x ∈ μ ⟩) → ⟪ μ ⟫↪ (ix x h) ≡ fst x
  ix-val x h = fiber μ h .snd

  -- THE BOUND.  `smallDom` over the carrier of `m`, at the diagonal
  -- pair.  [LJ-1.521]'s `Witness.bnd` (Probe521.agda:1046-1053) took the
  -- SQUARE of the carrier because its condition related two members;
  -- this one relates a member to itself, so the index is the carrier.
  bnd : Σ[ d ∈ S ] ((k : ⟪ μ ⟫) → ⟨ prʟ (memS k) (memS k) ∈ˢ d ⟩)
  bnd = smallDom ⟪ μ ⟫ (λ k → prʟ (memS k) (memS k))

  D : S
  D = bnd .fst

  inD : (x : S) (xm : ⟨ fst x ∈ μ ⟩) → ⟨ pr (fst x) (fst x) ∈ fst D ⟩
  inD x xm =
    subst (λ t → ⟨ t ∈ fst D ⟩)
      (prʟ-fst (memS (ix x xm)) (memS (ix x xm))
        ∙ cong₂ pr (ix-val x xm) (ix-val x xm))
      (bnd .snd (ix x xm))

  -- THE FORMULA.  Variable 0 of `Body` is the carved member, variable 1
  -- is the candidate pair.
  Body : Formula S 2
  Body = prAtL (suc zero) zero zero ∧̇ (var zero ∈̇ con m)

  Cond : Formula S 1
  Cond = ∃̇ Body

  opaque
    G : S
    G = hasSeparationL D Cond .fst .fst

    G-mem : (z : S) → (z ∈ˢ G) ≡ ((z ∈ˢ D) ⊓ ((z ∷ []) ⊨ Cond))
    G-mem = hasSeparationL D Cond .fst .snd

  -- THE TWO DIRECTIONS.  `graph-in` puts the diagonal pair of every
  -- member of `m` into `G`; `graph-out` says `G` holds nothing else.
  graph-in : (x : S) → ⟨ fst x ∈ μ ⟩ → ⟨ pr (fst x) (fst x) ∈ fst G ⟩
  graph-in x xm =
    subst (λ t → ⟨ t ∈ fst G ⟩) qz
      (subst ⟨_⟩ (sym (G-mem (prʟ x x)))
        ( subst (λ t → ⟨ t ∈ fst D ⟩) (sym qz) (inD x xm)
        , PT.∣ x , (hpr , xm) ∣₁ ))
    where
    qz : fst (prʟ x x) ≡ pr (fst x) (fst x)
    qz = prʟ-fst x x

    hpr : ⟨ (x ∷ prʟ x x ∷ []) ⊨ prAtL (suc zero) zero zero ⟩
    hpr = subst ⟨_⟩
      (sym (prAtL-adequate (suc zero) zero zero (x ∷ prʟ x x ∷ []))) qz

  graph-out : (x v : S) → ⟨ pr (fst x) (fst v) ∈ fst G ⟩
            → ⟨ fst x ∈ μ ⟩ × (fst v ≡ fst x)
  graph-out x v h = PT.rec isPropTgt at cnd
    where
    isPropTgt : isProp (⟨ fst x ∈ μ ⟩ × (fst v ≡ fst x))
    isPropTgt = isProp× (snd (fst x ∈ μ)) (setIsSet (fst v) (fst x))

    qz : fst (prʟ x v) ≡ pr (fst x) (fst v)
    qz = prʟ-fst x v

    cnd : ⟨ (prʟ x v ∷ []) ⊨ Cond ⟩
    cnd = subst ⟨_⟩ (G-mem (prʟ x v))
            (subst (λ t → ⟨ t ∈ fst G ⟩) (sym qz) h) .snd

    at : Σ[ c ∈ S ] ⟨ (c ∷ prʟ x v ∷ []) ⊨ Body ⟩
       → ⟨ fst x ∈ μ ⟩ × (fst v ≡ fst x)
    at (c , (hpr , cm)) =
      subst (λ t → ⟨ t ∈ μ ⟩) (sym (split .fst)) cm
      , (split .snd ∙ sym (split .fst))
      where
      qcv : pr (fst x) (fst v) ≡ pr (fst c) (fst c)
      qcv = sym qz
          ∙ subst ⟨_⟩
              (prAtL-adequate (suc zero) zero zero (c ∷ prʟ x v ∷ [])) hpr

      split : (fst x ≡ fst c) × (fst v ≡ fst c)
      split = pr-inj qcv
