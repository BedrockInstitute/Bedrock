{-# OPTIONS --cubical --safe --guardedness #-}

-- [LJ-1.492] PROBE.  CoverWitnessesInHull from H.T.closed, not wit.
-- It runs in agents/tasks/LJ-1-492/ and lands nothing in src/.
--
--   STEP ONE, W3 FIRST  coverFo.  Obligation omitted.
--                       Formula Code 1: ordinal predicate conjoined
--                       with level membership, y as a Code constant.
--
-- ONE Agda process per run, GHCRTS="-A64m -I0 -M8g", the wide caliber,
-- set on the pane by the program and untouched here.

open import Base.Prelude
open import Base.Truth
open import Base.Classical using ( LEM )

module LJ-1-492.Probe492 {ℓ : Level} (lem : LEM (ℓ-suc ℓ)) where

open import FOL.ZFStructure using ( module hPropStructure )
open import FOL.Syntax using ( Formula; var; con; _∈̇_; _≐_; _∧̇_; _∨̇_; ⊥̇; ∀̇∈; ∃̇∈; ∃̇_ )
open import FOL.Manipulation.Relabelling using ( mapFo )
open import V.Hierarchy {ℓ} using ( 𝒮ᵥ )
open import L.Constructible {ℓ} using ( IsOrd; isTransV; Lset; Lset-out; Lset-mono; 𝒟ₒ; 𝒮ʟ )
open import L.Axioms.Basic {ℓ} using ( Lset-suc )
open import L.Ordinal {ℓ} using ( suc-ord; mem-ord )
open import L.Ordinal.Stages {ℓ} lem using ( ord∈Lset-suc )
open import L.Hull {ℓ} lem using ( module AtStage )
open import L.Axioms.Numerals {ℓ} using ( numeralL )
open import L.Coding.Sequence {ℓ} lem using ( LsetGraphAt )

open import Cubical.Data.Nat using ( ℕ )
open import Cubical.Data.Sigma using ( Σ-syntax )
open import Cubical.Data.Sum using ( _⊎_; inl; inr )
import Cubical.HITs.PropositionalTruncation as PT
open PT using ( ∥_∥₁ ; map )
open import Cubical.HITs.CumulativeHierarchy.Constructions
  using ( ∅; module InfinitySet )
open InfinitySet using ( sucV )

open TruthAlgebra (hPropAlgebra (ℓ-suc ℓ))
open hPropStructure 𝒮ᵥ
module CS = hPropStructure 𝒮ʟ

-- W2: the ordinal formula once, generic in the constant domain.
-- Same spelling as isOrdAt at src/L/BoundedSubset.lagda.md:795-798
-- and as isOrdFo at agents/tasks/LJ-1-487/Probe487.agda:52-55.

isOrdFo : ∀ {ℓk} {K : Type ℓk} {n} (v : Fin n) → Formula K n
isOrdFo v =
    (∀̇∈ (var v) (∀̇∈ (var zero) (var zero ∈̇ var (suc (suc v)))))
  ∧̇ (∀̇∈ (var v) (∀̇∈ (var zero) (∀̇∈ (var zero) (var zero ∈̇ var (suc (suc zero))))))

-- W2: covering formula generic in K. y is a constant. The level
-- graph is LsetGraphAt at src/L/Coding/Sequence.lagda.md:349, sent
-- to K by mapFo at src/FOL/Manipulation/Relabelling.lagda.md:54-56.

coverFoGen : ∀ {ℓk} {K : Type ℓk} (yc : K) (emb : CS.S → K) → Formula K 1
coverFoGen yc emb =
    isOrdFo {K = _} {n = 1} zero
  ∧̇ ∃̇ ( mapFo emb (LsetGraphAt {n = 2} zero (suc zero))
      ∧̇ (con yc ∈̇ var zero) )

-- Decoder. Rebuilt from [LJ-1.474], Probe474.agda:69-83, not imported.
-- [LJ-1.466] census: every visible con of LsetGraph is numeralL k
-- for k ∈ {0,1,...,11}.

tagBound : ℕ
tagBound = 12

tagFrom : ℕ → ℕ → CS.S → ℕ
tagFrom k zero s = 0
tagFrom k (suc r) s with lem ((s ≡ numeralL k) , CS.isSetS s (numeralL k))
... | inl _ = k
... | inr _ = tagFrom (suc k) r s

tagOf : CS.S → ℕ
tagOf s = tagFrom 0 tagBound s

-- Numeral formulas, generic in K. Same spelling as Probe474.agda:50-60.

succFo : ∀ {ℓk} {K : Type ℓk} {n} (x y : Fin n) → Formula K n
succFo x y =
    (∀̇∈ (var y) ((var zero ∈̇ var (suc x)) ∨̇ (var zero ≐ var (suc x))))
  ∧̇ (∀̇∈ (var x) (var zero ∈̇ var (suc y)))
  ∧̇ (var x ∈̇ var y)

numeralFo : (n : ℕ) → ∀ {ℓk} {K : Type ℓk} {n'} (v : Fin (suc n'))
          → Formula K (suc n')
numeralFo zero v = ∀̇∈ (var v) ⊥̇
numeralFo (suc n) {ℓk} {K} {n'} v =
  ∃̇∈ (var v) (succFo zero (suc v) ∧̇ numeralFo n {K = K} {n' = suc n'} zero)

-- Telescope copied from src/L/BoundedSubset.lagda.md:903-914.
-- Nothing below module Condense is copied. levelIn is not a hypothesis.
-- cover is not a hypothesis.

module HullStage (lam : S) (ordλ : IsOrd lam)
  (succλ : (d : S) → ⟨ d ∈ˢ lam ⟩ → ⟨ sucV d ∈ˢ lam ⟩)
  (X : S) (X⊆L : (x : S) → ⟨ x ∈ˢ X ⟩ → ⟨ x ∈ˢ Lset lam ⟩)
  (∅∈λ : ⟨ ∅ ∈ˢ lam ⟩) where

  module ASt = AtStage lam ordλ

  module H = ASt.Hull X X⊆L ∅∈λ

  M : S
  M = H.T.Hull

  open H.T using ( Code; val; wit; closed; _⊨c_ )

  -- =====================================================================
  -- W3.  coverFo.
  -- =====================================================================

  φk : (k : ℕ) → Formula (⊥* {ℓ}) 1
  φk k = numeralFo k {n' = 0} zero

  ck : (k : ℕ) → Code
  ck k = wit 0 (φk k) []

  lset-emb : CS.S → Code
  lset-emb s = ck (tagOf s)

  coverFo : (yc : Code) → Formula Code 1
  coverFo yc = coverFoGen yc lset-emb

  -- =====================================================================
  -- STEP TWO.  Open closed. Rebuild ambient-level. Convert or stop.
  -- Do not use wit. Do not import a probe.
  -- =====================================================================

  code-of : (y : S) → ⟨ y ∈ˢ M ⟩ → ∥ Σ[ c ∈ Code ] (fst (val c) ≡ y) ∥₁
  code-of = H.hull-member

  -- Quote: agents/tasks/LJ-1-484/Probe484.agda:80-98. Rebuilt, not imported.

  ambient-cover : (y : S) → ⟨ y ∈ˢ M ⟩
                → ∥ Σ[ δ ∈ S ] (⟨ δ ∈ˢ lam ⟩ × ⟨ y ∈ˢ 𝒟ₒ (Lset δ) ⟩) ∥₁
  ambient-cover y y∈M = Lset-out lam y (H.Hull⊆L y y∈M)

  ambient-level : (y : S) → ⟨ y ∈ˢ M ⟩
                → ∥ Σ[ γ ∈ S ] (IsOrd γ × ⟨ γ ∈ˢ lam ⟩ × ⟨ y ∈ˢ Lset γ ⟩) ∥₁
  ambient-level y y∈M = PT.map go (ambient-cover y y∈M)
    where
    go : Σ[ δ ∈ S ] (⟨ δ ∈ˢ lam ⟩ × ⟨ y ∈ˢ 𝒟ₒ (Lset δ) ⟩)
       → Σ[ γ ∈ S ] (IsOrd γ × ⟨ γ ∈ˢ lam ⟩ × ⟨ y ∈ˢ Lset γ ⟩)
    go (δ , δ∈λ , y∈𝒟) =
      sucV δ
      , ( suc-ord (mem-ord {A = lam} ordλ δ δ∈λ)
        , succλ δ δ∈λ
        , subst (λ w → ⟨ y ∈ˢ w ⟩) (sym (Lset-suc δ)) y∈𝒟 )

  -- An ambient covering ordinal is a stage member. Not hull membership.
  -- Lset-mono at src/L/Constructible.lagda.md:355.
  -- ord∈Lset-suc at src/L/Ordinal/Stages.lagda.md:434.

  pack-index : (γ : S) → IsOrd γ → ⟨ γ ∈ˢ lam ⟩ → ⟨ γ ∈ˢ Lset lam ⟩
  pack-index γ oγ γ∈λ = Lset-mono (succλ γ γ∈λ) (ord∈Lset-suc γ oγ)

  -- isOrdFo at ⊨c, both directions. Δ₀. No constants. The graph is not this.

  isOrdFo-out : (a : ASt.SL)
              → ⟨ (a ∷ []) ⊨c (isOrdFo {K = Code} {n = 1} zero) ⟩
              → IsOrd (fst a)
  isOrdFo-out a (htr , hmem) = atr , amem
    where
    atr : isTransV (fst a)
    atr {x} {y} y∈x x∈a =
      htr (x , ASt.Ltr {x = fst a} {y = x} x∈a (a .snd)) x∈a
          (y , ASt.Ltr {x = x} {y = y} y∈x
                 (ASt.Ltr {x = fst a} {y = x} x∈a (a .snd))) y∈x
    amem : (x : S) → ⟨ x ∈ˢ fst a ⟩ → isTransV x
    amem x x∈a {y} {z} z∈y y∈x =
      hmem (x , ASt.Ltr {x = fst a} {y = x} x∈a (a .snd)) x∈a
           (y , ASt.Ltr {x = x} {y = y} y∈x
                  (ASt.Ltr {x = fst a} {y = x} x∈a (a .snd))) y∈x
           (z , ASt.Ltr {x = y} {y = z} z∈y
                  (ASt.Ltr {x = x} {y = y} y∈x
                     (ASt.Ltr {x = fst a} {y = x} x∈a (a .snd)))) z∈y

  isOrdFo-in : (a : ASt.SL) → IsOrd (fst a)
             → ⟨ (a ∷ []) ⊨c (isOrdFo {K = Code} {n = 1} zero) ⟩
  isOrdFo-in a (atr , amem) =
    (λ x hx y hy → atr {x = fst x} {y = fst y} hy hx)
    ,
    (λ x hx y hy z hz → amem (fst x) hx {x = fst y} {y = fst z} hz hy)

  -- closed, opened, at this formula. Site: src/L/Hull.lagda.md:120-122.
  -- toSet is fst. Hull is M.

  closed-at-cover :
      (yc : Code)
    → ∥ Σ[ a ∈ ASt.SL ] ⟨ (a ∷ []) ⊨c coverFo yc ⟩ ∥₁
    → ∥ Σ[ a ∈ ASt.SL ] (⟨ fst a ∈ˢ M ⟩ × ⟨ (a ∷ []) ⊨c coverFo yc ⟩) ∥₁
  closed-at-cover yc = closed (coverFo yc)

  -- The conversion closed needs and the tree does not deliver at this
  -- telescope. ambient-level is a meta-level covering. closed takes
  -- STAGE satisfaction of Formula Code 1. Lset-defines / Lset-only
  -- live at 𝒮ʟ (src/L/Hierarchy.lagda.md:646-648, :334-335). ⊨c lives
  -- at AbsL.𝒮M. The graph is an unbounded ∃̇
  -- (src/L/Coding/Sequence.lagda.md:292). Δ₀ transfer does not move it.
  -- Unbuilt. Not a hypothesis of CoverWitnessesInHull.

  StageSatOfCover : Type (ℓ-suc ℓ)
  StageSatOfCover =
      (yc : Code) (y : S) → fst (val yc) ≡ y
    → (γ : S) → IsOrd γ → ⟨ γ ∈ˢ lam ⟩ → ⟨ y ∈ˢ Lset γ ⟩
    → ∥ Σ[ a ∈ ASt.SL ] ⟨ (a ∷ []) ⊨c coverFo yc ⟩ ∥₁

  -- Step 4 of [LJ-1.484], the type that probe typechecked.
  -- Quote: agents/tasks/LJ-1-484/Probe484.agda:123-126.
  -- UNBUILT. closed is opened. The ambient witness of closed is not
  -- ambient-level. No term of this type. No postulate.

  CoverWitnessesInHull : Type (ℓ-suc ℓ)
  CoverWitnessesInHull =
      (y : S) → ⟨ y ∈ˢ M ⟩
    → ∥ Σ[ γ ∈ S ] (⟨ γ ∈ˢ M ⟩ × IsOrd γ × ⟨ y ∈ˢ Lset γ ⟩) ∥₁
