{-# OPTIONS --cubical --safe --guardedness #-}

-- [LJ-1.509] The subK family: what `T` is, and whether one argument
-- pays six positions.
--
-- W3 FIRST, and alone: WHAT `subValAt-adequate` PINS, WITH `T` NAMED.
-- The obligation is added only after W3 lands.
--
-- ONE Agda process per run, GHCRTS="-A64m -I0 -M8g", the wide caliber,
-- set on the pane by the program and untouched here.  Nothing lands in
-- src/.

open import Base.Prelude
open import Base.Truth
open import Base.Classical using ( LEM )

module LJ-1-509.Probe509 {ℓ : Level} (lem : LEM (ℓ-suc ℓ)) where

open import FOL.ZFStructure using ( module hPropStructure )
import FOL.Absoluteness
open import V.Hierarchy {ℓ} using ( 𝒮ᵥ )
open import V.Coding {ℓ} using ( pr )
open import L.Constructible {ℓ} using ( 𝒮ʟ; isL; isL-trans; isTransV; IsOrd; Lset )
open import L.Axioms.Basic {ℓ} using ( ∅ʟ; LsetS )
open import L.Axioms.Numerals {ℓ} using ( sucʟ; sucʟ-fst )
open import L.Coding.Model {ℓ} using ( prʟ; prʟ-fst )
open import V.Hierarchy {ℓ} using ( ∈-irrefl )
open import V.Model {ℓ} using ( self∈sucV )
import Cubical.Data.Empty as Empty
open import L.Coding.Model {ℓ} using ( subValAt; subValAt-adequate )
open import L.Coding.EnvSupply {ℓ} lem using ( module Fact )
open import L.Condensation {ℓ} lem using ( module KValue; module KFactsNS )
open import L.Condensation.TwelveAgree {ℓ} lem using ( TFacts )
open import Cubical.Data.Nat using ( _+_ )
open import Cubical.HITs.CumulativeHierarchy.Base using ( V; _∈_ )
open import Cubical.HITs.CumulativeHierarchy.Constructions
  using ( module InfinitySet; ∅ )
open InfinitySet {ℓ} using ( sucV )

open TruthAlgebra (hPropAlgebra (ℓ-suc ℓ))
open hPropStructure 𝒮ʟ

module AbsL = FOL.Absoluteness.Single 𝒮ᵥ isL isL-trans
open AbsL renaming ( _⊨ᵐ_ to _⊨_ )
open KFactsNS
open KFacts

-- =====================================================================
-- W3.  `T` IS A NAMED SLOT OF THE FRAME, NOT A BOUND VARIABLE.
--
-- `TFacts.subK₁-and` (src/L/Condensation/TwelveAgree.lagda.md:265-270)
-- states its hypothesis over the environment
--   (x ∷ y ∷ yc ∷ b ∷ a ∷ ar ∷ c ∷ γ')
-- at the four indices 8, 5, 4, 1.  Seven cells sit in front of `γ'`, so
-- index 8 is `lookup (suc zero) γ'`: THE SECOND CELL OF `γ'`, which is
-- the same cell `TFacts.valK` reads as its value set
-- (src/L/Condensation/TwelveAgree.lagda.md:175).
--
-- `subValAt-adequate` (src/L/Coding/Model.lagda.md:821-824) pins the
-- Kuratowski pair `pr (pr ar a) y` INTO that cell.  The equation below
-- is that instance with the right-hand side WRITTEN OUT, so Agda, and
-- not this comment, is what says `T` is `lookup (suc zero) γ'`.
-- =====================================================================

what-T-is : {n : ℕ} (γ' : S ^ (11 + n)) (x y yc b a ar c : S)
  → ((x ∷ y ∷ yc ∷ b ∷ a ∷ ar ∷ c ∷ γ') ⊨
       subValAt {7 + (11 + n)}
         (suc (suc (suc (suc (suc (suc (suc (suc zero))))))))
         (suc (suc (suc (suc (suc zero)))))
         (suc (suc (suc (suc zero))))
         (suc zero))
   ≡ (pr (pr (fst ar) (fst a)) (fst y) ∈ fst (lookup (suc zero) γ'))
what-T-is γ' x y yc b a ar c =
  subValAt-adequate
    (suc (suc (suc (suc (suc (suc (suc (suc zero))))))))
    (suc (suc (suc (suc (suc zero)))))
    (suc (suc (suc (suc zero))))
    (suc zero)
    (x ∷ y ∷ yc ∷ b ∷ a ∷ ar ∷ c ∷ γ')

-- =====================================================================
-- THE STATEMENT, WRITTEN ONCE AT THE GENERIC FRAME (W2).
--
-- `TFacts.subK₁-and`'s type verbatim
-- (src/L/Condensation/TwelveAgree.lagda.md:265-270), at `TFacts`'s own
-- generic shape: `K : Fin (5 + n)` over `γ' : S ^ (11 + n)`
-- (:130-131).  It is instantiated ONCE below, at `KValue`'s frame.
-- =====================================================================

SubKAnd : {n : ℕ} (K : Fin (5 + n)) (γ' : S ^ (11 + n)) → Type (ℓ-suc ℓ)
SubKAnd {n} K γ' =
    (x y yc b a ar c : S)
  → ⟨ (x ∷ y ∷ yc ∷ b ∷ a ∷ ar ∷ c ∷ γ') ⊨
        subValAt {7 + (11 + n)}
          (suc (suc (suc (suc (suc (suc (suc (suc zero))))))))
          (suc (suc (suc (suc (suc zero)))))
          (suc (suc (suc (suc zero))))
          (suc zero) ⟩
  → ⟨ fst y ∈ fst (lookup (suc (suc (suc (suc (suc (suc K)))))) γ') ⟩

-- `SubKAnd` IS THE FIELD'S TYPE, AND AGDA SAYS SO.  The term below is the
-- record's own `subK₁-and` read at `SubKAnd`, with no coercion, no
-- `subst` and no re-association.  It certifies the STATEMENT only; the
-- obligation below never calls it, and no `TFacts` field is used to
-- prove a `TFacts` field.

statement-matches : {n : ℕ}
    (N0 N1 N2 N3 N4 N5 N6 N7 N8 N9 N10 N11 t0 t1 K : Fin (5 + n))
    (γ' : S ^ (11 + n))
  → TFacts N0 N1 N2 N3 N4 N5 N6 N7 N8 N9 N10 N11 t0 t1 K γ'
  → SubKAnd {n} K γ'
statement-matches N0 N1 N2 N3 N4 N5 N6 N7 N8 N9 N10 N11 t0 t1 K γ' tf =
  TFacts.subK₁-and tf

-- =====================================================================
-- THE TWO INPUTS, AND NOTHING ELSE.
--
-- `[LJ-1.113]` row 18 (agents/tasks/LJ-1-113/lj-1.113-report.md:48) said
-- the family needs `T ∈ K` and that `arityK` closes it.  Both are
-- hypotheses of this module and neither pins a slot:
--
--   `arity` is `KFacts.arityK`'s SHAPE, over `S`, not `isTransV`'s
--   shape over the raw `V ℓ` (src/L/Condensation.lagda.md:6114-6115).
--   It is the weaker of the two, and `isL-trans`
--   (src/L/Constructible.lagda.md:379) is what closes the gap: every
--   set that this argument meets sits inside `fst Kset`, and `isL` is
--   inherited downwards, so each raw member packages back into `S`.
--
--   `TK` is the membership itself.  NO `TFacts` FIELD STATES IT: the
--   cell `lookup (suc zero) γ'` occurs in exactly two field types,
--   `valK` (src/L/Condensation/TwelveAgree.lagda.md:175) and `valK-un`
--   (:179), and in both it is the CONTAINER, never a member of `K`.
--
-- The derivation itself is NOT written here.  `Fact.subK-gen`
-- (src/L/Coding/EnvSupply.lagda.md:481-487) already carries it,
-- tower-neutral over `(K, Ktr)` and generic in the environment, so this
-- module supplies the two inputs and spends the delivered term.
-- =====================================================================

module SubK {n : ℕ} (K : Fin (5 + n)) (γ' : S ^ (11 + n))
  (arity : (N v : S) → ⟨ fst v ∈ fst N ⟩
         → ⟨ fst N ∈ fst (lookup (suc (suc (suc (suc (suc (suc K)))))) γ') ⟩
         → ⟨ fst v ∈ fst (lookup (suc (suc (suc (suc (suc (suc K)))))) γ') ⟩)
  (TK : ⟨ fst (lookup (suc zero) γ')
          ∈ fst (lookup (suc (suc (suc (suc (suc (suc K)))))) γ') ⟩)
  where

  Kset : S
  Kset = lookup (suc (suc (suc (suc (suc (suc K)))))) γ'

  -- `arityK` over `S` GIVES transitivity over the raw carrier.  The two
  -- packagings are the only content: a member of `fst Kset` is `isL`
  -- because `Kset` is, and a member of that member is `isL` again.
  Ktr : isTransV (fst Kset)
  Ktr {A} {u} u∈A A∈K = arity (A , isLA) (u , isL-trans u∈A isLA) u∈A A∈K
    where
    isLA : ⟨ isL A ⟩
    isLA = isL-trans A∈K (snd Kset)

  module F = Fact Kset Ktr

  subK-and : SubKAnd {n} K γ'
  subK-and x y yc b a ar c h =
    F.subK-gen (x ∷ y ∷ yc ∷ b ∷ a ∷ ar ∷ c ∷ γ')
      (suc (suc (suc (suc (suc (suc (suc (suc zero))))))))
      (suc (suc (suc (suc (suc zero)))))
      (suc (suc (suc (suc zero))))
      (suc zero)
      TK h

-- =====================================================================
-- THE OBLIGATION, AT `KValue`'s FRAME.
--
-- `KValue` (src/L/Condensation.lagda.md:7380-7395) binds the carrier and
-- the stage and supplies ONE `KFacts` value, `facts` (:7411), over
-- `Kenv : S ^ 14`.  Six cons cells put it at `TFacts`'s lengths, which
-- is the frame `[LJ-1.495]` measured
-- (agents/tasks/LJ-1-495/lj-1.495-report.md:56-60): `S ^ 20` is
-- `S ^ (11 + 9)` and `Fin 14` is `Fin (5 + 9)`.
--
-- `arityK` NEEDS NO `KFactsCons` HERE.  `lookup (suc i) (c ∷ γ)` is
-- `lookup i γ` by definition, and both the index and the environment are
-- literal chains, so the six-fold shift of THIS field is definitional
-- and `facts .arityK` has the shifted type already.
--
-- `TK` STAYS A HYPOTHESIS, and it must: `γ'` position 1 at this frame is
-- `c5`, one of the six cells the shift conses on, which `KValue` does
-- not determine.  Nothing here fixes what occupies that slot.
-- =====================================================================

module Frame
  (lam : V ℓ) (ordλ : IsOrd lam)
  (succλ : (d : V ℓ) → ⟨ d ∈ lam ⟩ → ⟨ sucV d ∈ lam ⟩)
  (∅∈λ : ⟨ ∅ ∈ lam ⟩)
  (gam : V ℓ) (ordγ : IsOrd gam) (γ∈λ : ⟨ gam ∈ lam ⟩) where

  open KValue lam ordλ succλ ∅∈λ gam ordγ γ∈λ

  subK-and-at-KValue :
      (c1 c2 c3 c4 c5 c6 : S)
    → ⟨ fst (lookup (suc zero) (c6 ∷ c5 ∷ c4 ∷ c3 ∷ c2 ∷ c1 ∷ Kenv))
         ∈ fst (lookup (suc (suc (suc (suc (suc (suc iK))))))
                 (c6 ∷ c5 ∷ c4 ∷ c3 ∷ c2 ∷ c1 ∷ Kenv)) ⟩
    → SubKAnd {9} iK (c6 ∷ c5 ∷ c4 ∷ c3 ∷ c2 ∷ c1 ∷ Kenv)
  subK-and-at-KValue c1 c2 c3 c4 c5 c6 TK =
    SubK.subK-and {9} iK (c6 ∷ c5 ∷ c4 ∷ c3 ∷ c2 ∷ c1 ∷ Kenv)
      (facts .arityK) TK

-- =====================================================================
-- AND `TK` CANNOT BE DROPPED.  THE FRAME DOES NOT DECIDE IT.
--
-- `[LJ-1.113]` row 18 said the family NEEDS `T ∈ K`
-- (agents/tasks/LJ-1-113/lj-1.113-report.md:48).  The term below turns
-- that from a note into a measurement, AT THIS FRAME and not at a
-- generic one (C-42 measures the site it names).
--
-- `γ'` position 1 is `c5`, so a counterexample only has to put ONE
-- Kuratowski pair into `c5` whose right component escapes `Lset lam`.
-- `Lset lam` itself escapes it, by `∈-irrefl`
-- (src/V/Hierarchy.lagda.md:155).  The pair goes into the successor of
-- itself (`self∈sucV`, src/V/Model.lagda.md:236), which is the same
-- one-line witness `[LJ-1.506]` used
-- (agents/tasks/LJ-1-506/Probe506.agda:128-130).
--
-- SO THE WEAKEST REPAIRING HYPOTHESIS IS `TK` ITSELF, and it is the one
-- the obligation takes.  No slot is pinned by it.
-- =====================================================================

module Refute
  (lam : V ℓ) (ordλ : IsOrd lam)
  (succλ : (d : V ℓ) → ⟨ d ∈ lam ⟩ → ⟨ sucV d ∈ lam ⟩)
  (∅∈λ : ⟨ ∅ ∈ lam ⟩)
  (gam : V ℓ) (ordγ : IsOrd gam) (γ∈λ : ⟨ gam ∈ lam ⟩) where

  open KValue lam ordλ succλ ∅∈λ gam ordγ γ∈λ

  Lλ : S
  Lλ = LsetS lam ordλ

  badPair : S
  badPair = prʟ (prʟ ∅ʟ ∅ʟ) Lλ

  badSet : S
  badSet = sucʟ badPair

  bad∈ : ⟨ fst badPair ∈ fst badSet ⟩
  bad∈ = subst (λ u → ⟨ fst badPair ∈ u ⟩) (sym (sucʟ-fst badPair))
           (self∈sucV (fst badPair))

  bad-shape : fst badPair ≡ pr (pr (fst ∅ʟ) (fst ∅ʟ)) (fst Lλ)
  bad-shape = prʟ-fst (prʟ ∅ʟ ∅ʟ) Lλ
            ∙ cong (λ w → pr w (fst Lλ)) (prʟ-fst ∅ʟ ∅ʟ)

  no-TK-is-not-a-theorem :
      ( (c1 c2 c3 c4 c5 c6 : S)
      → SubKAnd {9} iK (c6 ∷ c5 ∷ c4 ∷ c3 ∷ c2 ∷ c1 ∷ Kenv) )
    → Empty.⊥
  no-TK-is-not-a-theorem h = ∈-irrefl (Lset lam)
    (h ∅ʟ ∅ʟ ∅ʟ ∅ʟ badSet ∅ʟ
       ∅ʟ Lλ ∅ʟ ∅ʟ ∅ʟ ∅ʟ ∅ʟ
       (subst ⟨_⟩
         (sym (what-T-is {9}
                 (∅ʟ ∷ badSet ∷ ∅ʟ ∷ ∅ʟ ∷ ∅ʟ ∷ ∅ʟ ∷ Kenv)
                 ∅ʟ Lλ ∅ʟ ∅ʟ ∅ʟ ∅ʟ ∅ʟ))
         (subst (λ w → ⟨ w ∈ fst badSet ⟩) bad-shape bad∈)))

subK-and = Frame.subK-and-at-KValue
no-TK-is-not-a-theorem = Refute.no-TK-is-not-a-theorem
