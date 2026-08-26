{-# OPTIONS --cubical --safe --guardedness #-}

-- [LJ-1.659]  Does [LJ-1.651]'s delivered formula give the level formula?
--
--   THE BRIEF'S OBLIGATION  lset-formula-to-level, with [LJ-1.651]'s
--   delivered `lset-formula` as a HYPOTHESIS and [LJ-1.650]'s
--   `LevelFormula` as the target.
--
--   IT IS NOT INHABITED, AND SECTION 2 PROVES WHY IN THE STRONGEST
--   FORM AVAILABLE: the hypothesis is DEGENERATE.  What [LJ-1.651]
--   delivered is a term of type `Formula Code 2`, a bare piece of
--   SYNTAX.  That type is inhabited in the tree with no work at all
--   (`⊤̇`), so hypothesising it names no fact, and the obligation is
--   logically EQUIVALENT to `LevelFormula` itself.  Both directions of
--   that equivalence are built below and both typecheck.  The stop is
--   review-of-lset-formula-to-level.md.
--
--   THE DELIVERABLE THE BRIEF ASKED FOR INSTEAD is section 3 and
--   section 4: the term naming what the two-variable form has that the
--   delivered form does not, and the arrow from it.  It is exactly two
--   SEMANTIC laws, soundness and completeness for `_⊨c_`; add them and
--   the target follows for the price of ONE renaming.
--
--   THE FRAME.  [LJ-1.650] measured that importing LJ-1-595.Probe595
--   WALLS the wide caliber on the frame alone (its report section 1),
--   because that probe chains through 544/550/558/564/570/578.
--   Probe651 imports NO probe: only src/.  So this file takes the
--   predecessor's type BY IMPORT, which is the honest way, and the
--   floor measured the cost first: runs/Floor659.agda, runs/floor-1.out,
--   exit 0 in 5.82 s at 857,849,856 bytes.
--
--   Nothing is postulated.  No hole.  Nothing lands in src/.
--   ONE Agda process, caliber from the pane, never set here.

open import Base.Prelude
open import Base.Truth
open import Base.Classical using ( LEM )

module LJ-1-659.Probe659 {ℓ : Level} (lem : LEM (ℓ-suc ℓ)) where

open import FOL.ZFStructure using ( module hPropStructure )
open import FOL.Syntax using ( Formula; var; con; _∈̇_; _≐_; _∧̇_; ⊤̇; ∃̇_ )
open import FOL.Manipulation.Renaming using ( renameFo; module Sat )
open import FOL.LevyHierarchy using ( Δ₀; Σ₁; σ-Δ₀; σ-∃; δ-∧ )
open import FOL.Manipulation.Relabelling using ( mapFo )
open import V.Hierarchy {ℓ} using ( 𝒮ᵥ )
open import L.Constructible {ℓ} using ( IsOrd; Lset )
open import L.BoundedSubset {ℓ} lem using ( module HullStage )
open import Cubical.HITs.CumulativeHierarchy.Constructions
  using ( ∅; module InfinitySet )
open import Cubical.Data.Sigma using ( _×_ )
open import Cubical.Data.Vec using ( Vec; _∷_; [] )
import Cubical.Data.Empty as Empty
import Cubical.HITs.PropositionalTruncation as PT
open PT using ( ∥_∥₁; ∣_∣₁ )
open InfinitySet {ℓ} using ( sucV )

import LJ-1-651.Probe651
module P651 = LJ-1-651.Probe651 {ℓ} lem

open TruthAlgebra (hPropAlgebra (ℓ-suc ℓ))
module SV = hPropStructure 𝒮ᵥ
open SV using ( _∈ˢ_ )

module Level659 (lam : SV.S) (ordλ : IsOrd lam)
                (succλ : (d : SV.S) → ⟨ d ∈ˢ lam ⟩ → ⟨ sucV d ∈ˢ lam ⟩)
                (X : SV.S)
                (X⊆Lλ : (z : SV.S) → ⟨ z ∈ˢ X ⟩ → ⟨ z ∈ˢ Lset lam ⟩)
                (∅∈λ : ⟨ ∅ ∈ˢ lam ⟩) where

  module HS = HullStage lam ordλ succλ X X⊆Lλ ∅∈λ
  module T = HS.H.T
  open T using ( Code; val; _⊨c_ )

  SL : Type (ℓ-suc ℓ)
  SL = HS.ASt.SL

  -- [LJ-1.651]'s module at the SAME telescope, so its `Code` is this
  -- file's `Code`: both are AtStage lam ordλ .Hull X X⊆L ∅∈λ .T .Code
  -- (src/L/BoundedSubset.lagda.md:907-909 against
  -- agents/tasks/LJ-1-651/Probe651.agda:53-57).
  module P = P651.HullStage lam ordλ succλ X X⊆Lλ ∅∈λ

  -- ===================================================================
  -- SECTION 1.  THE TWO ENDS, EACH TAKEN FROM THE PROBE THAT
  --             TYPECHECKED IT.
  -- ===================================================================

  -- THE HYPOTHESIS, AS THE PREDECESSOR DELIVERED IT.  The type is read
  -- at agents/tasks/LJ-1-651/Probe651.agda:141-142, and the report's
  -- verdict on it is GO (agents/tasks/LJ-1-651/lj-1.651-report.md:3).
  LsetFormula : Type ℓ
  LsetFormula = Formula Code 2

  delivered : LsetFormula
  delivered = P.lset-formula

  -- THE TARGET, verbatim from agents/tasks/LJ-1-650/Probe650.agda:322-328.
  -- Its slot order is VALUE 0, ORDINAL 1: env (v ∷ γ ∷ []).
  LevelFormula : Type (ℓ-suc ℓ)
  LevelFormula =
    Σ[ lv ∈ Formula Code 2 ]
      ( ((v γ : SL) → ⟨ (v ∷ γ ∷ []) ⊨c lv ⟩ → fst v ≡ Lset (fst γ))
      × ((γ : SL) → IsOrd (fst γ)
         → ∥ Σ[ v ∈ SL ]
              ((fst v ≡ Lset (fst γ)) × ⟨ (v ∷ γ ∷ []) ⊨c lv ⟩) ∥₁) )

  -- THE BRIEF'S OBLIGATION, AS A TYPE.
  LsetFormulaToLevel : Type (ℓ-suc ℓ)
  LsetFormulaToLevel = LsetFormula → LevelFormula

  -- ===================================================================
  -- SECTION 2.  THE OBLIGATION IS DEGENERATE, AND HERE IS THE PROOF.
  --
  --   `Formula Code 2` is a type of SYNTAX.  It carries no law about
  --   `_⊨c_`, so it says nothing about `Lset`, and the tree inhabits it
  --   without leaving the syntax chapter.
  -- ===================================================================

  -- 2.1  THE HYPOTHESIS IS FREE.  No predecessor is needed to pay it.
  trivial : LsetFormula
  trivial = ⊤̇

  -- 2.2  SO THE OBLIGATION GIVES THE TARGET OUTRIGHT, twice over: at
  --      [LJ-1.651]'s actual term, and at a formula with no connection
  --      to `Lset` of any kind.
  level-from-obligation : LsetFormulaToLevel → LevelFormula
  level-from-obligation f = f delivered

  level-from-nothing : LsetFormulaToLevel → LevelFormula
  level-from-nothing f = f trivial

  -- 2.3  AND THE TARGET GIVES THE OBLIGATION BACK.
  obligation-from-level : LevelFormula → LsetFormulaToLevel
  obligation-from-level lf _ = lf

  -- 2.4  THE TWO TOGETHER.  The obligation and the target are
  --      interderivable, so the brief's arrow buys NOTHING: proving it
  --      is proving `LevelFormula`, which the brief itself records as a
  --      type nothing inhabits.
  obligation-is-the-target :
      (LsetFormulaToLevel → LevelFormula) × (LevelFormula → LsetFormulaToLevel)
  obligation-is-the-target = level-from-obligation , obligation-from-level

  -- ===================================================================
  -- SECTION 3.  WHAT THE TARGET HAS THAT THE DELIVERED TERM DOES NOT.
  --
  --   Two SEMANTIC laws about `_⊨c_`, stated at [LJ-1.651]'s OWN slot
  --   order: ORDINAL 0, VALUE 1, env (γ ∷ v ∷ [])
  --   (agents/tasks/LJ-1-651/lj-1.651-report.md:1, "the ordinal in
  --   slot 0 and the value in slot 1").  This is the term the brief
  --   asked for if the arrow did not follow.
  -- ===================================================================

  Sound : Formula Code 2 → Type (ℓ-suc ℓ)
  Sound lf = (γ v : SL) → ⟨ (γ ∷ v ∷ []) ⊨c lf ⟩ → fst v ≡ Lset (fst γ)

  Complete : Formula Code 2 → Type (ℓ-suc ℓ)
  Complete lf = (γ : SL) → IsOrd (fst γ)
              → ∥ Σ[ v ∈ SL ]
                   ((fst v ≡ Lset (fst γ)) × ⟨ (γ ∷ v ∷ []) ⊨c lf ⟩) ∥₁

  -- THE CORRECTED HYPOTHESIS.  Syntax PLUS the two laws.
  LsetFormulaWithLaws : Type (ℓ-suc ℓ)
  LsetFormulaWithLaws = Σ[ lf ∈ Formula Code 2 ] (Sound lf × Complete lf)

  -- And the delivered term is exactly the first component, so the
  -- correction ADDS to [LJ-1.651] and discards nothing.
  delivered-is-the-first-component :
      (Sound delivered × Complete delivered) → LsetFormulaWithLaws
  delivered-is-the-first-component laws = delivered , laws

  -- ===================================================================
  -- SECTION 4.  THE PRICE OF THE CORRECTED ARROW: ONE RENAMING.
  --
  --   [LJ-1.651] and [LJ-1.650] disagree about the slot order and
  --   nothing else.  The tree's whole variable calculus is `renameFo`
  --   on syntax and `⊨-rename` on meaning
  --   (src/FOL/Manipulation/Renaming.lagda.md:157-159), and the
  --   transposition is one instance of it.
  -- ===================================================================

  module RS = Sat (hPropAlgebra (ℓ-suc ℓ)) HS.ASt.AbsL.𝒮M {K = Code} val

  swap : Fin 2 → Fin 2
  swap zero       = suc zero
  swap (suc zero) = zero

  swap-agrees : (a b : SL) → RS.Agrees swap (a ∷ b ∷ []) (b ∷ a ∷ [])
  swap-agrees a b zero       = refl
  swap-agrees a b (suc zero) = refl

  transpose : (lf : Formula Code 2) (a b : SL)
            → ((a ∷ b ∷ []) ⊨c renameFo swap lf) ≡ ((b ∷ a ∷ []) ⊨c lf)
  transpose lf a b = RS.⊨-rename swap lf (a ∷ b ∷ []) (b ∷ a ∷ []) (swap-agrees a b)

  -- THE ARROW THE BRIEF WANTED, from the hypothesis that carries the
  -- two laws.  Nothing else is spent.
  level-from-laws : LsetFormulaWithLaws → LevelFormula
  level-from-laws (lf , so , co) = renameFo swap lf , (so' , co')
    where
    so' : (v γ : SL) → ⟨ (v ∷ γ ∷ []) ⊨c renameFo swap lf ⟩
        → fst v ≡ Lset (fst γ)
    so' v γ h = so γ v (subst ⟨_⟩ (transpose lf v γ) h)

    co' : (γ : SL) → IsOrd (fst γ)
        → ∥ Σ[ v ∈ SL ]
             ((fst v ≡ Lset (fst γ)) × ⟨ (v ∷ γ ∷ []) ⊨c renameFo swap lf ⟩) ∥₁
    co' γ oγ = PT.map step (co γ oγ)
      where
      step : Σ[ v ∈ SL ] ((fst v ≡ Lset (fst γ)) × ⟨ (γ ∷ v ∷ []) ⊨c lf ⟩)
           → Σ[ v ∈ SL ]
               ((fst v ≡ Lset (fst γ)) × ⟨ (v ∷ γ ∷ []) ⊨c renameFo swap lf ⟩)
      step (v , e , h) = v , (e , subst ⟨_⟩ (sym (transpose lf v γ)) h)

  -- ===================================================================
  -- SECTION 5.  W3.  THE INDEX BINDER, PRICED IN BOTH DIRECTIONS.
  --
  --   The brief's widest unmeasured term is the index binder of
  --   [LJ-1.650]'s premise: `lset-code-ord` is the index-FREE reading
  --   and `CodedCover` the index-BOUND one.  The binder that closes the
  --   index to a code CONSTANT cannot be a renaming: renaming "moves
  --   only variables, leaving constants alone"
  --   (src/FOL/Manipulation/Renaming.lagda.md:43-44), and the tree has
  --   NO substitution at all (:7, "no substitution, no weakening").
  --   So the ONLY route is the equality trick, and [LJ-1.651] already
  --   wrote it: `inF` at Probe651.agda:149-150.
  -- ===================================================================

  -- The same term, restated here so this file can reason about it.
  bindIx : (lf : Formula Code 2) (c : Code) → Formula Code 1
  bindIx lf c = ∃̇ (lf ∧̇ (var zero ≐ con c))

  bindIx-is-inF : (c : Code) → bindIx delivered c ≡ P.inF c
  bindIx-is-inF c = refl

  -- 5.1  SOUNDNESS SURVIVES THE BINDER.
  ix-sound : (lf : Formula Code 2) → Sound lf
           → (c : Code) (v : SL) → ⟨ (v ∷ []) ⊨c bindIx lf c ⟩
           → fst v ≡ Lset (fst (val c))
  ix-sound lf so c v h = PT.rec (snd (SV._≈ˢ_ (fst v) (Lset (fst (val c))))) step h
    where
    step : Σ[ x ∈ SL ] (⟨ (x ∷ v ∷ []) ⊨c lf ⟩ × (fst x ≡ fst (val c)))
         → fst v ≡ Lset (fst (val c))
    step (x , hlf , hx) = so x v hlf ∙ cong Lset hx

  -- 5.2  AND SO DOES COMPLETENESS.
  ix-complete : (lf : Formula Code 2) → Complete lf
              → (c : Code) → IsOrd (fst (val c))
              → ∥ Σ[ v ∈ SL ]
                   ((fst v ≡ Lset (fst (val c))) × ⟨ (v ∷ []) ⊨c bindIx lf c ⟩) ∥₁
  ix-complete lf co c oc = PT.map step (co (val c) oc)
    where
    step : Σ[ v ∈ SL ]
             ((fst v ≡ Lset (fst (val c))) × ⟨ (val c ∷ v ∷ []) ⊨c lf ⟩)
         → Σ[ v ∈ SL ]
             ((fst v ≡ Lset (fst (val c))) × ⟨ (v ∷ []) ⊨c bindIx lf c ⟩)
    step (v , e , h) = v , (e , ∣ val c , (h , refl) ∣₁)

  -- 5.3  THE BINDER IS FREE ON THE LAWS AND COSTS ONE `∃̇` AND ONE `≐`
  --      ON THE SYNTAX.  Both directions above are two-line terms.  The
  --      one thing it DOES cost is the delivered grade certificate:
  --      `Σ₁` is generated by `σ-Δ₀` and `σ-∃` ONLY
  --      (src/FOL/LevyHierarchy.lagda.md:73-75), so there is no `σ-∧`,
  --      and `lf ∧̇ (var zero ≐ con c)` leaves the class the moment `lf`
  --      is not Δ₀.  [LJ-1.651] certified `lset-formula` as Σ₁ with two
  --      unbounded `∃̇` (its report, section 4), so `inF` carries NO
  --      delivered certificate.  That is a machinery gap and not a
  --      mathematical one: prenexing is what is missing.

  -- 5.4  AND THE GRADE LOSS IS REFUTED HERE, NOT MERELY UNFOUND.
  --      `Δ₀` is generated by ten clauses and NONE of them is `∃̇`
  --      (src/FOL/LevyHierarchy.lagda.md:47-57); `Σ₁` is generated by
  --      `σ-Δ₀` and `σ-∃` and by nothing else (:73-75).  So a
  --      conjunction whose left half is an unbounded existential lies
  --      in NEITHER class, and the index binder puts exactly that
  --      conjunction under one `∃̇`.  Three machine-checked negatives,
  --      each by an absurd pattern on a constructor that does not
  --      exist.

  no-Δ₀-∃ : {n : ℕ} {φ : Formula Code (suc n)} → Δ₀ (∃̇ φ) → Empty.⊥
  no-Δ₀-∃ ()

  no-Σ₁-∃∧ : {n : ℕ} {φ : Formula Code (suc n)} {ψ : Formula Code n}
           → Σ₁ ((∃̇ φ) ∧̇ ψ) → Empty.⊥
  no-Σ₁-∃∧ (σ-Δ₀ (δ-∧ d _)) = no-Δ₀-∃ d

  -- The shape of the index binder over a formula that is itself an
  -- unbounded existential.  `[LJ-1.651]` certified `lset-formula` as
  -- Σ₁ with TWO unbounded `∃̇` (its report, section 4), so its head IS
  -- an `∃̇` and this is the shape `inF` has.
  no-Σ₁-bindIx :
      {n : ℕ} {φ : Formula Code (suc (suc n))} {ψ : Formula Code (suc n)}
    → Σ₁ (∃̇ ((∃̇ φ) ∧̇ ψ)) → Empty.⊥
  no-Σ₁-bindIx (σ-Δ₀ ())
  no-Σ₁-bindIx (σ-∃ s) = no-Σ₁-∃∧ s

  -- AND AT THE DELIVERED TERM ITSELF.  `inF` is the arity-1 reading
  -- [LJ-1.651] delivered beside the obligation
  -- (agents/tasks/LJ-1-651/Probe651.agda:149-150), and its report calls
  -- it "the exact shape `hull-closed` takes" (section 1).  It carries
  -- NO Σ₁ certificate, and no Δ₀ one either.
  no-Σ₁-inF : (c : Code) → Σ₁ (P.inF c) → Empty.⊥
  no-Σ₁-inF c (σ-Δ₀ ())
  no-Σ₁-inF c (σ-∃ (σ-Δ₀ (δ-∧ () _)))

  -- AND AT THE ALPHABET THE TRANSFER THEOREM READS.  `σ₁-up`
  -- (src/FOL/Absoluteness.lagda.md:182-183) has premise `Σ₁ φ` for
  -- `φ : Formula SM n`, and a code formula reaches that alphabet by
  -- `mapFo val`, which is the move `hull-closed` itself makes
  -- (src/L/Hull.lagda.md:415).  `mapFo` keeps the head constructor, so
  -- the refutation survives the move and no hedging is needed.
  no-Σ₁-mapped-inF : (c : Code) → Σ₁ (mapFo val (P.inF c)) → Empty.⊥
  no-Σ₁-mapped-inF c (σ-Δ₀ ())
  no-Σ₁-mapped-inF c (σ-∃ (σ-Δ₀ (δ-∧ () _)))

  -- The consequence, stated exactly: `σ₁-up`'s premise cannot be met
  -- for `inF` at any parameter and at either alphabet.  It says
  -- NOTHING about `hull-closed`, which takes a bare `Formula Code 1`
  -- and asks for no grade (src/L/Hull.lagda.md:415-417).

  -- ===================================================================
  -- SECTION 6.  WHAT THE CORRECTION EARNS, from [LJ-1.650]'s delivered
  --             theorem taken as a hypothesis.
  --
  --   `coded-cover-from-level : LevelFormula → CodedCover` typechecked
  --   at agents/tasks/LJ-1-650/Probe650.agda:385-386.  It enters here
  --   only as a hypothesis, because importing Probe650 is a second
  --   frame this task did not price.
  -- ===================================================================

  -- agents/tasks/LJ-1-650/Probe650.agda:88-92, unchanged.
  CodedCover : Type (ℓ-suc ℓ)
  CodedCover = (c : Code)
             → Σ[ d ∈ Code ]
                 ( IsOrd (fst (val d))
                 × ⟨ fst (val c) ∈ˢ Lset (fst (val d)) ⟩ )

  laws-to-coded-cover : (LevelFormula → CodedCover)
                      → LsetFormulaWithLaws → CodedCover
  laws-to-coded-cover cc lw = cc (level-from-laws lw)
