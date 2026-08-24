{-# OPTIONS --cubical --safe --guardedness #-}

-- [LJ-1.625]  W3.  THE OBLIGATION, TYPE ONLY: `landing-survey`.
--
-- WRITTEN FIRST AND TYPECHECKED ALONE, per the brief's W3 section:
-- "Write it FIRST and typecheck it ALONE before any content.  ESTIMATE:
-- about 10 lines, cap at one minute."  [LJ-1.620]'s probe died at
-- parse (`Syntax.WrongContentBlock`, the brief's premise 1), so the
-- smallest well-formed file that BINDS `landing-survey` is the widest
-- unmeasured term, and it is THIS file.  It is raw Agda with no
-- markdown anywhere: nothing in it can raise a content-block error.
-- The estimate of ten lines was for a term without witnesses; the
-- survey type below carries each ingredient's delivered type, so the
-- statement section of ingredient (iv) is restated here verbatim from
-- [LJ-1.608]'s alone-checked statement
-- (agents/tasks/LJ-1-608/runs/W3.agda), and the file is longer than
-- the estimate for that reason.  The tree decides, and this is the
-- tree's shape.
--
-- WHAT THE SURVEY IS.  For each of the four PAID `class-pred`
-- ingredients, one Row: the CHAPTER measured to host it, the import
-- EDGES the landing would add, the BLOCKER at the natural home, and
-- the ingredient ITSELF, re-derived from `src/` imports only, at the
-- delivered type.  Chapters are CONSTRUCTORS and not strings: the
-- tree carries no `String` from its dependencies, and a constructor
-- names a module exactly as unambiguously.  The reading behind each
-- constructor is in the report, at `file:line`.
--
-- THE HOLE, AND WHERE IT WENT.  `landing-survey : Survey` with a
-- hole ran ALONE in this file before anything else existed
-- (runs/w3-3.out: exit 42 at exactly ONE unsolved interaction meta
-- and no other error).  The declaration then moved to the probe so
-- that this module, hole-free, can be imported; the obligation is
-- discharged there AT this module's own `Survey` type, so the stated
-- survey and the delivered one cannot drift.  A green run of this
-- file is: the parse holds, the type elaborates,
-- and nothing is unsolved (runs/w3-5.out, exit 0).
--
-- CALIBER.  THE PROGRAM SET GHCRTS ON THIS PANE.  I DID NOT SET IT.
-- ONE AGDA PROCESS AT A TIME.

open import Base.Prelude
open import Base.Truth
open import Base.Classical using ( LEM )
open import Cubical.HITs.CumulativeHierarchy.Base using ( V; _∈_ )
open import Cubical.HITs.CumulativeHierarchy.Properties using ( ⟪_⟫; ⟪_⟫↪ )
open import Cubical.HITs.CumulativeHierarchy.Constructions using ( module InfinitySet )
open import L.Constructible using ( IsOrd )
import Cubical.Data.Empty as Empty

module LJ-1-625.runs.W3 {ℓ : Level} (lem : LEM (ℓ-suc ℓ))
  (α₀ : V ℓ) (oα₀ : IsOrd α₀)
  (sq : (δ : V ℓ) → ⟨ δ ∈ InfinitySet.sucV α₀ ⟩ → (⟨ δ ∈ InfinitySet.ω {ℓ} ⟩ → Empty.⊥)
      → Σ[ f ∈ (⟪ δ ⟫ × ⟪ δ ⟫ → ⟪ δ ⟫) ]
          ((x y : ⟪ δ ⟫ × ⟪ δ ⟫) → f x ≡ f y → x ≡ y)) where

open import Cubical.Data.List using ( List; [] )

-- ===================================================================
-- THE SURVEY'S ANSWER TYPES.
--
--   Chapter: the five masters the reading measured as hosts or as the
--   blocked natural home.  Nothing else appears in the survey.
--   Blocker: nothing, or the one cycle the brief gave for ingredient
--   (i) and ordered not re-derived.
--   Row: host, edges, blocker, and the ingredient at its delivered
--   type, re-derived from `src/` names only.
-- ===================================================================

data Chapter : Type where
  definibility constructible stageCardinal boundedSubset choiceFaithful
    : Chapter

data Blocker : Type where
  unblocked cycle-definability : Blocker

record Row {a : Level} (A : Type a) : Type (ℓ-suc a) where
  constructor lands-at
  field
    host : Chapter
    new-edges : List Chapter
    blocker : Blocker
    at-the-host : A


-- ===================================================================
-- SECTION 1.  INGREDIENT (i), THE TYPE.
--
--   The delivered shape is the first two components of
--   `first-two-internal` (agents/tasks/LJ-1-613/Probe613.agda:283-290):
--   `D` in `LimitStep`'s own parameter shape and its inversion, bound
--   together.  Spelled from `L.Constructible`, `L.Definability`,
--   `FOL.Syntax`, `FOL.ZFStructure` and `V.Hierarchy` only, the five
--   modules `L.Constructible` itself already has
--   (src/L/Constructible.lagda.md:34-37).
-- ===================================================================

module Ingredient-I where

  open import FOL.Syntax using ( Formula )
  open import FOL.ZFStructure using ( module hPropStructure )
  open import V.Hierarchy {ℓ} using ( 𝒮ᵥ )
  open import L.Constructible {ℓ} using ( Lset; 𝒟ₒ; 𝒟ₒ-inv )
  open import L.Definability {ℓ} using ( module DefOf )
  import Cubical.HITs.PropositionalTruncation as PT
  open PT using ( ∥_∥₁ )
  open hPropStructure 𝒮ᵥ using ( _∈ˢ_ )

  DInvType =
    Σ[ D ∈ ((δ : V ℓ) → Formula ⟪ Lset δ ⟫ 1 → V ℓ) ]
      ((δ : V ℓ) (y : V ℓ) → ⟨ y ∈ˢ 𝒟ₒ (Lset δ) ⟩
        → ∥ Σ[ φ₀ ∈ Formula ⟪ Lset δ ⟫ 1 ] (D δ φ₀ ≡ y) ∥₁)


-- ===================================================================
-- SECTION 2.  INGREDIENT (ii), THE TYPE.
--
--   The delivered shape is the third component of `first-two-internal`
--   (agents/tasks/LJ-1-613/Probe613.agda:283-290): `leastOf` over the
--   site's own ordinal well-order.  Spelled from `L.WellOrder.Base`,
--   `L.StageCardinal`, `L.Constructible`, `FOL.ZFStructure` and
--   `V.Hierarchy` only; `L.StageCardinal` itself already imports every
--   one of them (src/L/StageCardinal.lagda.md:12,24,27-28,35).
-- ===================================================================

module Ingredient-II where

  open import FOL.ZFStructure using ( module hPropStructure )
  open import V.Hierarchy {ℓ} using ( 𝒮ᵥ )
  import Cubical.HITs.PropositionalTruncation as PT
  open PT using ( ∥_∥₁ )
  open import L.WellOrder.Base {ℓₚ = ℓ-suc ℓ} using ( SWO; leastOf; IsLeast )
  import L.StageCardinal
  module SC = L.StageCardinal {ℓ} lem α₀ oα₀ sq
  open hPropStructure 𝒮ᵥ using ( _∈ˢ_ )

  LeastType =
    (δ : V ℓ) (oδ : IsOrd δ) (P : ⟪ δ ⟫ → hProp (ℓ-suc ℓ))
      → ∥ Σ[ a ∈ ⟪ δ ⟫ ] ⟨ P a ⟩ ∥₁
      → Σ[ a ∈ ⟪ δ ⟫ ] IsLeast (SC.OrdSWO.ordSWO δ oδ) P a


-- ===================================================================
-- SECTION 4.  INGREDIENT (iv), THE TYPE: THE STATEMENT, RESTATED.
--
--   [LJ-1.608]'s statement module, verbatim in its mathematical
--   content (agents/tasks/LJ-1-608/runs/W3.agda, `Site` and `At`):
--   the branch's graph at a strictly infinite member stage, both
--   directions, from the member stage's own graph.  Spelled from
--   `src/` imports only, which is the measurement: every name below
--   is importable by a module over exactly `L.StageCardinal`,
--   `L.Constructible`, `L.Ordinal`, `L.Ordinal.Stages`,
--   `L.Axioms.Basic`, `FOL.Syntax`, `FOL.ZFStructure`,
--   `FOL.Absoluteness`, `V.Hierarchy` and `V.Presentation`.
-- ===================================================================

module Ingredient-IV where

  open import V.Hierarchy {ℓ} using ( 𝒮ᵥ; ∈-irrefl )
  open import V.Presentation {ℓ} using ( member; fiber )
  open import FOL.Syntax using ( Formula )
  open import FOL.ZFStructure using ( module hPropStructure )
  open import FOL.Absoluteness
  open import L.Constructible {ℓ} using ( 𝒮ʟ; isL; isL-trans; Lset→isL; Lset )
  open import L.Ordinal {ℓ} using ( ω-ord; suc-ord; mem-ord )
  open import L.Ordinal.Stages {ℓ} lem using ( ord∈Lset-suc )
  open import L.Axioms.Basic {ℓ} using ( LsetS )
  import L.StageCardinal
  open InfinitySet {ℓ} using ( ω; sucV )
  open TruthAlgebra (hPropAlgebra (ℓ-suc ℓ))
  module SV = hPropStructure 𝒮ᵥ
  module SL = hPropStructure 𝒮ʟ
  open SV using ( _∈ˢ_ )
  open SL using ( S )
  module AbsL = FOL.Absoluteness.Single 𝒮ᵥ isL isL-trans
  open AbsL renaming ( _⊨ᵐ_ to _⊨_ )
  module SC = L.StageCardinal {ℓ} lem α₀ oα₀ sq
  open SC using ( _↪_ )

  -- The lifts, [LJ-1.561]'s discipline, one line each
  -- (agents/tasks/LJ-1-608/runs/W3.agda:81-89, verbatim).
  isL-ord : (β : V ℓ) → IsOrd β → ⟨ isL β ⟩
  isL-ord β oβ = Lset→isL (sucV β) (suc-ord oβ) β (ord∈Lset-suc β oβ)

  up : (b : S) → ⟪ fst b ⟫ → S
  up b m = ⟪ fst b ⟫↪ m , isL-trans (member (fst b) m) (snd b)

  ixOf : (b x : S) → ⟨ fst x ∈ fst b ⟩ → ⟪ fst b ⟫
  ixOf b x k = fiber (fst b) {x = fst x} k .fst

  module Site (α : V ℓ) (oα : IsOrd α) (α∈suc : ⟨ α ∈ˢ sucV α₀ ⟩)
              (infα : ⟨ α ∈ˢ ω ⟩ → Empty.⊥)
              (IH : (δ : V ℓ) → ⟨ δ ∈ˢ α ⟩ → SC.Upper.P δ) where

    module At (m : ⟪ α ⟫) (ω∈δ : ⟨ ω ∈ˢ (⟪ α ⟫↪ m) ⟩) where

      δ : V ℓ
      δ = ⟪ α ⟫↪ m

      δ∈α : ⟨ δ ∈ˢ α ⟩
      δ∈α = member α m

      oδ : IsOrd δ
      oδ = mem-ord {A = α} oα δ δ∈α

      δ∈suc : ⟨ δ ∈ˢ sucV α₀ ⟩
      δ∈suc = suc-ord oα₀ .fst {x = α} {y = δ} δ∈α α∈suc

      infδ : ⟨ δ ∈ˢ ω ⟩ → Empty.⊥
      infδ h = ∈-irrefl ω (ω-ord .fst ω∈δ h)

      IHδ : ⟪ Lset δ ⟫ ↪ ⟪ δ ⟫
      IHδ = IH δ δ∈α oδ δ∈suc infδ

      br : ⟪ Lset δ ⟫ ↪ ⟪ α ⟫
      br = SC.Upper.comp-inj IHδ (SC.Upper.Emb.emb α oα δ δ∈α)

      δL : S
      δL = LsetS δ oδ

      αO : S
      αO = α , isL-ord α oα

      δO : S
      δO = δ , isL-ord δ oδ

      val : (x : S) (k : ⟨ fst x ∈ fst δL ⟩) → S
      val x k = up αO (fst br (ixOf δL x k))

      valδ : (x : S) (k : ⟨ fst x ∈ fst δL ⟩) → S
      valδ x k = up δO (fst IHδ (ixOf δL x k))

      IHGraph : Type (ℓ-suc ℓ)
      IHGraph = Σ[ ψ ∈ Formula S 2 ]
        ( ((x y : S) (k : ⟨ fst x ∈ fst δL ⟩)
           → fst y ≡ fst (valδ x k) → ⟨ (y ∷ x ∷ []) ⊨ ψ ⟩)
        × ((x y : S) → ⟨ (y ∷ x ∷ []) ⊨ ψ ⟩ → (k : ⟨ fst x ∈ fst δL ⟩)
           → fst y ≡ fst (valδ x k)) )

      RecGraph∞ : Type (ℓ-suc ℓ)
      RecGraph∞ = IHGraph →
        Σ[ ψ ∈ Formula S 2 ]
          ( ((x y : S) (k : ⟨ fst x ∈ fst δL ⟩)
             → fst y ≡ fst (val x k) → ⟨ (y ∷ x ∷ []) ⊨ ψ ⟩)
          × ((x y : S) → ⟨ (y ∷ x ∷ []) ⊨ ψ ⟩ → (k : ⟨ fst x ∈ fst δL ⟩)
             → fst y ≡ fst (val x k)) )

  RecGraphType =
    (α : V ℓ) (oα : IsOrd α) (α∈suc : ⟨ α ∈ˢ sucV α₀ ⟩)
    (infα : ⟨ α ∈ˢ ω ⟩ → Empty.⊥)
    (IH : (δ : V ℓ) → ⟨ δ ∈ˢ α ⟩ → SC.Upper.P δ)
    (m : ⟪ α ⟫) (ω∈δ : ⟨ ω ∈ˢ (⟪ α ⟫↪ m) ⟩)
      → Site.At.RecGraph∞ α oα α∈suc infα IH m ω∈δ


-- ===================================================================
-- SECTION 3.  INGREDIENT (v), THE TYPE.
--
--   The delivered shape is `key-at-stage-1` bound with the two
--   collection rows of [LJ-1.600] (agents/tasks/LJ-1-600/
--   Probe600.agda:160-189): the coded copy at arity one, its
--   introduction half and its elimination half.  The elimination
--   half is the chapter's own ARITY-GENERIC application `keyS`, as
--   delivered; at `n := 1` it is `k` by the probe's definitional
--   tie, so the row below spells the chapter's own shape.  Spelled
--   from `L.Coding.CodeSet`, `L.Axioms.Basic`, `FOL.Syntax`,
--   `FOL.ZFStructure`, `L.Constructible` and `V.Hierarchy` only.
-- ===================================================================

module Ingredient-V where

  open import FOL.Syntax using ( Formula )
  open import FOL.ZFStructure using ( module hPropStructure )
  open import V.Hierarchy {ℓ} using ( 𝒮ᵥ )
  open import L.Constructible {ℓ} using ( 𝒮ʟ; Lset )
  open import L.Axioms.Basic {ℓ} using ( LsetS )
  open import L.Coding.CodeSet {ℓ} lem
    using ( keyS; AllCodes; key∈AllCodes; AllCodes-out )
  module SL = hPropStructure 𝒮ʟ
  open SL using ( S )
  import Cubical.HITs.PropositionalTruncation as PT
  open PT using ( ∥_∥₁ )

  KeyType =
    Σ[ k ∈ ((δ : V ℓ) (oδ : IsOrd δ) → Formula ⟪ Lset δ ⟫ 1 → S) ]
      ( Σ[ c ∈ ((δ : V ℓ) (oδ : IsOrd δ) (φ : Formula ⟪ Lset δ ⟫ 1)
               → ⟨ k δ oδ φ SL.∈ˢ AllCodes (LsetS δ oδ) ⟩) ]
        ((δ : V ℓ) (oδ : IsOrd δ) (x : S)
          → ⟨ x SL.∈ˢ AllCodes (LsetS δ oδ) ⟩
          → ∥ (Σ[ n ∈ ℕ ] Σ[ ψ ∈ Formula ⟪ Lset δ ⟫ n ]
                (x .fst ≡ keyS (LsetS δ oδ) ψ .fst)) ∥₁) )


-- ===================================================================
-- SECTION 5.  THE SURVEY.
--
--   One Row per paid ingredient, in the table's order (i), (ii),
--   (iv), (v).  `landing-survey : Survey` with a hole lived in THIS
--   file for the alone run and is recorded at runs/w3-3.out (exit
--   42, exactly ONE unsolved interaction meta, no other error,
--   1.71 s, 386,842,624 bytes).  The obligation itself is discharged
--   in Probe625.agda, at THIS module's own `Survey` type, imported,
--   so the stated survey and the delivered one cannot drift.
-- ===================================================================

Survey =
  Σ[ row-i ∈ Row Ingredient-I.DInvType ]
    Σ[ row-ii ∈ Row Ingredient-II.LeastType ]
      Σ[ row-iv ∈ Row Ingredient-IV.RecGraphType ]
        (Row Ingredient-V.KeyType)
