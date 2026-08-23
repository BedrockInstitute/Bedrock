{-# OPTIONS --cubical --safe --guardedness #-}

-- [LJ-1.596]  W3.  THE GRAPH OF stage-card-upper's `step`, AS A FORMULA,
-- TYPE ONLY.
--
-- WRITTEN FIRST AND TYPECHECKED ALONE, before any other Agda of this
-- task, as the brief orders.  CALIBER: the program sets GHCRTS on this
-- pane.  I do not set it.  One Agda process at a time.
--
-- THE QUESTION W3 SETTLES.  The machine's slot for a recursion's graph
-- is `Recursion.graph : Formula S 2` (src/L/Recursion.lagda.md:106), and
-- the chapter's prose says the graph is the whole condition
-- (src/L/Recursion.lagda.md:259-262).  Can that slot be FILLED for the
-- recursion this brief names, `stage-card-upper`
-- (src/L/StageCardinal.lagda.md:564-566)?  This slice states everything
-- the question needs, at ABSTRACT DATA where a term would be a claim:
--   0.  `step` and `stage-card-upper` themselves, TYPE ONLY, so no
--       conversion problem is created.  [LJ-1.584] measured one that
--       does not terminate (agents/tasks/LJ-1-584/runs/w3b-1.out).
--   1.  the value `P` is FUNCTION-valued, and the machine consumes
--       S-valued functions (`Definition.fn : S → S`,
--       src/L/Recursion.lagda.md:275).
--   2.  at a fixed stage, the element-level function `fn` the machine
--       would internalize, its adequacy `Adequate`, and the actual
--       `Recursion`/`Definition` records from src/, INSTANTIATED from
--       abstract adequacy.  The slot typechecks when handed abstract
--       data.  What no chapter of this tree supplies is the TERM
--       `ψ : Formula S 2` with `Adequate ψ`.
--   3.  the two ingredients of the graph's class predicate that the
--       object language cannot name, each stated as a type at its own
--       site: the meta syntax the existential ranges over, and the
--       count through the branch injection.
--
-- THE TOWER IS ABSTRACT DATA ([LJ-1.594]'s TYPE-ONLY idiom,
-- agents/tasks/LJ-1-594/Probe594.agda:75).  Nothing here asserts it.
--
-- TWO CARRIERS, kept apart as [LJ-1.592]'s own W3 slice kept them
-- (agents/tasks/LJ-1-592/runs/W3.agda:35-37): `L.StageCardinal` and
-- `L.StageBound` speak the raw carrier `V ℓ`, `L.Recursion` and
-- `L.Coding.Model` speak the L-carrier `S`.  The V-membership is
-- renamed `_∈ᵥ_` so the S-membership can keep the chapter's own name.

open import Base.Prelude
open import Base.Truth
open import Base.Classical using ( LEM )
open import Cubical.HITs.CumulativeHierarchy.Base using ( V; _∈_ )
open import L.Constructible using ( IsOrd )

module LJ-1-596.runs.W3 {ℓ : Level} (lem : LEM (ℓ-suc ℓ))
  (α₀ : V ℓ) (oα₀ : IsOrd α₀) where

open import FOL.ZFStructure using ( module hPropStructure )
open import FOL.Syntax using ( Formula )
import FOL.Absoluteness
open import V.Hierarchy {ℓ} using ( 𝒮ᵥ )
open import V.Presentation {ℓ} using ( member; fiber )
open import L.Constructible {ℓ}
  using ( 𝒮ʟ; isL; isL-trans; Lset; Lset→isL )
open import L.Ordinal {ℓ} using ( suc-ord )
open import L.Ordinal.Stages {ℓ} lem using ( ord∈Lset-suc )
open import L.Axioms.Basic {ℓ} using ( LsetS )
open import L.Coding.Model {ℓ} using ( prʟ )
open import L.Cardinal {ℓ} lem using ( _↪_ )
open import L.StageBound {ℓ} lem using ( SqFam )
import L.StageCardinal
import L.Recursion

open import Cubical.HITs.CumulativeHierarchy.Properties using ( ⟪_⟫; ⟪_⟫↪ )
open import Cubical.HITs.CumulativeHierarchy.Constructions
  using ( module InfinitySet )
open InfinitySet {ℓ} using ( ω; sucV )
open import Cubical.Data.Sum using ( _⊎_; inl; inr )
import Cubical.Data.Empty as Empty
import Cubical.HITs.PropositionalTruncation as PT
open PT using ( ∥_∥₁; ∣_∣₁ )

open TruthAlgebra (hPropAlgebra (ℓ-suc ℓ))
open hPropStructure 𝒮ᵥ hiding ( S; isSetS; _≈ˢ_ ) renaming ( _∈ˢ_ to _∈ᵥ_ )
open hPropStructure 𝒮ʟ using ( S; _∈ˢ_ )

module AbsL = FOL.Absoluteness.Single 𝒮ᵥ isL isL-trans
open AbsL renaming ( _⊨ᵐ_ to _⊨_ )

module Rec = L.Recursion {ℓ} lem

-- =====================================================================
-- 0 AND 1.  THE RECURSION ITSELF, TYPE ONLY, under the tower as
--     abstract data.  No conversion problem is created: both rows are
--     the chapter's own names, applied to nothing.  [LJ-1.584]
--     measured the conversion problem this avoids
--     (agents/tasks/LJ-1-584/runs/w3b-1.out).
-- =====================================================================

module Tower (sqf : SqFam α₀) where

  module SC = L.StageCardinal {ℓ} lem α₀ oα₀ sqf

  step : (α : V ℓ) → ((δ : V ℓ) → ⟨ δ ∈ᵥ α ⟩ → SC.Upper.P δ) → SC.Upper.P α
  step = SC.Upper.step

  stage-card-upper :
    (α : V ℓ) → IsOrd α → ⟨ α ∈ᵥ sucV α₀ ⟩ → (⟨ α ∈ᵥ ω ⟩ → Empty.⊥)
    → SC._↪_ (⟪ Lset α ⟫) (⟪ α ⟫)
  stage-card-upper = SC.Upper.stage-card-upper

  -- THE VALUE IS FUNCTION-VALUED.  The machine consumes an S-valued
  -- function (`Definition.fn : S → S`,
  -- src/L/Recursion.lagda.md:243); `step`'s value is an injection
  -- between fibers.  This is src/L/StageCardinal.lagda.md:530-532
  -- written out, and the `refl` is the check that it is written
  -- correctly.
  P-is-function-valued :
    (α : V ℓ) → SC.Upper.P α
            ≡ ( IsOrd α → ⟨ α ∈ᵥ sucV α₀ ⟩ → (⟨ α ∈ᵥ ω ⟩ → Empty.⊥)
              → Σ[ f ∈ (⟪ Lset α ⟫ → ⟪ α ⟫) ]
                  ((x y : ⟪ Lset α ⟫) → f x ≡ f y → x ≡ y) )
  P-is-function-valued α = refl

-- =====================================================================
-- 2.  THE GRAPH, AT A FIXED STAGE, TYPE ONLY.
-- =====================================================================

-- Every ordinal is an L-element, so the ordinal's members lift.
-- `agents/tasks/LJ-1-592/runs/W3.agda:45-46` is the same term.
isL-ord : (β : V ℓ) → IsOrd β → ⟨ isL β ⟩
isL-ord β oβ = Lset→isL (sucV β) (suc-ord oβ) β (ord∈Lset-suc β oβ)

module Elem (α : V ℓ) (oα : IsOrd α) (g : ⟪ Lset α ⟫ ↪ ⟪ α ⟫) where

  -- the ambient injection, as ABSTRACT DATA.  `Tower` above is where
  -- the tree's own chapter would deliver it, at the tower's own two
  -- side conditions (src/L/StageCardinal.lagda.md:564-565); the graph
  -- question is the same for any source of `g`, so the slice takes it
  -- abstract and `Tower` states the delivery.
  h : ⟪ Lset α ⟫ → ⟪ α ⟫
  h = fst g

  hα : ⟨ isL α ⟩
  hα = isL-ord α oα

  -- the value lifted to an L-element
  upα : ⟪ α ⟫ → S
  upα m = ⟪ α ⟫↪ m , isL-trans {x = α} (member α m) hα

  -- membership at this stage is decidable, from LEM
  ∈? : (x : V ℓ) (A : V ℓ) → ⟨ x ∈ᵥ A ⟩ ⊎ (⟨ x ∈ᵥ A ⟩ → Empty.⊥)
  ∈? x A = lem (x ∈ᵥ A)

  -- THE ELEMENT-LEVEL FUNCTION the machine would internalize: the
  -- ordered pair of the argument with its image.  `prʟ` is the model's
  -- own pairing (src/L/Coding/Model.lagda.md), with `prʟ-fst` beside
  -- it, so `fst (fn x)` is the `pr` of the underlying sets and a code
  -- read back through `InjCode`'s `pr`-reader needs no translation.
  fn : S → S
  fn x with ∈? (fst x) (Lset α)
  ... | inl x∈ = prʟ x (upα (h (fiber (Lset α) x∈ .fst)))
  ... | inr _  = prʟ x x

  -- THE ADEQUACY the machine demands of any candidate graph: the last
  -- two fields of `Definition` (src/L/Recursion.lagda.md:277-279)
  -- instantiated at this stage's data.  This is the TYPE; the TERM `ψ`
  -- is what no chapter of this tree supplies.
  Adequate : Formula S 2 → Type (ℓ-suc ℓ)
  Adequate ψ =
      ((x : S) → ⟨ x ∈ˢ LsetS α oα ⟩ → ⟨ (fn x ∷ x ∷ []) ⊨ ψ ⟩)
    × ((x : S) → ⟨ x ∈ˢ LsetS α oα ⟩ → (y : S)
        → ⟨ (y ∷ x ∷ []) ⊨ ψ ⟩ → y ≡ fn x)

  -- AND THE SLOT FILLS FROM ABSTRACT ADEQUACY.  Both records of
  -- src/L/Recursion.lagda.md, instantiated at this stage's data.  If a
  -- term `ψ` with `Adequate ψ` existed, the machine would run and
  -- `table` below would be a set of L.
  module Given (ψ : Formula S 2) (ad : Adequate ψ) where

    D : Rec.Definition
    D = record
      { dom     = LsetS α oα
      ; fn      = fn
      ; graph   = ψ
      ; defines = ad .fst
      ; only    = ad .snd }

    R : Rec.Recursion
    R = Rec.asRecursion D

    -- the machine's answer, `Of.table` (src/L/Recursion.lagda.md:179-180)
    table : S
    table = Rec.Of.table R

    table-in : (x y : S) → ⟨ x ∈ˢ LsetS α oα ⟩
             → ⟨ (y ∷ x ∷ []) ⊨ ψ ⟩ → ⟨ y ∈ˢ table ⟩
    table-in = Rec.Of.table-in R

    table-out : (y : S) → ⟨ y ∈ˢ table ⟩
              → ∥ (Σ[ x ∈ S ] (⟨ x ∈ˢ LsetS α oα ⟩
                    × ⟨ (y ∷ x ∷ []) ⊨ ψ ⟩)) ∥₁
    table-out = Rec.Of.table-out R

-- =====================================================================
-- 3.  THE TWO INGREDIENTS OF THE GRAPH'S PREDICATE THAT THE OBJECT
--     LANGUAGE CANNOT NAME.  Both live in `module LimitStep`
--     (src/L/StageCardinal.lagda.md:277-283); both are stated here at
--     their own sites, TYPE ONLY.
-- =====================================================================

module Ingredients (α : V ℓ) where

  -- (a)  THE META SYNTAX the class predicate's existential ranges over.
  --      `F m = Formula ⟪ Lset (⟪ α ⟫↪ m) ⟫ 1`
  --      (src/L/StageCardinal.lagda.md:281-282).  `Formula K n` is an
  --      Agda inductive family (src/FOL/Syntax.lagda.md:94); the object
  --      language quantifies over SETS, and no formula of it quantifies
  --      over this type.
  F-at : (m : ⟪ α ⟫) → Type ℓ
  F-at m = Formula ⟪ Lset (⟪ α ⟫↪ m) ⟫ 1

  -- (b)  THE COUNT THROUGH THE BRANCH INJECTION.  `cnt`
  --      (src/L/StageCardinal.lagda.md:288-289) counts `F m` into
  --      `⟪ α ⟫` through `ih m` (:283), and `ih m` is
  --      `stage-card-upper`'s own value at a member, by `branch`
  --      (:534-537).  A graph of the recursion would have to name this
  --      count, and the count is defined FROM the recursion.
  CntShape : Type ℓ
  CntShape = (m : ⟪ α ⟫) → F-at m → ⟪ α ⟫

  -- (c)  THE CLASS PREDICATE ITSELF, whose least element is the value
  --      (src/L/StageCardinal.lagda.md:319-324).  TYPE ONLY: it is
  --      stated as the Ω-valued relation it is, because a
  --      `Formula S 2` stating it does not exist in this tree.
  ClassPredShape : Type (ℓ-suc (ℓ-suc ℓ))
  ClassPredShape = (x : ⟪ Lset α ⟫) → ⟪ α ⟫ → Ω
