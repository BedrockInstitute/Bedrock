{-# OPTIONS --cubical --safe --guardedness #-}

-- [LJ-1.608]  THE GRAPH OF INGREDIENT (iv)'S RECURSION AT A STRICTLY
-- INFINITE MEMBER STAGE.
--
-- THE QUESTION.  [LJ-1.597]'s upheld table counts five ingredients of
-- the step's value equation; ingredient (iv) is the branch `ih`
-- (agents/tasks/LJ-1-597/review-of-step-graph.md, THE BLOCK, row iv).
-- [LJ-1.601] measured its finite half GO, the table
-- (agents/tasks/LJ-1-601/Probe601.agda section 2), and its report
-- names the remainder: "what remains unmeasured in (iv) is the
-- recursion at infinite member stages".  This probe measures that
-- remainder.
--
-- THE ANSWER IS A MEASUREMENT AND IT IS GO: at a strictly infinite
-- member stage the branch's value is the composed IH at the member
-- stage, embedded by the membership-fiber embedding
-- (src/L/StageCardinal.lagda.md:555-560, the `inr (inr)` row), and
-- the graph of THAT is the member stage's OWN graph, VERBATIM: the
-- object language reads equality and membership on underlying sets,
-- and the embedding changes presentations only.  The obligation
-- `rec-graph-at-infinite` at section 3 takes the member stage's own
-- graph as a hypothesis and returns the SAME formula with both
-- directions at the branch.  The run ledger is in
-- agents/tasks/LJ-1-608/lj-1.608-report.md.
--
-- NO ROW puts `step`, `branch`, `stage-card-upper` or `ord-tri` into
-- a conversion problem: [LJ-1.584] measured that one such row does
-- not terminate (agents/tasks/LJ-1-584/runs/w3b-1.out).  The branch's
-- value at the strictly infinite member stage is taken as the term
-- the source's own `inr (inr)` row delivers, `comp-inj` of the IH at
-- the member stage and the embedding, and the tie from
-- `fst (branch ...)` to that term is NOT writable in the tree:
-- `ord-tri` is a well-founded induction
-- (src/L/Ordinal/Linear.lagda.md:136-137) and no row eliminates it.
-- That tie is this task's stated boundary, in the report.
--
--   Section 0.  The statement, imported from runs/W3.agda, which was
--               written first and typechecked alone.
--   Section 1.  THE VALUE EQUATION at the strictly infinite member
--               stage: the composed pair's projection, and the one
--               underlying-set row the obligation rests on.
--   Section 2.  THE OBLIGATION'S ASSEMBLY, both directions, from
--               the same formula.
--   Section 3.  THE OBLIGATION, top level, at every strictly
--               infinite member stage of the assembly.
--
-- CALIBER.  THE PROGRAM SET GHCRTS ON THIS PANE.  I DID NOT SET IT.
-- ONE AGDA PROCESS AT A TIME.

open import Base.Prelude
open import Base.Truth
open import Base.Classical using ( LEM )
open import Cubical.HITs.CumulativeHierarchy.Base using ( V; _∈_ )
open import Cubical.HITs.CumulativeHierarchy.Properties using ( ⟪_⟫ )
open import Cubical.HITs.CumulativeHierarchy.Constructions using ( module InfinitySet )
open import L.Constructible using ( IsOrd )
import Cubical.Data.Empty as Empty

module LJ-1-608.Probe608 {ℓ : Level} (lem : LEM (ℓ-suc ℓ))
  (α₀ : V ℓ) (oα₀ : IsOrd α₀)
  (sq : (δ : V ℓ) → ⟨ δ ∈ InfinitySet.sucV α₀ ⟩ → (⟨ δ ∈ InfinitySet.ω {ℓ} ⟩ → Empty.⊥)
      → Σ[ f ∈ (⟪ δ ⟫ × ⟪ δ ⟫ → ⟪ δ ⟫) ]
          ((x y : ⟪ δ ⟫ × ⟪ δ ⟫) → f x ≡ f y → x ≡ y)) where

open import V.Hierarchy {ℓ} using ( 𝒮ᵥ )
open import V.Presentation {ℓ} using ( member; fiber )
open import FOL.Syntax using ( Formula )
open import FOL.ZFStructure using ( module hPropStructure )
open import FOL.Absoluteness
open import L.Constructible {ℓ} using ( 𝒮ʟ; isL; isL-trans )
open Cubical.HITs.CumulativeHierarchy.Properties using ( ⟪_⟫↪ )
open InfinitySet {ℓ} using ( ω; sucV )
import L.StageCardinal

module SV = hPropStructure 𝒮ᵥ
module SL = hPropStructure 𝒮ʟ
open SV using ( _∈ˢ_ )
open SL using ( S )

module AbsL = FOL.Absoluteness.Single 𝒮ᵥ isL isL-trans
open AbsL renaming ( _⊨ᵐ_ to _⊨_ )

module SC = L.StageCardinal {ℓ} lem α₀ oα₀ sq
open SC using ( _↪_ )

-- SECTION 0.  THE STATEMENT, IMPORTED.
import LJ-1-608.runs.W3 {ℓ} lem α₀ oα₀ sq as W3


-- ===================================================================
-- SECTION 1.  THE VALUE EQUATION AT THE STRICTLY INFINITE MEMBER
--              STAGE.
--
--   The branch's value at a strictly infinite member stage is the
--   composed pair `comp-inj IHδ emb` (src/L/StageCardinal.lagda.md:
--   555-556).  1.1 reads the pair's function part by casing, the
--   campaign's discipline for projections of computed pairs.  1.2 is
--   the row the obligation rests on: the branch's value and the
--   member stage's own recursion value have the SAME UNDERLYING SET,
--   because the embedding's presentations sit over the same sets
--   (`fiber ... .snd`).  No row computes a `leastOf`, a tally, a
--   `defSet`, or any `sq`: the value equation is one fiber equation.
-- ===================================================================

-- 1.1  THE COMPOSED PAIR'S PROJECTION, BY CASING.
comp-fst : {A B C : Type ℓ} (g : A ↪ B) (h : B ↪ C) (j : A)
  → fst (SC.Upper.comp-inj g h) j ≡ fst h (fst g j)
comp-fst (f , _) (g , _) j = refl

module Rows
  (α : V ℓ) (oα : IsOrd α) (α∈suc : ⟨ α ∈ˢ sucV α₀ ⟩)
  (infα : ⟨ α ∈ˢ ω ⟩ → Empty.⊥)
  (IH : (δ : V ℓ) → ⟨ δ ∈ˢ α ⟩ → SC.Upper.P δ)
  (m : ⟪ α ⟫) (ω∈δ : ⟨ ω ∈ˢ (⟪ α ⟫↪ m) ⟩) where

  module AT = W3.Site.At α oα α∈suc infα IH m ω∈δ
  open AT

  -- 1.2  THE VALUE EQUATION, ONE FIBER ROW.  `fst (val x k)` is
  --      `⟪ α ⟫↪` of the branch's value at the member's
  --      presentation; `fst (valδ x k)` is `⟪ δ ⟫↪` of the member
  --      stage's own recursion value at the same presentation.  The
  --      embedding picks the α-presentation of the SAME set
  --      (src/L/StageCardinal.lagda.md:504-511), so the two sides
  --      are one `fiber α ... .snd` apart.
  val-eq : (x : S) (k : ⟨ fst x ∈ fst δL ⟩)
    → fst (val x k) ≡ fst (valδ x k)
  val-eq x k =
    cong (⟪ α ⟫↪)
      ( comp-fst IHδ (SC.Upper.Emb.emb α oα δ δ∈α) (W3.ixOf δL x k) )
    ∙ fiber α {x = ⟪ δ ⟫↪ (fst IHδ (W3.ixOf δL x k))}
        ( oα .fst (member δ (fst IHδ (W3.ixOf δL x k))) δ∈α ) .snd

  -- =================================================================
  -- SECTION 2.  THE OBLIGATION'S ASSEMBLY, BOTH DIRECTIONS.
  --
  --   The formula is the hypothesis's own ψ, VERBATIM.  `defines`
  --   transports along the value equation into the member stage's
  --   `defines`; `only` transports back along its sym.  THE TERM IS
  --   THE MEASUREMENT: the recursion at strictly infinite member
  --   stages has a graph exactly when the member stage's own
  --   recursion does, and it is the same formula.  The obligation
  --   itself is the top-level `rec-graph-at-infinite` below, which
  --   delegates here at the site the witness meter names.
  -- =================================================================
  the-graph : RecGraph∞
  the-graph G = ψ , (defines-side , only-side)
    where
    ψ : Formula S 2
    ψ = fst G
    IHd : (x y : S) (k : ⟨ fst x ∈ fst δL ⟩)
      → fst y ≡ fst (valδ x k) → ⟨ (y ∷ x ∷ []) ⊨ ψ ⟩
    IHd = fst (snd G)
    IHo : (x y : S) → ⟨ (y ∷ x ∷ []) ⊨ ψ ⟩
      → (k : ⟨ fst x ∈ fst δL ⟩) → fst y ≡ fst (valδ x k)
    IHo = snd (snd G)
    defines-side : (x y : S) (k : ⟨ fst x ∈ fst δL ⟩)
      → fst y ≡ fst (val x k) → ⟨ (y ∷ x ∷ []) ⊨ ψ ⟩
    defines-side x y k e = IHd x y k (e ∙ val-eq x k)
    only-side : (x y : S) → ⟨ (y ∷ x ∷ []) ⊨ ψ ⟩
      → (k : ⟨ fst x ∈ fst δL ⟩) → fst y ≡ fst (val x k)
    only-side x y sat k = IHo x y sat k ∙ sym (val-eq x k)


-- ===================================================================
-- SECTION 3.  THE OBLIGATION, AT EVERY STRICTLY INFINITE MEMBER
--              STAGE OF EVERY INFINITE STAGE OF THE ASSEMBLY.
--
--   The type is `W3.Site.At.RecGraph∞` at the site: given the member
--   stage's OWN graph in [LJ-1.597]'s `Graph` shape, the branch's
--   graph at that strictly infinite member stage exists, and it is
--   the SAME formula.  [LJ-1.601]'s sibling obligation
--   `finite-base-measured` is the other half of the same reading at
--   the finite member stages.
-- ===================================================================
rec-graph-at-infinite :
  (α : V ℓ) (oα : IsOrd α) (α∈suc : ⟨ α ∈ˢ sucV α₀ ⟩)
  (infα : ⟨ α ∈ˢ ω ⟩ → Empty.⊥)
  (IH : (δ : V ℓ) → ⟨ δ ∈ˢ α ⟩ → SC.Upper.P δ)
  (m : ⟪ α ⟫) (ω∈δ : ⟨ ω ∈ˢ (⟪ α ⟫↪ m) ⟩)
  → W3.Site.At.RecGraph∞ α oα α∈suc infα IH m ω∈δ
rec-graph-at-infinite α oα α∈suc infα IH m ω∈δ =
  Rows.the-graph α oα α∈suc infα IH m ω∈δ
