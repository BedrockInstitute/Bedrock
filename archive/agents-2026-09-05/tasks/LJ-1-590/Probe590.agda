{-# OPTIONS --cubical --safe --guardedness #-}

-- [LJ-1.590]  StageOfCode, row 2's reflection step.
--
-- SECTION 1 is W3, written first and typechecked ALONE at
--   agents/tasks/LJ-1-590/runs/W3.agda (exit 0, runs/w3-1.out).
-- SECTION 2 is the D-10 the brief ordered before any Agda: does
--   [LJ-1.560]'s obligation apply here?  IT DOES NOT, and the
--   difference is written as a TYPE and not as a sentence.
-- SECTION 3 is THE OBLIGATION.  `stage-of-code` is inhabited, and it
--   is an INSTANTIATION of `L.Stage.leastOrd` and of nothing else.
-- SECTION 4 is what the obligation buys, and what row 2 still costs.
--
-- Nothing is postulated.  Nothing lands in src/.  No hole.
--
-- CALIBER.  The program set GHCRTS="-A64m -I0 -M8g" on this pane.  I
-- did not set it.  One Agda process at a time.

open import Base.Prelude
open import Base.Truth
open import Base.Classical using ( LEM )

module LJ-1-590.Probe590 {ℓ : Level} (lem : LEM (ℓ-suc ℓ)) where

open import FOL.ZFStructure using ( module hPropStructure )
open import FOL.Syntax using ( Formula; ∃̇_ )
import FOL.Absoluteness
open import V.Hierarchy {ℓ} using ( 𝒮ᵥ )
open import L.Constructible {ℓ}
  using ( 𝒮ʟ; isL; isL-trans; IsOrd; isPropIsOrd )
open import L.Cardinal {ℓ} lem using ( _↪_; InjCode )
open import L.GCH {ℓ} lem using ( InjL )
open import L.Reflect {ℓ} lem using ( Below; Wit; SatEx; module Single )
open import L.Stage {ℓ} lem using ( isLeastOrd; leastOrd )

-- [LJ-1.583]'s OWN TERMS.  The narrowed gap, the selection at an
-- arbitrary stage, and the truncated existence are its file's and are
-- not copied here.
open import LJ-1-583.Probe583 {ℓ} lem
  using ( StageOfCode; stage-of-code-truncated; module CodeSelectAt )

open import Cubical.HITs.CumulativeHierarchy.Base using ( V )
open import Cubical.HITs.CumulativeHierarchy.Properties using ( ⟪_⟫ )
open import Cubical.Foundations.HLevels using ( isPropΣ )
import Cubical.HITs.PropositionalTruncation as PT
open PT using ( ∥_∥₁; squash₁ )

open TruthAlgebra (hPropAlgebra (ℓ-suc ℓ))
open hPropStructure 𝒮ʟ using ( S )

module AbsL = FOL.Absoluteness.Single 𝒮ᵥ isL isL-trans
open AbsL renaming ( _⊨ᵐ_ to _⊨_ )

-- =====================================================================
-- SECTION 1.  W3.  TYPED ALONE FIRST, RESTATED HERE SO THIS FILE
-- STANDS ON ITS OWN.
--
--   1a is [LJ-1.560]'s obligation re-ascribed here.
--   1b is the shape `StageOfCode` asks for, with the predicate left
--      abstract: AN ORDINAL AS DATA OUT OF A TRUNCATED EXISTENCE OF
--      ONE.  1a and 1b are not the same shape and section 2 says why.
-- =====================================================================

-- 1a.  agents/tasks/LJ-1-560/Probe560.agda:165-176, re-ascribed.  The
--      term is `Single.reflect`'s bundle and is not rebuilt.
SearchBoundsHere : Type (ℓ-suc ℓ)
SearchBoundsHere =
  {k : ℕ} (ψ : Formula S (suc k))
  → Σ[ β ∈ V ℓ ] Σ[ oβ ∈ IsOrd β ]
      ((ρ : S ^ k) → Below β ρ → ⟨ ρ ⊨ (∃̇ ψ) ⟩ → ⟨ Wit ψ ρ β ⟩)

search-bounds-here : SearchBoundsHere
search-bounds-here ψ = Single.βω ψ , Single.L.top-ord ψ , Single.closed ψ

-- 1b.  `StageOfCode`'s shape, predicate abstract.  NO formula, NO
--      environment, NO `Below`.
StageShape : Type (ℓ-suc (ℓ-suc ℓ))
StageShape = (P : V ℓ → Ω)
           → ∥ (Σ[ α ∈ V ℓ ] (IsOrd α × ⟨ P α ⟩)) ∥₁
           → Σ[ α ∈ V ℓ ] Σ[ _ ∈ IsOrd α ] ⟨ P α ⟩

-- AND THE TREE HAS 1b ALREADY.  src/L/Stage.lagda.md:149-153.
stage-shape : StageShape
stage-shape P h = ℓo .fst , ℓo .snd .fst , ℓo .snd .snd .fst
  where
  ℓo : Σ[ α ∈ V ℓ ] (IsOrd α × ⟨ P α ⟩ × isLeastOrd P α)
  ℓo = leastOrd P h

-- =====================================================================
-- SECTION 2.  THE D-10.  [LJ-1.560]'s OBLIGATION DOES NOT APPLY, AND
-- THE DIFFERENCE IS NOT "BOUNDING A SEARCH VERSUS BOUNDING A CODE".
--
--   THE BRIEF EXPECTED THAT DISTINCTION AND IT IS NOT THE ONE MEASURED
--   HERE.  Read 1a's type.  Two things stand between it and 1b, and
--   both are about the ARGUMENT `search-bounds` takes, not about what
--   its conclusion bounds.
--
--   DIFFERENCE 1.  `search-bounds` IS INDEXED ON A FORMULA AND ON
--   NOTHING ELSE.  Its beta is `Single.betaomega psi`
--   (agents/tasks/LJ-1-560/Probe560.agda:172), a function of psi alone.
--   `StageOfCode`'s beta must be a function of `a` and `b`
--   (agents/tasks/LJ-1-583/Probe583.agda:259-262), and [LJ-1.583]
--   measured exactly that when it refused `SiteBound`: "the bound the
--   code needs is a function of a AND b, and the bound `CodeSelect`
--   offers is a function of a alone" (Probe583.agda:218-220).  Feeding
--   `a` and `b` in as PARAMETERS does not repair this: parameters ride
--   in `rho`, and beta is chosen before `rho` is seen.
--
--   DIFFERENCE 2.  AND THAT IS WHY 1a CHARGES `Below beta rho`
--   (src/L/Reflect.lagda.md:253-254).  Because beta did not read the
--   parameters, the caller must prove they are already inside it.
--   `StageOfCode` gives no such hypothesis and cannot: `a` and `b` are
--   arbitrary L-sets.  `mkReflect` (src/L/ReflectFo.lagda.md:525) is
--   the tree's repair for exactly this and it takes ONE prescribed
--   ordinal, not two arbitrary L-sets.
--
--   DIFFERENCE 3, AND IT IS THE ONE THAT ENDS IT.  1a's conclusion is
--   about an OBJECT-LANGUAGE formula read by the inner satisfaction.
--   `InjCode F a b` (src/L/Cardinal.lagda.md:223-224) is a META-LEVEL
--   hProp.  To reach 1a at all one must first internalize `InjCode` as
--   a `Formula S 3` and prove the two agree.  THE TYPE BELOW IS THAT
--   PRICE, WRITTEN DOWN AND **NOT INHABITED**.
--
--   SO THE ANSWER TO THE BRIEF'S QUESTION IS NO.  Section 3 says what
--   applies instead, and it is one layer BELOW the reflection chapter:
--   `L.Reflect` itself imports `leastOrd` from `L.Stage`
--   (src/L/Reflect.lagda.md:54) and spends it pointwise at
--   src/L/Reflect.lagda.md:176.  The reflection chapter's LADDER is
--   what does not transfer.  Its DESCENT is what this task needed, and
--   the descent was never the reflection chapter's own.
-- =====================================================================

-- NOT INHABITED.  The price of reaching `search-bounds` from here.
ViaSearchBounds : Type (ℓ-suc ℓ)
ViaSearchBounds =
  (a b : S)
  → Σ[ ψ ∈ Formula S 3 ]
      ( ((F : S) → ⟨ (F ∷ a ∷ b ∷ []) ⊨ ψ ⟩ → InjCode F a b)
      × ((F : S) → InjCode F a b → ⟨ (F ∷ a ∷ b ∷ []) ⊨ ψ ⟩)
      × Below (Single.βω ψ) (a ∷ b ∷ []) )

-- =====================================================================
-- SECTION 3.  THE OBLIGATION.
--
--   `StageOfCode` (agents/tasks/LJ-1-583/Probe583.agda:259-262) is an
--   INSTANTIATION of `L.Stage.leastOrd` at one predicate on ordinals.
--   NOTHING IS ASSUMED.  No choice principle is added, no postulate,
--   no hole.  The excluded middle is the module's own hypothesis and
--   is the one `leastOrd` already spends (src/L/Stage.lagda.md:137).
--
--   WHY IT WORKS, IN ONE SENTENCE.  [LJ-1.583] proved the truncated
--   form (Probe583.agda:269-274) and named the gap as the truncation
--   boundary: "The Sigma is not a proposition, so the beta cannot leave
--   the truncation" (Probe583.agda:266-267).  THAT SENTENCE IS TRUE OF
--   AN ARBITRARY BETA AND FALSE OF THE LEAST ONE.  `BoundedCodeAt` is
--   a proposition, `IsOrd` is a proposition (src/L/Constructible.lagda
--   .md:144), so the pair below is a proposition; the LEAST ordinal
--   carrying a propositional property is unique by trichotomy
--   (src/L/Stage.lagda.md:94-109), so the Sigma over the least one IS
--   a proposition and the truncation lifts.
-- =====================================================================

-- The predicate on ordinals.  hProp-valued, and that is the whole
-- content: a Sigma of a proposition over a proposition.
CodeAt : (a b : S) → V ℓ → Ω
CodeAt a b σ =
    (Σ[ oσ ∈ IsOrd σ ] CodeSelectAt.BoundedCodeAt σ oσ a b)
  , isPropΣ (isPropIsOrd σ) (λ _ → squash₁)

-- Its truncated existence is [LJ-1.583]'s term, repacked and not
-- reproved (Probe583.agda:269-274).
code-somewhere : (a b : S) → InjL a b
               → ∥ (Σ[ α ∈ V ℓ ] (IsOrd α × ⟨ CodeAt a b α ⟩)) ∥₁
code-somewhere a b h = PT.map
  (λ { (β , (oβ , bc)) → β , (oβ , (oβ , bc)) })
  (stage-of-code-truncated a b h)

-- THE OBLIGATION.
stage-of-code : StageOfCode
stage-of-code a b h = sh .fst , sh .snd .snd .fst , sh .snd .snd .snd
  where
  sh = stage-shape (CodeAt a b) (code-somewhere a b h)

-- =====================================================================
-- SECTION 4.  WHAT THIS BUYS, AND WHAT ROW 2 STILL COSTS.
--
--   THE BRIEF SAYS: "Do not read a discharge into anything you did not
--   inhabit."  Everything in this section is a composition of terms
--   that typecheck in this file or in a predecessor's, and nothing
--   else is claimed.
-- =====================================================================

-- 4a.  THE TRUNCATION ESCAPE, WHICH IS WHAT ROW 2 WANTED THE STAGE
--      FOR.  `InjL a b` is a truncation (src/L/GCH.lagda.md:37-38).
--      Out of it, a code AS DATA.  `bare-code` is [LJ-1.583]'s
--      (Probe583.agda:251-252) and `stage-of-code` is section 3's.
bare-code-of : (a b : S) → InjL a b → Σ[ F ∈ S ] InjCode F a b
bare-code-of a b h = CodeSelectAt.bare-code β oβ a b bc
  where
  soc = stage-of-code a b h
  β = soc .fst
  oβ = soc .snd .fst
  bc = soc .snd .snd

-- 4b.  AND THE SAME, READ AS AN INJECTION.  `bare-inj` is
--      [LJ-1.583]'s (Probe583.agda:254-255).
bare-inj-of : (a b : S) → InjL a b → ⟪ fst a ⟫ ↪ ⟪ fst b ⟫
bare-inj-of a b h = CodeSelectAt.bare-inj β oβ a b bc
  where
  soc = stage-of-code a b h
  β = soc .fst
  oβ = soc .snd .fst
  bc = soc .snd .snd

-- 4c.  WHAT IS **NOT** HERE.  `SquareCoded`
--      (agents/tasks/LJ-1-583/Probe583.agda:195-196) is row 2's other
--      open item and [LJ-1.591] asks about it.  AD12 gives this brief
--      one obligation, and this file does not touch it.  Nothing above
--      supplies a coded factor at the square, and no reader may take
--      one from here.
