{-# OPTIONS --cubical --safe --guardedness #-}

-- [LJ-1.656] PROBE, PART B.  WHERE THE OTHER TWO COMPONENTS OF
--            `LevelFormula` ACTUALLY LIVE.
--
--   IT SITS UNDER `runs/` ON PURPOSE.  The brief's write scope names
--   `agents/tasks/LJ-1-656/Probe656.agda` and
--   `agents/tasks/LJ-1-656/runs/`, and it names no second probe at the
--   task home's top level.  Rather than write outside the scope the
--   brief declared, part B is inside the directory the scope grants.
--   `[LJ-1.650]` set the precedent for a real, tracked, typechecking
--   Agda file under `runs/` (its `runs/W3.agda` and `runs/Floor650.agda`).
--
--   Part A is `Probe656.agda` and this file imports it.  ONE link, not
--   six: [LJ-1.650] measured the six-link LJ chain dead at the wide
--   caliber (agents/tasks/LJ-1-650/lj-1.650-report.md:59-67), and this
--   import is inside the same task home.
--
--   WHAT THIS FILE PROVES.  The passage between the stage's inner world
--   and the class carrier is an EQUALITY of truth values, so the two
--   satisfaction rows part A section 4 left open are rows at the CLASS
--   carrier and the stage does not appear in either.
--
--   Nothing is postulated.  No hole.  Nothing lands in src/.
--   ONE Agda process, caliber from the pane, never set here.

open import Base.Prelude
open import Base.Truth
open import Base.Classical using ( LEM )

module LJ-1-656.runs.Probe656B {ℓ : Level} (lem : LEM (ℓ-suc ℓ)) where

open import FOL.ZFStructure using ( module hPropStructure )
open import FOL.Syntax using ( Formula; var; _≐_; _∧̇_; ∃̇_ )
open import FOL.LevyHierarchy using ( Δ₀ )
open import FOL.Manipulation.Relabelling using ( embed; mapΔ₀ )
open import FOL.Manipulation.Renaming using ( renameFo; module Sat )
open import V.Hierarchy {ℓ} using ( 𝒮ᵥ )
open import L.Constructible {ℓ}
  using ( 𝒮ʟ; isL; isL-trans; IsOrd; Lset; 𝒟ₒ; Lset-out )
open import L.Ordinal {ℓ} using ( mem-ord )
open import L.Axioms.Basic {ℓ} using ( 𝒟ₒ→isL )
open import L.BoundedSubset {ℓ} lem
  using ( module HullStage; module LevelHood0; module Amb )
open import Cubical.HITs.CumulativeHierarchy.Constructions
  using ( ∅; module InfinitySet )
open import Cubical.Data.Sigma using ( _×_ )
open import Cubical.Data.Vec using ( Vec; _∷_; []; map )
open import Cubical.HITs.CumulativeHierarchy.Base using ( _∈_ )
import Cubical.Data.Empty as Empty
import Cubical.HITs.PropositionalTruncation as PT
open PT using ( ∥_∥₁; ∣_∣₁ )
open InfinitySet {ℓ} using ( sucV )
import FOL.Absoluteness

import LJ-1-656.Probe656 {ℓ} lem as A

open TruthAlgebra (hPropAlgebra (ℓ-suc ℓ))
module SV = hPropStructure 𝒮ᵥ
module CS = hPropStructure 𝒮ʟ
module AbsLC = FOL.Absoluteness.Single 𝒮ᵥ isL isL-trans
open SV using ( _∈ˢ_ )

module LH0 = LevelHood0
  zero zero zero zero zero zero zero zero zero zero zero zero zero zero
  zero zero zero zero zero zero zero zero zero zero zero zero zero zero

module FrameB (lam : SV.S) (ordλ : IsOrd lam)
              (succλ : (d : SV.S) → ⟨ d ∈ˢ lam ⟩ → ⟨ sucV d ∈ˢ lam ⟩)
              (X : SV.S)
              (X⊆Lλ : (z : SV.S) → ⟨ z ∈ˢ X ⟩ → ⟨ z ∈ˢ Lset lam ⟩)
              (∅∈λ : ⟨ ∅ ∈ˢ lam ⟩) where

  module F = A.Frame lam ordλ succλ X X⊆Lλ ∅∈λ
  module HS = HullStage lam ordλ succλ X X⊆Lλ ∅∈λ
  module T = HS.H.T
  open T using ( Code; val; _⊨c_ )
  -- ===================================================================
  -- SECTION 6.  WHERE THE OTHER TWO COMPONENTS ACTUALLY LIVE.
  --
  --   THE STAGE COSTS NOTHING.  Both rows of section 4 are rows at the
  --   CLASS carrier, and the passage between the two carriers is an
  --   EQUALITY of truth values, not an implication with a price.  The
  --   reason is one sentence: the matrix is Δ₀ (`A.Δ₀-matrix₀`), the
  --   witnesses the two outer existentials produce at the stage ARE
  --   members of the stage, and the stage is a transitive subclass of
  --   `L`.  `abs₀` (src/FOL/Absoluteness.lagda.md:122-124) then reads
  --   the same truth value at both carriers through the ambient one.
  -- ===================================================================

  module AbsS = HS.ASt.AbsL
  module RenS = Sat (hPropAlgebra (ℓ-suc ℓ)) AbsS.𝒮M val

  -- 6.1  THE STAGE LIES IN `L`.  `Lset-out` names the level a member
  -- appears at, `mem-ord` makes that level an ordinal, and `𝒟ₒ→isL`
  -- (src/L/Axioms/Basic.lagda.md:98) closes it.
  stage⊆L : (x : SV.S) → ⟨ x ∈ˢ Lset lam ⟩ → ⟨ isL x ⟩
  stage⊆L x x∈ = PT.rec (snd (isL x)) go (Lset-out lam x x∈)
    where
    go : Σ[ δ ∈ SV.S ] (⟨ δ ∈ˢ lam ⟩ × ⟨ x ∈ˢ 𝒟ₒ (Lset δ) ⟩) → ⟨ isL x ⟩
    go (δ , δ∈ , x∈𝒟) = 𝒟ₒ→isL δ (mem-ord {A = lam} ordλ δ δ∈) x x∈𝒟

  toC : HS.ASt.SL → CS.S
  toC a = fst a , stage⊆L (fst a) (snd a)

  fst-toC : ∀ {n} (δ : Vec HS.ASt.SL n) → map fst (map toC δ) ≡ map fst δ
  fst-toC [] = refl
  fst-toC (a ∷ δ) = cong (fst a ∷_) (fst-toC δ)

  -- 6.2  THE Δ₀ PASSAGE, AN EQUALITY AND NOT AN IMPLICATION.
  Δ₀-stage≡class : ∀ {n} (ψ : Formula (⊥* {ℓ-suc ℓ}) n) → Δ₀ ψ
                 → (δ : Vec HS.ASt.SL n)
                 → (δ AbsS.⊨ᵐ (embed ψ))
                   ≡ ((map toC δ) AbsLC.⊨ᵐ (embed ψ))
  Δ₀-stage≡class ψ dψ δ =
      AbsS.abs₀ (mapΔ₀ Empty.rec* dψ) δ
    ∙ A.Alphabet.irrel 𝒮ᵥ fst fst ψ (map fst δ)
    ∙ cong (λ e → e AbsLC.⊨ᵛ (embed ψ)) (sym (fst-toC δ))
    ∙ sym (AbsLC.abs₀ (mapΔ₀ Empty.rec* dψ) (map toC δ))

  -- 6.3  THE PEELING.  `F.lv` at the stage, opened to the matrix at the
  -- environment `u ∷ v ∷ γ ∷ K` the tree states the matrix at
  -- (src/L/BoundedSubset.lagda.md:69-71).
  agrees-rot : (K v γ : HS.ASt.SL)
             → RenS.Agrees A.rot (K ∷ v ∷ γ ∷ []) (v ∷ γ ∷ K ∷ [])
  agrees-rot K v γ zero             = refl
  agrees-rot K v γ (suc zero)       = refl
  agrees-rot K v γ (suc (suc zero)) = refl

  -- one step of the peel: the renamed body at the rotated environment.
  -- GENERIC IN THE FORMULA (law P-l): `⊨-rename` is defined by
  -- recursion on the formula, so applying it to a NAMED tree recurses
  -- over that tree, and applying it to a variable does not.
  peel-rot-gen : (φ : Formula Code 3) (K v γ : HS.ASt.SL)
               → ((K ∷ v ∷ γ ∷ []) ⊨c (renameFo A.rot φ))
                 ≡ ((v ∷ γ ∷ K ∷ []) ⊨c φ)
  peel-rot-gen φ K v γ =
    RenS.⊨-rename A.rot φ
      (K ∷ v ∷ γ ∷ []) (v ∷ γ ∷ K ∷ []) (agrees-rot K v γ)

  peel-rot : (K v γ : HS.ASt.SL)
           → ((K ∷ v ∷ γ ∷ []) ⊨c (renameFo A.rot (∃̇ (embed A.matrix₀))))
             ≡ ((v ∷ γ ∷ K ∷ []) ⊨c (∃̇ (embed A.matrix₀)))
  peel-rot = peel-rot-gen (∃̇ (embed A.matrix₀))

  -- the alphabet step, at the STAGE's own structure: `⊨c` reads the
  -- codes and `AbsS.⊨ᵐ` reads the stage's own members, and on a
  -- parameter-free formula the two readings are one.
  code≡id : ∀ {n} (ψ : Formula (⊥* {ℓ-suc ℓ}) n) (δ : Vec HS.ASt.SL n)
          → (δ ⊨c (embed ψ)) ≡ (δ AbsS.⊨ᵐ (embed ψ))
  code≡id ψ δ = A.Alphabet.irrel AbsS.𝒮M val (λ (a : HS.ASt.SL) → a) ψ δ

  -- 6.4  THE CLASS-CARRIER ROW THAT IS NOT DELIVERED.
  --
  --   `GraphAgree` is [LJ-1.52]'s hypothesis, restated at TODAY's slot
  --   roles by [LJ-1.570] (agents/tasks/LJ-1-570/Probe570.agda:286-292)
  --   and named there "THE ONE SYNTACTIC ROW THAT IS NOT DELIVERED".
  --   It is restated here verbatim, and it is a hypothesis here too.
  -- MEASURED, AND THE TREE MEASURED IT FIRST.  The row [LJ-1.52] and
  -- [LJ-1.570] state names `LsetGraphAt` IN ITS TYPE, and naming the
  -- graph in a type is the expensive move this chapter already priced:
  -- "Letting the pair graph enter as a VARIABLE carrying its own
  -- equation, rather than as the closed sentence it will be
  -- instantiated to, is worth 85 seconds" (src/L/Hierarchy.lagda.md:685,
  -- the recap).  This probe met the same wall and it was not 85 seconds:
  -- with `LsetGraphAt` in two types the file was KILLED, runs/p-13.out,
  -- EXIT=137 (SIGKILL), after runs/p-10.out spent 442.52 s to reach one
  -- unsolved meta.  The restructuring is below and it is the whole
  -- difference.
  --
  -- `GraphDecode` FOLDS `ride-only` INTO THE ROW.  `ride-only` is
  -- delivered (src/L/Condensation.lagda.md:422-425), and composing it
  -- with the row removes the graph from every type in this file.  The
  -- content is unchanged: `decode-from-agree` below is that composition
  -- and it names the graph EXACTLY ONCE.
  -- THE ROW IS STATED AT THE MATRIX, NOT AT THE GRAPH, and that is a
  -- MEASURED restructuring.  The row [LJ-1.52] and [LJ-1.570] state
  -- names `LsetGraphAt` in its type, and naming the graph in a type is
  -- the expensive move that chapter already priced at 85 seconds
  -- (src/L/Hierarchy.lagda.md, the recap).  With it in two types this
  -- probe was KILLED (runs/p-13.out, runs/p-14.out, EXIT=137).
  --
  -- `MatrixDecode` is one link BELOW that row and it is where this
  -- reduction actually bites: [LJ-1.570]'s `matrix-decode`
  -- (agents/tasks/LJ-1-570/Probe570.agda:300-322) is exactly the proof
  -- of `GraphAgree → MatrixDecode`, and it is delivered there, at
  -- today's tree, green.  This file does not reprove it and does not
  -- name the graph.
  MatrixDecode : Type (ℓ-suc ℓ)
  MatrixDecode =
    (u v γ K : CS.S) (oγ : IsOrd (fst γ))
    → ⟨ (u ∷ v ∷ γ ∷ K ∷ []) AbsLC.⊨ᵐ (embed A.matrix₀) ⟩
    → fst v ≡ Lset (fst γ)

  -- and the row at the tree's OWN spelling reaches it, by the one read
  -- lemma of part A's seal.
  matrixDecode-from-tree :
      ((u v γ K : CS.S) → IsOrd (fst γ)
       → ⟨ (u ∷ v ∷ γ ∷ K ∷ []) AbsLC.⊨ᵐ LH0.matrix ⟩
       → fst v ≡ Lset (fst γ))
    → MatrixDecode
  matrixDecode-from-tree f u v γ K oγ h =
    f u v γ K oγ
      (subst (λ e → ⟨ (u ∷ v ∷ γ ∷ K ∷ []) AbsLC.⊨ᵐ e ⟩) A.matrix₀-inv h)

  -- ===================================================================
  -- SECTION 6.5.  THE OBLIGATION, FROM TWO CLASS-CARRIER ROWS AND
  --               NOTHING ELSE.
  --
  --   `matrix-bridge` and `ord-bridge` are EQUALITIES, so they are spent
  --   in both directions and neither costs a hypothesis.  What is left
  --   is `GraphAgree` (the soundness row, [LJ-1.52]'s, unbuilt) and
  --   `ClassWitness` (the completeness row).  **THE STAGE IS NOT IN
  --   EITHER OF THEM.**
  -- ===================================================================

  matrix-bridge : (u v γ K : HS.ASt.SL)
    → ((u ∷ v ∷ γ ∷ K ∷ []) ⊨c (embed A.matrix₀))
      ≡ ((toC u ∷ toC v ∷ toC γ ∷ toC K ∷ []) AbsLC.⊨ᵐ (embed A.matrix₀))
  matrix-bridge u v γ K =
      code≡id A.matrix₀ (u ∷ v ∷ γ ∷ K ∷ [])
    ∙ Δ₀-stage≡class A.matrix₀ A.Δ₀-matrix₀ (u ∷ v ∷ γ ∷ K ∷ [])


  ord-bridge : (v γ : HS.ASt.SL)
    → ((v ∷ γ ∷ []) ⊨c (embed A.ordAt1))
      ≡ ((fst v ∷ fst γ ∷ []) Amb.⊨ₚ A.ordAt1)
  ord-bridge v γ =
      code≡id A.ordAt1 (v ∷ γ ∷ [])
    ∙ AbsS.abs₀ (mapΔ₀ Empty.rec* A.Δ₀-ordAt1) (v ∷ γ ∷ [])
    ∙ A.Alphabet.toAmb 𝒮ᵥ (λ (a : HS.ASt.SL) → fst a) A.ordAt1
        (fst v ∷ fst γ ∷ [])

  stage-sound-from-agree : MatrixDecode → F.StageSound
  stage-sound-from-agree ga v γ h =
    PT.rec (SV.isSetS (fst v) (Lset (fst γ))) outer (h .fst)
    where
    oγ : IsOrd (fst γ)
    oγ = A.ordAt1-out (fst v) (fst γ) (subst ⟨_⟩ (ord-bridge v γ) (h .snd))

    inner : (K : HS.ASt.SL)
          → Σ[ u ∈ HS.ASt.SL ] ⟨ (u ∷ v ∷ γ ∷ K ∷ []) ⊨c (embed A.matrix₀) ⟩
          → fst v ≡ Lset (fst γ)
    inner K (u , hu) =
      ga (toC u) (toC v) (toC γ) (toC K) oγ
        (subst ⟨_⟩ (matrix-bridge u v γ K) hu)

    outer : Σ[ K ∈ HS.ASt.SL ]
              ⟨ (K ∷ v ∷ γ ∷ []) ⊨c (renameFo A.rot (∃̇ (embed A.matrix₀))) ⟩
          → fst v ≡ Lset (fst γ)
    outer (K , hK) =
      PT.rec (SV.isSetS (fst v) (Lset (fst γ))) (inner K)
        (subst ⟨_⟩ (peel-rot K v γ) hK)

  -- LAW P-l, APPLIED PROPERLY, AND IT IS THE THIRD MEASUREMENT OF IT IN
  -- THIS TASK.  The two lemmas below keep the VALUE SLOT A VARIABLE and
  -- are instantiated at `F.levelOf` exactly once, in one application.
  -- Written with `F.levelOf γ oγ` inside them instead, the completeness
  -- half ran to 1,533,575,168 bytes and was killed
  -- (runs/pb-10.out), while the IDENTICAL construction over a variable
  -- value slot costs what the rest of the file costs.  Sealing
  -- `levelOf` in part A cut the time (229.22 s to 63.74 s,
  -- runs/pb-8.out against runs/pb-10.out) and did NOT cut the peak; only
  -- keeping the construction out of the lemma did.

  complete-at : (v γ : HS.ASt.SL)
              → ∥ Σ[ K ∈ HS.ASt.SL ] Σ[ u ∈ HS.ASt.SL ]
                   ⟨ (toC u ∷ toC v ∷ toC γ ∷ toC K ∷ [])
                       AbsLC.⊨ᵐ (embed A.matrix₀) ⟩ ∥₁
              → ⟨ (v ∷ γ ∷ []) ⊨c A.levelFo (embed A.matrix₀) ⟩
  complete-at v γ =
    PT.rec (snd ((v ∷ γ ∷ []) ⊨c A.levelFo (embed A.matrix₀))) mk
    where
    inner : (K u : HS.ASt.SL)
          → ⟨ (toC u ∷ toC v ∷ toC γ ∷ toC K ∷ [])
                AbsLC.⊨ᵐ (embed A.matrix₀) ⟩
          → ⟨ (u ∷ v ∷ γ ∷ K ∷ []) ⊨c (embed A.matrix₀) ⟩
    inner K u hc = subst ⟨_⟩ (sym (matrix-bridge u v γ K)) hc

    step : (K u : HS.ASt.SL)
         → ⟨ (toC u ∷ toC v ∷ toC γ ∷ toC K ∷ [])
               AbsLC.⊨ᵐ (embed A.matrix₀) ⟩
         → ⟨ (v ∷ γ ∷ K ∷ []) ⊨c (∃̇ (embed A.matrix₀)) ⟩
    step K u hc = ∣ u , inner K u hc ∣₁

    mid : (K : HS.ASt.SL)
        → ⟨ (v ∷ γ ∷ K ∷ []) ⊨c (∃̇ (embed A.matrix₀)) ⟩
        → ⟨ (K ∷ v ∷ γ ∷ []) ⊨c (renameFo A.rot (∃̇ (embed A.matrix₀))) ⟩
    mid K h = subst ⟨_⟩ (sym (peel-rot K v γ)) h

    mk : Σ[ K ∈ HS.ASt.SL ] Σ[ u ∈ HS.ASt.SL ]
           ⟨ (toC u ∷ toC v ∷ toC γ ∷ toC K ∷ [])
               AbsLC.⊨ᵐ (embed A.matrix₀) ⟩
       → ⟨ (v ∷ γ ∷ []) ⊨c A.levelFo (embed A.matrix₀) ⟩
    mk (K , u , hc) = ∣ K , mid K (step K u hc) ∣₁

  ord-at : (v γ : HS.ASt.SL) → IsOrd (fst γ) → fst v ≡ Lset (fst γ)
         → ⟨ (v ∷ γ ∷ []) ⊨c (embed A.ordAt1) ⟩
  ord-at v γ oγ q =
    subst ⟨_⟩ (sym (ord-bridge v γ))
      (subst (λ z → ⟨ (z ∷ fst γ ∷ []) Amb.⊨ₚ A.ordAt1 ⟩) (sym q)
             (A.ordAt1-in (Lset (fst γ)) (fst γ) oγ))

  ClassWitness : Type (ℓ-suc ℓ)
  ClassWitness = (γ : HS.ASt.SL) (oγ : IsOrd (fst γ))
    → ∥ Σ[ K ∈ HS.ASt.SL ] Σ[ u ∈ HS.ASt.SL ]
         ⟨ (toC u ∷ toC (F.levelOf γ oγ) ∷ toC γ ∷ toC K ∷ [])
             AbsLC.⊨ᵐ (embed A.matrix₀) ⟩ ∥₁

  stage-complete-from-witness : ClassWitness → F.StageComplete
  stage-complete-from-witness cw γ oγ =
      complete-at (F.levelOf γ oγ) γ (cw γ oγ)
    , ord-at (F.levelOf γ oγ) γ oγ (F.levelOf-fst γ oγ)

  -- THE HEADLINE.  TWO CLASS-CARRIER ROWS, AND THE OBLIGATION FOLLOWS.
  level-formula-from-class : MatrixDecode → ClassWitness → F.LevelFormula
  level-formula-from-class ga cw =
    F.level-formula-from-rows (stage-sound-from-agree ga)
                              (stage-complete-from-witness cw)
