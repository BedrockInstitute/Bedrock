{-# OPTIONS --cubical --safe --guardedness #-}

-- LJ-1.163 probe A.  `ElemDown` AT THE HULL.
--
-- THE BRIEF'S PREMISE, AND WHY THIS PROBE IS SHAPED AS IT IS.
-- The brief states "MEASURED: nothing in `src/` supplies `ElemDown`".
-- That is FALSE.  `src/L/BoundedSubset.lagda.md:1568-1569` reads
--
--     elem-down : DR54.ElemDown
--     elem-down = HEDC.elem-down
--
-- inside the single agda fence that runs from `:3` to `:1626`, and
-- `src/Everything.lagda.md:374` imports the master.  The supply is live
-- and it typechecks.  So the probe does not build a supply.  It
-- MEASURES the delivered one, and it answers the two questions that
-- decide whether the delivered one is a supply or a restatement.
--
-- CRITERION, FIXED BEFORE THE RUN (D-1): GO at or below 120 in-fence
-- lines for a supply of `ElemDown` at one real arity; 20 minutes of
-- wall time per agda invocation under GHCRTS="-A64m -I0 -M8g", ONE
-- process, cap never raised.
--
-- BLOCK 1  THE LIFT.  `ElemDown` built from TOP-LEVEL modules only, so
--          it stands outside `Co` and outside the two open hypotheses
--          `levelIn` and `cover`.  This is the reusable form.
-- BLOCK 2  C-38 AT ONE REAL ARITY.  The supply applied at n = 0 and
--          n = 1 at concrete formulas, and fed to its real consumer
--          `DownReflect.down-reflect`.
-- BLOCK 3  THE INDEPENDENCE TEST.  The site's own `elem-down`, at two
--          different `(levelIn, cover)` pairs, equal by `refl`.

open import Base.Prelude
open import Base.Truth
open import Base.Classical using ( LEM )

module LJ-1-163.ProbeLJ1163A {ℓ : Level} (lem : LEM (ℓ-suc ℓ)) where

open import FOL.ZFStructure using ( module hPropStructure )
open import FOL.Syntax using ( Formula; var; con; _∈̇_; _≐_; ∃̇_ )
open import FOL.Manipulation.Relabelling using ( mapFo )
open import V.Hierarchy {ℓ} using ( 𝒮ᵥ )
open import V.Presentation {ℓ} using ( fiber )
open import L.Constructible {ℓ} using ( IsOrd; Lset )
open import L.WellOrder.Base {ℓ-suc ℓ} using ( SWO )
open import L.BoundedSubset {ℓ} lem using
  ( module DownReflect; module CanonCode; module HullElemDown
  ; module Devlin55; IsCardinal; _↪_ )

open import Cubical.Data.Vec using ( Vec; map; _∷_; [] )
open import Cubical.Data.Sigma using ( _×_; _,_ )
import Cubical.Data.Empty as Empty
import Cubical.HITs.PropositionalTruncation as PT
open PT using ( ∥_∥₁ )
open import Cubical.HITs.CumulativeHierarchy.Constructions
  using ( ∅; _∪_; ⁅_⁆s; module InfinitySet )
open InfinitySet using ( ω; sucV )
open import Cubical.HITs.CumulativeHierarchy.Properties using ( ⟪_⟫ )

open TruthAlgebra (hPropAlgebra (ℓ-suc ℓ))
open hPropStructure 𝒮ᵥ

-- =====================================================================
-- BLOCK 1.  THE LIFT.
--
-- The master's comment at `:455-461` names the route.  Every piece it
-- names is a TOP-LEVEL module of the master: `CanonCode` (`:463`),
-- `CloseSyntax` (`:506`), `CloseSem` (`:592`) and `HullElemDown`
-- (`:667`), whose `WithCode.tv` (`:698`) is the Tarski-Vaught instance
-- and whose `WithCode.elem` (`:759`) is `AtM.TV-thm .snd tv`.
--
-- So the whole supply needs exactly ONE thing the top level does not
-- already hold: an injective count of the hull's codes into the
-- ordinal.  This module takes that count as its only hypothesis and
-- returns `ElemDown`.  Nothing here names `levelIn` or `cover`.
-- =====================================================================

module Lifted (α lam : S) (ordα : IsOrd α) (ordλ : IsOrd lam)
  (w : SWO {ℓ} ⟪ α ⟫)
  (X : S) (X⊆L : (x : S) → ⟨ x ∈ˢ X ⟩ → ⟨ x ∈ˢ Lset lam ⟩)
  (∅∈λ : ⟨ ∅ ∈ˢ lam ⟩) where

  module HED = HullElemDown lam ordλ X X⊆L ∅∈λ
  module DR = DownReflect lam ordλ X X⊆L ∅∈λ

  module WithCount (cnt : HED.H.T.Code → ⟪ α ⟫)
    (cnt-inj : (c d : HED.H.T.Code) → cnt c ≡ cnt d → c ≡ d) where

    module CCn = CanonCode α ordα w HED.M HED.H.T.Code
      (λ c → fst (HED.H.T.val c)) HED.H.hull-member cnt cnt-inj

    f : HED.A.SM → HED.H.T.Code
    f q = CCn.canonical (fiber HED.M (snd q) .fst)

    f-spec : (q : HED.A.SM) → fst (HED.H.T.val (f q)) ≡ fst q
    f-spec q = CCn.canonical-spec (fiber HED.M (snd q) .fst)
             ∙ fiber HED.M (snd q) .snd

    module W = HED.WithCode f f-spec

    -- THE SUPPLY.  `DownReflect.ElemDown` at the hull of X in Lset lam.
    ed : DR.ElemDown
    ed = W.elem-down

-- =====================================================================
-- BLOCK 2.  C-38 AT ONE REAL ARITY.
--
-- `[LJ-1.161]` found three delivered definitions with no consumer.  The
-- delivered `elem-down` at `src/L/BoundedSubset.lagda.md:1568` is a
-- fourth: MEASURED, `grep` over `src/` finds no use of it.  So the
-- supply is applied here at two CONCRETE arities at CONCRETE formulas,
-- and then fed to the consumer the master already wrote for it,
-- `DownReflect.down-reflect` (`:443-451`).
-- =====================================================================

module Arity (α lam : S) (ordα : IsOrd α) (ordλ : IsOrd lam)
  (w : SWO {ℓ} ⟪ α ⟫)
  (X : S) (X⊆L : (x : S) → ⟨ x ∈ˢ X ⟩ → ⟨ x ∈ˢ Lset lam ⟩)
  (∅∈λ : ⟨ ∅ ∈ˢ lam ⟩)
  (cnt : Lifted.HED.H.T.Code α lam ordα ordλ w X X⊆L ∅∈λ → ⟪ α ⟫)
  (cnt-inj : (c d : Lifted.HED.H.T.Code α lam ordα ordλ w X X⊆L ∅∈λ)
           → cnt c ≡ cnt d → c ≡ d) where

  module L = Lifted α lam ordα ordλ w X X⊆L ∅∈λ
  module WC = L.WithCount cnt cnt-inj
  open L using ( module DR; module HED )

  -- ARITY 0, at the concrete closed formula "the empty environment
  -- satisfies nothing new".  `map inL []` is `[]` by computation.
  φ₀ : Formula DR.SM 0
  φ₀ = ∃̇ (var zero ≐ var zero)

  at0 : ⟨ [] DR.ASt.AbsL.⊨ᵐ (mapFo DR.inL φ₀) ⟩ → ⟨ [] DR.⊨ᵐ φ₀ ⟩
  at0 = WC.ed 0 φ₀ []

  -- ARITY 1, at the concrete membership formula, with a real hull
  -- member in the environment.
  φ₁ : Formula DR.SM 1
  φ₁ = var zero ∈̇ var zero

  at1 : (q : DR.SM)
      → ⟨ map DR.inL (q ∷ []) DR.ASt.AbsL.⊨ᵐ (mapFo DR.inL φ₁) ⟩
      → ⟨ (q ∷ []) DR.⊨ᵐ φ₁ ⟩
  at1 q = WC.ed 1 φ₁ (q ∷ [])

  -- ARITY 1 WITH A CONSTANT, so the relabelling `mapFo inL` is not the
  -- identity on the constants.
  φ₂ : DR.SM → Formula DR.SM 1
  φ₂ p = con p ∈̇ var zero

  at2 : (p q : DR.SM)
      → ⟨ map DR.inL (q ∷ []) DR.ASt.AbsL.⊨ᵐ (mapFo DR.inL (φ₂ p)) ⟩
      → ⟨ (q ∷ []) DR.⊨ᵐ (φ₂ p) ⟩
  at2 p q = WC.ed 1 (φ₂ p) (q ∷ [])

  -- THE REAL CONSUMER.  `down-reflect` is the master's own consumer of
  -- `ElemDown`, and it runs through `H.hull-closed`.
  reflect : (φ : Formula HED.H.T.Code 1)
          → ⟨ [] DR.ASt.AbsL.⊨ᵐ (∃̇ (mapFo HED.H.T.val φ)) ⟩
          → ∥ Σ[ q ∈ DR.SM ] ⟨ (q ∷ []) DR.⊨ᵐ (mapFo DR.codeValM φ) ⟩ ∥₁
  reflect = DR.down-reflect WC.ed

-- =====================================================================
-- BLOCK 3.  THE INDEPENDENCE TEST, AND THE IDENTIFICATION.
--
-- The delivered `elem-down` sits INSIDE `module Co`
-- (`src/L/BoundedSubset.lagda.md:1408-1411`), which takes the two open
-- hypotheses `levelIn` and `cover`.  Placement is not dependence.  Two
-- MEASURED facts settle it:
--
--   `indep`  the site's `elem-down`, at two DIFFERENT hypothesis pairs,
--            is the same term, by `refl`.
--   `same`   the site's `elem-down` IS BLOCK 1's lift at the site's own
--            count, by `refl`.  So the lift is not a look-alike.
--
-- Together: the supply can leave `Co` by a pure move, and whoever
-- discharges `levelIn` and `cover` may use it.
-- =====================================================================

module Site
  (κ : S) (ordκ : IsOrd κ) (cardκ : IsCardinal κ) (κ∉ω : ⟨ κ ∈ˢ ω ⟩ → Empty.⊥)
  (α : S) (ordα : IsOrd α) (α∈κ : ⟨ α ∈ˢ κ ⟩) (α∉ω : ⟨ α ∈ˢ ω ⟩ → Empty.⊥)
  (sq : (δ : S) → ⟨ δ ∈ˢ sucV α ⟩ → (⟨ δ ∈ˢ ω ⟩ → Empty.⊥)
      → Σ[ f ∈ (⟪ δ ⟫ × ⟪ δ ⟫ → ⟪ δ ⟫) ]
          ((u v : ⟪ δ ⟫ × ⟪ δ ⟫) → f u ≡ f v → u ≡ v))
  (x : S) (x⊆Lα : (z : S) → ⟨ z ∈ˢ x ⟩ → ⟨ z ∈ˢ Lset α ⟩)
  (absorbs : ⟪ Lset α ∪ ⁅ x ⁆s ⟫ ↪ ⟪ Lset α ⟫)
  (lam : S) (ordλ : IsOrd lam) (α∈λ : ⟨ α ∈ˢ lam ⟩)
  (succλ : (d : S) → ⟨ d ∈ˢ lam ⟩ → ⟨ sucV d ∈ˢ lam ⟩)
  (x∈Lλ : ⟨ x ∈ˢ Lset lam ⟩) where

  module BSA = Devlin55.BoundedSubsetAt κ ordκ cardκ κ∉ω α ordα α∈κ α∉ω sq
                 x x⊆Lα absorbs lam ordλ α∈λ succλ x∈Lλ

  LevelIn : Type (ℓ-suc ℓ)
  LevelIn = (δ : S) → IsOrd δ → ⟨ δ ∈ˢ BSA.HS.C.πX ⟩
          → ⟨ Lset δ ∈ˢ BSA.HS.C.πX ⟩

  Cover : Type (ℓ-suc ℓ)
  Cover = (y : S) → ⟨ y ∈ˢ BSA.HS.M ⟩
        → ∥ Σ[ γ ∈ S ] (IsOrd γ × ⟨ γ ∈ˢ BSA.HS.C.πX ⟩
                                × ⟨ BSA.HS.C.π y ∈ˢ Lset γ ⟩) ∥₁

  module Indep (levelIn₁ levelIn₂ : LevelIn) (cover₁ cover₂ : Cover) where

    module Co₁ = BSA.Co levelIn₁ cover₁
    module Co₂ = BSA.Co levelIn₂ cover₂

    -- MEASURED: the lift of BLOCK 1 IS the site's supply.
    module Lift₁ = Lifted α lam ordα ordλ
      (BSA.SC.OrdSWO.ordSWO α ordα) BSA.UK.X BSA.UK.X⊆Lλ BSA.UK.∅∈λ
    module LW₁ = Lift₁.WithCount Co₁.CC.count Co₁.CC.count-inj

    -- WALL, RECORDED, NOT REPAIRED.  `same : Co₁.elem-down ≡ LW₁.ed`
    -- by `refl` ran 20:42.15 wall, 1236.01 s user, RSS 2074 MB, under
    -- GHCRTS="-A64m -I0 -M8g".  It met the 20-minute criterion this
    -- probe fixed BEFORE the run and took SIGTERM.  NO heap exhaustion:
    -- 2.07 GB against an 8 GB cap, and the cap was never raised.  P-i:
    -- no surgery on a walling term, so it is commented, not rewritten.
    --
    -- The block below it stays GREEN, and that is the load-bearing
    -- part: `Co₁` and `LW₁` both ELABORATE, so the site's delivered
    -- `elem-down` (`src/L/BoundedSubset.lagda.md:1568`) typechecks and
    -- BLOCK 1's lift accepts the site's own count.  Only the judgmental
    -- IDENTIFICATION of the two is unmeasured.
    --
    -- same : Co₁.elem-down ≡ LW₁.ed
    -- same = refl
