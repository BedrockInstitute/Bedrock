{-# OPTIONS --cubical --safe --guardedness #-}

-- [LJ-1.571]  Row 2, `SqAt`, and the collection that is not inhabited.
--
-- SECTION 1 is W3 and the brief ordered it written first and typechecked
-- ALONE.  That slice is kept at agents/tasks/LJ-1-571/runs/W3.agda.
-- SECTION 2 answers D-10: `SqLaw` is AMBIENT, and the proof is an
-- identity function into src/'s own `SqFam`.
-- SECTION 3 measures the three strengths of the square law and says
-- which one src/ delivers.
-- SECTION 4 is the obligation.
--
-- Nothing is postulated.  Nothing lands in src/.  No hole.

open import Base.Prelude
open import Base.Truth
open import Base.Classical using ( LEM )

module LJ-1-571.Probe571 {ℓ : Level} (lem : LEM (ℓ-suc ℓ)) where

open import FOL.ZFStructure using ( module hPropStructure )
open import V.Hierarchy {ℓ} using ( 𝒮ᵥ )
open import L.Constructible {ℓ} using ( 𝒮ʟ; IsOrd; Lset )
open import L.GCH {ℓ} lem using ( GCHStatement; SuccCardL; InjL )
open import L.Ordinal.SquareLaw {ℓ} lem using ( sq )
open import L.StageBound {ℓ} lem using ( SqFam; SqCollect )
import L.SquareLawClosed
import FOL.ZFModel

open import Cubical.HITs.CumulativeHierarchy.Constructions
  using ( module InfinitySet )
open InfinitySet {ℓ} using ( ω; sucV )
open import Cubical.HITs.CumulativeHierarchy.Properties using ( ⟪_⟫ )
open import Cubical.Data.Sigma using ( _×_ )
import Cubical.Data.Empty as Empty
import Cubical.HITs.PropositionalTruncation as PT
open PT using ( ∥_∥₁; ∣_∣₁ )

import LJ-1-550.Probe550 {ℓ} lem as P550
import LJ-1-558.Probe558 {ℓ} lem as P558
import LJ-1-564.Probe564 {ℓ} lem as P564

open TruthAlgebra (hPropAlgebra (ℓ-suc ℓ))
open hPropStructure 𝒮ᵥ using ( _∈ˢ_ )

module SV = hPropStructure 𝒮ᵥ
module SL = hPropStructure 𝒮ʟ
module ModelL = FOL.ZFModel 𝒮ʟ

-- =====================================================================
-- SECTION 1.  W3.  `SqLaw (fst κ)` UNFOLDED ONE STEP, TYPE ONLY.
--
--   Copied from agents/tasks/LJ-1-571/runs/W3.agda, which the brief
--   ordered written first and typechecked ALONE.  It exits 0 there.
-- =====================================================================

w3-sqlaw-at : SL.S → Type (ℓ-suc ℓ)
w3-sqlaw-at κ =
    (δ : SV.S) → ⟨ δ ∈ˢ sucV (fst κ) ⟩ → (⟨ δ ∈ˢ ω ⟩ → Empty.⊥)
  → Σ[ f ∈ (⟪ δ ⟫ × ⟪ δ ⟫ → ⟪ δ ⟫) ]
      ((u v : ⟪ δ ⟫ × ⟪ δ ⟫) → f u ≡ f v → u ≡ v)

-- =====================================================================
-- SECTION 2.  D-10.  THE CARRIER IS AMBIENT, AND THIS IS THE PROOF.
--
--   `SqLaw : SV.S → Type (ℓ-suc ℓ)` (Probe550.agda:82).  The binder is
--   `SV.S` and every carrier under the arrow is `⟪ δ ⟫`, the AMBIENT
--   presentation.  `SL.S` occurs ONLY at `SqAt`'s outer `κ`
--   (Probe550.agda:309-310) and is spent at once by `fst κ`.  Nothing
--   under the arrow mentions `isL`, `Lset` or `𝒮ʟ`.
--
--   An identity function is the machine's word for it.  Each of the
--   three lines below elaborates with `f` unchanged, so the three types
--   are DEFINITIONALLY EQUAL and not merely equivalent.
-- =====================================================================

-- `SqLaw` is W3's unfolding.
sqlaw-is-w3 : (κ : SL.S) → P550.SqLaw (fst κ) → w3-sqlaw-at κ
sqlaw-is-w3 κ f = f

-- `SqLaw` is src/'s own consumer-side family, `SqFam`
-- (src/L/StageBound.lagda.md:37-42).  THIS is the line that settles
-- D-10: `SqFam` is stated at the ambient `S` of `hPropStructure 𝒮ᵥ`
-- (src/L/StageBound.lagda.md:31), and the identity crosses.
sqlaw-is-sqfam : (α : SV.S) → P550.SqLaw α → SqFam α
sqlaw-is-sqfam α f = f

-- And back, so the two are interchangeable in both directions.
sqfam-is-sqlaw : (α : SV.S) → SqFam α → P550.SqLaw α
sqfam-is-sqlaw α f = f

-- src/'s pointwise square `sq` (src/L/Ordinal/SquareLaw.lagda.md:685)
-- is the codomain of both, which is what makes the chain in section 3
-- typecheck at all.  This is StageBound's own `adapter`
-- (src/L/StageBound.lagda.md:130-133) restated at `SqLaw`.
sqlaw-is-pointwise-sq :
    (α : SV.S)
  → ((δ : SV.S) → ⟨ δ ∈ˢ sucV α ⟩ → (⟨ δ ∈ˢ ω ⟩ → Empty.⊥) → sq δ)
  → P550.SqLaw α
sqlaw-is-pointwise-sq α f = f

-- =====================================================================
-- SECTION 3.  THE SQUARE LAW HAS THREE STRENGTHS, NOT TWO, AND src/
-- DELIVERS THE WEAKEST.
--
--   The brief points at src/L/StageBound.lagda.md:42, "Collection of
--   truncated squares to a truncated family. Not inhabited."  A comment
--   is not a measurement, so here is the measurement.  Read `SqCollect`
--   (src/L/StageBound.lagda.md:44-48): its ANTECEDENT is level 1 below
--   and its CONSEQUENT is level 2.  It is the step between them and it
--   is neither of them.
--
--     LEVEL 1.  (δ : ...) → ∥ sq δ ∥₁      pointwise truncated
--     LEVEL 2.  ∥ SqLaw α ∥₁               the family, truncated
--     LEVEL 3.  SqLaw α                    the family, BARE
--
--   `SqAt` asks for LEVEL 3 (Probe550.agda:309-310).  src/ delivers
--   LEVEL 1 and no more.  So the note names ONE of the TWO steps that
--   separate them, and section 4 is about which of the two is real.
-- =====================================================================

-- LEVEL 1, AND IT IS NOT A HYPOTHESIS OF ANYBODY.  `sq-trunc-closed`
-- (src/L/SquareLawClosed.lagda.md:325-327) is a theorem of src/, and
-- `IsOrd α` is the only thing it wants beyond `α` itself.  `SqAt`
-- carries `IsOrd (fst κ)` at its own head, so the fit is exact.
sq-pointwise-trunc :
    (α : SV.S) → IsOrd α
  → (δ : SV.S) → ⟨ δ ∈ˢ sucV α ⟩ → (⟨ δ ∈ˢ ω ⟩ → Empty.⊥) → ∥ sq δ ∥₁
sq-pointwise-trunc α oα = SLC.sq-trunc-closed
  where module SLC = L.SquareLawClosed {ℓ} lem α oα

-- LEVEL 1 TO LEVEL 2 IS EXACTLY `SqCollect`, WITH ITS ANTECEDENT PAID.
-- The consequent is `∥ SqFam α ∥₁` and the target is `∥ SqLaw α ∥₁`;
-- section 2 showed the two are definitionally equal, so no coercion
-- appears here.
sqlaw-trunc-from-collect :
    (α : SV.S) → IsOrd α → SqCollect α → ∥ P550.SqLaw α ∥₁
sqlaw-trunc-from-collect α oα collect = collect (sq-pointwise-trunc α oα)

-- =====================================================================
-- SECTION 4.  THE OBLIGATION.  ROW 2 DOES NOT NEED LEVEL 3, AND THE
-- INPUT IT LACKS IS `SqCollect` AND NOTHING ELSE.
--
--   THE MEASUREMENT THAT DECIDES IT.  `r2` is consumed EXACTLY ONCE in
--   the whole route, at `r2 κ ordκ` (Probe564.agda:358-360), inside
--   `power-into-succ-at`, at the SAME `κ` that `PowerIntoSuccAt` binds
--   (Probe564.agda:328-331).  It is not threaded, not stored, and not
--   used at a second ordinal.
--
--   AND THE GOAL THERE IS A PROPOSITION.  `PowerIntoSuccAt` concludes
--   `InjL (𝒫 κ) δ`, and `InjL a b = ∥ Σ[ F ∈ S ] InjCode F a b ∥₁`
--   (src/L/GCH.lagda.md:37-38).  So a `PT.rec` may spend a truncation
--   there, and LEVEL 2 does the work of LEVEL 3 for free.
--
--   THE THIRD STEP IS THEREFORE NOT ON THE PATH.  Untruncating
--   `∥ SqLaw α ∥₁` to `SqLaw α` would be a genuine choice principle,
--   because `sq δ` is a Σ of an injection and is no proposition.
--   NOBODY HAS TO PAY IT.
-- =====================================================================

-- Row 2, weakened to the input src/ is one named step away from.
SqCollectAt : Type (ℓ-suc ℓ)
SqCollectAt = (κ : SL.S) → IsOrd (fst κ) → SqCollect (fst κ)

-- Row 2 at LEVEL 2.
SqAtTrunc : Type (ℓ-suc ℓ)
SqAtTrunc = (κ : SL.S) → IsOrd (fst κ) → ∥ P550.SqLaw (fst κ) ∥₁

sqat-trunc-from-collect : SqCollectAt → SqAtTrunc
sqat-trunc-from-collect r2c κ oκ =
  sqlaw-trunc-from-collect (fst κ) oκ (r2c κ oκ)

-- `power-into-succ-at` (Probe564.agda:351-361) with row 2 at LEVEL 2.
-- The body is that term's body under one `PT.rec`, and the four rows
-- src/ already pays are plugged in rather than carried.
power-into-succ-at-trunc :
    (zf : ModelL.isZFModel)
  → P550.AmbientCardAtSucc → SqAtTrunc → P550.CoHyps
  → P564.StageCountedCoded
  → P564.PowerIntoSuccAt zf
power-into-succ-at-trunc zf r1 r2t r3 b9 κ ordκ κ∉ω δ sc =
  PT.rec PT.isPropPropTrunc
    (λ sqκ → P564.power-into-succ-from-landing zf b9 κ δ sc
               (U.member-in-stage (r1 κ δ sc) sqκ r3))
    (r2t κ ordκ)
  where
  module U = P550.UseSite zf P564.bounded-subset-theorem (P564.b6-paid zf)
               P564.b7-paid P564.b8-paid κ δ ordκ κ∉ω sc

-- THE OBLIGATION.  `gch-from-five` (Probe564.agda:456-463) with row 2
-- replaced by the input it actually lacks.  Four rows are untouched and
-- the fifth is now `SqCollect` at every ordinal L-cardinal.
sqat-or-what-it-wants :
    (zf : ModelL.isZFModel)
  → P550.AmbientCardAtSucc → SqCollectAt → P550.CoHyps
  → P564.StageCountedCoded
  → P558.SuccIntoPower zf
  → GCHStatement zf
sqat-or-what-it-wants zf r1 r2c r3 b9 b10 =
  P564.gch-route-with-premised-hard zf P564.b4-paid
    (power-into-succ-at-trunc zf r1 (sqat-trunc-from-collect r2c) r3 b9) b10

-- =====================================================================
-- SECTION 5.  THE NEW ROW IS WEAKER THAN THE OLD ONE, AND THE ROUTE
-- STILL REACHES `gch-from-five`'S TYPE.
--
--   A weakening that cannot be checked is a claim.  These two terms are
--   the check, and they run in both directions.
-- =====================================================================

-- DIRECTION 1.  `SqAt` gives `SqCollectAt`, so nothing was strengthened
-- and no new burden was smuggled in.  The antecedent of `SqCollect` is
-- discarded: at LEVEL 3 the family is already there.
sqat-gives-collect : P550.SqAt → SqCollectAt
sqat-gives-collect r2 κ oκ _ = ∣ r2 κ oκ ∣₁

-- DIRECTION 2.  Composing it with the obligation reproduces
-- `gch-from-five`'s type letter for letter (Probe564.agda:456-463).
-- So the weakened route loses nothing the five-row bill had.
five-rows-recovered :
    (zf : ModelL.isZFModel)
  → P550.AmbientCardAtSucc → P550.SqAt → P550.CoHyps
  → P564.StageCountedCoded
  → P558.SuccIntoPower zf
  → GCHStatement zf
five-rows-recovered zf r1 r2 = sqat-or-what-it-wants zf r1 (sqat-gives-collect r2)

-- =====================================================================
-- SECTION 6.  WHAT IS NOT HERE, WRITTEN DOWN SO NOBODY READS A GO INTO
-- IT.
--
--   `SqCollectAt` IS NOT INHABITED IN THIS FILE and no term of it
--   appears above.  Row 2 is NARROWED and it is NOT DISCHARGED.  The
--   bill stays at five rows; the fifth is smaller than it was.
--
--   AND THE TRUNCATION IS NOT REMOVABLE UPSTREAM.  It does not enter at
--   `sq-trunc-closed`.  It enters at `LeastCardInjL`, whose predicate is
--   `InjP γ = ∥ Inj γ ∥₁ , squash₁` (src/L/Cardinal.lagda.md:66-67),
--   and it is truncated there because the least-element search wants an
--   hProp-valued predicate.  `SquareLawClosed` spends that truncation at
--   its descent case with `PT.map2` (src/L/SquareLawClosed.lagda.md:315-319)
--   and cannot do otherwise.  So strengthening LEVEL 1 to a bare
--   pointwise square is not a repair anybody can make locally.
--
--   THIS IS NOT `[LJ-1.567]`'S SITE.  Every carrier above is `⟪ δ ⟫`,
--   the ambient presentation, and no term here is asked to be coded or
--   to be a member of `L`.  `[LJ-1.567]`'s `col-step`
--   (agents/tasks/LJ-1-567/Probe567.agda:259) is a satisfaction fact
--   about `pr (fst c) (fst z) ∈ fst f`, an INTERNAL statement.  The two
--   do not meet on this row.
-- =====================================================================
