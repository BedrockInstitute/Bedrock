{-# OPTIONS --cubical --safe --guardedness #-}

-- [LJ-1.638]  REDUCE THE ABOVE-OMEGA HALF TO CONJUNCT 4 ALONE.
--
-- THE OBLIGATION.  `above-half-needs-c4`, stated exactly as the brief
-- names it.  At the strictly-above-ω frame that [LJ-1.635] split off
-- (agents/tasks/LJ-1-635/Probe635.agda:92), `Init` at the site follows
-- from ONE hypothesis: the FOURTH conjunct.  The other three conjuncts
-- come free, and this file composes them.
--
-- CONJUNCT 4 IS A HYPOTHESIS AND IS NOT BUILT HERE.  Nothing lands in
-- src/.  No commit, no push.
--
-- WHY [LJ-1.629]'s NO-GO DOES NOT BITE AT THIS FRAME.  [LJ-1.629]
-- reported NO-GO on `site-is-init`, whose hypotheses were the BILL's
-- (agents/tasks/LJ-1-629/Probe629.agda:84-88), and its falsifier ran at
-- κ := ωʟ: the bill's trophy clause ⟨ fst κ ∈ˢ ω ⟩ → Empty.⊥ ADMITS
-- that site, and `Init ω` refutes itself (agents/tasks/LJ-1-629/
-- lj-1.629-report.md:96-103, the row `target-false` at Probe629.agda:
-- 138-139).  THIS obligation is a DIFFERENT statement: its second
-- hypothesis is ⟨ ω ∈ˢ fst κ ⟩, and `no-ω-site` below measures that
-- this hypothesis is UNINHABITED at κ := ωʟ.  The refuted site is not
-- admitted here, so no term of this file inhabits the refuted type.
-- The respell is the one [LJ-1.629]'s own report proposed as the cure
-- (agents/tasks/LJ-1-629/lj-1.629-report.md:183-192), and
-- runs/C3.agda's `above→∉ω` measures that it LOSES NOTHING: the
-- strictly-above hypothesis implies the trophy clause.
--
-- THE MODULE HYPOTHESES ARE THE PREDECESSOR'S DELIVERED TYPES, TAKEN BY
-- IMPORT AND NOT BY COPY (the coder's standing clause, owner
-- 2026-08-20).  Conjunct 4's type is `Init4` from [LJ-1.629]'s
-- alone-typechecked W3 (agents/tasks/LJ-1-629/runs/W3.agda:62-67, the
-- chapter's conjunct copied letter for letter, tied to `Init` by
-- `init-gives-4` at :69-70).  Conjunct 3 is [LJ-1.629]'s green
-- `c3-payable` (agents/tasks/LJ-1-629/Probe629.agda:227-233), reached
-- through this task's W3 file.
--
-- THIS FILE CARRIES NO HOLE AND NO POSTULATE, so every line of it is a
-- measurement and not a claim ([LJ-1.533]'s discipline).
--
-- WHAT THIS FILE MEASURES, IN ONE LINE EACH.
--
--   Section 1.  THE ASSEMBLY, `four-gives-init`: the four conjuncts
--               build `Init`, which pins `Init4` as the chapter's own
--               fourth conjunct in the BUILD direction (`init-gives-4`
--               already pinned the projection direction).
--   Section 2.  THE OBLIGATION, `above-half-needs-c4`.
--   Section 3.  THE PAYOFF, `above-c4→sq`: what supplying conjunct 4 at
--               this frame buys, and the frame shape the half carries.
--   Section 4.  THE FALSIFIER'S SITE, `no-ω-site`: excluded here.
--
-- CALIBER.  The program set GHCRTS on this pane.  I did not set it.
-- One Agda process at a time.  No heap wall occurred; the run ledger is
-- in the report.

open import Base.Prelude
open import Base.Truth
open import Base.Classical using ( LEM )

module LJ-1-638.Probe638 {ℓ : Level} (lem : LEM (ℓ-suc ℓ)) where

open import FOL.ZFStructure using ( module hPropStructure )
open import V.Hierarchy {ℓ} using ( 𝒮ᵥ; ∈-irrefl )
open import Cubical.HITs.CumulativeHierarchy.Constructions
  using ( module InfinitySet )
open InfinitySet using ( ω; sucV )
import Cubical.Data.Empty as Empty
import Cubical.HITs.PropositionalTruncation as PT
open PT using ( ∥_∥₁ )
open import Cubical.HITs.CumulativeHierarchy.Properties using ( ⟪_⟫ )
open import L.Constructible {ℓ} using ( 𝒮ʟ; IsOrd )
open import L.Cardinal {ℓ} lem using ( IsCardinalL; _↪_ )
open import L.Ordinal.SquareLaw {ℓ} lem using ( Init; sq; via-col-square )
open import L.Axioms.Infinity {ℓ} lem using ( ωʟ )
import LJ-1-629.runs.W3
module W3629 = LJ-1-629.runs.W3 lem
import LJ-1-638.runs.C3
module C3 = LJ-1-638.runs.C3 lem

open hPropStructure 𝒮ᵥ using ( S; _∈ˢ_ )
module SL = hPropStructure 𝒮ʟ

-- =====================================================================
-- SECTION 1.  THE ASSEMBLY.
--
--   Init α = IsOrd α                                  (conjunct 1)
--          × ⟨ ω ∈ˢ α ⟩                               (conjunct 2)
--          × ((γ : S) → ⟨ γ ∈ˢ α ⟩ → ⟨ sucV γ ∈ˢ α ⟩) (conjunct 3)
--          × <α injects into no infinite member's square> (conjunct 4)
--
--   src/L/Ordinal/SquareLaw.lagda.md:692-698.
--
--   `Closed` is conjunct 3 copied letter for letter from :695.
--   Conjunct 4 is NOT re-copied here: it is `W3629.Init4`, the copy
--   [LJ-1.629] typechecked alone.  `four-gives-init` is the build
--   direction, and it typechecks only if `Init4` IS the chapter's
--   fourth conjunct up to definitional equality, so the two spellings
--   cannot drift.  The projection direction is already delivered
--   (agents/tasks/LJ-1-629/runs/W3.agda:69-70).
--
--   The row is stated at an ARBITRARY ambient α, not at the site, so
--   it serves any future site unchanged (clause W2).
-- =====================================================================

Closed : S → Type (ℓ-suc ℓ)
Closed α = (γ : S) → ⟨ γ ∈ˢ α ⟩ → ⟨ sucV γ ∈ˢ α ⟩

four-gives-init :
    (α : S) → IsOrd α → ⟨ ω ∈ˢ α ⟩ → Closed α → W3629.Init4 α → Init α
four-gives-init α oα ω∈α clo c4 = oα , ω∈α , clo , c4

-- =====================================================================
-- SECTION 2.  THE OBLIGATION.
--
--   Three conjuncts come free at this frame, and the brief's premises
--   name each source:
--
--     1  IsOrd (fst κ)   the frame's own first hypothesis, verbatim
--                        ([LJ-1.629]'s `c1-given`, Probe629.agda:109-111)
--     2  ⟨ ω ∈ˢ fst κ ⟩  the frame's own third hypothesis, VERBATIM.
--                        Conjunct 2 IS the strictly-above hypothesis
--                        (src/L/Ordinal/SquareLaw.lagda.md:693)
--     3  closure         [LJ-1.629]'s `c3-payable`, composed at this
--                        frame by runs/C3.agda with no re-proof
--     4  the hypothesis  NOT built.  This is the whole remaining debt
--                        of the above-ω half.
-- =====================================================================

above-half-needs-c4 :
    (κ : SL.S) → IsOrd (fst κ) → IsCardinalL κ → ⟨ ω ∈ˢ fst κ ⟩
  → W3629.Init4 (fst κ)
  → Init (fst κ)
above-half-needs-c4 κ oκ cκ ω∈κ c4 =
  four-gives-init (fst κ) oκ ω∈κ (C3.c3-at-frame κ oκ cκ ω∈κ) c4

-- =====================================================================
-- SECTION 3.  THE PAYOFF, AND THE HALF'S FRAME SHAPE.
--
--   `AboveFrame X` is the shape of [LJ-1.635]'s strictly-above half
--   (agents/tasks/LJ-1-635/Probe635.agda:92) with its conclusion left
--   open: that half is `AboveFrame (Concl zf)`.  Written once at an
--   arbitrary conclusion, so every future row of the half reuses it
--   (clause W2).
--
--   `above-c4→sq` is [LJ-1.629]'s `route` (Probe629.agda:292-295)
--   restated at THIS frame.  There the premise was the refuted
--   `SiteIsInit`; here it is `AboveFrame` of conjunct 4 alone, and the
--   falsification is gone (section 4).  What supplying conjunct 4
--   across the half buys is the square law at every site of the half,
--   through the chapter's own theorem (`via-col-square`,
--   src/L/Ordinal/SquareLaw.lagda.md:960-961).
-- =====================================================================

AboveFrame : ∀ {ℓ'} → (SL.S → Type ℓ') → Type (ℓ-max (ℓ-suc ℓ) ℓ')
AboveFrame X =
  (κ : SL.S) → IsOrd (fst κ) → IsCardinalL κ → ⟨ ω ∈ˢ fst κ ⟩ → X κ

above-c4→sq :
    AboveFrame (λ κ → W3629.Init4 (fst κ)) → AboveFrame (λ κ → sq (fst κ))
above-c4→sq supply κ oκ cκ ω∈κ =
  via-col-square (fst κ)
    (above-half-needs-c4 κ oκ cκ ω∈κ (supply κ oκ cκ ω∈κ))

-- =====================================================================
-- SECTION 4.  THE FALSIFIER'S SITE IS NOT ADMITTED HERE.
--
--   [LJ-1.629]'s `target-false` (Probe629.agda:138-139) refuted the
--   BILL's statement at κ := ωʟ.  That falsifier cannot be run against
--   this obligation: it would have to supply ⟨ ω ∈ˢ fst ωʟ ⟩, and
--   `fst ωʟ` is `ω` by definition (src/L/Axioms/Infinity.lagda.md:69-70)
--   while regularity forbids ω ∈ ω (∈-irrefl, src/V/Hierarchy.lagda.md:
--   155).  This is [LJ-1.635]'s `above-half-misses-ω`
--   (agents/tasks/LJ-1-635/Probe635.agda:122-123) re-measured at this
--   file rather than transferred, and it is why the split of [LJ-1.635]
--   is what makes this task's statement stand: the at-ω half carries
--   the site that refuted the bill's uniform form.
-- =====================================================================

no-ω-site : ⟨ ω ∈ˢ fst ωʟ ⟩ → Empty.⊥
no-ω-site = ∈-irrefl ω

-- =====================================================================
-- SECTION 5.  WHAT THE C-42 SWEEP EARNED: CONJUNCT 4 HAS A ROUTE THAT
-- IS ALREADY GREEN IN src/, AND IT IS NOT THE ROUTE [LJ-1.629] PRICED.
--
--   C-42 says a refutation measures ONE site and never measures how far
--   the shape extends, so the next action is the SWEEP.  [LJ-1.629]
--   refuted `Init` at the bill's site and priced conjunct 4 as needing
--   ambient `IsCardinal` AT the site plus a pairing at every infinite
--   member (`c4-from`, agents/tasks/LJ-1-629/Probe629.agda:255-265).
--   The sweep over src/ finds a SECOND assembly of the same four
--   conjuncts, already closed: `init-at-kappa`,
--   src/L/SquareLawClosed.lagda.md:166-176.  Its conjunct 4 is
--   `clause4-at-kappa` (:96-115) and it pays a DIFFERENT bill:
--   MINIMALITY at the site (`κ-min-atL`, :86-89) plus `∥ sq β ∥₁` at
--   every infinite member, which the chapter's own recursion supplies
--   as an induction hypothesis.  NO ambient `IsCardinal` at the site
--   and NO `BandBelow` appear in it.
--
--   `c4-from-min` below is that argument RE-MEASURED at an arbitrary
--   site and an arbitrary injected type, because a measured cure does
--   not transfer by analogy (the Boundary).  It DOES NOT DISCHARGE
--   conjunct 4: all three of its hypotheses stay open.  It measures
--   that the src/ route is site-generic, so the bill's site may consume
--   it if a future task supplies minimality there.
-- =====================================================================

∘↪ : {A B C : Type ℓ} → A ↪ B → B ↪ C → A ↪ C
∘↪ (f , injf) (g , injg) =
  (λ x → g (f x)) , λ x y e → injf x y (injg (f x) (f y) e)

c4-from-min :
    (α : S) (X : Type ℓ)
  → ∥ X ↪ ⟪ α ⟫ ∥₁
  → ((β : S) → ⟨ β ∈ˢ α ⟩ → ∥ X ↪ ⟪ β ⟫ ∥₁ → Empty.⊥)
  → ((β : S) → IsOrd β → ⟨ β ∈ˢ α ⟩ → ⟨ ω ∈ˢ β ⟩ → ∥ sq β ∥₁)
  → W3629.Init4 α
c4-from-min α X inj min ih β oβ β∈α ω∈β f finj =
  PT.rec Empty.isProp⊥ from-sq (ih β oβ β∈α ω∈β)
  where
  from-sq : sq β → Empty.⊥
  from-sq (g , g-inj) = min β β∈α (PT.map (λ i → ∘↪ i α↪β) inj)
    where
    α↪β : ⟪ α ⟫ ↪ ⟪ β ⟫
    α↪β = (λ m → g (f m)) , λ m n e → finj m n (g-inj (f m) (f n) e)
