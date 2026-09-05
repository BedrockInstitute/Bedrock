{-# OPTIONS --cubical --safe --guardedness #-}

-- [LJ-1-641]  The commute at ordinal collapse.
--
-- THE OBLIGATION is one term, `commute-at-ordinal`, at the type
-- [LJ-1.602] named `Commute` (agents/tasks/LJ-1-602/Probe602.agda:178-182).
-- Nothing lands in src/.  Nothing is postulated.  The file carries
-- `--safe` and no hole.
--
-- THE FLOOR WAS PRICED BEFORE ANY PROOF (D-10, and the standing coder
-- clause).  runs/FLOOR.agda states the obligation at a BARE META in
-- this file's own trimmed frame: runs/floor-2.out, exit 42 at the one
-- designed hole, 2.81 s, peak RSS 745,275,392 bytes against the
-- 2,147,483,648-byte cap.  runs/floor-1.out is the same slice with
-- L.BoundedSubset COLD (23.06 s, peak 2,224,013,312 bytes); it prices
-- the dependency, not this frame.
--
-- THE IMPORTS ARE TRIMMED TO THE ROWS THIS FILE USES.  [LJ-1.602]'s
-- frame carried CollapseIso, Formula and mapFo because its clause was
-- a SYNTAX statement.  This obligation is a SET-LEVEL equation and
-- reads no formula anywhere, so none of the three is imported here.
--
-- CALIBER.  The program set GHCRTS="-A64m -I0 -M2g" on this pane.  I
-- did not set it.  One Agda process at a time.

open import Base.Prelude
open import Base.Truth
open import Base.Classical using ( LEM )

module LJ-1-641.Probe641 {ℓ : Level} (lem : LEM (ℓ-suc ℓ)) where

open import FOL.ZFStructure using ( module hPropStructure )
open import V.Hierarchy {ℓ} using ( 𝒮ᵥ; extensionalV )
open import V.Presentation {ℓ} using ( member )
open import L.Constructible {ℓ}
  using ( IsOrd; Lset; Lset-compute; LsetStep; 𝒟ₒ; Lset-in; Lset-out )
open import L.BoundedSubset {ℓ} lem using ( module HullStage )
open import Cubical.HITs.CumulativeHierarchy.Constructions
  using ( module InfinitySet; ∅ )
open import Cubical.HITs.CumulativeHierarchy.Properties
  using ( ⟪_⟫; ⟪_⟫↪; ∈∈ₛ )
open import Cubical.Functions.Logic using ( ⇔toPath )
open import Cubical.Data.Sigma using ( _×_ )
import Cubical.HITs.PropositionalTruncation as PT
open PT using ( ∥_∥₁; ∣_∣₁ )
open InfinitySet {ℓ} using ( sucV )

open TruthAlgebra (hPropAlgebra (ℓ-suc ℓ))
module SV = hPropStructure 𝒮ᵥ
open SV using ( _∈ˢ_ )

-- =====================================================================
-- THE FRAME.  One hull stage, exactly as [LJ-1.602] section "THE FRAME"
-- instantiated it, MINUS the extensionality and the collapse iso: this
-- obligation's type names neither.
-- =====================================================================

module Frame (lam : SV.S) (ordλ : IsOrd lam)
             (succλ : (d : SV.S) → ⟨ d ∈ˢ lam ⟩ → ⟨ sucV d ∈ˢ lam ⟩)
             (X : SV.S)
             (X⊆Lλ : (z : SV.S) → ⟨ z ∈ˢ X ⟩ → ⟨ z ∈ˢ Lset lam ⟩)
             (∅∈λ : ⟨ ∅ ∈ˢ lam ⟩) where

  module HS = HullStage lam ordλ succλ X X⊆Lλ ∅∈λ

  -- THE OBLIGATION'S TYPE, copied letter for letter from
  -- agents/tasks/LJ-1-602/Probe602.agda:178-182.
  Commute : Type (ℓ-suc ℓ)
  Commute =
    (δ : SV.S) (δ∈M : ⟨ δ ∈ˢ HS.M ⟩) → IsOrd (HS.C.π δ)
    → (Lδ∈M : ⟨ Lset δ ∈ˢ HS.M ⟩)
    → HS.C.π (Lset δ) ≡ Lset (HS.C.π δ)

  -- ===================================================================
  -- SECTION 1.  W3, THE WIDEST UNMEASURED TERM, ANSWERED.
  --
  --   The brief names W3: "Whether the two computation laws join once
  --   the collapse is an ordinal."  The slice runs/W3.agda states it
  --   alone and is green (runs/w3-2.out, exit 0, 3.18 s).
  --
  --   THE ANSWER IS NO, AND THE HYPOTHESES ARE NOT WHY.  `refl` at the
  --   join with `IsOrd (HS.C.π δ)` AND `⟨ Lset δ ∈ˢ HS.M ⟩` both in
  --   scope fails with [UnequalTerms] (runs/join-refl.out:4, the
  --   diagnostic runs/JOINREFL.agda), the SAME error class [LJ-1.477]
  --   measured WITHOUT the hypotheses (its runs/join-refl.out:2).  That
  --   is not a coincidence and it is not new evidence about the
  --   ordinal: `refl` is decided by conversion, and conversion does not
  --   read a hypothesis.  ADDING A HYPOTHESIS TO A TYPE CANNOT CHANGE
  --   WHETHER ITS TWO SIDES ARE DEFINITIONALLY EQUAL.  So the
  --   computation-law route is closed at the ordinal collapse for the
  --   same reason it was closed without it, and section 3 is where the
  --   ordinal hypothesis could earn its keep instead.
  -- ===================================================================

  law-π : (δ : SV.S)
        → HS.C.π (Lset δ) ≡ HS.C.step (Lset δ) (λ z _ → HS.C.π z)
  law-π δ = HS.C.π-compute (Lset δ)

  law-L : (δ : SV.S)
        → Lset (HS.C.π δ) ≡ LsetStep (HS.C.π δ) (λ β _ → Lset β)
  law-L δ = Lset-compute (HS.C.π δ)

  JoinStepsAtOrd : Type (ℓ-suc ℓ)
  JoinStepsAtOrd =
    (δ : SV.S) (δ∈M : ⟨ δ ∈ˢ HS.M ⟩) → IsOrd (HS.C.π δ)
    → (Lδ∈M : ⟨ Lset δ ∈ˢ HS.M ⟩)
    → HS.C.step (Lset δ) (λ z _ → HS.C.π z)
      ≡ LsetStep (HS.C.π δ) (λ β _ → Lset β)

  join-gives-commute : JoinStepsAtOrd → Commute
  join-gives-commute j δ δ∈M oπδ Lδ∈M =
    law-π δ ∙ j δ δ∈M oπδ Lδ∈M ∙ sym (law-L δ)

  -- ===================================================================
  -- SECTION 2.  THE MEMBER READING OF BOTH SIDES.
  --
  --   The computation-law route joins two CONSTRUCTORS (`sett` of
  --   filtered π-images against `⋃` of `𝒟ₒ` of levels) and they do not
  --   meet.  The member route asks instead what each side CONTAINS, and
  --   the tree already answers for both sides.  Nothing here is new
  --   mathematics; it is the two readings put in one place so section 3
  --   can join them where the constructors could not.
  --
  --   ONE LEMMA IS OWED.  `HS.C.π-member` (src/V/Collapse.lagda.md:63-73)
  --   returns the hull-membership of the preimage and its π-value, but
  --   DROPS the fact that the preimage is a member of the argument.
  --   This obligation needs that fact, because the preimage must be fed
  --   to `Lset-out` at δ.  `π-member'` below is that lemma, built at the
  --   same `π-compute` unfolding and keeping the third conjunct.
  -- ===================================================================

  π-member' : (x z : SV.S) → ⟨ z ∈ˢ HS.C.π x ⟩
            → ∥ Σ[ y ∈ SV.S ]
                 (⟨ y ∈ˢ x ⟩ × ⟨ y ∈ˢ HS.M ⟩ × (HS.C.π y ≡ z)) ∥₁
  π-member' x z z∈ =
    PT.map mk (subst (λ w → ⟨ z ∈ˢ w ⟩) (HS.C.π-compute x) z∈)
    where
    mk : Σ[ p ∈ HS.C.Fiber x ] (HS.C.π (⟪ x ⟫↪ (p .fst)) ≡ z)
       → Σ[ y ∈ SV.S ]
           (⟨ y ∈ˢ x ⟩ × ⟨ y ∈ˢ HS.M ⟩ × (HS.C.π y ≡ z))
    mk (p , q) = ⟪ x ⟫↪ (p .fst)
               , ( member x (p .fst)
                 , ∈∈ₛ {a = ⟪ x ⟫↪ (p .fst)} {b = HS.M} .snd (p .snd)
                 , q )

  -- the intro direction, straight from the tree: a hull member of a set
  -- collapses into the collapse of that set
  π-into : (x y : SV.S) → ⟨ y ∈ˢ x ⟩ → ⟨ y ∈ˢ HS.M ⟩
         → ⟨ HS.C.π y ∈ˢ HS.C.π x ⟩
  π-into = HS.C.π∈-fwd

  -- ===================================================================
  -- SECTION 3.  THE REDUCTION.  WHAT THE OBLIGATION ACTUALLY COSTS.
  --
  --   Set equality is mutual membership (`extensionalV`,
  --   src/V/Hierarchy.lagda.md:114-115) and membership is an hProp, so
  --   the obligation splits into two implications and nothing is lost:
  --   `halves-give-commute` is that split, as a term.
  --
  --   Then each half is expanded ONCE by the member readings of section
  --   2, and what survives the expansion is named.  THREE THINGS
  --   SURVIVE, and they are the price of this obligation:
  --
  --     IndexInHull  the index gap.  `Lset δ` unions over ALL members
  --                  of δ; `HS.C.π δ` sees only the members of δ that
  --                  lie in the hull.  A level contributed by a member
  --                  of δ OUTSIDE the hull has no counterpart on the
  --                  right.
  --     DefFwd       π carries a hull member of `𝒟ₒ (Lset β)` into
  --                  `𝒟ₒ (Lset (HS.C.π β))`.
  --     DefBwd       and every member of `𝒟ₒ (Lset (HS.C.π β))` is hit
  --                  by one.
  --
  --   DefFwd and DefBwd together are "π commutes with `𝒟ₒ`", which is
  --   the demand [LJ-1.477] named in prose and did not state as a type
  --   (agents/tasks/LJ-1-477/lj-1.477-report.md, "## 4. What the next
  --   brief needs": "it needs `π` to commute with `𝒟ₒ`, and it needs
  --   `Lset-out` witnesses to lie in `M`").  IndexInHull is that
  --   report's second demand.  This section states all three as types
  --   and DISCHARGES THE REST: the assembly below is complete, so the
  --   three are the whole remaining distance and no fourth thing is
  --   owed.
  -- ===================================================================

  Fwd : Type (ℓ-suc ℓ)
  Fwd = (δ : SV.S) → ⟨ δ ∈ˢ HS.M ⟩ → IsOrd (HS.C.π δ)
      → ⟨ Lset δ ∈ˢ HS.M ⟩
      → (z : SV.S) → ⟨ z ∈ˢ HS.C.π (Lset δ) ⟩ → ⟨ z ∈ˢ Lset (HS.C.π δ) ⟩

  Bwd : Type (ℓ-suc ℓ)
  Bwd = (δ : SV.S) → ⟨ δ ∈ˢ HS.M ⟩ → IsOrd (HS.C.π δ)
      → ⟨ Lset δ ∈ˢ HS.M ⟩
      → (z : SV.S) → ⟨ z ∈ˢ Lset (HS.C.π δ) ⟩ → ⟨ z ∈ˢ HS.C.π (Lset δ) ⟩

  -- the split, and it is lossless
  halves-give-commute : Fwd → Bwd → Commute
  halves-give-commute f b δ δ∈M oπδ Lδ∈M =
    extensionalV (λ x → ⇔toPath (f δ δ∈M oπδ Lδ∈M x)
                                (b δ δ∈M oπδ Lδ∈M x))

  -- THE THREE GAPS, AS TYPES.
  IndexInHull : Type (ℓ-suc ℓ)
  IndexInHull =
    (δ : SV.S) → ⟨ δ ∈ˢ HS.M ⟩ → IsOrd (HS.C.π δ)
    → (β : SV.S) → ⟨ β ∈ˢ δ ⟩
    → (y : SV.S) → ⟨ y ∈ˢ HS.M ⟩ → ⟨ y ∈ˢ 𝒟ₒ (Lset β) ⟩
    → ∥ Σ[ β' ∈ SV.S ]
         (⟨ β' ∈ˢ δ ⟩ × ⟨ β' ∈ˢ HS.M ⟩ × ⟨ y ∈ˢ 𝒟ₒ (Lset β') ⟩) ∥₁

  DefFwd : Type (ℓ-suc ℓ)
  DefFwd =
    (β y : SV.S) → ⟨ β ∈ˢ HS.M ⟩ → ⟨ y ∈ˢ HS.M ⟩
    → ⟨ y ∈ˢ 𝒟ₒ (Lset β) ⟩
    → ⟨ HS.C.π y ∈ˢ 𝒟ₒ (Lset (HS.C.π β)) ⟩

  DefBwd : Type (ℓ-suc ℓ)
  DefBwd =
    (β z : SV.S) → ⟨ β ∈ˢ HS.M ⟩
    → ⟨ z ∈ˢ 𝒟ₒ (Lset (HS.C.π β)) ⟩
    → ∥ Σ[ y ∈ SV.S ]
         (⟨ y ∈ˢ 𝒟ₒ (Lset β) ⟩ × ⟨ y ∈ˢ HS.M ⟩ × (HS.C.π y ≡ z)) ∥₁

  -- FORWARD HALF, from the index gap and the forward definability gap.
  fwd-from-gaps : IndexInHull → DefFwd → Fwd
  fwd-from-gaps ih df δ δ∈M oπδ Lδ∈M z z∈ =
    PT.rec (snd (z ∈ˢ Lset (HS.C.π δ))) step₁ (π-member' (Lset δ) z z∈)
    where
    step₁ : Σ[ y ∈ SV.S ]
              (⟨ y ∈ˢ Lset δ ⟩ × ⟨ y ∈ˢ HS.M ⟩ × (HS.C.π y ≡ z))
          → ⟨ z ∈ˢ Lset (HS.C.π δ) ⟩
    step₁ (y , y∈Lδ , y∈M , πy≡z) =
      subst (λ w → ⟨ w ∈ˢ Lset (HS.C.π δ) ⟩) πy≡z
        (PT.rec (snd (HS.C.π y ∈ˢ Lset (HS.C.π δ))) step₂
          (Lset-out δ y y∈Lδ))
      where
      step₂ : Σ[ β ∈ SV.S ] (⟨ β ∈ˢ δ ⟩ × ⟨ y ∈ˢ 𝒟ₒ (Lset β) ⟩)
            → ⟨ HS.C.π y ∈ˢ Lset (HS.C.π δ) ⟩
      step₂ (β , β∈δ , y∈𝒟β) =
        PT.rec (snd (HS.C.π y ∈ˢ Lset (HS.C.π δ))) step₃
          (ih δ δ∈M oπδ β β∈δ y y∈M y∈𝒟β)
        where
        step₃ : Σ[ β' ∈ SV.S ]
                  (⟨ β' ∈ˢ δ ⟩ × ⟨ β' ∈ˢ HS.M ⟩ × ⟨ y ∈ˢ 𝒟ₒ (Lset β') ⟩)
              → ⟨ HS.C.π y ∈ˢ Lset (HS.C.π δ) ⟩
        step₃ (β' , β'∈δ , β'∈M , y∈𝒟β') =
          Lset-in (HS.C.π δ) (HS.C.π β') (HS.C.π y)
            (π-into δ β' β'∈δ β'∈M)
            (df β' y β'∈M y∈M y∈𝒟β')

  -- BACKWARD HALF, from the backward definability gap alone: the index
  -- gap does NOT fire here, because every member of `HS.C.π δ` is by
  -- construction the image of a hull member of δ.
  bwd-from-gap : DefBwd → Bwd
  bwd-from-gap db δ δ∈M oπδ Lδ∈M z z∈ =
    PT.rec (snd (z ∈ˢ HS.C.π (Lset δ))) step₁ (Lset-out (HS.C.π δ) z z∈)
    where
    step₁ : Σ[ γ ∈ SV.S ] (⟨ γ ∈ˢ HS.C.π δ ⟩ × ⟨ z ∈ˢ 𝒟ₒ (Lset γ) ⟩)
          → ⟨ z ∈ˢ HS.C.π (Lset δ) ⟩
    step₁ (γ , γ∈πδ , z∈𝒟γ) =
      PT.rec (snd (z ∈ˢ HS.C.π (Lset δ))) step₂ (π-member' δ γ γ∈πδ)
      where
      step₂ : Σ[ β ∈ SV.S ]
                (⟨ β ∈ˢ δ ⟩ × ⟨ β ∈ˢ HS.M ⟩ × (HS.C.π β ≡ γ))
            → ⟨ z ∈ˢ HS.C.π (Lset δ) ⟩
      step₂ (β , β∈δ , β∈M , πβ≡γ) =
        PT.rec (snd (z ∈ˢ HS.C.π (Lset δ))) step₃
          (db β z β∈M
            (subst (λ w → ⟨ z ∈ˢ 𝒟ₒ (Lset w) ⟩) (sym πβ≡γ) z∈𝒟γ))
        where
        step₃ : Σ[ y ∈ SV.S ]
                  (⟨ y ∈ˢ 𝒟ₒ (Lset β) ⟩ × ⟨ y ∈ˢ HS.M ⟩ × (HS.C.π y ≡ z))
              → ⟨ z ∈ˢ HS.C.π (Lset δ) ⟩
        step₃ (y , y∈𝒟β , y∈M , πy≡z) =
          subst (λ w → ⟨ w ∈ˢ HS.C.π (Lset δ) ⟩) πy≡z
            (π-into (Lset δ) y (Lset-in δ β y β∈δ y∈𝒟β) y∈M)

  -- THE ASSEMBLY.  The obligation, from the three gaps and nothing else.
  commute-from-gaps : IndexInHull → DefFwd → DefBwd → Commute
  commute-from-gaps ih df db =
    halves-give-commute (fwd-from-gaps ih df) (bwd-from-gap db)

  -- ===================================================================
  -- SECTION 4.  PREMISE 4, MEASURED.  THE ORDINAL HYPOTHESIS DOES NO
  -- WORK IN THE REDUCTION.
  --
  --   The brief's premise 4 says the obligation's `IsOrd (HS.C.π δ)`
  --   "excludes exactly" the obstruction [LJ-1.477] named, and calls
  --   that the whole reason this is a dispatch and not a repeat.
  --
  --   SECTION 3 NEVER READ THAT HYPOTHESIS.  `fwd-from-gaps` and
  --   `bwd-from-gap` bind `oπδ` and pass it to `ih` unexamined; no row
  --   of either term eliminates it.  This section makes that checkable
  --   rather than asserted: it restates the SAME three gaps with the
  --   ordinality DROPPED, and derives the MORE GENERAL commute, the one
  --   [LJ-1.477] attacked (its `PiCommuteLset`,
  --   agents/tasks/LJ-1-477/Probe477.agda:100-102).  It typechecks.  So
  --   the hypothesis buys nothing between the obligation and the three
  --   gaps, and whatever it excludes it must exclude INSIDE
  --   `IndexInHull`, which is the only gap whose statement it can
  --   reach.
  --
  --   THIS IS NOT A REFUTATION OF THE OBLIGATION.  It is a measurement
  --   of where the hypothesis can and cannot be spent.
  -- ===================================================================

  CommuteNoOrd : Type (ℓ-suc ℓ)
  CommuteNoOrd =
    (δ : SV.S) → ⟨ δ ∈ˢ HS.M ⟩ → ⟨ Lset δ ∈ˢ HS.M ⟩
    → HS.C.π (Lset δ) ≡ Lset (HS.C.π δ)

  IndexInHullNoOrd : Type (ℓ-suc ℓ)
  IndexInHullNoOrd =
    (δ : SV.S) → ⟨ δ ∈ˢ HS.M ⟩
    → (β : SV.S) → ⟨ β ∈ˢ δ ⟩
    → (y : SV.S) → ⟨ y ∈ˢ HS.M ⟩ → ⟨ y ∈ˢ 𝒟ₒ (Lset β) ⟩
    → ∥ Σ[ β' ∈ SV.S ]
         (⟨ β' ∈ˢ δ ⟩ × ⟨ β' ∈ˢ HS.M ⟩ × ⟨ y ∈ˢ 𝒟ₒ (Lset β') ⟩) ∥₁

  -- the same assembly, ordinality nowhere in it
  commute-no-ord-from-gaps
    : IndexInHullNoOrd → DefFwd → DefBwd → CommuteNoOrd
  commute-no-ord-from-gaps ih df db δ δ∈M Lδ∈M =
    extensionalV (λ x → ⇔toPath (fwd x) (bwd x))
    where
    fwd : (z : SV.S) → ⟨ z ∈ˢ HS.C.π (Lset δ) ⟩
        → ⟨ z ∈ˢ Lset (HS.C.π δ) ⟩
    fwd z z∈ =
      PT.rec (snd (z ∈ˢ Lset (HS.C.π δ))) step₁ (π-member' (Lset δ) z z∈)
      where
      step₁ : Σ[ y ∈ SV.S ]
                (⟨ y ∈ˢ Lset δ ⟩ × ⟨ y ∈ˢ HS.M ⟩ × (HS.C.π y ≡ z))
            → ⟨ z ∈ˢ Lset (HS.C.π δ) ⟩
      step₁ (y , y∈Lδ , y∈M , πy≡z) =
        subst (λ w → ⟨ w ∈ˢ Lset (HS.C.π δ) ⟩) πy≡z
          (PT.rec (snd (HS.C.π y ∈ˢ Lset (HS.C.π δ))) step₂
            (Lset-out δ y y∈Lδ))
        where
        step₂ : Σ[ β ∈ SV.S ] (⟨ β ∈ˢ δ ⟩ × ⟨ y ∈ˢ 𝒟ₒ (Lset β) ⟩)
              → ⟨ HS.C.π y ∈ˢ Lset (HS.C.π δ) ⟩
        step₂ (β , β∈δ , y∈𝒟β) =
          PT.rec (snd (HS.C.π y ∈ˢ Lset (HS.C.π δ))) step₃
            (ih δ δ∈M β β∈δ y y∈M y∈𝒟β)
          where
          step₃ : Σ[ β' ∈ SV.S ]
                    (⟨ β' ∈ˢ δ ⟩ × ⟨ β' ∈ˢ HS.M ⟩ × ⟨ y ∈ˢ 𝒟ₒ (Lset β') ⟩)
                → ⟨ HS.C.π y ∈ˢ Lset (HS.C.π δ) ⟩
          step₃ (β' , β'∈δ , β'∈M , y∈𝒟β') =
            Lset-in (HS.C.π δ) (HS.C.π β') (HS.C.π y)
              (π-into δ β' β'∈δ β'∈M)
              (df β' y β'∈M y∈M y∈𝒟β')
    bwd : (z : SV.S) → ⟨ z ∈ˢ Lset (HS.C.π δ) ⟩
        → ⟨ z ∈ˢ HS.C.π (Lset δ) ⟩
    bwd z z∈ =
      PT.rec (snd (z ∈ˢ HS.C.π (Lset δ))) step₁ (Lset-out (HS.C.π δ) z z∈)
      where
      step₁ : Σ[ γ ∈ SV.S ] (⟨ γ ∈ˢ HS.C.π δ ⟩ × ⟨ z ∈ˢ 𝒟ₒ (Lset γ) ⟩)
            → ⟨ z ∈ˢ HS.C.π (Lset δ) ⟩
      step₁ (γ , γ∈πδ , z∈𝒟γ) =
        PT.rec (snd (z ∈ˢ HS.C.π (Lset δ))) step₂ (π-member' δ γ γ∈πδ)
        where
        step₂ : Σ[ β ∈ SV.S ]
                  (⟨ β ∈ˢ δ ⟩ × ⟨ β ∈ˢ HS.M ⟩ × (HS.C.π β ≡ γ))
              → ⟨ z ∈ˢ HS.C.π (Lset δ) ⟩
        step₂ (β , β∈δ , β∈M , πβ≡γ) =
          PT.rec (snd (z ∈ˢ HS.C.π (Lset δ))) step₃
            (db β z β∈M
              (subst (λ w → ⟨ z ∈ˢ 𝒟ₒ (Lset w) ⟩) (sym πβ≡γ) z∈𝒟γ))
          where
          step₃ : Σ[ y ∈ SV.S ]
                    (⟨ y ∈ˢ 𝒟ₒ (Lset β) ⟩ × ⟨ y ∈ˢ HS.M ⟩
                     × (HS.C.π y ≡ z))
                → ⟨ z ∈ˢ HS.C.π (Lset δ) ⟩
          step₃ (y , y∈𝒟β , y∈M , πy≡z) =
            subst (λ w → ⟨ w ∈ˢ HS.C.π (Lset δ) ⟩) πy≡z
              (π-into (Lset δ) y (Lset-in δ β y β∈δ y∈𝒟β) y∈M)

  -- and the ordinal-hypothesised obligation is a WEAKENING of it, so
  -- nothing the hypothesis could have bought is lost by dropping it
  no-ord-gives-commute : CommuteNoOrd → Commute
  no-ord-gives-commute c δ δ∈M oπδ Lδ∈M = c δ δ∈M Lδ∈M

  -- the ordinal gap is a weakening of the ordinal-free gap, the same way
  ord-gap-from-no-ord : IndexInHullNoOrd → IndexInHull
  ord-gap-from-no-ord ih δ δ∈M oπδ = ih δ δ∈M

  -- ===================================================================
  -- SECTION 5.  THE RESIDUE, NAMED, AND WHERE IT IS ALREADY QUEUED.
  --
  --   THE OBLIGATION IS NOT INHABITED HERE.  No name
  --   `commute-at-ordinal` is declared in this file.  What is delivered
  --   is `commute-from-gaps` (section 3): the obligation follows from
  --   `IndexInHull`, `DefFwd` and `DefBwd`, and from nothing else.
  --
  --   ALL THREE GAPS HAVE ONE PRODUCER, AND IT IS UNBUILT.  The hull is
  --   closed under DEFINABLE witnesses and only those: `hull-closed`
  --   (src/L/Hull.lagda.md:415-421) takes a `Formula Code 1` and
  --   returns a hull member satisfying it.  Each gap asks for a hull
  --   member picked out by a condition that mentions `Lset` or `𝒟ₒ`:
  --     IndexInHull  wants the index β' IN the hull, picked by
  --                  "y ∈ 𝒟ₒ (Lset β')";
  --     DefBwd       wants the preimage y IN the hull, picked by
  --                  "y ∈ 𝒟ₒ (Lset β) and π y ≡ z";
  --     DefFwd       wants the defining formula of y to survive π,
  --                  which is the same definability read downward.
  --   So each needs `Lset` to be NAMED in the hull's language, which is
  --   `lset-code` (agents/tasks/LJ-1-462/Probe462.agda:109-111), step 3
  --   of [LJ-1.462]'s four.  `grep -rn "lset-code" src/` returns
  --   nothing.  [LJ-1.474] is GO on `lset-codes`, the vector of
  --   CONSTANT codes of the graph formula, and its own report says in
  --   terms "I did not inhabit `levelIn` or `lset-code`"
  --   (agents/tasks/LJ-1-474/lj-1.474-report.md:74-75).
  --
  --   SO THE COMMUTE IS NOT A FOURTH INDEPENDENT DEBT.  It is step 3's
  --   consumer, and [LJ-1.477] said so in prose without a type
  --   ("it needs `π` to commute with `𝒟ₒ`, and it needs `Lset-out`
  --   witnesses to lie in `M`").  Section 3 is that prose as three
  --   types, with everything around them discharged.
  -- ===================================================================

  -- the residue, as one type: what a successor task must inhabit
  Residue : Type (ℓ-suc ℓ)
  Residue = IndexInHull × DefFwd × DefBwd

  residue-suffices : Residue → Commute
  residue-suffices (ih , df , db) = commute-from-gaps ih df db
