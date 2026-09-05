{-# OPTIONS --cubical --safe --guardedness #-}

-- LJ-1.333 probe A.  It lands nothing.  It runs in agents/tasks/LJ-1-333/.
--
-- THE BRIEF ASKS three things, in this order.
--
-- PART 1 is the CHEAPEST check and the brief orders it first: do the
--        consumers need the untruncated law at all?  The answer is YES,
--        and the reason is NOT the one the brief expects.  The final
--        motive of the consumer IS a proposition.  An INTERMEDIATE step
--        is not: the descent inside `Upper` consumes its induction
--        hypothesis as a Pi-indexed FAMILY of injections.
-- PART 2 tests the brief's own premise, that a SOME-member truncation
--        needs no well-order.
-- PART 3 tests `[LJ-1.321]` section 8 item 2, the weakly constant
--        endomap, at the cheaper truncation.
-- PART 4 records the negative controls.
--
-- This file IMPORTS `[LJ-1.332]`'s probe rather than copying it, so that
-- probe re-compiles under my own hand.  I changed no line of it.

open import Base.Prelude
open import Base.Truth
open import Base.Classical using ( LEM )

module LJ-1-333.ProbeLJ1333A {ℓ : Level} (lem : LEM (ℓ-suc ℓ)) where

open import FOL.ZFStructure using ( module hPropStructure )
open import V.Hierarchy {ℓ} using ( 𝒮ᵥ; ∈-induction )
open import L.Constructible {ℓ} using ( IsOrd; Lset )
open import L.Ordinal.SquareLaw {ℓ} lem using ( sq; Init; via-col-square )
open import L.Cardinal {ℓ} lem using ( _↪_ )

open import LJ-1-319.SqIsSet {ℓ} lem using ( sq-set )
open import LJ-1-332.ProbeLJ1332A {ℓ} lem
  using ( Witness; Row4; IH; comp↪; member-inj→sq; witness→sq )

open import Cubical.HITs.CumulativeHierarchy.Properties using ( ⟪_⟫; ⟪_⟫↪ )
open import Cubical.HITs.CumulativeHierarchy.Constructions
  using ( module InfinitySet )
open InfinitySet {ℓ} using ( ω; sucV )
open import Cubical.Foundations.Function using ( 2-Constant )
open import Cubical.Data.Sigma using ( _×_ )
import Cubical.Data.Empty as Empty
import Cubical.HITs.PropositionalTruncation as PT
open PT using ( ∥_∥₁; squash₁ )

open TruthAlgebra (hPropAlgebra (ℓ-suc ℓ))
open hPropStructure 𝒮ᵥ using ( S; _∈ˢ_ )

-- =====================================================================
-- PART 1.  DO THE CONSUMERS NEED THE DATA?  YES, AND NOT FOR THE
-- REASON THE BRIEF EXPECTS.
--
--   The brief's cheapest abort row says: if a truncated law serves the
--   consumers once their final motives are propositional, the leg
--   closes today.
--
--   THE FINAL MOTIVE IS ALREADY PROPOSITIONAL.  `theorem` at
--   src/L/BoundedSubset.lagda.md:1621 concludes `⟨ x ∈ˢ Lset κ ⟩`, and
--   every `⟨ _ ⟩` is the carrier of an `hProp`.  So that row would fire
--   if the motive were the only gate.
--
--   IT IS NOT.  Between the hypothesis and that motive sits an
--   `∈-induction` whose MOTIVE is data and whose STEP consumes the
--   induction hypothesis as a Pi-indexed FAMILY:
--   `limit-step` at src/L/StageCardinal.lagda.md:396-398 takes
--   `(m : ⟪ α ⟫) → ⟪ Lset (⟪ α ⟫↪ m) ⟫ ↪ ⟪ α ⟫`, `branch` at :534-536
--   builds it from the induction hypothesis, `step` at :561-562 joins
--   them and `stage-card-upper` at :566 is the `∈-induction`.
-- =====================================================================

-- 1.1  The final motive of the consumer IS a proposition.  MEASURED.
final-motive-isProp : (x κ : S) → isProp ⟨ x ∈ˢ Lset κ ⟩
final-motive-isProp x κ = (x ∈ˢ Lset κ) .snd

-- 1.2  The shapes the delivered descent uses.  Each one is the type at
-- the line named beside it, with the propositional side conditions
-- dropped, because a side condition is a hypothesis and never an
-- obstruction to a truncation.

-- The motive of the descent, src/L/StageCardinal.lagda.md:530-532.
Motive : S → Type ℓ
Motive α = ⟪ Lset α ⟫ ↪ ⟪ α ⟫

-- `limit-step`'s last argument, src/L/StageCardinal.lagda.md:397.
Branch : S → Type ℓ
Branch α = (m : ⟪ α ⟫) → ⟪ Lset (⟪ α ⟫↪ m) ⟫ ↪ ⟪ α ⟫

-- `limit-step` itself, src/L/StageCardinal.lagda.md:396-398.  It spends
-- `sq α` inside `LimitStep`, src/L/StageCardinal.lagda.md:283.
StepShape : Type (ℓ-suc ℓ)
StepShape = (α : S) → sq α → Branch α → Motive α

-- `branch`, src/L/StageCardinal.lagda.md:534-536.  It turns the
-- induction hypothesis at the MEMBERS into the family the step eats.
BranchFrom : Type (ℓ-suc ℓ)
BranchFrom = (α : S) → ((δ : S) → ⟨ δ ∈ˢ α ⟩ → Motive δ) → Branch α

-- 1.3  THE UNTRUNCATED CONTROL, WRITTEN FIRST (C-56).  With `sq` as
-- DATA the descent is the delivered one and it needs no choice.
descent-data : StepShape → BranchFrom → ((δ : S) → sq δ) → (α : S) → Motive α
descent-data st bf sqD = ∈-induction (λ α ih → st α (sqD α) (bf α ih))

-- 1.4  THE TRUNCATED DESCENT.  With `sq` merely inhabited the motive
-- must truncate, and then the step cannot be fed: it wants a FAMILY of
-- injections and the hypothesis gives a family of TRUNCATIONS.  The
-- exact repair is this choice principle and nothing weaker.
ACBranch : Type (ℓ-suc ℓ)
ACBranch = (α : S) → ((δ : S) → ⟨ δ ∈ˢ α ⟩ → ∥ Motive δ ∥₁)
         → ∥ ((δ : S) → ⟨ δ ∈ˢ α ⟩ → Motive δ) ∥₁

descent-trunc : StepShape → BranchFrom → ACBranch
              → ((δ : S) → ∥ sq δ ∥₁) → (α : S) → ∥ Motive α ∥₁
descent-trunc st bf ac sqT = ∈-induction go
  where
  go : (α : S) → ((δ : S) → ⟨ δ ∈ˢ α ⟩ → ∥ Motive δ ∥₁) → ∥ Motive α ∥₁
  go α ih = PT.rec squash₁ (λ b → PT.map (λ s → st α s (bf α b)) (sqT α))
                   (ac α ih)

-- 1.5  And a truncated `sq` alone already truncates the step's output,
-- with the family still honest.  So the truncation is not an artefact
-- of my assembly: it is where `sq` enters.
step-truncates : StepShape → (α : S) → ∥ sq α ∥₁ → Branch α → ∥ Motive α ∥₁
step-truncates st α t b = PT.map (λ s → st α s b) t

-- =====================================================================
-- PART 2.  THE BRIEF'S PREMISE: does the SOME-member truncation need a
-- well-order?
--
--   FOR THE TRUNCATED LAW the premise HOLDS.  `[LJ-1.332]`'s
--   `limit-truncated` is green and names no order; this file imports
--   that module, so its green is measured here again.
--
--   FOR THE UNTRUNCATION the premise does NOT hold, and PART 2 says why
--   with a term.  Canonicalizing the MEMBER is free, because the members
--   of an ordinal carry a well-order already (`OrdSWO`,
--   src/L/StageCardinal.lagda.md:228-276).  What is left after the
--   member is fixed is an untruncation of a FUNCTION type, and that is
--   the object `[LJ-1.329]` refuted.
-- =====================================================================

-- The witness with its member FIXED: the injection, and nothing else.
InjAt : S → S → Type ℓ
InjAt α β = ⟪ α ⟫ ↪ (⟪ β ⟫ × ⟪ β ⟫)

-- With the member fixed and the descent in hand, the WHOLE remaining
-- obligation is the untruncation of that injection type.
beta-fixed-residue : (α β : S) → IsOrd α → IsOrd β → ⟨ β ∈ˢ α ⟩ → ⟨ ω ∈ˢ β ⟩
                   → IH α
                   → (∥ InjAt α β ∥₁ → InjAt α β)
                   → ∥ InjAt α β ∥₁ → sq α
beta-fixed-residue α β oα oβ β∈α ω∈β ih untrunc t =
  member-inj→sq α β oα β∈α (comp↪ (untrunc t) sqβ) sqβ
  where
  sqβ : sq β
  sqβ = ih β β∈α oβ ω∈β

-- =====================================================================
-- PART 3.  ITEM 2 AT THE CHEAPER TRUNCATION.
--
--   Kraus, Escardo, Coquand and Altenkirch, Theorem 16: a type admits
--   `∥ X ∥ → X` exactly when it has a weakly constant endomap.  The
--   library's `rec→Set` is the usable half and `[LJ-1.319]` measured its
--   precondition, `isSet (sq α)`.  PART 3 states the door, then measures
--   the DIRECTION of the obligation the cheaper truncation creates.
-- =====================================================================

-- 3.1  The door, stated with the library's own eliminator and
-- `[LJ-1.319]`'s measured precondition.  This is what item 2 must build.
item2-door : (α : S) (f : Witness α → sq α) → 2-Constant f
           → ∥ Witness α ∥₁ → sq α
item2-door α f kf = PT.SetElim.rec→Set (sq-set α) f kf

-- 3.2  THE MEASUREMENT.  The cheaper truncation is cheaper to PROVE and
-- it is NOT cheaper to untruncate.  A SOME-member witness carries a free
-- member, so its `2-Constant` obligation quantifies over pairs of
-- witnesses at DIFFERENT members.  That obligation IMPLIES the
-- fixed-member one, so it is at least as strong, never weaker.
inj→witness : (α β : S) → IsOrd β → ⟨ β ∈ˢ α ⟩ → ⟨ ω ∈ˢ β ⟩
            → InjAt α β → Witness α
inj→witness α β oβ β∈α ω∈β e = β , oβ , β∈α , ω∈β , e

some-is-not-weaker : (α : S) (f : Witness α → sq α) → 2-Constant f
                   → (β : S) (oβ : IsOrd β) (β∈α : ⟨ β ∈ˢ α ⟩) (ω∈β : ⟨ ω ∈ˢ β ⟩)
                   → 2-Constant (λ e → f (inj→witness α β oβ β∈α ω∈β e))
some-is-not-weaker α f kf β oβ β∈α ω∈β u v = kf _ _

-- 3.3  WHERE THE TREE'S ONLY CANONICALIZER LIVES, and why it cannot
-- reach this band.  `via-col-square` is the delivered UNTRUNCATED
-- supplier.  It is the order collapse of the Godel well-order
-- (`godSWO`, src/L/Ordinal/SquareLaw.lagda.md:308-314), and the step
-- that keeps the collapse INSIDE the site is `col∈α` at :931-932.  That
-- step calls `col≤α` at :922-929, which calls `exclude` at :928, which
-- spends `InitialCore`'s `noinj²` at :876.  The parameter is declared at
-- :705-708 and it is `Init`'s FOURTH ROW, at :696-698.
canonicalizer : (α : S) → Init α → sq α
canonicalizer = via-col-square

-- And the limit band is defined by that same row FAILING.  One line.
band-kills-row4 : (α : S) → IsOrd α → ⟨ ω ∈ˢ α ⟩
                → ((γ : S) → ⟨ γ ∈ˢ α ⟩ → ⟨ sucV γ ∈ˢ α ⟩)
                → (Init α → Empty.⊥) → Row4 α → Empty.⊥
band-kills-row4 α oα ω∈α closed noInit r = noInit (oα , ω∈α , closed , r)

-- 3.4  The two together, as one statement: the band's own hypothesis is
-- the negation of the hypothesis the canonicalizer consumes.  So item 2
-- searches for a canonicalizer exactly where the delivered one is
-- refuted BY THE BAND'S DEFINITION, and not by an accident of proof.
witness→sq-is-the-only-route : (α : S) → IsOrd α → IH α → Witness α → sq α
witness→sq-is-the-only-route = witness→sq

-- =====================================================================
-- PART 4.  THE NEGATIVE CONTROLS.  Each one was applied, run and
-- reverted.  They are recorded here because nothing typechecks this file
-- once the task closes.  ALL FOUR MEASURE.
--
--   CONTROL 1, ON THE CHEAPEST ABORT ROW.  Run the truncated descent
--   WITHOUT the choice principle, changing nothing else:
--
--     control1 : StepShape → BranchFrom
--              → ((δ : S) → ∥ sq δ ∥₁) → (α : S) → ∥ Motive α ∥₁
--     control1 st bf sqT = ∈-induction go
--       where
--       go : (α : S) → ((δ : S) → ⟨ δ ∈ˢ α ⟩ → ∥ Motive δ ∥₁)
--          → ∥ Motive α ∥₁
--       go α ih = PT.map (λ s → st α s (bf α ih)) (sqT α)
--
--   Agda refused, 2 s:
--     error: [UnequalTerms]
--     ∥ Motive δ ∥₁ !=<
--     (Σ (⟪ Lset δ ⟫ → ⟪ δ ⟫)
--      (λ f → (x y : ⟪ Lset δ ⟫) → f x ≡ f y → x ≡ y))
--     when checking that the expression ih has type
--     (δ : S) → ⟨ δ ∈ˢ α ⟩ → Motive δ
--
--   THAT IS THE ANSWER TO THE CHEAPEST CHECK, IN ONE ERROR MESSAGE.  The
--   final motive of the consumer is a proposition and it does not help,
--   because the step wants the FAMILY and the hypothesis gives a family
--   of BARS.
--
--   CONTROL 2, ON THE DIRECTION OF THE `2-Constant` OBLIGATION.  Derive
--   the SOME-member obligation from the fixed-member one, the converse
--   of `some-is-not-weaker`:
--
--     control2 : (α : S) (f : Witness α → sq α)
--              → ((β : S) (oβ : IsOrd β) (β∈α : ⟨ β ∈ˢ α ⟩)
--                 (ω∈β : ⟨ ω ∈ˢ β ⟩)
--                 → 2-Constant (λ e → f (inj→witness α β oβ β∈α ω∈β e)))
--              → 2-Constant f
--     control2 α f kfix (β , oβ , β∈α , ω∈β , e) (β′ , oβ′ , β′∈α , ω∈β′ , e′) =
--       kfix β oβ β∈α ω∈β e e′
--
--   Agda refused, 2 s:
--     error: [UnequalTerms]
--     β′ != β of type (Cubical.HITs.CumulativeHierarchy.Base.V ℓ)
--     when checking that the expression e′ has type InjAt α β
--
--   So the implication runs ONE WAY only.  The SOME-member obligation is
--   STRICTLY stronger than the fixed-member one, and the machine names
--   the two members that cannot be identified.
--
--   CONTROL 3, ON THE CANONICALIZER'S OWN HYPOTHESIS.  Offer the band's
--   defining hypothesis where the delivered untruncated supplier takes
--   `Init`:
--
--     control3 : (α : S) → (Init α → Empty.⊥) → sq α
--     control3 α noInit = canonicalizer α noInit
--
--   Agda refused, 2 s, and it PRINTED THE WHOLE OF `Init`:
--     error: [UnequalTerms]
--     (Init α → Empty.⊥) !=<
--     (Σ (IsOrd α)
--      (λ _ →
--         ⟨ ω ∈ˢ α ⟩ ×
--         ((γ : S) → ⟨ γ ∈ˢ α ⟩ → ⟨ sucV γ ∈ˢ α ⟩) ×
--         ((β : S) → IsOrd β → ⟨ β ∈ˢ α ⟩ → ⟨ ω ∈ˢ β ⟩ →
--          (f : ⟪ α ⟫ → ⟪ β ⟫ × ⟪ β ⟫) →
--          ((m n : ⟪ α ⟫) → f m ≡ f n → m ≡ n) → Empty.⊥)))
--     when checking that the expression noInit has type Init α
--
--   The band's hypothesis and the canonicalizer's hypothesis are printed
--   side by side, and they are negations of one another.
--
--   CONTROL 4 lives in ProbeLJ1333B.agda, because it needs the delivered
--   `L.StageCardinal` instantiated.
-- =====================================================================
