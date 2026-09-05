{-# OPTIONS --cubical --safe --guardedness #-}

-- [LJ-1.573]  Row 2, `SqCollectAt`, and the principle it is.
--
-- SECTION 1 is W3, written first and typechecked ALONE at
--   agents/tasks/LJ-1-573/runs/W3.agda.
-- SECTION 2 answers D-10.  The tree HAS a uniform selector, it is
--   named, and this row is an instance of it.  The reduction is a term
--   and not a claim.
-- SECTION 3 is the narrowing, and it is the finding: the row does NOT
--   want a set-indexed choice principle.  It wants ONE untruncated
--   injection, and that buys LEVEL 3 rather than LEVEL 2.
-- SECTION 4 re-measures [LJ-1.568]'s definability cure AT THIS SITE.
-- SECTION 5 writes down what is not here.
--
-- Nothing is postulated.  Nothing lands in src/.  No hole.

open import Base.Prelude
open import Base.Truth
open import Base.Classical using ( LEM )

module LJ-1-573.Probe573 {ℓ : Level} (lem : LEM (ℓ-suc ℓ)) where

open import Base.Choice using ( SetChoice )
open import FOL.ZFStructure using ( module hPropStructure )
open import V.Hierarchy {ℓ} using ( 𝒮ᵥ; ∈-induction )
open import V.Presentation {ℓ} using ( member; fiber )
open import L.Constructible {ℓ} using ( 𝒮ʟ; IsOrd; isL; Lset )
open import L.Ordinal {ℓ} using ( ω-ord )
open import L.Ordinal.Linear {ℓ} lem using ( ord-tri )
open import L.Ordinal.SquareLaw {ℓ} lem using ( sq; Init; via-col-square )
open import L.InjChain {ℓ} lem using ( squareω )
open import L.Cardinal {ℓ} lem using ( _↪_; InjCode )
open import L.CantorBernstein {ℓ} lem using ( readL )
open import L.StageBound {ℓ} lem using ( SqFam; SqCollect )
import L.SquareLawClosed

import LJ-1-550.Probe550 {ℓ} lem as P550

open import Cubical.HITs.CumulativeHierarchy.Base using ( setIsSet )
open import Cubical.HITs.CumulativeHierarchy.Constructions
  using ( module InfinitySet )
open InfinitySet {ℓ} using ( ω; sucV )
open import Cubical.HITs.CumulativeHierarchy.Properties using ( ⟪_⟫ )
open import Cubical.Data.Sigma using ( _×_ )
open import Cubical.Data.Sum using ( _⊎_; inl; inr )
open import Cubical.Foundations.HLevels using ( isSetΣ; isPropΠ; isProp× )
open import Cubical.Foundations.Prelude using ( isProp→isSet )
import Cubical.Data.Empty as Empty
import Cubical.HITs.PropositionalTruncation as PT
open PT using ( ∥_∥₁; ∣_∣₁ )

open TruthAlgebra (hPropAlgebra (ℓ-suc ℓ))
open hPropStructure 𝒮ᵥ using ( _∈ˢ_ )

module SV = hPropStructure 𝒮ᵥ
module SL = hPropStructure 𝒮ʟ

-- =====================================================================
-- SECTION 1.  W3.  `SqFam (fst κ)` UNFOLDED ONE STEP, TYPE ONLY.
--
--   Copied from agents/tasks/LJ-1-573/runs/W3.agda, which the brief
--   ordered written FIRST and typechecked ALONE.  It exits 0 there
--   (agents/tasks/LJ-1-573/runs/w3-2.out).
--
--   THE CODOMAIN IS THE ANSWER.  A Σ of an AMBIENT function
--   `⟪ δ ⟫ × ⟪ δ ⟫ → ⟪ δ ⟫` with a proof that it is injective.  No
--   code, no `isL`, no `Lset`, no `𝒮ʟ`, no `⊨` under the arrow.
-- =====================================================================

w3-sqfam-at : SL.S → Type (ℓ-suc ℓ)
w3-sqfam-at κ =
    (δ : SV.S) → ⟨ δ ∈ˢ sucV (fst κ) ⟩ → (⟨ δ ∈ˢ ω ⟩ → Empty.⊥)
  → Σ[ f ∈ (⟪ δ ⟫ × ⟪ δ ⟫ → ⟪ δ ⟫) ]
      ((u v : ⟪ δ ⟫ × ⟪ δ ⟫) → f u ≡ f v → u ≡ v)

-- And it IS src/'s own `SqFam`, both directions, by an identity
-- function.  So section 1 is not a paraphrase of the chapter: it is
-- the chapter.
w3-is-sqfam : (κ : SL.S) → w3-sqfam-at κ → SqFam (fst κ)
w3-is-sqfam κ f = f

sqfam-is-w3 : (κ : SL.S) → SqFam (fst κ) → w3-sqfam-at κ
sqfam-is-w3 κ f = f

-- The row, from [LJ-1.571] (Probe571.agda:162-163).  Copied letter for
-- letter, so this file measures THAT row and not a neighbour.
SqCollectAt : Type (ℓ-suc ℓ)
SqCollectAt = (κ : SL.S) → IsOrd (fst κ) → SqCollect (fst κ)

-- =====================================================================
-- SECTION 2.  D-10.  THIS IS A CHOICE PRINCIPLE, THE TREE ALREADY HAS
-- IT BY NAME, AND HERE IS THE REDUCTION AS A TERM.
--
--   The brief orders: "Say at file:line whether the tree has anything
--   that performs one, and name it."
--
--   IT DOES.  `SetChoice ℓ` at src/Base/Choice.lagda.md:54-56:
--
--     SetChoice ℓ = (X : Type ℓ) → isSet X → (B : X → Type ℓ)
--                 → ((x : X) → ∥ B x ∥₁) → ∥ ((x : X) → B x) ∥₁
--
--   `SqCollect α` IS that implication, with the binder and the two
--   side conditions collected into ONE index.  The recognition is at
--   the level of the definitions, and the owner has already ruled that
--   this recognition is COMMON KNOWLEDGE, in the charge of [LJ-1.376]
--   (agents/tasks/LJ-1-376/LJ-1.376.md:11): "`BandChoice` is an
--   instance of `SetChoice (ℓ-suc ℓ)`".  So no experiment is funded
--   here to DISCOVER it.  What is measured is the PRICE.
--
--   THE LEVEL IS `ℓ-suc ℓ`, AND THE MACHINE FIXED IT, NOT ME.  W3's
--   first run refused `Type ℓ`: "Type (ℓ-suc ℓ) != Type ℓ"
--   (agents/tasks/LJ-1-573/runs/w3-1.out:4-5).  The squares live at
--   `Type ℓ`; the side conditions are read through
--   `TruthAlgebra (hPropAlgebra (ℓ-suc ℓ))` and drag the index up.
-- =====================================================================

-- The index, collected.  This is the `X` of `SetChoice (ℓ-suc ℓ)`.
Ix : SV.S → Type (ℓ-suc ℓ)
Ix α = Σ[ δ ∈ SV.S ] (⟨ δ ∈ˢ sucV α ⟩ × (⟨ δ ∈ˢ ω ⟩ → Empty.⊥))

-- `isSet X` is `SetChoice`'s second argument and it is the h-set
-- restriction that keeps the principle honest
-- (src/Base/Choice.lagda.md:9-11).  The ambient carrier is an h-set by
-- the library's `setIsSet`, and the two side conditions are
-- propositions, so the Σ is an h-set with nothing assumed.
isSetIx : (α : SV.S) → isSet (Ix α)
isSetIx α = isSetΣ setIsSet
  (λ δ → isProp→isSet
    (isProp× (snd (δ ∈ˢ sucV α)) (isPropΠ (λ _ → Empty.isProp⊥))))

-- THE PRICE, AS A TERM.  `SetChoice (ℓ-suc ℓ)` gives the row outright.
-- The `Lift` is bookkeeping only: `sq δ` is at `Type ℓ` and the index
-- is at `Type (ℓ-suc ℓ)`, so the fibre is raised and lowered again.
sq-collect-at-from-choice : SetChoice (ℓ-suc ℓ) → SqCollectAt
sq-collect-at-from-choice sc κ _ ptw =
  PT.map (λ g δ δ∈ infδ → lower (g (δ , δ∈ , infδ)))
    (sc (Ix (fst κ)) (isSetIx (fst κ))
        (λ x → Lift (sq (fst x)))
        (λ x → PT.map lift (ptw (fst x) (fst (snd x)) (snd (snd x)))))

-- =====================================================================
-- SECTION 3.  THE NARROWING, AND IT IS THE FINDING OF THIS TASK.
--
--   Section 2 prices the row at a SET-INDEXED choice principle.  That
--   price is real but it is NOT TIGHT, and this section measures how
--   far it is from tight.
--
--   READ src/'s OWN RECURSION (src/L/SquareLawClosed.lagda.md:280-323).
--   It is four cases and only ONE of them truncates:
--
--     case 1, x ∈ ω          refuted by the infinitude hypothesis
--     case 2, x ≡ ω          `squareω`, BARE (src/L/InjChain.lagda.md:184)
--     case 3, fst κ ≡ x      `via-col-square`, BARE
--                            (src/L/Ordinal/SquareLaw.lagda.md:960-961)
--     case 4, fst κ ∈ x      `PT.map2` over `κ-injL`, TRUNCATED
--                            (src/L/SquareLawClosed.lagda.md:314-319)
--
--   Cases 2 and 3 hand back a bare square and `by-init` then throws it
--   away into `∣ _ ∣₁` only because the MOTIVE is truncated
--   (src/L/SquareLawClosed.lagda.md:306-310).  So the whole truncation
--   of `sq-trunc-closed` is bought by ONE term, `κ-injL a ox`, whose
--   own truncation enters at `InjP γ = ∥ Inj γ ∥₁ , squash₁`
--   (src/L/Cardinal.lagda.md:66-67), because `leastOf` wants an
--   hProp-valued predicate.
--
--   SO THE ROW DOES NOT WANT A CHOICE FUNCTION OVER A SET OF SQUARES.
--   It wants ONE untruncated least-cardinal injection.  Below is that
--   statement, and then the recursion rebuilt bare from it.
-- =====================================================================

module Bare (α : SV.S) (oα : IsOrd α) where

  module SLC = L.SquareLawClosed {ℓ} lem α oα
  open SLC using
    ( κL; κoL; κ-injL; isL-ord; init-at-kappa; kappa-decides
    ; kappa-not-fin; mem-incl; descent-core; band-ord )

  -- THE INPUT, AND IT IS SMALLER THAN `SqCollect` IN EVERY DIRECTION:
  -- one injection rather than a family of squares, no antecedent to
  -- discharge, and no truncation anywhere in it.  It is `κ-injL`
  -- (src/L/SquareLawClosed.lagda.md:82-85) with the `∥ ∥₁` removed.
  BareLeastInj : Type (ℓ-suc ℓ)
  BareLeastInj =
    (a : SL.S) (oa : IsOrd (fst a)) → ⟪ fst a ⟫ ↪ ⟪ fst (κL a oa) ⟫

  -- And it IS a section of `κ-injL` and not something adjacent: this
  -- term is the machine's word that the two have the same subject.
  bare-refines-trunc :
    BareLeastInj → (a : SL.S) (oa : IsOrd (fst a))
    → ∥ ⟪ fst a ⟫ ↪ ⟪ fst (κL a oa) ⟫ ∥₁
  bare-refines-trunc bi a oa = ∣ bi a oa ∣₁

  trunc-is-src : (a : SL.S) (oa : IsOrd (fst a))
    → ∥ ⟪ fst a ⟫ ↪ ⟪ fst (κL a oa) ⟫ ∥₁
  trunc-is-src = κ-injL

  -- src/'s `Goal` (src/L/SquareLawClosed.lagda.md:277-278) with the
  -- truncation removed and NOTHING else changed.
  BareGoal : SV.S → Type (ℓ-suc ℓ)
  BareGoal x = IsOrd x → (⟨ x ∈ˢ ω ⟩ → Empty.⊥) → sq x

  -- src/'s `step` (src/L/SquareLawClosed.lagda.md:280-323), case for
  -- case, with `PT.map2` at case 4 replaced by direct application and
  -- the two `∣ _ ∣₁` of cases 2 and 3 simply not written.
  bare-step : BareLeastInj
    → (x : SV.S) → ((y : SV.S) → ⟨ y ∈ˢ x ⟩ → BareGoal y) → BareGoal x
  bare-step bi x ih ox infx = go (ord-tri x ox ω ω-ord)
    where
    a : SL.S
    a = x , isL-ord x ox

    go : ⟨ x ∈ˢ ω ⟩ ⊎ ((x ≡ ω) ⊎ ⟨ ω ∈ˢ x ⟩) → sq x
    go (inl x∈ω) = Empty.rec (infx x∈ω)
    go (inr (inl x≡ω)) = subst sq (sym x≡ω) squareω
    go (inr (inr ω∈x)) = splitOwn (kappa-decides a ox)
      where
      κ : SL.S
      κ = κL a ox
      oκ : IsOrd (fst κ)
      oκ = κoL a ox

      ω∈κ : fst κ ≡ x → ⟨ ω ∈ˢ fst κ ⟩
      ω∈κ κ≡x = subst (λ w → ⟨ ω ∈ˢ w ⟩) (sym κ≡x) ω∈x

      -- `init-at-kappa` still wants the TRUNCATED pointwise law at the
      -- members, so the bare recursion pays it back with `∣ _ ∣₁`.
      -- Nothing is lost: `Init`'s fourth conjunct concludes `Empty.⊥`,
      -- a proposition, which is why src/ could spend a truncation there
      -- for free in the first place
      -- (src/L/SquareLawClosed.lagda.md:97-113).
      members : fst κ ≡ x
              → (β : SV.S) → IsOrd β → ⟨ β ∈ˢ fst κ ⟩
              → (⟨ β ∈ˢ ω ⟩ → Empty.⊥) → ∥ sq β ∥₁
      members κ≡x β oβ β∈κ infβ =
        ∣ ih β (subst (λ w → ⟨ β ∈ˢ w ⟩) κ≡x β∈κ) oβ infβ ∣₁

      by-init : fst κ ≡ x → sq x
      by-init κ≡x =
        subst sq κ≡x
          (via-col-square (fst κ)
            (init-at-kappa a ox (ω∈κ κ≡x) (members κ≡x)))

      -- CASE 4, AND THIS IS THE WHOLE DIFFERENCE.  src/ writes
      -- `PT.map2 ... (κ-injL a ox) (ih ...)`.  With the injection bare
      -- the `PT.map2` is an application and the goal never truncates.
      by-descent : ⟨ fst κ ∈ˢ x ⟩ → sq x
      by-descent κ∈x =
        descent-core a κ (mem-incl x (fst κ) ox κ∈x)
          (ih (fst κ) κ∈x oκ (kappa-not-fin x ox ω∈x))
          (bi a ox)

      splitOwn : (fst κ ≡ x) ⊎ ⟨ fst κ ∈ˢ x ⟩ → sq x
      splitOwn (inl κ≡x) = by-init κ≡x
      splitOwn (inr κ∈x) = by-descent κ∈x

  -- LEVEL 3 OUTRIGHT.  src/'s `sq-trunc-closed`
  -- (src/L/SquareLawClosed.lagda.md:325-328) with the truncation gone.
  bare-sq-closed : BareLeastInj → SqFam α
  bare-sq-closed bi δ δ∈ infδ =
    ∈-induction {P = BareGoal} (bare-step bi) δ (band-ord δ δ∈) infδ

-- =====================================================================
-- SECTION 3b.  WHAT THE BARE INJECTION BUYS, AT EVERY ORDINAL
-- L-CARDINAL.  IT IS MORE THAN THE ROW ASKS FOR.
--
--   `SqCollectAt` asks for LEVEL 2, the truncated family
--   ([LJ-1.571]'s ladder, Probe571.agda:113-115).  The bare injection
--   delivers LEVEL 3, the BARE family, which is the row 2 that
--   [LJ-1.571] found and shrank.  So this input does not merely pay
--   the collection step: it makes the collection step unnecessary.
-- =====================================================================

BareLeastInjAt : Type (ℓ-suc ℓ)
BareLeastInjAt = (α : SV.S) (oα : IsOrd α) → Bare.BareLeastInj α oα

-- LEVEL 3.  This type is `[LJ-1.550]`'s `SqAt` (Probe550.agda:309-310),
-- the ORIGINAL row 2, and the two identity functions below are the
-- machine's word that it is the same type and not a look-alike.
SqAtHere : Type (ℓ-suc ℓ)
SqAtHere = (κ : SL.S) → IsOrd (fst κ) → SqFam (fst κ)

sqat-is-p550 : SqAtHere → P550.SqAt
sqat-is-p550 f = f

p550-is-sqat : P550.SqAt → SqAtHere
p550-is-sqat f = f

sqat-from-bare-inj : BareLeastInjAt → SqAtHere
sqat-from-bare-inj bi κ oκ = Bare.bare-sq-closed (fst κ) oκ (bi (fst κ) oκ)

-- LEVEL 2, which is the row this brief names.  One `∣ _ ∣₁`, and the
-- antecedent of `SqCollect` is never read.
sq-collect-at-from-bare-inj : BareLeastInjAt → SqCollectAt
sq-collect-at-from-bare-inj bi κ oκ _ = ∣ sqat-from-bare-inj bi κ oκ ∣₁

-- =====================================================================
-- SECTION 4.  [LJ-1.568]'S CURE, RE-MEASURED AT THIS SITE.
--
--   The brief offers the hint and then forbids me to take it on trust:
--   "A measured cure does not transfer by analogy; re-measure it here"
--   (AGENTS.md:45).  Here is the measurement.
--
--   `[LJ-1.568]`'s `Def` needs no choice because the carve runs through
--   `hasSeparationL`, which takes an ARBITRARY formula
--   (src/L/Axioms/Full.lagda.md:144-145).  Its subject is `S` of `𝒮ʟ`
--   and its output is an L-set carved by a `Formula S 1`.
--
--   IT DOES NOT TRANSFER, AND SECTION 1 IS THE REASON.  The thing that
--   would have to be carved here is an inhabitant of `sq δ`, an
--   AMBIENT function `⟪ δ ⟫ × ⟪ δ ⟫ → ⟪ δ ⟫`.  W3 shows nothing under
--   the arrow mentions `isL`, `Lset`, `𝒮ʟ`, a code or `⊨`.  A formula
--   of the object language has no subject here.  `hasSeparationL`
--   cannot be pointed at this row at all.
--
--   BUT THE HINT IS RIGHT ABOUT THE NEIGHBOUR, AND SECTION 3 SAYS
--   WHICH ONE.  The object that actually has to be selected is not the
--   square.  It is the least-cardinal INJECTION, and
--   `dev/literature/truncation-and-selection.md:323` already named it:
--   "what is missing is a well-order on the INJECTIONS."
--
--   AND `L` HAS ONE, PROVED, WITH NO AMBIENT PRINCIPLE SPENT.
--   `hasChoiceL` (src/L/Choice/Transversal.lagda.md:382-384) is a
--   THEOREM of this tree, not a hypothesis.  It does not apply as it
--   stands, because `LeastCardInjL.Inj γ = ⟪ fst α ⟫ ↪ ⟪ fst γ ⟫` is
--   the AMBIENT injection type (src/L/Cardinal.lagda.md:47-48, 63-64)
--   and an ambient function is no member of `L`.
--
--   SO THE ONE QUESTION THIS ROW REDUCES TO IS WHETHER
--   `LeastCardInjL` CAN BE RESTATED OVER L-INTERNAL INJECTIONS.  That
--   is a change to src/ and a different row.  I NAME IT AND I DO NOT
--   DO IT.
-- =====================================================================

-- The ambient injection type this row runs on, restated here so the
-- claim above is checkable rather than believed.  It is `_↪_` of
-- src/L/Cardinal.lagda.md:47-48, at `Type ℓ`, with no `isL` on it.
AmbientInjHere : SV.S → SV.S → Type ℓ
AmbientInjHere x y = ⟪ x ⟫ ↪ ⟪ y ⟫

ambient-inj-is-src : (x y : SV.S) → AmbientInjHere x y → ⟪ x ⟫ ↪ ⟪ y ⟫
ambient-inj-is-src x y f = f

-- AND THE ARCHIVE ALREADY NAMED THE CURE, WITH A GREEN PROBE BEHIND IT.
-- `archive/dev/LJ-dispatch-index.md:371` records [LJ-1.314]: "Select the
-- CODE, not the function: InjCode is a proposition, so leastOf
-- untruncates it."  `[LJ-1.305]` is the same wall this row is standing
-- at, under the name `InjData` (archive/dev/LJ-dispatch-index.md:362).
--
-- THE BRIDGE IS A TERM AND IT IS ALREADY IN src/.  `readL` turns a CODE
-- into a BARE ambient injection with no truncation anywhere
-- (src/L/CantorBernstein.lagda.md:33-35).  So the untruncation this row
-- needs is available AT THE CODE and not at the function.
inj-from-code :
  (a b : SL.S) → Σ[ F ∈ SL.S ] InjCode F a b → ⟪ fst a ⟫ ↪ ⟪ fst b ⟫
inj-from-code = readL

-- WHAT IS TRUNCATED IS THE CODE'S EXISTENCE, NOT THE CODE'S USE.
-- `InjL a b = ∥ Σ[ F ∈ S ] InjCode F a b ∥₁` (src/L/GCH.lagda.md:37-38).
-- `leastOf` (src/L/WellOrder/Base.lagda.md:158-160) removes exactly that
-- truncation when the predicate is hProp-valued, which is checklist
-- step 4 of dev/literature/truncation-and-selection.md:297-300.
--
-- THIS ROW CANNOT REACH IT AS src/ STANDS, and the reason is one
-- definition.  `LeastCardInjL.Inj γ = ⟪ fst α ⟫ ↪ ⟪ fst γ ⟫`
-- (src/L/Cardinal.lagda.md:63-64) is the AMBIENT function type.  An
-- arbitrary ambient injection carries NO code, so there is nothing for
-- `leastOf` to be least among.  `κL` is least for the ambient notion
-- and `InjL` is the coded notion, and they are not the same predicate.

-- =====================================================================
-- SECTION 5.  WHAT IS NOT HERE, WRITTEN DOWN SO NOBODY READS A GO INTO
-- IT.
--
--   `sq-collect-at` IS NOT DEFINED IN THIS FILE.  No term of type
--   `SqCollectAt` appears above with no hypothesis in front of it.
--   Both terms that reach `SqCollectAt` take an input:
--
--     sq-collect-at-from-choice   : SetChoice (ℓ-suc ℓ) → SqCollectAt
--     sq-collect-at-from-bare-inj : BareLeastInjAt      → SqCollectAt
--
--   THE ROW IS NOT DISCHARGED.  The bill stays at FIVE rows and row 2
--   is not paid.  What changed is what row 2 is a name FOR.
--
--   AND `BareLeastInjAt` IS NOT A DISCHARGE EITHER, WHICH I SAY HERE
--   BECAUSE IT IS THE EASIEST MISREADING OF THIS FILE.  It is not
--   inhabited above and I did not inhabit it.  Untruncating `κ-injL`
--   uniformly over every ordinal is itself a selection.  This section
--   is a RE-LOCALIZATION of the row's cost and not a payment of it.
--
--   NO POSTULATE.  NO HOLE.  NOTHING UNDER src/.
-- =====================================================================
