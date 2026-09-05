{-# OPTIONS --cubical --safe --guardedness #-}

-- [LJ-1.394] PROBE.  The AMBIENT DESCENT, and what the negation of
-- `AmbCard` delivers.  It runs in agents/tasks/LJ-1-394/ and lands
-- nothing.
--
--   TERM 1  `descent-amb`.  The four-arrow composite of [LJ-1.390],
--            with the descending arrow given as an AMBIENT injection
--            and the inclusion arrow ported from `mem-incl`:
--
--     ⟪ α ⟫ × ⟪ α ⟫  ↪  ⟪ β ⟫ × ⟪ β ⟫  ↪  ⟪ β ⟫  ↪  ⟪ α ⟫
--
--   TERM 2  `not-ambcard-gives`.  A negation of `AmbCard` must return
--            DATA: an ordinal AND an injection, untruncated.  Split by
--            the brief into two steps, and both are measured here:
--            STEP 1 asks whether `lem` reaches the ORDINAL, STEP 1B
--            asks whether the tree's own selection device reaches it
--            as DATA, STEP 2 asks whether anything reaches the ARROW.
--
--            STEP 2 IS EXPECTED TO FAIL.  The failure is the finding,
--            it is stated in the review-of file beside this probe, and
--            the hole is left at exactly the step that fails.
--
-- ONE Agda process per run, GHCRTS="-A64m -I0 -M8g", the wide caliber.

open import Base.Prelude
open import Base.Truth
open import Base.Classical using ( LEM )
open import Cubical.HITs.CumulativeHierarchy.Base using ( V; _∈_ )
open import Cubical.HITs.CumulativeHierarchy.Properties using ( ⟪_⟫; ⟪_⟫↪ )
open import Cubical.HITs.CumulativeHierarchy.Constructions
  using ( module InfinitySet )
open import Cubical.Data.Sigma using ( ΣPathP )
open import Cubical.Data.Sum using ( _⊎_; inl; inr )
open import Cubical.Foundations.HLevels using ( isProp×; isPropΠ )
import Cubical.Data.Empty as Empty
import Cubical.HITs.PropositionalTruncation as PT

module LJ-1-394.Probe394 {ℓ : Level} (lem : LEM (ℓ-suc ℓ)) where

open InfinitySet {ℓ} using ( ω; sucV )
open import V.Presentation {ℓ} using ( member; fiber; ↪-inj )
open import L.Constructible {ℓ}
  using ( IsOrd; isPropIsOrd; Lset; Lset-layer; layer-trans )
open import L.Ordinal {ℓ} using ( suc-ord )
open import L.Ordinal.Stages {ℓ} lem using ( ord∈Lset-suc )
open import L.Ordinal.SquareLaw {ℓ} lem using ( sq )
open import L.Cardinal {ℓ} lem using ( _↪_ )
open import L.Choice.Step {ℓ} lem using ( Mem; orderAt )
open import L.WellOrder.Base {ℓₚ = ℓ-suc ℓ} using ( SWO; IsLeast; leastOf )

open PT using ( ∥_∥₁; ∣_∣₁; squash₁ )

-- =====================================================================
-- PART 0.  THE AMBIENT CARDINAL, AND THE INCLUSION ARROW.
--
--   `AmbCard` is [LJ-1.393]'s notion, stated here locally because that
--   probe had not landed when this file was written: no ambient
--   injection of ⟪ α ⟫ into the square of a SMALLER infinite ordinal
--   member.  `mem-incl` is the PORT of [LJ-1.390]'s 12 lines
--   (agents/tasks/LJ-1-390/Probe390.agda:76-89), verbatim.
-- =====================================================================

AmbCard : V ℓ → Type (ℓ-suc ℓ)
AmbCard α = (β : V ℓ) → IsOrd β → ⟨ β ∈ α ⟩ → ⟨ ω ∈ β ⟩
          → (⟪ α ⟫ ↪ ⟪ β ⟫) → Empty.⊥

mem-incl : (d k : V ℓ) → IsOrd d → ⟨ k ∈ d ⟩ → ⟪ k ⟫ ↪ ⟪ d ⟫
mem-incl d k od k∈d = ι , ι-inj
  where
  raise : (m : ⟪ k ⟫) → ⟨ ⟪ k ⟫↪ m ∈ d ⟩
  raise m = fst od (member k m) k∈d

  ι : ⟪ k ⟫ → ⟪ d ⟫
  ι m = fst (fiber d (raise m))

  ι-inj : (m n : ⟪ k ⟫) → ι m ≡ ι n → m ≡ n
  ι-inj m n e = ↪-inj {a = k}
    (sym (snd (fiber d (raise m)))
     ∙ cong (⟪ d ⟫↪) e
     ∙ snd (fiber d (raise n)))

-- =====================================================================
-- PART 1.  TERM 1.  THE AMBIENT DESCENT.
--
--   The four arrows of [LJ-1.390]'s composite, with the descending
--   arrow given as an AMBIENT injection and NOT as a code, and the
--   door of that probe absent entirely: the arrow is a PARAMETER, as
--   [LJ-1.390]'s cure demands.
--
--     ARROW 1  the given injection, applied twice
--     ARROW 2  `sq β`
--     ARROW 3  `mem-incl`, the inclusion of a member in an ordinal
-- =====================================================================

descent-amb : (α β : V ℓ) → IsOrd α → IsOrd β
            → ⟨ β ∈ α ⟩ → ⟨ ω ∈ β ⟩
            → (⟪ α ⟫ ↪ ⟪ β ⟫) → sq β → sq α
descent-amb α β oα oβ β∈α ω∈β (d , d-inj) (g , g-inj) = f , f-inj
  where
  up : ⟪ β ⟫ ↪ ⟪ α ⟫
  up = mem-incl α β oα β∈α

  f : ⟪ α ⟫ × ⟪ α ⟫ → ⟪ α ⟫
  f (x , y) = fst up (g (d x , d y))

  f-inj : (p q : ⟪ α ⟫ × ⟪ α ⟫) → f p ≡ f q → p ≡ q
  f-inj (x₁ , y₁) (x₂ , y₂) e = ΣPathP (ex , ey)
    where
    -- ARROWS 1 and 2 reflected.
    step : (d x₁ , d y₁) ≡ (d x₂ , d y₂)
    step = g-inj _ _ (snd up _ _ e)

    -- ARROW 3 reflected.
    ex : x₁ ≡ x₂
    ex = d-inj x₁ x₂ (cong fst step)

    ey : y₁ ≡ y₂
    ey = d-inj y₁ y₂ (cong snd step)

-- =====================================================================
-- PART 2.  TERM 2, STEP 1.  `lem` REACHES THE ORDINAL.
--
--   The hypothesis of `not-ambcard-gives` is `¬ (AmbCard α)`: a
--   negation, and the negation names nothing.  The derivation spends
--   `lem` once, on the PROPOSITION `ex-amb α` itself: if `ex-amb α`
--   fails then `AmbCard α` holds vacuously (every injection refutes
--   the failed existence), contradicting the hypothesis.  So a β with
--   the three ordinal properties exists MERELY, and the injection
--   survives only under a double negation.
--
--   This step needs neither `oα` nor `ω∈α`.  The ordinal properties
--   of α itself enter only the consumer's recursion, not this lemma.
-- =====================================================================

ex-amb : (α : V ℓ) → Type (ℓ-suc ℓ)
ex-amb α =
  ∥ Σ[ β ∈ V ℓ ] (IsOrd β × ⟨ β ∈ α ⟩ × ⟨ ω ∈ β ⟩
      × (((⟪ α ⟫ ↪ ⟪ β ⟫) → Empty.⊥) → Empty.⊥)) ∥₁

ex-amb-prop : (α : V ℓ) → hProp (ℓ-suc ℓ)
ex-amb-prop α = ex-amb α , squash₁

amb-gives-merely : (α : V ℓ)
  → (AmbCard α → Empty.⊥) → ex-amb α
amb-gives-merely α h = go (lem (ex-amb-prop α))
  where
  go : ⟨ ex-amb-prop α ⟩ ⊎ (⟨ ex-amb-prop α ⟩ → Empty.⊥) → ex-amb α
  go (inl q) = q
  go (inr nq) = Empty.rec (h amb)
    where
    amb : AmbCard α
    amb β oβ β∈α ω∈β iβ =
      nq ∣ β , oβ , β∈α , ω∈β , (λ n → n iβ) ∣₁

-- =====================================================================
-- PART 3.  TERM 2, STEP 1B.  THE SELECTION DEVICE REACHES THE ORDINAL
-- AS DATA.
--
--   [LJ-1.314]'s mechanism, at this task's own site: `leastOf` over
--   `orderAt` untruncates ANY existence over a well-ordered carrier
--   whose payload is a PROPOSITION
--   (agents/tasks/LJ-1-314/CodeUntrunc.agda:75-101).  Here the
--   carrier is the stage `Lset (sucV α)`, which holds every member of
--   α by layer transitivity, and the payload carries the three
--   ordinal properties plus the DOUBLE NEGATION of the injection.
--   Every component is a proposition, so the mechanism applies, and
--   the ORDINAL arrives untruncated, with a LEAST-code certificate.
--   The injection component stays a double negation.  That residue is
--   PART 4's subject.
-- =====================================================================

ord-below-stage : (α : V ℓ) → IsOrd α → (β : V ℓ) → ⟨ β ∈ α ⟩
  → ⟨ β ∈ Lset (sucV α) ⟩
ord-below-stage α oα β β∈α =
  layer-trans (Lset-layer (sucV α)) β∈α (ord∈Lset-suc α oα)

Payload : (α β : V ℓ) → Type (ℓ-suc ℓ)
Payload α β = IsOrd β × ⟨ β ∈ α ⟩ × ⟨ ω ∈ β ⟩
            × (((⟪ α ⟫ ↪ ⟪ β ⟫) → Empty.⊥) → Empty.⊥)

isPropPayload : (α β : V ℓ) → isProp (Payload α β)
isPropPayload α β =
  isProp× (isPropIsOrd β)
  (isProp× (snd (β ∈ α))
  (isProp× (snd (ω ∈ β))
  (isPropΠ λ _ → Empty.isProp⊥)))

amb-gives-ord-data : (α : V ℓ) → IsOrd α
  → (AmbCard α → Empty.⊥)
  → Σ[ a ∈ Mem (Lset (sucV α)) ] Payload α (fst a)
amb-gives-ord-data α oα h =
  drop (leastOf (orderAt (sucV α) (suc-ord oα)) lem P
         (PT.map into (amb-gives-merely α h)))
  where
  P : Mem (Lset (sucV α)) → hProp (ℓ-suc ℓ)
  P a = Payload α (fst a) , isPropPayload α (fst a)

  drop : Σ[ a ∈ Mem (Lset (sucV α)) ]
           IsLeast (orderAt (sucV α) (suc-ord oα)) P a
       → Σ[ a ∈ Mem (Lset (sucV α)) ] Payload α (fst a)
  drop (a , pa , _) = a , pa

  into : Σ[ β ∈ V ℓ ] Payload α β
       → Σ[ a ∈ Mem (Lset (sucV α)) ] Payload α (fst a)
  into (β , p) = (β , ord-below-stage α oα β (fst (snd p))) , p

-- =====================================================================
-- PART 4.  TERM 2, STEP 2.  NOTHING REACHES THE ARROW.  THE HOLE.
--
--   PARTS 2 and 3 deliver the ORDINAL, merely and as data, and the
--   injection only under a DOUBLE NEGATION.  The obligation demands
--   the injection ITSELF, as data, and this is the step that fails.
--   The hole below is at exactly that step, and the review-of file
--   beside this probe states the obstruction.
--
--   WHY `lem` DOES NOT REACH.  `LEM (ℓ-suc ℓ)` decides PROPOSITIONS
--   (src/Base/Classical.lagda.md).  `⟪ α ⟫ ↪ ⟪ β ⟫` is a Σ over a
--   function type (src/L/Cardinal.lagda.md:47-48); two injections
--   can differ as functions, so it is not a proposition, and no
--   instance of `lem` decides it.  `lowerLEM` moves levels, not
--   grades (src/L/CantorBernstein.lagda.md:7).
--
--   WHY THE TREE'S ONE UNTRUNCATION DEVICE DOES NOT REACH.  `leastOf`
--   demands a payload in `A → hProp` (src/L/WellOrder/Base.lagda.md
--   :158-160), so the payload must be a PROPOSITION.  The device
--   worked at `[LJ-1.314]` only because `InjCode` is a proposition
--   (agents/tasks/LJ-1-314/CodeUntrunc.agda:75-101).  The payload
--   here is a function with an injectivity proof, and the ordinals'
--   well-order orders the ORDINALS, never the injections between
--   them.
--
--   WHAT WOULD CLOSE IT.  Either a double-negation eliminator at the
--   ambient injection type, which is a choice principle selecting a
--   canonical injection from a merely-existing family and which the
--   literature digest says needs a well-order on the INJECTIONS
--   (dev/literature/truncation-and-selection.md:334-336); or an
--   ambient-to-coded bridge turning the injection into an `InjCode`
--   proposition, after which PART 3's mechanism finishes the job.
--   The tree's only bridge runs coded to ambient
--   (src/L/CantorBernstein.lagda.md:33-38), and `[LJ-1.299]`'s
--   `amb→code` consumes the ambient face only to REFUTE a code, so
--   it is the same readback and not the missing bridge
--   (agents/tasks/LJ-1-299/NoInj2.agda:103-111).
-- =====================================================================

untrunc-amb : (α : V ℓ) → ex-amb α
  → Σ[ β ∈ V ℓ ] (IsOrd β × ⟨ β ∈ α ⟩ × ⟨ ω ∈ β ⟩ × (⟪ α ⟫ ↪ ⟪ β ⟫))
untrunc-amb α q = ?

not-ambcard-gives :
    (α : V ℓ) → IsOrd α → ⟨ ω ∈ α ⟩
  → (((β : V ℓ) → IsOrd β → ⟨ β ∈ α ⟩ → ⟨ ω ∈ β ⟩
                → (⟪ α ⟫ ↪ ⟪ β ⟫) → Empty.⊥) → Empty.⊥)
  → Σ[ β ∈ V ℓ ] (IsOrd β × ⟨ β ∈ α ⟩ × ⟨ ω ∈ β ⟩ × (⟪ α ⟫ ↪ ⟪ β ⟫))
not-ambcard-gives α oα ω∈α h = untrunc-amb α (amb-gives-merely α h)
