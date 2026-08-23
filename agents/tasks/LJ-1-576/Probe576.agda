{-# OPTIONS --cubical --safe --guardedness #-}

-- [LJ-1.576]  `LeastCardInjL` restated over the CODE.
--
-- The brief is the answer to the direct question [LJ-1.573] left:
-- "can `LeastCardInjL` be restated over the CODED injection `InjL`
-- (src/L/GCH.lagda.md:37-38) instead of the ambient one, so that
-- `leastOf` untruncates the code and `readL` reads it".
--
-- SECTION 1 is W3, written FIRST and typechecked ALONE at
--   agents/tasks/LJ-1-576/runs/W3.agda (exit 0, runs/w3-2.out).
-- SECTION 2 is THE OBLIGATION: the restatement, and `leastOf` applied.
-- SECTION 3 is where the untruncation actually happens, and it is NOT
--   in section 2.  This is the task's correction to the brief.
-- SECTION 4 answers the mandated question: does it select the same γ.
-- SECTION 5 measures what the five downstream projections now cost.
-- SECTION 6 writes down what is NOT here.
--
-- Nothing is postulated.  Nothing lands in src/.  No hole.

open import Base.Prelude
open import Base.Truth
open import Base.Classical using ( LEM )

module LJ-1-576.Probe576 {ℓ : Level} (lem : LEM (ℓ-suc ℓ)) where

open import FOL.ZFStructure using ( module hPropStructure )
import FOL.Absoluteness
open import V.Hierarchy {ℓ} using ( 𝒮ᵥ )
open import L.Constructible {ℓ} using ( 𝒮ʟ; IsOrd; isL; isL-trans; Lset )
open import L.Cardinal {ℓ} lem
  using ( _↪_; InjCode; module LeastCardInjL; module SiteBound )
open import L.GCH {ℓ} lem using ( InjL )
open import L.CantorBernstein {ℓ} lem using ( readL )
open import L.Choice.Step {ℓ} lem using ( Mem; orderAt )
open import L.WellOrder.Base {ℓₚ = ℓ-suc ℓ}
  using ( SWO; IsLeast; leastOf; Tri; lt; eq; gt; module SWO )
open import L.Coding.Model {ℓ} using ( svAt; domAt )
open import L.Coding.Injection {ℓ} lem using ( injAt )
open import L.Ordinal {ℓ} using ( mem-ord; suc-ord )
open import L.CodedShift {ℓ} lem using ( shift-coded )
open import L.Axioms.Infinity {ℓ} lem using ( ωʟ )
open import L.Axioms.Numerals {ℓ} using ( sucʟ )
open import V.Presentation {ℓ} using ( member; fiber )

open import Cubical.HITs.CumulativeHierarchy.Base using ( V; _∈_ )
open import Cubical.HITs.CumulativeHierarchy.Properties using ( ⟪_⟫; ⟪_⟫↪ )
open import Cubical.HITs.CumulativeHierarchy.Constructions
  using ( module InfinitySet )
open InfinitySet {ℓ} using ( sucV; #_ )
open import Cubical.Data.Sigma using ( Σ≡Prop )
open import Cubical.Foundations.HLevels using ( isProp× )
import Cubical.Data.Empty as Empty
import Cubical.HITs.PropositionalTruncation as PT
open PT using ( ∥_∥₁; ∣_∣₁; squash₁ )

open TruthAlgebra (hPropAlgebra (ℓ-suc ℓ))
open hPropStructure 𝒮ᵥ using ( _∈ˢ_ )
open hPropStructure 𝒮ʟ using ( S )

module AbsL = FOL.Absoluteness.Single 𝒮ᵥ isL isL-trans
open AbsL renaming ( _⊨ᵐ_ to _⊨_ )

-- =====================================================================
-- SECTION 1.  W3.  IS `InjCode` A PROPOSITION AT TODAY'S TREE.
--
--   [LJ-1.314]'s archived cure turns on this and that is an OLD tree
--   (archive/dev/LJ-dispatch-index.md:371).  The brief orders it
--   re-measured, not assumed (AGENTS.md:45).
--
--   IT IS.  Four conjuncts (src/L/Cardinal.lagda.md:224-228): three
--   satisfaction facts, each `⟨ _ ⟩` of an hProp of the truth algebra,
--   and one Π whose codomain is `⟨ _ ∈ _ ⟩`.  Every one is a
--   proposition, so the product is, with nothing assumed.
-- =====================================================================

isPropInjCode : (F a b : S) → isProp (InjCode F a b)
isPropInjCode F a b =
  isProp× (snd ((F ∷ a ∷ []) ⊨ svAt zero))
   (isProp× (snd ((F ∷ a ∷ []) ⊨ domAt zero (suc zero)))
    (isProp× (snd ((F ∷ a ∷ []) ⊨ injAt zero))
     (isPropΠ λ x → isPropΠ λ y → isPropΠ λ _ → snd (fst y ∈ fst b))))

-- AND THE DISTINCTION THAT DECIDES THE ROUTE, WHICH IS NOT THE SAME
-- QUESTION.  `leastOf` untruncates `∥ Σ[ F ∈ S ] InjCode F a b ∥₁` by
-- ITSELF only if THAT Σ is a proposition, which needs the code to be
-- UNIQUE.  Two different L-sets can both code an injection of `a` into
-- `b`, so `CodeUnique` is not expected to hold and it is NOT inhabited
-- here.  Section 3 is how the route reaches the code without it.
CodeUnique : Type (ℓ-suc ℓ)
CodeUnique = (a b : S) → isProp (Σ[ F ∈ S ] InjCode F a b)

-- =====================================================================
-- SECTION 2.  THE OBLIGATION.  `LeastCardInjL` RESTATED OVER `InjL`.
--
--   src/L/Cardinal.lagda.md:61-155 is the module.  Line 63-64 reads
--
--     Inj γ = ⟪ fst α ⟫ ↪ ⟪ fst γ ⟫
--
--   and that AMBIENT function type is the blocker the brief names.
--   Below is the same module with the CODED notion in its place.
--
--   THE ORDER AND THE CROSSING ARE src/'s OWN, NOT COPIES.  `w`, `up`,
--   `self` and `self-eq` are taken from `LeastCardInjL` itself, so the
--   comparison in section 4 runs in ONE well-order and there is nothing
--   to argue about.  `w` is sealed there (src/L/Cardinal.lagda.md:90-92)
--   and stays a stuck atom here.
-- =====================================================================

module Coded (α : S) (oα : IsOrd (fst α)) where

  open LeastCardInjL α oα
    using ( up; w; self; self-eq; InjP'; γ-card; κ; κ-inj; κ-min )

  -- The restatement, one line against src/'s one line.
  Injᶜ : S → Type (ℓ-suc ℓ)
  Injᶜ γ = InjL α γ

  -- src/L/Cardinal.lagda.md:66-67 reads `InjP γ = ∥ Inj γ ∥₁ , squash₁`.
  -- `InjL` IS already a truncation (src/L/GCH.lagda.md:38), so no
  -- `∥_∥₁` is added here: the truncation moved from the FUNCTION to the
  -- CODE'S EXISTENCE, which is the whole point of the restatement.
  InjPᶜ : S → hProp (ℓ-suc ℓ)
  InjPᶜ γ = Injᶜ γ , squash₁

  InjPᶜ' : ⟪ sucV (fst α) ⟫ → hProp (ℓ-suc ℓ)
  InjPᶜ' γ = InjPᶜ (up γ)

  -- src/L/Cardinal.lagda.md:112-114 pays this with `idInj`, the ambient
  -- identity, in one line.  THE CODED FORM HAS NO SUCH LINE: an
  -- L-element that CODES the identity on α is a set that must be built.
  -- Section 5 names it and prices it.
  Nonemptyᶜ : Type (ℓ-suc ℓ)
  Nonemptyᶜ = ∥ Σ[ b ∈ ⟪ sucV (fst α) ⟫ ] ⟨ InjPᶜ' b ⟩ ∥₁

  Leastᶜ : Type (ℓ-suc ℓ)
  Leastᶜ = Σ[ γ ∈ ⟪ sucV (fst α) ⟫ ] IsLeast w InjPᶜ' γ

  -- src/L/Cardinal.lagda.md:117 reads `least = leastOf w lem InjP' nonempty`.
  leastᶜ : Nonemptyᶜ → Leastᶜ
  leastᶜ = leastOf w lem InjPᶜ'

  γᶜ : Nonemptyᶜ → ⟪ sucV (fst α) ⟫
  γᶜ ne = fst (leastᶜ ne)

  κᶜ : Nonemptyᶜ → S
  κᶜ ne = up (γᶜ ne)

  -- The witness the restated module hands back, and it is STILL a
  -- truncation.  See section 3: this is the correction.
  κ-injᶜ : (ne : Nonemptyᶜ) → InjL α (κᶜ ne)
  κ-injᶜ ne = fst (snd (leastᶜ ne))

  -- The minimality clause, now at the CODED notion.
  κ-minᶜ : (ne : Nonemptyᶜ) (b : ⟪ sucV (fst α) ⟫) → InjL α (up b)
         → SWO._<∙_ w b (γᶜ ne) → Empty.⊥
  κ-minᶜ ne = snd (snd (leastᶜ ne))

-- THE OBLIGATION.  The restated predicate with `leastOf` applied to it,
-- taking the same non-emptiness argument `leastOf` itself takes
-- (src/L/WellOrder/Base.lagda.md:158-160).
least-card-inj-coded :
    (α : S) (oα : IsOrd (fst α))
  → Coded.Nonemptyᶜ α oα → Coded.Leastᶜ α oα
least-card-inj-coded α oα = Coded.leastᶜ α oα

-- =====================================================================
-- SECTION 3.  WHERE THE UNTRUNCATION ACTUALLY IS, AND IT IS NOT
-- SECTION 2.  THIS SECTION IS THIS TASK'S CORRECTION TO THE BRIEF.
--
--   The brief says: "so that `leastOf` untruncates the code and `readL`
--   reads it".  MEASURED, THAT IS TWO APPLICATIONS OF `leastOf` AND NOT
--   ONE, and section 2 is only the first of them.
--
--   `leastOf w lem P` returns `Σ[ a ] (⟨ P a ⟩ × ...)`
--   (src/L/WellOrder/Base.lagda.md:158-160).  It hands back a BARE `a`
--   and a BARE `⟨ P a ⟩`.  When `P a` is itself a truncation, as
--   `InjPᶜ' b = InjL α (up b) , squash₁` is, the thing handed back is
--   STILL `∥ Σ[ F ∈ S ] InjCode F α (up b) ∥₁`.  `Coded.κ-injᶜ` above
--   has exactly that type.  So the restatement ALONE untruncates
--   nothing, and a reader who stops at section 2 has read a GO into a
--   term that does not carry one.
--
--   WHAT DOES UNTRUNCATE IS A SECOND `leastOf`, RUN OVER THE CODE.
--   That is what W3 buys: `GoodF` below is hProp-VALUED because of
--   `isPropInjCode`, and it is NOT a truncation, so `leastOf` returns
--   the code as DATA.  This is [LJ-1.314]'s archived cure, re-measured
--   at today's tree and written as a term.
--
--   THE PRICE IS THE BOUND.  `leastOf` needs a well-order, and the only
--   well-order on codes the tree has is `orderAt β oβ` over
--   `Mem (Lset β)` (src/L/Choice/Step.lagda.md:730).  So the code must
--   be known to live in `Lset β`.  `SiteBound a` produces β above `a`'s
--   own stage and above ω (src/L/Choice/Stage.lagda.md:366-368); it
--   does NOT bound a set of pairs drawn from `a × b`.  So the bounded
--   non-emptiness is a hypothesis here, exactly as it is a hypothesis
--   in src/'s own `InternalLeastCard.Selected`
--   (src/L/Cardinal.lagda.md:242-243).
-- =====================================================================

module CodeSelect (a b : S) where

  open SiteBound a using ( β; oβ; up )

  -- hProp-VALUED, and NOT a truncation.  W3 is the second component.
  GoodF : Mem (Lset β) → hProp (ℓ-suc ℓ)
  GoodF F = InjCode (up F) a b , isPropInjCode (up F) a b

  BoundedCode : Type (ℓ-suc ℓ)
  BoundedCode = ∥ Σ[ F ∈ Mem (Lset β) ] ⟨ GoodF F ⟩ ∥₁

  chosen : BoundedCode → Σ[ F ∈ Mem (Lset β) ] IsLeast (orderAt β oβ) GoodF F
  chosen = leastOf (orderAt β oβ) lem GoodF

  -- THE UNTRUNCATION, AS A TERM.  A BARE code out of a TRUNCATED
  -- existence, with no choice principle and no postulate.
  bare-code : BoundedCode → Σ[ F ∈ S ] InjCode F a b
  bare-code h = up (fst (chosen h)) , fst (snd (chosen h))

  -- AND `readL` READS IT, with no truncation anywhere
  -- (src/L/CantorBernstein.lagda.md:33-35).
  bare-inj : BoundedCode → ⟪ fst a ⟫ ↪ ⟪ fst b ⟫
  bare-inj h = readL a b (bare-code h)

-- The two steps composed at the row's own types: from a BOUNDED coded
-- existence to the BARE ambient injection [LJ-1.573] said was missing.
-- Its `BareLeastInj` wanted exactly `⟪ fst α ⟫ ↪ ⟪ fst (κL α oα) ⟫`
-- without a truncation (agents/tasks/LJ-1-573/Probe573.agda:183-185).
bare-inj-at-coded-least :
    (α : S) (oα : IsOrd (fst α)) (ne : Coded.Nonemptyᶜ α oα)
  → CodeSelect.BoundedCode α (Coded.κᶜ α oα ne)
  → ⟪ fst α ⟫ ↪ ⟪ fst (Coded.κᶜ α oα ne) ⟫
bare-inj-at-coded-least α oα ne = CodeSelect.bare-inj α (Coded.κᶜ α oα ne)

-- WHAT IS STILL MISSING BETWEEN THE TWO, WRITTEN DOWN.  Section 2 hands
-- back `InjL α (κᶜ ne)`, which is `∥ Σ[ F ∈ S ] _ ∥₁` over the WHOLE
-- L-carrier; section 3 consumes `∥ Σ[ F ∈ Mem (Lset β) ] _ ∥₁`, over
-- one stage.  The gap is a reflection step and it is NOT inhabited here.
CodeBounded : Type (ℓ-suc ℓ)
CodeBounded = (a b : S) → InjL a b → CodeSelect.BoundedCode a b

-- =====================================================================
-- SECTION 4.  DOES THE RESTATEMENT SELECT THE SAME γ.
--
--   [LJ-1.573] warned it may not: "`κL`'s least is a different
--   predicate from `InjL`'s."  THE WARNING IS RIGHT, AND THE DIRECTION
--   IS ONE-WAY.  The two predicates run in ONE well-order, because
--   section 2 took `w` from `LeastCardInjL` itself, so the comparison
--   below is a comparison and not an analogy.
-- =====================================================================

-- Coded IMPLIES ambient, by `readL` under `PT.map`.  No truncation is
-- added and nothing is assumed.
coded→ambient : (a b : S) → InjL a b → ∥ ⟪ fst a ⟫ ↪ ⟪ fst b ⟫ ∥₁
coded→ambient a b = PT.map (readL a b)

-- At the row's own predicates: the coded subset is INSIDE the ambient
-- one.  `LeastCardInjL.InjP'` is src/L/Cardinal.lagda.md:82-83.
coded⊆ambient :
    (α : S) (oα : IsOrd (fst α)) (b : ⟪ sucV (fst α) ⟫)
  → ⟨ Coded.InjPᶜ' α oα b ⟩ → ⟨ LeastCardInjL.InjP' α oα b ⟩
coded⊆ambient α oα b = coded→ambient α (LeastCardInjL.up α oα b)

-- SO THE AMBIENT LEAST IS NEVER STRICTLY ABOVE THE CODED LEAST.  This
-- holds outright, with no hypothesis: the coded least satisfies the
-- ambient predicate too, and `κ-min` refutes anything smaller than the
-- ambient least that does (src/L/Cardinal.lagda.md:136-138).
ambient-not-above :
    (α : S) (oα : IsOrd (fst α)) (ne : Coded.Nonemptyᶜ α oα)
  → SWO._<∙_ (LeastCardInjL.w α oα)
      (Coded.γᶜ α oα ne) (LeastCardInjL.γ-card α oα)
  → Empty.⊥
ambient-not-above α oα ne =
  LeastCardInjL.κ-min α oα (Coded.γᶜ α oα ne)
    (coded⊆ambient α oα (Coded.γᶜ α oα ne)
      (fst (snd (Coded.leastᶜ α oα ne))))

-- THE OTHER DIRECTION IS NOT FREE, AND THIS IS THE ANSWER THE BRIEF
-- ASKED FOR.  It needs every ambient injection between L-elements to
-- carry a code.  That is an ABSOLUTENESS statement about L and it is
-- NOT inhabited here.
AmbientCoded : Type (ℓ-suc ℓ)
AmbientCoded = (a b : S) → ∥ ⟪ fst a ⟫ ↪ ⟪ fst b ⟫ ∥₁ → InjL a b

coded-not-above :
    AmbientCoded → (α : S) (oα : IsOrd (fst α)) (ne : Coded.Nonemptyᶜ α oα)
  → SWO._<∙_ (LeastCardInjL.w α oα)
      (LeastCardInjL.γ-card α oα) (Coded.γᶜ α oα ne)
  → Empty.⊥
coded-not-above ac α oα ne =
  Coded.κ-minᶜ α oα ne (LeastCardInjL.γ-card α oα)
    (ac α (LeastCardInjL.up α oα (LeastCardInjL.γ-card α oα))
       (LeastCardInjL.κ-inj α oα))

-- AND UNDER THAT HYPOTHESIS, AND ONLY UNDER IT, THE TWO AGREE.
-- Trichotomy of the shared well-order kills both strict cases
-- (src/L/WellOrder/Base.lagda.md:80-84).
same-γ :
    AmbientCoded → (α : S) (oα : IsOrd (fst α)) (ne : Coded.Nonemptyᶜ α oα)
  → LeastCardInjL.γ-card α oα ≡ Coded.γᶜ α oα ne
same-γ ac α oα ne = decide (SWO.tri∙ (LeastCardInjL.w α oα)
                              (LeastCardInjL.γ-card α oα) (Coded.γᶜ α oα ne))
  where
  decide : Tri (SWO._<∙_ (LeastCardInjL.w α oα)
                  (LeastCardInjL.γ-card α oα) (Coded.γᶜ α oα ne))
               (LeastCardInjL.γ-card α oα ≡ Coded.γᶜ α oα ne)
               (SWO._<∙_ (LeastCardInjL.w α oα)
                  (Coded.γᶜ α oα ne) (LeastCardInjL.γ-card α oα))
         → LeastCardInjL.γ-card α oα ≡ Coded.γᶜ α oα ne
  decide (lt p) = Empty.rec (coded-not-above ac α oα ne p)
  decide (eq e) = e
  decide (gt p) = Empty.rec (ambient-not-above α oα ne p)

-- =====================================================================
-- SECTION 5.  WHAT THE RESTATEMENT COSTS DOWNSTREAM.
--
--   `src/L/SquareLawClosed.lagda.md:72-89` seals FIVE projections of
--   `LeastCardInjL` and nothing else in the tree reads the module.
--   MEASURED: `grep -rn "LeastCardInjL" src/ | wc -l` returns 8, and
--   they are src/L/Cardinal.lagda.md:61, the module header, plus
--   src/L/SquareLawClosed.lagda.md:37 (the import), :65 (a comment) and
--   :74, :77, :80, :84, :89 (the five bodies).  So the restatement's
--   whole downstream bill is these five, and each is answered below
--   with a term or with a named gap.
-- =====================================================================

module Five (α : S) (oα : IsOrd (fst α)) (ne : Coded.Nonemptyᶜ α oα) where

  open Coded α oα using ( γᶜ; κᶜ; InjPᶜ'; leastᶜ; κ-minᶜ )
  open LeastCardInjL α oα using ( up; w; w-lt )

  -- PROJECTION 1, `κL`.  Delivered, and it is `Coded.κᶜ`.
  κ₁ : S
  κ₁ = κᶜ ne

  -- PROJECTION 2, `κoL`.  Delivered.  src/L/Cardinal.lagda.md:125-127
  -- line for line, with γᶜ in place of γ-card: the argument reads only
  -- membership in the stage and never the predicate.
  κ₂ : IsOrd (fst κ₁)
  κ₂ = mem-ord {A = sucV (fst α)} (suc-ord oα) (fst κ₁)
         (member (sucV (fst α)) (γᶜ ne))

  -- PROJECTION 3, `κ∈sucL`.  Delivered, src/L/Cardinal.lagda.md:130.
  κ₃ : ⟨ fst κ₁ ∈ˢ sucV (fst α) ⟩
  κ₃ = member (sucV (fst α)) (γᶜ ne)

  -- PROJECTION 4, `κ-injL`.  THIS IS THE GAIN, AND IT IS THE WHOLE
  -- POINT OF THE ROW.  src/L/SquareLawClosed.lagda.md:82-84 delivers
  -- `∥ ⟪ fst a ⟫ ↪ ⟪ fst (κL a oa) ⟫ ∥₁`, TRUNCATED, and [LJ-1.573]
  -- measured that this one truncation buys the entire truncation of
  -- `sq-trunc-closed`.  Under the restatement it comes out BARE, given
  -- the bound of section 3 and NOTHING ELSE.
  κ₄ : CodeSelect.BoundedCode α κ₁ → ⟪ fst α ⟫ ↪ ⟪ fst κ₁ ⟫
  κ₄ = CodeSelect.bare-inj α κ₁

  -- PROJECTION 5, `κ-min-atL`.  DELIVERED, BUT WEAKER, AND THIS IS THE
  -- LOSS.  src/L/Cardinal.lagda.md:140-155 refutes an AMBIENT injection
  -- below κ; the restatement refutes only a CODED one.  The proof is
  -- src/'s own, transported, and it reads `w-lt` from the seal.
  κ₅ : (δ : S) → ⟨ fst δ ∈ˢ fst κ₁ ⟩ → InjL α δ → Empty.⊥
  κ₅ δ δ∈κ α↪δ = κ-minᶜ ne b bInjP b<γ
    where
    δ∈sα : ⟨ fst δ ∈ˢ sucV (fst α) ⟩
    δ∈sα = suc-ord oα .fst {x = fst κ₁} {y = fst δ} δ∈κ κ₃
    b : ⟪ sucV (fst α) ⟫
    b = fiber (sucV (fst α)) δ∈sα .fst
    bδ : ⟪ sucV (fst α) ⟫↪ b ≡ fst δ
    bδ = fiber (sucV (fst α)) δ∈sα .snd
    -- The ascription is not decoration.  Without it `Σ≡Prop` has to
    -- invert `fst`, which it cannot: MEASURED, exit 42,
    -- [UnsolvedMetaVariables] at agents/tasks/LJ-1-576/runs/s5-1.out:4-5.
    up-b≡δ : up b ≡ δ
    up-b≡δ = Σ≡Prop (λ x → snd (isL x)) bδ
    bInjP : InjL α (up b)
    bInjP = subst (InjL α) (sym up-b≡δ) α↪δ
    b<γ : SWO._<∙_ w b (γᶜ ne)
    b<γ = transport (λ i → sym (w-lt b (γᶜ ne)) i)
            (subst (λ z → ⟨ z ∈ˢ fst κ₁ ⟩) (sym bδ) δ∈κ)

-- WHAT PROJECTION 5's WEAKENING COSTS ITS CONSUMERS, MEASURED AT THE
-- CALL SITES AND NOT GUESSED.  `grep -n "κ-min-atL" src/L/SquareLawClosed.lagda.md`
-- returns FIVE lines, of which :86 and :89 are the projection itself, so
-- there are THREE call sites: :109, :141 and :156.
--
-- ALL THREE HAVE THE SAME SHAPE, WHICH IS WHY THE BILL IS ONE ITEM AND
-- NOT THREE.  Each feeds `κ-min-atL` an AMBIENT composite of the
-- least-injection with a second injection, under `PT.map`:
--
--   :109  `PT.map (λ iaκ → comp-inj iaκ κ↪β) κ-inj`      (:115)
--   :141  `PT.map (λ f → comp-inj f (... Shiftω.shift↪)) (κ-injL a oa)`  (:142-143)
--   :156  `PT.map (λ f → comp-inj f (... (shift-at γ oγ ω∈γ))) (κ-injL a oa)`  (:157-158)
--
-- Under the restatement each needs a CODED composite instead.
CodedComp : Type (ℓ-suc ℓ)
CodedComp = (a b c : S) → InjL a b → InjL b c → InjL a c

-- AND THE SECOND FACTOR IS ALREADY CODED IN src/ FOR TWO OF THE THREE.
-- Both :141 and :156 use the shift, `Shiftω.shift↪` being
-- `ShiftAbs ω ω-ord (∈-irrefl ω) #∈ω` (src/L/SquareLawClosed.lagda.md:117)
-- and `shift-at` being the same module at γ (:119-120).  `shift-coded`
-- is built on `ShiftGraph` (src/L/Absorption.lagda.md:539-543), which
-- takes the SAME four hypotheses as `ShiftAbs`
-- (src/L/Absorption.lagda.md:74-76), so it is available at exactly the
-- γ each call site already has.  The remaining one, :109, wants the
-- SQUARE coded and that is a different object.
--
-- This line is not a citation: it is `shift-coded` itself, applied at
-- the coded type, so the claim is checked and not believed.
coded-shift-exists :
    (γ : S) (oγ : IsOrd (fst γ)) (γ∉ω : ⟨ fst γ ∈ fst ωʟ ⟩ → Empty.⊥)
    (numerals : (k : ℕ) → ⟨ # k ∈ fst γ ⟩)
  → InjL (sucʟ γ) γ
coded-shift-exists = shift-coded

-- AND THE NON-EMPTINESS.  src/L/Cardinal.lagda.md:109-114 pays the
-- ambient one with `idInj`, the ambient identity, in two lines.  The
-- coded form needs an L-ELEMENT that codes the identity on α, which is
-- a set to be built and not a lambda.  It is NOT inhabited here.  This
-- term is the exact reduction: the identity code pays section 2's
-- hypothesis, at every α, with nothing else.
IdCoded : Type (ℓ-suc ℓ)
IdCoded = (a : S) → InjL a a

id-coded→nonempty :
  IdCoded → (α : S) (oα : IsOrd (fst α)) → Coded.Nonemptyᶜ α oα
id-coded→nonempty idc α oα =
  ∣ LeastCardInjL.self α oα
  , subst (InjL α) (sym up-self≡α) (idc α) ∣₁
  where
  up-self≡α : LeastCardInjL.up α oα (LeastCardInjL.self α oα) ≡ α
  up-self≡α = Σ≡Prop (λ x → snd (isL x)) (LeastCardInjL.self-eq α oα)

-- =====================================================================
-- SECTION 6.  WHAT IS NOT HERE, WRITTEN DOWN SO NOBODY READS A GO INTO
-- IT.
--
--   THE OBLIGATION IS DELIVERED.  `least-card-inj-coded` above is the
--   restated `LeastCardInjL` with `leastOf` applied to it, and it is
--   green.  THAT IS ALL IT IS.
--
--   THESE FOUR TYPES ARE WRITTEN AND NONE IS INHABITED IN THIS FILE:
--
--     CodeUnique   -- and it is NOT expected to hold
--     CodeBounded  -- the reflection step of section 3
--     AmbientCoded -- what section 4's equality needs
--     CodedComp    -- what kappa-limit's two call sites need
--     IdCoded      -- what section 2's non-emptiness needs
--
--   NO ROW IS PAID.  `SqCollectAt` is not stated in this file, is not
--   inhabited in this file, and this task did not attempt it: the brief
--   forbids it ("DO NOT BUILD `SqCollectAt` ITSELF").
--
--   AND `bare-inj-at-coded-least` IS NOT A DISCHARGE, WHICH IS SAID
--   HERE BECAUSE IT IS THE EASIEST MISREADING OF THIS FILE.  It takes
--   `CodeSelect.BoundedCode` as a hypothesis.  What it proves is that
--   ONCE the code is known to sit at one stage, no choice principle is
--   spent to get the injection as DATA.  That is a re-localization of
--   [LJ-1.573]'s cost and not a payment of it.
--
--   NO POSTULATE.  NO HOLE.  NOTHING UNDER src/.
-- =====================================================================
