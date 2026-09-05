{-# OPTIONS --cubical --safe --guardedness #-}

-- [LJ-1.393] PROBE, second dispatch.  The AMBIENT cardinality notion, and
-- `Init` from it, at a GENERIC ordinal.  It runs in
-- agents/tasks/LJ-1-393/ and lands nothing in src/.
--
-- The tree holds two cardinality notions that point opposite ways:
-- `Init`'s fourth conjunct forbids an AMBIENT injection
-- (src/L/Ordinal/SquareLaw.lagda.md:696-698), while `IsCardinalL`
-- forbids a CODED one (src/L/Cardinal.lagda.md:230-233), and the one
-- bridge runs coded to ambient (src/L/CantorBernstein.lagda.md:33-38).
-- This probe does NOT bridge them.  It introduces the ambient notion
-- directly, as `AmbCard`, and measures what `Init` costs GIVEN it.
--
-- THE SPLIT VERDICT, and [LJ-1.392] decided it.  Between the first and
-- the second dispatch of this task, [LJ-1.392] returned a split verdict:
-- `suc-absorb` built (agents/tasks/LJ-1-392/Probe392.agda:121-203), the
-- bare `amb-limit` REFUTED (agents/tasks/LJ-1-392/Probe392.agda:236-244),
-- and a repaired form `amb-limit-ω∈γ` delivered green
-- (agents/tasks/LJ-1-392/Probe392.agda:255-266).  The refutation site
-- `α := sucV ω` refutes THIS task's `amb-init` too, because every
-- hypothesis `amb-init` names HOLDS there while `Init (sucV ω)` is
-- false: its third conjunct at `γ := ω` demands `⟨ sucV ω ∈ sucV ω ⟩`,
-- which `∈-irrefl` kills.  So:
--
--   AmbCard      no ambient injection of the index into an infinite
--                member.  A definition, not a producer.
--   amb-noinj²   `Init`'s FOURTH conjunct.  GO.  One composition: the
--                member's pairing (the induction hypothesis [LJ-1.395]
--                supplies, taken HERE as a hypothesis) flattens the
--                square, `AmbCard` refutes the rest.
--   amb-init     the assembly, AS THE BRIEF STATES IT.  NO-GO: no term
--                of this type exists.  Left as a hole, red by design,
--                exactly as [LJ-1.392] left its refuted obligation.  The
--                refutation is built green beside it, at PART 3.
--   amb-init'    the CORRECTED target, green.  `Init α` from the stated
--                hypotheses PLUS `⟨ sucV ω ∈ α ⟩`, the one membership the
--                stated form cannot supply at `α := sucV ω`.  The third
--                conjunct closes three ways: members below ω by ω-limit
--                and transitivity, ω itself by the new hypothesis, and
--                members containing ω by `amb-limit` in the form
--                [LJ-1.392] reports.
--   amb-sq'      the payoff in one line: with `via-col-square`
--                (src/L/Ordinal/SquareLaw.lagda.md:960-961) an
--                `amb-init'` is a square law producer GIVEN `AmbCard`
--                and the member square law.
--
-- THE MODULE HYPOTHESIS is `amb-limit` in the REPAIRED form [LJ-1.392]
-- reports (`amb-limit-ω∈γ`, closure at members that CONTAIN ω), and not
-- the refuted bare form the first dispatch took: [LJ-1.392]'s report
-- warns this task not to take the bare clause, and its refutation makes
-- the bare form uninstantiable.  The inner no-injection clause is
-- spelled as a Sigma because `_↪_` lives in `L.Cardinal`, whose explicit
-- `lem` parameter cannot be opened above the module header, and the
-- witness derivation copies only the lines above that header
-- (scripts/pod/witness.py:126-131).  The Sigma is `_↪_` unfolded
-- (src/L/Cardinal.lagda.md:47-48), so `amb-init'` passes `AmbCard α`
-- into it with no adapter.
--
-- `IsCardinalL` is imported from NOWHERE here.  `L.Cardinal` is opened
-- for `_↪_` alone.

open import Base.Prelude
open import Base.Truth
open import Base.Classical using ( LEM )
open import Cubical.HITs.CumulativeHierarchy.Base using ( V; _∈_ )
open import Cubical.HITs.CumulativeHierarchy.Properties using ( ⟪_⟫ )
open import Cubical.HITs.CumulativeHierarchy.Constructions
  using ( module InfinitySet )
open InfinitySet using ( ω; sucV )
open import L.Constructible using ( IsOrd )
open import Cubical.Data.Sigma using ( Σ; Σ-syntax )
import Cubical.Data.Empty as Empty

module LJ-1-393.Probe393 {ℓ : Level} (lem : LEM (ℓ-suc ℓ))
  (amb-limit : (α : V ℓ) → IsOrd α → ⟨ ω ∈ α ⟩
             → ((β : V ℓ) → IsOrd β → ⟨ β ∈ α ⟩ → ⟨ ω ∈ β ⟩
                → (Σ[ g ∈ (⟪ α ⟫ → ⟪ β ⟫) ]
                     ((m n : ⟪ α ⟫) → g m ≡ g n → m ≡ n))
                → Empty.⊥)
             → (γ : V ℓ) → ⟨ γ ∈ α ⟩ → ⟨ ω ∈ γ ⟩ → ⟨ sucV γ ∈ α ⟩) where

open import V.Hierarchy {ℓ} using ( ∈-irrefl )
open import V.Model {ℓ} using ( ∈sucV-elim; self∈sucV )
open import Cubical.Data.Sum using ( _⊎_; inl; inr )
open import L.Ordinal {ℓ} using ( mem-ord; suc-ord; ω-ord )
open import L.InjChain {ℓ} lem using ( ω-limit; ω∉β )
open import L.Ordinal.Linear {ℓ} lem using ( ord-tri )
open import L.Ordinal.SquareLaw {ℓ} lem using ( sq; Init; via-col-square )
open import L.Cardinal {ℓ} lem using ( _↪_ )

-- =====================================================================
-- PART 1.  THE AMBIENT CARDINALITY NOTION.
--
--   `AmbCard α` says: no ambient injection of `⟪ α ⟫` into `⟪ β ⟫`
--   for any infinite ordinal member β of α.  It is the notion `Init`'s
--   fourth conjunct already speaks, with the square lifted off.  It is
--   a DEFINITION: this probe does not produce it, and [LJ-1.394] is
--   where the campaign learns what producing it costs.
-- =====================================================================

AmbCard : V ℓ → Type (ℓ-suc ℓ)
AmbCard α = (β : V ℓ) → IsOrd β → ⟨ β ∈ α ⟩ → ⟨ ω ∈ β ⟩
          → (⟪ α ⟫ ↪ ⟪ β ⟫) → Empty.⊥

-- =====================================================================
-- PART 2.  `Init`'s FOURTH CONJUNCT, AND IT IS ONE COMPOSITION.
--
--   Given `f : ⟪ α ⟫ → ⟪ β ⟫ × ⟪ β ⟫` injective and the square law
--   `sq β` at the member, the composite `fst (sq β) ∘ f` is an
--   injection `⟪ α ⟫ ↪ ⟪ β ⟫`, and `AmbCard α` refutes it.  No level
--   lift is needed: everything the conjunct names is data at `Type ℓ`
--   used inside a conclusion at `Type (ℓ-suc ℓ)`.
--
--   The `sq` hypothesis is the induction hypothesis of a recursion this
--   task does not write: `[LJ-1.395]` supplies it.
-- =====================================================================

amb-noinj² : (α : V ℓ) → IsOrd α → AmbCard α
           → ((β : V ℓ) → IsOrd β → ⟨ β ∈ α ⟩ → ⟨ ω ∈ β ⟩ → sq β)
           → (β : V ℓ) → IsOrd β → ⟨ β ∈ α ⟩ → ⟨ ω ∈ β ⟩
           → (f : ⟪ α ⟫ → ⟪ β ⟫ × ⟪ β ⟫)
           → ((m n : ⟪ α ⟫) → f m ≡ f n → m ≡ n) → Empty.⊥
amb-noinj² α oα ac sqβ β oβ β∈α ω∈β f finj =
  ac β oβ β∈α ω∈β (g , g-inj)
  where
  g : ⟪ α ⟫ → ⟪ β ⟫
  g m = fst (sqβ β oβ β∈α ω∈β) (f m)

  g-inj : (m n : ⟪ α ⟫) → g m ≡ g n → m ≡ n
  g-inj m n e = finj m n (snd (sqβ β oβ β∈α ω∈β) (f m) (f n) e)

-- =====================================================================
-- PART 3.  THE REFUTATION OF THE STATED `amb-init`.  The site is
-- `α := sucV ω`, and it is the SAME site [LJ-1.392] measured for
-- `amb-limit` (agents/tasks/LJ-1-392/Probe392.agda:236-244).
--
-- (1) No member of `sucV ω` contains `ω`: a member is a member of `ω`
--     (a numeral, and no numeral contains `ω`, `ω∉β` at
--     src/L/InjChain.lagda.md:123-126) or `ω` itself (and `ω` does not
--     contain itself, `∈-irrefl`).  The core term is [LJ-1.392]'s
--     `noinj-vacuous-sucω` (Probe392.agda:229-235), rebuilt here.
-- (2) So `AmbCard (sucV ω)` holds vacuously, and so does the member
--     square-law hypothesis: both speak only at members that contain
--     `ω`, and there are none.
-- (3) `IsOrd (sucV ω)` and `⟨ ω ∈ sucV ω ⟩` are delivered facts.
-- (4) An `amb-init` fed all of that yields `Init (sucV ω)`, whose third
--     conjunct at `γ := ω` yields `⟨ sucV ω ∈ sucV ω ⟩`, which
--     `∈-irrefl` kills.
-- =====================================================================

no-ω-mem-sucω : (β : V ℓ) → ⟨ β ∈ sucV ω ⟩ → ⟨ ω ∈ β ⟩ → Empty.⊥
no-ω-mem-sucω β β∈ ω∈β = Empty.rec*
  (∈sucV-elim {A = ω} {x = β} {P = Empty.⊥* {ℓ-suc ℓ}} Empty.isProp⊥* β∈
    (λ β∈ω → lift (ω∉β β β∈ω ω∈β))
    (λ β≡ω → lift (∈-irrefl ω (subst (λ w → ⟨ ω ∈ w ⟩) β≡ω ω∈β))))

AmbCard-sucω : AmbCard (sucV ω)
AmbCard-sucω β oβ β∈ ω∈β inj = no-ω-mem-sucω β β∈ ω∈β

sqβ-sucω : (β : V ℓ) → IsOrd β → ⟨ β ∈ sucV ω ⟩ → ⟨ ω ∈ β ⟩ → sq β
sqβ-sucω β oβ β∈ ω∈β = Empty.rec (no-ω-mem-sucω β β∈ ω∈β)

amb-init-refuted : ((α : V ℓ) → IsOrd α → ⟨ ω ∈ α ⟩ → AmbCard α
                  → ((β : V ℓ) → IsOrd β → ⟨ β ∈ α ⟩ → ⟨ ω ∈ β ⟩ → sq β)
                  → Init α)
                 → Empty.⊥
amb-init-refuted amb =
  ∈-irrefl (sucV ω)
    ((amb (sucV ω) (suc-ord ω-ord) (self∈sucV ω) AmbCard-sucω sqβ-sucω)
       .snd .snd .fst ω (self∈sucV ω))

-- =====================================================================
-- PART 4.  THE STATED OBLIGATION, AS THE BRIEF STATES IT.
--
--   NO term of this type exists if the ambient theory is consistent,
--   because PART 3 builds a term of its negation.  The hole is the
--   formal remainder, red by design, exactly as [LJ-1.392] left its
--   refuted `amb-limit` (Probe392.agda:215).
-- =====================================================================

amb-init : (α : V ℓ) → IsOrd α → ⟨ ω ∈ α ⟩ → AmbCard α
         → ((β : V ℓ) → IsOrd β → ⟨ β ∈ α ⟩ → ⟨ ω ∈ β ⟩ → sq β)
         → Init α
amb-init = ?

-- =====================================================================
-- PART 5.  THE CORRECTED TARGET, GREEN.  Against the stated form, ONE
-- new hypothesis: `⟨ sucV ω ∈ α ⟩`, exactly the membership that fails
-- at the refutation site.  `Init α`'s four conjuncts, in order:
--
--   1  `IsOrd α`, a hypothesis.
--   2  `⟨ ω ∈ α ⟩`, a hypothesis.
--   3  successor closure, by the three-way ordinal trichotomy on a
--      member γ against ω (src/L/Ordinal/Linear.lagda.md:136):
--        γ ∈ ω    ω-limit closes inside ω, transitivity carries into α
--        γ ≡ ω    the new hypothesis
--        ω ∈ γ    `amb-limit`, the module hypothesis in the form
--                 [LJ-1.392] reports
--   4  `amb-noinj²`, PART 2.
--
-- `Initial` builds the `finite-excl` argument of `InitialCore` itself
-- from the second conjunct (src/L/Ordinal/SquareLaw.lagda.md:938-941),
-- so no finite-exclusion clause is owed here and none is built.
-- =====================================================================

amb-init' : (α : V ℓ) → IsOrd α → ⟨ ω ∈ α ⟩ → ⟨ sucV ω ∈ α ⟩ → AmbCard α
          → ((β : V ℓ) → IsOrd β → ⟨ β ∈ α ⟩ → ⟨ ω ∈ β ⟩ → sq β)
          → Init α
amb-init' α oα ω∈α sω∈α ac sqβ = oα , ω∈α , closure , amb-noinj² α oα ac sqβ
  where
  closure : (γ : V ℓ) → ⟨ γ ∈ α ⟩ → ⟨ sucV γ ∈ α ⟩
  closure γ γ∈α = tri (ord-tri γ oγ ω ω-ord)
    where
    oγ : IsOrd γ
    oγ = mem-ord {A = α} oα γ γ∈α

    tri : ⟨ γ ∈ ω ⟩ ⊎ ((γ ≡ ω) ⊎ ⟨ ω ∈ γ ⟩) → ⟨ sucV γ ∈ α ⟩
    tri (inl γ∈ω) = oα .fst (ω-limit γ γ∈ω) ω∈α
    tri (inr (inl γ≡ω)) = subst (λ w → ⟨ sucV w ∈ α ⟩) (sym γ≡ω) sω∈α
    tri (inr (inr ω∈γ)) = amb-limit α oα ω∈α ac γ γ∈α ω∈γ

-- =====================================================================
-- PART 6.  THE PAYOFF, ONE LINE.
--
--   With `via-col-square`, an `amb-init'` IS a square law producer, so
--   the open question the campaign carries away is not "how do we get
--   `Init`" but "how do we get `AmbCard` and the member square law".
--   This task does not settle that, and a report that presents
--   `amb-init'` as closing the square law is wrong.
-- =====================================================================

amb-sq' : (α : V ℓ) → IsOrd α → ⟨ ω ∈ α ⟩ → ⟨ sucV ω ∈ α ⟩ → AmbCard α
        → ((β : V ℓ) → IsOrd β → ⟨ β ∈ α ⟩ → ⟨ ω ∈ β ⟩ → sq β)
        → sq α
amb-sq' α oα ω∈α sω∈α ac sqβ = via-col-square α (amb-init' α oα ω∈α sω∈α ac sqβ)
