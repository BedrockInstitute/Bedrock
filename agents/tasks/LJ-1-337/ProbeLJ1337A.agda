{-# OPTIONS --cubical --safe --guardedness #-}

-- LJ-1.337 probe A.  It lands nothing.  It runs in agents/tasks/LJ-1-337/.
--
-- THE BRIEF ASKS: build the successor-or-limit dichotomy on ordinals, which
-- `[LJ-1.335]` measured absent from `src/`, and price it.  This file holds
-- the dichotomy ALONE, with no import of `L.Absorption` and no import of
-- `L.InjChain`, so its seconds are the dichotomy's own seconds.  The
-- assembly `sq-below` lives in `ProbeLJ1337B.agda`, which imports this one.
--
-- PART 1 proves `sucV` injective at an ordinal.
-- PART 2 makes the successor statement a PROPOSITION.  This is what Part 1
--        is for, and it is the whole reason the dichotomy is untruncated.
-- PART 3 builds the dichotomy from the excluded middle.
-- PART 4 proves `isProp (Init δ)`, so the excluded middle can read the
--        chapter's own initial-ordinal predicate.
-- PART 5 records the negative controls.
--
-- ONE REWRITE, ordered by the brief.  `_↪_` is NOT imported from
-- `L.Cardinal`, because `L.Cardinal` imports `L.Ordinal.SquareLaw` at
-- src/L/Cardinal.lagda.md:22 and the reverse edge is a cycle.  This file
-- names no injection type at all, and `ProbeLJ1337B.agda` writes the raw
-- Sigma shape of src/L/Ordinal/SquareLaw.lagda.md:686-687.

open import Base.Prelude
open import Base.Truth
open import Base.Classical using ( LEM )

module LJ-1-337.ProbeLJ1337A {ℓ : Level} (lem : LEM (ℓ-suc ℓ)) where

open import FOL.ZFStructure using ( module hPropStructure )
open import V.Hierarchy {ℓ} using ( 𝒮ᵥ; ∈-irrefl )
open import V.Model {ℓ} using ( ∈sucV-elim; self∈sucV )
open import L.Constructible {ℓ} using ( IsOrd; isPropIsOrd )
open import L.Ordinal {ℓ} using ( mem-ord; suc-ord )
open import L.Ordinal.Linear {ℓ} lem using ( ord-tri )
open import L.Ordinal.SquareLaw {ℓ} lem using ( Init )

open import Cubical.HITs.CumulativeHierarchy.Properties using ( ⟪_⟫ )
open import Cubical.HITs.CumulativeHierarchy.Constructions
  using ( module InfinitySet )
open InfinitySet {ℓ} using ( ω; sucV )
open import Cubical.Foundations.HLevels using ( isProp× )
open import Cubical.Data.Sigma using ( _×_; Σ≡Prop )
open import Cubical.Data.Sum using ( _⊎_; inl; inr )
import Cubical.Data.Empty as Empty
import Cubical.HITs.PropositionalTruncation as PT
open PT using ( ∣_∣₁; ∥_∥₁ )

open TruthAlgebra (hPropAlgebra (ℓ-suc ℓ))
open hPropStructure 𝒮ᵥ using ( S; _∈ˢ_; isSetS )

-- =====================================================================
-- PART 1.  `sucV` IS INJECTIVE AT AN ORDINAL.
--
--   `[LJ-1.335]` section 4.2 named this absent.  The proof is the
--   textbook one and it needs no new machinery: the successor holds its
--   own argument (`self∈sucV`, src/V/Model.lagda.md:236), a member of a
--   successor is a member or the point itself (`∈sucV-elim`,
--   src/V/Model.lagda.md:218), and a two-cycle dies by transitivity plus
--   irreflexivity (src/V/Hierarchy.lagda.md:155).
--
--   ONE hypothesis is load-bearing and CONTROL 1 measures it: `IsOrd a`
--   supplies the transitivity that kills the two-cycle.
-- =====================================================================

sucV-inj : (a b : S) → IsOrd a → sucV a ≡ sucV b → a ≡ b
sucV-inj a b oa e =
  ∈sucV-elim {A = b} {x = a} (isSetS a b) a∈sb from-mem (λ p → p)
  where
  a∈sb : ⟨ a ∈ˢ sucV b ⟩
  a∈sb = subst (λ w → ⟨ a ∈ˢ w ⟩) e (self∈sucV a)

  b∈sa : ⟨ b ∈ˢ sucV a ⟩
  b∈sa = subst (λ w → ⟨ b ∈ˢ w ⟩) (sym e) (self∈sucV b)

  from-mem : ⟨ a ∈ˢ b ⟩ → a ≡ b
  from-mem a∈b =
    ∈sucV-elim {A = a} {x = b} (isSetS a b) b∈sa
      (λ b∈a → Empty.rec (∈-irrefl a (oa .fst a∈b b∈a)))
      (λ b≡a → sym b≡a)

-- =====================================================================
-- PART 2.  THE SUCCESSOR STATEMENT IS A PROPOSITION.
--
--   This is the piece that turns a merely existing predecessor into an
--   honest one.  `[LJ-1.332]` took the dichotomy as a HYPOTHESIS named
--   `Split` (agents/tasks/LJ-1-332/ProbeLJ1332A.agda:234-236) because the
--   excluded middle returns a TRUNCATED witness and nothing here said the
--   target was a proposition.  Part 1 says it: the predecessor is unique.
--
--   The membership row `⟨ γ ∈ˢ α ⟩` is carried on purpose.  A descent over
--   the ordinal applies its induction hypothesis at members only, so a
--   predecessor without that row is useless to the consumer.
-- =====================================================================

IsSuc : S → Type (ℓ-suc ℓ)
IsSuc α = Σ[ γ ∈ S ] (IsOrd γ × (⟨ γ ∈ˢ α ⟩ × (α ≡ sucV γ)))

isPropIsSuc : (α : S) → isProp (IsSuc α)
isPropIsSuc α x y = Σ≡Prop rest γ≡
  where
  rest : (γ : S) → isProp (IsOrd γ × (⟨ γ ∈ˢ α ⟩ × (α ≡ sucV γ)))
  rest γ = isProp× (isPropIsOrd γ)
             (isProp× (snd (γ ∈ˢ α)) (isSetS α (sucV γ)))

  γ≡ : x .fst ≡ y .fst
  γ≡ = sucV-inj (x .fst) (y .fst) (x .snd .fst)
         (sym (x .snd .snd .snd) ∙ y .snd .snd .snd)

-- =====================================================================
-- PART 3.  THE DICHOTOMY.
--
--   For an ordinal α: either α is closed under successors, or α is the
--   successor of one of its own members.  Zero needs no branch, because
--   zero is closed under successors vacuously.
--
--   `Closed` is written to be the THIRD ROW of the chapter's own `Init`
--   (src/L/Ordinal/SquareLaw.lagda.md:695) and the fourth argument of
--   `[LJ-1.335]`'s `LimitBand`, so no adapter is needed at either end.
--
--   The excluded middle is used twice, in the shape `L.Ordinal.Linear`
--   already uses it (src/L/Ordinal/Linear.lagda.md:96-110): once to
--   decide the closure statement, once to turn its failure into a mere
--   witness.  Part 2 then reads the witness out of the truncation.
-- =====================================================================

Closed : S → Type (ℓ-suc ℓ)
Closed α = (γ : S) → ⟨ γ ∈ˢ α ⟩ → ⟨ sucV γ ∈ˢ α ⟩

isPropClosed : (α : S) → isProp (Closed α)
isPropClosed α = isPropΠ (λ γ → isPropΠ (λ _ → snd (sucV γ ∈ˢ α)))

Split : S → Type (ℓ-suc ℓ)
Split α = Closed α ⊎ IsSuc α

ord-split : (α : S) → IsOrd α → Split α
ord-split α oα = decide (lem (Closed α , isPropClosed α))
  where
  Wit : Type (ℓ-suc ℓ)
  Wit = Σ[ γ ∈ S ] (⟨ γ ∈ˢ α ⟩ × (⟨ sucV γ ∈ˢ α ⟩ → Empty.⊥))

  witness : (Closed α → Empty.⊥) → ∥ Wit ∥₁
  witness nc = go (lem (∥ Wit ∥₁ , PT.isPropPropTrunc))
    where
    go : ∥ Wit ∥₁ ⊎ (∥ Wit ∥₁ → Empty.⊥) → ∥ Wit ∥₁
    go (inl w) = w
    go (inr nw) = Empty.rec (nc closed)
      where
      closed : Closed α
      closed γ γ∈α = at (lem (sucV γ ∈ˢ α))
        where
        at : ⟨ sucV γ ∈ˢ α ⟩ ⊎ (⟨ sucV γ ∈ˢ α ⟩ → Empty.⊥) → ⟨ sucV γ ∈ˢ α ⟩
        at (inl h)  = h
        at (inr nh) = Empty.rec (nw ∣ γ , (γ∈α , nh) ∣₁)

  from-wit : Wit → IsSuc α
  from-wit (γ , (γ∈α , nsγ)) = at (ord-tri (sucV γ) (suc-ord oγ) α oα)
    where
    oγ : IsOrd γ
    oγ = mem-ord {A = α} oα γ γ∈α

    -- `∈sucV-elim` reads a motive one universe up, so the absurd motive
    -- is lifted.  `[LJ-1.301]` hit the same at Descent.agda:230-238.
    two-cycle : ⟨ α ∈ˢ sucV γ ⟩ → Empty.⊥
    two-cycle α∈sγ = lower
      (∈sucV-elim {A = γ} {x = α} {P = Lift {j = ℓ-suc ℓ} Empty.⊥}
        (λ p _ → Empty.rec (lower p)) α∈sγ
        (λ α∈γ → lift (∈-irrefl α (oα .fst α∈γ γ∈α)))
        (λ α≡γ → lift (∈-irrefl α (subst (λ w → ⟨ w ∈ˢ α ⟩) (sym α≡γ) γ∈α))))

    at : ⟨ sucV γ ∈ˢ α ⟩ ⊎ ((sucV γ ≡ α) ⊎ ⟨ α ∈ˢ sucV γ ⟩) → IsSuc α
    at (inl sγ∈α)      = Empty.rec (nsγ sγ∈α)
    at (inr (inl p))   = γ , (oγ , (γ∈α , sym p))
    at (inr (inr α∈s)) = Empty.rec (two-cycle α∈s)

  decide : Closed α ⊎ (Closed α → Empty.⊥) → Split α
  decide (inl c)  = inl c
  decide (inr nc) = inr (PT.rec (isPropIsSuc α) from-wit (witness nc))

-- =====================================================================
-- PART 4.  `isProp (Init δ)`.
--
--   `[LJ-1.335]` section 4.2 named this absent too, and named the reason
--   it is wanted: the assembly must DECIDE the initial band, and the
--   excluded middle reads a proposition.  Every row of `Init`
--   (src/L/Ordinal/SquareLaw.lagda.md:692-698) is already a proposition,
--   so this is bookkeeping over delivered parts.  The third row IS
--   `Closed`, definitionally.
-- =====================================================================

isPropInit : (α : S) → isProp (Init α)
isPropInit α =
  isProp× (isPropIsOrd α)
    (isProp× (snd (ω ∈ˢ α))
      (isProp× (isPropClosed α) row4))
  where
  row4 : isProp ((β : S) → IsOrd β → ⟨ β ∈ˢ α ⟩ → ⟨ ω ∈ˢ β ⟩
               → (f : ⟪ α ⟫ → ⟪ β ⟫ × ⟪ β ⟫)
               → ((m n : ⟪ α ⟫) → f m ≡ f n → m ≡ n) → Empty.⊥)
  row4 = isPropΠ (λ _ → isPropΠ (λ _ → isPropΠ (λ _ → isPropΠ (λ _ →
           isPropΠ (λ _ → isPropΠ (λ _ → Empty.isProp⊥))))))

-- =====================================================================
-- PART 5.  THE NEGATIVE CONTROLS.  Each one was applied, run and
-- reverted.  They are recorded here because nothing typechecks this file
-- once the task closes.  Every one MEASURES.
--
--   CONTROL 1, ON THE ONE HYPOTHESIS OF PART 1.  Drop `IsOrd a` and kill
--   the two-cycle by irreflexivity alone:
--
--     control1 : (a b : S) → sucV a ≡ sucV b → a ≡ b
--     control1 a b e = ∈sucV-elim {A = b} {x = a} (isSetS a b)
--       (subst (λ w → ⟨ a ∈ˢ w ⟩) e (self∈sucV a))
--       (λ a∈b → Empty.rec (∈-irrefl a a∈b)) (λ p → p)
--
--   Agda named it, 1.4 s, 0 agda slots before the run:
--     error: [UnequalTerms]
--     b != a of type (Cubical.HITs.CumulativeHierarchy.Base.V ℓ)
--     when checking that the expression a∈b has type ⟨ a ∈ˢ a ⟩
--
--   So the ordinal hypothesis is load-bearing for ONE step: transitivity
--   turns `a ∈ b` and `b ∈ a` into `a ∈ a`.
--
--   CONTROL 2, ON THE UNTRUNCATION.  Read the predecessor out of a
--   truncation with `refl` for propositionality:
--
--     control2 : (α : S) → ∥ IsSuc α ∥₁ → IsSuc α
--     control2 α = PT.rec (λ x y → refl) (λ s → s)
--
--   Agda refused, 2.0 s, 0 slots before the run:
--     error: [UnequalTerms]
--     x != y of type Σ S (λ γ → IsOrd γ × ⟨ γ ∈ˢ α ⟩ × (α ≡ sucV γ))
--     when checking that the expression refl has type x ≡ y
--
--   THE MACHINE NAMES THE TWO PREDECESSORS IT CANNOT IDENTIFY.
--   Identifying them IS PART 1.  That is why `[LJ-1.301]`'s descent
--   stayed truncated and never needed the delivered `ord-suc-inj`.
--
--   CONTROL 3, ON `[LJ-1.332]`'s STATED SHAPE.  Its `Split`
--   (agents/tasks/LJ-1-332/ProbeLJ1332A.agda:236) asks the successor
--   branch for `⟨ ω ∈ˢ γ ⟩`.  Offer it what the dichotomy delivers:
--
--     control3 : (α : S) → Split α
--       → Closed α ⊎ (Σ[ γ ∈ S ] (IsOrd γ × (⟨ ω ∈ˢ γ ⟩ × (α ≡ sucV γ))))
--     control3 α (inl c) = inl c
--     control3 α (inr (γ , (oγ , (γ∈α , p)))) = inr (γ , (oγ , (γ∈α , p)))
--
--   Agda refused, 2.1 s, 0 slots before the run:
--     error: [UnequalTerms]
--     γ != ...sett (...X InfinitySet.ωStructure)
--                  (...ix InfinitySet.ωStructure)
--     of type Cubical.HITs.CumulativeHierarchy.Base.V ℓ
--     when checking that the expression γ∈α has type ⟨ ω ∈ˢ γ ⟩
--
--   MEASURED: that shape is STRICTLY STRONGER and it is FALSE at
--   `α ≡ sucV ω`, where the predecessor IS ω and `⟨ ω ∈ˢ ω ⟩` is refuted
--   by `∈-irrefl`.  `IsSuc` carries `⟨ γ ∈ˢ α ⟩` instead, and
--   ProbeLJ1337B.agda:180-196 reads the `ShiftAbs` hypotheses off one
--   elimination.
-- =====================================================================
