{-# OPTIONS --cubical --safe --guardedness #-}

-- [LJ-1.395] PROBE.  The BAND RECURSION, assembled with every case fed
-- by a named supplier, and the residue it leaves.  It runs in
-- agents/tasks/LJ-1-395/ and lands nothing in src/.
--
--   TERM 1  `band-owes`.  The residue after every DELIVERED supplier is
--            spent.  [LJ-1.394] measured that nothing in this tree
--            untruncates the ambient ARROW
--            (agents/tasks/LJ-1-394/review-of-not-ambcard-gives.md,
--            STEP 2).  So the residue IS that datum, at every negative
--            site.
--
--   TERM 2  `sq-band`.  The recursion, by `∈-induction`.
--
--     case                              supplier
--     x ≡ ω                             `squareω`, delivered
--     AmbCard x and sucV ω ∈ x          `amb-init'`, then `via-col-square`
--     AmbCard x and sucV ω ∉ x          `sq-suc` at ω, then `squareω`
--     ¬ AmbCard x                       `band-owes`, then `descent-amb`
--
-- THE PREDECESSOR CLAUSE.  Owner 2026-08-20, audit F1 and F3.  A module
-- hypothesis is the type the predecessor TYPECHECKED, and the verdict
-- is the report.  [LJ-1.393] refuted the stated `amb-init`
-- (agents/tasks/LJ-1-393/Probe393.agda:164-171) and delivered
-- `amb-init'` (`:207-210`).  This file takes `amb-init'`, not the
-- refuted type.  [LJ-1.394] delivered `descent-amb` and left
-- `not-ambcard-gives` as a NO-GO; the latter is the residue, not a
-- hypothesis.  `sq-suc` is [LJ-1.330]'s delivered successor transfer
-- (agents/tasks/LJ-1-330/ProbeLJ1330A.agda:120-127), taken as a
-- hypothesis because `amb-init'` does not apply at `sucV ω` and the
-- three clauses forbid putting `sq (sucV ω)` in the residue.
--
-- THE SPELLING LAW OF THE TELESCOPE.  Supplier statements are
-- parameters with the types their reports give, but every named notion
-- inside them is UNFOLDED, because the named forms live in modules that
-- take `lem` explicitly and cannot be opened above this header
-- ([LJ-1.393] precedent, agents/tasks/LJ-1-393/Probe393.agda:53-59).
--
-- ONE Agda process per run.  GHCRTS is the pane caliber, untouched.

open import Base.Prelude
open import Base.Truth
open import Base.Classical using ( LEM )
open import Cubical.HITs.CumulativeHierarchy.Base using ( V; _∈_ )
open import Cubical.HITs.CumulativeHierarchy.Properties using ( ⟪_⟫ )
open import Cubical.HITs.CumulativeHierarchy.Constructions
  using ( module InfinitySet )
open InfinitySet using ( ω; sucV; #_ )
open import L.Constructible using ( IsOrd )
open import Cubical.Data.Nat using ( ℕ )
import Cubical.Data.Empty as Empty

module LJ-1-395.Probe395 {ℓ : Level} (lem : LEM (ℓ-suc ℓ))
  (α₀ : V ℓ) (oα₀ : IsOrd α₀)
  (amb-init' :
    (a : V ℓ) → IsOrd a → ⟨ ω ∈ a ⟩ → ⟨ sucV ω ∈ a ⟩
    → ((β : V ℓ) → IsOrd β → ⟨ β ∈ a ⟩ → ⟨ ω ∈ β ⟩
       → Σ[ d ∈ (⟪ a ⟫ → ⟪ β ⟫) ]
           ((m n : ⟪ a ⟫) → d m ≡ d n → m ≡ n)
       → Empty.⊥)
    → ((β : V ℓ) → IsOrd β → ⟨ β ∈ a ⟩ → ⟨ ω ∈ β ⟩
       → Σ[ g ∈ (⟪ β ⟫ × ⟪ β ⟫ → ⟪ β ⟫) ]
           ((p q : ⟪ β ⟫ × ⟪ β ⟫) → g p ≡ g q → p ≡ q))
    → IsOrd a
    × ⟨ ω ∈ a ⟩
    × ((γ : V ℓ) → ⟨ γ ∈ a ⟩ → ⟨ sucV γ ∈ a ⟩)
    × ((β : V ℓ) → IsOrd β → ⟨ β ∈ a ⟩ → ⟨ ω ∈ β ⟩
       → (f : ⟪ a ⟫ → ⟪ β ⟫ × ⟪ β ⟫)
       → ((m n : ⟪ a ⟫) → f m ≡ f n → m ≡ n) → Empty.⊥))
  (descent-amb :
    (a b : V ℓ) → IsOrd a → IsOrd b → ⟨ b ∈ a ⟩ → ⟨ ω ∈ b ⟩
    → Σ[ d ∈ (⟪ a ⟫ → ⟪ b ⟫) ]
        ((m n : ⟪ a ⟫) → d m ≡ d n → m ≡ n)
    → Σ[ g ∈ (⟪ b ⟫ × ⟪ b ⟫ → ⟪ b ⟫) ]
        ((p q : ⟪ b ⟫ × ⟪ b ⟫) → g p ≡ g q → p ≡ q)
    → Σ[ f ∈ (⟪ a ⟫ × ⟪ a ⟫ → ⟪ a ⟫) ]
        ((p q : ⟪ a ⟫ × ⟪ a ⟫) → f p ≡ f q → p ≡ q))
  (sq-suc :
    (γ : V ℓ) → IsOrd γ → (⟨ γ ∈ ω ⟩ → Empty.⊥)
    → ((k : ℕ) → ⟨ (# k) ∈ γ ⟩)
    → Σ[ f ∈ (⟪ γ ⟫ × ⟪ γ ⟫ → ⟪ γ ⟫) ]
        ((p q : ⟪ γ ⟫ × ⟪ γ ⟫) → f p ≡ f q → p ≡ q)
    → Σ[ f ∈ (⟪ sucV γ ⟫ × ⟪ sucV γ ⟫ → ⟪ sucV γ ⟫) ]
        ((p q : ⟪ sucV γ ⟫ × ⟪ sucV γ ⟫) → f p ≡ f q → p ≡ q)) where

open import V.Hierarchy {ℓ} using ( ∈-induction; ∈-irrefl )
open import V.Model {ℓ} using ( ∈sucV-elim )
open import L.Constructible {ℓ} using ( isPropIsOrd )
open import L.Ordinal {ℓ} using ( mem-ord; ω-ord; suc-ord; #∈ω )
open import L.Ordinal.Linear {ℓ} lem using ( ord-tri )
open import L.Ordinal.SquareLaw {ℓ} lem using ( sq; Init; via-col-square )
open import L.InjChain {ℓ} lem using ( squareω )
open import L.Cardinal {ℓ} lem using ( _↪_ )
open import Cubical.Foundations.HLevels using ( isPropΠ )
open import Cubical.Data.Sum using ( _⊎_; inl; inr )

-- [LJ-1.393]'s notion, named: judgmentally the fourth argument type of
-- `amb-init'` above, in the spelling the tree writes it.
AmbCard : (a : V ℓ) → Type (ℓ-suc ℓ)
AmbCard a = (β : V ℓ) → IsOrd β → ⟨ β ∈ a ⟩ → ⟨ ω ∈ β ⟩
          → (⟪ a ⟫ ↪ ⟪ β ⟫) → Empty.⊥

isPropAmbCard : (a : V ℓ) → isProp (AmbCard a)
isPropAmbCard a =
  isPropΠ λ _ → isPropΠ λ _ → isPropΠ λ _ → isPropΠ λ _ →
  isPropΠ λ _ → Empty.isProp⊥

-- =====================================================================
-- PART 1.  THE RESIDUE.
--
--   `band-owes` is what the recursion still owes after the delivered
--   suppliers are spent.  Its content is [LJ-1.394]'s
--   `not-ambcard-gives` conclusion
--   (agents/tasks/LJ-1-394/Probe394.agda:251-256), the statement that
--   probe left as a NO-GO at its STEP 2.
--
--   The three clauses that bind it:
--     1. CLOSED.  It is a `Type`.  Its `a` is its own binder, and it
--        takes no parameter of `sq-band`'s telescope.
--     2. NO `sq` AT A BOUND VARIABLE.  The type does not contain the
--        token `sq`, in either spelling, at any position.
--     3. The ONE line is in the report, section 2.
-- =====================================================================

band-owes : Type (ℓ-suc ℓ)
band-owes =
  (a : V ℓ) → IsOrd a → ⟨ ω ∈ a ⟩ → (AmbCard a → Empty.⊥)
  → Σ[ b ∈ V ℓ ] (IsOrd b × ⟨ b ∈ a ⟩ × ⟨ ω ∈ b ⟩ × (⟪ a ⟫ ↪ ⟪ b ⟫))

-- =====================================================================
-- PART 2.  THE MOTIVE.
--
--   The motive carries the ordinal certificate and the infinitude to
--   every member.  It carries NO band membership: no supplier reads
--   one at a member.  The band enters only at the top, through
--   `sq-band`'s own argument, and PART 5 spends it there.
-- =====================================================================

Goal : V ℓ → Type (ℓ-suc ℓ)
Goal x = IsOrd x → (⟨ x ∈ ω ⟩ → Empty.⊥) → sq x

inf-member : (b : V ℓ) → ⟨ ω ∈ b ⟩ → (⟨ b ∈ ω ⟩ → Empty.⊥)
inf-member b ω∈b h = ∈-irrefl ω (ω-ord .fst ω∈b h)

-- =====================================================================
-- PART 3.  THE STEP.
--
--   `ord-tri` first, as the chapter does at
--   src/L/StageCardinal.lagda.md:543-546.  Then `lem` on `AmbCard x`.
--   The AmbCard branch splits again on `sucV ω ∈ x`, because
--   `amb-init'` needs that membership and it fails at `x ≡ sucV ω`.
-- =====================================================================

step : band-owes
     → (x : V ℓ) → ((y : V ℓ) → ⟨ y ∈ x ⟩ → Goal y) → Goal x
step owes x ih ox infx = go (ord-tri x ox ω ω-ord)
  where
  go : ⟨ x ∈ ω ⟩ ⊎ ((x ≡ ω) ⊎ ⟨ ω ∈ x ⟩) → sq x
  go (inl x∈ω) = Empty.rec (infx x∈ω)
  go (inr (inl x≡ω)) = subst sq (sym x≡ω) squareω
  go (inr (inr ω∈x)) = split (lem (AmbCard x , isPropAmbCard x))
    where
    membersq : (β : V ℓ) → IsOrd β → ⟨ β ∈ x ⟩ → ⟨ ω ∈ β ⟩ → sq β
    membersq β oβ β∈x ω∈β = ih β β∈x oβ (inf-member β ω∈β)

    split : AmbCard x ⊎ (AmbCard x → Empty.⊥) → sq x
    split (inl ac) = at-amb (lem (sucV ω ∈ x))
      where
      at-amb : ⟨ sucV ω ∈ x ⟩ ⊎ (⟨ sucV ω ∈ x ⟩ → Empty.⊥) → sq x
      at-amb (inl sω∈x) =
        via-col-square x (amb-init' x ox ω∈x sω∈x ac membersq)
      at-amb (inr ¬sω) = at-suc (ord-tri (sucV ω) (suc-ord ω-ord) x ox)
        where
        not-below : ⟨ x ∈ sucV ω ⟩ → Empty.⊥
        not-below x∈sω = Empty.rec*
          (∈sucV-elim {A = ω} {x = x} {P = Empty.⊥* {ℓ-suc ℓ}}
            Empty.isProp⊥* x∈sω
            (λ x∈ω → lift (infx x∈ω))
            (λ x≡ω → lift (∈-irrefl ω
              (subst (λ w → ⟨ ω ∈ w ⟩) x≡ω ω∈x))))

        at-suc : ⟨ sucV ω ∈ x ⟩ ⊎ ((sucV ω ≡ x) ⊎ ⟨ x ∈ sucV ω ⟩) → sq x
        at-suc (inl sω∈x) = Empty.rec (¬sω sω∈x)
        at-suc (inr (inl sω≡x)) =
          subst sq sω≡x (sq-suc ω ω-ord (∈-irrefl ω) #∈ω squareω)
        at-suc (inr (inr x∈sω)) = Empty.rec (not-below x∈sω)

    split (inr nac) = at-data (owes x ox ω∈x nac)
      where
      at-data : Σ[ b ∈ V ℓ ]
                  (IsOrd b × ⟨ b ∈ x ⟩ × ⟨ ω ∈ b ⟩ × (⟪ x ⟫ ↪ ⟪ b ⟫))
              → sq x
      at-data (β , oβ , β∈x , ω∈β , d) =
        descent-amb x β ox oβ β∈x ω∈β d (membersq β oβ β∈x ω∈β)

-- =====================================================================
-- PART 4.  THE RECURSION.
-- =====================================================================

sq-band : band-owes
        → (x : V ℓ) → IsOrd x → ⟨ x ∈ sucV α₀ ⟩ → (⟨ x ∈ ω ⟩ → Empty.⊥)
        → sq x
sq-band owes x ox x∈suc infx = ∈-induction {P = Goal} (step owes) x ox infx

-- =====================================================================
-- PART 5.  THE CONSUMER MATCH.
-- =====================================================================

band-ord : (d : V ℓ) → ⟨ d ∈ sucV α₀ ⟩ → IsOrd d
band-ord d d∈ = ∈sucV-elim (isPropIsOrd d) d∈
  (λ d∈α₀ → mem-ord {A = α₀} oα₀ d d∈α₀)
  (λ d≡α₀ → subst IsOrd (sym d≡α₀) oα₀)

ConsumerShape : Type (ℓ-suc ℓ)
ConsumerShape =
  (δ : V ℓ) → ⟨ δ ∈ sucV α₀ ⟩ → (⟨ δ ∈ ω ⟩ → Empty.⊥)
  → Σ[ f ∈ (⟪ δ ⟫ × ⟪ δ ⟫ → ⟪ δ ⟫) ]
      ((p q : ⟪ δ ⟫ × ⟪ δ ⟫) → f p ≡ f q → p ≡ q)

plugs-in : band-owes → ConsumerShape
plugs-in owes δ δ∈ infδ = sq-band owes δ (band-ord δ δ∈) δ∈ infδ
