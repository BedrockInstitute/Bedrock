{-# OPTIONS --cubical --safe --guardedness #-}

-- [LJ-1.707] PROBE.  ThroughDoor closed by its two named misses,
-- taken as HYPOTHESES.  Lands nothing in src/.
--
--   THE OBLIGATION  through-door-closed :
--     [LJ-1.693]'s ThroughDoor, taking [LJ-1.704]'s identification
--     (carved ≡ hierL) and [LJ-1.705]'s bound (bound-of's stage ∈ α)
--     as hypotheses.
--   DELIVERED       the route: the two hypotheses composed with
--                   from-door give HierInK end to end.
--   PREDECESSORS    [LJ-1.693] delivered the type, not inhabited.
--                   [LJ-1.698] opened the door on an unidentified set
--                   and recorded exactly two misses (its report :38-39,
--                   corrected target :117-120).  Those two rows ARE the
--                   hypotheses here.  Nothing else is taken.
--   FORBIDDEN HERE  Not rebuilding adequacy-bnd, not funding DOWN, not
--                   inhabiting ApproxInK ([LJ-1.698] report, premise 4).
--
-- ONE Agda process per run, GHCRTS wide caliber, set on the pane by
-- the program and untouched here.

open import Base.Prelude
open import Base.Truth
open import Base.Classical using ( LEM )

module LJ-1-707.Probe707 {ℓ : Level} (lem : LEM (ℓ-suc ℓ)) where

open import Cubical.HITs.CumulativeHierarchy.Base using ( V; _∈_ )
open import L.Constructible {ℓ} using ( isL; IsOrd; Lset )
open import L.Hierarchy {ℓ} lem using ( hierL )
open import LJ-1-693.Probe693 {ℓ} lem
  using ( ThroughDoor; Door; from-door; HierInK; IsLimit )
open import LJ-1-698.Probe698 {ℓ} lem using ( module Carved )
open import Cubical.HITs.PropositionalTruncation
  using ( ∥_∥₁; ∣_∣₁ )


-- =====================================================================
-- SECTION 1.  THE TWO HYPOTHESES, AT THE ROWS [LJ-1.698] CORRECTED.
--
-- Each row is the projection [LJ-1.704] (identification) and
-- [LJ-1.705] (bound) would deliver, universally quantified over the
-- telescope [LJ-1.698] states them at (lj-1.698-report.md:118-119):
-- the identification over (γ, oγ, hγ) alone, the bound over the
-- bridge's α and γ ∈ α.  A hypothesis may be WEAKER than what the
-- keystone delivers; it must never be stronger.
--
-- Field access goes through the module alias `At`, because Carved
-- takes (γ, oγ, hγ) and its fields carry those parameters.
-- =====================================================================

module At (γ : V ℓ) (oγ : IsOrd γ) (hγ : ⟨ isL γ ⟩) = Carved γ oγ hγ

identification : Type (ℓ-suc ℓ)
identification =
    (γ : V ℓ) (oγ : IsOrd γ) (hγ : ⟨ isL γ ⟩)
  → At.carved γ oγ hγ ≡ fst (hierL γ hγ oγ)

the-bound : Type (ℓ-suc ℓ)
the-bound =
    (α : V ℓ) → IsLimit α
  → (γ : V ℓ) (oγ : IsOrd γ) (hγ : ⟨ isL γ ⟩) → ⟨ γ ∈ α ⟩
  → ⟨ At.σ γ oγ hγ ∈ α ⟩


-- =====================================================================
-- SECTION 2.  THE ASSEMBLY.  THE TWO HYPOTHESES CLOSE THE DOOR.
--
-- δ is [LJ-1.705]'s stage σ itself.  δ ∈ α is the bound hypothesis.
-- Door (Lset σ) carved is [LJ-1.698]'s carved-door (its report, row
-- p-6), transported along [LJ-1.704]'s equation to the table's set.
-- No third input appears, and none of [LJ-1.698]'s forbidden list is
-- touched: nothing rebuilds adequacy-bnd, funds DOWN or inhabits
-- ApproxInK.  The zero case needs NO separate branch: at γ = ∅ both
-- hypotheses instance exactly as anywhere else ([LJ-1.698] paid
-- empty-door only to learn the zero case was not the miss).
-- =====================================================================

through-door-closed :
    identification
  → the-bound
  → ThroughDoor
through-door-closed ident bnd α lim β hβ oβ β∈α =
  ∣ At.σ β oβ hβ ,
    ( bnd α lim β oβ hβ β∈α
    , subst (λ x → Door (Lset (At.σ β oβ hβ)) x)
        (ident β oβ hβ)
        (At.carved-door β oβ hβ) )
  ∣₁


-- =====================================================================
-- SECTION 3.  THE WHOLE ROUTE, PRICED END TO END.
--
-- Composed with [LJ-1.693]'s own consumer, the two keystones deliver
-- HierInK with NOTHING else between them.
-- =====================================================================

the-route : identification → the-bound → HierInK
the-route ident bnd = from-door (through-door-closed ident bnd)
