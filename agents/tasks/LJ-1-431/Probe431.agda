{-# OPTIONS --cubical --safe --guardedness #-}

-- [LJ-1.431] PROBE.  The 424 device restated at a GENERIC ordinal γ,
-- then joined to a coded selection on the ambient carrier.  It runs
-- in agents/tasks/LJ-1-431/ and lands nothing in src/.
--
--   W3 FIRST  `coded-to-arrow-at`.  Four-conjunct Good and isProp
--             witness rebuilt from Probe424.agda:57-70.  Bound is a
--             generic γ with oγ, not SiteBound's β.  Applied to a
--             bare truncated hypothesis.  Selection omitted.
--             Typechecked ALONE before the obligation was written.
--
--   TERM      `arrow-at-kappaC`.  fst (snd selected) fed to the
--             device at κC.  nonempty-coded is a hypothesis; this
--             probe does not inhabit it.  [LJ-1.429] owes that
--             existence.  kappaC-ord is not assumed; [LJ-1.430] owes
--             it.  This term does not need it.
--
-- ONE Agda process per run, GHCRTS the wide caliber the program set
-- on the pane, untouched here.
-- No ambient injection in the telescope, truncated or otherwise.

open import Base.Prelude
open import Base.Truth
open import Base.Classical using ( LEM )

module LJ-1-431.Probe431 {ℓ : Level} (lem : LEM (ℓ-suc ℓ)) where

open import FOL.ZFStructure using ( module hPropStructure )
import FOL.Absoluteness
open import V.Hierarchy {ℓ} using ( 𝒮ᵥ )
open import V.Presentation {ℓ} using ( member )
open import V.Coding {ℓ} using ( pr )
open import L.Constructible {ℓ}
  using ( 𝒮ʟ; isL; isL-trans; IsOrd; Lset; Lset→isL )
open import L.Ordinal {ℓ} using ( suc-ord )
open import L.Ordinal.Stages {ℓ} lem using ( ord∈Lset-suc )
open import L.Ordinal.SquareLaw {ℓ} lem using ( ordSWO )
open import L.Choice.Step {ℓ} lem using ( Mem; orderAt )
open import L.WellOrder.Base {ℓₚ = ℓ-suc ℓ}
  using ( SWO; IsLeast; leastOf )
open import L.Coding.Model {ℓ} using ( svAt; domAt )
open import L.Coding.Injection {ℓ} lem using ( injAt )
open import L.Cardinal {ℓ} lem
  using ( _↪_; InjCode )
open import L.CantorBernstein {ℓ} lem using ( readL )

open import Cubical.HITs.CumulativeHierarchy.Base using ( V; _∈_ )
open import Cubical.HITs.CumulativeHierarchy.Properties
  using ( ⟪_⟫; ⟪_⟫↪ )
open import Cubical.HITs.CumulativeHierarchy.Constructions
  using ( module InfinitySet )
open InfinitySet {ℓ} using ( sucV )
open import Cubical.Foundations.HLevels using ( isProp×; isPropΠ )
import Cubical.HITs.PropositionalTruncation as PT
open PT using ( ∥_∥₁; squash₁ )

open hPropStructure 𝒮ʟ using ( S )

module AbsL = FOL.Absoluteness.Single 𝒮ᵥ isL isL-trans
open AbsL renaming ( _⊨ᵐ_ to _⊨_ )

-- =====================================================================
-- The range clause of InjCode (src/L/Cardinal.lagda.md:228), and the
-- isProp witness.  Reconstruction of Probe424.agda:57-70, which
-- returned GO.  Generic in F a b.  Names no stage.
-- =====================================================================

clause4 : S → S → Type (ℓ-suc ℓ)
clause4 F b =
  (x y : S) → ⟨ pr (fst x) (fst y) ∈ fst F ⟩ → ⟨ fst y ∈ fst b ⟩

clause4-isProp : (F b : S) → isProp (clause4 F b)
clause4-isProp F b =
  isPropΠ (λ x → isPropΠ (λ y → isPropΠ (λ _ → snd (fst y ∈ fst b))))

isPropInjCode : (F a b : S) → isProp (InjCode F a b)
isPropInjCode F a b =
  isProp× (snd ((F ∷ a ∷ []) ⊨ svAt zero))
    (isProp× (snd ((F ∷ a ∷ []) ⊨ domAt zero (suc zero)))
      (isProp× (snd ((F ∷ a ∷ []) ⊨ injAt zero))
        (clause4-isProp F b)))

-- =====================================================================
-- W3.  The 424 device at a generic ordinal γ.  No SiteBound.
-- Generic in a and in γ.  Typechecked ALONE, selection omitted.
--
-- Step two.  Coded selection on the ambient carrier of a.  The
-- well-order is sealed, as the chapter seals it
-- (src/L/Cardinal.lagda.md:90-92).  nonempty-coded is a hypothesis.
-- =====================================================================

module _ (a : S) (oa : IsOrd (fst a)) (γ : V ℓ) (oγ : IsOrd γ) where

  upγ : Mem (Lset γ) → S
  upγ (x , m) = x , Lset→isL γ oγ x m

  Good4 : (b : S) → Mem (Lset γ) → hProp (ℓ-suc ℓ)
  Good4 b A = InjCode (upγ A) a b , isPropInjCode (upγ A) a b

  coded-to-arrow-at : (b : S)
                    → ∥ Σ[ F ∈ Mem (Lset γ) ] InjCode (upγ F) a b ∥₁
                    → ⟪ fst a ⟫ ↪ ⟪ fst b ⟫
  coded-to-arrow-at b h = readL a b (upγ (fst chosen) , fst (snd chosen))
    where
    chosen = leastOf (orderAt γ oγ) lem (Good4 b) h

  hSucα : ⟨ isL (sucV (fst a)) ⟩
  hSucα = Lset→isL (sucV (sucV (fst a))) (suc-ord (suc-ord oa)) (sucV (fst a))
            (ord∈Lset-suc (sucV (fst a)) (suc-ord oa))

  upα : ⟪ sucV (fst a) ⟫ → S
  upα m = ⟪ sucV (fst a) ⟫↪ m
        , isL-trans (member (sucV (fst a)) m) hSucα

  opaque
    w : SWO (⟪ sucV (fst a) ⟫)
    w = ordSWO (sucV (fst a)) (suc-ord oa)

  CodedInjP' : ⟪ sucV (fst a) ⟫ → hProp (ℓ-suc ℓ)
  CodedInjP' d =
    ∥ Σ[ F ∈ Mem (Lset γ) ] InjCode (upγ F) a (upα d) ∥₁ , squash₁

  module _ (nonempty-coded
              : ∥ Σ[ d ∈ ⟪ sucV (fst a) ⟫ ] ⟨ CodedInjP' d ⟩ ∥₁) where

    selected : Σ[ d ∈ ⟪ sucV (fst a) ⟫ ] IsLeast w CodedInjP' d
    selected = leastOf w lem CodedInjP' nonempty-coded

    κC : S
    κC = upα (fst selected)

    arrow-at-kappaC : ⟪ fst a ⟫ ↪ ⟪ fst κC ⟫
    arrow-at-kappaC = coded-to-arrow-at κC (fst (snd selected))
