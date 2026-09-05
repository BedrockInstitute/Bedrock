{-# OPTIONS --cubical --safe --guardedness #-}

-- [LJ-1.446] PROBE.  The coded least cardinal is not strictly below
-- the ambient one.  It runs in agents/tasks/LJ-1-446/ and lands
-- nothing in src/.
--
--   W3 FIRST  `plug`.  [LJ-1.438]'s delivered type assigned to
--             [LJ-1.431]'s truncated coded existence.  Obligation
--             omitted.  Typechecked ALONE.
--
--   TERM      `kappaC-not-below`.  Written after W3 was green.
--             One application: κ-min-atL on ∣ arrow-at-kappaC ∣₁.
--
--   MODULE HYPOTHESIS.  coded-nonempty is bare, at [LJ-1.438]'s
--             delivered type (Probe438.agda:128-131).  Not inhabited.
--             That task's probe is not imported.
--
-- ONE Agda process per run, GHCRTS the wide caliber the program set
-- on the pane, untouched here.

open import Base.Prelude
open import Base.Truth
open import Base.Classical using ( LEM )

module LJ-1-446.Probe446 {ℓ : Level} (lem : LEM (ℓ-suc ℓ)) where

open import FOL.ZFStructure using ( module hPropStructure )
import FOL.Absoluteness
open import V.Hierarchy {ℓ} using ( 𝒮ᵥ )
open import V.Presentation {ℓ} using ( member )
open import V.Coding {ℓ} using ( pr )
open import L.Constructible {ℓ}
  using ( 𝒮ʟ; isL; isL-trans; IsOrd; Lset; Lset→isL )
open import L.Ordinal {ℓ} using ( bound2; suc-ord )
open import L.Ordinal.Stages {ℓ} lem using ( ord∈Lset-suc )
open import L.Ordinal.SquareLaw {ℓ} lem using ( ordSWO )
open import L.Stage {ℓ} lem using ( stage; stage-ord )
open import L.Choice.Step {ℓ} lem using ( Mem; orderAt )
open import L.WellOrder.Base {ℓₚ = ℓ-suc ℓ}
  using ( SWO; IsLeast; leastOf )
open import L.Coding.Model {ℓ} using ( svAt; domAt )
open import L.Coding.Injection {ℓ} lem using ( injAt )
open import L.Cardinal {ℓ} lem
  using ( _↪_; InjCode; module LeastCardInjL; module SiteBound )
open import L.CantorBernstein {ℓ} lem using ( readL )
open import L.InjChain {ℓ} lem using ( module InclGraph )

open import Cubical.HITs.CumulativeHierarchy.Base using ( V; _∈_ )
open import Cubical.HITs.CumulativeHierarchy.Properties
  using ( ⟪_⟫; ⟪_⟫↪ )
open import Cubical.HITs.CumulativeHierarchy.Constructions
  using ( module InfinitySet )
open InfinitySet {ℓ} using ( sucV )
open import Cubical.Foundations.HLevels using ( isProp×; isPropΠ )
import Cubical.Data.Empty as Empty
import Cubical.HITs.PropositionalTruncation as PT
open PT using ( ∣_∣₁; ∥_∥₁; squash₁ )

open hPropStructure 𝒮ᵥ using ( _∈ˢ_ )
open hPropStructure 𝒮ʟ using ( S )

module AbsL = FOL.Absoluteness.Single 𝒮ᵥ isL isL-trans
open AbsL renaming ( _⊨ᵐ_ to _⊨_ )

-- =====================================================================
-- The range clause of InjCode (src/L/Cardinal.lagda.md:228), and the
-- isProp witness.  Reconstruction of Probe431.agda:69-82.  Generic in
-- F a b.  Names no stage.
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
-- The ambient least cardinal, sealed at the call site (P-i, R-36).
-- Copied from Probe437.agda:90-107.  Five projections.  Do not import
-- a probe.
-- =====================================================================

opaque
  κL : (a : S) (oa : IsOrd (fst a)) → S
  κL a oa = LeastCardInjL.κ a oa

  κoL : (a : S) (oa : IsOrd (fst a)) → IsOrd (fst (κL a oa))
  κoL a oa = LeastCardInjL.oκ a oa

  κ∈sucL : (a : S) (oa : IsOrd (fst a)) → ⟨ fst (κL a oa) ∈ sucV (fst a) ⟩
  κ∈sucL a oa = LeastCardInjL.κ∈sα a oa

  κ-injL : (a : S) (oa : IsOrd (fst a))
         → ∥ ⟪ fst a ⟫ ↪ ⟪ fst (κL a oa) ⟫ ∥₁
  κ-injL a oa = LeastCardInjL.κ-inj a oa

  κ-min-atL : (a : S) (oa : IsOrd (fst a))
            → (δ : S) → ⟨ fst δ ∈ˢ fst (κL a oa) ⟩
            → ∥ ⟪ fst a ⟫ ↪ ⟪ fst δ ⟫ ∥₁ → Empty.⊥
  κ-min-atL a oa = LeastCardInjL.κ-min-at a oa

-- =====================================================================
-- Generic in a and in oa.  γ rebuilt from Probe438.agda:59-79.
-- Crossing rebuilt from Probe431.agda:108-122.  CodedInjP' is the
-- 431 spelling.  coded-nonempty is the 438 spelling, as a hypothesis.
-- =====================================================================

module _ (a : S) (oa : IsOrd (fst a)) where

  open SiteBound a

  module IG = InclGraph a a (λ _ h → h)

  G : S
  G = IG.G

  stgG : V ℓ
  stgG = stage (fst G) (snd G)

  oStg : IsOrd stgG
  oStg = stage-ord (fst G) (snd G)

  pair : Σ[ γ ∈ V ℓ ] (IsOrd γ × ⟨ β ∈ˢ γ ⟩ × ⟨ sucV stgG ∈ˢ γ ⟩)
  pair = bound2 β (sucV stgG) oβ (suc-ord oStg)

  γ : V ℓ
  γ = pair .fst

  oγ : IsOrd γ
  oγ = pair .snd .fst

  -- Crossing restated at γ, the same line Probe431.agda:95-96 writes
  -- at a generic ordinal, and the same line Probe438.agda:86-87 writes
  -- at this constructed bound.
  upγ : Mem (Lset γ) → S
  upγ (x , m) = x , Lset→isL γ oγ x m

  -- LeastCardInjL's crossing, rebuilt at the call site.
  -- Copied from Probe431.agda:108-114 / Probe438.agda:97-103.
  hSucα : ⟨ isL (sucV (fst a)) ⟩
  hSucα = Lset→isL (sucV (sucV (fst a))) (suc-ord (suc-ord oa)) (sucV (fst a))
            (ord∈Lset-suc (sucV (fst a)) (suc-ord oa))

  upα : ⟪ sucV (fst a) ⟫ → S
  upα m = ⟪ sucV (fst a) ⟫↪ m
        , isL-trans (member (sucV (fst a)) m) hSucα

  -- [LJ-1.431] spelling.  Probe431.agda:120-122.
  CodedInjP' : ⟪ sucV (fst a) ⟫ → hProp (ℓ-suc ℓ)
  CodedInjP' d =
    ∥ Σ[ F ∈ Mem (Lset γ) ] InjCode (upγ F) a (upα d) ∥₁ , squash₁

  -- [LJ-1.438] delivered type, as a module hypothesis.
  -- Probe438.agda:128-131.  Not inhabited.
  module _ (coded-nonempty :
              ∥ Σ[ d ∈ ⟪ sucV (fst a) ⟫ ]
                  ∥ Σ[ F ∈ Mem (Lset γ) ] InjCode (upγ F) a (upα d) ∥₁ ∥₁) where

    -- W3.  One line.  Does the 438 payment plug into the 431 selection.
    plug : ∥ Σ[ d ∈ ⟪ sucV (fst a) ⟫ ] ⟨ CodedInjP' d ⟩ ∥₁
    plug = coded-nonempty

    -- [LJ-1.431] device, Probe431.agda:98-106, at this γ.
    Good4 : (b : S) → Mem (Lset γ) → hProp (ℓ-suc ℓ)
    Good4 b A = InjCode (upγ A) a b , isPropInjCode (upγ A) a b

    coded-to-arrow-at : (b : S)
                      → ∥ Σ[ F ∈ Mem (Lset γ) ] InjCode (upγ F) a b ∥₁
                      → ⟪ fst a ⟫ ↪ ⟪ fst b ⟫
    coded-to-arrow-at b h = readL a b (upγ (fst chosen) , fst (snd chosen))
      where
      chosen = leastOf (orderAt γ oγ) lem (Good4 b) h

    -- Sealed well-order, same seal as Probe431.agda:116-118 and
    -- src/L/Cardinal.lagda.md:90-92.
    opaque
      w : SWO (⟪ sucV (fst a) ⟫)
      w = ordSWO (sucV (fst a)) (suc-ord oa)

    -- [LJ-1.431] selection, Probe431.agda:127-134.  nonempty-coded
    -- is plug: W3 showed the two spellings meet.
    selected : Σ[ d ∈ ⟪ sucV (fst a) ⟫ ] IsLeast w CodedInjP' d
    selected = leastOf w lem CodedInjP' plug

    κC : S
    κC = upα (fst selected)

    arrow-at-kappaC : ⟪ fst a ⟫ ↪ ⟪ fst κC ⟫
    arrow-at-kappaC = coded-to-arrow-at κC (fst (snd selected))

    -- THE OBLIGATION.  One application.  The coded arrow is DATA, so
    -- ∣_∣₁ is the only step to the truncated injection the ambient
    -- minimality asks for.
    kappaC-not-below :
        ⟨ fst κC ∈ˢ fst (κL a oa) ⟩ → Empty.⊥
    kappaC-not-below κC∈κL =
      κ-min-atL a oa κC κC∈κL ∣ arrow-at-kappaC ∣₁
