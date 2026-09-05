{-# OPTIONS --cubical --safe --guardedness #-}

-- [LJ-1.739] PROBE.  asConst-in-carrier:  one carrier member, taken
-- as a constant, sits in the carrier's stage.  Lands nothing in src/.
--
--   THE OBLIGATION (brief LJ-1.739):
--     (γ : V ℓ) (oγ : IsOrd γ)
--     (A : S) → ⟨ fst A ∈ Lset γ ⟩
--     (m : ⟪ fst A ⟫)
--   → ⟨ fst (asConst A m) ∈ Lset γ ⟩
--
--   GLYPH RESOLUTIONS (recorded, the 738 discipline).
--   (1) The brief's third line puts the named binder (m : ⟪ fst A ⟫)
--       straight after the hypothesis ⟨ fst A ∈ Lset γ ⟩ with no
--       arrow between, and Agda parses that as application -- the
--       parse error at ⟪ on the brief-literal form is recorded in
--       runs/p-1.out.  The Pi is unambiguous, so the arrow moves
--       before the binder; argument order is exactly the brief's
--       (γ, oγ, A, hypothesis, m).
--   (2) `S` is the carrier of 𝒮ʟ, the Bridge's own carrier: a V ℓ
--       set with an isL proof (the Bridge opens hPropStructure 𝒮ʟ,
--       src/L/Coding/Bridge.lagda.md:27).  So `fst A : V ℓ`, and both
--       memberships of the obligation are the bare HITs `_∈_` of
--       CumulativeHierarchy.Base.
--   (3) `asConst A m : S` is the Bridge's constant embedding taken at
--       the module parameter B := A (src/L/Coding/Bridge.lagda.md:124-125).
--
--   THE ROUTE (the brief's premise 3, measured at
--   agents/tasks/LJ-1-725-SPLIT/Probe725Split.agda:71-79).  The
--   Bridge's ι = equivFun e (src/L/Definability.lagda.md:89-90)
--   lands m in the restricted carrier, and the Σ-component ι returns
--   IS the membership proof: SM = Σ[ x ∈ V ℓ ] ⟨ x ∈ fst A ⟩
--   (M x = x ∈ˢ A at 𝒮ᵥ, src/L/Definability.lagda.md:81-83;
--   InnerSmall.SM, src/V/Smallness.lagda.md:359-360), so
--   `fst (asConst A m)` -- definitionally `fst (DefOf.ι (fst A) m)`,
--   since intoL pairs and asConst composes (Bridge:121-125) -- is a
--   member of `fst A` by that component alone.  Lset-trans-set (this
--   file, Section 1: the 725-SPLIT three-line body rebuilt at the
--   bare membership glyph, from the same landed inputs Lset-out,
--   𝒟ₒ∋⊆, Lset-mono) then lifts it into Lset γ from the hypothesis.
--   The 725-SPLIT renaming ∈ˢᵥ is not needed here: the 𝒮ᵥ field
--   _∈ˢ_ is definitionally _∈_ (src/V/Hierarchy.lagda.md:78-85) and
--   𝒮ʟ's _∈ˢ_ is never named in this file.
--
--   THE PREDECESSOR.  [LJ-1.736] priced `Sat-in-carrier-lim` FALSE
--   over the wide alphabet Formula S n: a constant may sit above γ
--   (agents/tasks/LJ-1-736/lj-1.736-report.md:13, :15).  This bound
--   is the constant-side leaf the 736 review's corrected target and
--   the 738 report both point at (agents/tasks/LJ-1-738/
--   lj-1.738-report.md, section 3, point 2): every constant the
--   asConst alphabet names is an `asConst A m` with A's carrier in
--   Lset γ, and THIS file measures that the leaf holds.  Nothing here
--   inhabits Sat-in-carrier-lim or touches the wide alphabet.
--
--   WHAT IS DELIVERED.  One term, INHABITED: asConst-in-carrier
--   (Section 2), plus the transitivity lemma it consumes (Section 1).
--   `oγ` is carried unused: the transitivity of Lset γ needs no
--   ordinality.  No postulate; no hole; --safe.  ONE Agda process per
--   run, GHCRTS = "-A64m -I0 -M2g", the wide caliber, set on the pane
--   by the program and untouched here.

open import Base.Prelude
open import Base.Classical using ( LEM )

module LJ-1-739.Probe739 {ℓ : Level} (lem : LEM (ℓ-suc ℓ)) where

open import FOL.ZFStructure using ( module hPropStructure )
open import Cubical.HITs.CumulativeHierarchy.Base using ( V; _∈_ )
open import Cubical.HITs.CumulativeHierarchy.Properties using ( ⟪_⟫ )
import Cubical.HITs.PropositionalTruncation as PT
open PT using ( ∥_∥₁; squash₁ )

open import L.Constructible {ℓ}
  using ( 𝒮ʟ; IsOrd; Lset; Lset-mono; Lset-out; 𝒟ₒ; 𝒟ₒ∋⊆ )
open import L.Definability {ℓ} using ( module DefOf )
open import L.Coding.Bridge {ℓ} lem using ( asConst )

open hPropStructure 𝒮ʟ using ( S )

-- =====================================================================
-- SECTION 1.  Lset-trans-set.  Members of members of Lset γ lie in
-- Lset γ.  The 725-SPLIT delivery (Probe725Split.agda:71-79) rebuilt
-- at the bare membership glyph, from the same landed inputs:
-- Lset-out (src/L/Constructible.lagda.md:346-347) opens a member of
-- the stage as (δ in γ, x in 𝒟ₒ (Lset δ)), 𝒟ₒ∋⊆ (:323) pulls that
-- member's own members back under Lset δ, and Lset-mono (:365)
-- carries them up to Lset γ.
-- =====================================================================

Lset-trans-set : (γ a x : V ℓ)
               → ⟨ a ∈ x ⟩ → ⟨ x ∈ Lset γ ⟩ → ⟨ a ∈ Lset γ ⟩
Lset-trans-set γ a x a∈ x∈ = PT.rec (snd (a ∈ Lset γ)) step (Lset-out γ x x∈)
  where
  step : Σ[ δ ∈ V ℓ ] (⟨ δ ∈ γ ⟩ × ⟨ x ∈ 𝒟ₒ (Lset δ) ⟩)
       → ⟨ a ∈ Lset γ ⟩
  step (δ , (δ∈γ , x∈𝒟)) =
    Lset-mono {α = γ} {β = δ} δ∈γ {x = a}
      (𝒟ₒ∋⊆ (Lset δ) x x∈𝒟 a a∈)

-- =====================================================================
-- SECTION 2.  THE OBLIGATION.  INHABITED.
--
-- The member leaf: ι names m inside the restricted carrier, and the
-- Σ's second component IS the membership proof, so the term is that
-- component projected; the stage is transitive by Section 1.  The
-- conversion fst (asConst A m) ≡ fst (DefOf.ι (fst A) m) is
-- definitional (Bridge:121-125), so no transport appears.
-- =====================================================================

asConst-in-carrier :
    (γ : V ℓ) (oγ : IsOrd γ)
    (A : S) → ⟨ fst A ∈ Lset γ ⟩
  → (m : ⟪ fst A ⟫)
  → ⟨ fst (asConst A m) ∈ Lset γ ⟩
asConst-in-carrier γ oγ A hA m =
  Lset-trans-set γ (fst (asConst A m)) (fst A)
    (DefOf.ι (fst A) m .snd) hA
