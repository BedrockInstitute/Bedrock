{-# OPTIONS --cubical --safe --guardedness #-}

-- [LJ-1.739-SPLIT] PROBE.  asConst-in-carrier, re-landed at the path
-- the meter reads.  Lands nothing in src/.
--
--   THE OBLIGATION (brief LJ-1.739-SPLIT, the type taken literally):
--     asConst-in-carrier :
--         (γ : V ℓ) (oγ : IsOrd γ)
--         (A : S) → ⟨ fst A ∈ Lset γ ⟩
--       → (m : ⟪ fst A ⟫)
--       → ⟨ fst (asConst A m) ∈ Lset γ ⟩
--
--   THE PREDECESSOR.  [LJ-1.739] inhabited this exact term at
--   agents/tasks/LJ-1-739/Probe739.agda:110-117, verdict GO
--   (agents/tasks/LJ-1-739/lj-1.739-report.md:13).  That directory is
--   UNTRACKED in git, so the live meter reads supply 0 for the name;
--   this file is the tracked landing site the brief names.  The type
--   above is the brief's own bytes: the arrow before `(m : ⟪ fst A ⟫)`
--   is present, so no glyph repair is needed here (the 739 brief had
--   lost it; that resolution is recorded at Probe739.agda:21-29 and is
--   already baked into the type both briefs print).
--
--   GLYPH RESOLUTIONS (recorded, the 738 discipline).
--   (1) `S` is the carrier of 𝒮ʟ, the Bridge's own carrier: a V ℓ set
--       with an isL proof (the Bridge opens hPropStructure 𝒮ʟ,
--       src/L/Coding/Bridge.lagda.md:83; the restriction `_↾_` pairs
--       each element with its proof, src/FOL/ZFStructure.lagda.md:145-150).
--       So `fst A : V ℓ`, and both memberships of the obligation are
--       the bare HIT `_∈_`: the Lset-family names imported from
--       L.Constructible are stated over 𝒮ᵥ's carrier, and 𝒮ᵥ's `S` IS
--       `V ℓ` with `_∈ˢ_ = _∈_` (src/V/Hierarchy.lagda.md:79-85).
--   (2) `asConst A m : S` is the Bridge's constant embedding taken at
--       the module parameter B := A (src/L/Coding/Bridge.lagda.md:124-125).
--
--   THE ROUTE (the 739 probe's route, re-measured at this site).  The
--   Bridge's ι = equivFun e (src/L/Definability.lagda.md:89-90) lands
--   m in the restricted carrier, and the Σ-component ι returns IS the
--   membership proof: SM = Σ[ x ∈ S ] (x ∈ᶜ M) with M x = x ∈ˢ A at
--   𝒮ᵥ (src/L/Definability.lagda.md:80; InnerSmall.SM,
--   src/V/Smallness.lagda.md:359-360), so `fst (asConst A m)` --
--   definitionally `fst (DefOf.ι (fst A) m)`, since intoL pairs and
--   asConst composes (Bridge:121-125) -- is a member of `fst A` by
--   that component alone.  Lset-trans-set (Section 1: the 725-SPLIT
--   body rebuilt at the bare membership glyph, from the landed inputs
--   Lset-out, 𝒟ₒ∋⊆, Lset-mono) then lifts it into Lset γ from the
--   hypothesis.  No transport; no `≡` reasoning; `oγ` is carried
--   unused: transitivity of Lset γ needs no ordinality.
--
--   WHAT IS DELIVERED.  One term, INHABITED: asConst-in-carrier
--   (Section 2), plus the transitivity lemma it consumes (Section 1).
--   `Sat-in-carrier-lim` is NOT inhabited and the wide alphabet
--   `Formula S n` appears nowhere: [LJ-1.736] priced that statement
--   FALSE at the wide scope (agents/tasks/LJ-1-736/
--   lj-1.736-report.md:13), and this leaf is the constant-side
--   ingredient the corrected target consumes.  No postulate; no hole;
--   --safe.  ONE Agda process per run, GHCRTS = "-A64m -I0 -M2g", the
--   wide caliber, set on the pane by the program and untouched here.

open import Base.Prelude
open import Base.Classical using ( LEM )

module LJ-1-739-SPLIT.Probe739Split {ℓ : Level} (lem : LEM (ℓ-suc ℓ)) where

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
