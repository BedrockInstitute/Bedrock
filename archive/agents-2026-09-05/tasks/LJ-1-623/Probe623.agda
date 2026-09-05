{-# OPTIONS --cubical --safe --guardedness #-}

-- [LJ-1.623]  SiteFiber, THE LAST SUPPLY class-pred WANTS.  Second
-- attempt at this object, and the brief says so.
--
-- THE BRIEF'S OBLIGATION, re-stated VERBATIM:
--
--     site-fiber : SiteFiber α
--
-- with `SiteFiber` as [LJ-1.621] states it
-- (agents/tasks/LJ-1-621/Probe621.agda:77-78): one binary function
-- with its injectivity at ONE alpha.  Section 0's refl row proves
-- that type IS [LJ-1.618]'s `PairingAt α`
-- (agents/tasks/LJ-1-618/Probe618.agda:79-80), the payload of the
-- obligation [LJ-1.618] measured NO-GO.
--
-- NO TERM OF THIS FILE HAS THAT NAME, and no term of this file has
-- that type as its body: the tree does not inhabit it at an arbitrary
-- site, and this probe carries every row the tree holds, green, so
-- that each row is a measurement and not a claim.  What the probe
-- MEASURES is that the residue [LJ-1.618] left is the wall, UNCHANGED
-- at the site grain, and where the one route the tree grew since
-- [LJ-1.618] (the coded-injection readback) parks:
--
--   Section 0.  The obligation's type, tied to [LJ-1.618]'s payload.
--   Section 1.  THE RESIDUE, imported from this task's alone-checked
--               W3 and tied to [LJ-1.618]'s spelling by one refl.
--   Section 2.  THE DISCHARGE ROW: the residue ALONE finishes the
--               site.  [LJ-1.618]'s green recursion, applied at one
--               alpha.
--   Section 3.  THE CODED ROUTE, MEASURED.  `readL` re-ascribed; the
--               codes-as-data row; the ambient-to-coded bridge, TYPE
--               ONLY; and the LANDING row: every coded target sits at
--               or above the ambient least cardinal.
--   Section 4.  THE SITE COVERAGE: the site closes without the
--               residue exactly when the site is initial, and the
--               band still pays the site.
--   Section 5.  Why the residue is an untruncation and not a dne.
--
-- CALIBER.  THE PROGRAM SET GHCRTS ON THIS PANE.  I DID NOT SET IT.
-- ONE AGDA PROCESS AT A TIME.  Caps are set and reported per run in
-- `runs/`: the floor was measured BEFORE the final form (the landing
-- row holed), per the heavy-object rule.

open import Base.Prelude
open import Base.Truth
open import Base.Classical using ( LEM )
open import Cubical.HITs.CumulativeHierarchy.Base using ( V; _∈_ )
open import Cubical.HITs.CumulativeHierarchy.Properties using ( ⟪_⟫ )
open import Cubical.HITs.CumulativeHierarchy.Constructions
  using ( module InfinitySet )
open import L.Constructible using ( IsOrd )
import Cubical.Data.Empty as Empty
import Cubical.HITs.PropositionalTruncation as PT
open PT using ( ∣_∣₁; ∥_∥₁ )

module LJ-1-623.Probe623 {ℓ : Level} (lem : LEM (ℓ-suc ℓ))
  (α : V ℓ) (oα : IsOrd α)
  (α∉ω : ⟨ α ∈ InfinitySet.ω {ℓ} ⟩ → Empty.⊥) where

open InfinitySet using ( ω; sucV )
open import Cubical.Data.Sum using ( _⊎_; inl; inr )
open import Cubical.Data.Sigma using ( Σ-syntax )
open import L.Ordinal {ℓ} using ( ω-ord; suc-ord )
open import L.Ordinal.Linear {ℓ} lem using ( ord-tri )
open import L.Ordinal.SquareLaw {ℓ} lem using ( Init )
open import L.Cardinal {ℓ} lem using ( _↪_; InjCode )
open import L.SquareLawClosed {ℓ} lem ω ω-ord
open import L.CantorBernstein {ℓ} lem using ( readL )
open import FOL.ZFStructure using ( module hPropStructure )
open import V.Hierarchy {ℓ} using ( 𝒮ᵥ )
open import V.Model {ℓ} using ( self∈sucV )
open import L.Constructible {ℓ} using ( 𝒮ʟ )
open import LJ-1-594.runs.W3 using ( SqParam )
open hPropStructure 𝒮ᵥ using ( _∈ˢ_ )
open hPropStructure 𝒮ʟ using ( S )

import LJ-1-618.Probe618
import LJ-1-621.Probe621
import LJ-1-623.runs.W3

module P618 = LJ-1-618.Probe618 lem
module P621 = LJ-1-621.Probe621 lem α oα α∉ω
module W3site = LJ-1-623.runs.W3 lem α oα α∉ω

-- =====================================================================
-- SECTION 0.  THE OBLIGATION'S TYPE, and its identity with [LJ-1.618]'s
-- payload.  `SiteFiber` is IMPORTED from [LJ-1.621], not restated (the
-- brief's order, R-41's substance): one spelling.  The refl row is the
-- D-10 measurement that the site grain and [LJ-1.618]'s one-alpha
-- payload are the SAME type, so whatever wall [LJ-1.618] measured at
-- that payload is a wall at the site.
-- =====================================================================

site-is-pairing : P621.SiteFiber α ≡ P618.PairingAt α
site-is-pairing = refl

-- =====================================================================
-- SECTION 1.  THE RESIDUE, imported from the alone-typechecked W3 and
-- tied to [LJ-1.618]'s spelling by one refl, so the two cannot drift.
-- NOT INHABITED by any row of this file.
-- =====================================================================

residue-is-618s : W3site.Inj-extract-at-site ≡ P618.Inj-extract
residue-is-618s = refl

-- =====================================================================
-- SECTION 2.  THE DISCHARGE ROW.  [LJ-1.618]'s green recursion
-- (`pairing-from-extract`,
-- agents/tasks/LJ-1-618/Probe618.agda:210-211), applied at THIS site:
-- the residue alone finishes the site fiber.  This is the measurement
-- that the site grain needs exactly the residue, and nothing less.
-- =====================================================================

residue→site : P618.Inj-extract → P621.SiteFiber α
residue→site ext = P618.pairing-from-extract ext α oα α∉ω

-- =====================================================================
-- SECTION 3.  THE CODED ROUTE, MEASURED.  The tree's honest readback:
-- an L-ELEMENT coding an injection, held as DATA, reads out as an
-- ambient injection (`readL`, src/L/CantorBernstein.lagda.md:33-36,
-- through `Small`, src/L/Coding/Injection.lagda.md:123-151).
-- =====================================================================

-- 3.1  THE READBACK, RE-ASCRIBED.  Codes as data give the honest
--      ambient injection, at every pair, with no truncation anywhere.
coded→ambient : (a b : S) → Σ[ F ∈ S ] InjCode F a b
              → ⟪ fst a ⟫ ↪ ⟪ fst b ⟫
coded→ambient = readL

-- 3.2  CODES AS DATA, AT THE AMBIENT LEAST CARDINAL, CLEAR THE
--      RESIDUE.  The truncated hypothesis of the residue is discarded:
--      codes as data are strictly stronger than the truncated ambient
--      statement, and `readL` finishes from them.  The tree's own
--      device for turning truncated CODE existence into data is the
--      least-code selection (`chosen = leastOf (orderAt β oβ) lem
--      Good h`, src/L/Cardinal.lagda.md:194-195): the predicate is
--      hProp-valued, so the selection is legitimate.  What no row of
--      the tree supplies is the hypothesis below.
codes-at-κL→residue : ((a : S) (oa : IsOrd (fst a))
                       → Σ[ F ∈ S ] InjCode F a (κL a oa))
                    → P618.Inj-extract
codes-at-κL→residue h a oa _ = readL a (κL a oa) (h a oa)

codes→site : ((a : S) (oa : IsOrd (fst a))
              → Σ[ F ∈ S ] InjCode F a (κL a oa))
           → P621.SiteFiber α
codes→site h = residue→site (codes-at-κL→residue h)

-- 3.3  THE BRIDGE, TYPE ONLY.  From the truncated AMBIENT injection to
--      the truncated CODED one.  NOT INHABITED by any row of this file
--      or of the tree: the graph of an arbitrary ambient injection is
--      a subset of `a x b` that need not be constructible, so the
--      bridge is a choice principle and not a construction.  With it,
--      3.1 and the tree's least-code selection (3.2's comment) would
--      clear the residue outright.
AmbientToCoded : Type (ℓ-suc ℓ)
AmbientToCoded = (a b : S) → ∥ ⟪ fst a ⟫ ↪ ⟪ fst b ⟫ ∥₁
               → ∥ Σ[ F ∈ S ] InjCode F a b ∥₁

-- 3.4  THE LANDING ROW.  Every coded target sits AT OR ABOVE the
--      ambient least cardinal: a code at gamma carries an ambient
--      injection at gamma (`readL`), and the ambient search
--      (`leastOf ... InjP'`, src/L/Cardinal.lagda.md:116-117) then
--      cannot stop above gamma.  So the coded route parks at
--      `kappa-L(a) <= gamma`, and at `kappa-L(a)` itself only through
--      the bridge 3.3 declines to build.  Equality of the coded-least
--      and the ambient-least cardinal is exactly that bridge.
coded-sits-above : (a : S) (oa : IsOrd (fst a)) (γ : S)
                 → IsOrd (fst γ) → ∥ Σ[ F ∈ S ] InjCode F a γ ∥₁
                 → ⟨ fst (κL a oa) ∈ˢ sucV (fst γ) ⟩
coded-sits-above a oa γ oγ h = go (ord-tri (fst κ) oκ (fst γ) oγ)
  where
  κ : S
  κ = κL a oa

  oκ : IsOrd (fst κ)
  oκ = κoL a oa

  amb : ∥ ⟪ fst a ⟫ ↪ ⟪ fst γ ⟫ ∥₁
  amb = PT.map (readL a γ) h

  go : ⟨ fst κ ∈ fst γ ⟩ ⊎ ((fst κ ≡ fst γ) ⊎ ⟨ fst γ ∈ fst κ ⟩)
     → ⟨ fst κ ∈ˢ sucV (fst γ) ⟩
  go (inl κ∈γ) = suc-ord oγ .fst κ∈γ (self∈sucV (fst γ))
  go (inr (inl κ≡γ)) =
    subst (λ w → ⟨ fst κ ∈ˢ sucV w ⟩) κ≡γ (self∈sucV (fst κ))
  go (inr (inr γ∈κ)) =
    Empty.rec (κ-min-atL a oa (fst γ , isL-ord (fst γ) oγ) γ∈κ amb)

-- =====================================================================
-- SECTION 4.  THE SITE COVERAGE, at the site grain.
-- =====================================================================

-- 4.1  THE SITE CLOSES WITHOUT THE RESIDUE EXACTLY WHEN IT IS INITIAL.
--      [LJ-1.618]'s coverage map
--      (agents/tasks/LJ-1-618/lj-1.618-report.md:31-41) measured that
--      the tree's honest rows reach omega and the initial ordinals
--      only; this is the second half, re-ascribed at the site.
site-at-init : Init α → P621.SiteFiber α
site-at-init iα = P618.at-init α iα

-- 4.2  THE BAND STILL PAYS THE SITE, unchanged from [LJ-1.621]
--      (agents/tasks/LJ-1-621/Probe621.agda:135-136): the site
--      hypothesis is the strictly weaker one.
band-pays-site : SqParam α → P621.SiteFiber α
band-pays-site = P621.family-pays-the-site

-- =====================================================================
-- SECTION 5.  WHY THE RESIDUE IS AN UNTRUNCATION AND NOT A DNE.
--
-- 5.1  The truncation is BY CONSTRUCTION: the least-cardinal search
--      feeds `leastOf` an hProp, so the injection existence enters
--      truncated (`InjP γ = ∥ Inj γ ∥₁, squash₁`,
--      src/L/Cardinal.lagda.md:66-67) and the least index comes out
--      honest while the payload does not
--      (src/L/Cardinal.lagda.md:133-134).
--
-- 5.2  `dne` cannot extract it.  LEM in this tree gives
--      `dne : (P : hProp) → (¬⟨ P ⟩ → ⊥) → ⟨ P ⟩`
--      (src/L/StageCardinal.lagda.md:416), and it applies only to
--      PROPOSITIONS.  The payload `⟪ fst a ⟫ ↪ ⟪ fst (κL a oa) ⟫` is
--      a Sigma whose first component is a function: two injections
--      into one target can differ, so the payload is not a
--      proposition.  [LJ-1.107] recorded exactly this
--      (archive/dev/LJ-dispatch-index.md:183).
--
-- 5.3  The Kraus criterion (dev/literature/truncation-and-selection.md
--      :158-160, Theorem 16) says the residue is cleared exactly by a
--      weakly constant endomap on the payload type.  The tree BUILDS
--      one one grain over, at the CODE type: the least-code selection
--      normalizes every code to the least one
--      (src/L/Cardinal.lagda.md:194-195), and `readL` reads that one
--      back.  At the AMBIENT payload the endomap would have to
--      canonize injections into the least ordinal admitting them, and
--      no row of the tree builds one; section 3.3's bridge, which
--      would carry an ambient witness to the code grain where the
--      normalization lives, is a choice principle.  The full answer is
--      in the report's literature step.
-- =====================================================================
