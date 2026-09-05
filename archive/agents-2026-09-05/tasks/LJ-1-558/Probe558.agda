{-# OPTIONS --cubical --safe --guardedness #-}

-- [LJ-1.558]  A route to `GCHStatement` that never lands inside
-- `Lset (fst δ)`.
--
-- SECTION 1 is W3 and the brief ordered it written FIRST and typechecked
-- ALONE: the step of [LJ-1.523]'s bridge whose conclusion sits in the
-- stage at δ, restated by itself, TYPE ONLY.  That slice is kept at
-- agents/tasks/LJ-1-558/runs/w3-slice.agda.txt.
--
-- Nothing is postulated.  Nothing lands in src/.  No hole.

open import Base.Prelude
open import Base.Truth
open import Base.Classical using ( LEM )

module LJ-1-558.Probe558 {ℓ : Level} (lem : LEM (ℓ-suc ℓ)) where

open import FOL.ZFStructure using ( module hPropStructure )
open import V.Hierarchy {ℓ} using ( 𝒮ᵥ )
open import L.Constructible {ℓ} using ( 𝒮ʟ; IsOrd; Lset; isL; isL-trans )
open import L.Cardinal {ℓ} lem using ( IsCardinalL )
open import L.GCH {ℓ} lem using ( GCHStatement; SuccCardL; InjL )
import FOL.ZFModel
open import Cubical.HITs.CumulativeHierarchy.Constructions
  using ( module InfinitySet )
open InfinitySet {ℓ} using ( ω )
open import Cubical.Data.Sigma using ( _×_ )
import Cubical.Data.Empty as Empty
import Cubical.HITs.PropositionalTruncation as PT
open PT using ( ∥_∥₁ )

open TruthAlgebra (hPropAlgebra (ℓ-suc ℓ))
open hPropStructure 𝒮ᵥ using ( _∈ˢ_ )

-- The V-carrier.  The bounded-subset theorem lives here.
module SV = hPropStructure 𝒮ᵥ
-- The L-carrier.  `GCHStatement` lives here.
module SL = hPropStructure 𝒮ʟ
-- The same instance `src/L/GCH.lagda.md:30` names, at the same 𝒮ʟ.
module ModelL = FOL.ZFModel 𝒮ʟ

-- =====================================================================
-- SECTION 1.  W3.  THE STAGE LANDING, RESTATED ALONE.
--
--   THE STEP.  `Devlin55.BoundedSubsetAt.Co.theorem : ⟨ x ∈ˢ Lset κ ⟩`
--   (src/L/BoundedSubset.lagda.md:1621).  [LJ-1.523] restated it as the
--   codomain of `Tele.At` (Probe523.agda:139); [LJ-1.550] applied it at
--   the assignment that serves the statement, theorem-κ := `fst δ` and
--   theorem-α := `fst κ`, and the result is `UseSite.member-in-stage`
--   (Probe550.agda:257-261), whose conclusion is
--   `⟨ fst y ∈ˢ Lset (fst δ) ⟩`.
--
--   THIS TYPE IS THAT CONCLUSION AND NOTHING ELSE: the three slots the
--   nine inputs could not fill are dropped, because W3 asks what the
--   step SAYS, not what it costs.  It is stated here TYPE ONLY.
-- =====================================================================

StageLanding : ModelL.isZFModel → Type (ℓ-suc ℓ)
StageLanding zf =
    (κ δ : SL.S) → SuccCardL δ κ
  → (y : SL.S) → ⟨ fst y ∈ˢ fst (𝒫 κ) ⟩
  → ⟨ fst y ∈ˢ Lset (fst δ) ⟩
  where open ModelL.isZFModel zf using ( 𝒫 )

-- =====================================================================
-- SECTION 2.  THE INPUTS OF THE ROUTE, COPIED LETTER FOR LETTER.
--
--   THREE, AND THE BRIEF NAMES ALL THREE.  B4 and B10 are
--   [LJ-1.523]'s rows (Probe523.agda:191-195 and :266-268), copied
--   without a change.  The third is the hard leg itself, which the
--   brief permits as a hypothesis in those words: "You may take
--   `InjL (𝒫 κ) δ` and `InjL δ (𝒫 κ)` themselves as hypotheses".
--
--   NOT ONE OF THE THREE NAMES AN AMBIENT TYPE.  `IsCardinal`
--   (src/L/BoundedSubset.lagda.md:1046-1047) and `_↪_` do not occur
--   below, and this file never imports the module that defines them.
-- =====================================================================

-- B4.  The successor L-cardinal exists.  Every conjunct of `SuccCardL`
-- is a type `GCHStatement` already names: `IsOrd` (src/L/GCH.lagda.md:48
-- and :62), `IsCardinalL` (:49 and :63), the V-membership `∈` (:50) and
-- the model's own `_⊆ˢ_` (:51-52, src/FOL/ZFModel.lagda.md:141-142).
SuccCardExists : Type (ℓ-suc ℓ)
SuccCardExists =
    (κ : SL.S) → IsOrd (fst κ) → IsCardinalL κ
  → (⟨ fst κ ∈ˢ ω ⟩ → Empty.⊥)
  → ∥ Σ[ δ ∈ SL.S ] SuccCardL δ κ ∥₁

-- THE HARD LEG, AS A HYPOTHESIS.  `GCHStatement`'s second conjunct
-- (src/L/GCH.lagda.md:67), verbatim, at the δ that B4 produces.  It is
-- the mirror of B10 and it is B10's row shape exactly.
PowerIntoSucc : ModelL.isZFModel → Type (ℓ-suc ℓ)
PowerIntoSucc zf =
    (κ δ : SL.S) → SuccCardL δ κ → InjL (𝒫 κ) δ
  where open ModelL.isZFModel zf using ( 𝒫 )

-- B10.  `GCHStatement`'s third conjunct (src/L/GCH.lagda.md:68).
SuccIntoPower : ModelL.isZFModel → Type (ℓ-suc ℓ)
SuccIntoPower zf =
    (κ δ : SL.S) → SuccCardL δ κ → InjL δ (𝒫 κ)
  where open ModelL.isZFModel zf using ( 𝒫 )

-- =====================================================================
-- SECTION 3.  THE OBLIGATION.
--
--   `GCHStatement zf`, from the three inputs of section 2 and nothing
--   else.  NO AMBIENT CARDINALITY FACT IS AMONG THEM, and no step of
--   the derivation has a conclusion inside `Lset (fst δ)`: the name
--   `Lset` does not occur in this section, and
--   agents/tasks/LJ-1-558/runs/NoStage558.agda.txt is the same term
--   typechecked in a module where `Lset` is NOT IN SCOPE
--   (agents/tasks/LJ-1-558/runs/nostage-1.out).
--
--   READ IT AGAINST SECTION 1.  `StageLanding` is bound nowhere here.
-- =====================================================================

gch-route-without-stage :
    (zf : ModelL.isZFModel)
  → SuccCardExists → PowerIntoSucc zf → SuccIntoPower zf
  → GCHStatement zf
gch-route-without-stage zf b4 hard b10 κ ordκ cardLκ κ∉ω =
  PT.map step (b4 κ ordκ cardLκ κ∉ω)
  where
  open ModelL.isZFModel zf using ( 𝒫 )
  step : Σ[ δ ∈ SL.S ] SuccCardL δ κ
       → Σ[ δ ∈ SL.S ] (SuccCardL δ κ × InjL (𝒫 κ) δ × InjL δ (𝒫 κ))
  step (δ , sc) = δ , sc , hard κ δ sc , b10 κ δ sc

-- =====================================================================
-- SECTION 4.  THE STAGE IS A MIDDLE OBJECT, AND THE MIDDLE OBJECT IS A
-- PARAMETER.
--
--   Section 3 took the hard leg whole.  This section takes it apart the
--   way [LJ-1.523]'s bridge takes it apart, and shows that the piece
--   the bridge fixes is left OPEN by the target.
--
--   [LJ-1.550] builds the hard leg in one line
--   (Probe550.agda:361-362):
--
--       hard = r6 (𝒫 κ) Lδ δ (r5 (𝒫 κ) Lδ into) (b9 δ Lδ U.ordδ refl)
--
--   That is a composite `𝒫 κ ↣ Lδ ↣ δ` through a MIDDLE OBJECT, and the
--   middle object is `Lδ = Lset (fst δ) , r4 δ U.ordδ`
--   (Probe550.agda:358-359).  `into` (Probe550.agda:354-356) is the
--   inclusion into that middle object, and `into` is the ONLY consumer
--   of `U.member-in-stage`, which is section 1.
--
--   `GCHStatement` names no middle object.  It names one arrow,
--   `InjL (𝒫 κ) δ` (src/L/GCH.lagda.md:67).  So the middle object is a
--   parameter of the route, and the stage is one value of it.
-- =====================================================================

-- Coded injections compose.  [LJ-1.550]'s residue R6
-- (Probe550.agda:332-333), copied letter for letter.  src/ has
-- `mutual-inj→bijection` (src/L/CantorBernstein.lagda.md:51-55) and no
-- transitivity, so this is a hypothesis here as it was there.
InjLTrans : Type (ℓ-suc ℓ)
InjLTrans = (a b c : SL.S) → InjL a b → InjL b c → InjL a c

-- SOME middle object at the successor, with no property asked of it.
-- It is not required to be a stage, an ordinal or a cardinal.
MiddleAtSucc : ModelL.isZFModel → Type (ℓ-suc ℓ)
MiddleAtSucc zf =
    (κ δ : SL.S) → SuccCardL δ κ
  → ∥ Σ[ m ∈ SL.S ] (InjL (𝒫 κ) m × InjL m δ) ∥₁
  where open ModelL.isZFModel zf using ( 𝒫 )

-- `InjL a b` is a propositional truncation (src/L/GCH.lagda.md:37-38),
-- so it is an hProp and `PT.rec` may land in it.
isPropInjL : (a b : SL.S) → isProp (InjL a b)
isPropInjL a b = PT.squash₁

-- The hard leg from ANY middle object.
hard-from-middle : (zf : ModelL.isZFModel)
                 → InjLTrans → MiddleAtSucc zf → PowerIntoSucc zf
hard-from-middle zf tr mid κ δ sc =
  PT.rec (isPropInjL (𝒫 κ) δ) use (mid κ δ sc)
  where
  open ModelL.isZFModel zf using ( 𝒫 )
  use : Σ[ m ∈ SL.S ] (InjL (𝒫 κ) m × InjL m δ) → InjL (𝒫 κ) δ
  use (m , i , j) = tr (𝒫 κ) m δ i j

-- THE ROUTE, WITH THE MIDDLE OBJECT OPEN.  Section 3's obligation with
-- its third input replaced by the composite.  Still no ambient
-- cardinality fact, and still no `Lset`.
gch-route-via-any-middle :
    (zf : ModelL.isZFModel)
  → SuccCardExists → InjLTrans → MiddleAtSucc zf → SuccIntoPower zf
  → GCHStatement zf
gch-route-via-any-middle zf b4 tr mid b10 =
  gch-route-without-stage zf b4 (hard-from-middle zf tr mid) b10

-- =====================================================================
-- SECTION 5.  [LJ-1.523]'S BRIDGE IS SECTION 4 AT ONE VALUE OF THE
-- PARAMETER.
--
--   The two residues the stage instantiation needs, and they are
--   [LJ-1.550]'s R4 and R5 copied letter for letter
--   (Probe550.agda:317-318 and :324-327), plus B9
--   (Probe523.agda:258-261).  Feed them to section 1 and the middle
--   object comes out as the stage.
--
--   SO THE ROW `AmbientCardAtSucc` (Probe550.agda:301-302) SITS BEHIND
--   `StageLanding` AND NOWHERE ELSE ON THE ROUTE.  [LJ-1.550] spends it
--   at Probe550.agda:355, inside `into`, and `into` is what section 1
--   replaces.  Nothing else in `bridge-with-residues`
--   (Probe550.agda:341-362) mentions it.
-- =====================================================================

-- R4 (Probe550.agda:317-318).
StageIsL : Type (ℓ-suc ℓ)
StageIsL = (δ : SL.S) → IsOrd (fst δ) → ⟨ isL (Lset (fst δ)) ⟩

-- R5 (Probe550.agda:324-327).
InclusionCoded : Type (ℓ-suc ℓ)
InclusionCoded = (a b : SL.S)
               → ((z : SV.S) → ⟨ z ∈ˢ fst a ⟩ → ⟨ z ∈ˢ fst b ⟩)
               → InjL a b

-- B9 (Probe523.agda:258-261).
StageCountedCoded : Type (ℓ-suc ℓ)
StageCountedCoded =
    (δ Lδ : SL.S) → IsOrd (fst δ) → (fst Lδ ≡ Lset (fst δ))
  → InjL Lδ δ

-- THE STAGE IS ONE MIDDLE OBJECT.  Section 1 is the whole of what this
-- consumes about the stage.
stage-is-one-middle :
    (zf : ModelL.isZFModel)
  → StageLanding zf → StageIsL → InclusionCoded → StageCountedCoded
  → MiddleAtSucc zf
stage-is-one-middle zf land r4 r5 b9 κ δ sc =
  ∣ Lδ , r5 (𝒫 κ) Lδ into , b9 δ Lδ ordδ refl ∣₁
  where
  open ModelL.isZFModel zf using ( 𝒫 )
  open PT using ( ∣_∣₁ )

  ordδ : IsOrd (fst δ)
  ordδ = fst sc

  Lδ : SL.S
  Lδ = Lset (fst δ) , r4 δ ordδ

  -- Every member of the model's power set is constructible, because L
  -- is transitive (src/L/Constructible.lagda.md:379).  The same step
  -- [LJ-1.550] takes at Probe550.agda:356.
  into : (z : SV.S) → ⟨ z ∈ˢ fst (𝒫 κ) ⟩ → ⟨ z ∈ˢ fst Lδ ⟩
  into z z∈ = land κ δ sc (z , isL-trans z∈ (snd (𝒫 κ))) z∈

-- THE MEASUREMENT.  `bridge-with-residues` (Probe550.agda:335-362) is
-- THIS term at THIS instantiation.  Read the two input lists side by
-- side: the difference is exactly `StageLanding`, and `StageLanding` is
-- what carries R1, R2 and R3.
bridge-is-this-route-at-the-stage :
    (zf : ModelL.isZFModel)
  → SuccCardExists → InjLTrans → SuccIntoPower zf
  → StageLanding zf → StageIsL → InclusionCoded → StageCountedCoded
  → GCHStatement zf
bridge-is-this-route-at-the-stage zf b4 tr b10 land r4 r5 b9 =
  gch-route-via-any-middle zf b4 tr (stage-is-one-middle zf land r4 r5 b9) b10
