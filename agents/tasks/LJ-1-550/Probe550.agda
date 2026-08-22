{-# OPTIONS --cubical --safe --guardedness #-}

-- [LJ-1.550]  Is B5 needed at all, when the target crosses no ambient
-- boundary.
--
-- SECTION 1 is W3 and the brief ordered it written first and typechecked
-- ALONE.  That slice is kept at agents/tasks/LJ-1-550/runs/w3-slice.agda.txt.
-- SECTION 2 copies [LJ-1.523]'s antecedent.  SECTION 3 copies the nine
-- other inputs and states the obligation's TYPE.  SECTION 4 applies the
-- antecedent at the only site that can serve the statement, and its type
-- is the ANSWER: it names every slot the nine cannot fill.  SECTION 5
-- closes the bridge from the nine PLUS six named residues.  SECTION 6
-- shows the site cannot be moved, and that B5 is strictly weaker than
-- the slot it was meant to fill.
--
-- THE OBLIGATION `bridge-without-B5` IS NOT HERE.  It is a NO-GO and
-- agents/tasks/LJ-1-550/review-of-bridge-without-B5.md states it.
--
-- Nothing is postulated.  Nothing lands in src/.  No hole.

open import Base.Prelude
open import Base.Truth
open import Base.Classical using ( LEM )

module LJ-1-550.Probe550 {ℓ : Level} (lem : LEM (ℓ-suc ℓ)) where

open import FOL.ZFStructure using ( module hPropStructure )
open import V.Hierarchy {ℓ} using ( 𝒮ᵥ )
open import L.Constructible {ℓ} using ( 𝒮ʟ; IsOrd; Lset; isL; isL-trans )
open import L.Ordinal {ℓ} using ( ω-ord )
open import L.Cardinal {ℓ} lem using ( IsCardinalL )
open import L.BoundedSubset {ℓ} lem using ( IsCardinal; _↪_; module Devlin55 )
open import L.GCH {ℓ} lem using ( GCHStatement; SuccCardL; InjL )
open import L.CantorBernstein {ℓ} lem using ( readL )
import FOL.ZFModel
open import Cubical.HITs.CumulativeHierarchy.Constructions
  using ( module InfinitySet; _∪_; ⁅_⁆s )
open InfinitySet {ℓ} using ( ω; sucV )
open import Cubical.HITs.CumulativeHierarchy.Properties using ( ⟪_⟫ )
open import Cubical.Data.Sigma using ( _×_ )
import Cubical.Data.Empty as Empty
import Cubical.HITs.PropositionalTruncation as PT
open PT using ( ∥_∥₁ )

open TruthAlgebra (hPropAlgebra (ℓ-suc ℓ))
open hPropStructure 𝒮ᵥ using ( _∈ˢ_ )

module SV = hPropStructure 𝒮ᵥ
module SL = hPropStructure 𝒮ʟ
module ModelL = FOL.ZFModel 𝒮ʟ

-- =====================================================================
-- SECTION 1.  W3.  DOES [LJ-1.523]'S BRIDGE CONSUME B5 AT ALL.
--
--   B5 is `AmbientSpentAtSucc` (agents/tasks/LJ-1-523/Probe523.agda:218-220),
--   copied here letter for letter.  The brief orders the bridge's
--   conclusion written with B5 BOUND AND UNUSED.
-- =====================================================================

CardSpentAt : SV.S → SV.S → Type ℓ
CardSpentAt κ α = ⟪ κ ⟫ ↪ ⟪ α ⟫ → Empty.⊥

AmbientSpentAtSucc : Type (ℓ-suc ℓ)
AmbientSpentAtSucc =
  (κ δ : SL.S) → SuccCardL δ κ → CardSpentAt (fst δ) (fst κ)

-- The bridge's conclusion, with B5 bound and never mentioned to its
-- right.  It elaborates, so THE BRIDGE TYPE DOES NOT CONSUME B5.
-- What this does NOT settle is whether an INHABITANT consumes it, and
-- no inhabitant exists: [LJ-1.523] was forbidden the term.
bridge-b5-unused : AmbientSpentAtSucc → ModelL.isZFModel → Type (ℓ-suc ℓ)
bridge-b5-unused _ zf = GCHStatement zf

-- =====================================================================
-- SECTION 2.  [LJ-1.523]'S ANTECEDENT, COPIED LETTER FOR LETTER.
--
--   agents/tasks/LJ-1-523/Probe523.agda:97-156.  Nothing here is
--   weakened and nothing is strengthened: the brief forbids changing
--   any hypothesis but B5.
-- =====================================================================

SqLaw : SV.S → Type (ℓ-suc ℓ)
SqLaw α =
    (δ : SV.S) → ⟨ δ ∈ˢ sucV α ⟩ → (⟨ δ ∈ˢ ω ⟩ → Empty.⊥)
  → Σ[ f ∈ (⟪ δ ⟫ × ⟪ δ ⟫ → ⟪ δ ⟫) ]
      ((u v : ⟪ δ ⟫ × ⟪ δ ⟫) → f u ≡ f v → u ≡ v)

module Tele
  (κ : SV.S) (ordκ : IsOrd κ) (cardκ : IsCardinal κ)
  (κ∉ω : ⟨ κ ∈ˢ ω ⟩ → Empty.⊥)
  (α : SV.S) (ordα : IsOrd α) (α∈κ : ⟨ α ∈ˢ κ ⟩)
  (α∉ω : ⟨ α ∈ˢ ω ⟩ → Empty.⊥)
  (sq : SqLaw α)
  (x : SV.S) (x⊆Lα : (z : SV.S) → ⟨ z ∈ˢ x ⟩ → ⟨ z ∈ˢ Lset α ⟩)
  (absorbs : ⟪ Lset α ∪ ⁅ x ⁆s ⟫ ↪ ⟪ Lset α ⟫)
  (lam : SV.S) (ordλ : IsOrd lam) (α∈λ : ⟨ α ∈ˢ lam ⟩)
  (succλ : (d : SV.S) → ⟨ d ∈ˢ lam ⟩ → ⟨ sucV d ∈ˢ lam ⟩)
  (x∈Lλ : ⟨ x ∈ˢ Lset lam ⟩)
  where

  module BSA = Devlin55.BoundedSubsetAt
    κ ordκ cardκ κ∉ω α ordα α∈κ α∉ω sq x x⊆Lα absorbs lam ordλ α∈λ succλ x∈Lλ

  LevelIn : Type (ℓ-suc ℓ)
  LevelIn = (δ : SV.S) → IsOrd δ → ⟨ δ ∈ˢ BSA.HS.C.πX ⟩
          → ⟨ Lset δ ∈ˢ BSA.HS.C.πX ⟩

  Cover : Type (ℓ-suc ℓ)
  Cover = (y : SV.S) → ⟨ y ∈ˢ BSA.HS.M ⟩
        → ∥ Σ[ γ ∈ SV.S ]
             ( IsOrd γ
             × ⟨ γ ∈ˢ BSA.HS.C.πX ⟩
             × ⟨ BSA.HS.C.π y ∈ˢ Lset γ ⟩ ) ∥₁

  At : Type (ℓ-suc ℓ)
  At = LevelIn → Cover → ⟨ x ∈ˢ Lset κ ⟩

BoundedSubsetTheorem : Type (ℓ-suc ℓ)
BoundedSubsetTheorem =
    (κ : SV.S) (ordκ : IsOrd κ) (cardκ : IsCardinal κ)
    (κ∉ω : ⟨ κ ∈ˢ ω ⟩ → Empty.⊥)
    (α : SV.S) (ordα : IsOrd α) (α∈κ : ⟨ α ∈ˢ κ ⟩)
    (α∉ω : ⟨ α ∈ˢ ω ⟩ → Empty.⊥)
    (sq : SqLaw α)
    (x : SV.S) (x⊆Lα : (z : SV.S) → ⟨ z ∈ˢ x ⟩ → ⟨ z ∈ˢ Lset α ⟩)
    (absorbs : ⟪ Lset α ∪ ⁅ x ⁆s ⟫ ↪ ⟪ Lset α ⟫)
    (lam : SV.S) (ordλ : IsOrd lam) (α∈λ : ⟨ α ∈ˢ lam ⟩)
    (succλ : (d : SV.S) → ⟨ d ∈ˢ lam ⟩ → ⟨ sucV d ∈ˢ lam ⟩)
    (x∈Lλ : ⟨ x ∈ˢ Lset lam ⟩)
  → Tele.At κ ordκ cardκ κ∉ω α ordα α∈κ α∉ω sq x x⊆Lα absorbs
      lam ordλ α∈λ succλ x∈Lλ

-- =====================================================================
-- SECTION 3.  THE NINE OTHER INPUTS, COPIED LETTER FOR LETTER.
--
--   B1 is the model, the bridge's own argument.  B2 and B3 live in
--   src/ and are imported, not hypothesised.  B4 and B6 to B10 are
--   agents/tasks/LJ-1-523/Probe523.agda:191-268.  B5 IS ABSENT.
-- =====================================================================

-- B4
SuccCardExists : Type (ℓ-suc ℓ)
SuccCardExists =
    (κ : SL.S) → IsOrd (fst κ) → IsCardinalL κ
  → (⟨ fst κ ∈ˢ ω ⟩ → Empty.⊥)
  → ∥ Σ[ δ ∈ SL.S ] SuccCardL δ κ ∥₁

-- B6
SubsetIntoStage : ModelL.isZFModel → Type (ℓ-suc ℓ)
SubsetIntoStage zf =
    (κ y : SL.S) → IsOrd (fst κ) → ⟨ fst y ∈ˢ fst (𝒫 κ) ⟩
  → (z : SV.S) → ⟨ z ∈ˢ fst y ⟩ → ⟨ z ∈ˢ Lset (fst κ) ⟩
  where open ModelL.isZFModel zf using ( 𝒫 )

-- B7
AbsorbsAt : Type (ℓ-suc ℓ)
AbsorbsAt =
    (α x : SV.S) → IsOrd α → (⟨ α ∈ˢ ω ⟩ → Empty.⊥)
  → ((z : SV.S) → ⟨ z ∈ˢ x ⟩ → ⟨ z ∈ˢ Lset α ⟩)
  → ⟪ Lset α ∪ ⁅ x ⁆s ⟫ ↪ ⟪ Lset α ⟫

-- B8
LimitAbove : Type (ℓ-suc ℓ)
LimitAbove =
    (α x : SV.S) → IsOrd α → ⟨ isL x ⟩
  → ∥ Σ[ lam ∈ SV.S ]
       ( IsOrd lam
       × ⟨ α ∈ˢ lam ⟩
       × ((d : SV.S) → ⟨ d ∈ˢ lam ⟩ → ⟨ sucV d ∈ˢ lam ⟩)
       × ⟨ x ∈ˢ Lset lam ⟩ ) ∥₁

-- B9
StageCountedCoded : Type (ℓ-suc ℓ)
StageCountedCoded =
    (δ Lδ : SL.S) → IsOrd (fst δ) → (fst Lδ ≡ Lset (fst δ))
  → InjL Lδ δ

-- B10
SuccIntoPower : ModelL.isZFModel → Type (ℓ-suc ℓ)
SuccIntoPower zf =
    (κ δ : SL.S) → SuccCardL δ κ → InjL δ (𝒫 κ)
  where open ModelL.isZFModel zf using ( 𝒫 )

-- THE OBLIGATION'S TYPE.  [LJ-1.523]'s bridge, with the nine other
-- inputs named and B5 REMOVED.  B2 and B3 are not arguments because
-- they are delivered in src/ (src/L/CantorBernstein.lagda.md:33-38
-- and :51-55).
BridgeWithoutB5 : ModelL.isZFModel → Type (ℓ-suc ℓ)
BridgeWithoutB5 zf =
    BoundedSubsetTheorem
  → SuccCardExists
  → SubsetIntoStage zf
  → AbsorbsAt
  → LimitAbove
  → StageCountedCoded
  → SuccIntoPower zf
  → GCHStatement zf

-- =====================================================================
-- SECTION 4.  THE ANTECEDENT, APPLIED AT THE ONLY SITE THAT SERVES.
--
--   [LJ-1.523] fixed the assignment (Probe523.agda:197-201): to land a
--   member of the model's `𝒫 κ` in the stage at δ, the THEOREM's κ must
--   be `fst δ` and the THEOREM's α must be `fst κ`.  Section 6 shows the
--   assignment is not a choice.
--
--   `CoHyps` is `levelIn` and `cover` over the whole telescope: row B11
--   of [LJ-1.523]'s table, which that report placed OFF the bridge's
--   bill (lj-1.523-report.md:239-242).  It is on the bill.  An
--   inhabitant of the bridge must apply the antecedent, and the
--   antecedent's conclusion is `LevelIn → Cover → ⟨ x ∈ˢ Lset κ ⟩`
--   (Probe523.agda:139).
-- =====================================================================

CoHyps : Type (ℓ-suc ℓ)
CoHyps =
    (κ : SV.S) (ordκ : IsOrd κ) (cardκ : IsCardinal κ)
    (κ∉ω : ⟨ κ ∈ˢ ω ⟩ → Empty.⊥)
    (α : SV.S) (ordα : IsOrd α) (α∈κ : ⟨ α ∈ˢ κ ⟩)
    (α∉ω : ⟨ α ∈ˢ ω ⟩ → Empty.⊥)
    (sq : SqLaw α)
    (x : SV.S) (x⊆Lα : (z : SV.S) → ⟨ z ∈ˢ x ⟩ → ⟨ z ∈ˢ Lset α ⟩)
    (absorbs : ⟪ Lset α ∪ ⁅ x ⁆s ⟫ ↪ ⟪ Lset α ⟫)
    (lam : SV.S) (ordλ : IsOrd lam) (α∈λ : ⟨ α ∈ˢ lam ⟩)
    (succλ : (d : SV.S) → ⟨ d ∈ˢ lam ⟩ → ⟨ sucV d ∈ˢ lam ⟩)
    (x∈Lλ : ⟨ x ∈ˢ Lset lam ⟩)
  → Tele.LevelIn κ ordκ cardκ κ∉ω α ordα α∈κ α∉ω sq x x⊆Lα absorbs
      lam ordλ α∈λ succλ x∈Lλ
  × Tele.Cover κ ordκ cardκ κ∉ω α ordα α∈κ α∉ω sq x x⊆Lα absorbs
      lam ordλ α∈λ succλ x∈Lλ

module UseSite (zf : ModelL.isZFModel)
  (bst : BoundedSubsetTheorem) (b6 : SubsetIntoStage zf)
  (b7 : AbsorbsAt) (b8 : LimitAbove)
  (κ δ : SL.S) (ordκ : IsOrd (fst κ)) (κ∉ω : ⟨ fst κ ∈ˢ ω ⟩ → Empty.⊥)
  (sc : SuccCardL δ κ)
  where
  open ModelL.isZFModel zf using ( 𝒫 )

  ordδ : IsOrd (fst δ)
  ordδ = fst sc

  κ∈δ : ⟨ fst κ ∈ˢ fst δ ⟩
  κ∈δ = fst (snd (snd sc))

  -- δ is infinite because κ is and κ ∈ δ.  ω is transitive
  -- (src/L/Ordinal.lagda.md:263, src/L/Constructible.lagda.md:141).
  δ∉ω : ⟨ fst δ ∈ˢ ω ⟩ → Empty.⊥
  δ∉ω δ∈ω = κ∉ω (fst ω-ord κ∈δ δ∈ω)

  -- THE ANSWER, AND IT IS THE TYPE AND NOT THE TERM.  Four of the
  -- theorem's slots the nine inputs fill: `x⊆Lα` by B6, `absorbs` by
  -- B7, the four limit slots by B8, and the ordinal and membership
  -- slots by `SuccCardL`.  THREE THEY DO NOT FILL, and they are the
  -- three arguments to the left: the AMBIENT cardinality at δ, the
  -- square law at `fst κ`, and `levelIn` with `cover`.
  member-in-stage :
      IsCardinal (fst δ)
    → SqLaw (fst κ)
    → CoHyps
    → (y : SL.S) → ⟨ fst y ∈ˢ fst (𝒫 κ) ⟩ → ⟨ fst y ∈ˢ Lset (fst δ) ⟩
  member-in-stage cardδ sq co y y∈ =
    PT.rec (snd (fst y ∈ˢ Lset (fst δ))) use (b8 (fst κ) (fst y) ordκ (snd y))
    where
    x⊆ : (z : SV.S) → ⟨ z ∈ˢ fst y ⟩ → ⟨ z ∈ˢ Lset (fst κ) ⟩
    x⊆ = b6 κ y ordκ y∈

    abs : ⟪ Lset (fst κ) ∪ ⁅ fst y ⁆s ⟫ ↪ ⟪ Lset (fst κ) ⟫
    abs = b7 (fst κ) (fst y) ordκ κ∉ω x⊆

    use : Σ[ lam ∈ SV.S ]
            ( IsOrd lam
            × ⟨ fst κ ∈ˢ lam ⟩
            × ((d : SV.S) → ⟨ d ∈ˢ lam ⟩ → ⟨ sucV d ∈ˢ lam ⟩)
            × ⟨ fst y ∈ˢ Lset lam ⟩ )
        → ⟨ fst y ∈ˢ Lset (fst δ) ⟩
    use (lam , ordλ , α∈λ , succλ , x∈Lλ) =
      bst (fst δ) ordδ cardδ δ∉ω (fst κ) ordκ κ∈δ κ∉ω sq (fst y) x⊆ abs
          lam ordλ α∈λ succλ x∈Lλ
          (fst hyps) (snd hyps)
      where
      hyps = co (fst δ) ordδ cardδ δ∉ω (fst κ) ordκ κ∈δ κ∉ω sq (fst y) x⊆ abs
                lam ordλ α∈λ succλ x∈Lλ

-- =====================================================================
-- SECTION 5.  THE BRIDGE, CLOSED FROM THE NINE PLUS SIX RESIDUES.
--
--   This is NOT the obligation and it is not offered as one.  It is the
--   measurement of the distance: `bridge-with-residues` is the whole
--   implication, green, and its type is the exact bill the nine inputs
--   leave open.  SIX residues, and ONE of them is ambient.
--
--   R1 is NOT B5.  B5 refutes an injection at ONE member of δ; the
--   antecedent's `cardκ` slot is `IsCardinal (fst δ)`, which refutes it
--   at EVERY member (src/L/BoundedSubset.lagda.md:1046-1047).  Section 6
--   gives the one direction that holds, and it is the wrong one.
-- =====================================================================

-- R1.  [LJ-1.523]'s `AmbientAtSucc` (Probe523.agda:202-204), which is
-- the row the antecedent's Π actually asks for.
AmbientCardAtSucc : Type (ℓ-suc ℓ)
AmbientCardAtSucc = (κ δ : SL.S) → SuccCardL δ κ → IsCardinal (fst δ)

-- R2.  The square law at `fst κ`, in the BARE form the antecedent asks
-- for.  This is B12: `SqCollect` (src/L/StageBound.lagda.md:44-48) is
-- what would produce it from `sq-trunc-closed`
-- (src/L/SquareLawClosed.lagda.md:325-327), and its own comment at
-- src/L/StageBound.lagda.md:42 says it is not inhabited.
SqAt : Type (ℓ-suc ℓ)
SqAt = (κ : SL.S) → IsOrd (fst κ) → SqLaw (fst κ)

-- R4.  The stage at δ is itself constructible.  B9's type quantifies
-- over an `Lδ : SL.S` with `fst Lδ ≡ Lset (fst δ)`
-- (Probe523.agda:258-261), so a user of B9 must produce one.  src/ has
-- `ord∈Lset-suc` (src/L/Ordinal/Stages.lagda.md:434) for the ORDINAL,
-- and nothing for the stage.
StageIsL : Type (ℓ-suc ℓ)
StageIsL = (δ : SL.S) → IsOrd (fst δ) → ⟨ isL (Lset (fst δ)) ⟩

-- R5.  An internal inclusion is a coded injection.  The only producers
-- of `InjCode` in src/ are src/L/Absorption.lagda.md:614 and
-- src/L/CodedShift.lagda.md:40, and both deliver the single shape
-- `InjCode F (sucʟ γ) γ`.
InclusionCoded : Type (ℓ-suc ℓ)
InclusionCoded = (a b : SL.S)
               → ((z : SV.S) → ⟨ z ∈ˢ fst a ⟩ → ⟨ z ∈ˢ fst b ⟩)
               → InjL a b

-- R6.  Coded injections compose.  src/L/CantorBernstein.lagda.md is the
-- only consumer of `InjL` in src/ and it delivers `mutual-inj→bijection`
-- (:51-55), not transitivity.
InjLTrans : Type (ℓ-suc ℓ)
InjLTrans = (a b c : SL.S) → InjL a b → InjL b c → InjL a c

bridge-with-residues :
    (zf : ModelL.isZFModel)
  → BoundedSubsetTheorem → SuccCardExists → SubsetIntoStage zf → AbsorbsAt
  → LimitAbove → StageCountedCoded → SuccIntoPower zf
  → AmbientCardAtSucc → SqAt → CoHyps → StageIsL → InclusionCoded → InjLTrans
  → GCHStatement zf
bridge-with-residues zf bst b4 b6 b7 b8 b9 b10 r1 r2 r3 r4 r5 r6
                     κ ordκ cardLκ κ∉ω =
  PT.map step (b4 κ ordκ cardLκ κ∉ω)
  where
  open ModelL.isZFModel zf using ( 𝒫 )
  step : Σ[ δ ∈ SL.S ] SuccCardL δ κ
       → Σ[ δ ∈ SL.S ] (SuccCardL δ κ × InjL (𝒫 κ) δ × InjL δ (𝒫 κ))
  step (δ , sc) = δ , sc , hard , b10 κ δ sc
    where
    module U = UseSite zf bst b6 b7 b8 κ δ ordκ κ∉ω sc

    -- Every member of the model's power set is constructible, because L
    -- is transitive (src/L/Constructible.lagda.md:379).
    into : (z : SV.S) → ⟨ z ∈ˢ fst (𝒫 κ) ⟩ → ⟨ z ∈ˢ Lset (fst δ) ⟩
    into z z∈ = U.member-in-stage (r1 κ δ sc) (r2 κ ordκ) r3
                  (z , isL-trans z∈ (snd (𝒫 κ))) z∈

    Lδ : SL.S
    Lδ = Lset (fst δ) , r4 δ U.ordδ

    hard : InjL (𝒫 κ) δ
    hard = r6 (𝒫 κ) Lδ δ (r5 (𝒫 κ) Lδ into) (b9 δ Lδ U.ordδ refl)

-- =====================================================================
-- SECTION 6.  THE SITE IS FORCED, AND B5 DOES NOT FILL IT.
--
--   The brief asks whether the ambient hypothesis can be moved off the
--   bridge.  On THIS bridge it cannot, and the reason is inside
--   `SuccCardL` itself.
-- =====================================================================

-- An AMBIENT cardinal is an L-cardinal.  The readback
-- (src/L/CantorBernstein.lagda.md:33-38) turns a code into an ambient
-- injection, so an ambient refutation refutes every code.
ambient→internal : (μ : SL.S) → IsCardinal (fst μ) → IsCardinalL μ
ambient→internal μ cardμ ν ν∈μ =
  PT.rec Empty.isProp⊥ (λ code → cardμ (fst ν) ν∈μ (readL μ ν code))

-- THE SITE CANNOT BE MOVED.  Suppose the antecedent were applied at
-- some other ambient cardinal μ above κ.  `SuccCardL`'s fourth conjunct
-- (src/L/GCH.lagda.md:51-53) is leastness among ORDINAL L-CARDINALS
-- above κ, and `ambient→internal` puts μ in that class.  So δ ⊆ μ.
-- The antecedent concludes `x ∈ˢ Lset μ`, and the statement needs the
-- membership at δ, which needs μ ⊆ δ.  Both together force μ ≡ δ.
site-forced : (κ δ μ : SL.S) → SuccCardL δ κ → IsOrd (fst μ)
            → IsCardinal (fst μ) → ⟨ fst κ ∈ˢ fst μ ⟩
            → ⟨ ModelL._⊆ˢ_ δ μ ⟩
site-forced κ δ μ sc ordμ cardμ κ∈μ =
  snd (snd (snd sc)) μ ordμ (ambient→internal μ cardμ) κ∈μ

-- B5 IS A CONSEQUENCE OF THE SLOT, NOT A FILLER FOR IT.  This direction
-- typechecks.  The converse is not a term: `IsCardinal (fst δ)` is a Π
-- over every member of δ and B5 gives one member.
b5-from-cardδ : (κ δ : SL.S) → SuccCardL δ κ → IsCardinal (fst δ)
              → CardSpentAt (fst δ) (fst κ)
b5-from-cardδ κ δ sc cd = cd (fst κ) (fst (snd (snd sc)))

-- THE SLOT, AS A TYPE, AT THE TWO LINES THAT SPEND IT.  [LJ-1.523]
-- measured that `BoundedSubsetAt` spends `cardκ` exactly twice, at
-- src/L/BoundedSubset.lagda.md:1597 and :1601, and BOTH times as
-- `cardκ α α∈κ`.  At the site section 4 fixes, that application has
-- this type, and it is B5's payload letter for letter.
SpentSlot : Type (ℓ-suc ℓ)
SpentSlot = (κ δ : SL.S) → SuccCardL δ κ → CardSpentAt (fst δ) (fst κ)

-- B5 IS THE SPENT SLOT AND THE TERM IS THE IDENTITY.  So the gap is
-- not what the module SPENDS.  It is what the module's telescope ASKS
-- FOR, which is `IsCardinal κ` and not `CardSpentAt κ α`.  Closing that
-- gap is an edit in src/L/BoundedSubset.lagda.md:1386, and this task
-- writes nothing there.  NOT AN OBLIGATION.
b5-is-the-spent-slot : AmbientSpentAtSucc → SpentSlot
b5-is-the-spent-slot b5 = b5
