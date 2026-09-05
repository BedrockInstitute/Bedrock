{-# OPTIONS --cubical --safe --guardedness #-}

-- [LJ-1.546]  What B10 wants BESIDE a code, and it is a pair mismatch.
--
-- The obligation is `transfer-suffices`, section 4.  Section 1 is W3:
-- the brief ordered it written first and typechecked ALONE, and that
-- slice is kept at agents/tasks/LJ-1-546/runs/w3-slice.agda.txt.
--
-- THE FINDING THIS FILE MEASURES.  `InjCode F a b`
-- (src/L/Cardinal.lagda.md:222-227) mentions its TARGET `b` in exactly
-- one of four conjuncts, and there only as an upper bound on the
-- range; it mentions its SOURCE `a` in exactly one conjunct too, but
-- `domAt` is a BICONDITIONAL (src/L/Coding/Model.lagda.md:279-280), so
-- the source is pinned.  Sections 3A and 3B are that asymmetry, both
-- inhabited.  The whole distance from CodedShift's pair to B10's pair
-- therefore sits on the SOURCE coordinate, and section 5 pays the
-- target coordinate in full to show it.
--
-- Nothing is postulated.  There is no hole.  Nothing lands in src/.

open import Base.Prelude
open import Base.Truth
open import Base.Classical using ( LEM )

module LJ-1-546.Probe546 {ℓ : Level} (lem : LEM (ℓ-suc ℓ)) where

open import FOL.ZFStructure using ( module hPropStructure )
open import V.Hierarchy {ℓ} using ( 𝒮ᵥ )
open import L.Constructible {ℓ} using ( 𝒮ʟ; isL; IsOrd )
open import L.Axioms.Infinity {ℓ} lem using ( ωʟ )
open import L.Axioms.Numerals {ℓ} using ( sucʟ )
open import L.Coding.Model {ℓ} using ( domAt; domAt-in; domAt-out )
open import L.Cardinal {ℓ} lem using ( InjCode; IsCardinalL )
open import L.CodedShift {ℓ} lem using ( shift-coded )
open import L.GCH {ℓ} lem using ( SuccCardL; InjL )
import FOL.ZFModel

open import Cubical.HITs.CumulativeHierarchy.Base using ( _∈_ )
open import Cubical.HITs.CumulativeHierarchy.Constructions
  using ( module InfinitySet )
open InfinitySet {ℓ} using ( #_ )
open import Cubical.Data.Nat using ( ℕ )
open import Cubical.Data.Sigma using ( _×_ )
import Cubical.Data.Empty as Empty
import Cubical.HITs.PropositionalTruncation as PT
open PT using ( ∣_∣₁; ∥_∥₁; squash₁ )

open TruthAlgebra (hPropAlgebra (ℓ-suc ℓ))

-- The L-carrier, the statement's carrier.  `𝒮ʟ = 𝒮ᵥ ↾ isL`
-- (src/L/Constructible.lagda.md:411), so `SL.S` is
-- Σ[ x ∈ V ℓ ] ⟨ isL x ⟩ and `fst` is the only map out of it.
module SL = hPropStructure 𝒮ʟ

-- The same instance src/L/GCH.lagda.md:30 names, at the same 𝒮ʟ.
module ModelL = FOL.ZFModel 𝒮ʟ
open ModelL using ( _⊆ˢ_; ℩-spec )

-- =====================================================================
-- SECTION 1.  W3.  THE WIDEST UNMEASURED TERM, TYPE ONLY.
--
--   `InjCode` was written for a STAGE in its second argument
--   (src/L/CodedShift.lagda.md:40 feeds it the ordinal γ).  Nobody has
--   fed it a POWER SET.  If this type does not form, B10 is refuted
--   before any reduction and the task is over.
-- =====================================================================

W3-code-at-power : ModelL.isZFModel → SL.S → SL.S → SL.S → Type (ℓ-suc ℓ)
W3-code-at-power zf F δ κ = InjCode F δ (𝒫 κ)
  where open ModelL.isZFModel zf using ( 𝒫 )

-- =====================================================================
-- SECTION 2.  D-10.  THE TWO PAIRS, SIDE BY SIDE, AS TYPES.
--
--   What CodedShift DELIVERS (src/L/CodedShift.lagda.md:38-40): a code
--   at the pair (sucʟ γ , γ).  Source: the ORDINAL successor of γ.
--   Target: γ itself, an ordinal.
--
--   What B10 WANTS (agents/tasks/LJ-1-523/Probe523.agda:266-269): a
--   code at the pair (δ , 𝒫 κ).  Source: the CARDINAL successor of κ,
--   which `SuccCardL` pins by a leastness clause over every ordinal
--   L-cardinal above κ (src/L/GCH.lagda.md:51-52).  Target: the
--   model's own power set of κ, which is not an ordinal at all.
--
--   THE DIFFERENCE IS BOTH COORDINATES.  Sections 3 and 5 measure
--   which of the two costs anything.
-- =====================================================================

-- The coding leg's pair, at CodedShift's own binding.
CodedShiftPair : SL.S → Type (ℓ-suc ℓ)
CodedShiftPair γ = ∥ Σ[ F ∈ SL.S ] InjCode F (sucʟ γ) γ ∥₁

-- B10's pair.
B10Pair : ModelL.isZFModel → SL.S → SL.S → Type (ℓ-suc ℓ)
B10Pair zf δ κ = ∥ Σ[ F ∈ SL.S ] InjCode F δ (𝒫 κ) ∥₁
  where open ModelL.isZFModel zf using ( 𝒫 )

-- B10, restated from agents/tasks/LJ-1-523/Probe523.agda:266-269,
-- letter for letter.  `InjL a b` unfolds to `B10Pair`'s body
-- (src/L/GCH.lagda.md:37-38).
SuccIntoPower : ModelL.isZFModel → Type (ℓ-suc ℓ)
SuccIntoPower zf =
    (κ δ : SL.S) → SuccCardL δ κ → InjL δ (𝒫 κ)
  where open ModelL.isZFModel zf using ( 𝒫 )

-- =====================================================================
-- SECTION 3.  THE ASYMMETRY, AND IT IS THE WHOLE ANSWER.
-- =====================================================================

-- 3A.  THE TARGET COORDINATE IS FREE.  `b` occurs in conjunct 4 alone
-- and only positively, so ENLARGING the target costs one composition.
-- The first three conjuncts are returned untouched: the elaborator
-- accepts them at the new target because they never mention it.
code-target-mono :
    (F a b c : SL.S) → InjCode F a b
  → ((y : SL.S) → ⟨ fst y ∈ fst b ⟩ → ⟨ fst y ∈ fst c ⟩)
  → InjCode F a c
code-target-mono F a b c (sv , dm , ij , ran) mono =
  sv , dm , ij , (λ x y p → mono y (ran x y p))

-- 3B.  THE SOURCE COORDINATE IS PINNED.  `domAt`'s second half
-- (src/L/Coding/Model.lagda.md:280) sends a member of the source to an
-- entry of the table, and its first half sends an entry back.  So ONE
-- table has ONE source, up to membership: no monotone analogue of 3A
-- can exist, and only a path `a ≡ a'` transports a code, which is
-- exactly the `subst` at src/L/CodedShift.lagda.md:53.
code-source-determined :
    (F a a' b b' : SL.S) → InjCode F a b → InjCode F a' b'
  → (x : SL.S) → ⟨ fst x ∈ fst a ⟩ → ⟨ fst x ∈ fst a' ⟩
code-source-determined F a a' b b' (_ , dm , _ , _) (_ , dm' , _ , _) x m =
  PT.rec (snd (fst x ∈ fst a'))
    (λ { (y , p) → domAt-out zero (suc zero) (F ∷ a' ∷ []) dm' x y p })
    (domAt-in zero (suc zero) (F ∷ a ∷ []) dm x m)

-- =====================================================================
-- SECTION 4.  THE NAMED FACT, AND THE OBLIGATION.
--
--   `SuccIntoSubsets` is the fact B10 reduces to.  It is stated at its
--   OWN frame: it names δ, κ, `InjCode` and the model's `⊆ˢ`, and it
--   names NEITHER `SuccIntoPower` NOR `𝒫` NOR a model record.  A later
--   coder can take it as one obligation with no `zf` in scope.
--
--   It says: δ admits a code into SOME L-set every member of which is
--   a subset of κ.  It does NOT ask for that set to BE `𝒫 κ`.  That is
--   the whole liberation 3A buys, and it is not free elsewhere: `𝒫 κ`
--   is `℩ (hasPower κ)` (src/FOL/ZFModel.lagda.md:287-288), so proving
--   a constructed set EQUAL to it needs the two-sided `IsSetOf`
--   (:74-75), while proving its members are subsets of κ needs one
--   side.
-- =====================================================================

SuccIntoSubsets : Type (ℓ-suc ℓ)
SuccIntoSubsets =
    (κ δ : SL.S) → SuccCardL δ κ
  → ∥ Σ[ b ∈ SL.S ] Σ[ F ∈ SL.S ]
       ( InjCode F δ b
       × ((y : SL.S) → ⟨ fst y ∈ fst b ⟩ → ⟨ y ⊆ˢ κ ⟩) ) ∥₁

-- THE OBLIGATION.  The named fact suffices for B10.  The model is
-- spent in exactly one place: `hasPower`'s specification turns "is a
-- subset of κ" into "is a member of 𝒫 κ".  `SuccCardL`'s leastness
-- clause is NOT consumed here: `sc` is passed straight through.
transfer-suffices : (zf : ModelL.isZFModel) → SuccIntoSubsets → SuccIntoPower zf
transfer-suffices zf tr κ δ sc =
  PT.rec squash₁
    (λ { (b , F , code , sub) →
           ∣ F , code-target-mono F δ b (𝒫 κ) code
                   (λ y m → subst ⟨_⟩ (sym (℩-spec (hasPower κ) y)) (sub y m))
           ∣₁ })
    (tr κ δ sc)
  where open ModelL.isZFModel zf using ( 𝒫; hasPower )

-- =====================================================================
-- SECTION 5.  THE TARGET COORDINATE, PAID IN FULL AT B10's OWN TARGET.
--
--   This is the measurement the brief asked for, made rather than
--   argued.  `shift-coded` (src/L/CodedShift.lagda.md:38-40) is the
--   coding leg's delivered conclusion.  Every member of an ordinal κ
--   is a subset of κ, so κ's members are members of `𝒫 κ`, and 3A
--   moves the code there with no new hypothesis.
--
--   WHAT IT PROVES.  A code whose target is a POWER SET is reachable
--   today, from a term already in `src/`.  So `𝒫 κ` is NOT a coding
--   wall, and none of `[LJ-1.533]`'s or `[LJ-1.535]`'s obstructions
--   is entered: no `Formula` is built here and no ambient injection is
--   coded.  The residue is the SOURCE, `sucʟ κ` against δ, alone.
-- =====================================================================

shift-into-power :
    (zf : ModelL.isZFModel) (κ : SL.S)
  → IsOrd (fst κ)
  → (⟨ fst κ ∈ fst ωʟ ⟩ → Empty.⊥)
  → ((k : ℕ) → ⟨ # k ∈ fst κ ⟩)
  → InjL (sucʟ κ) (ModelL.isZFModel.𝒫 zf κ)
shift-into-power zf κ oκ κ∉ω numerals =
  PT.map
    (λ { (F , code) →
           F , code-target-mono F (sucʟ κ) κ (𝒫 κ) code
                 (λ y m → subst ⟨_⟩ (sym (℩-spec (hasPower κ) y)) (mem→sub y m)) })
    (shift-coded κ oκ κ∉ω numerals)
  where
  open ModelL.isZFModel zf using ( 𝒫; hasPower )

  -- Ordinal transitivity, at the L-carrier.  `IsOrd`'s first component
  -- is `isTransV` (src/L/Constructible.lagda.md:141-142).
  mem→sub : (y : SL.S) → ⟨ fst y ∈ fst κ ⟩ → ⟨ y ⊆ˢ κ ⟩
  mem→sub y m x xm = fst oκ xm m

-- =====================================================================
-- SECTION 6.  THE LEASTNESS CLAUSE, ANSWERED BY THE ELABORATOR.
--
--   The brief named `SuccCardL`'s fourth component
--   (src/L/GCH.lagda.md:51-52) as the suspect and asked whether the
--   transfer needs it.  IT DOES NOT, AND NOTHING ELSE OF `SuccCardL`
--   EITHER.  The measurement is section 4's term with the whole
--   `SuccCardL` hypothesis DELETED from both sides.  If any line of
--   `transfer-suffices` projected `sc`, the term below would not
--   exist.  This is the `[LJ-1.540]` device
--   (agents/tasks/LJ-1-540/Probe540.agda:371-376).
--
--   READ THIS BEFORE REUSING `SuccIntoSubsets⁻`.  IT IS A MEASURING
--   ROD AND IT IS FALSE.  Drop `SuccCardL` and δ ranges over every
--   L-element, δ := κ⁺⁺ included, so an inhabitant of it would refute
--   GCH.  It is NOT a target, it is NOT a weakening proposal, and no
--   brief may take it as a hypothesis.  The named fact is
--   `SuccIntoSubsets`, section 4, and it KEEPS `SuccCardL`: the
--   leastness is not removed from the problem, it is located, and it
--   is located inside the named fact rather than inside the transfer.
-- =====================================================================

SuccIntoSubsets⁻ : Type (ℓ-suc ℓ)
SuccIntoSubsets⁻ =
    (κ δ : SL.S)
  → ∥ Σ[ b ∈ SL.S ] Σ[ F ∈ SL.S ]
       ( InjCode F δ b
       × ((y : SL.S) → ⟨ fst y ∈ fst b ⟩ → ⟨ y ⊆ˢ κ ⟩) ) ∥₁

leastness-not-consumed :
    (zf : ModelL.isZFModel) → SuccIntoSubsets⁻
  → (κ δ : SL.S) → InjL δ (ModelL.isZFModel.𝒫 zf κ)
leastness-not-consumed zf tr κ δ =
  PT.rec squash₁
    (λ { (b , F , code , sub) →
           ∣ F , code-target-mono F δ b (𝒫 κ) code
                   (λ y m → subst ⟨_⟩ (sym (℩-spec (hasPower κ) y)) (sub y m))
           ∣₁ })
    (tr κ δ)
  where open ModelL.isZFModel zf using ( 𝒫; hasPower )
