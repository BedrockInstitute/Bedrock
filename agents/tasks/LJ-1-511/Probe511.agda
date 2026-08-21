{-# OPTIONS --cubical --safe --guardedness #-}

-- [LJ-1.511] someEnvDef with the numeral truncation in its OWN type.
--
-- W3 FIRST, and alone: IS THE CORRECTED TYPE NON-VACUOUS?  `[LJ-1.507]`
-- proved that a green term against an empty antecedent is worth
-- nothing, so the obligation is omitted from this stage and added only
-- if W3 lands.
--
-- REBUILT, NOT IMPORTED.  `[LJ-1.504]`'s `Frame`, `gam'` and `K6` are
-- probe-local at their own task and are restated here at the type that
-- task's probe delivered.
--
-- ONE Agda process per run, GHCRTS="-A64m -I0 -M8g", the wide caliber,
-- set on the pane by the program and untouched here.  Nothing lands in
-- src/.

open import Base.Prelude
open import Base.Truth
open import Base.Classical using ( LEM )

module LJ-1-511.Probe511 {ℓ : Level} (lem : LEM (ℓ-suc ℓ)) where

open import FOL.ZFStructure using ( module hPropStructure )
import FOL.Absoluteness
open import V.Hierarchy {ℓ} using ( 𝒮ᵥ )
open import L.Constructible {ℓ} using ( 𝒮ʟ; isL; isL-trans; IsOrd )
open import L.Axioms.Numerals {ℓ} using ( numeralL; numeralL-fst )
open import L.Coding.Model {ℓ} using ( prʟ )
open import L.Condensation {ℓ} lem
  using ( module KValue; module KFactsNS; envHypB2 )
open import L.Condensation.LowerAgree {ℓ} lem using ( someEnvDef )
open import L.Coding.EnvSupply {ℓ} lem using ( module SupplyEnv )
open import Cubical.Data.Nat using ( ℕ; _+_ )
open import Cubical.HITs.CumulativeHierarchy.Base using ( V; _∈_ )
open import Cubical.HITs.CumulativeHierarchy.Constructions
  using ( module InfinitySet; ∅ )
open InfinitySet {ℓ} using ( #_; sucV; ω )
import Cubical.HITs.PropositionalTruncation as PT
open PT using ( ∥_∥₁ )

open TruthAlgebra (hPropAlgebra (ℓ-suc ℓ))
open hPropStructure 𝒮ʟ
open KFactsNS
open KFacts

module AbsL = FOL.Absoluteness.Single 𝒮ᵥ isL isL-trans
open AbsL renaming ( _⊨ᵐ_ to _⊨_ )

-- =====================================================================
-- THE CORRECTED DEFINITION.
--
-- COPIED VERBATIM from `src/L/Condensation/LowerAgree.lagda.md:52-58`,
-- the whole of `someEnvDef`, signature and body.
--
-- ADDED: ONE line, the fourth hypothesis
-- `∥ Σ[ n ∈ ℕ ] (fst ar ≡ # n) ∥₁`, marked below.  It is the numeral
-- truncation that `SupplyEnv.someEnv` asks for at
-- `src/L/Coding/EnvSupply.lagda.md:418` and that the record's field
-- does not carry.  It is placed AFTER the three memberships and BEFORE
-- the `Σ`, so every line of the copy keeps its position.
--
-- NOT ADDED, and deliberately: `gam`, and the gate `⟨ ω ∈ sucV gam ⟩`.
-- `[LJ-1.488]` measured that the gate "cannot be stated there without
-- adding `gam` as a parameter"
-- (`agents/tasks/LJ-1-488/lj-1.488-report.md:277-279`), and P-l forbids
-- a presentation of the ambient tower in a tower-generic type.  The
-- gate stays where `SupplyEnv` states it, by `[LJ-1.503]`.
--
-- The truncation needs no such parameter: it mentions only `ar`, which
-- this type already binds.  That is the whole reason this half lands
-- and the other half does not.
-- =====================================================================
someEnvDef' : {n : ℕ} (K : Fin (5 + n)) (γ : S ^ (11 + n)) → Type (ℓ-suc ℓ)
someEnvDef' {n} K γ =
  (ya yc b a ar c : S) → ⟨ fst ya ∈ fst (lookup (suc (suc (suc (suc (suc (suc K)))))) γ) ⟩
  → ⟨ fst yc ∈ fst (lookup (suc (suc (suc (suc (suc (suc K)))))) γ) ⟩
  → ⟨ fst ar ∈ fst (lookup (suc (suc (suc (suc (suc (suc K)))))) γ) ⟩
  → ∥ Σ[ n ∈ ℕ ] (fst ar ≡ # n) ∥₁                                  -- ADDED
  → Σ S (λ E → ⟨ fst E ∈ fst (lookup (suc (suc (suc (suc (suc (suc K)))))) γ) ⟩
    × ⟨ (E ∷ ya ∷ yc ∷ b ∷ a ∷ ar ∷ c ∷ γ) ⊨ envHypB2 {11 + n} zero (suc (suc (suc (suc (suc (suc K)))))) ⟩)

-- =====================================================================
-- THE COPY IS FAITHFUL, AND THIS TERM CHECKS IT RATHER THAN ASSERTING
-- IT.  `someEnvDef'` is meant to be the master's `someEnvDef` plus one
-- hypothesis and NOTHING else.  If any other line of the copy had
-- drifted, this weakening would not elaborate: it drops the added
-- hypothesis and returns the master's own type, applied argument for
-- argument.  So the master's definition drives the check, not my
-- transcription of it.
--
-- IT ALSO STATES THE DIRECTION OF THE CORRECTION.  The corrected type
-- is strictly WEAKER: `someEnvDef` implies `someEnvDef'`, and
-- `non-numeral-in-K` below says the converse fails.
-- =====================================================================
corrected-is-weaker :
    {n : ℕ} (K : Fin (5 + n)) (γ : S ^ (11 + n))
  → someEnvDef {n} K γ → someEnvDef' {n} K γ
corrected-is-weaker K γ f ya yc b a ar c yaK ycK arK _ =
  f ya yc b a ar c yaK ycK arK

-- =====================================================================
-- THE FRAME.  Taken from `[LJ-1.504]`'s DELIVERED probe
-- (`agents/tasks/LJ-1-504/Probe504.agda:47-60`), which `[LJ-1.507]`
-- rebuilt unchanged (`agents/tasks/LJ-1-507/Probe507.agda:136-149`).
-- `KValue`'s telescope plus `SupplyEnv`'s own gate.
-- =====================================================================

module Frame
  (lam : V ℓ) (ordλ : IsOrd lam)
  (succλ : (d : V ℓ) → ⟨ d ∈ lam ⟩ → ⟨ sucV d ∈ lam ⟩)
  (∅∈λ : ⟨ ∅ ∈ lam ⟩)
  (gam : V ℓ) (ordγ : IsOrd gam) (γ∈λ : ⟨ gam ∈ lam ⟩)
  (ω∈σ : ⟨ ω ∈ sucV gam ⟩) where

  module KV = KValue lam ordλ succλ ∅∈λ gam ordγ γ∈λ
  module SE = SupplyEnv lam ordλ succλ ∅∈λ gam ordγ γ∈λ ω∈σ

  gam' : (g1 g2 g3 g4 g5 : S) → S ^ 20
  gam' g1 g2 g3 g4 g5 = SE.B₀ ∷ g1 ∷ g2 ∷ g3 ∷ g4 ∷ g5 ∷ KV.Kenv

  -- `[LJ-1.504]`'s K index (`Probe504.agda:91-92`).
  K6 : Fin 20
  K6 = suc (suc (suc (suc (suc (suc KV.iK)))))

  -- The numeral zero, the one member of K this file needs by name.
  z : S
  z = numeralL 0

  -- ===================================================================
  -- W3.  IS THE CORRECTED TYPE NON-VACUOUS AT THIS FRAME?
  --
  -- `[LJ-1.507]` proved that `[LJ-1.504]`'s `someEnvDef-gap` has NO
  -- inhabitant at this very frame (`Probe507.agda:257-268`), so a term
  -- built above it inhabits nothing.  The SAME formula is now an
  -- ANTECEDENT rather than a claim, and those are different questions:
  -- a false Pi-statement over K is not an unsatisfiable hypothesis.
  -- This stage settles the second question and nothing else.
  --
  -- STAGE 1, the raw exhibit: one tuple satisfying all four
  -- hypotheses.  `numeralL 0` is in K by `numK0` and IS a numeral by
  -- `numeralL-fst 0`, so the very witness `[LJ-1.507]` could not find
  -- for the universal claim is immediate for the hypothesis.
  -- ===================================================================
  witness-tuple :
      (g1 g2 g3 g4 g5 : S)
    → Σ[ ya ∈ S ] Σ[ yc ∈ S ] Σ[ b ∈ S ] Σ[ a ∈ S ] Σ[ ar ∈ S ] Σ[ c ∈ S ]
        ( ⟨ fst ya ∈ fst (lookup K6 (gam' g1 g2 g3 g4 g5)) ⟩
        × ⟨ fst yc ∈ fst (lookup K6 (gam' g1 g2 g3 g4 g5)) ⟩
        × ⟨ fst ar ∈ fst (lookup K6 (gam' g1 g2 g3 g4 g5)) ⟩
        × ∥ Σ[ n ∈ ℕ ] (fst ar ≡ # n) ∥₁ )
  witness-tuple g1 g2 g3 g4 g5 =
    z , z , z , z , z , z ,
      ( KV.facts .numK0 , KV.facts .numK0 , KV.facts .numK0
      , PT.∣ 0 , numeralL-fst 0 ∣₁ )

  -- ===================================================================
  -- STAGE 2, and this is the decisive one.  A raw tuple can drift from
  -- the definition; this term cannot.  It takes an ASSUMED inhabitant
  -- of `someEnvDef'` at this frame, FEEDS it the tuple above, and
  -- returns the conclusion.  It elaborates only if every one of
  -- `someEnvDef'`'s own four hypotheses is inhabited at these
  -- arguments, so it reads the antecedents off the definition by name
  -- and cannot go stale if the definition is edited.
  -- ===================================================================
  antecedents-inhabited :
      ((g1 g2 g3 g4 g5 : S) → someEnvDef' {9} KV.iK (gam' g1 g2 g3 g4 g5))
    → (g1 g2 g3 g4 g5 : S)
    → Σ S (λ E → ⟨ fst E ∈ fst (lookup K6 (gam' g1 g2 g3 g4 g5)) ⟩
        × ⟨ (E ∷ z ∷ z ∷ z ∷ z ∷ z ∷ z ∷ gam' g1 g2 g3 g4 g5) ⊨
              envHypB2 {11 + 9} zero K6 ⟩)
  antecedents-inhabited f g1 g2 g3 g4 g5 =
    f g1 g2 g3 g4 g5 z z z z z z
      (KV.facts .numK0) (KV.facts .numK0) (KV.facts .numK0)
      PT.∣ 0 , numeralL-fst 0 ∣₁

  -- ===================================================================
  -- THE OBLIGATION.  `someEnvDef'` at `[LJ-1.504]`'s frame, inhabited.
  --
  -- The body is ONE application of the DELIVERED supplier
  -- (`src/L/Coding/EnvSupply.lagda.md:417-425`) and nothing else.  No
  -- postulate, no hole, no weakening of any hypothesis, and no term
  -- taken from `[LJ-1.504]`: its `gap-suffices` is a true implication
  -- out of an empty antecedent (`[LJ-1.507]`,
  -- `agents/tasks/LJ-1-507/Probe507.agda:257-268`) and is NOT cited as
  -- sufficiency here.  The truncation is a HYPOTHESIS of this type, and
  -- it is used exactly where `[LJ-1.500]` uses `arNumC`'s output: as
  -- the supplier's own first argument.
  --
  -- The three differences `[LJ-1.504]` measured are all discharged by
  -- this one application: the membership form (difference 1), the
  -- `envSetB` to `envHypB2` layout (difference 2), and the truncation
  -- (difference 3), which is now paid by the type instead of by a gap.
  -- ===================================================================
  someEnv-at-corrected-def :
      (g1 g2 g3 g4 g5 : S) → someEnvDef' {9} KV.iK (gam' g1 g2 g3 g4 g5)
  someEnv-at-corrected-def g1 g2 g3 g4 g5 ya yc b a ar c yaK ycK arK arNum =
    SE.someEnv ya yc b a ar c arNum yaK ycK arK

  -- ===================================================================
  -- AND THE ADDED HYPOTHESIS CARRIES CONTENT.  It is NOT derivable from
  -- the three memberships, and this term is the reason: `prʟ z z` is a
  -- member of K, by `pairK` on `numK0` twice, and `[LJ-1.507]` proved
  -- that it is not a numeral (`Probe507.agda:124-130`, `:257-268`).
  --
  -- So the correction is not cosmetic.  `someEnvDef` demanded a
  -- conclusion at THIS `ar`; `someEnvDef'` does not.
  -- ===================================================================
  non-numeral-in-K :
      (g1 g2 g3 g4 g5 : S)
    → ⟨ fst (prʟ z z) ∈ fst (lookup K6 (gam' g1 g2 g3 g4 g5)) ⟩
  non-numeral-in-K g1 g2 g3 g4 g5 =
    KV.facts .pairK z z (KV.facts .numK0) (KV.facts .numK0)

witness-tuple            = Frame.witness-tuple
antecedents-inhabited    = Frame.antecedents-inhabited
someEnv-at-corrected-def = Frame.someEnv-at-corrected-def
non-numeral-in-K         = Frame.non-numeral-in-K
