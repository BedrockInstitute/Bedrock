{-# OPTIONS --cubical --safe --guardedness #-}

-- [LJ-1.399] PROBE.  What it costs to CODE one delivered ambient map,
-- measured at ω.  It runs in agents/tasks/LJ-1-399/ and lands nothing.
--
-- The brief asks for two terms:
--
--     omega-pair-code : ∥ Σ[ A ∈ Mem (Lset (SiteBound.β (prodL ωL ωL))) ]
--                          InjCode (SiteBound.up (prodL ωL ωL) A)
--                                  (prodL ωL ωL) ωL ∥₁
--     omega-leg1      : sq ω
--
-- with `prodL` and `prod-bridge` taken as module hypotheses
-- ([LJ-1.388]'s terms) and NOT imported.
--
-- WHAT IS BUILT HERE, AND WHAT IS NOT.
--
--   `omega-leg1`'s ASSEMBLY is built, green: `leg1-gives-sq` is the
--   door + bridge composition at `ωL`, the exact analogue of
--   [LJ-1.386]'s `leg1-gives-sq` at δ := +ω ω, and it proves NOTHING
--   NEW (as the brief requires it to).  It lands in `sq (fst ωL)`,
--   which is `sq ω` because `fst ωL ≡ ω`.
--
--   `omega-pair-code` is the hard half and it is NOT built.  Two walls
--   stop it, and both are named in the report and the review file:
--
--   W1.  THE HYPOTHESES ARE NOT ENOUGH.  `prodL` and `prod-bridge`
--        alone do not determine the members of `prodL ωL ωL`.  The
--        code's `dom` conjunct demands a VALUE for EVERY member of the
--        internal square, and `prod-bridge` is only an INJECTION, not
--        a surjection.  The membership reading `prodL-out`
--        ([LJ-1.388] Probe388.agda:307) is exactly what is missing and
--        exactly what the brief did not hand over.
--
--   W2.  THE PAIRING FORMULA NEEDS ARITHMETIC THE TREE LACKS.  Even
--        with the membership reading, the graph of the ambient pairing
--        `pairω` (src/L/InjChain.lagda.md:184-185) is the Godel
--        collapse.  Its value at (a,b) is max(a,b)² + a + b (for
--        a ≥ b; max² + a for a < b), so an object-language formula
--        for it needs ADDITION and SQUARING of numerals.  The coding
--        vocabulary holds `sucAt` (src/L/Coding/Environment.lagda.md:136)
--        and `prAt`, but no addition and no multiplication:
--        grep for an `addAt`/`multAt`/`squareAt` formula returns
--        nothing.  So the graph cannot be carved as an L-element.
--
--   The hole below is the formal remainder, red by design, exactly as
--   [LJ-1.393] left its refuted `amb-init` (Probe393.agda:171-176).
--   Everything else in this file is green.

open import Base.Prelude
open import Base.Truth
open import Base.Classical using ( LEM )
open import Cubical.HITs.CumulativeHierarchy.Base using ( V )
open import L.Constructible using ( isL )
open import Cubical.HITs.CumulativeHierarchy.Properties using ( ⟪_⟫ )

-- The L-carrier, spelled out: `𝒮ʟ = 𝒮ᵥ ↾ isL`
-- (src/L/Constructible.lagda.md:410-411), so its carrier is the pairs
-- of a hierarchy set with a constructibility proof.  It is spelled
-- rather than named because `𝒮ʟ` sits at a fixed level, and the module
-- level `ℓ` is not yet in scope above the header; `V ℓ` and `⟨ isL x ⟩`
-- force the level by application.  `prod-bridge`'s injection type is
-- also spelled as a Sigma (the body of L.Cardinal's `_↪_`,
-- src/L/Cardinal.lagda.md:47-48), for the same reason, and both are
-- definitionally the types the door consumes.
module LJ-1-399.Probe399 {ℓ : Level} (lem : LEM (ℓ-suc ℓ))
  (prodL : (Σ[ x ∈ V ℓ ] ⟨ isL x ⟩) → (Σ[ x ∈ V ℓ ] ⟨ isL x ⟩) → (Σ[ x ∈ V ℓ ] ⟨ isL x ⟩))
  (prod-bridge : (a b : Σ[ x ∈ V ℓ ] ⟨ isL x ⟩)
               → Σ[ f ∈ (⟪ fst a ⟫ × ⟪ fst b ⟫ → ⟪ fst (prodL a b) ⟫) ]
                   ((x y : ⟪ fst a ⟫ × ⟪ fst b ⟫) → f x ≡ f y → x ≡ y))
  where

open import L.Constructible {ℓ} using ( Lset )
open import L.Ordinal {ℓ} using ( ω-ord )
open import L.Ordinal.SquareLaw {ℓ} lem using ( sq )
open import L.Choice.Step {ℓ} lem using ( Mem )
open import L.Cardinal {ℓ} lem using ( _↪_; InjCode; module SiteBound )

-- The door and the L-hood of every ordinal, delivered by [LJ-1.386].
open import LJ-1-386.Probe386 {ℓ} lem using ( code-untruncates; isL-ord )

open import Cubical.HITs.CumulativeHierarchy.Constructions
  using ( module InfinitySet )
open InfinitySet {ℓ} using ( ω; sucV )
import Cubical.HITs.PropositionalTruncation as PT
open PT using ( ∣_∣₁; ∥_∥₁ )

-- =====================================================================
-- ω AS AN L-ELEMENT.  `ωL` is the ambient `ω` with its constructibility
-- certificate, by [LJ-1.386]'s `isL-ord`.
-- =====================================================================

ωL : Σ[ x ∈ V ℓ ] ⟨ isL x ⟩
ωL = ω , isL-ord ω ω-ord

-- =====================================================================
-- THE DOOR + BRIDGE COMPOSITION, AT ωL.  This is [LJ-1.386]'s
-- `leg1-gives-sq` (Probe386.agda:294-302) re-instantiated at δ := ωL.
-- It PROVES NOTHING NEW: it is the mechanical check that a code of the
-- shape `omega-pair-code` has, run through the door and the bridge,
-- lands in the delivered `sq ω`.  It takes the code as an argument, so
-- it is green today, with the code itself still owed.
-- =====================================================================

leg1-gives-sq : (P : Σ[ x ∈ V ℓ ] ⟨ isL x ⟩)
              → ((⟪ fst ωL ⟫ × ⟪ fst ωL ⟫) ↪ ⟪ fst P ⟫)
              → ∥ Σ[ A ∈ Mem (Lset (SiteBound.β P)) ]
                    InjCode (SiteBound.up P A) P ωL ∥₁
              → sq (fst ωL)
leg1-gives-sq P bridge h = (λ p → fst read (fst bridge p)) , inj
  where
  read : ⟪ fst P ⟫ ↪ ⟪ fst ωL ⟫
  read = code-untruncates P ωL h

  inj : (p q : ⟪ fst ωL ⟫ × ⟪ fst ωL ⟫)
      → fst read (fst bridge p) ≡ fst read (fst bridge q) → p ≡ q
  inj p q e = snd bridge p q (snd read (fst bridge p) (fst bridge q) e)

-- =====================================================================
-- THE FIRST OBLIGATION.  The code for the ambient pairing at ω, out of
-- the internal square `prodL ωL ωL` and into `ωL`.
--
--   THIS HOLE IS RED BY DESIGN.  The two walls named in the header and
--   in agents/tasks/LJ-1-399/review-of-omega-pair-code.md stop it:
--   the hypothesis set (W1) does not determine the members of the
--   internal square, and the pairing formula (W2) needs object-language
--   arithmetic the tree does not hold.  Everything else in this file is
--   green; the file's only error is this unsolved meta.
-- =====================================================================

omega-pair-code : ∥ Σ[ A ∈ Mem (Lset (SiteBound.β (prodL ωL ωL))) ]
                      InjCode (SiteBound.up (prodL ωL ωL) A) (prodL ωL ωL) ωL ∥₁
omega-pair-code = ?

-- =====================================================================
-- THE SECOND OBLIGATION.  `sq ω`, by the door and the bridge.  It
-- PROVES NOTHING NEW, and it is built with the door (`code-untruncates`)
-- and the bridge, never with `squareω`.  It is a closed term of the
-- delivered type once `omega-pair-code` fills its hole.
-- =====================================================================

omega-leg1 : sq ω
omega-leg1 = leg1-gives-sq (prodL ωL ωL) (prod-bridge ωL ωL) omega-pair-code
