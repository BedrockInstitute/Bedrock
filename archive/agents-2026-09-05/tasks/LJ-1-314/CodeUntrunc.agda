{-# OPTIONS --cubical --safe --guardedness #-}

-- [LJ-1.314] REVIEW PROBE.  Adversarial DD25 review of [LJ-1.305].
--
-- THE CLAIM UNDER TEST.  [LJ-1.305] section 4 says one ruling on
-- `InjData` covers THREE sites of the shape "a truncated classical
-- existence whose payload is data", and names
-- src/L/Cardinal.lagda.md:132 and :256 as two of them.
--
-- THIS FILE MEASURES THAT THE TWO SITES ARE NOT THE SAME DEBT.
--
--   * :132, `κ-inj`, carries a truncated AMBIENT injection.  Its payload
--     is a function, so no `leastOf` reaches it.
--   * :256, `δ-inj`, carries a truncated CODED injection.  Its payload
--     is `InjCode`, which is a PROPOSITION, so `leastOf` over `orderAt`
--     untruncates it with NO new principle, and `Small` reads the code
--     back to an honest ambient injection, UNTRUNCATED.
--
-- Nothing lands.  Tracked probe.  ONE agda process under
-- GHCRTS="-A64m -I0 -M8g".

open import Base.Prelude
open import Base.Truth
open import Base.Classical using ( LEM )

module LJ-1-314.CodeUntrunc {ℓ : Level} (lem : LEM (ℓ-suc ℓ)) where

open import FOL.ZFStructure using ( module hPropStructure )
import FOL.Absoluteness
open import V.Hierarchy {ℓ} using ( 𝒮ᵥ )
open import V.Coding {ℓ} using ( pr )
open import L.Constructible {ℓ}
  using ( 𝒮ʟ; isL; isL-trans; IsOrd; Lset; Lset→isL )
open import L.Choice.Step {ℓ} lem using ( Mem; orderAt )
open import L.WellOrder.Base {ℓₚ = ℓ-suc ℓ} using ( SWO; IsLeast; leastOf )
open import L.Coding.Model {ℓ} using ( svAt; domAt )
open import L.Coding.Injection {ℓ} lem using ( injAt; module Small )
open import L.Cardinal {ℓ} lem using ( _↪_; InjCode )

open import Cubical.HITs.CumulativeHierarchy.Base using ( V; _∈_ )
open import Cubical.HITs.CumulativeHierarchy.Properties using ( ⟪_⟫ )
open import Cubical.Foundations.HLevels using ( isProp× )
import Cubical.HITs.PropositionalTruncation as PT
open PT using ( ∥_∥₁ )

open TruthAlgebra (hPropAlgebra (ℓ-suc ℓ))
open hPropStructure 𝒮ᵥ using ( _∈ˢ_ )
open hPropStructure 𝒮ʟ using ( S )

module AbsL = FOL.Absoluteness.Single 𝒮ᵥ isL isL-trans
open AbsL renaming ( _⊨ᵐ_ to _⊨_ )

-- =====================================================================
-- PART 1.  THE MECHANISM, GENERIC.
--
--   `leastOf` untruncates ANY existence over a well-ordered carrier
--   whose payload is a PROPOSITION.  The payload is returned by
--   `IsLeast` (src/L/WellOrder/Base.lagda.md:130-131), and `leastOf`
--   (`:158-160`) demands `P : A → hProp`.  So the whole question is
--   whether the payload is a proposition, and never whether the
--   existence is truncated.
-- =====================================================================

untruncAt : (β : V ℓ) (oβ : IsOrd β)
          → (P : Mem (Lset β) → Type (ℓ-suc ℓ))
          → ((F : Mem (Lset β)) → isProp (P F))
          → ∥ Σ[ F ∈ Mem (Lset β) ] P F ∥₁
          → Σ[ F ∈ Mem (Lset β) ] P F
untruncAt β oβ P pp h = fst big , fst (snd big)
  where
  big : Σ[ F ∈ Mem (Lset β) ] IsLeast (orderAt β oβ) (λ F → P F , pp F) F
  big = leastOf (orderAt β oβ) lem (λ F → P F , pp F) h

-- =====================================================================
-- PART 2.  `InjCode` IS A PROPOSITION.
--
--   Three satisfaction facts and one bounded implication.  Every
--   conjunct is the carrier of an hProp, so the product is one.
-- =====================================================================

isPropInjCode : (F a b : S) → isProp (InjCode F a b)
isPropInjCode F a b =
  isProp× (snd ((F ∷ a ∷ []) ⊨ svAt zero))
    (isProp× (snd ((F ∷ a ∷ []) ⊨ domAt zero (suc zero)))
      (isProp× (snd ((F ∷ a ∷ []) ⊨ injAt zero))
        (isPropΠ λ x → isPropΠ λ y → isPropΠ λ _ → snd (fst y ∈ fst b))))

-- =====================================================================
-- PART 3.  THE CODED SITE UNTRUNCATES TODAY.
--
--   This is src/L/Cardinal.lagda.md:256-258's `δ-inj` verbatim in
--   shape, turned into data.  NO new principle: `lem` and `orderAt`
--   only, both already in the telescope of `L.Cardinal`.
-- =====================================================================

up : (β : V ℓ) → IsOrd β → Mem (Lset β) → S
up β oβ (x , m) = x , Lset→isL β oβ x m

codeData : (β : V ℓ) (oβ : IsOrd β) (a b : S)
         → ∥ Σ[ F ∈ Mem (Lset β) ] InjCode (up β oβ F) a b ∥₁
         → Σ[ F ∈ Mem (Lset β) ] InjCode (up β oβ F) a b
codeData β oβ a b =
  untruncAt β oβ (λ F → InjCode (up β oβ F) a b)
    (λ F → isPropInjCode (up β oβ F) a b)

-- =====================================================================
-- PART 4.  AND THE CODE READS BACK, UNTRUNCATED.
--
--   `Small` (src/L/Coding/Injection.lagda.md:123-152) is the delivered
--   readback.  Composed with PART 3 it turns a TRUNCATED coded
--   existence into an HONEST ambient injection, with no new principle.
--   `amb→code` (agents/tasks/LJ-1-299/NoInj2.agda:103-111) uses the same
--   readback, but only under a propositional motive; here the motive is
--   data.
-- =====================================================================

readback : (F a b : S) → InjCode F a b → ⟪ fst a ⟫ ↪ ⟪ fst b ⟫
readback F a b (sv , dm , ij , ran) = Sm.small , Sm.small-inj
  where
  module Sm = Small F a b sv dm ij ran

codeInj : (β : V ℓ) (oβ : IsOrd β) (a b : S)
        → ∥ Σ[ F ∈ Mem (Lset β) ] InjCode (up β oβ F) a b ∥₁
        → ⟪ fst a ⟫ ↪ ⟪ fst b ⟫
codeInj β oβ a b h =
  readback (up β oβ (fst got)) a b (snd got)
  where
  got = codeData β oβ a b h

-- =====================================================================
-- PART 5.  WHAT THE RESIDUE ACTUALLY IS.
--
--   `InjData`'s content, after `leastOf` has taken the member for free
--   (src/L/Cardinal.lagda.md:116-134), is ONE atom: untruncate an
--   injection between two FIXED extensions.  This part measures that a
--   STAGE-BOUNDED ambient-to-code bridge discharges that atom outright,
--   with no new principle beyond the bridge.
--
--   `AmbientToCode` (agents/tasks/LJ-1-299/NoInj2.agda:131-133) returns
--   `Σ[ F ∈ S ]`, unbounded, and NO `SWO` in the tree carries `S`, so
--   `leastOf` cannot take it.  The bounded form below is what the tree
--   already posits at src/L/Cardinal.lagda.md:239-240.
-- =====================================================================

BoundedToCode : Type (ℓ-suc ℓ)
BoundedToCode = (a b : S) → ∥ ⟪ fst a ⟫ ↪ ⟪ fst b ⟫ ∥₁
              → Σ[ β ∈ V ℓ ] Σ[ oβ ∈ IsOrd β ]
                  ∥ Σ[ F ∈ Mem (Lset β) ] InjCode (up β oβ F) a b ∥₁

bridge→data : BoundedToCode
            → (a b : S) → ∥ ⟪ fst a ⟫ ↪ ⟪ fst b ⟫ ∥₁ → ⟪ fst a ⟫ ↪ ⟪ fst b ⟫
bridge→data btc a b h =
  codeInj (fst got) (fst (snd got)) a b (snd (snd got))
  where
  got = btc a b h
