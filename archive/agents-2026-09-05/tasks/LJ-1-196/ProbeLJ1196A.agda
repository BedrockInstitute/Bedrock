{-# OPTIONS --cubical --safe --guardedness #-}

-- [LJ-1.196] probe A.  THE MINIATURE: can the ambient `DefAt` reading
-- be closed by `abs₀` + `DefAt-stage` + a slot-agreement lemma?
--
-- The dead agent's first step, VERIFIED GREEN below: the ambient
-- reading of the pushed `DefAt` is definitionally the class OUTER
-- reading (`⊨-map`, fst ∘ emb = fst).  Its second step is `abs₀`,
-- which demands a `Δ₀` witness.  The blocker, exposed at the bottom:
-- `DefAt u w` unfolds to `extAt u (∃̇ (∃̇ (DefBody w)))`, and `extAt`
-- is two UNBOUNDED `∀̇`.  `Δ₀` has no constructor for `∀̇` or `∃̇`
-- (FOL.LevyHierarchy: "absence is the classification"), so `abs₀`
-- cannot be applied to `DefAt` at all.
--
-- ONE agda process under GHCRTS="-A64m -I0 -M8g".  Tracked, never
-- deleted, lives beside its report.

open import Base.Prelude
open import Base.Truth
open import Base.Classical using ( LEM )

module LJ-1-196.ProbeLJ1196A {ℓ : Level} (lem : LEM (ℓ-suc ℓ)) where

open import FOL.ZFStructure using ( module hPropStructure; Transitive )
open import FOL.Syntax using ( Formula; ∃̇_ )
open import FOL.LevyHierarchy using ( Δ₀ )
open import FOL.Manipulation.Relabelling using ( mapFo; ⊨-map )
open import V.Hierarchy {ℓ} using ( 𝒮ᵥ )
open import L.Constructible {ℓ} using ( 𝒮ʟ; isL; isL-trans )
import FOL.Absoluteness
import FOL.Semantics
import L.Coding.Powerset {ℓ} lem as CP
import L.Coding.Model {ℓ} as CM

open import Cubical.Data.Sigma using ( _,_ )
open import Cubical.Data.Unit using ( Unit*; tt*; isPropUnit* )
open import Cubical.Data.Vec using ( Vec; map )

open TruthAlgebra (hPropAlgebra (ℓ-suc ℓ))
open hPropStructure 𝒮ᵥ
-- S = V ℓ: the ambient sets.  The class carrier's model elements are
-- Σ isL = Σ[ x ∈ S ] ⟨ isL x ⟩; the ambient carrier's are Σ Full.

module AbsL = FOL.Absoluteness.Single 𝒮ᵥ isL isL-trans
-- AbsL.SM = Σ isL.  _⊨ᵐ_ is the CLASS (inner) reading; _⊨ᵛ_ is the
-- class OUTER reading (interpretation fst : Σ isL → S).

Full : S → Ω
Full _ = Unit* {ℓ-suc ℓ} , isPropUnit*

Full-tr : Transitive 𝒮ᵥ Full
Full-tr {x = x} {y = y} h k = tt*

module AbsF = FOL.Absoluteness.Single 𝒮ᵥ Full (λ {x} {y} → Full-tr {x} {y})
-- AbsF.SM = Σ Full, the ambient carrier's model elements.

emb : AbsL.SM → AbsF.SM
emb (x , p) = x , tt*

-- THE AMBIENT READING, at the projected environment.
ambient : ∀ {n} → Vec AbsF.SM n → Formula AbsF.SM n → Ω
ambient γ φ = (map fst γ) AbsF.⊨ᵛ φ

-- =====================================================================
-- FACT 1 (GREEN): `DefAt` is the extensional description at two
-- UNBOUNDED existentials.  This is `src/L/Coding/Powerset.lagda.md:442-443`.
-- =====================================================================
defAt-shape : ∀ {n} (u w : Fin n)
  → CP.DefAt u w ≡ CM.extAt u (∃̇ (∃̇ (CP.DefBody w)))
defAt-shape u w = refl

-- =====================================================================
-- FACT 2 (GREEN): the dead agent's FIRST step.  The ambient reading of
-- the pushed `DefAt` IS the class OUTER reading, because fst ∘ emb is
-- fst definitionally.  This is `⊨-map` at f = emb, ι = fst.
-- =====================================================================
ambientPushed≡outer : ∀ {n} (u w : Fin n) (γ : Vec AbsF.SM n)
  → ambient γ (mapFo emb (CP.DefAt u w))
  ≡ (map fst γ) AbsL.⊨ᵛ (CP.DefAt u w)
ambientPushed≡outer u w γ =
  ⊨-map (hPropAlgebra (ℓ-suc ℓ)) 𝒮ᵥ emb fst (CP.DefAt u w) (map fst γ)

-- =====================================================================
-- FACT 3 (GREEN): the SECOND step is `abs₀`, and its type demands a
-- Δ₀ witness.  `abs₀` is the ONLY delivered bridge between the class
-- OUTER and class INNER readings (FOL.Absoluteness, `Single`).
-- =====================================================================
-- abs₀ : ∀ {n} {φ : Formula SM n} → Δ₀ φ → (δ : SM ^ n)
--      → (δ ⊨ᵐ φ) ≡ ((map fst δ) ⊨ᵛ φ)

-- =====================================================================
-- THE BLOCKER (the hole Agda reports is the ONLY open obligation of
-- this file, and it is UNFILLABLE).  The composition the miniature
-- asks for is:
--
--   ambient γ (mapFo emb (DefAt u w))
--     =[ ambientPushed≡outer ]  (map fst γ) ⊨ᵛ DefAt u w
--     =[ abs₀ (Δ₀-witness) δ ]  δ ⊨ᵐ DefAt u w
--     =[ DefAt-stage c oc ... ] fst (lookup u γ) ≡ 𝒟ₒ (Lset c)
--
-- The middle step needs `Δ₀ (CP.DefAt u w)`.  `DefAt` unfolds (Fact 1)
-- to `extAt u (∃̇(∃̇(DefBody w)))`, and `extAt` is `∀̇(...) ∧̇ ∀̇(...)`
-- (src/L/Coding/Model.lagda.md:662-663): two UNBOUNDED universals.
-- `Δ₀` (src/FOL/LevyHierarchy.lagda.md) has NO constructor for `∀̇`
-- or `∃̇` -- "absence is the classification".  So the witness does not
-- exist, and `abs₀` cannot be applied to `DefAt`.
-- =====================================================================
-- MEASURED ATTEMPT, run with the hole in place and recorded: the
-- single open obligation is
--
--   Δ₀-DefAt : ∀ {n} (u w : Fin n) → Δ₀ (CP.DefAt u w)
--   Δ₀-DefAt u w = {! !}
--
-- exit 1, error [UnsolvedInteractionMetas] at the hole, and NO other
-- error.  The goal type reduces (Fact 1) to Δ₀ of an `extAt`, i.e. of
-- `∀̇(...) ∧̇ ∀̇(...)`, and `Δ₀` has no constructor for `∀̇` or `∃̇`.
-- Unfillable.
