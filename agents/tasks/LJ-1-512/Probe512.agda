{-# OPTIONS --cubical --safe --guardedness #-}

-- [LJ-1.512] IS THE HONEST FORM THE RECORD'S FIELD PLUS ONE HYPOTHESIS?
--
-- ONE obligation, `honest-covers-record`: EnvSupply's delivered
-- `consK-exist`, at `KValue`'s frame, GIVES the `TFacts` field at that
-- frame under the hypothesis the honest form itself takes.
--
-- The census that this file's report carries is READING, not Agda.  The
-- only Agda here is the one correspondence and the two certificates that
-- fix its two endpoints to the tree.
--
-- ONE Agda process per run, GHCRTS="-A64m -I0 -M8g", the wide caliber,
-- set on the pane by the program and untouched here.  Nothing lands in
-- src/.  No postulate.  No `TFacts` field proves a `TFacts` field.

open import Base.Prelude
open import Base.Truth
open import Base.Classical using ( LEM )

module LJ-1-512.Probe512 {ℓ : Level} (lem : LEM (ℓ-suc ℓ)) where

open import FOL.ZFStructure using ( module hPropStructure )
import FOL.Absoluteness
open import V.Hierarchy {ℓ} using ( 𝒮ᵥ )
open import L.Constructible {ℓ} using ( 𝒮ʟ; isL; isL-trans )
open import L.Constructible {ℓ} using ( IsOrd; isTransV )
open import L.Condensation {ℓ} lem using ( module KValue; module KFactsNS )
open import L.Condensation.TwelveAgree {ℓ} lem using ( TFacts )
open import FOL.Syntax using ( var; _∈̇_; _∧̇_ )
open import L.Coding.Model {ℓ} using ( consAtL )
open import L.Coding.Environment {ℓ} using ( env; cons )
open import L.Coding.EnvSupply {ℓ} lem using ( module Fact )
open import Cubical.Data.Nat using ( _+_ )
open import Cubical.HITs.CumulativeHierarchy.Base using ( V; _∈_ )
open import Cubical.HITs.CumulativeHierarchy.Constructions
  using ( module InfinitySet; ∅ )
open InfinitySet {ℓ} using ( sucV )

open TruthAlgebra (hPropAlgebra (ℓ-suc ℓ))
open hPropStructure 𝒮ʟ

module AbsL = FOL.Absoluteness.Single 𝒮ᵥ isL isL-trans
open AbsL renaming ( _⊨ᵐ_ to _⊨_ )
open KFactsNS
open KFacts

-- =====================================================================
-- ENDPOINT ONE: THE RECORD'S FIELD, VERBATIM.
--
-- `TFacts.consK-exist` (src/L/Condensation/TwelveAgree.lagda.md:317-321)
-- at `TFacts`'s own generic shape, `K : Fin (5 + n)` over
-- `γ' : S ^ (11 + n)` (:130-131).  `ConsKExist⁺` is that type with the
-- one hypothesis the honest form takes restored.  `[LJ-1.510]` measured
-- that the bare form is FALSE at this frame
-- (agents/tasks/LJ-1-510/Probe510.agda:395-405) and its report returns
-- GO on exactly this repair (agents/tasks/LJ-1-510/lj-1.510-report.md
-- :15).  I take the TYPE from that probe and the VERDICT from that
-- report, and I do not re-derive either.
-- =====================================================================

ConsKExist : {n : ℕ} (K : Fin (5 + n)) (γ' : S ^ (11 + n)) → Type (ℓ-suc ℓ)
ConsKExist {n} K γ' =
    (ya yc a ar c E z x e' : S)
  → ⟨ (e' ∷ x ∷ z ∷ E ∷ ya ∷ yc ∷ a ∷ ar ∷ c ∷ γ') ⊨
        consAtL {9 + (11 + n)} zero (suc zero) (suc (suc zero))
        ∧̇ (var zero ∈̇ var (suc (suc (suc (suc zero))))) ⟩
  → ⟨ fst e' ∈ fst (lookup (suc (suc (suc (suc (suc (suc (suc (suc (suc (suc (suc (suc (suc (suc K))))))))))))))
                     (x ∷ z ∷ E ∷ ya ∷ yc ∷ a ∷ ar ∷ c ∷ γ')) ⟩

ConsKExist⁺ : {n : ℕ} (K : Fin (5 + n)) (γ' : S ^ (11 + n)) → Type (ℓ-suc ℓ)
ConsKExist⁺ {n} K γ' =
    (ya yc a ar c E z x e' : S)
  → ⟨ fst ya ∈ fst (lookup (suc (suc (suc (suc (suc (suc K)))))) γ') ⟩
  → ⟨ (e' ∷ x ∷ z ∷ E ∷ ya ∷ yc ∷ a ∷ ar ∷ c ∷ γ') ⊨
        consAtL {9 + (11 + n)} zero (suc zero) (suc (suc zero))
        ∧̇ (var zero ∈̇ var (suc (suc (suc (suc zero))))) ⟩
  → ⟨ fst e' ∈ fst (lookup (suc (suc (suc (suc (suc (suc (suc (suc (suc (suc (suc (suc (suc (suc K))))))))))))))
                     (x ∷ z ∷ E ∷ ya ∷ yc ∷ a ∷ ar ∷ c ∷ γ')) ⟩

-- `ConsKExist` IS the record's field type, and Agda says so: the term
-- reads the field at that type with no coercion and no `subst`.  It
-- certifies the STATEMENT only.  `honest-covers-record` never calls it.
record-field-matches : {n : ℕ}
    (N0 N1 N2 N3 N4 N5 N6 N7 N8 N9 N10 N11 t0 t1 K : Fin (5 + n))
    (γ' : S ^ (11 + n))
  → TFacts N0 N1 N2 N3 N4 N5 N6 N7 N8 N9 N10 N11 t0 t1 K γ'
  → ConsKExist {n} K γ'
record-field-matches N0 N1 N2 N3 N4 N5 N6 N7 N8 N9 N10 N11 t0 t1 K γ' tf =
  TFacts.consK-exist tf

-- =====================================================================
-- ENDPOINT TWO: THE HONEST FORM, VERBATIM.
--
-- `Fact.ConsK.consK-exist` (src/L/Coding/EnvSupply.lagda.md:661-668, and
-- the same three lines again at :742-749 inside `ConsKClosed`).  Two
-- things to see in this type, and the second is the finding:
--
--   1. it takes `⟨ fst ya ∈ fst K ⟩`, which the record's field does not;
--   2. ITS TAIL IS FIXED AT `Vec S 2`, where the record's is
--      `S ^ (11 + n)`.  So the honest form is NOT an instance of the
--      record's field and the record's field is not an instance of it.
--      They meet only after the coercion measured below.
--
-- `envConsK` is `ConsK`'s own module parameter, so it is a bound
-- variable here and nothing is postulated.  `consK-exist` does not use
-- it; `consK-forall` and `consK-allin` do.
-- =====================================================================

EnvConsK : (K : S) → Type (ℓ-suc ℓ)
EnvConsK K = {k : ℕ} (g : Fin k → V ℓ) (x : V ℓ)
           → ⟨ env g ∈ fst K ⟩ → ⟨ x ∈ fst K ⟩
           → ⟨ env (cons x g) ∈ fst K ⟩

HonestConsKExist : (K : S) → Type (ℓ-suc ℓ)
HonestConsKExist K =
    (γ₂ : S ^ 2) (ya yc a ar c E z x e' : S)
  → ⟨ fst ya ∈ fst K ⟩
  → ⟨ (e' ∷ x ∷ z ∷ E ∷ ya ∷ yc ∷ a ∷ ar ∷ c ∷ γ₂) ⊨
        consAtL {9 + 2} zero (suc zero) (suc (suc zero))
        ∧̇ (var zero ∈̇ var (suc (suc (suc (suc zero))))) ⟩
  → ⟨ fst e' ∈ fst K ⟩

honest-type-matches : (K : S) (Ktr : isTransV (fst K))
                    → EnvConsK K → HonestConsKExist K
honest-type-matches K Ktr envConsK = Fact.ConsK.consK-exist K Ktr envConsK

-- =====================================================================
-- THE ONE THING THAT SEPARATES THE TWO TYPES, AND IT IS FREE.
--
-- The honest form reads a NINE cell prefix over a TWO cell tail; the
-- record's field reads the same nine cells over an `11 + n` cell tail.
-- `consAtL zero (suc zero) (suc (suc zero))` and the atom
-- `var zero ∈̇ var (suc (suc (suc (suc zero))))` read cells 0, 1, 2 and
-- 4 only, all of them in the shared prefix, so the two satisfactions are
-- THE SAME PROPOSITION and the identity function is the coercion.  No
-- `consAtL-transport` (src/L/Coding/Model.lagda.md:1499-1510) is needed,
-- and that lemma's `g` with `fst z ≡ env g`, which this field is never
-- given, is therefore not a cost.
--
-- This is the same arithmetic `[LJ-1.510]` measured for the CONCLUSION
-- (`depth-is-free`, agents/tasks/LJ-1-510/Probe510.agda:130-135), read
-- at the HYPOTHESIS instead.  I re-measured it at this site rather than
-- transferring it (AGENTS.md:45).
-- =====================================================================

tail-is-free : {n : ℕ} (γ₂ : S ^ 2) (γ' : S ^ (11 + n))
               (ya yc a ar c E z x e' : S)
  → ⟨ (e' ∷ x ∷ z ∷ E ∷ ya ∷ yc ∷ a ∷ ar ∷ c ∷ γ') ⊨
        consAtL {9 + (11 + n)} zero (suc zero) (suc (suc zero))
        ∧̇ (var zero ∈̇ var (suc (suc (suc (suc zero))))) ⟩
  → ⟨ (e' ∷ x ∷ z ∷ E ∷ ya ∷ yc ∷ a ∷ ar ∷ c ∷ γ₂) ⊨
        consAtL {9 + 2} zero (suc zero) (suc (suc zero))
        ∧̇ (var zero ∈̇ var (suc (suc (suc (suc zero))))) ⟩
tail-is-free γ₂ γ' ya yc a ar c E z x e' h = h

-- =====================================================================
-- THE CORRESPONDENCE, AT THE GENERIC FRAME (W2).
--
-- Written ONCE at `TFacts`'s own shape and instantiated below at
-- `KValue`'s frame, so the fixed form is never the statement's home.
-- =====================================================================

covers-gen : {n : ℕ} (K : Fin (5 + n)) (γ' : S ^ (11 + n)) (γ₂ : S ^ 2)
           → HonestConsKExist (lookup (suc (suc (suc (suc (suc (suc K)))))) γ')
           → ConsKExist⁺ {n} K γ'
covers-gen K γ' γ₂ honest ya yc a ar c E z x e' yaK h =
  honest γ₂ ya yc a ar c E z x e' yaK
    (tail-is-free γ₂ γ' ya yc a ar c E z x e' h)

-- =====================================================================
-- THE OBLIGATION, AT `KValue`'s FRAME.
--
-- `KValue` (src/L/Condensation.lagda.md:7380-7395) supplies `Kenv : S ^ 14`
-- (:7389) and one `KFacts` value, `facts` (:7411).  Six cons cells put it
-- at `TFacts`'s lengths, the frame `[LJ-1.495]` measured and `[LJ-1.510]`
-- reused (agents/tasks/LJ-1-510/Probe510.agda:271-280): `S ^ 20` is
-- `S ^ (11 + 9)` and `Fin 14` is `Fin (5 + 9)`, with the bound at `iK`.
--
-- The honest form's `γ₂` is instantiated at the frame's OWN two slots,
-- the carrier and the bound, because that is what EnvSupply's `Vec S 2`
-- tail means: every `Fact` member reads its `K` at `lookup (suc zero) γ'`
-- (src/L/Coding/EnvSupply.lagda.md:497-498).
-- =====================================================================

module Frame
  (lam : V ℓ) (ordλ : IsOrd lam)
  (succλ : (d : V ℓ) → ⟨ d ∈ lam ⟩ → ⟨ sucV d ∈ lam ⟩)
  (∅∈λ : ⟨ ∅ ∈ lam ⟩)
  (gam : V ℓ) (ordγ : IsOrd gam) (γ∈λ : ⟨ gam ∈ lam ⟩) where

  open KValue lam ordλ succλ ∅∈λ gam ordγ γ∈λ

  frame₂ : S ^ 2
  frame₂ = lookup iA Kenv ∷ lookup iK Kenv ∷ []

  honest-covers-record :
      (c1 c2 c3 c4 c5 c6 : S)
    → HonestConsKExist (lookup iK Kenv)
    → ConsKExist⁺ {9} iK (c6 ∷ c5 ∷ c4 ∷ c3 ∷ c2 ∷ c1 ∷ Kenv)
  honest-covers-record c1 c2 c3 c4 c5 c6 honest =
    covers-gen {9} iK (c6 ∷ c5 ∷ c4 ∷ c3 ∷ c2 ∷ c1 ∷ Kenv) frame₂ honest

honest-covers-record = Frame.honest-covers-record
