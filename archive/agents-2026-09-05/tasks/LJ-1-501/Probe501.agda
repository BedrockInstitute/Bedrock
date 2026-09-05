{-# OPTIONS --cubical --safe --guardedness #-}

-- [LJ-1.501] The tag equation at the two extra indices t0 and t1.
--
-- W3 FIRST, and alone: does KValue's frame PROVE the layout at t0,
-- or must the frame take it as a hypothesis?  `Kenv` is a concrete
-- fourteen-slot list (Condensation.lagda.md:7387-7391) and
-- `KValue.facts` writes `tagEq0 = refl` at :7412, so the question is
-- whether the six-fold shift that [LJ-1.495] measured
-- (agents/tasks/LJ-1-495/Probe495.agda:166-199, GO) survives it.
--
-- Telescope is KValue's own, taken from Probe495.agda:84-91.
-- Do not import a probe.  Do not build a TFacts value.
--
-- ONE Agda process per run, GHCRTS="-A64m -I0 -M8g", the wide
-- caliber, set on the pane by the program and untouched here.
-- Nothing lands in src/.

open import Base.Prelude
open import Base.Truth
open import Base.Classical using ( LEM )

module LJ-1-501.Probe501 {ℓ : Level} (lem : LEM (ℓ-suc ℓ)) where

open import FOL.ZFStructure using ( module hPropStructure )
open import L.Constructible {ℓ} using ( 𝒮ʟ; IsOrd )
open import L.Axioms.Numerals {ℓ} using ( numeralL )
open import L.Coding.Model {ℓ} using ( prʟ )
open import L.Condensation {ℓ} lem
  using ( module KValue; module KFactsNS )
open import Cubical.Data.Nat using ( _+_ )
open import Cubical.HITs.CumulativeHierarchy.Base using ( V; _∈_ )
open import Cubical.HITs.CumulativeHierarchy.Constructions
  using ( module InfinitySet; ∅ )
open InfinitySet {ℓ} using ( sucV )

open TruthAlgebra (hPropAlgebra (ℓ-suc ℓ))
open hPropStructure 𝒮ʟ
open KFactsNS
open KFacts

-- =====================================================================
-- W3.  THE LAYOUT AT t0, at KValue's frame, with NO hypothesis.
--
-- If this `refl` forms, the layout at t0 is a THEOREM here and not a
-- hypothesis the record must carry.  If it does not, the finding is
-- that `TFacts` needs a layout hypothesis at every frame.
-- =====================================================================

module W3
  (lam : V ℓ) (ordλ : IsOrd lam)
  (succλ : (d : V ℓ) → ⟨ d ∈ lam ⟩ → ⟨ sucV d ∈ lam ⟩)
  (∅∈λ : ⟨ ∅ ∈ lam ⟩)
  (gam : V ℓ) (ordγ : IsOrd gam) (γ∈λ : ⟨ gam ∈ lam ⟩) where

  open KValue lam ordλ succλ ∅∈λ gam ordγ γ∈λ

  layout-at-t0 : (c1 c2 c3 c4 c5 c6 : S)
               → fst (lookup (suc (suc (suc (suc (suc (suc i0))))))
                        (c6 ∷ c5 ∷ c4 ∷ c3 ∷ c2 ∷ c1 ∷ Kenv))
                 ≡ fst (numeralL 0)
  layout-at-t0 c1 c2 c3 c4 c5 c6 = refl

layout-at-t0 = W3.layout-at-t0

-- =====================================================================
-- W2.  THE OBLIGATION, ONCE, AT A GENERIC CARRIER.
--
-- `TFacts` looks its slots up at `suc^6 t` over `Vec S (11 + n)`
-- while `t : Fin (5 + n)` (TwelveAgree.lagda.md:129-131).  Six sucs
-- through six conses is the six-fold shift [LJ-1.495] measured, and
-- `6 + (5 + n)` and `11 + n` are the same normal form, so the two
-- lengths meet with nothing to transport.
--
-- The hypothesis is what the frame gives about the layout, stated at
-- the SHORT environment: the slot the frame chose holds the numeral.
-- That is exactly the shape `KFacts.tagEqk` delivers
-- (Condensation.lagda.md:6079-6091), so a frame discharges it from a
-- delivered field and never from a new hypothesis.
--
-- It is generic in the tag `k` and generic in the index `t`, so ONE
-- term serves `tagEq0` to `tagEq11`, `t0eq` and `t1eq` alike (DD4).
-- =====================================================================

tagEq-at-t : {n : ℕ} (k : ℕ) (t : Fin (5 + n)) (γ : Vec S (5 + n))
             (c1 c2 c3 c4 c5 c6 : S)
           → fst (lookup t γ) ≡ fst (numeralL k)
           → fst (lookup (suc (suc (suc (suc (suc (suc t))))))
                    (c6 ∷ c5 ∷ c4 ∷ c3 ∷ c2 ∷ c1 ∷ γ))
             ≡ fst (numeralL k)
tagEq-at-t k t γ c1 c2 c3 c4 c5 c6 h = h

-- The transport [LJ-1.113] MEASURED but never built
-- (agents/tasks/LJ-1-113/lj-1.113-report.md:128-131): a tag equation
-- plus the delivered numeral membership gives the membership at the
-- slot.  Generic in the tag, the slot and the key index.
tagK-from-tagEq : {m : ℕ} (k : ℕ) (t K' : Fin m) (γ : Vec S m)
                → fst (lookup t γ) ≡ fst (numeralL k)
                → ⟨ fst (numeralL k) ∈ fst (lookup K' γ) ⟩
                → ⟨ fst (lookup t γ) ∈ fst (lookup K' γ) ⟩
tagK-from-tagEq k t K' γ eq mem =
  subst (λ v → ⟨ v ∈ fst (lookup K' γ) ⟩) (sym eq) mem

-- =====================================================================
-- THE FREE FIELD, DECIDED BY THE ELABORATOR AND NOT BY READING.
--
-- `TFacts.num1K` (TwelveAgree.lagda.md:185) and `TFacts.numK1`
-- (:146) are transcribed here SEPARATELY, each from its own line, at
-- `TFacts`'s own parameter shape.  If the two transcriptions are not
-- the same type, `num1K-is-numK1` fails to typecheck and the claim
-- that the field is free is refuted.  It is the identity or it is
-- nothing.
-- =====================================================================

NumK1Type : {n : ℕ} (K : Fin (5 + n)) (γ' : Vec S (11 + n)) → Type (ℓ-suc ℓ)
NumK1Type K γ' =
  ⟨ fst (numeralL 1) ∈ fst (lookup (suc (suc (suc (suc (suc (suc K)))))) γ') ⟩

Num1KType : {n : ℕ} (K : Fin (5 + n)) (γ' : Vec S (11 + n)) → Type (ℓ-suc ℓ)
Num1KType K γ' =
  ⟨ fst (numeralL 1) ∈ fst (lookup (suc (suc (suc (suc (suc (suc K)))))) γ') ⟩

num1K-is-numK1 : {n : ℕ} (K : Fin (5 + n)) (γ' : Vec S (11 + n))
               → NumK1Type K γ' → Num1KType K γ'
num1K-is-numK1 K γ' x = x

-- =====================================================================
-- THE FOUR FIELDS, AT KValue'S FRAME.
--
-- `t0` and `t1` are PARAMETERS of `TFacts`, exactly as `N0` to `N11`
-- are, and the record proves none of the twelve: `tagEq0` to
-- `tagEq11` are FIELDS (TwelveAgree.lagda.md:132-143).  So the record
-- fixes no layout.  The FRAME fixes it, and this is the frame
-- [LJ-1.495] landed on: `TFacts` at `n = 9`, indices `Fin 14`,
-- environment `S ^ 20` (Probe495.agda:169-170).
--
-- The frame chooses `t0 := i0` and `t1 := i1`.  Nothing forced that
-- choice and nothing forbids another one; see the report.
-- =====================================================================

module AtKValue
  (lam : V ℓ) (ordλ : IsOrd lam)
  (succλ : (d : V ℓ) → ⟨ d ∈ lam ⟩ → ⟨ sucV d ∈ lam ⟩)
  (∅∈λ : ⟨ ∅ ∈ lam ⟩)
  (gam : V ℓ) (ordγ : IsOrd gam) (γ∈λ : ⟨ gam ∈ lam ⟩) where

  open KValue lam ordλ succλ ∅∈λ gam ordγ γ∈λ

  -- FIELD 1.  `t0eq` at TwelveAgree.lagda.md:181, from the delivered
  -- `KFacts.tagEq0` through the generic obligation.
  t0eq : (c1 c2 c3 c4 c5 c6 : S)
       → KFacts iA iK i0 i1 i2 i3 i4 i5 i6 i7 i8 i9 i10 i11 Kenv
       → fst (lookup (suc (suc (suc (suc (suc (suc i0))))))
                (c6 ∷ c5 ∷ c4 ∷ c3 ∷ c2 ∷ c1 ∷ Kenv))
         ≡ fst (numeralL 0)
  t0eq c1 c2 c3 c4 c5 c6 f =
    tagEq-at-t {n = 9} 0 i0 Kenv c1 c2 c3 c4 c5 c6 (f .tagEq0)

  -- FIELD 2.  `t1eq` at TwelveAgree.lagda.md:182.  The SAME term at
  -- the next tag: this is what "generic in the tag" buys.
  t1eq : (c1 c2 c3 c4 c5 c6 : S)
       → KFacts iA iK i0 i1 i2 i3 i4 i5 i6 i7 i8 i9 i10 i11 Kenv
       → fst (lookup (suc (suc (suc (suc (suc (suc i1))))))
                (c6 ∷ c5 ∷ c4 ∷ c3 ∷ c2 ∷ c1 ∷ Kenv))
         ≡ fst (numeralL 1)
  t1eq c1 c2 c3 c4 c5 c6 f =
    tagEq-at-t {n = 9} 1 i1 Kenv c1 c2 c3 c4 c5 c6 (f .tagEq1)

  -- FIELD 3.  `t0K` at TwelveAgree.lagda.md:183-184, the transport
  -- [LJ-1.113] measured, over `t0eq` and the delivered `numK0`.
  t0K : (c1 c2 c3 c4 c5 c6 : S)
      → KFacts iA iK i0 i1 i2 i3 i4 i5 i6 i7 i8 i9 i10 i11 Kenv
      → ⟨ fst (lookup (suc (suc (suc (suc (suc (suc i0))))))
                 (c6 ∷ c5 ∷ c4 ∷ c3 ∷ c2 ∷ c1 ∷ Kenv))
          ∈ fst (lookup (suc (suc (suc (suc (suc (suc iK))))))
                   (c6 ∷ c5 ∷ c4 ∷ c3 ∷ c2 ∷ c1 ∷ Kenv)) ⟩
  t0K c1 c2 c3 c4 c5 c6 f =
    tagK-from-tagEq 0
      (suc (suc (suc (suc (suc (suc i0))))))
      (suc (suc (suc (suc (suc (suc iK))))))
      (c6 ∷ c5 ∷ c4 ∷ c3 ∷ c2 ∷ c1 ∷ Kenv)
      (t0eq c1 c2 c3 c4 c5 c6 f)
      (f .numK0)

  -- FIELD 4.  `num1K` at TwelveAgree.lagda.md:185.  Its type is
  -- `numK1`'s type at :146, character for character, so the field is
  -- the identity on the delivered one.  Nothing is proved here.
  num1K : (c1 c2 c3 c4 c5 c6 : S)
        → ⟨ fst (numeralL 1)
            ∈ fst (lookup (suc (suc (suc (suc (suc (suc iK))))))
                     (c6 ∷ c5 ∷ c4 ∷ c3 ∷ c2 ∷ c1 ∷ Kenv)) ⟩
        → ⟨ fst (numeralL 1)
            ∈ fst (lookup (suc (suc (suc (suc (suc (suc iK))))))
                     (c6 ∷ c5 ∷ c4 ∷ c3 ∷ c2 ∷ c1 ∷ Kenv)) ⟩
  num1K c1 c2 c3 c4 c5 c6 numK1' = numK1'

t0eq = AtKValue.t0eq
t1eq = AtKValue.t1eq
t0K = AtKValue.t0K
num1K = AtKValue.num1K
