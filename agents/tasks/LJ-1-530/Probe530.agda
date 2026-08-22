{-# OPTIONS --cubical --safe --guardedness #-}

-- [LJ-1.530] PROBE.  `dK`: the definable powerset of a recorded value
-- is a member of `K`.  It runs in agents/tasks/LJ-1-530/ and lands
-- nothing in src/.
--
--   W3, FIRST      runs/W3.agda, typechecked before this file existed.
--                  The brief's form is written there as a TYPE and is
--                  NOT inhabited; the corrected form, the same statement
--                  with the member a STAGE, IS inhabited and is what the
--                  obligation consumes.
--   DELIVERED      dK, the briefed obligation, at the frame the site
--                  supplies: K a limit level, and the value table
--                  correct below its own bound.
--   ALSO           zK, four lines on top of dK, because [LJ-1.527]
--                  reported that reduction without measuring it
--                  (agents/tasks/LJ-1-527/lj-1.527-report.md:196-198).
--
-- WHY THE FRAME IS NOT THE BRIEF'S.  The brief's frame gives `w` as an
-- arbitrary member of `K`.  Nothing in the tree puts the definable
-- powerset of an arbitrary member of a level back in that level; the
-- ONLY statement src/ makes about a level and a definable powerset is
-- `Lset-suc` (src/L/Axioms/Basic.lagda.md:196), which is about a STAGE.
-- The site supplies exactly that missing word: `Values`
-- (src/L/Hierarchy.lagda.md:117-119) says a value recorded at an
-- argument below the bound IS the tower there.  This is not a
-- weakening of the obligation: the conclusion is the briefed one, and
-- `Values` is the same hypothesis src/ already spends to discharge
-- `dK`'s `isL` sibling `PowOK` (src/L/Hierarchy.lagda.md:167-170).
--
-- ONE Agda process per run, GHCRTS="-A64m -I0 -M8g", the wide caliber,
-- set on the pane by the program and untouched here.

open import Base.Prelude
open import Base.Truth
open import Base.Classical using ( LEM )

module LJ-1-530.Probe530 {ℓ : Level} (lem : LEM (ℓ-suc ℓ)) where

open import FOL.Syntax using ( ⊤̇ )
open import FOL.ZFStructure using ( module hPropStructure )
import FOL.Absoluteness
open import V.Hierarchy {ℓ} using ( 𝒮ᵥ )
open import V.Coding {ℓ} using ( pr )
open import L.Definability {ℓ} using ( module DefOf )
open import L.Constructible {ℓ}
  using ( 𝒮ʟ; isL; isL-trans; IsOrd; Lset; 𝒟ₒ; 𝒟ₒ-intro; Lset-in
        ; Lset-layer; layer-trans )
open import L.Axioms.Basic {ℓ} using ( Lset-suc )
open import L.Ordinal {ℓ} using ( ω-ord )
open import L.Ordinal.Stages {ℓ} lem using ( ord∈Lset→∈ )
open import L.Hierarchy {ℓ} lem using ( Values; Domain )

open import Cubical.Data.FinData using ( Fin )
open import Cubical.Data.Vec using ( lookup )
open import Cubical.HITs.CumulativeHierarchy.Base using ( V; _∈_ )
open import Cubical.HITs.CumulativeHierarchy.Constructions
  using ( ∅; module InfinitySet )
open InfinitySet using ( sucV; ω; ω-empty; ω-next )
open import Cubical.HITs.CumulativeHierarchy.Properties using ( ∈∈ₛ )
import Cubical.HITs.PropositionalTruncation as PT
open PT using ( ∣_∣₁ )

open TruthAlgebra (hPropAlgebra (ℓ-suc ℓ))
open hPropStructure 𝒮ʟ

module AbsL = FOL.Absoluteness.Single 𝒮ᵥ isL isL-trans
open AbsL using ( _^_ )

-- ---------------------------------------------------------------------
-- SECTION 1.  THE LIMIT LEVEL, AND W3 RESTATED SO THE OBLIGATION CAN
-- CONSUME IT.  Both lines are runs/W3.agda's, which typechecked alone
-- before this file existed.
-- ---------------------------------------------------------------------

-- Verbatim from [LJ-1.522] (agents/tasks/LJ-1-522/Probe522.agda:75-79).
-- A limit is said of the INDEX and never of the stage.
IsLimit : V ℓ → Type (ℓ-suc ℓ)
IsLimit α = IsOrd α
          × ⟨ ∅ ∈ α ⟩
          × ((β : V ℓ) → ⟨ β ∈ α ⟩ → ⟨ sucV β ∈ α ⟩)

-- NOT VACUOUS.  ω is a limit level, so the obligation's antecedent is
-- inhabited and `dK` is not true by an empty hypothesis.  Verbatim from
-- [LJ-1.522] (agents/tasks/LJ-1-522/Probe522.agda:116-121).
ω-IsLimit : IsLimit ω
ω-IsLimit =
    ω-ord
  , ( ∈∈ₛ {a = ∅} {b = ω} .snd ω-empty
    , (λ β β∈ω → ∈∈ₛ {a = sucV β} {b = ω} .snd
        (ω-next β (∈∈ₛ {a = β} {b = ω} .fst β∈ω))) )

-- A stage is a member of its own definable powerset: the formula "true"
-- selects everyone.  `isL-Lset`'s first line
-- (src/L/Axioms/Basic.lagda.md:157-158) with the `isL` wrapper dropped,
-- because what this task needs is the BOUND and not constructibility.
stage∈𝒟ₒ : (β : V ℓ) → ⟨ Lset β ∈ 𝒟ₒ (Lset β) ⟩
stage∈𝒟ₒ β = 𝒟ₒ-intro (Lset β) (Lset β)
  ∣ ⊤̇ , DefOf.defSet⊤≡A (Lset β) ∣₁

-- THE CORRECTED W3.  A limit level holds the definable powerset of
-- every STAGE below it.  Successor closure is the whole of the limit
-- that is spent: neither ordinality nor `∅ ∈ α` is used here.
stage-dpow-in-level : (α : V ℓ) → IsLimit α → (δ : V ℓ) → ⟨ δ ∈ α ⟩
                    → ⟨ 𝒟ₒ (Lset δ) ∈ Lset α ⟩
stage-dpow-in-level α (_ , (_ , sc)) δ δ∈α =
  subst (λ u → ⟨ u ∈ Lset α ⟩) (Lset-suc δ)
    (Lset-in α (sucV δ) (Lset (sucV δ)) (sc δ δ∈α) (stage∈𝒟ₒ (sucV δ)))

-- ---------------------------------------------------------------------
-- SECTION 2.  THE OBLIGATION.
--
-- `dK`, the second of the three memberships rows three and four want
-- (agents/tasks/LJ-1-304/ProbeLJ1304A.agda:178-179), with the frame the
-- site supplies.  The conclusion is the briefed one, character for
-- character.  The hypotheses are five, and every one of them is a
-- delivered src/ type:
--
--   qK     the level identification, [LJ-1.525]'s row-one hypothesis
--          (agents/tasks/LJ-1-525/Probe525.agda), also [LJ-1.522]'s
--          (agents/tasks/LJ-1-522/Probe522.agda:359)
--   oB     the domain bound is an ordinal, as in
--          src/L/Hierarchy.lagda.md:167
--   B∈K    the domain bound lies in K, the frame's own vocabulary
--          (`carrierK`, src/L/Condensation.lagda.md:7424)
--   dom    Domain, src/L/Hierarchy.lagda.md:124-125
--   vals   Values, src/L/Hierarchy.lagda.md:117-119
--
-- NOTHING IS POSTULATED AND NOTHING IS WEAKENED TO THE SUBSET FORM.
-- ---------------------------------------------------------------------
dK : (α : V ℓ) → IsLimit α
   → ∀ {n} (b f K : Fin n) (γ : S ^ n)
   → fst (lookup K γ) ≡ Lset α
   → IsOrd (fst (lookup b γ))
   → ⟨ fst (lookup b γ) ∈ fst (lookup K γ) ⟩
   → Domain (lookup f γ) (fst (lookup b γ))
   → Values (lookup f γ) (fst (lookup b γ))
   → (c w : S) → ⟨ pr (fst c) (fst w) ∈ fst (lookup f γ) ⟩
   → ⟨ 𝒟ₒ (fst w) ∈ fst (lookup K γ) ⟩
dK α lim b f K γ qK oB B∈K dom vals c w hd =
  subst (λ u → ⟨ 𝒟ₒ (fst w) ∈ u ⟩) (sym qK)
    (subst (λ u → ⟨ 𝒟ₒ u ∈ Lset α ⟩) (sym (vals c w c∈B hd))
      (stage-dpow-in-level α lim (fst c) c∈α))
  where
  B : V ℓ
  B = fst (lookup b γ)

  c∈B : ⟨ fst c ∈ B ⟩
  c∈B = dom c w hd

  B∈α : ⟨ B ∈ α ⟩
  B∈α = ord∈Lset→∈ α (lim .fst) B oB
          (subst (λ u → ⟨ B ∈ u ⟩) qK B∈K)

  c∈α : ⟨ fst c ∈ α ⟩
  c∈α = lim .fst .fst c∈B B∈α

-- ---------------------------------------------------------------------
-- SECTION 3.  zK, WHICH [LJ-1.527] REPORTED AS A REDUCTION AND DID NOT
-- MEASURE.
--
-- Row four's own membership
-- (agents/tasks/LJ-1-304/ProbeLJ1304A.agda:180-182).  [LJ-1.527] said
-- it is `dK` plus the transitivity of a level, which src/ delivers as
-- `layer-trans (Lset-layer α)` (src/L/Constructible.lagda.md:183,
-- :246).  This is that sentence, typechecked.  It buys no hypothesis
-- that `dK` did not already buy.
-- ---------------------------------------------------------------------
zK : (α : V ℓ) → IsLimit α
   → ∀ {n} (b f K : Fin n) (γ : S ^ n)
   → fst (lookup K γ) ≡ Lset α
   → IsOrd (fst (lookup b γ))
   → ⟨ fst (lookup b γ) ∈ fst (lookup K γ) ⟩
   → Domain (lookup f γ) (fst (lookup b γ))
   → Values (lookup f γ) (fst (lookup b γ))
   → (c w x : S) → ⟨ pr (fst c) (fst w) ∈ fst (lookup f γ) ⟩
   → ⟨ fst x ∈ 𝒟ₒ (fst w) ⟩
   → ⟨ fst x ∈ fst (lookup K γ) ⟩
zK α lim b f K γ qK oB B∈K dom vals c w x hd hx =
  subst (λ u → ⟨ fst x ∈ u ⟩) (sym qK)
    (layer-trans (Lset-layer α) hx
      (subst (λ u → ⟨ 𝒟ₒ (fst w) ∈ u ⟩) qK
        (dK α lim b f K γ qK oB B∈K dom vals c w hd)))

-- ---------------------------------------------------------------------
-- SECTION 4.  THE BRIEFED SHAPE, AND dK INHABITS IT.
--
-- `DKShape` is the obligation's conclusion in [LJ-1.304]'s own words
-- (agents/tasks/LJ-1-304/ProbeLJ1304A.agda:178-179), with `SC` read as
-- `S`.  The line below it is `dK` and nothing else, so the frame
-- hypotheses are the ONLY difference between what the brief asked for
-- and what this file delivers.  If that line ever stops checking, the
-- obligation has drifted.
-- ---------------------------------------------------------------------
DKShape : ∀ {n} → Fin n → Fin n → S ^ n → Type (ℓ-suc ℓ)
DKShape f K γ = (c w : S) → ⟨ pr (fst c) (fst w) ∈ fst (lookup f γ) ⟩
              → ⟨ 𝒟ₒ (fst w) ∈ fst (lookup K γ) ⟩

dK-briefed : (α : V ℓ) → IsLimit α
           → ∀ {n} (b f K : Fin n) (γ : S ^ n)
           → fst (lookup K γ) ≡ Lset α
           → IsOrd (fst (lookup b γ))
           → ⟨ fst (lookup b γ) ∈ fst (lookup K γ) ⟩
           → Domain (lookup f γ) (fst (lookup b γ))
           → Values (lookup f γ) (fst (lookup b γ))
           → DKShape f K γ
dK-briefed = dK

-- ---------------------------------------------------------------------
-- SECTION 5.  WHAT THE SAME FRAME PAYS FOR FREE.
--
-- The brief says `wK` IS DELIVERED, because `entryK` returns both
-- components of a pair in `K` (src/L/Condensation.lagda.md:6615-6616).
-- THAT IS TRUE OF THE TYPE AND NOT OF A TERM: [LJ-1.527] measured that
-- `entryK` is a HYPOTHESIS in src/ and that nothing proves it
-- (agents/tasks/LJ-1-527/lj-1.527-report.md:181).  So `wK` is owed too,
-- and this section pays it, because the frame `dK` already needed pays
-- it in two lines.
--
-- `domK` is cheaper still and needs neither `Values` nor `Domain`: a
-- level is transitive.
--
-- NONE OF THIS IS A ROW.  Rows three to five are built at
-- agents/tasks/LJ-1-304/ProbeLJ1304A.agda:254-258 and :313-316 and are
-- NOT re-derived here.  These are the memberships those rows consume.
-- ---------------------------------------------------------------------

-- Every member of a slot that lies in a level lies in that level.
-- `domK`, src/L/Condensation.lagda.md:6617.
domK : (α : V ℓ) → ∀ {n} (d K : Fin n) (γ : S ^ n)
     → fst (lookup K γ) ≡ Lset α
     → ⟨ fst (lookup d γ) ∈ fst (lookup K γ) ⟩
     → (x : S) → ⟨ fst x ∈ fst (lookup d γ) ⟩
     → ⟨ fst x ∈ fst (lookup K γ) ⟩
domK α d K γ qK D∈K x x∈D =
  subst (λ u → ⟨ fst x ∈ u ⟩) (sym qK)
    (layer-trans (Lset-layer α) x∈D
      (subst (λ u → ⟨ fst (lookup d γ) ∈ u ⟩) qK D∈K))

-- The recorded value lies in K.  `wK`,
-- agents/tasks/LJ-1-304/ProbeLJ1304A.agda:176-177.  It is `dK` one
-- successor lower: `dK` needs `sucV c ∈ α` and this needs only `c ∈ α`.
wK : (α : V ℓ) → IsLimit α
   → ∀ {n} (b f K : Fin n) (γ : S ^ n)
   → fst (lookup K γ) ≡ Lset α
   → IsOrd (fst (lookup b γ))
   → ⟨ fst (lookup b γ) ∈ fst (lookup K γ) ⟩
   → Domain (lookup f γ) (fst (lookup b γ))
   → Values (lookup f γ) (fst (lookup b γ))
   → (c w : S) → ⟨ pr (fst c) (fst w) ∈ fst (lookup f γ) ⟩
   → ⟨ fst w ∈ fst (lookup K γ) ⟩
wK α lim b f K γ qK oB B∈K dom vals c w hd =
  subst (λ u → ⟨ fst w ∈ u ⟩) (sym qK)
    (subst (λ u → ⟨ u ∈ Lset α ⟩) (sym (vals c w c∈B hd))
      (Lset-in α (fst c) (Lset (fst c)) c∈α (stage∈𝒟ₒ (fst c))))
  where
  B : V ℓ
  B = fst (lookup b γ)

  c∈B : ⟨ fst c ∈ B ⟩
  c∈B = dom c w hd

  B∈α : ⟨ B ∈ α ⟩
  B∈α = ord∈Lset→∈ α (lim .fst) B oB
          (subst (λ u → ⟨ B ∈ u ⟩) qK B∈K)

  c∈α : ⟨ fst c ∈ α ⟩
  c∈α = lim .fst .fst c∈B B∈α

-- Both components of a recorded pair lie in K.  `entryK`,
-- src/L/Condensation.lagda.md:6615-6616, which src/ states and does not
-- prove.  The argument half is the level's transitivity; the value half
-- is `wK`.
entryK : (α : V ℓ) → IsLimit α
       → ∀ {n} (b f K : Fin n) (γ : S ^ n)
       → fst (lookup K γ) ≡ Lset α
       → IsOrd (fst (lookup b γ))
       → ⟨ fst (lookup b γ) ∈ fst (lookup K γ) ⟩
       → Domain (lookup f γ) (fst (lookup b γ))
       → Values (lookup f γ) (fst (lookup b γ))
       → (c w : S) → ⟨ pr (fst c) (fst w) ∈ fst (lookup f γ) ⟩
       → ⟨ fst c ∈ fst (lookup K γ) ⟩ × ⟨ fst w ∈ fst (lookup K γ) ⟩
entryK α lim b f K γ qK oB B∈K dom vals c w hd =
    domK α b K γ qK B∈K c (dom c w hd)
  , wK α lim b f K γ qK oB B∈K dom vals c w hd
