{-# OPTIONS --cubical --safe --guardedness #-}

-- LJ-1.365 probe A.  It lands nothing.  It runs in agents/tasks/LJ-1-365/.
--
-- THE BRIEF ASKS ONE QUESTION: does a `PT.rec` at the use site dissolve
-- the last untruncation?  `[LJ-1.301]` wrote, as an aside marked INFERRED
-- by its own author, that the GCH conclusion is itself truncated, so a
-- proof body that consumes the law under a propositional motive wraps in
-- ONE `PT.rec` over `∥ sq κ ∥₁` per use
-- (agents/tasks/LJ-1-301/lj-1.301-report.md:157-163).  Nobody has put
-- that sentence beside `[LJ-1.332]`'s blocker.
--
-- PART 1 restates the trophy's conclusion at kappa, re-derived from
--        src/L/GCH.lagda.md:59-69.  `[LJ-1.301]` cited `:85-87`; that
--        line range is stale, the file is 69 lines long.
-- PART 2 builds the top wrap at the real conclusion type.  GREEN.  The
--        outermost elimination is free, and that is a measurement, not a
--        formality: the same wrap one level down, at the body's first
--        data goal, is refused, and the controls file carries the
--        refusals.
-- PART 3 re-measures that the body needs the FAMILY below kappa and not
--        the point at kappa.  `[LJ-1.332]`'s one-liner, restated.
-- PART 4 re-derives the set preconditions C-54 leans on, at this file's
--        own hand.  `sq-set` matches `[LJ-1.319]`; `inj-set` is new.
-- PART 5 states the C-54 shape at the named goal.  GREEN.  A 2-Constant
--        map from the law to the injection is exactly what the set
--        eliminator demands at the goal the propositional eliminator
--        refuses.
-- PART 6 spells the truncated band, checks it against `[LJ-1.332]`'s
--        delivered term, and restates the delivered consumer
--        (`[LJ-1.337]` probe D) inside this file.
--
-- The refusals live in ProbeLJ1365C.agda.  EXPECTED RED.  Repair none.

open import Base.Prelude
open import Base.Truth
open import Base.Classical using ( LEM )

module LJ-1-365.ProbeLJ1365A {ℓ : Level} (lem : LEM (ℓ-suc ℓ)) where

open import FOL.ZFStructure using ( module hPropStructure )
open import V.Hierarchy {ℓ} using ( 𝒮ᵥ )
open import V.Model {ℓ} using ( self∈sucV )
open import L.Constructible {ℓ} using ( 𝒮ʟ; IsOrd; Lset )
open import L.Ordinal.SquareLaw {ℓ} lem using ( sq; Init )
open import L.Cardinal {ℓ} lem using ( _↪_; IsCardinalL )
open import L.GCH {ℓ} lem

open import LJ-1-332.ProbeLJ1332A {ℓ} lem using ( limit-truncated )
open import LJ-1-337.ProbeLJ1337A {ℓ} lem using ( Closed )
open import LJ-1-337.ProbeLJ1337B {ℓ} lem using ( SqBelow; LimitBand )
open import LJ-1-337.ProbeLJ1337D {ℓ} lem using ( stage-card-from-band )

open import Cubical.HITs.CumulativeHierarchy.Base using ( V; setIsSet )
open import Cubical.HITs.CumulativeHierarchy.Properties
  using ( ⟪_⟫; _∈ₛ_; presentation )
open import Cubical.HITs.CumulativeHierarchy.Constructions
  using ( module InfinitySet )
open InfinitySet {ℓ} using ( ω )
open import Cubical.Foundations.HLevels
  using ( isSetΣ; isSetΣSndProp; isSetΠ; isSet×; isPropΠ3
        ; isOfHLevelRespectEquiv )
open import Cubical.Foundations.Function using ( 2-Constant )
import Cubical.Data.Empty as Empty
import Cubical.HITs.PropositionalTruncation as PT
open PT using ( ∥_∥₁; squash₁ )

open TruthAlgebra (hPropAlgebra (ℓ-suc ℓ))
open hPropStructure 𝒮ᵥ using ( S; _∈ˢ_ )

-- =====================================================================
-- PART 1.  THE CONCLUSION AT KAPPA, re-derived (C-44).
--
--   `GCHStatement` is src/L/GCH.lagda.md:59-69.  The conclusion at kappa
--   is the truncated existential at :65-68.  It is a proposition by
--   construction, because it is a truncation, and `squash₁` is its
--   propositionality proof.  `[LJ-1.301]`'s citation `:85-87` pointed at
--   a restatement that no longer exists.
-- =====================================================================

Concl : (zf : ModelL.isZFModel) (κ : hPropStructure.S 𝒮ʟ)
      → IsOrd (fst κ) → IsCardinalL κ
      → (⟨ fst κ ∈ˢ ω ⟩ → Empty.⊥)
      → Type (ℓ-suc ℓ)
Concl zf κ oκ cκ κ∉ω =
  ∥ Σ[ δ ∈ hPropStructure.S 𝒮ʟ ]
       ( SuccCardL δ κ
       × InjL (𝒫 κ) δ
       × InjL δ (𝒫 κ) ) ∥₁
  where open ModelL.isZFModel zf using ( 𝒫 )

--   And the spelled type IS the statement's conclusion at κ, by machine:
--   the statement applies to it.  The application converts only if the
--   spelling matches src/L/GCH.lagda.md:60-69 line for line.
statement-fits : (zf : ModelL.isZFModel) (κ : hPropStructure.S 𝒮ʟ)
               → (oκ : IsOrd (fst κ)) (cκ : IsCardinalL κ)
               → (κ∉ω : ⟨ fst κ ∈ˢ ω ⟩ → Empty.⊥)
               → GCHStatement zf → Concl zf κ oκ cκ κ∉ω
statement-fits zf κ oκ cκ κ∉ω st = st κ oκ cκ κ∉ω

-- =====================================================================
-- PART 2.  THE TOP WRAP.  GREEN.
--
--   The brief's miniature, at the real goal type: given `∥ sq κ ∥₁`,
--   produce the trophy's conclusion at κ.  The body is a hypothesis,
--   because the GCH proof does not exist yet.  What is MEASURED here is
--   the eliminator's own side condition at the real conclusion: ONE
--   `PT.rec` over `∥ sq κ ∥₁` types, with `squash₁` as the motive's
--   proof, and nothing else is demanded at the outermost goal.
--
--   The measurement is not vacuous.  The same wrap at the body's first
--   data goal is refused by the machine, and Control 2 of
--   ProbeLJ1365C.agda carries the refusal with Agda's own type.
-- =====================================================================

wrap-top : (zf : ModelL.isZFModel) (κ : hPropStructure.S 𝒮ʟ)
         → (oκ : IsOrd (fst κ)) (cκ : IsCardinalL κ)
         → (κ∉ω : ⟨ fst κ ∈ˢ ω ⟩ → Empty.⊥)
         → (body : sq (fst κ) → Concl zf κ oκ cκ κ∉ω)
         → ∥ sq (fst κ) ∥₁ → Concl zf κ oκ cκ κ∉ω
wrap-top zf κ oκ cκ κ∉ω body = PT.rec squash₁ body

-- =====================================================================
-- PART 3.  THE BODY NEEDS THE FAMILY, NOT THE POINT.
--
--   `[LJ-1.332]` measured that `L.StageCardinal`'s parameter at a site
--   contains the site itself (`lead-hypothesis-is-goal`,
--   ProbeLJ1332A.agda:61-63).  Restated against `[LJ-1.337]`'s delivered
--   `SqBelow`: the family at `sucV α` already yields `sq α`.  So the
--   point at κ is ONE member of what the body consumes, and the members
--   below κ are not funded by it.  A per-use wrap at κ binds one stage;
--   the delivered consumer reads the law at every infinite member of the
--   stage above (`src/L/StageCardinal.lagda.md:17-19`, spent at `:283`).
-- =====================================================================

point-is-not-family : (α : S) → SqBelow α
                    → (⟨ α ∈ˢ ω ⟩ → Empty.⊥) → sq α
point-is-not-family α h = h α (self∈sucV α)

-- =====================================================================
-- PART 4.  THE SET PRECONDITIONS, re-derived at this file's own hand.
--
--   C-54 leans on `sq α` being a set.  `[LJ-1.319]` measured it green at
--   agents/tasks/LJ-1-319/SqIsSet.agda.  This file re-derives it rather
--   than importing it, so the precondition is re-measured under this
--   session.  `inj-set` is the same algebra one level up the chain, at
--   the injection the conclusion's truncation is witnessed with.
-- =====================================================================

carrier-set : (a : V ℓ) → isSet ⟪ a ⟫
carrier-set a = isOfHLevelRespectEquiv 2 (presentation a)
  (isSetΣSndProp setIsSet (λ v → snd (v ∈ₛ a)))

sq-set : (α : V ℓ) → isSet (sq α)
sq-set α = isSetΣ
  (isSetΠ (λ _ → carrier-set α))
  (λ f → isProp→isSet (isPropΠ3 (λ x y _ →
    isSet× (carrier-set α) (carrier-set α) x y)))

inj-set : (α : V ℓ) → isSet (⟪ Lset α ⟫ ↪ ⟪ α ⟫)
inj-set α = isSetΣ
  (isSetΠ (λ _ → carrier-set α))
  (λ f → isProp→isSet (isPropΠ3 (λ x y _ → carrier-set (Lset α) x y)))

-- =====================================================================
-- PART 5.  THE C-54 SHAPE AT THE NAMED GOAL.  GREEN.
--
--   The goal between the trophy's conclusion and the band is data, and
--   data of a SET.  So the library's set eliminator applies, and its
--   price is exact: a 2-Constant map from the law to the injection.  No
--   such map is built here and none is assumed.  The term states what
--   would have to exist for the wrap to go through at this goal.
-- =====================================================================

c54-at-injection : (α : V ℓ) (f : sq α → ⟪ Lset α ⟫ ↪ ⟪ α ⟫)
                 → 2-Constant f
                 → ∥ sq α ∥₁ → ⟪ Lset α ⟫ ↪ ⟪ α ⟫
c54-at-injection α f kf = PT.SetElim.rec→Set (inj-set α) f kf

-- =====================================================================
-- PART 6.  THE TRUNCATED BAND, AND THE DELIVERED CONSUMER.
--
--   `LimitBandT` is `[LJ-1.337]`'s `LimitBand` with the truncation put
--   back, which is `[LJ-1.332]`'s delivered `limit-truncated` conclusion
--   shape.  `bandT-from-332` checks that identity by machine: the
--   delivered term inhabits this spelled type.  `body-demand` restates
--   `[LJ-1.337]` probe D's consumer inside this file: the two delivered
--   legs compose only through the UNtruncated band.
--
--   Feeding `LimitBandT` to `body-demand` is refused.  Control 3 of
--   ProbeLJ1365C.agda carries the refusal.
-- =====================================================================

LimitBandT : Type (ℓ-suc ℓ)
LimitBandT = (δ : S) → IsOrd δ → ⟨ ω ∈ˢ δ ⟩ → Closed δ
           → (Init δ → Empty.⊥)
           → ((β : S) → ⟨ β ∈ˢ δ ⟩ → IsOrd β → ⟨ ω ∈ˢ β ⟩ → sq β)
           → ∥ sq δ ∥₁

bandT-from-332 : LimitBandT
bandT-from-332 δ oδ ω∈δ closed noInit ih =
  limit-truncated δ oδ ω∈δ closed noInit ih

body-demand : (α : S) (oα : IsOrd α) → LimitBand
            → (⟨ α ∈ˢ ω ⟩ → Empty.⊥) → ⟪ Lset α ⟫ ↪ ⟪ α ⟫
body-demand α oα = stage-card-from-band α oα
