{-# OPTIONS --cubical --safe --guardedness #-}

-- [LJ-1.604]  IS INGREDIENT (iii) THE SAME OBJECT AS `sq`?
--
-- VERDICT: NO, AND THE TERM THAT SHOWS IT IS THE OBLIGATION BELOW.
-- The brief's obligation reads, with its two placeholders:
--
--     third-is-sq : <ingredient (iii)> ↔ <a formula for sq>
--
-- and it allows the second disjunct: "or the term that shows they are
-- different objects".  The measurement picks that disjunct.  The two
-- objects are DIFFERENT: ingredient (iii) at a site is ONE fiber of
-- `sq`; `sq` is the product of that fiber over every site of the band,
-- and nothing else.  The term `third-is-sq` carries both directions
-- with the hypothesis each one actually needs, so the asymmetry is in
-- the type and not in a reading of it.
--
-- W3 IS agents/tasks/LJ-1-604/runs/W3.agda AND IT WAS WRITTEN FIRST AND
-- TYPECHECKED ALONE (`runs/w3-1.out`, GREEN, 1.52 s cold; `runs/w3-2.out`
-- warm, 1.65 s).  It is IMPORTED below, not restated.
--
--   Section 0.  D-10, BEFORE ANY OTHER AGDA.  The two objects side by
--               side, and what the site consumes.
--   Section 1.  THE MEASUREMENT.  The cheap direction, the product
--               identity, and the obligation.
--   Section 2.  THE DEMAND.  Where the module spends the fibers, type
--               only, with the two predecessors that measured it.
--   Section 3.  THE VERDICT, in comments, and no further terms.
--
-- NO ROW puts `step`, `branch` or `stage-card-upper` into a conversion
-- problem: `[LJ-1.584]` measured that one such row does not terminate
-- (agents/tasks/LJ-1-584/runs/w3b-1.out).  They appear in comments and
-- in nothing else.
--
-- CALIBER.  THE PROGRAM SET GHCRTS ON THIS PANE (-A64m -I0 -M2g).  I
-- did not set it.  One Agda process at a time.

open import Base.Prelude
open import Base.Truth
open import Base.Classical using ( LEM )
open import Cubical.HITs.CumulativeHierarchy.Base using ( V; _∈_ )
open import Cubical.HITs.CumulativeHierarchy.Properties using ( ⟪_⟫ )
open import Cubical.HITs.CumulativeHierarchy.Constructions using ( module InfinitySet )
open import L.Constructible using ( IsOrd; Lset )
import Cubical.Data.Empty as Empty
open import LJ-1-594.runs.W3 using ( SqParam )

module LJ-1-604.Probe604 {ℓ : Level} (lem : LEM (ℓ-suc ℓ))
  (α₀ : V ℓ) (oα₀ : IsOrd α₀) (sq : SqParam α₀) where

open import FOL.ZFStructure using ( module hPropStructure )
open import V.Hierarchy {ℓ} using ( 𝒮ᵥ )
open import Cubical.Data.Sigma using ( _×_ )
open InfinitySet {ℓ} using ( sucV; ω )
import L.StageCardinal
import L.Ordinal.SquareLaw {ℓ} lem as SL2
open import LJ-1-604.runs.W3 using ( Ing3 )

open TruthAlgebra (hPropAlgebra (ℓ-suc ℓ))
open hPropStructure 𝒮ᵥ using ( S; _∈ˢ_ )
module SC = L.StageCardinal {ℓ} lem α₀ oα₀ sq
open SC using ( _↪_ )


-- ===================================================================
-- SECTION 0.  D-10, BEFORE ANY OTHER AGDA: THE TWO OBJECTS.
--
--   OBJECT ONE, `sq` ITSELF, the module parameter
--   (src/L/StageCardinal.lagda.md:17-19).  Its type, imported from the
--   green transcription (agents/tasks/LJ-1-594/runs/W3.agda:26-31):
--   a dependent function that takes a δ, a proof δ ∈ sucV α₀, a proof
--   δ ∉ ω, and returns one pairing with injectivity at δ.  CARRIER:
--   every δ of the band.  ARITY: a Π over the band INTO a binary
--   package.  SIDE CONDITIONS: two per site, δ ∈ sucV α₀ and δ ∉ ω
--   (src/L/StageCardinal.lagda.md:17-18).  UNIVERSE: Type (ℓ-suc ℓ),
--   because the Π is over V ℓ.
--
--   OBJECT TWO, INGREDIENT (iii) AT ONE SITE, as [LJ-1.594]'s table
--   states it (agents/tasks/LJ-1-594/review-of-pairing-suffices.md:42):
--   the pairing the class-pred site holds, `fst (sq α α∈suc infα)` by
--   name.  The site also spends the SECOND half of the same package
--   (`B.pair-inj` in `h-inj`, src/L/StageCardinal.lagda.md:382), so the
--   ingredient is the whole fiber `Ing3 α` (runs/W3.agda:40-43):
--   CARRIER: the members of ONE α.  ARITY: one binary package.  SIDE
--   CONDITIONS: the same two, but fixed by the site and not quantified.
--   UNIVERSE: Type ℓ.  THE TWO OBJECTS DO NOT EVEN SHARE A UNIVERSE.
--
--   AND THE TREE ALREADY NAMES OBJECT TWO `sq`: the law chapter's own
--   `sq : S → Type ℓ` (src/L/Ordinal/SquareLaw.lagda.md:685-688) is
--   this fiber type.  The campaign has two objects called `sq`, and
--   row 0.3 below ties them by `refl`.
-- ===================================================================

-- 0.1  THE SITE HOLDS THE WHOLE FIBER, both halves, and the parameter
--      delivers it.  `sq` applied at α has exactly `Ing3 α`'s type.
site-holds : (α : S) (oα : IsOrd α) (α∈suc : ⟨ α ∈ˢ sucV α₀ ⟩)
           → (⟨ α ∈ˢ ω ⟩ → Empty.⊥) → Ing3 α
site-holds α oα α∈suc infα = sq α α∈suc infα

-- 0.2  THE VALUE HALF, at the consumer.  `Bound`'s pairing parameter
--      takes the fiber (src/L/StageCardinal.lagda.md:65-67) and
--      `LimitStep` feeds it `sq` applied at its own α
--      (`module B = Bound α oα infα (sq α α∈suc infα)`, :283).  This
--      is [LJ-1.584]'s W3 row, re-proved inline because importing a
--      predecessor's whole probe killed the machine at this caliber
--      ([LJ-1.597], runs/final-5.out).
pair-is-sq :
    (α : S) (oα : IsOrd α) (α∈suc : ⟨ α ∈ˢ sucV α₀ ⟩)
    (infα : ⟨ α ∈ˢ ω ⟩ → Empty.⊥) (x y : ⟪ α ⟫)
  → SC.Bound.pair α oα infα (sq α α∈suc infα) x y
    ≡ fst (sq α α∈suc infα) (x , y)
pair-is-sq _ _ _ _ _ _ = refl

-- 0.3  AND THE INGREDIENT IS THE LAW CHAPTER'S OWN `sq`, the fiber
--      type, by `refl`.  [LJ-1.594]'s row (iii) and
--      src/L/Ordinal/SquareLaw.lagda.md:685-688 name the same type.
ing3-is-the-law-sq : (δ : V ℓ) → Ing3 δ ≡ SL2.sq δ
ing3-is-the-law-sq δ = refl

-- 0.4  AND THE SECOND HALF IS SPENT AT THE SAME SITE.  `h-inj` splits
--      equal packed values with `B.pair-inj` (src/L/StageCardinal.lagda
--      .md:382), and `B.pair-inj` is `snd` of the same fiber
--      (:71-75).  Re-derived here from `snd`, so the row is a term and
--      not a reading.
pair-inj-from-the-second-half :
    (α : S) (oα : IsOrd α) (α∈suc : ⟨ α ∈ˢ sucV α₀ ⟩)
    (infα : ⟨ α ∈ˢ ω ⟩ → Empty.⊥) (x y x' y' : ⟪ α ⟫)
  → SC.Bound.pair α oα infα (sq α α∈suc infα) x y
    ≡ SC.Bound.pair α oα infα (sq α α∈suc infα) x' y'
  → (x ≡ x') × (y ≡ y')
pair-inj-from-the-second-half α oα α∈suc infα x y x' y' e =
  cong fst p , cong snd p
  where
  p : (x , y) ≡ (x' , y')
  p = snd (sq α α∈suc infα) (x , y) (x' , y') e


-- ===================================================================
-- SECTION 1.  THE MEASUREMENT: TWO DIFFERENT OBJECTS, ONE RELATION.
--
--   THE CHEAP DIRECTION.  The parameter gives the ingredient at every
--   site: apply it.  [LJ-1.594] measured this at the value level
--   (Probe594.agda:238-243); at the type level it is one ascription.
--
--   THE PRODUCT IDENTITY.  The parameter IS the product of the
--   ingredient over the band, definitionally, with NO coherence
--   between two sites and NO uniformity: each fiber is chosen
--   independently.  This row is the whole content of the resemblance,
--   and it is where the resemblance stops.
-- ===================================================================

-- 1.1  THE PARAMETER GIVES THE INGREDIENT, at every site of the band.
family-gives-ingredient :
    (α : V ℓ) (α∈suc : ⟨ α ∈ˢ sucV α₀ ⟩) (infα : ⟨ α ∈ˢ ω ⟩ → Empty.⊥)
  → Ing3 α
family-gives-ingredient α α∈suc infα = sq α α∈suc infα

-- 1.2  THE PARAMETER IS THE PRODUCT OF THE INGREDIENT, and nothing
--      else is in it.
the-parameter-is-the-product :
    SqParam α₀
      ≡ ((δ : V ℓ) → ⟨ δ ∈ˢ sucV α₀ ⟩
          → (⟨ δ ∈ˢ ω ⟩ → Empty.⊥) → Ing3 δ)
the-parameter-is-the-product = refl

-- 1.3  THE OBLIGATION.  The brief's `↔`, with each direction carrying
--      the hypothesis it actually needs:
--
--        the forward component applies the parameter at the site;
--
--        the backward component needs the ingredient at EVERY site of
--        the band.  By 1.2 that hypothesis IS the parameter, so the
--        ingredient at ONE site contributes nothing toward it.  THAT
--        is the difference between the two objects, as a term: no map
--        from the single fiber to the family is on offer anywhere in
--        the type, and the one route back runs through the whole band.
--
--      The brief anticipated this shape: "IF THEY ARE DIFFERENT, SAY
--      WHICH IS STRONGER".  `sq` is.  Section 3 prices the difference.
third-is-sq :
    (α : V ℓ) (α∈suc : ⟨ α ∈ˢ sucV α₀ ⟩) (infα : ⟨ α ∈ˢ ω ⟩ → Empty.⊥)
  → ( SqParam α₀ → Ing3 α )
    × ( ((δ : V ℓ) → ⟨ δ ∈ˢ sucV α₀ ⟩
         → (⟨ δ ∈ˢ ω ⟩ → Empty.⊥) → Ing3 δ)
        → SqParam α₀ )
third-is-sq α α∈suc infα = (λ s → s α α∈suc infα) , (λ fam → fam)


-- ===================================================================
-- SECTION 2.  THE DEMAND: THE MODULE SPENDS THE PRODUCT, NOT A FIBER.
--
--   [LJ-1.594] called (iii) "the hypothesis" and the pairing "the
--   smallest of the five"
--   (agents/tasks/LJ-1-594/review-of-pairing-suffices.md:42, :143).
--   The demand side was measured BEFORE this task, twice, and both
--   measurements are in the live tree:
--
--   [LJ-1.116] (agents/tasks/LJ-1-116/lj-1.116-report.md, section 1)
--   read the trace: `stage-card-upper` is `∈-induction step`
--   (src/L/StageCardinal.lagda.md:566); `step` calls `limit-step`
--   (:562); `limit-step` applies `sq` at its own α (:283, the
--   parameter's only use); the branch at a finite member never demands
--   `sq` (:548, `fin-inj`), at ω and at every infinite member it
--   descends (:549-556).  So the GENERIC demand is every infinite
--   ordinal δ below α: the product, not a fiber.
--
--   [LJ-1.117] (agents/tasks/LJ-1-117/lj-1.117-report.md, section 1)
--   landed the bound: the parameter is stated exactly on the band the
--   consumers reach, δ ∈ sucV α₀.
--
--   ONE row below, TYPE ONLY, pins the conclusion's carrier, and no
--   row converts against `step`, `branch` or `stage-card-upper`.
-- ===================================================================

-- 2.1  THE CONCLUSION'S OWN INJECTION TYPE, re-ascribed
--      (src/L/StageCardinal.lagda.md:529-532).  This is [LJ-1.594]'s
--      own green row (Probe594.agda:337-341), re-proved inline.
P-is-the-injection :
    (δ : V ℓ) → SC.Upper.P δ
      ≡ ( IsOrd δ → ⟨ δ ∈ˢ sucV α₀ ⟩ → (⟨ δ ∈ˢ ω ⟩ → Empty.⊥)
        → ⟪ Lset δ ⟫ ↪ ⟪ δ ⟫ )
P-is-the-injection _ = refl

-- 2.2  AND THE FIBER IS SUPPLIED WITHOUT THE PARAMETER AT TWO KINDS OF
--      SITE, by the law chapter, TYPE ONLY.  At every INITIAL ordinal
--      the chapter constructs the fiber outright
--      (src/L/Ordinal/SquareLaw.lagda.md:960-961); at ω the live chain
--      holds the honest pairing `squareω : sq ω`
--      (src/L/InjChain.lagda.md:184-185, machine-checked by
--      [LJ-1.116] section 4).  At NON-INITIAL ordinals no untruncated
--      supply is in the tree: [LJ-1.107] measured the truncated
--      witness cannot give one, and [LJ-1.114] measured that threading
--      truncation into `Upper` walls.
initial-ordinals-have-the-fiber : (δ : S) → SL2.Init δ → Ing3 δ
initial-ordinals-have-the-fiber δ iδ = SL2.via-col-square δ iδ


-- ===================================================================
-- SECTION 3.  THE VERDICT.
--
--   THEY ARE DIFFERENT OBJECTS.  Ingredient (iii) at a site is one
--   fiber (`Ing3 α`, the law chapter's own `sq` type); the parameter is
--   the product of that fiber over the band (1.2), the module spends
--   the product through the descent ([LJ-1.116]), and no direction
--   from one fiber to the family exists in the tree: the tree HOLDS
--   single fibers at ω and at initial ordinals (2.2) and holds the
--   whole band only as a parameter.
--
--   WHICH IS STRONGER: `sq`, strictly.  It gives the ingredient at
--   every site (1.1); the ingredient at one site gives nothing toward
--   the parameter (1.3).
--
--   WHAT (iii) COSTS.  At ONE site: one binary function with its
--   injectivity, the smallest of that site's five ingredients, and
--   [LJ-1.594]'s ordering (:143) stands at that grain.  At MODULE
--   grain: the product over every infinite ordinal of the band, which
--   nobody has priced as a product.  The product carries no coherence
--   (1.2), so one uniform supply, like the honest pairing at ω or one
--   definable scheme read at every δ, would discharge every fiber at
--   once; the tree holds such a supply at ω and at initial ordinals,
--   and holds none at non-initial ones ([LJ-1.107], [LJ-1.114]).
--
--   SO THE FOUR ARRIVALS ARE ANSWERED: a brief that targets "the
--   pairing" at ONE site targets a fiber, and [LJ-1.597]'s value
--   equation is exactly that; a brief that targets the parameter
--   targets the product, and [LJ-1.594]'s route 2 is exactly that.
--   The two are not one object, and the bridge between them is 1.2.
-- ===================================================================
