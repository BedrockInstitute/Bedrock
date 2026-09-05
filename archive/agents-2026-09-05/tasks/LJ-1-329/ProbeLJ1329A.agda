{-# OPTIONS --cubical --safe --guardedness #-}

-- LJ-1.329 probe A.  It lands nothing.  It runs in agents/tasks/LJ-1-329/.
--
-- THE BRIEF ORDERS: take ONE ambient function the descent needs, and code it
-- as a member of an L-set.  The choice step refuted the order.  Consumer A
-- does not want ONE function coded.  It wants a TOTAL injective map on the
-- ambient type `sq α`, because that is what `pullOrder` takes.
--
-- PART 1 re-derives the shape consumer A demands, by reading `pullOrder`.
-- PART 2 builds an injection of the ambient decidable power set of the index
--        type into `sq α`, from ONE member of `sq α` and two distinct points.
-- PART 3 measures the consequence: the map consumer A asks for well-orders
--        the ambient power set, and then selects from every ambient property
--        of subsets.  That is a choice principle, not a coding problem.
-- PART 4 discharges the two points at the descent's own alpha.

open import Base.Prelude
open import Base.Truth
open import Base.Classical using ( LEM )

module LJ-1-329.ProbeLJ1329A {ℓ : Level} (lem : LEM (ℓ-suc ℓ)) where

open import FOL.ZFStructure using ( module hPropStructure )
open import V.Hierarchy {ℓ} using ( 𝒮ᵥ )
open import V.Presentation {ℓ} using ( fiber; ↪-inj )
open import V.Model {ℓ} using ( self∈sucV )
open import L.Constructible {ℓ} using ( 𝒮ʟ; IsOrd )
open import L.Ordinal.SquareLaw {ℓ} lem using ( sq )
open import L.Choice.Step {ℓ} lem using ( pullOrder )
open import L.WellOrder.Base {ℓₚ = ℓ-suc ℓ} using ( SWO; leastOf )

open import Cubical.HITs.CumulativeHierarchy.Base using ( V; _∈_ )
open import Cubical.HITs.CumulativeHierarchy.Properties using ( ⟪_⟫; ⟪_⟫↪; ∈∈ₛ )
open import Cubical.HITs.CumulativeHierarchy.Constructions
  using ( ∅; ∅-empty; module InfinitySet )
open InfinitySet {ℓ} using ( ω; sucV; #_; #-in-ω )
open import Cubical.Data.Bool using ( Bool; true; false )
open import Cubical.Data.Sigma using ( _×_ )
open import Cubical.Data.Unit using ( Unit; tt; isPropUnit )
import Cubical.Data.Empty as Empty
import Cubical.HITs.PropositionalTruncation as PT
open PT using ( ∥_∥₁; ∣_∣₁ )

open TruthAlgebra (hPropAlgebra (ℓ-suc ℓ))
open hPropStructure 𝒮ᵥ using ( _∈ˢ_ )

-- =====================================================================
-- PART 1.  THE SHAPE CONSUMER A DEMANDS, re-derived from `pullOrder`.
--
--   `pullOrder` (src/L/Choice/Step.lagda.md:236-258) takes `f : B → C`.
--   The parameter is a TOTAL function on `B`.  At consumer A's site
--   B is `sq α`, the ambient type of injective pairing functions
--   (src/L/Ordinal/SquareLaw.lagda.md:685-688).  So the obligation is a
--   map defined at EVERY ambient function, not a code for one of them.
--   `[LJ-1.321]` wrote the same term at Door.agda:415-418; it is
--   re-derived here so that this probe compiles the claim it acts on.
-- =====================================================================

code→order : (α : V ℓ) {ℓc : Level} (C : Type ℓc) (w : SWO {ℓc} C)
           → (c : sq α → C) → ((u v : sq α) → c u ≡ c v → u ≡ v)
           → SWO {ℓ} (sq α)
code→order α C w c cinj = pullOrder (sq α) C w c cinj

-- Split support from a well-order.  `[LJ-1.321]`, Door.agda:394-396.
Triv : {ℓa : Level} {A : Type ℓa} → A → hProp ℓ-zero
Triv _ = Unit , isPropUnit

least-elt : {A : Type ℓ} → SWO {ℓ} A → ∥ A ∥₁ → A
least-elt w h = fst (leastOf w lem Triv (PT.map (λ a → a , tt) h))

-- =====================================================================
-- PART 2.  THE AMBIENT POWER SET INJECTS INTO `sq α`.
--
--   Given ONE member of `sq α` and two distinct points of the index
--   type, every decidable subset of the index type names its own member
--   of `sq α`, and distinct subsets name distinct members.  The tag is
--   read back through the injectivity of the given function alone, so
--   nothing here needs the tower, the ordinal or a formula.
-- =====================================================================

module Encode (α : V ℓ) (a₀ a₁ : ⟪ α ⟫) (a≢ : a₀ ≡ a₁ → Empty.⊥) where

  Pow : Type ℓ
  Pow = ⟪ α ⟫ → Bool

  pick : Bool → ⟪ α ⟫
  pick false = a₀
  pick true  = a₁

  pick-inj : (b c : Bool) → pick b ≡ pick c → b ≡ c
  pick-inj false false _ = refl
  pick-inj false true  e = Empty.rec (a≢ e)
  pick-inj true  false e = Empty.rec (a≢ (sym e))
  pick-inj true  true  _ = refl

  module _ (s : sq α) where

    fn : ⟪ α ⟫ × ⟪ α ⟫ → ⟪ α ⟫
    fn = fst s

    fn-inj : (x y : ⟪ α ⟫ × ⟪ α ⟫) → fn x ≡ fn y → x ≡ y
    fn-inj = snd s

    -- The subset rides in the SECOND argument of the outer application.
    tag : Pow → ⟪ α ⟫ × ⟪ α ⟫ → ⟪ α ⟫
    tag S (x , y) = fn (fn (x , y) , pick (S x))

    tag-inj : (S : Pow) (u v : ⟪ α ⟫ × ⟪ α ⟫) → tag S u ≡ tag S v → u ≡ v
    tag-inj S (x , y) (x' , y') e =
      fn-inj (x , y) (x' , y') (cong fst (fn-inj _ _ e))

    enc : Pow → sq α
    enc S = tag S , tag-inj S

    enc-inj : (S T : Pow) → enc S ≡ enc T → S ≡ T
    enc-inj S T e = funExt step
      where
      step : (x : ⟪ α ⟫) → S x ≡ T x
      step x = pick-inj (S x) (T x)
        (cong snd (fn-inj _ _ (cong (λ h → h (x , x)) (cong fst e))))

-- =====================================================================
-- PART 3.  WHAT THE CROSSING WOULD BUY, MEASURED.
--
--   `crossing→powerWO` takes exactly what consumer A asks for, a
--   well-order on `sq α`, and returns a well-order on the ambient
--   decidable power set of the index type.  `powerChoice` then selects,
--   untruncated, from every ambient property of those subsets.
--   So the map consumer A wants is not a coding obligation.  It is an
--   ambient choice principle over a power set.
-- =====================================================================

crossing→powerWO : (α : V ℓ) (a₀ a₁ : ⟪ α ⟫) → (a₀ ≡ a₁ → Empty.⊥)
                 → ∥ sq α ∥₁ → SWO {ℓ} (sq α)
                 → SWO {ℓ} (⟪ α ⟫ → Bool)
crossing→powerWO α a₀ a₁ a≢ t w =
  pullOrder (⟪ α ⟫ → Bool) (sq α) w (E.enc s) (E.enc-inj s)
  where
  module E = Encode α a₀ a₁ a≢
  s : sq α
  s = least-elt w t

powerChoice : (α : V ℓ) → SWO {ℓ} (⟪ α ⟫ → Bool)
            → (P : (⟪ α ⟫ → Bool) → hProp (ℓ-suc ℓ))
            → ∥ Σ[ S ∈ (⟪ α ⟫ → Bool) ] ⟨ P S ⟩ ∥₁
            → Σ[ S ∈ (⟪ α ⟫ → Bool) ] ⟨ P S ⟩
powerChoice α w P h = fst got , fst (snd got)
  where
  got = leastOf w lem P h

-- The composite, at consumer A's own hypotheses.
crossing→powerChoice : (α : V ℓ) (a₀ a₁ : ⟪ α ⟫) → (a₀ ≡ a₁ → Empty.⊥)
                     → ∥ sq α ∥₁ → SWO {ℓ} (sq α)
                     → (P : (⟪ α ⟫ → Bool) → hProp (ℓ-suc ℓ))
                     → ∥ Σ[ S ∈ (⟪ α ⟫ → Bool) ] ⟨ P S ⟩ ∥₁
                     → Σ[ S ∈ (⟪ α ⟫ → Bool) ] ⟨ P S ⟩
crossing→powerChoice α a₀ a₁ a≢ t w =
  powerChoice α (crossing→powerWO α a₀ a₁ a≢ t w)

-- =====================================================================
-- PART 4.  THE TWO POINTS ARE FREE AT THE DESCENT'S OWN ALPHA.
--
--   The descent runs at infinite ordinals: `BoundedSubsetAt` excludes
--   omega and below (src/L/BoundedSubset.lagda.md:1388-1391), and
--   `Init`'s second row is `⟨ ω ∈ˢ α ⟩`
--   (src/L/Ordinal/SquareLaw.lagda.md:692).  So the empty set and its
--   successor are both members, and they are distinct.
-- =====================================================================

module Points (α : V ℓ) (oα : IsOrd α) (ω∈α : ⟨ ω ∈ˢ α ⟩) where

  ∅∈ω : ⟨ ∅ ∈ˢ ω ⟩
  ∅∈ω = ∈∈ₛ {a = ∅} {b = ω} .snd (#-in-ω 0)

  s∅∈ω : ⟨ sucV ∅ ∈ˢ ω ⟩
  s∅∈ω = ∈∈ₛ {a = sucV ∅} {b = ω} .snd (#-in-ω 1)

  ∅∈α : ⟨ ∅ ∈ˢ α ⟩
  ∅∈α = oα .fst ∅∈ω ω∈α

  s∅∈α : ⟨ sucV ∅ ∈ˢ α ⟩
  s∅∈α = oα .fst s∅∈ω ω∈α

  p₀ : ⟪ α ⟫
  p₀ = fst (fiber α {x = ∅} ∅∈α)

  p₁ : ⟪ α ⟫
  p₁ = fst (fiber α {x = sucV ∅} s∅∈α)

  p₀≢p₁ : p₀ ≡ p₁ → Empty.⊥
  p₀≢p₁ e = ∅-empty ∅
    (∈∈ₛ {a = ∅} {b = ∅} .fst
      (subst (λ w → ⟨ ∅ ∈ˢ w ⟩) (sym val) (self∈sucV ∅)))
    where
    val : ∅ ≡ sucV ∅
    val = sym (snd (fiber α {x = ∅} ∅∈α))
        ∙ cong ⟪ α ⟫↪ e
        ∙ snd (fiber α {x = sucV ∅} s∅∈α)

-- The statement with no point hypothesis left: at every infinite ordinal,
-- the well-order consumer A asks for selects from every ambient property
-- of subsets of the index type.
descent-crossing→choice
  : (α : V ℓ) → IsOrd α → ⟨ ω ∈ˢ α ⟩
  → ∥ sq α ∥₁ → SWO {ℓ} (sq α)
  → (P : (⟪ α ⟫ → Bool) → hProp (ℓ-suc ℓ))
  → ∥ Σ[ S ∈ (⟪ α ⟫ → Bool) ] ⟨ P S ⟩ ∥₁
  → Σ[ S ∈ (⟪ α ⟫ → Bool) ] ⟨ P S ⟩
descent-crossing→choice α oα ω∈α t w =
  crossing→powerChoice α Pt.p₀ Pt.p₁ Pt.p₀≢p₁ t w
  where
  module Pt = Points α oα ω∈α

-- =====================================================================
-- THE THREE NEGATIVE CONTROLS, and what each one named.
--
--   Each control was applied to this file, run, and reverted.  The
--   backups sit in the session scratchpad, outside the repository.
--
--   CONTROL 1.  `pick true = a₀`, so the two points collapse.  Agda
--   refused at line 93, the `pick-inj false true` clause, with
--   `[UnequalTerms] a₀ != a₁ ... when checking that the expression e has
--   type a₀ ≡ a₁`.  Exit 42.  So the encoding really consumes the
--   distinctness of the two points.
--
--   CONTROL 2.  `cong fst` became `cong snd` in `tag-inj`.  Agda refused
--   at line 111 with `[UnequalTerms] pick (S x) != fst s (x , y)`.
--   Exit 42.  So the readback really reads the composite value and not
--   the tag.
--
--   CONTROL 3, WHICH MEASURES.  The brief's premise written as a type:
--   ONE coded function, a POINT `c₀ : C` of the well-ordered carrier,
--   offered where `code→order` takes its map.  Agda refused with
--   `[UnequalTerms] C !=< (sq α → C) when checking that the expression
--   c₀ has type sq α → C`.  Exit 42.  THAT ERROR IS THE FINDING: the
--   obligation is a function out of `sq α`, and one code is a point.
-- =====================================================================
