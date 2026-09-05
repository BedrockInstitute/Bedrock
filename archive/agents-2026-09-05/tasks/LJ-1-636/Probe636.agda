{-# OPTIONS --cubical --safe --guardedness #-}

-- [LJ-1.636]  AT WHICH DELTA IS THE `sq` PARAMETER ACTUALLY APPLIED?
--
-- THE OBLIGATION.  `sq-demand`: for EACH application of
-- `L.StageCardinal`'s `sq` parameter in `src/`, a term naming the delta
-- it is applied at, and whether that delta is forced to be `ω`, forced
-- to be strictly above `ω`, or ranges over both.
--
-- THIS FILE CARRIES NO HOLE AND NO POSTULATE, so every line of it is a
-- measurement and not a claim.  Nothing lands in `src/`.  This MEASURES
-- A DEMAND; IT BUILDS NO SQUARE LAW.  Every `sq` below is a HYPOTHESIS.
-- The one inhabitant used, `squareω`, is already in the tree
-- (src/L/InjChain.lagda.md:184) and this file constructs no other.
--
-- ---------------------------------------------------------------------
-- THE CENSUS IS TWO SITES.  Re-derived here, not taken from the brief:
--
--   grep -rn '\bsq\b' src/ --include='*.lagda.md'
--
-- Unrelated names carrying the letters `sq`: `sq-lt`/`sq-lemma` in
-- src/FOL/Count.lagda.md:38-60, the bound variable at
-- src/L/Hierarchy.lagda.md:508, `sqκ` at
-- src/L/SquareLawClosed.lagda.md:317, and `squash₁` throughout.  The
-- `sq` of src/L/Ordinal/SquareLaw.lagda.md:685 is the square-law
-- PREDICATE, not this parameter.  What remains is:
--
--   BINDERS      src/L/StageCardinal.lagda.md:17     the parameter
--                src/L/BoundedSubset.lagda.md:1388   re-bound
--                src/L/BoundedSubset.lagda.md:1748   re-bound (BSA634)
--                src/L/StageBound.lagda.md:67        re-bound (SqFam)
--   FORWARDINGS  src/L/BoundedSubset.lagda.md:1397   handed to the module
--                src/L/BoundedSubset.lagda.md:1751   handed on
--                src/L/StageBound.lagda.md:75, :115  handed on
--   APPLICATIONS src/L/StageCardinal.lagda.md:293    SITE A, section 3
--                src/L/BoundedSubset.lagda.md:1526   SITE B, section 4
--
-- A forwarding applies no argument to `sq`, so it is not an application.
-- The count of APPLICATIONS is TWO, and the brief's premise 3 stands.
--
-- ---------------------------------------------------------------------
-- SHAPE NOTE.  ONE HEAP WALL OCCURRED AND WAS ROUTED AROUND IN THIS
-- DISPATCH.  The census row was first written as an Agda `record` whose
-- fields were `hyps`, `applies`, `verdict`, `evidence`.  It walled the
-- 2 GB caliber at runs/final-1.out and runs/final-2.out.  Bisection
-- (runs/bisect-*.out) put the wall on ONE FIELD: `applies`, whose type
-- quantifies over `SqParam`.  A record carrying the same content minus
-- that field is green in 1.15 s (runs/bisect-e.out); the field alone,
-- with only `hyps` beside it, walls (runs/bisect-f.out); and the SAME
-- four components as a nested `Σ` are green in 1.30 s
-- (runs/bisect-c.out).  Section 1 therefore uses the `Σ` encoding.
--
-- CALIBER.  The program set GHCRTS on this pane.  I did not set it.
-- One Agda process at a time.

open import Base.Prelude
open import Base.Truth
open import Base.Classical using ( LEM )

module LJ-1-636.Probe636 {ℓ : Level} (lem : LEM (ℓ-suc ℓ)) where

open import FOL.ZFStructure using ( module hPropStructure )
open import V.Hierarchy {ℓ} using ( 𝒮ᵥ; ∈-irrefl )
open import V.Model {ℓ} using ( self∈sucV; ∈sucV-inl; ∈sucV-elim )
open import L.Constructible {ℓ} using ( IsOrd; Lset )
open import L.Ordinal {ℓ} using ( ω-ord; suc-ord )
open import L.Ordinal.Linear {ℓ} lem using ( ord-tri )
open import L.InjChain {ℓ} lem using ( squareω )
open import L.BoundedSubset {ℓ} lem using ( IsCardinal )
open import L.CardinalAbove {ℓ} lem using ( cardAboveAt; module Hartogs )
import L.StageCardinal

open import Cubical.Data.Sigma using ( Σ-syntax; _×_ )
open import Cubical.Data.Sum using ( _⊎_; inl; inr )
import Cubical.Data.Empty as Empty
open import Cubical.HITs.CumulativeHierarchy.Base using ( setIsSet )
open import Cubical.HITs.CumulativeHierarchy.Constructions
  using ( module InfinitySet )
open InfinitySet using ( ω; sucV )
open import Cubical.HITs.CumulativeHierarchy.Properties using ( ⟪_⟫ )

open TruthAlgebra (hPropAlgebra (ℓ-suc ℓ))
open hPropStructure 𝒮ᵥ

-- =====================================================================
-- SECTION 0.  THE PARAMETER, COPIED FROM ITS BINDER.
-- =====================================================================

-- The value the parameter delivers at one delta.  This is the tail of
-- src/L/StageCardinal.lagda.md:18-20, verbatim up to binder names, and
-- it is also src/L/Ordinal/SquareLaw.lagda.md:685-687 verbatim.  The
-- next term is the proof of that second claim: it typechecks only
-- because the two are the same type.
Sq : S → Type ℓ
Sq δ = Σ[ f ∈ (⟪ δ ⟫ × ⟪ δ ⟫ → ⟪ δ ⟫) ]
         ((u v : ⟪ δ ⟫ × ⟪ δ ⟫) → f u ≡ f v → u ≡ v)

-- PREMISE 2 OF THE BRIEF, CHECKED.  `squareω` is untruncated and it
-- inhabits the parameter's value type AT ω, on the nose.
delivered-at-ω : Sq ω
delivered-at-ω = squareω

-- The parameter itself: src/L/StageCardinal.lagda.md:17-20.  Its own
-- clause EXCLUDES `δ ∈ ω` and ADMITS `δ ≡ ω`, so the parameter's DOMAIN
-- is both-sided before any site is looked at.  What this file settles is
-- where the two CALL SITES reach into that domain.
SqParam : S → Type (ℓ-suc ℓ)
SqParam α₀ = (δ : S) → ⟨ δ ∈ˢ sucV α₀ ⟩ → (⟨ δ ∈ˢ ω ⟩ → Empty.⊥) → Sq δ

-- The injection shape, definitionally src/L/StageCardinal.lagda.md:221.
Inj : Type ℓ → Type ℓ → Type ℓ
Inj A B = Σ[ f ∈ (A → B) ] ((x y : A) → f x ≡ f y → x ≡ y)

-- =====================================================================
-- SECTION 1.  WHAT A CENSUS ROW IS.
-- =====================================================================

-- A site's hypotheses on its own delta, as a family over the ambient
-- `α₀` at which `L.StageCardinal` is instantiated.
Hyp : Type (ℓ-suc (ℓ-suc ℓ))
Hyp = S → S → Type (ℓ-suc ℓ)

data Verdict : Type where
  only-ω           : Verdict
  strictly-above-ω : Verdict
  ranges-over-both : Verdict

Forces-ω : Hyp → Type (ℓ-suc ℓ)
Forces-ω H = (α₀ δ : S) → H α₀ δ → δ ≡ ω

Forces-above : Hyp → Type (ℓ-suc ℓ)
Forces-above H = (α₀ δ : S) → H α₀ δ → ⟨ ω ∈ˢ δ ⟩

Admits-ω : Hyp → Type (ℓ-suc ℓ)
Admits-ω H = Σ[ α₀ ∈ S ] (IsOrd α₀ × H α₀ ω)

Admits-above : Hyp → Type (ℓ-suc ℓ)
Admits-above H = Σ[ α₀ ∈ S ] Σ[ δ ∈ S ] (IsOrd α₀ × H α₀ δ × ⟨ ω ∈ˢ δ ⟩)

-- THE VERDICT IS NOT A TAG: its evidence type is computed from it, so a
-- row cannot carry a verdict it has not paid for.  `ranges-over-both`
-- costs two witnesses AND the refutation of the other two verdicts.
Evidence : Hyp → Verdict → Type (ℓ-suc ℓ)
Evidence H only-ω           = Forces-ω H
Evidence H strictly-above-ω = Forces-above H
Evidence H ranges-over-both =
  Admits-ω H × Admits-above H
  × ((Forces-ω H → Empty.⊥) × (Forces-above H → Empty.⊥))

-- THE TERM THAT NAMES THE DELTA: a site's own application of `sq`,
-- rebuilt from that site's hypotheses and nothing else.
Applies : Hyp → Type (ℓ-suc ℓ)
Applies H = (α₀ : S) → IsOrd α₀ → (sq : SqParam α₀)
          → (δ : S) → H α₀ δ → Sq δ

-- One census row.  A `record` here is what walled the heap; see the
-- shape note in the header.
Site : Type (ℓ-suc (ℓ-suc ℓ))
Site = Σ[ H ∈ Hyp ] (Applies H × (Σ[ v ∈ Verdict ] Evidence H v))

-- The two refutations, once, for every row that claims both sides.
no-force-ω : (H : Hyp) → Admits-above H → Forces-ω H → Empty.⊥
no-force-ω H (α₀ , δ , _ , h , ω∈δ) f =
  ∈-irrefl ω (subst (λ z → ⟨ ω ∈ˢ z ⟩) (f α₀ δ h) ω∈δ)

no-force-above : (H : Hyp) → Admits-ω H → Forces-above H → Empty.⊥
no-force-above H (α₀ , _ , h) f = ∈-irrefl ω (f α₀ ω h)

both : (H : Hyp) → Applies H → Admits-ω H → Admits-above H → Site
both H ap aω aa =
  H , ap , ranges-over-both
    , (aω , aa , no-force-ω H aa , no-force-above H aω)

-- =====================================================================
-- SECTION 2.  THE TWO ORDINALS THE WITNESSES USE.
-- =====================================================================

ω∉ω : ⟨ ω ∈ˢ ω ⟩ → Empty.⊥
ω∉ω = ∈-irrefl ω

sucVω-ord : IsOrd (sucV ω)
sucVω-ord = suc-ord ω-ord

ω∈sucVω : ⟨ ω ∈ˢ sucV ω ⟩
ω∈sucVω = self∈sucV ω

-- `sucV ω ∉ ω`: the shape of src/L/StageCardinal.lagda.md:569.
sucVω∉ω : ⟨ sucV ω ∈ˢ ω ⟩ → Empty.⊥
sucVω∉ω h = ∈-irrefl ω (ω-ord .fst ω∈sucVω h)

ω∈sucVsucVω : ⟨ ω ∈ˢ sucV (sucV ω) ⟩
ω∈sucVsucVω = ∈sucV-inl {A = sucV ω} {x = ω} ω∈sucVω

-- An ordinal above ω is never inside ω.
above-ω→∉ω : (a : S) → ⟨ ω ∈ˢ a ⟩ → ⟨ a ∈ˢ ω ⟩ → Empty.⊥
above-ω→∉ω a ω∈a h = ∈-irrefl ω (ω-ord .fst ω∈a h)

-- =====================================================================
-- SECTION 3.  SITE A.  src/L/StageCardinal.lagda.md:293
--
--   module LimitStep (α : S) (α∈suc : ⟨ α ∈ˢ sucV α₀ ⟩) (oα : IsOrd α)
--                    (infα : ⟨ α ∈ˢ ω ⟩ → Empty.⊥) ... where
--     module B = Bound α oα infα (sq α α∈suc infα)
--
-- THE DELTA IS `LimitStep`'s OWN `α`, and the application reads exactly
-- `α∈suc` and `infα`.  `LimitStep` is reached through `limit-step`
-- (:406-413), `Upper.step` (:571-572) and `Upper.stage-card-upper =
-- ∈-induction step` (:574-576).  So the site is NOT reached at one delta:
-- the ∈-induction reaches it at EVERY member of `H-A`, and `H-A` is
-- exactly `stage-card-upper`'s own telescope.
-- =====================================================================

H-A : Hyp
H-A α₀ δ = IsOrd δ × ⟨ δ ∈ˢ sucV α₀ ⟩ × (⟨ δ ∈ˢ ω ⟩ → Empty.⊥)

applies-A : Applies H-A
applies-A α₀ oα₀ sq δ (oδ , δ∈suc , infδ) = sq δ δ∈suc infδ

-- THE REACH, MEASURED AND NOT ARGUED.  `stage-card-upper` accepts every
-- member of `H-A` and asks for nothing more, so `H-A` is the site's
-- reachable set and not an approximation to it.
module AtFrame (α₀ : S) (oα₀ : IsOrd α₀) (sq : SqParam α₀) where

  module SC = L.StageCardinal {ℓ} lem α₀ oα₀ sq

  reach-A : (δ : S) → H-A α₀ δ → Inj ⟪ Lset δ ⟫ ⟪ δ ⟫
  reach-A δ (oδ , δ∈suc , infδ) = SC.Upper.stage-card-upper δ oδ δ∈suc infδ

  -- SITE B's application, rebuilt at this same frame.  See section 4.
  applies-B-here : (α₀∉ω : ⟨ α₀ ∈ˢ ω ⟩ → Empty.⊥) → Sq α₀
  applies-B-here α₀∉ω = sq α₀ (self∈sucV α₀) α₀∉ω

-- BOTH WITNESSES LIVE AT ONE AMBIENT `α₀ = sucV ω`, so the site is
-- reached at `ω` AND strictly above `ω` inside a SINGLE instantiation of
-- the chapter.  That is stronger than two separate frames would be.
A-admits-ω : Admits-ω H-A
A-admits-ω = sucV ω , sucVω-ord , (ω-ord , ω∈sucVsucVω , ω∉ω)

A-admits-above : Admits-above H-A
A-admits-above =
  sucV ω , sucV ω
  , sucVω-ord
  , (sucVω-ord , self∈sucV (sucV ω) , sucVω∉ω)
  , ω∈sucVω

site-A : Site
site-A = both H-A applies-A A-admits-ω A-admits-above

-- =====================================================================
-- SECTION 4.  SITE B.  src/L/BoundedSubset.lagda.md:1526
--
--   module SC = L.StageCardinal {ℓ} lem α ordα sq           (:1397)
--   ...
--   module B = SC.Bound α ordα α∉ω (sq α (self∈sucV α) α∉ω)  (:1526)
--
-- THE DELTA IS THE AMBIENT `α₀` ITSELF.  `SC` is instantiated at the
-- enclosing module's own `α` (:1397), so `α₀ ≡ α`, and the application
-- sits at `δ = α₀`, the TOP of the parameter's domain `sucV α₀`.
--
-- MEASURED: the application reads only `α∉ω`.  It reads neither `ordα`
-- nor any of `κ`, `ordκ`, `cardκ`, `κ∉ω`, `α∈κ`.  `H-B` is therefore the
-- site's own hypothesis set; section 5 pays the verdict AGAIN against
-- the enclosing telescope, so that dropping the cardinal side here costs
-- the census nothing.
-- =====================================================================

H-B : Hyp
H-B α₀ δ = (δ ≡ α₀) × (⟨ α₀ ∈ˢ ω ⟩ → Empty.⊥)

applies-B : Applies H-B
applies-B α₀ oα₀ sq δ (e , α₀∉ω) =
  subst Sq (sym e) (sq α₀ (self∈sucV α₀) α₀∉ω)

B-admits-ω : Admits-ω H-B
B-admits-ω = ω , ω-ord , (refl , ω∉ω)

B-admits-above : Admits-above H-B
B-admits-above = sucV ω , sucV ω , sucVω-ord , (refl , sucVω∉ω) , ω∈sucVω

site-B : Site
site-B = both H-B applies-B B-admits-ω B-admits-above

-- =====================================================================
-- SECTION 5.  SITE B AGAIN, AGAINST ITS ENCLOSING TELESCOPE.
--
-- `BoundedSubsetAt` (src/L/BoundedSubset.lagda.md:1385-1394) adds a
-- cardinal `κ` with `α ∈ κ` and `κ ∉ ω`.  The application at :1526 never
-- reads it, but a census that simply dropped it could be accused of
-- measuring a weaker site.  So the same verdict is paid again with the
-- cardinal side carried.
--
-- THE WITNESS IS UNTRUNCATED.  `cardAboveAt`
-- (src/L/CardinalAbove.lagda.md:205-208) is the untruncated half of
-- `ambientCardAbove`, and `Hartogs.μ` supplies its input without the
-- truncation that `noInjOrd` puts on it
-- (src/L/CardinalAbove.lagda.md:575-576).
-- =====================================================================

H-B-outer : Hyp
H-B-outer α₀ δ =
  (δ ≡ α₀) × (⟨ α₀ ∈ˢ ω ⟩ → Empty.⊥)
  × (Σ[ κ ∈ S ] (IsOrd κ × IsCardinal κ
                × (⟨ κ ∈ˢ ω ⟩ → Empty.⊥) × ⟨ α₀ ∈ˢ κ ⟩))

applies-B-outer : Applies H-B-outer
applies-B-outer α₀ oα₀ sq δ (e , α₀∉ω , _) =
  subst Sq (sym e) (sq α₀ (self∈sucV α₀) α₀∉ω)

-- A cardinal above any ordinal, untruncated.
card-above : (a : S) → IsOrd a
           → Σ[ θ ∈ S ] (IsOrd θ × IsCardinal θ × ⟨ a ∈ˢ θ ⟩)
card-above a oa =
  cardAboveAt a oa (Hartogs.μ a , Hartogs.μ-ord a , Hartogs.noInj a)

-- ONE cardinal serves both halves: it contains `sucV ω`, hence `ω`.
module TheCardinal where

  K : Σ[ θ ∈ S ] (IsOrd θ × IsCardinal θ × ⟨ sucV ω ∈ˢ θ ⟩)
  K = card-above (sucV ω) sucVω-ord

  κ : S
  κ = fst K

  ordκ : IsOrd κ
  ordκ = fst (snd K)

  cardκ : IsCardinal κ
  cardκ = fst (snd (snd K))

  sucVω∈κ : ⟨ sucV ω ∈ˢ κ ⟩
  sucVω∈κ = snd (snd (snd K))

  ω∈κ : ⟨ ω ∈ˢ κ ⟩
  ω∈κ = ordκ .fst ω∈sucVω sucVω∈κ

  κ∉ω : ⟨ κ ∈ˢ ω ⟩ → Empty.⊥
  κ∉ω = above-ω→∉ω κ ω∈κ

open TheCardinal using ( κ; ordκ; cardκ; κ∉ω; ω∈κ; sucVω∈κ )

B-outer-admits-ω : Admits-ω H-B-outer
B-outer-admits-ω =
  ω , ω-ord , (refl , ω∉ω , (κ , ordκ , cardκ , κ∉ω , ω∈κ))

B-outer-admits-above : Admits-above H-B-outer
B-outer-admits-above =
  sucV ω , sucV ω , sucVω-ord
  , (refl , sucVω∉ω , (κ , ordκ , cardκ , κ∉ω , sucVω∈κ))
  , ω∈sucVω

site-B-outer : Site
site-B-outer =
  both H-B-outer applies-B-outer B-outer-admits-ω B-outer-admits-above

-- The cardinal side never forces the delta above ω, WHATEVER the
-- cardinal: from the site's own hypotheses `ω ∈ κ` follows, so `α₀ = ω`
-- is always a legal choice.  This does not depend on the witness above.
cardinal-side-admits-ω : (κ' α : S) → IsOrd κ' → (⟨ κ' ∈ˢ ω ⟩ → Empty.⊥)
                       → ⟨ α ∈ˢ κ' ⟩ → (⟨ α ∈ˢ ω ⟩ → Empty.⊥)
                       → ⟨ ω ∈ˢ κ' ⟩
cardinal-side-admits-ω κ' α oκ' κ'∉ω α∈κ' α∉ω = go (ord-tri κ' oκ' ω ω-ord)
  where
  go : ⟨ κ' ∈ˢ ω ⟩ ⊎ ((κ' ≡ ω) ⊎ ⟨ ω ∈ˢ κ' ⟩) → ⟨ ω ∈ˢ κ' ⟩
  go (inl κ'∈ω)      = Empty.rec (κ'∉ω κ'∈ω)
  go (inr (inl e))   = Empty.rec (α∉ω (subst (λ z → ⟨ α ∈ˢ z ⟩) e α∈κ'))
  go (inr (inr h))   = h

-- =====================================================================
-- SECTION 6.  THE CONTROL.  WHAT DECIDES THE WHOLE DEMAND.
--
-- Both sites read the delta out of the SAME ambient `α₀`.  So the demand
-- is decided by one fact and no other: whether `α₀` is `ω`.
-- =====================================================================

-- AT AMBIENT `ω` THE DEMAND COLLAPSES TO A SINGLE POINT.  No ordinality
-- hypothesis is needed: `δ ∈ sucV ω` with `δ ∉ ω` already forces `δ ≡ ω`.
collapse-at-ω : (δ : S) → ⟨ δ ∈ˢ sucV ω ⟩ → (⟨ δ ∈ˢ ω ⟩ → Empty.⊥) → δ ≡ ω
collapse-at-ω δ δ∈sucVω infδ =
  ∈sucV-elim {A = ω} {x = δ} (setIsSet δ ω) δ∈sucVω
    (λ δ∈ω → Empty.rec (infδ δ∈ω))
    (λ e → e)

-- SITE A's verdict at ambient ω, in the census's own vocabulary.
A-at-ω-forces-ω : Forces-ω (λ α₀ δ → H-A ω δ)
A-at-ω-forces-ω α₀ δ (oδ , δ∈suc , infδ) = collapse-at-ω δ δ∈suc infδ

-- THE HEADLINE.  AT AMBIENT `α₀ = ω` THE PARAMETER IS ALREADY
-- DELIVERED, WHOLE, BY `squareω` ALONE.  Nothing is postulated, nothing
-- is truncated, and no square law is built here: `squareω` is the one
-- already in the tree at src/L/InjChain.lagda.md:184.
param-at-ω : SqParam ω
param-at-ω δ δ∈suc infδ = subst Sq (sym (collapse-at-ω δ δ∈suc infδ)) squareω

-- AND AS SOON AS `ω ∈ α₀` THE DEMAND REACHES STRICTLY ABOVE `ω`:
-- `α₀` is itself such a delta, at BOTH sites.
reaches-above : (α₀ : S) → IsOrd α₀ → ⟨ ω ∈ˢ α₀ ⟩
              → Σ[ δ ∈ S ] (H-A α₀ δ × H-B α₀ δ × ⟨ ω ∈ˢ δ ⟩)
reaches-above α₀ oα₀ ω∈α₀ =
  α₀
  , (oα₀ , self∈sucV α₀ , above-ω→∉ω α₀ ω∈α₀)
  , (refl , above-ω→∉ω α₀ ω∈α₀)
  , ω∈α₀

-- THE DICHOTOMY, IN ONE TERM.  Every ambient the chapter admits falls in
-- exactly one of the two cases above, so there is no third thing to
-- measure.
control : (α₀ : S) → IsOrd α₀ → (⟨ α₀ ∈ˢ ω ⟩ → Empty.⊥)
        → (α₀ ≡ ω)
        ⊎ (Σ[ δ ∈ S ] (H-A α₀ δ × H-B α₀ δ × ⟨ ω ∈ˢ δ ⟩))
control α₀ oα₀ α₀∉ω = go (ord-tri α₀ oα₀ ω ω-ord)
  where
  go : ⟨ α₀ ∈ˢ ω ⟩ ⊎ ((α₀ ≡ ω) ⊎ ⟨ ω ∈ˢ α₀ ⟩)
     → (α₀ ≡ ω) ⊎ (Σ[ δ ∈ S ] (H-A α₀ δ × H-B α₀ δ × ⟨ ω ∈ˢ δ ⟩))
  go (inl h)          = Empty.rec (α₀∉ω h)
  go (inr (inl e))    = inl e
  go (inr (inr ω∈α₀)) = inr (reaches-above α₀ oα₀ ω∈α₀)

-- =====================================================================
-- SECTION 7.  THE OBLIGATION.
-- =====================================================================

sq-demand :
    Σ[ A ∈ Site ] Σ[ B ∈ Site ] Σ[ B' ∈ Site ]
      ( SqParam ω
      × ((α₀ : S) → IsOrd α₀ → (⟨ α₀ ∈ˢ ω ⟩ → Empty.⊥)
         → (α₀ ≡ ω)
         ⊎ (Σ[ δ ∈ S ] (H-A α₀ δ × H-B α₀ δ × ⟨ ω ∈ˢ δ ⟩))) )
sq-demand = site-A , site-B , site-B-outer , param-at-ω , control

-- THE ANSWER, READ OFF `sq-demand`.
--
--   ROW 1  src/L/StageCardinal.lagda.md:293   RANGES OVER BOTH
--          delta = LimitStep's own α, universally quantified by the
--          ∈-induction at :574-576 over every ordinal in sucV α₀ outside ω.
--   ROW 2  src/L/BoundedSubset.lagda.md:1526  RANGES OVER BOTH
--          delta = the ambient α₀, which is BoundedSubsetAt's own α.
--   ROW 3  the same site with the cardinal side carried: unchanged.
--
-- NO SITE IS FORCED TO ω AND NO SITE IS FORCED ABOVE IT.  But the fourth
-- and fifth components sharpen that into the fact the campaign needs:
-- the demand has ONE control, the ambient α₀.  At α₀ ≡ ω the parameter
-- is wholly delivered by `squareω` (`param-at-ω`, no residue at all);
-- at ω ∈ α₀ both sites reach α₀ itself, strictly above ω.
