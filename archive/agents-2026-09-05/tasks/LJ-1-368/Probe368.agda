{-# OPTIONS --cubical --safe --guardedness #-}

-- LJ-1.368 probe.  DD25 adversarial review of `[LJ-1.365]`.  It lands
-- nothing.  It runs in agents/tasks/LJ-1-368/.
--
-- `[LJ-1.365]` returned SET-MOTIVE: the top `PT.rec` types, the body
-- cannot exist, because the chain from the trophy's conclusion to the
-- band crosses a SET goal.  Its central control is SoloC2.agda:24-27,
-- exit 42, where `PT.rec squash₁` is refused at the goal
-- `⟪ Lset α ⟫ ↪ ⟪ α ⟫`.
--
-- THIS FILE MEASURES THREE THINGS THE TARGET DID NOT MEASURE.
--
-- PART 1  The conclusion at kappa, spelled again by hand, and the
--         pinning check.  MustFail368C.agda is the control that the
--         pinning is real.
-- PART 2  `squash₁` is refused at a motive that IS a proposition and is
--         not a truncation, and the SAME motive goes green with its own
--         `isProp`.  So an exit 42 on `PT.rec squash₁ ...` measures the
--         choice of `squash₁` and never the goal's h-level.
--         MustFail368A.agda is the red half.
-- PART 3  ONE `PT.rec` carries the whole delivered chain, THROUGH the
--         set-typed injection `⟪ Lset α ⟫ ↪ ⟪ α ⟫`, into the trophy's
--         own conclusion.  So a set-typed intermediate does not block a
--         wrap whose final motive is propositional.
-- PART 4  Where the elimination site really is: at `sq δ`, under the
--         Pi of the band, not at the injection.  The C-54 obligation is
--         a weakly constant endomap of `sq δ`.
-- PART 5  The only missing step, stated: the truncation must commute
--         with the band's Pi.  Given that ONE step, the trophy's
--         conclusion follows with one `PT.rec` and no untruncation.

open import Base.Prelude
open import Base.Truth
open import Base.Classical using ( LEM )

module LJ-1-368.Probe368 {ℓ : Level} (lem : LEM (ℓ-suc ℓ)) where

open import FOL.ZFStructure using ( module hPropStructure )
open import V.Hierarchy {ℓ} using ( 𝒮ᵥ )
open import L.Constructible {ℓ} using ( 𝒮ʟ; IsOrd; Lset )
open import L.Ordinal.SquareLaw {ℓ} lem using ( sq; Init )
open import L.Cardinal {ℓ} lem using ( _↪_; IsCardinalL )
open import L.GCH {ℓ} lem

open import LJ-1-337.ProbeLJ1337A {ℓ} lem using ( Closed )
open import LJ-1-337.ProbeLJ1337B {ℓ} lem using ( LimitBand; SqBelow )
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
-- PART 1.  THE CONCLUSION AT KAPPA, spelled again, and the pinning.
--
--   src/L/GCH.lagda.md:65-68 is the conclusion; :59-69 is the whole
--   statement.  `statement-fits` applies the delivered statement to the
--   hand spelling.  The application converts only if the spelling is
--   right.  MustFail368C.agda offers a WRONG spelling to the same
--   application and must be refused; without that control this term
--   proves nothing about pinning.
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

statement-fits : (zf : ModelL.isZFModel) (κ : hPropStructure.S 𝒮ʟ)
               → (oκ : IsOrd (fst κ)) (cκ : IsCardinalL κ)
               → (κ∉ω : ⟨ fst κ ∈ˢ ω ⟩ → Empty.⊥)
               → GCHStatement zf → Concl zf κ oκ cκ κ∉ω
statement-fits zf κ oκ cκ κ∉ω st = st κ oκ cκ κ∉ω

-- =====================================================================
-- PART 2.  WHAT `squash₁` MEASURES, AND WHAT IT DOES NOT.
--
--   `squash₁ : (x y : ∥ A ∥₁) → x ≡ y`
--   (Cubical/HITs/PropositionalTruncation/Base.agda).  So
--   `PT.rec squash₁` demands that the MOTIVE unify with `∥ _ ∥₁`.  A
--   motive that is a proposition, but is not literally a truncation,
--   is refused too.
--
--   The pair to read is `path-motive-ok` here and `squash-at-a-path`
--   in MustFail368A.agda.  Both have the motive `x ≡ y` for `x y : ⟪ δ ⟫`.
--   That motive IS a proposition, because `⟪ δ ⟫` is a set.  The green
--   half passes the real `isProp`; the red half passes `squash₁` and is
--   refused with the shape of message `[LJ-1.365]` read as「the goal is
--   not a proposition」.  Only the eliminator's proof argument differs.
--
--   `squash-serves-∈ˢ` is the same point from the other side, and it
--   was MEASURED by accident: `squash₁` SERVES the motive `⟨ δ ∈ˢ ω ⟩`,
--   because that hProp unfolds to a truncation.  So `squash₁` succeeds
--   exactly when the motive unfolds to `∥ _ ∥₁`, and it fails exactly
--   when the motive does not.  Neither outcome reads the h-level.
-- =====================================================================

carrier-set : (a : V ℓ) → isSet ⟪ a ⟫
carrier-set a = isOfHLevelRespectEquiv 2 (presentation a)
  (isSetΣSndProp setIsSet (λ v → snd (v ∈ₛ a)))

path-motive-ok : (δ : S) (x y : ⟪ δ ⟫) → (body : sq δ → x ≡ y)
               → ∥ sq δ ∥₁ → x ≡ y
path-motive-ok δ x y body = PT.rec (carrier-set δ x y) body

squash-serves-∈ˢ : (δ : S) → (body : sq δ → ⟨ δ ∈ˢ ω ⟩)
                 → ∥ sq δ ∥₁ → ⟨ δ ∈ˢ ω ⟩
squash-serves-∈ˢ δ body = PT.rec {P = ⟨ δ ∈ˢ ω ⟩} squash₁ body

-- =====================================================================
-- PART 3.  ONE `PT.rec`, THROUGH THE SET-TYPED INJECTION, TO THE
--          TROPHY'S CONCLUSION.  GREEN.
--
--   `StageCards` is what a GCH body reads out of `L.StageCardinal`:
--   the ambient injection at every infinite stage
--   (src/L/StageCardinal.lagda.md:564-566).  Its value type is the
--   SET that `[LJ-1.365]`'s `inj-set` (ProbeLJ1365A.agda:160-163)
--   re-derives, and it is the goal SoloC2.agda:24-27 is refused at.
--
--   `one-rec-through-injection` crosses exactly that set, inside the
--   body of ONE `PT.rec` whose motive is the trophy's conclusion.  The
--   set-typed term is built UNDER the wrap, so it is never an
--   elimination site.  A data goal in the chain therefore does not
--   block the wrap by itself.
-- =====================================================================

StageCards : Type (ℓ-suc ℓ)
StageCards = (α : S) → IsOrd α → (⟨ α ∈ˢ ω ⟩ → Empty.⊥)
           → ⟪ Lset α ⟫ ↪ ⟪ α ⟫

cards-from-band : LimitBand → StageCards
cards-from-band lb α oα = stage-card-from-band α oα lb

one-rec-through-injection :
    (zf : ModelL.isZFModel) (κ : hPropStructure.S 𝒮ʟ)
  → (oκ : IsOrd (fst κ)) (cκ : IsCardinalL κ)
  → (κ∉ω : ⟨ fst κ ∈ˢ ω ⟩ → Empty.⊥)
  → (use : StageCards → Concl zf κ oκ cκ κ∉ω)
  → ∥ LimitBand ∥₁ → Concl zf κ oκ cκ κ∉ω
one-rec-through-injection zf κ oκ cκ κ∉ω use =
  PT.rec squash₁ (λ lb → use (cards-from-band lb))

--   And the DELIVERED use site says the same thing.
--   `Devlin55.BoundedSubsetAt` takes the whole `sq` family as a module
--   parameter (src/L/BoundedSubset.lagda.md:1388-1390); `SqBelow` IS
--   that parameter type (`[LJ-1.332]`, ProbeLJ1332A.agda:68-79).  Its
--   export is `theorem : ⟨ x ∈ˢ Lset κ ⟩`
--   (src/L/BoundedSubset.lagda.md:1621-1622), and that type is an
--   hProp: the delivered file eliminates a truncation at exactly this
--   motive at :1607.  So ONE `PT.rec` over the WHOLE family serves the
--   delivered consumer's own conclusion.
delivered-motive-is-prop : (α x κ : S)
                         → (body : SqBelow α → ⟨ x ∈ˢ Lset κ ⟩)
                         → ∥ SqBelow α ∥₁ → ⟨ x ∈ˢ Lset κ ⟩
delivered-motive-is-prop α x κ body = PT.rec (snd (x ∈ˢ Lset κ)) body

-- =====================================================================
-- PART 4.  THE REAL ELIMINATION SITE, AND C-54 AT IT.
--
--   `LimitBandT` is the band as `[LJ-1.332]` delivers it
--   (`limit-truncated`, ProbeLJ1332A.agda:196-204): the truncation
--   sits INSIDE the Pi, at each δ.  `LimitBand` (ProbeLJ1337B.agda:
--   124-129) is what `L.StageCardinal` consumes.  So the eliminator
--   must run at the motive `sq δ`, once per δ.  That motive, and not
--   the injection, is the first data goal any assembly meets.
--
--   `sq δ` is a set (`[LJ-1.319]`, re-derived here).  C-54 therefore
--   prices the step exactly: a weakly constant endomap of `sq δ`.
--   `band-from-endomap` states that price and is green.  It builds no
--   such endomap and assumes none (C-36).
-- =====================================================================

LimitBandT : Type (ℓ-suc ℓ)
LimitBandT = (δ : S) → IsOrd δ → ⟨ ω ∈ˢ δ ⟩ → Closed δ
           → (Init δ → Empty.⊥)
           → ((β : S) → ⟨ β ∈ˢ δ ⟩ → IsOrd β → ⟨ ω ∈ˢ β ⟩ → sq β)
           → ∥ sq δ ∥₁

sq-set : (α : V ℓ) → isSet (sq α)
sq-set α = isSetΣ
  (isSetΠ (λ _ → carrier-set α))
  (λ f → isProp→isSet (isPropΠ3 (λ x y _ →
    isSet× (carrier-set α) (carrier-set α) x y)))

band-from-endomap : ((δ : S) → Σ[ e ∈ (sq δ → sq δ) ] 2-Constant e)
                  → LimitBandT → LimitBand
band-from-endomap canon t δ oδ ω∈δ cl ni ih =
  PT.rec→Set (sq-set δ) (fst (canon δ)) (snd (canon δ))
    (t δ oδ ω∈δ cl ni ih)

-- =====================================================================
-- PART 5.  THE ONE MISSING STEP, STATED.
--
--   `BandChoice` says the truncation commutes with the band's Pi.  It
--   is the whole distance between `[LJ-1.332]`'s delivered band and a
--   proof of the trophy that never untruncates: `closes-from-choice`
--   is green, and it takes NO untruncation of `sq`, only `BandChoice`
--   and one `PT.rec` at the propositional conclusion.
--
--   Nothing here proves `BandChoice`, and nothing here refutes it.
--   MustFail368B.agda records what the naive proof does: the refusal
--   lands at `isProp (sq δ)`, inside the Pi, and that is the goal an
--   assembly cannot avoid.
-- =====================================================================

BandChoice : Type (ℓ-suc ℓ)
BandChoice = LimitBandT → ∥ LimitBand ∥₁

closes-from-choice :
    (zf : ModelL.isZFModel) (κ : hPropStructure.S 𝒮ʟ)
  → (oκ : IsOrd (fst κ)) (cκ : IsCardinalL κ)
  → (κ∉ω : ⟨ fst κ ∈ˢ ω ⟩ → Empty.⊥)
  → (use : StageCards → Concl zf κ oκ cκ κ∉ω)
  → BandChoice → LimitBandT → Concl zf κ oκ cκ κ∉ω
closes-from-choice zf κ oκ cκ κ∉ω use bc t =
  one-rec-through-injection zf κ oκ cκ κ∉ω use (bc t)

--   And `BandChoice` is no STRONGER than the untruncation `[LJ-1.332]`
--   asks for: the untruncation gives it in one line.  The converse is
--   not measured here, and nothing below assumes it.
choice-from-untruncation : (LimitBandT → LimitBand) → BandChoice
choice-from-untruncation u t = PT.∣ u t ∣₁
