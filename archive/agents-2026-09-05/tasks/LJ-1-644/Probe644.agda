{-# OPTIONS --cubical --safe --guardedness #-}

-- [LJ-1.644]  IS THE BILL'S KAPPA THE SITE THE PRODUCER CHOOSES?
--
-- THE ANSWER.  `fst κ` is a site `cardAboveAt` chooses EXACTLY WHEN two
-- things hold at once: `fst κ` is an AMBIENT cardinal, and `fst κ` has
-- a PREDECESSOR.  Section 5 states that as one biconditional.  Both
-- halves are unpaid at the bill, and the first of them is the very
-- thing the join defect wanted to buy, so this route is a LOOP.
--
-- The floor was measured first, with the three real bodies as holes:
-- runs/floor-1.out, 4.13 s, 715.7 MB, EXIT=42 on those holes alone.
--
-- CALIBER.  The program set GHCRTS on this pane.  I did not set it.
-- One Agda process at a time.  Nothing lands in src/.

open import Base.Prelude
open import Base.Truth
open import Base.Classical using ( LEM )

module LJ-1-644.Probe644 {ℓ : Level} (lem : LEM (ℓ-suc ℓ)) where

open import FOL.ZFStructure using ( module hPropStructure )
open import V.Hierarchy {ℓ} using ( 𝒮ᵥ; ∈-irrefl )
open import V.Model {ℓ} using ( self∈sucV )
open import L.Constructible {ℓ} using ( 𝒮ʟ; IsOrd )
open import L.Ordinal {ℓ} using ( suc-ord )
open import L.Ordinal.Linear {ℓ} lem using ( Tri; ord-tri )
open import L.Cardinal {ℓ} lem using ( IsCardinalL )
open import L.BoundedSubset {ℓ} lem using ( IsCardinal; _↪_ )
open import L.CardinalAbove {ℓ} lem
  using ( cardAboveAt; noInjOrd; ordL; module Sep )

open import Cubical.HITs.CumulativeHierarchy.Properties using ( ⟪_⟫ )
open import Cubical.HITs.CumulativeHierarchy.Constructions
  using ( module InfinitySet )
open InfinitySet {ℓ} using ( ω; sucV )
open import Cubical.Data.Sigma using ( _×_ )
open import Cubical.Data.Sum using ( inl; inr )
import Cubical.Data.Empty as Empty
import Cubical.HITs.PropositionalTruncation as PT
open PT using ( ∥_∥₁ )

module SV = hPropStructure 𝒮ᵥ
module SL = hPropStructure 𝒮ʟ
open SV using ( _∈ˢ_ )

-- =====================================================================
-- SECTION 1.  WHAT "THE SITE THE PRODUCER CHOOSES" IS.
-- =====================================================================

NoInjAt : SV.S → Type (ℓ-suc ℓ)
NoInjAt a = Σ[ γ ∈ SV.S ] (IsOrd γ × (⟪ γ ⟫ ↪ ⟪ a ⟫ → Empty.⊥))

ChosenSite : SL.S → Type (ℓ-suc ℓ)
ChosenSite κ =
  Σ[ a ∈ SV.S ] Σ[ oa ∈ IsOrd a ] Σ[ h ∈ NoInjAt a ]
    (fst (cardAboveAt a oa h) ≡ fst κ)

Predecessor : SL.S → Type (ℓ-suc ℓ)
Predecessor κ =
  Σ[ a ∈ SV.S ]
    (IsOrd a × ⟨ a ∈ˢ fst κ ⟩
     × ((x : SV.S) → ⟨ x ∈ˢ fst κ ⟩ → ∥ ⟪ x ⟫ ↪ ⟪ a ⟫ ∥₁))

-- =====================================================================
-- SECTION 2.  WHAT A CHOSEN SITE BUYS.
-- =====================================================================

-- THE PAYOFF.  The producer hands its `IsCardinal` out at the site IT
-- built; an equality with the bill's site transports it there.  THIS IS
-- THE WHOLE POINT OF THE ROUTE, and it is three lines.
--
-- MEASURED, AND IT IS A PRICE AND NOT A REMARK.  This row is cheap at a
-- VARIABLE `e`, and it walls at a CONCRETE one: applying it where `θ` is
-- a literal separation term cost more than 240 s and did not finish
-- (runs/s6-c.out, EXIT=142), against 2.66 s for the same fact taken
-- straight out of `cardAboveAt` (runs/s6-a.out).  `IsCardinal θ` is a
-- Π-type over `⟪ θ ⟫`, so `subst` is a `transp` across the whole
-- separation set.  Section 6 obeys that measurement.
chosen→amb : (κ : SL.S) → ChosenSite κ → IsCardinal (fst κ)
chosen→amb κ (a , oa , h , e) =
  subst IsCardinal e (cardAboveAt a oa h .snd .snd .fst)

-- AND THE PAYOFF IS NOT FREE OF THE SECOND INPUT EITHER.  A chosen site
-- FORCES a predecessor: the producer's own `a` sits inside it (that is
-- the third component of `cardAboveAt`'s output) and every member of the
-- separation injects into `a` by `θ-inj`.  So `Predecessor` below is not
-- an artefact of the proof in section 3.  It is what the route IS.
chosen→pred : (κ : SL.S) → ChosenSite κ → Predecessor κ
chosen→pred κ (a , oa , (γ , oγ , noinj) , e) =
    a , oa
  , subst (λ z → ⟨ a ∈ˢ z ⟩) e
      (cardAboveAt a oa (γ , oγ , noinj) .snd .snd .snd)
  , (λ x x∈κ → S.θ-inj x (subst (λ z → ⟨ x ∈ˢ z ⟩) (sym e) x∈κ))
  where
  module S = Sep a (sucV γ) (suc-ord oγ)

-- =====================================================================
-- SECTION 3.  WHAT PINNING THE BILL'S SITE COSTS.
-- =====================================================================

-- THE CONVERSE, AND `a := κ` IS NOT AVAILABLE HERE.  [LJ-1.640] closed
-- its own converse by instantiating the producer AT the bill's site
-- (Probe640.agda:110-114, `amb→least-at-self`).  That move is BLOCKED
-- for `cardAboveAt`, because its output carries `⟨ a ∈ˢ θ ⟩`: the chosen
-- site is STRICTLY above `a`, so `a := fst κ` can never give `θ ≡ fst κ`.
-- The witness `a` must come from BELOW, and nothing hands one in.
--
-- The bound `γ` costs nothing: `fst κ` is its own bound, and the one
-- fact `cardAboveAt` wants of it, that it does not inject into `a`, is
-- the ambient cardinality applied to `a ∈ κ`.
pred+amb→chosen :
    (κ : SL.S) (oκ : IsOrd (fst κ))
  → IsCardinal (fst κ) → Predecessor κ → ChosenSite κ
pred+amb→chosen κ oκ amb (a , oa , a∈κ , allinj) = a , oa , h , θ≡κ
  where
  noinj : ⟪ fst κ ⟫ ↪ ⟪ a ⟫ → Empty.⊥
  noinj = amb a a∈κ

  h : NoInjAt a
  h = fst κ , oκ , noinj

  module S = Sep a (sucV (fst κ)) (suc-ord oκ)

  -- Trichotomy at the two sites, and each losing leg is one witness.
  --   θ ∈ κ : then θ injects into `a` by the predecessor clause, and θ
  --           is inside the bound, so the separation puts θ into θ.
  --   κ ∈ θ : then κ injects into `a` by the separation's own clause,
  --           and that is exactly what ambient cardinality refuses.
  θ≡κ : S.θ ≡ fst κ
  θ≡κ = go (ord-tri S.θ S.θ-ord (fst κ) oκ)
    where
    go : Tri S.θ (fst κ) → S.θ ≡ fst κ
    go (inl θ∈κ) =
      Empty.rec (∈-irrefl S.θ (S.θ-in S.θ θ∈sκ (allinj S.θ θ∈κ)))
      where
      θ∈sκ : ⟨ S.θ ∈ˢ sucV (fst κ) ⟩
      θ∈sκ = suc-ord oκ .fst θ∈κ (self∈sucV (fst κ))
    go (inr (inl e))   = e
    go (inr (inr κ∈θ)) =
      Empty.rec (PT.rec Empty.isProp⊥ noinj (S.θ-inj (fst κ) κ∈θ))

-- =====================================================================
-- SECTION 4.  THE OBLIGATION.
-- =====================================================================

-- THE BRIEF'S TYPE, IN THE FORM THAT NAMES THE INPUTS.  The brief let
-- the conclusion be "the statement that `fst κ` IS the chosen `θ`, or
-- the term naming the one input that statement needs".  It needs TWO,
-- and both stand in the telescope below.
--
-- `cκ` AND `κ∉ω` ARE DEAD ON THIS ROUTE.  Neither body mentions either,
-- exactly as `noInjOrd→CardAboveLᵀ` reports of the same two hypotheses
-- (src/L/CardinalAbove.lagda.md:223-225).  `IsCardinalL` is the CODED
-- predicate; every step above is ambient, and [LJ-1.533] settled that
-- the coded one does not buy the ambient one.
kappa-is-chosen :
    (κ : SL.S) → IsOrd (fst κ) → IsCardinalL κ
  → (⟨ fst κ ∈ˢ ω ⟩ → Empty.⊥)
  → IsCardinal (fst κ) → Predecessor κ
  → ChosenSite κ
kappa-is-chosen κ oκ cκ κ∉ω amb p = pred+amb→chosen κ oκ amb p

-- =====================================================================
-- SECTION 5.  THE ANSWER IN ONE TYPE, AND THE LOOP.
-- =====================================================================

chosen⟺ :
    (κ : SL.S) (oκ : IsOrd (fst κ))
  → (ChosenSite κ → IsCardinal (fst κ) × Predecessor κ)
  × (IsCardinal (fst κ) × Predecessor κ → ChosenSite κ)
chosen⟺ κ oκ =
    (λ c → chosen→amb κ c , chosen→pred κ c)
  , (λ q → pred+amb→chosen κ oκ (fst q) (snd q))

-- THE ROUTE IS A LOOP, AND THIS TERM IS THE STATEMENT OF IT.  What a
-- chosen site BUYS at the bill's site is `IsCardinal (fst κ)`.  What
-- pinning the bill's site as a chosen site COSTS is `IsCardinal (fst κ)`
-- and a predecessor.  So the producer census of [LJ-1.643] closes here:
-- no producer of ambient cardinality can be pointed at a site handed in,
-- and `cardAboveAt` is no exception even with its equality supplied.
route-is-circular :
    (κ : SL.S) (oκ : IsOrd (fst κ)) → Predecessor κ
  → IsCardinal (fst κ) → IsCardinal (fst κ)
route-is-circular κ oκ p amb =
  chosen→amb κ (pred+amb→chosen κ oκ amb p)

-- =====================================================================
-- SECTION 6.  THE OTHER HALF OF THE ANSWER: WHAT IS FREE.
--
--   Nothing above says the tree is short of ambient cardinals.  It is
--   short of one AT A SITE HANDED IN.  Above ANY ordinal the tree hands
--   one over with no hypothesis at all, because `noInjOrd`
--   (src/L/CardinalAbove.lagda.md:575) discharges `cardAboveAt`'s one
--   external input; and the site it hands over IS a chosen site, by
--   `refl`.  So the restatement the mathematician may want, the bill run
--   at the PRODUCER's site rather than at its own, is already paid here.
--   Its one price is the truncation.
--
--   `IsCardinal` IS READ FROM `cardAboveAt` AND NOT TRANSPORTED ALONG
--   THE EQUALITY, for the reason section 2 measured.
-- =====================================================================

free-chosen-above :
    (a : SV.S) → IsOrd a
  → ∥ Σ[ θ ∈ SL.S ]
       (ChosenSite θ × IsCardinal (fst θ) × ⟨ a ∈ˢ fst θ ⟩) ∥₁
free-chosen-above a oa = PT.map build (noInjOrd a oa)
  where
  build : NoInjAt a
        → Σ[ θ ∈ SL.S ]
            (ChosenSite θ × IsCardinal (fst θ) × ⟨ a ∈ˢ fst θ ⟩)
  build h =
      ordL (fst (cardAboveAt a oa h)) (cardAboveAt a oa h .snd .fst)
    , (a , oa , h , refl)
    , cardAboveAt a oa h .snd .snd .fst
    , cardAboveAt a oa h .snd .snd .snd
