{-# OPTIONS --cubical --safe --guardedness #-}

-- [LJ-1.637]  THE CONSUMER, ASSEMBLED FROM THE LANDED TABLE, WITH
-- INGREDIENT (iii) AS THE ONE REMAINING HYPOTHESIS.
--
-- THE OBLIGATION is `class-pred-debt` (section 4): the class-pred
-- consumer of the class-pred table, assembled from the four landed
-- rows of `src/`, with (iii) as the ONLY remaining hypothesis and
-- (iii)'s exact type written out (section 1): one binary function on
-- the site's index with its injectivity at one ordinal.  The
-- consumer is the tree's own: `class-pred` at
-- src/L/StageCardinal.lagda.md:329-330, read at `:361` by `leastOf`,
-- exactly as the brief states it.  Its grain is the site-fixed
-- re-run of the `∈-induction` whose limit step IS that consumer:
-- [LJ-1.617] ran this same re-run green
-- (agents/tasks/LJ-1-617/Probe617.agda:464-471) and [LJ-1.621]
-- packaged the same obligation from the same fiber
-- (agents/tasks/LJ-1-621/Probe621.agda:128-129).  What this file adds
-- is the read: the step's D and inv ARE the landed row (i)
-- (src/L/Constructible.lagda.md:314-317), its selection IS the landed
-- row (ii) (src/L/StageCardinal.lagda.md:265-272), its pairing IS the
-- hypothesis (iii) spent once, at the site, in the landed `Bound`; the
-- induction hypothesis it consumes is the ambient mirror of the branch
-- the landed row (iv) graphs (src/L/BoundedSubset.lagda.md:1512-1518),
-- named in term position in section 5; and the landed row (v)
-- (src/L/Choice/Faithful.lagda.md:962-963) is named, not consumed, in
-- section 6.
--
-- D-10, BEFORE ANY AGDA: the assembly is a substitution instance of a
-- GREEN TERM.  The tree's `LimitStep` at its site typechecks in the
-- tree (src/L/StageCardinal.lagda.md:329-403); [LJ-1.617] ran the
-- site-fixed re-run of the same step green, and [LJ-1.621] delivered
-- the same obligation from the same fiber green.  Every row of
-- `DebtStep` below is the corresponding [LJ-1.617] row with the
-- landed name in place of the probe-local one, so the target is TRUE
-- by construction and no Tarskian or cardinality objection applies.
-- The measurement in this file is the W3 the brief names, "the
-- assembly itself": the cost of the step reading the landed rows,
-- against the brief's 100-to-200-line estimate.  The only risk is
-- frame cost, in the import closure (the `L.BoundedSubset`
-- interface, for the (iv) read, is the largest object here) and in
-- the step body itself.  This file carries NO postulate and NO hole
-- in its final form, so every row is a measurement.  Nothing lands in
-- `src/`.
--
--   Section 1.  INGREDIENT (iii), THE EXACT TYPE, and its identity
--               with the law chapter's `sq` and with [LJ-1.618]'s
--               payload.
--   Section 2.  INGREDIENTS (i) AND (ii), THE LANDED ROWS, READ.
--   Section 3.  THE CONSUMER, ASSEMBLED: `DebtStep`, the limit step
--               reading the table.
--   Section 4.  THE DEBT: `class-pred-debt`, (iii) the only
--               remaining hypothesis.
--   Section 5.  INGREDIENT (iv), READ AT THE BRANCH.
--   Section 6.  INGREDIENT (v), NAMED AT THE RANGE.
--
-- NO ROW puts `step`, `branch` or `stage-card-upper` into a
-- conversion problem ([LJ-1.584]'s measurement): the step's body is
-- applied by `∈-induction` only, and no line equates two step-shaped
-- terms.  The band parameter `band` stays the ABSTRACT module
-- parameter it is in `src/`; no row instantiates it, prices it, or
-- reaches into the circle.
--
-- CALIBER.  THE PROGRAM SET GHCRTS ON THIS PANE.  I DID NOT SET IT.
-- ONE AGDA PROCESS AT A TIME.  Caps are set and reported per run in
-- `runs/`: W3 alone first, then the floor (the step bodies holed),
-- then the final.

open import Base.Prelude
open import Base.Truth
open import Base.Classical using ( LEM )
open import Cubical.HITs.CumulativeHierarchy.Base using ( V; _∈_ )
open import Cubical.HITs.CumulativeHierarchy.Properties using ( ⟪_⟫ )
open import Cubical.HITs.CumulativeHierarchy.Constructions using ( module InfinitySet )
open import Cubical.Data.Sigma using ( Σ-syntax )
open import Cubical.Data.Nat using ( ℕ )
open import L.Constructible using ( IsOrd; Lset )
open import LJ-1-594.runs.W3 using ( SqParam )
import Cubical.Data.Empty as Empty

module LJ-1-637.Probe637 {ℓ : Level} (lem : LEM (ℓ-suc ℓ))
  (α₀ : V ℓ) (oα₀ : IsOrd α₀)
  (α∉ω₀ : ⟨ α₀ ∈ InfinitySet.ω {ℓ} ⟩ → Empty.⊥)
  (band : SqParam α₀) where

open import FOL.Syntax using ( Formula )
open import FOL.ZFStructure using ( module hPropStructure )
open import Cubical.HITs.CumulativeHierarchy.Properties using ( ⟪_⟫↪ )
open import V.Hierarchy {ℓ} using ( 𝒮ᵥ; ∈-induction )
open import V.Presentation {ℓ} using ( fiber; member; ↪-inj )
open import V.Model {ℓ} using ( self∈sucV; ∈sucV-elim )
open import L.Constructible {ℓ} using ( 𝒟ₒ; class-pred-i; Lset-out; 𝒮ʟ )
open import L.Ordinal {ℓ} using ( mem-ord; suc-ord )
open import L.Ordinal.SquareLaw {ℓ} lem using ( sq )
open import L.WellOrder.Base {ℓₚ = ℓ-suc ℓ} using ( IsLeast )
open import Cubical.Foundations.Prelude using ( J; substRefl )
open InfinitySet using ( ω; sucV )
import Cubical.HITs.PropositionalTruncation as PT
open PT using ( ∣_∣₁; ∥_∥₁; squash₁ )

import L.StageCardinal {ℓ} lem α₀ oα₀ band as SC

import L.Choice.Faithful {ℓ} lem as F637
import L.BoundedSubset {ℓ} lem as LB
import LJ-1-618.Probe618
module P618 = LJ-1-618.Probe618 lem

open TruthAlgebra (hPropAlgebra (ℓ-suc ℓ))
open hPropStructure 𝒮ᵥ
module SLv = hPropStructure 𝒮ʟ

-- =====================================================================
-- SECTION 0.  THE INJECTION TYPE, LOCAL.  The tree's own shape
-- (src/L/StageCardinal.lagda.md:243-246, restated at
-- src/L/BoundedSubset.lagda.md:1365-1368 and at
-- agents/tasks/LJ-1-617/Probe617.agda:107-108).  Stated here because
-- the type of the obligation is written before the read names it.
-- =====================================================================

_↪_ : Type ℓ → Type ℓ → Type ℓ
X ↪ Y = Σ[ f ∈ (X → Y) ] ((x y : X) → f x ≡ f y → x ≡ y)

-- =====================================================================
-- SECTION 1.  INGREDIENT (iii), THE EXACT TYPE.  One binary function
-- on the site's index with its injectivity, at ONE ordinal.  This is
-- the value half of the band parameter applied at the site (the
-- tree's own spend, src/L/BoundedSubset.lagda.md:1410), and the
-- written type of the debt's one argument below.
-- =====================================================================

SiteFiber : V ℓ → Type ℓ
SiteFiber β = Σ[ f ∈ (⟪ β ⟫ × ⟪ β ⟫ → ⟪ β ⟫) ]
  ((u v : ⟪ β ⟫ × ⟪ β ⟫) → f u ≡ f v → u ≡ v)

-- 1.1  IT IS THE LAW CHAPTER'S OWN FIBER TYPE, by one delta step
--      (src/L/Ordinal/SquareLaw.lagda.md:685-688); [LJ-1.604]
--      measured the identity and [LJ-1.618] recorded it at its
--      payload (agents/tasks/LJ-1-618/Probe618.agda:85-86).
fiber-is-the-law-sq : SiteFiber α₀ ≡ sq α₀
fiber-is-the-law-sq = refl

-- 1.2  IT IS [LJ-1.618]'s PAYLOAD, the same type by one delta step
--      (agents/tasks/LJ-1-618/Probe618.agda:79-83).  Whatever wall
--      [LJ-1.618] measured at that payload — the untruncation, and
--      the residue it parked (agents/tasks/LJ-1-618/Probe618.agda:
--      210-211) — is a wall and a residue at the site.
fiber-is-618s-payload : SiteFiber α₀ ≡ P618.PairingAt α₀
fiber-is-618s-payload = refl

-- =====================================================================
-- SECTION 2.  INGREDIENTS (i), (ii) AND (v), THE LANDED ROWS, READ.
-- =====================================================================

-- 2.1  (i) THE LANDED ROW, its two projections in the parameter
--      shapes the consumer declares (src/L/StageCardinal.lagda.md:
--      277-280).  The row is sealed opaque at its birth site
--      (src/L/Constructible.lagda.md:301-317); its body was measured
--      inside the seal by [LJ-1.613]'s alone-typechecked W3, and this
--      file reads the row as the constant it is, without reaching
--      into the seal.
D-i : (δ : S) → Formula ⟪ Lset δ ⟫ 1 → S
D-i = fst class-pred-i

inv-i : (δ : S) (y : S) → ⟨ y ∈ˢ 𝒟ₒ (Lset δ) ⟩
      → ∥ Σ[ φ₀ ∈ Formula ⟪ Lset δ ⟫ 1 ] (D-i δ φ₀ ≡ y) ∥₁
inv-i = snd class-pred-i

-- 2.2  (ii) THE LANDED SELECTION, the standalone row the consumer's
--      `h` makes inline at its site (src/L/StageCardinal.lagda.md:
--      265-272, the call at `:361`): least element of a nonempty
--      class over the members of a stage, over the ordinal order,
--      with the leastness certified in the result by `IsLeast`.
--      The binding below is the row itself, in the tree's own type.
selection-at : (δ : S) (oδ : IsOrd δ) (P : ⟪ δ ⟫ → hProp (ℓ-suc ℓ))
             → ∥ Σ[ a ∈ ⟪ δ ⟫ ] ⟨ P a ⟩ ∥₁
             → Σ[ a ∈ ⟪ δ ⟫ ] IsLeast (SC.OrdSWO.ordSWO δ oδ) P a
selection-at = SC.least-at-site

-- =====================================================================
-- SECTION 3.  THE CONSUMER, ASSEMBLED.  The limit step at every
-- ordinal γ of the site's band, with the COUNTING and PACKING
-- carrier fixed at the site α₀, so the pairing is spent ONCE, at the
-- site, and nowhere else.  Source of the proof text: [LJ-1.617]'s
-- `SiteStep` (agents/tasks/LJ-1-617/Probe617.agda:318-462), which is
-- the tree's `LimitStep` (src/L/StageCardinal.lagda.md:277-403) with
-- the target fixed at the site; against [LJ-1.617], this module
-- differs ONLY in the four reads:
--   * `B` is the LANDED `Bound` (src/L/StageCardinal.lagda.md:69-
--     241), instantiated once, at the site, on the hypothesis (iii) —
--     not [LJ-1.617]'s byte copy;
--   * `D` and `inv` ARE the landed row (i), section 2.1;
--   * `h` and `h-inj` make their selection through the LANDED row
--     (ii), section 2.2 — definitionally the tree's inline `leastOf`
--     call;
--   * the key row of [LJ-1.617]'s step is ABSENT from the tree's own
--     consumer: the class-pred witness (src/L/StageCardinal.lagda.md:
--     329-334) carries the formula itself, and the landed row (v) is
--     named, not consumed, section 6.
-- The composed induction hypothesis `ih` is the ambient mirror of the
-- branch the landed row (iv) graphs; the read is section 5.
-- =====================================================================

module DebtStep (iii : SiteFiber α₀)
  (γ : S) (oγ : IsOrd γ) (γ∈suc : ⟨ γ ∈ˢ sucV α₀ ⟩)
  (IH : (δ : S) → ⟨ δ ∈ˢ γ ⟩ → IsOrd δ → ⟨ δ ∈ˢ sucV α₀ ⟩
      → ⟪ Lset δ ⟫ ↪ ⟪ α₀ ⟫) where

  -- (iii) the assembly's ONE hypothesis, into the landed `Bound`,
  -- instantiated ONCE, at the site: the tree's own spend shape
  -- (src/L/BoundedSubset.lagda.md:1410).
  module B = SC.Bound α₀ oα₀ α∉ω₀ iii

  δ∈sucV : (δ : S) → ⟨ δ ∈ˢ γ ⟩ → ⟨ δ ∈ˢ sucV α₀ ⟩
  δ∈sucV δ δ∈γ = suc-ord oα₀ .fst {x = γ} {y = δ} δ∈γ γ∈suc

  -- (iv) the hypothesis the consumer consumes, per member ordinal:
  -- the branch `class-pred-iv` graphs at each strictly-infinite
  -- member stage is the object-language twin of this `ihm`
  -- (src/L/BoundedSubset.lagda.md:1512-1518).  The read is section 5.
  ihm : (m : ⟪ γ ⟫) → ⟪ Lset (⟪ γ ⟫↪ m) ⟫ ↪ ⟪ α₀ ⟫
  ihm m = IH (⟪ γ ⟫↪ m) (member γ m)
    (mem-ord {A = γ} oγ (⟪ γ ⟫↪ m) (member γ m))
    (δ∈sucV (⟪ γ ⟫↪ m) (member γ m))

  γ⊆α₀ : (δ : S) → ⟨ δ ∈ˢ γ ⟩ → ⟨ δ ∈ˢ α₀ ⟩
  γ⊆α₀ δ δ∈γ = ∈sucV-elim {A = α₀} {x = γ} {P = ⟨ δ ∈ˢ α₀ ⟩} ((δ ∈ˢ α₀) .snd)
    γ∈suc
    (λ γ∈α₀ → oα₀ .fst {x = γ} {y = δ} δ∈γ γ∈α₀)
    (λ γ≡α₀ → subst (λ w → ⟨ δ ∈ˢ w ⟩) γ≡α₀ δ∈γ)

  emb : ⟪ γ ⟫ → ⟪ α₀ ⟫
  emb m = fiber α₀ {x = ⟪ γ ⟫↪ m} (γ⊆α₀ (⟪ γ ⟫↪ m) (member γ m)) .fst

  emb-inj : (m n : ⟪ γ ⟫) → emb m ≡ emb n → m ≡ n
  emb-inj m n e = ↪-inj {a = γ}
    (sym (fiber α₀ {x = ⟪ γ ⟫↪ m} (γ⊆α₀ (⟪ γ ⟫↪ m) (member γ m)) .snd)
      ∙ cong (⟪ α₀ ⟫↪) e
      ∙ fiber α₀ {x = ⟪ γ ⟫↪ n} (γ⊆α₀ (⟪ γ ⟫↪ n) (member γ n)) .snd)

  -- (i) read: the landed row of section 2.1, in the parameter shapes
  -- the consumer declares.
  D : (δ : S) → Formula ⟪ Lset δ ⟫ 1 → S
  D = D-i

  inv : (δ : S) (y : S) → ⟨ y ∈ˢ 𝒟ₒ (Lset δ) ⟩
      → ∥ Σ[ φ₀ ∈ Formula ⟪ Lset δ ⟫ 1 ] (D δ φ₀ ≡ y) ∥₁
  inv = inv-i

  F : ⟪ γ ⟫ → Type ℓ
  F m = Formula ⟪ Lset (⟪ γ ⟫↪ m) ⟫ 1

  cnt : (m : ⟪ γ ⟫) → F m → ⟪ α₀ ⟫
  cnt m = fst (B.formula-bound {K = ⟪ Lset (⟪ γ ⟫↪ m) ⟫} (ihm m))

  cnt-inj : (m : ⟪ γ ⟫) (φ ψ : F m) → cnt m φ ≡ cnt m ψ → φ ≡ ψ
  cnt-inj m = snd (B.formula-bound {K = ⟪ Lset (⟪ γ ⟫↪ m) ⟫} (ihm m))

  cnt-stable : (m₁ m₂ : ⟪ γ ⟫) (q : m₂ ≡ m₁) (φ : F m₂)
             → cnt m₁ (subst F q φ) ≡ cnt m₂ φ
  cnt-stable m₁ m₂ q φ =
    J (λ m₁ q → (φ : F m₂) → cnt m₁ (subst F q φ) ≡ cnt m₂ φ)
      (λ φ → cong (cnt m₂) (substRefl {B = F} {x = m₂} φ)) q φ

  defset-stable : (m₁ m₂ : ⟪ γ ⟫) (q : m₂ ≡ m₁) (φ : F m₂)
                → D (⟪ γ ⟫↪ m₁) (subst F q φ)
                  ≡ D (⟪ γ ⟫↪ m₂) φ
  defset-stable m₁ m₂ q φ =
    J (λ m₁ q → (φ : F m₂) → D (⟪ γ ⟫↪ m₁) (subst F q φ)
                ≡ D (⟪ γ ⟫↪ m₂) φ)
      (λ φ → cong (D (⟪ γ ⟫↪ m₂)) (substRefl {B = F} {x = m₂} φ)) q φ

  defset-stable-δ : (δ₁ δ₂ : S) (p : δ₁ ≡ δ₂) (φ₀ : Formula ⟪ Lset δ₁ ⟫ 1)
                  → D δ₁ φ₀
                    ≡ D δ₂
                        (subst (λ w → Formula ⟪ Lset w ⟫ 1) p φ₀)
  defset-stable-δ δ₁ δ₂ p φ₀ =
    J (λ δ₂ p → (φ₀ : Formula ⟪ Lset δ₁ ⟫ 1) → D δ₁ φ₀
                ≡ D δ₂
                    (subst (λ w → Formula ⟪ Lset w ⟫ 1) p φ₀))
      (λ φ₀ → sym (cong (D δ₁)
                   (substRefl {B = λ w → Formula ⟪ Lset w ⟫ 1} {x = δ₁} φ₀))) p φ₀

  -- THE CONSUMER ITSELF, the tree's own family
  -- (src/L/StageCardinal.lagda.md:329-330), at the fixed site: each
  -- member of Lset γ is merely a member of 𝒟ₒ (Lset δ) for δ ∈ γ
  -- (Lset-out), hence merely a D φ for some φ (the landed row (i));
  -- the count of φ's formula type into ⟪ α₀ ⟫ is the landed `Bound`'s
  -- formula-bound on the branch; packing the stage index and the
  -- count through the pairing (the hypothesis (iii)) forms the class.
  class-pred : (x : ⟪ Lset γ ⟫) → ⟪ α₀ ⟫ → hProp (ℓ-suc ℓ)
  class-pred x y = ( ∥ Σ[ m ∈ ⟪ γ ⟫ ] Σ[ φ ∈ F m ]
                        ( ( D (⟪ γ ⟫↪ m) φ ≡ ⟪ Lset γ ⟫↪ x )
                        × ( B.pair (emb m) (cnt m φ) ≡ y ) ) ∥₁
                   , squash₁ )

  nonempty : (x : ⟪ Lset γ ⟫)
           → ∥ Σ[ y ∈ ⟪ α₀ ⟫ ] ⟨ class-pred x y ⟩ ∥₁
  nonempty x = PT.rec (squash₁) toWitness
    (Lset-out γ (⟪ Lset γ ⟫↪ x) (member (Lset γ) x))
    where
    toWitness : Σ[ δ ∈ S ] (⟨ δ ∈ˢ γ ⟩ × ⟨ ⟪ Lset γ ⟫↪ x ∈ˢ 𝒟ₒ (Lset δ) ⟩)
              → ∥ Σ[ y ∈ ⟪ α₀ ⟫ ] ⟨ class-pred x y ⟩ ∥₁
    toWitness (δ , (δ∈γ , x∈𝒟ₒδ)) =
      PT.map mk (inv δ (⟪ Lset γ ⟫↪ x) x∈𝒟ₒδ)
      where
      fib = fiber γ δ∈γ
      m : ⟪ γ ⟫
      m = fib .fst
      p : ⟪ γ ⟫↪ m ≡ δ
      p = fib .snd
      mk : Σ[ φ₀ ∈ Formula ⟪ Lset δ ⟫ 1 ]
             (D δ φ₀ ≡ ⟪ Lset γ ⟫↪ x)
         → Σ[ y ∈ ⟪ α₀ ⟫ ] ⟨ class-pred x y ⟩
      mk (φ₀ , e₀) = (B.pair (emb m) (cnt m φ) , ∣ (m , φ , (e , refl)) ∣₁)
        where
        φ : F m
        φ = subst (λ w → Formula ⟪ Lset w ⟫ 1) (sym p) φ₀
        e : D (⟪ γ ⟫↪ m) φ ≡ ⟪ Lset γ ⟫↪ x
        e = sym (defset-stable-δ δ (⟪ γ ⟫↪ m) (sym p) φ₀) ∙ e₀

  -- (ii) read: the selection is the landed row of section 2.2; the
  -- tree's own `h` makes this very call inline at its site
  -- (src/L/StageCardinal.lagda.md:361).
  h : ⟪ Lset γ ⟫ → ⟪ α₀ ⟫
  h x = fst (selection-at α₀ oα₀ (class-pred x) (nonempty x))

  h-inj : (x y : ⟪ Lset γ ⟫) → h x ≡ h y → x ≡ y
  h-inj x y e = ↪-inj {a = Lset γ} (go pm)
    where
    lx = selection-at α₀ oα₀ (class-pred x) (nonempty x)
    ly = selection-at α₀ oα₀ (class-pred y) (nonempty y)
    pm : ⟨ class-pred x (fst ly) ⟩
    pm = subst (λ z → ⟨ class-pred x z ⟩) e (fst (snd lx))
    py : ⟨ class-pred y (fst ly) ⟩
    py = fst (snd ly)
    go : ⟨ class-pred x (fst ly) ⟩
       → ⟪ Lset γ ⟫↪ x ≡ ⟪ Lset γ ⟫↪ y
    go = PT.rec (isSetS (⟪ Lset γ ⟫↪ x) (⟪ Lset γ ⟫↪ y)) go₁
      where
      go₁ : Σ[ m₁ ∈ ⟪ γ ⟫ ] Σ[ φ₁ ∈ F m₁ ]
              ( ( D (⟪ γ ⟫↪ m₁) φ₁ ≡ ⟪ Lset γ ⟫↪ x )
              × ( B.pair (emb m₁) (cnt m₁ φ₁) ≡ fst ly ) )
          → ⟪ Lset γ ⟫↪ x ≡ ⟪ Lset γ ⟫↪ y
      go₁ (m₁ , φ₁ , eφ₁ , ec₁) =
        PT.rec (isSetS (⟪ Lset γ ⟫↪ x) (⟪ Lset γ ⟫↪ y)) go₂ py
        where
        go₂ : Σ[ m₂ ∈ ⟪ γ ⟫ ] Σ[ φ₂ ∈ F m₂ ]
                ( ( D (⟪ γ ⟫↪ m₂) φ₂ ≡ ⟪ Lset γ ⟫↪ y )
                × ( B.pair (emb m₂) (cnt m₂ φ₂) ≡ fst ly ) )
            → ⟪ Lset γ ⟫↪ x ≡ ⟪ Lset γ ⟫↪ y
        go₂ (m₂ , φ₂ , eφ₂ , ec₂) = sym eφ₁ ∙ eq-defset ∙ eφ₂
          where
          ec : B.pair (emb m₁) (cnt m₁ φ₁) ≡ B.pair (emb m₂) (cnt m₂ φ₂)
          ec = ec₁ ∙ sym ec₂
          p-pair : (emb m₁ ≡ emb m₂) × (cnt m₁ φ₁ ≡ cnt m₂ φ₂)
          p-pair = B.pair-inj (emb m₁) (cnt m₁ φ₁) (emb m₂) (cnt m₂ φ₂) ec
          qm : m₁ ≡ m₂
          qm = emb-inj m₁ m₂ (fst p-pair)
          ecount : cnt m₁ φ₁ ≡ cnt m₂ φ₂
          ecount = snd p-pair
          ecount' : cnt m₁ φ₁ ≡ cnt m₁ (subst F (sym qm) φ₂)
          ecount' = ecount ∙ sym (cnt-stable m₁ m₂ (sym qm) φ₂)
          eφ : φ₁ ≡ subst F (sym qm) φ₂
          eφ = cnt-inj m₁ φ₁ (subst F (sym qm) φ₂) ecount'
          eq-defset : D (⟪ γ ⟫↪ m₁) φ₁
                    ≡ D (⟪ γ ⟫↪ m₂) φ₂
          eq-defset = cong (D (⟪ γ ⟫↪ m₁)) eφ
                    ∙ defset-stable m₁ m₂ (sym qm) φ₂

  leg : ⟪ Lset γ ⟫ ↪ ⟪ α₀ ⟫
  leg = h , h-inj

-- =====================================================================
-- SECTION 4.  THE DEBT.  The consumer, at the whole site-fixed
-- induction: the predicate Q fixes the injection's TARGET at the
-- site α₀ (compare Upper's own predicate `P`,
-- src/L/StageCardinal.lagda.md:530-532, which fixes it at each step's
-- OWN ordinal and thereby buys the band), and the step is the
-- assembly of section 3.  (iii) is the ONLY remaining hypothesis:
-- the ordinality and the infinity of the site are given, the band
-- stays abstract, and the pairing is spent once, at the site.  The
-- predicate is [LJ-1.617]'s Q (agents/tasks/LJ-1-617/Probe617.agda:
-- 464-465) spelled at the site, and [LJ-1.621] delivered this same
-- obligation from this same fiber (agents/tasks/LJ-1-621/Probe621.
-- agda:128-129), its step re-derived probe-local; this file's step
-- reads the landed table instead.
-- =====================================================================

Q : S → Type (ℓ-suc ℓ)
Q γ = IsOrd γ → ⟨ γ ∈ˢ sucV α₀ ⟩ → ⟪ Lset γ ⟫ ↪ ⟪ α₀ ⟫

step : SiteFiber α₀ → (γ : S) → ((δ : S) → ⟨ δ ∈ˢ γ ⟩ → Q δ) → Q γ
step iii γ IH oγ γ∈suc = DebtStep.leg iii γ oγ γ∈suc IH


class-pred-debt : SiteFiber α₀ → (γ : V ℓ) → Q γ
class-pred-debt iii = ∈-induction (step iii)

-- THE BILL'S OWN READING: the consumer at γ = α₀, the one grain
-- src/L/BoundedSubset.lagda.md:1513 consumes, at the site.
site-leg-α : SiteFiber α₀ → ⟪ Lset α₀ ⟫ ↪ ⟪ α₀ ⟫
site-leg-α iii = class-pred-debt iii α₀ oα₀ (self∈sucV α₀)

-- =====================================================================
-- SECTION 5.  INGREDIENT (iv), READ AT THE BRANCH.  The landed row
-- (src/L/BoundedSubset.lagda.md:1512-1518), named in term position at
-- one certified instantiation of the metered module (src/L/
-- BoundedSubset.lagda.md:1743-1753): the object-language graph of the
-- strictly-infinite branch of the induction hypothesis.  The
-- ambient step of section 3 consumes that branch's ambient mirror —
-- `ihm` — at every member stage; this section reads the object-
-- language row that CERTIFIES it.  Its domain, restated from the
-- source:
--   (β : V ℓ) (oβ : IsOrd β) (β∈suc : ⟨ β ∈ˢ sucV α′ ⟩)
--     (infβ : ⟨ β ∈ˢ ω ⟩ → Empty.⊥)
--     (IH : (δ : V ℓ) → ⟨ δ ∈ˢ β ⟩ → B634.SC.Upper.P δ)
--     (m : ⟪ β ⟫) (ω∈δ : ⟨ ω ∈ˢ (⟪ β ⟫↪ m) ⟩)
--   → B634.RGraph.At.RecGraph∞ β oβ β∈suc infβ IH m ω∈δ
-- The green term that implements it is [LJ-1.608]'s; restated, not
-- re-proved, here.
-- =====================================================================

module IV-read (κ : S) (ordκ : IsOrd κ)
               (cardκ : LB.IsCardinal κ)
               (κ∉ω : ⟨ κ ∈ˢ ω ⟩ → Empty.⊥)
               (α′ : S) (ordα′ : IsOrd α′) (α′∈κ : ⟨ α′ ∈ˢ κ ⟩)
               (α′∉ω : ⟨ α′ ∈ˢ ω ⟩ → Empty.⊥)
               (band′ : SqParam α′) where

  -- One certified instantiation of the metered module.
  module B634 = LB.BSA634
    κ ordκ cardκ κ∉ω α′ ordα′ α′∈κ α′∉ω band′

  -- The landed row, named.
  row-iv = B634.RGraph.class-pred-iv

-- =====================================================================
-- SECTION 6.  INGREDIENT (v), NAMED AT THE RANGE.  The landed row
-- (src/L/Choice/Faithful.lagda.md:962-963), named at one
-- instantiation of the Faithful chapter: the carrier's key at the
-- certified stage, into the constructible carrier.  The ambient
-- consumer of section 3 does NOT consume it: the tree's own
-- class-pred witness (src/L/StageCardinal.lagda.md:329-334) carries
-- the formula itself, and [LJ-1.617]'s green step (agents/tasks/
-- LJ-1-617/Probe617.agda:313-462) has no key row at all.  The row is
-- the object-language ingredient of the table; it is named here so
-- the table is read whole, and its type is recorded:
--   (δ : V ℓ) (oδ : IsOrd δ) {n : ℕ} → Formula ⟪ Lset δ ⟫ n → Sʟ
-- The green term that implements it is in the chapter; named, not
-- re-proved, here.
-- =====================================================================

row-v : (δ : V ℓ) (oδ : IsOrd δ) {n : ℕ} → Formula ⟪ Lset δ ⟫ n → SLv.S
row-v = F637.class-pred-v
