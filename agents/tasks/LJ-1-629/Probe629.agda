{-# OPTIONS --cubical --safe --guardedness #-}

-- [LJ-1.629]  IS THE BILL'S SITE AN INITIAL ORDINAL?
--
-- THE OBLIGATION.  `site-is-init : <the bill's own site hypotheses> →
-- Init <the site>`, with `Init` as src/L/Ordinal/SquareLaw.lagda.md:
-- 692-698 states it.  The site is `fst κ` and the bill's own three
-- hypotheses on κ are [LJ-1.589]'s (agents/tasks/LJ-1-589/
-- Probe589.agda:243-247): IsOrd (fst κ), IsCardinalL κ and the trophy
-- clause ⟨ fst κ ∈ˢ ω ⟩ → Empty.⊥.  NO TERM OF THIS FILE CARRIES THE
-- OBLIGATION NAME `site-is-init`, because the target is FALSE at a
-- site the bill admits: see `target-false` below.  The stop is stated
-- in agents/tasks/LJ-1-629/review-of-site-is-init.md.
--
-- THIS FILE CARRIES NO HOLE AND NO POSTULATE, so every line of it is a
-- measurement and not a claim ([LJ-1.533]'s discipline).  Nothing
-- lands in src/.  No commit, no push.
--
-- WHAT THIS FILE MEASURES, IN ONE LINE EACH.
--
--   Section 0.  THE OBLIGATION'S TYPE, restated at the bill's grain,
--               and its shadow, tied to the alone-typechecked W3.
--   Section 1.  THE FOUR CONJUNCTS, one block each: 1 given, 2 refuted
--               at ω, 3 payable given 2, 4 priced by what it needs.
--   Section 2.  ROW 1 COMPARED, and the route the brief prices,
--               closed as an implication and green.
--
-- W3 IS `agents/tasks/LJ-1-629/runs/W3.agda`, written first and
-- typechecked alone (runs/w3-2.out at 1.47 s and, after a name-only
-- rename, runs/w3-3.out at 1.86 s, both EXIT=0 under the two-minute
-- cap).
--
-- CALIBER.  The program set GHCRTS on this pane.  I did not set it.
-- One Agda process at a time.  ONE heap wall occurred and was routed
-- around by restructuring in the same dispatch; see the shape note at
-- section 1.3 and runs/final-5.out.

open import Base.Prelude
open import Base.Truth
open import Base.Classical using ( LEM )

module LJ-1-629.Probe629 {ℓ : Level} (lem : LEM (ℓ-suc ℓ)) where

open import FOL.ZFStructure using ( module hPropStructure )
open import V.Hierarchy {ℓ} using ( 𝒮ᵥ; ∈-irrefl )
open import V.Model {ℓ} using ( self∈sucV; ∈sucV-elim )
open import Cubical.HITs.CumulativeHierarchy.Constructions
  using ( module InfinitySet )
open InfinitySet using ( ω; sucV; #_ )
open import Cubical.HITs.CumulativeHierarchy.Properties using ( ⟪_⟫ )
open import Cubical.Data.Sigma using ( Σ-syntax; Σ≡Prop )
open import Cubical.Data.Sum using ( _⊎_; inl; inr )
import Cubical.Data.Empty as Empty
import Cubical.HITs.PropositionalTruncation as PT
open PT using ( ∣_∣₁; ∥_∥₁; squash₁ )
open import L.Constructible {ℓ} using ( 𝒮ʟ; isL; isL-trans; IsOrd )
open import L.Ordinal {ℓ} using ( ω-ord; suc-ord; mem-ord; #∈ω )
open import L.Ordinal.Linear {ℓ} lem using ( Tri; ord-tri )
open import L.Ordinal.SquareLaw {ℓ} lem
  using ( Init; sq; via-col-square; module FiniteBase )
open FiniteBase using ( ω-mem→numeral )
open import L.Axioms.Infinity {ℓ} lem using ( ωʟ )
open import L.Cardinal {ℓ} lem using ( IsCardinalL; InjCode; _↪_ )
open import L.CodedShift {ℓ} lem using ( shift-coded )
open import L.Axioms.Numerals {ℓ} using ( sucʟ; sucʟ-fst )
open import L.BoundedSubset {ℓ} lem using ( IsCardinal )
open import L.GCH {ℓ} lem using ( SuccCardL )

open hPropStructure 𝒮ᵥ using ( S; _∈ˢ_ )
module SL = hPropStructure 𝒮ʟ
import LJ-1-629.runs.W3
module W3 = LJ-1-629.runs.W3 lem

-- =====================================================================
-- SECTION 0.  THE OBLIGATION'S TYPE, at the bill's own grain.
--
--   SiteIsInit is the brief's obligation verbatim: the three
--   hypotheses [LJ-1.589] fixed, the conclusion `Init` at `fst κ`.
--   It is NOT inhabited here.  `site-init→site4` ties it to the
--   alone-typechecked W3 (runs/W3.agda), so the probe's spelling and
--   the W3 spelling cannot drift.
-- =====================================================================

SiteIsInit : Type (ℓ-suc ℓ)
SiteIsInit =
    (κ : SL.S) → IsOrd (fst κ) → IsCardinalL κ
  → (⟨ fst κ ∈ˢ ω ⟩ → Empty.⊥)
  → Init (fst κ)

obligation→w3 : SiteIsInit → W3.SiteFrame
obligation→w3 = W3.site-init→site4

-- =====================================================================
-- SECTION 1.  THE FOUR CONJUNCTS (D-10: priced before any proof).
--
--   Init α = IsOrd α                                  (conjunct 1)
--          × ⟨ ω ∈ˢ α ⟩                               (conjunct 2)
--          × ((γ : S) → ⟨ γ ∈ˢ α ⟩ → ⟨ sucV γ ∈ˢ α ⟩) (conjunct 3)
--          × <α injects into no infinite member's square> (conjunct 4)
--
--   src/L/Ordinal/SquareLaw.lagda.md:692-698.
-- =====================================================================

-- ---------------------------------------------------------------------
-- 1.1  CONJUNCT 1, IsOrd (fst κ): GIVEN, verbatim.  The bill's first
--      hypothesis IS the conjunct.
-- ---------------------------------------------------------------------

c1-given : (κ : SL.S) → IsOrd (fst κ) → IsCardinalL κ
         → (⟨ fst κ ∈ˢ ω ⟩ → Empty.⊥) → IsOrd (fst κ)
c1-given κ oκ _ _ = oκ

-- ---------------------------------------------------------------------
-- 1.2  CONJUNCT 2, ⟨ ω ∈ˢ fst κ ⟩: NOT GIVEN, AND FALSE AT A SITE THE
--      BILL ADMITS.  The trophy clause excludes fst κ ∈ˢ ω; it does
--      NOT exclude fst κ ≡ ω.  At κ := ωʟ the first and third
--      hypotheses hold by two terms below, and the conjunct refutes
--      itself: ω ∈ˢ ω is impossible.  [LJ-1.116] measured the same
--      fact at the demand side (archive/dev/LJ-dispatch-index.md:192,
--      "Init is false at omega and at successors"); this row
--      re-measures it AT THE BILL'S SITE.
-- ---------------------------------------------------------------------

init-ω-false : Init (fst ωʟ) → Empty.⊥
init-ω-false iω = ∈-irrefl ω (fst (snd iω))

ord-ωʟ : IsOrd (fst ωʟ)
ord-ωʟ = ω-ord

∉-ωʟ : ⟨ fst ωʟ ∈ˢ ω ⟩ → Empty.⊥
∉-ωʟ = ∈-irrefl ω

-- THE OBLIGATION IS REFUTABLE, modulo the one fact it hangs on:
-- IsCardinalL ωʟ.  That fact is TRUE (a code at a member δ ∈ ω reads
-- back to an ambient injection ω ↪ δ with δ ≡ # n, and the tree's own
-- pigeonhole at src/L/Ordinal/SquareLaw.lagda.md:604-660 refutes it);
-- building it is priced in the report, not here.
target-false : IsCardinalL ωʟ → SiteIsInit → Empty.⊥
target-false cω h = init-ω-false (h ωʟ ord-ωʟ cω ∉-ωʟ)

-- ---------------------------------------------------------------------
-- 1.3  CONJUNCT 3, successor closure at the site: PAYABLE FROM THE
--      BILL GIVEN CONJUNCT 2.  The row takes ⟨ ω ∈ˢ fst κ ⟩ as an
--      explicit hypothesis, so the dependency is visible: closure at
--      the numerals rides on ω being a member (transitivity), and
--      closure at an infinite member rides on IsCardinalL plus the
--      tree's own coded successor shift (shift-coded,
--      src/L/CodedShift.lagda.md:37-41).
--
--      SHAPE NOTE (the first shape walled, and the cure).  A first
--      version wrote this row as one term with two `with`
--      abstractions inside nested `where` closures: it died at the
--      heap cap, 56 s, 2.4 GB, exit 251 (runs/final-5.out).  Two
--      restructures at the same caliber cured it, and both are
--      measured: first, the trichotomy values became ARGUMENTS of
--      plain case functions instead of `with` scrutinees
--      (runs/bisect-1.out green at the pieces); second, every
--      `mem-ord` application passes the implicit {A} explicitly, the
--      tree's own idiom (src/L/Hierarchy.lagda.md:171), because
--      leaving it implicit left isTransV metas unsolved
--      (runs/bisect-5.out, runs/bisect-7.out).  Green whole:
--      runs/final-9.out, 2.74 s.
-- ---------------------------------------------------------------------

-- The numeral branch: a member of ω is a numeral, and numerals step
-- inside ω, which sits inside the site by the row's own hypothesis.
c3-numeral : (κ : SL.S) (oκ : IsOrd (fst κ)) → ⟨ ω ∈ˢ fst κ ⟩
           → (γ : S) → ⟨ γ ∈ˢ ω ⟩ → ⟨ sucV γ ∈ˢ fst κ ⟩
c3-numeral κ oκ ω∈κ γ γ∈ω =
  PT.rec (snd (sucV γ ∈ˢ fst κ)) hit (ω-mem→numeral γ γ∈ω)
  where
    hit : Σ[ n ∈ ℕ ] (γ ≡ # n) → ⟨ sucV γ ∈ˢ fst κ ⟩
    hit (n , p) =
      subst (λ w → ⟨ sucV w ∈ˢ fst κ ⟩) (sym p)
        (oκ .fst (#∈ω (suc n)) ω∈κ)

-- The infinite branch, as a case function on the site trichotomy.
-- The left case is the goal; the right case contradicts irreflexivity;
-- the middle case makes the site a coded successor, and IsCardinalL
-- refutes the shift code the tree already carries.
c3-inf : (κ : SL.S) (oκ : IsOrd (fst κ)) (cκ : IsCardinalL κ)
       → (γ : S) (oγ : IsOrd γ) (γ∈κ : ⟨ γ ∈ˢ fst κ ⟩)
       → (⟨ γ ∈ˢ ω ⟩ → Empty.⊥) → ((k : ℕ) → ⟨ (# k) ∈ˢ γ ⟩)
       → Tri (sucV γ) (fst κ)
       → ⟨ sucV γ ∈ˢ fst κ ⟩
c3-inf κ _ cκ γ oγ γ∈κ γ∉ω numerals (inl s) = s
c3-inf κ _ cκ γ oγ γ∈κ γ∉ω numerals (inr (inl p)) =
  Empty.rec (subst IsCardinalL κ≡suc cκ γ' γ'∈suc sc)
  where
    isLγ : ⟨ isL γ ⟩
    isLγ = isL-trans γ∈κ (snd κ)
    γ' : SL.S
    γ' = γ , isLγ
    γ'∈suc : ⟨ fst γ' ∈ˢ fst (sucʟ γ') ⟩
    γ'∈suc = subst (λ w → ⟨ γ ∈ˢ w ⟩) (sym (sucʟ-fst γ')) (self∈sucV γ)
    sc : ∥ Σ[ F ∈ SL.S ] InjCode F (sucʟ γ') γ' ∥₁
    sc = shift-coded γ' oγ γ∉ω numerals
    κ≡suc : κ ≡ sucʟ γ'
    κ≡suc = Σ≡Prop (λ x → snd (isL x)) (sym p ∙ sym (sucʟ-fst γ'))
c3-inf κ _ _ γ oγ γ∈κ _ _ (inr (inr q)) =
  ∈sucV-elim {A = γ} {x = fst κ} (snd (sucV γ ∈ˢ fst κ)) q
    (λ κ∈γ → Empty.rec (∈-irrefl γ (oγ .fst γ∈κ κ∈γ)))
    (λ p → Empty.rec (∈-irrefl γ (subst (λ w → ⟨ γ ∈ˢ w ⟩) p γ∈κ)))

c3-triω-inr : (κ : SL.S) (oκ : IsOrd (fst κ)) (cκ : IsCardinalL κ)
            → ⟨ ω ∈ˢ fst κ ⟩ → (γ : S) → ⟨ γ ∈ˢ fst κ ⟩
            → ((γ ≡ ω) ⊎ ⟨ ω ∈ˢ γ ⟩) → ⟨ sucV γ ∈ˢ fst κ ⟩
c3-triω-inr κ oκ cκ ω∈κ γ γ∈κ (inl γ≡ω) =
  c3-inf κ oκ cκ γ (mem-ord {A = fst κ} oκ γ γ∈κ) γ∈κ
    (λ h → ∈-irrefl ω (subst (λ w → ⟨ w ∈ˢ ω ⟩) γ≡ω h))
    (λ k → subst (λ w → ⟨ (# k) ∈ˢ w ⟩) (sym γ≡ω) (#∈ω k))
    (ord-tri (sucV γ) (suc-ord (mem-ord {A = fst κ} oκ γ γ∈κ)) (fst κ) oκ)
c3-triω-inr κ oκ cκ ω∈κ γ γ∈κ (inr ω∈γ) =
  c3-inf κ oκ cκ γ (mem-ord {A = fst κ} oκ γ γ∈κ) γ∈κ
    (λ h → ∈-irrefl γ (mem-ord {A = fst κ} oκ γ γ∈κ .fst h ω∈γ))
    (λ k → mem-ord {A = fst κ} oκ γ γ∈κ .fst (#∈ω k) ω∈γ)
    (ord-tri (sucV γ) (suc-ord (mem-ord {A = fst κ} oκ γ γ∈κ)) (fst κ) oκ)

-- The top row: trichotomy against ω first, as a case function.
c3-triω : (κ : SL.S) (oκ : IsOrd (fst κ)) (cκ : IsCardinalL κ)
        → ⟨ ω ∈ˢ fst κ ⟩ → (γ : S) → ⟨ γ ∈ˢ fst κ ⟩
        → Tri γ ω → ⟨ sucV γ ∈ˢ fst κ ⟩
c3-triω κ oκ cκ ω∈κ γ γ∈κ (inl γ∈ω) = c3-numeral κ oκ ω∈κ γ γ∈ω
c3-triω κ oκ cκ ω∈κ γ γ∈κ (inr t) =
  c3-triω-inr κ oκ cκ ω∈κ γ γ∈κ t

c3-payable :
    (κ : SL.S) (oκ : IsOrd (fst κ)) (cκ : IsCardinalL κ)
  → (⟨ fst κ ∈ˢ ω ⟩ → Empty.⊥)
  → ⟨ ω ∈ˢ fst κ ⟩
  → (γ : S) → ⟨ γ ∈ˢ fst κ ⟩ → ⟨ sucV γ ∈ˢ fst κ ⟩
c3-payable κ oκ cκ _ ω∈κ γ γ∈κ =
  c3-triω κ oκ cκ ω∈κ γ γ∈κ (ord-tri γ (mem-ord {A = fst κ} oκ γ γ∈κ) ω ω-ord)

-- ---------------------------------------------------------------------
-- 1.4  CONJUNCT 4, the ambient non-injection: MISSING AT THE STATED
--      GRAIN, and this row is the measurement of what it needs.
--      IsCardinalL refutes CODED injections only
--      (src/L/Cardinal.lagda.md:238-241); the conjunct asks that NO
--      ambient injection send ⟪ fst κ ⟫ into the square of an
--      infinite member.  The row: the conjunct follows from ambient
--      cardinality AT THE SITE plus a pairing at every infinite
--      MEMBER of the site.  Both ingredients are named as hypotheses;
--      neither is discharged here.
-- ---------------------------------------------------------------------

-- A pairing at one ordinal, the site-fiber shape ([LJ-1.617]'s
-- measurement: agents/tasks/LJ-1-617/Probe617.agda:500-502).
BandBelow : S → Type (ℓ-suc ℓ)
BandBelow α =
    (β : S) → IsOrd β → ⟨ β ∈ˢ α ⟩ → ⟨ ω ∈ˢ β ⟩
  → Σ[ f ∈ (⟪ β ⟫ × ⟪ β ⟫ → ⟪ β ⟫) ]
      ((u v : ⟪ β ⟫ × ⟪ β ⟫) → f u ≡ f v → u ≡ v)

c4-from : (κ : SL.S) → IsOrd (fst κ)
        → IsCardinal (fst κ) → BandBelow (fst κ)
        → W3.Init4 (fst κ)
c4-from κ _ cardκ band β oβ β∈κ ω∈β f finj =
  cardκ β β∈κ (g , g-inj)
  where
    p = band β oβ β∈κ ω∈β
    g : ⟪ fst κ ⟫ → ⟪ β ⟫
    g m = fst p (f m)
    g-inj : (m n : ⟪ fst κ ⟫) → g m ≡ g n → m ≡ n
    g-inj m n e = finj m n (snd p (f m) (f n) e)

-- =====================================================================
-- SECTION 2.  ROW 1 COMPARED, AND THE ROUTE.
--
--   The brief's question: is ingredient (iii) the same demand as row 1
--   of [LJ-1.564]'s bill?  Row 1 is quoted VERBATIM from
--   agents/tasks/LJ-1-550/Probe550.agda:301-302.  The comparison rows
--   measure the two demands' shapes; the verdict is in the report.
-- =====================================================================

-- Row 1: ambient cardinality AT THE SUCCESSOR.
Row1 : Type (ℓ-suc ℓ)
Row1 = (κ δ : SL.S) → SuccCardL δ κ → IsCardinal (fst δ)

-- Ambient cardinality at EVERY internal cardinal pays row 1 outright
-- (the successor δ is an internal cardinal, SuccCardL's second
-- conjunct, src/L/GCH.lagda.md:51-53).  So row 1 is a WEAKENING of
-- that instance family, and it never covers a site that is nobody's
-- successor: ω is one, and every limit cardinal above it is another.
ambient-all→row1 : ((μ : SL.S) → IsCardinal (fst μ)) → Row1
ambient-all→row1 all κ δ sc = all δ

-- And the route the brief prices, closed and green AS AN IMPLICATION:
-- if the site were initial, the tree's own theorem pays the site fiber
-- (via-col-square, src/L/Ordinal/SquareLaw.lagda.md:960-961).  The
-- route is real; its premise is what this task measures false.
route : SiteIsInit
      → (κ : SL.S) → IsOrd (fst κ) → IsCardinalL κ
      → (⟨ fst κ ∈ˢ ω ⟩ → Empty.⊥) → sq (fst κ)
route h κ oκ cκ κ∉ω = via-col-square (fst κ) (h κ oκ cκ κ∉ω)
