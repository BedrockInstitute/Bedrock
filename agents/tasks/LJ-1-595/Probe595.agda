{-# OPTIONS --cubical --safe --guardedness #-}

-- [LJ-1.595]  Clause (ii) of the level-hood certificate.
--
-- W3 IS SECTION 1 and the brief ordered it written FIRST and typechecked
-- ALONE.  The slice is agents/tasks/LJ-1-595/runs/W3.agda; its runs are
-- runs/w3-1.out (exit 42, an import that does not exist) and runs/w3-2.out
-- (exit 0).
--
-- Nothing is postulated.  Nothing lands in src/.  No hole.
--
-- CALIBER.  The program set GHCRTS="-A64m -I0 -M8g" on this pane.  I did
-- not set it.  One Agda process at a time.
--
-- [LJ-1.582] IS NOT IN THE TREE.  `ls agents/tasks/` returns no LJ-1-582
-- directory in this worktree, so nothing of clause (i) is reused and the
-- brief's instruction "build clause (ii) alone" is the one in force.

open import Base.Prelude
open import Base.Truth
open import Base.Classical using ( LEM )

module LJ-1-595.Probe595 {ℓ : Level} (lem : LEM (ℓ-suc ℓ)) where

open import FOL.ZFStructure using ( module hPropStructure )
open import FOL.Syntax using ( Formula; con; var; _∈̇_; _≐_; _∧̇_; ∃̇_ )
open import FOL.Manipulation.Relabelling
  using ( embed; mapFo; mapFo-comp; mapΔ₀; ⊨-map )
import Cubical.Data.Empty as Empty
open import V.Hierarchy {ℓ} using ( 𝒮ᵥ; ∈-induction )
open import V.Presentation {ℓ} using ( member )
open import V.Collapse {ℓ} using ( module Collapse )
open import L.Constructible {ℓ}
  using ( IsOrd; Lset; isTransV; isPropIsTransV; 𝒟ₒ; Lset-in; Lset-out )
open import V.Model {ℓ} using ( self∈sucV )
open import L.Ordinal {ℓ} using ( mem-ord; suc-ord )
open import L.Ordinal.Stages {ℓ} lem
  using ( ord∈Lset-suc; ord∈Lset→∈; Lset-cumul )
open import L.BoundedSubset {ℓ} lem
  using ( module HullStage; isOrdAt; Δ₀-isOrdAt; module Amb )
open import Cubical.HITs.CumulativeHierarchy.Constructions
  using ( module InfinitySet; ∅ )
open import Cubical.HITs.CumulativeHierarchy.Properties using ( ⟪_⟫↪; ∈∈ₛ )
open import Cubical.Data.Sigma using ( _×_ )
import Cubical.HITs.PropositionalTruncation as PT
open PT using ( ∥_∥₁; ∣_∣₁ )
open InfinitySet {ℓ} using ( sucV )

-- THE PREDECESSOR, BY THE TYPE IT DELIVERED (coder clause, owner
-- 2026-08-20).  [LJ-1.578] is a NO-GO on `cohyps-supplied`
-- (lj-1.578-report.md:21-23) and that stop is about `CoHyps`, not about
-- the three clauses it named.  Clause (ii) is one of those three, it is a
-- TYPE in that probe's green module, and this file takes it from there
-- rather than restating it.
import LJ-1-578.Probe578 {ℓ} lem as P578

open TruthAlgebra (hPropAlgebra (ℓ-suc ℓ))
module SV = hPropStructure 𝒮ᵥ
open SV using ( _∈ˢ_ )

-- =====================================================================
-- SECTION 1.  W3.  THE WIDEST UNMEASURED TERM, TYPE ONLY.
--
--   The brief names it "the covering ordinal itself", and asks whether it
--   STATES at the stage's inner world at all.  IT DOES: the type below is
--   runs/W3.agda:52-58 letter for letter, and runs/w3-2.out is exit 0.
--
--   It is clause (ii)'s own adequacy (Probe578.agda:249-251) with the
--   FORMULA removed and the witness existentially bound.  Section 5
--   INHABITS it, so the object is free and only the formula is not.
-- =====================================================================

module Cover (lam : SV.S) (ordλ : IsOrd lam)
             (succλ : (d : SV.S) → ⟨ d ∈ˢ lam ⟩ → ⟨ sucV d ∈ˢ lam ⟩)
             (X : SV.S)
             (X⊆Lλ : (z : SV.S) → ⟨ z ∈ˢ X ⟩ → ⟨ z ∈ˢ Lset lam ⟩)
             (∅∈λ : ⟨ ∅ ∈ˢ lam ⟩) where

  module HS = HullStage lam ordλ succλ X X⊆Lλ ∅∈λ
  module T = HS.H.T

  -- the covering ordinal of a hull member, at the stage's inner world,
  -- TYPE ONLY
  CoveringOrdinal : Type (ℓ-suc ℓ)
  CoveringOrdinal =
    (c : T.Code)
    → ∥ Σ[ a ∈ HS.ASt.SL ]
        ( IsOrd (HS.C.π (fst a))
        × ⟨ fst (T.val c) ∈ˢ Lset (fst a) ⟩ ) ∥₁

-- =====================================================================
-- SECTION 2.  THE TWO CLAUSES, TAKEN AND NOT RESTATED.
--
--   D-10 asks what differs between clause (i) and clause (ii).  A
--   comparison of two RESTATEMENTS answers nothing, so both are named
--   here at [LJ-1.578]'s own module and the report reads them at that
--   file's lines.
-- =====================================================================

ClauseI : (lam : SV.S) (ordλ : IsOrd lam)
          (succλ : (d : SV.S) → ⟨ d ∈ˢ lam ⟩ → ⟨ sucV d ∈ˢ lam ⟩)
          (X : SV.S)
          (X⊆Lλ : (z : SV.S) → ⟨ z ∈ˢ X ⟩ → ⟨ z ∈ˢ Lset lam ⟩)
          (∅∈λ : ⟨ ∅ ∈ˢ lam ⟩) → Type (ℓ-suc ℓ)
ClauseI = P578.Cert.DefinesLevel

ClauseII : (lam : SV.S) (ordλ : IsOrd lam)
           (succλ : (d : SV.S) → ⟨ d ∈ˢ lam ⟩ → ⟨ sucV d ∈ˢ lam ⟩)
           (X : SV.S)
           (X⊆Lλ : (z : SV.S) → ⟨ z ∈ˢ X ⟩ → ⟨ z ∈ˢ Lset lam ⟩)
           (∅∈λ : ⟨ ∅ ∈ˢ lam ⟩) → Type (ℓ-suc ℓ)
ClauseII = P578.Cert.DefinesCover

-- =====================================================================
-- SECTION 3.  THE COLLAPSE SENDS AN ORDINAL TO AN ORDINAL.
--
--   Clause (ii) concludes `IsOrd (π a)` and NOT `IsOrd a`, so a witness
--   must be carried across the collapse.  `V.Collapse` delivers no such
--   lemma: `π-member` (src/V/Collapse.lagda.md:63-73) forgets that the
--   pre-image is a MEMBER of the argument, and that is exactly what an
--   induction on the argument needs.  So the read is re-derived here at
--   the same computation law, and the lemma is proved on top of it.
--
--   IT IS GENERAL: no hull, no stage, no hypothesis on the carrier.
-- =====================================================================

module CollapseOrd (Mc : SV.S) where

  module C = Collapse Mc

  -- the read `π-member` does not give: the pre-image is a member of the
  -- argument AND of the carrier
  π-mem : (x z : SV.S) → ⟨ z ∈ˢ C.π x ⟩
        → ∥ Σ[ y ∈ SV.S ]
             (⟨ y ∈ˢ x ⟩ × ⟨ y ∈ˢ Mc ⟩ × (C.π y ≡ z)) ∥₁
  π-mem x z z∈ = PT.map mk (subst (λ w → ⟨ z ∈ˢ w ⟩) (C.π-compute x) z∈)
    where
    mk : Σ[ p ∈ C.Fiber x ] (C.π (⟪ x ⟫↪ (p .fst)) ≡ z)
       → Σ[ y ∈ SV.S ] (⟨ y ∈ˢ x ⟩ × ⟨ y ∈ˢ Mc ⟩ × (C.π y ≡ z))
    mk (p , q) = ⟪ x ⟫↪ (p .fst)
               , ( member x (p .fst)
                 , ∈∈ₛ {a = ⟪ x ⟫↪ (p .fst)} {b = Mc} .snd (p .snd)
                 , q )

  π-ord : (x : SV.S) → IsOrd x → IsOrd (C.π x)
  π-ord = ∈-induction {P = λ x → IsOrd x → IsOrd (C.π x)} step
    where
    step : (x : SV.S) → (∀ y → ⟨ y ∈ˢ x ⟩ → IsOrd y → IsOrd (C.π y))
         → IsOrd x → IsOrd (C.π x)
    step x IH ox = tr , mems
      where
      tr : isTransV (C.π x)
      tr {x = z} {y = w} w∈z z∈πx =
        PT.rec (snd (w ∈ˢ C.π x)) go (π-mem x z z∈πx)
        where
        go : Σ[ y ∈ SV.S ] (⟨ y ∈ˢ x ⟩ × ⟨ y ∈ˢ Mc ⟩ × (C.π y ≡ z))
           → ⟨ w ∈ˢ C.π x ⟩
        go (y , y∈x , y∈M , e) =
          PT.rec (snd (w ∈ˢ C.π x)) go₂
            (π-mem y w (subst (λ v → ⟨ w ∈ˢ v ⟩) (sym e) w∈z))
          where
          go₂ : Σ[ u ∈ SV.S ] (⟨ u ∈ˢ y ⟩ × ⟨ u ∈ˢ Mc ⟩ × (C.π u ≡ w))
              → ⟨ w ∈ˢ C.π x ⟩
          go₂ (u , u∈y , u∈M , e₂) =
            subst (λ v → ⟨ v ∈ˢ C.π x ⟩) e₂
              (C.π∈-fwd x u (ox .fst u∈y y∈x) u∈M)
      mems : (z : SV.S) → ⟨ z ∈ˢ C.π x ⟩ → isTransV z
      mems z z∈πx = PT.rec (isPropIsTransV z) go (π-mem x z z∈πx)
        where
        go : Σ[ y ∈ SV.S ] (⟨ y ∈ˢ x ⟩ × ⟨ y ∈ˢ Mc ⟩ × (C.π y ≡ z))
           → isTransV z
        go (y , y∈x , y∈M , e) =
          subst isTransV e (IH y y∈x (mem-ord {A = x} ox y y∈x) .fst)

-- =====================================================================
-- SECTION 4.  THE ORDINAL FORMULA, READ AT THE STAGE'S INNER WORLD.
--
--   Clause (ii) must PROVE that its witness collapses to an ordinal,
--   where clause (i) is GIVEN that its argument does.  The only route
--   from a formula to that fact is Δ₀ absoluteness at the stage, and
--   `isOrdAt` (src/L/BoundedSubset.lagda.md:795-801) is the tree's own
--   Δ₀ spelling of "x is an ordinal".
--
--   THE MEASUREMENT THE BRIEF ORDERED.  [LJ-1.562] paid `AtStage`'s two
--   hypotheses at a DIFFERENT formula and a DIFFERENT site
--   (lj-1.562-report.md:1-6), so nothing of it transfers (AGENTS.md:45).
--   Re-measured here: at THIS formula the Δ₀ witness is delivered
--   (`Δ₀-isOrdAt`) and the constant count is ZERO, so the boundedness
--   hypothesis that task priced does not arise at all.  What the site
--   costs instead is the three-step relabelling below, because the hull
--   reads its formulas at the CODE alphabet and `abs₀` reads them at the
--   stage's.
-- =====================================================================

module CoverAt (lam : SV.S) (ordλ : IsOrd lam)
               (succλ : (d : SV.S) → ⟨ d ∈ˢ lam ⟩ → ⟨ sucV d ∈ˢ lam ⟩)
               (X : SV.S)
               (X⊆Lλ : (z : SV.S) → ⟨ z ∈ˢ X ⟩ → ⟨ z ∈ˢ Lset lam ⟩)
               (∅∈λ : ⟨ ∅ ∈ˢ lam ⟩) where

  module HS = HullStage lam ordλ succλ X X⊆Lλ ∅∈λ
  module T = HS.H.T
  module AB = HS.ASt.AbsL
  module CO = CollapseOrd HS.M

  ordFo : Formula T.Code 1
  ordFo = embed isOrdAt

  ordSL : Formula HS.ASt.SL 1
  ordSL = embed isOrdAt

  -- relabelling the code alphabet along `val` is the same embedding.
  -- The empty alphabet makes the two interpretations equal, and the
  -- endpoints are written out because `Empty.rec*` proves anything and
  -- would leave them unsolved.
  -- the stage's projection, named so that `⊨-map` can see which Sigma
  -- it projects; passing `fst` bare leaves that meta unsolved
  prj : HS.ASt.SL → SV.S
  prj = fst

  private
    ι-irr : (λ (b : Empty.⊥* {ℓ-suc ℓ}) → T.val (Empty.rec* b))
          ≡ (λ (b : Empty.⊥* {ℓ-suc ℓ}) → Empty.rec* b)
    ι-irr = funExt (λ b → Empty.rec* b)

  ord-relabel : mapFo T.val ordFo ≡ ordSL
  ord-relabel = mapFo-comp Empty.rec* T.val isOrdAt
              ∙ cong (λ f → mapFo f isOrdAt) ι-irr

  private
    step-code : (a : HS.ASt.SL)
              → ((a ∷ []) AB.⊨ᵐ (mapFo T.val ordFo)) ≡ ((a ∷ []) T.⊨c ordFo)
    step-code a = ⊨-map (hPropAlgebra (ℓ-suc ℓ)) AB.𝒮M T.val id ordFo (a ∷ [])

    step-amb : (a : HS.ASt.SL)
             → ((fst a ∷ []) AB.⊨ᵛ ordSL) ≡ ((fst a ∷ []) Amb.⊨ₚ isOrdAt)
    step-amb a =
      ⊨-map (hPropAlgebra (ℓ-suc ℓ)) 𝒮ᵥ Empty.rec* prj isOrdAt (fst a ∷ [])

    step-abs : (a : HS.ASt.SL)
             → ((a ∷ []) AB.⊨ᵐ ordSL) ≡ ((fst a ∷ []) AB.⊨ᵛ ordSL)
    step-abs a = AB.abs₀ (mapΔ₀ Empty.rec* Δ₀-isOrdAt) (a ∷ [])

  -- the whole chain, as ONE equation between the two readings
  ord-read : (a : HS.ASt.SL)
           → ((a ∷ []) T.⊨c ordFo) ≡ ((fst a ∷ []) Amb.⊨ₚ isOrdAt)
  ord-read a = sym (step-code a)
             ∙ cong (λ ψ → (a ∷ []) AB.⊨ᵐ ψ) ord-relabel
             ∙ step-abs a ∙ step-amb a

  ord-out : (a : HS.ASt.SL) → ⟨ (a ∷ []) T.⊨c ordFo ⟩ → IsOrd (fst a)
  ord-out a h = Amb.isOrdAt-out (fst a) (subst ⟨_⟩ (ord-read a) h)

  ord-in : (a : HS.ASt.SL) → IsOrd (fst a) → ⟨ (a ∷ []) T.⊨c ordFo ⟩
  ord-in a o = subst ⟨_⟩ (sym (ord-read a)) (Amb.isOrdAt-in (fst a) o)

  -- ===================================================================
  -- SECTION 5.  THE COVERING ORDINAL EXISTS.  W3, INHABITED.
  --
  --   Every member of the stage's inner world is covered by an ORDINAL
  --   of that same inner world, unconditionally.  `Lset-out` names an
  --   index below lam, one successor covers there, and `succλ` keeps the
  --   successor below lam.  Nothing of the hull enters.
  --
  --   SO THE OBJECT CLAUSE (ii) ASKS FOR IS FREE.  What clause (ii) asks
  --   for on top of it is a FORMULA that selects such an ordinal, and
  --   that is the whole of its price.
  -- ===================================================================

  cover-in-stage : (y : SV.S) (y∈ : ⟨ y ∈ˢ Lset lam ⟩)
                 → ∥ Σ[ a ∈ HS.ASt.SL ]
                      (IsOrd (fst a) × ⟨ y ∈ˢ Lset (fst a) ⟩) ∥₁
  cover-in-stage y y∈ = PT.map go (Lset-out lam y y∈)
    where
    go : Σ[ δ ∈ SV.S ] (⟨ δ ∈ˢ lam ⟩ × ⟨ y ∈ˢ 𝒟ₒ (Lset δ) ⟩)
       → Σ[ a ∈ HS.ASt.SL ] (IsOrd (fst a) × ⟨ y ∈ˢ Lset (fst a) ⟩)
    go (δ , δ∈λ , y∈𝒟) =
        (sucV δ , sδ∈Lλ)
      , ( osδ , Lset-in (sucV δ) δ y (self∈sucV δ) y∈𝒟 )
      where
      oδ : IsOrd δ
      oδ = mem-ord {A = lam} ordλ δ δ∈λ
      osδ : IsOrd (sucV δ)
      osδ = suc-ord oδ
      sδ∈Lλ : ⟨ sucV δ ∈ˢ Lset lam ⟩
      sδ∈Lλ = Lset-cumul (sucV δ) lam osδ ordλ (succλ δ δ∈λ)
                (ord∈Lset-suc (sucV δ) osδ)

  covering-ordinal : Cover.CoveringOrdinal lam ordλ succλ X X⊆Lλ ∅∈λ
  covering-ordinal c =
    PT.map go (cover-in-stage (fst (T.val c)) (snd (T.val c)))
    where
    go : Σ[ a ∈ HS.ASt.SL ]
           (IsOrd (fst a) × ⟨ fst (T.val c) ∈ˢ Lset (fst a) ⟩)
       → Σ[ a ∈ HS.ASt.SL ]
           (IsOrd (HS.C.π (fst a)) × ⟨ fst (T.val c) ∈ˢ Lset (fst a) ⟩)
    go (a , oa , h) = a , CO.π-ord (fst a) oa , h

  -- ===================================================================
  -- SECTION 6.  CLAUSE (ii) AT ONE CODE, AND THE TWO CASES I CAN PAY.
  --
  --   `CoverBody c` is clause (ii)'s own conclusion at ONE code, written
  --   as [LJ-1.578] wrote it (Probe578.agda:246-251).  It is not a
  --   lookalike: `body-is-clause-ii` is the identity and typechecks only
  --   because the two are the same type.
  -- ===================================================================

  CoverBody : T.Code → Type (ℓ-suc ℓ)
  CoverBody c =
    Σ[ φ ∈ Formula T.Code 1 ]
      ( ∥ Σ[ a ∈ HS.ASt.SL ] ⟨ (a ∷ []) T.⊨c φ ⟩ ∥₁
      × ((a : HS.ASt.SL) → ⟨ (a ∷ []) T.⊨c φ ⟩
         → IsOrd (HS.C.π (fst a))
         × ⟨ fst (T.val c) ∈ˢ Lset (fst a) ⟩) )

  body-is-clause-ii : ((c : T.Code) → CoverBody c)
                    → P578.Cert.DefinesCover lam ordλ succλ X X⊆Lλ ∅∈λ
  body-is-clause-ii f = f

  -- CASE 1.  A CODE WHOSE VALUE IS AN ORDINAL.  PAID, UNCONDITIONALLY,
  -- AND WITH NO LEVEL FORMULA ANYWHERE.  The selecting formula is
  -- "x is an ordinal and the code is a member of x": membership in an
  -- ordinal is a Δ₀ atom, and `Lset-cumul` turns it into the covering.
  cover-at-ordinal : (c : T.Code) → IsOrd (fst (T.val c)) → CoverBody c
  cover-at-ordinal c oc = φ , sat , adeq
    where
    vc : SV.S
    vc = fst (T.val c)
    φ : Formula T.Code 1
    φ = ordFo ∧̇ (con c ∈̇ var zero)
    osvc : IsOrd (sucV vc)
    osvc = suc-ord oc
    vc∈λ : ⟨ vc ∈ˢ lam ⟩
    vc∈λ = ord∈Lset→∈ lam ordλ vc oc (snd (T.val c))
    a₀ : HS.ASt.SL
    a₀ = sucV vc
       , Lset-cumul (sucV vc) lam osvc ordλ (succλ vc vc∈λ)
           (ord∈Lset-suc (sucV vc) osvc)
    sat : ∥ Σ[ a ∈ HS.ASt.SL ] ⟨ (a ∷ []) T.⊨c φ ⟩ ∥₁
    sat = ∣ a₀ , (ord-in a₀ osvc , self∈sucV vc) ∣₁
    adeq : (a : HS.ASt.SL) → ⟨ (a ∷ []) T.⊨c φ ⟩
         → IsOrd (HS.C.π (fst a)) × ⟨ vc ∈ˢ Lset (fst a) ⟩
    adeq a h = CO.π-ord (fst a) oa
             , Lset-cumul vc (fst a) oc oa (h .snd) (ord∈Lset-suc vc oc)
      where
      oa : IsOrd (fst a)
      oa = ord-out a (h .fst)

  -- CASE 2.  A CODE OF ANY VALUE, GIVEN THAT SOME CODE NAMES A COVERING
  -- ORDINAL FOR IT.  The formula is then an EQUATION at that code, so
  -- clause (ii) asks for no definability of the level construction at
  -- all: it asks that the hull CONTAIN the covering ordinal.
  CodedCover : Type (ℓ-suc ℓ)
  CodedCover = (c : T.Code)
             → Σ[ d ∈ T.Code ]
                 ( IsOrd (fst (T.val d))
                 × ⟨ fst (T.val c) ∈ˢ Lset (fst (T.val d)) ⟩ )

  cover-from-coded : CodedCover → (c : T.Code) → CoverBody c
  cover-from-coded cc c = φ , sat , adeq
    where
    d : T.Code
    d = fst (cc c)
    od : IsOrd (fst (T.val d))
    od = fst (snd (cc c))
    cov : ⟨ fst (T.val c) ∈ˢ Lset (fst (T.val d)) ⟩
    cov = snd (snd (cc c))
    φ : Formula T.Code 1
    φ = ordFo ∧̇ (var zero ≐ con d)
    sat : ∥ Σ[ a ∈ HS.ASt.SL ] ⟨ (a ∷ []) T.⊨c φ ⟩ ∥₁
    sat = ∣ T.val d , (ord-in (T.val d) od , refl) ∣₁
    adeq : (a : HS.ASt.SL) → ⟨ (a ∷ []) T.⊨c φ ⟩
         → IsOrd (HS.C.π (fst a))
         × ⟨ fst (T.val c) ∈ˢ Lset (fst a) ⟩
    adeq a h = CO.π-ord (fst a) (ord-out a (h .fst))
             , subst (λ w → ⟨ fst (T.val c) ∈ˢ Lset w ⟩) (sym (h .snd)) cov

  -- AND THE TWO CASES TOGETHER GIVE CLAUSE (ii), because `CodedCover`
  -- covers case 1 as well: this is the whole residue, in one line.
  cover-from-coded-all : CodedCover
                       → P578.Cert.DefinesCover lam ordλ succλ X X⊆Lλ ∅∈λ
  cover-from-coded-all cc = body-is-clause-ii (cover-from-coded cc)

  -- ===================================================================
  -- SECTION 7.  WHERE THE PRICE OF CLAUSE (ii) ACTUALLY SITS.
  --
  --   Section 6 pays clause (ii) at one case and reduces it at the
  --   other.  This section says what the reduction costs, in three
  --   terms, and each one narrows the residue.
  --
  --   7.1  THE ORDINAL HALF OF CLAUSE (ii) IS FREE.  A formula that only
  --        COVERS, together with one ordinal witness, gives the whole
  --        clause: `ordFo` supplies the rest and `π-ord` carries it over
  --        the collapse.  So the price of clause (ii) is the covering
  --        half and nothing else.
  --
  --   7.2  AND FACT C DOES NOT NEED A FORMULA AT ALL.  `Covered`
  --        (Probe578.agda:130-136) is TRUNCATED, so the covering
  --        ordinal never has to be selected by a formula: it is enough
  --        that the hull CONTAIN one.  `factC-from-hull` is that route,
  --        and it also discharges `Covered`'s collapse condition from
  --        the external one, again by `π-ord`.
  --
  --   7.3  So `CodedCover` and clause (ii) both sit above ONE
  --        set-theoretic statement with no syntax in it: the hull is
  --        covered.  `coded-gives-hull` is one direction of that.
  -- ===================================================================

  InternalCover : Type (ℓ-suc ℓ)
  InternalCover =
    (c : T.Code)
    → Σ[ ψ ∈ Formula T.Code 1 ]
        ( ∥ Σ[ a ∈ HS.ASt.SL ]
             (IsOrd (fst a) × ⟨ (a ∷ []) T.⊨c ψ ⟩) ∥₁
        × ((a : HS.ASt.SL) → ⟨ (a ∷ []) T.⊨c ψ ⟩
           → ⟨ fst (T.val c) ∈ˢ Lset (fst a) ⟩) )

  cover-from-internal : InternalCover → (c : T.Code) → CoverBody c
  cover-from-internal ic c = (ordFo ∧̇ ψ) , sat , adeq
    where
    ψ : Formula T.Code 1
    ψ = fst (ic c)
    sat : ∥ Σ[ a ∈ HS.ASt.SL ] ⟨ (a ∷ []) T.⊨c (ordFo ∧̇ ψ) ⟩ ∥₁
    sat = PT.map (λ { (a , oa , hψ) → a , (ord-in a oa , hψ) })
            (fst (snd (ic c)))
    adeq : (a : HS.ASt.SL) → ⟨ (a ∷ []) T.⊨c (ordFo ∧̇ ψ) ⟩
         → IsOrd (HS.C.π (fst a))
         × ⟨ fst (T.val c) ∈ˢ Lset (fst a) ⟩
    adeq a h = CO.π-ord (fst a) (ord-out a (h .fst))
             , snd (snd (ic c)) a (h .snd)

  -- The hull is covered: every member sits inside a level whose index is
  -- an ordinal OF THE HULL.  No formula, no satisfaction, no collapse.
  HullCovered : Type (ℓ-suc ℓ)
  HullCovered = (y : SV.S) → ⟨ y ∈ˢ HS.M ⟩
              → ∥ Σ[ γ ∈ SV.S ]
                   ( ⟨ γ ∈ˢ HS.M ⟩ × IsOrd γ × ⟨ y ∈ˢ Lset γ ⟩ ) ∥₁

  factC-from-hull : HullCovered
                  → P578.Facts.Covered lam ordλ succλ X X⊆Lλ ∅∈λ
  factC-from-hull hc y y∈M = PT.map go (hc y y∈M)
    where
    go : Σ[ γ ∈ SV.S ] (⟨ γ ∈ˢ HS.M ⟩ × IsOrd γ × ⟨ y ∈ˢ Lset γ ⟩)
       → Σ[ γ ∈ SV.S ]
           (⟨ γ ∈ˢ HS.M ⟩ × IsOrd (HS.C.π γ) × ⟨ y ∈ˢ Lset γ ⟩)
    go (γ , γ∈M , oγ , h) = γ , γ∈M , CO.π-ord γ oγ , h

  coded-gives-hull : CodedCover → HullCovered
  coded-gives-hull cc y y∈M = PT.map go (HS.H.hull-member y y∈M)
    where
    go : Σ[ c ∈ T.Code ] (fst (T.val c) ≡ y)
       → Σ[ γ ∈ SV.S ] (⟨ γ ∈ˢ HS.M ⟩ × IsOrd γ × ⟨ y ∈ˢ Lset γ ⟩)
    go (c , e) = fst (T.val (fst (cc c)))
               , HS.H.val-in-Hull (fst (cc c))
               , fst (snd (cc c))
               , subst (λ w → ⟨ w ∈ˢ Lset (fst (T.val (fst (cc c)))) ⟩) e
                   (snd (snd (cc c)))

  -- ===================================================================
  -- SECTION 8.  DEVLIN'S SHARED MATRIX, AND WHAT IT GIVES.
  --
  --   Devlin does NOT prove two unrelated statements.  He fixes ONE Σ₀
  --   matrix Φ(z, v, γ) (`dev/literature/devlin-II5.md:95-99`) and then
  --   builds two Σ₁ statements out of it: the forward inclusion runs on
  --   "∃v∃z φ(z, v, γ)", the index FREE (`:102-103`), and the reverse
  --   inclusion on "∃γ∃v∃z(φ(z,v,γ) ∧ x ∈ v)", the index BOUND
  --   (`:107-108`).  THE MATRIX IS THE SHARED OBJECT AND THE BINDER IS
  --   WHAT DIFFERS.
  --
  --   [LJ-1.578]'s clause (i) (Probe578.agda:234-240) hides the matrix
  --   behind an existential, ONE CODE AT A TIME.  That is why clause (ii)
  --   does not follow from it: a family of index-fixed formulas cannot be
  --   put under a binder.  The module below states the matrix instead,
  --   and clause (ii) follows from it with no further mathematics.
  --
  --   THE MATRIX IS NOT BUILT HERE AND I DO NOT CLAIM IT.  `Sound` and
  --   `Complete` are Devlin's (b), left to right and right to left, and
  --   they are the hypotheses of the two terms below.
  -- ===================================================================

  module Shared (Φ : Formula T.Code 3) where

    -- The reading is at the environment (z ∷ v ∷ γ ∷ []): a witness, the
    -- level, the index, in Devlin's own order.
    Sound : Type (ℓ-suc ℓ)
    Sound = (z v γ : HS.ASt.SL) → ⟨ (z ∷ v ∷ γ ∷ []) T.⊨c Φ ⟩
          → fst v ≡ Lset (fst γ)

    Complete : Type (ℓ-suc ℓ)
    Complete = (γ : HS.ASt.SL) → IsOrd (fst γ)
             → ∥ Σ[ v ∈ HS.ASt.SL ] Σ[ z ∈ HS.ASt.SL ]
                  ( (fst v ≡ Lset (fst γ))
                  × ⟨ (z ∷ v ∷ γ ∷ []) T.⊨c Φ ⟩ ) ∥₁

    -- Devlin's reverse-inclusion statement, at the index: the level and
    -- the witness are bound and the INDEX is the free variable, because
    -- clause (ii) asks for the ordinal and not for the level.
    coverFo : T.Code → Formula T.Code 1
    coverFo c = ∃̇ (∃̇ (Φ ∧̇ (con c ∈̇ var (suc zero))))

    shared-gives-cover : Sound → Complete → (c : T.Code) → CoverBody c
    shared-gives-cover so co c = (ordFo ∧̇ coverFo c) , sat , adeq
      where
      vc : SV.S
      vc = fst (T.val c)
      sat : ∥ Σ[ a ∈ HS.ASt.SL ] ⟨ (a ∷ []) T.⊨c (ordFo ∧̇ coverFo c) ⟩ ∥₁
      sat = PT.rec PT.squash₁ mk (cover-in-stage vc (snd (T.val c)))
        where
        mk : Σ[ a ∈ HS.ASt.SL ] (IsOrd (fst a) × ⟨ vc ∈ˢ Lset (fst a) ⟩)
           → ∥ Σ[ a ∈ HS.ASt.SL ]
                ⟨ (a ∷ []) T.⊨c (ordFo ∧̇ coverFo c) ⟩ ∥₁
        mk (a , oa , h) = PT.map mk₂ (co a oa)
          where
          mk₂ : Σ[ v ∈ HS.ASt.SL ] Σ[ z ∈ HS.ASt.SL ]
                  ( (fst v ≡ Lset (fst a))
                  × ⟨ (z ∷ v ∷ a ∷ []) T.⊨c Φ ⟩ )
              → Σ[ a' ∈ HS.ASt.SL ]
                  ⟨ (a' ∷ []) T.⊨c (ordFo ∧̇ coverFo c) ⟩
          mk₂ (v , z , e , hΦ) =
              a
            , ( ord-in a oa
              , ∣ v , ∣ z
                      , ( hΦ
                        , subst (λ w → ⟨ vc ∈ˢ w ⟩) (sym e) h ) ∣₁ ∣₁ )
      adeq : (a : HS.ASt.SL) → ⟨ (a ∷ []) T.⊨c (ordFo ∧̇ coverFo c) ⟩
           → IsOrd (HS.C.π (fst a)) × ⟨ vc ∈ˢ Lset (fst a) ⟩
      adeq a h = CO.π-ord (fst a) (ord-out a (h .fst))
               , PT.rec (snd (vc ∈ˢ Lset (fst a))) go (h .snd)
        where
        go : Σ[ v ∈ HS.ASt.SL ]
               ⟨ (v ∷ a ∷ []) T.⊨c (∃̇ (Φ ∧̇ (con c ∈̇ var (suc zero)))) ⟩
           → ⟨ vc ∈ˢ Lset (fst a) ⟩
        go (v , hv) = PT.rec (snd (vc ∈ˢ Lset (fst a))) go₂ hv
          where
          go₂ : Σ[ z ∈ HS.ASt.SL ]
                  ⟨ (z ∷ v ∷ a ∷ [])
                      T.⊨c (Φ ∧̇ (con c ∈̇ var (suc zero))) ⟩
              → ⟨ vc ∈ˢ Lset (fst a) ⟩
          go₂ (z , hz) =
            subst (λ w → ⟨ vc ∈ˢ w ⟩) (so z v a (hz .fst)) (hz .snd)

    shared-gives-clause-ii : Sound → Complete
                           → P578.Cert.DefinesCover lam ordλ succλ X X⊆Lλ ∅∈λ
    shared-gives-clause-ii so co = body-is-clause-ii (shared-gives-cover so co)
