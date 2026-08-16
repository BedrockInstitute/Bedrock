{-# OPTIONS --cubical --safe --guardedness #-}

-- [LJ-1.378] probe.  THE COMPOSITE'S TERM, ASSEMBLED AT ONE INSTANCE.
--
-- THE QUESTION: is the assembly of the composite MECHANICAL, or does it
-- hide mathematics?  [LJ-1.302] wrote the composite's TYPE and fed a
-- HYPOTHETICAL term; [LJ-1.304] built the two stems; [LJ-1.338]
-- instantiated the leaf modulo six residues; [LJ-1.52] archived a
-- graph assembly at the class carrier.  NOBODY has assembled a term.
--
-- WHAT THIS FILE BUILDS, at the ambient carrier, at φ₀'s own frame
-- (u ∷ v ∷ g ∷ K ∷ δ₀..δ₁₁, sixteen slots, `LevelHood {12}`'s layout):
--
--   * the GRAPH STEM at ambient: `[LJ-1.52]`'s `graph-assembly` shape,
--     re-landed on `[LJ-1.304]`'s stems (imported as terms) and
--     `[LJ-1.238]`'s `LsetGraph-in`.  This is the factor
--     `[LJ-1.304]` section 10 called「the last unpriced term」.
--   * the LEVEL STEM: `levelHoodB`'s row (∃ x ∈ K, graph row ∧ x ≐ v)
--     to the machine graph at the frame, through the graph stem.
--   * comp : Composite, and amb-from-composite from `[LJ-1.302]`'s
--     Fed, fed MY comp.
--
-- WHAT STAYS NAMED, with its real type: the φ₀ EXTRACTION (the
-- fourteen witnesses and the level row; [LJ-1.302] called this
-- trivial BY DESCRIPTION), the leaf bridge at the composite's frame
-- (the leaf stem's output, priced by [LJ-1.298]/[LJ-1.338]), the
-- in-K site facts (the tie family, 327 measured lines), `dK`
-- ([LJ-1.304]'s new tie), the frame RESTRICTION (the delivered
-- ⊨-rename supplies it; the instantiation is not measured here), and
-- the Def-step trio, a hypothesis by design.
--
-- The leaf contents ψs ψa stay parameters: the assembly holds for
-- every leaf content, which is the generic form the port wants.
--
-- ONE agda process under GHCRTS="-A64m -I0 -M8g".

open import Base.Prelude
open import Base.Truth
open import Base.Classical using ( LEM )

open import FOL.ZFStructure using ( module hPropStructure; Transitive; _↾_ )
open import FOL.Syntax using
  ( Formula; var; _∈̇_; _∧̇_; _≐_; ∃̇_; ∃̇∈ )
open import FOL.Manipulation.Relabelling using ( embed )
import FOL.Absoluteness
open import Cubical.HITs.CumulativeHierarchy.Base using ( V; _∈_ )
open import Cubical.HITs.CumulativeHierarchy.Constructions
  using ( ⁅_,_⁆ ) renaming ( module InfinitySet to Inf )
open import Cubical.Data.Unit using ( tt*; isPropUnit* )
open import Cubical.Data.Nat using ( _+_ )
open import Cubical.Data.Vec using ( Vec; lookup; _∷_; [] )
open import Cubical.Data.Sigma.Properties using ( Σ≡Prop )
import Cubical.HITs.PropositionalTruncation as PT
open PT using ( ∣_∣₁; squash₁; ∥_∥₁ )

module LJ-1-378.Control378 {ℓ : Level} (lem : LEM (ℓ-suc ℓ)) where

open import V.Hierarchy {ℓ} using ( 𝒮ᵥ )
open import V.Coding {ℓ} using ( pr )
open import L.Constructible {ℓ} using ( 𝒟ₒ )
open Inf using ( #_; sucV )

import LJ-1-184.ProbeLJ1184A {ℓ} as P184
import LJ-1-297.ProbeLJ1297A {ℓ} lem as P1297A
import LJ-1-297.ProbeLJ1297C {ℓ} as P1297C
import LJ-1-297.ProbeLJ1297D {ℓ} lem as P1297D
import LJ-1-302.ProbeLJ1302A {ℓ} lem as P1302A
import LJ-1-304.ProbeLJ1304A {ℓ} lem as P1304
import LJ-1-238.GenSequence

module A = P184.Ambient
module P1241 = P1297A.P1241
open P1297C using ( absFull )

module GS = LJ-1-238.GenSequence {ℓ} lem P1297A.Full
  (λ {x} {y} → P1297A.Full-tr {x} {y})
  (λ k → # k , tt*) (λ k → refl)
  (λ a b → ⁅ fst a , fst b ⁆ , tt*) (λ a b → refl)
  (λ a → sucV (fst a) , tt*) (λ a → refl)

SC : Type (ℓ-suc ℓ)
SC = A.R.SC

-- The ambient-class reading, the same instantiation `P1297A.AbsL`
-- and `[LJ-1.304]`'s `AbsF` carry.
module AbsF = FOL.Absoluteness.Single 𝒮ᵥ P1297A.Full
  (λ {x} {y} → P1297A.Full-tr {x} {y})
open AbsF using ( _^_ ) renaming ( _⊨ᵐ_ to _⊨_ )

toAmb : ∀ {n} (φ : Formula SC n) (γ : Vec SC n)
      → ⟨ γ ⊨ φ ⟩ → ⟨ A.ambient γ φ ⟩
toAmb φ γ = subst ⟨_⟩ (absFull φ γ)

fromAmb : ∀ {n} (φ : Formula SC n) (γ : Vec SC n)
        → ⟨ A.ambient γ φ ⟩ → ⟨ γ ⊨ φ ⟩
fromAmb φ γ = subst ⟨_⟩ (sym (absFull φ γ))

-- =====================================================================
-- THE COMPOSITE'S ASSEMBLY.  The frame is φ₀'s own sixteen slots
-- (u ∷ v ∷ g ∷ K ∷ δ₀..δ₁₁); every named parameter is an obligation
-- the route prices elsewhere.  Everything between them is built here.
-- =====================================================================
module Comp
  (DefAt : ∀ {n} → Fin n → Fin n → Formula SC n)
  (DefAt-in : (X : SC) → ∀ {n} (u w : Fin n) (γ : Vec SC n)
            → fst (lookup w γ) ≡ fst X
            → fst (lookup u γ) ≡ 𝒟ₒ (fst X)
            → ⟨ γ ⊨ DefAt u w ⟩)
  (DefAt-out : (X : SC) → ∀ {n} (u w : Fin n) (γ : Vec SC n) → GS.DefOK X
             → fst (lookup w γ) ≡ fst X
             → ⟨ γ ⊨ DefAt u w ⟩
             → fst (lookup u γ) ≡ 𝒟ₒ (fst X))
  (ψs : Formula SC 25)
  (ψa : Formula SC 27)
  where

  module S304 = P1304.Supply DefAt DefAt-in DefAt-out
  module SD = P1297D.Supply DefAt DefAt-in DefAt-out
  module CT = P1302A.CompositeTy DefAt DefAt-in DefAt-out

  Composite : Type (ℓ-suc ℓ)
  Composite = CT.Composite

  -- The carrier's second components are `Full`'s `Unit*`, so a
  -- first-component path is a path.  Used to retarget the graph's
  -- witness slot along the level row's `x ≐ v` and to move the
  -- two-slot environment to γ.
  SCeq : (a b : SC) → fst a ≡ fst b → a ≡ b
  SCeq a b p = Σ≡Prop (λ _ → isPropUnit*) p

  -- THE GRAPH ROW, at the seventeen-slot frame
  -- (x ∷ u ∷ v ∷ g ∷ K ∷ δ₀..δ₁₁): `GraphB`'s row with the graph's
  -- witness at zero, g at three, K at four.  Verbatim `LevelHood`'s
  -- `G` application (`src/L/BoundedSubset.lagda.md:81-107`), at the
  -- ambient carrier, on `[LJ-1.304]`'s copies of the bounded
  -- matrices.
  graphRow : Formula SC 17
  graphRow =
    ∃̇∈ (var (suc (suc (suc (suc zero)))))
      (S304.approxBndAt ψa zero
         (suc (suc (suc (suc zero))))
         (suc (suc (suc (suc (suc zero)))))
      ∧̇ S304.stepBndAt ψs (suc zero)
         (suc (suc (suc (suc zero)))) zero
         (suc (suc (suc (suc (suc zero))))))

  -- THE LEVEL ROW, at the sixteen-slot frame
  -- (u ∷ v ∷ g ∷ K ∷ δ₀..δ₁₁): `levelHoodB`'s own shape, `∃ x ∈ K`
  -- of the graph row and `x ≐ v` (`src/L/BoundedSubset.lagda.md:109`).
  levelRow : Formula SC 16
  levelRow =
    ∃̇∈ (var (suc (suc (suc zero))))
      (graphRow ∧̇ (var (suc (suc zero)) ≐ var zero))

  -- THE SITE OBLIGATIONS at a frame.  These are the tie family the
  -- route prices: `[LJ-1.302]`/`[LJ-1.336]`/`[LJ-1.338]`'s 327 lines
  -- and `[LJ-1.304]`'s `dK`.  The eighteen-frame is
  -- (y ∷ x ∷ u ∷ v ∷ g ∷ K ∷ δ₀..δ₁₁), the graph matrix's own.
  SiteObl : (frame : SC ^ 16) → Type (ℓ-suc ℓ)
  SiteObl frame =
      -- StepAgree's leaf bridge, at the frame's own witnesses.
      ( (y x d w c z : SC)
        → ⟨ (d ∷ w ∷ c ∷ z ∷ y ∷ x ∷ frame) ⊨
              S304.leafB ψs (suc (suc (suc (suc (suc zero))))) ⟩
        → ⟨ (d ∷ w ∷ c ∷ z ∷ y ∷ x ∷ frame) ⊨ DefAt zero (suc zero) ⟩ )
    × ( (y x d w c z : SC)
        → ⟨ (d ∷ w ∷ c ∷ z ∷ y ∷ x ∷ frame) ⊨ DefAt zero (suc zero) ⟩
        → ⟨ (d ∷ w ∷ c ∷ z ∷ y ∷ x ∷ frame) ⊨
              S304.leafB ψs (suc (suc (suc (suc (suc zero))))) ⟩ )
      -- ApproxAgree's leaf bridge, six-extended, arbitrary
      -- satisfiers, at the frame's own witnesses.
    × ( (y x d w c z y' x' : SC)
        → ⟨ (d ∷ w ∷ c ∷ z ∷ y' ∷ x' ∷ y ∷ x ∷ frame) ⊨
              S304.leafB ψa
                (suc (suc (suc (suc (suc (suc (suc zero))))))) ⟩
        → ⟨ (d ∷ w ∷ c ∷ z ∷ y' ∷ x' ∷ y ∷ x ∷ frame) ⊨
              DefAt zero (suc zero) ⟩ )
    × ( (y x d w c z y' x' : SC)
        → ⟨ (d ∷ w ∷ c ∷ z ∷ y' ∷ x' ∷ y ∷ x ∷ frame) ⊨
              DefAt zero (suc zero) ⟩
        → ⟨ (d ∷ w ∷ c ∷ z ∷ y' ∷ x' ∷ y ∷ x ∷ frame) ⊨
              S304.leafB ψa
                (suc (suc (suc (suc (suc (suc (suc zero))))))) ⟩ )
      -- The in-K facts, at the frame's own witnesses.
    × ( (y x c w : SC)
        → ⟨ pr (fst c) (fst w) ∈ fst y ⟩
        → ⟨ fst w ∈ fst (lookup (suc (suc (suc (suc (suc zero)))))
                                 (y ∷ x ∷ frame)) ⟩ )
    × ( (y x c w : SC)
        → ⟨ pr (fst c) (fst w) ∈ fst y ⟩
        → ⟨ 𝒟ₒ (fst w) ∈ fst (lookup (suc (suc (suc (suc (suc zero)))))
                                      (y ∷ x ∷ frame)) ⟩ )
    × ( (y x c w a : SC)
        → ⟨ pr (fst c) (fst w) ∈ fst y ⟩
        → ⟨ fst a ∈ 𝒟ₒ (fst w) ⟩
        → ⟨ fst a ∈ fst (lookup (suc (suc (suc (suc (suc zero)))))
                                 (y ∷ x ∷ frame)) ⟩ )
    × ( (y x : SC)
        → ⟨ (y ∷ x ∷ frame) ⊨
              P1304.GDA.domB zero (suc (suc (suc (suc zero))))
                (suc (suc (suc (suc (suc zero))))) ⟩
        → ⟨ (y ∷ x ∷ frame) ⊨
              P1304.GDA.GM.domAt zero (suc (suc (suc (suc zero)))) ⟩ )
    × ( (y x c z : SC)
        → ⟨ pr (fst c) (fst z) ∈ fst y ⟩
        → ⟨ fst c ∈ fst (lookup (suc (suc (suc (suc (suc zero)))))
                                 (y ∷ x ∷ frame)) ⟩
          × ⟨ fst z ∈ fst (lookup (suc (suc (suc (suc (suc zero)))))
                                   (y ∷ x ∷ frame)) ⟩ )
      -- The frame RESTRICTION: the machine graph at the seventeen-slot
      -- frame moves to the two-slot pair.  The delivered ⊨-rename
      -- (`src/FOL/Manipulation/Renaming.lagda.md:127`) supplies it;
      -- this probe does not measure that instantiation.
    × ( (x : SC)
        → ⟨ (x ∷ frame) ⊨ S304.Seq.LsetGraphAt zero
              (suc (suc (suc zero))) ⟩
        → ⟨ (x ∷ lookup (suc (suc zero)) frame ∷ []) ⊨
              S304.Seq.LsetGraphAt zero (suc zero) ⟩ )

  -- THE TWO STEMS, applied at the graph matrix's own eighteen-frame.
  -- `[LJ-1.304]`'s terms, imported; the obligations are the site's,
  -- read off the bundle once.
  module AtFrame (frame : SC ^ 16) (so : SiteObl frame) where
    private
      lf4  = so .fst
      lb4  = so .snd .fst
      lf6  = so .snd .snd .fst
      lb6  = so .snd .snd .snd .fst
      wk   = so .snd .snd .snd .snd .fst
      dk   = so .snd .snd .snd .snd .snd .fst
      zk   = so .snd .snd .snd .snd .snd .snd .fst
      dm   = so .snd .snd .snd .snd .snd .snd .snd .fst
      ek   = so .snd .snd .snd .snd .snd .snd .snd .snd .fst
      rs   = so .snd .snd .snd .snd .snd .snd .snd .snd .snd

    stepAt18 : (y x : SC)
      → ⟨ (y ∷ x ∷ frame) ⊨ S304.stepBndAt ψs (suc zero)
             (suc (suc (suc (suc zero)))) zero
             (suc (suc (suc (suc (suc zero))))) ⟩
      → ⟨ (y ∷ x ∷ frame) ⊨ S304.Seq.StepAt (suc zero)
             (suc (suc (suc (suc zero)))) zero ⟩
    stepAt18 y x h =
      S304.StepAgree.step-agree ψs (suc zero)
        (suc (suc (suc (suc zero)))) zero
        (suc (suc (suc (suc (suc zero))))) (y ∷ x ∷ frame)
        (λ d w c z → lf4 y x d w c z)
        (λ d w c z → lb4 y x d w c z)
        (λ c w → wk y x c w)
        (λ c w → dk y x c w)
        (λ c w a → zk y x c w a)
        h

    approxAt18 : (y x : SC)
      → ⟨ (y ∷ x ∷ frame) ⊨ S304.approxBndAt ψa zero
             (suc (suc (suc (suc zero))))
             (suc (suc (suc (suc (suc zero))))) ⟩
      → ⟨ (y ∷ x ∷ frame) ⊨ S304.Seq.ApproxAt zero
             (suc (suc (suc (suc zero)))) ⟩
    approxAt18 y x h =
      S304.ApproxAgree.approx-agree ψa zero
        (suc (suc (suc (suc zero))))
        (suc (suc (suc (suc (suc zero))))) (y ∷ x ∷ frame)
        (λ d w c z y' x' → lf6 y x d w c z y' x')
        (λ d w c z y' x' → lb6 y x d w c z y' x')
        (λ c w → wk y x c w)
        (λ c w → dk y x c w)
        (λ c w a → zk y x c w a)
        (dm y x)
        (λ c z → ek y x c z)
        h

    -- THE GRAPH STEM, at ambient: `[LJ-1.52]`'s assembly, re-landed.
    -- The row's witness y bounds the approximation's f-slot and the
    -- step's f-slot; the stems lift both rows; `LsetGraph-in`
    -- packages them at the graph's own slots.
    graphStem : (x : SC)
      → ⟨ (x ∷ frame) ⊨ graphRow ⟩
      → ⟨ (x ∷ frame) ⊨ S304.Seq.LsetGraphAt zero (suc (suc (suc zero))) ⟩
    graphStem x h =
      PT.rec (snd ((x ∷ frame) ⊨
                     S304.Seq.LsetGraphAt zero (suc (suc (suc zero))))) go h
      where
      go : Σ[ y ∈ SC ]
             ( ⟨ fst y ∈ fst (lookup (suc (suc (suc (suc zero)))) (x ∷ frame)) ⟩
             × ( ⟨ (y ∷ x ∷ frame) ⊨ S304.approxBndAt ψa zero
                     (suc (suc (suc (suc zero))))
                     (suc (suc (suc (suc (suc zero))))) ⟩
               × ⟨ (y ∷ x ∷ frame) ⊨ S304.stepBndAt ψs (suc zero)
                     (suc (suc (suc (suc zero)))) zero
                     (suc (suc (suc (suc (suc zero))))) ⟩ ) )
        → ⟨ (x ∷ frame) ⊨
              S304.Seq.LsetGraphAt zero (suc (suc (suc zero))) ⟩
      go (y , (_ , (happ , hstep))) =
        S304.Seq.LsetGraph-in zero (suc (suc (suc zero))) (x ∷ frame) y
          (approxAt18 y x hstep) (stepAt18 y x happ)

    -- THE LEVEL STEM: `levelHoodB`'s row to the machine graph, at the
    -- frame's own v and g slots, retargeted along the row's `x ≐ v`.
    levelStem : ⟨ frame ⊨ levelRow ⟩
      → ⟨ (lookup (suc zero) frame ∷ lookup (suc (suc zero)) frame ∷ []) ⊨
             S304.Seq.LsetGraphAt zero (suc zero) ⟩
    levelStem h =
      PT.rec (snd ((lookup (suc zero) frame ∷
                      lookup (suc (suc zero)) frame ∷ []) ⊨
                     S304.Seq.LsetGraphAt zero (suc zero))) go h
      where
      go : Σ[ x ∈ SC ]
             ( ⟨ fst x ∈ fst (lookup (suc (suc (suc zero))) frame) ⟩
             × ( ⟨ (x ∷ frame) ⊨ graphRow ⟩
               × ⟨ (x ∷ frame) ⊨ (var (suc (suc zero)) ≐ var zero) ⟩ ) )
        → ⟨ (lookup (suc zero) frame ∷
               lookup (suc (suc zero)) frame ∷ []) ⊨
               S304.Seq.LsetGraphAt zero (suc zero) ⟩
      go (x , (_ , (hrow , hdot))) =
        subst (λ e → ⟨ (e ∷ lookup (suc (suc zero)) frame ∷ []) ⊨
                         S304.Seq.LsetGraphAt zero (suc zero) ⟩)
          (SCeq x (lookup (suc zero) frame) (sym hdot))
          (rs x (graphStem x hrow))

  -- THE EXTRACTION, named: φ₀'s fourteen witnesses, the level row,
  -- and the two slot equations that tie the frame to γ.  The
  -- equations are CARRIER-LEVEL: the extraction builds the frame from
  -- γ's own entries, so they are `refl` at construction.  This is
  -- the factor `[LJ-1.302]` section 1 priced as trivial, by
  -- description.
  Extraction : (γ : Vec SC 2) → Type (ℓ-suc ℓ)
  Extraction γ =
    ⟨ A.ambient γ (embed P1241.φ₀) ⟩
      → Σ[ frame ∈ SC ^ 16 ]
          ( (lookup (suc zero) frame ≡ lookup zero γ)
          × (lookup (suc (suc zero)) frame ≡ lookup (suc zero) γ)
          × ⟨ frame ⊨ levelRow ⟩ )

  -- THE COMPOSITE'S TERM, at one instance: extraction and site
  -- obligations in, `amb`'s missing input out.
  comp : (extr : (γ : Vec SC 2) → Extraction γ)
       → ((frame : SC ^ 16) → SiteObl frame)
       → Composite
  comp extr so (v ∷ g ∷ []) h =
    toAmb (SD.Graph* {2} zero (suc zero)) (v ∷ g ∷ [])
      (let frame = extr (v ∷ g ∷ []) h .fst
           pv    = extr (v ∷ g ∷ []) h .snd .fst
           pg    = extr (v ∷ g ∷ []) h .snd .snd .fst
           row   = extr (v ∷ g ∷ []) h .snd .snd .snd
       in subst (λ e → ⟨ e ⊨ SD.Graph* {2} zero (suc zero) ⟩)
            (cong₂ _∷_ pv (cong (_∷ []) pg))
            (AtFrame.levelStem frame (so frame) row))

  -- THE FEEDING, with MY comp: `amb` is a term at this instance.
  module Fed
    (extr : (γ : Vec SC 2) → Extraction γ)
    (so : (frame : SC ^ 16) → SiteObl frame) where

    c : Composite
    c = comp extr so

    module F = CT.Fed c

    amb-from-composite = F.AS.amb
