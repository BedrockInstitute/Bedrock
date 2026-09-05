{-# OPTIONS --cubical --safe --guardedness #-}

-- [LJ-1.655] PROBE.  Does the chapter's own `elem` ARRIVE at the site
-- where `C.π` is defined?  Lands nothing in src/.  ANSWER: YES.
--
--   PART 0   The collapse site, the chapter's own cut at
--            src/L/BoundedSubset.lagda.md:903-916, plus the ONE move
--            this task measures: `HullElemDown` instantiated at that
--            site's telescope with NO new hypothesis.
--
--   PART 1   W3.  The carrier `Elementary` quantifies over IS the
--            carrier the collapse site uses.  Four agreements, all
--            `refl`: the hull, the code type, the member type, and the
--            two readings of a formula at it.  MEASURED FLOOR: 3.08 s.
--
--   PART 2   THE OBLIGATION.  `elem` does not sit in `HullElemDown`; it
--            sits one module deeper, in `WithCode`, which asks for a
--            code function on the hull's members and its spec.  That
--            pair is the WHOLE price, and `elem-at-collapse` composes
--            `elem` with the collapse's own iso-invariance so a
--            consumer at `C.π`'s site can apply it.
--
--   PART 3   What the arrival buys.  `collapse-stage-agree` is the
--            parameter-free form the two NO-GOs named and never had.
--            `hood-complete-from-stage` discharges [LJ-1.653]'s
--            hypothesis 2 down to a fact that names neither M nor C.π.
--
--   PART 4   The price is already paid in the tree: the chapter's own
--            `hedF` and `hedF-spec`, cited by name so the citation is
--            machine-checked.
--
--   PART 5   THE DECISIVE ARM.  The pair SPENT at the chapter's own
--            telescope, so `elem-at-collapse-free` takes no code
--            hypothesis at all.  Every argument left is one the
--            chapter's `BoundedSubsetAt` already takes.
--
-- ONE Agda process per run, GHCRTS="-A64m -I0 -M2g", the wide caliber,
-- set on the pane by the program and untouched here.  No heap event.

open import Base.Prelude
open import Base.Truth
open import Base.Classical using ( LEM )

module LJ-1-655.Probe655 {ℓ : Level} (lem : LEM (ℓ-suc ℓ)) where

open import FOL.ZFStructure using ( module hPropStructure )
open import FOL.Syntax using ( Formula )
open import FOL.Manipulation.Relabelling using ( mapFo; mapFo-comp; embed )
open import V.Hierarchy {ℓ} using ( 𝒮ᵥ )
open import L.Constructible {ℓ} using ( IsOrd; Lset )
open import L.Hull {ℓ} lem using ( module AtStage )
open import V.Collapse {ℓ} using ( module Collapse; isExt )
open import L.BoundedSubset {ℓ} lem
  using ( module HullExt; module CollapseIso; module HullElemDown
        ; module Devlin55; module UnionKit; IsCardinal; _↪_ )

import Cubical.Data.Empty as Empty
open import Cubical.Data.Sigma using ( _×_; _,_ )
open import Cubical.Data.Vec using ( Vec; _∷_; []; map )
open import Cubical.HITs.CumulativeHierarchy.Constructions
  using ( ∅; _∪_; ⁅_⁆s; module InfinitySet )
open import Cubical.HITs.CumulativeHierarchy.Properties using ( ⟪_⟫ )
open InfinitySet using ( ω; sucV )

open TruthAlgebra (hPropAlgebra (ℓ-suc ℓ))
open hPropStructure 𝒮ᵥ

-- =====================================================================
-- PART 0.  THE COLLAPSE SITE.
-- =====================================================================

-- Telescope copied from src/L/BoundedSubset.lagda.md:903-916, the same
-- cut as Probe653.agda:75-88 and Probe477.agda:44-57.  Nothing below
-- `module Condense` (:916) is copied.
module AtCollapse (lam : S) (ordλ : IsOrd lam)
  (succλ : (d : S) → ⟨ d ∈ˢ lam ⟩ → ⟨ sucV d ∈ˢ lam ⟩)
  (X : S) (X⊆L : (x : S) → ⟨ x ∈ˢ X ⟩ → ⟨ x ∈ˢ Lset lam ⟩)
  (∅∈λ : ⟨ ∅ ∈ˢ lam ⟩) where

  module ASt = AtStage lam ordλ
  module H = ASt.Hull X X⊆L ∅∈λ

  M : S
  M = H.T.Hull

  module C = Collapse M

  -- The hull is extensional.  DELIVERED, src/L/BoundedSubset.lagda.md:1340.
  module HE = HullExt lam ordλ X X⊆L ∅∈λ

  Mext : isExt M
  Mext = HE.hullExt

  module CIso = CollapseIso M Mext

  -- THE ONE MOVE THIS PROBE MEASURES.  `HullElemDown`
  -- (src/L/BoundedSubset.lagda.md:667-668) takes exactly the collapse
  -- site's telescope MINUS `succλ`, so the instance is built here with
  -- NO new hypothesis at all.
  module HED = HullElemDown lam ordλ X X⊆L ∅∈λ

  -- =====================================================================
  -- PART 1.  W3: IS `A.SM` THE CARRIER THE COLLAPSE SITE USES?
  -- =====================================================================

  hull-agree : HED.M ≡ M
  hull-agree = refl

  code-agree : HED.H.T.Code ≡ H.T.Code
  code-agree = refl

  -- `AtStage.AtM.SM` (src/L/Hull.lagda.md:165-166) and `IsoInv.SM`
  -- (src/L/BoundedSubset.lagda.md:164-166) are the SAME Σ type.
  carrier-agree : HED.A.SM ≡ CIso.I.SM
  carrier-agree = refl

  -- And the two readings of a formula at that carrier are the same
  -- reading: both are `FOL.Semantics ... (𝒮ᵥ ↾ (λ x → x ∈ˢ M)) .At SM id`.
  sat-agree : {n : ℕ} (φ : Formula CIso.I.SM n) (δ : Vec CIso.I.SM n)
            → HED.Mse._⊨_ δ φ ≡ CIso.I._⊨ᵐ_ δ φ
  sat-agree φ δ = refl

  -- The stage side agrees too: `HED.ASt.AbsL` is this site's own `ASt.AbsL`.
  stage-agree : {n : ℕ} (φ : Formula ASt.SL n) (δ : Vec ASt.SL n)
              → HED.ASt.AbsL._⊨ᵐ_ δ φ ≡ ASt.AbsL._⊨ᵐ_ δ φ
  stage-agree φ δ = refl

  -- =====================================================================
  -- PART 2.  THE OBLIGATION.  WHAT ELEMENTARITY COSTS TO GET HERE.
  -- =====================================================================

  -- `elem` does not live in `HullElemDown` itself.  It lives one module
  -- deeper, in `WithCode` (src/L/BoundedSubset.lagda.md:681-682), which
  -- asks for a CODE FUNCTION on the hull's members and its spec.  That
  -- pair is the WHOLE price of elementarity at this site, and it is the
  -- only thing the collapse site does not already hold.
  module WithCode (f : HED.A.SM → H.T.Code)
    (f-spec : (q : HED.A.SM) → fst (H.T.val (f q)) ≡ fst q) where

    module HEDC = HED.WithCode f f-spec

    -- The chapter's own term, src/L/BoundedSubset.lagda.md:759-760,
    -- reached from the collapse site with nothing added.
    elem : HED.A.Elementary
    elem = HEDC.elem

    -- THE OBLIGATION.  Elementarity composed with the collapse's own
    -- iso-invariance (src/L/BoundedSubset.lagda.md:250, 350): the
    -- COLLAPSE's reading of a formula and the STAGE's reading of it agree,
    -- in both directions, at every arity.  This is the statement a
    -- consumer at `C.π`'s site can apply; `elem` alone speaks about `M`,
    -- which is the side of the site nobody was stuck on.
    elem-at-collapse :
        (n : ℕ) (φ : Formula CIso.I.SM n) (δ : Vec CIso.I.SM n)
      → (⟨ map CIso.I.g δ CIso.I.⊨ᵖᵐ (mapFo CIso.I.g φ) ⟩
          → ⟨ map HED.A.inL δ ASt.AbsL.⊨ᵐ (mapFo HED.A.inL φ) ⟩)
      × (⟨ map HED.A.inL δ ASt.AbsL.⊨ᵐ (mapFo HED.A.inL φ) ⟩
          → ⟨ map CIso.I.g δ CIso.I.⊨ᵖᵐ (mapFo CIso.I.g φ) ⟩)
    elem-at-collapse n φ δ =
        (λ h → subst ⟨_⟩ (elem n φ δ) (CIso.I.iso-inv-bwd n φ δ h))
      , (λ h → CIso.I.iso-inv n φ δ (subst ⟨_⟩ (sym (elem n φ δ)) h))


    -- =====================================================================
    -- PART 3.  WHAT THE ARRIVAL BUYS AT THE TWO STUCK CONSUMERS.
    -- =====================================================================

    -- A parameter-free formula is fixed by BOTH relabellings.  The `g`
    -- half is [LJ-1.653]'s `embed-fixed` (Probe653.agda:224-228); the
    -- `inL` half is the same argument at the other map, re-measured at
    -- its own site and not transferred by analogy.
    g-fixed : {n : ℕ} (φ₀ : Formula (⊥* {ℓ-suc ℓ}) n)
            → mapFo CIso.I.g (embed φ₀) ≡ embed φ₀
    g-fixed φ₀ =
      mapFo-comp Empty.rec* CIso.I.g φ₀
      ∙ cong (λ h → mapFo h φ₀) (funExt (λ b → Empty.rec* b))

    inL-fixed : {n : ℕ} (φ₀ : Formula (⊥* {ℓ-suc ℓ}) n)
              → mapFo HED.A.inL (embed φ₀) ≡ embed φ₀
    inL-fixed φ₀ =
      mapFo-comp Empty.rec* HED.A.inL φ₀
      ∙ cong (λ h → mapFo h φ₀) (funExt (λ b → Empty.rec* b))

    -- THE FORM THE TWO NO-GOs NAMED AND NEVER HAD.  At a formula with no
    -- constants, the COLLAPSE and the STAGE agree outright, in both
    -- directions.  `[LJ-1.489]`'s verdict was "cannot agree without
    -- elementarity" (agents/tasks/LJ-1-489/lj-1.489-report.md:100); this
    -- is that agreement, and it costs `(f , f-spec)` and nothing else.
    collapse-stage-agree :
        (n : ℕ) (φ₀ : Formula (⊥* {ℓ-suc ℓ}) n) (δ : Vec CIso.I.SM n)
      → (⟨ map CIso.I.g δ CIso.I.⊨ᵖᵐ (embed φ₀) ⟩
          → ⟨ map HED.A.inL δ ASt.AbsL.⊨ᵐ (embed φ₀) ⟩)
      × (⟨ map HED.A.inL δ ASt.AbsL.⊨ᵐ (embed φ₀) ⟩
          → ⟨ map CIso.I.g δ CIso.I.⊨ᵖᵐ (embed φ₀) ⟩)
    collapse-stage-agree n φ₀ δ =
        (λ h → subst (λ ψ → ⟨ map HED.A.inL δ ASt.AbsL.⊨ᵐ ψ ⟩) (inL-fixed φ₀)
                 (elem-at-collapse n (embed φ₀) δ .fst
                   (subst (λ ψ → ⟨ map CIso.I.g δ CIso.I.⊨ᵖᵐ ψ ⟩)
                      (sym (g-fixed φ₀)) h)))
      , (λ h → subst (λ ψ → ⟨ map CIso.I.g δ CIso.I.⊨ᵖᵐ ψ ⟩) (g-fixed φ₀)
                 (elem-at-collapse n (embed φ₀) δ .snd
                   (subst (λ ψ → ⟨ map HED.A.inL δ ASt.AbsL.⊨ᵐ ψ ⟩)
                      (sym (inL-fixed φ₀)) h)))

    -- [LJ-1.653]'s hypothesis 2, the type that predecessor DELIVERED
    -- (agents/tasks/LJ-1-653/Probe653.agda:230-233).
    HoodCompleteP : Formula (⊥* {ℓ-suc ℓ}) 2 → Type (ℓ-suc ℓ)
    HoodCompleteP φ₀ =
      (y : S) (y∈ : ⟨ y ∈ˢ M ⟩) → IsOrd y → (Ly∈ : ⟨ Lset y ∈ˢ M ⟩)
      → ⟨ ((Lset y , Ly∈) ∷ (y , y∈) ∷ []) CIso.I.⊨ᵐ (embed φ₀) ⟩

    -- The SAME statement read at the STAGE.  It names neither `M` nor
    -- `C.π`: it is a fact about `Lset lam` and the level construction,
    -- which is what SECTION 4A of the chapter is about.
    HoodCompleteStage : Formula (⊥* {ℓ-suc ℓ}) 2 → Type (ℓ-suc ℓ)
    HoodCompleteStage φ₀ =
      (y : S) (y∈L : ⟨ y ∈ˢ Lset lam ⟩) → IsOrd y
      → (Ly∈L : ⟨ Lset y ∈ˢ Lset lam ⟩)
      → ⟨ ((Lset y , Ly∈L) ∷ (y , y∈L) ∷ []) ASt.AbsL.⊨ᵐ (embed φ₀) ⟩

    -- ELEMENTARITY DISCHARGES HYPOTHESIS 2 DOWN TO THE STAGE.  The hull
    -- believes the level-hood formula because the STAGE does, and for no
    -- other reason.  [LJ-1.653] had to take this as a priced hypothesis.
    hood-complete-from-stage :
        (φ₀ : Formula (⊥* {ℓ-suc ℓ}) 2)
      → HoodCompleteStage φ₀ → HoodCompleteP φ₀
    hood-complete-from-stage φ₀ st y y∈ oy Ly∈ =
      subst ⟨_⟩ (sym (elem 2 (embed φ₀) δ))
        (subst (λ ψ → ⟨ map HED.A.inL δ ASt.AbsL.⊨ᵐ ψ ⟩) (sym (inL-fixed φ₀))
          (st y (H.Hull⊆L y y∈) oy (H.Hull⊆L (Lset y) Ly∈)))
      where
      δ : Vec HED.A.SM 2
      δ = (Lset y , Ly∈) ∷ (y , y∈) ∷ []

-- THE OBLIGATION, at this module's own top level, so the witness reaches
-- it by the bare name the brief declares.  The type is the one signed
-- above; Agda copies it through the two telescopes.
elem-at-collapse = AtCollapse.WithCode.elem-at-collapse

-- =====================================================================
-- PART 4.  THE PRICE IS ALREADY PAID IN THE TREE.
-- =====================================================================

-- `(f , f-spec)` is not a new obligation.  The chapter builds exactly
-- this pair at its own consumer, `src/L/BoundedSubset.lagda.md:1651`
-- and `:1655`, from `CanonCode` at the delivered code count, and feeds
-- it to `HullElemDown.WithCode` at `:1665` beside `HS.C.π`.  The two
-- lines below are that citation, MACHINE-CHECKED: they name the
-- chapter's own terms and nothing else.  If either name moved, this
-- probe would go red.
chapter-hedF = Devlin55.BoundedSubsetAt.hedF
chapter-hedF-spec = Devlin55.BoundedSubsetAt.hedF-spec

-- And the chapter's own `WithCode` instance, at the same telescope as
-- its `HullStage`.  src/L/BoundedSubset.lagda.md:1664-1665.
chapter-elem-down = Devlin55.BoundedSubsetAt.elem-down

-- =====================================================================
-- PART 5.  THE ARRIVAL AT THE CHAPTER'S OWN CONSUMER, UNCONDITIONAL.
-- =====================================================================

-- PART 2 prices elementarity at the collapse site as `(f , f-spec)`.
-- This module SPENDS the chapter's own pair, at the chapter's own
-- telescope (src/L/BoundedSubset.lagda.md:1385-1396), so nothing below
-- is a hypothesis this campaign has to buy.  `UK` and the collapse site
-- are built exactly as the chapter builds them at `:1520-1521`.
module AtChapterSite
  (κ : S) (ordκ : IsOrd κ) (cardκ : IsCardinal κ) (κ∉ω : ⟨ κ ∈ˢ ω ⟩ → Empty.⊥)
  (α : S) (ordα : IsOrd α) (α∈κ : ⟨ α ∈ˢ κ ⟩) (α∉ω : ⟨ α ∈ˢ ω ⟩ → Empty.⊥)
  (sq : (δ : S) → ⟨ δ ∈ˢ sucV α ⟩ → (⟨ δ ∈ˢ ω ⟩ → Empty.⊥)
      → Σ[ f ∈ (⟪ δ ⟫ × ⟪ δ ⟫ → ⟪ δ ⟫) ]
          ((u v : ⟪ δ ⟫ × ⟪ δ ⟫) → f u ≡ f v → u ≡ v))
  (x : S) (x⊆Lα : (z : S) → ⟨ z ∈ˢ x ⟩ → ⟨ z ∈ˢ Lset α ⟩)
  (absorbs : ⟪ Lset α ∪ ⁅ x ⁆s ⟫ ↪ ⟪ Lset α ⟫)
  (lam : S) (ordλ : IsOrd lam) (α∈λ : ⟨ α ∈ˢ lam ⟩)
  (succλ : (d : S) → ⟨ d ∈ˢ lam ⟩ → ⟨ sucV d ∈ˢ lam ⟩)
  (x∈Lλ : ⟨ x ∈ˢ Lset lam ⟩) where

  module UK = UnionKit α lam x ordα ordλ α∈λ x⊆Lα x∈Lλ α∉ω
  module AC = AtCollapse lam ordλ succλ UK.X UK.X⊆Lλ UK.∅∈λ

  -- The chapter's own code pair, taken BY NAME and not rebuilt.
  hedF : AC.HED.A.SM → AC.H.T.Code
  hedF = Devlin55.BoundedSubsetAt.hedF
           κ ordκ cardκ κ∉ω α ordα α∈κ α∉ω sq x x⊆Lα absorbs
           lam ordλ α∈λ succλ x∈Lλ

  hedF-spec : (q : AC.HED.A.SM) → fst (AC.H.T.val (hedF q)) ≡ fst q
  hedF-spec = Devlin55.BoundedSubsetAt.hedF-spec
                κ ordκ cardκ κ∉ω α ordα α∈κ α∉ω sq x x⊆Lα absorbs
                lam ordλ α∈λ succλ x∈Lλ

  module W = AC.WithCode hedF hedF-spec

-- THE ANSWER, WITH NO CODE HYPOTHESIS LEFT.  At the chapter's own
-- consumer the collapse's reading of a formula and the stage's reading
-- of it agree, in both directions, at every arity.  Every argument this
-- term still takes is a parameter the chapter's `BoundedSubsetAt`
-- already takes.
elem-at-collapse-free = AtChapterSite.W.elem-at-collapse

-- The same, at a parameter-free formula: the shape `[LJ-1.477]` and
-- `[LJ-1.489]` named as the missing ingredient.
collapse-stage-agree-free = AtChapterSite.W.collapse-stage-agree
