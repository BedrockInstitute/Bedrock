{-# OPTIONS --cubical --safe --guardedness #-}

-- [LJ-1.658] PROBE.  Is the collapse image inside L?  [LJ-1.653]'s
-- fork (a), `C.πX ⊆ L` (agents/tasks/LJ-1-653/lj-1.653-report.md:1).
-- Lands nothing in src/.
--
--   PART 1   The generic core, at an ARBITRARY carrier M.  No hull, no
--            stage, no L.BoundedSubset.  `CoverL` is the weakest
--            hypothesis that closes the target: every collapse VALUE of
--            a member of M is constructible.  `πX⊆L` is the target from
--            it.  W2: the mathematics is written once here and every
--            later row is an instance.
--
--   PART 2   `cover→coverL`.  The chapter's OWN Condense hypothesis
--            (src/L/BoundedSubset.lagda.md:918-920) implies `CoverL`,
--            and it implies it by dropping two of its three components.
--            So fork (a) is NOT new debt: it is a corollary of a
--            hypothesis the chapter already carries.
--
--   PART 3   The site.  The generic core instantiated at the chapter's
--            own HullStage telescope (src/L/BoundedSubset.lagda.md:903-914).
--            This is the obligation, and `pix-in-L` at the bottom of the
--            file is where the witness meter reads it.
--
--   PART 5   WHAT FORK (a) BUYS, and it is the reason the task was
--            funded.  `soundP-from-lset-only` discharges [LJ-1.653]'s
--            `HoodSoundP` (agents/tasks/LJ-1-653/Probe653.agda:235) from
--            THREE things: the chapter's own `cover`, a Δ₀ witness for
--            the level-hood formula, and the CLASS-CARRIER reading of
--            `Lset-only` (src/L/Hierarchy.lagda.md:334-335) at that
--            formula.  Nothing else.  Fork (a) is the ONLY content the
--            transfer between the two carriers needed, and PART 1
--            delivers it from `cover`.
--
--   PART 4   THE MEASURED CONTRAST, and the reason PART 1 does not go
--            through premise 2.  The brief's premise 2 names
--            `πX⊆Lβ` (src/L/BoundedSubset.lagda.md:997).  That term is
--            INSIDE `module Condense`, whose FIRST parameter is
--            `levelIn` (src/L/BoundedSubset.lagda.md:917).  Agda gives
--            no term of a parameterised module without its parameters,
--            so premise 2's route carries `levelIn` whatever its body
--            uses.  `pix-in-L-via-premise2` typechecks and CARRIES that
--            extra hypothesis; PART 3 does not.  `levelIn` is the very
--            fact fork (a) was funded to close, so the difference
--            between the two terms is the whole point of this task.
--
-- ONE Agda process per run, GHCRTS="-A64m -I0 -M2g", the wide caliber,
-- set on the pane by the program and untouched here.

open import Base.Prelude
open import Base.Truth
open import Base.Classical using ( LEM )

module LJ-1-658.Probe658 {ℓ : Level} (lem : LEM (ℓ-suc ℓ)) where

open import FOL.ZFStructure using ( module hPropStructure )
open import FOL.Syntax using ( Formula )
open import FOL.LevyHierarchy using ( Δ₀ )
open import FOL.Manipulation.Relabelling using
  ( mapFo; mapFo-comp; mapΔ₀; embed; ⊨-map )
import FOL.Absoluteness
open import V.Hierarchy {ℓ} using ( 𝒮ᵥ )
open import L.Constructible {ℓ} using ( IsOrd; Lset; isL; isL-trans; Lset→isL )
open import V.Collapse {ℓ} using ( module Collapse; isExt )
open import L.BoundedSubset {ℓ} lem using
  ( module HullStage; module HullExt; module CollapseIso )

import Cubical.Data.Empty as Empty
open import Cubical.Data.Sigma using ( _×_; _,_ )
open import Cubical.Data.Vec using ( _∷_; []; map; lookup )
import Cubical.HITs.PropositionalTruncation as PT
open PT using ( ∥_∥₁ )
open import Cubical.HITs.CumulativeHierarchy.Constructions
  using ( ∅; module InfinitySet )
open InfinitySet using ( sucV )

open TruthAlgebra (hPropAlgebra (ℓ-suc ℓ))
open hPropStructure 𝒮ᵥ

-- =====================================================================
-- PART 1.  The generic core.  M is an ARBITRARY set: no hull, no stage,
-- no extensionality, no ordinal.
-- =====================================================================

module Coll (M : S) where
  module C = Collapse M

  -- The WEAKEST hypothesis that closes the target.  It drops the
  -- ordinal index and the index's own membership in the collapse, both
  -- of which the chapter's `cover` carries and neither of which the
  -- target uses.
  CoverL : Type (ℓ-suc ℓ)
  CoverL = (y : S) → ⟨ y ∈ˢ M ⟩ → ⟨ isL (C.π y) ⟩

  -- The chapter's own hypothesis, copied verbatim from
  -- src/L/BoundedSubset.lagda.md:918-920.
  Cover : Type (ℓ-suc ℓ)
  Cover = (y : S) → ⟨ y ∈ˢ M ⟩
        → ∥ Σ[ γ ∈ S ] (IsOrd γ × ⟨ γ ∈ˢ C.πX ⟩ × ⟨ C.π y ∈ˢ Lset γ ⟩) ∥₁

  -- The target, as a type, so PART 3 and PART 4 state the SAME thing.
  PiXinL : Type (ℓ-suc ℓ)
  PiXinL = (x : S) → ⟨ x ∈ˢ C.πX ⟩ → ⟨ isL x ⟩

  -- THE CORE.  Every member of the collapse image is the collapse value
  -- of a member of M (C.πX-member, src/V/Collapse.lagda.md:78-84), and
  -- CoverL says every such value is constructible.
  πX⊆L : CoverL → PiXinL
  πX⊆L cl x x∈πX = PT.rec (snd (isL x)) go (C.πX-member x x∈πX)
    where
    go : Σ[ y ∈ S ] (⟨ y ∈ˢ M ⟩ × (C.π y ≡ x)) → ⟨ isL x ⟩
    go (y , y∈M , e) = subst (λ w → ⟨ isL w ⟩) e (cl y y∈M)

  -- =====================================================================
  -- PART 2.  The chapter's hypothesis is already enough.
  -- =====================================================================

  -- Lset→isL (src/L/Constructible.lagda.md:405-406) is the whole body.
  -- The ordinal index the chapter carries is used, and its membership in
  -- C.πX is DISCARDED: `_` in the pattern is the measurement.
  cover→coverL : Cover → CoverL
  cover→coverL cov y y∈M = PT.rec (snd (isL (C.π y))) go (cov y y∈M)
    where
    go : Σ[ γ ∈ S ] (IsOrd γ × ⟨ γ ∈ˢ C.πX ⟩ × ⟨ C.π y ∈ˢ Lset γ ⟩)
       → ⟨ isL (C.π y) ⟩
    go (γ , oγ , _ , h) = Lset→isL γ oγ (C.π y) h

  πX⊆L-from-cover : Cover → PiXinL
  πX⊆L-from-cover cov = πX⊆L (cover→coverL cov)

-- =====================================================================
-- PART 3.  THE SITE.  The chapter's own telescope, copied from
-- src/L/BoundedSubset.lagda.md:903-905, and nothing below :914.
-- =====================================================================

module Site (lam : S) (ordλ : IsOrd lam)
  (succλ : (d : S) → ⟨ d ∈ˢ lam ⟩ → ⟨ sucV d ∈ˢ lam ⟩)
  (X : S) (X⊆L : (x : S) → ⟨ x ∈ˢ X ⟩ → ⟨ x ∈ˢ Lset lam ⟩)
  (∅∈λ : ⟨ ∅ ∈ˢ lam ⟩) where

  module HS = HullStage lam ordλ succλ X X⊆L ∅∈λ
  module K = Coll HS.M

  -- The chapter's `cover`, at the chapter's own M and C.  Nothing is
  -- restated: this is PART 1's type at HS.M.
  Cover : Type (ℓ-suc ℓ)
  Cover = K.Cover

  -- The brief's obligation, as a type.
  Target : Type (ℓ-suc ℓ)
  Target = (x : S) → ⟨ x ∈ˢ HS.C.πX ⟩ → ⟨ isL x ⟩

  -- THE OBLIGATION AT THE SITE.  `Coll HS.M`'s C and `HullStage`'s C are
  -- the SAME `Collapse HS.M`, so no transport is needed between them:
  -- the body is PART 1's term applied and nothing else.  This answers
  -- the brief's premise 4, which expected a transport and priced it at
  -- 40 to 100 lines: the transport is ZERO lines, because the generic
  -- core was written at the carrier the site already uses.
  pix-in-L-at : Cover → Target
  pix-in-L-at cov = K.πX⊆L-from-cover cov

  -- =====================================================================
  -- PART 4.  Premise 2's route, and the hypothesis it cannot drop.
  -- =====================================================================

  -- `levelIn`, the FIRST parameter of module Condense
  -- (src/L/BoundedSubset.lagda.md:917).  Same type as
  -- agents/tasks/LJ-1-653/Probe653.agda:269-270.
  LevelIn : Type (ℓ-suc ℓ)
  LevelIn = (δ : S) → IsOrd δ → ⟨ δ ∈ˢ HS.C.πX ⟩ → ⟨ Lset δ ∈ˢ HS.C.πX ⟩

  -- THE CONTRAST, AND IT IS A MEASUREMENT AND NOT A CLAIM.  This term
  -- reaches the target through the brief's premise 2, `πX⊆Lβ`
  -- (src/L/BoundedSubset.lagda.md:997), and it typechecks.  It takes
  -- LevelIn, which `pix-in-L-at` above does NOT.  The body of `πX⊆Lβ`
  -- never mentions `levelIn`; the MODULE does, and that is enough to
  -- make premise 2 unusable for the purpose fork (a) was funded for.
  pix-in-L-via-premise2 : LevelIn → Cover → Target
  pix-in-L-via-premise2 li cov x x∈πX =
    Lset→isL Cd.β Cd.β-isOrd x (Cd.πX⊆Lβ x x∈πX)
    where
    module Cd = HS.Condense li cov

  -- =====================================================================
  -- PART 5.  WHAT FORK (a) BUYS: HoodSoundP, from cover and the
  -- class-carrier Lset-only, with NO further absoluteness work.
  -- =====================================================================

  -- The hull is extensional.  DELIVERED, src/L/BoundedSubset.lagda.md:1340.
  module HE = HullExt lam ordλ X X⊆L ∅∈λ

  Mext : isExt HS.M
  Mext = HE.hullExt

  module CIso = CollapseIso HS.M Mext

  -- The two restricted carriers.  AbsπX is [LJ-1.653]'s leg 1
  -- (agents/tasks/LJ-1-653/Probe653.agda:156); AbsL is the chapter's own
  -- class carrier, src/L/Hierarchy.lagda.md:78.
  module AbsπX = FOL.Absoluteness.Single 𝒮ᵥ (λ x → x ∈ˢ HS.C.πX) HS.C.πX-trans
  module AbsL  = FOL.Absoluteness.Single 𝒮ᵥ isL isL-trans
  open AbsL using ( _^_ )

  -- FORK (a) AS A MAP OF CARRIERS.  This is the whole content this task
  -- adds to the transfer: a member of the collapse is a member of L,
  -- with the SAME underlying set.  `fst (toL cov k)` is `fst k` by eta,
  -- which is what makes the relabelling below cost nothing.
  -- IT TAKES `Target` AND NOT `Cover`, AND THAT IS THE MEASUREMENT.
  -- The only way a parameter crosses from the collapse's carrier to the
  -- class carrier is this map, and its type IS fork (a).  Nothing weaker
  -- than `C.πX ⊆ L` inhabits it.
  toL : Target → CIso.I.SPM → AbsL.SM
  toL pil k = fst k , pil (fst k) (snd k)

  -- The class-carrier reading of Lset-only (src/L/Hierarchy.lagda.md:334-335)
  -- at a pinned parameter-free formula, read at w = zero, b = suc zero.
  -- PINNING φ₀ IS THE CHAPTER'S OWN RESIDUE (src/L/BoundedSubset.lagda.md:901-902)
  -- and is not this task's work, so it is a hypothesis here.
  LsetOnlyAt : Formula (⊥* {ℓ-suc ℓ}) 2 → Type (ℓ-suc ℓ)
  LsetOnlyAt φ₀ = (γL : AbsL.SM ^ 2)
                → ⟨ γL AbsL.⊨ᵐ (embed φ₀) ⟩
                → IsOrd (fst (lookup (suc zero) γL))
                → fst (lookup zero γL) ≡ Lset (fst (lookup (suc zero) γL))

  -- [LJ-1.653]'s HoodSoundP, verbatim (Probe653.agda:235-239).
  HoodSoundP : Formula (⊥* {ℓ-suc ℓ}) 2 → Type (ℓ-suc ℓ)
  HoodSoundP φ₀ =
    (v γ : S) (v∈ : ⟨ v ∈ˢ HS.C.πX ⟩) (γ∈ : ⟨ γ ∈ˢ HS.C.πX ⟩) → IsOrd γ
    → ⟨ ((v , v∈) ∷ (γ , γ∈) ∷ []) CIso.I.⊨ᵖᵐ (embed φ₀) ⟩
    → v ≡ Lset γ

  -- LEG 2, DISCHARGED.  The chain is: the inner reading at C.πX equals
  -- the ambient reading (AbsπX.abs₀, leg 1, free); the ambient reading
  -- does not see which constant domain carries it (⊨-map along toL, plus
  -- the parameter-free fixpoint); the ambient reading equals the inner
  -- reading at L (AbsL.abs₀, backwards); and Lset-only reads it off.
  soundP-from-pix : (φ₀ : Formula (⊥* {ℓ-suc ℓ}) 2) → Δ₀ φ₀
                  → Target → LsetOnlyAt φ₀ → HoodSoundP φ₀
  soundP-from-pix φ₀ dφ pil only v γ v∈ γ∈ oγ h = only γL inner oγ
    where
    f : CIso.I.SPM → AbsL.SM
    f = toL pil

    δ : CIso.I.SPM ^ 2
    δ = (v , v∈) ∷ (γ , γ∈) ∷ []

    γL : AbsL.SM ^ 2
    γL = map f δ

    -- The parameter-free fixpoint, [LJ-1.653]'s embed-fixed
    -- (Probe653.agda:224-228) at this map of carriers.
    embed-fixed : mapFo f (embed φ₀) ≡ embed φ₀
    embed-fixed =
      mapFo-comp Empty.rec* f φ₀
      ∙ cong (λ g → mapFo g φ₀) (funExt (λ b → Empty.rec* b))

    -- Leg 1: out of the collapse's own reading, into the ambient one.
    amb-πX : ⟨ (map fst δ) AbsπX.⊨ᵛ (embed φ₀) ⟩
    amb-πX = subst ⟨_⟩ (AbsπX.abs₀ (mapΔ₀ Empty.rec* dφ) δ) h

    -- The constant domain does not survive into the ambient reading.
    amb-L : ⟨ (map fst δ) AbsL.⊨ᵛ (embed φ₀) ⟩
    amb-L = subst ⟨_⟩
      (sym (cong (λ ψ → (map fst δ) AbsL.⊨ᵛ ψ) (sym embed-fixed)
             ∙ ⊨-map (hPropAlgebra (ℓ-suc ℓ)) 𝒮ᵥ f fst (embed φ₀) (map fst δ)))
      amb-πX

    -- Back into the class carrier's own reading.
    inner : ⟨ γL AbsL.⊨ᵐ (embed φ₀) ⟩
    inner = subst ⟨_⟩ (sym (AbsL.abs₀ (mapΔ₀ Empty.rec* dφ) γL)) amb-L

  -- The same, from the chapter's own hypothesis, through PART 3.
  soundP-from-lset-only : (φ₀ : Formula (⊥* {ℓ-suc ℓ}) 2) → Δ₀ φ₀
                        → Cover → LsetOnlyAt φ₀ → HoodSoundP φ₀
  soundP-from-lset-only φ₀ dφ cov = soundP-from-pix φ₀ dφ (pix-in-L-at cov)

-- =====================================================================
-- THE OBLIGATION AT THE TOP LEVEL, where the witness meter reads it
-- (`witness = Target.<dotted-name>`, scripts/pod/witness.py:278).
-- =====================================================================

pix-in-L : (lam : S) (ordλ : IsOrd lam)
  (succλ : (d : S) → ⟨ d ∈ˢ lam ⟩ → ⟨ sucV d ∈ˢ lam ⟩)
  (X : S) (X⊆L : (x : S) → ⟨ x ∈ˢ X ⟩ → ⟨ x ∈ˢ Lset lam ⟩)
  (∅∈λ : ⟨ ∅ ∈ˢ lam ⟩)
  → Site.Cover lam ordλ succλ X X⊆L ∅∈λ
  → Site.Target lam ordλ succλ X X⊆L ∅∈λ
pix-in-L = Site.pix-in-L-at

-- The same target through premise 2, carrying the hypothesis fork (a)
-- was funded to CLOSE.  Kept green so the contrast is checkable.
pix-in-L-premise2-price : (lam : S) (ordλ : IsOrd lam)
  (succλ : (d : S) → ⟨ d ∈ˢ lam ⟩ → ⟨ sucV d ∈ˢ lam ⟩)
  (X : S) (X⊆L : (x : S) → ⟨ x ∈ˢ X ⟩ → ⟨ x ∈ˢ Lset lam ⟩)
  (∅∈λ : ⟨ ∅ ∈ˢ lam ⟩)
  → Site.LevelIn lam ordλ succλ X X⊆L ∅∈λ
  → Site.Cover lam ordλ succλ X X⊆L ∅∈λ
  → Site.Target lam ordλ succλ X X⊆L ∅∈λ
pix-in-L-premise2-price = Site.pix-in-L-via-premise2


-- Leg 2 of HoodSoundP, at the top level.  The obligation `pix-in-L` is
-- its only new input; everything else is delivered or is the chapter's
-- own named residue.
soundP-leg2 : (lam : S) (ordλ : IsOrd lam)
  (succλ : (d : S) → ⟨ d ∈ˢ lam ⟩ → ⟨ sucV d ∈ˢ lam ⟩)
  (X : S) (X⊆L : (x : S) → ⟨ x ∈ˢ X ⟩ → ⟨ x ∈ˢ Lset lam ⟩)
  (∅∈λ : ⟨ ∅ ∈ˢ lam ⟩)
  (φ₀ : Formula (⊥* {ℓ-suc ℓ}) 2) → Δ₀ φ₀
  → Site.Cover lam ordλ succλ X X⊆L ∅∈λ
  → Site.LsetOnlyAt lam ordλ succλ X X⊆L ∅∈λ φ₀
  → Site.HoodSoundP lam ordλ succλ X X⊆L ∅∈λ φ₀
soundP-leg2 = Site.soundP-from-lset-only

-- The same leg, from fork (a) ALONE.  This is the campaign statement:
-- `C.πX ⊆ L` is the ONLY new input HoodSoundP leg 2 needs.
soundP-leg2-from-pix : (lam : S) (ordλ : IsOrd lam)
  (succλ : (d : S) → ⟨ d ∈ˢ lam ⟩ → ⟨ sucV d ∈ˢ lam ⟩)
  (X : S) (X⊆L : (x : S) → ⟨ x ∈ˢ X ⟩ → ⟨ x ∈ˢ Lset lam ⟩)
  (∅∈λ : ⟨ ∅ ∈ˢ lam ⟩)
  (φ₀ : Formula (⊥* {ℓ-suc ℓ}) 2) → Δ₀ φ₀
  → Site.Target lam ordλ succλ X X⊆L ∅∈λ
  → Site.LsetOnlyAt lam ordλ succλ X X⊆L ∅∈λ φ₀
  → Site.HoodSoundP lam ordλ succλ X X⊆L ∅∈λ φ₀
soundP-leg2-from-pix = Site.soundP-from-pix
