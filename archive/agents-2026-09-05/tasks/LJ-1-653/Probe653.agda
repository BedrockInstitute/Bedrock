{-# OPTIONS --cubical --safe --guardedness #-}

-- [LJ-1.653] PROBE.  Is [LJ-1.462]'s step 4 TRUE at ordinals, before
-- anyone prices its proof (D-10).  Lands nothing in src/.
--
--   PART 1   π-member-in.  The tree's π-member (src/V/Collapse.lagda.md:63-71)
--            drops the witness's membership in the ARGUMENT.  This
--            restatement keeps it.  Green.
--
--   PART 2   π-trans and π-ord.  The collapse carries transitivity and
--            ordinality FORWARD, unconditionally.  Green, and NEW: the
--            tree had πX-trans (src/V/Collapse.lagda.md:89) for the RANGE
--            only, and [LJ-1.649] named the CONVERSE (PiReflectsOrd,
--            agents/tasks/LJ-1-649/Probe649.agda:222-223) as unbuilt.
--            Without π-ord the target's own right-hand side, Lset (C.π y),
--            is not known to be a level at all.
--
--   PART 2b  hoodSound-Δ₀-leg.  MEASURED: the Δ₀ transfer between the
--            collapse and the AMBIENT hierarchy costs nothing, because
--            C.πX is transitive and CollapseIso reads the SAME restricted
--            structure FOL.Absoluteness.Single builds.  This prices one
--            of PART 3's two hypotheses down to a single remaining leg.
--
--   PART 3   step4-at-ord-status.  THE OBLIGATION.  Step 4 restricted to
--            ordinal y, from the elementarity route: the level-hood
--            formula complete at M, sound at C.πX, and [LJ-1.647]'s
--            step 2.  The transfer between the two carriers is the
--            tree's own iso-invariance, CollapseIso.I.iso-inv
--            (src/L/BoundedSubset.lagda.md:195-196, 350).
--
--   PART 4   levelin-from-hood.  The SAME adequacy pair discharges the
--            consumer's own goal with no step 4 in the chain.  This is
--            what re-plans the campaign: step 4 is not an independent
--            obstruction, it shares levelIn's one residue.
--
-- ONE Agda process per run, GHCRTS="-A64m -I0 -M2g", the wide caliber,
-- set on the pane by the program and untouched here.

open import Base.Prelude
open import Base.Truth
open import Base.Classical using ( LEM )

module LJ-1-653.Probe653 {ℓ : Level} (lem : LEM (ℓ-suc ℓ)) where

open import FOL.ZFStructure using ( module hPropStructure )
open import FOL.Syntax using ( Formula )
open import FOL.LevyHierarchy using ( Δ₀ )
import FOL.Absoluteness
open import FOL.Manipulation.Relabelling using ( mapFo; mapFo-comp; embed )
open import V.Hierarchy {ℓ} using ( 𝒮ᵥ )
open import V.Presentation {ℓ} using ( member )
open import L.Constructible {ℓ} using ( IsOrd; isTransV; Lset )
open import L.Hull {ℓ} lem using ( module AtStage )
open import V.Collapse {ℓ} using ( module Collapse; isExt )
open import L.BoundedSubset {ℓ} lem using ( module HullExt; module CollapseIso )

import Cubical.Data.Empty as Empty
open import Cubical.Data.Sigma using ( _×_; _,_ )
open import Cubical.Data.Vec using ( _∷_; []; map )
import Cubical.HITs.PropositionalTruncation as PT
open PT using ( ∥_∥₁; ∣_∣₁ )
open import Cubical.HITs.CumulativeHierarchy.Constructions
  using ( ∅; module InfinitySet )
open import Cubical.HITs.CumulativeHierarchy.Properties
  using ( ∈∈ₛ; ⟪_⟫↪ )
open InfinitySet using ( sucV )

open TruthAlgebra (hPropAlgebra (ℓ-suc ℓ))
open hPropStructure 𝒮ᵥ

-- Telescope copied from src/L/BoundedSubset.lagda.md:903-916, the same
-- cut as Probe477.agda:44-57 and Probe462.agda:78-90.  Nothing below
-- `module Condense` (:916) is copied.
module HullStage (lam : S) (ordλ : IsOrd lam)
  (succλ : (d : S) → ⟨ d ∈ˢ lam ⟩ → ⟨ sucV d ∈ˢ lam ⟩)
  (X : S) (X⊆L : (x : S) → ⟨ x ∈ˢ X ⟩ → ⟨ x ∈ˢ Lset lam ⟩)
  (∅∈λ : ⟨ ∅ ∈ˢ lam ⟩) where

  module ASt = AtStage lam ordλ

  module H = ASt.Hull X X⊆L ∅∈λ

  M : S
  M = H.T.Hull

  module C = Collapse M

  -- The hull is extensional.  DELIVERED, src/L/BoundedSubset.lagda.md:1340.
  -- No hypothesis is taken for it here, and none is needed.
  module HE = HullExt lam ordλ X X⊆L ∅∈λ

  Mext : isExt M
  Mext = HE.hullExt

  -- The collapse as an isomorphism of structures, and the satisfaction
  -- transfer along it.  DELIVERED, src/L/BoundedSubset.lagda.md:321-350.
  module CIso = CollapseIso M Mext

  -- =====================================================================
  -- PART 1.  The member readback, with the argument membership kept.
  -- =====================================================================

  π-member-in : (x z : S) → ⟨ z ∈ˢ C.π x ⟩
              → ∥ Σ[ y ∈ S ] (⟨ y ∈ˢ M ⟩ × ⟨ y ∈ˢ x ⟩ × (C.π y ≡ z)) ∥₁
  π-member-in x z z∈ =
    PT.map mk (subst (λ w → ⟨ z ∈ˢ w ⟩) (C.π-compute x) z∈)
    where
    mk : Σ[ p ∈ C.Fiber x ] (C.π (⟪ x ⟫↪ (p .fst)) ≡ z)
       → Σ[ y ∈ S ] (⟨ y ∈ˢ M ⟩ × ⟨ y ∈ˢ x ⟩ × (C.π y ≡ z))
    mk (p , q) = ⟪ x ⟫↪ (p .fst)
               , ( ∈∈ₛ {a = ⟪ x ⟫↪ (p .fst)} {b = M} .snd (p .snd)
                 , member x (p .fst)
                 , q )

  -- =====================================================================
  -- PART 2.  The collapse carries transitivity and ordinality forward.
  -- =====================================================================

  π-trans : (x : S) → isTransV x → isTransV (C.π x)
  π-trans x tx {u} {v} v∈u u∈πx =
    PT.rec (snd (v ∈ˢ C.π x)) go (π-member-in x u u∈πx)
    where
    go : Σ[ w ∈ S ] (⟨ w ∈ˢ M ⟩ × ⟨ w ∈ˢ x ⟩ × (C.π w ≡ u))
       → ⟨ v ∈ˢ C.π x ⟩
    go (w , w∈M , w∈x , e) =
      PT.rec (snd (v ∈ˢ C.π x)) go₂ (π-member-in w v v∈πw)
      where
      v∈πw : ⟨ v ∈ˢ C.π w ⟩
      v∈πw = subst (λ z → ⟨ v ∈ˢ z ⟩) (sym e) v∈u
      go₂ : Σ[ a ∈ S ] (⟨ a ∈ˢ M ⟩ × ⟨ a ∈ˢ w ⟩ × (C.π a ≡ v))
          → ⟨ v ∈ˢ C.π x ⟩
      go₂ (a , a∈M , a∈w , f) =
        subst (λ z → ⟨ z ∈ˢ C.π x ⟩) f
          (C.π∈-fwd x a (tx {x = w} {y = a} a∈w w∈x) a∈M)

  π-ord : (x : S) → IsOrd x → IsOrd (C.π x)
  π-ord x ox = π-trans x (ox .fst) , mem
    where
    mem : (b : S) → ⟨ b ∈ˢ C.π x ⟩ → isTransV b
    mem b b∈ {u} {v} v∈u u∈b =
      PT.rec (snd (v ∈ˢ b)) go (π-member-in x b b∈)
      where
      go : Σ[ w ∈ S ] (⟨ w ∈ˢ M ⟩ × ⟨ w ∈ˢ x ⟩ × (C.π w ≡ b)) → ⟨ v ∈ˢ b ⟩
      go (w , w∈M , w∈x , e) =
        subst (λ z → ⟨ v ∈ˢ z ⟩) e
          (π-trans w (ox .snd w w∈x) {x = u} {y = v} v∈u
            (subst (λ z → ⟨ u ∈ˢ z ⟩) (sym e) u∈b))

  -- MEASURED, AND IT IS THE NEXT BRIEF'S NUMBER.  The Δ₀ transfer between
  -- the collapse and the AMBIENT hierarchy is free: C.πX is transitive
  -- (src/V/Collapse.lagda.md:89) and transitivity is the only hypothesis
  -- FOL.Absoluteness.Single asks for (src/FOL/Absoluteness.lagda.md:57-59).
  -- The restricted structure the absoluteness module builds is the SAME
  -- one CollapseIso reads, so abs₀ lands on HoodSoundP's antecedent with
  -- no adapter at all: the term below is `AbsπX.abs₀` and nothing else.
  module AbsπX = FOL.Absoluteness.Single 𝒮ᵥ (λ x → x ∈ˢ C.πX) C.πX-trans
  open AbsπX using ( _^_ )

  hoodSound-Δ₀-leg : ∀ {n} {φ : Formula CIso.I.SPM n} → Δ₀ φ
                   → (δ : CIso.I.SPM ^ n)
                   → (δ CIso.I.⊨ᵖᵐ φ) ≡ ((map fst δ) AbsπX.⊨ᵛ φ)
  hoodSound-Δ₀-leg = AbsπX.abs₀

  -- =====================================================================
  -- PART 3.  THE OBLIGATION.
  -- =====================================================================

  -- [LJ-1.647]'s delivered step 2, as a hypothesis.  The type is the one
  -- that predecessor DELIVERED (agents/tasks/LJ-1-647/Probe647.agda:165-167),
  -- restated at agents/tasks/LJ-1-649/Probe649.agda:216-217.
  HullClosedLsetOrd : Type (ℓ-suc ℓ)
  HullClosedLsetOrd = (y : S) → ⟨ y ∈ˢ M ⟩ → IsOrd y → ⟨ Lset y ∈ˢ M ⟩

  -- The target.  [LJ-1.462]'s step 4 (Probe462.agda:140-142), restricted
  -- to ordinal y.  Same type as [LJ-1.649]'s PiCommuteLsetOrd
  -- (Probe649.agda:233-235).
  PiCommuteLsetOrd : Type (ℓ-suc ℓ)
  PiCommuteLsetOrd =
    (y : S) → ⟨ y ∈ˢ M ⟩ → IsOrd y → C.π (Lset y) ≡ Lset (C.π y)

  -- The level-hood formula, at the hull's own constants.  Slot zero is
  -- the value, slot one the ordinal index: "v is the level at γ".  The
  -- concrete formula is the chapter's LevelHood0 shape
  -- (src/L/BoundedSubset.lagda.md:840-859); nothing here depends on
  -- which formula it is.
  HoodComplete : Formula CIso.I.SM 2 → Type (ℓ-suc ℓ)
  HoodComplete φ =
    (y : S) (y∈ : ⟨ y ∈ˢ M ⟩) → IsOrd y → (Ly∈ : ⟨ Lset y ∈ˢ M ⟩)
    → ⟨ ((Lset y , Ly∈) ∷ (y , y∈) ∷ []) CIso.I.⊨ᵐ φ ⟩

  HoodSound : Formula CIso.I.SM 2 → Type (ℓ-suc ℓ)
  HoodSound φ =
    (v γ : S) (v∈ : ⟨ v ∈ˢ C.πX ⟩) (γ∈ : ⟨ γ ∈ˢ C.πX ⟩) → IsOrd γ
    → ⟨ ((v , v∈) ∷ (γ , γ∈) ∷ []) CIso.I.⊨ᵖᵐ (mapFo CIso.I.g φ) ⟩
    → v ≡ Lset γ

  -- THE ANSWER.  Step 4 IS TRUE at ordinals whenever the level-hood
  -- formula is complete at M and sound at C.πX.  Neither half is step 4,
  -- and neither half mentions Lset ∘ π or π ∘ Lset.
  step4-at-ord : (φ : Formula CIso.I.SM 2)
               → HoodComplete φ → HoodSound φ
               → HullClosedLsetOrd
               → PiCommuteLsetOrd
  step4-at-ord φ comp sound hcl y y∈ oy =
    sound (C.π (Lset y)) (C.π y) v∈ γ∈ (π-ord y oy) transferred
    where
    Ly∈ : ⟨ Lset y ∈ˢ M ⟩
    Ly∈ = hcl y y∈ oy
    v∈ : ⟨ C.π (Lset y) ∈ˢ C.πX ⟩
    v∈ = C.πX-intro (Lset y) Ly∈
    γ∈ : ⟨ C.π y ∈ˢ C.πX ⟩
    γ∈ = C.πX-intro y y∈
    transferred : ⟨ ((C.π (Lset y) , v∈) ∷ (C.π y , γ∈) ∷ [])
                     CIso.I.⊨ᵖᵐ (mapFo CIso.I.g φ) ⟩
    transferred = CIso.I.iso-inv 2 φ ((Lset y , Ly∈) ∷ (y , y∈) ∷ [])
                    (comp y y∈ oy Ly∈)

  -- THE SAME, WITH THE FORMULA PINNED PARAMETER-FREE.  This is the shape
  -- the chapter's own level-hood carries (`embed isOrdAt`,
  -- src/L/BoundedSubset.lagda.md:866), and it is the shape that makes the
  -- reduction decisive: neither half below mentions C.π, so neither half
  -- is step 4 in disguise.  The relabelling along the collapse fixes a
  -- parameter-free formula.
  embed-fixed : (φ₀ : Formula (⊥* {ℓ-suc ℓ}) 2)
              → mapFo CIso.I.g (embed φ₀) ≡ embed φ₀
  embed-fixed φ₀ =
    mapFo-comp Empty.rec* CIso.I.g φ₀
    ∙ cong (λ f → mapFo f φ₀) (funExt (λ b → Empty.rec* b))

  HoodCompleteP : Formula (⊥* {ℓ-suc ℓ}) 2 → Type (ℓ-suc ℓ)
  HoodCompleteP φ₀ =
    (y : S) (y∈ : ⟨ y ∈ˢ M ⟩) → IsOrd y → (Ly∈ : ⟨ Lset y ∈ˢ M ⟩)
    → ⟨ ((Lset y , Ly∈) ∷ (y , y∈) ∷ []) CIso.I.⊨ᵐ (embed φ₀) ⟩

  HoodSoundP : Formula (⊥* {ℓ-suc ℓ}) 2 → Type (ℓ-suc ℓ)
  HoodSoundP φ₀ =
    (v γ : S) (v∈ : ⟨ v ∈ˢ C.πX ⟩) (γ∈ : ⟨ γ ∈ˢ C.πX ⟩) → IsOrd γ
    → ⟨ ((v , v∈) ∷ (γ , γ∈) ∷ []) CIso.I.⊨ᵖᵐ (embed φ₀) ⟩
    → v ≡ Lset γ

  soundP→sound : (φ₀ : Formula (⊥* {ℓ-suc ℓ}) 2)
               → HoodSoundP φ₀ → HoodSound (embed φ₀)
  soundP→sound φ₀ sound v γ v∈ γ∈ oγ h =
    sound v γ v∈ γ∈ oγ
      (subst (λ ψ → ⟨ ((v , v∈) ∷ (γ , γ∈) ∷ []) CIso.I.⊨ᵖᵐ ψ ⟩)
             (embed-fixed φ₀) h)

  step4-at-ord-pf : (φ₀ : Formula (⊥* {ℓ-suc ℓ}) 2)
                  → HoodCompleteP φ₀ → HoodSoundP φ₀
                  → HullClosedLsetOrd
                  → PiCommuteLsetOrd
  step4-at-ord-pf φ₀ comp sound =
    step4-at-ord (embed φ₀) comp (soundP→sound φ₀ sound)

  -- =====================================================================
  -- PART 4.  The same adequacy pair, at the consumer's own goal, with
  -- no step 4 in the chain and no step 2 either.
  -- =====================================================================

  -- The existential half at the collapse: the collapse believes every
  -- one of its ordinals has a level.  This is what elementarity plus
  -- iso-invariance deliver from `Lset lam ⊨ ∃v levelHood(v, γ)`.
  HoodExists : Formula CIso.I.SM 2 → Type (ℓ-suc ℓ)
  HoodExists φ =
    (γ : S) (γ∈ : ⟨ γ ∈ˢ C.πX ⟩) → IsOrd γ
    → ∥ Σ[ v ∈ S ] Σ[ v∈ ∈ ⟨ v ∈ˢ C.πX ⟩ ]
         ⟨ ((v , v∈) ∷ (γ , γ∈) ∷ []) CIso.I.⊨ᵖᵐ (mapFo CIso.I.g φ) ⟩ ∥₁

  LevelIn : Type (ℓ-suc ℓ)
  LevelIn = (δ : S) → IsOrd δ → ⟨ δ ∈ˢ C.πX ⟩ → ⟨ Lset δ ∈ˢ C.πX ⟩

  levelin-from-hood : (φ : Formula CIso.I.SM 2)
                    → HoodExists φ → HoodSound φ → LevelIn
  levelin-from-hood φ ex sound δ oδ δ∈ =
    PT.rec (snd (Lset δ ∈ˢ C.πX)) go (ex δ δ∈ oδ)
    where
    go : Σ[ v ∈ S ] Σ[ v∈ ∈ ⟨ v ∈ˢ C.πX ⟩ ]
           ⟨ ((v , v∈) ∷ (δ , δ∈) ∷ []) CIso.I.⊨ᵖᵐ (mapFo CIso.I.g φ) ⟩
       → ⟨ Lset δ ∈ˢ C.πX ⟩
    go (v , v∈ , h) =
      subst (λ z → ⟨ z ∈ˢ C.πX ⟩) (sound v δ v∈ δ∈ oδ h) v∈

  HoodExistsP : Formula (⊥* {ℓ-suc ℓ}) 2 → Type (ℓ-suc ℓ)
  HoodExistsP φ₀ =
    (γ : S) (γ∈ : ⟨ γ ∈ˢ C.πX ⟩) → IsOrd γ
    → ∥ Σ[ v ∈ S ] Σ[ v∈ ∈ ⟨ v ∈ˢ C.πX ⟩ ]
         ⟨ ((v , v∈) ∷ (γ , γ∈) ∷ []) CIso.I.⊨ᵖᵐ (embed φ₀) ⟩ ∥₁

  levelin-from-hood-pf : (φ₀ : Formula (⊥* {ℓ-suc ℓ}) 2)
                       → HoodExistsP φ₀ → HoodSoundP φ₀ → LevelIn
  levelin-from-hood-pf φ₀ ex sound δ oδ δ∈ =
    PT.rec (snd (Lset δ ∈ˢ C.πX)) go (ex δ δ∈ oδ)
    where
    go : Σ[ v ∈ S ] Σ[ v∈ ∈ ⟨ v ∈ˢ C.πX ⟩ ]
           ⟨ ((v , v∈) ∷ (δ , δ∈) ∷ []) CIso.I.⊨ᵖᵐ (embed φ₀) ⟩
       → ⟨ Lset δ ∈ˢ C.πX ⟩
    go (v , v∈ , h) =
      subst (λ z → ⟨ z ∈ˢ C.πX ⟩) (sound v δ v∈ δ∈ oδ h) v∈

-- =====================================================================
-- THE OBLIGATION AT THE TOP LEVEL, where the witness meter reads it
-- (`witness = Target.<dotted-name>`, scripts/pod/witness.py:278).
-- =====================================================================

step4-at-ord-status : (lam : S) (ordλ : IsOrd lam)
  (succλ : (d : S) → ⟨ d ∈ˢ lam ⟩ → ⟨ sucV d ∈ˢ lam ⟩)
  (X : S) (X⊆L : (x : S) → ⟨ x ∈ˢ X ⟩ → ⟨ x ∈ˢ Lset lam ⟩)
  (∅∈λ : ⟨ ∅ ∈ˢ lam ⟩)
  (φ₀ : Formula (⊥* {ℓ-suc ℓ}) 2)
  → HullStage.HoodCompleteP lam ordλ succλ X X⊆L ∅∈λ φ₀
  → HullStage.HoodSoundP lam ordλ succλ X X⊆L ∅∈λ φ₀
  → HullStage.HullClosedLsetOrd lam ordλ succλ X X⊆L ∅∈λ
  → HullStage.PiCommuteLsetOrd lam ordλ succλ X X⊆L ∅∈λ
step4-at-ord-status lam ordλ succλ X X⊆L ∅∈λ =
  HullStage.step4-at-ord-pf lam ordλ succλ X X⊆L ∅∈λ

-- The companion, at the consumer's own goal, with neither step 4 nor
-- step 2 in the chain.  Same two hypotheses, one of them existential.
levelin-from-hood-status : (lam : S) (ordλ : IsOrd lam)
  (succλ : (d : S) → ⟨ d ∈ˢ lam ⟩ → ⟨ sucV d ∈ˢ lam ⟩)
  (X : S) (X⊆L : (x : S) → ⟨ x ∈ˢ X ⟩ → ⟨ x ∈ˢ Lset lam ⟩)
  (∅∈λ : ⟨ ∅ ∈ˢ lam ⟩)
  (φ₀ : Formula (⊥* {ℓ-suc ℓ}) 2)
  → HullStage.HoodExistsP lam ordλ succλ X X⊆L ∅∈λ φ₀
  → HullStage.HoodSoundP lam ordλ succλ X X⊆L ∅∈λ φ₀
  → HullStage.LevelIn lam ordλ succλ X X⊆L ∅∈λ
levelin-from-hood-status lam ordλ succλ X X⊆L ∅∈λ =
  HullStage.levelin-from-hood-pf lam ordλ succλ X X⊆L ∅∈λ
