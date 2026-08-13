{-# OPTIONS --cubical --safe --guardedness #-}

-- [L3.32-T126] O4's instantiation check at the first limit: the generic
-- successor-clause module instantiated at Lset ω with the scratch graph
-- layer (the archived StepInL with T121's left-compute bridge, under
-- /tmp/t125-scratch), and the decode exercised in both directions on the
-- op0 graph and on the clause itself.  Untracked probe, no git.

open import Base.Prelude
open import Base.Truth
open import Base.Classical using ( LEM )
open import Cubical.HITs.CumulativeHierarchy.Base using ( V )

module ProbeT126 {ℓ : Level} (lem : LEM (ℓ-suc ℓ)) (A : V ℓ) where

open import FOL.ZFStructure using ( module hPropStructure )
open import FOL.Syntax using ( Formula )
open import V.Hierarchy {ℓ} using ( 𝒮ᵥ )
open import V.Coding {ℓ} using ( pr )
open import V.Model {ℓ} using ( self∈sucV; ∈sucV-elim; ∈sucV-inl )
open import L.Constructible {ℓ} using ( Lset; isTransV; layer-trans; Lset-layer; Lset-mono )
open import L.InitialSegment {ℓ} using ( _⟷_ )
open import L.LevelKit {ℓ} using ( module LevelKit )
open import L.Rud.Step {ℓ} lem A using
  ( step; step-out; step-in-img; Fof; op0; StepArm; arm-member; arm-self
  ; arm-image; u-self-in; limit-succ-mem )
open import L.TowerKit {ℓ} lem A using ( Ltr; suc⁴ )
open import L.Rud.Bridge {ℓ} lem A using
  ( ∅∈Lset; suc⁴-up; suc⁴∈; Lstage₂; Lval )
open import L.Rud.Finite {ℓ} lem A using ( limω )
open import L.Ordinal {ℓ} using ( #∈ω )
open import L.Rud.StepInL {ℓ} lem A using ( module Slot; module Desc; values∈L )
open import Cubical.HITs.CumulativeHierarchy.Properties
  using ( ∈∈ₛ; ∈-asFiber; ⟪_⟫ )
open import Cubical.HITs.CumulativeHierarchy.Constructions
  using ( ∅; ∅-empty; ω; module InfinitySet )
open InfinitySet using ( sucV; #_ )
import Cubical.HITs.PropositionalTruncation as PT
open PT using ( ∣_∣₁; ∥_∥₁; squash₁ )
open import Cubical.Data.Sum using ( _⊎_; inl; inr )
import Cubical.Data.Empty as Empty

open TruthAlgebra (hPropAlgebra (ℓ-suc ℓ))
open hPropStructure 𝒮ᵥ

∅∈ω : ⟨ ∅ ∈ˢ ω ⟩
∅∈ω = #∈ω 0

module K = LevelKit (Lset ω) (layer-trans (Lset-layer ω))
open K public

-- The carrier's transitivity certificate, named before the instantiation.
utr : isTransV (Lset ω)
utr = layer-trans (Lset-layer ω)

-- The module under test, instantiated at the carrier.
open import L.Rud.StepStory {ℓ} lem A (Lset ω) utr using ( module Clause )

-- The scratch Slot layer at the carrier: the archived graph bundle with the
-- T121 bridge, exactly as the first-limit gate used it.
module Gate (A∈ω : ⟨ A ∈ˢ Lset ω ⟩) where

  module Sl = Slot (Lset ω) (Ltr ω)
    (∈-asFiber {a = A} {b = Lset ω} A∈ω .fst)
    (∈-asFiber {a = A} {b = Lset ω} A∈ω .snd)
    (∅∈Lset ω limω ∅∈ω)

  -- The equality frame the graphs are built from lives in the archived
  -- Desc module (Slot does not re-export it), opened at the carrier.
  module Dc = Desc (Lset ω) (Ltr ω)

  -- The step closure into the carrier, the instantiation of stepSub: the
  -- delivered values read places every step member in the stage above the
  -- argument's stage, and limit closure brings it into Lset ω.
  stepInL : (c : S) → ⟨ c ∈ˢ Lset ω ⟩ → (v : S) → ⟨ v ∈ˢ step c ⟩ → ⟨ v ∈ˢ Lset ω ⟩
  stepInL c c∈ v v∈step = PT.rec (snd (v ∈ˢ Lset ω)) go (step-out c v v∈step)
    where
    go : StepArm c v → ⟨ v ∈ˢ Lset ω ⟩
    go (arm-member v∈c) = Ltr ω {x = c} {y = v} v∈c c∈
    go (arm-self e) = subst (λ w → ⟨ w ∈ˢ Lset ω ⟩) (sym e) c∈
    go (arm-image i a b sa sb e) = PT.rec (snd (v ∈ˢ Lset ω)) both
      (Lstage₂ ω limω c A c∈ A∈ω)
      where
      both : Σ[ ξ ∈ S ] (⟨ ξ ∈ˢ ω ⟩ × ⟨ c ∈ˢ Lset ξ ⟩ × ⟨ A ∈ˢ Lset ξ ⟩)
           → ⟨ v ∈ˢ Lset ω ⟩
      both (ξ , ξ∈ω , c∈ξ , A∈ξ) =
        Lset-mono {α = ω} {β = sucV (suc⁴ ξ)}
          (limit-succ-mem ω (suc⁴ ξ) limω (suc⁴∈ ω ξ limω ξ∈ω))
          (subst (λ w → ⟨ w ∈ˢ Lset (sucV (suc⁴ ξ)) ⟩) (sym e)
            (Lval (suc⁴ ξ) (suc⁴-up ξ A A∈ξ) i a b a∈ b∈
              (values∈L c ξ c∈ξ i a b sa sb)))
        where
        argIn : (x : S) → (⟨ x ∈ˢ c ⟩ ⊎ (x ≡ c)) → ⟨ x ∈ˢ Lset ξ ⟩
        argIn x (inl h) = Ltr ξ h c∈ξ
        argIn x (inr e) = subst (λ w → ⟨ w ∈ˢ Lset ξ ⟩) (sym e) c∈ξ
        a∈ : ⟨ a ∈ˢ Lset (suc⁴ ξ) ⟩
        a∈ = suc⁴-up ξ a (argIn a sa)
        b∈ : ⟨ b ∈ˢ Lset (suc⁴ ξ) ⟩
        b∈ = suc⁴-up ξ b (argIn b sb)

  -- The equality frame's two directions, combined into the module's single
  -- bidirectional parameter.
  eqFrame-ok : {n : ℕ} (k : Fin n) (M : Formula ⟪ Lset ω ⟫ (suc n))
               (δ : Vec SM n) (W : S)
             → ((v : S) → ⟨ v ∈ˢ W ⟩ → ⟨ v ∈ˢ Lset ω ⟩)
             → ((v : S) (v∈ : ⟨ v ∈ˢ Lset ω ⟩) → ⟨ ((v , v∈) ∷ δ) ⊨ᵐ M ⟩ → ⟨ v ∈ˢ W ⟩)
             → ((v : S) (v∈ : ⟨ v ∈ˢ Lset ω ⟩) → ⟨ v ∈ˢ W ⟩ → ⟨ ((v , v∈) ∷ δ) ⊨ᵐ M ⟩)
             → ⟨ δ ⊨ᵐ Dc.eqFrame k M ⟩ ⟷ fst (lookup k δ) ≡ W
  eqFrame-ok k M δ W wsub mout min =
    ( Dc.eqFrame-out k M δ W wsub mout min
    , Dc.eqFrame-in k M δ W wsub mout min )

  -- The clause module, instantiated with the scratch layer: this is the
  -- whole telescope, unchanged.
  module O4 = Clause stepInL Sl.graphOf Sl.graph-out Sl.graph-in Sl.bigOr
    Sl.bigOr-in Sl.bigOr-out Dc.eqFrame eqFrame-ok

  ∅∈L : ⟨ ∅ ∈ˢ Lset ω ⟩
  ∅∈L = ∅∈Lset ω limω ∅∈ω

  -- Exercise 1, the step atom's decode in both directions on op0: the
  -- value Fof op0 ∅ ∅ is a member of step ∅ by the image arm, and the
  -- decode reads the membership into the formula and back.
  v0 : S
  v0 = Fof op0 ∅ ∅

  v0∈step : ⟨ v0 ∈ˢ step ∅ ⟩
  v0∈step = step-in-img ∅ v0 op0 ∅ ∅ (u-self-in ∅) (u-self-in ∅) refl

  v0∈L : ⟨ v0 ∈ˢ Lset ω ⟩
  v0∈L = stepInL ∅ ∅∈L v0 v0∈step

  sm : SM
  sm = PK.pt v0 v0∈L

  cm : SM
  cm = PK.pt ∅ ∅∈L

  stepMemIn : ⟨ (sm ∷ cm ∷ []) ⊨ᵐ O4.stepMem zero ⟩
  stepMemIn = O4.stepMem-ok zero (sm ∷ cm ∷ []) .snd v0∈step

  stepMemOut : ⟨ v0 ∈ˢ step ∅ ⟩
  stepMemOut = O4.stepMem-ok zero (sm ∷ cm ∷ []) .fst stepMemIn

  -- Exercise 2, the clause decode in both directions on the empty witness:
  -- the clause holds vacuously, the backward direction builds the formula
  -- satisfaction, and the forward direction reads it back.
  succClause∅ : O4.succClause ∅
  succClause∅ a c b ac∈f ab∈f =
    Empty.rec (∅-empty (pr a c) (∈∈ₛ {a = pr a c} {b = ∅} .fst ac∈f))

  f∅ : SM
  f∅ = PK.pt ∅ ∅∈L

  x∅ : ⟪ Lset ω ⟫
  x∅ = ∈-asFiber {a = ∅} {b = Lset ω} ∅∈L .fst

  sat∅ : ⟨ (f∅ ∷ ι x∅ ∷ []) ⊨ᵐ O4.succForm ⟩
  sat∅ = O4.succ-ok f∅ x∅ .snd succClause∅

  round∅ : O4.succClause ∅
  round∅ = O4.succ-ok f∅ x∅ .fst sat∅
