{-# OPTIONS --cubical --safe --guardedness #-}

-- [L3.32-T242b] The escape miniature: T240's story-decode family in
-- T222's shape.  The carrier is W = Lset γ, bound to the parameter γ.
-- The story has six clauses: the kit's four, the successor clause and
-- the limit clause.  The decode is hand-written with named branches,
-- exactly T222's shape.  No clause bundle, no LevelKit aliases.
-- Untracked probe, no git, no master.

open import Base.Prelude
open import Base.Truth
open import Base.Classical using ( LEM )
open import Cubical.HITs.CumulativeHierarchy.Base using ( V )

module ProbeT242b {ℓ : Level} (lem : LEM (ℓ-suc ℓ)) where

open import FOL.ZFStructure using ( module hPropStructure )
open import FOL.Syntax using ( Formula; _∧̇_ )
open import V.Hierarchy {ℓ} using ( 𝒮ᵥ )
open import L.Constructible {ℓ} using
  ( IsOrd; Lset; Lset-mono; Lset-layer; layer-trans; isTransV )
open import L.InitialSegment {ℓ} using ( _⟷_ )
open import L.Ordinal {ℓ} using ( ∅-ord )
open import L.Ordinal.Linear {ℓ} lem using ( ord-tri )
open import L.Rud.OrdArith {ℓ} lem using
  ( isLimit; isLimit-ord; isLimit-not-zero )
open import Cubical.HITs.CumulativeHierarchy.Constructions
  using ( ∅; ∅-empty; module InfinitySet )
open InfinitySet using ( sucV )
open import L.Rud.Step {ℓ} lem ∅ using
  ( Op16; Fof; Sset; step; step-out; StepArm; arm-member; arm-self; arm-image
  ; limit-succ-mem )
open import L.TowerKit {ℓ} lem ∅ using ( Ltr; suc⁴ )
open import L.Rud.Bridge {ℓ} lem ∅ using
  ( ∅∈Lset; Lstage₂; Lval; suc⁴∈; suc⁴-up )
import L.Rud.StepGraph {ℓ} lem ∅ as StepGraph
import L.Rud.StepStory {ℓ} lem ∅ as StepStory
open import L.LevelKit {ℓ} using ( module LevelKit )
open import Cubical.Data.Sum using ( _⊎_; inl; inr )
import Cubical.Data.Empty as Empty
import Cubical.HITs.PropositionalTruncation as PT
open PT using ( ∣_∣₁; ∥_∥₁ )
open import Cubical.HITs.CumulativeHierarchy.Properties
  using ( ⟪_⟫; ⟪_⟫↪; ∈-asFiber; ∈∈ₛ )

open TruthAlgebra (hPropAlgebra (ℓ-suc ℓ))
open hPropStructure 𝒮ᵥ

module StepAt
  (γ : S) (limγ : ⟨ isLimit γ ⟩)
  (IH : (β : S) → β ∈ᵗ γ → ⟨ isLimit β ⟩ → ⟨ Sset β ∈ˢ Lset (sucV β) ⟩)
  where

  W : S
  W = Lset γ

  Wtr : isTransV W
  Wtr = layer-trans (Lset-layer γ)

  ∅∈γ : ⟨ ∅ ∈ˢ γ ⟩
  ∅∈γ = go (ord-tri ∅ ∅-ord γ (isLimit-ord γ limγ))
    where
    go : ⟨ ∅ ∈ˢ γ ⟩ ⊎ ((∅ ≡ γ) ⊎ ⟨ γ ∈ˢ ∅ ⟩) → ⟨ ∅ ∈ˢ γ ⟩
    go (inl h) = h
    go (inr (inl e)) = Empty.rec (isLimit-not-zero γ limγ (sym e))
    go (inr (inr h)) = Empty.rec (∅-empty γ (∈∈ₛ {a = γ} {b = ∅} .fst h))

  ∅∈W : ⟨ ∅ ∈ˢ W ⟩
  ∅∈W = ∅∈Lset γ limγ ∅∈γ

  mA : ⟪ W ⟫
  mA = ∈-asFiber {a = ∅} {b = W} ∅∈W .fst

  qA : ⟪ W ⟫↪ mA ≡ ∅
  qA = ∈-asFiber {a = ∅} {b = W} ∅∈W .snd

  stepInW : (c : S) → ⟨ c ∈ˢ W ⟩ → (v : S) → ⟨ v ∈ˢ step c ⟩ → ⟨ v ∈ˢ W ⟩
  stepInW c c∈ v v∈step = PT.rec (snd (v ∈ˢ W)) go (step-out c v v∈step)
    where
    go : StepArm c v → ⟨ v ∈ˢ W ⟩
    go (arm-member v∈c) = Ltr γ {x = c} {y = v} v∈c c∈
    go (arm-self e) = subst (λ w → ⟨ w ∈ˢ W ⟩) (sym e) c∈
    go (arm-image i a b sa sb e) = PT.rec (snd (v ∈ˢ W)) both
      (Lstage₂ γ limγ c ∅ c∈ ∅∈W)
      where
      both : Σ[ ξ ∈ S ] (⟨ ξ ∈ˢ γ ⟩ × ⟨ c ∈ˢ Lset ξ ⟩ × ⟨ ∅ ∈ˢ Lset ξ ⟩)
           → ⟨ v ∈ˢ W ⟩
      both (ξ , (ξ∈γ , c∈ξ , A∈ξ)) =
        Lset-mono {α = γ} {β = sucV (suc⁴ ξ)}
          (limit-succ-mem γ (suc⁴ ξ) limγ (suc⁴∈ γ ξ limγ ξ∈γ))
          (subst (λ w → ⟨ w ∈ˢ Lset (sucV (suc⁴ ξ)) ⟩) (sym e)
            (Lval (suc⁴ ξ) (suc⁴-up ξ ∅ A∈ξ) i a b a∈ b∈
              (StepGraph.values∈L c ξ c∈ξ i a b sa sb)))
        where
        argIn : (x : S) → (⟨ x ∈ˢ c ⟩ ⊎ (x ≡ c)) → ⟨ x ∈ˢ Lset ξ ⟩
        argIn x (inl h) = Ltr ξ h c∈ξ
        argIn x (inr e') = subst (λ w → ⟨ w ∈ˢ Lset ξ ⟩) (sym e') c∈ξ
        a∈ : ⟨ a ∈ˢ Lset (suc⁴ ξ) ⟩
        a∈ = suc⁴-up ξ a (argIn a sa)
        b∈ : ⟨ b ∈ˢ Lset (suc⁴ ξ) ⟩
        b∈ = suc⁴-up ξ b (argIn b sb)

  module WL = StepGraph.Layer W Wtr mA qA ∅∈W
  module WB = WL.BigOr WL.graphOf

  import L.Rud.StepStory {ℓ} lem ∅ W Wtr as StepStoryW
  module WCl = StepStoryW.Clause stepInW WL.graphOf WL.graph-out WL.graph-in
    WB.bigOr WB.bigOr-in WB.bigOr-out WL.eqFrame WL.eqFrame-ok

  memberAtLim : (ξ : S) → ⟨ ξ ∈ˢ γ ⟩ → ⟨ isLimit ξ ⟩ → ⟨ Sset ξ ∈ˢ W ⟩
  memberAtLim ξ ξ∈γ limξ = Lset-mono {α = γ} {β = sucV ξ}
    (limit-succ-mem γ ξ limγ ξ∈γ) (IH ξ ξ∈γ limξ)

  module KW = LevelKit W Wtr

  module LimW = StepStoryW.Limit
  open LimW public

  -- The six-clause story: the kit's four clauses, the successor clause,
  -- and the limit clause, hand-written in T222's shape.
  storyW6 : S → Type (ℓ-suc ℓ)
  storyW6 f = KW.pairhood f × KW.singleValued f × KW.zeroClause f
           × KW.exactDom f × WCl.succClause f × limitClause f

  storyFormW6 : Formula ⟪ W ⟫ 2
  storyFormW6 = KW.pairForm ∧̇ KW.singleForm ∧̇ KW.zeroForm
             ∧̇ KW.exactDomForm ∧̇ WCl.succForm ∧̇ limitForm

  storyW6-out : (f : KW.SM) (x : ⟪ W ⟫)
              → ⟨ (f ∷ KW.ι x ∷ []) KW.⊨ᵐ storyFormW6 ⟩ → storyW6 (fst f)
  storyW6-out f x (h₁ , (h₂ , (h₃ , (h₄ , (h₅ , h₆))))) =
    ( KW.pairhood-out f x h₁
    , ( KW.single-out f x h₂
      , ( KW.zero-out f x h₃
        , ( KW.exactDom-out f x h₄
          , ( WCl.succ-ok f x .fst h₅ , limit-ok f x .fst h₆ ) ) ) ) )

  storyW6-in : (f : KW.SM) (x : ⟪ W ⟫)
             → storyW6 (fst f) → ⟨ (f ∷ KW.ι x ∷ []) KW.⊨ᵐ storyFormW6 ⟩
  storyW6-in f x (h₁ , (h₂ , (h₃ , (h₄ , (h₅ , h₆))))) =
    ( KW.pairhood-in f x h₁
    , ( KW.single-in f x h₂
      , ( KW.zero-in f x h₃
        , ( KW.exactDom-in f x h₄
          , ( WCl.succ-ok f x .snd h₅ , limit-ok f x .snd h₆ ) ) ) ) )

  storyW6-ok : (f : KW.SM) (x : ⟪ W ⟫)
             → ⟨ (f ∷ KW.ι x ∷ []) KW.⊨ᵐ storyFormW6 ⟩ ⟷ storyW6 (fst f)
  storyW6-ok f x = storyW6-out f x , storyW6-in f x
