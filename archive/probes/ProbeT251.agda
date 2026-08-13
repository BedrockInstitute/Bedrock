{-# OPTIONS --cubical --safe --guardedness #-}

-- [L3.32-T251] Gate 1 of T250: the carried-sequence miniature restated
-- with the strengthened induction hypothesis as a module parameter.  The
-- pair family at xi, its meta-level decode and its placement come from
-- the parameter.  The nested formula stack at Lset xi is deleted.  The
-- strengthened Assembly motive is stated at the end of the probe.
-- Untracked probe, no git, no master.

open import Base.Prelude
open import Base.Truth
open import Base.Classical using ( LEM )
open import Cubical.HITs.CumulativeHierarchy.Base using ( V; setIsSet )
open import L.Constructible using ( isTransV )

module ProbeT251 {ℓ : Level} (lem : LEM (ℓ-suc ℓ))
  (C : V ℓ) (Ctr : isTransV C)
  where

open import FOL.ZFStructure using ( module hPropStructure; _↾_ )
open import FOL.Syntax using
  ( Formula; _∧̇_; _⇒̇_; _≐_; ∃̇_; ∀̇_; ∃̇∈; ∀̇∈; _∈̇_; var; con )
open import FOL.Manipulation.Renaming using ( renameFo; module Sat )
open import V.Hierarchy {ℓ} using ( 𝒮ᵥ; extensionalV; ∈-irrefl; ∈-induction )
open import V.Model {ℓ} using ( self∈sucV; ∈sucV-elim; ∈sucV-inl; pair-singleton )
open import V.Coding {ℓ} using ( pr; pr-inj )
open import L.Constructible {ℓ} using
  ( IsOrd; Lset; Lset-mono; Lset-layer; layer-trans; 𝒟ₒ; 𝒟ₒ-intro )
open import L.InitialSegment {ℓ} using ( _⟷_ )
open import L.LevelKit {ℓ} using ( module LevelKit )
open import L.Definability {ℓ} using ( module DefOf )
open import L.Rud.BelowLim {ℓ} lem C Ctr
open import L.Ordinal {ℓ} using
  ( ∅-ord; numeral-ord; suc-ord; ω-ord; mem-ord )
open import L.Ordinal.Stages {ℓ} lem using ( ord∈Lset-suc; ord∈Lset→∈ )
open import L.Ordinal.Linear {ℓ} lem using ( ord-tri; Tri )
open import L.PairAtoms {ℓ} using ( isPair )
open import L.Rud.OrdArith {ℓ} lem using
  ( isLimit; isLimit-ord; isLimit-not-zero; isLimit-not-succ; isSucc
  ; limit-mem-ord; ord-case; predecessor-mem )
open import L.Rud.OrdBlocks {ℓ} lem using ( +ω; +ω-limit; +ω-ord; suc-⊆ )
open import Cubical.HITs.CumulativeHierarchy.Constructions
  using ( ∅; ∅-empty; ω; ⋃_; union-ax; ⁅_,_⁆; module InfinitySet )
open InfinitySet using ( sucV; #_ )
open import L.Rud.Step {ℓ} lem ∅ using
  ( Op16; Fof; Sset; Sset-suc; Sset-mono; step; step-in-self; step-out
  ; StepArm; arm-member; arm-self; arm-image; f5; limit-succ-mem )
open import L.Rud.Ops {ℓ} using ( F0; F5; F0-spec; F5-spec )
open import L.Rud.Bridge {ℓ} lem ∅ using
  ( Sset-union-limit; Lpair-limit; Lpr-limit; Lstage; Lstage₂; Lval
  ; Lstep⊆; suc⁴∈; suc⁴-up; ∅∈Lset )
open import L.TowerKit {ℓ} lem ∅ using ( Lpair; Ltr; 𝒟ₒ⊆Lsuc; suc⁴ )
import L.Rud.StepGraph {ℓ} lem ∅ as StepGraph
open import L.Axioms.Basic {ℓ} using ( finSet; finSet-in; finSet-out )
open import Cubical.Data.Nat using ( ℕ; zero; suc )
open import Cubical.Data.FinData.Base using ( Fin; toℕ )
open import Cubical.Data.FinData.Properties using ( toℕ<n; fromℕ'; toFromId' )
open import Cubical.Data.Sum using ( _⊎_; inl; inr )
open import Cubical.Functions.Logic using ( ⇔toPath )
import Cubical.Functions.Logic as Logic
import Cubical.Data.Empty as Empty
import Cubical.HITs.PropositionalTruncation as PT
open PT using ( ∣_∣₁; ∥_∥₁; squash₁ )
open import Cubical.Data.Sigma.Properties using ( ΣPathP )
open import Cubical.Foundations.Prelude using ( isProp→PathP; PathP )
open import Cubical.Foundations.HLevels using ( isProp×; isPropΠ )
open import Cubical.HITs.CumulativeHierarchy.Properties
  using ( ⟪_⟫; ⟪_⟫↪; ∈-asFiber; _∈ₛ_; ∈∈ₛ; extensionality )
  renaming ( _⊆_ to _⊆ₛ_ )

open TruthAlgebra (hPropAlgebra (ℓ-suc ℓ))
open hPropStructure 𝒮ᵥ

module _ (γ : S) (limγ : ⟨ isLimit γ ⟩)
  (IH : (β : S) → β ∈ᵗ γ → ⟨ isLimit β ⟩ → ⟨ Sset β ∈ˢ Lset (sucV β) ⟩)
  (stepSub : (c : S) → ⟨ c ∈ˢ C ⟩ → (v : S) → ⟨ v ∈ˢ step c ⟩ → ⟨ v ∈ˢ C ⟩)
  (graphOf : Op16 → Formula ⟪ C ⟫ 3)
  (graph-out : (i : Op16) (b a y : S) (b∈ : ⟨ b ∈ˢ C ⟩) (a∈ : ⟨ a ∈ˢ C ⟩)
               (y∈ : ⟨ y ∈ˢ C ⟩) → ((v : S) → ⟨ v ∈ˢ Fof i a b ⟩ → ⟨ v ∈ˢ C ⟩)
             → ⟨ ((b , b∈) ∷ (a , a∈) ∷ (y , y∈) ∷ []) ⊨ᵐ graphOf i ⟩
             → y ≡ Fof i a b)
  (graph-in : (i : Op16) (b a y : S) (b∈ : ⟨ b ∈ˢ C ⟩) (a∈ : ⟨ a ∈ˢ C ⟩)
              (y∈ : ⟨ y ∈ˢ C ⟩) → ((v : S) → ⟨ v ∈ˢ Fof i a b ⟩ → ⟨ v ∈ˢ C ⟩)
            → y ≡ Fof i a b
            → ⟨ ((b , b∈) ∷ (a , a∈) ∷ (y , y∈) ∷ []) ⊨ᵐ graphOf i ⟩)
  (bigOr : Formula ⟪ C ⟫ 3)
  (bigOr-in : (i : Op16) (δ : Vec SM 3) → ⟨ δ ⊨ᵐ graphOf i ⟩ → ⟨ δ ⊨ᵐ bigOr ⟩)
  (bigOr-out : (δ : Vec SM 3) (R : hProp (ℓ-suc ℓ))
             → ((i : Op16) → ⟨ δ ⊨ᵐ graphOf i ⟩ → ⟨ R ⟩)
             → ⟨ δ ⊨ᵐ bigOr ⟩ → ⟨ R ⟩)
  (eqFrame : {n : ℕ} → Fin n → Formula ⟪ C ⟫ (suc n) → Formula ⟪ C ⟫ n)
  (eqFrame-ok : {n : ℕ} (k : Fin n) (M : Formula ⟪ C ⟫ (suc n))
                (δ : Vec SM n) (W : S)
              → ((v : S) → ⟨ v ∈ˢ W ⟩ → ⟨ v ∈ˢ C ⟩)
              → ((v : S) (v∈ : ⟨ v ∈ˢ C ⟩) → ⟨ ((v , v∈) ∷ δ) ⊨ᵐ M ⟩ → ⟨ v ∈ˢ W ⟩)
              → ((v : S) (v∈ : ⟨ v ∈ˢ C ⟩) → ⟨ v ∈ˢ W ⟩
                 → ⟨ ((v , v∈) ∷ δ) ⊨ᵐ M ⟩)
              → ⟨ δ ⊨ᵐ eqFrame k M ⟩ ⟷ fst (lookup k δ) ≡ W)
  (Tgeom : ⟨ Lset (sucV (sucV (sucV γ))) ∈ˢ C ⟩)
  (segGeom : ⟨ Lset (sucV (sucV (sucV (sucV (sucV (sucV γ)))))) ∈ˢ C ⟩)
  (ξ : S) (ξ∈γ : ⟨ ξ ∈ˢ γ ⟩) (limξ : ⟨ isLimit ξ ⟩)
  where

  _ : S
  _ = γ

  -- The landed Stepγ machinery at gamma, instantiated with the given layer.
  module S = Stepγ γ limγ IH stepSub graphOf graph-out graph-in
    bigOr bigOr-in bigOr-out eqFrame eqFrame-ok Tgeom segGeom

  -- The nested carrier at xi: the witness carrier of the segment at xi.
  Wξ : S
  Wξ = Lset ξ

  Wtrξ : isTransV Wξ
  Wtrξ = layer-trans (Lset-layer ξ)

  ∅∈ξ : ⟨ ∅ ∈ˢ ξ ⟩
  ∅∈ξ = go (ord-tri ∅ ∅-ord ξ (isLimit-ord ξ limξ))
    where
    go : ⟨ ∅ ∈ˢ ξ ⟩ ⊎ ((∅ ≡ ξ) ⊎ ⟨ ξ ∈ˢ ∅ ⟩) → ⟨ ∅ ∈ˢ ξ ⟩
    go (inl h) = h
    go (inr (inl e)) = Empty.rec (isLimit-not-zero ξ limξ (sym e))
    go (inr (inr h)) = Empty.rec (∅-empty ξ (∈∈ₛ {a = ξ} {b = ∅} .fst h))

  ∅∈Wξ : ⟨ ∅ ∈ˢ Wξ ⟩
  ∅∈Wξ = ∅∈Lset ξ limξ ∅∈ξ

  mAξ : ⟪ Wξ ⟫
  mAξ = ∈-asFiber {a = ∅} {b = Wξ} ∅∈Wξ .fst

  qAξ : ⟪ Wξ ⟫↪ mAξ ≡ ∅
  qAξ = ∈-asFiber {a = ∅} {b = Wξ} ∅∈Wξ .snd

  -- The step closure at the nested carrier, the T222 slice at Lset xi.
  stepInWξ : (c : S) → ⟨ c ∈ˢ Wξ ⟩ → (v : S) → ⟨ v ∈ˢ step c ⟩ → ⟨ v ∈ˢ Wξ ⟩
  stepInWξ c c∈ v v∈step = PT.rec (snd (v ∈ˢ Wξ)) go (step-out c v v∈step)
    where
    go : StepArm c v → ⟨ v ∈ˢ Wξ ⟩
    go (arm-member v∈c) = Ltr ξ {x = c} {y = v} v∈c c∈
    go (arm-self e) = subst (λ w → ⟨ w ∈ˢ Wξ ⟩) (sym e) c∈
    go (arm-image i a b sa sb e) = PT.rec (snd (v ∈ˢ Wξ)) both
      (Lstage₂ ξ limξ c ∅ c∈ ∅∈Wξ)
      where
      both : Σ[ ζ ∈ S ] (⟨ ζ ∈ˢ ξ ⟩ × ⟨ c ∈ˢ Lset ζ ⟩ × ⟨ ∅ ∈ˢ Lset ζ ⟩)
           → ⟨ v ∈ˢ Wξ ⟩
      both (ζ , (ζ∈ξ , c∈ζ , A∈ζ)) =
        Lset-mono {α = ξ} {β = sucV (suc⁴ ζ)}
          (limit-succ-mem ξ (suc⁴ ζ) limξ (suc⁴∈ ξ ζ limξ ζ∈ξ))
          (subst (λ w → ⟨ w ∈ˢ Lset (sucV (suc⁴ ζ)) ⟩) (sym e)
            (Lval (suc⁴ ζ) (suc⁴-up ζ ∅ A∈ζ) i a b a∈ b∈
              (StepGraph.values∈L c ζ c∈ζ i a b sa sb)))
        where
        argIn : (x : S) → (⟨ x ∈ˢ c ⟩ ⊎ (x ≡ c)) → ⟨ x ∈ˢ Lset ζ ⟩
        argIn x (inl h) = Ltr ζ h c∈ζ
        argIn x (inr e') = subst (λ w → ⟨ w ∈ˢ Lset ζ ⟩) (sym e') c∈ζ
        a∈ : ⟨ a ∈ˢ Lset (suc⁴ ζ) ⟩
        a∈ = suc⁴-up ζ a (argIn a sa)
        b∈ : ⟨ b ∈ˢ Lset (suc⁴ ζ) ⟩
        b∈ = suc⁴-up ζ b (argIn b sb)


  -- The nested formula stack at Lset xi is deleted (T250's gate 1): the
  -- graph layer, the story formula, the rename decode and the defSet for
  -- the pair family.  The family, its decode and its placement come from
  -- the strengthened induction hypothesis, as module parameters.

  -- The carried sequence at xi, restated with the strengthened IH as a
  -- module parameter: the pair family at xi, its meta-level decode, and
  -- its placement.  The segment, its limit clause and the placements
  -- survive as meta-level content.
  module Carried
    (Pξ : S)
    (P∈ξ : (p : S) → ⟨ p ∈ˢ Pξ ⟩ ⟷ ∥ Σ[ η ∈ S ] (⟨ η ∈ˢ ξ ⟩
            × (p ≡ pr η (Sset η))) ∥₁)
    (Pξ∈Lsucξ : ⟨ Pξ ∈ˢ Lset (sucV ξ) ⟩)
    where

    -- The top pair and the segment at xi, placed below gamma.
    Tξ : S
    Tξ = pr ξ (Sset ξ)

    segξ : S
    segξ = F5 (F0 Pξ (F0 Tξ Tξ)) Tξ

    sucVξ∈W : ⟨ sucV ξ ∈ˢ S.W ⟩
    sucVξ∈W = Lset-mono {α = γ} {β = sucV (sucV ξ)}
      (limit-succ-mem γ (sucV ξ) limγ (limit-succ-mem γ ξ limγ ξ∈γ))
      (ord∈Lset-suc (sucV ξ) (suc-ord (isLimit-ord ξ limξ)))

    module Segξ = S.St.Segment ξ limξ Pξ P∈ξ sucVξ∈W

    -- The sixth clause at the segment at xi: at a limit member a the decode
    -- reads the value below, and the top case is the machinery's own limit
    -- clause (T229's structure).
    segLimitClauseξ : S.St.limitClause segξ
    segLimitClauseξ a b lima pr∈ z = PT.rec isPropRhsa go
      (Segξ.seg∈ (pr a b) .fst pr∈)
      where
      rhs : S → Type (ℓ-suc ℓ)
      rhs i = ∥ Σ[ η ∈ S ] (⟨ η ∈ˢ i ⟩
           × ∥ Σ[ w ∈ S ] (⟨ pr η w ∈ˢ segξ ⟩ × ⟨ z ∈ˢ w ⟩) ∥₁) ∥₁
      isPropRhsa : isProp (⟨ z ∈ˢ b ⟩ ⟷ rhs a)
      isPropRhsa = isProp× (isPropΠ (λ _ → squash₁)) (isPropΠ (λ _ → snd (z ∈ˢ b)))
      go : ⟨ pr a b ∈ˢ Pξ ⟩ ⊎ (pr a b ≡ Tξ) → ⟨ z ∈ˢ b ⟩ ⟷ rhs a
      go (inl p∈P) = PT.rec isPropRhsa aStep (P∈ξ (pr a b) .fst p∈P)
        where
        aStep : Σ[ η ∈ S ] (⟨ η ∈ˢ ξ ⟩ × (pr a b ≡ pr η (Sset η)))
              → ⟨ z ∈ˢ b ⟩ ⟷ rhs a
        aStep (η , (η∈ξ , q)) = (fwd , bwd)
          where
          a≡η : a ≡ η
          a≡η = pr-inj q .fst
          b≡Sη : b ≡ Sset η
          b≡Sη = pr-inj q .snd
          a∈ξ : ⟨ a ∈ˢ ξ ⟩
          a∈ξ = subst (λ w → ⟨ w ∈ˢ ξ ⟩) (sym a≡η) η∈ξ
          b≡Sa : b ≡ Sset a
          b≡Sa = b≡Sη ∙ cong Sset (sym a≡η)
          fwd : ⟨ z ∈ˢ b ⟩ → rhs a
          fwd z∈b = PT.map go' (Sset-union-limit a lima z
            (subst (λ w → ⟨ z ∈ˢ w ⟩) b≡Sa z∈b))
            where
            go' : Σ[ δ ∈ S ] (⟨ δ ∈ˢ a ⟩ × ⟨ z ∈ˢ Sset (sucV δ) ⟩)
                → Σ[ η ∈ S ] (⟨ η ∈ˢ a ⟩
                     × ∥ Σ[ w ∈ S ] (⟨ pr η w ∈ˢ segξ ⟩ × ⟨ z ∈ˢ w ⟩) ∥₁)
            go' (δ , (δ∈a , z∈Sδ')) = sucV δ , ( δ'∈a
              , ∣ Sset (sucV δ) , ( prδ'∈ , z∈Sδ' ) ∣₁ )
              where
              δ'∈a : ⟨ sucV δ ∈ˢ a ⟩
              δ'∈a = limit-succ-mem a δ lima δ∈a
              δ'∈ξ : ⟨ sucV δ ∈ˢ ξ ⟩
              δ'∈ξ = isLimit-ord ξ limξ .fst {x = a} {y = sucV δ} δ'∈a a∈ξ
              prδ'∈ : ⟨ pr (sucV δ) (Sset (sucV δ)) ∈ˢ segξ ⟩
              prδ'∈ = Segξ.prξSξ∈seg (sucV δ) δ'∈ξ
          bwd : rhs a → ⟨ z ∈ˢ b ⟩
          bwd = PT.rec (snd (z ∈ˢ b)) go'
            where
            go' : Σ[ η ∈ S ] (⟨ η ∈ˢ a ⟩
                 × ∥ Σ[ w ∈ S ] (⟨ pr η w ∈ˢ segξ ⟩ × ⟨ z ∈ˢ w ⟩) ∥₁)
                → ⟨ z ∈ˢ b ⟩
            go' (η , (η∈a , rest)) = subst (λ w → ⟨ z ∈ˢ w ⟩) (sym b≡Sa)
              (PT.rec (snd (z ∈ˢ Sset a)) s₂ rest)
              where
              s₂ : Σ[ w ∈ S ] (⟨ pr η w ∈ˢ segξ ⟩ × ⟨ z ∈ˢ w ⟩)
                 → ⟨ z ∈ˢ Sset a ⟩
              s₂ (w , (pr∈ , z∈w)) = PT.rec (snd (z ∈ˢ Sset a)) d
                (Segξ.seg∈ (pr η w) .fst pr∈)
                where
                d : ⟨ pr η w ∈ˢ Pξ ⟩ ⊎ (pr η w ≡ Tξ) → ⟨ z ∈ˢ Sset a ⟩
                d (inl p∈P) = PT.rec (snd (z ∈ˢ Sset a)) pgo (P∈ξ (pr η w) .fst p∈P)
                  where
                  pgo : Σ[ η' ∈ S ] (⟨ η' ∈ˢ ξ ⟩ × (pr η w ≡ pr η' (Sset η')))
                      → ⟨ z ∈ˢ Sset a ⟩
                  pgo (η' , (η'∈ξ , q)) = Sset-mono {α = a} {β = η} η∈a z z∈Sη
                    where
                    w≡Sη : w ≡ Sset η
                    w≡Sη = subst (λ t → w ≡ Sset t) (sym (pr-inj q .fst))
                      (pr-inj q .snd)
                    z∈Sη : ⟨ z ∈ˢ Sset η ⟩
                    z∈Sη = subst (λ t → ⟨ z ∈ˢ t ⟩) (w≡Sη) z∈w
                d (inr q) = Empty.rec {A = ⟨ z ∈ˢ Sset a ⟩} (∈-irrefl ξ ξ∈ξ)
                  where
                  η≡ξ : η ≡ ξ
                  η≡ξ = pr-inj q .fst
                  ξ∈a : ⟨ ξ ∈ˢ a ⟩
                  ξ∈a = subst (λ t → ⟨ t ∈ˢ a ⟩) η≡ξ η∈a
                  ξ∈ξ : ⟨ ξ ∈ˢ ξ ⟩
                  ξ∈ξ = isLimit-ord ξ limξ .fst {x = a} {y = ξ} ξ∈a a∈ξ
      go (inr q) = (fwd , bwd)
        where
        a≡ξ : a ≡ ξ
        a≡ξ = pr-inj q .fst
        b≡Sξ : b ≡ Sset ξ
        b≡Sξ = pr-inj q .snd
        fwd : ⟨ z ∈ˢ b ⟩ → rhs a
        fwd z∈b = subst rhs (sym a≡ξ)
          (Segξ.segLimit₀ z .fst (subst (λ w → ⟨ z ∈ˢ w ⟩) b≡Sξ z∈b))
        bwd : rhs a → ⟨ z ∈ˢ b ⟩
        bwd h = subst (λ w → ⟨ z ∈ˢ w ⟩) (sym b≡Sξ)
          (Segξ.segLimit₀ z .snd (subst rhs a≡ξ h))

    -- The six-clause story at the segment at xi, at the gamma carrier.
    segmentStory : S.storyW segξ
    segmentStory = ( Segξ.segPairhood , ( Segξ.segSingleValued
      , ( Segξ.segZeroClause , ( Segξ.segDom₀
        , ( Segξ.segSuccClause , segLimitClauseξ ) ) ) ) )

    -- The placements: the top pair and the segment, all below gamma.  The
    -- family's placement comes from the parameter.
    ξ∈Lsucξ : ⟨ ξ ∈ˢ Lset (sucV ξ) ⟩
    ξ∈Lsucξ = ord∈Lset-suc ξ (isLimit-ord ξ limξ)

    Sξ∈Lsucξ : ⟨ Sset ξ ∈ˢ Lset (sucV ξ) ⟩
    Sξ∈Lsucξ = IH ξ ξ∈γ limξ

    F0ξξ∈L : ⟨ F0 ξ ξ ∈ˢ Lset (sucV (sucV ξ)) ⟩
    F0ξξ∈L = Lpair (sucV ξ) ξ ξ ξ∈Lsucξ ξ∈Lsucξ

    F0ξSξ∈L : ⟨ F0 ξ (Sset ξ) ∈ˢ Lset (sucV (sucV ξ)) ⟩
    F0ξSξ∈L = Lpair (sucV ξ) ξ (Sset ξ) ξ∈Lsucξ Sξ∈Lsucξ

    pr≡F0 : pr ξ (Sset ξ) ≡ F0 (F0 ξ ξ) (F0 ξ (Sset ξ))
    pr≡F0 = sym (cong (λ w → ⁅ w , ⁅ ξ , Sset ξ ⁆ ⁆) (pair-singleton ξ))

    Tξ∈L : ⟨ Tξ ∈ˢ Lset (sucV (sucV (sucV ξ))) ⟩
    Tξ∈L = subst (λ w → ⟨ w ∈ˢ Lset (sucV (sucV (sucV ξ))) ⟩) (sym pr≡F0)
      (Lpair (sucV (sucV ξ)) (F0 ξ ξ) (F0 ξ (Sset ξ)) F0ξξ∈L F0ξSξ∈L)

    F0TT∈L : ⟨ F0 Tξ Tξ ∈ˢ Lset (sucV (sucV (sucV (sucV ξ)))) ⟩
    F0TT∈L = Lpair (sucV (sucV (sucV ξ))) Tξ Tξ Tξ∈L Tξ∈L

    oξ⁴ : IsOrd (sucV (sucV (sucV (sucV ξ))))
    oξ⁴ = suc-ord (suc-ord (suc-ord (suc-ord (isLimit-ord ξ limξ))))

    sucVξ∈sucV⁴ξ : ⟨ sucV ξ ∈ˢ sucV (sucV (sucV (sucV ξ))) ⟩
    sucVξ∈sucV⁴ξ = oξ⁴ .fst {x = sucV (sucV ξ)} {y = sucV ξ}
      (self∈sucV (sucV ξ))
      (oξ⁴ .fst {x = sucV (sucV (sucV ξ))} {y = sucV (sucV ξ)}
        (self∈sucV (sucV (sucV ξ))) (self∈sucV (sucV (sucV (sucV ξ)))))

    Pξ∈L⁴ : ⟨ Pξ ∈ˢ Lset (sucV (sucV (sucV (sucV ξ)))) ⟩
    Pξ∈L⁴ = Lset-mono {α = sucV (sucV (sucV (sucV ξ)))} {β = sucV ξ}
      sucVξ∈sucV⁴ξ Pξ∈Lsucξ

    F0PTT∈L : ⟨ F0 Pξ (F0 Tξ Tξ) ∈ˢ Lset (sucV (sucV (sucV (sucV (sucV ξ))))) ⟩
    F0PTT∈L = Lpair (sucV (sucV (sucV (sucV ξ)))) Pξ (F0 Tξ Tξ)
      Pξ∈L⁴ F0TT∈L

    -- The union of a stage member lands one step up.
    module UnionClosure (σ : S) (oσ : IsOrd σ) (a : S)
      (a∈ : ⟨ a ∈ˢ Lset σ ⟩) where

      union∈Lsuc : ⟨ (⋃ a) ∈ˢ Lset (sucV σ) ⟩
      union∈Lsuc = 𝒟ₒ⊆Lsuc σ (⋃ a) (𝒟ₒ-intro (Lset σ) (⋃ a) ∣ φ , defSet≡ ∣₁)
        where
        module Dσ = DefOf (Lset σ)
        Atr : isTransV (Lset σ)
        Atr = layer-trans (Lset-layer σ)
        mₐ : ⟪ Lset σ ⟫
        mₐ = ∈-asFiber {a = a} {b = Lset σ} a∈ .fst
        qₐ : ⟪ Lset σ ⟫↪ mₐ ≡ a
        qₐ = ∈-asFiber {a = a} {b = Lset σ} a∈ .snd
        φ : Formula ⟪ Lset σ ⟫ 1
        φ = ∃̇∈ (con mₐ) (var (suc zero) ∈̇ var zero)
        defSet≡ : Dσ.defSet φ ≡ ⋃ a
        defSet≡ = extensionality (Dσ.defSet φ) (⋃ a) (sub₁ , sub₂)
          where
          sub₁ : ⟨ Dσ.defSet φ ⊆ₛ (⋃ a) ⟩
          sub₁ y y∈ₛ = PT.rec (snd (y ∈ₛ (⋃ a)))
            (λ { ((m , h) , q) →
              subst (λ w → ⟨ w ∈ₛ (⋃ a) ⟩) q
                (PT.rec (snd (⟪ Lset σ ⟫↪ m ∈ₛ (⋃ a)))
                  (λ { (v , (fv∈a , m∈ₛv)) →
                    union-ax a (⟪ Lset σ ⟫↪ m) .snd
                      ∣ fst v
                        , ( ∈∈ₛ {a = fst v} {b = a} .fst
                              (subst (λ w → ⟨ fst v ∈ˢ w ⟩) qₐ fv∈a)
                          , ∈∈ₛ {a = ⟪ Lset σ ⟫↪ m} {b = fst v} .fst m∈ₛv ) ∣₁ })
                  (subst ⟨_⟩ (Dσ.defSet-mem φ m) ∣ (m , h) , refl ∣₁)) })
            (∈∈ₛ {a = y} {b = Dσ.defSet φ} .snd y∈ₛ)
          sub₂ : ⟨ (⋃ a) ⊆ₛ Dσ.defSet φ ⟩
          sub₂ y y∈ₛ = PT.rec (snd (y ∈ₛ Dσ.defSet φ))
            (λ { (v , (v∈ₛa , y∈ₛv)) → memOf v v∈ₛa y∈ₛv })
            (union-ax a y .fst y∈ₛ)
            where
            memOf : (v : S) → ⟨ v ∈ₛ a ⟩ → ⟨ y ∈ₛ v ⟩ → ⟨ y ∈ₛ Dσ.defSet φ ⟩
            memOf v v∈ₛa y∈ₛv =
              subst (λ w → ⟨ w ∈ₛ Dσ.defSet φ ⟩) q'
                (∈∈ₛ {a = ⟪ Lset σ ⟫↪ m'} {b = Dσ.defSet φ} .fst
                  (subst ⟨_⟩ (sym (Dσ.defSet-mem φ m')) sat))
              where
              v∈a = ∈∈ₛ {a = v} {b = a} .snd v∈ₛa
              y∈v = ∈∈ₛ {a = y} {b = v} .snd y∈ₛv
              v∈A = Atr {x = a} {y = v} v∈a a∈
              y∈A = Atr {x = v} {y = y} y∈v v∈A
              m' = ∈-asFiber {a = y} {b = Lset σ} y∈A .fst
              q' = ∈-asFiber {a = y} {b = Lset σ} y∈A .snd
              sat : ⟨ (Dσ.ι m' ∷ []) Dσ.⊨ᵐ φ ⟩
              sat = ∣ (v , v∈A)
                    , ( subst (λ w → ⟨ v ∈ˢ w ⟩) (sym qₐ) v∈a
                      , subst (λ w → ⟨ w ∈ˢ v ⟩) (sym q') y∈v ) ∣₁

    module UC = UnionClosure (sucV (sucV (sucV (sucV (sucV ξ)))))
      (suc-ord oξ⁴) (F0 Pξ (F0 Tξ Tξ)) F0PTT∈L

    segξ∈L⁶ : ⟨ segξ ∈ˢ Lset (sucV (sucV (sucV (sucV (sucV (sucV ξ)))))) ⟩
    segξ∈L⁶ = UC.union∈Lsuc

    sucV⁶ξ∈γ : ⟨ sucV (sucV (sucV (sucV (sucV (sucV ξ))))) ∈ˢ γ ⟩
    sucV⁶ξ∈γ = limit-succ-mem γ (sucV (sucV (sucV (sucV (sucV ξ))))) limγ
      (limit-succ-mem γ (sucV (sucV (sucV (sucV ξ)))) limγ
        (limit-succ-mem γ (sucV (sucV (sucV ξ))) limγ
          (limit-succ-mem γ (sucV (sucV ξ)) limγ
            (limit-succ-mem γ (sucV ξ) limγ (limit-succ-mem γ ξ limγ ξ∈γ)))))

    segξ∈W : ⟨ segξ ∈ˢ S.W ⟩
    segξ∈W = Lset-mono {α = γ} {β = sucV (sucV (sucV (sucV (sucV (sucV ξ)))))}
        sucV⁶ξ∈γ segξ∈L⁶

    prξSξ∈segξ : ⟨ pr ξ (Sset ξ) ∈ˢ segξ ⟩
    prξSξ∈segξ = Segξ.seg∈ (pr ξ (Sset ξ)) .snd ∣ inr refl ∣₁

  -- The strengthened Assembly motive (T250's gate 1, item 4): the plain
  -- statement, the pair family, its meta-level decode, and its placement.
  -- The motive is not an hProp.  The Rec' precedent runs a non-truncated
  -- Sigma through ∈-induction at BelowLim 3358-3359 and 3439.
  Strengthened : S → Type (ℓ-suc ℓ)
  Strengthened γ = ⟨ Sset γ ∈ˢ Lset (sucV γ) ⟩
    × Σ[ P ∈ S ] ((p : S) → ⟨ p ∈ˢ P ⟩ ⟷ ∥ Σ[ ζ ∈ S ]
         (⟨ ζ ∈ˢ γ ⟩ × (p ≡ pr ζ (Sset ζ))) ∥₁)
    × ⟨ P ∈ˢ Lset (sucV γ) ⟩

  module StrengthenedAssembly
    (stepHyp : (γ : S) → ⟨ isLimit γ ⟩
             → ((β : S) → β ∈ᵗ γ → ⟨ isLimit β ⟩ → Strengthened β)
             → Strengthened γ)
    where

    below-lim : (γ : S) → ⟨ isLimit γ ⟩ → Strengthened γ
    below-lim = ∈-induction {P = P} indStep
      where
      P : S → Type (ℓ-suc ℓ)
      P γ = ⟨ isLimit γ ⟩ → Strengthened γ

      indStep : (γ : S) → ((β : S) → β ∈ᵗ γ → P β) → P γ
      indStep γ IH limγ = stepHyp γ limγ ih
        where
        ih : (β : S) → β ∈ᵗ γ → ⟨ isLimit β ⟩ → Strengthened β
        ih β β∈γ limβ = IH β β∈γ limβ
