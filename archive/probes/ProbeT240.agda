{-# OPTIONS --cubical --safe --guardedness #-}

-- [L3.32-T240] The carried-sequence gate, re-measured: the segment at a
-- variable limit xi in gamma, with the pair family and its decode at the
-- nested carrier Lset xi, consuming the carrier-generic limit clause of
-- L.Rud.StepStory instead of restating it.  Untracked probe, no git, no
-- master.

open import Base.Prelude
open import Base.Truth
open import Base.Classical using ( LEM )
open import Cubical.HITs.CumulativeHierarchy.Base using ( V; setIsSet )
open import L.Constructible using ( isTransV )

module ProbeT240 {ℓ : Level} (lem : LEM (ℓ-suc ℓ))
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

  -- The graph layer and the step clause at the nested carrier.
  module WLξ = StepGraph.Layer Wξ Wtrξ mAξ qAξ ∅∈Wξ
  module WBξ = WLξ.BigOr WLξ.graphOf

  import L.Rud.StepStory {ℓ} lem ∅ Wξ Wtrξ as StepStoryWξ
  module WClξ = StepStoryWξ.Clause stepInWξ WLξ.graphOf WLξ.graph-out WLξ.graph-in
    WBξ.bigOr WBξ.bigOr-in WBξ.bigOr-out WLξ.eqFrame WLξ.eqFrame-ok

  -- The story at the nested carrier, instantiated with the graph layer.
  module Stξ = Story Wξ Wtrξ stepInWξ WLξ.graphOf WLξ.graph-out
    WLξ.graph-in WBξ.bigOr WBξ.bigOr-in WBξ.bigOr-out WLξ.eqFrame WLξ.eqFrame-ok

  module KWξ = LevelKit Wξ Wtrξ

  -- The sixth clause, from the carrier-generic Limit module of
  -- L.Rud.StepStory (T239 section 4's glue).
  module Limξ = StepStoryWξ.Limit
  open Limξ public

  -- The six-clause story at the nested carrier, assembled from the kit, the
  -- step clause and the sixth limit clause.
  storyWClausesξ : KWξ.StoryClauses
  storyWClausesξ = KWξ.mkClause KWξ.pairhood KWξ.pairForm KWξ.pairhood-out KWξ.pairhood-in KWξ.∷₊
                   KWξ.mkClause KWξ.singleValued KWξ.singleForm KWξ.single-out KWξ.single-in KWξ.∷₊
                   KWξ.mkClause KWξ.zeroClause KWξ.zeroForm KWξ.zero-out KWξ.zero-in KWξ.∷₊
                   KWξ.mkClause KWξ.exactDom KWξ.exactDomForm KWξ.exactDom-out KWξ.exactDom-in KWξ.∷₊
                   KWξ.clauseOk WClξ.succClause WClξ.succForm WClξ.succ-ok KWξ.∷₊
                   KWξ.clauseOk Stξ.limitClause limitForm limit-ok KWξ.∷₊ KWξ.end

  storyWξ : S → Type (ℓ-suc ℓ)
  storyWξ = KWξ.storyCl storyWClausesξ

  storyFormWξ : Formula ⟪ Wξ ⟫ 2
  storyFormWξ = KWξ.storyForm storyWClausesξ

  storyWξ-out : (f : KWξ.SM) (x : ⟪ Wξ ⟫)
              → ⟨ (f ∷ KWξ.ι x ∷ []) KWξ.⊨ᵐ storyFormWξ ⟩ → storyWξ (fst f)
  storyWξ-out = KWξ.story-out storyWClausesξ

  storyWξ-in : (f : KWξ.SM) (x : ⟪ Wξ ⟫)
             → storyWξ (fst f) → ⟨ (f ∷ KWξ.ι x ∷ []) KWξ.⊨ᵐ storyFormWξ ⟩
  storyWξ-in = KWξ.story-in storyWClausesξ

  storyWξ-ok : (f : KWξ.SM) (x : ⟪ Wξ ⟫)
             → ⟨ (f ∷ KWξ.ι x ∷ []) KWξ.⊨ᵐ storyFormWξ ⟩ ⟷ storyWξ (fst f)
  storyWξ-ok = KWξ.story-ok storyWClausesξ

  -- The story at the nested carrier implies the story at gamma: every clause
  -- is carrier-free except the exact domain, whose witness lies in Lset xi.
  storyWξ→storyW : (f : S) → storyWξ f → S.storyW f
  storyWξ→storyW f st = ( st .fst , ( st .snd .fst , ( st .snd .snd .fst
    , ( exactDomW , ( st .snd .snd .snd .snd .fst
      , st .snd .snd .snd .snd .snd ) ) ) ) )
    where
    exactDomW : S.KW.exactDom f
    exactDomW = PT.rec squash₁ go (st .snd .snd .snd .fst)
      where
      go : Σ[ δ ∈ S ] ( ⟨ δ ∈ˢ Wξ ⟩ × IsOrd δ
             × ((a : S) → ⟨ a ∈ˢ δ ⟩ → ∥ Σ[ b ∈ S ] ⟨ pr a b ∈ˢ f ⟩ ∥₁)
             × ((a : S) → ∥ Σ[ b ∈ S ] ⟨ pr a b ∈ˢ f ⟩ ∥₁ → ⟨ a ∈ˢ δ ⟩) )
         → S.KW.exactDom f
      go (δ , (δ∈Wξ , ordδ , in-dir , out-dir)) =
        ∣ δ , ( Lset-mono {α = γ} {β = ξ} ξ∈γ δ∈Wξ , ordδ , in-dir , out-dir ) ∣₁

-- The carried sequence at xi: the pair family at the nested carrier, its
-- decode at bound xi, and the segment with its six-clause story at gamma.
-- The witnesses below xi (the recursion) and the memberships at xi are
-- parameters, the smallest decisive miniature of the general limit case.
  module Carried
    (memLξ : (δ : S) → ⟨ δ ∈ˢ ξ ⟩ → ⟨ Sset δ ∈ˢ Lset ξ ⟩)
    (below : (η : S) → ⟨ η ∈ˢ ξ ⟩
           → Σ[ s ∈ S ] (⟨ s ∈ˢ Wξ ⟩ × storyWξ s × ⟨ pr η (Sset η) ∈ˢ s ⟩))
    where

    -- The story formula renamed into the arity-4 environment.
    embStoryξ : Fin 2 → Fin 4
    embStoryξ zero = suc (suc zero)
    embStoryξ (suc zero) = suc zero

    storyRenξ : Formula ⟪ Wξ ⟫ 4
    storyRenξ = renameFo embStoryξ storyFormWξ

    module RenSξ = Sat (hPropAlgebra (ℓ-suc ℓ)) (𝒮ᵥ ↾ (λ x → x ∈ˢ Wξ))
      {ℓ} {⟪ Wξ ⟫} KWξ.ι

    smEtaξ : (x : KWξ.SM) → x ≡ KWξ.ι (∈-asFiber {a = fst x} {b = Wξ} (snd x) .fst)
    smEtaξ x = ΣPathP (p , q)
      where
      p : fst x ≡ fst (KWξ.ι (∈-asFiber {a = fst x} {b = Wξ} (snd x) .fst))
      p = sym (∈-asFiber {a = fst x} {b = Wξ} (snd x) .snd)
      q : PathP (λ i → ⟨ p i ∈ˢ Wξ ⟩) (snd x)
             (snd (KWξ.ι (∈-asFiber {a = fst x} {b = Wξ} (snd x) .fst)))
      q = isProp→PathP (λ i → snd (p i ∈ˢ Wξ))
        (snd x) (snd (KWξ.ι (∈-asFiber {a = fst x} {b = Wξ} (snd x) .fst)))

    storyRen-okξ : (δ : Vec KWξ.SM 4)
                 → ⟨ δ KWξ.⊨ᵐ storyRenξ ⟩ ⟷ storyWξ (fst (lookup (suc (suc zero)) δ))
    storyRen-okξ δ = (out , bwd)
      where
      sm ym : KWξ.SM
      sm = lookup (suc (suc zero)) δ
      ym = lookup (suc zero) δ
      fibY : ⟪ Wξ ⟫
      fibY = ∈-asFiber {a = fst ym} {b = Wξ} (snd ym) .fst
      ag : RenSξ.Agrees embStoryξ δ (sm ∷ ym ∷ [])
      ag zero = refl
      ag (suc zero) = refl
      out : ⟨ δ KWξ.⊨ᵐ storyRenξ ⟩ → storyWξ (fst sm)
      out h = storyWξ-ok sm fibY .fst
        (subst (λ w → ⟨ (sm ∷ w ∷ []) KWξ.⊨ᵐ storyFormWξ ⟩) (smEtaξ ym)
          (subst ⟨_⟩ (sym (RenSξ.⊨-rename embStoryξ storyFormWξ δ (sm ∷ ym ∷ []) ag)) h))
      bwd : storyWξ (fst sm) → ⟨ δ KWξ.⊨ᵐ storyRenξ ⟩
      bwd st = subst ⟨_⟩
        (RenSξ.⊨-rename embStoryξ storyFormWξ δ (sm ∷ ym ∷ []) ag)
        (subst (λ w → ⟨ (sm ∷ w ∷ []) KWξ.⊨ᵐ storyFormWξ ⟩) (sym (smEtaξ ym))
          (storyWξ-ok sm fibY .snd st))

    -- The pair family's defining formula at the nested carrier (T159's, with
    -- the bound read from the exact domain at xi, not from the carrier).
    segBodyξ : Formula ⟪ Wξ ⟫ 4
    segBodyξ = (KWξ.PK.prAt (suc (suc (suc zero))) zero (suc zero))
            ∧̇ (KWξ.isOrdAt zero)
            ∧̇ storyRenξ
            ∧̇ (∃̇∈ (var (suc (suc zero)))
                  (KWξ.PK.prAt zero (suc zero) (suc (suc zero))))

    segFormξ : Formula ⟪ Wξ ⟫ 1
    segFormξ = ∃̇ (∃̇ (∃̇ segBodyξ))

    module Dξ = DefOf Wξ

    Pξ : S
    Pξ = Dξ.defSet segFormξ

    -- The bound read: an exact-domain witness of a story at Lset xi is an
    -- ordinal member of xi, so its pairs' first components lie below xi.
    exactDom-ξ∈ξ : (f : S) (η y : S) → storyWξ f → ⟨ pr η y ∈ˢ f ⟩ → ⟨ η ∈ˢ ξ ⟩
    exactDom-ξ∈ξ f η y h4 pr∈ = PT.rec (snd (η ∈ˢ ξ)) dStep (h4 .snd .snd .snd .fst)
      where
      dStep : Σ[ δ₀ ∈ S ] ( ⟨ δ₀ ∈ˢ Wξ ⟩ × IsOrd δ₀
               × ((a : S) → ⟨ a ∈ˢ δ₀ ⟩ → ∥ Σ[ b ∈ S ] ⟨ pr a b ∈ˢ f ⟩ ∥₁)
               × ((a : S) → ∥ Σ[ b ∈ S ] ⟨ pr a b ∈ˢ f ⟩ ∥₁ → ⟨ a ∈ˢ δ₀ ⟩) )
            → ⟨ η ∈ˢ ξ ⟩
      dStep (δ₀ , (δ₀∈u , ordδ₀ , _ , out-d)) =
        isLimit-ord ξ limξ .fst {x = δ₀} {y = η} η∈δ₀ δ₀∈ξ
        where
        η∈δ₀ : ⟨ η ∈ˢ δ₀ ⟩
        η∈δ₀ = out-d η ∣ y , pr∈ ∣₁
        δ₀∈ξ : ⟨ δ₀ ∈ˢ ξ ⟩
        δ₀∈ξ = ord∈Lset→∈ ξ (isLimit-ord ξ limξ) δ₀ ordδ₀ δ₀∈u

    -- The decode at the nested carrier: the extension is exactly the pairs
    -- (eta, Sset eta) with eta below xi.
    segForm-okξ : (m : ⟪ Wξ ⟫)
                → ⟨ (KWξ.ι m ∷ []) KWξ.⊨ᵐ segFormξ ⟩
                ⟷ ∥ Σ[ η ∈ S ] (⟨ η ∈ˢ ξ ⟩ × (⟪ Wξ ⟫↪ m ≡ pr η (Sset η))) ∥₁
    segForm-okξ m = (out , bwd)
      where
      δ₁ : Vec KWξ.SM 1
      δ₁ = KWξ.ι m ∷ []
      out : ⟨ δ₁ KWξ.⊨ᵐ segFormξ ⟩
          → ∥ Σ[ η ∈ S ] (⟨ η ∈ˢ ξ ⟩ × (⟪ Wξ ⟫↪ m ≡ pr η (Sset η))) ∥₁
      out sat = PT.rec squash₁ s₁ sat
        where
        s₁ : Σ[ sm ∈ KWξ.SM ] ⟨ (sm ∷ δ₁) KWξ.⊨ᵐ ∃̇ (∃̇ segBodyξ) ⟩
           → ∥ Σ[ η ∈ S ] (⟨ η ∈ˢ ξ ⟩ × (⟪ Wξ ⟫↪ m ≡ pr η (Sset η))) ∥₁
        s₁ (sm , rest₁) = PT.rec squash₁ s₂ rest₁
          where
          s₂ : Σ[ ym ∈ KWξ.SM ] ⟨ (ym ∷ sm ∷ δ₁) KWξ.⊨ᵐ ∃̇ segBodyξ ⟩
             → ∥ Σ[ η ∈ S ] (⟨ η ∈ˢ ξ ⟩ × (⟪ Wξ ⟫↪ m ≡ pr η (Sset η))) ∥₁
          s₂ (ym , rest₂) = PT.rec squash₁ s₃ rest₂
            where
            s₃ : Σ[ ηm ∈ KWξ.SM ] ⟨ (ηm ∷ ym ∷ sm ∷ δ₁) KWξ.⊨ᵐ segBodyξ ⟩
               → ∥ Σ[ η ∈ S ] (⟨ η ∈ˢ ξ ⟩ × (⟪ Wξ ⟫↪ m ≡ pr η (Sset η))) ∥₁
            s₃ (ηm , (pr-sat , (ord-sat , (st-sat , pr∈-sat)))) =
              ∣ fst ηm , (η∈ξ , x≡prηSη) ∣₁
              where
              δ₄ : Vec KWξ.SM 4
              δ₄ = ηm ∷ ym ∷ sm ∷ δ₁
              x≡prηy : ⟪ Wξ ⟫↪ m ≡ pr (fst ηm) (fst ym)
              x≡prηy = KWξ.PK.prAt-out (suc (suc (suc zero))) zero (suc zero)
                δ₄ pr-sat
              stξ : storyWξ (fst sm)
              stξ = storyRen-okξ δ₄ .fst st-sat
              prηy∈s : ⟨ pr (fst ηm) (fst ym) ∈ˢ fst sm ⟩
              prηy∈s = KWξ.pair∈ (suc (suc zero)) zero (suc zero) δ₄ .fst pr∈-sat
              η∈ξ : ⟨ fst ηm ∈ˢ ξ ⟩
              η∈ξ = exactDom-ξ∈ξ (fst sm) (fst ηm) (fst ym) stξ prηy∈s
              η∈γ : ⟨ fst ηm ∈ˢ γ ⟩
              η∈γ = isLimit-ord γ limγ .fst {x = ξ} {y = fst ηm} η∈ξ ξ∈γ
              y≡Ssetη : fst ym ≡ Sset (fst ηm)
              y≡Ssetη = S.chain (fst sm) (storyWξ→storyW (fst sm) stξ)
                (fst ηm) (fst ym) η∈γ prηy∈s
              x≡prηSη : ⟪ Wξ ⟫↪ m ≡ pr (fst ηm) (Sset (fst ηm))
              x≡prηSη = x≡prηy ∙ cong₂ pr refl y≡Ssetη
      bwd : ∥ Σ[ η ∈ S ] (⟨ η ∈ˢ ξ ⟩ × (⟪ Wξ ⟫↪ m ≡ pr η (Sset η))) ∥₁
          → ⟨ δ₁ KWξ.⊨ᵐ segFormξ ⟩
      bwd h = PT.rec (snd (δ₁ KWξ.⊨ᵐ segFormξ)) step₀ h
        where
        step₀ : Σ[ η ∈ S ] (⟨ η ∈ˢ ξ ⟩ × (⟪ Wξ ⟫↪ m ≡ pr η (Sset η)))
              → ⟨ δ₁ KWξ.⊨ᵐ segFormξ ⟩
        step₀ (η , (η∈ξ , x≡prηSη)) = ∣ sm , (∣ ym , (∣ ηm , body-sat ∣₁) ∣₁) ∣₁
          where
          w : Σ[ s ∈ S ] (⟨ s ∈ˢ Wξ ⟩ × storyWξ s × ⟨ pr η (Sset η) ∈ˢ s ⟩)
          w = below η η∈ξ
          η∈W : ⟨ η ∈ˢ Wξ ⟩
          η∈W = Lset-mono {α = ξ} {β = sucV η} (limit-succ-mem ξ η limξ η∈ξ)
            (ord∈Lset-suc η (mem-ord {A = ξ} (isLimit-ord ξ limξ) η η∈ξ))
          sm ym ηm : KWξ.SM
          sm = KWξ.PK.pt (fst w) (w .snd .fst)
          ym = KWξ.PK.pt (Sset η) (memLξ η η∈ξ)
          ηm = KWξ.PK.pt η η∈W
          δ₄ : Vec KWξ.SM 4
          δ₄ = ηm ∷ ym ∷ sm ∷ δ₁
          body-sat : ⟨ δ₄ KWξ.⊨ᵐ segBodyξ ⟩
          body-sat = ( pr-sat , (ord-sat , (st-sat , pr∈-sat)) )
            where
            pr-sat : ⟨ δ₄ KWξ.⊨ᵐ KWξ.PK.prAt (suc (suc (suc zero))) zero (suc zero) ⟩
            pr-sat = KWξ.PK.prAt-in (suc (suc (suc zero))) zero (suc zero) δ₄
              x≡prηSη
            ord-sat : ⟨ δ₄ KWξ.⊨ᵐ KWξ.isOrdAt zero ⟩
            ord-sat = KWξ.isOrd-in zero δ₄
              (mem-ord {A = ξ} (isLimit-ord ξ limξ) η η∈ξ)
            st-sat : ⟨ δ₄ KWξ.⊨ᵐ storyRenξ ⟩
            st-sat = storyRen-okξ δ₄ .snd (w .snd .snd .fst)
            pr∈-sat : ⟨ δ₄ KWξ.⊨ᵐ ∃̇∈ (var (suc (suc zero)))
                         (KWξ.PK.prAt zero (suc zero) (suc (suc zero))) ⟩
            pr∈-sat = KWξ.pair∈ (suc (suc zero)) zero (suc zero) δ₄ .snd
              (w .snd .snd .snd)

    -- The pair family's decode at bound xi, in the Segment shape.
    P∈ξ : (p : S) → ⟨ p ∈ˢ Pξ ⟩ ⟷ ∥ Σ[ η ∈ S ] (⟨ η ∈ˢ ξ ⟩
            × (p ≡ pr η (Sset η))) ∥₁
    P∈ξ p = (out , bwd)
      where
      out : ⟨ p ∈ˢ Pξ ⟩ → ∥ Σ[ η ∈ S ] (⟨ η ∈ˢ ξ ⟩ × (p ≡ pr η (Sset η))) ∥₁
      out p∈ = PT.rec squash₁ go (segForm-okξ m .fst sat)
        where
        m : ⟪ Wξ ⟫
        m = ∈-asFiber {a = p} {b = Wξ} (Dξ.defSet⊆A segFormξ p p∈) .fst
        sat : ⟨ (KWξ.ι m ∷ []) KWξ.⊨ᵐ segFormξ ⟩
        sat = subst ⟨_⟩ (Dξ.defSet-mem segFormξ m)
          (subst (λ w → ⟨ w ∈ˢ Pξ ⟩) (sym (∈-asFiber {a = p} {b = Wξ}
            (Dξ.defSet⊆A segFormξ p p∈) .snd)) p∈)
        go : Σ[ η ∈ S ] (⟨ η ∈ˢ ξ ⟩ × (⟪ Wξ ⟫↪ m ≡ pr η (Sset η)))
           → ∥ Σ[ η ∈ S ] (⟨ η ∈ˢ ξ ⟩ × (p ≡ pr η (Sset η))) ∥₁
        go (η , (η∈ξ , q)) = ∣ η
          , ( η∈ξ , sym (∈-asFiber {a = p} {b = Wξ} (Dξ.defSet⊆A segFormξ p p∈) .snd) ∙ q ) ∣₁
      bwd : ∥ Σ[ η ∈ S ] (⟨ η ∈ˢ ξ ⟩ × (p ≡ pr η (Sset η))) ∥₁
          → ⟨ p ∈ˢ Pξ ⟩
      bwd = PT.rec (snd (p ∈ˢ Pξ)) go
        where
        go : Σ[ η ∈ S ] (⟨ η ∈ˢ ξ ⟩ × (p ≡ pr η (Sset η))) → ⟨ p ∈ˢ Pξ ⟩
        go (η , (η∈ξ , q)) = subst (λ w → ⟨ w ∈ˢ Pξ ⟩) (sym q)
          (subst (λ w → ⟨ w ∈ˢ Pξ ⟩) (fib .snd)
            (subst ⟨_⟩ (sym (Dξ.defSet-mem segFormξ m))
              (segForm-okξ m .snd ∣ η , (η∈ξ , fib .snd) ∣₁)))
          where
          w : Σ[ s ∈ S ] (⟨ s ∈ˢ Wξ ⟩ × storyWξ s × ⟨ pr η (Sset η) ∈ˢ s ⟩)
          w = below η η∈ξ
          pr∈W : ⟨ pr η (Sset η) ∈ˢ Wξ ⟩
          pr∈W = Wtrξ {x = fst w} {y = pr η (Sset η)} (w .snd .snd .snd) (w .snd .fst)
          fib : Σ[ m ∈ ⟪ Wξ ⟫ ] (⟪ Wξ ⟫↪ m ≡ pr η (Sset η))
          fib = ∈-asFiber {a = pr η (Sset η)} {b = Wξ} pr∈W
          m : ⟪ Wξ ⟫
          m = fib .fst

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

    -- The placements: the family, the top pair, and the segment, all below
    -- gamma.
    Pξ∈Lsucξ : ⟨ Pξ ∈ˢ Lset (sucV ξ) ⟩
    Pξ∈Lsucξ = 𝒟ₒ⊆Lsuc ξ Pξ (𝒟ₒ-intro Wξ Pξ ∣ segFormξ , refl ∣₁)

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
