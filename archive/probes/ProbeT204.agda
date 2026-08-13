{-# OPTIONS --cubical --safe --guardedness #-}

-- [L3.32-T204] Probe: the bounded family formula at the second limit
-- l = +ω ω.  Prove carve-⊇ through the general value chain (successor
-- case gated on the general identification, SURVEY).  Untracked probe.

open import Base.Prelude
open import Base.Truth
open import Base.Classical using ( LEM )
open import Cubical.HITs.CumulativeHierarchy.Base using ( V; setIsSet )

module ProbeT204 {ℓ : Level} (lem : LEM (ℓ-suc ℓ)) where

open import FOL.ZFStructure using ( module hPropStructure )
open import FOL.Syntax using ( Formula )
open import V.Hierarchy {ℓ} using ( 𝒮ᵥ; extensionalV; ∈-induction )
open import V.Model {ℓ} using ( self∈sucV )
open import V.Coding {ℓ} using ( pr )
open import Cubical.HITs.CumulativeHierarchy.Constructions
  using ( ∅; ω; module InfinitySet )
open InfinitySet using ( sucV; #_ )
open import L.Constructible {ℓ} using ( IsOrd; Lset; Lset-mono )
open import L.Ordinal {ℓ} using ( ω-ord )
open import L.Rud.OrdArith {ℓ} lem using ( isLimit; limit-mem-ord; isSucc; predecessor-mem; ord-case )
open import L.Rud.OrdBlocks {ℓ} lem using ( +ω; +ω-limit; +ω-ord )
open import L.Rud.Step {ℓ} lem ∅ using ( Sset; Sset-trans; limit-succ-mem )
open import L.Rud.Bridge {ℓ} lem ∅ using ( U; Lset-union-limit; Lset-zero )
open import L.LevelKit {ℓ} using ( module LevelKit )
open import L.Definability {ℓ} using ( module DefOf )
open import L.InitialSegment {ℓ} using ( _∈ran_; _⟷_ )
open import L.TowerKit {ℓ} lem ∅ using ( empty-⊆ )
open import Cubical.Functions.Logic using ( ⇔toPath )
import Cubical.HITs.PropositionalTruncation as PT
open PT using ( ∣_∣₁; ∥_∥₁; squash₁ )
import Cubical.Data.Empty as Empty
open import Cubical.Data.Sum using ( _⊎_; inl; inr )
open import Cubical.Foundations.HLevels using ( isProp×; isPropΠ2; isPropΠ3 )
open import Cubical.HITs.CumulativeHierarchy.Properties using ( ⟪_⟫ )
open TruthAlgebra (hPropAlgebra (ℓ-suc ℓ))
open hPropStructure 𝒮ᵥ

_⊆_ : S → S → Type (ℓ-suc ℓ)
u ⊆ v = (x : S) → ⟨ x ∈ˢ u ⟩ → ⟨ x ∈ˢ v ⟩

ext-⊆ : {u v : S} → u ⊆ v → v ⊆ u → u ≡ v
ext-⊆ {u} {v} sub sup = extensionalV (λ x → ⇔toPath (sub x) (sup x))

-- The second limit l = +ω ω and its limit certificate.
l : S
l = +ω ω

l-ord : IsOrd l
l-ord = +ω-ord ω ω-ord

l-lim : ⟨ isLimit l ⟩
l-lim = +ω-limit ω ω-ord

-- The carrier Sset (U l) and the delivered clause kit at it.
u : S
u = Sset (U l)

module Kit = LevelKit u (Sset-trans (U l))

-- The internal powerset and the one-way successor clause (the meta shapes).
powRel : S → S → Type (ℓ-suc ℓ)
powRel c b = (⟨ b ∈ˢ u ⟩ × ((z : S) → ⟨ z ∈ˢ b ⟩ → z ⊆ c)
             × ((z : S) → ⟨ z ∈ˢ u ⟩ → z ⊆ c → ⟨ z ∈ˢ b ⟩))

succValClause1 : S → Type (ℓ-suc ℓ)
succValClause1 f = (a c b : S) → ⟨ pr a c ∈ˢ f ⟩ → ⟨ pr (sucV a) b ∈ˢ f ⟩ → powRel c b

powRelProp : (c b : S) → isProp (powRel c b)
powRelProp c b = isProp× (snd (b ∈ˢ u)) (isProp× (isPropΠ2 (λ z _ → isPropΠ2 (λ w _ → snd (w ∈ˢ c)))) (isPropΠ3 (λ z _ _ → snd (z ∈ˢ b))))

limClause : S → Type (ℓ-suc ℓ)
limClause f = (a b : S) → ⟨ isLimit a ⟩ → ⟨ pr a b ∈ˢ f ⟩ → (z : S)
  → ⟨ z ∈ˢ b ⟩ ⟷ ∥ Σ[ ξ ∈ S ] (⟨ ξ ∈ˢ a ⟩
       × ∥ Σ[ w ∈ S ] (⟨ pr ξ w ∈ˢ f ⟩ × ⟨ z ∈ˢ w ⟩) ∥₁) ∥₁

bound : S → Type (ℓ-suc ℓ)
bound f = (a : S) → ∥ Σ[ y ∈ S ] ⟨ pr a y ∈ˢ f ⟩ ∥₁ → ⟨ a ∈ˢ l ⟩

-- The bounded story: the kit's four clauses, successor, limit, bound.
boundedStory : S → Type (ℓ-suc ℓ)
boundedStory f = Kit.pairhood f × Kit.singleValued f × Kit.zeroClause f × Kit.exactDom f × succValClause1 f × limClause f × bound f

-- SURVEY parameter: the general identification (Bridge:338-352 records the
-- ω·2 instance as a classical fact, undelivered).
module BoundedCarve
  (ident : (b : S) → ⟨ b ∈ˢ l ⟩ → (x : S) → powRel (Lset b) x
         → x ≡ Lset (sucV b))
  where

  -- The value chain at a general ordinal index: a bounded story's value at
  -- the pair index a is the L-stage at a, by ordinal induction on a.
  chain : (f : S) → boundedStory f → (a x : S) → ⟨ a ∈ˢ l ⟩
        → ⟨ pr a x ∈ˢ f ⟩ → x ≡ Lset a
  chain f st a x a∈l ax∈f = ∈-induction {P = P} step a a∈l x ax∈f
    where
    P : S → Type (ℓ-suc ℓ)
    P b = ⟨ b ∈ˢ l ⟩ → (x : S) → ⟨ pr b x ∈ˢ f ⟩ → x ≡ Lset b
    step : (b : S) → ((y : S) → y ∈ᵗ b → P y) → P b
    step b IH b∈l x bx∈f =
      go (ord-case b (limit-mem-ord l l-lim b b∈l)) x bx∈f
      where
      go : (b ≡ ∅) ⊎ (⟨ isSucc b ⟩ ⊎ ⟨ isLimit b ⟩) → (x : S)
         → ⟨ pr b x ∈ˢ f ⟩ → x ≡ Lset b
      go (inl z) x px = subst (λ w → x ≡ Lset w) (sym z) (x≡∅ ∙ sym Lset-zero)
        where
        px' : ⟨ pr ∅ x ∈ˢ f ⟩
        px' = subst (λ w → ⟨ pr w x ∈ˢ f ⟩) z px
        x≡∅ : x ≡ ∅
        x≡∅ = PT.rec (setIsSet x ∅) zStep (st .snd .snd .fst)
          where
          zStep : Σ[ a ∈ S ] ( ((y : S) → ⟨ y ∈ˢ a ⟩ → Empty.⊥)
                   × ⟨ pr a a ∈ˢ f ⟩ ) → x ≡ ∅
          zStep (a , (emp , aa∈f)) = st .snd .fst ∅ x ∅ px' pr∅∅
            where
            a≡∅ : a ≡ ∅
            a≡∅ = empty-⊆ a emp
            pr∅∅ : ⟨ pr ∅ ∅ ∈ˢ f ⟩
            pr∅∅ = subst (λ w → ⟨ pr w w ∈ˢ f ⟩) a≡∅ aa∈f
      go (inr (inl (c , ordC , sc≡b))) x px = subst (λ w → x ≡ Lset w) sc≡b
        (PT.rec (setIsSet x (Lset (sucV c))) δStep (st .snd .snd .snd .fst))
        where
        c∈b : ⟨ c ∈ˢ b ⟩
        c∈b = predecessor-mem c b sc≡b
        c∈l : ⟨ c ∈ˢ l ⟩
        c∈l = l-ord .fst c∈b b∈l
        px' : ⟨ pr (sucV c) x ∈ˢ f ⟩
        px' = subst (λ w → ⟨ pr w x ∈ˢ f ⟩) (sym sc≡b) px
        δStep : Σ[ δ ∈ S ] (⟨ δ ∈ˢ u ⟩ × IsOrd δ
                 × ((a : S) → ⟨ a ∈ˢ δ ⟩ → ∥ Σ[ b ∈ S ] ⟨ pr a b ∈ˢ f ⟩ ∥₁)
                 × ((a : S) → ∥ Σ[ b ∈ S ] ⟨ pr a b ∈ˢ f ⟩ ∥₁ → ⟨ a ∈ˢ δ ⟩))
              → x ≡ Lset (sucV c)
        δStep (δ , (δ∈u , ordδ , in-dir , out-dir)) =
          ident c c∈l x pb
          where
          suc∈δ : ⟨ sucV c ∈ˢ δ ⟩
          suc∈δ = out-dir (sucV c) ∣ x , px' ∣₁
          c∈δ : ⟨ c ∈ˢ δ ⟩
          c∈δ = ordδ .fst {x = sucV c} {y = c} (self∈sucV c) suc∈δ
          pb : powRel (Lset c) x
          pb = PT.rec (powRelProp (Lset c) x) cStep (in-dir c c∈δ)
            where
            cStep : Σ[ w ∈ S ] ⟨ pr c w ∈ˢ f ⟩ → powRel (Lset c) x
            cStep (w , pcw) = st .snd .snd .snd .snd .fst c (Lset c) x
              prcL px'
              where
              prcL : ⟨ pr c (Lset c) ∈ˢ f ⟩
              prcL = subst (λ w' → ⟨ pr c w' ∈ˢ f ⟩)
                (IH c c∈b c∈l w pcw) pcw
      go (inr (inr limB)) x px = ext-⊆ x⊆L L⊆x
        where
        x⊆L : x ⊆ Lset b
        x⊆L z z∈x = PT.rec (snd (z ∈ˢ Lset b)) step₁
          (st .snd .snd .snd .snd .snd .fst b x limB px z .fst z∈x)
          where
          step₁ : Σ[ ξ ∈ S ] (⟨ ξ ∈ˢ b ⟩
                    × ∥ Σ[ w ∈ S ] (⟨ pr ξ w ∈ˢ f ⟩ × ⟨ z ∈ˢ w ⟩) ∥₁)
                → ⟨ z ∈ˢ Lset b ⟩
          step₁ (ξ , (ξ∈b , rest)) = PT.rec (snd (z ∈ˢ Lset b)) step₂ rest
            where
            ξ∈l : ⟨ ξ ∈ˢ l ⟩
            ξ∈l = l-ord .fst ξ∈b b∈l
            step₂ : Σ[ w ∈ S ] (⟨ pr ξ w ∈ˢ f ⟩ × ⟨ z ∈ˢ w ⟩)
                  → ⟨ z ∈ˢ Lset b ⟩
            step₂ (w , (pw , z∈w)) = Lset-mono {α = b} {β = ξ} ξ∈b
              (subst (λ w' → ⟨ z ∈ˢ w' ⟩) (IH ξ ξ∈b ξ∈l w pw) z∈w)
        L⊆x : Lset b ⊆ x
        L⊆x z z∈L = PT.rec (snd (z ∈ˢ x)) step₁
          (Lset-union-limit b limB z z∈L)
          where
          step₁ : Σ[ δ ∈ S ] (⟨ δ ∈ˢ b ⟩ × ⟨ z ∈ˢ Lset (sucV δ) ⟩)
                → ⟨ z ∈ˢ x ⟩
          step₁ (δ , (δ∈b , z∈Lsucδ)) =
            PT.rec (snd (z ∈ˢ x)) step₂ (st .snd .snd .snd .fst)
            where
            δ'∈b : ⟨ sucV δ ∈ˢ b ⟩
            δ'∈b = limit-succ-mem b δ limB δ∈b
            step₂ : Σ[ δ₀ ∈ S ] (⟨ δ₀ ∈ˢ u ⟩ × IsOrd δ₀
                     × ((a : S) → ⟨ a ∈ˢ δ₀ ⟩
                          → ∥ Σ[ b ∈ S ] ⟨ pr a b ∈ˢ f ⟩ ∥₁)
                     × ((a : S) → ∥ Σ[ b ∈ S ] ⟨ pr a b ∈ˢ f ⟩ ∥₁
                          → ⟨ a ∈ˢ δ₀ ⟩)) → ⟨ z ∈ˢ x ⟩
            step₂ (δ₀ , (δ₀∈u , ordδ₀ , in-dir , out-dir)) =
              PT.rec (snd (z ∈ˢ x)) step₃ (in-dir (sucV δ) δ'∈δ₀)
              where
              b∈δ₀ : ⟨ b ∈ˢ δ₀ ⟩
              b∈δ₀ = out-dir b ∣ x , px ∣₁
              δ'∈δ₀ : ⟨ sucV δ ∈ˢ δ₀ ⟩
              δ'∈δ₀ = ordδ₀ .fst {x = b} {y = sucV δ} δ'∈b b∈δ₀
              step₃ : Σ[ w ∈ S ] ⟨ pr (sucV δ) w ∈ˢ f ⟩ → ⟨ z ∈ˢ x ⟩
              step₃ (w , pδ'w) =
                st .snd .snd .snd .snd .snd .fst b x limB px z .snd
                ∣ sucV δ , (δ'∈b
                  , ∣ Lset (sucV δ) , (pδ'L , z∈Lsucδ) ∣₁) ∣₁
                where
                pδ'L : ⟨ pr (sucV δ) (Lset (sucV δ)) ∈ˢ f ⟩
                pδ'L = subst (λ w' → ⟨ pr (sucV δ) w' ∈ˢ f ⟩)
                  (IH (sucV δ) δ'∈b (l-ord .fst δ'∈b b∈l) w pδ'w) pδ'w

  -- carve-⊇ from the decode of the bounded family formula (parameter).
  module Carve (σb : Formula ⟪ u ⟫ 1)
    (σb-out : (y : S) → ⟨ y ∈ˢ DefOf.defSet u σb ⟩
            → ∥ Σ[ f ∈ S ] Σ[ st ∈ boundedStory f ] Σ[ fu ∈ ⟨ f ∈ˢ u ⟩ ] (y ∈ran f) ∥₁)
    where
    carve-⊇ : (y : S) → ⟨ y ∈ˢ DefOf.defSet u σb ⟩
            → ∥ Σ[ δ ∈ S ] (⟨ δ ∈ˢ l ⟩ × (y ≡ Lset δ)) ∥₁
    carve-⊇ y y∈ = PT.rec squash₁ fStep (σb-out y y∈)
      where
      fStep : Σ[ f ∈ S ] Σ[ st ∈ boundedStory f ] Σ[ fu ∈ ⟨ f ∈ˢ u ⟩ ] (y ∈ran f)
            → ∥ Σ[ δ ∈ S ] (⟨ δ ∈ˢ l ⟩ × (y ≡ Lset δ)) ∥₁
      fStep (f , (st , (fu , r))) = PT.rec squash₁ aStep r
        where
        aStep : Σ[ a ∈ S ] ⟨ pr a y ∈ˢ f ⟩ → ∥ Σ[ δ ∈ S ] (⟨ δ ∈ˢ l ⟩ × (y ≡ Lset δ)) ∥₁
        aStep (a , pray) = ∣ a , (a∈l , chain f st a y a∈l pray) ∣₁
          where
          a∈l : ⟨ a ∈ˢ l ⟩
          a∈l = st .snd .snd .snd .snd .snd .snd a ∣ y , pray ∣₁
