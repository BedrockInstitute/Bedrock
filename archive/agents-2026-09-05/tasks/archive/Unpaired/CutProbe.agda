{-# OPTIONS --cubical --guardedness #-}

open import Base.Prelude
open import Base.Classical using ( LEM )

module CutProbe {ℓ : Level} where

open import FOL.Syntax using ( Formula; ⊤̇; ⊥̇; _∧̇_ )
open import V.Hierarchy {ℓ} using ( extensionalV )
open import V.Coding {ℓ} using ( pr; pr-inj )
open import V.Model {ℓ} using ( self∈sucV )
open import L.Definability {ℓ} using ( module DefOf )
open import L.Godel.Operations {ℓ}
  using ( _∩_; ∩-in; ∩-out; _∖_; ∖-in; ∖-out
        ; values; values-in; values-wit
        ; extendGraph; extendGraph-zero; extendGraph-suc; extendGraph-out
        ; extendFamily; extendFamily-in; extendFamily-out )
open import L.Godel.Tuples {ℓ}
  using ( allTuples; allTuples-zero; allTuples-suc; tuple; tuple-empty )
open import L.Godel.Satisfaction {ℓ}
  using ( satSet; sat-in; sat-out; sat-⊤; sat-∧; sat-⊥; sat-defSet )
open import L.Godel.Terms {ℓ}
  using ( KT; ⟦_⟧ᴷ; toFormula; sound; module WithLEM )

import Cubical.HITs.PropositionalTruncation as PT
open PT using ( ∣_∣₁; ∥_∥₁ )
open import Cubical.Relation.Nullary using ( ¬_ )
import Cubical.Data.Empty as Empty
open import Cubical.Data.Empty using ( ⊥; isProp⊥ )
import Cubical.Data.Sum as Sum
open Sum using ( _⊎_; inl; inr )
open import Cubical.HITs.CumulativeHierarchy.Base using ( V; sett; _∈_; setIsSet )
open import Cubical.HITs.CumulativeHierarchy.Properties
  using ( _∈ₛ_; ∈∈ₛ; ⟪_⟫; ⟪_⟫↪; ∈ₛ⟪_⟫↪_; ∈-asFiber; _⊆_ )
open import Cubical.HITs.CumulativeHierarchy.Constructions
  using ( ∅; ∅-empty; module InfinitySet )
open InfinitySet using ( sucV; #_ )
open import Cubical.Functions.Logic using ( ⇔toPath )
open import Cubical.Foundations.Equiv using ( equivFun )
open import Cubical.Data.Unit using ( tt* )

module _ (A : V ℓ) where
  open DefOf A using ( defSet; Def; ι; ⊨ᵐ-small )

  -- ----------------------------------------------------------------
  -- Small helpers: the empty tuple family, and contradictions
  -- ----------------------------------------------------------------

  w∈allTuples0 : (w : V ℓ) → ⟨ w ∈ allTuples A 0 ⟩ → w ≡ ∅
  w∈allTuples0 w = PT.rec (setIsSet w ∅)
    λ { (g , e) → sym e ∙ tuple-empty A g }

  ∅∈allTuples0 : ⟨ ∅ ∈ allTuples A 0 ⟩
  ∅∈allTuples0 = ∣ (λ ()) , tuple-empty A (λ ()) ∣₁

  snotz-suc∅ : (a : V ℓ) → ¬ (sucV a ≡ ∅)
  snotz-suc∅ a e = ∅-empty a (∈∈ₛ {a = a} {b = ∅} .fst
    (subst (λ z → ⟨ a ∈ z ⟩) e (self∈sucV a)))

  notIn∅ : {x : V ℓ} → ⟨ x ∈ ∅ ⟩ → Empty.⊥
  notIn∅ {x} h = ∅-empty x (∈∈ₛ {a = x} {b = ∅} .fst h)

  values∅ : values ∅ ≡ ∅
  values∅ = extensionalV λ v → ⇔toPath
    (λ h → PT.rec (snd (v ∈ ∅)) (λ { (γ , hγ , _) → Empty.rec (notIn∅ hγ) })
      (values-wit {X = ∅} {v = v} h))
    (λ h → Empty.rec (notIn∅ h))

  -- ----------------------------------------------------------------
  -- Junk case 1: a mixed-arity intersection of two tuple families
  -- is empty, so its values-cut is ∅, which IS a definable subset.
  -- ----------------------------------------------------------------

  allTuples1-shape : (w : V ℓ) → ⟨ w ∈ allTuples A 1 ⟩
                   → ∥ Σ[ y ∈ V ℓ ] (⟨ y ∈ A ⟩ × (w ≡ extendGraph y ∅)) ∥₁
  allTuples1-shape w h = PT.rec PT.squash₁ go
    (extendFamily-out {X = allTuples A 0} {Y = A} {w = w}
      (subst (λ z → ⟨ w ∈ z ⟩) (allTuples-suc A 0) h))
    where
    go : Σ[ γ ∈ V ℓ ] Σ[ y ∈ V ℓ ]
           (⟨ γ ∈ allTuples A 0 ⟩ × ⟨ y ∈ A ⟩ × (w ≡ extendGraph y γ))
       → ∥ Σ[ y ∈ V ℓ ] (⟨ y ∈ A ⟩ × (w ≡ extendGraph y ∅)) ∥₁
    go (γ , y , hγ , hy , e) =
      ∣ y , hy , e ∙ cong (extendGraph y) (w∈allTuples0 γ hγ) ∣₁

  allTuples-12-disjoint : allTuples A 1 ∩ allTuples A 2 ≡ ∅
  allTuples-12-disjoint = extensionalV λ w → ⇔toPath (fwd w) (λ h → Empty.rec (notIn∅ h))
    where
    fwd : (w : V ℓ) → ⟨ w ∈ allTuples A 1 ∩ allTuples A 2 ⟩ → ⟨ w ∈ ∅ ⟩
    fwd w h = PT.rec (snd (w ∈ ∅)) step
      (allTuples1-shape w (∩-out {X = allTuples A 1} {Y = allTuples A 2} {x = w} h .fst))
      where
      step : Σ[ y ∈ V ℓ ] (⟨ y ∈ A ⟩ × (w ≡ extendGraph y ∅)) → ⟨ w ∈ ∅ ⟩
      step (y , hy , e1) = PT.rec (snd (w ∈ ∅)) step2
        (extendFamily-out {X = allTuples A 1} {Y = A} {w = w}
          (subst (λ z → ⟨ w ∈ z ⟩) (allTuples-suc A 1)
            (∩-out {X = allTuples A 1} {Y = allTuples A 2} {x = w} h .snd)))
        where
        step2 : Σ[ γ' ∈ V ℓ ] Σ[ y' ∈ V ℓ ]
                  (⟨ γ' ∈ allTuples A 1 ⟩ × ⟨ y' ∈ A ⟩ × (w ≡ extendGraph y' γ'))
              → ⟨ w ∈ ∅ ⟩
        step2 (γ' , y' , hγ' , hy' , e2) = PT.rec (snd (w ∈ ∅)) step3
          (allTuples1-shape γ' hγ')
          where
            step3 : Σ[ y'' ∈ V ℓ ] (⟨ y'' ∈ A ⟩ × (γ' ≡ extendGraph y'' ∅)) → ⟨ w ∈ ∅ ⟩
            step3 (y'' , hy'' , eγ') = Empty.rec (PT.rec Empty.isProp⊥ go
                (extendGraph-out {y = y} {γ = ∅} {z = pr (sucV ∅) y''}
                  (subst (λ z → ⟨ pr (sucV ∅) y'' ∈ z ⟩) (sym e2 ∙ e1) m₁))) where
              m₁ : ⟨ pr (sucV ∅) y'' ∈ extendGraph y' γ' ⟩
              m₁ = extendGraph-suc {y = y'} {γ = γ'} {a = ∅} {v = y''}
                (subst (λ z → ⟨ pr ∅ y'' ∈ z ⟩) (sym eγ')
                  (extendGraph-zero {y = y''} {γ = ∅}))
              go : (pr (sucV ∅) y'' ≡ pr ∅ y)
                 ⊎ (Σ[ a ∈ V ℓ ] Σ[ v ∈ V ℓ ]
                      (⟨ pr a v ∈ ∅ ⟩ × (pr (sucV ∅) y'' ≡ pr (sucV a) v)))
                 → ⊥
              go (inl e) = snotz-suc∅ ∅ (pr-inj {a = sucV ∅} {b = y''}
                                                {c = ∅} {d = y} e .fst)
              go (inr (a , v , hav , _)) = notIn∅ hav

  mixedArityInter : values (allTuples A 1 ∩ allTuples A 2) ≡ ∅
  mixedArityInter = cong values allTuples-12-disjoint ∙ values∅

  defSet⊥ : defSet ⊥̇ ≡ ∅
  defSet⊥ = sym (sat-defSet A ⊥̇) ∙ cong values (sat-⊥ A) ∙ values∅

  ∅∈Def : ⟨ ∅ ∈ Def ⟩
  ∅∈Def = ∣ ⊥̇ , defSet⊥ ∣₁

  -- ----------------------------------------------------------------
  -- Junk case 2: a same-arity intersection of satisfaction sets is
  -- again a satisfaction set (banked sat-∧), so its values-cut is a
  -- definable subset (banked sat-defSet).
  -- ----------------------------------------------------------------

  goodInter : values (allTuples A 1 ∩ allTuples A 1)
            ≡ defSet (⊤̇ ∧̇ ⊤̇)
  goodInter =
    cong values
      (cong₂ _∩_ (sym (sat-⊤ A)) (sym (sat-⊤ A)) ∙ sym (sat-∧ A ⊤̇ ⊤̇))
    ∙ sat-defSet A (⊤̇ ∧̇ ⊤̇)

  goodInter∈Def : ⟨ values (allTuples A 1 ∩ allTuples A 1) ∈ Def ⟩
  goodInter∈Def = subst (λ z → ⟨ z ∈ Def ⟩) (sym goodInter)
    ∣ (⊤̇ ∧̇ ⊤̇) , refl ∣₁

  -- ----------------------------------------------------------------
  -- Junk case 3: a complement over mismatched arities is the whole
  -- family, whose values-cut is the carrier A, a definable subset.
  -- ----------------------------------------------------------------

  ∖-disjoint : (X Y : V ℓ) → X ∩ Y ≡ ∅ → X ∖ Y ≡ X
  ∖-disjoint X Y d = extensionalV λ w → ⇔toPath
    (λ h → ∖-out {X = X} {Y = Y} {x = w} h .fst)
    (λ h → ∖-in {X = X} {Y = Y} {x = w} h λ hY →
      Empty.rec (notIn∅ (subst (λ z → ⟨ w ∈ z ⟩) d (∩-in {X = X} {Y = Y} h hY))))

  valuesAllTuples2 : values (allTuples A 2) ≡ A
  valuesAllTuples2 = extensionalV λ v → ⇔toPath (fwdV v) (bwdV v)
    where
    fwdV : (v : V ℓ) → ⟨ v ∈ values (allTuples A 2) ⟩ → ⟨ v ∈ A ⟩
    fwdV v h = PT.rec (snd (v ∈ A)) go (values-wit {X = allTuples A 2} {v = v} h)
      where
      go : Σ[ γ ∈ V ℓ ] (⟨ γ ∈ allTuples A 2 ⟩ × ⟨ pr (# 0) v ∈ γ ⟩)
         → ⟨ v ∈ A ⟩
      go (γ , hγ , hv) = PT.rec (snd (v ∈ A)) step
        (extendFamily-out {X = allTuples A 1} {Y = A} {w = γ}
          (subst (λ z → ⟨ γ ∈ z ⟩) (allTuples-suc A 1) hγ))
        where
        step : Σ[ γ' ∈ V ℓ ] Σ[ y' ∈ V ℓ ]
                 (⟨ γ' ∈ allTuples A 1 ⟩ × ⟨ y' ∈ A ⟩ × (γ ≡ extendGraph y' γ'))
             → ⟨ v ∈ A ⟩
        step (γ' , y' , hγ' , hy' , eγ) = PT.rec (snd (v ∈ A)) step2
          (extendGraph-out {y = y'} {γ = γ'} {z = pr ∅ v}
            (subst (λ z → ⟨ pr ∅ v ∈ z ⟩) eγ hv))
          where
          step2 : (pr ∅ v ≡ pr ∅ y')
                ⊎ (Σ[ a ∈ V ℓ ] Σ[ w ∈ V ℓ ]
                     (⟨ pr a w ∈ γ' ⟩ × (pr ∅ v ≡ pr (sucV a) w)))
                → ⟨ v ∈ A ⟩
          step2 (inl e) = subst (λ z → ⟨ z ∈ A ⟩) (sym (pr-inj {a = ∅} {b = v}
                                                          {c = ∅} {d = y'} e .snd)) hy'
          step2 (inr (a , w , haw , e)) = PT.rec (snd (v ∈ A)) step3
            (allTuples1-shape γ' hγ')
            where
            step3 : Σ[ y'' ∈ V ℓ ] (⟨ y'' ∈ A ⟩ × (γ' ≡ extendGraph y'' ∅))
                  → ⟨ v ∈ A ⟩
            step3 (y'' , hy'' , eγ'') =
              Empty.rec (PT.rec Empty.isProp⊥ go2
                (extendGraph-out {y = y''} {γ = ∅} {z = pr a w}
                  (subst (λ z → ⟨ pr a w ∈ z ⟩) eγ'' haw)))
              where
              go2 : (pr a w ≡ pr ∅ y'')
                  ⊎ (Σ[ a₂ ∈ V ℓ ] Σ[ w₂ ∈ V ℓ ]
                       (⟨ pr a₂ w₂ ∈ ∅ ⟩ × (pr a w ≡ pr (sucV a₂) w₂)))
                  → ⊥
              go2 (inl e1) = snotz-suc∅ ∅
                (cong sucV (sym (pr-inj {a = a} {b = w} {c = ∅} {d = y''} e1 .fst))
                 ∙ pr-inj {a = sucV a} {b = w} {c = ∅} {d = v} (sym e) .fst)
              go2 (inr (a₂ , w₂ , ha₂w₂ , _)) = notIn∅ ha₂w₂

    bwdV : (v : V ℓ) → ⟨ v ∈ A ⟩ → ⟨ v ∈ values (allTuples A 2) ⟩
    bwdV v h = build (∈-asFiber {a = v} {b = A} h)
      where
      build : Σ[ m ∈ ⟪ A ⟫ ] (⟪ A ⟫↪ m ≡ v)
            → ⟨ v ∈ values (allTuples A 2) ⟩
      build (m , e) = subst (λ z → ⟨ z ∈ values (allTuples A 2) ⟩) e work
        where
        membM : ⟨ ⟪ A ⟫↪ m ∈ A ⟩
        membM = ∈∈ₛ {a = ⟪ A ⟫↪ m} {b = A} .snd (∈ₛ⟪ A ⟫↪ m)
        γ₁ : V ℓ
        γ₁ = extendGraph (⟪ A ⟫↪ m) ∅
        γ₂ : V ℓ
        γ₂ = extendGraph (⟪ A ⟫↪ m) γ₁
        hγ₁ : ⟨ γ₁ ∈ allTuples A 1 ⟩
        hγ₁ = subst (λ z → ⟨ γ₁ ∈ z ⟩) (sym (allTuples-suc A 0))
            (extendFamily-in {X = allTuples A 0} {Y = A} ∅∈allTuples0
              membM)
        work : ⟨ ⟪ A ⟫↪ m ∈ values (allTuples A 2) ⟩
        work = values-in {X = allTuples A 2} {γ = γ₂} {v = ⟪ A ⟫↪ m}
            (subst (λ z → ⟨ γ₂ ∈ z ⟩) (sym (allTuples-suc A 1))
              (extendFamily-in {X = allTuples A 1} {Y = A} hγ₁
                membM))
            (extendGraph-zero {y = ⟪ A ⟫↪ m} {γ = γ₁})

  junkComplement : values (allTuples A 2 ∖ allTuples A 1) ≡ A
  junkComplement =
      cong values (∖-disjoint (allTuples A 2) (allTuples A 1)
        (subst (λ z → z ≡ ∅)
          (comm∩ (allTuples A 1) (allTuples A 2)) allTuples-12-disjoint))
    ∙ valuesAllTuples2
    where
    comm∩ : (X Y : V ℓ) → X ∩ Y ≡ Y ∩ X
    comm∩ X Y = extensionalV λ w → ⇔toPath
      (λ h → ∩-in {X = Y} {Y = X} (∩-out {X = X} {Y = Y} {x = w} h .snd)
                                      (∩-out {X = X} {Y = Y} {x = w} h .fst))
      (λ h → ∩-in {X = X} {Y = Y} (∩-out {X = Y} {Y = X} {x = w} h .snd)
                                      (∩-out {X = Y} {Y = X} {x = w} h .fst))

  defSet⊤ : defSet ⊤̇ ≡ A
  defSet⊤ = extensionalV λ w → ⇔toPath (fwd w) (bwd w)
    where
    fwd : (w : V ℓ) → ⟨ w ∈ defSet ⊤̇ ⟩ → ⟨ w ∈ A ⟩
    fwd w = PT.rec (snd (w ∈ A)) λ { ((m , _) , e) →
      subst (λ z → ⟨ z ∈ A ⟩) e (∈∈ₛ {a = ⟪ A ⟫↪ m} {b = A} .snd (∈ₛ⟪ A ⟫↪ m)) }
    bwd : (w : V ℓ) → ⟨ w ∈ A ⟩ → ⟨ w ∈ defSet ⊤̇ ⟩
    bwd w h = branch (∈-asFiber {a = w} {b = A} h)
      where
      branch : Σ[ m ∈ ⟪ A ⟫ ] (⟪ A ⟫↪ m ≡ w) → ⟨ w ∈ defSet ⊤̇ ⟩
      branch (m , e) = subst (λ z → ⟨ z ∈ defSet ⊤̇ ⟩) e
        ∣ (m , equivFun (⊨ᵐ-small ⊤̇ (ι m ∷ []) .snd) tt*) , refl ∣₁

  A∈Def : ⟨ A ∈ Def ⟩
  A∈Def = ∣ ⊤̇ , defSet⊤ ∣₁

  -- ----------------------------------------------------------------
  -- Junk case 4: the seed cut.  values (A ∩ allTuples A 1) is the
  -- set of carrier members whose code lies in A:
  --   { v : ⟨ {pr ∅ v} ∈ A ⟩ }
  -- This is a subset of A, but it is NOT first-order definable in
  -- (A, ∈) in general (automorphism argument in the report): the naive
  -- values-cut over an unkinded closure is unsound.
  -- ----------------------------------------------------------------

  junkSeedInter : ⟨ values (A ∩ allTuples A 1) ⊆ A ⟩
  junkSeedInter v h = PT.rec (snd (v ∈ₛ A)) step
    (values-wit {X = A ∩ allTuples A 1} {v = v}
      (∈∈ₛ {a = v} {b = values (A ∩ allTuples A 1)} .snd h))
    where
    step : Σ[ γ ∈ V ℓ ] (⟨ γ ∈ A ∩ allTuples A 1 ⟩ × ⟨ pr ∅ v ∈ γ ⟩)
         → ⟨ v ∈ₛ A ⟩
    step (γ , hγ , hv) = PT.rec (snd (v ∈ₛ A)) step2
      (allTuples1-shape γ (∩-out {X = A} {Y = allTuples A 1} {x = γ} hγ .snd))
      where
      step2 : Σ[ y ∈ V ℓ ] (⟨ y ∈ A ⟩ × (γ ≡ extendGraph y ∅)) → ⟨ v ∈ₛ A ⟩
      step2 (y , hy , e) = PT.rec (snd (v ∈ₛ A)) step3
        (extendGraph-out {y = y} {γ = ∅} {z = pr ∅ v}
          (subst (λ z → ⟨ pr ∅ v ∈ z ⟩) e hv))
        where
        step3 : (pr ∅ v ≡ pr ∅ y)
              ⊎ (Σ[ a ∈ V ℓ ] Σ[ w ∈ V ℓ ]
                   (⟨ pr a w ∈ ∅ ⟩ × (pr ∅ v ≡ pr (sucV a) w)))
              → ⟨ v ∈ₛ A ⟩
        step3 (inl e1) = ∈∈ₛ {a = v} {b = A} .fst
          (subst (λ z → ⟨ z ∈ A ⟩)
            (sym (pr-inj {a = ∅} {b = v} {c = ∅} {d = y} e1 .snd)) hy)
        step3 (inr (a , w , haw , _)) = Empty.rec (notIn∅ haw)

  -- The decisive negative: there are carriers E and arity-one terms t
  -- whose seed-cut values (E ∩ ⟦t⟧) escapes the definable powerset.
  -- POSTULATED (flagged in the report): the supporting argument is
  -- model-theoretic (an automorphism of (E, ∈) that does not preserve
  -- code-membership), not expressible in this library.
  postulate
    escape-witness : Σ[ E ∈ V ℓ ] Σ[ t ∈ KT ⟪ E ⟫ 1 ]
      (¬ ⟨ values (E ∩ ⟦_⟧ᴷ E t) ∈ DefOf.Def E ⟩)

  -- ----------------------------------------------------------------
  -- The chosen cut condition (values-cut with the arity guard), and
  -- its two directions against the real library.  Clos is the closure
  -- carrier (abstract here; the internal closure is Unknown 3).
  -- ----------------------------------------------------------------

  CutMem : (Clos : V ℓ) → V ℓ → Type (ℓ-suc ℓ)
  CutMem Clos v =
    ∥ Σ[ u ∈ V ℓ ] (⟨ u ∈ Clos ⟩ × ⟨ u ⊆ allTuples A 1 ⟩ × (values u ≡ v)) ∥₁

  -- The heart of the soundness direction: the values of an arity-one
  -- satisfaction set ARE the definable subset, by the banked bridge.
  valuesSatSet : (u : V ℓ)
               → ∥ Σ[ φ ∈ Formula ⟪ A ⟫ 1 ] (u ≡ satSet A φ) ∥₁
               → ⟨ values u ∈ Def ⟩
  valuesSatSet u = PT.rec (snd (values u ∈ Def))
    λ { (φ , eq) →
        subst (λ z → ⟨ z ∈ Def ⟩)
          (sym (cong values eq ∙ sat-defSet A φ))
          (∣ φ , refl ∣₁) }

  -- Soundness: if the arity-one slice of the closure is kinded (every
  -- member is a satisfaction set), the values-cut stays inside Def A.
  -- The proof is the kinded invariant discharged through sat-defSet.
  cut-sound : (Clos : V ℓ)
            → ((u : V ℓ) → ⟨ u ∈ Clos ⟩ → ⟨ u ⊆ allTuples A 1 ⟩
               → ∥ Σ[ φ ∈ Formula ⟪ A ⟫ 1 ] (u ≡ satSet A φ) ∥₁)
            → (v : V ℓ) → CutMem Clos v → ⟨ v ∈ Def ⟩
  cut-sound Clos kinded v = PT.rec (snd (v ∈ Def))
    λ { (u , hu , hsub , eq) →
        subst (λ z → ⟨ z ∈ Def ⟩) eq
          (valuesSatSet u (kinded u hu hsub)) }

  satSet⊆ : {n : ℕ} (φ : Formula ⟪ A ⟫ n) → ⟨ satSet A φ ⊆ allTuples A n ⟩
  satSet⊆ {n} φ = λ x hx →
    ∈∈ₛ {a = x} {b = allTuples A n} .fst
      (PT.map (λ { (g , _ , e) → g , e })
        (sat-out A φ x (∈∈ₛ {a = x} {b = satSet A φ} .snd hx)))

  -- ----------------------------------------------------------------
  -- Completeness: with LEM, every definable subset is the values-cut
  -- of an arity-one term (banked termDef≡Def), so if the terms reach
  -- the closure (the terms-to-levels lemma, abstract here), the cut
  -- covers Def A.
  -- ----------------------------------------------------------------

  module LEMSection (lem : LEM (ℓ-suc ℓ)) where
    module TW = WithLEM A lem

    cut-complete : (Clos : V ℓ)
                 → ((t : KT ⟪ A ⟫ 1) → ⟨ ⟦_⟧ᴷ A t ∈ Clos ⟩)
                 → (v : V ℓ) → ⟨ v ∈ Def ⟩ → CutMem Clos v
    cut-complete Clos termsIn v h =
      PT.map build (subst (λ z → ⟨ v ∈ z ⟩) (sym TW.termDef≡Def) h)
      where
      ⟦t⟧⊆1 : (t : KT ⟪ A ⟫ 1) → ⟨ ⟦_⟧ᴷ A t ⊆ allTuples A 1 ⟩
      ⟦t⟧⊆1 t = subst (λ z → ⟨ z ⊆ allTuples A 1 ⟩) (sym (sound A t))
        (satSet⊆ (toFormula A t))

      build : Σ[ t ∈ KT ⟪ A ⟫ 1 ] (values (⟦_⟧ᴷ A t) ≡ v)
            → Σ[ u ∈ V ℓ ] (⟨ u ∈ Clos ⟩ × ⟨ u ⊆ allTuples A 1 ⟩ × (values u ≡ v))
      build (t , eq) = ⟦_⟧ᴷ A t , (termsIn t , ⟦t⟧⊆1 t , eq)

  -- ----------------------------------------------------------------
  -- The four junk cases, tabulated (statement : verdict).
  -- ----------------------------------------------------------------

  -- 1. mixed-arity intersection   : values (⟦allK₁⟧ ∩ ⟦allK₂⟧) = ∅ ∈ Def A
  -- 2. same-arity intersection    : values (⟦allK₁⟧ ∩ ⟦allK₁⟧) = defSet (⊤ ∧ ⊤) ∈ Def A
  -- 3. mismatched complement      : values (allTuples 2 ∖ allTuples 1) = A ∈ Def A
  -- 4. seed cut                   : values (A ∩ allTuples 1) ⊆ A, but escapes Def A
  --                                  in general (postulate escape-witness)
