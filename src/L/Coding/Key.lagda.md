# The split key, and its stage

```agda
{-# OPTIONS --cubical --safe --guardedness #-}

open import Base.Prelude
open import Base.Truth
open import Base.Classical using ( LEM )

module L.Coding.Key {ℓ : Level} (lem : LEM (ℓ-suc ℓ)) where

open import FOL.ZFStructure using ( module hPropStructure )
open import FOL.Syntax using ( Formula; var; con; _≐_; _∧̇_; _⇒̇_; ∀̇∈; ∃̇∈ )
open import FOL.LevyHierarchy using ( Δ₀; δ-≐; δ-∧; δ-⇒; δ-∀∈; δ-∃∈ )
open import FOL.Manipulation.Bounding using ( BoundedFo )
open import FOL.Manipulation.Relabelling using ( embed )
open import FOL.Manipulation.Parameters using ( constantsFo; absFo )
import FOL.Absoluteness
open import V.Hierarchy {ℓ} using ( 𝒮ᵥ; extensionalV )
open import V.Coding {ℓ} using ( pr; pr-inj; module VCode )
open import V.Model {ℓ} using ( ∈sucV-inl; self∈sucV )
open import L.Constructible {ℓ}
  using ( 𝒮ʟ; isL; isL-trans; IsOrd; Lset; 𝒟ₒ; Lset-mono; Lset→isL
        ; Lset-layer; layer-trans )
open import L.Absoluteness {ℓ} using ( Δ₀-liftFo )
open import L.Axioms.Basic {ℓ}
  using ( Lset-suc; pr∈Lset-suc; finSet; module FinOf )
open import L.Axioms.Numerals {ℓ} using ( numeralL; numeralL-fst )
open import L.Axioms.Separation {ℓ} lem using ( module AtStage )
open import L.Coding.Base {ℓ} using ( Δ₀-prAt )
open import L.Coding.Environment {ℓ} using ( env )
open import L.Coding.Model {ℓ}
  using ( appAt; prAtL; appAt-adequate; prAtL-adequate
        ; svAt; svAt-in; svAt-out; domAt; domAt-in; domAt-intro
        ; valuesInAt; valuesInAt-in; valuesInAt-out
        ; pairsInAt; pairsIn-in; pairsIn-out
        ; envOverAt; envOver-sv; envOver-dom; envOver-values; envOver-pairs
        ; envOverAt-transport )
open import L.Coding.EnvSet {ℓ} lem
  using ( Ix; envS; envSet; envSet-in; envSet-out; envSet-mem; module Recover )
open import L.Choice.Name {ℓ} lem using ( numeral∈limit; code∈limit )
open import L.Ordinal.StageArith {ℓ} lem using ( sucIter; sucIter-ord )

open import Cubical.Data.Nat using ( _+_ )
open import Cubical.Data.FinData using ( toℕ; zero; suc )
open import Cubical.Data.Vec using ( lookup )
open import Cubical.Data.Sigma using ( _×_ )
open import Cubical.Functions.Logic using ( ⇔toPath )
import Cubical.HITs.PropositionalTruncation as PT
open PT using ( ∣_∣₁; squash₁ )
open import Cubical.HITs.CumulativeHierarchy.Base using ( V; _∈_ )
open import Cubical.HITs.CumulativeHierarchy.Properties
  using ( ⟪_⟫; ⟪_⟫↪; ∈∈ₛ; ∈ₛ⟪_⟫↪_; ∈-asFiber )
open import Cubical.HITs.CumulativeHierarchy.Constructions
  using ( module InfinitySet )
open InfinitySet using ( #_; ω; sucV )

open TruthAlgebra (hPropAlgebra (ℓ-suc ℓ))
open hPropStructure 𝒮ᵥ

-- The environment-set block below lives in the OTHER structure, so it
-- is qualified rather than opened ([LJ-1.173], the pattern
-- src/L/BoundedSubset.lagda.md:56-58 uses).
module CS = hPropStructure 𝒮ʟ
module AbsL = FOL.Absoluteness.Single 𝒮ᵥ isL isL-trans
open AbsL using ( _^_ ) renaming ( _⊨ᵐ_ to _⊨_ )

-- A stage function and the five facts the key's bound uses.  Nothing here
-- names a tower.  The key is the arity, the code of the parameter-free
-- formula, and the parameter environment, and the bound mentions neither the
-- formula's depth nor the number of parameters.
module KeyOver
  (T : S → S)
  (T-mono : {α β : S} → ⟨ β ∈ˢ α ⟩ → {x : S} → ⟨ x ∈ˢ T β ⟩ → ⟨ x ∈ˢ T α ⟩)
  (T-pr : (σ x y : S) → ⟨ x ∈ˢ T σ ⟩ → ⟨ y ∈ˢ T σ ⟩
        → ⟨ pr x y ∈ˢ T (sucV (sucV σ)) ⟩)
  (T-fin : (σ : S) → IsOrd σ → (k : ℕ) (h : Fin k → S)
         → ((i : Fin k) → ⟨ h i ∈ˢ T σ ⟩) → ⟨ finSet k h ∈ˢ T (sucV σ) ⟩)
  (T-num : (k : ℕ) → ⟨ (# k) ∈ˢ T ω ⟩)
  (T-code : ∀ {m} (χ : Formula (⊥* {ℓ}) m) → ⟨ VCode.⌜ embed χ ⌝ ∈ˢ T ω ⟩)
  where

  -- A member of the ω-stage sits in every finite iterate above σ once ω ∈ σ.
  fromω : (σ : S) → ⟨ ω ∈ˢ σ ⟩ → (d : ℕ) (x : S)
        → ⟨ x ∈ˢ T ω ⟩ → ⟨ x ∈ˢ T (sucIter (suc d) σ) ⟩
  fromω σ ω∈ zero    x h = T-mono {α = sucV σ} {β = ω} (∈sucV-inl ω∈) {x = x} h
  fromω σ ω∈ (suc d) x h =
    T-mono {α = sucIter (suc (suc d)) σ} {β = ω}
      (∈sucV-inl (fromω′ d)) {x = x} h
    where
    fromω′ : (e : ℕ) → ⟨ ω ∈ˢ sucIter (suc e) σ ⟩
    fromω′ zero    = ∈sucV-inl ω∈
    fromω′ (suc e) = ∈sucV-inl (fromω′ e)

  -- The parameter component is a SEQUENCE and never a finite set.  A finite
  -- set keeps no index, and the reading substitutes BY POSITION.
  paramEnv : {k : ℕ} → (Fin k → S) → S
  paramEnv h = env h

  -- Three stages, whatever k is: the index pairs cost two, the span one.
  paramEnv∈ : (σ : S) → IsOrd σ → ⟨ ω ∈ˢ σ ⟩ → (k : ℕ) (h : Fin k → S)
            → ((i : Fin k) → ⟨ h i ∈ˢ T σ ⟩)
            → ⟨ paramEnv h ∈ˢ T (sucIter 3 σ) ⟩
  paramEnv∈ σ oσ ω∈ k h hm =
    T-fin (sucIter 2 σ) (sucIter-ord 2 oσ) k
      (λ i → pr (# (toℕ i)) (h i)) pair∈
    where
    pair∈ : (i : Fin k) → ⟨ pr (# (toℕ i)) (h i) ∈ˢ T (sucIter 2 σ) ⟩
    pair∈ i = T-pr σ (# (toℕ i)) (h i)
      (T-mono {α = σ} {β = ω} ω∈ {x = # (toℕ i)} (T-num (toℕ i))) (hm i)

  -- THE KEY, and the bound is a FIXED iterate, uniform in χ and in k.
  splitKey : (n : ℕ) {k : ℕ} (χ : Formula (⊥* {ℓ}) (n + k)) (h : Fin k → S) → S
  splitKey n χ h = pr (# n) (pr VCode.⌜ embed χ ⌝ (paramEnv h))

  splitKey∈ : (σ : S) → IsOrd σ → ⟨ ω ∈ˢ σ ⟩ → (n : ℕ) {k : ℕ}
              (χ : Formula (⊥* {ℓ}) (n + k)) (h : Fin k → S)
            → ((i : Fin k) → ⟨ h i ∈ˢ T σ ⟩)
            → ⟨ splitKey n χ h ∈ˢ T (sucIter 7 σ) ⟩
  splitKey∈ σ oσ ω∈ n {k} χ h hm =
    T-pr (sucIter 5 σ) (# n) (pr VCode.⌜ embed χ ⌝ (paramEnv h))
      (fromω σ ω∈ 4 (# n) (T-num n))
      (T-pr (sucIter 3 σ) VCode.⌜ embed χ ⌝ (paramEnv h)
        (fromω σ ω∈ 2 VCode.⌜ embed χ ⌝ (T-code χ))
        (paramEnv∈ σ oσ ω∈ k h hm))

-- The L tower supplies the five facts.  One needs an adapter: the delivered
-- finite-family law is stated over fibers, and the generic law over members.
Lset-fin : (σ : S) → IsOrd σ → (k : ℕ) (h : Fin k → S)
         → ((i : Fin k) → ⟨ h i ∈ˢ Lset σ ⟩) → ⟨ finSet k h ∈ˢ Lset (sucV σ) ⟩
Lset-fin σ oσ k h hm =
  subst (λ w → ⟨ finSet k h ∈ˢ w ⟩) (sym (Lset-suc σ))
    (subst (λ w → ⟨ w ∈ˢ 𝒟ₒ (Lset σ) ⟩)
      (cong (finSet k) (funExt (λ i → fib i .snd)))
      (FinOf.finSet∈𝒟ₒ σ oσ k (λ i → fib i .fst)))
  where
  fib : (i : Fin k) → Σ[ m ∈ ⟪ Lset σ ⟫ ] (⟪ Lset σ ⟫↪ m ≡ h i)
  fib i = ∈-asFiber {a = h i} {b = Lset σ} (hm i)

open KeyOver Lset Lset-mono pr∈Lset-suc Lset-fin numeral∈limit code∈limit public

-- The delivered parameter split feeds the key unchanged, so the bound holds
-- for EVERY formula over the carrier.  `⌜_⌝` is not touched.
deliveredSplit : (σ : S) (φ : Formula ⟪ Lset σ ⟫ 1) → S
deliveredSplit σ φ = splitKey 1 (absFo {ℓz = ℓ} {n = 1} φ)
  (λ i → ⟪ Lset σ ⟫↪ (lookup i (constantsFo φ)))

deliveredSplit∈ : (σ : S) → IsOrd σ → ⟨ ω ∈ˢ σ ⟩ → (φ : Formula ⟪ Lset σ ⟫ 1)
                → ⟨ deliveredSplit σ φ ∈ˢ Lset (sucIter 7 σ) ⟩
deliveredSplit∈ σ oσ ω∈ φ = splitKey∈ σ oσ ω∈ 1 (absFo {ℓz = ℓ} {n = 1} φ)
  (λ i → ⟪ Lset σ ⟫↪ (lookup i (constantsFo φ)))
  (λ i → ∈∈ₛ {a = ⟪ Lset σ ⟫↪ (lookup i (constantsFo φ))} {b = Lset σ} .snd
           (∈ₛ⟪ Lset σ ⟫↪ (lookup i (constantsFo φ))))

open AbsL using ( _^_ ) renaming ( _⊨ᵐ_ to _⊨_ )

-- =====================================================================
-- THE NUMERAL-ARITY ENVIRONMENT SET, AND ITS STAGE.
--
-- [LJ-1.172] refuted the general-arity form: at an unrestricted arity
-- the environment set is the FULL constructible function space, and a
-- successor-closed limit does not hold it.  The NUMERAL case is true,
-- and it is the form Devlin's `K(u)` has, since every sequence there is
-- finite.  [LJ-1.173] gates and closes it here.
--
-- The argument has two halves and a JOIN, and the join is the content:
-- the first half is a CONTAINMENT, the second is a MEMBERSHIP OF A
-- DIFFERENT SET, and `carvedEq` is what makes them speak about one set.
--
-- The two Δ₀ facts below are the two `L.Condensation` derives at :88-89
-- and :94-95.  They are re-derived here, four lines, because this
-- master sits BELOW that one (src/Everything.lagda.md:351 against :373).
-- A later pass may point the consumer at this copy.
Δ₀-prAtLK : ∀ {m} (q u v : Fin m) → Δ₀ (prAtL q u v)
Δ₀-prAtLK q u v = Δ₀-liftFo _ (Δ₀-prAt q u v)

Δ₀-appAtK : ∀ {m} (f x y : Fin m) → Δ₀ (appAt f x y)
Δ₀-appAtK f x y = δ-∃∈ (Δ₀-prAtLK zero (suc x) (suc y))

-- HALF ONE, the containment.
-- =====================================================================

-- One environment over `B` of numeral length `n` lands three stages
-- above the stage that holds `B`, and the three is the same for every
-- `n`.  `paramEnv h = env h`, so the conclusion is already the shape
-- `envS` has.
memberIn : (σ : V ℓ) → IsOrd σ → ⟨ ω ∈ σ ⟩ → (B : CS.S) (n : ℕ)
         → ⟨ fst B ∈ Lset σ ⟩ → (g : Ix B n)
         → ⟨ fst (envS B g) ∈ Lset (sucIter 3 σ) ⟩
memberIn σ oσ ω∈ B n hB g =
  paramEnv∈ σ oσ ω∈ n (λ i → ⟪ fst B ⟫↪ (g i)) mem
  where
  mem : (i : Fin n) → ⟨ ⟪ fst B ⟫↪ (g i) ∈ Lset σ ⟩
  mem i = layer-trans (Lset-layer σ) {x = fst B} {y = ⟪ fst B ⟫↪ (g i)}
    (∈∈ₛ {a = ⟪ fst B ⟫↪ (g i)} {b = fst B} .snd (∈ₛ⟪ fst B ⟫↪ (g i))) hB

-- The whole set is therefore INSIDE the fixed iterate.  This is a
-- containment and it is NOT a membership.
setSub : (σ : V ℓ) → IsOrd σ → ⟨ ω ∈ σ ⟩ → (B : CS.S) (n : ℕ)
       → ⟨ fst B ∈ Lset σ ⟩ → (x : CS.S) → ⟨ fst x ∈ fst (envSet B n) ⟩
       → ⟨ fst x ∈ Lset (sucIter 3 σ) ⟩
setSub σ oσ ω∈ B n hB x hx =
  PT.rec (snd (fst x ∈ Lset (sucIter 3 σ)))
    (λ { (g , q) → subst (λ w → ⟨ w ∈ Lset (sucIter 3 σ) ⟩) (sym q)
                     (memberIn σ oσ ω∈ B n hB g) })
    (envSet-out B n x hx)

-- =====================================================================
-- HALF TWO, the membership.  A subset of a level is a MEMBER of the
-- next level only when it is DEFINABLE there, and the stage-controlled
-- carve takes a Δ₀ formula.  The delivered description is not Δ₀
-- (`svAt` and `domAt` use `∀̇`, `inDomAt` uses `∃̇`), so this is the
-- bounded one.
-- =====================================================================

-- A bounded description of "e is a function with domain `d` and values
-- in `B`".  Every quantifier is bounded, by `con d`, by `con B` or by
-- `e` itself, so the formula is Δ₀ and the carve at a stage is
-- available.  The delivered `envFo` is the same content with UNBOUNDED
-- quantifiers (`svAt` and `domAt` use `∀̇`, `inDomAt` uses `∃̇`), and
-- that is why it cannot be carved at a controlled stage.
-- The description names NO tower.  It is a `Formula CS.S 1` and a `Δ₀`
-- witness, and both towers read it (DD4).
module Desc (B d : CS.S) where

  -- single-valued, total on `d`, and every member a pair from `d × B`
  C1 C2 C3 : Formula CS.S 1
  C1 = ∀̇∈ (con d) (∀̇∈ (con B) (∀̇∈ (con B)
         ( appAt (suc (suc (suc zero))) (suc (suc zero)) (suc zero)
         ⇒̇ ( appAt (suc (suc (suc zero))) (suc (suc zero)) zero
         ⇒̇ (var (suc zero) ≐ var zero) ))))
  C2 = ∀̇∈ (con d) (∃̇∈ (con B) (appAt (suc (suc zero)) (suc zero) zero))
  C3 = ∀̇∈ (var zero) (∃̇∈ (con d) (∃̇∈ (con B)
         (prAtL (suc (suc zero)) (suc zero) zero)))

  envFoB : Formula CS.S 1
  envFoB = C1 ∧̇ (C2 ∧̇ C3)

  Δ₀-envFoB : Δ₀ envFoB
  Δ₀-envFoB =
    δ-∧ (δ-∀∈ (δ-∀∈ (δ-∀∈
          (δ-⇒ (Δ₀-appAtK (suc (suc (suc zero))) (suc (suc zero)) (suc zero))
               (δ-⇒ (Δ₀-appAtK (suc (suc (suc zero))) (suc (suc zero)) zero)
                    δ-≐)))))
        (δ-∧ (δ-∀∈ (δ-∃∈ (Δ₀-appAtK (suc (suc zero)) (suc zero) zero)))
             (δ-∀∈ (δ-∃∈ (δ-∃∈ (Δ₀-prAtLK (suc (suc zero)) (suc zero) zero)))))

module Carve (α : V ℓ) (oα : IsOrd α) (B d : CS.S)
             (hB : ⟨ fst B ∈ Lset α ⟩) (hd : ⟨ fst d ∈ Lset α ⟩) where

  open Desc B d public

  bddEnvFoB : BoundedFo (AtStage.Below α oα) envFoB
  bddEnvFoB = ((hd , (hB , (hB , ((_ , _) , ((_ , _) , _)))))
              , ((hd , (hB , (_ , _))) , (_ , (hd , (hB , _)))))

  module AS = AtStage α oα

  ψ : Formula ⟪ Lset α ⟫ 1
  ψ = AS.RL.liftFo envFoB bddEnvFoB

  carved : V ℓ
  carved = AS.carve ψ

  carved∈ : ⟨ carved ∈ Lset (sucV α) ⟩
  carved∈ = subst (λ w → ⟨ carved ∈ w ⟩) (sym (Lset-suc α)) (AS.carve∈𝒟ₒ ψ)

-- =====================================================================
-- THE ADEQUACY: the bounded description defines `envSet B n`.
--
-- Both directions pass through the DELIVERED unbounded description at
-- ONE environment, `δ x = x ∷ d ∷ B ∷ []`.  Nothing here rewrites
-- `Recover` or `envSet-mem`; both are reused.
-- =====================================================================

module Join (B d : CS.S) (n : ℕ) (qdn : fst d ≡ # n) where

  open Desc B d

  δ : CS.S → CS.S ^ 3
  δ x = x ∷ d ∷ B ∷ []

  E D Bi : Fin 3
  E = zero
  D = suc zero
  Bi = suc (suc zero)

  -- THE ONE FACT THAT RELEASES THE UNBOUNDED QUANTIFIERS.  A recorded
  -- pair has its index in `d` and its value in `B`, so the three
  -- quantifiers the delivered description leaves unbounded range over
  -- nothing the bounded one misses.
  slots : (x : CS.S) → ⟨ (x ∷ []) ⊨ envFoB ⟩ → (i b : CS.S)
        → ⟨ pr (fst i) (fst b) ∈ fst x ⟩
        → ⟨ (fst i ∈ fst d) ⊓ (fst b ∈ fst B) ⟩
  slots x h i b m =
    PT.rec (snd ((fst i ∈ fst d) ⊓ (fst b ∈ fst B)))
      (λ { (u , (u∈ , hv)) → PT.rec (snd ((fst i ∈ fst d) ⊓ (fst b ∈ fst B)))
        (λ { (v , (v∈ , hp)) → pin u v u∈ v∈
               (subst ⟨_⟩ (prAtL-adequate (suc (suc zero)) (suc zero) zero
                             (v ∷ u ∷ pS ∷ x ∷ [])) hp) }) hv })
      (h .snd .snd pS m)
    where
    pS : CS.S
    pS = pr (fst i) (fst b)
       , isL-trans {x = fst x} {y = pr (fst i) (fst b)} m (snd x)

    pin : (u v : CS.S) → ⟨ fst u ∈ fst d ⟩ → ⟨ fst v ∈ fst B ⟩
        → pr (fst i) (fst b) ≡ pr (fst u) (fst v)
        → ⟨ (fst i ∈ fst d) ⊓ (fst b ∈ fst B) ⟩
    pin u v u∈ v∈ e =
        subst (λ w → ⟨ w ∈ fst d ⟩) (sym (pr-inj e .fst)) u∈
      , subst (λ w → ⟨ w ∈ fst B ⟩) (sym (pr-inj e .snd)) v∈

  -- BOUNDED to UNBOUNDED.
  unbound : (x : CS.S) → ⟨ (x ∷ []) ⊨ envFoB ⟩ → ⟨ δ x ⊨ envOverAt E D Bi ⟩
  unbound x h = sv , (dom , (vals , prs))
    where
    sl = slots x h

    ap : (i b b' : CS.S) → ⟨ pr (fst i) (fst b) ∈ fst x ⟩
       → ⟨ (b' ∷ b ∷ i ∷ x ∷ [])
           ⊨ appAt (suc (suc (suc zero))) (suc (suc zero)) (suc zero) ⟩
    ap i b b' p = subst ⟨_⟩ (sym (appAt-adequate (suc (suc (suc zero)))
      (suc (suc zero)) (suc zero) (b' ∷ b ∷ i ∷ x ∷ []))) p

    ap' : (i b b' : CS.S) → ⟨ pr (fst i) (fst b') ∈ fst x ⟩
        → ⟨ (b' ∷ b ∷ i ∷ x ∷ [])
            ⊨ appAt (suc (suc (suc zero))) (suc (suc zero)) zero ⟩
    ap' i b b' q = subst ⟨_⟩ (sym (appAt-adequate (suc (suc (suc zero)))
      (suc (suc zero)) zero (b' ∷ b ∷ i ∷ x ∷ []))) q

    sv : ⟨ δ x ⊨ svAt E ⟩
    sv = svAt-in E (δ x) (λ i b b' p q →
      h .fst i (sl i b p .fst) b (sl i b p .snd) b' (sl i b' q .snd)
        (ap i b b' p) (ap' i b b' q))

    dom : ⟨ δ x ⊨ domAt E D ⟩
    dom = domAt-intro E D (δ x) (λ i →
        (λ hex → PT.rec (snd (fst i ∈ fst d))
                   (λ { (y , p) → sl i y p .fst }) hex)
      , (λ i∈ → PT.map (λ { (b , (b∈ , hp)) → b
                   , subst ⟨_⟩ (appAt-adequate (suc (suc zero)) (suc zero) zero
                                  (b ∷ i ∷ x ∷ [])) hp })
                  (h .snd .fst i i∈)))

    vals : ⟨ δ x ⊨ valuesInAt E Bi ⟩
    vals = valuesInAt-in E Bi (δ x) (λ i b p → sl i b p .snd)

    prs : ⟨ δ x ⊨ pairsInAt E D Bi ⟩
    prs = pairsIn-in E D Bi (δ x) (λ s s∈ →
      PT.rec squash₁ (λ { (u , (u∈ , hv)) → PT.map
        (λ { (v , (v∈ , hp)) → u , (v , (u∈ , (v∈
             , subst ⟨_⟩ (prAtL-adequate (suc (suc zero)) (suc zero) zero
                            (v ∷ u ∷ s ∷ x ∷ [])) hp))) }) hv })
        (h .snd .snd s s∈))

  -- UNBOUNDED to BOUNDED.  Restriction, and it costs the four readers.
  rebound : (x : CS.S) → ⟨ δ x ⊨ envOverAt E D Bi ⟩ → ⟨ (x ∷ []) ⊨ envFoB ⟩
  rebound x h = sv , (dom , prs)
    where
    sv : ⟨ (x ∷ []) ⊨ C1 ⟩
    sv i i∈ b b∈ b' b'∈ p q =
      svAt-out E (δ x) (envOver-sv E D Bi (δ x) h) i b b'
        (subst ⟨_⟩ (appAt-adequate (suc (suc (suc zero))) (suc (suc zero))
                      (suc zero) (b' ∷ b ∷ i ∷ x ∷ [])) p)
        (subst ⟨_⟩ (appAt-adequate (suc (suc (suc zero))) (suc (suc zero))
                      zero (b' ∷ b ∷ i ∷ x ∷ [])) q)

    dom : ⟨ (x ∷ []) ⊨ C2 ⟩
    dom i i∈ = PT.map
      (λ { (y , p) → y
         , (valuesInAt-out E Bi (δ x) (envOver-values E D Bi (δ x) h) i y p
           , subst ⟨_⟩ (sym (appAt-adequate (suc (suc zero)) (suc zero) zero
                               (y ∷ i ∷ x ∷ []))) p) })
      (domAt-in E D (δ x) (envOver-dom E D Bi (δ x) h) i i∈)

    prs : ⟨ (x ∷ []) ⊨ C3 ⟩
    prs s s∈ = PT.map
      (λ { (u , (v , (u∈ , (v∈ , eq)))) → u , (u∈ , ∣ v , (v∈
           , subst ⟨_⟩ (sym (prAtL-adequate (suc (suc zero)) (suc zero) zero
                               (v ∷ u ∷ s ∷ x ∷ []))) eq) ∣₁) })
      (pairsIn-out E D Bi (δ x) (envOver-pairs E D Bi (δ x) h) s s∈)

  -- THE DELIVERED SET, both ways, and neither way is rewritten here.
  intoSet : (x : CS.S) → ⟨ δ x ⊨ envOverAt E D Bi ⟩ → ⟨ fst x ∈ fst (envSet B n) ⟩
  intoSet x h = subst (λ w → ⟨ w ∈ fst (envSet B n) ⟩)
    (sym (Recover.recovers B n (δ x) E D Bi qdn refl h))
    (envSet-in B (Recover.g B n (δ x) E D Bi qdn refl h))

  outSet : (x : CS.S) → ⟨ fst x ∈ fst (envSet B n) ⟩ → ⟨ δ x ⊨ envOverAt E D Bi ⟩
  outSet x hx = PT.rec (snd (δ x ⊨ envOverAt E D Bi))
    (λ { (dd , hdd) → PT.rec (snd (δ x ⊨ envOverAt E D Bi))
      (λ { (bb , (qd , (qb , hov))) →
        envOverAt-transport (bb ∷ dd ∷ x ∷ []) (δ x)
          (suc (suc zero)) (suc zero) zero E D Bi
          refl (qd ∙ sym qdn) qb hov }) hdd })
    (subst ⟨_⟩ (envSet-mem B n x) hx .snd)

  -- THE JOIN ITSELF, stated at the join and not at the two ends.
  adequate : (x : CS.S) → (⟨ (x ∷ []) ⊨ envFoB ⟩ → ⟨ fst x ∈ fst (envSet B n) ⟩)
           × (⟨ fst x ∈ fst (envSet B n) ⟩ → ⟨ (x ∷ []) ⊨ envFoB ⟩)
  adequate x = (λ h → intoSet x (unbound x h))
             , (λ hx → rebound x (outSet x hx))

-- =====================================================================
-- THE IDENTIFICATION.  The carved set IS `envSet B n`, so the two
-- halves now speak about the SAME set and the bound falls out.
-- =====================================================================

module Land (σ : V ℓ) (oσ : IsOrd σ) (ω∈ : ⟨ ω ∈ σ ⟩) (B d : CS.S) (n : ℕ)
            (qdn : fst d ≡ # n) (hB : ⟨ fst B ∈ Lset σ ⟩) where

  α : V ℓ
  α = sucIter 3 σ

  private
    σ∈α : ⟨ σ ∈ α ⟩
    σ∈α = ∈sucV-inl {A = sucIter 2 σ} {x = σ}
            (∈sucV-inl {A = sucIter 1 σ} {x = σ} (self∈sucV σ))

    hBα : ⟨ fst B ∈ Lset α ⟩
    hBα = Lset-mono {α = α} {β = σ} σ∈α {x = fst B} hB

    hdα : ⟨ fst d ∈ Lset α ⟩
    hdα = subst (λ w → ⟨ w ∈ Lset α ⟩) (sym qdn)
            (fromω σ ω∈ 2 (# n) (numeral∈limit n))

  open Carve α (sucIter-ord 3 oσ) B d hBα hdα
  open Join B d n qdn

  private
    fib : (w : V ℓ) → ⟨ w ∈ Lset α ⟩ → ⟪ Lset α ⟫
    fib w h = ∈-asFiber {a = w} {b = Lset α} h .fst

    fibEq : (w : V ℓ) (h : ⟨ w ∈ Lset α ⟩) → ⟪ Lset α ⟫↪ (fib w h) ≡ w
    fibEq w h = ∈-asFiber {a = w} {b = Lset α} h .snd

    fibL : (m : ⟪ Lset α ⟫) → ⟨ isL (⟪ Lset α ⟫↪ m) ⟩
    fibL m = Lset→isL α (sucIter-ord 3 oσ) (⟪ Lset α ⟫↪ m)
      (∈∈ₛ {a = ⟪ Lset α ⟫↪ m} {b = Lset α} .snd (∈ₛ⟪ Lset α ⟫↪ m))

  -- Out of the carve and into the set.
  private
    out : (w : V ℓ) → ⟨ w ∈ carved ⟩ → ⟨ w ∈ fst (envSet B n) ⟩
    out w hw = subst (λ z → ⟨ z ∈ fst (envSet B n) ⟩) q
      (adequate (⟪ Lset α ⟫↪ m , fibL m) .fst
        (AS.imageOut envFoB bddEnvFoB Δ₀-envFoB m (fibL m)
          (subst (λ z → ⟨ z ∈ carved ⟩) (sym q) hw)))
      where
      m = fib w (AS.carve⊆ ψ w hw)
      q = fibEq w (AS.carve⊆ ψ w hw)

    into : (w : V ℓ) → ⟨ w ∈ fst (envSet B n) ⟩ → ⟨ w ∈ carved ⟩
    into w hw = subst (λ z → ⟨ z ∈ carved ⟩) q
      (AS.imageIn envFoB bddEnvFoB Δ₀-envFoB m (fibL m)
        (adequate (⟪ Lset α ⟫↪ m , fibL m) .snd
          (subst (λ z → ⟨ z ∈ fst (envSet B n) ⟩) (sym q) hw)))
      where
      wL : ⟨ isL w ⟩
      wL = isL-trans {x = fst (envSet B n)} {y = w} hw (snd (envSet B n))
      w∈ : ⟨ w ∈ Lset α ⟩
      w∈ = setSub σ oσ ω∈ B n hB (w , wL) hw
      m = fib w w∈
      q = fibEq w w∈

  -- THE JOIN, and it is one equation between the two halves' two sets.
  carvedEq : carved ≡ fst (envSet B n)
  carvedEq = extensionalV (λ w → ⇔toPath (out w) (into w))

  landed : ⟨ fst (envSet B n) ∈ Lset (sucIter 4 σ) ⟩
  landed = subst (λ z → ⟨ z ∈ Lset (sucIter 4 σ) ⟩) carvedEq carved∈

-- THE BOUND.  The iterate is 4 and it does not depend on `n`, so it is
-- uniform in `n`, exactly as `splitKey∈` above is uniform in the
-- formula and in the parameter count.
envSetNumeral∈ : (σ : V ℓ) → IsOrd σ → ⟨ ω ∈ σ ⟩ → (B : CS.S) (n : ℕ)
               → ⟨ fst B ∈ Lset σ ⟩
               → ⟨ fst (envSet B n) ∈ Lset (sucIter 4 σ) ⟩
envSetNumeral∈ σ oσ ω∈ B n hB =
  Land.landed σ oσ ω∈ B (numeralL n) n (numeralL-fst n) hB
```
