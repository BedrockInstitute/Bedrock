{-# OPTIONS --cubical --safe --guardedness #-}

-- LJ-1.173 probe A.  THE GATE on the numeral-arity restriction of
-- `envSetK` (src/L/Condensation/TwelveAgree.lagda.md:271-275).
--
-- THE ONE DECLARATION THE GATE ASKS FOR:
--
--   envSetNumeral∈ : (σ : V ℓ) → IsOrd σ → ⟨ ω ∈ σ ⟩ (B : S) (n : ℕ)
--                  → ⟨ fst B ∈ Lset σ ⟩
--                  → ⟨ fst (envSet B n) ∈ Lset (sucIter k σ) ⟩
--
-- with `k` a FIXED natural, the same for every `n`.  That is the
-- brief's "uniformly in n".
--
-- CRITERION, FIXED BEFORE THE FIRST RUN (D-1):
--   GO    at 40 or fewer non-blank, non-comment lines of Agda, module
--         header and imports excluded, with no postulate, no hole and
--         no unsolved meta.
--   NO-GO above 40, or if the declaration cannot be closed from
--         delivered material.  Report the figure and STOP.
--   20 minutes of wall time per agda invocation, GHCRTS="-A64m -I0
--   -M8g", ONE process, the cap NEVER raised.
--
-- THE ROUTE, and the two blocks are the two halves of the gate.
--   BLOCK 1  the SUBSET half.  Every member of `envSet B n` lies in a
--            FIXED iterate above the stage that holds `B`, uniformly
--            in `n`.  This is the half [LJ-1.172] measured, through
--            `paramEnv∈` (src/L/Coding/Key.lagda.md:71-81).
--   BLOCK 2  the MEMBERSHIP half.  A subset of a stage is a MEMBER of
--            the next stage only when it is DEFINABLE there.  The
--            tree's only stage-controlled carve, `AtStage.carve`
--            (src/L/Axioms/Separation.lagda.md:193-199), takes a Δ₀
--            formula.  The delivered description `envFo`
--            (src/L/Coding/EnvSet.lagda.md:176-180) is NOT Δ₀, so the
--            block must write a bounded one.  BLOCK 2 writes the
--            MANDATORY SYNTAX LAYER of that carve and nothing else:
--            the formula, its Δ₀ witness, its constant certificate,
--            and the `∈ 𝒟ₒ` step.  The adequacy is not written here;
--            the report prices it.
--
-- P-i [F] is obeyed: every lemma with an implicit set index applied at
-- a concrete argument gets the index EXPLICITLY.

open import Base.Prelude
open import Base.Truth
open import Base.Classical using ( LEM )

module LJ-1-173.ProbeLJ1173A {ℓ : Level} (lem : LEM (ℓ-suc ℓ)) where

open import FOL.ZFStructure using ( module hPropStructure )
open import FOL.Syntax using ( Formula; var; con; _≐_; _∧̇_; _⇒̇_; ∀̇∈; ∃̇∈ )
open import FOL.LevyHierarchy using ( Δ₀; δ-≐; δ-∧; δ-⇒; δ-∀∈; δ-∃∈ )
open import FOL.Manipulation.Bounding using ( BoundedFo )
import FOL.Absoluteness
open import V.Hierarchy {ℓ} using ( 𝒮ᵥ; extensionalV )
open import V.Coding {ℓ} using ( pr; pr-inj )
open import L.Constructible {ℓ}
  using ( 𝒮ʟ; isL; isL-trans; IsOrd; Lset; Lset-layer; layer-trans; Lset-mono; Lset→isL )
open import L.Axioms.Basic {ℓ} using ( Lset-suc )
open import L.Axioms.Numerals {ℓ} using ( numeralL; numeralL-fst )
open import V.Model {ℓ} using ( ∈sucV-inl; self∈sucV )
open import L.Axioms.Separation {ℓ} lem using ( module AtStage )
open import L.Coding.Model {ℓ}
  using ( appAt; prAtL; appAt-adequate; prAtL-adequate
        ; svAt; svAt-in; svAt-out; domAt; domAt-in; domAt-intro
        ; valuesInAt; valuesInAt-in; valuesInAt-out
        ; pairsInAt; pairsIn-in; pairsIn-out
        ; envOverAt; envOver-sv; envOver-dom; envOver-values; envOver-pairs
        ; envOverAt-transport )
open import L.Condensation {ℓ} lem using ( Δ₀-appAt; Δ₀-prAtL )
open import L.Coding.Key {ℓ} lem using ( paramEnv∈; fromω )
open import L.Choice.Name {ℓ} lem using ( numeral∈limit )
open import L.Coding.EnvSet {ℓ} lem
  using ( Ix; envS; envSet; envSet-in; envSet-out; envSet-mem; module Recover )
open import L.Ordinal.StageArith {ℓ} lem using ( sucIter; sucIter-ord )

open import Cubical.Data.FinData using ( Fin; zero; suc )
open import Cubical.Data.Sigma using ( _×_; Σ≡Prop )
open import Cubical.Functions.Logic using ( ⇔toPath )
import Cubical.HITs.PropositionalTruncation as PT
open PT using ( ∣_∣₁; ∥_∥₁; squash₁ )
open import Cubical.HITs.CumulativeHierarchy.Base using ( V; _∈_ )
open import Cubical.HITs.CumulativeHierarchy.Properties
  using ( ⟪_⟫; ⟪_⟫↪; ∈∈ₛ; ∈ₛ⟪_⟫↪_; ∈-asFiber )
open import Cubical.HITs.CumulativeHierarchy.Constructions
  using ( module InfinitySet )
open InfinitySet using ( ω; sucV; #_ )

open TruthAlgebra (hPropAlgebra (ℓ-suc ℓ))
open hPropStructure 𝒮ʟ

module AbsL = FOL.Absoluteness.Single 𝒮ᵥ isL isL-trans
open AbsL using ( _^_ ) renaming ( _⊨ᵐ_ to _⊨_ )

-- =====================================================================
-- BLOCK 1.  THE SUBSET HALF.
-- =====================================================================

-- One environment over `B` of numeral length `n` lands three stages
-- above the stage that holds `B`, and the three is the same for every
-- `n`.  `paramEnv h = env h`, so the conclusion is already the shape
-- `envS` has.
memberIn : (σ : V ℓ) → IsOrd σ → ⟨ ω ∈ σ ⟩ → (B : S) (n : ℕ)
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
setSub : (σ : V ℓ) → IsOrd σ → ⟨ ω ∈ σ ⟩ → (B : S) (n : ℕ)
       → ⟨ fst B ∈ Lset σ ⟩ → (x : S) → ⟨ x ∈ˢ envSet B n ⟩
       → ⟨ fst x ∈ Lset (sucIter 3 σ) ⟩
setSub σ oσ ω∈ B n hB x hx =
  PT.rec (snd (fst x ∈ Lset (sucIter 3 σ)))
    (λ { (g , q) → subst (λ w → ⟨ w ∈ Lset (sucIter 3 σ) ⟩) (sym q)
                     (memberIn σ oσ ω∈ B n hB g) })
    (envSet-out B n x hx)

-- =====================================================================
-- BLOCK 2.  THE MEMBERSHIP HALF: the mandatory syntax layer.
-- =====================================================================

-- A bounded description of "e is a function with domain `d` and values
-- in `B`".  Every quantifier is bounded, by `con d`, by `con B` or by
-- `e` itself, so the formula is Δ₀ and the carve at a stage is
-- available.  The delivered `envFo` is the same content with UNBOUNDED
-- quantifiers (`svAt` and `domAt` use `∀̇`, `inDomAt` uses `∃̇`), and
-- that is why it cannot be carved at a controlled stage.
-- The description names NO tower.  It is a `Formula S 1` and a `Δ₀`
-- witness, and both towers read it (DD4).
module Desc (B d : S) where

  -- single-valued, total on `d`, and every member a pair from `d × B`
  C1 C2 C3 : Formula S 1
  C1 = ∀̇∈ (con d) (∀̇∈ (con B) (∀̇∈ (con B)
         ( appAt (suc (suc (suc zero))) (suc (suc zero)) (suc zero)
         ⇒̇ ( appAt (suc (suc (suc zero))) (suc (suc zero)) zero
         ⇒̇ (var (suc zero) ≐ var zero) ))))
  C2 = ∀̇∈ (con d) (∃̇∈ (con B) (appAt (suc (suc zero)) (suc zero) zero))
  C3 = ∀̇∈ (var zero) (∃̇∈ (con d) (∃̇∈ (con B)
         (prAtL (suc (suc zero)) (suc zero) zero)))

  envFoB : Formula S 1
  envFoB = C1 ∧̇ (C2 ∧̇ C3)

  Δ₀-envFoB : Δ₀ envFoB
  Δ₀-envFoB =
    δ-∧ (δ-∀∈ (δ-∀∈ (δ-∀∈
          (δ-⇒ (Δ₀-appAt (suc (suc (suc zero))) (suc (suc zero)) (suc zero))
               (δ-⇒ (Δ₀-appAt (suc (suc (suc zero))) (suc (suc zero)) zero)
                    δ-≐)))))
        (δ-∧ (δ-∀∈ (δ-∃∈ (Δ₀-appAt (suc (suc zero)) (suc zero) zero)))
             (δ-∀∈ (δ-∃∈ (δ-∃∈ (Δ₀-prAtL (suc (suc zero)) (suc zero) zero)))))

module Carve (α : V ℓ) (oα : IsOrd α) (B d : S)
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
-- BLOCK 3.  THE ADEQUACY, and it is the JOIN the gate was spent before.
--
-- Both directions pass through the DELIVERED unbounded description at
-- ONE environment, `δ x = x ∷ d ∷ B ∷ []`.  Nothing here rewrites
-- `Recover` or `envSet-mem`; both are reused.
-- =====================================================================

module Join (B d : S) (n : ℕ) (qdn : fst d ≡ # n) where

  open Desc B d

  δ : S → S ^ 3
  δ x = x ∷ d ∷ B ∷ []

  E D Bi : Fin 3
  E = zero
  D = suc zero
  Bi = suc (suc zero)

  -- THE ONE FACT THAT RELEASES THE UNBOUNDED QUANTIFIERS.  A recorded
  -- pair has its index in `d` and its value in `B`, so the three
  -- quantifiers the delivered description leaves unbounded range over
  -- nothing the bounded one misses.
  slots : (x : S) → ⟨ (x ∷ []) ⊨ envFoB ⟩ → (i b : S)
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
    pS : S
    pS = pr (fst i) (fst b)
       , isL-trans {x = fst x} {y = pr (fst i) (fst b)} m (snd x)

    pin : (u v : S) → ⟨ fst u ∈ fst d ⟩ → ⟨ fst v ∈ fst B ⟩
        → pr (fst i) (fst b) ≡ pr (fst u) (fst v)
        → ⟨ (fst i ∈ fst d) ⊓ (fst b ∈ fst B) ⟩
    pin u v u∈ v∈ e =
        subst (λ w → ⟨ w ∈ fst d ⟩) (sym (pr-inj e .fst)) u∈
      , subst (λ w → ⟨ w ∈ fst B ⟩) (sym (pr-inj e .snd)) v∈

  -- BOUNDED to UNBOUNDED.
  unbound : (x : S) → ⟨ (x ∷ []) ⊨ envFoB ⟩ → ⟨ δ x ⊨ envOverAt E D Bi ⟩
  unbound x h = sv , (dom , (vals , prs))
    where
    sl = slots x h

    ap : (i b b' : S) → ⟨ pr (fst i) (fst b) ∈ fst x ⟩
       → ⟨ (b' ∷ b ∷ i ∷ x ∷ [])
           ⊨ appAt (suc (suc (suc zero))) (suc (suc zero)) (suc zero) ⟩
    ap i b b' p = subst ⟨_⟩ (sym (appAt-adequate (suc (suc (suc zero)))
      (suc (suc zero)) (suc zero) (b' ∷ b ∷ i ∷ x ∷ []))) p

    ap' : (i b b' : S) → ⟨ pr (fst i) (fst b') ∈ fst x ⟩
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
  rebound : (x : S) → ⟨ δ x ⊨ envOverAt E D Bi ⟩ → ⟨ (x ∷ []) ⊨ envFoB ⟩
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
  intoSet : (x : S) → ⟨ δ x ⊨ envOverAt E D Bi ⟩ → ⟨ x ∈ˢ envSet B n ⟩
  intoSet x h = subst (λ w → ⟨ w ∈ fst (envSet B n) ⟩)
    (sym (Recover.recovers B n (δ x) E D Bi qdn refl h))
    (envSet-in B (Recover.g B n (δ x) E D Bi qdn refl h))

  outSet : (x : S) → ⟨ x ∈ˢ envSet B n ⟩ → ⟨ δ x ⊨ envOverAt E D Bi ⟩
  outSet x hx = PT.rec (snd (δ x ⊨ envOverAt E D Bi))
    (λ { (dd , hdd) → PT.rec (snd (δ x ⊨ envOverAt E D Bi))
      (λ { (bb , (qd , (qb , hov))) →
        envOverAt-transport (bb ∷ dd ∷ x ∷ []) (δ x)
          (suc (suc zero)) (suc zero) zero E D Bi
          refl (qd ∙ sym qdn) qb hov }) hdd })
    (subst ⟨_⟩ (envSet-mem B n x) hx .snd)

  -- THE JOIN ITSELF, stated at the join and not at the two ends.
  adequate : (x : S) → (⟨ (x ∷ []) ⊨ envFoB ⟩ → ⟨ x ∈ˢ envSet B n ⟩)
           × (⟨ x ∈ˢ envSet B n ⟩ → ⟨ (x ∷ []) ⊨ envFoB ⟩)
  adequate x = (λ h → intoSet x (unbound x h))
             , (λ hx → rebound x (outSet x hx))

-- =====================================================================
-- BLOCK 4.  THE IDENTIFICATION, AND THE ONE DECLARATION THE GATE ASKED
-- FOR.  The carved set IS `envSet B n`, so the containment of BLOCK 1
-- and the membership of BLOCK 2 now speak about the SAME set.
-- =====================================================================

module Land (σ : V ℓ) (oσ : IsOrd σ) (ω∈ : ⟨ ω ∈ σ ⟩) (B d : S) (n : ℕ)
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

-- THE GATE'S DECLARATION.  The iterate is 4 and it does not depend on
-- `n`, so the bound is uniform in `n`.
envSetNumeral∈ : (σ : V ℓ) → IsOrd σ → ⟨ ω ∈ σ ⟩ → (B : S) (n : ℕ)
               → ⟨ fst B ∈ Lset σ ⟩
               → ⟨ fst (envSet B n) ∈ Lset (sucIter 4 σ) ⟩
envSetNumeral∈ σ oσ ω∈ B n hB =
  Land.landed σ oσ ω∈ B (numeralL n) n (numeralL-fst n) hB
