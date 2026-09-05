{-# OPTIONS --cubical --safe --guardedness #-}

-- [LJ-1.567]  The Step formula for `col`.
--
-- W3 IS agents/tasks/LJ-1-567/runs/W3.agda, WRITTEN FIRST AND
-- TYPECHECKED ALONE.  Run runs/w3-1.out (cold) and runs/w3-2.out
-- (warm), exit 0 both.  W3 IS GO: `RecShape` instantiates at
-- dom = Square.sqL κ on the first try.
--
-- THE OBLIGATION IS `col-step`, AND IT IS INHABITED.  This file
-- carries NO hole and NO postulate, so every reduction in it is a
-- measurement and not a claim ([LJ-1.533]'s discipline, kept by
-- [LJ-1.549], [LJ-1.552] and [LJ-1.556]).  Nothing lands in src/.
--
-- WHAT THIS FILE MEASURES, IN ONE LINE EACH.
--
--   Section 1.  THE ORDER IS A PARAMETER, AND IT IS A FORMULA WITH A
--               READING.  `Order` is the whole of what the step needs
--               from `≺`, and it holds no set.
--   Section 2.  THE STEP FORMULA FOR col, AND ITS TWO READINGS.
--               `StepFo`, `StepFo-out`, `StepFo-in`.  `sucV` never
--               has to be an element of the model: the successor is
--               spelled as a disjunction inside the formula.
--   Section 3.  THE OBLIGATION.  `col-step` is Section 2's step read
--               through `RecShape` AT dom = Square.sqL κ, both ways.
--   Section 4.  THE ORDER SLOT IS FILLABLE, MEASURED AND NOT ASSUMED.
--               A BINARY relation between two pair codes is a formula
--               with a reading.  [LJ-1.556] section 2 measured a
--               UNARY condition on one pair code; that is a different
--               shape, and AGENTS.md:45 refuses the analogy.
--
-- WHAT IS NOT HERE.  The Goedel max-then-lexicographic order is NOT
-- built and NOT claimed.  Section 4's witness is the membership order
-- on FIRST components, which is a real binary order formula and is
-- not that order.  See the report's `## WHAT SQUARESTEP STILL WANTS`.
--
-- CALIBER.  The program set GHCRTS="-A64m -I0 -M8g" on this pane.  I
-- did not set it.  One Agda process at a time.  No heap event.

open import Base.Prelude
open import Base.Truth
open import Base.Classical using ( LEM )

module LJ-1-567.Probe567 {ℓ : Level} (lem : LEM (ℓ-suc ℓ)) where

open import FOL.ZFStructure using ( module hPropStructure )
import FOL.Absoluteness
open import FOL.Syntax using ( Formula; var; _∈̇_; _≐_; _∧̇_; _∨̇_; ∃̇_ )
open import V.Hierarchy {ℓ} using ( 𝒮ᵥ )
open import V.Coding {ℓ} using ( pr )
open import V.Model {ℓ} using ( ∈sucV-elim; ∈sucV-inl; self∈sucV )
open import L.Constructible {ℓ} using ( 𝒮ʟ; isL; isL-trans )
open import L.Coding.Model {ℓ}
  using ( extAt; extAt-out; extAt-in; appAt; appAt-adequate
        ; prAtL; prAtL-adequate )
open import L.Coding.Sequence {ℓ} lem using ( module RecShape )

import LJ-1-556.Probe556 {ℓ} lem as P556

open import Cubical.Data.Sigma using ( _×_ )
open import Cubical.Functions.Logic using ( ⇔toPath )
import Cubical.Data.Sum as Sum
import Cubical.HITs.PropositionalTruncation as PT
open PT using ( ∣_∣₁; ∥_∥₁; squash₁ )
open import Cubical.HITs.CumulativeHierarchy.Base using ( V; _∈_ )
open import Cubical.HITs.CumulativeHierarchy.Constructions
  using ( module InfinitySet )
open InfinitySet using ( sucV )

open TruthAlgebra (hPropAlgebra (ℓ-suc ℓ))
open hPropStructure 𝒮ʟ using ( S )

module AbsL = FOL.Absoluteness.Single 𝒮ᵥ isL isL-trans
open AbsL using ( _^_ ) renaming ( _⊨ᵐ_ to _⊨_ )

-- =====================================================================
-- SECTION 1.  THE ORDER IS A PARAMETER, AND IT IS A FORMULA.
--
--   [LJ-1.556] measured that `RecShape` takes its step as a FORMULA
--   and never as a set, and concluded that the order the collapse
--   consults "enters as a FORMULA, so section 2's device carries it
--   and no order-as-a-set is needed"
--   (agents/tasks/LJ-1-556/lj-1.556-report.md:298).
--
--   `Order` IS that conclusion, written as a type.  It holds three
--   things and no fourth: a formula with two free places, the
--   relation on L that the formula is about, and the reading that
--   ties them.  IT HOLDS NO ELEMENT OF L.  So a consumer of the step
--   below never has to produce the order as a set, and W2's rule is
--   answered: the step is written ONCE at a generic order and each
--   order instantiates it.
-- =====================================================================

record Order : Type (ℓ-suc (ℓ-suc ℓ)) where
  field
    fo  : ∀ {n} → Fin n → Fin n → Formula S n
    rel : S → S → Ω
    adq : ∀ {n} (i j : Fin n) (γ : S ^ n)
        → (γ ⊨ fo i j) ≡ rel (lookup i γ) (lookup j γ)

open Order using ( fo; rel; adq )

-- =====================================================================
-- SECTION 2.  THE STEP FORMULA FOR col, AND ITS TWO READINGS.
--
--   The step is  z = ⋃ { sucV (f r) : r ≺ c }.  Membership in that
--   union unfolds to two existentials and no more: `x` lies in the
--   step exactly when SOME predecessor `r` of `c` carries SOME
--   recorded value `w`, with `x` in `sucV w`.
--
--   THE WHOLE STEP IS ONE `extAt`, for the reason the previous
--   chapter states at src/L/Coding/Sequence.lagda.md:81: a
--   set-valued recursion clause says "this value is the set of
--   exactly those things meeting a condition", and `extAt` writes
--   the condition once and returns both readings as projections.
--
--   `sucV` NEVER HAS TO BE AN ELEMENT OF THE MODEL, and that is the
--   one measurement of this section that a chapter should copy.
--   `sucAtL` (src/L/Coding/Model.lagda.md:1395) would say "s is the
--   successor of w", and using it costs a THIRD bound variable whose
--   object-language existential ranges over L, so the step would
--   carry a closure side condition exactly like `PowOK`
--   (src/L/Coding/Sequence.lagda.md:130).  Spelled instead as
--   `x ∈ w ∨̇ x ≐ w` the successor is a DISJUNCTION inside the
--   formula, the side condition disappears, and the two readings
--   below need nothing but `∈sucV-elim` and `∈sucV-inl`
--   (src/V/Model.lagda.md:218 and :230).
-- =====================================================================

private
  sh3 : ∀ {n} → Fin n → Fin (suc (suc (suc n)))
  sh3 i = suc (suc (suc i))

-- The body, at the environment (w ∷ r ∷ x ∷ γ).
--   x  the member of the step, bound by `extAt`   (suc (suc zero))
--   r  a predecessor of the argument c            (suc zero)
--   w  the value the approximation records at r   (zero)
ColBody : (O : Order) → ∀ {n} → Fin n → Fin n → Formula S (suc (suc (suc n)))
ColBody O c f = fo O (suc zero) (sh3 c)
              ∧̇ ( appAt (sh3 f) (suc zero) zero
                ∧̇ ( (var (suc (suc zero)) ∈̇ var zero)
                  ∨̇ (var (suc (suc zero)) ≐ var zero) ) )

-- THE STEP FORMULA.  This is what `RecShape` takes, at exactly its
-- parameter type: three places, the value, the argument, the function.
StepFo : (O : Order) → ∀ {n} → Fin n → Fin n → Fin n → Formula S n
StepFo O z c f = extAt z (∃̇ (∃̇ (ColBody O c f)))

-- One member of the step, as a payload.
ColOf : (O : Order) (f c x : S) → Type (ℓ-suc ℓ)
ColOf O f c x = Σ[ r ∈ S ] Σ[ w ∈ S ]
                  ( ⟨ rel O r c ⟩
                  × ( ⟨ pr (fst r) (fst w) ∈ fst f ⟩
                    × ⟨ fst x ∈ sucV (fst w) ⟩ ) )

module _ (O : Order) {n : ℕ} (z c f : Fin n) (γ : S ^ n) where
  private
    Φ : Formula S (suc n)
    Φ = ∃̇ (∃̇ (ColBody O c f))

    -- perf: env spelled out at both ends (src/L/Coding/Sequence.lagda.md:175)
    readBody : (x r w : S) → ⟨ (w ∷ r ∷ x ∷ γ) ⊨ ColBody O c f ⟩
             → ColOf O (lookup f γ) (lookup c γ) x
    readBody x r w (hlt , (ha , hs)) = r , w , (lt , (ap , suc∈))
      where
      lt : ⟨ rel O r (lookup c γ) ⟩
      lt = subst ⟨_⟩ (adq O (suc zero) (sh3 c) (w ∷ r ∷ x ∷ γ)) hlt

      ap : ⟨ pr (fst r) (fst w) ∈ fst (lookup f γ) ⟩
      ap = subst ⟨_⟩
        (appAt-adequate (sh3 f) (suc zero) zero (w ∷ r ∷ x ∷ γ)) ha

      suc∈ : ⟨ fst x ∈ sucV (fst w) ⟩
      suc∈ = PT.rec (snd (fst x ∈ sucV (fst w)))
        (λ { (Sum.inl m) → ∈sucV-inl {A = fst w} {x = fst x} m
           ; (Sum.inr e) → subst (λ v → ⟨ v ∈ sucV (fst w) ⟩) (sym e)
                             (self∈sucV (fst w)) })
        hs

    writeBody : (x r w : S) → ⟨ rel O r (lookup c γ) ⟩
              → ⟨ pr (fst r) (fst w) ∈ fst (lookup f γ) ⟩
              → ⟨ fst x ∈ sucV (fst w) ⟩
              → ⟨ (w ∷ r ∷ x ∷ γ) ⊨ ColBody O c f ⟩
    writeBody x r w lt ap suc∈ =
        subst ⟨_⟩ (sym (adq O (suc zero) (sh3 c) (w ∷ r ∷ x ∷ γ))) lt
      , ( subst ⟨_⟩
            (sym (appAt-adequate (sh3 f) (suc zero) zero (w ∷ r ∷ x ∷ γ))) ap
        , ∈sucV-elim {A = fst w} {x = fst x}
            (snd ((w ∷ r ∷ x ∷ γ) ⊨ ( (var (suc (suc zero)) ∈̇ var zero)
                                    ∨̇ (var (suc (suc zero)) ≐ var zero) )))
            suc∈ (λ m → ∣ Sum.inl m ∣₁) (λ e → ∣ Sum.inr e ∣₁) )

    unfold : (x : S) → ⟨ (x ∷ γ) ⊨ Φ ⟩
           → ∥ ColOf O (lookup f γ) (lookup c γ) x ∥₁
    unfold x = PT.rec squash₁ viaPred
      where
      viaVal : (r : S) → Σ[ w ∈ S ] ⟨ (w ∷ r ∷ x ∷ γ) ⊨ ColBody O c f ⟩
             → ∥ ColOf O (lookup f γ) (lookup c γ) x ∥₁
      viaVal r (w , hw) = ∣ readBody x r w hw ∣₁

      viaPred : Σ[ r ∈ S ] ⟨ (r ∷ x ∷ γ) ⊨ ∃̇ (ColBody O c f) ⟩
              → ∥ ColOf O (lookup f γ) (lookup c γ) x ∥₁
      viaPred (r , hr) = PT.rec squash₁ (viaVal r) hr

  -- READING ONE.  Every member of the step is in the successor of a
  -- value recorded at a predecessor.
  StepFo-out : ⟨ γ ⊨ StepFo O z c f ⟩ → (x : S)
             → ⟨ fst x ∈ fst (lookup z γ) ⟩
             → ∥ ColOf O (lookup f γ) (lookup c γ) x ∥₁
  StepFo-out h x x∈ = unfold x (extAt-out z Φ γ h x x∈)

  -- READING TWO.  And every such thing is a member.
  StepFo-in : ⟨ γ ⊨ StepFo O z c f ⟩ → (x : S)
            → ColOf O (lookup f γ) (lookup c γ) x
            → ⟨ fst x ∈ fst (lookup z γ) ⟩
  StepFo-in h x (r , w , (lt , (ap , suc∈))) =
    extAt-in z Φ γ h x ∣ r , ∣ w , writeBody x r w lt ap suc∈ ∣₁ ∣₁

-- =====================================================================
-- SECTION 3.  THE OBLIGATION.
--
--   `RecShape` (src/L/Coding/Sequence.lagda.md:281) instantiated at
--   Section 2's step, and read AT dom = Square.sqL κ, which is the
--   domain [LJ-1.556] delivered (agents/tasks/LJ-1-556/Probe556.agda:148).
--
--   `RecShape`'s `Step` HAS THREE `Fin n` ARGUMENTS, and the brief
--   asks what each is here.  Read off `ApproxAt`
--   (src/L/Coding/Sequence.lagda.md:286) and `ApproxAt-step`
--   (src/L/Coding/Sequence.lagda.md:303), which pin them:
--
--     first   THE VALUE.  `z`, the step's own result.  In `col` it is
--             the ordinal the collapse assigns to the argument.
--     second  THE ARGUMENT.  `c`, a member of the domain.  In `col`
--             it is a member of `Square.sqL κ`, so a coded pair.
--     third   THE APPROXIMATION.  `f`, the partial collapse already
--             built.  `Step` may look at it ONLY through `appAt`.
--
--   The instantiation itself never inspects the domain: `RecShape`
--   holds it in one environment slot of type `S`.  That is what W3
--   measured (runs/W3.agda, runs/w3-1.out), and it is why the brief's
--   question "will `RecShape` instantiate there" has the answer YES
--   with nothing to pay.
--
--   `col-step` DELIVERS BOTH DIRECTIONS AT ONCE, because one
--   direction is not the statement.  `z = ⋃ { sucV (f r) : r ≺ c }`
--   is a set identity, and a set identity read only outward is an
--   inclusion.
-- =====================================================================

module RS (O : Order) = RecShape (StepFo O)

-- `RecShape`'s approximation predicate, AT dom = Square.sqL κ.
-- The two slots are the function and the domain, in that order.
Approx : (O : Order) (κ f : S) → Type (ℓ-suc ℓ)
Approx O κ f =
  ⟨ (f ∷ P556.Square.sqL κ ∷ []) ⊨ RS.ApproxAt O zero (suc zero) ⟩

-- THE OBLIGATION.
col-step : (O : Order) (κ f : S) → Approx O κ f → (c z : S)
         → ⟨ pr (fst c) (fst z) ∈ fst f ⟩
         → ( ((x : S) → ⟨ fst x ∈ fst z ⟩ → ∥ ColOf O f c x ∥₁)
           × ((x : S) → ColOf O f c x → ⟨ fst x ∈ fst z ⟩) )
col-step O κ f ha c z hp =
    StepFo-out O zero (suc zero) (suc (suc zero))
      (z ∷ c ∷ f ∷ P556.Square.sqL κ ∷ []) hs
  , StepFo-in O zero (suc zero) (suc (suc zero))
      (z ∷ c ∷ f ∷ P556.Square.sqL κ ∷ []) hs
  where
  hs : ⟨ (z ∷ c ∷ f ∷ P556.Square.sqL κ ∷ [])
         ⊨ StepFo O zero (suc zero) (suc (suc zero)) ⟩
  hs = RS.ApproxAt-step O zero (suc zero)
         (f ∷ P556.Square.sqL κ ∷ []) ha c z hp

-- =====================================================================
-- SECTION 4.  THE ORDER SLOT IS FILLABLE, AND IT IS MEASURED HERE.
--
--   Section 1's `Order` is a parameter, and a parameter nobody can
--   fill is not a measurement.  [LJ-1.556] section 2 filled a
--   different shape: `ltFo` (agents/tasks/LJ-1-556/Probe556.agda:219)
--   is a UNARY condition on ONE pair code, with one free place.  An
--   order is BINARY: two pair codes, four components, and a condition
--   across them.  AGENTS.md:45 refuses the transfer by analogy, so
--   the binary shape is built and read at its own site below.
--
--   THIS IS NOT THE GOEDEL ORDER AND IT IS NOT CLAIMED TO BE.  It is
--   membership on FIRST components: `r ≺ c` when `r = pr a b`,
--   `c = pr d e` and `a ∈ d`.  It is not total on `Square.sqL κ` and
--   it is not well-founded there, so no collapse runs on it.  What it
--   measures is the SHAPE: four bound components, two `prAtL` reads,
--   one condition across them, and a two-way reading, with NO set
--   anywhere.  The Goedel max-then-lexicographic order adds a `max`
--   and a case split over the same four components; it costs more
--   conjuncts and NOT a different shape, and it is not built here.
--
--   THE BRIEF'S TEST IS PASSED: I did not build an order-as-a-set at
--   any point, so [LJ-1.556]'s finding holds at this frame.
-- =====================================================================

private
  sh4 : ∀ {n} → Fin n → Fin (suc (suc (suc (suc n))))
  sh4 i = suc (suc (suc (suc i)))

  -- At the environment (e ∷ d ∷ b ∷ a ∷ γ), with r = pr a b and
  -- c = pr d e the two pair codes the order compares.
  FstBody : ∀ {n} → Fin n → Fin n → Formula S (suc (suc (suc (suc n))))
  FstBody i j = prAtL (sh4 i) (suc (suc (suc zero))) (suc (suc zero))
              ∧̇ ( prAtL (sh4 j) (suc zero) zero
                ∧̇ (var (suc (suc (suc zero))) ∈̇ var (suc zero)) )

FstFo : ∀ {n} → Fin n → Fin n → Formula S n
FstFo i j = ∃̇ (∃̇ (∃̇ (∃̇ (FstBody i j))))

FstOf : S → S → Type (ℓ-suc ℓ)
FstOf r c = Σ[ a ∈ S ] Σ[ b ∈ S ] Σ[ d ∈ S ] Σ[ e ∈ S ]
              ( (fst r ≡ pr (fst a) (fst b))
              × ( (fst c ≡ pr (fst d) (fst e))
                × ⟨ fst a ∈ fst d ⟩ ) )

FstRel : S → S → Ω
FstRel r c = ∥ FstOf r c ∥₁ , squash₁

FstFo-adequate : ∀ {n} (i j : Fin n) (γ : S ^ n)
  → (γ ⊨ FstFo i j) ≡ FstRel (lookup i γ) (lookup j γ)
FstFo-adequate i j γ = ⇔toPath fwd bwd
  where
  fwd : ⟨ γ ⊨ FstFo i j ⟩ → ∥ FstOf (lookup i γ) (lookup j γ) ∥₁
  fwd = PT.rec squash₁ viaA
    where
    -- perf: env spelled out at both ends (src/L/Coding/Sequence.lagda.md:175)
    viaE : (a b d : S) → Σ[ e ∈ S ] ⟨ (e ∷ d ∷ b ∷ a ∷ γ) ⊨ FstBody i j ⟩
         → ∥ FstOf (lookup i γ) (lookup j γ) ∥₁
    viaE a b d (e , (hr , (hc , hm))) = ∣ a , b , d , e , (qr , (qc , hm)) ∣₁
      where
      qr : fst (lookup i γ) ≡ pr (fst a) (fst b)
      qr = subst ⟨_⟩ (prAtL-adequate (sh4 i) (suc (suc (suc zero)))
             (suc (suc zero)) (e ∷ d ∷ b ∷ a ∷ γ)) hr

      qc : fst (lookup j γ) ≡ pr (fst d) (fst e)
      qc = subst ⟨_⟩ (prAtL-adequate (sh4 j) (suc zero) zero
             (e ∷ d ∷ b ∷ a ∷ γ)) hc

    viaD : (a b : S) → Σ[ d ∈ S ] ⟨ (d ∷ b ∷ a ∷ γ) ⊨ ∃̇ (FstBody i j) ⟩
         → ∥ FstOf (lookup i γ) (lookup j γ) ∥₁
    viaD a b (d , hd) = PT.rec squash₁ (viaE a b d) hd

    viaB : (a : S) → Σ[ b ∈ S ] ⟨ (b ∷ a ∷ γ) ⊨ ∃̇ (∃̇ (FstBody i j)) ⟩
         → ∥ FstOf (lookup i γ) (lookup j γ) ∥₁
    viaB a (b , hb) = PT.rec squash₁ (viaD a b) hb

    viaA : Σ[ a ∈ S ] ⟨ (a ∷ γ) ⊨ ∃̇ (∃̇ (∃̇ (FstBody i j))) ⟩
         → ∥ FstOf (lookup i γ) (lookup j γ) ∥₁
    viaA (a , ha) = PT.rec squash₁ (viaB a) ha

  bwd : ∥ FstOf (lookup i γ) (lookup j γ) ∥₁ → ⟨ γ ⊨ FstFo i j ⟩
  bwd = PT.rec (snd (γ ⊨ FstFo i j))
    (λ { (a , b , d , e , (qr , (qc , hm))) →
      ∣ a , ∣ b , ∣ d , ∣ e
        , ( subst ⟨_⟩ (sym (prAtL-adequate (sh4 i) (suc (suc (suc zero)))
              (suc (suc zero)) (e ∷ d ∷ b ∷ a ∷ γ))) qr
          , ( subst ⟨_⟩ (sym (prAtL-adequate (sh4 j) (suc zero) zero
                (e ∷ d ∷ b ∷ a ∷ γ))) qc
            , hm ) ) ∣₁ ∣₁ ∣₁ ∣₁ })

FstOrder : Order
FstOrder = record { fo = FstFo ; rel = FstRel ; adq = FstFo-adequate }

-- THE PARAMETER IS NOT VACUOUS.  The obligation, at a concrete order.
col-step-at-Fst : (κ f : S) → Approx FstOrder κ f → (c z : S)
                → ⟨ pr (fst c) (fst z) ∈ fst f ⟩
                → ( ((x : S) → ⟨ fst x ∈ fst z ⟩ → ∥ ColOf FstOrder f c x ∥₁)
                  × ((x : S) → ColOf FstOrder f c x → ⟨ fst x ∈ fst z ⟩) )
col-step-at-Fst = col-step FstOrder
