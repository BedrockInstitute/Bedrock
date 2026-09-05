# The pinned matrix and its soundness frame

```agda
{-# OPTIONS --cubical --safe --guardedness #-}

open import Base.Prelude
open import Base.Truth
open import Base.Classical using ( LEM )

module L.GCH.Sound {ℓ : Level} (lem : LEM (ℓ-suc ℓ)) where

open import FOL.ZFStructure using ( module hPropStructure )
open import FOL.Syntax using
  ( Formula; var; _∈̇_; _∧̇_; ∃̇∈; ∀̇∈ )
open import FOL.LevyHierarchy using
  ( Δ₀; δ-∧; δ-∀∈; δ-∃∈ )
open import FOL.Manipulation.Parameters using ( countFo )
open import FOL.Manipulation.Relabelling using ( embed; embed-⊨; mapΔ₀ )
import FOL.Absoluteness
import FOL.Semantics
open import V.Hierarchy {ℓ} using ( 𝒮ᵥ; extensionalV )
open import V.Coding {ℓ} using ( pr )
open import L.Constructible {ℓ} using ( 𝒮ʟ; IsOrd; Lset; isL; isL-trans )
open import L.Coding.Model {ℓ} using
  ( prAtL; prAtL-adequate; sucAtL; sucAtL-adequate; prʟ; prʟ-fst )
open import L.Axioms.Numerals {ℓ} using ( numeralL; numeralL-fst )
open import L.Condensation {ℓ} lem using ( Δ₀-prAtL; Δ₀-sucAtL; module KFactsNS )
open import L.Coding.Sequence {ℓ} lem using ( LsetGraphAt )
open import L.Hierarchy {ℓ} lem using ( Lset-only )
open import L.GCH.Hull {ℓ} lem using
  ( module Cnt; erase-Δ₀; isOrd-at-p; Δ₀-isOrd-at-p; _⊨ₚ_ )
open import L.GCH.Frame {ℓ} lem using ( module Matrix; module W3 )

open import Cubical.Data.Vec using ( _∷_; []; map; lookup )
open import Cubical.Data.Sigma using ( _×_ )
open import Cubical.Functions.Logic using ( ⇔toPath )
import Cubical.Data.Empty as Empty
import Cubical.HITs.PropositionalTruncation as PT
open import Cubical.HITs.CumulativeHierarchy.Base using ( V; _∈_; setIsSet )
open import Cubical.HITs.CumulativeHierarchy.Properties using ( ∈∈ₛ )
open import Cubical.HITs.CumulativeHierarchy.Constructions
  using ( ∅; ∅-empty; module InfinitySet )
open InfinitySet {ℓ} using ( #_; sucV )

open TruthAlgebra (hPropAlgebra (ℓ-suc ℓ))
open hPropStructure 𝒮ᵥ
open KFactsNS

-- The class-carrier reading, as src/L/Condensation.lagda.md:76-77.
module AbsL = FOL.Absoluteness.Single 𝒮ᵥ isL isL-trans
open AbsL using ( _^_ ) renaming ( _⊨ᵐ_ to _⊨_ )

module SemVᵃ = FOL.Semantics (hPropAlgebra (ℓ-suc ℓ)) 𝒮ᵥ

-- The 𝒮ʟ carrier, for the syntax.  Same name as src/L/GCH/Frame.lagda.md.
module CS = hPropStructure 𝒮ʟ

-- =====================================================================
-- STEP 1.  THE PINNED MATRIX.  Frame's `Matrix` pins only the
-- transitivity of K and the twelve numerals.  `MatrixP` adds the pair
-- pin: K is closed under ordered pairs.  Everything else is Frame's.
-- =====================================================================

module MatrixP {m : ℕ} (w b K : Fin m)
               (N0 N1 N2 N3 N4 N5 N6 N7 N8 N9 N10 N11 : Fin m) where

  module Mx = Matrix {m} w b K N0 N1 N2 N3 N4 N5 N6 N7 N8 N9 N10 N11
  open Mx public using ( transK; Δ₀-transK; pins; Δ₀-pins; module G
                       ; Δ₀-ψs; Δ₀-ψa )

  -- K IS CLOSED UNDER ORDERED PAIRS.  At x ∷ γ the bound is suc K; at
  -- y ∷ x ∷ γ it is suc (suc K); at p ∷ y ∷ x ∷ γ the pair slot is
  -- zero, x is suc (suc zero) and y is suc zero.
  pairK : Formula CS.S m
  pairK = ∀̇∈ (var K)
            (∀̇∈ (var (suc K))
              (∃̇∈ (var (suc (suc K)))
                (prAtL zero (suc (suc zero)) (suc zero))))

  Δ₀-pairK : Δ₀ pairK
  Δ₀-pairK = δ-∀∈ (δ-∀∈ (δ-∃∈ (Δ₀-prAtL zero (suc (suc zero)) (suc zero))))

  -- K IS CLOSED UNDER SUCCESSOR.  `KFacts.innerK` and `innerPairK`
  -- (src/L/Condensation.lagda.md:6106-6110) range over EVERY numeral,
  -- and twelve pinned tags reach only twelve; the successor pin reaches
  -- them all by induction.  At y ∷ x ∷ γ, x is suc zero and y is zero.
  sucK : Formula CS.S m
  sucK = ∀̇∈ (var K) (∃̇∈ (var (suc K)) (sucAtL (suc zero) zero))

  Δ₀-sucK : Δ₀ sucK
  Δ₀-sucK = δ-∀∈ (δ-∃∈ (Δ₀-sucAtL (suc zero) zero))

  -- THE WHOLE MATRIX, WITH THE TWO PINS, AND IT IS Δ₀.
  matrix′ : Formula CS.S m
  matrix′ = transK ∧̇ ( pairK ∧̇ ( sucK ∧̇ ( pins ∧̇ G.graphBndAt ) ) )

  Δ₀-matrix′ : Δ₀ matrix′
  Δ₀-matrix′ =
    δ-∧ Δ₀-transK
      (δ-∧ Δ₀-pairK
        (δ-∧ Δ₀-sucK (δ-∧ Δ₀-pins (G.Δ₀-graphBndAt Δ₀-ψs Δ₀-ψa))))

-- The three-slot erased form, built exactly as Frame's `W3` builds
-- `three`: twelve bounded existentials over the witness slot, outermost
-- environment a ∷ p ∷ z.
module W3′ where

  n0 n1 n2 n3 n4 n5 n6 n7 n8 n9 n10 n11 ww bb kk : Fin 15
  n0  = zero
  n1  = suc zero
  n2  = suc (suc zero)
  n3  = suc (suc (suc zero))
  n4  = suc (suc (suc (suc zero)))
  n5  = suc (suc (suc (suc (suc zero))))
  n6  = suc (suc (suc (suc (suc (suc zero)))))
  n7  = suc (suc (suc (suc (suc (suc (suc zero))))))
  n8  = suc (suc (suc (suc (suc (suc (suc (suc zero)))))))
  n9  = suc (suc (suc (suc (suc (suc (suc (suc (suc zero))))))))
  n10 = suc (suc (suc (suc (suc (suc (suc (suc (suc (suc zero)))))))))
  n11 = suc (suc (suc (suc (suc (suc (suc (suc (suc (suc (suc zero))))))))))
  ww  = suc (suc (suc (suc (suc (suc (suc (suc (suc (suc (suc (suc zero)))))))))))
  bb  = suc (suc (suc (suc (suc (suc (suc (suc (suc (suc (suc (suc (suc zero))))))))))))
  kk  = suc (suc (suc (suc (suc (suc (suc (suc (suc (suc (suc (suc (suc (suc zero)))))))))))))

  module Mx = MatrixP {15} ww bb kk n0 n1 n2 n3 n4 n5 n6 n7 n8 n9 n10 n11

  open W3 using ( wrap; δ-wrap )

  -- SEALED.  The bounded graph is thousands of nodes; every conversion
  -- that reaches it through `_⊨_` normalises it whole, and the twelve
  -- wraps below hit it twelve times: one such check ran past 280 s.
  -- Sealed, `γ ⊨ inner` is stuck and the wraps compare in one step.
  -- The measured cure of src/L/GCH/OrderType.lagda.md:106-117.
  opaque
    inner : Formula CS.S 15
    inner = Mx.matrix′

  opaque
    unfolding inner

    Δ₀-inner : Δ₀ inner
    Δ₀-inner = Mx.Δ₀-matrix′

    inner-out : (γ : CS.S ^ 15) → ⟨ γ ⊨ inner ⟩ → ⟨ γ ⊨ Mx.matrix′ ⟩
    inner-out γ h = h

    inner-in : (γ : CS.S ^ 15) → ⟨ γ ⊨ Mx.matrix′ ⟩ → ⟨ γ ⊨ inner ⟩
    inner-in γ h = h

  s14 = wrap {13} inner
  s13 = wrap {12} s14
  s12 = wrap {11} s13
  s11 = wrap {10} s12
  s10 = wrap {9}  s11
  s9  = wrap {8}  s10
  s8  = wrap {7}  s9
  s7  = wrap {6}  s8
  s6  = wrap {5}  s7
  s5  = wrap {4}  s6
  s4  = wrap {3}  s5
  three : Formula CS.S 3
  three = wrap {2} s4

  Δ₀-three : Δ₀ three
  Δ₀-three =
    δ-wrap (δ-wrap (δ-wrap (δ-wrap (δ-wrap (δ-wrap
      (δ-wrap (δ-wrap (δ-wrap (δ-wrap (δ-wrap (δ-wrap Δ₀-inner)))))))))))

  opaque
    unfolding inner

    count-three : countFo three ≡ 0
    count-three = refl

  erased : Formula (⊥* {ℓ-suc ℓ}) 3
  erased = Cnt.erase three count-three

  Δ₀-erased : Δ₀ erased
  Δ₀-erased = erase-Δ₀ three count-three Δ₀-three

-- THE PINNED MATRIX THE LITERATURE HAS, at the consumer's slot order
-- (value, parameter, witness) = (a, p, z).
φ₃′ : Formula (⊥* {ℓ-suc ℓ}) 3
φ₃′ = W3′.erased

Δ₀-φ₃′ : Δ₀ φ₃′
Δ₀-φ₃′ = W3′.Δ₀-erased

matrix₃′ : Formula (⊥* {ℓ-suc ℓ}) 3
matrix₃′ = isOrd-at-p ∧̇ φ₃′

Δ₀-matrix₃′ : Δ₀ matrix₃′
Δ₀-matrix₃′ = δ-∧ Δ₀-isOrd-at-p Δ₀-φ₃′

opaque
  unfolding W3′.inner

  count-matrix₃′ : countFo matrix₃′ ≡ 0
  count-matrix₃′ = refl
```

```agda
-- =====================================================================
-- STEP 2.  THE PIN IS SPENT.  From the class-carrier reading of the
-- pinned matrix at any environment, the `KFacts` record of
-- src/L/Condensation.lagda.md:6079 at the value slot `w` and the bound
-- `K`: the twelve tag equalities from `pins`, the twelve numeral
-- memberships from the tag slots' membership in K (the twelve bounded
-- existentials of `W3′`), the pair closures from `pairK`, the carrier
-- and arity closures from `transK` and the step frame.
-- =====================================================================

module Read {m : ℕ} (w b K : Fin m)
            (N0 N1 N2 N3 N4 N5 N6 N7 N8 N9 N10 N11 : Fin m)
            (γ : CS.S ^ m) where

  module P = MatrixP {m} w b K N0 N1 N2 N3 N4 N5 N6 N7 N8 N9 N10 N11

  Kv : CS.S
  Kv = lookup K γ

  InK : V ℓ → Type (ℓ-suc ℓ)
  InK x = ⟨ x ∈ fst Kv ⟩

  -- A member of a class-carrier element, packaged as one.
  down : (x : CS.S) (y : V ℓ) → ⟨ y ∈ fst x ⟩ → CS.S
  down x y y∈x = y , isL-trans {x = fst x} {y = y} y∈x (snd x)

  -- K IS TRANSITIVE.
  trans-out : ⟨ γ ⊨ P.transK ⟩
            → (x y : V ℓ) → InK x → ⟨ y ∈ x ⟩ → InK y
  trans-out h x y xK yx =
    h (x , isL-trans {x = fst Kv} {y = x} xK (snd Kv)) xK
      (down (x , isL-trans {x = fst Kv} {y = x} xK (snd Kv)) y yx) yx

  -- K IS CLOSED UNDER ORDERED PAIRS.
  pair-out : ⟨ γ ⊨ P.pairK ⟩
           → (x y : CS.S) → InK (fst x) → InK (fst y) → InK (pr (fst x) (fst y))
  pair-out h x y xK yK =
    PT.rec (snd (pr (fst x) (fst y) ∈ fst Kv)) go (h x xK y yK)
    where
    go : Σ[ q ∈ CS.S ] (InK (fst q)
           × ⟨ (q ∷ y ∷ x ∷ γ) ⊨ prAtL zero (suc (suc zero)) (suc zero) ⟩)
       → InK (pr (fst x) (fst y))
    go (q , qK , hq) =
      subst (λ u → ⟨ u ∈ fst Kv ⟩)
        (subst ⟨_⟩ (prAtL-adequate zero (suc (suc zero)) (suc zero)
                      (q ∷ y ∷ x ∷ γ)) hq)
        qK

  -- THE TWELVE TAG SLOTS HOLD THE TWELVE NUMERALS.  N0 is empty, each
  -- next slot is the successor: `# k` on the nose, then `numeralL-fst`.
  suc-out : (i j : Fin m) → ⟨ γ ⊨ sucAtL i j ⟩
          → fst (lookup j γ) ≡ sucV (fst (lookup i γ))
  suc-out i j h = subst ⟨_⟩ (sucAtL-adequate i j γ) h

  -- EVERY NUMERAL LIES IN K, from the empty tag and the successor pin.
  numK-all : ⟨ γ ⊨ P.sucK ⟩ → InK (fst (numeralL 0))
           → (k : ℕ) → InK (fst (numeralL k))
  numK-all hs h0 zero = h0
  numK-all hs h0 (suc k) =
    PT.rec (snd (fst (numeralL (suc k)) ∈ fst Kv)) go
      (hs (numeralL k) (numK-all hs h0 k))
    where
    go : Σ[ y ∈ CS.S ] (InK (fst y)
           × ⟨ (y ∷ numeralL k ∷ γ) ⊨ sucAtL (suc zero) zero ⟩)
       → InK (fst (numeralL (suc k)))
    go (y , yK , hy) =
      subst InK
        (subst ⟨_⟩ (sucAtL-adequate (suc zero) zero (y ∷ numeralL k ∷ γ)) hy
         ∙ cong sucV (numeralL-fst k) ∙ sym (numeralL-fst (suc k)))
        yK

  module Tags (hp : ⟨ γ ⊨ P.pins ⟩) where
    N0v : CS.S
    N0v = lookup N0 γ

    t0 : fst N0v ≡ # 0
    t0 = extensionalV {a = fst N0v} {b = ∅} (λ x → ⇔toPath (fwd x) (bwd x))
      where
      fwd : (x : V ℓ) → ⟨ x ∈ fst N0v ⟩ → ⟨ x ∈ ∅ ⟩
      fwd x x∈ = Empty.rec (hp .fst (down N0v x x∈) x∈ .lower)
      bwd : (x : V ℓ) → ⟨ x ∈ ∅ ⟩ → ⟨ x ∈ fst N0v ⟩
      bwd x x∈ = Empty.rec (∅-empty x (∈∈ₛ {a = x} {b = ∅} .fst x∈))

    t1 : fst (lookup N1 γ) ≡ # 1
    t1 = suc-out N0 N1 (hp .snd .fst) ∙ cong sucV t0
    t2 : fst (lookup N2 γ) ≡ # 2
    t2 = suc-out N1 N2 (hp .snd .snd .fst) ∙ cong sucV t1
    t3 : fst (lookup N3 γ) ≡ # 3
    t3 = suc-out N2 N3 (hp .snd .snd .snd .fst) ∙ cong sucV t2
    t4 : fst (lookup N4 γ) ≡ # 4
    t4 = suc-out N3 N4 (hp .snd .snd .snd .snd .fst) ∙ cong sucV t3
    t5 : fst (lookup N5 γ) ≡ # 5
    t5 = suc-out N4 N5 (hp .snd .snd .snd .snd .snd .fst) ∙ cong sucV t4
    t6 : fst (lookup N6 γ) ≡ # 6
    t6 = suc-out N5 N6 (hp .snd .snd .snd .snd .snd .snd .fst) ∙ cong sucV t5
    t7 : fst (lookup N7 γ) ≡ # 7
    t7 = suc-out N6 N7 (hp .snd .snd .snd .snd .snd .snd .snd .fst) ∙ cong sucV t6
    t8 : fst (lookup N8 γ) ≡ # 8
    t8 = suc-out N7 N8 (hp .snd .snd .snd .snd .snd .snd .snd .snd .fst) ∙ cong sucV t7
    t9 : fst (lookup N9 γ) ≡ # 9
    t9 = suc-out N8 N9 (hp .snd .snd .snd .snd .snd .snd .snd .snd .snd .fst) ∙ cong sucV t8
    t10 : fst (lookup N10 γ) ≡ # 10
    t10 = suc-out N9 N10 (hp .snd .snd .snd .snd .snd .snd .snd .snd .snd .snd .fst) ∙ cong sucV t9
    t11 : fst (lookup N11 γ) ≡ # 11
    t11 = suc-out N10 N11 (hp .snd .snd .snd .snd .snd .snd .snd .snd .snd .snd .snd) ∙ cong sucV t10

  -- THE VALUE'S MEMBERS LIE IN K.  A member x of the value satisfies
  -- the bounded step witness: some d ∈ K with x ∈ d, and K is
  -- transitive.  This is the `carrierK` field at A := w.
  value-in-K : ⟨ γ ⊨ P.transK ⟩ → ⟨ γ ⊨ P.G.graphBndAt ⟩
             → (v : CS.S) → ⟨ fst v ∈ fst (lookup w γ) ⟩ → InK (fst v)
  value-in-K ht hg v v∈w = PT.rec (snd (fst v ∈ fst Kv)) byF hg
    where
    byF : Σ[ f ∈ CS.S ] (InK (fst f)
            × ⟨ (f ∷ γ) ⊨ (P.G.A.approxBndAt ∧̇ P.G.S.stepBndAt) ⟩)
        → InK (fst v)
    byF (f , fK , (_ , hs)) =
      PT.rec (snd (fst v ∈ fst Kv)) byC (hs .fst v v∈w)
      where
      byC : Σ[ c ∈ CS.S ] (⟨ fst c ∈ fst (lookup b γ) ⟩
              × ⟨ (c ∷ v ∷ f ∷ γ) ⊨
                  ∃̇∈ (var (suc (suc (suc K))))
                    (∃̇∈ (var (suc (suc (suc (suc K))))) P.G.S.bodyB) ⟩)
          → InK (fst v)
      byC (c , _ , hc) = PT.rec (snd (fst v ∈ fst Kv)) byW hc
        where
        byW : Σ[ w' ∈ CS.S ] (InK (fst w')
                × ⟨ (w' ∷ c ∷ v ∷ f ∷ γ) ⊨
                    ∃̇∈ (var (suc (suc (suc (suc K))))) P.G.S.bodyB ⟩)
            → InK (fst v)
        byW (w' , _ , hw) = PT.rec (snd (fst v ∈ fst Kv)) byD hw
          where
          byD : Σ[ d ∈ CS.S ] (InK (fst d)
                  × ⟨ (d ∷ w' ∷ c ∷ v ∷ f ∷ γ) ⊨ P.G.S.bodyB ⟩)
              → InK (fst v)
          byD (d , dK , hb) = trans-out ht (fst d) (fst v) dK (hb .snd .snd .snd)

  -- THE TWELVE TAG SLOTS LIE IN K.  Not part of `matrix′`: the twelve
  -- bounded existentials of `W3′` supply it at the reading.
  record TagsInK : Type (ℓ-suc ℓ) where
    field
      k0 : InK (fst (lookup N0 γ))
      k1 : InK (fst (lookup N1 γ))
      k2 : InK (fst (lookup N2 γ))
      k3 : InK (fst (lookup N3 γ))
      k4 : InK (fst (lookup N4 γ))
      k5 : InK (fst (lookup N5 γ))
      k6 : InK (fst (lookup N6 γ))
      k7 : InK (fst (lookup N7 γ))
      k8 : InK (fst (lookup N8 γ))
      k9 : InK (fst (lookup N9 γ))
      k10 : InK (fst (lookup N10 γ))
      k11 : InK (fst (lookup N11 γ))
  open TagsInK

  -- THE RECORD.  Every field from the reading and the tag memberships.
  kfacts : ⟨ γ ⊨ P.matrix′ ⟩ → TagsInK
         → KFacts w K N0 N1 N2 N3 N4 N5 N6 N7 N8 N9 N10 N11 γ
  kfacts (ht , (hq , (hs , (hp , hg)))) tk = record
    { tagEq0 = e0 ; tagEq1 = e1 ; tagEq2 = e2 ; tagEq3 = e3
    ; tagEq4 = e4 ; tagEq5 = e5 ; tagEq6 = e6 ; tagEq7 = e7
    ; tagEq8 = e8 ; tagEq9 = e9 ; tagEq10 = e10 ; tagEq11 = e11
    ; numK0 = subst InK e0 (tk .k0) ; numK1 = subst InK e1 (tk .k1)
    ; numK2 = subst InK e2 (tk .k2) ; numK3 = subst InK e3 (tk .k3)
    ; numK4 = subst InK e4 (tk .k4) ; numK5 = subst InK e5 (tk .k5)
    ; numK6 = subst InK e6 (tk .k6) ; numK7 = subst InK e7 (tk .k7)
    ; numK8 = subst InK e8 (tk .k8) ; numK9 = subst InK e9 (tk .k9)
    ; numK10 = subst InK e10 (tk .k10) ; numK11 = subst InK e11 (tk .k11)
    ; innerK = λ k a ha →
        subst InK (sym (prʟ-fst (numeralL k) a))
          (pair-out hq (numeralL k) a (num k) ha)
    ; innerPairK = λ k a b ha hb →
        subst InK (sym (prʟ-fst (numeralL k) (prʟ a b)))
          (pair-out hq (numeralL k) (prʟ a b) (num k)
            (subst InK (sym (prʟ-fst a b)) (pair-out hq a b ha hb)))
    ; pairK = λ a b ha hb →
        subst InK (sym (prʟ-fst a b)) (pair-out hq a b ha hb)
    ; carrierK = value-in-K ht hg
    ; arityK = λ N v v∈N N∈K → trans-out ht (fst N) (fst v) N∈K v∈N }
    where
    module T = Tags hp
    e0 : fst (lookup N0 γ) ≡ fst (numeralL 0)
    e0 = T.t0 ∙ sym (numeralL-fst 0)
    e1 : fst (lookup N1 γ) ≡ fst (numeralL 1)
    e1 = T.t1 ∙ sym (numeralL-fst 1)
    e2 : fst (lookup N2 γ) ≡ fst (numeralL 2)
    e2 = T.t2 ∙ sym (numeralL-fst 2)
    e3 : fst (lookup N3 γ) ≡ fst (numeralL 3)
    e3 = T.t3 ∙ sym (numeralL-fst 3)
    e4 : fst (lookup N4 γ) ≡ fst (numeralL 4)
    e4 = T.t4 ∙ sym (numeralL-fst 4)
    e5 : fst (lookup N5 γ) ≡ fst (numeralL 5)
    e5 = T.t5 ∙ sym (numeralL-fst 5)
    e6 : fst (lookup N6 γ) ≡ fst (numeralL 6)
    e6 = T.t6 ∙ sym (numeralL-fst 6)
    e7 : fst (lookup N7 γ) ≡ fst (numeralL 7)
    e7 = T.t7 ∙ sym (numeralL-fst 7)
    e8 : fst (lookup N8 γ) ≡ fst (numeralL 8)
    e8 = T.t8 ∙ sym (numeralL-fst 8)
    e9 : fst (lookup N9 γ) ≡ fst (numeralL 9)
    e9 = T.t9 ∙ sym (numeralL-fst 9)
    e10 : fst (lookup N10 γ) ≡ fst (numeralL 10)
    e10 = T.t10 ∙ sym (numeralL-fst 10)
    e11 : fst (lookup N11 γ) ≡ fst (numeralL 11)
    e11 = T.t11 ∙ sym (numeralL-fst 11)
    num : (k : ℕ) → InK (fst (numeralL k))
    num = numK-all hs (subst InK e0 (tk .k0))

-- The reading at the fifteen-slot environment of `W3′`.
module R15 (γ : CS.S ^ 15) =
  Read {15} W3′.ww W3′.bb W3′.kk
    W3′.n0 W3′.n1 W3′.n2 W3′.n3 W3′.n4 W3′.n5
    W3′.n6 W3′.n7 W3′.n8 W3′.n9 W3′.n10 W3′.n11 γ

kfacts-from-reading :
    (γ : CS.S ^ 15) → ⟨ γ ⊨ W3′.Mx.matrix′ ⟩ → R15.TagsInK γ
  → KFacts W3′.ww W3′.kk
      W3′.n0 W3′.n1 W3′.n2 W3′.n3 W3′.n4 W3′.n5
      W3′.n6 W3′.n7 W3′.n8 W3′.n9 W3′.n10 W3′.n11 γ
kfacts-from-reading γ = R15.kfacts γ
```

```agda
-- =====================================================================
-- STEP 3.  THE SOUNDNESS FRAME.  The reading of `matrix₃′` at a
-- class-carrier triple is the ordinality of p and the fifteen-slot
-- reading of `matrix′` under twelve bounded existentials.  `GraphLift` is
-- the one hypothesis: the bounded graph reaches the unbounded
-- `LsetGraphAt` at the same environment.  It is NOT proved here; the
-- report says why the two pins cannot supply it.  Given it, `Lset-only`
-- (src/L/Hierarchy.lagda.md:334) closes the theorem.
-- =====================================================================

GraphLift : Type (ℓ-suc ℓ)
GraphLift = (γ : CS.S ^ 15) → ⟨ γ ⊨ W3′.Mx.matrix′ ⟩ → R15.TagsInK γ
     → ⟨ γ ⊨ LsetGraphAt W3′.ww W3′.bb ⟩

-- The class-carrier reading of a parameter-free Δ₀ formula is its
-- ambient reading at the underlying sets.  src/L/GCH/Frame.lagda.md
-- `AtTrans.read`, at the class L instead of a transitive set.
read : {n : ℕ} {φ : Formula (⊥* {ℓ-suc ℓ}) n} → Δ₀ φ → (δ : CS.S ^ n)
     → (δ ⊨ embed φ) ≡ (map fst δ ⊨ₚ φ)
read {n} {φ} dφ δ =
    AbsL.abs₀ (mapΔ₀ Empty.rec* dφ) δ
  ∙ embed-⊨ (hPropAlgebra (ℓ-suc ℓ)) 𝒮ᵥ {K = CS.S} fst φ (map fst δ)
  ∙ cong (λ ι → SemVᵃ.At._⊨_ (⊥* {ℓ-suc ℓ}) ι (map fst δ) φ)
         (funExt (λ b → Empty.rec* b))

-- The ordinality conjunct, read at the class carrier.  The pattern of
-- src/L/BoundedSubset.lagda.md `isOrdAt-out`, with the members
-- packaged into the carrier by `isL-trans`.
ord-out : (a p z : CS.S) → ⟨ (a ∷ p ∷ z ∷ []) ⊨ embed isOrd-at-p ⟩
        → IsOrd (fst p)
ord-out a p z h =
    ( λ {x} {y} y∈x x∈p → h .fst (dn p x x∈p) x∈p (dn (dn p x x∈p) y y∈x) y∈x )
  , ( λ x x∈p {y} {u} u∈y y∈x →
        h .snd (dn p x x∈p) x∈p (dn (dn p x x∈p) y y∈x) y∈x
          (dn (dn (dn p x x∈p) y y∈x) u u∈y) u∈y )
  where
  dn : (x : CS.S) (y : V ℓ) → ⟨ y ∈ fst x ⟩ → CS.S
  dn x y y∈x = y , isL-trans {x = fst x} {y = y} y∈x (snd x)

-- One bounded existential over the last slot, spent into a proposition.
unwrap : {n : ℕ} (φ : Formula CS.S (suc (suc n))) (γ : CS.S ^ (suc n))
         {P : hProp (ℓ-suc ℓ)}
       → ((x : CS.S) → ⟨ fst x ∈ fst (lookup (W3.lastFin {n}) γ) ⟩
            → ⟨ (x ∷ γ) ⊨ φ ⟩ → ⟨ P ⟩)
       → ⟨ γ ⊨ W3.wrap {n} φ ⟩ → ⟨ P ⟩
unwrap φ γ {P} k h = PT.rec (snd P) (λ { (x , xz , hx) → k x xz hx }) h

module Sound (lift : GraphLift) where
  open W3′

  -- THE THEOREM AT THE CLASS CARRIER, read there.  perf: the
  -- environment is spelled out at every step and never abbreviated;
  -- through a `where` name one conversion ran past 200 s
  -- (src/L/Coding/Sequence.lagda.md:162 records the same law).
  sound-L : (a p z : CS.S) → ⟨ (a ∷ p ∷ z ∷ []) ⊨ embed matrix₃′ ⟩
          → fst a ≡ Lset (fst p)
  sound-L a p z (ho , hφ) =
    go (subst (λ ψ → ⟨ (a ∷ p ∷ z ∷ []) ⊨ ψ ⟩)
              (Cnt.erase-inv three count-three) hφ)
    where
    ordp : IsOrd (fst p)
    ordp = ord-out a p z ho

    G : hProp (ℓ-suc ℓ)
    G = (fst a ≡ Lset (fst p)) , setIsSet (fst a) (Lset (fst p))

    go : ⟨ (a ∷ p ∷ z ∷ []) ⊨ three ⟩ → ⟨ G ⟩
    go =
      unwrap s4 (a ∷ p ∷ z ∷ []) {G} λ x11 m11 →
      unwrap s5 (x11 ∷ a ∷ p ∷ z ∷ []) {G} λ x10 m10 →
      unwrap s6 (x10 ∷ x11 ∷ a ∷ p ∷ z ∷ []) {G} λ x9 m9 →
      unwrap s7 (x9 ∷ x10 ∷ x11 ∷ a ∷ p ∷ z ∷ []) {G} λ x8 m8 →
      unwrap s8 (x8 ∷ x9 ∷ x10 ∷ x11 ∷ a ∷ p ∷ z ∷ []) {G} λ x7 m7 →
      unwrap s9 (x7 ∷ x8 ∷ x9 ∷ x10 ∷ x11 ∷ a ∷ p ∷ z ∷ []) {G} λ x6 m6 →
      unwrap s10 (x6 ∷ x7 ∷ x8 ∷ x9 ∷ x10 ∷ x11 ∷ a ∷ p ∷ z ∷ []) {G} λ x5 m5 →
      unwrap s11 (x5 ∷ x6 ∷ x7 ∷ x8 ∷ x9 ∷ x10 ∷ x11 ∷ a ∷ p ∷ z ∷ []) {G} λ x4 m4 →
      unwrap s12 (x4 ∷ x5 ∷ x6 ∷ x7 ∷ x8 ∷ x9 ∷ x10 ∷ x11 ∷ a ∷ p ∷ z ∷ []) {G} λ x3 m3 →
      unwrap s13 (x3 ∷ x4 ∷ x5 ∷ x6 ∷ x7 ∷ x8 ∷ x9 ∷ x10 ∷ x11 ∷ a ∷ p ∷ z ∷ []) {G} λ x2 m2 →
      unwrap s14 (x2 ∷ x3 ∷ x4 ∷ x5 ∷ x6 ∷ x7 ∷ x8 ∷ x9 ∷ x10 ∷ x11 ∷ a ∷ p ∷ z ∷ []) {G} λ x1 m1 →
      unwrap inner (x1 ∷ x2 ∷ x3 ∷ x4 ∷ x5 ∷ x6 ∷ x7 ∷ x8 ∷ x9 ∷ x10 ∷ x11 ∷ a ∷ p ∷ z ∷ []) {G}
        λ x0 m0 hm →
          Lset-only ww bb
            (x0 ∷ x1 ∷ x2 ∷ x3 ∷ x4 ∷ x5 ∷ x6 ∷ x7 ∷ x8 ∷ x9 ∷ x10 ∷ x11 ∷ a ∷ p ∷ z ∷ [])
            (lift (x0 ∷ x1 ∷ x2 ∷ x3 ∷ x4 ∷ x5 ∷ x6 ∷ x7 ∷ x8 ∷ x9 ∷ x10 ∷ x11 ∷ a ∷ p ∷ z ∷ [])
              (inner-out (x0 ∷ x1 ∷ x2 ∷ x3 ∷ x4 ∷ x5 ∷ x6 ∷ x7 ∷ x8 ∷ x9 ∷ x10 ∷ x11 ∷ a ∷ p ∷ z ∷ []) hm)
              (record { k0 = m0 ; k1 = m1 ; k2 = m2 ; k3 = m3
                      ; k4 = m4 ; k5 = m5 ; k6 = m6 ; k7 = m7
                      ; k8 = m8 ; k9 = m9 ; k10 = m10 ; k11 = m11 }))
            ordp

  -- THE THEOREM AT THE AMBIENT READING OF A CLASS-CARRIER TRIPLE.
  matrix₃′-sound : (a p z : CS.S)
                 → ⟨ (fst a ∷ fst p ∷ fst z ∷ []) ⊨ₚ matrix₃′ ⟩
                 → fst a ≡ Lset (fst p)
  matrix₃′-sound a p z h =
    sound-L a p z (subst ⟨_⟩ (sym (read Δ₀-matrix₃′ (a ∷ p ∷ z ∷ []))) h)

  -- The same at three ambient sets known to be constructible.
  sound-in-L : (a p z : S) → ⟨ isL a ⟩ → ⟨ isL p ⟩ → ⟨ isL z ⟩
             → ⟨ (a ∷ p ∷ z ∷ []) ⊨ₚ matrix₃′ ⟩ → a ≡ Lset p
  sound-in-L a p z la lp lz = matrix₃′-sound (a , la) (p , lp) (z , lz)

-- THE BRIEF'S TYPE, at the ambient carrier with no constructibility
-- premise.  Named, not inhabited: the report gives the reason.
SoundV : Type (ℓ-suc ℓ)
SoundV = (a p z : S) → ⟨ (a ∷ p ∷ z ∷ []) ⊨ₚ matrix₃′ ⟩ → a ≡ Lset p
```
