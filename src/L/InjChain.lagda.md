# Injections into L, composed and paired

```agda
{-# OPTIONS --cubical --safe --guardedness #-}

open import Base.Prelude
open import Base.Truth
open import Base.Classical using ( LEM )

module L.InjChain {ℓ : Level} (lem : LEM (ℓ-suc ℓ)) where

open import FOL.ZFStructure using ( module hPropStructure )
open import FOL.Syntax
  using ( Formula; con; _∧̇_; ∃̇_; ∃̇∈ )
import FOL.Absoluteness
open import V.Hierarchy {ℓ} using ( 𝒮ᵥ; ∈-irrefl )
open import V.Coding {ℓ} using ( pr; pr-inj )
open import V.Presentation {ℓ} using ( member; fiber; ↪-inj )
open import L.Constructible {ℓ}
  using ( 𝒮ʟ; isL; isL-trans; IsOrd; Lset; Lset-mono )
open import L.Ordinal {ℓ} using ( ω-ord; #∈ω; boundingOrd )
import L.Ordinal.SquareLaw {ℓ} lem as SQ
open SQ using ( sq; module FiniteBase; module InitialCore )
open import L.Stage {ℓ} lem using ( stage; stage-ord; stage-mem )
open import L.Axioms.Basic {ℓ} using ( LsetS )
open import L.Axioms.Full {ℓ} lem using ( hasSeparationL )
open import L.Coding.Model {ℓ}
  using ( prAtL; prAtL-adequate; prʟ; prʟ-fst
        ; svAt; svAt-in; svAt-out
        ; domAt; domAt-in; domAt-out; domAt-intro )
open import L.Coding.Injection {ℓ} lem
  using ( injAt; injAt-out; injAt-in; module Small )

import Cubical.Data.Empty as Empty
import Cubical.HITs.PropositionalTruncation as PT
open PT using ( ∣_∣₁; ∥_∥₁; squash₁ )
open import Cubical.Data.Nat using ( ℕ )
open import Cubical.Data.Sigma using ( _×_ )
import Cubical.Foundations.Equiv as Equiv
open Equiv using ( equivFun; invEq; retEq; _≃_ )
open import Cubical.Foundations.Univalence using ( pathToEquiv )
open import Cubical.HITs.CumulativeHierarchy.Base using ( V; _∈_; setIsSet )
open import Cubical.HITs.CumulativeHierarchy.Constructions
  using ( module InfinitySet )
module IS = InfinitySet {ℓ}
open IS using ( sucV; #_; ω )
open import Cubical.HITs.CumulativeHierarchy.Properties
  using ( ⟪_⟫; ⟪_⟫↪ )
open import Cubical.Functions.Logic using ( ⇔toPath; ∃[∶]-syntax )

open TruthAlgebra (hPropAlgebra (ℓ-suc ℓ))
open hPropStructure 𝒮ʟ using ( S; _∈ˢ_ )

module AbsL = FOL.Absoluteness.Single 𝒮ᵥ isL isL-trans
open AbsL using ( _^_ ) renaming ( _⊨ᵐ_ to _⊨_ )

open FiniteBase using ( ω-mem→numeral; toFin; toFin-inj; fromFin; fromFin-inj )
open FiniteBase using ( module AbstractChase )

-- ---------------------------------------------------------------------
-- ROW 5.  The pairing on ω, by the order route, zero arithmetic.
--
-- `InitialCore` (src/L/Ordinal/SquareLaw.lagda.md:703) gives the square
-- law at an initial ordinal from three hypotheses.  The base at ω is not
-- initial (`Init ω` needs `⟨ ω ∈ˢ ω ⟩`, refuted by `∈-irrefl`), so the
-- three hypotheses are supplied at ω directly.
-- ---------------------------------------------------------------------

-- Successor closure at ω: every member of ω is a numeral.
ω-limit : (γ : V ℓ) → ⟨ γ ∈ ω ⟩ → ⟨ sucV γ ∈ ω ⟩
ω-limit γ γ∈ω = PT.rec (snd (sucV γ ∈ ω)) go (ω-mem→numeral γ γ∈ω)
  where
  go : Σ[ n ∈ ℕ ] (γ ≡ # n) → ⟨ sucV γ ∈ ω ⟩
  go (n , p) = subst (λ w → ⟨ sucV w ∈ ω ⟩) (sym p) (#∈ω (suc n))

-- No member of ω contains ω.
ω∉β : (β : V ℓ) → ⟨ β ∈ ω ⟩ → ⟨ ω ∈ β ⟩ → Empty.⊥
ω∉β β β∈ω ω∈β = PT.rec Empty.isProp⊥ go (ω-mem→numeral β β∈ω)
  where
  go : Σ[ n ∈ ℕ ] (β ≡ # n) → Empty.⊥
  go (n , p) = ∈-irrefl ω (ω-ord .fst (subst (λ w → ⟨ ω ∈ w ⟩) p ω∈β) (#∈ω n))

-- The vacuous infinite-member clause, in the square form.
noinj²ω : (β : V ℓ) → IsOrd β → ⟨ β ∈ ω ⟩ → ⟨ ω ∈ β ⟩
        → (f : ⟪ ω ⟫ → ⟪ β ⟫ × ⟪ β ⟫)
        → ((m n : ⟪ ω ⟫) → f m ≡ f n → m ≡ n) → Empty.⊥
noinj²ω β oβ β∈ω ω∈β f finj = ω∉β β β∈ω ω∈β

-- The numeral-into-ω injection, without `ω ∈ ω`.
numeral-into-ω : (m : ℕ) → ⟪ # m ⟫ → ⟪ ω ⟫
numeral-into-ω m i = fiber ω (ω-ord .fst (member (# m) i) (#∈ω m)) .fst

numeral-into-ω-inj : (m : ℕ) (i₁ i₂ : ⟪ # m ⟫)
                   → numeral-into-ω m i₁ ≡ numeral-into-ω m i₂ → i₁ ≡ i₂
numeral-into-ω-inj m i₁ i₂ e = ↪-inj {a = # m}
  (sym (fiber ω (ω-ord .fst (member (# m) i₁) (#∈ω m)) .snd)
    ∙ cong (⟪ ω ⟫↪) e
    ∙ fiber ω (ω-ord .fst (member (# m) i₂) (#∈ω m)) .snd)

-- No injection of ω into a finite square.
no-inj-finite-ω : (n : ℕ) → (f : ⟪ ω ⟫ → ⟪ # n ⟫ × ⟪ # n ⟫)
                → ((x y : ⟪ ω ⟫) → f x ≡ f y → x ≡ y) → Empty.⊥
no-inj-finite-ω n f finj =
  AbstractChase.NoInj.no-inj
    (λ n → ⟪ # n ⟫)
    toFin toFin-inj
    fromFin fromFin-inj
    (⟪ ω ⟫)
    (numeral-into-ω)
    (numeral-into-ω-inj)
    n f finj

-- The finite-exclusion clause at ω.
finite-excl-ω : (β : V ℓ) → IsOrd β → ⟨ β ∈ ω ⟩
              → (f : ⟪ ω ⟫ → ⟪ β ⟫ × ⟪ β ⟫)
              → ((x y : ⟪ ω ⟫) → f x ≡ f y → x ≡ y) → Empty.⊥
finite-excl-ω β oβ β∈ω f finj =
  PT.rec Empty.isProp⊥ go (ω-mem→numeral β β∈ω)
  where
  go : Σ[ n ∈ ℕ ] (β ≡ # n) → Empty.⊥
  go (n , p) = no-inj-finite-ω n f' finj'
    where
    e : ⟪ β ⟫ × ⟪ β ⟫ ≃ ⟪ # n ⟫ × ⟪ # n ⟫
    e = pathToEquiv (cong (λ w → ⟪ w ⟫ × ⟪ w ⟫) p)
    f' : ⟪ ω ⟫ → ⟪ # n ⟫ × ⟪ # n ⟫
    f' x = equivFun e (f x)
    finj' : (x y : ⟪ ω ⟫) → f' x ≡ f' y → x ≡ y
    finj' x y e' = finj x y
      (sym (retEq e (f x)) ∙ cong (invEq e) e' ∙ retEq e (f y))

-- The base at ω: `InitialCore` instantiated, then the direct pairing.
module Coreω = InitialCore ω ω-ord ω-limit noinj²ω finite-excl-ω

open Coreω using ( colA; col∈α )

pairω : ⟪ ω ⟫ × ⟪ ω ⟫ → ⟪ ω ⟫
pairω p = fiber ω {x = colA p} (col∈α p) .fst

pairω-inj : (p q : ⟪ ω ⟫ × ⟪ ω ⟫) → pairω p ≡ pairω q → p ≡ q
pairω-inj p q e = SQ.col-inj ω ω-ord {p = p} {q = q}
  (sym (fiber ω {x = colA p} (col∈α p) .snd)
   ∙ cong (⟪ ω ⟫↪) e
   ∙ fiber ω {x = colA q} (col∈α q) .snd)

squareω : sq ω
squareω = pairω , pairω-inj

-- ---------------------------------------------------------------------
-- ROW 1.  The composition of two injection graphs, by separation.
--
-- `appC` reads a graph out of a CONSTANT (not the context), because
-- separation takes a formula of one place.  `compFo` is the composite
-- condition; `PairBound` builds the bound as a stage (no replacement);
-- `Comp` carves the composite and reads it back as an honest injection.
-- ---------------------------------------------------------------------

appC : ∀ {n} → S → Fin n → Fin n → Formula S n
appC F x y = ∃̇∈ (con F) (prAtL zero (suc x) (suc y))

appC-adequate : ∀ {n} (F : S) (x y : Fin n) (γ : S ^ n)
  → (γ ⊨ appC F x y)
  ≡ (pr (fst (lookup x γ)) (fst (lookup y γ)) ∈ fst F)
appC-adequate F x y γ = ⇔toPath fwd bwd
  where
  a = fst (lookup x γ)
  b = fst (lookup y γ)

  read : (z : S) → ⟨ (z ∷ γ) ⊨ prAtL zero (suc x) (suc y) ⟩ → fst z ≡ pr a b
  read z h = subst ⟨_⟩ (prAtL-adequate zero (suc x) (suc y) (z ∷ γ)) h

  fwd : ⟨ γ ⊨ appC F x y ⟩ → ⟨ pr a b ∈ fst F ⟩
  fwd = PT.rec (snd (pr a b ∈ fst F))
    (λ { (z , (z∈F , h)) → subst (λ w → ⟨ w ∈ fst F ⟩) (read z h) z∈F })

  bwd : ⟨ pr a b ∈ fst F ⟩ → ⟨ γ ⊨ appC F x y ⟩
  bwd h = ∣ zS , (h , subst ⟨_⟩
      (sym (prAtL-adequate zero (suc x) (suc y) (zS ∷ γ))) refl) ∣₁
    where
    zS : S
    zS = pr a b , isL-trans {x = fst F} {y = pr a b} h (F .snd)

-- The composite condition, as one formula of one place.
compFo : (F H : S) → Formula S 1
compFo F H = ∃̇ (∃̇ (∃̇ (
       prAtL (suc (suc (suc zero))) (suc (suc zero)) zero
    ∧̇ (appC F (suc (suc zero)) (suc zero)
    ∧̇  appC H (suc zero) zero))))

module CompFo (F H : S) where

  Chain : S → S → S → S → Type (ℓ-suc ℓ)
  Chain p x y z = (fst p ≡ pr (fst x) (fst z))
                × (⟨ pr (fst x) (fst y) ∈ fst F ⟩
                × ⟨ pr (fst y) (fst z) ∈ fst H ⟩)

  private
    ctx : (p x y z : S) → S ^ 4
    ctx p x y z = z ∷ y ∷ x ∷ p ∷ []

    atPr : (p x y z : S)
         → ((ctx p x y z) ⊨ prAtL (suc (suc (suc zero))) (suc (suc zero)) zero)
         ≡ ((fst p ≡ pr (fst x) (fst z)) , setIsSet (fst p) (pr (fst x) (fst z)))
    atPr p x y z =
      prAtL-adequate (suc (suc (suc zero))) (suc (suc zero)) zero (ctx p x y z)

    atF : (p x y z : S)
        → ((ctx p x y z) ⊨ appC F (suc (suc zero)) (suc zero))
        ≡ (pr (fst x) (fst y) ∈ fst F)
    atF p x y z = appC-adequate F (suc (suc zero)) (suc zero) (ctx p x y z)

    atH : (p x y z : S)
        → ((ctx p x y z) ⊨ appC H (suc zero) zero)
        ≡ (pr (fst y) (fst z) ∈ fst H)
    atH p x y z = appC-adequate H (suc zero) zero (ctx p x y z)

  out : (p : S) → ⟨ (p ∷ []) ⊨ compFo F H ⟩
      → ∥ Σ[ x ∈ S ] Σ[ y ∈ S ] Σ[ z ∈ S ] Chain p x y z ∥₁
  out p = PT.rec squash₁ (λ { (x , hx) →
          PT.rec squash₁ (λ { (y , hy) →
          PT.rec squash₁ (λ { (z , (hp , (hf , hh))) →
            ∣ x , y , z
            , ( subst ⟨_⟩ (atPr p x y z) hp
              , ( subst ⟨_⟩ (atF p x y z) hf
                , subst ⟨_⟩ (atH p x y z) hh ) ) ∣₁ }) hy }) hx })

  into : (p x y z : S) → Chain p x y z → ⟨ (p ∷ []) ⊨ compFo F H ⟩
  into p x y z (hp , (hf , hh)) =
    ∣ x , ∣ y , ∣ z
    , ( subst ⟨_⟩ (sym (atPr p x y z)) hp
      , ( subst ⟨_⟩ (sym (atF p x y z)) hf
        , subst ⟨_⟩ (sym (atH p x y z)) hh ) ) ∣₁ ∣₁ ∣₁

-- The bound.  No replacement builds it: the pairs form a family over a
-- SMALL index type, and `boundingOrd` bounds it; a stage is an element
-- of L.  `hasPowerL`'s own device, with the resizing dropped.
module PairBound (D C : S) where

  Ix : Type ℓ
  Ix = ⟪ fst D ⟫ × ⟪ fst C ⟫

  private
    toD : ⟪ fst D ⟫ → S
    toD m = ⟪ fst D ⟫↪ m
          , isL-trans {x = fst D} {y = ⟪ fst D ⟫↪ m} (member (fst D) m) (snd D)

    toC : ⟪ fst C ⟫ → S
    toC k = ⟪ fst C ⟫↪ k
          , isL-trans {x = fst C} {y = ⟪ fst C ⟫↪ k} (member (fst C) k) (snd C)

    pw : Ix → S
    pw (m , k) = prʟ (toD m) (toC k)

    stg : Ix → V ℓ
    stg i = stage (fst (pw i)) (snd (pw i))

    b : Σ[ β ∈ V ℓ ] (IsOrd β × ((i : Ix) → ⟨ stg i ∈ β ⟩))
    b = boundingOrd Ix stg (λ i → stage-ord (fst (pw i)) (snd (pw i)))

  -- Sealed: consumers want the bound as an atom.
  opaque
    β : V ℓ
    β = b .fst

    oβ : IsOrd β
    oβ = b .snd .fst

    bnd : S
    bnd = LsetS β oβ

    below : (x z : S) → ⟨ fst x ∈ fst D ⟩ → ⟨ fst z ∈ fst C ⟩
          → ⟨ pr (fst x) (fst z) ∈ fst bnd ⟩
    below x z mx mz = subst (λ w → ⟨ w ∈ Lset β ⟩) pa
      (Lset-mono {α = β} {β = stg i} (b .snd .snd i)
        (stage-mem (fst (pw i)) (snd (pw i))))
      where
      fD : Σ[ m ∈ ⟪ fst D ⟫ ] (⟪ fst D ⟫↪ m ≡ fst x)
      fD = fiber (fst D) mx
      fC : Σ[ k ∈ ⟪ fst C ⟫ ] (⟪ fst C ⟫↪ k ≡ fst z)
      fC = fiber (fst C) mz
      i : Ix
      i = fD .fst , fC .fst
      pa : fst (pw i) ≡ pr (fst x) (fst z)
      pa = prʟ-fst (toD (fD .fst)) (toC (fC .fst))
         ∙ cong₂ pr (fD .snd) (fC .snd)

-- THE COMPOSITE.  Two graphs, four conjuncts each, not one replacement.
module Comp (D E C F H : S)
            (svF : ⟨ (F ∷ D ∷ []) ⊨ svAt zero ⟩)
            (dmF : ⟨ (F ∷ D ∷ []) ⊨ domAt zero (suc zero) ⟩)
            (ijF : ⟨ (F ∷ D ∷ []) ⊨ injAt zero ⟩)
            (ranF : (x y : S) → ⟨ pr (fst x) (fst y) ∈ fst F ⟩
                  → ⟨ fst y ∈ fst E ⟩)
            (svH : ⟨ (H ∷ E ∷ []) ⊨ svAt zero ⟩)
            (dmH : ⟨ (H ∷ E ∷ []) ⊨ domAt zero (suc zero) ⟩)
            (ijH : ⟨ (H ∷ E ∷ []) ⊨ injAt zero ⟩)
            (ranH : (y z : S) → ⟨ pr (fst y) (fst z) ∈ fst H ⟩
                  → ⟨ fst z ∈ fst C ⟩) where

  private
    module PB = PairBound D C
    module CF = CompFo F H

    γF : S ^ 2
    γF = F ∷ D ∷ []

    γH : S ^ 2
    γH = H ∷ E ∷ []

  -- THE COMPOSITE, BY SEPARATION.
  opaque
    K : S
    K = fst (fst (hasSeparationL PB.bnd (compFo F H)))

    K-spec : (p : S) → (p ∈ˢ K)
           ≡ ((p ∈ˢ PB.bnd) ⊓ ((p ∷ []) ⊨ compFo F H))
    K-spec = snd (fst (hasSeparationL PB.bnd (compFo F H)))

  -- The two readings of membership.
  K-out : (x z : S) → ⟨ pr (fst x) (fst z) ∈ fst K ⟩
        → ∥ Σ[ y ∈ S ] (⟨ pr (fst x) (fst y) ∈ fst F ⟩
                      × ⟨ pr (fst y) (fst z) ∈ fst H ⟩) ∥₁
  K-out x z h = PT.rec squash₁ step (CF.out (prʟ x z) (snd (subst ⟨_⟩ (K-spec (prʟ x z)) h')))
    where
    h' : ⟨ prʟ x z ∈ˢ K ⟩
    h' = subst (λ w → ⟨ w ∈ fst K ⟩) (sym (prʟ-fst x z)) h

    step : (Σ[ u ∈ S ] Σ[ v ∈ S ] Σ[ w ∈ S ] CF.Chain (prʟ x z) u v w)
         → ∥ Σ[ y ∈ S ] (⟨ pr (fst x) (fst y) ∈ fst F ⟩
                       × ⟨ pr (fst y) (fst z) ∈ fst H ⟩) ∥₁
    step (u , v , w , (hp , (hf , hh))) = ∣ v , (hf' , hh') ∣₁
      where
      q : (fst x ≡ fst u) × (fst z ≡ fst w)
      q = pr-inj (sym (prʟ-fst x z) ∙ hp)
      hf' : ⟨ pr (fst x) (fst v) ∈ fst F ⟩
      hf' = subst (λ t → ⟨ pr t (fst v) ∈ fst F ⟩) (sym (fst q)) hf
      hh' : ⟨ pr (fst v) (fst z) ∈ fst H ⟩
      hh' = subst (λ t → ⟨ pr (fst v) t ∈ fst H ⟩) (sym (snd q)) hh

  K-in : (x y z : S) → ⟨ fst x ∈ fst D ⟩ → ⟨ fst z ∈ fst C ⟩
       → ⟨ pr (fst x) (fst y) ∈ fst F ⟩ → ⟨ pr (fst y) (fst z) ∈ fst H ⟩
       → ⟨ pr (fst x) (fst z) ∈ fst K ⟩
  K-in x y z mx mz hf hh =
    subst (λ w → ⟨ w ∈ fst K ⟩) (prʟ-fst x z)
      (subst ⟨_⟩ (sym (K-spec (prʟ x z)))
        ( subst (λ w → ⟨ w ∈ fst PB.bnd ⟩) (sym (prʟ-fst x z))
            (PB.below x z mx mz)
        , CF.into (prʟ x z) x y z (prʟ-fst x z , (hf , hh)) ))

  -- THE FOUR CONJUNCTS, for the composite.
  γK : S ^ 2
  γK = K ∷ D ∷ []

  svK : ⟨ γK ⊨ svAt zero ⟩
  svK = svAt-in zero γK (λ x y y' p q →
    PT.rec (setIsSet (fst y) (fst y'))
      (λ { (w , (hf , hh)) → PT.rec (setIsSet (fst y) (fst y'))
        (λ { (w' , (hf' , hh')) →
          svAt-out zero γH svH w y y' hh
            (subst (λ t → ⟨ pr t (fst y') ∈ fst H ⟩)
              (sym (svAt-out zero γF svF x w w' hf hf')) hh') })
        (K-out x y' q) })
      (K-out x y p))

  ijK : ⟨ γK ⊨ injAt zero ⟩
  ijK = injAt-in zero γK (λ y x x' p q →
    PT.rec (setIsSet (fst x) (fst x'))
      (λ { (w , (hf , hh)) → PT.rec (setIsSet (fst x) (fst x'))
        (λ { (w' , (hf' , hh')) →
          injAt-out zero γF ijF w x x' hf
            (subst (λ t → ⟨ pr (fst x') t ∈ fst F ⟩)
              (sym (injAt-out zero γH ijH y w w' hh hh')) hf') })
        (K-out x' y q) })
      (K-out x y p))

  dmK : ⟨ γK ⊨ domAt zero (suc zero) ⟩
  dmK = domAt-intro zero (suc zero) γK (λ x → fwd x , bwd x)
    where
    fwd : (x : S) → ⟨ ∃[ y ∶ S ] (pr (fst x) (fst y) ∈ fst K) ⟩
        → ⟨ fst x ∈ fst D ⟩
    fwd x = PT.rec (snd (fst x ∈ fst D))
      (λ { (y , p) → PT.rec (snd (fst x ∈ fst D))
        (λ { (w , (hf , _)) → domAt-out zero (suc zero) γF dmF x w hf })
        (K-out x y p) })

    bwd : (x : S) → ⟨ fst x ∈ fst D ⟩
        → ⟨ ∃[ y ∶ S ] (pr (fst x) (fst y) ∈ fst K) ⟩
    bwd x mx = PT.rec squash₁
      (λ { (w , hf) → PT.rec squash₁
        (λ { (z , hh) → ∣ z , K-in x w z mx (ranH w z hh) hf hh ∣₁ })
        (domAt-in zero (suc zero) γH dmH w (ranF x w hf)) })
      (domAt-in zero (suc zero) γF dmF x mx)

  ranK : (x z : S) → ⟨ pr (fst x) (fst z) ∈ fst K ⟩ → ⟨ fst z ∈ fst C ⟩
  ranK x z h = PT.rec (snd (fst z ∈ fst C))
    (λ { (w , (_ , hh)) → ranH w z hh }) (K-out x z h)

  -- The composite, read back as an honest function.  Sealed.
  private
    module Sm = Small K D C svK dmK ijK ranK

  opaque
    compFun : ⟪ fst D ⟫ → ⟪ fst C ⟫
    compFun = Sm.small

    compFun-inj : (m n : ⟪ fst D ⟫) → compFun m ≡ compFun n → m ≡ n
    compFun-inj = Sm.small-inj

-- ---------------------------------------------------------------------
-- ROW 3 (the inclusion j) lands here, in wave 3, once its probe is
-- re-sited.  It is not in this master.
-- ---------------------------------------------------------------------
```
