# The order type of a well-founded relation of L is an ordinal of L

```agda
{-# OPTIONS --cubical --safe --guardedness #-}

open import Base.Prelude
open import Base.Truth
open import Base.Classical using ( LEM )

module L.GCH.OrderType {ℓ : Level} (lem : LEM (ℓ-suc ℓ)) where

open import FOL.ZFStructure using ( module hPropStructure )
open import FOL.Syntax
  using ( Formula; var; con; _∈̇_; _≐_; _∧̇_; _∨̇_; _⇒̇_; ¬̇_; ∃̇_; ∀̇_ )
open import FOL.Manipulation.Renaming using ( renameFo; module Sat )
import FOL.Absoluteness
open import V.Hierarchy {ℓ} using ( 𝒮ᵥ; extensionalV; ∈-irrefl )
open import V.Presentation {ℓ} using ( member; fiber; ↪-inj )
open import V.Coding {ℓ} using ( pr; pr-inj )
open import L.Constructible {ℓ}
  using ( 𝒮ʟ; isL; isL-trans; IsOrd; Lset→isL; isTransV; isPropIsTransV )
open import L.Ordinal {ℓ} using ( suc-ord )
open import L.Ordinal.Stages {ℓ} lem using ( ord∈Lset-suc )
open import L.Recursion {ℓ} lem using ( Recursion; module Of; mereFunct )
open import L.Coding.Model {ℓ}
  using ( prAtL; prAtL-adequate; appAt; appAt-adequate; prʟ; prʟ-fst
        ; svAt; svAt-in; domAt; domAt-intro )
open import L.Coding.Injection {ℓ} lem using ( injAt; injAt-in )
open import L.Cardinal {ℓ} lem using ( InjCode )

open import Cubical.Data.Sigma using ( _×_; Σ≡Prop )
open import Cubical.Foundations.Prelude using ( subst2 )
open import Cubical.Data.Sum using ( _⊎_; inl; inr )
open import Cubical.Foundations.HLevels using ( isProp×; isPropΠ; isPropΣ; isSetΣSndProp )
open import Cubical.Functions.Logic using ( ⇔toPath; ∃[∶]-syntax )
open import Cubical.HITs.CumulativeHierarchy.Base using ( V; _∈_; sett; setIsSet )
open import Cubical.HITs.CumulativeHierarchy.Properties
  using ( ⟪_⟫; ⟪_⟫↪; _∈ₛ_; ∈∈ₛ )
open import Cubical.HITs.CumulativeHierarchy.Constructions using ( module InfinitySet )
open InfinitySet {ℓ} using ( sucV )
open import Cubical.Induction.WellFounded using ( WellFounded; module WFI )
import Cubical.Data.Empty as Empty
import Cubical.HITs.PropositionalTruncation as PT
open PT using ( ∥_∥₁; ∣_∣₁; squash₁ )

open TruthAlgebra (hPropAlgebra (ℓ-suc ℓ))
open hPropStructure 𝒮ʟ using ( S; _∈ˢ_ )

module AbsL = FOL.Absoluteness.Single 𝒮ᵥ isL isL-trans using ( _^_; _⊨ᵐ_ )
open AbsL using ( _^_ ) renaming ( _⊨ᵐ_ to _⊨_ )

-- Renaming, read at the same satisfaction as `_⊨_` (as L.Axioms.Full does).
module Ren = Sat (hPropAlgebra (ℓ-suc ℓ)) 𝒮ʟ id using ( Agrees; ⊨-rename )

isSetS : isSet S
isSetS = isSetΣSndProp setIsSet (λ v → snd (isL v))

-- "The pair (x, y) is a member of F", the shape every clause below reads.
Holds : S → S → S → Type (ℓ-suc ℓ)
Holds F x y = ⟨ pr (fst x) (fst y) ∈ fst F ⟩

-- =====================================================================
-- SECTION 1.  THE SETTING, AND THE HOST-LEVEL COLLAPSE.
--
--   D is a set of L, R is a set of L of pairs of members of D, and the
--   relation "pr x y ∈ R" is well-founded and transitive on the members
--   of D.  `col` is the Mostowski collapse, by well-founded recursion as
--   `Hartogs.Col.col` (src/L/CardinalAbove.lagda.md); `ot` its image.
-- =====================================================================

module Collapse (D R : S)
                (Rsub : (y x : S) → Holds R y x
                      → ⟨ fst y ∈ fst D ⟩ × ⟨ fst x ∈ fst D ⟩) where

  Mem : S → Type (ℓ-suc ℓ)
  Mem x = ⟨ fst x ∈ fst D ⟩

  isPropMem : (x : S) → isProp (Mem x)
  isPropMem x = snd (fst x ∈ fst D)

  -- The members of D, as the small type that presents D.  The index of
  -- a `sett` must be small, so the relation is read through the small
  -- membership `_∈ₛ_` (as `Hartogs` reads a Bool-valued one).
  Dom : Type ℓ
  Dom = ⟪ fst D ⟫

  ↪ : Dom → V ℓ
  ↪ = ⟪ fst D ⟫↪

  up : Dom → S
  up m = ↪ m , isL-trans {x = fst D} {y = ↪ m} (member (fst D) m) (snd D)

  up-mem : (m : Dom) → Mem (up m)
  up-mem m = member (fst D) m

  Dom≡ : {a b : Dom} → ↪ a ≡ ↪ b → a ≡ b
  Dom≡ {a} {b} e = ↪-inj {a = fst D} {m = a} {n = b} e

  toDom : (x : S) → Mem x → Dom
  toDom x mx = fst (fiber (fst D) mx)

  toDom-val : (x : S) (mx : Mem x) → ↪ (toDom x mx) ≡ fst x
  toDom-val x mx = snd (fiber (fst D) mx)

  -- Sealed: `_∈ₛ_` unfolds the presentation, and an unsealed relation
  -- exhausts an 8g heap at the first check.
  opaque
    _≺_ : Dom → Dom → Type ℓ
    a ≺ b = ⟨ pr (↪ a) (↪ b) ∈ₛ fst R ⟩

    isProp≺ : (a b : Dom) → isProp (a ≺ b)
    isProp≺ a b = snd (pr (↪ a) (↪ b) ∈ₛ fst R)

    ≺-in : (a b : Dom) → Holds R (up a) (up b) → a ≺ b
    ≺-in a b = ∈∈ₛ {a = pr (↪ a) (↪ b)} {b = fst R} .fst

    ≺-out : (a b : Dom) → a ≺ b → Holds R (up a) (up b)
    ≺-out a b = ∈∈ₛ {a = pr (↪ a) (↪ b)} {b = fst R} .snd

  module Col (wf : WellFounded _≺_)
             (≺-trans : {a b c : Dom} → a ≺ b → b ≺ c → a ≺ c) where

    module W = WFI wf using ( induction; induction-compute )

    colStep : (p : Dom) → (∀ r → r ≺ p → V ℓ) → V ℓ
    colStep p rec = sett (Σ[ r ∈ Dom ] (r ≺ p)) (λ z → rec (fst z) (snd z))

    opaque
      col : Dom → V ℓ
      col = W.induction {P = λ _ → V ℓ} colStep

      col-eq : (p : Dom)
             → col p ≡ sett (Σ[ r ∈ Dom ] (r ≺ p)) (λ z → col (fst z))
      col-eq = W.induction-compute colStep

    col-in : (p r : Dom) → r ≺ p → ⟨ col r ∈ col p ⟩
    col-in p r rp =
      subst (λ v → ⟨ col r ∈ v ⟩) (sym (col-eq p)) ∣ (r , rp) , refl ∣₁

    col-out : (p : Dom) (b : V ℓ) → ⟨ b ∈ col p ⟩
            → ∥ Σ[ r ∈ Dom ] ((r ≺ p) × (col r ≡ b)) ∥₁
    col-out p b b∈ =
      PT.map (λ z → fst (fst z) , snd (fst z) , snd z)
        (subst (λ v → ⟨ b ∈ v ⟩) (col-eq p) b∈)

    col-ord : (p : Dom) → IsOrd (col p)
    col-ord = W.induction {P = λ p → IsOrd (col p)} ih
      where
      ih : (p : Dom) → (∀ r → r ≺ p → IsOrd (col r)) → IsOrd (col p)
      ih p rec = tr , mem
        where
        mem : (x : V ℓ) → ⟨ x ∈ col p ⟩ → isTransV x
        mem x x∈ = PT.rec (isPropIsTransV x)
          (λ z → subst isTransV (snd (snd z)) (rec (fst z) (fst (snd z)) .fst))
          (col-out p x x∈)
        tr : isTransV (col p)
        tr {x} {y} y∈x x∈col = PT.rec (snd (y ∈ col p)) outer (col-out p x x∈col)
          where
          outer : Σ[ r ∈ Dom ] ((r ≺ p) × (col r ≡ x)) → ⟨ y ∈ col p ⟩
          outer (r , rp , e) =
            PT.rec (snd (y ∈ col p)) inner
              (col-out r y (subst (λ v → ⟨ y ∈ v ⟩) (sym e) y∈x))
            where
            inner : Σ[ s ∈ Dom ] ((s ≺ r) × (col s ≡ y)) → ⟨ y ∈ col p ⟩
            inner (s , sr , e2) =
              subst (λ v → ⟨ v ∈ col p ⟩) e2 (col-in p s (≺-trans sr rp))

    -- An ordinal is constructible: it appears at the stage after itself.
    -- Sealed: a proof of a proposition, and unsealed it is normalised at
    -- every conversion of a `colʟ` pair (measured: one transport of the
    -- graph formula along an index equation exceeds 100 s).
    opaque
      col-isL : (p : Dom) → ⟨ isL (col p) ⟩
      col-isL p = Lset→isL (sucV (col p)) (suc-ord (col-ord p)) (col p)
                    (ord∈Lset-suc (col p) (col-ord p))

    colʟ : Dom → S
    colʟ p = col p , col-isL p

    -- The order type, as a bare image.
    ot : V ℓ
    ot = sett Dom col

    ot-in : (p : Dom) → ⟨ col p ∈ ot ⟩
    ot-in p = ∣ p , refl ∣₁

    ot-ord : IsOrd ot
    ot-ord = tr , mem
      where
      mem : (x : V ℓ) → ⟨ x ∈ ot ⟩ → isTransV x
      mem x x∈ = PT.rec (isPropIsTransV x)
        (λ z → subst isTransV (snd z) (col-ord (fst z) .fst)) x∈
      tr : isTransV ot
      tr {x} {y} y∈x x∈ot = PT.rec (snd (y ∈ ot)) outer x∈ot
        where
        outer : Σ[ p ∈ Dom ] (col p ≡ x) → ⟨ y ∈ ot ⟩
        outer (p , e) =
          PT.rec (snd (y ∈ ot))
            (λ z → subst (λ v → ⟨ v ∈ ot ⟩) (snd (snd z)) (ot-in (fst z)))
            (col-out p y (subst (λ v → ⟨ y ∈ v ⟩) (sym e) y∈x))
```

<!--en-->
## The formulas
<!--zh-->
## 诸公式
<!--/-->

```agda
-- =====================================================================
-- SECTION 2.  THE OBJECT-LANGUAGE FORMULAS, AND HOW TO READ THEM.
--
--   A set F of pairs is CORRECT for R when every entry (x, v) of F is
--   complete (every R-predecessor of x has an entry) and its value is
--   right relative to F (v is exactly the set of values recorded at the
--   R-predecessors of x).  No domain clause: a correct set may record
--   more than a segment, and section 3 shows every entry is the collapse.
--
--   Every formula is sealed with its two reading lemmas inside the seal,
--   so a later renaming or replacement never unfolds it.
-- =====================================================================

-- Host-level readings.
Complete : S → S → S → Type (ℓ-suc ℓ)
Complete F R x = (y : S) → Holds R y x → ∥ Σ[ u ∈ S ] Holds F y u ∥₁

Src : S → S → S → S → Type (ℓ-suc ℓ)
Src F R x w = ∥ Σ[ y ∈ S ] (Holds R y x × Holds F y w) ∥₁

ValueIs : S → S → S → S → Type (ℓ-suc ℓ)
ValueIs F R x v = (w : S) → (⟨ fst w ∈ fst v ⟩ → Src F R x w)
                          × (Src F R x w → ⟨ fst w ∈ fst v ⟩)

Correct : S → S → Type (ℓ-suc ℓ)
Correct F R = (x v : S) → Holds F x v → Complete F R x × ValueIs F R x v

-- "Every R-predecessor y of x has an entry in f."  Inside: y is 0, then
-- u is 0 and y is 1.
opaque
  completeAt : ∀ {n} → Fin n → Fin n → Fin n → Formula S n
  completeAt f r x =
    ∀̇ ( appAt (suc r) zero (suc x)
      ⇒̇ ∃̇ (appAt (suc (suc f)) (suc zero) zero) )

  complete-out : ∀ {n} (f r x : Fin n) (γ : S ^ n)
               → ⟨ γ ⊨ completeAt f r x ⟩
               → Complete (lookup f γ) (lookup r γ) (lookup x γ)
  complete-out f r x γ h y p = PT.map
    (λ { (u , q) → u , subst ⟨_⟩ (appAt-adequate (suc (suc f)) (suc zero) zero (u ∷ y ∷ γ)) q })
    (h y (subst ⟨_⟩ (sym (appAt-adequate (suc r) zero (suc x) (y ∷ γ))) p))

  complete-in : ∀ {n} (f r x : Fin n) (γ : S ^ n)
              → Complete (lookup f γ) (lookup r γ) (lookup x γ)
              → ⟨ γ ⊨ completeAt f r x ⟩
  complete-in f r x γ h y p = PT.map
    (λ { (u , q) → u , subst ⟨_⟩ (sym (appAt-adequate (suc (suc f)) (suc zero) zero (u ∷ y ∷ γ))) q })
    (h y (subst ⟨_⟩ (appAt-adequate (suc r) zero (suc x) (y ∷ γ)) p))

-- "w is in v iff w is recorded in f at some R-predecessor of x."
-- Inside: w is 0; then y is 0 and w is 1.
opaque
  srcAt : ∀ {n} → Fin n → Fin n → Fin n → Fin n → Formula S n
  srcAt f r x w = ∃̇ ( appAt (suc r) zero (suc x) ∧̇ appAt (suc f) zero (suc w) )

  src-out : ∀ {n} (f r x w : Fin n) (γ : S ^ n)
          → ⟨ γ ⊨ srcAt f r x w ⟩
          → Src (lookup f γ) (lookup r γ) (lookup x γ) (lookup w γ)
  src-out f r x w γ = PT.map (λ { (y , (p , q)) → y
    , ( subst ⟨_⟩ (appAt-adequate (suc r) zero (suc x) (y ∷ γ)) p
      , subst ⟨_⟩ (appAt-adequate (suc f) zero (suc w) (y ∷ γ)) q ) })

  src-in : ∀ {n} (f r x w : Fin n) (γ : S ^ n)
         → Src (lookup f γ) (lookup r γ) (lookup x γ) (lookup w γ)
         → ⟨ γ ⊨ srcAt f r x w ⟩
  src-in f r x w γ = PT.map (λ { (y , (p , q)) → y
    , ( subst ⟨_⟩ (sym (appAt-adequate (suc r) zero (suc x) (y ∷ γ))) p
      , subst ⟨_⟩ (sym (appAt-adequate (suc f) zero (suc w) (y ∷ γ))) q ) })

opaque
  unfolding srcAt
  valueAt : ∀ {n} → Fin n → Fin n → Fin n → Fin n → Formula S n
  valueAt f r x v =
    ∀̇ ( ((var zero ∈̇ var (suc v)) ⇒̇ srcAt (suc f) (suc r) (suc x) zero)
      ∧̇ (srcAt (suc f) (suc r) (suc x) zero ⇒̇ (var zero ∈̇ var (suc v))) )

  value-out : ∀ {n} (f r x v : Fin n) (γ : S ^ n)
            → ⟨ γ ⊨ valueAt f r x v ⟩
            → ValueIs (lookup f γ) (lookup r γ) (lookup x γ) (lookup v γ)
  value-out f r x v γ h w =
      (λ w∈ → src-out (suc f) (suc r) (suc x) zero (w ∷ γ) (h w .fst w∈))
    , (λ s → h w .snd (src-in (suc f) (suc r) (suc x) zero (w ∷ γ) s))

  value-in : ∀ {n} (f r x v : Fin n) (γ : S ^ n)
           → ValueIs (lookup f γ) (lookup r γ) (lookup x γ) (lookup v γ)
           → ⟨ γ ⊨ valueAt f r x v ⟩
  value-in f r x v γ h w =
      (λ w∈ → src-in (suc f) (suc r) (suc x) zero (w ∷ γ) (h w .fst w∈))
    , (λ s → h w .snd (src-out (suc f) (suc r) (suc x) zero (w ∷ γ) s))

-- Inside: x is 1 and v is 0.
opaque
  unfolding completeAt valueAt
  correctAt : ∀ {n} → Fin n → Fin n → Formula S n
  correctAt f r =
    ∀̇ (∀̇ ( appAt (suc (suc f)) (suc zero) zero
          ⇒̇ ( completeAt (suc (suc f)) (suc (suc r)) (suc zero)
            ∧̇ valueAt (suc (suc f)) (suc (suc r)) (suc zero) zero ) ))

  correct-out : ∀ {n} (f r : Fin n) (γ : S ^ n)
              → ⟨ γ ⊨ correctAt f r ⟩ → Correct (lookup f γ) (lookup r γ)
  correct-out f r γ h x v p =
    let (c , w) = h x v (subst ⟨_⟩ (sym (appAt-adequate (suc (suc f)) (suc zero) zero (v ∷ x ∷ γ))) p)
    in complete-out (suc (suc f)) (suc (suc r)) (suc zero) (v ∷ x ∷ γ) c
     , value-out (suc (suc f)) (suc (suc r)) (suc zero) zero (v ∷ x ∷ γ) w

  correct-in : ∀ {n} (f r : Fin n) (γ : S ^ n)
             → Correct (lookup f γ) (lookup r γ) → ⟨ γ ⊨ correctAt f r ⟩
  correct-in f r γ h x v p =
    let (c , w) = h x v (subst ⟨_⟩ (appAt-adequate (suc (suc f)) (suc zero) zero (v ∷ x ∷ γ)) p)
    in complete-in (suc (suc f)) (suc (suc r)) (suc zero) (v ∷ x ∷ γ) c
     , value-in (suc (suc f)) (suc (suc r)) (suc zero) zero (v ∷ x ∷ γ) w

-- THE GRAPH FORMULA, over (z ∷ p ∷ []): "z is recorded at p by some set
-- correct for R".  Inside: r is 0, z is 1, p is 2; then f is 0, r is 1,
-- z is 2, p is 3.  R enters as a constant, bound to a variable.
module ColFo (R : S) where

  opaque
    unfolding correctAt
    colFo : Formula S 2
    colFo = ∃̇ ( (var zero ≐ con R)
              ∧̇ ∃̇ ( correctAt zero (suc zero)
                   ∧̇ appAt zero (suc (suc (suc zero))) (suc (suc zero)) ) )

    colFo-out : (z p : S) → ⟨ (z ∷ p ∷ []) ⊨ colFo ⟩
              → ∥ Σ[ F ∈ S ] (Correct F R × Holds F p z) ∥₁
    colFo-out z p = PT.rec squash₁ (λ { (r , (er , hf)) → PT.map
      (λ { (F , (hc , ha)) → F
        , ( subst (Correct F) (Σ≡Prop (λ v → snd (isL v)) {u = r} {v = R} er)
              (correct-out zero (suc zero) (F ∷ r ∷ z ∷ p ∷ []) hc)
          , subst ⟨_⟩ (appAt-adequate zero (suc (suc (suc zero))) (suc (suc zero)) (F ∷ r ∷ z ∷ p ∷ [])) ha ) })
      hf })

    colFo-in : (z p F : S) → Correct F R → Holds F p z
             → ⟨ (z ∷ p ∷ []) ⊨ colFo ⟩
    colFo-in z p F hc hp = ∣ R , (refl , ∣ F
      , ( correct-in zero (suc zero) (F ∷ R ∷ z ∷ p ∷ []) hc
        , subst ⟨_⟩ (sym (appAt-adequate zero (suc (suc (suc zero))) (suc (suc zero)) (F ∷ R ∷ z ∷ p ∷ []))) hp ) ∣₁) ∣₁

-- The pair form of a graph, over (e ∷ p ∷ []): "e is the pair of p and
-- some z with φ z p" (the shape src/L/Hierarchy.lagda.md pays for the
-- hierarchy).  Inside the binder z is 0, e is 1, p is 2.
module PairFo (φ : Formula S 2) where

  ρ : Fin 2 → Fin 3
  ρ zero       = zero
  ρ (suc zero) = suc (suc zero)

  opaque
    pairFo : Formula S 2
    pairFo = ∃̇ (prAtL (suc zero) (suc (suc zero)) zero ∧̇ renameFo ρ φ)

    private
      ag : (z e p : S) → Ren.Agrees ρ (z ∷ e ∷ p ∷ []) (z ∷ p ∷ [])
      ag z e p zero       = refl
      ag z e p (suc zero) = refl

      at : (z e p : S)
         → ⟨ (z ∷ e ∷ p ∷ []) ⊨ prAtL (suc zero) (suc (suc zero)) zero ⟩
         ≡ (fst e ≡ pr (fst p) (fst z))
      at z e p = cong ⟨_⟩ (prAtL-adequate (suc zero) (suc (suc zero)) zero (z ∷ e ∷ p ∷ []))

      gr : (z e p : S)
         → ⟨ (z ∷ e ∷ p ∷ []) ⊨ renameFo ρ φ ⟩ ≡ ⟨ (z ∷ p ∷ []) ⊨ φ ⟩
      gr z e p = cong ⟨_⟩ (Ren.⊨-rename ρ φ (z ∷ e ∷ p ∷ []) (z ∷ p ∷ []) (ag z e p))

    pair-out : (e p : S) → ⟨ (e ∷ p ∷ []) ⊨ pairFo ⟩
             → ∥ Σ[ z ∈ S ] ((fst e ≡ pr (fst p) (fst z)) × ⟨ (z ∷ p ∷ []) ⊨ φ ⟩) ∥₁
    pair-out e p = PT.map (λ { (z , (q , h)) →
      z , (transport (at z e p) q , transport (gr z e p) h) })

    pair-in : (e p z : S) → fst e ≡ pr (fst p) (fst z) → ⟨ (z ∷ p ∷ []) ⊨ φ ⟩
            → ⟨ (e ∷ p ∷ []) ⊨ pairFo ⟩
    pair-in e p z q h = ∣ z , (transport (sym (at z e p)) q , transport (sym (gr z e p)) h) ∣₁
```

<!--en-->
## Uniqueness, existence, and the tables
<!--zh-->
## 唯一性、存在性与诸表
<!--/-->

```agda
-- =====================================================================
-- SECTION 3.  EVERY CORRECT SET RECORDS THE COLLAPSE, AND ONE EXISTS.
--
--   Uniqueness is one well-founded induction on the entry's index.
--   Existence at a is one replacement over D: the set of the pairs
--   (q, col q) for q R a, with the pair (a, col a) as the value at every
--   other q, so no separation and no union is needed.  Its graph is
--   decided by `lem`, inside `mereFunct`, where a proposition is proved.
-- =====================================================================

module Internal (D R : S)
                (Rsub : (y x : S) → Holds R y x
                      → ⟨ fst y ∈ fst D ⟩ × ⟨ fst x ∈ fst D ⟩) where

  open Collapse D R Rsub public
  module CF = ColFo R using ( colFo; colFo-in; colFo-out )
  module PF = PairFo CF.colFo using ( pair-in; pair-out; pairFo )

  up-toDom : (q : S) (mq : Mem q) → up (toDom q mq) ≡ q
  up-toDom q mq = Σ≡Prop (λ v → snd (isL v)) (toDom-val q mq)

  -- Transport of the graph formula along an equation of the index.
  colFo-at : (v : S) {x y : S} → x ≡ y
           → ⟨ (v ∷ x ∷ []) ⊨ CF.colFo ⟩ → ⟨ (v ∷ y ∷ []) ⊨ CF.colFo ⟩
  colFo-at v e = subst (λ t → ⟨ (v ∷ t ∷ []) ⊨ CF.colFo ⟩) e

  module Graph (wf : WellFounded _≺_)
               (≺-trans : {a b c : Dom} → a ≺ b → b ≺ c → a ≺ c) where

    open Col wf ≺-trans public

    ≺-irrefl : (a : Dom) → a ≺ a → Empty.⊥
    ≺-irrefl = W.induction {P = λ a → a ≺ a → Empty.⊥} (λ a rec h → rec a h h)

    -- UNIQUENESS: a value a correct set records at a member of D is the
    -- collapse there.
    correct-val : (F : S) → Correct F R → (a : Dom) (v : S)
                → Holds F (up a) v → fst v ≡ col a
    correct-val F hc = W.induction {P = λ a → (v : S) → Holds F (up a) v → fst v ≡ col a} go
      where
      go : (a : Dom) → ((b : Dom) → b ≺ a → (v : S) → Holds F (up b) v → fst v ≡ col b)
         → (v : S) → Holds F (up a) v → fst v ≡ col a
      go a IH v hv = extensionalV {a = fst v} {b = col a} (λ w → ⇔toPath (fwd w) (bwd w))
        where
        cmp : Complete F R (up a)
        cmp = hc (up a) v hv .fst
        val : ValueIs F R (up a) v
        val = hc (up a) v hv .snd

        fwd : (w : V ℓ) → ⟨ w ∈ fst v ⟩ → ⟨ w ∈ col a ⟩
        fwd w w∈ = PT.rec (snd (w ∈ col a)) read (val wS .fst w∈)
          where
          wS : S
          wS = w , isL-trans {x = fst v} {y = w} w∈ (snd v)
          read : Σ[ y ∈ S ] (Holds R y (up a) × Holds F y wS) → ⟨ w ∈ col a ⟩
          read (y , (ry , fy)) = subst (λ t → ⟨ t ∈ col a ⟩) (sym e) (col-in a b b≺a)
            where
            my : Mem y
            my = Rsub y (up a) ry .fst
            b : Dom
            b = toDom y my
            b≺a : b ≺ a
            b≺a = ≺-in b a (subst (λ t → ⟨ pr t (↪ a) ∈ fst R ⟩) (sym (toDom-val y my)) ry)
            e : w ≡ col b
            e = IH b b≺a wS (subst (λ t → ⟨ pr t w ∈ fst F ⟩) (sym (toDom-val y my)) fy)

        bwd : (w : V ℓ) → ⟨ w ∈ col a ⟩ → ⟨ w ∈ fst v ⟩
        bwd w w∈ = PT.rec (snd (w ∈ fst v)) read (col-out a w w∈)
          where
          wS : S
          wS = w , isL-trans {x = col a} {y = w} w∈ (col-isL a)
          read : Σ[ r ∈ Dom ] ((r ≺ a) × (col r ≡ w)) → ⟨ w ∈ fst v ⟩
          read (r , (ra , e)) = PT.rec (snd (w ∈ fst v)) inner (cmp (up r) (≺-out r a ra))
            where
            inner : Σ[ u ∈ S ] Holds F (up r) u → ⟨ w ∈ fst v ⟩
            inner (u , fu) = val wS .snd
              ∣ up r , (≺-out r a ra , subst (λ t → ⟨ pr (↪ r) t ∈ fst F ⟩) (IH r ra u fu ∙ e) fu) ∣₁

    -- The graph formula, read at a member of D given as an element.
    colFo-val : (q : S) (mq : Mem q) (v : S) → ⟨ (v ∷ q ∷ []) ⊨ CF.colFo ⟩
              → fst v ≡ col (toDom q mq)
    colFo-val q mq v h = PT.rec (setIsSet (fst v) (col (toDom q mq)))
      (λ { (F , (hc , hv)) → correct-val F hc (toDom q mq) v
             (subst (λ t → ⟨ pr t (fst v) ∈ fst F ⟩) (sym (toDom-val q mq)) hv) })
      (CF.colFo-out v q h)

    -- EXISTENCE, at one a, from the graph formula below a.
    module Approx (a : Dom)
                  (IH : (b : Dom) → b ≺ a → ⟨ (colʟ b ∷ up b ∷ []) ⊨ CF.colFo ⟩) where

      -- The default entry.
      ea : S
      ea = prʟ (up a) (colʟ a)

      ρ₂ : Fin 2 → Fin 4
      ρ₂ zero       = suc (suc zero)
      ρ₂ (suc zero) = suc (suc (suc zero))

      -- The graph, read: at q R a the pair of q and the value the graph
      -- formula gives there; elsewhere the default entry.
      Body : S → S → Type (ℓ-suc ℓ)
      Body z q =
          (Holds R q (up a)
             × ∥ Σ[ v ∈ S ] ((fst z ≡ pr (fst q) (fst v)) × ⟨ (v ∷ q ∷ []) ⊨ CF.colFo ⟩) ∥₁)
        ⊎ ((Holds R q (up a) → Empty.⊥) × (fst z ≡ fst ea))

      -- Inside: p is 0, r is 1, z is 2, q is 3.
      opaque
        body : Formula S 4
        body = ( appAt (suc zero) (suc (suc (suc zero))) zero ∧̇ renameFo ρ₂ PF.pairFo )
             ∨̇ ( (¬̇ appAt (suc zero) (suc (suc (suc zero))) zero)
               ∧̇ (var (suc (suc zero)) ≐ con ea) )

        ψ : Formula S 2
        ψ = ∀̇ ( (var zero ≐ con R) ⇒̇ ∀̇ ( (var zero ≐ con (up a)) ⇒̇ body ) )

        private
          env : S → S → S ^ 4
          env z q = up a ∷ R ∷ z ∷ q ∷ []

          ag : (z q : S) → Ren.Agrees ρ₂ (env z q) (z ∷ q ∷ [])
          ag z q zero       = refl
          ag z q (suc zero) = refl

          at : (z q : S)
             → ⟨ env z q ⊨ appAt (suc zero) (suc (suc (suc zero))) zero ⟩ ≡ Holds R q (up a)
          at z q = cong ⟨_⟩ (appAt-adequate (suc zero) (suc (suc (suc zero))) zero (env z q))

          gr : (z q : S)
             → ⟨ env z q ⊨ renameFo ρ₂ PF.pairFo ⟩ ≡ ⟨ (z ∷ q ∷ []) ⊨ PF.pairFo ⟩
          gr z q = cong ⟨_⟩ (Ren.⊨-rename ρ₂ PF.pairFo (env z q) (z ∷ q ∷ []) (ag z q))

        ψ-out : (z q : S) → ⟨ (z ∷ q ∷ []) ⊨ ψ ⟩ → ∥ Body z q ∥₁
        ψ-out z q h = PT.map
          (λ { (inl (h1 , h2)) → inl (transport (at z q) h1 , PF.pair-out z q (transport (gr z q) h2))
             ; (inr (h1 , h2)) → inr ((λ k → h1 (transport (sym (at z q)) k)) , h2) })
          (h R refl (up a) refl)

        ψ-in : (z q : S) → Body z q → ⟨ (z ∷ q ∷ []) ⊨ ψ ⟩
        ψ-in z q b r er p ep =
          subst2 (λ p' r' → ⟨ (p' ∷ r' ∷ z ∷ q ∷ []) ⊨ body ⟩)
            (sym (Σ≡Prop (λ v → snd (isL v)) {u = p} {v = up a} ep))
            (sym (Σ≡Prop (λ v → snd (isL v)) {u = r} {v = R} er))
            (put b)
          where
          put : Body z q → ⟨ env z q ⊨ body ⟩
          put (inl (h1 , hv)) = PT.rec (snd (env z q ⊨ body))
            (λ { (v , (e , hc)) → ∣ inl ( transport (sym (at z q)) h1
                                         , transport (sym (gr z q)) (PF.pair-in z q v e hc) ) ∣₁ })
            hv
          put (inr (h1 , e)) = ∣ inr ((λ k → h1 (transport (at z q) k)) , e) ∣₁

      private
        b≺a-of : (q : S) (mq : Mem q) → Holds R q (up a) → toDom q mq ≺ a
        b≺a-of q mq h = ≺-in (toDom q mq) a
          (subst (λ t → ⟨ pr t (↪ a) ∈ fst R ⟩) (sym (toDom-val q mq)) h)

        IHq : (q : S) (mq : Mem q) → toDom q mq ≺ a
            → ⟨ (colʟ (toDom q mq) ∷ q ∷ []) ⊨ CF.colFo ⟩
        IHq q mq k = colFo-at (colʟ (toDom q mq)) (up-toDom q mq) (IH (toDom q mq) k)

        fc : (q : S) → ⟨ q ∈ˢ D ⟩ → isContr (Σ[ z ∈ S ] ⟨ (z ∷ q ∷ []) ⊨ ψ ⟩)
        fc q mq = mereFunct ψ q (decide (lem (pr (fst q) (↪ a) ∈ fst R)))
          where
          b : Dom
          b = toDom q mq
          zb : S
          zb = prʟ q (colʟ b)
          decide : Holds R q (up a) ⊎ (Holds R q (up a) → Empty.⊥)
                 → ∥ Σ[ z ∈ S ] (⟨ (z ∷ q ∷ []) ⊨ ψ ⟩
                                × ((z' : S) → ⟨ (z' ∷ q ∷ []) ⊨ ψ ⟩ → z' ≡ z)) ∥₁
          decide (inl h) = ∣ zb
            , ( ψ-in zb q (inl (h , ∣ colʟ b , (prʟ-fst q (colʟ b) , IHq q mq (b≺a-of q mq h)) ∣₁))
              , λ z' hz' → PT.rec (isSetS z' zb)
                  (λ { (inl (_ , hv)) → PT.rec (isSetS z' zb)
                         (λ { (v , (e , hcol)) → Σ≡Prop (λ w → snd (isL w))
                                (e ∙ cong (pr (fst q)) (colFo-val q mq v hcol) ∙ sym (prʟ-fst q (colʟ b))) })
                         hv
                     ; (inr (nh , _)) → Empty.rec (nh h) })
                  (ψ-out z' q hz') ) ∣₁
          decide (inr nh) = ∣ ea
            , ( ψ-in ea q (inr (nh , refl))
              , λ z' hz' → PT.rec (isSetS z' ea)
                  (λ { (inl (h , _)) → Empty.rec (nh h)
                     ; (inr (_ , e)) → Σ≡Prop (λ w → snd (isL w)) e })
                  (ψ-out z' q hz') ) ∣₁

        module T = Of (record { dom = D ; graph = ψ ; funct = fc }) using ( table; table-in; table-out )

      Fa : S
      Fa = T.table

      Below : Dom → Type ℓ
      Below b = (b ≺ a) ⊎ (b ≡ a)

      Fa-in : (b : Dom) → Below b → Holds Fa (up b) (colʟ b)
      Fa-in b k = subst (λ w → ⟨ w ∈ fst Fa ⟩) (prʟ-fst (up b) (colʟ b))
        (T.table-in (up b) (prʟ (up b) (colʟ b)) (up-mem b) (ψ-in _ (up b) (bodyOf k)))
        where
        bodyOf : Below b → Body (prʟ (up b) (colʟ b)) (up b)
        bodyOf (inl k) = inl (≺-out b a k , ∣ colʟ b , (prʟ-fst (up b) (colʟ b) , IH b k) ∣₁)
        bodyOf (inr e) = inr
          ( (λ h → ≺-irrefl a (≺-in a a (subst (λ t → Holds R (up t) (up a)) e h)))
          , prʟ-fst (up b) (colʟ b) ∙ cong (λ t → pr (↪ t) (col t)) e ∙ sym (prʟ-fst (up a) (colʟ a)) )

      Fa-out : (y : S) → ⟨ y ∈ˢ Fa ⟩
             → ∥ Σ[ b ∈ Dom ] (Below b × (fst y ≡ pr (↪ b) (col b))) ∥₁
      Fa-out y hy = PT.rec squash₁
        (λ { (q , (mq , hψ)) → PT.rec squash₁
          (λ { (inl (h , hv)) → PT.map
                 (λ { (v , (e , hcol)) → toDom q mq
                    , (inl (b≺a-of q mq h)
                      , e ∙ cong₂ pr (sym (toDom-val q mq)) (colFo-val q mq v hcol)) })
                 hv
             ; (inr (_ , e)) → ∣ a , (inr refl , e ∙ prʟ-fst (up a) (colʟ a)) ∣₁ })
          (ψ-out y q hψ) })
        (T.table-out y hy)

      Fa-pair : (x v : S) → Holds Fa x v
              → ∥ Σ[ b ∈ Dom ] (Below b × (↪ b ≡ fst x) × (col b ≡ fst v)) ∥₁
      Fa-pair x v h = PT.map step
        (Fa-out (prʟ x v) (subst (λ w → ⟨ w ∈ fst Fa ⟩) (sym (prʟ-fst x v)) h))
        where
        step : Σ[ b ∈ Dom ] (Below b × (fst (prʟ x v) ≡ pr (↪ b) (col b)))
             → Σ[ b ∈ Dom ] (Below b × (↪ b ≡ fst x) × (col b ≡ fst v))
        step (b , (k , e)) = b , (k , sym (fst q) , sym (snd q))
          where
          q : (fst x ≡ ↪ b) × (fst v ≡ col b)
          q = pr-inj (sym (prʟ-fst x v) ∙ e)

      below-trans : {c b : Dom} → c ≺ b → Below b → c ≺ a
      below-trans cb (inl k) = ≺-trans cb k
      below-trans {c} cb (inr e) = subst (c ≺_) e cb

      Fa-correct : Correct Fa R
      Fa-correct x v hxv = PT.rec
        (isProp× (isPropΠ (λ _ → isPropΠ (λ _ → squash₁)))
                 (isPropΠ (λ w → isProp× (isPropΠ (λ _ → squash₁))
                                          (isPropΠ (λ _ → snd (fst w ∈ fst v))))))
        build (Fa-pair x v hxv)
        where
        build : Σ[ b ∈ Dom ] (Below b × (↪ b ≡ fst x) × (col b ≡ fst v))
              → Complete Fa R x × ValueIs Fa R x v
        build (b , (k , ex , ev)) = cmp , (λ w → fwd w , bwd w)
          where
          -- An R-predecessor of x, as a member below b.
          pred : (y : S) → Holds R y x → Σ[ c ∈ Dom ] ((c ≺ b) × (↪ c ≡ fst y))
          pred y hy = c , (≺-in c b (subst2 (λ s t → ⟨ pr s t ∈ fst R ⟩)
                              (sym (toDom-val y my)) (sym ex) hy) , toDom-val y my)
            where
            my : Mem y
            my = Rsub y x hy .fst
            c : Dom
            c = toDom y my

          cmp : Complete Fa R x
          cmp y hy = ∣ colʟ c , subst (λ t → ⟨ pr t (col c) ∈ fst Fa ⟩) ec
                                 (Fa-in c (inl (below-trans cb k))) ∣₁
            where
            c = pred y hy .fst
            cb = pred y hy .snd .fst
            ec = pred y hy .snd .snd

          fwd : (w : S) → ⟨ fst w ∈ fst v ⟩ → Src Fa R x w
          fwd w w∈ = PT.map read (col-out b (fst w) (subst (λ t → ⟨ fst w ∈ t ⟩) (sym ev) w∈))
            where
            read : Σ[ r ∈ Dom ] ((r ≺ b) × (col r ≡ fst w)) → Σ[ y ∈ S ] (Holds R y x × Holds Fa y w)
            read (r , (rb , er)) = up r
              , ( subst (λ t → ⟨ pr (↪ r) t ∈ fst R ⟩) ex (≺-out r b rb)
                , subst (λ t → ⟨ pr (↪ r) t ∈ fst Fa ⟩) er (Fa-in r (inl (below-trans rb k))) )

          bwd : (w : S) → Src Fa R x w → ⟨ fst w ∈ fst v ⟩
          bwd w = PT.rec (snd (fst w ∈ fst v)) (λ { (y , (hy , fy)) →
            PT.rec (snd (fst w ∈ fst v)) (read y hy) (Fa-pair y w fy) })
            where
            read : (y : S) → Holds R y x
                 → Σ[ c ∈ Dom ] (Below c × (↪ c ≡ fst y) × (col c ≡ fst w))
                 → ⟨ fst w ∈ fst v ⟩
            read y hy (c , (_ , ey , ew)) =
              subst2 (λ s t → ⟨ s ∈ t ⟩) ew ev (col-in b c cb)
              where
              cb : c ≺ b
              cb = ≺-in c b (subst2 (λ s t → ⟨ pr s t ∈ fst R ⟩) (sym ey) (sym ex) hy)

      approx-step : ⟨ (colʟ a ∷ up a ∷ []) ⊨ CF.colFo ⟩
      approx-step = CF.colFo-in (colʟ a) (up a) Fa Fa-correct (Fa-in a (inr refl))

    -- THE GRAPH FORMULA HOLDS OF THE COLLAPSE, everywhere on D.
    approx : (a : Dom) → ⟨ (colʟ a ∷ up a ∷ []) ⊨ CF.colFo ⟩
    approx = W.induction {P = λ a → ⟨ (colʟ a ∷ up a ∷ []) ⊨ CF.colFo ⟩}
      (λ a IH → Approx.approx-step a IH)

    approx-at : (q : S) (mq : Mem q) → ⟨ (colʟ (toDom q mq) ∷ q ∷ []) ⊨ CF.colFo ⟩
    approx-at q mq = colFo-at (colʟ (toDom q mq)) (up-toDom q mq) (approx (toDom q mq))

    -- =================================================================
    -- SECTION 4.  THE TABLES: THE ORDER TYPE AND THE GRAPH, IN L.
    -- =================================================================

    private
      otR : Recursion
      otR = record
        { dom   = D
        ; graph = CF.colFo
        ; funct = λ q mq → mereFunct CF.colFo q
            ∣ colʟ (toDom q mq)
            , (approx-at q mq , λ v hv → Σ≡Prop (λ w → snd (isL w)) (colFo-val q mq v hv)) ∣₁ }

      module OT = Of otR using ( table; table-in; table-out )

    otL : S
    otL = OT.table

    otL-in : (b : Dom) → ⟨ col b ∈ fst otL ⟩
    otL-in b = OT.table-in (up b) (colʟ b) (up-mem b) (approx b)

    otL-out : (y : V ℓ) → ⟨ y ∈ fst otL ⟩ → ∥ Σ[ b ∈ Dom ] (col b ≡ y) ∥₁
    otL-out y hy = PT.map (λ { (q , (mq , h)) → toDom q mq , sym (colFo-val q mq yS h) })
      (OT.table-out yS hy)
      where
      yS : S
      yS = y , isL-trans {x = fst otL} {y = y} hy (snd otL)

    otL≡ot : fst otL ≡ ot
    otL≡ot = extensionalV {a = fst otL} {b = ot} (λ y → ⇔toPath
      (λ h → PT.map (λ { (b , e) → b , e }) (otL-out y h))
      (λ h → PT.rec (snd (y ∈ fst otL))
               (λ { (b , e) → subst (λ t → ⟨ t ∈ fst otL ⟩) e (otL-in b) }) h))

    otL-ord : IsOrd (fst otL)
    otL-ord = subst IsOrd (sym otL≡ot) ot-ord

    private
      tabR : Recursion
      tabR = record
        { dom   = D
        ; graph = PF.pairFo
        ; funct = λ q mq → mereFunct PF.pairFo q (wit q mq) }
        where
        wit : (q : S) (mq : Mem q)
            → ∥ Σ[ e ∈ S ] (⟨ (e ∷ q ∷ []) ⊨ PF.pairFo ⟩
                           × ((e' : S) → ⟨ (e' ∷ q ∷ []) ⊨ PF.pairFo ⟩ → e' ≡ e)) ∥₁
        wit q mq = ∣ zb
          , ( PF.pair-in zb q (colʟ b) (prʟ-fst q (colʟ b)) (approx-at q mq)
            , λ e' he' → PT.rec (isSetS e' zb)
                (λ { (v , (e , hv)) → Σ≡Prop (λ w → snd (isL w))
                       (e ∙ cong (pr (fst q)) (colFo-val q mq v hv) ∙ sym (prʟ-fst q (colʟ b))) })
                (PF.pair-out e' q he') ) ∣₁
          where
          b : Dom
          b = toDom q mq
          zb : S
          zb = prʟ q (colʟ b)

      module CT = Of tabR using ( table; table-in; table-out )

    colTable : S
    colTable = CT.table

    colTable-in : (b : Dom) → ⟨ pr (↪ b) (col b) ∈ fst colTable ⟩
    colTable-in b = subst (λ w → ⟨ w ∈ fst colTable ⟩) (prʟ-fst (up b) (colʟ b))
      (CT.table-in (up b) (prʟ (up b) (colʟ b)) (up-mem b)
        (PF.pair-in (prʟ (up b) (colʟ b)) (up b) (colʟ b) (prʟ-fst (up b) (colʟ b)) (approx b)))

    colTable-out : (y : S) → ⟨ y ∈ˢ colTable ⟩
                 → ∥ Σ[ b ∈ Dom ] (fst y ≡ pr (↪ b) (col b)) ∥₁
    colTable-out y hy = PT.rec squash₁
      (λ { (q , (mq , h)) → PT.map
        (λ { (v , (e , hv)) → toDom q mq
           , e ∙ cong₂ pr (sym (toDom-val q mq)) (colFo-val q mq v hv) })
        (PF.pair-out y q h) })
      (CT.table-out y hy)

    -- A pair in the table, read as a value of `col`.  The target is a
    -- proposition, so the truncation comes off.
    Fib : S → S → Type (ℓ-suc ℓ)
    Fib x v = Σ[ mx ∈ Mem x ] (fst v ≡ col (toDom x mx))

    isPropFib : (x v : S) → isProp (Fib x v)
    isPropFib x v = isPropΣ (isPropMem x) (λ mx → setIsSet (fst v) (col (toDom x mx)))

    colTable-pair : (x v : S) → Holds colTable x v → Fib x v
    colTable-pair x v h = PT.rec (isPropFib x v) step
      (colTable-out (prʟ x v) (subst (λ w → ⟨ w ∈ fst colTable ⟩) (sym (prʟ-fst x v)) h))
      where
      step : Σ[ b ∈ Dom ] (fst (prʟ x v) ≡ pr (↪ b) (col b)) → Fib x v
      step (b , e) = mx , (ev ∙ cong col (sym (Dom≡ (toDom-val x mx ∙ ex))))
        where
        q : (fst x ≡ ↪ b) × (fst v ≡ col b)
        q = pr-inj (sym (prʟ-fst x v) ∙ e)
        ex = fst q
        ev = snd q
        mx : Mem x
        mx = subst (λ t → ⟨ t ∈ fst D ⟩) (sym ex) (up-mem b)
```

<!--en-->
## The graph as a coded injection
<!--zh-->
## 作为编码单射的图
<!--/-->

```agda
-- =====================================================================
-- SECTION 5.  THE FOUR CONJUNCTS, IN THE SHAPE `InjCode` CONSUMES.
--
--   Single-valuedness, the domain and the range come from the table's
--   pair reading alone.  Injectivity needs the relation to be linear:
--   trichotomy is a hypothesis of this section only.
-- =====================================================================

module Code (D R : S)
            (Rsub : (y x : S) → Holds R y x
                  → ⟨ fst y ∈ fst D ⟩ × ⟨ fst x ∈ fst D ⟩) where

  open Internal D R Rsub public

  module Conjuncts (wf : WellFounded _≺_)
                   (≺-trans : {a b c : Dom} → a ≺ b → b ≺ c → a ≺ c) where

    open Graph wf ≺-trans public

    γ : S ^ 2
    γ = colTable ∷ D ∷ []

    sv : ⟨ γ ⊨ svAt zero ⟩
    sv = svAt-in zero γ (λ x y y' p q →
      let (m , e)   = colTable-pair x y p
          (m' , e') = colTable-pair x y' q
      in e ∙ cong (λ k → col (toDom x k)) (isPropMem x m m') ∙ sym e')

    dm : ⟨ γ ⊨ domAt zero (suc zero) ⟩
    dm = domAt-intro zero (suc zero) γ (λ x → fwd x , bwd x)
      where
      fwd : (x : S) → ⟨ ∃[ y ∶ S ] (pr (fst x) (fst y) ∈ fst colTable) ⟩ → Mem x
      fwd x = PT.rec (isPropMem x) (λ { (y , p) → fst (colTable-pair x y p) })

      bwd : (x : S) → Mem x → ⟨ ∃[ y ∶ S ] (pr (fst x) (fst y) ∈ fst colTable) ⟩
      bwd x m = ∣ colʟ (toDom x m)
        , subst (λ t → ⟨ pr t (col (toDom x m)) ∈ fst colTable ⟩) (toDom-val x m)
            (colTable-in (toDom x m)) ∣₁

    ran : (x y : S) → Holds colTable x y → ⟨ fst y ∈ fst otL ⟩
    ran x y h = subst (λ t → ⟨ t ∈ fst otL ⟩) (sym (snd (colTable-pair x y h)))
      (otL-in (toDom x (fst (colTable-pair x y h))))

    -- Injectivity, under trichotomy.
    module Inj (tri : (a b : Dom) → (a ≺ b) ⊎ ((a ≡ b) ⊎ (b ≺ a))) where

      col-inj : (a b : Dom) → col a ≡ col b → a ≡ b
      col-inj a b e = go (tri a b)
        where
        go : (a ≺ b) ⊎ ((a ≡ b) ⊎ (b ≺ a)) → a ≡ b
        go (inl k)       = Empty.rec (∈-irrefl (col b)
          (subst (λ t → ⟨ t ∈ col b ⟩) e (col-in b a k)))
        go (inr (inl q)) = q
        go (inr (inr k)) = Empty.rec (∈-irrefl (col a)
          (subst (λ t → ⟨ t ∈ col a ⟩) (sym e) (col-in a b k)))

      ij : ⟨ γ ⊨ injAt zero ⟩
      ij = injAt-in zero γ (λ y x x' p q →
        let (m , e)   = colTable-pair x y p
            (m' , e') = colTable-pair x' y q
        in sym (toDom-val x m)
         ∙ cong ↪ (col-inj (toDom x m) (toDom x' m') (sym e ∙ e'))
         ∙ toDom-val x' m')

      code : InjCode colTable D otL
      code = sv , dm , ij , ran
```
