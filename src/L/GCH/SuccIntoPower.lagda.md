# The successor cardinal injects into the power set

```agda
{-# OPTIONS --cubical --safe --guardedness #-}

open import Base.Prelude
open import Base.Truth
open import Base.Classical using ( LEM )

module L.GCH.SuccIntoPower {ℓ : Level} (lem : LEM (ℓ-suc ℓ)) where

open import FOL.ZFStructure using ( module hPropStructure )
open import FOL.Syntax
  using ( Formula; var; con; _∈̇_; _≐_; _∧̇_; _∨̇_; _⇒̇_; ¬̇_; ∃̇_; ∀̇_; ∀̇∈; ∃̇∈ )
import FOL.ZFModel
import FOL.Absoluteness
open import V.Hierarchy {ℓ} using ( 𝒮ᵥ; regularityV; extensionalV; ∈-irrefl )
open import V.Coding {ℓ} using ( pr; pr-inj )
open import L.Constructible {ℓ}
  using ( 𝒮ʟ; IsOrd; Lset; Lset-mono; isL; isL-trans )
open import L.Ordinal {ℓ} using ( mem-ord; #∈ω )
open import L.Axioms.Basic {ℓ} using ( ∅ʟ )
open import L.Axioms.Full {ℓ} lem using ( hasSeparationL )
open import L.Axioms.Power {ℓ} lem using ( hasPowerL )
open import L.Choice.Stage {ℓ} lem using ( stage-below; stageBound )
open import L.Cardinal {ℓ} lem using ( InjCode; IsCardinalL )
open import L.InjChain {ℓ} lem using ( module PairBound; appC; appC-adequate )
open import L.GCH.Least {ℓ} lem using ( module Least )
open import L.Coding.Model {ℓ}
  using ( prʟ; prʟ-fst; prAtL; prAtL-adequate; appAt; appAt-adequate
        ; domAt-in; domAt-out )
open import L.Coding.Injection {ℓ} lem using ( injAt-out )
open import L.GCH {ℓ} lem using ( SuccCardL; InjL )
open import L.GCH.BelowSucc {ℓ} lem using ( below-succ-injects )
open import L.GCH.Assembly {ℓ} lem using ( SuccIntoPower; injl-trans )
open import L.GCH.Definable {ℓ} lem using ( DefinableMap; module Inj )
open import L.GCH.OrderType {ℓ} lem
  using ( Holds; Complete; Src; ValueIs; Correct; correctAt; correct-out; correct-in )
open import L.GCH.Pairing {ℓ} lem
  using ( prodL; prodL-in; ω⊆; no-fin; prod-inj; Goal; module Step )
open import L.GCH.CardOf {ℓ} lem using ( cardOf )

open import Cubical.Data.Sigma using ( _×_; Σ≡Prop )
open import Cubical.Data.Sum using ( _⊎_; inl; inr )
open import Cubical.Foundations.Prelude using ( subst2 )
open import Cubical.Foundations.HLevels using ( isProp×; isPropΠ )
open import Cubical.Functions.Logic using ( ⇔toPath )
open import Cubical.HITs.CumulativeHierarchy.Base using ( _∈_; setIsSet )
open import Cubical.HITs.CumulativeHierarchy.Properties using ( ∈∈ₛ )
open import Cubical.HITs.CumulativeHierarchy.Constructions
  using ( ∅; ∅-empty; module InfinitySet )
open InfinitySet {ℓ} using ( ω )
import Cubical.Induction.WellFounded as WF
import Cubical.Data.Empty as Empty
import Cubical.HITs.PropositionalTruncation as PT
open PT using ( ∥_∥₁; ∣_∣₁; squash₁ )

open TruthAlgebra (hPropAlgebra (ℓ-suc ℓ))
open hPropStructure 𝒮ᵥ using ( _∈ˢ_ )
```

The V-carrier: the ambient membership lives here.

```agda
module SV = hPropStructure 𝒮ᵥ using ( S )
```

The L-carrier: `SuccCardL`, `InjL` and the model live here.

```agda
module SL = hPropStructure 𝒮ʟ using ( S; _∈ˢ_ )
```

The instance src/L/GCH.lagda.md names, at the same 𝒮ʟ.

```agda
module ModelL = FOL.ZFModel 𝒮ʟ using ( isZFModel; module isZFModel; ℩-spec )
```

Satisfaction, read exactly as `L.GCH.Definable` reads it: the record
`DefinableMap` is built here, so the two must be the same relation.

```agda
module AbsL = FOL.Absoluteness.Single 𝒮ᵥ isL isL-trans using ( _^_; _⊨ᵐ_ )
open AbsL using ( _^_ ) renaming ( _⊨ᵐ_ to _⊨_ )
```

Two elements of L with the same underlying set are equal.

```agda
S≡ : {x y : SL.S} → fst x ≡ fst y → x ≡ y
S≡ = Σ≡Prop (λ v → snd (isL v))
```

SECTION 1.  A SUBSET OF κ IS A MEMBER OF THE MODEL'S POWER SET.

  `𝒫 κ` IS `℩ (hasPower κ)` by definition, so `℩-spec` is the whole
  proof.  This is the converse of `z-strongest`
  (src/L/GCH/Assembly.lagda.md:229), which reads the same equation in
  the other direction.  `_⊆ˢ_` is the model's own subset relation
  (src/FOL/ZFModel.lagda.md:141), so it quantifies over L-elements
  only, and that is exactly what the caller can supply.

```agda
into-power :
    (zf : ModelL.isZFModel) (κ y : SL.S)
  → ((z : SL.S) → ⟨ fst z ∈ˢ fst y ⟩ → ⟨ fst z ∈ˢ fst κ ⟩)
  → ⟨ fst y ∈ˢ fst (ModelL.isZFModel.𝒫 zf κ) ⟩
into-power zf κ y sub =
  subst ⟨_⟩ (sym (ModelL.℩-spec (hasPower κ) y)) sub
  where open ModelL.isZFModel zf using ( hasPower )
```

SECTION 2.  AN ORDINAL WITHOUT ∅ AS A MEMBER IS ∅.

  One membership induction: a member x of a is either empty, and then
  ∅ ∈ a, or has a member w, and w ∈ a by transitivity.

```agda
ord-∅ : (a : SV.S) → IsOrd a → (⟨ ∅ ∈ a ⟩ → Empty.⊥) → a ≡ ∅
ord-∅ a oa n∅ = extensionalV {a = a} {b = ∅} (λ x → ⇔toPath
  (λ h → Empty.rec (none x h))
  (λ h → Empty.rec (∅-empty x (∈∈ₛ {a = x} {b = ∅} .fst h))))
  where
  Inh : SV.S → Type (ℓ-suc ℓ)
  Inh x = ∥ Σ[ w ∈ SV.S ] ⟨ w ∈ x ⟩ ∥₁

  empty : (x : SV.S) → (Inh x → Empty.⊥) → x ≡ ∅
  empty x h = extensionalV {a = x} {b = ∅} (λ w → ⇔toPath
    (λ w∈x → Empty.rec (h ∣ w , w∈x ∣₁))
    (λ w∈∅ → Empty.rec (∅-empty w (∈∈ₛ {a = w} {b = ∅} .fst w∈∅))))

  none : (x : SV.S) → ⟨ x ∈ a ⟩ → Empty.⊥
  none = WF.WFI.induction regularityV {P = λ x → ⟨ x ∈ a ⟩ → Empty.⊥} step
    where
    step : (x : SV.S) → (∀ x' → ⟨ x' ∈ x ⟩ → ⟨ x' ∈ a ⟩ → Empty.⊥)
         → ⟨ x ∈ a ⟩ → Empty.⊥
    step x IH x∈a = go (lem (Inh x , squash₁))
      where
      go : Inh x ⊎ (Inh x → Empty.⊥) → Empty.⊥
      go (inl h) = PT.rec Empty.isProp⊥
        (λ { (w , w∈x) → IH w w∈x (oa .fst w∈x x∈a) }) h
      go (inr h) = n∅ (subst (λ t → ⟨ t ∈ a ⟩) (empty x h) x∈a)
```

SECTION 3.  THE CONSTRUCTION, AT ONE SUCCESSOR CARDINAL.

  κ is infinite and δ is its successor cardinal in L.  The injection
  δ ↪ 𝒫 κ is the composite of two definable maps:

    1.  α ↦ R_α, the stage-order-least subset R of prodL κ that carries a
        CORRECT TABLE (src/L/GCH/OrderType.lagda.md, `Correct`) with
        an entry at every member of κ whose set of values is α.  The
        member ∅ of δ, which no such R fits, is sent to prodL κ
        itself, which no such table fits either.
    2.  R ↦ g[R], the image under the coded pairing g : prodL κ ↪ κ.

  Both maps land in one fixed set, so `DefinableMap` applies to each
  and `injl-trans` composes the two coded injections.

```agda
module Main (κ δ : SL.S) (κ∉ω : ⟨ fst κ ∈ˢ ω ⟩ → Empty.⊥)
            (sc : SuccCardL δ κ) where

  ordδ : IsOrd (fst δ)
  ordδ = sc .fst

  κ∈δ : ⟨ fst κ ∈ fst δ ⟩
  κ∈δ = sc .snd .snd .fst

  ordκ : IsOrd (fst κ)
  ordκ = mem-ord {A = fst δ} ordδ (fst κ) κ∈δ

  ∅∈κ : ⟨ ∅ ∈ fst κ ⟩
  ∅∈κ = ω⊆ (fst κ) ordκ κ∉ω ∅ (#∈ω zero)

  ∅∈δ : ⟨ ∅ ∈ fst δ ⟩
  ∅∈δ = ordδ .fst ∅∈κ κ∈δ

  -- The product, and its power set: every relation the selection sees.
  Sq : SL.S
  Sq = prodL κ

  A : SL.S
  A = hasPowerL Sq .fst .fst

  A-in : (R : SL.S) → ((z : SL.S) → ⟨ fst z ∈ fst R ⟩ → ⟨ fst z ∈ fst Sq ⟩)
       → ⟨ fst R ∈ fst A ⟩
  A-in R sub = subst ⟨_⟩ (sym (hasPowerL Sq .fst .snd R)) sub

  A-out : (R : SL.S) → ⟨ fst R ∈ fst A ⟩
        → (z : SL.S) → ⟨ fst z ∈ fst R ⟩ → ⟨ fst z ∈ fst Sq ⟩
  A-out R h = subst ⟨_⟩ (hasPowerL Sq .fst .snd R) h

  Sq∈A : ⟨ fst Sq ∈ fst A ⟩
  Sq∈A = A-in Sq (λ z h → h)

  -- The site: one stage holding every member of A; the stage order
  -- there is the one `L.GCH.Least` selects by.
  β : SV.S
  β = stageBound (fst A) (snd A) .fst

  oβ : IsOrd β
  oβ = stageBound (fst A) (snd A) .snd .fst

  site : (R : SL.S) → ⟨ fst R ∈ fst A ⟩ → ⟨ fst R ∈ Lset β ⟩
  site R h = Lset-mono (stageBound (fst A) (snd A) .snd .snd .snd)
                       (stage-below (fst A) (snd A) (fst R) h)

  -- -------------------------------------------------------------------
  -- 3.1  The host predicate "R carries a total correct table with
  --      values α", and its formula.
  -- -------------------------------------------------------------------

  Total : SL.S → Type (ℓ-suc ℓ)
  Total F = (x : SL.S) → ⟨ fst x ∈ fst κ ⟩ → ∥ Σ[ v ∈ SL.S ] Holds F x v ∥₁

  Rec : SL.S → SL.S → Type (ℓ-suc ℓ)
  Rec F v = ∥ Σ[ x ∈ SL.S ] (⟨ fst x ∈ fst κ ⟩ × Holds F x v) ∥₁

  Values : SL.S → SL.S → Type (ℓ-suc ℓ)
  Values F α = (v : SL.S) → (⟨ fst v ∈ fst α ⟩ → Rec F v) × (Rec F v → ⟨ fst v ∈ fst α ⟩)

  Table : SL.S → SL.S → SL.S → Type (ℓ-suc ℓ)
  Table F R α = Correct F R × Total F × Values F α

  Codes : SL.S → SL.S → Type (ℓ-suc ℓ)
  Codes R α = ∥ Σ[ F ∈ SL.S ] Table F R α ∥₁

  opaque
    -- "f has an entry at every member of κ".  Inside: x is 0; then v
    -- is 0 and x is 1.
    totalAt : ∀ {n} → Fin n → Formula SL.S n
    totalAt f = ∀̇∈ (con κ) (∃̇ (appAt (suc (suc f)) (suc zero) zero))

    total-out : ∀ {n} (f : Fin n) (γ : SL.S ^ n)
              → ⟨ γ ⊨ totalAt f ⟩ → Total (lookup f γ)
    total-out f γ h x mx = PT.map
      (λ { (v , q) → v , subst ⟨_⟩ (appAt-adequate (suc (suc f)) (suc zero) zero (v ∷ x ∷ γ)) q })
      (h x mx)

    total-in : ∀ {n} (f : Fin n) (γ : SL.S ^ n)
             → Total (lookup f γ) → ⟨ γ ⊨ totalAt f ⟩
    total-in f γ h x mx = PT.map
      (λ { (v , q) → v , subst ⟨_⟩ (sym (appAt-adequate (suc (suc f)) (suc zero) zero (v ∷ x ∷ γ))) q })
      (h x mx)

    -- "v is recorded in f at some member of κ".  Inside: x is 0.
    recAt : ∀ {n} → Fin n → Fin n → Formula SL.S n
    recAt f v = ∃̇∈ (con κ) (appAt (suc f) zero (suc v))

    rec-out : ∀ {n} (f v : Fin n) (γ : SL.S ^ n)
            → ⟨ γ ⊨ recAt f v ⟩ → Rec (lookup f γ) (lookup v γ)
    rec-out f v γ = PT.map (λ { (x , (mx , q)) →
      x , mx , subst ⟨_⟩ (appAt-adequate (suc f) zero (suc v) (x ∷ γ)) q })

    rec-in : ∀ {n} (f v : Fin n) (γ : SL.S ^ n)
           → Rec (lookup f γ) (lookup v γ) → ⟨ γ ⊨ recAt f v ⟩
    rec-in f v γ = PT.map (λ { (x , mx , q) →
      x , (mx , subst ⟨_⟩ (sym (appAt-adequate (suc f) zero (suc v) (x ∷ γ))) q) })

    -- "the values f records are exactly the members of a".  Inside: v
    -- is 0.
    valuesAt : ∀ {n} → Fin n → Fin n → Formula SL.S n
    valuesAt f a = ∀̇ ( ((var zero ∈̇ var (suc a)) ⇒̇ recAt (suc f) zero)
                    ∧̇ (recAt (suc f) zero ⇒̇ (var zero ∈̇ var (suc a))) )

    values-out : ∀ {n} (f a : Fin n) (γ : SL.S ^ n)
               → ⟨ γ ⊨ valuesAt f a ⟩ → Values (lookup f γ) (lookup a γ)
    values-out f a γ h v =
        (λ m → rec-out (suc f) zero (v ∷ γ) (h v .fst m))
      , (λ r → h v .snd (rec-in (suc f) zero (v ∷ γ) r))

    values-in : ∀ {n} (f a : Fin n) (γ : SL.S ^ n)
              → Values (lookup f γ) (lookup a γ) → ⟨ γ ⊨ valuesAt f a ⟩
    values-in f a γ h v =
        (λ m → rec-in (suc f) zero (v ∷ γ) (h v .fst m))
      , (λ r → h v .snd (rec-out (suc f) zero (v ∷ γ) r))

    -- "some f is a total correct table for r whose values are a".
    -- Inside: f is 0.
    predAt : ∀ {n} → Fin n → Fin n → Formula SL.S n
    predAt r a = ∃̇ (correctAt zero (suc r) ∧̇ (totalAt zero ∧̇ valuesAt zero (suc a)))

    pred-out : ∀ {n} (r a : Fin n) (γ : SL.S ^ n)
             → ⟨ γ ⊨ predAt r a ⟩ → Codes (lookup r γ) (lookup a γ)
    pred-out r a γ = PT.map (λ { (F , (hc , (ht , hv))) →
      F , correct-out zero (suc r) (F ∷ γ) hc
        , total-out zero (F ∷ γ) ht
        , values-out zero (suc a) (F ∷ γ) hv })

    pred-in : ∀ {n} (r a : Fin n) (γ : SL.S ^ n)
            → Codes (lookup r γ) (lookup a γ) → ⟨ γ ⊨ predAt r a ⟩
    pred-in r a γ = PT.map (λ { (F , hc , ht , hv) →
      F , ( correct-in zero (suc r) (F ∷ γ) hc
          , ( total-in zero (F ∷ γ) ht
            , values-in zero (suc a) (F ∷ γ) hv )) })

  -- -------------------------------------------------------------------
  -- 3.2  UNIQUENESS.  Two total correct tables for one R record the
  --      same value everywhere, by one membership induction on the
  --      value; so R determines its value set.  No well-foundedness of
  --      R is needed.  And prodL κ carries no table at all: at ∅ ∈ κ
  --      the pair (∅, ∅) is in prodL κ, so the value there would be a
  --      member of itself.
  -- -------------------------------------------------------------------

  agree : (F F' R : SL.S) → Correct F R → Correct F' R
        → (u : SV.S) (lu : ⟨ isL u ⟩) (x v' : SL.S)
        → Holds F x (u , lu) → Holds F' x v' → fst v' ≡ u
  agree F F' R hc hc' = WF.WFI.induction regularityV {P = Pu} step
    where
    Pu : SV.S → Type (ℓ-suc ℓ)
    Pu u = (lu : ⟨ isL u ⟩) (x v' : SL.S)
         → Holds F x (u , lu) → Holds F' x v' → fst v' ≡ u

    step : (u : SV.S) → (∀ u' → ⟨ u' ∈ u ⟩ → Pu u') → Pu u
    step u IH lu x v' hv hv' =
      extensionalV {a = fst v'} {b = u} (λ w → ⇔toPath (fwd w) (bwd w))
      where
      v : SL.S
      v = u , lu

      cmp : Complete F R x
      cmp = hc x v hv .fst
      val : ValueIs F R x v
      val = hc x v hv .snd
      cmp' : Complete F' R x
      cmp' = hc' x v' hv' .fst
      val' : ValueIs F' R x v'
      val' = hc' x v' hv' .snd

      fwd : (w : SV.S) → ⟨ w ∈ fst v' ⟩ → ⟨ w ∈ u ⟩
      fwd w w∈ = PT.rec (snd (w ∈ u)) read (val' wS .fst w∈)
        where
        wS : SL.S
        wS = w , isL-trans {x = fst v'} {y = w} w∈ (snd v')
        read : Σ[ y ∈ SL.S ] (Holds R y x × Holds F' y wS) → ⟨ w ∈ u ⟩
        read (y , ry , fy) = PT.rec (snd (w ∈ u)) inner (cmp y ry)
          where
          inner : Σ[ t ∈ SL.S ] Holds F y t → ⟨ w ∈ u ⟩
          inner (t , ft) =
            subst (λ z → ⟨ z ∈ u ⟩) (sym (IH (fst t) t∈u (snd t) y wS ft fy)) t∈u
            where
            t∈u : ⟨ fst t ∈ u ⟩
            t∈u = val t .snd ∣ y , ry , ft ∣₁

      bwd : (w : SV.S) → ⟨ w ∈ u ⟩ → ⟨ w ∈ fst v' ⟩
      bwd w w∈ = PT.rec (snd (w ∈ fst v')) read (val wS .fst w∈)
        where
        wS : SL.S
        wS = w , isL-trans {x = u} {y = w} w∈ lu
        read : Σ[ y ∈ SL.S ] (Holds R y x × Holds F y wS) → ⟨ w ∈ fst v' ⟩
        read (y , ry , fy) = PT.rec (snd (w ∈ fst v')) inner (cmp' y ry)
          where
          inner : Σ[ t ∈ SL.S ] Holds F' y t → ⟨ w ∈ fst v' ⟩
          inner (t , ft) = val' wS .snd
            ∣ y , ry , subst (λ z → ⟨ pr (fst y) z ∈ fst F' ⟩) (IH w w∈ (snd wS) y t fy ft) ft ∣₁

  push : (F F' R α α' : SL.S) → Correct F R → Correct F' R → Total F'
       → Values F α → Values F' α'
       → (w : SV.S) → ⟨ w ∈ fst α ⟩ → ⟨ w ∈ fst α' ⟩
  push F F' R α α' hc hc' ht' hv hv' w w∈ =
    PT.rec (snd (w ∈ fst α')) (λ { (x , mx , hx) →
      PT.rec (snd (w ∈ fst α')) (λ { (u , hu) →
        hv' wS .snd ∣ x , mx
          , subst (λ z → ⟨ pr (fst x) z ∈ fst F' ⟩) (agree F F' R hc hc' w (snd wS) x u hx hu) hu ∣₁ })
      (ht' x mx) })
    (hv wS .fst w∈)
    where
    wS : SL.S
    wS = w , isL-trans {x = fst α} {y = w} w∈ (snd α)

  values-unique : (R α α' : SL.S) → Codes R α → Codes R α' → fst α ≡ fst α'
  values-unique R α α' = PT.rec2 (setIsSet (fst α) (fst α'))
    (λ { (F , hc , ht , hv) (F' , hc' , ht' , hv') →
      extensionalV {a = fst α} {b = fst α'} (λ w → ⇔toPath
        (push F F' R α α' hc hc' ht' hv hv' w)
        (push F' F R α' α hc' hc ht hv' hv w)) })

  noCodesSq : (α : SL.S) → Codes Sq α → Empty.⊥
  noCodesSq α = PT.rec Empty.isProp⊥ (λ { (F , hc , ht , _) →
    PT.rec Empty.isProp⊥ (λ { (v , hv) →
      ∈-irrefl (fst v) (hc ∅ʟ v hv .snd v .snd ∣ ∅ʟ , p∅ , hv ∣₁) })
    (ht ∅ʟ ∅∈κ) })
    where
    p∅ : Holds Sq ∅ʟ ∅ʟ
    p∅ = prodL-in κ ∅ʟ ∅ʟ ∅∈κ ∅∈κ

  -- -------------------------------------------------------------------
  -- 3.3  THE SELECTION AT ONE α ∈ δ.
  -- -------------------------------------------------------------------

  module At (α : SL.S) (mα : ⟨ fst α ∈ fst δ ⟩) where

    ordα : IsOrd (fst α)
    ordα = mem-ord {A = fst δ} ordδ (fst α) mα

    α⊆δ : (z : SV.S) → ⟨ z ∈ fst α ⟩ → ⟨ z ∈ fst δ ⟩
    α⊆δ z h = ordδ .fst h mα

    -- EXISTENCE.  From a coded injection f : α ↪ κ and ∅ ∈ α: the
    -- order R = { (f ξ, f η) : ξ ∈ η ∈ α } on prodL κ, and the table
    -- F = { (f ξ, ξ) : ξ ∈ α } ∪ { (x, ∅) : x ∈ κ outside the range }.
    -- F is correct for R, total on κ, and its values are α ∪ {∅} = α.
    module Exist (∅∈α : ⟨ ∅ ∈ fst α ⟩) (Ff : SL.S) (code : InjCode Ff α κ) where

      γF : SL.S ^ 2
      γF = Ff ∷ α ∷ []

      ranF : (x y : SL.S) → Holds Ff x y → ⟨ fst y ∈ fst κ ⟩
      ranF = code .snd .snd .snd

      domF : (x y : SL.S) → Holds Ff x y → ⟨ fst x ∈ fst α ⟩
      domF = domAt-out zero (suc zero) γF (code .snd .fst)

      valF : (x : SL.S) → ⟨ fst x ∈ fst α ⟩ → ∥ Σ[ y ∈ SL.S ] Holds Ff x y ∥₁
      valF = domAt-in zero (suc zero) γF (code .snd .fst)

      injF : (y x x' : SL.S) → Holds Ff x y → Holds Ff x' y → fst x ≡ fst x'
      injF = injAt-out zero γF (code .snd .snd .fst)

      -- THE ORDER.  Over (p ∷ []): "p is the pair of the values at ξ
      -- and at η, for some ξ ∈ η ∈ α".  Inside the four binders: y is
      -- 0, x is 1, ξ is 2, η is 3, p is 4.
      InR : SL.S → Type (ℓ-suc ℓ)
      InR p = ∥ Σ[ η ∈ SL.S ] Σ[ ξ ∈ SL.S ] Σ[ x ∈ SL.S ] Σ[ y ∈ SL.S ]
                ( ⟨ fst η ∈ fst α ⟩ × ⟨ fst ξ ∈ fst η ⟩
                × Holds Ff ξ x × Holds Ff η y × (fst p ≡ pr (fst x) (fst y)) ) ∥₁

      opaque
        φR : Formula SL.S 1
        φR = ∃̇∈ (con α) (∃̇∈ (var zero) (∃̇ (∃̇
               ( appC Ff (suc (suc zero)) (suc zero)
               ∧̇ ( appC Ff (suc (suc (suc zero))) zero
                 ∧̇ prAtL (suc (suc (suc (suc zero)))) (suc zero) zero ) ))))

        private
          env : SL.S → SL.S → SL.S → SL.S → SL.S → SL.S ^ 5
          env p η ξ x y = y ∷ x ∷ ξ ∷ η ∷ p ∷ []

          a1 : (p η ξ x y : SL.S)
             → ⟨ env p η ξ x y ⊨ appC Ff (suc (suc zero)) (suc zero) ⟩ ≡ Holds Ff ξ x
          a1 p η ξ x y = cong ⟨_⟩ (appC-adequate Ff (suc (suc zero)) (suc zero) (env p η ξ x y))

          a2 : (p η ξ x y : SL.S)
             → ⟨ env p η ξ x y ⊨ appC Ff (suc (suc (suc zero))) zero ⟩ ≡ Holds Ff η y
          a2 p η ξ x y = cong ⟨_⟩ (appC-adequate Ff (suc (suc (suc zero))) zero (env p η ξ x y))

          a3 : (p η ξ x y : SL.S)
             → ⟨ env p η ξ x y ⊨ prAtL (suc (suc (suc (suc zero)))) (suc zero) zero ⟩
             ≡ (fst p ≡ pr (fst x) (fst y))
          a3 p η ξ x y = cong ⟨_⟩ (prAtL-adequate (suc (suc (suc (suc zero)))) (suc zero) zero (env p η ξ x y))

        φR-out : (p : SL.S) → ⟨ (p ∷ []) ⊨ φR ⟩ → InR p
        φR-out p = PT.rec squash₁ (λ { (η , (mη , h)) →
          PT.rec squash₁ (λ { (ξ , (mξ , h')) →
            PT.rec squash₁ (λ { (x , h'') →
              PT.map (λ { (y , (q1 , (q2 , q3))) →
                η , ξ , x , y , mη , mξ
                  , transport (a1 p η ξ x y) q1
                  , transport (a2 p η ξ x y) q2
                  , transport (a3 p η ξ x y) q3 }) h'' }) h' }) h })

        φR-in : (p η ξ x y : SL.S) → ⟨ fst η ∈ fst α ⟩ → ⟨ fst ξ ∈ fst η ⟩
              → Holds Ff ξ x → Holds Ff η y → fst p ≡ pr (fst x) (fst y)
              → ⟨ (p ∷ []) ⊨ φR ⟩
        φR-in p η ξ x y mη mξ q1 q2 q3 =
          ∣ η , (mη , ∣ ξ , (mξ , ∣ x , ∣ y
            , ( transport (sym (a1 p η ξ x y)) q1
              , ( transport (sym (a2 p η ξ x y)) q2
                , transport (sym (a3 p η ξ x y)) q3 )) ∣₁ ∣₁) ∣₁) ∣₁

      R : SL.S
      R = fst (fst (hasSeparationL Sq φR))

      R-spec : (e : SL.S) → (e SL.∈ˢ R) ≡ ((e SL.∈ˢ Sq) ⊓ ((e ∷ []) ⊨ φR))
      R-spec = snd (fst (hasSeparationL Sq φR))

      R⊆Sq : (z : SL.S) → ⟨ fst z ∈ fst R ⟩ → ⟨ fst z ∈ fst Sq ⟩
      R⊆Sq z h = subst ⟨_⟩ (R-spec z) h .fst

      R∈A : ⟨ fst R ∈ fst A ⟩
      R∈A = A-in R R⊆Sq

      R-out : (y x : SL.S) → Holds R y x → InR (prʟ y x)
      R-out y x h = φR-out (prʟ y x)
        (subst ⟨_⟩ (R-spec (prʟ y x))
          (subst (λ w → ⟨ w ∈ fst R ⟩) (sym (prʟ-fst y x)) h) .snd)

      R-in : (η ξ x y : SL.S) → ⟨ fst η ∈ fst α ⟩ → ⟨ fst ξ ∈ fst η ⟩
           → Holds Ff ξ x → Holds Ff η y → Holds R x y
      R-in η ξ x y mη mξ q1 q2 = subst (λ w → ⟨ w ∈ fst R ⟩) (prʟ-fst x y)
        (subst ⟨_⟩ (sym (R-spec (prʟ x y)))
          ( subst (λ w → ⟨ w ∈ fst Sq ⟩) (sym (prʟ-fst x y))
              (prodL-in κ x y (ranF ξ x q1) (ranF η y q2))
          , φR-in (prʟ x y) η ξ x y mη mξ q1 q2 (prʟ-fst x y) ))

      -- An entry of R at a coded pair, read at its own components.
      Ent : SL.S → SL.S → Type (ℓ-suc ℓ)
      Ent y x = ∥ Σ[ η ∈ SL.S ] Σ[ ξ ∈ SL.S ]
                  (⟨ fst η ∈ fst α ⟩ × ⟨ fst ξ ∈ fst η ⟩ × Holds Ff ξ y × Holds Ff η x) ∥₁

      R-ent : (y x : SL.S) → Holds R y x → Ent y x
      R-ent y x h = PT.map (λ { (η , ξ , x₁ , y₁ , mη , mξ , q1 , q2 , e) →
          let q = pr-inj (sym (prʟ-fst y x) ∙ e)
          in η , ξ , mη , mξ
               , subst (λ t → ⟨ pr (fst ξ) t ∈ fst Ff ⟩) (sym (fst q)) q1
               , subst (λ t → ⟨ pr (fst η) t ∈ fst Ff ⟩) (sym (snd q)) q2 })
        (R-out y x h)

      -- THE TABLE.  Over (e ∷ []): "e is the pair of a member x of κ
      -- and a v that is either the member of α sent to x, or ∅ when
      -- nothing is sent to x".  Inside: x is 0 and e is 1; then v is 0,
      -- x is 1, e is 2; inside the negated binder ξ is 0, v is 1, x is 2.
      Body : SL.S → SL.S → Type (ℓ-suc ℓ)
      Body v x = ∥ (⟨ fst v ∈ fst α ⟩ × Holds Ff v x)
                 ⊎ ((fst v ≡ ∅) × ((ξ : SL.S) → Holds Ff ξ x → Empty.⊥)) ∥₁

      InF : SL.S → Type (ℓ-suc ℓ)
      InF e = ∥ Σ[ x ∈ SL.S ] Σ[ v ∈ SL.S ]
                (⟨ fst x ∈ fst κ ⟩ × (fst e ≡ pr (fst x) (fst v)) × Body v x) ∥₁

      opaque
        bodyFo : Formula SL.S 3
        bodyFo = ((var zero ∈̇ con α) ∧̇ appC Ff zero (suc zero))
               ∨̇ ((var zero ≐ con ∅ʟ) ∧̇ (¬̇ (∃̇ (appC Ff zero (suc (suc zero))))))

        φF : Formula SL.S 1
        φF = ∃̇∈ (con κ) (∃̇ (prAtL (suc (suc zero)) (suc zero) zero ∧̇ bodyFo))

        private
          envF : SL.S → SL.S → SL.S → SL.S ^ 3
          envF e x v = v ∷ x ∷ e ∷ []

          b1 : (e x v : SL.S)
             → ⟨ envF e x v ⊨ prAtL (suc (suc zero)) (suc zero) zero ⟩
             ≡ (fst e ≡ pr (fst x) (fst v))
          b1 e x v = cong ⟨_⟩ (prAtL-adequate (suc (suc zero)) (suc zero) zero (envF e x v))

          b2 : (e x v : SL.S) → ⟨ envF e x v ⊨ appC Ff zero (suc zero) ⟩ ≡ Holds Ff v x
          b2 e x v = cong ⟨_⟩ (appC-adequate Ff zero (suc zero) (envF e x v))

          b3 : (e x v ξ : SL.S)
             → ⟨ (ξ ∷ envF e x v) ⊨ appC Ff zero (suc (suc zero)) ⟩ ≡ Holds Ff ξ x
          b3 e x v ξ = cong ⟨_⟩ (appC-adequate Ff zero (suc (suc zero)) (ξ ∷ envF e x v))

          body-out : (e x v : SL.S) → ⟨ envF e x v ⊨ bodyFo ⟩ → Body v x
          body-out e x v = PT.map
            (λ { (inl (m , q)) → inl (m , transport (b2 e x v) q)
               ; (inr (z , n)) → inr (z , λ ξ h → n ∣ ξ , transport (sym (b3 e x v ξ)) h ∣₁) })

          body-in : (e x v : SL.S) → Body v x → ⟨ envF e x v ⊨ bodyFo ⟩
          body-in e x v = PT.map
            (λ { (inl (m , q)) → inl (m , transport (sym (b2 e x v)) q)
               ; (inr (z , n)) → inr (z , PT.rec Empty.isProp⊥
                                       (λ { (ξ , h) → n ξ (transport (b3 e x v ξ) h) })) })

        φF-out : (e : SL.S) → ⟨ (e ∷ []) ⊨ φF ⟩ → InF e
        φF-out e = PT.rec squash₁ (λ { (x , (mx , h)) →
          PT.map (λ { (v , (q , b)) →
            x , v , mx , transport (b1 e x v) q , body-out e x v b }) h })

        φF-in : (e x v : SL.S) → ⟨ fst x ∈ fst κ ⟩ → fst e ≡ pr (fst x) (fst v)
              → Body v x → ⟨ (e ∷ []) ⊨ φF ⟩
        φF-in e x v mx q b =
          ∣ x , (mx , ∣ v , (transport (sym (b1 e x v)) q , body-in e x v b) ∣₁) ∣₁

      bnd : SL.S
      bnd = PairBound.bnd κ δ

      F : SL.S
      F = fst (fst (hasSeparationL bnd φF))

      F-spec : (e : SL.S) → (e SL.∈ˢ F) ≡ ((e SL.∈ˢ bnd) ⊓ ((e ∷ []) ⊨ φF))
      F-spec = snd (fst (hasSeparationL bnd φF))

      F-in : (x v : SL.S) → ⟨ fst x ∈ fst κ ⟩ → ⟨ fst v ∈ fst δ ⟩ → Body v x
           → Holds F x v
      F-in x v mx mv b = subst (λ w → ⟨ w ∈ fst F ⟩) (prʟ-fst x v)
        (subst ⟨_⟩ (sym (F-spec (prʟ x v)))
          ( subst (λ w → ⟨ w ∈ fst bnd ⟩) (sym (prʟ-fst x v)) (PairBound.below κ δ x v mx mv)
          , φF-in (prʟ x v) x v mx (prʟ-fst x v) b ))

      F-out : (x v : SL.S) → Holds F x v → Body v x
      F-out x v h = PT.rec squash₁ (λ { (x' , v' , _ , e , b) →
          let q = pr-inj (sym (prʟ-fst x v) ∙ e)
          in subst2 Body (sym (S≡ {v} {v'} (snd q))) (sym (S≡ {x} {x'} (fst q))) b })
        (φF-out (prʟ x v)
          (subst ⟨_⟩ (F-spec (prʟ x v))
            (subst (λ w → ⟨ w ∈ fst F ⟩) (sym (prʟ-fst x v)) h) .snd))

      total : Total F
      total x mx = go (lem (Hit , squash₁))
        where
        Hit : Type (ℓ-suc ℓ)
        Hit = ∥ Σ[ ξ ∈ SL.S ] Holds Ff ξ x ∥₁

        go : Hit ⊎ (Hit → Empty.⊥) → ∥ Σ[ v ∈ SL.S ] Holds F x v ∥₁
        go (inl h) = PT.map (λ { (ξ , q) →
          ξ , F-in x ξ mx (α⊆δ (fst ξ) (domF ξ x q)) ∣ inl (domF ξ x q , q) ∣₁ }) h
        go (inr n) = ∣ ∅ʟ , F-in x ∅ʟ mx ∅∈δ ∣ inr (refl , λ ξ q → n ∣ ξ , q ∣₁) ∣₁ ∣₁

      values : Values F α
      values v = fwd , bwd
        where
        fwd : ⟨ fst v ∈ fst α ⟩ → Rec F v
        fwd mv = PT.map (λ { (x , q) →
          x , ranF v x q , F-in x v (ranF v x q) (α⊆δ (fst v) mv) ∣ inl (mv , q) ∣₁ })
          (valF v mv)

        bwd : Rec F v → ⟨ fst v ∈ fst α ⟩
        bwd = PT.rec (snd (fst v ∈ fst α)) (λ { (x , mx , h) →
          PT.rec (snd (fst v ∈ fst α))
            (λ { (inl (mv , _)) → mv
               ; (inr (e , _)) → subst (λ t → ⟨ t ∈ fst α ⟩) (sym e) ∅∈α })
            (F-out x v h) })

      isPropCV : (x v : SL.S) → isProp (Complete F R x × ValueIs F R x v)
      isPropCV x v = isProp× (isPropΠ (λ _ → isPropΠ (λ _ → squash₁)))
        (isPropΠ (λ w → isProp× (isPropΠ (λ _ → squash₁))
                                (isPropΠ (λ _ → snd (fst w ∈ fst v)))))

      correct : Correct F R
      correct x v hxv = PT.rec (isPropCV x v) build (F-out x v hxv)
        where
        build : (⟨ fst v ∈ fst α ⟩ × Holds Ff v x)
              ⊎ ((fst v ≡ ∅) × ((ξ : SL.S) → Holds Ff ξ x → Empty.⊥))
              → Complete F R x × ValueIs F R x v
        -- x is f v: its predecessors are f ξ for ξ ∈ v, recorded at ξ.
        build (inl (mv , hvx)) = cmp , (λ w → fwd w , bwd w)
          where
          cmp : Complete F R x
          cmp y hyx = PT.map (λ { (η , ξ , mη , mξ , q1 , q2) →
              ξ , F-in y ξ (ranF ξ y q1) (α⊆δ (fst ξ) (ordα .fst mξ mη))
                    ∣ inl (ordα .fst mξ mη , q1) ∣₁ })
            (R-ent y x hyx)

          fwd : (w : SL.S) → ⟨ fst w ∈ fst v ⟩ → Src F R x w
          fwd w w∈v = PT.map (λ { (y , hwy) →
              y , R-in v w y x mv w∈v hwy hvx
                , F-in y w (ranF w y hwy) (α⊆δ (fst w) mw) ∣ inl (mw , hwy) ∣₁ })
            (valF w mw)
            where
            mw : ⟨ fst w ∈ fst α ⟩
            mw = ordα .fst w∈v mv

          bwd : (w : SL.S) → Src F R x w → ⟨ fst w ∈ fst v ⟩
          bwd w = PT.rec (snd (fst w ∈ fst v)) (λ { (y , hyx , hyw) →
            PT.rec (snd (fst w ∈ fst v)) (λ { (η , ξ , mη , mξ , q1 , q2) →
              PT.rec (snd (fst w ∈ fst v))
                (λ { (inl (mw , hwy)) →
                       subst (λ t → ⟨ fst w ∈ t ⟩) (injF x η v q2 hvx)
                         (subst (λ t → ⟨ t ∈ fst η ⟩) (injF y ξ w q1 hwy) mξ)
                   ; (inr (_ , none)) → Empty.rec (none ξ q1) })
                (F-out y w hyw) })
              (R-ent y x hyx) })
        -- x is outside the range: it has no predecessor, and v is ∅.
        build (inr (ev , none)) = cmp , (λ w → fwd w , bwd w)
          where
          noPred : (y : SL.S) → Holds R y x → Empty.⊥
          noPred y hyx = PT.rec Empty.isProp⊥
            (λ { (η , ξ , mη , mξ , q1 , q2) → none η q2 }) (R-ent y x hyx)

          cmp : Complete F R x
          cmp y hyx = Empty.rec (noPred y hyx)

          fwd : (w : SL.S) → ⟨ fst w ∈ fst v ⟩ → Src F R x w
          fwd w w∈v = Empty.rec (∅-empty (fst w)
            (∈∈ₛ {a = fst w} {b = ∅} .fst (subst (λ t → ⟨ fst w ∈ t ⟩) ev w∈v)))

          bwd : (w : SL.S) → Src F R x w → ⟨ fst w ∈ fst v ⟩
          bwd w = PT.rec (snd (fst w ∈ fst v))
            (λ { (y , hyx , _) → Empty.rec (noPred y hyx) })

      codes : Codes R α
      codes = ∣ F , correct , total , values ∣₁

  -- -------------------------------------------------------------------
  -- 3.4  THE CODE PREDICATE, over (R ∷ α ∷ []): either ∅ ∉ α and R is
  --      prodL κ, or ∅ ∈ α and R ∈ A codes α.  The selection of the
  --      stage-order-least such R, its graph and its table are `L.GCH.Least`
  --      at the site β.
  -- -------------------------------------------------------------------

  LeftOf : SL.S → SL.S → Type (ℓ-suc ℓ)
  LeftOf R α = (⟨ ∅ ∈ fst α ⟩ → Empty.⊥) × (fst R ≡ fst Sq)

  RightOf : SL.S → SL.S → Type (ℓ-suc ℓ)
  RightOf R α = ⟨ ∅ ∈ fst α ⟩ × ⟨ fst R ∈ fst A ⟩ × Codes R α

  opaque
    codeFo : Formula SL.S 2
    codeFo = ( (¬̇ (con ∅ʟ ∈̇ var (suc zero))) ∧̇ (var zero ≐ con Sq) )
           ∨̇ ( (con ∅ʟ ∈̇ var (suc zero))
             ∧̇ ( (var zero ∈̇ con A) ∧̇ predAt zero (suc zero) ) )

    code-out : (R α : SL.S) → ⟨ (R ∷ α ∷ []) ⊨ codeFo ⟩ → ∥ LeftOf R α ⊎ RightOf R α ∥₁
    code-out R α = PT.map
      (λ { (inl (n , e)) → inl (n , e)
         ; (inr (h , (hA , p))) → inr (h , hA , pred-out zero (suc zero) (R ∷ α ∷ []) p) })

    code-left : (R α : SL.S) → LeftOf R α → ⟨ (R ∷ α ∷ []) ⊨ codeFo ⟩
    code-left R α (n , e) = ∣ inl (n , e) ∣₁

    code-right : (R α : SL.S) → RightOf R α → ⟨ (R ∷ α ∷ []) ⊨ codeFo ⟩
    code-right R α (h , hA , c) =
      ∣ inr (h , (hA , pred-in zero (suc zero) (R ∷ α ∷ []) c)) ∣₁

  -- THE FIRST MAP, δ → A.
  module Map1 where

    -- A witness at the site: a code when ∅ ∈ α, and Sq otherwise.
    have : (α : SL.S) (mα : ⟨ fst α ∈ fst δ ⟩)
         → ∥ Σ[ R ∈ SL.S ] (⟨ fst R ∈ Lset β ⟩ × ⟨ (R ∷ α ∷ []) ⊨ codeFo ⟩) ∥₁
    have α mα = go (lem (∅ ∈ fst α))
      where
      from : (h : ⟨ ∅ ∈ fst α ⟩) → Σ[ Ff ∈ SL.S ] InjCode Ff α κ
           → Σ[ R ∈ SL.S ] (⟨ fst R ∈ Lset β ⟩ × ⟨ (R ∷ α ∷ []) ⊨ codeFo ⟩)
      from h (Ff , code) = E.R , site E.R E.R∈A , code-right E.R α (h , E.R∈A , E.codes)
        where
        module E = At.Exist α mα h Ff code using ( R; R∈A; codes )
      go : ⟨ ∅ ∈ fst α ⟩ ⊎ (⟨ ∅ ∈ fst α ⟩ → Empty.⊥)
         → ∥ Σ[ R ∈ SL.S ] (⟨ fst R ∈ Lset β ⟩ × ⟨ (R ∷ α ∷ []) ⊨ codeFo ⟩) ∥₁
      go (inl h) = PT.map (from h) (below-succ-injects κ δ sc α (At.ordα α mα) mα)
      go (inr n) = ∣ Sq , site Sq Sq∈A , code-left Sq α (n , refl) ∣₁

    module Ls = Least β oβ δ codeFo have using ( fn; fn-holds; Dmap )

    fn : (α : SL.S) → ⟨ fst α ∈ fst δ ⟩ → SL.S
    fn = Ls.fn

    -- The value, read at the predicate.
    fn-read : (α : SL.S) (mα : ⟨ fst α ∈ fst δ ⟩) → ∥ LeftOf (fn α mα) α ⊎ RightOf (fn α mα) α ∥₁
    fn-read α mα = code-out (fn α mα) α (Ls.fn-holds α mα)

    -- The value is a member of A, in both cases.
    fn∈A : (α : SL.S) (mα : ⟨ fst α ∈ fst δ ⟩) → ⟨ fst (fn α mα) ∈ fst A ⟩
    fn∈A α mα = PT.rec (snd (fst (fn α mα) ∈ fst A))
      (λ { (inl (_ , e)) → subst (λ w → ⟨ w ∈ fst A ⟩) (sym e) Sq∈A
         ; (inr (_ , hA , _)) → hA })
      (fn-read α mα)

    M : DefinableMap
    M = record Ls.Dmap { cod = A ; into = fn∈A }

    inj : (α : SL.S) (mα : ⟨ fst α ∈ fst δ ⟩) (α' : SL.S) (mα' : ⟨ fst α' ∈ fst δ ⟩)
        → fst (fn α mα) ≡ fst (fn α' mα') → fst α ≡ fst α'
    inj α mα α' mα' q = PT.rec2 (setIsSet (fst α) (fst α')) go (fn-read α mα) (fn-read α' mα')
      where
      go : LeftOf (fn α mα) α ⊎ RightOf (fn α mα) α
         → LeftOf (fn α' mα') α' ⊎ RightOf (fn α' mα') α' → fst α ≡ fst α'
      go (inl (n , _)) (inl (n' , _)) =
        ord-∅ (fst α) (At.ordα α mα) n ∙ sym (ord-∅ (fst α') (At.ordα α' mα') n')
      go (inl (_ , e)) (inr (_ , _ , c')) =
        Empty.rec (noCodesSq α' (subst (λ w → Codes w α') (S≡ {fn α' mα'} {Sq} (sym q ∙ e)) c'))
      go (inr (_ , _ , c)) (inl (_ , e')) =
        Empty.rec (noCodesSq α (subst (λ w → Codes w α) (S≡ {fn α mα} {Sq} (q ∙ e')) c))
      go (inr (_ , _ , c)) (inr (_ , _ , c')) =
        values-unique (fn α mα) α α' c (subst (λ w → Codes w α') (S≡ {fn α' mα'} {fn α mα} (sym q)) c')

    injL : InjL δ A
    injL = Inj.injL M inj

  -- -------------------------------------------------------------------
  -- 3.5  THE SECOND MAP, A → 𝒫 κ: the image under a coded pairing.
  -- -------------------------------------------------------------------

  module Image (zf : ModelL.isZFModel) (G : SL.S) (code : InjCode G Sq κ) where

    open ModelL.isZFModel zf using ( 𝒫 )

    γG : SL.S ^ 2
    γG = G ∷ Sq ∷ []

    ranG : (p z : SL.S) → Holds G p z → ⟨ fst z ∈ fst κ ⟩
    ranG = code .snd .snd .snd

    valG : (p : SL.S) → ⟨ fst p ∈ fst Sq ⟩ → ∥ Σ[ z ∈ SL.S ] Holds G p z ∥₁
    valG = domAt-in zero (suc zero) γG (code .snd .fst)

    injG : (z p p' : SL.S) → Holds G p z → Holds G p' z → fst p ≡ fst p'
    injG = injAt-out zero γG (code .snd .snd .fst)

    InImg : SL.S → SL.S → Type (ℓ-suc ℓ)
    InImg R z = ∥ Σ[ p ∈ SL.S ] (⟨ fst p ∈ fst R ⟩ × Holds G p z) ∥₁

    -- Over (z ∷ []) with R a constant: "z is the value at some member
    -- of R".  Inside: p is 0, z is 1.
    opaque
      φI : SL.S → Formula SL.S 1
      φI R = ∃̇∈ (con R) (appC G zero (suc zero))

      φI-out : (R z : SL.S) → ⟨ (z ∷ []) ⊨ φI R ⟩ → InImg R z
      φI-out R z = PT.map (λ { (p , (mp , q)) →
        p , mp , transport (cong ⟨_⟩ (appC-adequate G zero (suc zero) (p ∷ z ∷ []))) q })

      φI-in : (R z : SL.S) → InImg R z → ⟨ (z ∷ []) ⊨ φI R ⟩
      φI-in R z = PT.map (λ { (p , mp , q) →
        p , (mp , transport (sym (cong ⟨_⟩ (appC-adequate G zero (suc zero) (p ∷ z ∷ [])))) q) })

    img : SL.S → SL.S
    img R = fst (fst (hasSeparationL κ (φI R)))

    img-spec : (R z : SL.S) → (z SL.∈ˢ img R) ≡ ((z SL.∈ˢ κ) ⊓ ((z ∷ []) ⊨ φI R))
    img-spec R = snd (fst (hasSeparationL κ (φI R)))

    img⊆κ : (R : SL.S) (z : SL.S) → ⟨ fst z ∈ fst (img R) ⟩ → ⟨ fst z ∈ fst κ ⟩
    img⊆κ R z h = subst ⟨_⟩ (img-spec R z) h .fst

    img-out : (R z : SL.S) → ⟨ fst z ∈ fst (img R) ⟩ → InImg R z
    img-out R z h = φI-out R z (subst ⟨_⟩ (img-spec R z) h .snd)

    img-in : (R z : SL.S) → InImg R z → ⟨ fst z ∈ fst (img R) ⟩
    img-in R z i = subst ⟨_⟩ (sym (img-spec R z)) (zκ , φI-in R z i)
      where
      zκ : ⟨ fst z ∈ fst κ ⟩
      zκ = PT.rec (snd (fst z ∈ fst κ)) (λ { (p , _ , q) → ranG p z q }) i

    -- THE GRAPH, over (s ∷ R ∷ []): "the members of s are exactly the
    -- values at the members of R".  Inside the ∀̇: z is 0, s is 1, R is
    -- 2; inside the bounded binder: p is 0, z is 1, s is 2, R is 3.
    Graph2 : SL.S → SL.S → Type (ℓ-suc ℓ)
    Graph2 s R = (z : SL.S) → (⟨ fst z ∈ fst s ⟩ → InImg R z) × (InImg R z → ⟨ fst z ∈ fst s ⟩)

    opaque
      graph2 : Formula SL.S 2
      graph2 = ∀̇ ( ((var zero ∈̇ var (suc zero)) ⇒̇ ∃̇∈ (var (suc (suc zero))) (appC G zero (suc zero)))
                 ∧̇ (∃̇∈ (var (suc (suc zero))) (appC G zero (suc zero)) ⇒̇ (var zero ∈̇ var (suc zero))) )

      private
        ex-out : (s R z : SL.S)
               → ⟨ (z ∷ s ∷ R ∷ []) ⊨ ∃̇∈ (var (suc (suc zero))) (appC G zero (suc zero)) ⟩
               → InImg R z
        ex-out s R z = PT.map (λ { (p , (mp , q)) →
          p , mp , transport (cong ⟨_⟩ (appC-adequate G zero (suc zero) (p ∷ z ∷ s ∷ R ∷ []))) q })

        ex-in : (s R z : SL.S) → InImg R z
              → ⟨ (z ∷ s ∷ R ∷ []) ⊨ ∃̇∈ (var (suc (suc zero))) (appC G zero (suc zero)) ⟩
        ex-in s R z = PT.map (λ { (p , mp , q) →
          p , (mp , transport (sym (cong ⟨_⟩ (appC-adequate G zero (suc zero) (p ∷ z ∷ s ∷ R ∷ [])))) q) })

      graph2-out : (s R : SL.S) → ⟨ (s ∷ R ∷ []) ⊨ graph2 ⟩ → Graph2 s R
      graph2-out s R h z = (λ m → ex-out s R z (h z .fst m)) , (λ i → h z .snd (ex-in s R z i))

      graph2-in : (s R : SL.S) → Graph2 s R → ⟨ (s ∷ R ∷ []) ⊨ graph2 ⟩
      graph2-in s R h z = (λ m → ex-in s R z (h z .fst m)) , (λ i → h z .snd (ex-out s R z i))

    defines : (R : SL.S) → ⟨ fst R ∈ fst A ⟩ → ⟨ (img R ∷ R ∷ []) ⊨ graph2 ⟩
    defines R _ = graph2-in (img R) R (λ z → img-out R z , img-in R z)

    only : (R : SL.S) → ⟨ fst R ∈ fst A ⟩ → (y : SL.S)
         → ⟨ (y ∷ R ∷ []) ⊨ graph2 ⟩ → y ≡ img R
    only R _ y h = S≡ (extensionalV {a = fst y} {b = fst (img R)} (λ w → ⇔toPath (fwd w) (bwd w)))
      where
      g : Graph2 y R
      g = graph2-out y R h

      fwd : (w : SV.S) → ⟨ w ∈ fst y ⟩ → ⟨ w ∈ fst (img R) ⟩
      fwd w w∈ = img-in R wS (g wS .fst w∈)
        where
        wS : SL.S
        wS = w , isL-trans {x = fst y} {y = w} w∈ (snd y)

      bwd : (w : SV.S) → ⟨ w ∈ fst (img R) ⟩ → ⟨ w ∈ fst y ⟩
      bwd w w∈ = g wS .snd (img-out R wS w∈)
        where
        wS : SL.S
        wS = w , isL-trans {x = fst (img R)} {y = w} w∈ (snd (img R))

    -- Injective: g is, and every member of R ∈ A has a value under g.
    half : (R : SL.S) → ⟨ fst R ∈ fst A ⟩ → (R' : SL.S)
         → fst (img R) ≡ fst (img R')
         → (w : SV.S) → ⟨ w ∈ fst R ⟩ → ⟨ w ∈ fst R' ⟩
    half R mR R' e w w∈ = PT.rec (snd (w ∈ fst R')) (λ { (z , q) →
        PT.rec (snd (w ∈ fst R'))
          (λ { (p' , mp' , q') → subst (λ t → ⟨ t ∈ fst R' ⟩) (sym (injG z wS p' q q')) mp' })
          (img-out R' z (subst (λ t → ⟨ fst z ∈ t ⟩) e (img-in R z ∣ wS , w∈ , q ∣₁))) })
      (valG wS (A-out R mR wS w∈))
      where
      wS : SL.S
      wS = w , isL-trans {x = fst R} {y = w} w∈ (snd R)

    inj : (R : SL.S) → ⟨ fst R ∈ fst A ⟩ → (R' : SL.S) → ⟨ fst R' ∈ fst A ⟩
        → fst (img R) ≡ fst (img R') → fst R ≡ fst R'
    inj R m R' m' e = extensionalV {a = fst R} {b = fst R'}
      (λ w → ⇔toPath (half R m R' e w) (half R' m' R (sym e) w))

    M : DefinableMap
    M = record
      { dom     = A
      ; cod     = 𝒫 κ
      ; fn      = λ R _ → img R
      ; into    = λ R _ → into-power zf κ (img R) (img⊆κ R)
      ; graph   = graph2
      ; defines = defines
      ; only    = only }

    injL : InjL A (𝒫 κ)
    injL = Inj.injL M inj

  -- -------------------------------------------------------------------
  -- 3.6  THE PAIRING AT κ.  κ need not be an L-cardinal: at its
  --      internal cardinal μ the square law of src/L/GCH/Pairing holds,
  --      and prodL κ ↪ prodL μ ↪ μ ↪ κ.  μ is infinite because κ is and
  --      κ ↪ μ, and the induction there needs no more than that.
  -- -------------------------------------------------------------------

  pairing : InjL Sq κ
  pairing = PT.rec squash₁ build (cardOf κ ordκ)
    where
    build : Σ[ μ ∈ SL.S ]
              ( IsOrd (fst μ) × IsCardinalL μ
              × ((z : SV.S) → ⟨ z ∈ˢ fst μ ⟩ → ⟨ z ∈ˢ fst κ ⟩)
              × InjL κ μ × InjL μ κ )
          → InjL Sq κ
    build (μ , oμ , cardμ , _ , κ↪μ , μ↪κ) =
      injl-trans Sq (prodL μ) κ (prod-inj κ μ κ↪μ)
        (injl-trans (prodL μ) μ κ
          (WF.WFI.induction regularityV {P = Goal} Step.result (fst μ) (snd μ) oμ cardμ μ∉ω)
          μ↪κ)
      where
      μ∉ω : ⟨ fst μ ∈ˢ ω ⟩ → Empty.⊥
      μ∉ω h = no-fin κ μ ordκ κ∉ω oμ h κ↪μ

  module Final (zf : ModelL.isZFModel) where

    open ModelL.isZFModel zf using ( 𝒫 )

    result : InjL δ (𝒫 κ)
    result = PT.rec squash₁
      (λ { (G , code) → injl-trans δ A (𝒫 κ) Map1.injL (Image.injL zf G code) })
      pairing
```

SECTION 4.  HYPOTHESIS 3 OF src/L/GCH/Assembly.lagda.md, discharged.

```agda
succ-into-power : (zf : ModelL.isZFModel) → SuccIntoPower zf
succ-into-power zf κ δ κ∉ω sc = Main.Final.result κ δ κ∉ω sc zf
```
