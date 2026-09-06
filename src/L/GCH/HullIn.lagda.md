# The Skolem hull and its collapse are elements of L

```agda
{-# OPTIONS --cubical --safe --guardedness #-}

open import Base.Prelude
open import Base.Truth
open import Base.Classical using ( LEM )

module L.GCH.HullIn {ℓ : Level} (lem : LEM (ℓ-suc ℓ)) where

open import FOL.ZFStructure using ( module hPropStructure )
open import FOL.Syntax
  using ( Formula; var; con; _∈̇_; _≐_; _∧̇_; _∨̇_; _⇒̇_; ¬̇_; ∃̇_; ∀̇_; ∀̇∈; ⊥̇ )
open import FOL.Manipulation.Relabelling using ( mapFo; mapFo-comp; ⊨-map )
open import FOL.Manipulation.Renaming using ( renameFo; module Sat )
import FOL.Absoluteness
import FOL.Semantics
open import V.Hierarchy {ℓ} using ( 𝒮ᵥ; ∈-induction; extensionalV )
open import V.Presentation {ℓ} using ( member; fiber )
open import V.Coding {ℓ} using ( pr; pr-inj; module VCode )
open import V.Collapse {ℓ} using ( module Collapse )
open import L.Constructible {ℓ}
  using ( 𝒮ʟ; isL; isL-trans; IsOrd; Lset; Lset-out; Lset→isL; 𝒟ₒ; 𝒟ₒ∋⊆
        ; Lset-layer; layer-trans )
open import L.Ordinal {ℓ} using ( mem-ord; #∈ω )
open import L.Axioms.Basic {ℓ} using ( LsetS; ∅ʟ )
open import L.Axioms.Full {ℓ} lem using ( hasSeparationL )
open import L.Axioms.Infinity {ℓ} lem using ( ωʟ; ω-specL )
open import L.Axioms.Numerals {ℓ} using ( numeralL-fst; pairʟ; unionʟ )
open import L.Recursion {ℓ} lem using ( Recursion; module Of; mereFunct )
open import L.Definability {ℓ} using ( module DefOf )
open import L.Coding.Model {ℓ}
  using ( prAtL; prAtL-adequate; prʟ; prʟ-fst; numL; sucAtL; sucAtL-adequate
        ; consAtL; consAtL-adequate; envOverAt; envOverAt-transport )
open import L.Coding.Environment {ℓ} using ( env; cons )
open import L.Coding.EnvSet {ℓ} lem using ( envS; Ix; envOver; module Recover )
open import L.Coding.Bridge {ℓ} lem using ( graph; envFor; envFor-graph )
open import L.Coding.CodeSet {ℓ} lem using ( AllCodes; keyS; key∈AllCodes )
open import L.Coding.Uniform {ℓ} lem using ( val-sat )
open import L.Choice.Name {ℓ} lem using ( limitCode )
open import L.Choice.Internal {ℓ} lem using ( freeCode-in; freeCode-out )
open import L.Choice.Order {ℓ} lem using ( relL; relL-fill; relL-rep )
open import L.Choice.Step {ℓ} lem using ( orderAt; relOf )
open import L.WellOrder.Base {ℓ-suc ℓ} using ( SWO; IsLeast; leastOf; isPropLeastOf )
open import L.GCH.Pairing {ℓ} lem using ( prodL; prodL-in; prodL-out; isL-ord )
open import L.GCH.OrderType {ℓ} lem
  using ( Holds; Complete; Src; ValueIs; Correct
        ; completeAt; complete-in; complete-out
        ; valueAt; value-in; value-out
        ; correctAt; correct-in; correct-out
        ; module PairFo )
open import L.GCH.OmegaRec {ℓ} lem
  using ( module Iterate; pairʟ-in; unionʟ-in )
open import L.GCH.Hull {ℓ} lem using ( module HullStage; module Frame )
open import L.InjChain {ℓ} lem using ( appC; appC-adequate )
open import L.GCH.Complete {ℓ} lem using ( Superadequate )
open import L.GCH.SatFrame {ℓ} lem using ( module SatGraph )
open import L.GCH.Condense {ℓ} lem using ( module Condense )

open import Cubical.Data.Sigma using ( _×_; Σ≡Prop )
open import Cubical.Data.Nat.Properties using ( max )
open import Cubical.Data.Nat.Order using ( _≤_; left-≤-max; right-≤-max )
open import Cubical.Data.Sum using ( _⊎_; inl; inr )
import Cubical.Data.Sum as Sum
import Cubical.Data.Empty as Empty
open import Cubical.Foundations.Prelude using ( subst2; J )
open import Cubical.Data.Vec using ( Vec; _∷_; []; lookup )
open import Cubical.HITs.CumulativeHierarchy.Constructions
  using ( ∅; ⁅_,_⁆; ⁅_⁆s; module InfinitySet )
open import V.Model {ℓ} using ( pair-spec )
open InfinitySet {ℓ} using ( sucV; #_ )
open import Cubical.Foundations.HLevels
  using ( isProp×; isPropΣ; isPropΠ; isPropΠ2; isSetΣSndProp )
open import Cubical.Functions.Logic using ( ⇔toPath )
import Cubical.HITs.PropositionalTruncation as PT
open PT using ( ∥_∥₁; ∣_∣₁; squash₁ )
open import Cubical.HITs.CumulativeHierarchy.Base using ( V; setIsSet )
open import Cubical.HITs.CumulativeHierarchy.Properties using ( ⟪_⟫; ⟪_⟫↪; ∈∈ₛ )

open TruthAlgebra (hPropAlgebra (ℓ-suc ℓ))
open hPropStructure 𝒮ᵥ
```

The 𝒮ʟ carrier, for the syntax of every formula below.

```agda
module CS = hPropStructure 𝒮ʟ using ( S; _∈ˢ_ )

module AbsL = FOL.Absoluteness.Single 𝒮ᵥ isL isL-trans using ( _^_; _⊨ᵐ_ )
open AbsL using ( _^_ ) renaming ( _⊨ᵐ_ to _⊨_ )
```

Renaming, read at the same satisfaction as `_⊨_` (as `OmegaRec` does).

```agda
module Ren = Sat (hPropAlgebra (ℓ-suc ℓ)) 𝒮ʟ id using ( Agrees; ⊨-rename )

private
  i0 : ∀ {k} → Fin (suc k)
  i0 = zero
  i1 : ∀ {k} → Fin (suc (suc k))
  i1 = suc i0
  i2 : ∀ {k} → Fin (suc (suc (suc k)))
  i2 = suc i1
  i3 : ∀ {k} → Fin (suc (suc (suc (suc k))))
  i3 = suc i2
  i4 : ∀ {k} → Fin (suc (suc (suc (suc (suc k)))))
  i4 = suc i3
  i5 : ∀ {k} → Fin (suc (suc (suc (suc (suc (suc k))))))
  i5 = suc i4
  i6 : ∀ {k} → Fin (suc (suc (suc (suc (suc (suc (suc k)))))))
  i6 = suc i5

  S≡ : {x y : CS.S} → fst x ≡ fst y → x ≡ y
  S≡ = Σ≡Prop (λ v → snd (isL v))

  isSetSʟ : isSet CS.S
  isSetSʟ = isSetΣSndProp setIsSet (λ v → snd (isL v))
```

The two renamings of the witness formula and their agreements, at the top level.
Measured in this file: the same clauses cost 0.24-0.41 s per definition inside
`Telescope.Build`.

```agda
  ρs : Fin 2 → Fin 2
  ρs zero = suc zero
  ρs (suc zero) = zero

  ρf : Fin 2 → Fin 3
  ρf zero = zero
  ρf (suc zero) = suc (suc zero)

  ags : (Z'' w : CS.S) → Ren.Agrees ρs (Z'' ∷ w ∷ []) (w ∷ Z'' ∷ [])
  ags Z'' w zero = refl
  ags Z'' w (suc zero) = refl

  agf : (w Z' Z : CS.S) → Ren.Agrees ρf (w ∷ Z' ∷ Z ∷ []) (w ∷ Z ∷ [])
  agf w Z' Z zero = refl
  agf w Z' Z (suc zero) = refl
```

## Section 1. The collapse of a carrier that is an element of L lands in L

Generic in the carrier `M`. The graph of the collapse on `M` is read by
src/L/GCH/OrderType.lagda.md's three table formulas at the membership relation
of `M`; that chapter's `Graph` is not used, since its `col-isL` rests on
`col-ord`, which needs the relation to be transitive, and a hull is not. Here
the L-membership of a collapse value is proved by an induction on the stage of
the argument: the values at the slice `M ∩ Lset δ` form one table in L, and the
value at a member born at `δ` is the image of that table at it.

```agda
module PiIn (Mʟ : CS.S) where

  M : S
  M = fst Mʟ

  module C = Collapse M using ( Fiber; π; π-compute; πX; πX-member; π∈-fwd )

  memL : (y : S) → ⟨ y ∈ˢ M ⟩ → ⟨ isL y ⟩
  memL y y∈M = isL-trans {x = M} {y = y} y∈M (snd Mʟ)

  up : (y : S) → ⟨ y ∈ˢ M ⟩ → CS.S
  up y y∈M = y , memL y y∈M
```

A member of a collapse value is the collapse of a member of the argument that
lies in `M` (`π-compute`, with the fibre kept).

```agda
  π-mem-out : (x w : S) → ⟨ w ∈ˢ C.π x ⟩
            → ∥ Σ[ y ∈ S ] (⟨ y ∈ˢ x ⟩ × ⟨ y ∈ˢ M ⟩ × (C.π y ≡ w)) ∥₁
  π-mem-out x w w∈ = PT.map mk (subst (λ u → ⟨ w ∈ˢ u ⟩) (C.π-compute x) w∈)
    where
    mk : Σ[ p ∈ C.Fiber x ] (C.π (⟪ x ⟫↪ (p .fst)) ≡ w)
       → Σ[ y ∈ S ] (⟨ y ∈ˢ x ⟩ × ⟨ y ∈ˢ M ⟩ × (C.π y ≡ w))
    mk (p , q) = ⟪ x ⟫↪ (p .fst)
               , ( member x (p .fst)
                 , ∈∈ₛ {a = ⟪ x ⟫↪ (p .fst)} {b = M} .snd (p .snd)
                 , q )
```

THE MEMBERSHIP RELATION OF `M`, as a set of pairs in L: carved out of the
product by "z is the pair of a member of a member". Inside the two binders: `x`
is 0, `y` is 1, `z` is 2.

```agda
  opaque
    memFo : Formula CS.S 1
    memFo = ∃̇ (∃̇ ( prAtL i2 i1 i0 ∧̇ (var i1 ∈̇ var i0) ))

    private
      at : (x y z : CS.S)
         → ⟨ (x ∷ y ∷ z ∷ []) ⊨ prAtL i2 i1 i0 ⟩ ≡ (fst z ≡ pr (fst y) (fst x))
      at x y z = cong ⟨_⟩ (prAtL-adequate i2 i1 i0 (x ∷ y ∷ z ∷ []))

    R : CS.S
    R = hasSeparationL (prodL Mʟ) memFo .fst .fst

    R-mem : (z : CS.S)
          → (z CS.∈ˢ R) ≡ ((z CS.∈ˢ prodL Mʟ) ⊓ ((z ∷ []) ⊨ memFo))
    R-mem = hasSeparationL (prodL Mʟ) memFo .fst .snd

    R-in : (y x : CS.S) → ⟨ fst y ∈ˢ M ⟩ → ⟨ fst x ∈ˢ M ⟩ → ⟨ fst y ∈ˢ fst x ⟩
         → Holds R y x
    R-in y x my mx yx =
      subst (λ w → ⟨ w ∈ˢ fst R ⟩) (prʟ-fst y x)
        (subst ⟨_⟩ (sym (R-mem (prʟ y x)))
          ( subst (λ w → ⟨ w ∈ˢ fst (prodL Mʟ) ⟩) (sym (prʟ-fst y x))
              (prodL-in Mʟ y x my mx)
          , ∣ y , ∣ x , (transport (sym (at x y (prʟ y x))) (prʟ-fst y x) , yx) ∣₁ ∣₁ ))

    R-out : (y x : CS.S) → Holds R y x
          → ⟨ fst y ∈ˢ M ⟩ × ⟨ fst x ∈ˢ M ⟩ × ⟨ fst y ∈ˢ fst x ⟩
    R-out y x h = mems .fst , (mems .snd , mem)
      where
      both : ⟨ prʟ y x CS.∈ˢ prodL Mʟ ⟩ × ⟨ (prʟ y x ∷ []) ⊨ memFo ⟩
      both = subst ⟨_⟩ (R-mem (prʟ y x))
               (subst (λ w → ⟨ w ∈ˢ fst R ⟩) (sym (prʟ-fst y x)) h)

      mems : ⟨ fst y ∈ˢ M ⟩ × ⟨ fst x ∈ˢ M ⟩
      mems = PT.rec (isProp× (snd (fst y ∈ˢ M)) (snd (fst x ∈ˢ M)))
        (λ { (a , b , ma , mb , q) →
           let e = pr-inj (sym (prʟ-fst y x) ∙ q)
           in subst (λ w → ⟨ w ∈ˢ M ⟩) (sym (e .fst)) ma
            , subst (λ w → ⟨ w ∈ˢ M ⟩) (sym (e .snd)) mb })
        (prodL-out Mʟ (prʟ y x) (both .fst))

      mem : ⟨ fst y ∈ˢ fst x ⟩
      mem = PT.rec (snd (fst y ∈ˢ fst x))
        (λ { (y' , hy') → PT.rec (snd (fst y ∈ˢ fst x))
          (λ { (x' , (q , m)) →
             let e = pr-inj (sym (prʟ-fst y x) ∙ transport (at x' y' (prʟ y x)) q)
             in subst2 (λ u v → ⟨ u ∈ˢ v ⟩) (sym (e .fst)) (sym (e .snd)) m })
          hy' })
        (both .snd)
```

THE GRAPH FORMULA, over `(v ∷ p ∷ [])`: "some set correct for the membership of
`M` is complete at p, and v is its value at p". Inside: `r` is 0, `v` is 1, `p`
is 2; then `F` is 0, `r` is 1, `v` is 2, `p` is 3.

```agda
  opaque
    piFo : Formula CS.S 2
    piFo = ∃̇ ( (var i0 ≐ con R)
             ∧̇ ∃̇ ( correctAt i0 i1
                  ∧̇ ( completeAt i0 i1 i3 ∧̇ valueAt i0 i1 i3 i2 ) ) )

    piFo-out : (v p : CS.S) → ⟨ (v ∷ p ∷ []) ⊨ piFo ⟩
             → ∥ Σ[ F ∈ CS.S ] (Correct F R × (Complete F R p × ValueIs F R p v)) ∥₁
    piFo-out v p = PT.rec squash₁ (λ { (r , (er , hf)) → PT.map
      (λ { (F , (hc , (hm , hv))) → F
        , ( subst (Correct F) (S≡ {x = r} {y = R} er)
              (correct-out i0 i1 (F ∷ r ∷ v ∷ p ∷ []) hc)
          , ( subst (λ r' → Complete F r' p) (S≡ {x = r} {y = R} er)
                (complete-out i0 i1 i3 (F ∷ r ∷ v ∷ p ∷ []) hm)
            , subst (λ r' → ValueIs F r' p v) (S≡ {x = r} {y = R} er)
                (value-out i0 i1 i3 i2 (F ∷ r ∷ v ∷ p ∷ []) hv) ) ) })
      hf })

    piFo-in : (v p F : CS.S) → Correct F R → Complete F R p → ValueIs F R p v
            → ⟨ (v ∷ p ∷ []) ⊨ piFo ⟩
    piFo-in v p F hc hm hv = ∣ R , (refl , ∣ F
      , ( correct-in i0 i1 (F ∷ R ∷ v ∷ p ∷ []) hc
        , ( complete-in i0 i1 i3 (F ∷ R ∷ v ∷ p ∷ []) hm
          , value-in i0 i1 i3 i2 (F ∷ R ∷ v ∷ p ∷ []) hv ) ) ∣₁) ∣₁
```

UNIQUENESS. A value that is complete and right relative to a correct set is the
collapse. One membership induction.

```agda
  private
    Pv : CS.S → S → Type (ℓ-suc ℓ)
    Pv F x = (xL : ⟨ isL x ⟩) → ⟨ x ∈ˢ M ⟩ → (v : CS.S)
           → Complete F R (x , xL) → ValueIs F R (x , xL) v → fst v ≡ C.π x

  value-val′ : (F : CS.S) → Correct F R → (x : S) → Pv F x
  value-val′ F hc = ∈-induction {P = Pv F} go
    where
    go : (x : S) → ((y : S) → ⟨ y ∈ˢ x ⟩ → Pv F y) → Pv F x
    go x IH xL x∈M v cmp val =
      extensionalV {a = fst v} {b = C.π x} (λ w → ⇔toPath (fwd w) (bwd w))
      where
      xS : CS.S
      xS = x , xL

      fwd : (w : S) → ⟨ w ∈ˢ fst v ⟩ → ⟨ w ∈ˢ C.π x ⟩
      fwd w w∈ = PT.rec (snd (w ∈ˢ C.π x)) read (val wS .fst w∈)
        where
        wS : CS.S
        wS = w , isL-trans {x = fst v} {y = w} w∈ (snd v)
        read : Σ[ y ∈ CS.S ] (Holds R y xS × Holds F y wS) → ⟨ w ∈ˢ C.π x ⟩
        read (y , (ry , fy)) =
          subst (λ t → ⟨ t ∈ˢ C.π x ⟩) e (C.π∈-fwd x (fst y) y∈x y∈M)
          where
          y∈M : ⟨ fst y ∈ˢ M ⟩
          y∈M = R-out y xS ry .fst
          y∈x : ⟨ fst y ∈ˢ x ⟩
          y∈x = R-out y xS ry .snd .snd
          e : C.π (fst y) ≡ w
          e = sym (IH (fst y) y∈x (snd y) y∈M wS (hc y wS fy .fst) (hc y wS fy .snd))

      bwd : (w : S) → ⟨ w ∈ˢ C.π x ⟩ → ⟨ w ∈ˢ fst v ⟩
      bwd w w∈ = PT.rec (snd (w ∈ˢ fst v)) read (π-mem-out x w w∈)
        where
        read : Σ[ y ∈ S ] (⟨ y ∈ˢ x ⟩ × ⟨ y ∈ˢ M ⟩ × (C.π y ≡ w)) → ⟨ w ∈ˢ fst v ⟩
        read (y , (y∈x , y∈M , e)) = PT.rec (snd (w ∈ˢ fst v)) inner (cmp yS ry)
          where
          yS : CS.S
          yS = up y y∈M
          ry : Holds R yS xS
          ry = R-in yS xS y∈M x∈M y∈x
          inner : Σ[ u ∈ CS.S ] Holds F yS u → ⟨ w ∈ˢ fst v ⟩
          inner (u , fu) =
            subst (λ t → ⟨ t ∈ˢ fst v ⟩) (eu ∙ e) (val u .snd ∣ yS , (ry , fu) ∣₁)
            where
            eu : fst u ≡ C.π y
            eu = IH y y∈x (snd yS) y∈M u (hc yS u fu .fst) (hc yS u fu .snd)

  value-val : (F : CS.S) → Correct F R → (x : CS.S) → ⟨ fst x ∈ˢ M ⟩ → (v : CS.S)
            → Complete F R x → ValueIs F R x v → fst v ≡ C.π (fst x)
  value-val F hc x = value-val′ F hc (fst x) (snd x)
```

The graph formula, read at a member of `M`.

```agda
  piFo-val : (q : CS.S) → ⟨ fst q ∈ˢ M ⟩ → (v : CS.S) → ⟨ (v ∷ q ∷ []) ⊨ piFo ⟩
           → fst v ≡ C.π (fst q)
  piFo-val q mq v h = PT.rec (setIsSet (fst v) (C.π (fst q)))
    (λ { (F , (hc , (hm , hv))) → value-val F hc q mq v hm hv })
    (piFo-out v q h)
```

A SLICE OF `M`: the members of `M` that lie in a given element `K` of L, as an
element of L.

```agda
  module Cut (K : CS.S) where

    cutFo : Formula CS.S 1
    cutFo = var i0 ∈̇ con K

    opaque
      cut : CS.S
      cut = hasSeparationL Mʟ cutFo .fst .fst

      cut-mem : (y : CS.S) → (y CS.∈ˢ cut) ≡ ((y CS.∈ˢ Mʟ) ⊓ ((y ∷ []) ⊨ cutFo))
      cut-mem = hasSeparationL Mʟ cutFo .fst .snd

      cut-in : (y : CS.S) → ⟨ fst y ∈ˢ M ⟩ → ⟨ fst y ∈ˢ fst K ⟩ → ⟨ y CS.∈ˢ cut ⟩
      cut-in y my yK = subst ⟨_⟩ (sym (cut-mem y)) (my , yK)

      cut-out : (y : CS.S) → ⟨ y CS.∈ˢ cut ⟩ → ⟨ fst y ∈ˢ M ⟩ × ⟨ fst y ∈ˢ fst K ⟩
      cut-out y h = subst ⟨_⟩ (cut-mem y) h
```

THE INDUCTION. At an ordinal `δ`: every member of `M` in `Lset δ` has its
collapse in L, and the graph formula holds there. The hypothesis at `δ' ∈ δ`
gives one table of pairs over the slice `M ∩ Lset δ'`, and that table is correct
because the slice is closed under membership within `M`.

```agda
  Good : S → S → Type (ℓ-suc ℓ)
  Good δ q = ⟨ q ∈ˢ M ⟩ → ⟨ q ∈ˢ Lset δ ⟩
           → Σ[ qL ∈ ⟨ isL (C.π q) ⟩ ] ((mq : ⟨ q ∈ˢ M ⟩)
                → ⟨ ((C.π q , qL) ∷ up q mq ∷ []) ⊨ piFo ⟩)

  isPropGood : (δ q : S) → isProp (Good δ q)
  isPropGood δ q = isPropΠ2 λ _ _ → isPropΣ (snd (isL (C.π q)))
    λ qL → isPropΠ λ mq → snd (((C.π q , qL) ∷ up q mq ∷ []) ⊨ piFo)

  module Step (δ' : S) (oδ' : IsOrd δ')
              (IH : (q : S) → Good δ' q) where

    module Sl = Cut (LsetS δ' oδ') using ( cut; cut-in; cut-out )

    Lδ'-trans : {x y : S} → ⟨ y ∈ˢ x ⟩ → ⟨ x ∈ˢ Lset δ' ⟩ → ⟨ y ∈ˢ Lset δ' ⟩
    Lδ'-trans {x} {y} = layer-trans (Lset-layer δ') {x = x} {y = y}
```

The collapse of a slice member, as an element of L.

```agda
    πʟ : (y : CS.S) → ⟨ y CS.∈ˢ Sl.cut ⟩ → CS.S
    πʟ y hy = C.π (fst y) , IH (fst y) (Sl.cut-out y hy .fst) (Sl.cut-out y hy .snd) .fst

    πʟ-graph : (y : CS.S) (hy : ⟨ y CS.∈ˢ Sl.cut ⟩)
             → ⟨ (πʟ y hy ∷ y ∷ []) ⊨ piFo ⟩
    πʟ-graph y hy =
      subst (λ y' → ⟨ (πʟ y hy ∷ y' ∷ []) ⊨ piFo ⟩) (S≡ refl)
        (IH (fst y) my (Sl.cut-out y hy .snd) .snd my)
      where
      my : ⟨ fst y ∈ˢ M ⟩
      my = Sl.cut-out y hy .fst

    module PF = PairFo piFo using ( pairFo; pair-in; pair-out )

    private
      tabR : Recursion
      tabR = record
        { dom   = Sl.cut
        ; graph = PF.pairFo
        ; funct = λ y hy → mereFunct PF.pairFo y (wit y hy) }
        where
        wit : (y : CS.S) (hy : ⟨ y CS.∈ˢ Sl.cut ⟩)
            → ∥ Σ[ e ∈ CS.S ] (⟨ (e ∷ y ∷ []) ⊨ PF.pairFo ⟩
                              × ((e' : CS.S) → ⟨ (e' ∷ y ∷ []) ⊨ PF.pairFo ⟩ → e' ≡ e)) ∥₁
        wit y hy = ∣ prʟ y (πʟ y hy)
          , ( PF.pair-in (prʟ y (πʟ y hy)) y (πʟ y hy) (prʟ-fst y (πʟ y hy)) (πʟ-graph y hy)
            , λ e' he' → PT.rec (isSetSʟ e' (prʟ y (πʟ y hy)))
                (λ { (v , (e , hv)) → S≡
                   (e ∙ cong (pr (fst y)) (piFo-val y (Sl.cut-out y hy .fst) v hv)
                      ∙ sym (prʟ-fst y (πʟ y hy))) })
                (PF.pair-out e' y he') ) ∣₁

      module T = Of tabR using ( table; table-in; table-out )

    Tab : CS.S
    Tab = T.table

    Tab-in : (y : CS.S) (hy : ⟨ y CS.∈ˢ Sl.cut ⟩) → Holds Tab y (πʟ y hy)
    Tab-in y hy = subst (λ w → ⟨ w ∈ˢ fst Tab ⟩) (prʟ-fst y (πʟ y hy))
      (T.table-in y (prʟ y (πʟ y hy)) hy
        (PF.pair-in (prʟ y (πʟ y hy)) y (πʟ y hy) (prʟ-fst y (πʟ y hy)) (πʟ-graph y hy)))

    Tab-pair : (x v : CS.S) → Holds Tab x v
             → ⟨ x CS.∈ˢ Sl.cut ⟩ × (fst v ≡ C.π (fst x))
    Tab-pair x v h = PT.rec (isProp× (snd (x CS.∈ˢ Sl.cut)) (setIsSet (fst v) (C.π (fst x))))
      (λ { (q , (hq , hp)) → PT.rec (isProp× (snd (x CS.∈ˢ Sl.cut)) (setIsSet (fst v) (C.π (fst x))))
        (λ { (z , (e , hz)) →
           let ee = pr-inj (sym (prʟ-fst x v) ∙ e)
           in subst (λ w → ⟨ w CS.∈ˢ Sl.cut ⟩) (S≡ {x = q} {y = x} (sym (ee .fst))) hq
            , ee .snd ∙ piFo-val q (Sl.cut-out q hq .fst) z hz ∙ cong C.π (sym (ee .fst)) })
        (PF.pair-out (prʟ x v) q hp) })
      (T.table-out (prʟ x v) (subst (λ w → ⟨ w ∈ˢ fst Tab ⟩) (sym (prʟ-fst x v)) h))
```

A member is CLOSED when its members in `M` lie in the slice.

```agda
    Closed : CS.S → Type (ℓ-suc ℓ)
    Closed x = (y : S) (y∈x : ⟨ y ∈ˢ fst x ⟩) (y∈M : ⟨ y ∈ˢ M ⟩)
             → ⟨ up y y∈M CS.∈ˢ Sl.cut ⟩

    slice-closed : (x : CS.S) → ⟨ x CS.∈ˢ Sl.cut ⟩ → Closed x
    slice-closed x hx y y∈x y∈M =
      Sl.cut-in (up y y∈M) y∈M (Lδ'-trans {x = fst x} {y = y} y∈x (Sl.cut-out x hx .snd))

    complete-of : (x : CS.S) → Closed x → Complete Tab R x
    complete-of x cl y ry = ∣ πʟ y' hy' , subst (λ w → ⟨ pr w (C.π (fst y)) ∈ˢ fst Tab ⟩) refl (Tab-in y' hy') ∣₁
      where
      ro = R-out y x ry
      y' : CS.S
      y' = up (fst y) (ro .fst)
      hy' : ⟨ y' CS.∈ˢ Sl.cut ⟩
      hy' = cl (fst y) (ro .snd .snd) (ro .fst)

    valueIs-of : (x : CS.S) → ⟨ fst x ∈ˢ M ⟩ → Closed x → (v : CS.S) → fst v ≡ C.π (fst x)
               → ValueIs Tab R x v
    valueIs-of x mx cl v ev w = fwd , bwd
      where
      fwd : ⟨ fst w ∈ˢ fst v ⟩ → Src Tab R x w
      fwd w∈ = PT.map read (π-mem-out (fst x) (fst w) (subst (λ t → ⟨ fst w ∈ˢ t ⟩) ev w∈))
        where
        read : Σ[ y ∈ S ] (⟨ y ∈ˢ fst x ⟩ × ⟨ y ∈ˢ M ⟩ × (C.π y ≡ fst w))
             → Σ[ y ∈ CS.S ] (Holds R y x × Holds Tab y w)
        read (y , (y∈x , y∈M , e)) = up y y∈M
          , ( R-in (up y y∈M) x y∈M mx y∈x
            , subst (λ t → ⟨ pr y t ∈ˢ fst Tab ⟩) e (Tab-in (up y y∈M) (cl y y∈x y∈M)) )

      bwd : Src Tab R x w → ⟨ fst w ∈ˢ fst v ⟩
      bwd = PT.rec (snd (fst w ∈ˢ fst v)) (λ { (y , (ry , ty)) →
        subst2 (λ s t → ⟨ s ∈ˢ t ⟩) (sym (Tab-pair y w ty .snd)) (sym ev)
          (C.π∈-fwd (fst x) (fst y) (R-out y x ry .snd .snd) (R-out y x ry .fst)) })

    Tab-correct : Correct Tab R
    Tab-correct x v hxv = complete-of x cl , valueIs-of x mx cl v (Tab-pair x v hxv .snd)
      where
      hx : ⟨ x CS.∈ˢ Sl.cut ⟩
      hx = Tab-pair x v hxv .fst
      mx : ⟨ fst x ∈ˢ M ⟩
      mx = Sl.cut-out x hx .fst
      cl : Closed x
      cl = slice-closed x hx
```

THE STEP: a member of `M` whose members lie in `Lset δ'` is good.

```agda
    module At (q : S) (mq : ⟨ q ∈ˢ M ⟩) (q⊆ : (y : S) → ⟨ y ∈ˢ q ⟩ → ⟨ y ∈ˢ Lset δ' ⟩) where

      qS : CS.S
      qS = up q mq

      cl : Closed qS
      cl y y∈q y∈M = Sl.cut-in (up y y∈M) y∈M (q⊆ y y∈q)
```

The collapse value itself: the image of the graph over the members of `q` in
`M`.

```agda
      module Mq = Cut qS using ( cut; cut-in; cut-out )

      private
        valR : Recursion
        valR = record
          { dom   = Mq.cut
          ; graph = piFo
          ; funct = λ y hy → mereFunct piFo y (wit y hy) }
          where
          wit : (y : CS.S) (hy : ⟨ y CS.∈ˢ Mq.cut ⟩)
              → ∥ Σ[ v ∈ CS.S ] (⟨ (v ∷ y ∷ []) ⊨ piFo ⟩
                                × ((v' : CS.S) → ⟨ (v' ∷ y ∷ []) ⊨ piFo ⟩ → v' ≡ v)) ∥₁
          wit y hy = ∣ πʟ y hy'
            , ( πʟ-graph y hy'
              , λ v' hv' → S≡ (piFo-val y my v' hv') ) ∣₁
            where
            my : ⟨ fst y ∈ˢ M ⟩
            my = Mq.cut-out y hy .fst
            hy' : ⟨ y CS.∈ˢ Sl.cut ⟩
            hy' = Sl.cut-in y my (q⊆ (fst y) (Mq.cut-out y hy .snd))

        module Vq = Of valR using ( table; table-in; table-out )

      val≡π : fst Vq.table ≡ C.π q
      val≡π = extensionalV {a = fst Vq.table} {b = C.π q} (λ w → ⇔toPath (fwd w) (bwd w))
        where
        fwd : (w : S) → ⟨ w ∈ˢ fst Vq.table ⟩ → ⟨ w ∈ˢ C.π q ⟩
        fwd w hw = PT.rec (snd (w ∈ˢ C.π q))
          (λ { (y , (hy , h)) →
             subst (λ t → ⟨ t ∈ˢ C.π q ⟩)
               (sym (piFo-val y (Mq.cut-out y hy .fst) wS h))
               (C.π∈-fwd q (fst y) (Mq.cut-out y hy .snd) (Mq.cut-out y hy .fst)) })
          (Vq.table-out wS hw)
          where
          wS : CS.S
          wS = w , isL-trans {x = fst Vq.table} {y = w} hw (snd Vq.table)

        bwd : (w : S) → ⟨ w ∈ˢ C.π q ⟩ → ⟨ w ∈ˢ fst Vq.table ⟩
        bwd w hw = PT.rec (snd (w ∈ˢ fst Vq.table)) read (π-mem-out q w hw)
          where
          read : Σ[ y ∈ S ] (⟨ y ∈ˢ q ⟩ × ⟨ y ∈ˢ M ⟩ × (C.π y ≡ w)) → ⟨ w ∈ˢ fst Vq.table ⟩
          read (y , (y∈q , y∈M , e)) =
            subst (λ t → ⟨ t ∈ˢ fst Vq.table ⟩) e
              (Vq.table-in yS (πʟ yS hy') hy (πʟ-graph yS hy'))
            where
            yS : CS.S
            yS = up y y∈M
            hy : ⟨ yS CS.∈ˢ Mq.cut ⟩
            hy = Mq.cut-in yS y∈M y∈q
            hy' : ⟨ yS CS.∈ˢ Sl.cut ⟩
            hy' = Sl.cut-in yS y∈M (q⊆ y y∈q)

      πq-isL : ⟨ isL (C.π q) ⟩
      πq-isL = subst (λ t → ⟨ isL t ⟩) val≡π (snd Vq.table)

      good : (mq' : ⟨ q ∈ˢ M ⟩) → ⟨ ((C.π q , πq-isL) ∷ up q mq' ∷ []) ⊨ piFo ⟩
      good mq' = subst (λ q' → ⟨ ((C.π q , πq-isL) ∷ q' ∷ []) ⊨ piFo ⟩) (S≡ refl)
        (piFo-in (C.π q , πq-isL) qS Tab Tab-correct (complete-of qS cl)
          (valueIs-of qS mq cl (C.π q , πq-isL) refl))
```

The induction on the stage.

```agda
  good-at : (δ : S) → IsOrd δ → (q : S) → Good δ q
  good-at = ∈-induction {P = λ δ → IsOrd δ → (q : S) → Good δ q} go
    where
    go : (δ : S) → ((δ' : S) → ⟨ δ' ∈ˢ δ ⟩ → IsOrd δ' → (q : S) → Good δ' q)
       → IsOrd δ → (q : S) → Good δ q
    go δ IH oδ q mq q∈Lδ = PT.rec (isPropGood δ q) read (Lset-out δ q q∈Lδ) mq q∈Lδ
      where
      read : Σ[ δ' ∈ S ] (⟨ δ' ∈ˢ δ ⟩ × ⟨ q ∈ˢ 𝒟ₒ (Lset δ') ⟩) → Good δ q
      read (δ' , (δ'∈δ , q∈𝒟)) _ _ = A.πq-isL , A.good
        where
        oδ' : IsOrd δ'
        oδ' = mem-ord {A = δ} oδ δ' δ'∈δ
        module A = Step.At δ' oδ' (IH δ' δ'∈δ oδ') q mq (λ y y∈q → 𝒟ₒ∋⊆ (Lset δ') q q∈𝒟 y y∈q)
          using ( πq-isL; good )
```

THE RESULT: every collapse value of a member of `M` is constructible.

```agda
  π-isL : (y : S) → ⟨ y ∈ˢ M ⟩ → ⟨ isL (C.π y) ⟩
  π-isL y y∈M = PT.rec (snd (isL (C.π y)))
    (λ { (α , (oα , M∈Lα)) →
       good-at α oα y y∈M (layer-trans (Lset-layer α) {x = M} {y = y} y∈M M∈Lα) .fst })
    (snd Mʟ)
```

And so is every member of the collapse image.

```agda
  πX-isL : (x : S) → ⟨ x ∈ˢ C.πX ⟩ → ⟨ isL x ⟩
  πX-isL x x∈πX = PT.rec (snd (isL x))
    (λ { (y , (y∈M , e)) → subst (λ w → ⟨ isL w ⟩) e (π-isL y y∈M) })
    (C.πX-member x x∈πX)
```

## Section 2. The hull as the union of an ω-iteration

One hull stage (src/L/GCH/Hull.lagda.md `HullStage`), a start `X` that is an
element of L, and a one-step closure `Φ` that is definable on the whole model
(the shape src/L/GCH/OmegaRec.lagda.md `Iterate` takes) and reads the hull's own
search: `Φ Z` keeps `Z`, holds the junk value, holds the least witness of every
parameter-free formula at every parameter vector drawn from `Z`, and holds
nothing else.

```agda
module Telescope (lam : S) (ordλ : IsOrd lam)
  (succλ : (d : S) → ⟨ d ∈ˢ lam ⟩ → ⟨ sucV d ∈ˢ lam ⟩)
  (X : S) (X⊆L : (x : S) → ⟨ x ∈ˢ X ⟩ → ⟨ x ∈ˢ Lset lam ⟩)
  (∅∈λ : ⟨ ∅ ∈ˢ lam ⟩) where
```

Every module application below carries a `using` list: an unrestricted
application copies every definition of the module into this interface (measured
on this file: the `Condense` copy alone cost 7 s and 0.6 MB).

```agda
  module HS = HullStage lam ordλ succλ X X⊆L ∅∈λ using ( M )
  module HSH = HullStage.H lam ordλ succλ X X⊆L ∅∈λ
    using ( ∅∈Lsetα; hull-member; X⊆M; Hull⊆L )
  open HullStage.H.T lam ordλ succλ X X⊆L ∅∈λ public
    using ( Code; base; wit; val; vals; search; Sat; Hull; val-wit )
  open HullStage.H.T lam ordλ succλ X X⊆L ∅∈λ using ( inHull; _⊨₀_ )

  SL : Type (ℓ-suc ℓ)
  SL = HullStage.ASt.SL lam ordλ succλ X X⊆L ∅∈λ
```

Parameters drawn from a set.

```agda
  From : {k : ℕ} → CS.S → Vec SL k → Type (ℓ-suc ℓ)
  From {k} Z vs = (i : Fin k) → ⟨ fst (lookup i vs) ∈ˢ fst Z ⟩
```

A least witness at parameters from `Z`.

```agda
  Searched : CS.S → S → Type (ℓ-suc ℓ)
  Searched Z z = Σ[ k ∈ ℕ ] Σ[ ψ ∈ Formula (⊥* {ℓ}) (suc k) ] Σ[ vs ∈ Vec SL k ]
                 Σ[ w ∈ Sat k ψ vs ] (From Z vs × (z ≡ fst (search k ψ vs w)))
```

What a member of the closure of `Z` is.

```agda
  Reads : CS.S → S → Type (ℓ-suc ℓ)
  Reads Z z = ⟨ z ∈ˢ fst Z ⟩ ⊎ ((z ≡ ∅) ⊎ Searched Z z)

  record StepPack : Type (ℓ-suc (ℓ-suc ℓ)) where
    field
      Φ       : CS.S → CS.S
      ΦFo     : Formula CS.S 2
      defines : (Z : CS.S) → ⟨ (Φ Z ∷ Z ∷ []) ⊨ ΦFo ⟩
      only    : (Z Z' : CS.S) → ⟨ (Z' ∷ Z ∷ []) ⊨ ΦFo ⟩ → Z' ≡ Φ Z
      grows   : (Z : CS.S) (z : S) → ⟨ z ∈ˢ fst Z ⟩ → ⟨ z ∈ˢ fst (Φ Z) ⟩
      junk    : (Z : CS.S) → ⟨ ∅ ∈ˢ fst (Φ Z) ⟩
      least   : (Z : CS.S) (k : ℕ) (ψ : Formula (⊥* {ℓ}) (suc k)) (vs : Vec SL k)
              → From Z vs → (w : Sat k ψ vs) → ⟨ fst (search k ψ vs w) ∈ˢ fst (Φ Z) ⟩
      out     : (Z : CS.S) → ((z : S) → ⟨ z ∈ˢ fst Z ⟩ → ⟨ z ∈ˢ Lset lam ⟩)
              → (z : S) → ⟨ z ∈ˢ fst (Φ Z) ⟩ → ∥ Reads Z z ∥₁

  module HullIter (X-isL : ⟨ isL X ⟩) (P : StepPack) where
    open StepPack P

    Xʟ : CS.S
    Xʟ = X , X-isL

    module It = Iterate Xʟ ΦFo Φ defines only
      using ( it; module Closure; iterUnion; iterUnion-in; iterUnion-out; iter; iter-in; iter-out; ω-num; Num )
    module Cl = It.Closure (λ Z z → grows Z (fst z)) using ( it-up )

    hullStep : ℕ → CS.S
    hullStep = It.it

    hullStep-suc : (n : ℕ) → hullStep (suc n) ≡ Φ (hullStep n)
    hullStep-suc n = refl

    hullStep-≤ : (n n' : ℕ) → n ≤ n' → (z : S)
               → ⟨ z ∈ˢ fst (hullStep n) ⟩ → ⟨ z ∈ˢ fst (hullStep n') ⟩
    hullStep-≤ n n' (k , e) z h =
      subst (λ m → ⟨ z ∈ˢ fst (hullStep m) ⟩) e (Cl.it-up n k (z , zL) h)
      where
      zL : ⟨ isL z ⟩
      zL = isL-trans {x = fst (hullStep n)} {y = z} h (snd (hullStep n))
```

HULL ⊆ UNION: a code of depth `n` has its value at the `n`-th stage.

```agda
    mutual
      depth : Code → ℕ
      depth (base m) = 0
      depth (wit k ψ cs) = suc (depths cs)

      depths : {m : ℕ} → Vec Code m → ℕ
      depths [] = 0
      depths (c ∷ cs) = max (depth c) (depths cs)

    private
      stuck-r : {A : Type (ℓ-suc ℓ)} (na : A → Empty.⊥)
                (f : A → SL) (g : (A → Empty.⊥) → SL) (s : A ⊎ (A → Empty.⊥))
              → Sum.rec f g s ≡ g na
      stuck-r na f g (inl a) = Empty.rec (na a)
      stuck-r na f g (inr h) = cong g (funExt (λ a → Empty.rec (na a)))

    mutual
      hullStep-in : (c : Code) → ⟨ fst (val c) ∈ˢ fst (hullStep (depth c)) ⟩
      hullStep-in (base m) = member X m
      hullStep-in (wit k ψ cs) = go (lem (Sat k ψ (vals cs) , squash₁))
        where
        n : ℕ
        n = depths cs
        go : (s : Sat k ψ (vals cs) ⊎ (Sat k ψ (vals cs) → Empty.⊥))
           → ⟨ fst (Sum.rec (search k ψ (vals cs)) (λ _ → (∅ , HSH.∅∈Lsetα)) s)
                ∈ˢ fst (hullStep (suc n)) ⟩
        go (inl w) = least (hullStep n) k ψ (vals cs) (vals-in cs) w
        go (inr h) = junk (hullStep n)

      vals-in : {m : ℕ} (cs : Vec Code m) → From (hullStep (depths cs)) (vals cs)
      vals-in (c ∷ cs) zero =
        hullStep-≤ (depth c) (max (depth c) (depths cs)) left-≤-max (fst (val c)) (hullStep-in c)
      vals-in (c ∷ cs) (suc i) =
        hullStep-≤ (depths cs) (max (depth c) (depths cs)) right-≤-max
          (fst (lookup i (vals cs))) (vals-in cs i)
```

UNION ⊆ HULL: the start is in the hull, and the hull is closed under the step,
since every parameter vector from the hull is the value vector of a code vector.

```agda
    private
```

Codes for a vector of hull members.

```agda
      choose : {k : ℕ} (vs : Vec SL k)
             → ((i : Fin k) → ⟨ fst (lookup i vs) ∈ˢ Hull ⟩)
             → ∥ Σ[ cs ∈ Vec Code k ] (vals cs ≡ vs) ∥₁
      choose [] h = ∣ [] , refl ∣₁
      choose (v ∷ vs) h = PT.rec squash₁ (λ { (c , ec) → PT.map
        (λ { (cs , ecs) → (c ∷ cs)
           , cong₂ _∷_ (Σ≡Prop (λ z → snd (z ∈ˢ Lset lam)) ec) ecs })
        (choose vs (λ i → h (suc i))) })
        (HSH.hull-member (fst v) (h zero))
```

The search at a value vector is the value of the witness code.

```agda
      search-val : (k : ℕ) (ψ : Formula (⊥* {ℓ}) (suc k)) (cs : Vec Code k) (vs : Vec SL k)
                 → vals cs ≡ vs → (w : Sat k ψ vs) → ⟨ fst (search k ψ vs w) ∈ˢ Hull ⟩
      search-val k ψ cs vs e w =
        J (λ vs' e' → (w' : Sat k ψ vs') → ⟨ fst (search k ψ vs' w') ∈ˢ Hull ⟩)
          (λ w' → subst (λ z → ⟨ fst z ∈ˢ Hull ⟩) (val-wit k ψ cs w') (inHull (wit k ψ cs)))
          e w

      junk∈Hull : ⟨ ∅ ∈ˢ Hull ⟩
      junk∈Hull = subst (λ z → ⟨ fst z ∈ˢ Hull ⟩)
        (stuck-r no (search 0 ⊥̇ []) (λ _ → (∅ , HSH.∅∈Lsetα)) (lem (Sat 0 ⊥̇ [] , squash₁)))
        (inHull (wit 0 ⊥̇ []))
        where
        no : Sat 0 ⊥̇ [] → Empty.⊥
        no = PT.rec Empty.isProp⊥ (λ { (a , h) → Empty.rec* h })

    hullStep⊆Hull : (n : ℕ) (z : S) → ⟨ z ∈ˢ fst (hullStep n) ⟩ → ⟨ z ∈ˢ Hull ⟩
    hullStep⊆Hull zero z h = HSH.X⊆M z h
    hullStep⊆Hull (suc n) z h = PT.rec (snd (z ∈ˢ Hull)) read
      (out (hullStep n) (λ z' hz' → HSH.Hull⊆L z' (hullStep⊆Hull n z' hz')) z h)
      where
      read : Reads (hullStep n) z → ⟨ z ∈ˢ Hull ⟩
      read (inl h') = hullStep⊆Hull n z h'
      read (inr (inl e)) = subst (λ t → ⟨ t ∈ˢ Hull ⟩) (sym e) junk∈Hull
      read (inr (inr (k , ψ , vs , w , from , e))) =
        subst (λ t → ⟨ t ∈ˢ Hull ⟩) (sym e)
          (PT.rec (snd (fst (search k ψ vs w) ∈ˢ Hull))
            (λ { (cs , ecs) → search-val k ψ cs vs ecs w })
            (choose vs (λ i → hullStep⊆Hull n (fst (lookup i vs)) (from i))))
```

THE HULL AS AN ELEMENT OF L.

```agda
    hullL : CS.S
    hullL = It.iterUnion

    hullL-spec : fst hullL ≡ Hull
    hullL-spec = extensionalV {a = fst hullL} {b = Hull} (λ z → ⇔toPath (fwd z) (bwd z))
      where
      fwd : (z : S) → ⟨ z ∈ˢ fst hullL ⟩ → ⟨ z ∈ˢ Hull ⟩
      fwd z h = PT.rec (snd (z ∈ˢ Hull))
        (λ { (n , hn) → hullStep⊆Hull n z hn })
        (It.iterUnion-out (z , isL-trans {x = fst hullL} {y = z} h (snd hullL)) h)

      bwd : (z : S) → ⟨ z ∈ˢ Hull ⟩ → ⟨ z ∈ˢ fst hullL ⟩
      bwd z h = PT.rec (snd (z ∈ˢ fst hullL))
        (λ { (c , ec) → It.iterUnion-in (depth c) zS
               (subst (λ t → ⟨ t ∈ˢ fst (hullStep (depth c)) ⟩) ec (hullStep-in c)) })
        (HSH.hull-member z h)
        where
        zS : CS.S
        zS = z , Lset→isL lam ordλ z (HSH.Hull⊆L z h)

    M-isL : ⟨ isL HS.M ⟩
    M-isL = subst (λ t → ⟨ isL t ⟩) hullL-spec (snd hullL)
```

THE DEFINABLE STEP. The formula names, as constants, the code set of the
parameter-free formulas (src/L/Choice/Internal.lagda.md `freeCode-in/out` at
`AllCodes ∅ʟ`), the stage `Lset lam`, the graph of the stage's uniform
satisfaction table (src/L/GCH/SatFrame.lagda.md `SatGraph.pairs`), the stage's
order element `relL lam` and `ωʟ`. Every host reading is stated at a variable
and reaches the construction by an equation.

```agda
  module Build where

    λ-isL : ⟨ isL lam ⟩
    λ-isL = isL-ord lam ordλ

    A : CS.S
    A = LsetS lam ordλ

    module SM = SatGraph A using ( pairs; pairs-in; pairs-shape; valOf; valOf≡ )
```

A member of the graph, read as a pair of a code and its value.

```agda
    pairs-out : (x : V ℓ) → ⟨ x ∈ˢ fst SM.pairs ⟩
              → ∥ Σ[ c ∈ CS.S ] Σ[ m ∈ ⟨ fst c ∈ˢ fst (AllCodes A) ⟩ ] (x ≡ pr (fst c) (fst (SM.valOf c m))) ∥₁
    pairs-out x h = SM.pairs-shape (x , isL-trans {x = fst SM.pairs} {y = x} h (snd SM.pairs)) h
    module DA = DefOf (Lset lam) using ( ι; _⊨ᵐ_; 𝒮M )

    C₀ : CS.S
    C₀ = AllCodes ∅ʟ

    Rel : CS.S
    Rel = relL lam λ-isL ordλ

    wL : SWO SL
    wL = orderAt lam ordλ
```

The stage order, as the relation `relL` represents.

```agda
    relOf-at : SL → SL → Type (ℓ-suc ℓ)
    relOf-at = relOf wL
```

The second component of a constructible pair is constructible.

```agda
    pr-snd-isL : (a b : V ℓ) → ⟨ isL (pr a b) ⟩ → ⟨ isL b ⟩
    pr-snd-isL a b h =
      isL-trans {x = ⁅ a , b ⁆} {y = b} (subst ⟨_⟩ (sym (pair-spec a b b)) ∣ inr refl ∣₁)
        (isL-trans {x = pr a b} {y = ⁅ a , b ⁆}
          (subst ⟨_⟩ (sym (pair-spec ⁅ a ⁆s ⁅ a , b ⁆ ⁅ a , b ⁆)) ∣ inr refl ∣₁) h)

    nn : ℕ → CS.S
    nn k = # k , numL k

    ε′ : ⊥* {ℓ} → ⟪ Lset lam ⟫
    ε′ = Empty.rec*
```

The stage's inner satisfaction of a parameter-free formula, read with the
constants relabelled into the stage's alphabet.

```agda
    sat-bridge : (k : ℕ) (χ : Formula (⊥* {ℓ}) k) (δ : SL ^ k)
               → (δ ⊨₀ χ) ≡ (δ DA.⊨ᵐ mapFo ε′ χ)
    sat-bridge k χ δ =
        cong (λ κ → FOL.Semantics.At._⊨_ (hPropAlgebra (ℓ-suc ℓ)) DA.𝒮M (⊥* {ℓ}) κ δ χ)
          (funExt (λ b → Empty.rec* b))
      ∙ sym (⊨-map (hPropAlgebra (ℓ-suc ℓ)) DA.𝒮M ε′ DA.ι χ δ)
```

THE KEY OF A PARAMETER-FREE FORMULA AT THE STAGE, sealed
(src/L/Coding/Uniform.lagda.md's law: a key written out inside a satisfaction
does not elaborate).

```agda
    opaque
      keyOf : (k : ℕ) → Formula (⊥* {ℓ}) k → CS.S
      keyOf k χ = keyS A (mapFo ε′ χ)

      keyOf∈ : (k : ℕ) (χ : Formula (⊥* {ℓ}) k) → ⟨ keyOf k χ CS.∈ˢ AllCodes A ⟩
      keyOf∈ k χ = key∈AllCodes A (mapFo ε′ χ)

      keyOf≡ : (k : ℕ) (χ : Formula (⊥* {ℓ}) k) → keyOf k χ ≡ keyS A (mapFo ε′ χ)
      keyOf≡ k χ = refl

      keyOf-fst : (k : ℕ) (χ : Formula (⊥* {ℓ}) k)
                → fst (keyOf k χ) ≡ pr (# k) (fst (limitCode χ))
      keyOf-fst k χ = cong (pr (# k)) (cong VCode.⌜_⌝
        ( mapFo-comp ε′ ⟪ Lset lam ⟫↪ χ
        ∙ cong (λ f → mapFo f χ) (funExt (λ b → Empty.rec* b)) ))
```

The satisfaction set at that key, sealed with the key.

```agda
    Tof : (k : ℕ) → Formula (⊥* {ℓ}) k → CS.S
    Tof k χ = SM.valOf (keyOf k χ) (keyOf∈ k χ)

    Tof-pair : (k : ℕ) (χ : Formula (⊥* {ℓ}) k)
             → ⟨ pr (fst (keyOf k χ)) (fst (Tof k χ)) ∈ˢ fst SM.pairs ⟩
    Tof-pair k χ = SM.pairs-in (keyOf k χ) (keyOf∈ k χ)
```

A satisfaction value at another member with the same key.

```agda
    valOf-same : (x : CS.S) (m : ⟨ x CS.∈ˢ AllCodes A ⟩) (k : ℕ) (χ : Formula (⊥* {ℓ}) k)
               → fst x ≡ fst (keyOf k χ) → SM.valOf x m ≡ Tof k χ
    valOf-same x m k χ e =
      J (λ x' e' → (m' : ⟨ x' CS.∈ˢ AllCodes A ⟩) → SM.valOf x m ≡ SM.valOf x' m')
        (λ m' → cong (SM.valOf x) (snd (x CS.∈ˢ AllCodes A) m m'))
        (S≡ {x = x} {y = keyOf k χ} e) (keyOf∈ k χ)
```

MEMBERSHIP IN THE SATISFACTION SET IS THE STAGE'S SATISFACTION.

```agda
    sat-at : (k : ℕ) (χ : Formula (⊥* {ℓ}) k) (δ : SL ^ k) (z : CS.S)
           → fst z ≡ graph A δ → (z CS.∈ˢ Tof k χ) ≡ (δ ⊨₀ χ)
    sat-at k χ δ z qz =
        cong (z CS.∈ˢ_) (SM.valOf≡ (keyOf k χ) (keyOf∈ k χ))
      ∙ val-sat A (mapFo ε′ χ) (keyOf k χ) (keyOf∈ k χ) (cong fst (keyOf≡ k χ)) δ z qz
      ∙ sym (sat-bridge k χ δ)
```

THE ATOMS. "The pair of x and y is in the constant F"; "s is the code of a
parameter-free formula of arity a+1" (the shape of
src/L/Choice/Internal.lagda.md `FreeAt`, at the constant `C₀`).

"s is a key of C₀ of arity a+1": `s` is in `C₀` and `s` is the pair of the
successor of `a` with some code. Inside: the successor is 0; then the code is 0,
the successor 1. Sealed at its slots; the two readings are stated at a variable
environment.

```agda
    opaque
      keyIn : ∀ {n} → Fin n → Fin n → Formula CS.S n
      keyIn s a = (var s ∈̇ con C₀)
                ∧̇ ∃̇ ( sucAtL (suc a) zero
                     ∧̇ ∃̇ (prAtL (suc (suc s)) (suc zero) zero) )

    module KeyIn {n : ℕ} (s a : Fin n) (γ : CS.S ^ n) (k : ℕ)
                 (qa : fst (lookup a γ) ≡ # k) where

      opaque
        unfolding keyIn

        keyIn-in : ⟨ fst (lookup s γ) ∈ˢ fst C₀ ⟩ → (c : V ℓ)
                 → fst (lookup s γ) ≡ pr (# (suc k)) c → ⟨ γ ⊨ keyIn s a ⟩
        keyIn-in h c q = h , ∣ numAt , ( hsuc , ∣ cS , hpr ∣₁ ) ∣₁
          where
          numAt : CS.S
          numAt = nn (suc k)
          cS : CS.S
          cS = c , pr-snd-isL (# (suc k)) c
                     (subst (λ u → ⟨ isL u ⟩) q (isL-trans h (snd C₀)))
          hsuc : ⟨ (numAt ∷ γ) ⊨ sucAtL (suc a) zero ⟩
          hsuc = subst ⟨_⟩ (sym (sucAtL-adequate (suc a) zero (numAt ∷ γ)))
            (cong sucV (sym qa))
          hpr : ⟨ (cS ∷ numAt ∷ γ) ⊨ prAtL (suc (suc s)) (suc zero) zero ⟩
          hpr = subst ⟨_⟩
            (sym (prAtL-adequate (suc (suc s)) (suc zero) zero (cS ∷ numAt ∷ γ))) q

        keyIn-out : ⟨ γ ⊨ keyIn s a ⟩
                  → ⟨ fst (lookup s γ) ∈ˢ fst C₀ ⟩
                  × ∥ Σ[ c ∈ V ℓ ] (fst (lookup s γ) ≡ pr (# (suc k)) c) ∥₁
        keyIn-out (h , hk) = h , PT.rec squash₁ atNum hk
          where
          atNum : Σ[ z ∈ CS.S ] ( ⟨ (z ∷ γ) ⊨ sucAtL (suc a) zero ⟩
                                × ⟨ (z ∷ γ) ⊨ ∃̇ (prAtL (suc (suc s)) (suc zero) zero) ⟩ )
                → ∥ Σ[ c ∈ V ℓ ] (fst (lookup s γ) ≡ pr (# (suc k)) c) ∥₁
          atNum (z , (hs , hc)) = PT.map
            (λ { (c , hp) → fst c
               , ( subst ⟨_⟩ (prAtL-adequate (suc (suc s)) (suc zero) zero (c ∷ z ∷ γ)) hp
                 ∙ cong (λ u → pr u (fst c)) (qz ∙ cong sucV qa) ) })
            hc
            where
            qz : fst z ≡ sucV (fst (lookup a γ))
            qz = subst ⟨_⟩ (sucAtL-adequate (suc a) zero (z ∷ γ)) hs
```

THE WITNESS FORMULA, over `(w ∷ Z ∷ [])`. Five binders: `k`, the code `s`, the
environment `e`, the extended environment `e'`, and the satisfaction set `T`.
Inside the body: `T` is 0, `e'` is 1, `e` is 2, `s` is 3, `k` is 4, `w` is 5,
`Z` is 6. Under the minimality binder `w'` is 0 and the rest shift by one; under
its existential `e''` is 0.

The body is sealed at its slots. Its eight readings and its filling are stated
once, at a variable environment (`BodyRd`), and every concrete site instantiates
them: the concrete instance is only ever compared under the seal.

```agda
    Env : CS.S → CS.S → CS.S → CS.S → CS.S → CS.S → CS.S → CS.S ^ 7
    Env T e' e s k w Z = T ∷ e' ∷ e ∷ s ∷ k ∷ w ∷ Z ∷ []

    opaque
      minFo : Formula CS.S 7
      minFo = ∀̇∈ (con A)
        ( (∃̇ ( consAtL i0 i1 i4 ∧̇ (var i0 ∈̇ var i2) )) ⇒̇ ¬̇ (appC Rel i0 i6) )

      bodyFo : Formula CS.S 7
      bodyFo = (var i4 ∈̇ con ωʟ)
            ∧̇ ( keyIn i3 i4
            ∧̇ ( envOverAt i2 i4 i6
            ∧̇ ( consAtL i1 i5 i2
            ∧̇ ( appC SM.pairs i3 i0
            ∧̇ ( (var i1 ∈̇ var i0)
            ∧̇ ( (var i5 ∈̇ con A)
            ∧̇ minFo ))))))

    module BodyRd (T e' e s k w Z : CS.S) where

      γ₇ : CS.S ^ 7
      γ₇ = Env T e' e s k w Z
```

The minimality clause, host-side, at a family `g` presenting `e`.

```agda
      Min : {m : ℕ} (g : Fin m → V ℓ) → Type (ℓ-suc ℓ)
      Min g = (w' : CS.S) → ⟨ fst w' ∈ˢ fst A ⟩ → (e'' : CS.S)
            → fst e'' ≡ env (cons (fst w') g) → ⟨ fst e'' ∈ˢ fst T ⟩
            → ⟨ pr (fst w') (fst w) ∈ˢ fst Rel ⟩ → Empty.⊥

      opaque
        unfolding bodyFo

        b-num : ⟨ γ₇ ⊨ bodyFo ⟩ → ⟨ fst k ∈ˢ fst ωʟ ⟩
        b-num h = h .fst

        b-key : ⟨ γ₇ ⊨ bodyFo ⟩ → ⟨ γ₇ ⊨ keyIn i3 i4 ⟩
        b-key h = h .snd .fst

        b-env : ⟨ γ₇ ⊨ bodyFo ⟩ → ⟨ γ₇ ⊨ envOverAt i2 i4 i6 ⟩
        b-env h = h .snd .snd .fst

        b-cons : {m : ℕ} (g : Fin m → V ℓ) → fst e ≡ env g
               → ⟨ γ₇ ⊨ bodyFo ⟩ → fst e' ≡ env (cons (fst w) g)
        b-cons g hE h =
          subst ⟨_⟩ (consAtL-adequate i1 i5 i2 γ₇ g hE) (h .snd .snd .snd .fst)

        b-tab : ⟨ γ₇ ⊨ bodyFo ⟩ → ⟨ pr (fst s) (fst T) ∈ˢ fst SM.pairs ⟩
        b-tab h = subst ⟨_⟩ (appC-adequate SM.pairs i3 i0 γ₇) (h .snd .snd .snd .snd .fst)

        b-mem : ⟨ γ₇ ⊨ bodyFo ⟩ → ⟨ fst e' ∈ˢ fst T ⟩
        b-mem h = h .snd .snd .snd .snd .snd .fst

        b-stage : ⟨ γ₇ ⊨ bodyFo ⟩ → ⟨ fst w ∈ˢ fst A ⟩
        b-stage h = h .snd .snd .snd .snd .snd .snd .fst

        b-min : {m : ℕ} (g : Fin m → V ℓ) → fst e ≡ env g → ⟨ γ₇ ⊨ bodyFo ⟩ → Min g
        b-min g hE h w' hw' e'' qe hm hr =
          h .snd .snd .snd .snd .snd .snd .snd w' hw' ∣ e'' , (hc , hm) ∣₁
            (subst ⟨_⟩ (sym (appC-adequate Rel i0 i6 (w' ∷ γ₇))) hr)
          where
          hc : ⟨ (e'' ∷ w' ∷ γ₇) ⊨ consAtL i0 i1 i4 ⟩
          hc = subst ⟨_⟩ (sym (consAtL-adequate i0 i1 i4 (e'' ∷ w' ∷ γ₇) g hE)) qe

        b-fill : {m : ℕ} (g : Fin m → V ℓ) → fst e ≡ env g
               → ⟨ fst k ∈ˢ fst ωʟ ⟩ → ⟨ γ₇ ⊨ keyIn i3 i4 ⟩ → ⟨ γ₇ ⊨ envOverAt i2 i4 i6 ⟩
               → fst e' ≡ env (cons (fst w) g) → ⟨ pr (fst s) (fst T) ∈ˢ fst SM.pairs ⟩
               → ⟨ fst e' ∈ˢ fst T ⟩ → ⟨ fst w ∈ˢ fst A ⟩ → Min g
               → ⟨ γ₇ ⊨ bodyFo ⟩
        b-fill g hE c1 c2 c3 c4 c5 c6 c7 mn =
          c1 , c2 , c3
          , subst ⟨_⟩ (sym (consAtL-adequate i1 i5 i2 γ₇ g hE)) c4
          , subst ⟨_⟩ (sym (appC-adequate SM.pairs i3 i0 γ₇)) c5
          , c6 , c7
          , λ w' hw' hex hr → PT.rec Empty.isProp⊥
              (λ { (e'' , (hc , hm)) → mn w' hw' e''
                     (subst ⟨_⟩ (consAtL-adequate i0 i1 i4 (e'' ∷ w' ∷ γ₇) g hE) hc) hm
                     (subst ⟨_⟩ (appC-adequate Rel i0 i6 (w' ∷ γ₇)) hr) })
              hex
```

The five binders, sealed with their two readings.

```agda
    opaque
      witFo : Formula CS.S 2
      witFo = ∃̇ (∃̇ (∃̇ (∃̇ (∃̇ bodyFo))))

      witFo-in : (w Z T e' e s k : CS.S) → ⟨ Env T e' e s k w Z ⊨ bodyFo ⟩
               → ⟨ (w ∷ Z ∷ []) ⊨ witFo ⟩
      witFo-in w Z T e' e s k h = ∣ k , ∣ s , ∣ e , ∣ e' , ∣ T , h ∣₁ ∣₁ ∣₁ ∣₁ ∣₁

      witFo-out : (w Z : CS.S) → ⟨ (w ∷ Z ∷ []) ⊨ witFo ⟩
                → ∥ Σ[ T ∈ CS.S ] Σ[ e' ∈ CS.S ] Σ[ e ∈ CS.S ] Σ[ s ∈ CS.S ] Σ[ k ∈ CS.S ]
                     ⟨ Env T e' e s k w Z ⊨ bodyFo ⟩ ∥₁
      witFo-out w Z = PT.rec squash₁ (λ { (k , hk) → PT.rec squash₁ (λ { (s , hs) →
        PT.rec squash₁ (λ { (e , he) → PT.rec squash₁ (λ { (e' , he') → PT.map
          (λ { (T , hT) → T , e' , e , s , k , hT }) he' }) he }) hs }) hk })
```

The numeral read out of a member of `ωʟ`.

```agda
    ω-num : (q : CS.S) → ⟨ fst q ∈ˢ fst ωʟ ⟩ → ∥ Σ[ n ∈ ℕ ] (fst q ≡ # n) ∥₁
    ω-num q h = PT.map (λ { (n , e) → lower n , (e ∙ numeralL-fst (lower n)) })
      (subst ⟨_⟩ (ω-specL q) h)
```

A vector from a family, with its lookups.

```agda
    vecOf : {k : ℕ} → (Fin k → SL) → Vec SL k
    vecOf {zero} f = []
    vecOf {suc k} f = f zero ∷ vecOf (λ i → f (suc i))

    lookup-vecOf : {k : ℕ} (f : Fin k → SL) (i : Fin k) → lookup i (vecOf f) ≡ f i
    lookup-vecOf {suc k} f zero = refl
    lookup-vecOf {suc k} f (suc i) = lookup-vecOf (λ j → f (suc j)) i
```

THE SEARCH SATISFIES THE FORMULA (the `least` clause).

```agda
    module Least (Z : CS.S) (k : ℕ) (χ : Formula (⊥* {ℓ}) (suc k)) (vs : Vec SL k)
                 (from : From Z vs) (w₀ : Sat k χ vs) where

      P : SL → hProp (ℓ-suc ℓ)
      P a = (a ∷ vs) ⊨₀ χ

      a : SL
      a = leastOf wL {ℓ'' = ℓ-suc ℓ} lem P w₀ .fst

      a-least : IsLeast wL P a
      a-least = leastOf wL {ℓ'' = ℓ-suc ℓ} lem P w₀ .snd

      aS : CS.S
      aS = fst a , Lset→isL lam ordλ (fst a) (snd a)
```

The parameters, as indices of `Z`.

```agda
      g : Ix Z k
      g i = fiber (fst Z) (from i) .fst

      g-val : (i : Fin k) → ⟪ fst Z ⟫↪ (g i) ≡ fst (lookup i vs)
      g-val i = fiber (fst Z) (from i) .snd

      g′ : Fin k → V ℓ
      g′ i = ⟪ fst Z ⟫↪ (g i)

      e : CS.S
      e = envS Z g
```

The extended environments.

```agda
      ext : SL → CS.S
      ext b = envFor A (b ∷ vs)

      ext-graph : (b : SL) → fst (ext b) ≡ env (cons (fst b) g′)
      ext-graph b = envFor-graph A (b ∷ vs)
        ∙ cong env (funExt (λ { zero → refl ; (suc i) → sym (g-val i) }))

      ext-sat : (b : SL) → (ext b CS.∈ˢ Tof (suc k) χ) ≡ ((b ∷ vs) ⊨₀ χ)
      ext-sat b = sat-at (suc k) χ (b ∷ vs) (ext b) (envFor-graph A (b ∷ vs))

      sS : CS.S
      sS = keyOf (suc k) χ

      T : CS.S
      T = Tof (suc k) χ

      γ₇ : CS.S ^ 7
      γ₇ = Env T (ext a) e sS (nn k) aS Z

      c1 : ⟨ γ₇ ⊨ (var i4 ∈̇ con ωʟ) ⟩
      c1 = #∈ω k

      c2 : ⟨ γ₇ ⊨ keyIn i3 i4 ⟩
      c2 = KeyIn.keyIn-in i3 i4 γ₇ k refl
        (subst (λ u → ⟨ u ∈ˢ fst C₀ ⟩) (sym (keyOf-fst (suc k) χ)) (freeCode-in (suc k) χ))
        (fst (limitCode χ)) (keyOf-fst (suc k) χ)

      c3 : ⟨ γ₇ ⊨ envOverAt i2 i4 i6 ⟩
      c3 = envOverAt-transport (Z ∷ nn k ∷ e ∷ []) γ₇ i2 i1 i0 i2 i4 i6 refl refl refl
             (envOver Z g)

      c4 : fst (ext a) ≡ env (cons (fst a) g′)
      c4 = ext-graph a

      c5 : ⟨ pr (fst sS) (fst T) ∈ˢ fst SM.pairs ⟩
      c5 = Tof-pair (suc k) χ

      c6 : ⟨ fst (ext a) ∈ˢ fst T ⟩
      c6 = transport (sym (cong ⟨_⟩ (ext-sat a))) (a-least .fst)

      c7 : ⟨ fst aS ∈ˢ fst A ⟩
      c7 = snd a

      c8 : BodyRd.Min T (ext a) e sS (nn k) aS Z g′
      c8 w' w'∈ e'' q hm hr = a-least .snd w'S sat lt
        where
        w'S : SL
        w'S = fst w' , w'∈
        lt : relOf-at w'S a
        lt = relL-rep lam λ-isL ordλ w'S a hr
        sat : ⟨ (w'S ∷ vs) ⊨₀ χ ⟩
        sat = transport (cong ⟨_⟩ (ext-sat w'S))
                (subst (λ t → ⟨ t ∈ˢ fst T ⟩) (q ∙ sym (ext-graph w'S)) hm)

      least : ⟨ (aS ∷ Z ∷ []) ⊨ witFo ⟩
      least = witFo-in aS Z T (ext a) e sS (nn k)
        (BodyRd.b-fill T (ext a) e sS (nn k) aS Z g′ refl c1 c2 c3 c4 c5 c6 c7 c8)
```

THE FORMULA READS BACK AS A SEARCH (the `out` clause).

```agda
    module Out (Z : CS.S) (Z⊆ : (z : S) → ⟨ z ∈ˢ fst Z ⟩ → ⟨ z ∈ˢ Lset lam ⟩)
               (w T e' e s k : CS.S) (h : ⟨ Env T e' e s k w Z ⊨ bodyFo ⟩) where

      module Rd = BodyRd T e' e s k w Z
        using ( b-num; b-key; b-env; b-cons; b-tab; b-mem; b-stage; b-min )

      wS : SL
      wS = fst w , Rd.b-stage h

      module AtNum (n : ℕ) (qk : fst k ≡ # n) where

        s∈ : ⟨ fst s ∈ˢ fst C₀ ⟩
        s∈ = KeyIn.keyIn-out i3 i4 (Env T e' e s k w Z) n qk (Rd.b-key h) .fst

        module R = Recover Z n (Env T e' e s k w Z) i2 i4 i6 qk refl (Rd.b-env h) using ( g; recovers )

        g′ : Fin n → V ℓ
        g′ i = ⟪ fst Z ⟫↪ (R.g i)

        vs : Vec SL n
        vs = vecOf (λ i → g′ i , Z⊆ (g′ i) (member (fst Z) (R.g i)))

        vs-val : (i : Fin n) → fst (lookup i vs) ≡ g′ i
        vs-val i = cong fst (lookup-vecOf (λ i → g′ i , Z⊆ (g′ i) (member (fst Z) (R.g i))) i)

        from : From Z vs
        from i = subst (λ u → ⟨ u ∈ˢ fst Z ⟩) (sym (vs-val i)) (member (fst Z) (R.g i))

        hE : fst e ≡ env g′
        hE = R.recovers

        ext : SL → CS.S
        ext b = envFor A (b ∷ vs)

        ext-graph : (b : SL) → fst (ext b) ≡ env (cons (fst b) g′)
        ext-graph b = envFor-graph A (b ∷ vs)
          ∙ cong env (funExt (λ { zero → refl ; (suc i) → vs-val i }))

        e'≡ : fst e' ≡ fst (ext wS)
        e'≡ = Rd.b-cons g′ hE h ∙ sym (ext-graph wS)

        module AtCode (χ : Formula (⊥* {ℓ}) (suc n)) (qs : fst s ≡ fst (keyOf (suc n) χ)) where

          P : SL → hProp (ℓ-suc ℓ)
          P b = (b ∷ vs) ⊨₀ χ

          ext-sat : (b : SL) → ⟨ ext b CS.∈ˢ Tof (suc n) χ ⟩ ≡ ⟨ P b ⟩
          ext-sat b = cong ⟨_⟩ (sat-at (suc n) χ (b ∷ vs) (ext b) (envFor-graph A (b ∷ vs)))

          module AtTable (qT : fst T ≡ fst (Tof (suc n) χ)) where

            sat : ⟨ P wS ⟩
            sat = transport (ext-sat wS)
              (subst2 (λ u t → ⟨ u ∈ˢ t ⟩) e'≡ qT (Rd.b-mem h))

            min : (b : SL) → ⟨ P b ⟩ → relOf-at b wS → Empty.⊥
            min b pb lt = Rd.b-min g′ hE h bS (snd b) (ext b) (ext-graph b) hm
              (relL-fill lam λ-isL ordλ b wS lt)
              where
              bS : CS.S
              bS = fst b , Lset→isL lam ordλ (fst b) (snd b)
              hm : ⟨ fst (ext b) ∈ˢ fst T ⟩
              hm = subst (λ t → ⟨ fst (ext b) ∈ˢ t ⟩) (sym qT) (transport (sym (ext-sat b)) pb)

            w₀ : Sat n χ vs
            w₀ = ∣ wS , sat ∣₁

            searched : Searched Z (fst w)
            searched = n , χ , vs , w₀ , (from , sym (cong (λ q → fst (fst q))
              (isPropLeastOf wL P (leastOf wL {ℓ'' = ℓ-suc ℓ} lem P w₀) (wS , (sat , min)))))
```

The table slot is the satisfaction set at the key.

```agda
          table : ∥ Searched Z (fst w) ∥₁
          table = PT.rec squash₁
            (λ { (x , m , e) →
               let ex : fst s ≡ fst x
                   ex = pr-inj e .fst
                   qT : fst T ≡ fst (Tof (suc n) χ)
                   qT = pr-inj e .snd ∙ cong fst (valOf-same x m (suc n) χ (sym ex ∙ qs))
               in ∣ AtTable.searched qT ∣₁ })
            (pairs-out (pr (fst s) (fst T)) (Rd.b-tab h))

        code : ∥ Searched Z (fst w) ∥₁
        code = PT.rec squash₁
          (λ { (c , qc) → PT.rec squash₁
            (λ { (χ , ec) → AtCode.table χ
                   (qc ∙ cong (pr (# (suc n))) ec ∙ sym (keyOf-fst (suc n) χ)) })
            (freeCode-out (suc n) c (subst (λ u → ⟨ u ∈ˢ fst C₀ ⟩) qc s∈)) })
          (KeyIn.keyIn-out i3 i4 (Env T e' e s k w Z) n qk (Rd.b-key h) .snd)

      searched : ∥ Searched Z (fst w) ∥₁
      searched = PT.rec squash₁ (λ { (n , qk) → AtNum.code n qk }) (ω-num k (Rd.b-num h))
```

THE STEP ITSELF: carved by separation out of `Z ∪ Lset lam`.

```agda
    Bnd : CS.S → CS.S
    Bnd Z = unionʟ (pairʟ Z A)

    bnd-Z : (Z z : CS.S) → ⟨ fst z ∈ˢ fst Z ⟩ → ⟨ z CS.∈ˢ Bnd Z ⟩
    bnd-Z Z z h = unionʟ-in (pairʟ Z A) z Z (pairʟ-in Z A Z (inl refl)) h

    bnd-L : (Z z : CS.S) → ⟨ fst z ∈ˢ Lset lam ⟩ → ⟨ z CS.∈ˢ Bnd Z ⟩
    bnd-L Z z h = unionʟ-in (pairʟ Z A) z A (pairʟ-in Z A A (inr refl)) h
```

What a member of the step is, host-side.

```agda
    Body : CS.S → CS.S → Type (ℓ-suc ℓ)
    Body Z w = ⟨ fst w ∈ˢ fst Z ⟩ ⊎ ((fst w ≡ ∅) ⊎ ⟨ (w ∷ Z ∷ []) ⊨ witFo ⟩)

    wit-L : (Z w : CS.S) → ⟨ (w ∷ Z ∷ []) ⊨ witFo ⟩ → ⟨ fst w ∈ˢ Lset lam ⟩
    wit-L Z w hw = PT.rec (snd (fst w ∈ˢ Lset lam))
      (λ { (T , e' , e , s , k , h) → BodyRd.b-stage T e' e s k w Z h })
      (witFo-out w Z hw)
```

The separating description, over `(w ∷ [])`, with `Z` a constant; the witness
formula is reached by binding `Z` and renaming. Sealed with its two readings.

```agda
    opaque
      sepFo : CS.S → Formula CS.S 1
      sepFo Z = (var i0 ∈̇ con Z)
              ∨̇ ( (var i0 ≐ con ∅ʟ)
                ∨̇ ∃̇ ( (var i0 ≐ con Z) ∧̇ renameFo ρs witFo ) )

      private
        rs : (Z'' w : CS.S)
           → ⟨ (Z'' ∷ w ∷ []) ⊨ renameFo ρs witFo ⟩ ≡ ⟨ (w ∷ Z'' ∷ []) ⊨ witFo ⟩
        rs Z'' w = cong ⟨_⟩ (Ren.⊨-rename ρs witFo (Z'' ∷ w ∷ []) (w ∷ Z'' ∷ []) (ags Z'' w))

      sep-out : (Z w : CS.S) → ⟨ (w ∷ []) ⊨ sepFo Z ⟩ → ∥ Body Z w ∥₁
      sep-out Z w = PT.rec squash₁ (λ
        { (inl hz) → ∣ inl hz ∣₁
        ; (inr h') → PT.rec squash₁ (λ
          { (inl e) → ∣ inr (inl e) ∣₁
          ; (inr hw) → PT.map (λ { (Z'' , (eZ , hr)) → inr (inr
              (subst (λ u → ⟨ (w ∷ u ∷ []) ⊨ witFo ⟩) (S≡ {x = Z''} {y = Z} eZ)
                (transport (rs Z'' w) hr))) }) hw }) h' })

      sep-in : (Z w : CS.S) → Body Z w → ⟨ (w ∷ []) ⊨ sepFo Z ⟩
      sep-in Z w (inl hz) = ∣ inl hz ∣₁
      sep-in Z w (inr (inl e)) = ∣ inr ∣ inl e ∣₁ ∣₁
      sep-in Z w (inr (inr hw)) = ∣ inr ∣ inr ∣ Z , (refl , transport (sym (rs Z w)) hw) ∣₁ ∣₁ ∣₁

    opaque
      Φ : CS.S → CS.S
      Φ Z = hasSeparationL (Bnd Z) (sepFo Z) .fst .fst

      Φ-mem : (Z w : CS.S) → (w CS.∈ˢ Φ Z) ≡ ((w CS.∈ˢ Bnd Z) ⊓ ((w ∷ []) ⊨ sepFo Z))
      Φ-mem Z = hasSeparationL (Bnd Z) (sepFo Z) .fst .snd

    Φ-in : (Z w : CS.S) → Body Z w → ⟨ fst w ∈ˢ fst (Φ Z) ⟩
    Φ-in Z w b = subst ⟨_⟩ (sym (Φ-mem Z w)) (bnd b , sep-in Z w b)
      where
      bnd : Body Z w → ⟨ w CS.∈ˢ Bnd Z ⟩
      bnd (inl hz) = bnd-Z Z w hz
      bnd (inr (inl e)) = bnd-L Z w (subst (λ u → ⟨ u ∈ˢ Lset lam ⟩) (sym e) HSH.∅∈Lsetα)
      bnd (inr (inr hw)) = bnd-L Z w (wit-L Z w hw)

    Φ-out : (Z w : CS.S) → ⟨ fst w ∈ˢ fst (Φ Z) ⟩ → ∥ Body Z w ∥₁
    Φ-out Z w h = sep-out Z w (subst ⟨_⟩ (Φ-mem Z w) h .snd)
```

The step formula, over `(Z' ∷ Z ∷ [])`: "the members of Z' are exactly the
members of Z, the empty set, and the witnesses at Z". Sealed with the two facts
the iteration consumes.

```agda
    opaque
      bodyF : Formula CS.S 3
      bodyF = (var i0 ∈̇ var i2) ∨̇ ((var i0 ≐ con ∅ʟ) ∨̇ renameFo ρf witFo)

      ΦFo : Formula CS.S 2
      ΦFo = ∀̇ ( ((var i0 ∈̇ var i1) ⇒̇ bodyF) ∧̇ (bodyF ⇒̇ (var i0 ∈̇ var i1)) )

      private
        rf : (w Z' Z : CS.S)
           → ⟨ (w ∷ Z' ∷ Z ∷ []) ⊨ renameFo ρf witFo ⟩ ≡ ⟨ (w ∷ Z ∷ []) ⊨ witFo ⟩
        rf w Z' Z = cong ⟨_⟩ (Ren.⊨-rename ρf witFo (w ∷ Z' ∷ Z ∷ []) (w ∷ Z ∷ []) (agf w Z' Z))

        bodyF-out : (w Z' Z : CS.S) → ⟨ (w ∷ Z' ∷ Z ∷ []) ⊨ bodyF ⟩ → ∥ Body Z w ∥₁
        bodyF-out w Z' Z = PT.rec squash₁ (λ
          { (inl hz) → ∣ inl hz ∣₁
          ; (inr h') → PT.map (λ
            { (inl e) → inr (inl e)
            ; (inr hw) → inr (inr (transport (rf w Z' Z) hw)) }) h' })

        bodyF-in : (w Z' Z : CS.S) → Body Z w → ⟨ (w ∷ Z' ∷ Z ∷ []) ⊨ bodyF ⟩
        bodyF-in w Z' Z (inl hz) = ∣ inl hz ∣₁
        bodyF-in w Z' Z (inr (inl e)) = ∣ inr ∣ inl e ∣₁ ∣₁
        bodyF-in w Z' Z (inr (inr hw)) = ∣ inr ∣ inr (transport (sym (rf w Z' Z)) hw) ∣₁ ∣₁

      Φ-defines : (Z : CS.S) → ⟨ (Φ Z ∷ Z ∷ []) ⊨ ΦFo ⟩
      Φ-defines Z w =
          (λ h → PT.rec (snd ((w ∷ Φ Z ∷ Z ∷ []) ⊨ bodyF)) (bodyF-in w (Φ Z) Z) (Φ-out Z w h))
        , (λ h → PT.rec (snd (fst w ∈ˢ fst (Φ Z))) (Φ-in Z w) (bodyF-out w (Φ Z) Z h))

      Φ-only : (Z Z' : CS.S) → ⟨ (Z' ∷ Z ∷ []) ⊨ ΦFo ⟩ → Z' ≡ Φ Z
      Φ-only Z Z' h = S≡ (extensionalV {a = fst Z'} {b = fst (Φ Z)}
        (λ v → ⇔toPath (fwd v) (bwd v)))
        where
        fwd : (v : S) → ⟨ v ∈ˢ fst Z' ⟩ → ⟨ v ∈ˢ fst (Φ Z) ⟩
        fwd v hv = PT.rec (snd (v ∈ˢ fst (Φ Z))) (Φ-in Z vS) (bodyF-out vS Z' Z (h vS .fst hv))
          where
          vS : CS.S
          vS = v , isL-trans {x = fst Z'} {y = v} hv (snd Z')
        bwd : (v : S) → ⟨ v ∈ˢ fst (Φ Z) ⟩ → ⟨ v ∈ˢ fst Z' ⟩
        bwd v hv = h vS .snd
          (PT.rec (snd ((vS ∷ Z' ∷ Z ∷ []) ⊨ bodyF)) (bodyF-in vS Z' Z) (Φ-out Z vS hv))
          where
          vS : CS.S
          vS = v , isL-trans {x = fst (Φ Z)} {y = v} hv (snd (Φ Z))
```

THE PACK.

```agda
    pack : StepPack
    pack = record
      { Φ       = Φ
      ; ΦFo     = ΦFo
      ; defines = Φ-defines
      ; only    = Φ-only
      ; grows   = λ Z z hz → Φ-in Z (z , isL-trans {x = fst Z} {y = z} hz (snd Z)) (inl hz)
      ; junk    = λ Z → Φ-in Z ∅ʟ (inr (inl refl))
      ; least   = λ Z k χ vs from w₀ →
                    Φ-in Z (Least.aS Z k χ vs from w₀) (inr (inr (Least.least Z k χ vs from w₀)))
      ; out     = λ Z Z⊆ z hz → PT.rec squash₁ (λ
          { (inl h') → ∣ inl h' ∣₁
          ; (inr (inl e)) → ∣ inr (inl e) ∣₁
          ; (inr (inr hw)) → PT.rec squash₁
              (λ { (T , e' , e , s , k , hb) →
                 PT.map (λ sr → inr (inr sr)) (Out.searched Z Z⊆ (zS Z z hz) T e' e s k hb) })
              (witFo-out (zS Z z hz) Z hw) })
          (Φ-out Z (zS Z z hz) hz) }
      where
      zS : (Z : CS.S) (z : S) → ⟨ z ∈ˢ fst (Φ Z) ⟩ → CS.S
      zS Z z hz = z , isL-trans {x = fst (Φ Z)} {y = z} hz (snd (Φ Z))
```

## Section 3. The transfer with `pixL` discharged

From the hull as an element of L: its collapse values are in L (section 1), so
the premise of src/L/GCH/Condense.lagda.md's `Condense` is met.

```agda
module Discharge (lam : S) (ordλ : IsOrd lam)
  (succλ : (d : S) → ⟨ d ∈ˢ lam ⟩ → ⟨ sucV d ∈ˢ lam ⟩)
  (X : S) (X⊆L : (x : S) → ⟨ x ∈ˢ X ⟩ → ⟨ x ∈ˢ Lset lam ⟩)
  (∅∈λ : ⟨ ∅ ∈ˢ lam ⟩)
  (M-isL : ⟨ isL (HullStage.M lam ordλ succλ X X⊆L ∅∈λ) ⟩) where

  module HS = HullStage lam ordλ succλ X X⊆L ∅∈λ using ( M )
  module HSC = HullStage.C lam ordλ succλ X X⊆L ∅∈λ using ( πX )
  module P = PiIn (HS.M , M-isL) using ( πX-isL )

  pixL : (x : S) → ⟨ x ∈ˢ HSC.πX ⟩ → ⟨ isL x ⟩
  pixL = P.πX-isL
```

The telescope of `Condense` minus `pixL`, plus the start `X` as an element of L
(the iteration begins at `X`, and `OmegaRec`'s `Iterate` starts at an element of
L).

```agda
module Condense′ (lam : S) (ordλ : IsOrd lam)
  (succλ : (d : S) → ⟨ d ∈ˢ lam ⟩ → ⟨ sucV d ∈ˢ lam ⟩)
  (X : S) (X⊆L : (x : S) → ⟨ x ∈ˢ X ⟩ → ⟨ x ∈ˢ Lset lam ⟩)
  (∅∈λ : ⟨ ∅ ∈ˢ lam ⟩)
  (elem : Frame.A.Elementary lam ordλ succλ X X⊆L ∅∈λ)
  (sup : Superadequate lam)
  (X-isL : ⟨ isL X ⟩)
  where

  module T = Telescope lam ordλ succλ X X⊆L ∅∈λ using ( Code; val; Reads; module StepPack )
  module TB = Telescope.Build lam ordλ succλ X X⊆L ∅∈λ using ( pack; Φ )
  module HI = Telescope.HullIter lam ordλ succλ X X⊆L ∅∈λ X-isL TB.pack
    using ( hullL; hullL-spec; hullStep; hullStep-suc; hullStep-in; hullStep⊆Hull; depth; M-isL )
  module HS = HullStage lam ordλ succλ X X⊆L ∅∈λ using ( M )
  module HSH = HullStage.H lam ordλ succλ X X⊆L ∅∈λ using ( Hull⊆L )
  module HSC = HullStage.C lam ordλ succλ X X⊆L ∅∈λ using ( πX )
  module D = Discharge lam ordλ succλ X X⊆L ∅∈λ HI.M-isL using ( pixL )
```

The hull as an element of L, and the iteration that reaches it.

```agda
  hullL : CS.S
  hullL = HI.hullL

  hullL-spec : fst hullL ≡ HS.M
  hullL-spec = HI.hullL-spec

  hullStep : ℕ → CS.S
  hullStep = HI.hullStep

  hullStep-suc : (n : ℕ) → hullStep (suc n) ≡ TB.Φ (hullStep n)
  hullStep-suc = HI.hullStep-suc

  hullStep-in : (c : T.Code) → ⟨ fst (T.val c) ∈ˢ fst (hullStep (HI.depth c)) ⟩
  hullStep-in = HI.hullStep-in

  M-isL : ⟨ isL HS.M ⟩
  M-isL = HI.M-isL

  pixL : (x : S) → ⟨ x ∈ˢ HSC.πX ⟩ → ⟨ isL x ⟩
  pixL = D.pixL

  condenses′ : Σ[ β ∈ S ] (IsOrd β × (HSC.πX ≡ Lset β))
  condenses′ = Condense.condenses lam ordλ succλ X X⊆L ∅∈λ elem sup D.pixL
```
