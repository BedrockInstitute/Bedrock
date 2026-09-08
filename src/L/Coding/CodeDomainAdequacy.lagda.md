<!--en-->
# Soundness and completeness of the closed code domain
<!--zh-->
# 封闭码定义域的可靠性与完备性
<!--ja-->
# 閉じた符号の定義域の健全性と完全性
<!--/-->

<!--en-->
Assuming a set satisfies the shape and closure formula `codesAt`, this chapter
decodes every member to a formula at its recorded arity and proves conversely
that every formula key enters the domain. It then applies both directions to
the canonical set `AllCodes`; the constants used by its syntax come from
`CodeAlphabet`, while the ten constructor tags come from `CodeDomain`.
<!--zh-->
假设一个集合满足形状与封闭公式 `codesAt`，本章把其中每个成员解码为其记录元数上的公式，并反向证明每条公式的键都进入该定义域。随后把两个方向施于典范集合 `AllCodes`；其语法所用的常元来自 `CodeAlphabet`，十个构造子标签则来自 `CodeDomain`。
<!--ja-->
集合が形と閉性の論理式 `codesAt` を満たすと仮定し、本章では各要素を記録されたアリティの論理式へ復号し、逆に各論理式のキーがその定義域へ入ることを示す。最後に両方向を正準集合 `AllCodes` へ適用する。構文が使う定数は `CodeAlphabet` から、十個の構成子タグは `CodeDomain` から得る。
<!--/-->

```agda
{-# OPTIONS --cubical --safe --guardedness #-}

open import Base.Prelude
open import Base.Truth
open import Base.Classical using ( LEM )

module L.Coding.CodeDomainAdequacy {ℓ : Level} (lem : LEM (ℓ-suc ℓ)) where

open import FOL.ZFStructure using ( module hPropStructure )
open import FOL.Syntax using
  ( Formula; Term; var; con; _∈̇_; _≐_; _∧̇_; _∨̇_; _⇒̇_; ⊥̇; ∃̇_; ∀̇_; ∃̇∈; ∀̇∈ )
import FOL.Absoluteness
open import V.Hierarchy {ℓ} using ( 𝒮ᵥ )
open import V.Coding {ℓ} using ( pr; pr-inj; #-inj′; #mono )
open import L.Constructible {ℓ} using ( 𝒮ʟ; isL; isL-trans )
open import L.Coding.Environment {ℓ} using ( env )
open import L.Coding.EnvironmentSet {ℓ} lem using ( envSet )
open import L.Axioms.Numerals {ℓ} using ( numeralL-fst; sucʟ; sucʟ-fst )
open import L.Coding.Model {ℓ} using ( appAt; appAt-adequate )
open import L.Coding.Expressions {ℓ} using ( sucAtL )
open import L.Coding.Model {ℓ} using ( container )
import L.Coding.Expressions {ℓ} as CodingExpressions
module E = CodingExpressions.PairExpression
open import L.Coding.Quantification {ℓ} using
  ( i0; i1; i2; i3; i4; i5; i6; i7; i8; sh
  ; pr-out; pr-in; down; fstS; sndS; suc-out; suc-in
  ; sndEx; sndAll; bothEx
  ; sndEx-out; sndAll-in; bothEx-out; bothAll-in
  ; fillSnd; fillBoth; useSnd; useBoth
  ; f0; f1; f2; f3; f4; f5; f6; f7; f8; f9
  ; bigOr-in; bigOr-out )
open import L.Coding.EnvironmentTower {ℓ} lem using ( module Tower; nn )
open import L.Coding.CodeDomain {ℓ} using
  ( isTm; keyUp; keyExpr; atomKeyExpr; bndKeyExpr
  ; unKey; binKey; atomKey; bndKey
  ; Tags; shN; module Shape; shapeAt; module Close; closeAt; codesAt )
open import L.Coding.CodeAlphabet {ℓ} using ( module Alphabet )

open import Cubical.Data.Nat using ( _+_ )
open import Cubical.Data.FinData using ( toℕ )
open import Cubical.Data.FinData.Properties using ( toℕ<n )
open import Cubical.Data.Vec using ( _∷_; lookup )
open import Cubical.Data.Sigma using ( _×_ )
open import Cubical.Data.Sum using ( _⊎_; inl; inr )
open import Cubical.Foundations.Prelude using ( subst2 )
import Cubical.Data.Empty as Empty
import Cubical.HITs.PropositionalTruncation as PT
open PT using ( ∥_∥₁; ∣_∣₁; squash₁ )
open import Cubical.HITs.CumulativeHierarchy.Base using ( V; _∈_; setIsSet )
open import Cubical.HITs.CumulativeHierarchy.Properties using ( ⟪_⟫; ∈-asFiber )
open import Cubical.HITs.CumulativeHierarchy.Constructions
  using ( module InfinitySet )
open InfinitySet {ℓ} using ( #_; sucV )

open hPropStructure 𝒮ʟ using ( S )

module AbsL = FOL.Absoluteness.Single 𝒮ᵥ isL isL-trans using ( _^_; _⊨ᵐ_ )
open AbsL using ( _^_ ) renaming ( _⊨ᵐ_ to _⊨_ )
```
<!--en-->
## Reading the description

The semantic elimination lemmas turn satisfaction of the description into concrete data. They recover term codes, successor-arity keys, constructor tags and payloads, then expose the shape and closure clauses needed to follow a code to its immediate subcodes.
<!--zh-->
## 读取描述

语义消去引理把对描述的满足化为具体数据：恢复词项码、后继元数键、构造子标签与载荷，再给出沿码走向其直接子码所需的形状与封闭子句。
<!--ja-->
## 記述の読み出し

意味論的な除去補題は、記述の充足から具体的なデータを取り出します。項の符号、後続アリティのキー、構成子タグとペイロードを復元し、符号から直下の部分符号へ進むための形と閉性の条件を明らかにします。
<!--/-->

The codes, read. The semantic content of the ten payloads, and one reader per
macro, at variable environments.

```agda
```

A term code over the carrier `Wv` at the arity `ar`.

```agda
IsTmV : V ℓ → V ℓ → V ℓ → Type (ℓ-suc ℓ)
IsTmV Wv t ar = ∥ (Σ[ x ∈ V ℓ ] ((t ≡ pr (# 0) x) × ⟨ x ∈ Wv ⟩))
                ⊎ (Σ[ i ∈ V ℓ ] ((t ≡ pr (# 1) i) × ⟨ i ∈ ar ⟩)) ∥₁

module CodesSem (Wv Cv : V ℓ) where
  AtomP BinP ConP QuP BqP : V ℓ → V ℓ → Type (ℓ-suc ℓ)
  AtomP ar r = ∥ Σ[ t ∈ V ℓ ] Σ[ u ∈ V ℓ ] ((r ≡ pr t u) × (IsTmV Wv t ar × IsTmV Wv u ar)) ∥₁
  BinP ar r = ∥ Σ[ a ∈ V ℓ ] Σ[ b ∈ V ℓ ] ((r ≡ pr a b) × (⟨ pr ar a ∈ Cv ⟩ × ⟨ pr ar b ∈ Cv ⟩)) ∥₁
  ConP ar r = r ≡ # 0
  QuP ar r = ⟨ pr (sucV ar) r ∈ Cv ⟩
  BqP ar r = ∥ Σ[ t ∈ V ℓ ] Σ[ a ∈ V ℓ ] ((r ≡ pr t a) × (IsTmV Wv t ar × ⟨ pr (sucV ar) a ∈ Cv ⟩)) ∥₁

  PayN : ℕ → V ℓ → V ℓ → Type (ℓ-suc ℓ)
  PayN 0 = AtomP
  PayN 1 = AtomP
  PayN 2 = BinP
  PayN 3 = BinP
  PayN 4 = BinP
  PayN 5 = ConP
  PayN 6 = QuP
  PayN 7 = QuP
  PayN 8 = BqP
  PayN 9 = BqP
  PayN (suc (suc (suc (suc (suc (suc (suc (suc (suc (suc _)))))))))) _ _ = Empty.⊥*
```

`p` is the tagged payload of some tag.

```agda
  Key : V ℓ → V ℓ → Type (ℓ-suc ℓ)
  Key ar p = ∥ Σ[ k ∈ Fin 10 ] Σ[ r ∈ V ℓ ] ((p ≡ pr (# (toℕ k)) r) × PayN (toℕ k) ar r) ∥₁
```

The term reader, at any frame.

```agda
module _ {k : ℕ} (t ar w N0 N1 : Fin k) (δ : S ^ k)
  (q0 : fst (lookup N0 δ) ≡ # 0) (q1 : fst (lookup N1 δ) ≡ # 1) where
  private
    Wv = fst (lookup w δ)

  isTm-out : ⟨ δ ⊨ isTm t ar w N0 N1 ⟩ → IsTmV Wv (fst (lookup t δ)) (fst (lookup ar δ))
  isTm-out = PT.rec squash₁
    (λ { (inl h) → PT.map
           (λ { (v , s , (e , v∈)) → inl (fst v , (e ∙ cong (λ a → pr a (fst v)) q0 , v∈)) })
           (sndEx-out t N0 (var i0 ∈̇ var (sh 2 w)) δ h)
       ; (inr h) → PT.map
           (λ { (v , s , (e , v∈)) → inr (fst v , (e ∙ cong (λ a → pr a (fst v)) q1 , v∈)) })
           (sndEx-out t N1 (var i0 ∈̇ var (sh 2 ar)) δ h) })

  isTm-in : IsTmV Wv (fst (lookup t δ)) (fst (lookup ar δ)) → ⟨ δ ⊨ isTm t ar w N0 N1 ⟩
  isTm-in = PT.rec (snd (δ ⊨ isTm t ar w N0 N1))
    (λ { (inl (x , (e , x∈))) →
           ∣ inl (fillSnd t δ (lookup N0 δ) (down (lookup w δ) x x∈)
                    (e ∙ cong (λ a → pr a x) (sym q0)) (var i0 ∈̇ var (sh 2 w)) x∈ N0 refl) ∣₁
       ; (inr (i , (e , i∈))) →
           ∣ inr (fillSnd t δ (lookup N1 δ) (down (lookup ar δ) i i∈)
                    (e ∙ cong (λ a → pr a i) (sym q1)) (var i0 ∈̇ var (sh 2 ar)) i∈ N1 refl) ∣₁ })
```

The successor key.

```agda
module _ {k : ℕ} (C ar r : Fin k) (δ : S ^ k) where
  keyUp-out : ⟨ δ ⊨ keyUp C ar r ⟩ → ⟨ pr (sucV (fst (lookup ar δ))) (fst (lookup r δ)) ∈ fst (lookup C δ) ⟩
  keyUp-out = PT.rec (snd (pr (sucV (fst (lookup ar δ))) (fst (lookup r δ)) ∈ fst (lookup C δ)))
    (λ { (c' , (c'∈ , h)) → PT.rec (snd (pr (sucV (fst (lookup ar δ))) (fst (lookup r δ)) ∈ fst (lookup C δ)))
      (λ { (s , (s∈ , h')) → PT.rec (snd (pr (sucV (fst (lookup ar δ))) (fst (lookup r δ)) ∈ fst (lookup C δ)))
        (λ { (ar' , (ar'∈ , (e , hs))) →
          subst (λ u → ⟨ u ∈ fst (lookup C δ) ⟩)
            (pr-out i2 i0 (sh 3 r) (ar' ∷ s ∷ c' ∷ δ) e
             ∙ cong (λ a → pr a (fst (lookup r δ))) (suc-out (sh 3 ar) i0 (ar' ∷ s ∷ c' ∷ δ) hs))
            c'∈ })
        h' })
      h })

  keyUp-in : ⟨ pr (sucV (fst (lookup ar δ))) (fst (lookup r δ)) ∈ fst (lookup C δ) ⟩ → ⟨ δ ⊨ keyUp C ar r ⟩
  keyUp-in h = ∣ c' , (h , ∣ c .fst , (c .snd .fst , ∣ ar' , (c .snd .snd .fst
    , ( pr-in i2 i0 (sh 3 r) (ar' ∷ c .fst ∷ c' ∷ δ) (sym (cong (λ a → pr a (fst (lookup r δ))) (sucʟ-fst (lookup ar δ))))
      , suc-in (sh 3 ar) i0 (ar' ∷ c .fst ∷ c' ∷ δ) (sucʟ-fst (lookup ar δ)) )) ∣₁) ∣₁) ∣₁
    where
    ar' : S
    ar' = sucʟ (lookup ar δ)
    c' : S
    c' = down (lookup C δ) (pr (sucV (fst (lookup ar δ))) (fst (lookup r δ))) h
    c = container c' ar' (lookup r δ) (cong (λ a → pr a (fst (lookup r δ))) (sym (sucʟ-fst (lookup ar δ))))
```

The key readers are instances of structural membership adequacy.

```agda
module _ {k : ℕ} (C ar N a : Fin k) (δ : S ^ k) where
  private
    Cv = fst (lookup C δ)
    A = fst (lookup ar δ)
    Nv = fst (lookup N δ)

  unKey-out : ⟨ δ ⊨ unKey C ar N a ⟩ → ⟨ pr A (pr Nv (fst (lookup a δ))) ∈ Cv ⟩
  unKey-out = E.member-out (keyExpr ar N (E.slot a)) (var C) δ

  unKey-in : ⟨ pr A (pr Nv (fst (lookup a δ))) ∈ Cv ⟩ → ⟨ δ ⊨ unKey C ar N a ⟩
  unKey-in = E.member-in (keyExpr ar N (E.slot a)) (var C) δ

module _ {k : ℕ} (C ar N a b : Fin k) (δ : S ^ k) where
  private
    Cv = fst (lookup C δ)
    A = fst (lookup ar δ)
    Nv = fst (lookup N δ)
    P = pr (fst (lookup a δ)) (fst (lookup b δ))

  binKey-out : ⟨ δ ⊨ binKey C ar N a b ⟩ → ⟨ pr A (pr Nv P) ∈ Cv ⟩
  binKey-out = E.member-out (keyExpr ar N (E.pair (E.slot a) (E.slot b))) (var C) δ

  binKey-in : ⟨ pr A (pr Nv P) ∈ Cv ⟩ → ⟨ δ ⊨ binKey C ar N a b ⟩
  binKey-in = E.member-in (keyExpr ar N (E.pair (E.slot a) (E.slot b))) (var C) δ

module _ {k : ℕ} (C ar N Nx x Ny y : Fin k) (δ : S ^ k) where
  private
    Cv = fst (lookup C δ)
    A = fst (lookup ar δ)
    Nv = fst (lookup N δ)
    T = pr (fst (lookup Nx δ)) (fst (lookup x δ))
    U = pr (fst (lookup Ny δ)) (fst (lookup y δ))

  atomKey-out : ⟨ δ ⊨ atomKey C ar N Nx x Ny y ⟩ → ⟨ pr A (pr Nv (pr T U)) ∈ Cv ⟩
  atomKey-out = E.member-out (atomKeyExpr ar N Nx x Ny y) (var C) δ

  atomKey-in : ⟨ pr A (pr Nv (pr T U)) ∈ Cv ⟩ → ⟨ δ ⊨ atomKey C ar N Nx x Ny y ⟩
  atomKey-in = E.member-in (atomKeyExpr ar N Nx x Ny y) (var C) δ

module _ {k : ℕ} (C ar N Nx x a : Fin k) (δ : S ^ k) where
  private
    Cv = fst (lookup C δ)
    A = fst (lookup ar δ)
    Nv = fst (lookup N δ)
    T = pr (fst (lookup Nx δ)) (fst (lookup x δ))
    Av = fst (lookup a δ)

  bndKey-out : ⟨ δ ⊨ bndKey C ar N Nx x a ⟩ → ⟨ pr A (pr Nv (pr T Av)) ∈ Cv ⟩
  bndKey-out = E.member-out (bndKeyExpr ar N Nx x a) (var C) δ

  bndKey-in : ⟨ pr A (pr Nv (pr T Av)) ∈ Cv ⟩ → ⟨ δ ⊨ bndKey C ar N Nx x a ⟩
  bndKey-in = E.member-in (bndKeyExpr ar N Nx x a) (var C) δ
```

The payloads, read. At `r ∷ s'' ∷ p ∷ s' ∷ F ∷ ar ∷ s ∷ q ∷ c ∷ γ`.

```agda
module PayRead {m : ℕ} (C w : Fin m) (N : Fin 10 → Fin m) (δ : S ^ (9 + m))
  (tg : Tags δ (shN 9 N)) where
  private
    Cv = fst (lookup (sh 9 C) δ)
    Wv = fst (lookup (sh 9 w) δ)
    A = fst (lookup i5 δ)
    R = fst (lookup i0 δ)
    q0 = tg f0
    q1 = tg f1
    rS = lookup i0 δ
    module Sh = Shape C w N
  open CodesSem Wv Cv

  private
    tmBody : Formula S (12 + m)
    tmBody = isTm i1 i8 (sh 12 w) (sh 12 (N f0)) (sh 12 (N f1)) ∧̇ isTm i0 i8 (sh 12 w) (sh 12 (N f0)) (sh 12 (N f1))
    binBody : Formula S (12 + m)
    binBody = appAt (sh 12 C) i8 i1 ∧̇ appAt (sh 12 C) i8 i0
    bqBody : Formula S (12 + m)
    bqBody = isTm i1 i8 (sh 12 w) (sh 12 (N f0)) (sh 12 (N f1)) ∧̇ keyUp (sh 12 C) i8 i0

  atom-out : ⟨ δ ⊨ Sh.atomPay ⟩ → AtomP A R
  atom-out h = PT.map
    (λ { (t , u , s , (e , (ht , hu))) → fst t , fst u
       , ( e , ( isTm-out i1 i8 (sh 12 w) (sh 12 (N f0)) (sh 12 (N f1)) (u ∷ t ∷ s ∷ δ) q0 q1 ht
               , isTm-out i0 i8 (sh 12 w) (sh 12 (N f0)) (sh 12 (N f1)) (u ∷ t ∷ s ∷ δ) q0 q1 hu ) ) })
    (bothEx-out i0 tmBody δ h)

  atom-in : AtomP A R → ⟨ δ ⊨ Sh.atomPay ⟩
  atom-in = PT.rec (snd (δ ⊨ Sh.atomPay))
    (λ { (t , u , (e , (ht , hu))) →
      fillBoth i0 δ (fstS rS t u e) (sndS rS t u e) e tmBody
        ( isTm-in i1 i8 (sh 12 w) (sh 12 (N f0)) (sh 12 (N f1)) (δ12 t u e) q0 q1 ht
        , isTm-in i0 i8 (sh 12 w) (sh 12 (N f0)) (sh 12 (N f1)) (δ12 t u e) q0 q1 hu ) })
    where
    δ12 : (t u : V ℓ) (e : R ≡ pr t u) → S ^ (12 + m)
    δ12 t u e = sndS rS t u e ∷ fstS rS t u e ∷ container rS (fstS rS t u e) (sndS rS t u e) e .fst ∷ δ

  bin-out : ⟨ δ ⊨ Sh.binPay ⟩ → BinP A R
  bin-out h = PT.map
    (λ { (a , b , s , (e , (ha , hb))) → fst a , fst b
       , ( e , ( subst ⟨_⟩ (appAt-adequate (sh 12 C) i8 i1 (b ∷ a ∷ s ∷ δ)) ha
               , subst ⟨_⟩ (appAt-adequate (sh 12 C) i8 i0 (b ∷ a ∷ s ∷ δ)) hb ) ) })
    (bothEx-out i0 binBody δ h)

  bin-in : BinP A R → ⟨ δ ⊨ Sh.binPay ⟩
  bin-in = PT.rec (snd (δ ⊨ Sh.binPay))
    (λ { (a , b , (e , (ha , hb))) →
      fillBoth i0 δ (fstS rS a b e) (sndS rS a b e) e binBody
        ( subst ⟨_⟩ (sym (appAt-adequate (sh 12 C) i8 i1 (δ12 a b e))) ha
        , subst ⟨_⟩ (sym (appAt-adequate (sh 12 C) i8 i0 (δ12 a b e))) hb ) })
    where
    δ12 : (a b : V ℓ) (e : R ≡ pr a b) → S ^ (12 + m)
    δ12 a b e = sndS rS a b e ∷ fstS rS a b e ∷ container rS (fstS rS a b e) (sndS rS a b e) e .fst ∷ δ

  con-out : ⟨ δ ⊨ Sh.conPay ⟩ → ConP A R
  con-out h = h ∙ q0

  con-in : ConP A R → ⟨ δ ⊨ Sh.conPay ⟩
  con-in h = h ∙ sym q0

  qu-out : ⟨ δ ⊨ Sh.quPay ⟩ → QuP A R
  qu-out = keyUp-out (sh 9 C) i5 i0 δ

  qu-in : QuP A R → ⟨ δ ⊨ Sh.quPay ⟩
  qu-in = keyUp-in (sh 9 C) i5 i0 δ

  bq-out : ⟨ δ ⊨ Sh.bqPay ⟩ → BqP A R
  bq-out h = PT.map
    (λ { (t , a , s , (e , (ht , ha))) → fst t , fst a
       , ( e , ( isTm-out i1 i8 (sh 12 w) (sh 12 (N f0)) (sh 12 (N f1)) (a ∷ t ∷ s ∷ δ) q0 q1 ht
               , keyUp-out (sh 12 C) i8 i0 (a ∷ t ∷ s ∷ δ) ha ) ) })
    (bothEx-out i0 bqBody δ h)

  bq-in : BqP A R → ⟨ δ ⊨ Sh.bqPay ⟩
  bq-in = PT.rec (snd (δ ⊨ Sh.bqPay))
    (λ { (t , a , (e , (ht , ha))) →
      fillBoth i0 δ (fstS rS t a e) (sndS rS t a e) e bqBody
        ( isTm-in i1 i8 (sh 12 w) (sh 12 (N f0)) (sh 12 (N f1)) (δ12 t a e) q0 q1 ht
        , keyUp-in (sh 12 C) i8 i0 (δ12 t a e) ha ) })
    where
    δ12 : (t a : V ℓ) (e : R ≡ pr t a) → S ^ (12 + m)
    δ12 t a e = sndS rS t a e ∷ fstS rS t a e ∷ container rS (fstS rS t a e) (sndS rS t a e) e .fst ∷ δ

  payN-out : (k : ℕ) → ⟨ δ ⊨ Sh.payN k ⟩ → PayN k A R
  payN-out 0 = atom-out
  payN-out 1 = atom-out
  payN-out 2 = bin-out
  payN-out 3 = bin-out
  payN-out 4 = bin-out
  payN-out 5 = con-out
  payN-out 6 = qu-out
  payN-out 7 = qu-out
  payN-out 8 = bq-out
  payN-out 9 = bq-out
  payN-out (suc (suc (suc (suc (suc (suc (suc (suc (suc (suc _)))))))))) h = h

  payN-in : (k : ℕ) → PayN k A R → ⟨ δ ⊨ Sh.payN k ⟩
  payN-in 0 = atom-in
  payN-in 1 = atom-in
  payN-in 2 = bin-in
  payN-in 3 = bin-in
  payN-in 4 = bin-in
  payN-in 5 = con-in
  payN-in 6 = qu-in
  payN-in 7 = qu-in
  payN-in 8 = bq-in
  payN-in 9 = bq-in
  payN-in (suc (suc (suc (suc (suc (suc (suc (suc (suc (suc _)))))))))) h = h
```

The ten, read. At `p ∷ s' ∷ F ∷ ar ∷ s ∷ q ∷ c ∷ γ`.

```agda
module TenRead {m : ℕ} (C w : Fin m) (N : Fin 10 → Fin m) (δ : S ^ (7 + m))
  (tg : Tags δ (shN 7 N)) where
  private
    Cv = fst (lookup (sh 7 C) δ)
    Wv = fst (lookup (sh 7 w) δ)
    A = fst (lookup i3 δ)
    P = fst (lookup i0 δ)
    pS = lookup i0 δ
    module Sh = Shape C w N
  open CodesSem Wv Cv

  at-out : (j : Fin 10) → ⟨ δ ⊨ Sh.at j ⟩ → Key A P
  at-out j h = PT.map
    (λ { (r , s , (e , hp)) → j , fst r
       , ( e ∙ cong (λ a → pr a (fst r)) (tg j)
         , PayRead.payN-out C w N (r ∷ s ∷ δ) tg (toℕ j) hp ) })
    (sndEx-out i0 (sh 7 (N j)) (Sh.pay j) δ h)

  at-in : (j : Fin 10) (r : V ℓ) (e : P ≡ pr (# (toℕ j)) r) → PayN (toℕ j) A r → ⟨ δ ⊨ Sh.at j ⟩
  at-in j r e pay =
    fillSnd i0 δ (lookup (sh 7 (N j)) δ) rS e' (Sh.pay j)
      (PayRead.payN-in C w N (rS ∷ container pS (lookup (sh 7 (N j)) δ) rS e' .fst ∷ δ) tg (toℕ j) pay)
      (sh 7 (N j)) refl
    where
    rS : S
    rS = sndS pS (# (toℕ j)) r e
    e' : P ≡ pr (fst (lookup (sh 7 (N j)) δ)) (fst rS)
    e' = e ∙ cong (λ a → pr a r) (sym (tg j))

  ten-out : ⟨ δ ⊨ Sh.ten ⟩ → Key A P
  ten-out h = PT.rec squash₁ (λ { (j , hj) → at-out j hj }) (bigOr-out δ 9 Sh.at h)

  ten-in : Key A P → ⟨ δ ⊨ Sh.ten ⟩
  ten-in = PT.rec (snd (δ ⊨ Sh.ten))
    (λ { (j , r , (e , pay)) → bigOr-in δ 9 Sh.at j (at-in j r e pay) })
```

The shape clause, read.

```agda
module ShapeRead {m : ℕ} (C w E : Fin m) (N : Fin 10 → Fin m) (γ : S ^ m) (tg : Tags γ N) where
  private
    Cv = fst (lookup C γ)
    Wv = fst (lookup w γ)
    Ev = fst (lookup E γ)
    module Sh = Shape C w N
    inner : Formula S (5 + m)
    inner = sndEx i4 i1 Sh.ten
  open CodesSem Wv Cv

  Shaped : V ℓ → Type (ℓ-suc ℓ)
  Shaped c = ∥ Σ[ ar ∈ V ℓ ] Σ[ F ∈ V ℓ ] Σ[ p ∈ V ℓ ]
               (⟨ pr ar F ∈ Ev ⟩ × ((c ≡ pr ar p) × Key ar p)) ∥₁

  shape-out : ⟨ γ ⊨ shapeAt C w E N ⟩ → (c : S) → ⟨ fst c ∈ Cv ⟩ → Shaped (fst c)
  shape-out h c c∈ = PT.rec squash₁
    (λ { (q , (q∈ , hb)) → PT.rec squash₁
      (λ { (ar , F , s , (eq , hs)) → PT.map
        (λ { (p , s' , (ec , ht)) →
          fst ar , fst F , fst p
          , ( subst (λ u → ⟨ u ∈ Ev ⟩) eq q∈
            , ( ec , TenRead.ten-out C w N (p ∷ s' ∷ F ∷ ar ∷ s ∷ q ∷ c ∷ γ) tg ht ) ) })
        (sndEx-out i4 i1 Sh.ten (F ∷ ar ∷ s ∷ q ∷ c ∷ γ) hs) })
      (bothEx-out i0 inner (q ∷ c ∷ γ) hb) })
    (h c c∈)

  shape-in : ((c : S) → ⟨ fst c ∈ Cv ⟩ → Shaped (fst c)) → ⟨ γ ⊨ shapeAt C w E N ⟩
  shape-in k c c∈ = PT.rec (snd ((c ∷ γ) ⊨ ∃̇∈ (var (sh 1 E)) (bothEx i0 inner)))
    (λ { (ar , F , p , (q∈ , (ec , key))) →
      let qS = down (lookup E γ) (pr ar F) q∈
          arS = fstS qS ar F refl
          FS = sndS qS ar F refl
          δ2 = qS ∷ c ∷ γ
          cq = container qS arS FS refl
          δ5 = FS ∷ arS ∷ cq .fst ∷ δ2
          pS = sndS c ar p ec
          cp = container c arS pS ec
          δ7 = pS ∷ cp .fst ∷ δ5
      in ∣ qS , ( q∈ , fillBoth i0 δ2 arS FS refl inner
            (fillSnd i4 δ5 arS pS ec Sh.ten
              (TenRead.ten-in C w N δ7 tg key) i1 refl) ) ∣₁ })
    (k c c∈)
```

The closure clauses, read. At `F ∷ ar ∷ s ∷ q ∷ γ`, with `ar` at `i1`.

```agda
module CloseRead {m : ℕ} (C w : Fin m) (N : Fin 10 → Fin m) (δ : S ^ (4 + m)) (tg : Tags δ (shN 4 N)) where
  private
    Cv = fst (lookup (sh 4 C) δ)
    A = fst (lookup i1 δ)
    arS = lookup i1 δ
    CS = lookup (sh 4 C) δ
    module Cl = Close C w N
```

The atoms.

```agda
  atomClose-out : (k Nx Ny : Fin 10) (X : Fin (4 + m)) (Y : Fin (5 + m))
                → ⟨ δ ⊨ Cl.atomClose k Nx Ny X Y ⟩
                → (x y : S) → ⟨ fst x ∈ fst (lookup X δ) ⟩ → ⟨ fst y ∈ fst (lookup Y (x ∷ δ)) ⟩
                → ⟨ pr A (pr (# (toℕ k)) (pr (pr (# (toℕ Nx)) (fst x)) (pr (# (toℕ Ny)) (fst y)))) ∈ Cv ⟩
  atomClose-out k Nx Ny X Y h x y x∈ y∈ =
    subst (λ u → ⟨ u ∈ Cv ⟩)
      (cong (pr A) (cong₂ pr (tg k) (cong₂ pr (cong (λ a → pr a (fst x)) (tg Nx)) (cong (λ a → pr a (fst y)) (tg Ny)))))
      (atomKey-out (sh 6 C) i3 (sh 6 (N k)) (sh 6 (N Nx)) i1 (sh 6 (N Ny)) i0 (y ∷ x ∷ δ) (h x x∈ y y∈))

  atomClose-in : (k Nx Ny : Fin 10) (X : Fin (4 + m)) (Y : Fin (5 + m))
               → ((x y : S) → ⟨ fst x ∈ fst (lookup X δ) ⟩ → ⟨ fst y ∈ fst (lookup Y (x ∷ δ)) ⟩
                  → ⟨ pr A (pr (# (toℕ k)) (pr (pr (# (toℕ Nx)) (fst x)) (pr (# (toℕ Ny)) (fst y)))) ∈ Cv ⟩)
               → ⟨ δ ⊨ Cl.atomClose k Nx Ny X Y ⟩
  atomClose-in k Nx Ny X Y g x x∈ y y∈ =
    atomKey-in (sh 6 C) i3 (sh 6 (N k)) (sh 6 (N Nx)) i1 (sh 6 (N Ny)) i0 (y ∷ x ∷ δ)
      (subst (λ u → ⟨ u ∈ Cv ⟩)
        (sym (cong (pr A) (cong₂ pr (tg k) (cong₂ pr (cong (λ a → pr a (fst x)) (tg Nx)) (cong (λ a → pr a (fst y)) (tg Ny))))))
        (g x y x∈ y∈))
```

The binary connectives.

```agda
  binClose-out : (k : Fin 10) → ⟨ δ ⊨ Cl.binClose k ⟩
               → (c₁ c₂ a b : S) → ⟨ fst c₁ ∈ Cv ⟩ → ⟨ fst c₂ ∈ Cv ⟩
               → fst c₁ ≡ pr A (fst a) → fst c₂ ≡ pr A (fst b)
               → ⟨ pr A (pr (# (toℕ k)) (pr (fst a) (fst b))) ∈ Cv ⟩
  binClose-out k h c₁ c₂ a b c₁∈ c₂∈ e₁ e₂ =
    subst (λ u → ⟨ u ∈ Cv ⟩) (cong (pr A) (cong (λ v → pr v (pr (fst a) (fst b))) (tg k)))
      (binKey-out (sh 10 C) i7 (sh 10 (N k)) i3 i0 δ10
        (useSnd i0 δ8 arS b e₂ (binKey (sh 10 C) i7 (sh 10 (N k)) i3 i0) i5 refl
          (useSnd i0 (c₁ ∷ δ) arS a e₁ inner i2 refl (h c₁ c₁∈) c₂ c₂∈)))
    where
    inner : Formula S (7 + m)
    inner = ∀̇∈ (var (sh 7 C)) (sndAll i0 i5 (binKey (sh 10 C) i7 (sh 10 (N k)) i3 i0))
    δ7 : S ^ (7 + m)
    δ7 = a ∷ container c₁ arS a e₁ .fst ∷ c₁ ∷ δ
    δ8 : S ^ (8 + m)
    δ8 = c₂ ∷ δ7
    δ10 : S ^ (10 + m)
    δ10 = b ∷ container c₂ arS b e₂ .fst ∷ δ8

  binClose-in : (k : Fin 10)
              → ((c₁ c₂ a b : S) → ⟨ fst c₁ ∈ Cv ⟩ → ⟨ fst c₂ ∈ Cv ⟩
                 → fst c₁ ≡ pr A (fst a) → fst c₂ ≡ pr A (fst b)
                 → ⟨ pr A (pr (# (toℕ k)) (pr (fst a) (fst b))) ∈ Cv ⟩)
              → ⟨ δ ⊨ Cl.binClose k ⟩
  binClose-in k g c₁ c₁∈ = sndAll-in i0 i2 (∀̇∈ (var (sh 7 C)) (sndAll i0 i5 (binKey (sh 10 C) i7 (sh 10 (N k)) i3 i0))) (c₁ ∷ δ) (λ a s s∈ a∈ e₁ c₂ c₂∈ →
    sndAll-in i0 i5 (binKey (sh 10 C) i7 (sh 10 (N k)) i3 i0) (c₂ ∷ a ∷ s ∷ c₁ ∷ δ) (λ b s' s'∈ b∈ e₂ →
      binKey-in (sh 10 C) i7 (sh 10 (N k)) i3 i0 (b ∷ s' ∷ c₂ ∷ a ∷ s ∷ c₁ ∷ δ)
        (subst (λ u → ⟨ u ∈ Cv ⟩) (sym (cong (pr A) (cong (λ v → pr v (pr (fst a) (fst b))) (tg k))))
          (g c₁ c₂ a b c₁∈ c₂∈ e₁ e₂))))
```

The constants.

```agda
  conClose-out : (k : Fin 10) → ⟨ δ ⊨ Cl.conClose k ⟩ → ⟨ pr A (pr (# (toℕ k)) (# 0)) ∈ Cv ⟩
  conClose-out k h =
    subst (λ u → ⟨ u ∈ Cv ⟩) (cong (pr A) (cong₂ pr (tg k) (tg f0)))
      (unKey-out (sh 4 C) i1 (sh 4 (N k)) (sh 4 (N f0)) δ h)

  conClose-in : (k : Fin 10) → ⟨ pr A (pr (# (toℕ k)) (# 0)) ∈ Cv ⟩ → ⟨ δ ⊨ Cl.conClose k ⟩
  conClose-in k h =
    unKey-in (sh 4 C) i1 (sh 4 (N k)) (sh 4 (N f0)) δ
      (subst (λ u → ⟨ u ∈ Cv ⟩) (sym (cong (pr A) (cong₂ pr (tg k) (tg f0)))) h)
```

The unbounded quantifiers.

```agda
  quClose-out : (k : Fin 10) → ⟨ δ ⊨ Cl.quClose k ⟩
              → (c₁ ar' a : S) → ⟨ fst c₁ ∈ Cv ⟩ → fst c₁ ≡ pr (fst ar') (fst a) → fst ar' ≡ sucV A
              → ⟨ pr A (pr (# (toℕ k)) (fst a)) ∈ Cv ⟩
  quClose-out k h c₁ ar' a c₁∈ e₁ es =
    subst (λ u → ⟨ u ∈ Cv ⟩) (cong (pr A) (cong (λ v → pr v (fst a)) (tg k)))
      (unKey-out (sh 8 C) i5 (sh 8 (N k)) i0 δ8
        (useBoth i0 (c₁ ∷ δ) ar' a e₁ (sucAtL i5 i1 ⇒̇ unKey (sh 8 C) i5 (sh 8 (N k)) i0) (h c₁ c₁∈)
          (suc-in i5 i1 δ8 es)))
    where
    δ8 : S ^ (8 + m)
    δ8 = a ∷ ar' ∷ container c₁ ar' a e₁ .fst ∷ c₁ ∷ δ

  quClose-in : (k : Fin 10)
             → ((c₁ ar' a : S) → ⟨ fst c₁ ∈ Cv ⟩ → fst c₁ ≡ pr (fst ar') (fst a) → fst ar' ≡ sucV A
                → ⟨ pr A (pr (# (toℕ k)) (fst a)) ∈ Cv ⟩)
             → ⟨ δ ⊨ Cl.quClose k ⟩
  quClose-in k g c₁ c₁∈ = bothAll-in i0 (sucAtL i5 i1 ⇒̇ unKey (sh 8 C) i5 (sh 8 (N k)) i0) (c₁ ∷ δ) (λ ar' a s s∈ ar'∈ a∈ e₁ hs →
    unKey-in (sh 8 C) i5 (sh 8 (N k)) i0 (a ∷ ar' ∷ s ∷ c₁ ∷ δ)
      (subst (λ u → ⟨ u ∈ Cv ⟩) (sym (cong (pr A) (cong (λ v → pr v (fst a)) (tg k))))
        (g c₁ ar' a c₁∈ e₁ (suc-out i5 i1 (a ∷ ar' ∷ s ∷ c₁ ∷ δ) hs))))
```

The bounded quantifiers. The bound `X` is read at the frame the container
makes, which reduces at either instance.

```agda
  bqClose-out : (k Nx : Fin 10) (X : Fin (8 + m)) → ⟨ δ ⊨ Cl.bqClose k Nx X ⟩
              → (c₁ ar' a : S) → ⟨ fst c₁ ∈ Cv ⟩ → (e₁ : fst c₁ ≡ pr (fst ar') (fst a)) → fst ar' ≡ sucV A
              → (x : S) → ⟨ fst x ∈ fst (lookup X (a ∷ ar' ∷ container c₁ ar' a e₁ .fst ∷ c₁ ∷ δ)) ⟩
              → ⟨ pr A (pr (# (toℕ k)) (pr (pr (# (toℕ Nx)) (fst x)) (fst a))) ∈ Cv ⟩
  bqClose-out k Nx X h c₁ ar' a c₁∈ e₁ es x x∈ =
    subst (λ u → ⟨ u ∈ Cv ⟩)
      (cong (pr A) (cong₂ pr (tg k) (cong (λ v → pr v (fst a)) (cong (λ v → pr v (fst x)) (tg Nx)))))
      (bndKey-out (sh 9 C) i6 (sh 9 (N k)) (sh 9 (N Nx)) i0 i1 (x ∷ δ8)
        (useBoth i0 (c₁ ∷ δ) ar' a e₁ (sucAtL i5 i1 ⇒̇ ∀̇∈ (var X) (bndKey (sh 9 C) i6 (sh 9 (N k)) (sh 9 (N Nx)) i0 i1))
          (h c₁ c₁∈) (suc-in i5 i1 δ8 es) x x∈))
    where
    δ8 : S ^ (8 + m)
    δ8 = a ∷ ar' ∷ container c₁ ar' a e₁ .fst ∷ c₁ ∷ δ

  bqClose-in : (k Nx : Fin 10) (X : Fin (8 + m))
             → ((c₁ ar' a s : S) → ⟨ fst c₁ ∈ Cv ⟩ → fst c₁ ≡ pr (fst ar') (fst a) → fst ar' ≡ sucV A
                → (x : S) → ⟨ fst x ∈ fst (lookup X (a ∷ ar' ∷ s ∷ c₁ ∷ δ)) ⟩
                → ⟨ pr A (pr (# (toℕ k)) (pr (pr (# (toℕ Nx)) (fst x)) (fst a))) ∈ Cv ⟩)
             → ⟨ δ ⊨ Cl.bqClose k Nx X ⟩
  bqClose-in k Nx X g c₁ c₁∈ = bothAll-in i0 (sucAtL i5 i1 ⇒̇ ∀̇∈ (var X) (bndKey (sh 9 C) i6 (sh 9 (N k)) (sh 9 (N Nx)) i0 i1)) (c₁ ∷ δ) (λ ar' a s s∈ ar'∈ a∈ e₁ hs x x∈ →
    bndKey-in (sh 9 C) i6 (sh 9 (N k)) (sh 9 (N Nx)) i0 i1 (x ∷ a ∷ ar' ∷ s ∷ c₁ ∷ δ)
      (subst (λ u → ⟨ u ∈ Cv ⟩)
        (sym (cong (pr A) (cong₂ pr (tg k) (cong (λ v → pr v (fst a)) (cong (λ v → pr v (fst x)) (tg Nx))))))
        (g c₁ ar' a s c₁∈ e₁ (suc-out i5 i1 (a ∷ ar' ∷ s ∷ c₁ ∷ δ) hs) x x∈)))
```

<!--en-->
## Soundness: decoding every member

Every member of a domain satisfying the description decodes to a formula over the chosen constant set. The proof reads its constructor shape, recursively decodes the required subcodes through closure, and reconstructs the corresponding term or formula.
<!--zh-->
## 可靠性：解码每个成员

满足该描述的定义域中，每个成员都解码为选定常元集上的公式。证明读取其构造子形状，经封闭性递归解码所需子码，再重建对应词项或公式。
<!--ja-->
## 健全性：各要素の復号

記述を満たす定義域の各要素は、選んだ定数集合上の論理式へ復号できます。構成子の形を読み、閉性を使って必要な部分符号を再帰的に復号し、対応する項または論理式を再構成します。
<!--/-->

`C` is sound: every member is the key of a formula over `w`. The Δ₀ shape clause
supplies src/L/Coding/Model.lagda.md `closedAt` and
src/L/Coding/CodeShape.lagda.md `shapedAt` for `C` itself, and the decode of
src/L/Coding/CodeSet.lagda.md `witnessAt-out` does the rest.

```agda
open import L.Coding.Expressions {ℓ} using ( tagAtL-adequate )
open import L.Coding.Closure {ℓ} using ( closedAt; binSameClosed-in; unSuccClosed-in; binSuccClosed-in )
open import L.Coding.CodeShape {ℓ} using
  ( shapedAt; shaped-in; ShapeWit; BinWit; bothTm; fstTm; noneB; isTmAt )
open import L.Coding.CodeSet {ℓ} lem using
  ( AllCodes; AllCodes-out; key∈AllCodes; keyS; codeS; witnessAt-out )
open import Cubical.Foundations.HLevels using ( isProp× )

module _ (Wv Cv : V ℓ) where
  open CodesSem Wv Cv

  isPropPayN : (n : ℕ) (ar r : V ℓ) → isProp (PayN n ar r)
  isPropPayN 0 ar r = squash₁
  isPropPayN 1 ar r = squash₁
  isPropPayN 2 ar r = squash₁
  isPropPayN 3 ar r = squash₁
  isPropPayN 4 ar r = squash₁
  isPropPayN 5 ar r = setIsSet r (# 0)
  isPropPayN 6 ar r = snd (pr (sucV ar) r ∈ Cv)
  isPropPayN 7 ar r = snd (pr (sucV ar) r ∈ Cv)
  isPropPayN 8 ar r = squash₁
  isPropPayN 9 ar r = squash₁
  isPropPayN (suc (suc (suc (suc (suc (suc (suc (suc (suc (suc _)))))))))) ar r = Empty.isProp⊥*
```

A key read at a stated tag.

```agda
  keyAt : (ar p : V ℓ) → Key ar p → (n : ℕ) (r : V ℓ) → p ≡ pr (# n) r → PayN n ar r
  keyAt ar p key n r e = PT.rec (isPropPayN n ar r)
    (λ { (k , r' , (e' , pay)) →
      let q = pr-inj (sym e ∙ e')
      in subst2 (λ j x → PayN j ar x) (sym (#-inj′ (q .fst))) (sym (q .snd)) pay })
    key
```

A term witness for src/L/Coding/CodeShape.lagda.md `isTmAt`, at any frame.

```agda
tmWit : ∀ {j} (ti Ni Ai : Fin j) (env : S ^ j)
      → IsTmV (fst (lookup Ai env)) (fst (lookup ti env)) (fst (lookup Ni env))
      → ⟨ env ⊨ isTmAt ti Ni Ai ⟩
tmWit ti Ni Ai env = PT.rec (snd (env ⊨ isTmAt ti Ni Ai))
  (λ { (inl (x , (e , x∈))) →
         ∣ inl ∣ down (lookup Ai env) x x∈
           , ( subst ⟨_⟩ (sym (tagAtL-adequate (suc ti) 0 zero (down (lookup Ai env) x x∈ ∷ env))) e
             , x∈ ) ∣₁ ∣₁
     ; (inr (i , (e , i∈))) →
         ∣ inr ∣ down (lookup Ni env) i i∈
           , ( subst ⟨_⟩ (sym (tagAtL-adequate (suc ti) 1 zero (down (lookup Ni env) i i∈ ∷ env))) e
             , i∈ ) ∣₁ ∣₁ })

module CodesSound {m : ℕ} (C w E : Fin m) (N : Fin 10 → Fin m) (γ : S ^ m) (W : S)
  (qw : fst (lookup w γ) ≡ fst W) (tg : Tags γ N)
  (arity : (n F : S) → ⟨ pr (fst n) (fst F) ∈ fst (lookup E γ) ⟩ → ∥ Σ[ k ∈ ℕ ] (fst n ≡ # k) ∥₁)
  (hs : ⟨ γ ⊨ shapeAt C w E N ⟩) where
  private
    Cv = fst (lookup C γ)
    CS = lookup C γ
    Wv = fst (lookup w γ)
    Ev = fst (lookup E γ)
    module SR = ShapeRead C w E N γ tg
  open CodesSem Wv Cv

  private
```

The frame the decode reads in: `C` at slot zero, the member at one.

```agda
    δ' : S → S ^ (2 + m)
    δ' c = CS ∷ c ∷ γ
```

The shape of a member, at a stated tag.

```agda
    at : (c : S) → ⟨ fst c ∈ Cv ⟩ → (n : ℕ) (ar r : V ℓ) → fst c ≡ pr ar (pr (# n) r)
       → PayN n ar r
    at c c∈ n ar r e = PT.rec (isPropPayN Wv Cv n ar r)
      (λ { (ar' , F , p , (q∈ , (ec , key))) →
        let q = pr-inj (sym ec ∙ e)
        in subst (λ a → PayN n a r) (q .fst) (keyAt Wv Cv ar' p key n r (q .snd)) })
      (SR.shape-out hs c c∈)

    binAt : (k : ℕ) → PayN k ≡ BinP → (c ar a b : S) → ⟨ fst c ∈ Cv ⟩
          → fst c ≡ pr (fst ar) (pr (# k) (pr (fst a) (fst b)))
          → ⟨ pr (fst ar) (fst a) ∈ Cv ⟩ × ⟨ pr (fst ar) (fst b) ∈ Cv ⟩
    binAt k eq c ar a b c∈ e = PT.rec (isProp× (snd (pr (fst ar) (fst a) ∈ Cv)) (snd (pr (fst ar) (fst b) ∈ Cv)))
      (λ { (a' , b' , (er , (ha , hb))) →
        let q = pr-inj er
        in subst (λ u → ⟨ pr (fst ar) u ∈ Cv ⟩) (sym (q .fst)) ha
         , subst (λ u → ⟨ pr (fst ar) u ∈ Cv ⟩) (sym (q .snd)) hb })
      (subst (λ P → P (fst ar) (pr (fst a) (fst b))) eq (at c c∈ k (fst ar) (pr (fst a) (fst b)) e))

    bqAt : (k : ℕ) → PayN k ≡ BqP → (c ar a b : S) → ⟨ fst c ∈ Cv ⟩
         → fst c ≡ pr (fst ar) (pr (# k) (pr (fst a) (fst b)))
         → ⟨ pr (sucV (fst ar)) (fst b) ∈ Cv ⟩
    bqAt k eq c ar a b c∈ e = PT.rec (snd (pr (sucV (fst ar)) (fst b) ∈ Cv))
      (λ { (t , a' , (er , (ht , ha))) →
        subst (λ u → ⟨ pr (sucV (fst ar)) u ∈ Cv ⟩) (sym (pr-inj er .snd)) ha })
      (subst (λ P → P (fst ar) (pr (fst a) (fst b))) eq (at c c∈ k (fst ar) (pr (fst a) (fst b)) e))

    hcl : (c : S) → ⟨ δ' c ⊨ closedAt zero ⟩
    hcl c =
        binSameClosed-in zero 2 (δ' c) (binAt 2 refl)
      , ( binSameClosed-in zero 3 (δ' c) (binAt 3 refl)
      , ( binSameClosed-in zero 4 (δ' c) (binAt 4 refl)
      , ( unSuccClosed-in zero 6 (δ' c) (λ c' ar a c'∈ e → at c' c'∈ 6 (fst ar) (fst a) e)
      , ( unSuccClosed-in zero 7 (δ' c) (λ c' ar a c'∈ e → at c' c'∈ 7 (fst ar) (fst a) e)
      , ( binSuccClosed-in zero 8 (δ' c) (bqAt 8 refl)
      ,   binSuccClosed-in zero 9 (δ' c) (bqAt 9 refl) )))))
```

A member's shape witness for `shapedAt`.

```agda
    wit : (c c' : S) → ⟨ fst c' ∈ Cv ⟩ → ∥ ShapeWit (sh 2 w) (δ' c) c' ∥₁
    wit c c' c'∈ = PT.rec squash₁
      (λ { (ar , F , p , (q∈ , (ec , key))) → PT.rec squash₁
        (λ { (k , r , (e' , pay)) →
          let qS = down (lookup E γ) (pr ar F) q∈
              arS = fstS qS ar F refl
              pS = sndS c' ar p ec
              rS = sndS pS (# (toℕ k)) r e'
              ek : fst c' ≡ pr (fst arS) (pr (# (toℕ k)) (fst rS))
              ek = ec ∙ cong (pr ar) e'
          in fill k c' arS rS pay ek })
        key })
      (SR.shape-out hs c' c'∈)
      where
      env4 : (c' arS b a : S) → S ^ (6 + m)
      env4 c' arS b a = b ∷ a ∷ arS ∷ c' ∷ δ' c
```

The pair witness of an atom, a connective or a bounded quantifier.

```agda
      pairWit : (k : ℕ) (rel : Formula S (4 + (2 + m))) (c' arS rS : S)
              → fst c' ≡ pr (fst arS) (pr (# k) (fst rS))
              → (t u : V ℓ) → fst rS ≡ pr t u
              → ((tS uS : S) → fst tS ≡ t → fst uS ≡ u → ⟨ env4 c' arS uS tS ⊨ rel ⟩)
              → BinWit k rel (δ' c) c'
      pairWit k rel c' arS rS ek t u er g =
        arS , (fstS rS t u er , (sndS rS t u er
        , ( ek ∙ cong (λ v → pr (fst arS) (pr (# k) v)) er
          , g (fstS rS t u er) (sndS rS t u er) refl refl )))

      both : (c' arS : S) (t u : V ℓ) → IsTmV Wv t (fst arS) → IsTmV Wv u (fst arS)
           → (tS uS : S) → fst tS ≡ t → fst uS ≡ u → ⟨ env4 c' arS uS tS ⊨ bothTm (sh 2 w) ⟩
      both c' arS t u ht hu tS uS qt qu =
          tmWit (suc zero) (suc (suc zero)) (sh 4 (sh 2 w)) (env4 c' arS uS tS)
            (subst (λ x → IsTmV Wv x (fst arS)) (sym qt) ht)
        , tmWit zero (suc (suc zero)) (sh 4 (sh 2 w)) (env4 c' arS uS tS)
            (subst (λ x → IsTmV Wv x (fst arS)) (sym qu) hu)

      first : (c' arS : S) (t u : V ℓ) → IsTmV Wv t (fst arS)
            → (tS uS : S) → fst tS ≡ t → fst uS ≡ u → ⟨ env4 c' arS uS tS ⊨ fstTm (sh 2 w) ⟩
      first c' arS t u ht tS uS qt qu =
        tmWit (suc zero) (suc (suc zero)) (sh 4 (sh 2 w)) (env4 c' arS uS tS)
          (subst (λ x → IsTmV Wv x (fst arS)) (sym qt) ht)

      fill : (k : Fin 10) (c' arS rS : S) → PayN (toℕ k) (fst arS) (fst rS)
           → fst c' ≡ pr (fst arS) (pr (# (toℕ k)) (fst rS))
           → ∥ ShapeWit (sh 2 w) (δ' c) c' ∥₁
      fill zero c' arS rS pay ek = PT.map
        (λ { (t , u , (er , (ht , hu))) → inl (pairWit 0 (bothTm (sh 2 w)) c' arS rS ek t u er (both c' arS t u ht hu)) })
        pay
      fill (suc zero) c' arS rS pay ek = PT.map
        (λ { (t , u , (er , (ht , hu))) → inr (inl (pairWit 1 (bothTm (sh 2 w)) c' arS rS ek t u er (both c' arS t u ht hu))) })
        pay
      fill (suc (suc zero)) c' arS rS pay ek = PT.map
        (λ { (a , b , (er , _)) → inr (inr (inl (pairWit 2 noneB c' arS rS ek a b er (λ _ _ _ _ b → b)))) })
        pay
      fill (suc (suc (suc zero))) c' arS rS pay ek = PT.map
        (λ { (a , b , (er , _)) → inr (inr (inr (inl (pairWit 3 noneB c' arS rS ek a b er (λ _ _ _ _ b → b))))) })
        pay
      fill (suc (suc (suc (suc zero)))) c' arS rS pay ek = PT.map
        (λ { (a , b , (er , _)) → inr (inr (inr (inr (inl (pairWit 4 noneB c' arS rS ek a b er (λ _ _ _ _ b → b)))))) })
        pay
      fill (suc (suc (suc (suc (suc zero))))) c' arS rS pay ek =
        ∣ inr (inr (inr (inr (inr (inl (arS , (rS , (ek , pay ∙ sym (numeralL-fst 0))))))))) ∣₁
      fill (suc (suc (suc (suc (suc (suc zero)))))) c' arS rS pay ek =
        ∣ inr (inr (inr (inr (inr (inr (inl (arS , (rS , (ek , (λ b → b)))))))))) ∣₁
      fill (suc (suc (suc (suc (suc (suc (suc zero))))))) c' arS rS pay ek =
        ∣ inr (inr (inr (inr (inr (inr (inr (inl (arS , (rS , (ek , (λ b → b))))))))))) ∣₁
      fill (suc (suc (suc (suc (suc (suc (suc (suc zero)))))))) c' arS rS pay ek = PT.map
        (λ { (t , a , (er , (ht , _))) → inr (inr (inr (inr (inr (inr (inr (inr (inl
          (pairWit 8 (fstTm (sh 2 w)) c' arS rS ek t a er (first c' arS t a ht)))))))))) })
        pay
      fill (suc (suc (suc (suc (suc (suc (suc (suc (suc zero))))))))) c' arS rS pay ek = PT.map
        (λ { (t , a , (er , (ht , _))) → inr (inr (inr (inr (inr (inr (inr (inr (inr
          (pairWit 9 (fstTm (sh 2 w)) c' arS rS ek t a er (first c' arS t a ht)))))))))) })
        pay

    hsh : (c : S) → ⟨ δ' c ⊨ shapedAt zero (sh 2 w) ⟩
    hsh c = shaped-in zero (sh 2 w) (δ' c) (wit c)
```

The same eight, read at `C` in `γ` rather than at the decode's frame.

```agda
  closed : ⟨ γ ⊨ closedAt C ⟩
  closed =
      binSameClosed-in C 2 γ (binAt 2 refl)
    , ( binSameClosed-in C 3 γ (binAt 3 refl)
    , ( binSameClosed-in C 4 γ (binAt 4 refl)
    , ( unSuccClosed-in C 6 γ (λ c' ar a c'∈ e → at c' c'∈ 6 (fst ar) (fst a) e)
    , ( unSuccClosed-in C 7 γ (λ c' ar a c'∈ e → at c' c'∈ 7 (fst ar) (fst a) e)
    , ( binSuccClosed-in C 8 γ (bqAt 8 refl)
    ,   binSuccClosed-in C 9 γ (bqAt 9 refl) )))))

  key-out : (c : S) → ⟨ fst c ∈ Cv ⟩
          → ∥ Σ[ k ∈ ℕ ] Σ[ ψ ∈ Formula ⟪ fst W ⟫ k ] (fst c ≡ fst (keyS W ψ)) ∥₁
  key-out c c∈ = PT.rec squash₁
    (λ { (ar , F , p , (q∈ , (ec , key))) → PT.rec squash₁
      (λ { (k , qk) → PT.map (λ { (ψ , e) → k , ψ , e })
        (witnessAt-out W (suc w) zero (c ∷ γ) qw
          ∣ CS , (c∈ , (hcl c , hsh c)) ∣₁
          k (sndS c ar p ec) (ec ∙ cong (λ a → pr a p) qk)) })
      (arity (fstS (down (lookup E γ) (pr ar F) q∈) ar F refl)
             (sndS (down (lookup E γ) (pr ar F) q∈) ar F refl) q∈) })
    (SR.shape-out hs c c∈)
```

<!--en-->
## Completeness: encoding every formula

Conversely, structural induction on a formula shows that its key belongs to the closed domain. Term codes enter through the constant set or arity numeral, and each formula constructor uses the matching closure clause after its subformulas have entered.
<!--zh-->
## 完备性：编码每条公式

反过来，对公式作结构归纳可证其键属于封闭定义域。词项码经常元集或元数数码进入，而每个公式构造子都在其子公式进入后使用对应的封闭子句。
<!--ja-->
## 完全性：各論理式の符号化

逆に、論理式の構造帰納法により、そのキーが閉じた定義域に属することを示せます。項の符号は定数集合またはアリティの数項から入り、各論理式構成子は部分論理式が入った後で対応する閉性条件を使います。
<!--/-->

`C` is complete: the key of every formula over `w` is a member, by induction on
the formula through the closure clauses.

```agda
open import L.Ordinal {ℓ} using ( ∈#-elim )
open import Cubical.Data.FinData.Properties using ( fromℕ'; toFromId' )

module CodesComplete {m : ℕ} (C w E : Fin m) (N : Fin 10 → Fin m) (γ : S ^ m) (W : S)
  (qw : fst (lookup w γ) ≡ fst W) (tg : Tags γ N)
  (arity∈ : (n : ℕ) → ⟨ pr (# n) (fst (envSet W n)) ∈ fst (lookup E γ) ⟩)
  (hc : ⟨ γ ⊨ closeAt C w E N ⟩) where
  open Alphabet W
  private
    Cv = fst (lookup C γ)

    ι∈w : (q : Ab) → ⟨ ι q ∈ fst (lookup w γ) ⟩
    ι∈w q = subst (λ u → ⟨ ι q ∈ u ⟩) (sym qw) (ι∈ q)

    ιS : Ab → S
    ιS q = down (lookup w γ) (ι q) (ι∈w q)

    qS : ℕ → S
    qS n = down (lookup E γ) (pr (# n) (fst (envSet W n))) (arity∈ n)

    δ4 : ℕ → S ^ (4 + m)
    δ4 n = envSet W n ∷ nn n ∷ container (qS n) (nn n) (envSet W n) refl .fst ∷ qS n ∷ γ

    frame : (n : ℕ) → ⟨ δ4 n ⊨ Close.all C w N ⟩
    frame n = useBoth i0 (qS n ∷ γ) (nn n) (envSet W n) refl (Close.all C w N) (hc (qS n) (arity∈ n))

    module CR (n : ℕ) = CloseRead C w N (δ4 n) tg
```

The variable index as a member of the arity numeral.

```agda
    var∈ : (n : ℕ) (i : Fin n) → ⟨ # (toℕ i) ∈ # n ⟩
    var∈ n i = #mono (toℕ i) n (toℕ<n i)

  key-in : ∀ {n} (ψ : Formula Ab n) → ⟨ fst (keyS W ψ) ∈ Cv ⟩
  key-in {n} (con x ∈̇ con y) = CR.atomClose-out n f0 f0 f0 (sh 4 w) (sh 5 w) (frame n .fst) (ιS x) (ιS y) (ι∈w x) (ι∈w y)
  key-in {n} (con x ∈̇ var j) = CR.atomClose-out n f0 f0 f1 (sh 4 w) i2 (frame n .snd .fst) (ιS x) (nn (toℕ j)) (ι∈w x) (var∈ n j)
  key-in {n} (var i ∈̇ con y) = CR.atomClose-out n f0 f1 f0 i1 (sh 5 w) (frame n .snd .snd .fst) (nn (toℕ i)) (ιS y) (var∈ n i) (ι∈w y)
  key-in {n} (var i ∈̇ var j) = CR.atomClose-out n f0 f1 f1 i1 i2 (frame n .snd .snd .snd .fst) (nn (toℕ i)) (nn (toℕ j)) (var∈ n i) (var∈ n j)
  key-in {n} (con x ≐ con y) = CR.atomClose-out n f1 f0 f0 (sh 4 w) (sh 5 w) (frame n .snd .snd .snd .snd .fst) (ιS x) (ιS y) (ι∈w x) (ι∈w y)
  key-in {n} (con x ≐ var j) = CR.atomClose-out n f1 f0 f1 (sh 4 w) i2 (frame n .snd .snd .snd .snd .snd .fst) (ιS x) (nn (toℕ j)) (ι∈w x) (var∈ n j)
  key-in {n} (var i ≐ con y) = CR.atomClose-out n f1 f1 f0 i1 (sh 5 w) (frame n .snd .snd .snd .snd .snd .snd .fst) (nn (toℕ i)) (ιS y) (var∈ n i) (ι∈w y)
  key-in {n} (var i ≐ var j) = CR.atomClose-out n f1 f1 f1 i1 i2 (frame n .snd .snd .snd .snd .snd .snd .snd .fst) (nn (toℕ i)) (nn (toℕ j)) (var∈ n i) (var∈ n j)
  key-in {n} (a ∧̇ b) = CR.binClose-out n f2 (frame n .snd .snd .snd .snd .snd .snd .snd .snd .fst) (keyS W a) (keyS W b) (codeS W a) (codeS W b) (key-in a) (key-in b) refl refl
  key-in {n} (a ∨̇ b) = CR.binClose-out n f3 (frame n .snd .snd .snd .snd .snd .snd .snd .snd .snd .fst) (keyS W a) (keyS W b) (codeS W a) (codeS W b) (key-in a) (key-in b) refl refl
  key-in {n} (a ⇒̇ b) = CR.binClose-out n f4 (frame n .snd .snd .snd .snd .snd .snd .snd .snd .snd .snd .fst) (keyS W a) (keyS W b) (codeS W a) (codeS W b) (key-in a) (key-in b) refl refl
  key-in {n} ⊥̇ = CR.conClose-out n f5 (frame n .snd .snd .snd .snd .snd .snd .snd .snd .snd .snd .snd .fst)
  key-in {n} (∃̇ a) = CR.quClose-out n f6 (frame n .snd .snd .snd .snd .snd .snd .snd .snd .snd .snd .snd .snd .fst) (keyS W a) (nn (suc n)) (codeS W a) (key-in a) refl refl
  key-in {n} (∀̇ a) = CR.quClose-out n f7 (frame n .snd .snd .snd .snd .snd .snd .snd .snd .snd .snd .snd .snd .snd .fst) (keyS W a) (nn (suc n)) (codeS W a) (key-in a) refl refl
  key-in {n} (∀̇∈ (con x) a) =
    CR.bqClose-out n f8 f0 (sh 8 w) (frame n .snd .snd .snd .snd .snd .snd .snd .snd .snd .snd .snd .snd .snd .snd .fst) (keyS W a) (nn (suc n)) (codeS W a) (key-in a) refl refl (ιS x) (ι∈w x)
  key-in {n} (∀̇∈ (var i) a) =
    CR.bqClose-out n f8 f1 i5 (frame n .snd .snd .snd .snd .snd .snd .snd .snd .snd .snd .snd .snd .snd .snd .snd .fst) (keyS W a) (nn (suc n)) (codeS W a) (key-in a) refl refl (nn (toℕ i)) (var∈ n i)
  key-in {n} (∃̇∈ (con x) a) =
    CR.bqClose-out n f9 f0 (sh 8 w) (frame n .snd .snd .snd .snd .snd .snd .snd .snd .snd .snd .snd .snd .snd .snd .snd .snd .fst) (keyS W a) (nn (suc n)) (codeS W a) (key-in a) refl refl (ιS x) (ι∈w x)
  key-in {n} (∃̇∈ (var i) a) =
    CR.bqClose-out n f9 f1 i5 (frame n .snd .snd .snd .snd .snd .snd .snd .snd .snd .snd .snd .snd .snd .snd .snd .snd .snd ) (keyS W a) (nn (suc n)) (codeS W a) (key-in a) refl refl (nn (toℕ i)) (var∈ n i)
```

<!--en-->
## The canonical closed code domain

Instantiating the description with `AllCodes w`{.Agda} gives both directions at once: every member decodes at its stated arity, and the key of every formula over `w` belongs to the domain. The final term lemmas identify constants and variables at their respective bounds.
<!--zh-->
## 典范的封闭码定义域

以 `AllCodes w`{.Agda} 实例化该描述便同时得到两个方向：每个成员都在其声明元数上解码，而 `w` 上每条公式的键都属于该定义域。最后的词项引理在各自的界中识别常元与变量。
<!--ja-->
## 正準な閉じた符号の定義域

記述を `AllCodes w`{.Agda} で具体化すると、二つの方向が同時に得られます。各要素は指定されたアリティで復号でき、`w` 上の各論理式のキーは定義域に属します。最後の項の補題は、定数と変数をそれぞれの境界の中で同定します。
<!--/-->

The code set satisfies the description, at `C = AllCodes w` and `E` the tower.
Shape: every member is decoded to its formula. Closure: the key of the formula
the parts decode to is a member.

```agda
module CodesHolds {m : ℕ} (C w E : Fin m) (N : Fin 10 → Fin m) (γ : S ^ m) (W : S)
  (qw : fst (lookup w γ) ≡ fst W) (qC : fst (lookup C γ) ≡ fst (AllCodes W))
  (qE : fst (lookup E γ) ≡ fst (Tower.tower W)) (tg : Tags γ N) where
  open Alphabet W
  private
    Cv = fst (lookup C γ)
    Wv = fst (lookup w γ)
    Ev = fst (lookup E γ)
    open CodesSem Wv Cv

    tmV : ∀ {n} (Wv′ : V ℓ) → ((q : Ab) → ⟨ ι q ∈ Wv′ ⟩) → (t : Term Ab n) → IsTmV Wv′ (ct t) (# n)
    tmV Wv′ into (con q) = ∣ inl (ι q , (refl , into q)) ∣₁
    tmV {n} Wv′ into (var i) = ∣ inr (# (toℕ i) , (refl , #mono (toℕ i) n (toℕ<n i))) ∣₁

    ι∈w : (q : Ab) → ⟨ ι q ∈ Wv ⟩
    ι∈w q = subst (λ u → ⟨ ι q ∈ u ⟩) (sym qw) (ι∈ q)

    mem : ∀ {n} (ψ : Formula Ab n) → ⟨ fst (keyS W ψ) ∈ Cv ⟩
    mem ψ = subst (λ u → ⟨ fst (keyS W ψ) ∈ u ⟩) (sym qC) (key∈AllCodes W ψ)

    entry∈ : (n : ℕ) → ⟨ pr (# n) (fst (envSet W n)) ∈ Ev ⟩
    entry∈ n = subst (λ u → ⟨ pr (# n) (fst (envSet W n)) ∈ u ⟩) (sym qE) (Tower.tower-in′ W n)

    tm : ∀ {n} (t : Term Ab n) → IsTmV Wv (ct t) (# n)
    tm = tmV Wv ι∈w
```

The key of every formula, as the description sees it.

```agda
    keyOf : ∀ {n} (ψ : Formula Ab n) → Key (# n) (cd ψ)
    keyOf (t ∈̇ u) = ∣ f0 , pr (ct t) (ct u) , (refl , ∣ ct t , ct u , (refl , (tm t , tm u)) ∣₁) ∣₁
    keyOf (t ≐ u) = ∣ f1 , pr (ct t) (ct u) , (refl , ∣ ct t , ct u , (refl , (tm t , tm u)) ∣₁) ∣₁
    keyOf (a ∧̇ b) = ∣ f2 , pr (cd a) (cd b) , (refl , ∣ cd a , cd b , (refl , (mem a , mem b)) ∣₁) ∣₁
    keyOf (a ∨̇ b) = ∣ f3 , pr (cd a) (cd b) , (refl , ∣ cd a , cd b , (refl , (mem a , mem b)) ∣₁) ∣₁
    keyOf (a ⇒̇ b) = ∣ f4 , pr (cd a) (cd b) , (refl , ∣ cd a , cd b , (refl , (mem a , mem b)) ∣₁) ∣₁
    keyOf ⊥̇ = ∣ f5 , # 0 , (refl , refl) ∣₁
    keyOf (∃̇ a) = ∣ f6 , cd a , (refl , mem a) ∣₁
    keyOf (∀̇ a) = ∣ f7 , cd a , (refl , mem a) ∣₁
    keyOf (∀̇∈ t a) = ∣ f8 , pr (ct t) (cd a) , (refl , ∣ ct t , cd a , (refl , (tm t , mem a)) ∣₁) ∣₁
    keyOf (∃̇∈ t a) = ∣ f9 , pr (ct t) (cd a) , (refl , ∣ ct t , cd a , (refl , (tm t , mem a)) ∣₁) ∣₁

    shape : ⟨ γ ⊨ shapeAt C w E N ⟩
    shape = ShapeRead.shape-in C w E N γ tg (λ c c∈ → PT.map
      (λ { (n , ψ , e) → # n , fst (envSet W n) , cd ψ , (entry∈ n , (e , keyOf ψ)) })
      (AllCodes-out W c (subst (λ u → ⟨ fst c ∈ u ⟩) qC c∈)))
```

A member handed over as a key at a stated arity decodes to a formula at that
arity.

```agda
    decodeAt : (c : S) → ⟨ fst c ∈ Cv ⟩ → (n : ℕ) (z : V ℓ) → fst c ≡ pr (# n) z
             → ∥ Σ[ ψ ∈ Formula Ab n ] (z ≡ cd ψ) ∥₁
    decodeAt c c∈ n z e = PT.map
      (λ { (n₁ , ψ₁ , e₁) →
        let q = pr-inj (sym e₁ ∙ e)
            nq = #-inj′ (q .fst)
        in subst (Formula Ab) nq ψ₁ , (sym (q .snd) ∙ sym (cd-subst nq ψ₁)) })
      (AllCodes-out W c (subst (λ u → ⟨ fst c ∈ u ⟩) qC c∈))
```

The term decoders: a member of `w` is a constant's code, a member of the arity
is a variable's.

```agda
    TmDec : ∀ {n} → Fin 10 → V ℓ → Type (ℓ-suc ℓ)
    TmDec {n} Nx bound = (x : V ℓ) → ⟨ x ∈ bound ⟩ → ∥ Σ[ t ∈ Term Ab n ] (ct t ≡ pr (# (toℕ Nx)) x) ∥₁

    conDec : ∀ {n} → TmDec {n} f0 Wv
    conDec x x∈ = ∣ con (fib .fst) , cong (pr (# 0)) (fib .snd) ∣₁
      where
      fib : Σ[ q ∈ Ab ] (ι q ≡ x)
      fib = ∈-asFiber {a = x} {b = fst W} (subst (λ u → ⟨ x ∈ u ⟩) qw x∈)

    varDec : (n : ℕ) (A : V ℓ) → A ≡ # n → TmDec {n} f1 A
    varDec n A qa x x∈ = PT.map
      (λ { (j , (p , ex)) → var (fromℕ' n j p) , cong (pr (# 1)) (cong #_ (toFromId' n j p) ∙ sym ex) })
      (∈#-elim n x (subst (λ u → ⟨ x ∈ u ⟩) qa x∈))
```

The closure clauses at an entry `(ar, F)` of the tower, `ar = # n`.

```agda
    module At (q : S) (q∈ : ⟨ fst q ∈ Ev ⟩) (ar F s : S) (n : ℕ) (qa : fst ar ≡ # n) where
      private
        δ4 : S ^ (4 + m)
        δ4 = F ∷ ar ∷ s ∷ q ∷ γ
        A = fst ar
        module CR = CloseRead C w N δ4 tg
        module Cl = Close C w N

        in-key : ∀ {k} (ψ : Formula Ab k) (x : V ℓ) → x ≡ fst (keyS W ψ) → ⟨ x ∈ Cv ⟩
        in-key ψ x e = subst (λ u → ⟨ u ∈ Cv ⟩) (sym e) (mem ψ)
```

Every truncated payload is named before `PT.rec` sees it (the law of
src/L/Coding/CodeSet.lagda.md, met again).

```agda
        TmAt : (Nx : Fin 10) (x : V ℓ) → Type (ℓ-suc ℓ)
        TmAt Nx x = Σ[ t ∈ Term Ab n ] (ct t ≡ pr (# (toℕ Nx)) x)

        FoAt : (k : ℕ) (z : V ℓ) → Type (ℓ-suc ℓ)
        FoAt k z = Σ[ ψ ∈ Formula Ab k ] (z ≡ cd ψ)

        atomIn : (k Nx Ny : Fin 10) (X : Fin (4 + m)) (Y : Fin (5 + m))
               → (op : Term Ab n → Term Ab n → Formula Ab n)
               → ((t u : Term Ab n) → cd (op t u) ≡ pr (# (toℕ k)) (pr (ct t) (ct u)))
               → TmDec Nx (fst (lookup X δ4)) → ((x : S) → TmDec Ny (fst (lookup Y (x ∷ δ4))))
               → ⟨ δ4 ⊨ Cl.atomClose k Nx Ny X Y ⟩
        atomIn k Nx Ny X Y op code dx dy = CR.atomClose-in k Nx Ny X Y (λ x y x∈ y∈ →
          let d1 : ∥ TmAt Nx (fst x) ∥₁
              d1 = dx (fst x) x∈
              d2 : ∥ TmAt Ny (fst y) ∥₁
              d2 = dy x (fst y) y∈
              G : V ℓ
              G = pr A (pr (# (toℕ k)) (pr (pr (# (toℕ Nx)) (fst x)) (pr (# (toℕ Ny)) (fst y))))
          in PT.rec (snd (G ∈ Cv))
            (λ { (t , et) → PT.rec (snd (G ∈ Cv))
              (λ { (u , eu) → in-key (op t u) G
                (cong₂ pr qa (cong (pr (# (toℕ k))) (cong₂ pr (sym et) (sym eu)) ∙ sym (code t u))) })
              d2 })
            d1)

        binIn : (k : Fin 10) (op : Formula Ab n → Formula Ab n → Formula Ab n)
              → ((a b : Formula Ab n) → cd (op a b) ≡ pr (# (toℕ k)) (pr (cd a) (cd b)))
              → ⟨ δ4 ⊨ Cl.binClose k ⟩
        binIn k op code = CR.binClose-in k (λ c₁ c₂ a b c₁∈ c₂∈ e₁ e₂ →
          let d1 : ∥ FoAt n (fst a) ∥₁
              d1 = decodeAt c₁ c₁∈ n (fst a) (e₁ ∙ cong (λ v → pr v (fst a)) qa)
              d2 : ∥ FoAt n (fst b) ∥₁
              d2 = decodeAt c₂ c₂∈ n (fst b) (e₂ ∙ cong (λ v → pr v (fst b)) qa)
              G : V ℓ
              G = pr A (pr (# (toℕ k)) (pr (fst a) (fst b)))
          in PT.rec (snd (G ∈ Cv))
            (λ { (ψ₁ , ea) → PT.rec (snd (G ∈ Cv))
              (λ { (ψ₂ , eb) → in-key (op ψ₁ ψ₂) G
                (cong₂ pr qa (cong (pr (# (toℕ k))) (cong₂ pr ea eb) ∙ sym (code ψ₁ ψ₂))) })
              d2 })
            d1)

        conIn : (k : Fin 10) (c₀ : Formula Ab n) → cd c₀ ≡ pr (# (toℕ k)) (# 0) → ⟨ δ4 ⊨ Cl.conClose k ⟩
        conIn k c₀ code = CR.conClose-in k (in-key c₀ (pr A (pr (# (toℕ k)) (# 0))) (cong₂ pr qa (sym code)))

        quIn : (k : Fin 10) (op : Formula Ab (suc n) → Formula Ab n)
             → ((a : Formula Ab (suc n)) → cd (op a) ≡ pr (# (toℕ k)) (cd a))
             → ⟨ δ4 ⊨ Cl.quClose k ⟩
        quIn k op code = CR.quClose-in k (λ c₁ ar' a c₁∈ e₁ es →
          let d1 : ∥ FoAt (suc n) (fst a) ∥₁
              d1 = decodeAt c₁ c₁∈ (suc n) (fst a) (e₁ ∙ cong (λ v → pr v (fst a)) (es ∙ cong sucV qa))
              G : V ℓ
              G = pr A (pr (# (toℕ k)) (fst a))
          in PT.rec (snd (G ∈ Cv))
            (λ { (ψ₁ , ea) → in-key (op ψ₁) G (cong₂ pr qa (cong (pr (# (toℕ k))) ea ∙ sym (code ψ₁))) })
            d1)

        bqIn : (k Nx : Fin 10) (X : Fin (8 + m))
             → (op : Term Ab n → Formula Ab (suc n) → Formula Ab n)
             → ((t : Term Ab n) (a : Formula Ab (suc n)) → cd (op t a) ≡ pr (# (toℕ k)) (pr (ct t) (cd a)))
             → ((ar' a s' c₁ : S) → TmDec Nx (fst (lookup X (a ∷ ar' ∷ s' ∷ c₁ ∷ δ4))))
             → ⟨ δ4 ⊨ Cl.bqClose k Nx X ⟩
        bqIn k Nx X op code dx = CR.bqClose-in k Nx X (λ c₁ ar' a s' c₁∈ e₁ es x x∈ →
          let d1 : ∥ TmAt Nx (fst x) ∥₁
              d1 = dx ar' a s' c₁ (fst x) x∈
              d2 : ∥ FoAt (suc n) (fst a) ∥₁
              d2 = decodeAt c₁ c₁∈ (suc n) (fst a) (e₁ ∙ cong (λ v → pr v (fst a)) (es ∙ cong sucV qa))
              G : V ℓ
              G = pr A (pr (# (toℕ k)) (pr (pr (# (toℕ Nx)) (fst x)) (fst a)))
          in PT.rec (snd (G ∈ Cv))
            (λ { (t , et) → PT.rec (snd (G ∈ Cv))
              (λ { (ψ₁ , ea) → in-key (op t ψ₁) G
                (cong₂ pr qa (cong (pr (# (toℕ k))) (cong₂ pr (sym et) ea) ∙ sym (code t ψ₁))) })
              d2 })
            d1)

      all : ⟨ δ4 ⊨ Cl.all ⟩
      all =
          atomIn f0 f0 f0 (sh 4 w) (sh 5 w) _∈̇_ (λ _ _ → refl) conDec (λ _ → conDec)
        , ( atomIn f0 f0 f1 (sh 4 w) i2 _∈̇_ (λ _ _ → refl) conDec (λ _ → varDec n A qa)
        , ( atomIn f0 f1 f0 i1 (sh 5 w) _∈̇_ (λ _ _ → refl) (varDec n A qa) (λ _ → conDec)
        , ( atomIn f0 f1 f1 i1 i2 _∈̇_ (λ _ _ → refl) (varDec n A qa) (λ _ → varDec n A qa)
        , ( atomIn f1 f0 f0 (sh 4 w) (sh 5 w) _≐_ (λ _ _ → refl) conDec (λ _ → conDec)
        , ( atomIn f1 f0 f1 (sh 4 w) i2 _≐_ (λ _ _ → refl) conDec (λ _ → varDec n A qa)
        , ( atomIn f1 f1 f0 i1 (sh 5 w) _≐_ (λ _ _ → refl) (varDec n A qa) (λ _ → conDec)
        , ( atomIn f1 f1 f1 i1 i2 _≐_ (λ _ _ → refl) (varDec n A qa) (λ _ → varDec n A qa)
        , ( binIn f2 _∧̇_ (λ _ _ → refl)
        , ( binIn f3 _∨̇_ (λ _ _ → refl)
        , ( binIn f4 _⇒̇_ (λ _ _ → refl)
        , ( conIn f5 ⊥̇ refl
        , ( quIn f6 ∃̇_ (λ _ → refl)
        , ( quIn f7 ∀̇_ (λ _ → refl)
        , ( bqIn f8 f0 (sh 8 w) ∀̇∈ (λ _ _ → refl) (λ _ _ _ _ → conDec)
        , ( bqIn f8 f1 i5 ∀̇∈ (λ _ _ → refl) (λ _ _ _ _ → varDec n A qa)
        , ( bqIn f9 f0 (sh 8 w) ∃̇∈ (λ _ _ → refl) (λ _ _ _ _ → conDec)
        ,   bqIn f9 f1 i5 ∃̇∈ (λ _ _ → refl) (λ _ _ _ _ → varDec n A qa) ))))))))))))))))

    close : ⟨ γ ⊨ closeAt C w E N ⟩
    close q q∈ = bothAll-in i0 (Close.all C w N) (q ∷ γ) (λ ar F s s∈ ar∈ F∈ e →
      PT.rec (snd ((F ∷ ar ∷ s ∷ q ∷ γ) ⊨ Close.all C w N))
        (λ { (n , qp) → At.all q q∈ ar F s n (pr-inj (sym e ∙ qp) .fst) })
        (Tower.tower-out W q (subst (λ u → ⟨ fst q ∈ u ⟩) qE q∈)))

  holds : ⟨ γ ⊨ codesAt C w E N ⟩
  holds = shape , close
```

<!--en-->
## Recap

The readers expose the mathematical content of `codesAt`: soundness decodes every member of a satisfying domain, completeness inserts every formula key, and `AllCodes` supplies the canonical constructible domain satisfying both requirements at every arity.
<!--zh-->
## 小结

这些读式揭示 `codesAt` 的数学内容：可靠性解码满足该谓词的定义域中每个成员，完备性加入每条公式的键，而 `AllCodes` 给出在每个元数上同时满足两项要求的典范可构造定义域。
<!--ja-->
## まとめ

読み補題は `codesAt` の数学的内容を明らかにする。健全性は条件を満たす定義域の各要素を復号し、完全性は各論理式のキーを入れ、`AllCodes` はすべてのアリティで両方を満たす正準な構成可能な定義域を与える。
<!--/-->
