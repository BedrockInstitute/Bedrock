<!--en-->
# Reading and validating the satisfaction clauses

Why does a table satisfying ten local clauses give the correct interpretation of
terms and formulas in each environment? This chapter reads those conditions one
constructor at a time and connects the judgments recorded by the internal table
with the external satisfaction relation.
<!--zh-->
# 读取并验证满足关系子句

为什么一张满足十条局部子句的表会给出词项与公式在每个环境中的正确解释？本章逐个构造子读取这些条件，并把内部表所记录的判断与外部满足关系连接起来。
<!--ja-->
# 充足関係の節の読み取りと検証

十個の局所的な節を満たす表が、なぜ各環境における項と論理式の正しい解釈を与えるのでしょうか。本章では条件を構成子ごとに読み取り、内部の表が記録する判断を外部の充足関係へ結び付けます。
<!--/-->

```agda
{-# OPTIONS --cubical --safe --guardedness #-}

open import Base.Prelude
open import Base.Truth
open import Base.Classical using ( LEM )

module L.Coding.SatisfactionClauseSemantics {ℓ : Level} (lem : LEM (ℓ-suc ℓ)) where

open import FOL.ZFStructure using ( module hPropStructure )
open import FOL.Syntax using
  ( Formula; Term; var; con; _∈̇_; _∧̇_; _∨̇_; _⇒̇_; ⊤̇; ⊥̇; ∃̇_; ∀̇_; ∃̇∈; ∀̇∈ )
import FOL.Absoluteness
open import V.Hierarchy {ℓ} using ( 𝒮ᵥ )
open import V.Coding {ℓ} using ( pr; pr-inj; #-inj′ )
open import L.Constructible {ℓ} using ( 𝒮ʟ; isL; isL-trans )
open import L.Coding.Environment {ℓ} using ( env; lookup-spec )
open import L.Coding.EnvironmentSet {ℓ} lem using ( envSet )
open import L.Coding.Model {ℓ} using ( prAtL; container )
open import L.Coding.Expressions {ℓ} using ( sucAtL; consAtL )
import L.Coding.Expressions {ℓ} as CodingExpressions
module E = CodingExpressions.PairExpression
open import L.Axioms.Basic {ℓ} using ( extensionalL )
open import L.Coding.Quantification {ℓ} using
  ( i0; i1; i2; i3; i4; i5; i6; i8; i9; i11; i12; i14; i16; i17; i19; sh
  ; pr-out; pr-in; down; sndS; suc-out; suc-in
  ; sndEx; sndAll; bothEx
  ; sndEx-out; sndAll-in; bothEx-out; bothAll-in
  ; fillSnd; fillBoth; useSnd; useBoth )
open import L.Coding.CodeDomain {ℓ} using ( Tags )
open import L.Coding.CodeAlphabet {ℓ} using ( module Alphabet )
open import L.Coding.SatisfactionClauses {ℓ}
  using ( extB; fstAll; subAt; subSucAt; tmIs; module Rel; module Clause )

open import Cubical.Data.Nat using ( _+_ )
open import Cubical.Data.FinData using ( toℕ )
open import Cubical.Data.Vec using ( _∷_; []; lookup )
open import Cubical.Data.Sigma using ( _×_ )
open import Cubical.Data.Sum using ( _⊎_; inl; inr )
open import Cubical.Foundations.Prelude using ( subst2 )
open import Cubical.Functions.Logic using ( ⇔toPath )
import Cubical.Data.Empty as Empty
import Cubical.HITs.PropositionalTruncation as PT
open PT using ( ∥_∥₁; ∣_∣₁; squash₁ )
open import Cubical.HITs.CumulativeHierarchy.Base using ( V; _∈_; setIsSet )
open import Cubical.HITs.CumulativeHierarchy.Constructions using ( module InfinitySet )
open InfinitySet {ℓ} using ( #_; sucV )

open hPropStructure 𝒮ʟ using ( S )
module AbsL = FOL.Absoluteness.Single 𝒮ᵥ isL isL-trans using ( _^_; _⊨ᵐ_ )
open AbsL using ( _^_ ) renaming ( _⊨ᵐ_ to _⊨_ )
```

<!--en-->
## Reading the shared frame
<!--zh-->
## 读取共同框架
<!--ja-->
## 共通の枠組みを読む
<!--/-->

<!--en-->
The readers beginning with `extB-out` recover an extension from a clause body,
read subformula values and term values from table entries, and expose the coded
frame through `clause-out`, `total-out`, and `onC-out` together with converse
constructors.
<!--zh-->
从 `extB-out` 开始的读式由子句主体恢复外延，读取表条目中的子公式值与词项值，并借助 `clause-out`、`total-out`、`onC-out` 及其逆向构造子，揭示被码化的框架。
<!--ja-->
`extB-out` から始まる読み補題は、節の本体から外延を復元し、表の要素から部分論理式の値と項の値を読み出す。さらに `clause-out`、`total-out`、`onC-out` と逆向きの構成によって、符号化された枠組みを取り出す。
<!--/-->

The table, read. The frame and the subvalue macros are read at variable
environments; each relation is read to an extension fact whose condition is the
relation's own body at the frame the reader makes.

`y` is exactly the members of `F` with the property `P`.

```agda
ExtFact : (y F : V ℓ) (P : S → Type (ℓ-suc ℓ)) → Type (ℓ-suc ℓ)
ExtFact y F P = ((z : S) → ⟨ fst z ∈ y ⟩ → ⟨ fst z ∈ F ⟩ × P z)
              × ((z : S) → ⟨ fst z ∈ F ⟩ → P z → ⟨ fst z ∈ y ⟩)

module _ {j : ℕ} (y F : Fin j) (φ : Formula S (1 + j)) (δ : S ^ j) where
  extB-out : ⟨ δ ⊨ extB y F φ ⟩ → ExtFact (fst (lookup y δ)) (fst (lookup F δ)) (λ z → ⟨ (z ∷ δ) ⊨ φ ⟩)
  extB-out h = h

  extB-in : ExtFact (fst (lookup y δ)) (fst (lookup F δ)) (λ z → ⟨ (z ∷ δ) ⊨ φ ⟩) → ⟨ δ ⊨ extB y F φ ⟩
  extB-in h = h
```

Two extension facts with the same condition name the same set.

```agda
ext-unique : (y y' F : S) (P : S → Type (ℓ-suc ℓ))
           → ExtFact (fst y) (fst F) P → ExtFact (fst y') (fst F) P → fst y ≡ fst y'
ext-unique y y' F P (o1 , i1') (o2 , i2') =
  cong fst (extensionalL {a = y} {b = y'} (λ z → ⇔toPath
    (λ hz → i2' z (o1 z hz .fst) (o1 z hz .snd))
    (λ hz → i1' z (o2 z hz .fst) (o2 z hz .snd))))
```

The subvalue macros, read.

```agda
module _ {j : ℕ} (T ar a : Fin j) (body : Formula S (4 + j)) (δ : S ^ j) where
  private
    Tv = fst (lookup T δ)
    TS = lookup T δ
    A = fst (lookup ar δ)
    Av = fst (lookup a δ)

  subAt-out : ⟨ δ ⊨ subAt T ar a body ⟩ → (c₁ ya : S) (m : ⟨ pr (fst c₁) (fst ya) ∈ Tv ⟩)
            → fst c₁ ≡ pr A Av
            → ⟨ (ya ∷ c₁ ∷ container (down TS (pr (fst c₁) (fst ya)) m) c₁ ya refl .fst
                 ∷ down TS (pr (fst c₁) (fst ya)) m ∷ δ) ⊨ body ⟩
  subAt-out h c₁ ya m e =
    useBoth i0 (down TS (pr (fst c₁) (fst ya)) m ∷ δ) c₁ ya refl (prAtL i1 (sh 4 ar) (sh 4 a) ⇒̇ body)
      (h (down TS (pr (fst c₁) (fst ya)) m) m)
      (pr-in i1 (sh 4 ar) (sh 4 a)
        (ya ∷ c₁ ∷ container (down TS (pr (fst c₁) (fst ya)) m) c₁ ya refl .fst
           ∷ down TS (pr (fst c₁) (fst ya)) m ∷ δ) e)

  subAt-in : ((c₁ ya s e' : S) → ⟨ fst e' ∈ Tv ⟩ → fst e' ≡ pr (fst c₁) (fst ya) → fst c₁ ≡ pr A Av
              → ⟨ (ya ∷ c₁ ∷ s ∷ e' ∷ δ) ⊨ body ⟩)
           → ⟨ δ ⊨ subAt T ar a body ⟩
  subAt-in g e' e'∈ = bothAll-in i0 (prAtL i1 (sh 4 ar) (sh 4 a) ⇒̇ body) (e' ∷ δ)
    (λ c₁ ya s s∈ c₁∈ ya∈ e hp → g c₁ ya s e' e'∈ e (pr-out i1 (sh 4 ar) (sh 4 a) (ya ∷ c₁ ∷ s ∷ e' ∷ δ) hp))

module _ {j : ℕ} (T ar a : Fin j) (body : Formula S (6 + j)) (δ : S ^ j) where
  private
    Tv = fst (lookup T δ)
    TS = lookup T δ
    A = fst (lookup ar δ)
    Av = fst (lookup a δ)

  subSucAt-out : ⟨ δ ⊨ subSucAt T ar a body ⟩ → (c₁ ya ar' : S) (m : ⟨ pr (fst c₁) (fst ya) ∈ Tv ⟩)
               → (e : fst c₁ ≡ pr (fst ar') Av) → fst ar' ≡ sucV A
               → ⟨ (ar' ∷ container c₁ ar' (lookup a δ) e .fst ∷ ya ∷ c₁
                    ∷ container (down TS (pr (fst c₁) (fst ya)) m) c₁ ya refl .fst
                    ∷ down TS (pr (fst c₁) (fst ya)) m ∷ δ) ⊨ body ⟩
  subSucAt-out h c₁ ya ar' m e es =
    (h4 (container c₁ ar' (lookup a δ) e .fst) (container c₁ ar' (lookup a δ) e .snd .fst)
        ar' (container c₁ ar' (lookup a δ) e .snd .snd .fst)
        (pr-in (sh 2 i1) i0 (sh 2 (sh 4 a)) δ6 e))
      (suc-in (sh 6 ar) i0 δ6 es)
    where
    e'S = down TS (pr (fst c₁) (fst ya)) m
    δ4 : S ^ (4 + j)
    δ4 = ya ∷ c₁ ∷ container e'S c₁ ya refl .fst ∷ e'S ∷ δ
    δ6 : S ^ (6 + j)
    δ6 = ar' ∷ container c₁ ar' (lookup a δ) e .fst ∷ δ4
    h4 : ⟨ δ4 ⊨ fstAll i1 (sh 4 a) (sucAtL (sh 6 ar) i0 ⇒̇ body) ⟩
    h4 = useBoth i0 (e'S ∷ δ) c₁ ya refl (fstAll i1 (sh 4 a) (sucAtL (sh 6 ar) i0 ⇒̇ body)) (h e'S m)

  subSucAt-in : ((c₁ ya ar' s s' e' : S) → ⟨ fst e' ∈ Tv ⟩ → fst e' ≡ pr (fst c₁) (fst ya)
                 → fst c₁ ≡ pr (fst ar') Av → fst ar' ≡ sucV A
                 → ⟨ (ar' ∷ s' ∷ ya ∷ c₁ ∷ s ∷ e' ∷ δ) ⊨ body ⟩)
              → ⟨ δ ⊨ subSucAt T ar a body ⟩
  subSucAt-in g e' e'∈ = bothAll-in i0 (fstAll i1 (sh 4 a) (sucAtL (sh 6 ar) i0 ⇒̇ body)) (e' ∷ δ)
    (λ c₁ ya s s∈ c₁∈ ya∈ e s' s'∈ ar' ar'∈ hp hs →
      g c₁ ya ar' s s' e' e'∈ e
        (pr-out (sh 2 i1) i0 (sh 2 (sh 4 a)) (ar' ∷ s' ∷ ya ∷ c₁ ∷ s ∷ e' ∷ δ) hp)
        (suc-out (sh 6 ar) i0 (ar' ∷ s' ∷ ya ∷ c₁ ∷ s ∷ e' ∷ δ) hs))
```

The term value, read.

```agda
TmIsV : V ℓ → V ℓ → V ℓ → Type (ℓ-suc ℓ)
TmIsV t z v = ∥ (t ≡ pr (# 0) v) ⊎ (Σ[ i ∈ V ℓ ] ((t ≡ pr (# 1) i) × ⟨ pr i v ∈ z ⟩)) ∥₁

module _ {j : ℕ} (t z v N0 N1 : Fin j) (δ : S ^ j)
  (q0 : fst (lookup N0 δ) ≡ # 0) (q1 : fst (lookup N1 δ) ≡ # 1) where
  private
    Tv = fst (lookup t δ)
    Z = fst (lookup z δ)
    Vv = fst (lookup v δ)
    N1v = fst (lookup N1 δ)

    inner : Formula S (2 + j)
    inner = ∃̇∈ (var (sh 2 z)) (prAtL i0 i1 (sh 3 v))

    Inner : (i s : S) → Type (ℓ-suc ℓ)
    Inner i s = ∥ Σ[ q ∈ S ] (⟨ fst q ∈ Z ⟩ × ⟨ (q ∷ i ∷ s ∷ δ) ⊨ prAtL i0 i1 (sh 3 v) ⟩) ∥₁

    Outer : Type (ℓ-suc ℓ)
    Outer = ∥ Σ[ i ∈ S ] Σ[ s ∈ S ] ((Tv ≡ pr N1v (fst i)) × ⟨ (i ∷ s ∷ δ) ⊨ inner ⟩) ∥₁

    viaQ : (i s : S) → Tv ≡ pr N1v (fst i) → Inner i s → TmIsV Tv Z Vv
    viaQ i s e = PT.map
      (λ { (q , (q∈ , hp)) → inr (fst i , ( e ∙ cong (λ a → pr a (fst i)) q1
         , subst (λ u → ⟨ u ∈ Z ⟩) (pr-out i0 i1 (sh 3 v) (q ∷ i ∷ s ∷ δ) hp) q∈ )) })

    viaI : Outer → TmIsV Tv Z Vv
    viaI = PT.rec squash₁ (λ { (i , s , (e , hq)) → viaQ i s e hq })

    cases : ⟨ δ ⊨ prAtL t N0 v ⟩ ⊎ ⟨ δ ⊨ sndEx t N1 inner ⟩ → TmIsV Tv Z Vv
    cases (inl h) = ∣ inl (pr-out t N0 v δ h ∙ cong (λ a → pr a Vv) q0) ∣₁
    cases (inr h) = viaI (sndEx-out t N1 inner δ h)

  tmIs-out : ⟨ δ ⊨ tmIs t z v N0 N1 ⟩ → TmIsV Tv Z Vv
  tmIs-out h = PT.rec squash₁ cases h

  private
    build : (Tv ≡ pr (# 0) Vv) ⊎ (Σ[ i ∈ V ℓ ] ((Tv ≡ pr (# 1) i) × ⟨ pr i Vv ∈ Z ⟩))
          → ⟨ δ ⊨ tmIs t z v N0 N1 ⟩
    build (inl e) = ∣ inl (pr-in t N0 v δ (e ∙ cong (λ a → pr a Vv) (sym q0))) ∣₁
    build (inr (i , (e , hp))) = ∣ inr (fillSnd t δ (lookup N1 δ) iS e' inner hq N1 refl) ∣₁
      where
      iS : S
      iS = sndS (lookup t δ) (# 1) i e
      qS : S
      qS = down (lookup z δ) (pr i Vv) hp
      e' : Tv ≡ pr N1v (fst iS)
      e' = e ∙ cong (λ a → pr a i) (sym q1)
      δ3 : S ^ (3 + j)
      δ3 = qS ∷ iS ∷ container (lookup t δ) (lookup N1 δ) iS e' .fst ∷ δ
      hq : ⟨ (iS ∷ container (lookup t δ) (lookup N1 δ) iS e' .fst ∷ δ) ⊨ inner ⟩
      hq = ∣ qS , (hp , pr-in i0 i1 (sh 3 v) δ3 refl) ∣₁

  tmIs-in : TmIsV Tv Z Vv → ⟨ δ ⊨ tmIs t z v N0 N1 ⟩
  tmIs-in = PT.rec (snd (δ ⊨ tmIs t z v N0 N1)) build
```

The frame, read. The ten-slot frame at the data of an entry.

```agda
module Frame {m : ℕ} (T w C E : Fin m) (N : Fin 10 → Fin m) (γ : S ^ m) (tg : Tags γ N) where
  private
    Tv = fst (lookup T γ)
    Cv = fst (lookup C γ)
    Ev = fst (lookup E γ)
    module Cl = Clause T w C E N
    module R = Rel T w N
    inner9 : Fin 10 → Formula S (9 + m)
    inner9 k = ∀̇∈ (var (sh 9 T)) (sndAll i0 i5 (R.relN (toℕ k)))
    inner7 : Fin 10 → Formula S (7 + m)
    inner7 k = sndAll i0 (sh 7 (N k)) (inner9 k)
    inner4 : Fin 10 → Formula S (4 + m)
    inner4 k = ∀̇∈ (var (sh 4 C)) (sndAll i0 i2 (inner7 k))
```

The frame environment of an entry, with its containers.

```agda
  module At (ar F c p r yc : S) (q∈ : ⟨ pr (fst ar) (fst F) ∈ Ev ⟩)
            (ec : fst c ≡ pr (fst ar) (fst p)) (k : Fin 10)
            (ep : fst p ≡ pr (fst (lookup (N k) γ)) (fst r))
            (e∈ : ⟨ pr (fst c) (fst yc) ∈ Tv ⟩) where
    qS eS : S
    qS = down (lookup E γ) (pr (fst ar) (fst F)) q∈
    eS = down (lookup T γ) (pr (fst c) (fst yc)) e∈

    δ4 : S ^ (4 + m)
    δ4 = F ∷ ar ∷ container qS ar F refl .fst ∷ qS ∷ γ
    δ7 : S ^ (7 + m)
    δ7 = p ∷ container c ar p ec .fst ∷ c ∷ δ4
    δ9 : S ^ (9 + m)
    δ9 = r ∷ container p (lookup (N k) γ) r ep .fst ∷ δ7
    δ12 : S ^ (12 + m)
    δ12 = yc ∷ container eS c yc refl .fst ∷ eS ∷ δ9

  clause-out : (k : Fin 10) → ⟨ γ ⊨ Cl.clause k ⟩
             → (ar F c p r yc : S) (q∈ : ⟨ pr (fst ar) (fst F) ∈ Ev ⟩) → ⟨ fst c ∈ Cv ⟩
             → (ec : fst c ≡ pr (fst ar) (fst p)) → (ep : fst p ≡ pr (# (toℕ k)) (fst r))
             → (e∈ : ⟨ pr (fst c) (fst yc) ∈ Tv ⟩)
             → ⟨ At.δ12 ar F c p r yc q∈ ec k (ep ∙ cong (λ a → pr a (fst r)) (sym (tg k))) e∈ ⊨ R.relN (toℕ k) ⟩
  clause-out k h ar F c p r yc q∈ c∈ ec ep e∈ =
    useSnd i0 (A.eS ∷ A.δ9) c yc refl (R.relN (toℕ k)) i5 refl (h9 A.eS e∈)
    where
    module A = At ar F c p r yc q∈ ec k (ep ∙ cong (λ a → pr a (fst r)) (sym (tg k))) e∈
    h4 : ⟨ A.δ4 ⊨ inner4 k ⟩
    h4 = useBoth i0 (A.qS ∷ γ) ar F refl (inner4 k) (h A.qS q∈)
    h7 : ⟨ A.δ7 ⊨ inner7 k ⟩
    h7 = useSnd i0 (c ∷ A.δ4) ar p ec (inner7 k) i2 refl (h4 c c∈)
    h9 : ⟨ A.δ9 ⊨ inner9 k ⟩
    h9 = useSnd i0 A.δ7 (lookup (N k) γ) r (ep ∙ cong (λ a → pr a (fst r)) (sym (tg k))) (inner9 k) (sh 7 (N k)) refl h7

  clause-in : (k : Fin 10)
            → ((q ar F s c p s1 r s2 e yc s3 : S) → ⟨ fst q ∈ Ev ⟩ → fst q ≡ pr (fst ar) (fst F)
               → ⟨ fst c ∈ Cv ⟩ → fst c ≡ pr (fst ar) (fst p) → fst p ≡ pr (# (toℕ k)) (fst r)
               → ⟨ fst e ∈ Tv ⟩ → fst e ≡ pr (fst c) (fst yc)
               → ⟨ (yc ∷ s3 ∷ e ∷ r ∷ s2 ∷ p ∷ s1 ∷ c ∷ F ∷ ar ∷ s ∷ q ∷ γ) ⊨ R.relN (toℕ k) ⟩)
            → ⟨ γ ⊨ Cl.clause k ⟩
  clause-in k g q q∈ = bothAll-in i0 (inner4 k) (q ∷ γ) (λ ar F s s∈ ar∈ F∈ eq c c∈ →
    sndAll-in i0 i2 (inner7 k) (c ∷ F ∷ ar ∷ s ∷ q ∷ γ) (λ p s1 s1∈ p∈ ec →
      sndAll-in i0 (sh 7 (N k)) (inner9 k) (p ∷ s1 ∷ c ∷ F ∷ ar ∷ s ∷ q ∷ γ) (λ r s2 s2∈ r∈ ep e e∈ →
        sndAll-in i0 i5 (R.relN (toℕ k)) (e ∷ r ∷ s2 ∷ p ∷ s1 ∷ c ∷ F ∷ ar ∷ s ∷ q ∷ γ) (λ yc s3 s3∈ yc∈ ee →
          g q ar F s c p s1 r s2 e yc s3 q∈ eq c∈ ec (ep ∙ cong (λ a → pr a (fst r)) (tg k)) e∈ ee))))
```

Totality and the domain.

```agda
  total-out : ⟨ γ ⊨ Cl.total ⟩ → (c : S) → ⟨ fst c ∈ Cv ⟩ → ∥ Σ[ yc ∈ S ] ⟨ pr (fst c) (fst yc) ∈ Tv ⟩ ∥₁
  total-out h c c∈ = PT.rec squash₁
    (λ { (e , (e∈ , hs)) → PT.map
      (λ { (yc , s , (ee , _)) → yc , subst (λ u → ⟨ u ∈ Tv ⟩) ee e∈ })
      (sndEx-out i0 i1 ⊤̇ (e ∷ c ∷ γ) hs) })
    (h c c∈)

  total-in : ((c : S) → ⟨ fst c ∈ Cv ⟩ → ∥ Σ[ yc ∈ S ] ⟨ pr (fst c) (fst yc) ∈ Tv ⟩ ∥₁) → ⟨ γ ⊨ Cl.total ⟩
  total-in g c c∈ = PT.map
    (λ { (yc , m) → down (lookup T γ) (pr (fst c) (fst yc)) m
       , ( m , fillSnd i0 (down (lookup T γ) (pr (fst c) (fst yc)) m ∷ c ∷ γ) c yc refl ⊤̇ (λ b → b) i1 refl ) })
    (g c c∈)

  onC-out : ⟨ γ ⊨ Cl.onC ⟩ → (e : S) → ⟨ fst e ∈ Tv ⟩
          → ∥ Σ[ c ∈ S ] Σ[ yc ∈ S ] ((fst e ≡ pr (fst c) (fst yc)) × ⟨ fst c ∈ Cv ⟩) ∥₁
  onC-out h e e∈ = PT.map (λ { (c , yc , s , (ee , c∈)) → c , yc , (ee , c∈) })
    (bothEx-out i0 (var i1 ∈̇ var (sh 4 C)) (e ∷ γ) (h e e∈))

  onC-in : ((e : S) → ⟨ fst e ∈ Tv ⟩ → ∥ Σ[ c ∈ S ] Σ[ yc ∈ S ] ((fst e ≡ pr (fst c) (fst yc)) × ⟨ fst c ∈ Cv ⟩) ∥₁)
         → ⟨ γ ⊨ Cl.onC ⟩
  onC-in g e e∈ = PT.rec (snd ((e ∷ γ) ⊨ bothEx i0 (var i1 ∈̇ var (sh 4 C))))
    (λ { (c , yc , (ee , c∈)) → fillBoth i0 (e ∷ γ) c yc ee (var i1 ∈̇ var (sh 4 C)) c∈ })
    (g e e∈)
```

<!--en-->
## Reading the constructor relations
<!--zh-->
## 读取构造子关系
<!--ja-->
## 構成子の関係を読む
<!--/-->

<!--en-->
The relation readers `bin-out`, `qu-out`, `bq-out`, and `atom-out`, with their
converses, turn each connective, quantifier, and atom clause into the precise
extension condition on its value set while eliminating the auxiliary bounded
witnesses.
<!--zh-->
关系读式 `bin-out`、`qu-out`、`bq-out` 与 `atom-out` 及其逆向读式，把每个联结词、量词和原子子句化为其值集合的精确外延条件，同时消去辅助的有界见证。
<!--ja-->
関係の読み補題 `bin-out`、`qu-out`、`bq-out`、`atom-out` とその逆向きは、各結合子、量化子、原子の節を、その値集合に対する正確な外延条件へ変換し、補助的な有界証人を消去する。
<!--/-->

The relations, read. Each reader hands back the extension fact at the body's own
frame; the junk slots are existential going out and universal coming in.

```agda
module RelRead {m : ℕ} (T w : Fin m) (N : Fin 10 → Fin m) (δ : S ^ (12 + m)) where
  private
    module R = Rel T w N
    yc = lookup i0 δ
    r = lookup i3 δ
    F = lookup i8 δ
    ar = lookup i9 δ
    Tv = fst (lookup (sh 12 T) δ)
    A = fst ar
    Rv = fst r
```

The extension fact of `yc` in `F` with the body at a frame.

```agda
  Ext : ∀ {k} (env : S ^ k) (φ : Formula S (1 + k)) → Type (ℓ-suc ℓ)
  Ext env φ = ExtFact (fst yc) (fst F) (λ z → ⟨ (z ∷ env) ⊨ φ ⟩)
```

The binary connectives.

```agda
  bin-out : (op : ∀ {j} → Formula S j → Formula S j → Formula S j) → ⟨ δ ⊨ R.binRel op ⟩
          → (a b c₁ ya c₂ yb : S) → Rv ≡ pr (fst a) (fst b)
          → ⟨ pr (fst c₁) (fst ya) ∈ Tv ⟩ → fst c₁ ≡ pr A (fst a)
          → ⟨ pr (fst c₂) (fst yb) ∈ Tv ⟩ → fst c₂ ≡ pr A (fst b)
          → ∥ Σ[ s ∈ S ] Σ[ s₁ ∈ S ] Σ[ e₁ ∈ S ] Σ[ s₂ ∈ S ] Σ[ e₂ ∈ S ]
              Ext (yb ∷ c₂ ∷ s₂ ∷ e₂ ∷ ya ∷ c₁ ∷ s₁ ∷ e₁ ∷ b ∷ a ∷ s ∷ δ) (R.binBody op) ∥₁
  bin-out op h a b c₁ ya c₂ yb er m₁ e₁ m₂ e₂ =
    ∣ container r a b er .fst , container e₁S c₁ ya refl .fst , e₁S , container e₂S c₂ yb refl .fst , e₂S ,
      subAt-out (sh 19 T) i16 i4 (extB i11 i19 (R.binBody op)) δ19
        (subAt-out (sh 15 T) i12 i1 (subAt (sh 19 T) i16 i4 (extB i11 i19 (R.binBody op))) δ15
          (useBoth i3 δ a b er (subAt (sh 15 T) i12 i1 (subAt (sh 19 T) i16 i4 (extB i11 i19 (R.binBody op)))) h)
          c₁ ya m₁ e₁)
        c₂ yb m₂ e₂ ∣₁
    where
    δ15 : S ^ (15 + m)
    δ15 = b ∷ a ∷ container r a b er .fst ∷ δ
    e₁S : S
    e₁S = down (lookup (sh 15 T) δ15) (pr (fst c₁) (fst ya)) m₁
    δ19 : S ^ (19 + m)
    δ19 = ya ∷ c₁ ∷ container e₁S c₁ ya refl .fst ∷ e₁S ∷ δ15
    e₂S : S
    e₂S = down (lookup (sh 19 T) δ19) (pr (fst c₂) (fst yb)) m₂

  bin-in : (op : ∀ {j} → Formula S j → Formula S j → Formula S j)
         → ((a b s c₁ ya s₁ e₁ c₂ yb s₂ e₂ : S) → Rv ≡ pr (fst a) (fst b)
            → ⟨ fst e₁ ∈ Tv ⟩ → fst e₁ ≡ pr (fst c₁) (fst ya) → fst c₁ ≡ pr A (fst a)
            → ⟨ fst e₂ ∈ Tv ⟩ → fst e₂ ≡ pr (fst c₂) (fst yb) → fst c₂ ≡ pr A (fst b)
            → Ext (yb ∷ c₂ ∷ s₂ ∷ e₂ ∷ ya ∷ c₁ ∷ s₁ ∷ e₁ ∷ b ∷ a ∷ s ∷ δ) (R.binBody op))
         → ⟨ δ ⊨ R.binRel op ⟩
  bin-in op g = bothAll-in i3 (subAt (sh 15 T) i12 i1 (subAt (sh 19 T) i16 i4 (extB i11 i19 (R.binBody op)))) δ
    (λ a b s s∈ a∈ b∈ er →
      subAt-in (sh 15 T) i12 i1 (subAt (sh 19 T) i16 i4 (extB i11 i19 (R.binBody op))) (b ∷ a ∷ s ∷ δ)
        (λ c₁ ya s₁ e₁ e₁∈ ee₁ e₁' →
          subAt-in (sh 19 T) i16 i4 (extB i11 i19 (R.binBody op)) (ya ∷ c₁ ∷ s₁ ∷ e₁ ∷ b ∷ a ∷ s ∷ δ)
            (λ c₂ yb s₂ e₂ e₂∈ ee₂ e₂' →
              g a b s c₁ ya s₁ e₁ c₂ yb s₂ e₂ er e₁∈ ee₁ e₁' e₂∈ ee₂ e₂')))
```

The unbounded quantifiers.

```agda
  qu-out : (q : ∀ {j} → Term S j → Formula S (suc j) → Formula S j) → ⟨ δ ⊨ R.quRel q ⟩
         → (c₁ ya ar' : S) → ⟨ pr (fst c₁) (fst ya) ∈ Tv ⟩ → fst c₁ ≡ pr (fst ar') Rv → fst ar' ≡ sucV A
         → ∥ Σ[ s ∈ S ] Σ[ s' ∈ S ] Σ[ e' ∈ S ] Ext (ar' ∷ s' ∷ ya ∷ c₁ ∷ s ∷ e' ∷ δ) (R.quBody q) ∥₁
  qu-out q h c₁ ya ar' mem e es =
    ∣ container e'S c₁ ya refl .fst , container c₁ ar' r e .fst , e'S
    , subSucAt-out (sh 12 T) i9 i3 (extB i6 i14 (R.quBody q)) δ h c₁ ya ar' mem e es ∣₁
    where
    e'S : S
    e'S = down (lookup (sh 12 T) δ) (pr (fst c₁) (fst ya)) mem

  qu-in : (q : ∀ {j} → Term S j → Formula S (suc j) → Formula S j)
        → ((c₁ ya ar' s s' e' : S) → ⟨ fst e' ∈ Tv ⟩ → fst e' ≡ pr (fst c₁) (fst ya)
           → fst c₁ ≡ pr (fst ar') Rv → fst ar' ≡ sucV A
           → Ext (ar' ∷ s' ∷ ya ∷ c₁ ∷ s ∷ e' ∷ δ) (R.quBody q))
        → ⟨ δ ⊨ R.quRel q ⟩
  qu-in q g = subSucAt-in (sh 12 T) i9 i3 (extB i6 i14 (R.quBody q)) δ g
```

The bounded quantifiers.

```agda
  bq-out : (q : ∀ {j} → Term S j → Formula S (suc j) → Formula S j)
         → (c : ∀ {j} → Formula S j → Formula S j → Formula S j) → ⟨ δ ⊨ R.bqRel q c ⟩
         → (t a c₁ ya ar' : S) → Rv ≡ pr (fst t) (fst a)
         → ⟨ pr (fst c₁) (fst ya) ∈ Tv ⟩ → fst c₁ ≡ pr (fst ar') (fst a) → fst ar' ≡ sucV A
         → ∥ Σ[ s ∈ S ] Σ[ s₁ ∈ S ] Σ[ s' ∈ S ] Σ[ e' ∈ S ]
             Ext (ar' ∷ s' ∷ ya ∷ c₁ ∷ s₁ ∷ e' ∷ a ∷ t ∷ s ∷ δ) (R.bqBody q c) ∥₁
  bq-out q c h t a c₁ ya ar' er mem e es =
    ∣ container r t a er .fst , container e'S c₁ ya refl .fst , container c₁ ar' a e .fst , e'S ,
      subSucAt-out (sh 15 T) i12 i0 (extB i9 i17 (R.bqBody q c)) δ15
        (useBoth i3 δ t a er (subSucAt (sh 15 T) i12 i0 (extB i9 i17 (R.bqBody q c))) h)
        c₁ ya ar' mem e es ∣₁
    where
    δ15 : S ^ (15 + m)
    δ15 = a ∷ t ∷ container r t a er .fst ∷ δ
    e'S : S
    e'S = down (lookup (sh 15 T) δ15) (pr (fst c₁) (fst ya)) mem

  bq-in : (q : ∀ {j} → Term S j → Formula S (suc j) → Formula S j)
        → (c : ∀ {j} → Formula S j → Formula S j → Formula S j)
        → ((t a s c₁ ya ar' s₁ s' e' : S) → Rv ≡ pr (fst t) (fst a)
           → ⟨ fst e' ∈ Tv ⟩ → fst e' ≡ pr (fst c₁) (fst ya)
           → fst c₁ ≡ pr (fst ar') (fst a) → fst ar' ≡ sucV A
           → Ext (ar' ∷ s' ∷ ya ∷ c₁ ∷ s₁ ∷ e' ∷ a ∷ t ∷ s ∷ δ) (R.bqBody q c))
        → ⟨ δ ⊨ R.bqRel q c ⟩
  bq-in q c g = bothAll-in i3 (subSucAt (sh 15 T) i12 i0 (extB i9 i17 (R.bqBody q c))) δ
    (λ t a s s∈ t∈ a∈ er →
      subSucAt-in (sh 15 T) i12 i0 (extB i9 i17 (R.bqBody q c)) (a ∷ t ∷ s ∷ δ)
        (λ c₁ ya ar' s₁ s' e' e'∈ ee e es → g t a s c₁ ya ar' s₁ s' e' er e'∈ ee e es))
```

The atoms.

```agda
  atom-out : (rel : Formula S (18 + m)) → ⟨ δ ⊨ R.atomRel rel ⟩
           → (t u : S) → Rv ≡ pr (fst t) (fst u)
           → ∥ Σ[ s ∈ S ] Ext (u ∷ t ∷ s ∷ δ) (R.atomBody rel) ∥₁
  atom-out rel h t u er = ∣ container r t u er .fst , useBoth i3 δ t u er (extB i3 i11 (R.atomBody rel)) h ∣₁

  atom-in : (rel : Formula S (18 + m))
          → ((t u s : S) → Rv ≡ pr (fst t) (fst u) → Ext (u ∷ t ∷ s ∷ δ) (R.atomBody rel))
          → ⟨ δ ⊨ R.atomRel rel ⟩
  atom-in rel g = bothAll-in i3 (extB i3 i11 (R.atomBody rel)) δ (λ t u s s∈ t∈ u∈ er → g t u s er)
```

<!--en-->
## Bridging clauses to semantic satisfaction
<!--zh-->
## 从子句桥接到语义满足关系
<!--ja-->
## 節から意味論的充足へ橋渡しする
<!--/-->

<!--en-->
The bridge lemmas compare each constructor relation with the value produced by
the external recursion `Sat`: after decoding an environment, membership in a
child value becomes satisfaction of the child formula, yielding bridges for the
constant, connectives, quantifiers, and atoms.
<!--zh-->
这些桥接引理把每种构造子关系与外部递归 `Sat` 产生的值比较；解码环境后，属于子公式值就化为该子公式的满足关系，从而得到常元、联结词、量词与原子的桥接结果。
<!--ja-->
橋渡し補題は、各構成子の関係を外部再帰 `Sat` が作る値と比較する。環境を復号すると、子の値への所属は子論理式の充足に変わり、定数、結合子、量化子、原子のそれぞれに対する橋渡しが得られる。
<!--/-->

The bridge to the meta-level value. For every constructor, the value
src/L/Coding/Satisfaction.lagda.md builds is the extension of the clause's body over the
environment set: each bridge is `Sat-mem` read back, with the term and cons
readers carried between the clause's frame and the recursion's.

```agda
open import FOL.Manipulation.ConstantMapping using ( mapFo; mapTm )
open import L.Coding.Satisfaction {ℓ} lem using ( Sat; Sat-mem; cond )
open import L.Coding.SatisfactionBridge {ℓ} lem using ( asConst )
import L.Coding.SatisfactionBridge {ℓ} lem as Semantic
open import Cubical.Data.Nat using ( znots; snotz )

module Bridge (W : S) where
  open Alphabet W
  open TruthAlgebra (hPropAlgebra (ℓ-suc ℓ)) using ( _⊓_; _⊔_; _⇒_ )
  private
    module DB = Semantic.DB W
    module Sem = Semantic.SemB W
    open Sem.At DB.SM id using () renaming ( _⊨_ to _⊨ᴮ_ ; ⟦_⟧ to ⟦_⟧ᴮ )

    Meaning : ∀ {n} → Formula Ab n → DB.SM ^ n → hProp (ℓ-suc ℓ)
    Meaning ψ δ = δ ⊨ᴮ mapFo DB.ι ψ

  private
    Wv = fst W

  toS : ∀ {n} → Formula Ab n → Formula S n
  toS = mapFo (asConst W)

  SatW : ∀ {n} → Formula Ab n → S
  SatW ψ = Sat W (toS ψ)
```

An environment over `W` is recovered as a vector of members by
`envSet-vectors` in src/L/Coding/SatisfactionBridge.lagda.md. Its term values therefore lie
in `W`, and its extension is the graph of the vector with one member prepended.
The same chapter identifies membership in the recursion's value with satisfaction
at this vector, so the clause readers can use that interpretation directly.

The recursion's value, read.

```agda
  Sat-out : ∀ {n} (ψ : Formula Ab n) (z : S) → ⟨ fst z ∈ fst (SatW ψ) ⟩
          → ⟨ fst z ∈ fst (envSet W n) ⟩ × ⟨ (z ∷ []) ⊨ cond W (toS ψ) ⟩
  Sat-out ψ z h = subst ⟨_⟩ (Sat-mem W (toS ψ) z) h

  Sat-in : ∀ {n} (ψ : Formula Ab n) (z : S) → ⟨ fst z ∈ fst (envSet W n) ⟩
         → ⟨ (z ∷ []) ⊨ cond W (toS ψ) ⟩ → ⟨ fst z ∈ fst (SatW ψ) ⟩
  Sat-in ψ z hz hc = subst ⟨_⟩ (sym (Sat-mem W (toS ψ) z)) (hz , hc)
```

A pointwise reading of the recursion's condition determines its extension.
The environment witness is eliminated once for both directions.

```agda
  private
    extension-path : ∀ {n} (ψ : Formula Ab n) (P : S → hProp (ℓ-suc ℓ))
                   → ((z : S) → ((z ∷ []) ⊨ cond W (toS ψ)) ≡ P z)
                   → ExtFact (fst (SatW ψ)) (fst (envSet W n)) (λ z → ⟨ P z ⟩)
    extension-path ψ P e =
        (λ z hz → Sat-out ψ z hz .fst , subst ⟨_⟩ (e z) (Sat-out ψ z hz .snd))
      , (λ z hz hp → Sat-in ψ z hz (subst ⟨_⟩ (sym (e z)) hp))
```

The constant.

```agda
  botBridge : (n : ℕ) {k : ℕ} (env : S ^ k)
            → ExtFact (fst (SatW (⊥̇ {n = n}))) (fst (envSet W n)) (λ z → ⟨ (z ∷ env) ⊨ ⊥̇ ⟩)
  botBridge n env = (λ z hz → Sat-out ⊥̇ z hz .fst , Sat-out ⊥̇ z hz .snd) , (λ z hz b → Empty.rec* b)
```

The connectives, with the subvalues at slots.

```agda
  andBridge : ∀ {n} (a b : Formula Ab n) {k : ℕ} (env : S ^ k) (ya yb : Fin k)
            → fst (lookup ya env) ≡ fst (SatW a) → fst (lookup yb env) ≡ fst (SatW b)
            → ExtFact (fst (SatW (a ∧̇ b))) (fst (envSet W n))
                (λ z → ⟨ (z ∷ env) ⊨ (var i0 ∈̇ var (suc ya)) ∧̇ (var i0 ∈̇ var (suc yb)) ⟩)
  andBridge a b env ya yb qa qb = extension-path (a ∧̇ b)
    (λ z → (z ∷ env) ⊨ (var i0 ∈̇ var (suc ya)) ∧̇ (var i0 ∈̇ var (suc yb)))
    (λ z i → (fst z ∈ sym qa i) ⊓ (fst z ∈ sym qb i))

  orBridge : ∀ {n} (a b : Formula Ab n) {k : ℕ} (env : S ^ k) (ya yb : Fin k)
           → fst (lookup ya env) ≡ fst (SatW a) → fst (lookup yb env) ≡ fst (SatW b)
           → ExtFact (fst (SatW (a ∨̇ b))) (fst (envSet W n))
               (λ z → ⟨ (z ∷ env) ⊨ (var i0 ∈̇ var (suc ya)) ∨̇ (var i0 ∈̇ var (suc yb)) ⟩)
  orBridge a b env ya yb qa qb = extension-path (a ∨̇ b)
    (λ z → (z ∷ env) ⊨ (var i0 ∈̇ var (suc ya)) ∨̇ (var i0 ∈̇ var (suc yb)))
    (λ z i → (fst z ∈ sym qa i) ⊔ (fst z ∈ sym qb i))

  impBridge : ∀ {n} (a b : Formula Ab n) {k : ℕ} (env : S ^ k) (ya yb : Fin k)
            → fst (lookup ya env) ≡ fst (SatW a) → fst (lookup yb env) ≡ fst (SatW b)
            → ExtFact (fst (SatW (a ⇒̇ b))) (fst (envSet W n))
                (λ z → ⟨ (z ∷ env) ⊨ (var i0 ∈̇ var (suc ya)) ⇒̇ (var i0 ∈̇ var (suc yb)) ⟩)
  impBridge a b env ya yb qa qb = extension-path (a ⇒̇ b)
    (λ z → (z ∷ env) ⊨ (var i0 ∈̇ var (suc ya)) ⇒̇ (var i0 ∈̇ var (suc yb)))
    (λ z i → (fst z ∈ sym qa i) ⇒ (fst z ∈ sym qb i))

```

The unbounded quantifiers. The body at `z`: for some/every `x` in `w`, some
member of `ya` is `cons x z`.

```agda
  quEx quAll : ∀ {k} → Fin k → Fin k → Formula S (1 + k)
  quEx wi yai = ∃̇∈ (var (suc wi)) (∃̇∈ (var (suc (suc yai))) (consAtL i0 i1 i2))
  quAll wi yai = ∀̇∈ (var (suc wi)) (∃̇∈ (var (suc (suc yai))) (consAtL i0 i1 i2))
```

Recover the environment vector once, then read the clause as ordinary
satisfaction. A child value is the graph of the extended vector; its membership
in the recursive value is precisely satisfaction of the child formula.

```agda
  private
    direct-extension : ∀ {n} (ψ : Formula Ab n) (P : S → hProp (ℓ-suc ℓ))
      → ((δ : DB.SM ^ n) (z : S) → fst z ≡ Semantic.graph W δ → ⟨ Meaning ψ δ ⟩ → ⟨ P z ⟩)
      → ((δ : DB.SM ^ n) (z : S) → fst z ≡ Semantic.graph W δ → ⟨ P z ⟩ → ⟨ Meaning ψ δ ⟩)
      → ExtFact (fst (SatW ψ)) (fst (envSet W n)) (λ z → ⟨ P z ⟩)
    direct-extension {n} ψ P f b = out , inn
      where
      out : (z : S) → ⟨ fst z ∈ fst (SatW ψ) ⟩ → ⟨ fst z ∈ fst (envSet W n) ⟩ × ⟨ P z ⟩
      out z hz = Sat-out ψ z hz .fst , PT.rec (snd (P z))
        (λ { (δ , q) → f δ z q (subst ⟨_⟩ (Semantic.Sat-small-spec W ψ δ z q) hz) })
        (Semantic.envSet-vectors W z (Sat-out ψ z hz .fst))
      inn : (z : S) → ⟨ fst z ∈ fst (envSet W n) ⟩ → ⟨ P z ⟩ → ⟨ fst z ∈ fst (SatW ψ) ⟩
      inn z hz hp = PT.rec (snd (fst z ∈ fst (SatW ψ)))
        (λ { (δ , q) → subst ⟨_⟩ (sym (Semantic.Sat-small-spec W ψ δ z q)) (b δ z q hp) })
        (Semantic.envSet-vectors W z hz)

    child : ∀ {n k} (a : Formula Ab (suc n)) (δ : DB.SM ^ n) (x : DB.SM)
      (γ : S ^ k) (zi yai : Fin k) → fst (lookup zi γ) ≡ Semantic.graph W δ
      → fst (lookup yai γ) ≡ fst (SatW a)
      → ((Semantic.intoL W x ∷ γ) ⊨ ∃̇∈ (var (suc yai)) (consAtL i0 i1 (sh 2 zi)))
        ≡ Meaning a (x ∷ δ)
    child a δ x γ zi yai qz qa = ⇔toPath out inn
      where
      out : ⟨ (Semantic.intoL W x ∷ γ) ⊨ ∃̇∈ (var (suc yai)) (consAtL i0 i1 (sh 2 zi)) ⟩
          → ⟨ Meaning a (x ∷ δ) ⟩
      out = PT.rec (snd (Meaning a (x ∷ δ))) (λ { (e , he , hc) →
        subst ⟨_⟩ (Semantic.Sat-small-spec W a (x ∷ δ) e
          (Semantic.consAtL-out W δ x (e ∷ Semantic.intoL W x ∷ γ) i0 i1 (sh 2 zi) qz refl hc))
          (subst (λ X → ⟨ fst e ∈ X ⟩) qa he) })
      inn : ⟨ Meaning a (x ∷ δ) ⟩
          → ⟨ (Semantic.intoL W x ∷ γ) ⊨ ∃̇∈ (var (suc yai)) (consAtL i0 i1 (sh 2 zi)) ⟩
      inn h = ∣ Semantic.envFor W (x ∷ δ)
        , subst (λ X → ⟨ fst (Semantic.envFor W (x ∷ δ)) ∈ X ⟩) (sym qa)
          (subst ⟨_⟩ (sym (Semantic.Sat-small-spec W a (x ∷ δ) (Semantic.envFor W (x ∷ δ))
            (Semantic.envFor-graph W (x ∷ δ)))) h)
        , Semantic.consAtL-in W δ x (Semantic.envFor W (x ∷ δ) ∷ Semantic.intoL W x ∷ γ)
            i0 i1 (sh 2 zi) qz refl (Semantic.envFor-graph W (x ∷ δ)) ∣₁

  exBridge : ∀ {n} (a : Formula Ab (suc n)) {k : ℕ} (γ : S ^ k) (wi yai : Fin k)
           → fst (lookup wi γ) ≡ Wv → fst (lookup yai γ) ≡ fst (SatW a)
           → ExtFact (fst (SatW (∃̇ a))) (fst (envSet W n)) (λ z → ⟨ (z ∷ γ) ⊨ quEx wi yai ⟩)
  exBridge a γ wi yai qw qa = direct-extension (∃̇ a) (λ z → (z ∷ γ) ⊨ quEx wi yai)
    (λ δ z qz → PT.map (λ { (x , h) → Semantic.intoL W x
      , subst (λ X → ⟨ fst x ∈ X ⟩) (sym qw) (snd x)
      , subst ⟨_⟩ (sym (child a δ x (z ∷ γ) i0 (suc yai) qz qa)) h }))
    (λ δ z qz → PT.map (λ { (x , hx , h) → (fst x , subst (λ X → ⟨ fst x ∈ X ⟩) qw hx)
      , subst ⟨_⟩ (child a δ (fst x , subst (λ X → ⟨ fst x ∈ X ⟩) qw hx)
        (z ∷ γ) i0 (suc yai) qz qa) h }))

  allBridge : ∀ {n} (a : Formula Ab (suc n)) {k : ℕ} (γ : S ^ k) (wi yai : Fin k)
            → fst (lookup wi γ) ≡ Wv → fst (lookup yai γ) ≡ fst (SatW a)
            → ExtFact (fst (SatW (∀̇ a))) (fst (envSet W n)) (λ z → ⟨ (z ∷ γ) ⊨ quAll wi yai ⟩)
  allBridge a γ wi yai qw qa = direct-extension (∀̇ a) (λ z → (z ∷ γ) ⊨ quAll wi yai)
    (λ δ z qz h x hx → subst ⟨_⟩
      (sym (child a δ (fst x , subst (λ X → ⟨ fst x ∈ X ⟩) qw hx) (z ∷ γ) i0 (suc yai) qz qa))
      (h (fst x , subst (λ X → ⟨ fst x ∈ X ⟩) qw hx)))
    (λ δ z qz h x → subst ⟨_⟩ (child a δ x (z ∷ γ) i0 (suc yai) qz qa)
      (h (Semantic.intoL W x) (subst (λ X → ⟨ fst x ∈ X ⟩) (sym qw) (snd x))))
```

The bounded quantifiers. The body at `z`: for the value `v` of `t` at `z` and
some/every `x ∈ w` with `x ∈ v`, some member of `ya` is `cons x z`.

```agda
  bqAll bqEx : ∀ {k} → Fin k → Fin k → Fin k → Fin k → Fin k → Formula S (1 + k)
  bqAll wi ti yai N0i N1i =
    ∀̇∈ (var (suc wi)) (tmIs (suc (suc ti)) i1 i0 (suc (suc N0i)) (suc (suc N1i))
      ⇒̇ ∀̇∈ (var (suc (suc wi))) ((var i0 ∈̇ var i1) ⇒̇ ∃̇∈ (var (suc (suc (suc yai)))) (consAtL i0 i1 i3)))
  bqEx wi ti yai N0i N1i =
    ∃̇∈ (var (suc wi)) (tmIs (suc (suc ti)) i1 i0 (suc (suc N0i)) (suc (suc N1i))
      ∧̇ ∃̇∈ (var (suc (suc wi))) ((var i0 ∈̇ var i1) ∧̇ ∃̇∈ (var (suc (suc (suc yai)))) (consAtL i0 i1 i3)))
```

The term readers at any frame and slots.

```agda
  private
    value : ∀ {n} → Term Ab n → DB.SM ^ n → DB.SM
    value t δ = ⟦ mapTm DB.ι t ⟧ᴮ δ

    term-out : ∀ {n} (t : Term Ab n) (δ : DB.SM ^ n) (z v : S)
      → fst z ≡ Semantic.graph W δ → TmIsV (ct t) (fst z) (fst v)
      → fst v ≡ fst (value t δ)
    term-out (con q) δ z v qz = PT.rec (setIsSet _ _)
      (λ { (inl e) → sym (pr-inj e .snd)
         ; (inr (i , e , _)) → Empty.rec (znots (#-inj′ {0} {1} (pr-inj e .fst))) })
    term-out (var i) δ z v qz = PT.rec (setIsSet _ _)
      (λ { (inl e) → Empty.rec (snotz (#-inj′ {1} {0} (pr-inj e .fst)))
         ; (inr (j , e , hp)) → subst ⟨_⟩ (lookup-spec (Semantic.values W δ) i (fst v))
             (subst2 (λ a E → ⟨ pr a (fst v) ∈ E ⟩) (sym (pr-inj e .snd)) qz hp) })

    term-in : ∀ {n} (t : Term Ab n) (δ : DB.SM ^ n) (z v : S)
      → fst z ≡ Semantic.graph W δ → fst v ≡ fst (value t δ)
      → TmIsV (ct t) (fst z) (fst v)
    term-in (con q) δ z v qz e = ∣ inl (cong (pr (# 0)) (sym e)) ∣₁
    term-in (var i) δ z v qz e = ∣ inr (# (toℕ i) , refl
      , subst (λ E → ⟨ pr (# (toℕ i)) (fst v) ∈ E ⟩) (sym qz)
          (subst ⟨_⟩ (sym (lookup-spec (Semantic.values W δ) i (fst v))) e)) ∣₁

  module BqBridge {n : ℕ} (t : Term Ab n) (a : Formula Ab (suc n)) {k : ℕ} (Γ : S ^ k)
    (wi ti yai N0i N1i : Fin k)
    (qw : fst (lookup wi Γ) ≡ Wv) (qt : fst (lookup ti Γ) ≡ ct t) (qa : fst (lookup yai Γ) ≡ fst (SatW a))
    (q0 : fst (lookup N0i Γ) ≡ # 0) (q1 : fst (lookup N1i Γ) ≡ # 1) where

    private
```

The term, read at `v ∷ z ∷ Γ` and carried to the recursion's frame.

```agda
      tmOut : (z v : S) → ⟨ (v ∷ z ∷ Γ) ⊨ tmIs (suc (suc ti)) i1 i0 (suc (suc N0i)) (suc (suc N1i)) ⟩
            → TmIsV (ct t) (fst z) (fst v)
      tmOut z v h = subst (λ u → TmIsV u (fst z) (fst v)) qt
        (tmIs-out (suc (suc ti)) i1 i0 (suc (suc N0i)) (suc (suc N1i)) (v ∷ z ∷ Γ) q0 q1 h)

      tmIn' : (z v : S) → TmIsV (ct t) (fst z) (fst v)
            → ⟨ (v ∷ z ∷ Γ) ⊨ tmIs (suc (suc ti)) i1 i0 (suc (suc N0i)) (suc (suc N1i)) ⟩
      tmIn' z v h = tmIs-in (suc (suc ti)) i1 i0 (suc (suc N0i)) (suc (suc N1i)) (v ∷ z ∷ Γ) q0 q1
        (subst (λ u → TmIsV u (fst z) (fst v)) (sym qt) h)

      bound : DB.SM ^ n → S
      bound δ = Semantic.intoL W (value t δ)

      bound∈W : (δ : DB.SM ^ n) → ⟨ fst (bound δ) ∈ fst (lookup wi Γ) ⟩
      bound∈W δ = subst (λ X → ⟨ fst (value t δ) ∈ X ⟩)
        (sym qw) (snd (value t δ))

      bound-term : (δ : DB.SM ^ n) (z : S) → fst z ≡ Semantic.graph W δ
                 → TmIsV (ct t) (fst z) (fst (bound δ))
      bound-term δ z qz = term-in t δ z (bound δ) qz refl

      bound-read : (δ : DB.SM ^ n) (z : S) → fst z ≡ Semantic.graph W δ
                 → ⟨ (bound δ ∷ z ∷ Γ)
                     ⊨ tmIs (suc (suc ti)) i1 i0
                         (suc (suc N0i)) (suc (suc N1i)) ⟩
      bound-read δ z qz = tmIn' z (bound δ) (bound-term δ z qz)
```

The bound term has its semantic value in `W`. Both bounded quantifiers use
that value and the same child-satisfaction path as the unbounded quantifiers.

```agda
    allInBridge : ExtFact (fst (SatW (∀̇∈ t a))) (fst (envSet W n)) (λ z → ⟨ (z ∷ Γ) ⊨ bqAll wi ti yai N0i N1i ⟩)
    allInBridge = direct-extension (∀̇∈ t a) (λ z → (z ∷ Γ) ⊨ bqAll wi ti yai N0i N1i)
      (λ δ z qz h v hv ht x hx hxv → subst ⟨_⟩
        (sym (child a δ (fst x , subst (λ X → ⟨ fst x ∈ X ⟩) qw hx)
          (v ∷ z ∷ Γ) i1 (sh 2 yai) qz qa))
        (h (fst x , subst (λ X → ⟨ fst x ∈ X ⟩) qw hx)
          (subst (λ V → ⟨ fst x ∈ V ⟩) (term-out t δ z v qz (tmOut z v ht)) hxv)))
      (λ δ z qz h x hx → subst ⟨_⟩
        (child a δ x (bound δ ∷ z ∷ Γ) i1 (sh 2 yai) qz qa)
        (h (bound δ) (bound∈W δ) (bound-read δ z qz)
          (Semantic.intoL W x) (subst (λ X → ⟨ fst x ∈ X ⟩) (sym qw) (snd x)) hx))

    exInBridge : ExtFact (fst (SatW (∃̇∈ t a))) (fst (envSet W n)) (λ z → ⟨ (z ∷ Γ) ⊨ bqEx wi ti yai N0i N1i ⟩)
    exInBridge = direct-extension (∃̇∈ t a) (λ z → (z ∷ Γ) ⊨ bqEx wi ti yai N0i N1i)
      (λ δ z qz → PT.map (λ { (x , hx , h) → bound δ
        , bound∈W δ
        , bound-read δ z qz
        , ∣ Semantic.intoL W x , subst (λ X → ⟨ fst x ∈ X ⟩) (sym qw) (snd x) , hx
            , subst ⟨_⟩ (sym (child a δ x (bound δ ∷ z ∷ Γ) i1 (sh 2 yai) qz qa)) h ∣₁ }))
      (λ δ z qz → PT.rec squash₁ (λ { (v , hv , ht , h) → PT.map
        (λ { (x , hx , hxv , hc) → (fst x , subst (λ X → ⟨ fst x ∈ X ⟩) qw hx)
          , subst (λ V → ⟨ fst x ∈ V ⟩) (term-out t δ z v qz (tmOut z v ht)) hxv
          , subst ⟨_⟩ (child a δ (fst x , subst (λ X → ⟨ fst x ∈ X ⟩) qw hx)
              (v ∷ z ∷ Γ) i1 (sh 2 yai) qz qa) hc }) h }))
```

The atoms. The body at `z`: for the values `v`, `x` of `t`, `u` at `z`,
`v rel x`.

```agda
  atomEx : ∀ {k} → Fin k → Fin k → Fin k → Fin k → Fin k → Formula S (3 + k) → Formula S (1 + k)
  atomEx wi ti ui N0i N1i rel =
    ∃̇∈ (var (suc wi)) (∃̇∈ (var (suc (suc wi)))
      (tmIs (suc (suc (suc ti))) i2 i1 (sh 3 N0i) (sh 3 N1i)
        ∧̇ (tmIs (suc (suc (suc ui))) i2 i0 (sh 3 N0i) (sh 3 N1i) ∧̇ rel)))

  module AtomBridge {n : ℕ} (t u : Term Ab n) {k : ℕ} (Γ : S ^ k)
    (wi ti ui N0i N1i : Fin k)
    (qw : fst (lookup wi Γ) ≡ Wv) (qt : fst (lookup ti Γ) ≡ ct t) (qu : fst (lookup ui Γ) ≡ ct u)
    (q0 : fst (lookup N0i Γ) ≡ # 0) (q1 : fst (lookup N1i Γ) ≡ # 1)
    (op : ∀ {j} → Term Ab j → Term Ab j → Formula Ab j)
    (R : V ℓ → V ℓ → Type (ℓ-suc ℓ))
    (rel : Formula S (3 + k))
    (agree : (z v x : S) → (⟨ (x ∷ v ∷ z ∷ Γ) ⊨ rel ⟩ → R (fst v) (fst x))
                           × (R (fst v) (fst x) → ⟨ (x ∷ v ∷ z ∷ Γ) ⊨ rel ⟩))
    (cnd-out : (δ : DB.SM ^ n) → ⟨ Meaning (op t u) δ ⟩ → R (fst (value t δ)) (fst (value u δ)))
    (cnd-in : (δ : DB.SM ^ n) → R (fst (value t δ)) (fst (value u δ)) → ⟨ Meaning (op t u) δ ⟩) where

    private
      δ3 : (z v x : S) → S ^ (3 + k)
      δ3 z v x = x ∷ v ∷ z ∷ Γ

      tOut : (z v x : S) → ⟨ δ3 z v x ⊨ tmIs (suc (suc (suc ti))) i2 i1 (sh 3 N0i) (sh 3 N1i) ⟩ → TmIsV (ct t) (fst z) (fst v)
      tOut z v x h = subst (λ w → TmIsV w (fst z) (fst v)) qt
        (tmIs-out (suc (suc (suc ti))) i2 i1 (sh 3 N0i) (sh 3 N1i) (δ3 z v x) q0 q1 h)
      uOut : (z v x : S) → ⟨ δ3 z v x ⊨ tmIs (suc (suc (suc ui))) i2 i0 (sh 3 N0i) (sh 3 N1i) ⟩ → TmIsV (ct u) (fst z) (fst x)
      uOut z v x h = subst (λ w → TmIsV w (fst z) (fst x)) qu
        (tmIs-out (suc (suc (suc ui))) i2 i0 (sh 3 N0i) (sh 3 N1i) (δ3 z v x) q0 q1 h)
      tIn : (z v x : S) → TmIsV (ct t) (fst z) (fst v) → ⟨ δ3 z v x ⊨ tmIs (suc (suc (suc ti))) i2 i1 (sh 3 N0i) (sh 3 N1i) ⟩
      tIn z v x h = tmIs-in (suc (suc (suc ti))) i2 i1 (sh 3 N0i) (sh 3 N1i) (δ3 z v x) q0 q1
        (subst (λ w → TmIsV w (fst z) (fst v)) (sym qt) h)
      uIn : (z v x : S) → TmIsV (ct u) (fst z) (fst x) → ⟨ δ3 z v x ⊨ tmIs (suc (suc (suc ui))) i2 i0 (sh 3 N0i) (sh 3 N1i) ⟩
      uIn z v x h = tmIs-in (suc (suc (suc ui))) i2 i0 (sh 3 N0i) (sh 3 N1i) (δ3 z v x) q0 q1
        (subst (λ w → TmIsV w (fst z) (fst x)) (sym qu) h)

    atomBridge : ExtFact (fst (SatW (op t u))) (fst (envSet W n)) (λ z → ⟨ (z ∷ Γ) ⊨ atomEx wi ti ui N0i N1i rel ⟩)
    atomBridge = direct-extension (op t u) (λ z → (z ∷ Γ) ⊨ atomEx wi ti ui N0i N1i rel) out inn
      where
      out : (δ : DB.SM ^ n) (z : S) → fst z ≡ Semantic.graph W δ → ⟨ Meaning (op t u) δ ⟩
          → ⟨ (z ∷ Γ) ⊨ atomEx wi ti ui N0i N1i rel ⟩
      out δ z qz h = ∣ v , subst (λ X → ⟨ fst v ∈ X ⟩) (sym qw) (snd (value t δ))
        , ∣ x , subst (λ X → ⟨ fst x ∈ X ⟩) (sym qw) (snd (value u δ))
          , tIn z v x (term-in t δ z v qz refl)
          , uIn z v x (term-in u δ z x qz refl)
          , agree z v x .snd (cnd-out δ h) ∣₁ ∣₁
        where
        v x : S
        v = Semantic.intoL W (value t δ)
        x = Semantic.intoL W (value u δ)

      inn : (δ : DB.SM ^ n) (z : S) → fst z ≡ Semantic.graph W δ
          → ⟨ (z ∷ Γ) ⊨ atomEx wi ti ui N0i N1i rel ⟩ → ⟨ Meaning (op t u) δ ⟩
      inn δ z qz = PT.rec (snd (Meaning (op t u) δ)) (λ { (v , hv , h) →
        PT.rec (snd (Meaning (op t u) δ)) (λ { (x , hx , ht , hu , hr) →
          cnd-in δ (subst2 R (term-out t δ z v qz (tOut z v x ht))
            (term-out u δ z x qz (uOut z v x hu)) (agree z v x .fst hr)) }) h })
```

<!--en-->
## Recap
<!--zh-->
## 回顾
<!--ja-->
## まとめ
<!--/-->

<!--en-->
`tableAt` packages the ten satisfaction clauses into one Δ₀ table specification;
its readers expose the frame and constructor meanings, and the bridge lemmas
identify every clause value with the corresponding external satisfaction
condition.
<!--zh-->
`tableAt` 把十条满足关系子句封装成一个 Δ₀ 表规格；相应读式揭示框架与各构造子的含义，而桥接引理把每个子句的值识别为对应的外部满足条件。
<!--ja-->
`tableAt` は十個の充足関係の節を一つの Δ₀ 表仕様にまとめる。その読み補題が枠組みと各構成子の意味を取り出し、橋渡し補題が各節の値を対応する外部の充足条件と同定する。
<!--/-->
