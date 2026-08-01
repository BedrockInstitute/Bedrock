# The tower's step, described

<!--en-->
The tower's step is described from the inside here. An entry of the step is a
pair of a code with its value, and the table chapter already said, one
constructor at a time, what an entry must look like against the family it sits
in. What that chapter could not say is what this one can: that the entry is
readable as a code at all. A naked existential over tables admits junk, because
the clause shapes are conditional on numeral-ness and nothing else pins the
payload down. The certificate closes the gap with local conditions only: each
branch pins its tag by a sealed numeral, its payload pieces as members of ω or
of the carrier, its children present in the main table, and its annotations in
a table that is required functional, so an annotation is unique and can be
trusted. Reading a certificate back into an honest term of the syntax is the
next section's work; here the certificate shape is described, not yet
recovered.
<!--zh-->
本章从内部描述塔的一步。步的条目是码与其取值的对，表章已逐构造子说出条目对着所在族必须长什么样。表章说不出、而本章能说的，是条目根本可被读作码。对诸表的裸存在量词接纳垃圾，因为子句形状以数码性为条件，此外再无别物把载荷钉住。证书只用局部条件补上这个缺口：每个分支以封印数码钉住标签，以 ω 或载体的成员钉住载荷诸件，以主表钉住孩子的在场，并把注解放进一条被要求为函数性的表，故注解唯一而可信任。把证书读回语法中诚实的项，是下一节的工作；此处描述证书形状，尚未收回。
<!--/-->

```agda
{-# OPTIONS --cubical --safe --guardedness #-}

open import Base.Prelude
open import Base.Truth
open import Base.Classical using ( LEM )

module L.Godel.Tower {ℓ : Level} where

open import FOL.ZFStructure using ( module hPropStructure )
open import FOL.Syntax
  using ( Formula; var; con; _∈̇_; _≐_; _∧̇_; _∨̇_; _⇒̇_; ∃̇_; ∀̇_ )
import FOL.Absoluteness
open import V.Hierarchy {ℓ} using ( 𝒮ᵥ; regularityV )
open import V.Coding {ℓ} using ( pr )
open import L.Constructible {ℓ} using ( 𝒮ʟ; isL; isL-trans; Lset→isL )
open import L.Axioms.Numerals {ℓ} using ( numeralL; numeralL-fst )
open import L.Coding.Model {ℓ}
  using ( prʟ; prʟ-fst; prAtL; prAtL-adequate; appAt; appAt-adequate
        ; sucAtL; sucAtL-adequate )
open import L.Godel.Table {ℓ} using ( tagPrAt; tagPr-out; tagPr-in )
open import L.Godel.Terms {ℓ}
  using ( KT; allK; selMemK; selEqK; selEqConK; interK; unionK; complK; shiftK )
open import L.Godel.Codes {ℓ} using ( module Codes )
open import L.Ordinal {ℓ} using ( suc-ord; ω-ord; ∈#-elim )

open import Cubical.Data.Sum using ( _⊎_; inl; inr )
open import Cubical.Data.FinData using ( toℕ )
open import Cubical.Data.FinData.Properties using ( fromℕ'; toFromId' )
open import Cubical.Data.Bool using ( true; false )
open import Cubical.Data.Unit using ( tt* )
open import Cubical.Induction.WellFounded using ( Acc; acc )
import Cubical.HITs.PropositionalTruncation as PT
open PT using ( ∣_∣₁; ∥_∥₁ )
open import Cubical.HITs.CumulativeHierarchy.Base using ( V; _∈_ )
open import Cubical.HITs.CumulativeHierarchy.Properties
  using ( ∈-asFiber; ⟪_⟫; ⟪_⟫↪ )
open import Cubical.HITs.CumulativeHierarchy.Constructions
  using ( module InfinitySet; ⁅_,_⁆; ⁅_⁆s )
open InfinitySet using ( sucV; #_; ω )

open hPropStructure 𝒮ᵥ using ( _∈ˢ_; _∈ᵗ_ )
open hPropStructure 𝒮ʟ using ( S )

module AbsL = FOL.Absoluteness.Single 𝒮ᵥ isL isL-trans
open AbsL using ( _^_ ) renaming ( _⊨ᵐ_ to _⊨_ )
```

<!--en-->
One piece of infrastructure is laid down before the classical modules, since
nothing classical is involved. The honesty proof recurses on the accessibility
of the transitive closure of membership, not of membership itself: a child code
sits four membership steps below its node code, and the termination checker
follows only one step at a time. The closure records the whole descent in a
single derivation, `_∈⁺_`, built once from the one-step relation `_∈ᵗ_`, with
its accessibility transported in from regularity, along with the two-step
chains that reach the components of a Kuratowski pair and the transitivity that
composes chains to depth four.
<!--zh-->
在经典模块之前先铺下一件基础设施，因为它不涉经典。诚实性证明跑在成员关系传递闭包的可及性上，而非成员关系本身的可及性上：孩子码坐在节点码之下四步成员关系处，而终止检查器一次只跟一步。闭包把整段下降记在一条推导 `_∈⁺_` 里，由一步关系 `_∈ᵗ_` 一次建成，其可及性从正则搬运过来，并配上直达 Kuratowski 对两个分量的两步链与把链复合到四层深的传递性。
<!--/-->

```agda
private
  data _∈⁺_ : V ℓ → V ℓ → Type (ℓ-suc ℓ) where
    here  : {u v : V ℓ} → u ∈ᵗ v → u ∈⁺ v
    there : {u w v : V ℓ} → u ∈⁺ w → w ∈ᵗ v → u ∈⁺ v

  accTC : (x : V ℓ) → Acc _∈ᵗ_ x → Acc _∈⁺_ x
  goTC  : (x : V ℓ) → Acc _∈ᵗ_ x → (y : V ℓ) → y ∈⁺ x → Acc _∈⁺_ y
  accTC x ax = acc (goTC x ax)
  goTC x (acc r) y (here hy)            = accTC y (r y hy)
  goTC x (acc r) y (there {w = w} p hw) = goTC w (r w hw) y p

  wf⁺ : (x : V ℓ) → Acc _∈⁺_ x
  wf⁺ x = accTC x (regularityV x)

  chainFst : (u v : V ℓ) → u ∈⁺ pr u v
  chainFst u v = there (here ∣ lift false , refl ∣₁) ∣ lift true , refl ∣₁

  chainSnd : (u v : V ℓ) → v ∈⁺ pr u v
  chainSnd u v = there (here ∣ lift true , refl ∣₁) ∣ lift true , refl ∣₁

  trans⁺ : {u w v : V ℓ} → u ∈⁺ w → w ∈⁺ v → u ∈⁺ v
  trans⁺ p (here h)     = there p h
  trans⁺ p (there q h)  = there (trans⁺ p q) h
```

<!--en-->
## The packaged omega
<!--zh-->
## 打包的 ω
<!--/-->

<!--en-->
The branch shapes pin numeral payloads by membership in ω, so the chapter needs
ω as a constant of the object language: an element of the model whose underlying
set is the hierarchy's ω. That ω is constructible is the axiom-of-infinity step,
settled classically by the stage chapter: an ordinal appears at the stage after
itself. This chapter inherits the price exactly as the table chapter's tail
does, so everything below lives in one module under the excluded middle; the
constructibility proof is the choice chapter's one line.
<!--zh-->
分支形状以「属于 ω」钉住数码载荷，故本章需要 ω 作为对象语言的常元：一个模型元素，其底集是层级的 ω。ω 可构造正是无穷公理那一步，由阶段章以经典方式了结：序数现身于自身之后的阶段。本章照表章尾部的方式继承这份代价，故以下一切住进排中律之下的同一个模块；可构造性证明就是选择章的那一行。
<!--/-->

```agda
module WithLEM (lem : LEM (ℓ-suc ℓ)) where
  open import L.Ordinal.Stages {ℓ} lem using ( ord∈Lset-suc )

  private
    ω-isL : ⟨ isL ω ⟩
    ω-isL = Lset→isL (sucV ω) (suc-ord ω-ord) ω (ord∈Lset-suc ω ω-ord)

    ωS : S
    ωS = ω , ω-isL
```

<!--en-->
## The functionality of the annotation table
<!--zh-->
## 注解表的函数性
<!--/-->

<!--en-->
An annotation pairs a code with a numeral, and the certificate will trust it,
so the same code must have at most one annotation. The first conjunct of the
certificate says exactly this: the h-slot is a functional set of pairs. Three
binders pick the argument and the two recorded values, two application readers
read the two pairs out of h, and one object equality forces the values to
agree. The two readings are the model chapter's single-valuedness pair, with
the hypothesis read through the conjunction; per the recorded law they travel
as two directions, never as a path, and each direction's application facts are
transported through the adequacy equation.
<!--zh-->
注解把码与数码配成对，而证书将要信任它，故同一个码至多有一条注解。证书的第一条合取说的恰是这一点：h 槽位是一个函数性的有序对之集。三个绑定子挑出自变量与两个被记录的取值，两条应用读式从 h 中读出两个对，一条对象等式迫使两个取值一致。两个读式是模型章的单值性那一对，假设改经合取读出；按在案定律，它们以两个方向行走，绝不以一条路径，每个方向的应用事实都经适足性等式传输。
<!--/-->

```agda
  private
    sh2 : ∀ {n} → Fin n → Fin (suc (suc n))
    sh2 x = suc (suc x)

    sh3 : ∀ {n} → Fin n → Fin (suc (suc (suc n)))
    sh3 x = suc (suc (suc x))

    sh4 : ∀ {n} → Fin n → Fin (suc (suc (suc (suc n))))
    sh4 x = suc (suc (suc (suc x)))

    sh5 : ∀ {n} → Fin n → Fin (suc (suc (suc (suc (suc n)))))
    sh5 x = suc (suc (suc (suc (suc x))))

    sh6 : ∀ {n} → Fin n → Fin (suc (suc (suc (suc (suc (suc n))))))
    sh6 x = suc (suc (suc (suc (suc (suc x)))))

  FunAt : ∀ {n} → Fin n → Formula S n
  FunAt h = ∀̇ (∀̇ (∀̇ (
      ( appAt (sh3 h) (suc (suc zero)) (suc zero)
      ∧̇ appAt (sh3 h) (suc (suc zero)) zero )
    ⇒̇ (var (suc zero) ≐ var zero) )))

  module _ {n : ℕ} (h : Fin n) (γ : S ^ n) where
    Fun-out : ⟨ γ ⊨ FunAt h ⟩ → (u v v' : S)
            → ⟨ pr (fst u) (fst v) ∈ fst (lookup h γ) ⟩
            → ⟨ pr (fst u) (fst v') ∈ fst (lookup h γ) ⟩
            → fst v ≡ fst v'
    Fun-out f u v v' p q =
      f u v v'
        ( subst ⟨_⟩ (sym (appAt-adequate (sh3 h) (suc (suc zero)) (suc zero)
            (v' ∷ v ∷ u ∷ γ))) p
        , subst ⟨_⟩ (sym (appAt-adequate (sh3 h) (suc (suc zero)) zero
            (v' ∷ v ∷ u ∷ γ))) q )

    Fun-in : ((u v v' : S) → ⟨ pr (fst u) (fst v) ∈ fst (lookup h γ) ⟩
            → ⟨ pr (fst u) (fst v') ∈ fst (lookup h γ) ⟩
            → fst v ≡ fst v')
           → ⟨ γ ⊨ FunAt h ⟩
    Fun-in hstep u v v' p =
      hstep u v v'
        ( subst ⟨_⟩ (appAt-adequate (sh3 h) (suc (suc zero)) (suc zero)
            (v' ∷ v ∷ u ∷ γ)) (p .fst) )
        ( subst ⟨_⟩ (appAt-adequate (sh3 h) (suc (suc zero)) zero
            (v' ∷ v ∷ u ∷ γ)) (p .snd) )
```

<!--en-->
## The certificate branches
<!--zh-->
## 证书分支
<!--/-->

<!--en-->
One frame per constructor, in tag order, each with its meta shape and both
readings, following the node clauses of the table chapter. The shapes are the
certificate's meta-level content: the numeral payloads against ω, the indices
as members of their numerals, the parameter leaf as a member of the carrier,
the children present in the main table, and the annotations agreeing.
<!--zh-->
每构造子一个框架，按标签排序，各带元层形状与双向读式，沿表章的节点子句。形状是证书的元层内容：数码载荷对着 ω，指标作为其数码的成员，参数叶作为载体的成员，孩子在场于主表，注解彼此一致。
<!--/-->

<!--en-->
The allK leaf is the base: x is the pair of tag zero with a numeral payload m,
m is a member of ω, and the pair (x, m) is annotated in h. Its meta shape is
the smallest of the eight: one existential, three conjuncts, and both readings
assemble directly from the tag reader and the application reader, no
composition needed.
<!--zh-->
allK 叶是基底：x 是标签零与数码载荷 m 的对，m 是 ω 的成员，而对 (x, m) 在 h 中被注解。它的元层形状是八个中最小的：一个存在量词、三条合取，两个读式由标签读式与应用读式直接组装，无需复合。
<!--/-->

```agda
  Cert0At : ∀ {n} → Fin n → Fin n → Formula S n
  Cert0At x h = ∃̇
    ( (var zero ∈̇ con ωS)
    ∧̇ ( tagPrAt 0 (suc x) zero
      ∧̇ appAt (suc h) (suc x) zero ) )

  Cert0Of : V ℓ → V ℓ → Type (ℓ-suc ℓ)
  Cert0Of h x = Σ[ mv ∈ S ]
    ( ⟨ fst mv ∈ˢ ω ⟩ × (x ≡ pr (# 0) (fst mv)) × ⟨ pr x (fst mv) ∈ h ⟩ )

  module _ {n : ℕ} (x h : Fin n) (γ : S ^ n) where
    Cert0-out : ⟨ γ ⊨ Cert0At x h ⟩
              → ∥ Cert0Of (fst (lookup h γ)) (fst (lookup x γ)) ∥₁
    Cert0-out = PT.rec PT.squash₁ (λ { (mv , body) → finish mv body })
      where
      finish : (mv : S)
             → ⟨ (mv ∷ γ) ⊨ (var zero ∈̇ con ωS)
                   ∧̇ ( tagPrAt 0 (suc x) zero
                     ∧̇ appAt (suc h) (suc x) zero ) ⟩
             → ∥ Cert0Of (fst (lookup h γ)) (fst (lookup x γ)) ∥₁
      finish mv (h1 , (h2 , h3)) =
        ∣ mv
        , ( h1
          , ( tagPr-out 0 (suc x) zero (mv ∷ γ) h2
            , subst ⟨_⟩ (appAt-adequate (suc h) (suc x) zero (mv ∷ γ)) h3 ) )
        ∣₁

    Cert0-in : Cert0Of (fst (lookup h γ)) (fst (lookup x γ))
             → ⟨ γ ⊨ Cert0At x h ⟩
    Cert0-in (mv , (m∈ω , (qe , eh))) =
      ∣ mv
      , ( m∈ω
        , ( tagPr-in 0 (suc x) zero (mv ∷ γ) qe
          , subst ⟨_⟩ (sym (appAt-adequate (suc h) (suc x) zero (mv ∷ γ))) eh ) )
      ∣₁
```

<!--en-->
The two selection leaves share one frame: the payload is a pair of pairs, so
the tag reader's payload is one intermediate pair value, split twice by the
pair reader into a numeral n and two indices i and j, each a member of n. The
memberships are n against ω and the two indices against n, and the annotation
pairs x with n. The meta shape collapses the intermediates into one composed
equation, exactly as the table chapter's selection leaf does, and both readings
walk the same chain in opposite directions.
<!--zh-->
两条选择叶共用一个框架：载荷是两层对，故标签读式的载荷是一个中间对值，由对读式两次拆成数码 n 与两个指标 i、j，各为 n 的成员。成员关系是 n 对 ω、两个指标对 n，而注解把 x 与 n 配成对。元层形状把中间件塌缩成一条复合等式，恰如表章的选择叶，两个读式沿同一条链反向行走。
<!--/-->

```agda
  module CertSel (tg : ℕ) where
    CertSelAt : ∀ {n} → Fin n → Fin n → Formula S n
    CertSelAt x h = ∃̇ (∃̇ (∃̇ (∃̇ (∃̇
      ( tagPrAt tg (sh5 x) (suc (suc (suc (suc zero))))
      ∧̇ ( prAtL (suc (suc (suc (suc zero)))) (suc (suc zero))
            (suc (suc (suc zero)))
      ∧̇ ( prAtL (suc (suc (suc zero))) (suc zero) zero
      ∧̇ ( (var (suc (suc zero)) ∈̇ con ωS)
      ∧̇ ( (var (suc zero) ∈̇ var (suc (suc zero)))
      ∧̇ ( (var zero ∈̇ var (suc (suc zero)))
      ∧̇ appAt (sh5 h) (sh5 x) (suc (suc zero)) ))))))))))

    CertSelOf : V ℓ → V ℓ → Type (ℓ-suc ℓ)
    CertSelOf h x = Σ[ nv ∈ S ] Σ[ iv ∈ S ] Σ[ jv ∈ S ]
      ( ⟨ fst nv ∈ˢ ω ⟩ × ⟨ fst iv ∈ˢ fst nv ⟩ × ⟨ fst jv ∈ˢ fst nv ⟩
      × (x ≡ pr (# tg) (pr (fst nv) (pr (fst iv) (fst jv))))
      × ⟨ pr x (fst nv) ∈ h ⟩ )

    module _ {n : ℕ} (x h : Fin n) (γ : S ^ n) where
      CertSel-out : ⟨ γ ⊨ CertSelAt x h ⟩
                  → ∥ CertSelOf (fst (lookup h γ)) (fst (lookup x γ)) ∥₁
      CertSel-out =
        PT.rec PT.squash₁ (λ { (p₁ , w₁) →
        PT.rec PT.squash₁ (λ { (p₂ , w₂) →
        PT.rec PT.squash₁ (λ { (nv , w₃) →
        PT.rec PT.squash₁ (λ { (iv , w₄) →
        PT.rec PT.squash₁ (λ { (jv , body) → finish p₁ p₂ nv iv jv body })
        w₄ }) w₃ }) w₂ }) w₁ })
        where
        finish : (p₁ p₂ nv iv jv : S)
               → ⟨ (jv ∷ iv ∷ nv ∷ p₂ ∷ p₁ ∷ γ)
                     ⊨ ( tagPrAt tg (sh5 x) (suc (suc (suc (suc zero))))
                       ∧̇ ( prAtL (suc (suc (suc (suc zero)))) (suc (suc zero))
                             (suc (suc (suc zero)))
                       ∧̇ ( prAtL (suc (suc (suc zero))) (suc zero) zero
                       ∧̇ ( (var (suc (suc zero)) ∈̇ con ωS)
                       ∧̇ ( (var (suc zero) ∈̇ var (suc (suc zero)))
                       ∧̇ ( (var zero ∈̇ var (suc (suc zero)))
                       ∧̇ appAt (sh5 h) (sh5 x) (suc (suc zero)) )))))) ⟩
               → ∥ CertSelOf (fst (lookup h γ)) (fst (lookup x γ)) ∥₁
        finish p₁ p₂ nv iv jv (h1 , (h2 , (h3 , (h4 , (h5 , (h6 , h7)))))) =
          ∣ nv , iv , jv ,
            ( h4
            , ( h5
              , ( h6
                , ( ( tagPr-out tg (sh5 x) (suc (suc (suc (suc zero)))) env h1
                    ∙ cong (pr (# tg))
                        ( subst ⟨_⟩ (prAtL-adequate (suc (suc (suc (suc zero))))
                            (suc (suc zero)) (suc (suc (suc zero))) env) h2
                        ∙ cong (pr (fst nv))
                            (subst ⟨_⟩ (prAtL-adequate (suc (suc (suc zero)))
                              (suc zero) zero env) h3) ) )
                  , subst ⟨_⟩ (appAt-adequate (sh5 h) (sh5 x)
                      (suc (suc zero)) env) h7 ) ) ) ) ∣₁
          where
          env : S ^ (suc (suc (suc (suc (suc n)))))
          env = jv ∷ iv ∷ nv ∷ p₂ ∷ p₁ ∷ γ

      CertSel-in : CertSelOf (fst (lookup h γ)) (fst (lookup x γ))
                 → ⟨ γ ⊨ CertSelAt x h ⟩
      CertSel-in (nv , iv , jv , (n∈ω , (i∈n , (j∈n , (qe , eh))))) =
        ∣ prʟ nv (prʟ iv jv) , ∣ prʟ iv jv , ∣ nv , ∣ iv , ∣ jv ,
          ( tagPr-in tg (sh5 x) (suc (suc (suc (suc zero)))) env
              (qe ∙ cong (pr (# tg))
                (sym ( prʟ-fst nv (prʟ iv jv)
                     ∙ cong (pr (fst nv)) (prʟ-fst iv jv) )))
          , ( subst ⟨_⟩ (sym (prAtL-adequate (suc (suc (suc (suc zero))))
                (suc (suc zero)) (suc (suc (suc zero))) env))
                (prʟ-fst nv (prʟ iv jv))
          , ( subst ⟨_⟩ (sym (prAtL-adequate (suc (suc (suc zero)))
                (suc zero) zero env)) (prʟ-fst iv jv)
          , ( n∈ω
            , ( i∈n
              , ( j∈n
                , subst ⟨_⟩ (sym (appAt-adequate (sh5 h) (sh5 x)
                    (suc (suc zero)) env)) eh ) ) ) ) ) )
        ∣₁ ∣₁ ∣₁ ∣₁ ∣₁
        where
        env : S ^ (suc (suc (suc (suc (suc n)))))
        env = jv ∷ iv ∷ nv ∷ prʟ iv jv ∷ prʟ nv (prʟ iv jv) ∷ γ

  module CertSelMem = CertSel 1
  module CertSelEq = CertSel 2
```

<!--en-->
The constant selection leaf is the selection shape with the second index
replaced by a parameter: the payload splits into a numeral n, an index i inside
n, and a member p of the carrier a. The memberships are n against ω, i against
n, and p against the carrier; the annotation still pairs x with n.
<!--zh-->
常量选择叶把选择形状的第二个指标换成参数：载荷拆成数码 n、n 内的指标 i 与载体 a 的成员 p。成员关系是 n 对 ω、i 对 n、p 对载体；注解仍把 x 与 n 配成对。
<!--/-->

```agda
  Cert3At : ∀ {n} → Fin n → Fin n → Fin n → Formula S n
  Cert3At x h a = ∃̇ (∃̇ (∃̇ (∃̇ (∃̇
    ( tagPrAt 3 (sh5 x) (suc (suc (suc (suc zero))))
    ∧̇ ( prAtL (suc (suc (suc (suc zero)))) (suc (suc zero))
          (suc (suc (suc zero)))
    ∧̇ ( prAtL (suc (suc (suc zero))) (suc zero) zero
    ∧̇ ( (var (suc (suc zero)) ∈̇ con ωS)
    ∧̇ ( (var (suc zero) ∈̇ var (suc (suc zero)))
    ∧̇ ( (var zero ∈̇ var (sh5 a))
    ∧̇ appAt (sh5 h) (sh5 x) (suc (suc zero)) ))))))))))

  Cert3Of : V ℓ → V ℓ → V ℓ → Type (ℓ-suc ℓ)
  Cert3Of a h x = Σ[ nv ∈ S ] Σ[ iv ∈ S ] Σ[ pv ∈ S ]
    ( ⟨ fst nv ∈ˢ ω ⟩ × ⟨ fst iv ∈ˢ fst nv ⟩ × ⟨ fst pv ∈ˢ a ⟩
    × (x ≡ pr (# 3) (pr (fst nv) (pr (fst iv) (fst pv))))
    × ⟨ pr x (fst nv) ∈ h ⟩ )

  module _ {n : ℕ} (x h a : Fin n) (γ : S ^ n) where
    Cert3-out : ⟨ γ ⊨ Cert3At x h a ⟩
              → ∥ Cert3Of (fst (lookup a γ)) (fst (lookup h γ))
                    (fst (lookup x γ)) ∥₁
    Cert3-out =
      PT.rec PT.squash₁ (λ { (p₁ , w₁) →
      PT.rec PT.squash₁ (λ { (p₂ , w₂) →
      PT.rec PT.squash₁ (λ { (nv , w₃) →
      PT.rec PT.squash₁ (λ { (iv , w₄) →
      PT.rec PT.squash₁ (λ { (pv , body) → finish p₁ p₂ nv iv pv body })
      w₄ }) w₃ }) w₂ }) w₁ })
      where
      finish : (p₁ p₂ nv iv pv : S)
             → ⟨ (pv ∷ iv ∷ nv ∷ p₂ ∷ p₁ ∷ γ)
                   ⊨ ( tagPrAt 3 (sh5 x) (suc (suc (suc (suc zero))))
                     ∧̇ ( prAtL (suc (suc (suc (suc zero)))) (suc (suc zero))
                           (suc (suc (suc zero)))
                     ∧̇ ( prAtL (suc (suc (suc zero))) (suc zero) zero
                     ∧̇ ( (var (suc (suc zero)) ∈̇ con ωS)
                     ∧̇ ( (var (suc zero) ∈̇ var (suc (suc zero)))
                     ∧̇ ( (var zero ∈̇ var (sh5 a))
                     ∧̇ appAt (sh5 h) (sh5 x) (suc (suc zero)) )))))) ⟩
             → ∥ Cert3Of (fst (lookup a γ)) (fst (lookup h γ))
                   (fst (lookup x γ)) ∥₁
      finish p₁ p₂ nv iv pv (h1 , (h2 , (h3 , (h4 , (h5 , (h6 , h7)))))) =
        ∣ nv , iv , pv ,
          ( h4
          , ( h5
            , ( h6
              , ( ( tagPr-out 3 (sh5 x) (suc (suc (suc (suc zero)))) env h1
                  ∙ cong (pr (# 3))
                      ( subst ⟨_⟩ (prAtL-adequate (suc (suc (suc (suc zero))))
                          (suc (suc zero)) (suc (suc (suc zero))) env) h2
                      ∙ cong (pr (fst nv))
                          (subst ⟨_⟩ (prAtL-adequate (suc (suc (suc zero)))
                            (suc zero) zero env) h3) ) )
                , subst ⟨_⟩ (appAt-adequate (sh5 h) (sh5 x)
                    (suc (suc zero)) env) h7 ) ) ) ) ∣₁
        where
        env : S ^ (suc (suc (suc (suc (suc n)))))
        env = pv ∷ iv ∷ nv ∷ p₂ ∷ p₁ ∷ γ

    Cert3-in : Cert3Of (fst (lookup a γ)) (fst (lookup h γ))
                 (fst (lookup x γ))
             → ⟨ γ ⊨ Cert3At x h a ⟩
    Cert3-in (nv , iv , pv , (n∈ω , (i∈n , (p∈a , (qe , eh))))) =
      ∣ prʟ nv (prʟ iv pv) , ∣ prʟ iv pv , ∣ nv , ∣ iv , ∣ pv ,
        ( tagPr-in 3 (sh5 x) (suc (suc (suc (suc zero)))) env
            (qe ∙ cong (pr (# 3))
              (sym ( prʟ-fst nv (prʟ iv pv)
                   ∙ cong (pr (fst nv)) (prʟ-fst iv pv) )))
        , ( subst ⟨_⟩ (sym (prAtL-adequate (suc (suc (suc (suc zero))))
              (suc (suc zero)) (suc (suc (suc zero))) env))
              (prʟ-fst nv (prʟ iv pv))
        , ( subst ⟨_⟩ (sym (prAtL-adequate (suc (suc (suc zero)))
              (suc zero) zero env)) (prʟ-fst iv pv)
        , ( n∈ω
          , ( i∈n
            , ( p∈a
              , subst ⟨_⟩ (sym (appAt-adequate (sh5 h) (sh5 x)
                  (suc (suc zero)) env)) eh ) ) ) ) ) )
      ∣₁ ∣₁ ∣₁ ∣₁ ∣₁
      where
      env : S ^ (suc (suc (suc (suc (suc n)))))
      env = pv ∷ iv ∷ nv ∷ prʟ iv pv ∷ prʟ nv (prʟ iv pv) ∷ γ
```

<!--en-->
The two binary nodes share one frame: the payload is the pair of the children's
codes, read as one intermediate pair value, then split; a numeral m is a member
of ω; the children are present in the main table with their values; and the
annotations agree, x with m and each child with the same m. The meta shape
keeps the equation for x composed and the five V-facts flat, mirroring the node
clause's shape.
<!--zh-->
两条二元节点共用一个框架：载荷是两个孩子码的对，作为一个中间对值读出、再行拆开；数码 m 是 ω 的成员；孩子连同取值在场于主表；注解彼此一致，x 对 m、每个孩子对同一个 m。元层形状把 x 的等式保持复合、五个 V 事实平放，镜像节点子句的形状。
<!--/-->

```agda
  module CertBin (tg : ℕ) where
    CertBinAt : ∀ {n} → Fin n → Fin n → Fin n → Formula S n
    CertBinAt x g h = ∃̇ (∃̇ (∃̇ (∃̇ (∃̇ (∃̇
      ( tagPrAt tg (sh6 x) (suc (suc (suc (suc (suc zero)))))
      ∧̇ ( prAtL (suc (suc (suc (suc (suc zero)))))
            (suc (suc (suc (suc zero)))) (suc (suc (suc zero)))
      ∧̇ ( (var (suc (suc zero)) ∈̇ con ωS)
      ∧̇ ( appAt (sh6 g) (suc (suc (suc (suc zero)))) (suc zero)
      ∧̇ ( appAt (sh6 g) (suc (suc (suc zero))) zero
      ∧̇ ( appAt (sh6 h) (sh6 x) (suc (suc zero))
      ∧̇ ( appAt (sh6 h) (suc (suc (suc (suc zero)))) (suc (suc zero))
      ∧̇ appAt (sh6 h) (suc (suc (suc zero))) (suc (suc zero)) ))))))))))))

    CertBinOf : V ℓ → V ℓ → V ℓ → Type (ℓ-suc ℓ)
    CertBinOf g h x = Σ[ c₁ ∈ S ] Σ[ c₂ ∈ S ] Σ[ mv ∈ S ] Σ[ y₁ ∈ S ] Σ[ y₂ ∈ S ]
      ( (x ≡ pr (# tg) (pr (fst c₁) (fst c₂)))
      × ( ⟨ fst mv ∈ˢ ω ⟩
      × ( ⟨ pr (fst c₁) (fst y₁) ∈ g ⟩
      × ( ⟨ pr (fst c₂) (fst y₂) ∈ g ⟩
      × ( ⟨ pr x (fst mv) ∈ h ⟩
      × ( ⟨ pr (fst c₁) (fst mv) ∈ h ⟩
        × ⟨ pr (fst c₂) (fst mv) ∈ h ⟩ ))))))

    module _ {n : ℕ} (x g h : Fin n) (γ : S ^ n) where
      CertBin-out : ⟨ γ ⊨ CertBinAt x g h ⟩
                  → ∥ CertBinOf (fst (lookup g γ)) (fst (lookup h γ))
                        (fst (lookup x γ)) ∥₁
      CertBin-out =
        PT.rec PT.squash₁ (λ { (p₁ , w₁) →
        PT.rec PT.squash₁ (λ { (c₁ , w₂) →
        PT.rec PT.squash₁ (λ { (c₂ , w₃) →
        PT.rec PT.squash₁ (λ { (mv , w₄) →
        PT.rec PT.squash₁ (λ { (y₁ , w₅) →
        PT.rec PT.squash₁ (λ { (y₂ , body) → finish p₁ c₁ c₂ mv y₁ y₂ body })
        w₅ }) w₄ }) w₃ }) w₂ }) w₁ })
        where
        finish : (p₁ c₁ c₂ mv y₁ y₂ : S)
               → ⟨ (y₂ ∷ y₁ ∷ mv ∷ c₂ ∷ c₁ ∷ p₁ ∷ γ)
                     ⊨ ( tagPrAt tg (sh6 x) (suc (suc (suc (suc (suc zero)))))
                       ∧̇ ( prAtL (suc (suc (suc (suc (suc zero)))))
                             (suc (suc (suc (suc zero)))) (suc (suc (suc zero)))
                       ∧̇ ( (var (suc (suc zero)) ∈̇ con ωS)
                       ∧̇ ( appAt (sh6 g) (suc (suc (suc (suc zero)))) (suc zero)
                       ∧̇ ( appAt (sh6 g) (suc (suc (suc zero))) zero
                       ∧̇ ( appAt (sh6 h) (sh6 x) (suc (suc zero))
                       ∧̇ ( appAt (sh6 h) (suc (suc (suc (suc zero))))
                             (suc (suc zero))
                       ∧̇ appAt (sh6 h) (suc (suc (suc zero))) (suc (suc zero))
                            ))))))) ⟩
               → ∥ CertBinOf (fst (lookup g γ)) (fst (lookup h γ))
                     (fst (lookup x γ)) ∥₁
        finish p₁ c₁ c₂ mv y₁ y₂ (h1 , (h2 , (h3 , (h4 , (h5 , (h6 , (h7 , h8))))))) =
          ∣ c₁ , c₂ , mv , y₁ , y₂ ,
            ( ( tagPr-out tg (sh6 x) (suc (suc (suc (suc (suc zero))))) env h1
                ∙ cong (pr (# tg))
                    (subst ⟨_⟩ (prAtL-adequate (suc (suc (suc (suc (suc zero)))))
                      (suc (suc (suc (suc zero)))) (suc (suc (suc zero))) env) h2) )
            , ( h3
              , ( subst ⟨_⟩ (appAt-adequate (sh6 g)
                    (suc (suc (suc (suc zero)))) (suc zero) env) h4
                , ( subst ⟨_⟩ (appAt-adequate (sh6 g)
                      (suc (suc (suc zero))) zero env) h5
                  , ( subst ⟨_⟩ (appAt-adequate (sh6 h) (sh6 x)
                        (suc (suc zero)) env) h6
                    , ( subst ⟨_⟩ (appAt-adequate (sh6 h)
                          (suc (suc (suc (suc zero)))) (suc (suc zero)) env) h7
                      , subst ⟨_⟩ (appAt-adequate (sh6 h)
                          (suc (suc (suc zero))) (suc (suc zero)) env) h8 ) ) ) ) ) ) ∣₁
          where
          env : S ^ (suc (suc (suc (suc (suc (suc n))))))
          env = y₂ ∷ y₁ ∷ mv ∷ c₂ ∷ c₁ ∷ p₁ ∷ γ

      CertBin-in : CertBinOf (fst (lookup g γ)) (fst (lookup h γ))
                     (fst (lookup x γ))
                 → ⟨ γ ⊨ CertBinAt x g h ⟩
      CertBin-in (c₁ , c₂ , mv , y₁ , y₂ , (qe , (m∈ω , (e1 , (e2 , (e3 , (e4 , e5))))))) =
        ∣ prʟ c₁ c₂ , ∣ c₁ , ∣ c₂ , ∣ mv , ∣ y₁ , ∣ y₂ ,
          ( tagPr-in tg (sh6 x) (suc (suc (suc (suc (suc zero))))) env
              (qe ∙ cong (pr (# tg)) (sym (prʟ-fst c₁ c₂)))
          , ( subst ⟨_⟩ (sym (prAtL-adequate (suc (suc (suc (suc (suc zero)))))
                (suc (suc (suc (suc zero)))) (suc (suc (suc zero))) env))
                (prʟ-fst c₁ c₂)
          , ( m∈ω
            , ( subst ⟨_⟩ (sym (appAt-adequate (sh6 g)
                  (suc (suc (suc (suc zero)))) (suc zero) env)) e1
              , ( subst ⟨_⟩ (sym (appAt-adequate (sh6 g)
                    (suc (suc (suc zero))) zero env)) e2
                , ( subst ⟨_⟩ (sym (appAt-adequate (sh6 h) (sh6 x)
                      (suc (suc zero)) env)) e3
                  , ( subst ⟨_⟩ (sym (appAt-adequate (sh6 h)
                        (suc (suc (suc (suc zero)))) (suc (suc zero)) env)) e4
                    , subst ⟨_⟩ (sym (appAt-adequate (sh6 h)
                        (suc (suc (suc zero))) (suc (suc zero)) env)) e5 ) ) ) ) ) ) )
        ∣₁ ∣₁ ∣₁ ∣₁ ∣₁ ∣₁
        where
        env : S ^ (suc (suc (suc (suc (suc (suc n))))))
        env = y₂ ∷ y₁ ∷ mv ∷ c₂ ∷ c₁ ∷ prʟ c₁ c₂ ∷ γ

  module CertBin4 = CertBin 4
  module CertBin5 = CertBin 5
```

<!--en-->
The complement node is the unary sibling: the payload splits into a numeral n
and a child code c, the child is present in the main table with its value, and
the annotations agree, x with n and the child with the same n.
<!--zh-->
补节点是一元的同胞：载荷拆成数码 n 与孩子码 c，孩子连同取值在场于主表，注解彼此一致，x 对 n、孩子对同一个 n。
<!--/-->

```agda
  Cert6At : ∀ {n} → Fin n → Fin n → Fin n → Formula S n
  Cert6At x g h = ∃̇ (∃̇ (∃̇ (∃̇
    ( tagPrAt 6 (sh4 x) (suc (suc (suc zero)))
    ∧̇ ( prAtL (suc (suc (suc zero))) (suc (suc zero)) (suc zero)
    ∧̇ ( (var (suc (suc zero)) ∈̇ con ωS)
    ∧̇ ( appAt (sh4 g) (suc zero) zero
    ∧̇ ( appAt (sh4 h) (sh4 x) (suc (suc zero))
    ∧̇ appAt (sh4 h) (suc zero) (suc (suc zero)) ))))))))

  Cert6Of : V ℓ → V ℓ → V ℓ → Type (ℓ-suc ℓ)
  Cert6Of g h x = Σ[ nv ∈ S ] Σ[ cv ∈ S ] Σ[ yv ∈ S ]
    ( ⟨ fst nv ∈ˢ ω ⟩
    × (x ≡ pr (# 6) (pr (fst nv) (fst cv)))
    × ( ⟨ pr (fst cv) (fst yv) ∈ g ⟩
    × ( ⟨ pr x (fst nv) ∈ h ⟩
      × ⟨ pr (fst cv) (fst nv) ∈ h ⟩ )))

  module _ {n : ℕ} (x g h : Fin n) (γ : S ^ n) where
    Cert6-out : ⟨ γ ⊨ Cert6At x g h ⟩
              → ∥ Cert6Of (fst (lookup g γ)) (fst (lookup h γ))
                    (fst (lookup x γ)) ∥₁
    Cert6-out =
      PT.rec PT.squash₁ (λ { (p₁ , w₁) →
      PT.rec PT.squash₁ (λ { (nv , w₂) →
      PT.rec PT.squash₁ (λ { (cv , w₃) →
      PT.rec PT.squash₁ (λ { (yv , body) → finish p₁ nv cv yv body })
      w₃ }) w₂ }) w₁ })
      where
      finish : (p₁ nv cv yv : S)
             → ⟨ (yv ∷ cv ∷ nv ∷ p₁ ∷ γ)
                   ⊨ ( tagPrAt 6 (sh4 x) (suc (suc (suc zero)))
                     ∧̇ ( prAtL (suc (suc (suc zero))) (suc (suc zero)) (suc zero)
                     ∧̇ ( (var (suc (suc zero)) ∈̇ con ωS)
                     ∧̇ ( appAt (sh4 g) (suc zero) zero
                     ∧̇ ( appAt (sh4 h) (sh4 x) (suc (suc zero))
                     ∧̇ appAt (sh4 h) (suc zero) (suc (suc zero)) ))))) ⟩
             → ∥ Cert6Of (fst (lookup g γ)) (fst (lookup h γ))
                   (fst (lookup x γ)) ∥₁
      finish p₁ nv cv yv (h1 , (h2 , (h3 , (h4 , (h5 , h6))))) =
        ∣ nv , cv , yv ,
          ( h3
          , ( ( tagPr-out 6 (sh4 x) (suc (suc (suc zero))) env h1
              ∙ cong (pr (# 6))
                  (subst ⟨_⟩ (prAtL-adequate (suc (suc (suc zero)))
                    (suc (suc zero)) (suc zero) env) h2) )
          , ( subst ⟨_⟩ (appAt-adequate (sh4 g) (suc zero) zero env) h4
            , ( subst ⟨_⟩ (appAt-adequate (sh4 h) (sh4 x) (suc (suc zero)) env) h5
              , subst ⟨_⟩ (appAt-adequate (sh4 h) (suc zero) (suc (suc zero)) env) h6 ) ) ) ) ∣₁
        where
        env : S ^ (suc (suc (suc (suc n))))
        env = yv ∷ cv ∷ nv ∷ p₁ ∷ γ

    Cert6-in : Cert6Of (fst (lookup g γ)) (fst (lookup h γ))
                 (fst (lookup x γ))
             → ⟨ γ ⊨ Cert6At x g h ⟩
    Cert6-in (nv , cv , yv , (n∈ω , (qe , (e1 , (e2 , e3))))) =
      ∣ prʟ nv cv , ∣ nv , ∣ cv , ∣ yv ,
        ( tagPr-in 6 (sh4 x) (suc (suc (suc zero))) env
            (qe ∙ cong (pr (# 6)) (sym (prʟ-fst nv cv)))
        , ( subst ⟨_⟩ (sym (prAtL-adequate (suc (suc (suc zero)))
              (suc (suc zero)) (suc zero) env)) (prʟ-fst nv cv)
        , ( n∈ω
          , ( subst ⟨_⟩ (sym (appAt-adequate (sh4 g) (suc zero) zero env)) e1
            , ( subst ⟨_⟩ (sym (appAt-adequate (sh4 h) (sh4 x)
                  (suc (suc zero)) env)) e2
              , subst ⟨_⟩ (sym (appAt-adequate (sh4 h) (suc zero)
                  (suc (suc zero)) env)) e3 ) ) ) ) )
      ∣₁ ∣₁ ∣₁ ∣₁
      where
      env : S ^ (suc (suc (suc (suc n))))
      env = yv ∷ cv ∷ nv ∷ prʟ nv cv ∷ γ
```

<!--en-->
The shift is the one branch whose annotation is not the shared numeral itself:
x is the pair of tag seven with a child code c, a numeral m is a member of ω,
and the child's annotation is the internal successor of m, read by the
successor atom, while the shift's own annotation is m. The meta shape therefore
records the m'-value as sucV of the m-value.
<!--zh-->
移位是注解并非共享数码本身的那一个分支：x 是标签七与孩子码 c 的对，数码 m 是 ω 的成员，孩子的注解是 m 的内层后继，由后继原子读出，而移位自身的注解是 m。元层形状因此把 m′ 的取值记为 m 取值的 sucV。
<!--/-->

```agda
  Cert7At : ∀ {n} → Fin n → Fin n → Fin n → Formula S n
  Cert7At x g h = ∃̇ (∃̇ (∃̇ (∃̇
    ( tagPrAt 7 (sh4 x) (suc (suc (suc zero)))
    ∧̇ ( (var (suc (suc zero)) ∈̇ con ωS)
    ∧̇ ( sucAtL (suc (suc zero)) (suc zero)
    ∧̇ ( appAt (sh4 g) (suc (suc (suc zero))) zero
    ∧̇ ( appAt (sh4 h) (sh4 x) (suc (suc zero))
    ∧̇ appAt (sh4 h) (suc (suc (suc zero))) (suc zero) ))))))))

  Cert7Of : V ℓ → V ℓ → V ℓ → Type (ℓ-suc ℓ)
  Cert7Of g h x = Σ[ cv ∈ S ] Σ[ mv ∈ S ] Σ[ mv' ∈ S ] Σ[ yv ∈ S ]
    ( (x ≡ pr (# 7) (fst cv))
    × ( ⟨ fst mv ∈ˢ ω ⟩
    × ( (fst mv' ≡ sucV (fst mv))
    × ( ⟨ pr (fst cv) (fst yv) ∈ g ⟩
    × ( ⟨ pr x (fst mv) ∈ h ⟩
      × ⟨ pr (fst cv) (fst mv') ∈ h ⟩ )))))

  module _ {n : ℕ} (x g h : Fin n) (γ : S ^ n) where
    Cert7-out : ⟨ γ ⊨ Cert7At x g h ⟩
              → ∥ Cert7Of (fst (lookup g γ)) (fst (lookup h γ))
                    (fst (lookup x γ)) ∥₁
    Cert7-out =
      PT.rec PT.squash₁ (λ { (cv , w₁) →
      PT.rec PT.squash₁ (λ { (mv , w₂) →
      PT.rec PT.squash₁ (λ { (mv' , w₃) →
      PT.rec PT.squash₁ (λ { (yv , body) → finish cv mv mv' yv body })
      w₃ }) w₂ }) w₁ })
      where
      finish : (cv mv mv' yv : S)
             → ⟨ (yv ∷ mv' ∷ mv ∷ cv ∷ γ)
                   ⊨ ( tagPrAt 7 (sh4 x) (suc (suc (suc zero)))
                     ∧̇ ( (var (suc (suc zero)) ∈̇ con ωS)
                     ∧̇ ( sucAtL (suc (suc zero)) (suc zero)
                     ∧̇ ( appAt (sh4 g) (suc (suc (suc zero))) zero
                     ∧̇ ( appAt (sh4 h) (sh4 x) (suc (suc zero))
                     ∧̇ appAt (sh4 h) (suc (suc (suc zero))) (suc zero) ))))) ⟩
             → ∥ Cert7Of (fst (lookup g γ)) (fst (lookup h γ))
                   (fst (lookup x γ)) ∥₁
      finish cv mv mv' yv (h1 , (h2 , (h3 , (h4 , (h5 , h6))))) =
        ∣ cv , mv , mv' , yv ,
          ( tagPr-out 7 (sh4 x) (suc (suc (suc zero))) env h1
          , ( h2
            , ( subst ⟨_⟩ (sucAtL-adequate (suc (suc zero)) (suc zero) env) h3
              , ( subst ⟨_⟩ (appAt-adequate (sh4 g) (suc (suc (suc zero))) zero env) h4
                , ( subst ⟨_⟩ (appAt-adequate (sh4 h) (sh4 x) (suc (suc zero)) env) h5
                  , subst ⟨_⟩ (appAt-adequate (sh4 h) (suc (suc (suc zero)))
                      (suc zero) env) h6 ) ) ) ) ) ∣₁
        where
        env : S ^ (suc (suc (suc (suc n))))
        env = yv ∷ mv' ∷ mv ∷ cv ∷ γ

    Cert7-in : Cert7Of (fst (lookup g γ)) (fst (lookup h γ))
                 (fst (lookup x γ))
             → ⟨ γ ⊨ Cert7At x g h ⟩
    Cert7-in (cv , mv , mv' , yv , (qe , (m∈ω , (qq , (e1 , (e2 , e3)))))) =
      ∣ cv , ∣ mv , ∣ mv' , ∣ yv ,
        ( tagPr-in 7 (sh4 x) (suc (suc (suc zero))) env qe
        , ( m∈ω
          , ( subst ⟨_⟩ (sym (sucAtL-adequate (suc (suc zero)) (suc zero) env)) qq
            , ( subst ⟨_⟩ (sym (appAt-adequate (sh4 g) (suc (suc (suc zero))) zero env)) e1
              , ( subst ⟨_⟩ (sym (appAt-adequate (sh4 h) (sh4 x)
                    (suc (suc zero)) env)) e2
                , subst ⟨_⟩ (sym (appAt-adequate (sh4 h) (suc (suc (suc zero)))
                    (suc zero) env)) e3 ) ) ) ) )
      ∣₁ ∣₁ ∣₁ ∣₁
      where
      env : S ^ (suc (suc (suc (suc n))))
      env = yv ∷ mv' ∷ mv ∷ cv ∷ γ
```

<!--en-->
## The disjunction
<!--zh-->
## 析取
<!--/-->

<!--en-->
Eight shapes, one disjunction, in tag order, with the same right-nested
associativity as the table chapter's clause. The outward reader peels the
disjunction and hands each branch to its own reader; the eight injections are
what the certificate uses on the way in, one per branch; and the inward reader
dispatches the meta shape back to the disjunction through the injections, so
the certificate can assemble satisfaction from a shape.
<!--zh-->
八个形状，一个析取，按标签排序，与表章子句同样的右嵌套结合。向外的读式剥开析取，把每个分支递给自己的读式；八个注入是证书进入方向将使用的东西，每分支一个；向内的读式把元层形状经注入分发回析取，使证书能从形状装配满足。
<!--/-->

```agda
  CertShapeAt : ∀ {n} → Fin n → Fin n → Fin n → Fin n → Formula S n
  CertShapeAt x g h a =
    Cert0At x h
    ∨̇ ( CertSelMem.CertSelAt x h
    ∨̇ ( CertSelEq.CertSelAt x h
    ∨̇ ( Cert3At x h a
    ∨̇ ( CertBin4.CertBinAt x g h
    ∨̇ ( CertBin5.CertBinAt x g h
    ∨̇ ( Cert6At x g h
      ∨̇ Cert7At x g h ))))))

  CertOf : V ℓ → V ℓ → V ℓ → V ℓ → Type (ℓ-suc ℓ)
  CertOf a g h x =
    Cert0Of h x
    ⊎ ( CertSelMem.CertSelOf h x
    ⊎ ( CertSelEq.CertSelOf h x
    ⊎ ( Cert3Of a h x
    ⊎ ( CertBin4.CertBinOf g h x
    ⊎ ( CertBin5.CertBinOf g h x
    ⊎ ( Cert6Of g h x
      ⊎ Cert7Of g h x ))))))

  module _ {n : ℕ} (x g h a : Fin n) (γ : S ^ n) where
    CertShape-out : ⟨ γ ⊨ CertShapeAt x g h a ⟩
                  → ∥ CertOf (fst (lookup a γ)) (fst (lookup g γ))
                        (fst (lookup h γ)) (fst (lookup x γ)) ∥₁
    CertShape-out = PT.rec PT.squash₁ br₁
      where
      br₈ : ⟨ γ ⊨ Cert6At x g h ⟩ ⊎ ⟨ γ ⊨ Cert7At x g h ⟩
          → ∥ CertOf (fst (lookup a γ)) (fst (lookup g γ))
                (fst (lookup h γ)) (fst (lookup x γ)) ∥₁
      br₈ (inl p) = PT.map (λ c → inr (inr (inr (inr (inr (inr (inl c)))))))
        (Cert6-out x g h γ p)
      br₈ (inr p) = PT.map (λ c → inr (inr (inr (inr (inr (inr (inr c)))))))
        (Cert7-out x g h γ p)
      br₇ : ⟨ γ ⊨ CertBin5.CertBinAt x g h ⟩
          ⊎ ⟨ γ ⊨ (Cert6At x g h ∨̇ Cert7At x g h) ⟩
          → ∥ CertOf (fst (lookup a γ)) (fst (lookup g γ))
                (fst (lookup h γ)) (fst (lookup x γ)) ∥₁
      br₇ (inl p) = PT.map (λ c → inr (inr (inr (inr (inr (inl c))))))
        (CertBin5.CertBin-out x g h γ p)
      br₇ (inr r) = PT.rec PT.squash₁ br₈ r
      br₆ : ⟨ γ ⊨ CertBin4.CertBinAt x g h ⟩
          ⊎ ⟨ γ ⊨ (CertBin5.CertBinAt x g h
                ∨̇ (Cert6At x g h ∨̇ Cert7At x g h)) ⟩
          → ∥ CertOf (fst (lookup a γ)) (fst (lookup g γ))
                (fst (lookup h γ)) (fst (lookup x γ)) ∥₁
      br₆ (inl p) = PT.map (λ c → inr (inr (inr (inr (inl c)))))
        (CertBin4.CertBin-out x g h γ p)
      br₆ (inr r) = PT.rec PT.squash₁ br₇ r
      br₅ : ⟨ γ ⊨ Cert3At x h a ⟩
          ⊎ ⟨ γ ⊨ (CertBin4.CertBinAt x g h
                ∨̇ (CertBin5.CertBinAt x g h
                ∨̇ (Cert6At x g h ∨̇ Cert7At x g h))) ⟩
          → ∥ CertOf (fst (lookup a γ)) (fst (lookup g γ))
                (fst (lookup h γ)) (fst (lookup x γ)) ∥₁
      br₅ (inl p) = PT.map (λ c → inr (inr (inr (inl c))))
        (Cert3-out x h a γ p)
      br₅ (inr r) = PT.rec PT.squash₁ br₆ r
      br₄ : ⟨ γ ⊨ CertSelEq.CertSelAt x h ⟩
          ⊎ ⟨ γ ⊨ (Cert3At x h a
                ∨̇ (CertBin4.CertBinAt x g h
                ∨̇ (CertBin5.CertBinAt x g h
                ∨̇ (Cert6At x g h ∨̇ Cert7At x g h)))) ⟩
          → ∥ CertOf (fst (lookup a γ)) (fst (lookup g γ))
                (fst (lookup h γ)) (fst (lookup x γ)) ∥₁
      br₄ (inl p) = PT.map (λ c → inr (inr (inl c)))
        (CertSelEq.CertSel-out x h γ p)
      br₄ (inr r) = PT.rec PT.squash₁ br₅ r
      br₃ : ⟨ γ ⊨ CertSelMem.CertSelAt x h ⟩
          ⊎ ⟨ γ ⊨ (CertSelEq.CertSelAt x h
                ∨̇ (Cert3At x h a
                ∨̇ (CertBin4.CertBinAt x g h
                ∨̇ (CertBin5.CertBinAt x g h
                ∨̇ (Cert6At x g h ∨̇ Cert7At x g h))))) ⟩
          → ∥ CertOf (fst (lookup a γ)) (fst (lookup g γ))
                (fst (lookup h γ)) (fst (lookup x γ)) ∥₁
      br₃ (inl p) = PT.map (λ c → inr (inl c))
        (CertSelMem.CertSel-out x h γ p)
      br₃ (inr r) = PT.rec PT.squash₁ br₄ r
      br₁ : ⟨ γ ⊨ Cert0At x h ⟩
          ⊎ ⟨ γ ⊨ (CertSelMem.CertSelAt x h
                ∨̇ (CertSelEq.CertSelAt x h
                ∨̇ (Cert3At x h a
                ∨̇ (CertBin4.CertBinAt x g h
                ∨̇ (CertBin5.CertBinAt x g h
                ∨̇ (Cert6At x g h ∨̇ Cert7At x g h)))))) ⟩
          → ∥ CertOf (fst (lookup a γ)) (fst (lookup g γ))
                (fst (lookup h γ)) (fst (lookup x γ)) ∥₁
      br₁ (inl p) = PT.map inl (Cert0-out x h γ p)
      br₁ (inr r) = PT.rec PT.squash₁ br₃ r

    cert₀ : ⟨ γ ⊨ Cert0At x h ⟩ → ⟨ γ ⊨ CertShapeAt x g h a ⟩
    cert₀ p = ∣ inl p ∣₁
    cert₁ : ⟨ γ ⊨ CertSelMem.CertSelAt x h ⟩ → ⟨ γ ⊨ CertShapeAt x g h a ⟩
    cert₁ p = ∣ inr ∣ inl p ∣₁ ∣₁
    cert₂ : ⟨ γ ⊨ CertSelEq.CertSelAt x h ⟩ → ⟨ γ ⊨ CertShapeAt x g h a ⟩
    cert₂ p = ∣ inr ∣ inr ∣ inl p ∣₁ ∣₁ ∣₁
    cert₃ : ⟨ γ ⊨ Cert3At x h a ⟩ → ⟨ γ ⊨ CertShapeAt x g h a ⟩
    cert₃ p = ∣ inr ∣ inr ∣ inr ∣ inl p ∣₁ ∣₁ ∣₁ ∣₁
    cert₄ : ⟨ γ ⊨ CertBin4.CertBinAt x g h ⟩ → ⟨ γ ⊨ CertShapeAt x g h a ⟩
    cert₄ p = ∣ inr ∣ inr ∣ inr ∣ inr ∣ inl p ∣₁ ∣₁ ∣₁ ∣₁ ∣₁
    cert₅ : ⟨ γ ⊨ CertBin5.CertBinAt x g h ⟩ → ⟨ γ ⊨ CertShapeAt x g h a ⟩
    cert₅ p = ∣ inr ∣ inr ∣ inr ∣ inr ∣ inr ∣ inl p ∣₁ ∣₁ ∣₁ ∣₁ ∣₁ ∣₁
    cert₆ : ⟨ γ ⊨ Cert6At x g h ⟩ → ⟨ γ ⊨ CertShapeAt x g h a ⟩
    cert₆ p = ∣ inr ∣ inr ∣ inr ∣ inr ∣ inr ∣ inr ∣ inl p ∣₁ ∣₁ ∣₁ ∣₁ ∣₁ ∣₁ ∣₁
    cert₇ : ⟨ γ ⊨ Cert7At x g h ⟩ → ⟨ γ ⊨ CertShapeAt x g h a ⟩
    cert₇ p = ∣ inr ∣ inr ∣ inr ∣ inr ∣ inr ∣ inr ∣ inr p ∣₁ ∣₁ ∣₁ ∣₁ ∣₁ ∣₁ ∣₁

    CertShape-in : CertOf (fst (lookup a γ)) (fst (lookup g γ))
                     (fst (lookup h γ)) (fst (lookup x γ))
                 → ⟨ γ ⊨ CertShapeAt x g h a ⟩
    CertShape-in (inl c) = cert₀ (Cert0-in x h γ c)
    CertShape-in (inr (inl c)) = cert₁ (CertSelMem.CertSel-in x h γ c)
    CertShape-in (inr (inr (inl c))) = cert₂ (CertSelEq.CertSel-in x h γ c)
    CertShape-in (inr (inr (inr (inl c)))) = cert₃ (Cert3-in x h a γ c)
    CertShape-in (inr (inr (inr (inr (inl c))))) =
      cert₄ (CertBin4.CertBin-in x g h γ c)
    CertShape-in (inr (inr (inr (inr (inr (inl c)))))) =
      cert₅ (CertBin5.CertBin-in x g h γ c)
    CertShape-in (inr (inr (inr (inr (inr (inr (inl c))))))) =
      cert₆ (Cert6-in x g h γ c)
    CertShape-in (inr (inr (inr (inr (inr (inr (inr c))))))) =
      cert₇ (Cert7-in x g h γ c)
```

<!--en-->
## The certificate
<!--zh-->
## 证书
<!--/-->

<!--en-->
The certificate is the step condition, approximation-shaped: functionality of
the annotation table, then two binders reading the main table's membership at
the pair (x, y) and demanding the certificate shape at x, with the carrier and
both tables riding at their own slots. Its three readers are the
approximation's three, with the functionality split out: the outward direction
yields the functional reading and the step reading, and the inward direction
reassembles the formula from the two.
<!--zh-->
证书就是那条步条件，逼近形状：注解表的函数性，然后两个绑定子读出主表在对 (x, y) 处的隶属，并要求 x 处的证书形状，载体与两张表落在各自的槽位上。它的三个读式是逼近的三个，只是把函数性单独拆出：向外得出函数读式与步读式，向内从二者重新组装公式。
<!--/-->

```agda
  CertAt : ∀ {n} → Fin n → Fin n → Fin n → Formula S n
  CertAt g h a = FunAt h ∧̇ ∀̇ (∀̇ ( appAt (sh2 g) (suc zero) zero
                                ⇒̇ CertShapeAt (suc zero) (sh2 g) (sh2 h) (sh2 a) ))

  module _ {n : ℕ} (g h a : Fin n) (γ : S ^ n) where
    Cert-fun : ⟨ γ ⊨ CertAt g h a ⟩ → (u v v' : S)
             → ⟨ pr (fst u) (fst v) ∈ fst (lookup h γ) ⟩
             → ⟨ pr (fst u) (fst v') ∈ fst (lookup h γ) ⟩
             → fst v ≡ fst v'
    Cert-fun cert u v v' p q = Fun-out h γ (cert .fst) u v v' p q

    Cert-step : ⟨ γ ⊨ CertAt g h a ⟩ → (x y : S)
              → ⟨ pr (fst x) (fst y) ∈ fst (lookup g γ) ⟩
              → ∥ CertOf (fst (lookup a γ)) (fst (lookup g γ))
                    (fst (lookup h γ)) (fst x) ∥₁
    Cert-step cert x y p =
      CertShape-out (suc zero) (sh2 g) (sh2 h) (sh2 a) (y ∷ x ∷ γ)
        (cert .snd x y (subst ⟨_⟩ (sym (appAt-adequate (sh2 g)
          (suc zero) zero (y ∷ x ∷ γ))) p))

    Cert-in : ((u v v' : S) → ⟨ pr (fst u) (fst v) ∈ fst (lookup h γ) ⟩
             → ⟨ pr (fst u) (fst v') ∈ fst (lookup h γ) ⟩
             → fst v ≡ fst v')
            → ((x y : S) → ⟨ pr (fst x) (fst y) ∈ fst (lookup g γ) ⟩
               → ∥ CertOf (fst (lookup a γ)) (fst (lookup g γ))
                     (fst (lookup h γ)) (fst x) ∥₁)
            → ⟨ γ ⊨ CertAt g h a ⟩
    Cert-in hstep xstep =
      Fun-in h γ hstep
      , (λ x y p →
          PT.rec PT.squash₁
            (CertShape-in (suc zero) (sh2 g) (sh2 h) (sh2 a) (y ∷ x ∷ γ))
            (xstep x y (subst ⟨_⟩ (appAt-adequate (sh2 g) (suc zero) zero
              (y ∷ x ∷ γ)) p)))
```

<!--en-->
## Honesty
<!--zh-->
## 诚实性
<!--/-->

<!--en-->
Honesty is the certificate's payoff: every pair in a certified table, at its
unique annotation m, is the code of an honest term of arity m. The recursion
that reads the branches back into terms runs on the accessibility of the
transitive closure, not of membership itself. A child code sits four
membership steps below its node code, and the termination checker follows only
one step, so composing accessibility projections through helper functions
would be rejected; the closure records the whole descent in one derivation, and
each recursive call applies the matched accessibility function to a chain.
The eight branches are the eight code equations run backwards. A branch pins
its tag, numeral, indices, parameter leaf, and children locally, and each
continuation assembles a term constructor, rewrites the branch's shape
equation along the numeral paths, and closes against the constructor's code
equation. Functionality is what lets the given arity meet the branch's
recorded one: the annotation table is functional by the certificate's first
conjunct, so the annotated pair (x, # m) and the pair (x, mv) force
`fst mv ≡ # m`, and every numeral-shaped datum of the branch is then read at
the arity the caller supplied.
<!--zh-->
诚实性是证书的兑现：受证的表中的每个对，在其唯一注解 m 处，就是元数 m 的诚实项的码。把各分支读回项的递归，跑在传递闭包的可及性上，而非成员关系本身的可及性上。孩子码坐在节点码之下四步成员关系处，而终止检查器只跟一步，故经辅助函数复合可及性投影会被拒绝；闭包把整段下降记在一条推导里，每次递归调用把被匹配的可及性函数施于一条链。八个分支就是把八条码等式反向运行。分支在局部钉住标签、数码、指标、参数叶与孩子，每条续延组装一个项构造子，沿数码路径重写分支的形状等式，再对构造子的码等式反向收口。函数性正是让给定元数与分支记录的元数相遇的地方：注解表由证书第一条合取保证函数性，故被注解的对 (x, # m) 与 (x, mv) 迫使 `fst mv ≡ # m`，分支的每个数码形数据随后都按调用者给出的元数读出。
<!--/-->

```agda
  module Honest {n : ℕ} (g h a : Fin n) (γ : S ^ n)
                (cert : ⟨ γ ⊨ CertAt g h a ⟩) where
    private
      G  = fst (lookup g γ)
      H  = fst (lookup h γ)
      A₀ = fst (lookup a γ)
      module C = Codes A₀ (snd (lookup a γ))

    Honest : V ℓ → ℕ → Type (ℓ-suc ℓ)
    Honest x m = ∥ Σ[ t ∈ KT ⟪ A₀ ⟫ m ] (x ≡ C.code t) ∥₁

    honest : (x : V ℓ) → Acc _∈⁺_ x
           → (y : V ℓ) → ⟨ pr x y ∈ G ⟩
           → (m : ℕ) → ⟨ pr x (# m) ∈ H ⟩
           → Honest x m
    honest x (acc r) y hy m hm =
      PT.rec PT.squash₁ fromShape
        (Cert-step g h a γ cert (x , lx) (y , ly) hy)
      where
      lx : ⟨ isL x ⟩
      lx = isL-trans {x = ⁅ x ⁆s} {y = x}
             (∣ tt* , refl ∣₁)
             (isL-trans {x = pr x (# m)} {y = ⁅ x ⁆s}
               (∣ lift false , refl ∣₁)
               (isL-trans {x = H} {y = pr x (# m)} hm (snd (lookup h γ))))

      ly : ⟨ isL y ⟩
      ly = isL-trans {x = ⁅ x , y ⁆} {y = y}
             (∣ lift true , refl ∣₁)
             (isL-trans {x = pr x y} {y = ⁅ x , y ⁆}
               (∣ lift true , refl ∣₁)
               (isL-trans {x = G} {y = pr x y} hy (snd (lookup g γ))))

      l#m : ⟨ isL (# m) ⟩
      l#m = subst (λ z → ⟨ isL z ⟩) (numeralL-fst m) (numeralL m .snd)

      mEq : (mv : S) → ⟨ fst mv ∈ˢ ω ⟩ → ⟨ pr x (fst mv) ∈ H ⟩ → fst mv ≡ # m
      mEq mv mω ann = sym (Cert-fun g h a γ cert (x , lx) (# m , l#m) mv hm ann)

      fromB0 : Cert0Of H x → Honest x m
      fromB0 (mv , (mω , (qe , ann))) =
        ∣ allK
        , ( qe
          ∙ cong (pr (# 0)) (mEq mv mω ann)
          ∙ sym (C.code-allK m) ) ∣₁

      fromSel : (tg : ℕ) (mk : (i j : Fin m) → KT ⟪ A₀ ⟫ m)
              → ((i j : Fin m) → C.code (mk i j)
                    ≡ pr (# tg) (pr (# m) (pr (# (toℕ i)) (# (toℕ j)))))
              → Σ[ nv ∈ S ] Σ[ iv ∈ S ] Σ[ jv ∈ S ]
                  ( ⟨ fst nv ∈ˢ ω ⟩ × ⟨ fst iv ∈ˢ fst nv ⟩
                  × ⟨ fst jv ∈ˢ fst nv ⟩
                  × (x ≡ pr (# tg) (pr (fst nv) (pr (fst iv) (fst jv))))
                  × ⟨ pr x (fst nv) ∈ H ⟩ )
              → Honest x m
      fromSel tg mk codeEq (nv , iv , jv , (nω , (i∈n , (j∈n , (qe , ann))))) =
        PT.rec PT.squash₁
          (λ { (î , î<m , ivEq) →
          PT.rec PT.squash₁
            (λ { (ĵ , ĵ<m , jvEq) →
              let
                i : Fin m
                i = fromℕ' m î î<m
                j : Fin m
                j = fromℕ' m ĵ ĵ<m
                iv→#i : # (toℕ i) ≡ fst iv
                iv→#i = cong #_ (toFromId' m î î<m) ∙ sym ivEq
                jv→#j : # (toℕ j) ≡ fst jv
                jv→#j = cong #_ (toFromId' m ĵ ĵ<m) ∙ sym jvEq
                eq : x ≡ C.code (mk i j)
                eq = qe
                   ∙ cong (pr (# tg))
                       ( cong (pr (fst nv))
                           ( cong (pr (fst iv)) (sym jv→#j)
                           ∙ cong₂ pr (sym iv→#i) refl )
                       ∙ cong₂ pr nv→m refl )
                   ∙ sym (codeEq i j)
              in ∣ mk i j , eq ∣₁ })
            (∈#-elim m (fst jv) j∈m) })
          (∈#-elim m (fst iv) i∈m)
        where
        nv→m : fst nv ≡ # m
        nv→m = mEq nv nω ann
        i∈m : ⟨ fst iv ∈ˢ (# m) ⟩
        i∈m = subst (λ w → ⟨ fst iv ∈ˢ w ⟩) nv→m i∈n
        j∈m : ⟨ fst jv ∈ˢ (# m) ⟩
        j∈m = subst (λ w → ⟨ fst jv ∈ˢ w ⟩) nv→m j∈n

      fromSelMem : CertSelMem.CertSelOf H x → Honest x m
      fromSelMem = fromSel 1 selMemK (C.code-selMemK m)

      fromSelEq : CertSelEq.CertSelOf H x → Honest x m
      fromSelEq = fromSel 2 selEqK (C.code-selEqK m)

      fromCon : Cert3Of A₀ H x → Honest x m
      fromCon (nv , iv , pv , (nω , (i∈n , (p∈a , (qe , ann))))) =
        PT.rec PT.squash₁
          (λ { (î , î<m , ivEq) →
            let
              i : Fin m
              i = fromℕ' m î î<m
              iv→#i : # (toℕ i) ≡ fst iv
              iv→#i = cong #_ (toFromId' m î î<m) ∙ sym ivEq
              par : ⟪ A₀ ⟫
              par = ∈-asFiber {a = fst pv} {b = A₀} p∈a .fst
              epar : ⟪ A₀ ⟫↪ par ≡ fst pv
              epar = ∈-asFiber {a = fst pv} {b = A₀} p∈a .snd
              eq : x ≡ C.code (selEqConK i par)
              eq = qe
                 ∙ cong (pr (# 3))
                     ( cong (pr (fst nv))
                         ( cong (pr (fst iv)) (sym epar)
                         ∙ cong₂ pr (sym iv→#i) refl )
                     ∙ cong₂ pr nv→m refl )
                 ∙ sym (C.code-selEqConK m i par)
            in ∣ selEqConK i par , eq ∣₁ })
          (∈#-elim m (fst iv) i∈m)
        where
        nv→m : fst nv ≡ # m
        nv→m = mEq nv nω ann
        i∈m : ⟨ fst iv ∈ˢ (# m) ⟩
        i∈m = subst (λ w → ⟨ fst iv ∈ˢ w ⟩) nv→m i∈n

      fromInter : CertBin4.CertBinOf G H x → Honest x m
      fromInter (c₁ , c₂ , mv , y₁ , y₂ ,
                 (qe , (mω , (e1 , (e2 , (ann , (ann₁₀ , ann₂₀))))))) =
        PT.rec PT.squash₁
          (λ { (t₁ , e₁) →
          PT.rec PT.squash₁
            (λ { (t₂ , e₂) →
              let
                eq : x ≡ C.code (interK t₁ t₂)
                eq = qe
                   ∙ cong (pr (# 4))
                       ( cong (pr (fst c₁)) e₂
                       ∙ cong₂ pr e₁ refl )
                   ∙ sym (C.code-interK t₁ t₂)
              in ∣ interK t₁ t₂ , eq ∣₁ })
            (honest (fst c₂) (r (fst c₂) chain₂) (fst y₂) e2 m ann₂) })
          (honest (fst c₁) (r (fst c₁) chain₁) (fst y₁) e1 m ann₁)
        where
        nv→m : fst mv ≡ # m
        nv→m = mEq mv mω ann
        ann₁ : ⟨ pr (fst c₁) (# m) ∈ H ⟩
        ann₁ = subst (λ w → ⟨ pr (fst c₁) w ∈ H ⟩) nv→m ann₁₀
        ann₂ : ⟨ pr (fst c₂) (# m) ∈ H ⟩
        ann₂ = subst (λ w → ⟨ pr (fst c₂) w ∈ H ⟩) nv→m ann₂₀
        chain₀ : fst c₁ ∈⁺ pr (# 4) (pr (fst c₁) (fst c₂))
        chain₀ = trans⁺ (chainFst (fst c₁) (fst c₂))
                         (chainSnd (# 4) (pr (fst c₁) (fst c₂)))
        chain₁ : fst c₁ ∈⁺ x
        chain₁ = subst (λ w → fst c₁ ∈⁺ w) (sym qe) chain₀
        chain₂₀ : fst c₂ ∈⁺ pr (# 4) (pr (fst c₁) (fst c₂))
        chain₂₀ = trans⁺ (chainSnd (fst c₁) (fst c₂))
                          (chainSnd (# 4) (pr (fst c₁) (fst c₂)))
        chain₂ : fst c₂ ∈⁺ x
        chain₂ = subst (λ w → fst c₂ ∈⁺ w) (sym qe) chain₂₀

      fromUnion : CertBin5.CertBinOf G H x → Honest x m
      fromUnion (c₁ , c₂ , mv , y₁ , y₂ ,
                 (qe , (mω , (e1 , (e2 , (ann , (ann₁₀ , ann₂₀))))))) =
        PT.rec PT.squash₁
          (λ { (t₁ , e₁) →
          PT.rec PT.squash₁
            (λ { (t₂ , e₂) →
              let
                eq : x ≡ C.code (unionK t₁ t₂)
                eq = qe
                   ∙ cong (pr (# 5))
                       ( cong (pr (fst c₁)) e₂
                       ∙ cong₂ pr e₁ refl )
                   ∙ sym (C.code-unionK t₁ t₂)
              in ∣ unionK t₁ t₂ , eq ∣₁ })
            (honest (fst c₂) (r (fst c₂) chain₂) (fst y₂) e2 m ann₂) })
          (honest (fst c₁) (r (fst c₁) chain₁) (fst y₁) e1 m ann₁)
        where
        nv→m : fst mv ≡ # m
        nv→m = mEq mv mω ann
        ann₁ : ⟨ pr (fst c₁) (# m) ∈ H ⟩
        ann₁ = subst (λ w → ⟨ pr (fst c₁) w ∈ H ⟩) nv→m ann₁₀
        ann₂ : ⟨ pr (fst c₂) (# m) ∈ H ⟩
        ann₂ = subst (λ w → ⟨ pr (fst c₂) w ∈ H ⟩) nv→m ann₂₀
        chain₀ : fst c₁ ∈⁺ pr (# 5) (pr (fst c₁) (fst c₂))
        chain₀ = trans⁺ (chainFst (fst c₁) (fst c₂))
                         (chainSnd (# 5) (pr (fst c₁) (fst c₂)))
        chain₁ : fst c₁ ∈⁺ x
        chain₁ = subst (λ w → fst c₁ ∈⁺ w) (sym qe) chain₀
        chain₂₀ : fst c₂ ∈⁺ pr (# 5) (pr (fst c₁) (fst c₂))
        chain₂₀ = trans⁺ (chainSnd (fst c₁) (fst c₂))
                          (chainSnd (# 5) (pr (fst c₁) (fst c₂)))
        chain₂ : fst c₂ ∈⁺ x
        chain₂ = subst (λ w → fst c₂ ∈⁺ w) (sym qe) chain₂₀

      fromCompl : Cert6Of G H x → Honest x m
      fromCompl (nv , cv , yv , (nω , (qe , (e1 , (ann , ann₀))))) =
        PT.rec PT.squash₁
          (λ { (t' , e') →
            let
              eq : x ≡ C.code (complK t')
              eq = qe
                 ∙ cong (pr (# 6))
                     ( cong (pr (fst nv)) e'
                     ∙ cong₂ pr nv→m refl )
                 ∙ sym (C.code-complK t')
            in ∣ complK t' , eq ∣₁ })
          (honest (fst cv) (r (fst cv) chain) (fst yv) e1 m ann₁)
        where
        nv→m : fst nv ≡ # m
        nv→m = mEq nv nω ann
        ann₁ : ⟨ pr (fst cv) (# m) ∈ H ⟩
        ann₁ = subst (λ w → ⟨ pr (fst cv) w ∈ H ⟩) nv→m ann₀
        chain₀ : fst cv ∈⁺ pr (# 6) (pr (fst nv) (fst cv))
        chain₀ = trans⁺ (chainSnd (fst nv) (fst cv))
                         (chainSnd (# 6) (pr (fst nv) (fst cv)))
        chain : fst cv ∈⁺ x
        chain = subst (λ w → fst cv ∈⁺ w) (sym qe) chain₀

      fromShift : Cert7Of G H x → Honest x m
      fromShift (cv , mv , mv' , yv , (qe , (mω , (qq , (e1 , (ann , ann₀)))))) =
        PT.rec PT.squash₁
          (λ { (t' , e') →
            let
              eq : x ≡ C.code (shiftK t')
              eq = qe ∙ cong (pr (# 7)) e' ∙ sym (C.code-shiftK t')
            in ∣ shiftK t' , eq ∣₁ })
          (honest (fst cv) (r (fst cv) chain) (fst yv) e1 (suc m) ann₁)
        where
        mv→m : fst mv ≡ # m
        mv→m = mEq mv mω ann
        mv'→m' : fst mv' ≡ # (suc m)
        mv'→m' = qq ∙ cong sucV mv→m
        ann₁ : ⟨ pr (fst cv) (# (suc m)) ∈ H ⟩
        ann₁ = subst (λ w → ⟨ pr (fst cv) w ∈ H ⟩) mv'→m' ann₀
        chain₀ : fst cv ∈⁺ pr (# 7) (fst cv)
        chain₀ = chainSnd (# 7) (fst cv)
        chain : fst cv ∈⁺ x
        chain = subst (λ w → fst cv ∈⁺ w) (sym qe) chain₀

      fromShape : CertOf A₀ G H x → Honest x m
      fromShape (inl c) = fromB0 c
      fromShape (inr (inl c)) = fromSelMem c
      fromShape (inr (inr (inl c))) = fromSelEq c
      fromShape (inr (inr (inr (inl c)))) = fromCon c
      fromShape (inr (inr (inr (inr (inl c))))) = fromInter c
      fromShape (inr (inr (inr (inr (inr (inl c)))))) = fromUnion c
      fromShape (inr (inr (inr (inr (inr (inr (inl c))))))) = fromCompl c
      fromShape (inr (inr (inr (inr (inr (inr (inr c))))))) = fromShift c
```

<!--en-->
## Recap
<!--zh-->
## 小结
<!--/-->

<!--en-->
The certificate describes the tower's step with local conditions only. Each
branch pins its tag by a sealed numeral, its payload pieces as members of ω or
of the carrier, its children in the main table, and its annotations in a
functional table, so every numeral-shaped leaf is genuinely numeral, every
index genuinely sits inside its numeral, and every annotation is unique and
trustworthy. Honesty delivers the payoff: every certified pair is read back,
at its unique annotation, as the code of an honest term, by running the eight
code equations backwards on the transitive closure of membership. What
remains is the step body and its two laws, where this layer pays off.
<!--zh-->
证书只用局部条件描述塔的一步。每个分支以封印数码钉住标签，以 ω 或载体钉住载荷诸件，以主表钉住孩子，并以函数性的表钉住注解，故每个数码形叶真是数码，每个指标真在其数码之内，每条注解唯一而可信任。诚实性交付了兑现：每个受证的对在唯一注解处读回为诚实项的码，办法是在成员关系的传递闭包上反向运行八条码等式。剩下的工作是步本体及其两条定律，也是这一层兑现之处。
<!--/-->
