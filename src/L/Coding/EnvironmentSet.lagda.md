<!--en-->
# The set of fixed-length environments
<!--zh-->
# 定长环境之集
<!--ja-->
# 固定長環境の集合
<!--/-->

<!--en-->
For a constructible set `B` and a natural number `n`, this chapter constructs an element `envSet n` of `L` whose members are exactly the length-`n` environments with values in `B`.
<!--zh-->
给定可构造集合 `B` 与自然数 `n`，本章构造 `L` 的元素 `envSet n`，其成员恰为取值于 `B` 的长度 `n` 环境。
<!--ja-->
構成可能集合 `B` と自然数 `n` に対し、本章は `L` の要素 `envSet n` を構成し、その要素がちょうど `B` に値を取る長さ `n` の環境であることを示します。
<!--/-->

<!--en-->
The chapter that wrote the ten clauses said what it means for one thing to be
an environment over a set, and set aside the question of whether all of them
together form a set. This chapter answers it: the satisfaction predicates will
be separated from this common set of environments.

The route is the one the axioms already provide. Environments over a set of `L` at a
fixed length are indexed by a small type; each is an element of `L`, so they all
lie below one stage, and separating that stage by the description gives exactly them.
Nothing here needs replacement, and nothing here needs recursion.
<!--zh-->
写下十条子句的那一章说了「单个东西是某集合之上的环境」是什么意思，却把「它们全体是否构成一个集合」这个问题推开了。本章回答它：满足关系的谓词将从这个共同的环境集合中分离出来。

这里使用的是诸公理已经给出的路线。给定一个长度，所有取值落在 `L` 的某个集合中的环境由一个小类型索引；每个环境都是 `L` 的元素，因此它们全都位于某个共同阶段之下。再按相应描述从该阶段中分离，所得集合恰好包含这些环境。此处不需要替换，也不需要递归。
<!--/-->

```agda
{-# OPTIONS --cubical --safe --guardedness #-}

open import Base.Prelude
open import Base.Truth
open import Base.Classical using ( LEM )

module L.Coding.EnvironmentSet {ℓ : Level} (lem : LEM (ℓ-suc ℓ)) where

open import FOL.ZFStructure using ( module hPropStructure )
open import FOL.Syntax using ( Formula; var; con; _≐_; _∧̇_; ∃̇_ )
import FOL.Absoluteness
import FOL.ZFModel
open import V.Hierarchy {ℓ} using ( 𝒮ᵥ; extensionalV )
open import V.Coding {ℓ} using ( pr; #-inj′ )
open import L.Constructible {ℓ}
  using ( 𝒮ʟ; isL; isL-trans; IsOrd; Lset; Lset-mono )
open import L.Ordinal {ℓ} using ( boundingOrd; ∈#-elim )
open import V.Coding {ℓ} using ( #mono; pr-inj )
open import L.Stage {ℓ} lem using ( stage; stage-ord; stage-mem )
open import L.Axioms.Basic {ℓ} using ( LsetS )
open import L.Axioms.Full {ℓ} lem using ( hasSeparationL )
open import L.Axioms.Numerals {ℓ} using ( numeralL; numeralL-fst )
open import L.Coding.Environment {ℓ} using ( env )
open import L.Coding.CodeConstructibility {ℓ} using ( envL )
open import L.Coding.Model {ℓ} using ( envOverAt; svAt; domAt; valuesInAt; pairsInAt; inDomAt; prʟ; prʟ-fst; svAt-in; svAt-out; inDomAt-adequate; appAt-adequate; domAt-in; valuesInAt-out; envOver-sv; envOver-dom; envOver-values; envOver-pairs; pairsIn-in; pairsIn-out )
open import L.Coding.Expressions {ℓ} using ( numL )

open import Cubical.Data.FinData using ( toℕ; inj-toℕ )
open import Cubical.Data.FinData.Properties using ( toℕ<n; fromℕ'; toFromId' )
open import Cubical.Data.Sigma using ( Σ≡Prop )
open import Cubical.Functions.Logic using ( ⇔toPath )
import Cubical.HITs.PropositionalTruncation as PT
open PT using ( ∣_∣₁; ∥_∥₁; squash₁ )
open import Cubical.HITs.CumulativeHierarchy.Base using ( V; _∈_; setIsSet )
open import Cubical.HITs.CumulativeHierarchy.Properties
  using ( ⟪_⟫; ⟪_⟫↪; ∈ₛ⟪_⟫↪_; ∈∈ₛ; ∈-asFiber )
open import Cubical.HITs.CumulativeHierarchy.Constructions
  using ( module InfinitySet )
open InfinitySet using ( #_ )

open TruthAlgebra (hPropAlgebra (ℓ-suc ℓ))
open hPropStructure 𝒮ʟ

module ModelL = FOL.ZFModel 𝒮ʟ

module AbsL = FOL.Absoluteness.Single 𝒮ᵥ isL isL-trans
open AbsL renaming ( _⊨ᵐ_ to _⊨_ )
```

<!--en-->
## A stage under a small family
<!--zh-->
## 小族之下的一个阶段
<!--ja-->
## 小さい族を覆う段階
<!--/-->

<!--en-->
`stageFor` finds one ordinal stage containing every member of any small family of constructible sets, providing the common ambient stage needed by separation.
<!--zh-->
`stageFor` 找到一个包含任意可构造集合小族所有成员的序数阶段，从而提供分离所需的共同外围阶段。
<!--ja-->
`stageFor` は構成可能集合からなる任意の小さい族の全要素を含む一つの順序数段階を見つけ、分出に必要な共通の周囲の段階を与えます。
<!--/-->

<!--en-->
The move `smallDom`{.Agda} makes, with the ordinal kept rather than hidden,
because what is needed here is a lemma stated about stages rather than about a set
of the model.
<!--zh-->
它做的正是 `smallDom`{.Agda} 所做的事，但把那个序数保留下来而不隐藏，因为此处需要的是一条关于阶段、而非关于模型某集合的引理。
<!--/-->

```agda
stageFor : (X : Type ℓ) (f : X → S)
         → Σ[ β ∈ V ℓ ] (IsOrd β × ((x : X) → ⟨ fst (f x) ∈ Lset β ⟩))
stageFor X f = β , (oβ , mem)
  where
  b = boundingOrd X (λ x → stage (fst (f x)) (f x .snd))
        (λ x → stage-ord (fst (f x)) (f x .snd))
  β = b .fst
  oβ : IsOrd β
  oβ = b .snd .fst
  mem : (x : X) → ⟨ fst (f x) ∈ Lset β ⟩
  mem x = Lset-mono {α = β} {β = stage (fst (f x)) (f x .snd)} (b .snd .snd x)
            (stage-mem (fst (f x)) (f x .snd))
```

<!--en-->
## One environment, as an element of the model
<!--zh-->
## 单个环境，作为模型的元素
<!--ja-->
## 一つの環境をモデルの要素にする
<!--/-->

<!--en-->
For each `g : Fin n → ⟪ B ⟫`, `envSL` proves that its finite graph is constructible, so the packaged `envS g` can be bounded by `stageFor`.
<!--zh-->
对每个 `g : Fin n → ⟪ B ⟫`，`envSL` 证明其有穷图可构造，因此封装后的 `envS g` 可由 `stageFor` 定界。
<!--ja-->
各 `g : Fin n → ⟪ B ⟫` について `envSL` はその有限グラフが構成可能であることを示すので、包装された `envS g` を `stageFor` で抑えられます。
<!--/-->

<!--en-->
An environment over a set of `L` is a finite set of pairs of a numeral with a
member, and a member of an element of `L` is an element of `L`, so the pairs are
too and the stage lemma above closes it.
<!--zh-->
落在 `L` 的某集合之上的环境是由「数码与成员」之对组成的有穷集；而 `L` 之元素的成员仍是 `L` 的元素，故这些对也是，于是前一条阶段引理恰好适用于此。
<!--/-->

```agda
module _ (B : S) where
  private
    ix : ⟪ fst B ⟫ → S
    ix m = ⟪ fst B ⟫↪ m
         , isL-trans (∈∈ₛ {a = ⟪ fst B ⟫↪ m} {b = fst B} .snd (∈ₛ⟪ fst B ⟫↪ m))
             (snd B)

  Ix : ℕ → Type ℓ
  Ix n = Fin n → ⟪ fst B ⟫

  opaque
    envSL : {n : ℕ} (g : Ix n) → ⟨ isL (env (λ i → fst (ix (g i)))) ⟩
    envSL {n} g = envL β oβ (λ i → fst (ix (g i))) mem
      where
      pairs : Lift {ℓ-zero} {ℓ} (Fin n) → S
      pairs i = prʟ (numeralL (toℕ (lower i))) (ix (g (lower i)))

      sf : Σ[ b ∈ V ℓ ] (IsOrd b
         × ((i : Lift {ℓ-zero} {ℓ} (Fin n)) → ⟨ fst (pairs i) ∈ Lset b ⟩))
      sf = stageFor (Lift {ℓ-zero} {ℓ} (Fin n)) pairs

      β : V ℓ
      β = sf .fst

      oβ : IsOrd β
      oβ = sf .snd .fst

      mem : (i : Fin n) → ⟨ pr (# (toℕ i)) (fst (ix (g i))) ∈ Lset β ⟩
      mem i = subst (λ w → ⟨ w ∈ Lset β ⟩)
        (prʟ-fst (numeralL (toℕ i)) (ix (g i))
          ∙ cong₂ pr (numeralL-fst (toℕ i)) refl)
        (sf .snd .snd (lift i))

  envS : {n : ℕ} → Ix n → S
  envS g = env (λ i → fst (ix (g i))) , envSL g
```

<!--en-->
## Separating the environment set
<!--zh-->
## 分离出环境之集
<!--ja-->
## 環境の集合を分出する
<!--/-->

<!--en-->
`envFo n` specializes `envOverAt` to the fixed length `n` and base set `B`; separation in the common stage defines `envSet n` and its membership equation.
<!--zh-->
`envFo n` 把 `envOverAt` 特化到固定长度 `n` 与基集合 `B`；在共同阶段中的分离定义 `envSet n` 及其成员等式。
<!--ja-->
`envFo n` は `envOverAt` を固定された長さ `n` と基礎集合 `B` に特殊化し、共通の段階での分出が `envSet n` とその要素条件を定義します。
<!--/-->

<!--en-->
The description takes three arguments and separation offers one variable, so the
other two are bound and pinned to constants. That is three lines and it keeps the
description as the chapter wrote it, which is worth more than saving them.
<!--zh-->
那条描述需要三个自变量，而分离只提供一个变元，故另外两个被绑定到固定的常元上。这要花三行，却让那条描述保持本章当初写下的形式，比省下这三行更值得。
<!--/-->

```agda
  private
    nn : ℕ → S
    nn k = # k , numL k

  envFo : (n : ℕ) → Formula S 1
  envFo n = ∃̇ (∃̇ ( (var (suc zero) ≐ con (nn n))
                 ∧̇ ((var zero ≐ con B)
                 ∧̇ envOverAt (suc (suc zero)) (suc zero) zero) ))

  private
    sf : (n : ℕ) → Σ[ β ∈ V ℓ ] (IsOrd β × ((g : Ix n) → ⟨ fst (envS g) ∈ Lset β ⟩))
    sf n = stageFor (Ix n) envS

    amb : (n : ℕ) → S
    amb n = LsetS (sf n .fst) (sf n .snd .fst)

  opaque
    envSet : (n : ℕ) → S
    envSet n = hasSeparationL (amb n) (envFo n) .fst .fst

    envSet-mem : (n : ℕ) (x : S)
               → (x ∈ˢ envSet n) ≡ ((x ∈ˢ amb n) ⊓ ((x ∷ []) ⊨ envFo n))
    envSet-mem n = hasSeparationL (amb n) (envFo n) .fst .snd
```

<!--en-->
## Every environment is in it
<!--zh-->
## 每个环境都在其中
<!--ja-->
## すべての環境がその集合に入る
<!--/-->

<!--en-->
For `g : Fin n → ⟪ B ⟫`, the proof checks that its graph is single-valued, has domain `n`, and contains exactly the required values and pairs, hence belongs to `envSet n`.
<!--zh-->
对 `g : Fin n → ⟪ B ⟫`，证明的核心是核对其图为单值、定义域为 `n`，且恰含所需的值与有序对，因而属于 `envSet n`。
<!--ja-->
`g : Fin n → ⟪ B ⟫` について、そのグラフが単値で定義域が `n` であり、必要な値と対をちょうど含むことを確認し、`envSet n` に属することを示します。
<!--/-->

<!--en-->
Four conjuncts, and each is the description read against what an environment
actually is. Single-valuedness and the two containments come straight off the
membership specification, which is `refl`{.Agda}; the domain is the only one that
does arithmetic, because saying the domain is the numeral `n` means saying that
the indices below `n` are exactly the numerals below `n`.
<!--zh-->
四个合取项，而每一条都只是把那条描述对着「环境究竟是什么」读一遍。单值性与那两条包含关系直接由成员规格得出，而后者是 `refl`{.Agda}；只有定义域那一条需要算术，因为「定义域是数码 `n`」说的正是「`n` 以下的诸序号恰是 `n` 以下的诸数码」。
<!--/-->

```agda
  module _ {n : ℕ} (g : Ix n) where
    private
      out : (s : V ℓ) → ⟨ s ∈ fst (envS g) ⟩
          → ∥ (Σ[ i ∈ Fin n ] (pr (# (toℕ i)) (fst (ix (g i))) ≡ s)) ∥₁
      out s = PT.map (λ { (li , e) → lower li , e })

      into : (i : Fin n) → ⟨ pr (# (toℕ i)) (fst (ix (g i))) ∈ fst (envS g) ⟩
      into i = ∣ lift i , refl ∣₁

      val∈ : (i : Fin n) → ⟨ fst (ix (g i)) ∈ fst B ⟩
      val∈ i = ∈∈ₛ {a = ⟪ fst B ⟫↪ (g i)} {b = fst B} .snd (∈ₛ⟪ fst B ⟫↪ (g i))

      δ : S ^ 3
      δ = B ∷ nn n ∷ envS g ∷ []

      E : Fin 3
      E = suc (suc zero)

    envOver : ⟨ δ ⊨ envOverAt E (suc zero) zero ⟩
    envOver = sv , (dom , (vals , pairs))
      where
      sv : ⟨ δ ⊨ svAt E ⟩
      sv = svAt-in E δ (λ x y y' p q →
        PT.rec (setIsSet (fst y) (fst y'))
          (λ { (i , ei) → PT.rec (setIsSet (fst y) (fst y'))
            (λ { (j , ej) → sym (pr-inj ei .snd)
               ∙ cong (λ k → fst (ix (g k)))
                   (inj-toℕ (#-inj′ (pr-inj ei .fst ∙ sym (pr-inj ej .fst))))
               ∙ pr-inj ej .snd })
            (out (pr (fst x) (fst y')) q) })
          (out (pr (fst x) (fst y)) p))

      dom : ⟨ δ ⊨ domAt E (suc zero) ⟩
      dom x = fwd , bwd
        where
        fwd : ⟨ (x ∷ δ) ⊨ inDomAt (suc E) zero ⟩ → ⟨ fst x ∈ (# n) ⟩
        fwd hd = PT.rec (snd (fst x ∈ (# n)))
          (λ { (y , p) → PT.rec (snd (fst x ∈ (# n)))
            (λ { (i , ei) → subst (λ w → ⟨ w ∈ (# n) ⟩) (pr-inj ei .fst)
                   (#mono (toℕ i) n (toℕ<n i)) })
            (out (pr (fst x) (fst y)) p) })
          (subst ⟨_⟩ (inDomAt-adequate (suc E) zero (x ∷ δ)) hd)

        bwd : ⟨ fst x ∈ (# n) ⟩ → ⟨ (x ∷ δ) ⊨ inDomAt (suc E) zero ⟩
        bwd hx = subst ⟨_⟩ (sym (inDomAt-adequate (suc E) zero (x ∷ δ)))
          (PT.map
            (λ { (m , m<n , e) →
              ix (g (fromℕ' n m m<n))
              , subst (λ w → ⟨ pr w (fst (ix (g (fromℕ' n m m<n))))
                                 ∈ fst (envS g) ⟩)
                  (cong #_ (toFromId' n m m<n) ∙ sym e) (into (fromℕ' n m m<n)) })
            (∈#-elim n (fst x) hx))

      vals : ⟨ δ ⊨ valuesInAt E zero ⟩
      vals x y hp = PT.rec (snd (fst y ∈ fst B))
        (λ { (i , ei) → subst (λ w → ⟨ w ∈ fst B ⟩) (pr-inj ei .snd) (val∈ i) })
        (out (pr (fst x) (fst y))
          (subst ⟨_⟩ (appAt-adequate (suc (suc E)) (suc zero) zero (y ∷ x ∷ δ))
            hp))

      pairs : ⟨ δ ⊨ pairsInAt E (suc zero) zero ⟩
      pairs = pairsIn-in E (suc zero) zero δ
        (λ s s∈ → PT.map
          (λ { (i , ei) → nn (toℕ i)
             , ( ix (g i)
               , ( #mono (toℕ i) n (toℕ<n i) , (val∈ i , sym ei) ) ) })
          (out (fst s) s∈))

    envSetIn : ⟨ (envS g ∷ []) ⊨ envFo n ⟩
    envSetIn = ∣ nn n , ∣ B , (refl , (refl , envOver)) ∣₁ ∣₁
```

<!--en-->
## Recovering an environment from a member
<!--zh-->
## 从成员恢复环境
<!--ja-->
## 要素から環境を復元する
<!--/-->

<!--en-->
Conversely, the four `envOverAt` clauses for a member `x` determine a function `g : Fin n → ⟪ B ⟫`, and extensionality identifies `x` with `envS g`.
<!--zh-->
反过来，成员 `x` 满足的四条 `envOverAt` 子句确定函数 `g : Fin n → ⟪ B ⟫`，外延性再把 `x` 与 `envS g` 等同起来。
<!--ja-->
逆に、要素 `x` が満たす `envOverAt` の四条件から関数 `g : Fin n → ⟪ B ⟫` が定まり、外延性によって `x` と `envS g` が同一視されます。
<!--/-->

<!--en-->
The other direction is what four clauses need when they read a bound variable
off an environment, and seven further clauses use it in a weaker form: a clause
binds its own ambient set and says only that its members are the environments,
so a proof that consumes the clause has to recognize that description as
**this** set. Both uses come from the same recovery, which is why it takes the
environment and the three slots as parameters rather than fixing them: a clause
places them where its own frame places them, not where this chapter would. A set satisfying the description is the graph of a function,
and recovering that function is the only place the four conjuncts must work
together: the domain conjunct says every index below the length has an entry,
and single-valuedness says there is at most one, so the existence of that entry
is a **proposition** and the truncation given by the domain conjunct can be
eliminated. Membership then names the index, which is untruncated because the
fibers of a set's own indexing are.

Extensionality completes the proof: one direction comes from the entries and
the other from the pairs conjunct, which is the conjunct without which
unwanted elements could enter.
<!--zh-->
另一个方向也是四条子句从环境中读出被绑定变元时所需的；另有七条子句以较弱的形式使用它：子句绑定自己的周遭集合，只断言其成员恰为这些环境，因此使用该子句时必须把这项描述识别为**这个**集合。两种用途来自同一个恢复过程。这也解释了为何环境和三个槽位作为参数给出，而不固定为特定对象：各子句可以把它们放在自身框架要求的位置。满足该描述的集合是一个函数图。恢复这个函数是四个合取项唯一需要共同作用之处：定义域条件说明长度以下的每个序号都有条目，单值性说明条目至多一个，所以「该条目存在」是**命题**，可以消去定义域条件给出的截断。随后由隶属关系取得索引；这里无需截断，因为集合自身索引的纤维本来就是不截断的。

外延性补全证明：一个方向来自诸条目，另一个来自「由诸对构成」那一条，而若缺了那一条，不需要的元素就会混进来。
<!--/-->

```agda
  module Recover (n : ℕ) {k : ℕ} (γ : S ^ k) (Ei di bi : Fin k)
    (qd : fst (lookup di γ) ≡ # n) (qb : fst (lookup bi γ) ≡ fst B)
    (h : ⟨ γ ⊨ envOverAt Ei di bi ⟩)
    where
    private
      e : S
      e = lookup Ei γ

      Entry : Fin n → Type (ℓ-suc ℓ)
      Entry i = Σ[ y ∈ S ] ⟨ pr (# (toℕ i)) (fst y) ∈ fst e ⟩

      isPropEntry : (i : Fin n) → isProp (Entry i)
      isPropEntry i (y , p) (y' , p') =
        Σ≡Prop (λ w → snd (pr (# (toℕ i)) (fst w) ∈ fst e))
          (Σ≡Prop (λ v → snd (isL v))
            (svAt-out Ei γ (envOver-sv Ei di bi γ h)
              (nn (toℕ i)) y y' p p'))

      entry : (i : Fin n) → Entry i
      entry i = PT.rec (isPropEntry i) (λ z → z)
        (domAt-in Ei di γ (envOver-dom Ei di bi γ h)
          (nn (toℕ i)) (subst (λ z → ⟨ (# (toℕ i)) ∈ z ⟩) (sym qd)
            (#mono (toℕ i) n (toℕ<n i))))

      fib : (i : Fin n) → Σ[ m ∈ ⟪ fst B ⟫ ] (⟪ fst B ⟫↪ m ≡ fst (entry i .fst))
      fib i = ∈-asFiber {a = fst (entry i .fst)} {b = fst B}
        (subst (λ z → ⟨ fst (entry i .fst) ∈ z ⟩) qb
          (valuesInAt-out Ei bi γ (envOver-values Ei di bi γ h)
            (nn (toℕ i)) (entry i .fst) (entry i .snd)))

    g : Ix n
    g i = fib i .fst

    private
      val≡ : (i : Fin n) → fst (ix (g i)) ≡ fst (entry i .fst)
      val≡ i = fib i .snd

      fwd : (w : V ℓ) → ⟨ w ∈ fst (envS g) ⟩ → ⟨ w ∈ fst e ⟩
      fwd w = PT.rec (snd (w ∈ fst e))
        (λ { (li , q) → subst (λ z → ⟨ z ∈ fst e ⟩)
               (cong (pr (# (toℕ (lower li)))) (sym (val≡ (lower li))) ∙ q)
               (entry (lower li) .snd) })

      bwd : (w : V ℓ) → ⟨ w ∈ fst e ⟩ → ⟨ w ∈ fst (envS g) ⟩
      bwd w hw = PT.rec squash₁
        (λ { (u , (v , (u∈ , (v∈ , eq)))) → PT.rec squash₁
          (λ { (m , (m<n , um)) →
            let i = fromℕ' n m m<n
                iu : # (toℕ i) ≡ fst u
                iu = cong #_ (toFromId' n m m<n) ∙ sym um
                hv : ⟨ pr (# (toℕ i)) (fst v) ∈ fst e ⟩
                hv = subst (λ z → ⟨ z ∈ fst e ⟩)
                       (eq ∙ cong (λ z → pr z (fst v)) (sym iu)) hw
                same : fst v ≡ fst (entry i .fst)
                same = svAt-out Ei γ (envOver-sv Ei di bi γ h)
                         (nn (toℕ i)) v (entry i .fst) hv (entry i .snd)
            in ∣ lift i , cong (pr (# (toℕ i))) (val≡ i ∙ sym same)
                        ∙ cong (λ z → pr z (fst v)) iu ∙ sym eq ∣₁ })
          (∈#-elim n (fst u) (subst (λ z → ⟨ fst u ∈ z ⟩) qd u∈)) })
        (pairsIn-out Ei di bi γ
          (envOver-pairs Ei di bi γ h)
          (w , isL-trans {x = fst e} {y = w} hw (snd e)) hw)

    recovers : fst e ≡ fst (envS g)
    recovers = extensionalV (λ w → ⇔toPath (bwd w) (fwd w))

  envSet-in : {n : ℕ} (g : Ix n) → ⟨ envS g ∈ˢ envSet n ⟩
  envSet-in {n} g = subst ⟨_⟩ (sym (envSet-mem n (envS g)))
    (sf n .snd .snd g , envSetIn g)

  envSet-out : (n : ℕ) (x : S) → ⟨ x ∈ˢ envSet n ⟩
             → ∥ (Σ[ g ∈ Ix n ] (fst x ≡ fst (envS g))) ∥₁
  envSet-out n x hx = PT.rec squash₁
    (λ { (d , hd) → PT.map
      (λ { (b , (qd , (qb , hov))) →
        Recover.g n (b ∷ d ∷ x ∷ []) (suc (suc zero)) (suc zero) zero qd qb hov
        , Recover.recovers n (b ∷ d ∷ x ∷ []) (suc (suc zero)) (suc zero) zero
            qd qb hov })
      hd })
    (subst ⟨_⟩ (envSet-mem n x) hx .snd)

```

<!--en-->
## Recap
<!--zh-->
## 小结
<!--ja-->
## まとめ
<!--/-->

<!--en-->
The two directions specify `envSet n`: membership is equivalent to being the graph of a length-`n` assignment into `B`, so later constructions can quantify over environments inside `L`.
<!--zh-->
两个方向刻画了 `envSet n`：属于该集合等价于它是取值于 `B` 的长度 `n` 赋值图，因此后面的构造能在 `L` 内量化环境。
<!--ja-->
二方向は `envSet n` を特徴づけます。その要素であることは `B` に値を取る長さ `n` の割当てのグラフであることと同値なので、後の構成は `L` 内で環境を量化できます。
<!--/-->

<!--en-->
`envSet`{.Agda} is the ambient set the negative clauses take their complements
in, and it reads both ways: `envSet-in`{.Agda} puts every environment over the
carrier into it, `envSet-out`{.Agda} recovers from any member the function whose
graph it is. The second is what four clauses want when they read a bound variable
off an environment, and it is the one that needed all four conjuncts of the
description at once.

Two measurements, and the second is a sharper form of a rule the development
already had. Proving the fourth conjunct with the environment written out **did
not finish in ten minutes**; proving the same statement as a lemma whose
environment is a *variable*, then applying it, takes no measurable time. A
satisfaction substitution along an adequacy equation must be discharged where the
arguments are variables: at concrete elements it drags the whole absoluteness
bridge through normalization, and the elements' constructibility certificates
with it. Sealing the certificate at the construction site was necessary and not
sufficient. The recovery is written the same way, with the description's two
constant slots left as parameters constrained by equations rather than written in,
so that nothing substitutes underneath a satisfaction at a concrete environment.
<!--zh-->
`envSet`{.Agda} 是诸负子句取补集所在的那个周遭集合，而它双向可读：`envSet-in`{.Agda} 把载体之上的每个环境放进去，`envSet-out`{.Agda} 从任一成员恢复出「它是其图」的那个函数。后者正是四条子句在从环境读出被绑变元时所要的，也是唯一需要那条描述的四个合取项协同上阵的一条。

这里记录两次测量，第二次把本书已有的一条规则说得更精确。把环境固定为具体值后证明第四个合取项，**十分钟仍未完成**；先在环境为**变元**时证明同一引理，再将其应用，耗时则几乎无法测出。沿充分性等式替换满足关系时，替换必须发生在自变量仍是变元之处；若写在具体元素上，归一化会展开整套绝对性结果以及这些元素的可构造性证书。只在构造处封装证书仍不足以避免这一点。恢复部分采用同样的写法：那条描述的两个常元槽保留为由等式约束的参数，而不固定为具体对象，因此不会在具体环境的满足关系之下发生替换。
<!--/-->
