# The cardinal chapter's counting side

<!--en-->
The cardinal chapter has two halves. The definitional half, the three
certified predicates, is delivered; the counting half is this chapter. The
object is Devlin 5.4's size claim for the definable hull, |M| =
max(|X|, ω), and of its two directions this chapter is the counting one, the
upper bound. The count runs on the hull's own index, the `sett` over the
`X`-parameter formulas: the second component of that index is propositional,
so the count's injection from `Formula ⟪ X ⟫ 1` is the whole counting
obligation, and the composition the count chapter promised, the shape-count
read through the count, is delivered here as the formula-count. Everything
after that is an injection into an ordinal, and the one fact the bound
consumes that is not yet delivered is the square law, the injection of an
ordinal's square into itself. The chapter therefore stops exactly there:
everything up to the law is proved conditional on it, the call site is named
with its ordinal and its goal type, and no workaround is invented.
<!--zh-->
基数章有两半。定义层，三条经证书的内部谓词，已经交付；计数层是本章。对象是 Devlin 5.4 对可定义外壳的大小断言，`|M| = max(|X|, ω)`，而两个方向中本章做的是计数那一个，即上界。计数跑在外壳自己的索引上，即以 `X` 参数公式为索引的 `sett`：该索引的第二分量是命题，故计数章那条从 `Formula ⟪ X ⟫ 1` 出发的单射就是全部计数义务，而计数章承诺的复合，即经计数读形状计数，在本章以公式计数的身份交付。此后的一切都是到序数的单射，而这个界所消费而尚未交付的唯一事实是平方律，即序数自身的平方到自身的单射。本章因此恰在那里停下：律之前的一切都在以律为假设的意义下证毕，调用点连同其序数与目标类型被具名，不发明任何绕行。
<!--/-->

```agda
{-# OPTIONS --cubical --safe --guardedness #-}

open import Base.Prelude
open import Base.Classical using ( LEM )

module L.CardinalCount {ℓ : Level} (lem : LEM (ℓ-suc ℓ)) where

open import FOL.Syntax using ( Formula )
open import FOL.Count {ℓ} using ( module Count; shape-count-inj; code )
open import FOL.ZFStructure using ( module hPropStructure )
open import V.Hierarchy {ℓ} using ( 𝒮ᵥ )
open import V.Presentation {ℓ} using ( fiber )
open import V.Coding {ℓ} using ( #-inj′ )
open import L.Constructible {ℓ} using ( isTransV; IsOrd; Lset; layer-trans; Lset-layer )
open import L.Ordinal {ℓ} using ( #∈ω )
import L.Hull {ℓ} lem as Hull
open import Cubical.HITs.CumulativeHierarchy.Properties using ( ⟪_⟫; ⟪_⟫↪ )
open import Cubical.Data.Sigma using ( Σ≡Prop )
open import Cubical.Data.Sigma.Properties using ( ΣPathP )
open import Cubical.Foundations.Prelude using ( PathP; J; toPathP; transportRefl )
open import Cubical.Foundations.Transport using ( substSubst⁻ )
open import Cubical.HITs.PropositionalTruncation using ( squash₁ )
open import Cubical.HITs.CumulativeHierarchy.Constructions using ( module InfinitySet )
open InfinitySet using ( ω; #_ )

open hPropStructure 𝒮ᵥ
```

<!--en-->
## The composed count
<!--zh-->
## 复合计数
<!--/-->

<!--en-->
The count chapter's two injections compose into the formula-count of the
cardinal chapter: a formula over `K` with one free variable is a shape over
the empty domain together with a tuple of constants, and the shape is coded
into `ℕ`. The composition keeps the shape in the image, so its injectivity is
structural: the natural projection that drops the code and keeps the shape
and the tuple recovers the count chapter's own pair, whose injectivity is
delivered. The statement is generic in the constant domain `K`, exactly the
strength the bound below consumes.
<!--zh-->
计数章的两条单射复合出基数章的公式计数：`K` 上带一个自由变量的公式是一个空域上的形状连同一条常量元组，而形状被编入 `ℕ`。复合把形状留在像中，故其单射性是结构的：丢码而留形状与元组的自然投影还原出计数章自己的对，而它的单射性已交付。陈述对常量域 `K` 泛型，正是下文之界所要的强度。
<!--/-->

```agda
composed-count : {K : Type ℓ}
               → Σ[ f ∈ (Formula K 1 → Σ[ k ∈ ℕ ] (Formula (⊥* {ℓ}) k × (ℕ × Vec K k))) ]
                   ((φ ψ : Formula K 1) → f φ ≡ f ψ → φ ≡ ψ)
composed-count {K} = f , inj
  where
  module C = Count K
  f : Formula K 1 → Σ[ k ∈ ℕ ] (Formula (⊥* {ℓ}) k × (ℕ × Vec K k))
  f φ = let (k , (ψ , cs)) = fst C.count-inj φ in (k , (ψ , (code ψ , cs)))
  drop : Σ[ k ∈ ℕ ] (Formula (⊥* {ℓ}) k × (ℕ × Vec K k))
       → Σ[ k ∈ ℕ ] (Formula (⊥* {ℓ}) k × Vec K k)
  drop (k , (ψ , (n , cs))) = (k , (ψ , cs))
  inj : (φ ψ : Formula K 1) → f φ ≡ f ψ → φ ≡ ψ
  inj φ ψ e = snd C.count-inj {φ = φ} {ψ = ψ} (cong drop e)
```

<!--en-->
## The index reduction
<!--zh-->
## 索引归约
<!--/-->

<!--en-->
The hull's index is a `sett` over the pairs of a formula and a small
witness. The witness component is a truncation, hence a proposition, so the
first projection is an injection: two indices with the same formula carry the
same witness, since a proposition has at most one element. This is the step
that lets the count run on `Formula ⟪ X ⟫ 1` directly, without re-encoding,
exactly as the hull chapter's closing note prescribed. The lemma is stated
generic in the proposition `P`.
<!--zh-->
外壳的索引是「一条公式配一个小见证」之对上的 `sett`。见证分量是截断，故而是命题，于是第一投影是单射：公式相同的两个索引携带相同的见证，因为命题至多一个元素。正是这一步让计数直接在 `Formula ⟪ X ⟫ 1` 上跑，无须重新编码，恰如外壳一章收尾处的注记所定。引理对命题 `P` 泛型陈述。
<!--/-->

```agda
index↪formula : {K : Type ℓ} (P : Formula K 1 → Type ℓ) → ((φ : Formula K 1) → isProp (P φ))
              → Σ[ f ∈ (Σ[ φ ∈ Formula K 1 ] P φ → Formula K 1) ]
                  ((x y : Σ[ φ ∈ Formula K 1 ] P φ) → f x ≡ f y → x ≡ y)
index↪formula {K} P Pprop = (λ (φ , _) → φ) , inj
  where
  inj : (x y : Σ[ φ ∈ Formula K 1 ] P φ) → fst x ≡ fst y → x ≡ y
  inj (φ , p) (ψ , q) e = Σ≡Prop Pprop e
```

<!--en-->
## The counting bound, conditional on the square law
<!--zh-->
## 计数界，以平方律为假设
<!--/-->

<!--en-->
The bound lives at an infinite ordinal `β`, and it needs two things: the
numerals inside `β`, and the square law at `β`. The numerals are delivered by
the ordinal layer: every numeral is a member of `ω`, and `ω ⊆ β` for an
infinite `β`, so the members of `ω` inject into `⟪ β ⟫`, injectively by the
numeral code. The square law, the injection of `⟪ β ⟫ × ⟪ β ⟫` into `⟪ β ⟫`,
is exactly the shape `L.Ordinal.SquareLaw` delivers at `ω` and at successors
of delivered ordinals, and nothing beyond that. The bound is therefore built
inside a module parameterized by the law at `β`, and the call site is named
in the report: at the ordinal `β`, with the goal type
`Σ[ f ∈ (⟪ β ⟫ × ⟪ β ⟫ → ⟪ β ⟫) ] ((x y : ⟪ β ⟫ × ⟪ β ⟫) → f x ≡ f y → x ≡ y)`,
which is not proposition-valued, because the law's first component is a
function. That is precisely where the square-law chapter's extraction risk
bites: its least-of cardinal search returns equinumerosity only as a
truncation, and a truncated witness cannot supply a function.

The bound itself runs on the count's image: an arity `k`, a shape, a natural
code, and a tuple of `k` constants. It packs the arity and the two natural
coordinates through the numerals and the tuple through the iterated pairing,
into one square of `β`, and injectivity recovers each coordinate by
unpacking the pairing and the numerals. Two arity-transport stabilities are
the only new raw material: the shape-code and the tuple both commute with
transport along an arity path, each by the path induction of `J`, so a
recovered equality of arities aligns two shapes and two tuples before the
per-arity injectivities apply. The finite-tuple half of the counting bound,
the injection of `Vec K k` into `⟪ β ⟫` through `g : K ↪ ⟪ β ⟫` and the
pairing, is generic in `K`, which is what lets the hull's constants ride
through the same bound.
<!--zh-->
界住在无穷序数 `β` 处，它要两样东西：`β` 内的数码，以及 `β` 处的平方律。数码由序数层交付：每个数码都是 `ω` 的成员，而无穷 `β` 满足 `ω ⊆ β`，故 `ω` 的成员单射进入 `⟪ β ⟫`，单射性来自数码码。平方律，即 `⟪ β ⟫ × ⟪ β ⟫` 到 `⟪ β ⟫` 的单射，恰是 `L.Ordinal.SquareLaw` 在 `ω` 处及已交付序数的后继处交付的形状，此外再无。故这个界建在以 `β` 处律为参数的模块内，而调用点在报告中具名：序数 `β`，目标类型`Σ[ f ∈ (⟪ β ⟫ × ⟪ β ⟫ → ⟪ β ⟫) ] ((x y : ⟪ β ⟫ × ⟪ β ⟫) → f x ≡ f y → x ≡ y)`，它并非命题值，因为律的第一分量是函数。这正是平方律一章那个提取风险咬住的地方：其最小者基数搜索只在截断意义下交回等势，而截断的见证供不出函数。

界本身跑在计数的像上：一个元数 `k`、一个形状、一个自然码、一条 `k` 个常量的元组。它把元数与两个自然坐标经数码、把元组经迭代配对，打进 `β` 的一个平方里，而单射性靠拆开配对与数码逐坐标还原。两条元数搬运稳定性是唯一的新原料：形状码与元组都沿元数路径与搬运交换，各自由 `J` 的路径归纳给出，于是还原出的元数等式先把两个形状与两条元组对齐，再施用逐元数单射。计数界的有穷元组一半，即经 `g : K ↪ ⟪ β ⟫` 与配对把 `Vec K k` 单射进 `⟪ β ⟫` 的那半，对 `K` 泛型，这正让外壳的常量穿过同一个界。
<!--/-->

```agda
module Bound (β : S) (oβ : IsOrd β) (ω∈β : ⟨ ω ∈ˢ β ⟩)
  (pairing : Σ[ f ∈ (⟪ β ⟫ × ⟪ β ⟫ → ⟪ β ⟫) ] ((x y : ⟪ β ⟫ × ⟪ β ⟫) → f x ≡ f y → x ≡ y)) where

  pair : ⟪ β ⟫ → ⟪ β ⟫ → ⟪ β ⟫
  pair x y = fst pairing (x , y)

  pair-inj : (x y x' y' : ⟪ β ⟫) → pair x y ≡ pair x' y' → (x ≡ x') × (y ≡ y')
  pair-inj x y x' y' e = cong fst p , cong snd p
    where
    p : (x , y) ≡ (x' , y')
    p = snd pairing (x , y) (x' , y') e

  numeral : ℕ → ⟪ β ⟫
  numeral n = fiber β {x = # n} (oβ .fst (#∈ω n) ω∈β) .fst

  numeral-inj : (n m : ℕ) → numeral n ≡ numeral m → n ≡ m
  numeral-inj n m e = #-inj′ (sym (fiber β {x = # n} (oβ .fst (#∈ω n) ω∈β) .snd)
    ∙ cong (⟪ β ⟫↪) e ∙ fiber β {x = # m} (oβ .fst (#∈ω m) ω∈β) .snd)

  code-stable : (k k' : ℕ) (p : k' ≡ k) (ψ : Formula (⊥* {ℓ}) k')
              → code (subst (Formula (⊥* {ℓ})) p ψ) ≡ code ψ
  code-stable k k' p ψ =
    J (λ k p → code (subst (Formula (⊥* {ℓ})) p ψ) ≡ code ψ)
      (cong code (transportRefl ψ)) p

  tuple-g : {K : Type ℓ} (g : Σ[ f ∈ (K → ⟪ β ⟫) ] ((x y : K) → f x ≡ f y → x ≡ y))
          → (k : ℕ) → Vec K k → ⟪ β ⟫
  tuple-g g zero [] = numeral 0
  tuple-g g (suc k) (x ∷ xs) = pair (fst g x) (tuple-g g k xs)

  tuple-g-inj : {K : Type ℓ} (g : Σ[ f ∈ (K → ⟪ β ⟫) ] ((x y : K) → f x ≡ f y → x ≡ y))
              → (k : ℕ) (xs ys : Vec K k) → tuple-g g k xs ≡ tuple-g g k ys → xs ≡ ys
  tuple-g-inj g zero [] [] _ = refl
  tuple-g-inj g (suc k) (x ∷ xs) (y ∷ ys) e = cong₂ _∷_ xeq (tuple-g-inj g k xs ys xs≡ys)
    where
    p : (fst g x , tuple-g g k xs) ≡ (fst g y , tuple-g g k ys)
    p = snd pairing (fst g x , tuple-g g k xs) (fst g y , tuple-g g k ys) e
    xeq : x ≡ y
    xeq = snd g x y (cong fst p)
    xs≡ys : tuple-g g k xs ≡ tuple-g g k ys
    xs≡ys = cong snd p

  tuple-g-stable : (K : Type ℓ) (g : Σ[ f ∈ (K → ⟪ β ⟫) ] ((x y : K) → f x ≡ f y → x ≡ y))
                 → (k k' : ℕ) (p : k' ≡ k) (cs : Vec K k')
                 → tuple-g {K} g k (subst (Vec K) p cs) ≡ tuple-g {K} g k' cs
  tuple-g-stable K g k k' p cs =
    J (λ k p → tuple-g {K} g k (subst (Vec K) p cs) ≡ tuple-g {K} g k' cs)
      (cong (tuple-g {K} g k') (transportRefl cs)) p

  count-bound : {K : Type ℓ} (g : Σ[ f ∈ (K → ⟪ β ⟫) ] ((x y : K) → f x ≡ f y → x ≡ y))
              → Σ[ k ∈ ℕ ] (Formula (⊥* {ℓ}) k × (ℕ × Vec K k)) → ⟪ β ⟫
  count-bound g (k , (ψ , (n , cs))) =
    pair (numeral k) (pair (pair (numeral (code ψ)) (numeral n)) (tuple-g g k cs))

  count-bound-inj : {K : Type ℓ} (g : Σ[ f ∈ (K → ⟪ β ⟫) ] ((x y : K) → f x ≡ f y → x ≡ y))
                  → (x y : Σ[ k ∈ ℕ ] (Formula (⊥* {ℓ}) k × (ℕ × Vec K k)))
                  → count-bound g x ≡ count-bound g y → x ≡ y
  count-bound-inj {K} g (k , (ψ , (n , cs))) (k' , (ψ' , (n' , cs'))) e = outer
    where
    P : ⟪ β ⟫
    P = pair (pair (numeral (code ψ)) (numeral n)) (tuple-g g k cs)
    P' : ⟪ β ⟫
    P' = pair (pair (numeral (code ψ')) (numeral n')) (tuple-g g k' cs')
    e-out : (numeral k , P) ≡ (numeral k' , P')
    e-out = snd pairing (numeral k , P) (numeral k' , P') e
    pk : k ≡ k'
    pk = numeral-inj k k' (cong fst e-out)
    e-in : P ≡ P'
    e-in = cong snd e-out
    e-pair : (pair (numeral (code ψ)) (numeral n) , tuple-g g k cs)
           ≡ (pair (numeral (code ψ')) (numeral n') , tuple-g g k' cs')
    e-pair = snd pairing (pair (numeral (code ψ)) (numeral n) , tuple-g g k cs)
                         (pair (numeral (code ψ')) (numeral n') , tuple-g g k' cs') e-in
    e-code : code ψ ≡ code ψ'
    e-code = numeral-inj (code ψ) (code ψ')
      (cong fst (snd pairing (numeral (code ψ) , numeral n) (numeral (code ψ') , numeral n') (cong fst e-pair)))
    e-num : numeral n ≡ numeral n'
    e-num = cong snd (snd pairing (numeral (code ψ) , numeral n) (numeral (code ψ') , numeral n') (cong fst e-pair))
    qn : PathP (λ _ → ℕ) n n'
    qn = numeral-inj n n' e-num
    e-tup : tuple-g g k cs ≡ tuple-g g k' cs'
    e-tup = cong snd e-pair
    ψ₀ : Formula (⊥* {ℓ}) k
    ψ₀ = subst (Formula (⊥* {ℓ})) (sym pk) ψ'
    sψ : ψ ≡ ψ₀
    sψ = snd shape-count-inj {k = k} {φ = ψ} {ψ = ψ₀} (e-code ∙ sym (code-stable k k' (sym pk) ψ'))
    qψ : PathP (λ i → Formula (⊥* {ℓ}) (pk i)) ψ ψ'
    qψ = toPathP (cong (subst (Formula (⊥* {ℓ})) pk) sψ ∙ substSubst⁻ (Formula (⊥* {ℓ})) pk ψ')
    cs₀ : Vec K k
    cs₀ = subst (Vec K) (sym pk) cs'
    scs : cs ≡ cs₀
    scs = tuple-g-inj g k cs cs₀ (e-tup ∙ sym (tuple-g-stable K g k k' (sym pk) cs'))
    qcs : PathP (λ i → Vec K (pk i)) cs cs'
    qcs = toPathP (cong (subst (Vec K) pk) scs ∙ substSubst⁻ (Vec K) pk cs')
    inner₂ : PathP (λ i → ℕ × Vec K (pk i)) (n , cs) (n' , cs')
    inner₂ = ΣPathP {A = λ _ → ℕ} {B = λ i _ → Vec K (pk i)} (qn , qcs)
    inner₁ : PathP (λ i → Formula (⊥* {ℓ}) (pk i) × (ℕ × Vec K (pk i)))
                   (ψ , (n , cs)) (ψ' , (n' , cs'))
    inner₁ = ΣPathP {A = λ i → Formula (⊥* {ℓ}) (pk i)} {B = λ i _ → ℕ × Vec K (pk i)} (qψ , inner₂)
    outer : (k , (ψ , (n , cs))) ≡ (k' , (ψ' , (n' , cs')))
    outer = ΣPathP {A = λ _ → ℕ} {B = λ _ k → Formula (⊥* {ℓ}) k × (ℕ × Vec K k)} (pk , inner₁)

  formula-bound : {K : Type ℓ} (g : Σ[ f ∈ (K → ⟪ β ⟫) ] ((x y : K) → f x ≡ f y → x ≡ y))
                → Σ[ f ∈ (Formula K 1 → ⟪ β ⟫) ] ((φ ψ : Formula K 1) → f φ ≡ f ψ → φ ≡ ψ)
  formula-bound {K} g = f , inj
    where
    f : Formula K 1 → ⟪ β ⟫
    f φ = count-bound g (fst (composed-count {K}) φ)
    inj : (φ ψ : Formula K 1) → f φ ≡ f ψ → φ ≡ ψ
    inj φ ψ e = snd (composed-count {K}) φ ψ
      (count-bound-inj g (fst (composed-count {K}) φ) (fst (composed-count {K}) ψ) e)
```

<!--en-->
## The hull's bound
<!--zh-->
## 外壳之界
<!--/-->

<!--en-->
The hull of `X` inside the stage `Lset α` is a `sett` over the index whose
second component is the small-witness truncation. The index reduction feeds
that index into `Formula ⟪ X ⟫ 1`, and the counting bound above, instantiated
at `K = ⟪ X ⟫` with any injection `⟪ X ⟫ ↪ ⟪ β ⟫` into an infinite `β`
carrying the square law, bounds the hull by `β`. This is Devlin 5.4's upper
half, |M| ≤ max(|X|, ω), in the honest injection shape: the equality's lower
half and the bijection form are the cardinal chapter's other side, which
consumes the delivered predicates.
<!--zh-->
阶段 `Lset α` 内集合 `X` 的外壳是以索引为底的 `sett`，该索引的第二分量是小见证截断。索引归约把该索引喂进 `Formula ⟪ X ⟫ 1`，而上文的计数界在 `K = ⟪ X ⟫` 处实例化，配任何一条进入无穷且载平方律的 `β` 的单射 `⟪ X ⟫ ↪ ⟪ β ⟫`，即把外壳界住于 `β`。这就是 Devlin 5.4 的上半，`|M| ≤ max(|X|, ω)`，取诚实的单射形状：等式的下半与双射形态是基数章的另一侧，由已交付的谓词消费。
<!--/-->

```agda
module AtHull (α : S) (ordα : IsOrd α) (X : S) (X⊆L : (x : S) → ⟨ x ∈ˢ X ⟩ → ⟨ x ∈ˢ Lset α ⟩) where

  module H = Hull.AtStage α ordα

  Ltr : isTransV (Lset α)
  Ltr = layer-trans (Lset-layer α)

  module HullX = H.AtM.Hull (Lset α) Ltr (λ x x∈ → x∈) X X⊆L

  Index : Type ℓ
  Index = Σ[ φ ∈ Formula ⟪ X ⟫ 1 ] HullX.Witnessed-small φ

  idx-prop : (φ : Formula ⟪ X ⟫ 1) → isProp (HullX.Witnessed-small φ)
  idx-prop φ = squash₁

  hull-index : Σ[ f ∈ (Index → Formula ⟪ X ⟫ 1) ] ((x y : Index) → f x ≡ f y → x ≡ y)
  hull-index = index↪formula HullX.Witnessed-small idx-prop

  hull-bound : (β : S) → IsOrd β → ⟨ ω ∈ˢ β ⟩
             → (g : Σ[ f ∈ (⟪ X ⟫ → ⟪ β ⟫) ] ((x y : ⟪ X ⟫) → f x ≡ f y → x ≡ y))
             → (pairing : Σ[ f ∈ (⟪ β ⟫ × ⟪ β ⟫ → ⟪ β ⟫) ] ((x y : ⟪ β ⟫ × ⟪ β ⟫) → f x ≡ f y → x ≡ y))
             → Σ[ f ∈ (Index → ⟪ β ⟫) ] ((x y : Index) → f x ≡ f y → x ≡ y)
  hull-bound β oβ ω∈β g pairing = f , inj
    where
    module B = Bound β oβ ω∈β pairing
    fb : Σ[ f ∈ (Formula ⟪ X ⟫ 1 → ⟪ β ⟫) ] ((φ ψ : Formula ⟪ X ⟫ 1) → f φ ≡ f ψ → φ ≡ ψ)
    fb = B.formula-bound {K = ⟪ X ⟫} g
    f : Index → ⟪ β ⟫
    f i = fst fb (fst hull-index i)
    inj : (x y : Index) → f x ≡ f y → x ≡ y
    inj x y e = snd hull-index x y (snd fb (fst hull-index x) (fst hull-index y) e)
```

<!--en-->
## Recap
<!--zh-->
## 小结
<!--/-->

<!--en-->
The chapter delivers the counting side of the cardinal chapter in three
pieces. The composed count injects the one-free-variable formulas over any
domain into the arity-indexed image of a shape, its code, and a tuple. The
index reduction injects any propositionally-witnessed index into the formula
family, which is the step that lets the count run on the hull's own index.
The counting bound then injects the count's image into an infinite ordinal
`β`, conditional on the square law at `β`; everything before the law is
proved, and the law itself is named as the call site with its ordinal and its
goal type. The hull's bound assembles the three: for every infinite `β` with
the square law and an injection of `⟪ X ⟫` into `⟪ β ⟫`, the hull injects
into `⟪ β ⟫`, which is Devlin 5.4's upper half in the honest injection shape.
<!--zh-->
本章以三件交付基数章的计数侧。复合计数把任意域上带一个自由变量的公式单射进「形状、码、元组」的按元数索引之像。索引归约把任意带命题见证的索引单射进公式族，这一步让计数得以跑在外壳自己的索引上。计数界随即把计数的像单射进无穷序数 `β`，以 `β` 处平方律为假设；律之前的一切证毕，律本身以调用点身份连同其序数与目标类型被具名。外壳之界把三者组装：对每个载平方律且带 `⟪ X ⟫` 到 `⟪ β ⟫` 单射的无穷 `β`，外壳单射进 `⟪ β ⟫`，即 Devlin 5.4 上半取诚实的单射形状。
<!--/-->
