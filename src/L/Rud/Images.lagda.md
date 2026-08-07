# The image half of the rud operations

<!--en-->
The operations layer of the rud trunk splits in half, and this chapter is the
image half: seven of the sixteen basis functions of Schindler-Zeman's list
(SZ p. 10), stated as total operations on the cumulative hierarchy with
extension specifications. `F8` and `F10` are the image constructions, where
`x"{y}` collects the second components of the pairs in `x` whose first
component is `y`. `F11`-`F14` shuffle a third component into a pair through
the left and right projections, and `F15` is the relativization slot
`A ∩ x`, matching Devlin's `F9` shape (Dev VI.1.12). Nothing is assumed:
every operation is built from the `sett` machinery, and every specification
is a membership equivalence proved from the hierarchy's own classification
axioms.
<!--zh-->
初步函数的运算层一分为二，本章是其中像的一半：Schindler-Zeman 清单 (SZ p. 10) 的十六个基函数中的七个，全部陈述为累积层级上的全函数并配以外延规格。`F8` 与 `F10` 是像的构造，其中 `x"{y}` 收集 `x` 中首分量为 `y` 的那些对的第二分量。`F11`-`F14` 经左右投影把第三个分量塞进一个对，`F15` 则是相对化槽 `A ∩ x`，对应 Devlin 的 `F9` 形状 (Dev VI.1.12)。此处无一假设：每个运算都由 `sett` 机制造出，每条规格都是从层级自己的分类公理证明出来的成员等价。
<!--/-->

<!--en-->
The module is level-generic over the hierarchy's universe `ℓ`{.Agda}. It
reuses the coding chapter's pairing kit (`pr`{.Agda} with its injectivity)
and the hierarchy's own constructions: `sett`{.Agda} builds sets from small
families, the union and pairing axioms classify their membership, and
separation cuts a set by a small predicate. The truth algebra supplies the
logic connectives that the specifications are written with.
<!--zh-->
本模块在层级的宇宙 `ℓ`{.Agda} 上是层泛的。它复用编码章的配对器材 (`pr`{.Agda} 及其单射性) 与层级自己的构造：`sett`{.Agda} 以小族造集，并与配对公理分类其成员关系，分离则按小谓词切集。规格所用的逻辑联结词由真值代数供应。
<!--/-->

```agda
{-# OPTIONS --cubical --safe --guardedness #-}

open import Base.Prelude
open import Base.Truth

module L.Rud.Images {ℓ : Level} where

open import V.Coding {ℓ} using ( pr; pr-inj )
open import Cubical.Data.Sum using ( _⊎_; inl; inr )
import Cubical.HITs.PropositionalTruncation as PT
open PT using ( ∣_∣₁ )
open import Cubical.Functions.Logic using ( ⇔toPath; ∃[]-syntax )
open import Cubical.Foundations.Equiv using ( equivFun )
open import Cubical.HITs.CumulativeHierarchy.Base using ( V; _∈_; sett; setIsSet )
open import Cubical.HITs.CumulativeHierarchy.Properties
  using ( _∈ₛ_; ∈∈ₛ; ⟪_⟫; ⟪_⟫↪; ∈ₛ⟪_⟫↪_; _≡ₕ_; _⊆_; extensionality
        ; identityPrinciple; ix∈ₛ )
-- lint-agda: keep (used qualified: SetPackage.classification)
open import Cubical.HITs.CumulativeHierarchy.Constructions
  using ( ⁅_,_⁆; pairing-ax; ⋃_; union-ax; ⁅_⁆s; SingletonPackage; SetPackage )
open import Cubical.HITs.CumulativeHierarchy.Constructions
  using ( ⁅_∶_⁆; separation-ax; ∅; ∅-empty )
import Cubical.Data.Empty as Empty

open TruthAlgebra (hPropAlgebra (ℓ-suc ℓ))
```

<!--en-->
## The pairing kit: left and right
<!--zh-->
## 配对器材：left 与 right
<!--/-->

<!--en-->
The first construction is the intersection of a set, the common membership
that a left projection reads. `⋂ z` is the `sett` of the unions `⋃ u` of
the members `u` of `z`, keeping only those that lie in every member of `z`;
at a Kuratowski pair `pr a b` the member `⁅ a ⁆s` contributes `a`, which
also lies in `⁅ a , b ⁆`, so the intersection is the singleton `⁅ a ⁆s`.
The pair memberships below are the recurring atoms of this chapter: each
one names a member of a Kuratowski pair through the hierarchy's pairing
axiom.
<!--zh-->
第一个构造是集合的交，即左投影读取的那种公共成员关系。`⋂ z` 是 `z` 的成员 `u` 之并 `⋃ u` 的 `sett`，只保留落在 `z` 的每个成员之内的那些并；在 Kuratowski 对 `pr a b` 上，成员 `⁅ a ⁆s` 贡献 `a`，而 `a` 也在 `⁅ a , b ⁆` 中，于是交集就是单点集 `⁅ a ⁆s`。下面的对成员关系是本章反复出现的原子：每一条都经层级的配对公理点出 Kuratowski 对的一个成员。
<!--/-->

```agda
private
  -- the index of a small membership, with the path back to the member
  fibre : (b a : V ℓ) → ⟨ a ∈ₛ b ⟩ → Σ[ m ∈ ⟪ b ⟫ ] (⟪ b ⟫↪ m ≡ a)
  fibre b a h = h .fst , equivFun identityPrinciple (h .snd)

  ∈singl : {a x : V ℓ} → ⟨ x ∈ₛ ⁅ a ⁆s ⟩ → x ≡ a
  ∈singl {a} {x} = SetPackage.classification (SingletonPackage a) x .fst

  singl∈ : {a x : V ℓ} → x ≡ a → ⟨ x ∈ₛ ⁅ a ⁆s ⟩
  singl∈ {a} {x} = SetPackage.classification (SingletonPackage a) x .snd

  singl∈pr : (a b : V ℓ) → ⟨ ⁅ a ⁆s ∈ₛ pr a b ⟩
  singl∈pr a b = pairing-ax (⁅ a ⁆s) (⁅ a , b ⁆) (⁅ a ⁆s) .snd ∣ inl refl ∣₁

  pair∈pr : (a b : V ℓ) → ⟨ ⁅ a , b ⁆ ∈ₛ pr a b ⟩
  pair∈pr a b = pairing-ax (⁅ a ⁆s) (⁅ a , b ⁆) (⁅ a , b ⁆) .snd ∣ inr refl ∣₁

  a∈⁅a⁆s : (a : V ℓ) → ⟨ a ∈ₛ ⁅ a ⁆s ⟩
  a∈⁅a⁆s a = singl∈ refl

  a∈⁅a,b⁆ : (a b : V ℓ) → ⟨ a ∈ₛ ⁅ a , b ⁆ ⟩
  a∈⁅a,b⁆ a b = pairing-ax a b a .snd ∣ inl refl ∣₁

  v∈⁅y,v⁆ : (y v : V ℓ) → ⟨ v ∈ₛ ⁅ y , v ⁆ ⟩
  v∈⁅y,v⁆ y v = pairing-ax y v v .snd ∣ inr refl ∣₁

⋂ : V ℓ → V ℓ
⋂ z = sett (Σ[ m ∈ ⟪ z ⟫ ] ((k : ⟪ z ⟫) → ⟨ ⋃ (⟪ z ⟫↪ m) ∈ₛ ⟪ z ⟫↪ k ⟩))
           (λ p → ⋃ (⟪ z ⟫↪ (p .fst)))

private
  a∈members : (a b : V ℓ) (n : ⟪ pr a b ⟫) → ⟨ a ∈ₛ ⟪ pr a b ⟫↪ n ⟩
  a∈members a b n = PT.rec (snd (a ∈ₛ ⟪ pr a b ⟫↪ n))
    (λ { (inl e) → subst (λ t → ⟨ a ∈ₛ t ⟩) (sym e) (a∈⁅a⁆s a)
       ; (inr e) → subst (λ t → ⟨ a ∈ₛ t ⟩) (sym e) (a∈⁅a,b⁆ a b) })
    (pairing-ax (⁅ a ⁆s) (⁅ a , b ⁆) (⟪ pr a b ⟫↪ n) .fst (∈ₛ⟪ pr a b ⟫↪ n))

  ⋃singl : (a : V ℓ) → ⋃ ⁅ a ⁆s ≡ a
  ⋃singl a = extensionality (⋃ ⁅ a ⁆s) a (sub₁ , sub₂)
    where
    sub₁ : ⟨ ⋃ ⁅ a ⁆s ⊆ a ⟩
    sub₁ w w∈ₛ = PT.rec (snd (w ∈ₛ a))
      (λ { (v , (v∈ₛs , w∈v)) → subst (λ t → ⟨ w ∈ₛ t ⟩) (∈singl v∈ₛs) w∈v })
      (union-ax ⁅ a ⁆s w .fst w∈ₛ)
    sub₂ : ⟨ a ⊆ ⋃ ⁅ a ⁆s ⟩
    sub₂ w w∈ₛa = union-ax ⁅ a ⁆s w .snd ∣ a , (a∈⁅a⁆s a , w∈ₛa) ∣₁

  ⋂pair : (a b : V ℓ) → ⋂ (pr a b) ≡ ⁅ a ⁆s
  ⋂pair a b = extensionality (⋂ (pr a b)) (⁅ a ⁆s) (sub₁ , sub₂)
    where
    fs : Σ[ m ∈ ⟪ pr a b ⟫ ] (⟪ pr a b ⟫↪ m ≡ ⁅ a ⁆s)
    fs = fibre (pr a b) (⁅ a ⁆s) (singl∈pr a b)
    sub₁ : ⟨ ⋂ (pr a b) ⊆ ⁅ a ⁆s ⟩
    sub₁ w w∈ₛ⋂ = singl∈ (PT.rec (setIsSet w a) go
      (∈∈ₛ {a = w} {b = ⋂ (pr a b)} .snd w∈ₛ⋂))
      where
      go : Σ[ p ∈ (Σ[ m ∈ ⟪ pr a b ⟫ ]
                     ((k : ⟪ pr a b ⟫) → ⟨ ⋃ (⟪ pr a b ⟫↪ m) ∈ₛ ⟪ pr a b ⟫↪ k ⟩)) ]
             (⋃ (⟪ pr a b ⟫↪ (p .fst)) ≡ w)
         → w ≡ a
      go (p , q) = ∈singl (subst (λ t → ⟨ w ∈ₛ t ⟩) (fs .snd)
        (subst (λ t → ⟨ t ∈ₛ ⟪ pr a b ⟫↪ (fs .fst) ⟩) q (p .snd (fs .fst))))
    sub₂ : ⟨ ⁅ a ⁆s ⊆ ⋂ (pr a b) ⟩
    sub₂ w w∈singl = subst (λ t → ⟨ t ∈ₛ ⋂ (pr a b) ⟩)
      (fp ∙ sym (∈singl w∈singl)) (ix∈ₛ (fs .fst , prop))
      where
      fp : ⋃ (⟪ pr a b ⟫↪ (fs .fst)) ≡ a
      fp = cong ⋃_ (fs .snd) ∙ ⋃singl a
      prop : (k : ⟪ pr a b ⟫) → ⟨ ⋃ (⟪ pr a b ⟫↪ (fs .fst)) ∈ₛ ⟪ pr a b ⟫↪ k ⟩
      prop k = subst (λ t → ⟨ t ∈ₛ ⟪ pr a b ⟫↪ k ⟩) (sym fp) (a∈members a b k)
```

<!--en-->
The left projection reads the intersection: `left z` is the union of `⋂ z`,
so on a pair it is the first component. The projection is total, and on
non-pairs it is junk; only the pair equation is ever used.
<!--zh-->
左投影读取交集：`left z` 是 `⋂ z` 之并，于是在对上它取第一分量。投影是全函数，在非对上取值是垃圾；只有对等式会被使用。
<!--/-->

```agda
-- perf: transparent left re-normalized the ⋂ presentation per consumer
-- use (rightSlice-pair 16.5s, sub₂ 15.7s, b∈ₛR 9.0s, sub₁ 8.9s)
opaque
  left : V ℓ → V ℓ
  left z = ⋃ (⋂ z)

  left-spec : (a b : V ℓ) → left (pr a b) ≡ a
  left-spec a b = cong ⋃_ (⋂pair a b) ∙ ⋃singl a
  left-compute : (b : V ℓ) → left b ≡ ⋃ (⋂ b)
  left-compute b = refl
```

<!--en-->
The right projection reads through the left: `right z` extracts the second
component of each member of `z`, keeps the extractions whose pair with
`left z` is `z` itself, and unions them. On `pr a b` the members are
`⁅ a ⁆s` and `⁅ a , b ⁆`; the second component of the pair member is `b`,
and `pr a b` is the singleton of `z`, so the collection is `⁅ b ⁆s`, by
injectivity of pairing. On non-pairs it is junk, and the spec below is
used only at pairs.
<!--zh-->
右投影经左分量读取：`right z` 提取 `z` 每个成员的第二分量，只保留与 `left z` 成对后等于 `z` 自身的那些提取结果并求并。在 `pr a b` 上成员是 `⁅ a ⁆s` 与 `⁅ a , b ⁆`；对成员的提取结果是 `b`，而 `pr a b` 恰是 `z` 的单点集，故收集到 `⁅ b ⁆s`，靠配对单射。在非对上取值是垃圾，下面的规格只在对上使用。
<!--/-->

```agda
private
  sepSet : (u y : V ℓ) → V ℓ
  sepSet u y = ⁅ u ∶ (λ v → ⁅ y , v ⁆ ∈ₛ ⁅ u ⁆s) ⁆

  sndExtract : (u y : V ℓ) → V ℓ
  sndExtract u y = ⋃ (sepSet u y)

  pair-eq-snd : (y w v : V ℓ) → ⁅ y , w ⁆ ≡ ⁅ y , v ⁆ → w ≡ v
  pair-eq-snd y w v p = PT.rec2 (setIsSet w v) go H₁ H₂
    where
    v∈ₛyw : ⟨ v ∈ₛ ⁅ y , w ⁆ ⟩
    v∈ₛyw = subst (λ t → ⟨ v ∈ₛ t ⟩) (sym p) (v∈⁅y,v⁆ y v)
    w∈ₛyv : ⟨ w ∈ₛ ⁅ y , v ⁆ ⟩
    w∈ₛyv = subst (λ t → ⟨ w ∈ₛ t ⟩) p (v∈⁅y,v⁆ y w)
    H₁ : ⟨ (v ≡ₕ y) ⊔ (v ≡ₕ w) ⟩
    H₁ = pairing-ax y w v .fst v∈ₛyw
    H₂ : ⟨ (w ≡ₕ y) ⊔ (w ≡ₕ v) ⟩
    H₂ = pairing-ax y v w .fst w∈ₛyv
    go : (⟨ v ≡ₕ y ⟩ ⊎ ⟨ v ≡ₕ w ⟩) → (⟨ w ≡ₕ y ⟩ ⊎ ⟨ w ≡ₕ v ⟩) → w ≡ v
    go (inl vy) (inl wy) = wy ∙ sym vy
    go (inl vy) (inr wv) = wv
    go (inr vw) _        = sym vw

  sepSet-pair : (y v : V ℓ) → sepSet (⁅ y , v ⁆) y ≡ ⁅ v ⁆s
  sepSet-pair y v = extensionality (sepSet (⁅ y , v ⁆) y) (⁅ v ⁆s) (sub₁ , sub₂)
    where
    ϕ : V ℓ → hProp ℓ
    ϕ w = ⁅ y , w ⁆ ∈ₛ ⁅ ⁅ y , v ⁆ ⁆s
    sub₁ : ⟨ sepSet (⁅ y , v ⁆) y ⊆ ⁅ v ⁆s ⟩
    sub₁ w w∈ₛ = singl∈ (pair-eq-snd y w v (∈singl ϕw))
      where
      ϕw : ⟨ ϕ w ⟩
      ϕw = separation-ax (⁅ y , v ⁆) ϕ w .fst w∈ₛ .snd
    sub₂ : ⟨ ⁅ v ⁆s ⊆ sepSet (⁅ y , v ⁆) y ⟩
    sub₂ w w∈singl = separation-ax (⁅ y , v ⁆) ϕ w .snd (w∈u , ϕw)
      where
      w≡v : w ≡ v
      w≡v = ∈singl w∈singl
      w∈u : ⟨ w ∈ₛ ⁅ y , v ⁆ ⟩
      w∈u = subst (λ t → ⟨ t ∈ₛ ⁅ y , v ⁆ ⟩) (sym w≡v) (v∈⁅y,v⁆ y v)
      ϕw : ⟨ ϕ w ⟩
      ϕw = singl∈ (cong (λ t → ⁅ y , t ⁆) w≡v)

  sndExtract-pair : (y v : V ℓ) → sndExtract (⁅ y , v ⁆) y ≡ v
  sndExtract-pair y v = cong ⋃_ (sepSet-pair y v) ∙ ⋃singl v

  rightSlice : (z : V ℓ) → V ℓ
  rightSlice z = sett (Σ[ m ∈ ⟪ z ⟫ ] ⟨ pr (left z) (sndExtract (⟪ z ⟫↪ m) (left z)) ∈ₛ ⁅ z ⁆s ⟩)
                      (λ p → sndExtract (⟪ z ⟫↪ (p .fst)) (left z))

right : V ℓ → V ℓ
right z = ⋃ (rightSlice z)

private
  rightSlice-pair : (a b : V ℓ) → rightSlice (pr a b) ≡ ⁅ b ⁆s
  rightSlice-pair a b = extensionality (rightSlice (pr a b)) (⁅ b ⁆s) (sub₁ , sub₂)
    where
    fp : Σ[ m ∈ ⟪ pr a b ⟫ ] (⟪ pr a b ⟫↪ m ≡ ⁅ a , b ⁆)
    fp = fibre (pr a b) (⁅ a , b ⁆) (pair∈pr a b)
    sub₁ : ⟨ rightSlice (pr a b) ⊆ ⁅ b ⁆s ⟩
    sub₁ w w∈ₛ = singl∈ (PT.rec (setIsSet w b) go
      (∈∈ₛ {a = w} {b = rightSlice (pr a b)} .snd w∈ₛ))
      where
      go : Σ[ p ∈ (Σ[ m ∈ ⟪ pr a b ⟫ ]
                     ⟨ pr (left (pr a b)) (sndExtract (⟪ pr a b ⟫↪ m) (left (pr a b))) ∈ₛ ⁅ pr a b ⁆s ⟩) ]
             (sndExtract (⟪ pr a b ⟫↪ (p .fst)) (left (pr a b)) ≡ w)
         → w ≡ b
      go (p , q) = sym q ∙ snd≡b
        where
        h1 : ⟨ pr a (sndExtract (⟪ pr a b ⟫↪ (p .fst)) (left (pr a b))) ∈ₛ ⁅ pr a b ⁆s ⟩
        h1 = subst (λ l → ⟨ pr l (sndExtract (⟪ pr a b ⟫↪ (p .fst)) (left (pr a b))) ∈ₛ ⁅ pr a b ⁆s ⟩)
              (left-spec a b) (p .snd)
        snd≡b : sndExtract (⟪ pr a b ⟫↪ (p .fst)) (left (pr a b)) ≡ b
        snd≡b = pr-inj (∈singl h1) .snd
    sub₂ : ⟨ ⁅ b ⁆s ⊆ rightSlice (pr a b) ⟩
    sub₂ w w∈singl = subst (λ t → ⟨ t ∈ₛ rightSlice (pr a b) ⟩)
      (sym (∈singl w∈singl)) b∈ₛR
      where
      se-path : sndExtract (⟪ pr a b ⟫↪ (fp .fst)) (left (pr a b)) ≡ b
      se-path = cong (λ t → sndExtract t (left (pr a b))) (fp .snd)
              ∙ subst (λ l → sndExtract (⁅ a , b ⁆) l ≡ b) (sym (left-spec a b))
                      (sndExtract-pair a b)
      h2 : ⟨ pr (left (pr a b)) b ∈ₛ ⁅ pr a b ⁆s ⟩
      h2 = subst (λ l → ⟨ pr l b ∈ₛ ⁅ pr a b ⁆s ⟩) (sym (left-spec a b)) (singl∈ refl)
      h : ⟨ pr (left (pr a b)) (sndExtract (⟪ pr a b ⟫↪ (fp .fst)) (left (pr a b))) ∈ₛ ⁅ pr a b ⁆s ⟩
      h = subst (λ t → ⟨ pr (left (pr a b)) t ∈ₛ ⁅ pr a b ⁆s ⟩) (sym se-path) h2
      b∈ₛR : ⟨ b ∈ₛ rightSlice (pr a b) ⟩
      b∈ₛR = subst (λ t → ⟨ t ∈ₛ rightSlice (pr a b) ⟩) se-path (ix∈ₛ (fp .fst , h))

opaque
  right-spec : (a b : V ℓ) → right (pr a b) ≡ b
  right-spec a b = cong ⋃_ (rightSlice-pair a b) ∙ ⋃singl b
```

<!--en-->
## F10: one image set
<!--zh-->
## F10：单个像集
<!--/-->

<!--en-->
The image set `F10 x y = x"{y}` collects the second components of the pairs
of `x` whose first component is `y`. It is a `sett` over the small
representation of `x`: each member `z` contributes its right projection,
and the index keeps only the contributions `w` whose pair `pr y w` is a
member of `x`. On a pair `pr y v` the right projection is exactly `v`, so
the members are precisely the `v` with `pr y v ∈ₛ x`. The specification
below is the inner content that `F8`'s will quantify over.
<!--zh-->
像集 `F10 x y = x"{y}` 收集 `x` 中首分量为 `y` 的那些对的第二分量。它是 `x` 的小表示上的一个 `sett`：每个成员 `z` 贡献其右投影，索引再只保留「`pr y w` 属于 `x`」的贡献 `w`。在对 `pr y v` 上右投影恰为 `v`，故成员恰是满足 `pr y v ∈ₛ x` 的那些 `v`。下面的规格正是 `F8` 的规格将要量化的内部内容。
<!--/-->

```agda
F10 : V ℓ → V ℓ → V ℓ
F10 x y = sett (Σ[ m ∈ ⟪ x ⟫ ] ⟨ pr y (right (⟪ x ⟫↪ m)) ∈ₛ x ⟩)
               (λ p → right (⟪ x ⟫↪ (p .fst)))

F10-spec : (x y v : V ℓ) → (v ∈ F10 x y) ≡ (pr y v ∈ x)
F10-spec x y v = ⇔toPath fwd bwd
  where
  fwd : ⟨ v ∈ F10 x y ⟩ → ⟨ pr y v ∈ x ⟩
  fwd = PT.rec (snd (pr y v ∈ x))
    (λ { ((_ , h) , q) → ∈∈ₛ {a = pr y v} {b = x} .snd
      (subst (λ t → ⟨ pr y t ∈ₛ x ⟩) q h) })
  bwd : ⟨ pr y v ∈ x ⟩ → ⟨ v ∈ F10 x y ⟩
  bwd pr∈x = ∣ (f .fst , h) , cong right (f .snd) ∙ right-spec y v ∣₁
    where
    h₀ : ⟨ pr y v ∈ₛ x ⟩
    h₀ = ∈∈ₛ {a = pr y v} {b = x} .fst pr∈x
    f : Σ[ m ∈ ⟪ x ⟫ ] (⟪ x ⟫↪ m ≡ pr y v)
    f = fibre x (pr y v) h₀
    h : ⟨ pr y (right (⟪ x ⟫↪ (f .fst))) ∈ₛ x ⟩
    h = subst (λ t → ⟨ pr y (right t) ∈ₛ x ⟩) (sym (f .snd))
          (subst (λ u → ⟨ pr y u ∈ₛ x ⟩) (sym (right-spec y v)) h₀)
```

<!--en-->
## F8: the image collection
<!--zh-->
## F8：像的收集
<!--/-->

<!--en-->
The collection `F8 x y` gathers one slice `F10 x z` per member `z` of `y`,
as a `sett` over the small representation of `y`. This is the image half's
load-bearing operation, Mathias's `R8`: it is the single function
separating the Gandy-Jensen world from the Devlin Basic world (MB 2.0,
p. 13; WS 1.12, p. 11). Its specification is stated over the small index
type: `w` lies in the collection exactly when it equals the slice
`F10 x (⟪ y ⟫↪ m)` for some index `m`, which is the same as the classical
reading, one member `z` of `y` with `w = x"{z}`, because every member of
`y` is the image of an index. The inner shape is the one that
`F10-spec`{.Agda} already states.
<!--zh-->
收集 `F8 x y` 为 `y` 的每个成员 `z` 收拢一个切片 `F10 x z`，即 `y` 的小表示上的一个 `sett`。这是像半的承重运算，即 Mathias 的 `R8`：它是把 Gandy-Jensen 世界与 Devlin Basic 世界分开的那唯一一个函数 (MB 2.0, p. 13; WS 1.12, p. 11)。其规格对小索引类型陈述：`w` 属于该收集，恰在它等于某个索引 `m` 的切片 `F10 x (⟪ y ⟫↪ m)` 之时，这与经典读法，存在 `y` 中的成员 `z` 使 `w = x"{z}`，是同一件事，因为 `y` 的每个成员都是某个索引的像。内层形状即 `F10-spec`{.Agda} 已经陈述的那一条。
<!--/-->

```agda
F8 : V ℓ → V ℓ → V ℓ
F8 x y = sett ⟪ y ⟫ (λ m → F10 x (⟪ y ⟫↪ m))

F8-spec : (x y w : V ℓ) → (w ∈ F8 x y) ≡ (∃[ m ] (F10 x (⟪ y ⟫↪ m) ≡ₕ w))
F8-spec x y w = ⇔toPath fwd bwd
  where
  fwd : ⟨ w ∈ F8 x y ⟩ → ⟨ (∃[ m ] (F10 x (⟪ y ⟫↪ m) ≡ₕ w)) ⟩
  fwd = PT.rec (snd (∃[ m ] (F10 x (⟪ y ⟫↪ m) ≡ₕ w))) ∣_∣₁
  bwd : ⟨ (∃[ m ] (F10 x (⟪ y ⟫↪ m) ≡ₕ w)) ⟩ → ⟨ w ∈ F8 x y ⟩
  bwd = PT.rec (snd (w ∈ F8 x y)) ∣_∣₁
```

<!--en-->
## F11-F14: the tuple plumbing
<!--zh-->
## F11-F14：三元组管道
<!--/-->

<!--en-->
The four tuple operations read the pair decomposition of their second
argument. The triple convention of this development is the right-nested
pair `⟨a, b, c⟩ = pr a (pr b c)`, stated here once and used throughout.
`F11` puts `x` in the middle of `y`'s components, `F12` at the end, and
`F13`/`F14` form the unordered pair of `left y` with the two-component
pair in which `x` is second or first. The definitions are total; on a
non-pair `y` the projections return junk. Each specification quantifies
over the pair decomposition `y ≡ pr a b`, and no pairhood guard is built
into the operation.
<!--zh-->
这四个三元组运算读取其第二实参的对分解。本发展的三元组约定是右嵌套对 `⟨a, b, c⟩ = pr a (pr b c)`，此处一次声明，全程使用。`F11` 把 `x` 放进 `y` 两个分量的中间，`F12` 放到末尾，`F13`/`F14` 则形成 `left y` 与一个二元对的无序对，其中 `x` 分别位居第二或第一。定义是全函数；在非对 `y` 上投影返回垃圾。每条规格都对对分解 `y ≡ pr a b` 量化，运算中不设对性守卫。
<!--/-->

```agda
F11 : V ℓ → V ℓ → V ℓ
F11 x y = pr (left y) (pr x (right y))

F12 : V ℓ → V ℓ → V ℓ
F12 x y = pr (left y) (pr (right y) x)

F13 : V ℓ → V ℓ → V ℓ
F13 x y = ⁅ left y , pr (right y) x ⁆

F14 : V ℓ → V ℓ → V ℓ
F14 x y = ⁅ left y , pr x (right y) ⁆

private
  leftAt : {y a b : V ℓ} → y ≡ pr a b → left y ≡ a
  leftAt {y} {a} {b} y≡ = subst (λ t → left t ≡ a) (sym y≡) (left-spec a b)

  rightAt : {y a b : V ℓ} → y ≡ pr a b → right y ≡ b
  rightAt {y} {a} {b} y≡ = subst (λ t → right t ≡ b) (sym y≡) (right-spec a b)

F11-spec : (x y a b : V ℓ) → y ≡ pr a b → F11 x y ≡ pr a (pr x b)
F11-spec x y a b y≡ = cong₂ (λ l r → pr l (pr x r)) (leftAt y≡) (rightAt y≡)

F12-spec : (x y a b : V ℓ) → y ≡ pr a b → F12 x y ≡ pr a (pr b x)
F12-spec x y a b y≡ = cong₂ (λ l r → pr l (pr r x)) (leftAt y≡) (rightAt y≡)

F13-spec : (x y a b : V ℓ) → y ≡ pr a b → F13 x y ≡ ⁅ a , pr b x ⁆
F13-spec x y a b y≡ = cong₂ (λ l r → ⁅ l , pr r x ⁆) (leftAt y≡) (rightAt y≡)

F14-spec : (x y a b : V ℓ) → y ≡ pr a b → F14 x y ≡ ⁅ a , pr x b ⁆
F14-spec x y a b y≡ = cong₂ (λ l r → ⁅ l , pr x r ⁆) (leftAt y≡) (rightAt y≡)
```

<!--en-->
## F15: the relativization slot
<!--zh-->
## F15：相对化槽
<!--/-->

<!--en-->
The relativized basis adds one predicate slot `A`, and the corresponding
operation is the intersection `F15 A x = A ∩ x`, matching Devlin's
extended basis lemma `F9(x, y) = A ∩ x` (Dev VI.1.12). The slot enters as
a module parameter: `F15Of`{.Agda} takes a set `A` of the hierarchy and
cuts `x` by membership in `A`, using the library's separation
construction. The unrelativized trunk instantiates `A` as the empty set at
assembly, never here.
<!--zh-->
相对化基函数增加一个谓词槽 `A`，对应运算即交集 `F15 A x = A ∩ x`，匹配 Devlin 扩展基函数引理 `F9(x, y) = A ∩ x` (Dev VI.1.12)。槽以模块参数进场：`F15Of`{.Agda} 取层级的一个集合 `A`，用库的分离构造按 `A` 的成员关系切割 `x`。非相对化的主干在合龙处把 `A` 实例化为空集，绝不在此处。
<!--/-->

```agda
module F15Of (A : V ℓ) where
  F15 : V ℓ → V ℓ
  F15 x = ⁅ x ∶ (λ u → u ∈ₛ A) ⁆

  F15-spec : (x u : V ℓ) → (u ∈ F15 x) ≡ (u ∈ x) ⊓ (u ∈ A)
  F15-spec x u = ⇔toPath fwd bwd
    where
    fwd : ⟨ u ∈ F15 x ⟩ → ⟨ (u ∈ x) ⊓ (u ∈ A) ⟩
    fwd u∈F = ∈∈ₛ {a = u} {b = x} .snd (sep .fst) , ∈∈ₛ {a = u} {b = A} .snd (sep .snd)
      where
      sep : ⟨ u ∈ₛ x ⟩ × ⟨ u ∈ₛ A ⟩
      sep = separation-ax x (λ u → u ∈ₛ A) u .fst (∈∈ₛ {a = u} {b = F15 x} .fst u∈F)
    bwd : ⟨ (u ∈ x) ⊓ (u ∈ A) ⟩ → ⟨ u ∈ F15 x ⟩
    bwd (u∈x , u∈A) = ∈∈ₛ {a = u} {b = F15 x} .snd
      (separation-ax x (λ u → u ∈ₛ A) u .snd
        (∈∈ₛ {a = u} {b = x} .fst u∈x , ∈∈ₛ {a = u} {b = A} .fst u∈A))
```

<!--en-->
## Recap
<!--zh-->
## 小结
<!--/-->

<!--en-->
Seven operations, all total, all specified extensionally. The pairing kit
contributes the projections `left`{.Agda} and `right`{.Agda} with their
pair equations; `F10`{.Agda} builds one image slice and `F8`{.Agda} the
collection of slices; `F11`-`F14` shuffle components through the pair
decomposition; `F15`{.Agda} is the relativization slot, parameterized by
the predicate set `A`. The other half of the operations layer states the
remaining nine functions in the same shape, and the hierarchy engine will
consume these specifications as its one-step images.
<!--zh-->
七个运算，全部全函数，全部以外延方式规格化。配对器材贡献了投影 `left`{.Agda} 与 `right`{.Agda} 及其对等式；`F10`{.Agda} 造出单个像片，`F8`{.Agda} 造出片的收集；`F11`-`F14` 经对分解搬运分量；`F15`{.Agda} 是相对化槽，以谓词集 `A` 为参数。运算层的另一半将以同样形状陈述其余九个函数，层级引擎将消费这些规格作为其单步像。
<!--/-->

<!--en-->
## The non-pair junk readings
<!--zh-->
## 非对的垃圾读取
<!--/-->

<!--en-->
The projections are total, so on a non-pair they return junk, and the
concrete step batch needs the junk characterised. The right projection of
`b` is built from the right slice, whose every witness would exhibit `b` as
an ordered pair; under a non-pair hypothesis the slice is empty and
`right b` is the empty set. The left projection reads the intersection: a
member `c` of `⋂ b` lies in every member of `b`, and the intersection has at
most one distinct member, so `left b` either collapses onto such a `c` or is
the empty set. These are read lemmas in the same shape as the operations
chapter's appendix: each is sealed `opaque`{.Agda} with an explicit type and
proved from the private machinery in scope, and nothing existing is
changed, renamed, or unsealed.
<!--zh-->
投影是全函数，在非对上取值即垃圾，具体 step 批次需要这批垃圾的刻画。`b` 的右投影由右片构成，而右片的每个见证都会把 `b` 展成有序对；在非对假设下该片为空，`right b` 即空集。左投影读取交集：`⋂ b` 的成员 `c` 落在 `b` 的每个成员之中，且交集至多有一个互异成员，故 `left b` 或塌缩到这样的 `c`，或为空集。这些是与运算章附录同形的读引理：每条封以 `opaque`{.Agda}、带显式类型，凭作用域内的私有机制证出；既有内容没有任何改动、改名或解封。
<!--/-->

```agda
private
  ⋃∅ : ⋃ ∅ ≡ ∅
  ⋃∅ = extensionality (⋃ ∅) ∅ (sub₁ , sub₂)
    where
    sub₁ : ⟨ ⋃ ∅ ⊆ ∅ ⟩
    sub₁ x h = PT.rec (snd (x ∈ₛ ∅)) go (union-ax ∅ x .fst h)
      where
      go : Σ[ v ∈ V ℓ ] (⟨ v ∈ₛ ∅ ⟩ × ⟨ x ∈ₛ v ⟩) → ⟨ x ∈ₛ ∅ ⟩
      go (v , v∈∅ , _) = Empty.rec (∅-empty v v∈∅)
    sub₂ : ⟨ ∅ ⊆ ⋃ ∅ ⟩
    sub₂ x h = Empty.rec (∅-empty x h)

  ⋂-single : (b c d : V ℓ) → ⟨ c ∈ₛ ⋂ b ⟩ → ⟨ d ∈ₛ ⋂ b ⟩ → c ≡ d
  ⋂-single b c d c∈⋂ d∈⋂ = extensionality c d (c⊆d , d⊆c)
    where
    c⊆d : ⟨ c ⊆ d ⟩
    c⊆d x x∈c = PT.rec (snd (x ∈ₛ d)) goC (∈∈ₛ {a = c} {b = ⋂ b} .snd c∈⋂)
      where
      goC : Σ[ p ∈ Σ[ m ∈ ⟪ b ⟫ ] ((k : ⟪ b ⟫) → ⟨ ⋃ (⟪ b ⟫↪ m) ∈ₛ ⟪ b ⟫↪ k ⟩) ]
              (⋃ (⟪ b ⟫↪ (p .fst)) ≡ c)
          → ⟨ x ∈ₛ d ⟩
      goC (p , q) = PT.rec (snd (x ∈ₛ d)) goD (∈∈ₛ {a = d} {b = ⋂ b} .snd d∈⋂)
        where
        goD : Σ[ r ∈ Σ[ m ∈ ⟪ b ⟫ ] ((k : ⟪ b ⟫) → ⟨ ⋃ (⟪ b ⟫↪ m) ∈ₛ ⟪ b ⟫↪ k ⟩) ]
                (⋃ (⟪ b ⟫↪ (r .fst)) ≡ d)
            → ⟨ x ∈ₛ d ⟩
        goD (r , s) = subst (λ t → ⟨ x ∈ₛ t ⟩) s
          (union-ax (⟪ b ⟫↪ (r .fst)) x .snd
            ∣ c , ( c∈ₛb₍r₎ , x∈c ) ∣₁)
          where
          c∈ₛb₍r₎ : ⟨ c ∈ₛ ⟪ b ⟫↪ (r .fst) ⟩
          c∈ₛb₍r₎ = subst (λ t → ⟨ t ∈ₛ ⟪ b ⟫↪ (r .fst) ⟩) q
            (p .snd (r .fst))
    d⊆c : ⟨ d ⊆ c ⟩
    d⊆c x x∈d = PT.rec (snd (x ∈ₛ c)) goD' (∈∈ₛ {a = d} {b = ⋂ b} .snd d∈⋂)
      where
      goD' : Σ[ r ∈ Σ[ m ∈ ⟪ b ⟫ ] ((k : ⟪ b ⟫) → ⟨ ⋃ (⟪ b ⟫↪ m) ∈ₛ ⟪ b ⟫↪ k ⟩) ]
               (⋃ (⟪ b ⟫↪ (r .fst)) ≡ d)
           → ⟨ x ∈ₛ c ⟩
      goD' (r , s) = PT.rec (snd (x ∈ₛ c)) goC' (∈∈ₛ {a = c} {b = ⋂ b} .snd c∈⋂)
        where
        goC' : Σ[ p ∈ Σ[ m ∈ ⟪ b ⟫ ] ((k : ⟪ b ⟫) → ⟨ ⋃ (⟪ b ⟫↪ m) ∈ₛ ⟪ b ⟫↪ k ⟩) ]
                 (⋃ (⟪ b ⟫↪ (p .fst)) ≡ c)
             → ⟨ x ∈ₛ c ⟩
        goC' (p , q) = subst (λ t → ⟨ x ∈ₛ t ⟩) q
          (union-ax (⟪ b ⟫↪ (p .fst)) x .snd
            ∣ d , ( d∈ₛb₍p₎ , x∈d ) ∣₁)
          where
          d∈ₛb₍p₎ : ⟨ d ∈ₛ ⟪ b ⟫↪ (p .fst) ⟩
          d∈ₛb₍p₎ = subst (λ t → ⟨ t ∈ₛ ⟪ b ⟫↪ (p .fst) ⟩) s
            (r .snd (p .fst))

opaque
  right-nonpair : (b : V ℓ) → ((p q : V ℓ) → ⟨ b ≡ₕ pr p q ⟩ → Empty.⊥) → right b ≡ ∅
  right-nonpair b nb = cong ⋃_ (rightSlice-nonpair b nb) ∙ ⋃∅
    where
    rightSlice-nonpair : (b : V ℓ) → ((p q : V ℓ) → ⟨ b ≡ₕ pr p q ⟩ → Empty.⊥)
                       → rightSlice b ≡ ∅
    rightSlice-nonpair b nb = extensionality (rightSlice b) ∅ (sub₁ , sub₂)
      where
      sub₁ : ⟨ rightSlice b ⊆ ∅ ⟩
      sub₁ w h = PT.rec (snd (w ∈ₛ ∅)) go (∈∈ₛ {a = w} {b = rightSlice b} .snd h)
        where
        go : Σ[ p ∈ Σ[ m ∈ ⟪ b ⟫ ] ⟨ pr (left b) (sndExtract (⟪ b ⟫↪ m) (left b)) ∈ₛ ⁅ b ⁆s ⟩ ]
               (sndExtract (⟪ b ⟫↪ (p .fst)) (left b) ≡ w)
           → ⟨ w ∈ₛ ∅ ⟩
        go (p , _) = Empty.rec (nb (left b) (sndExtract (⟪ b ⟫↪ (p .fst)) (left b))
          (subst (λ t → ⟨ b ≡ₕ t ⟩) (sym (pr≡b p)) refl))
          where
          pr≡b : (p : Σ[ m ∈ ⟪ b ⟫ ] ⟨ pr (left b) (sndExtract (⟪ b ⟫↪ m) (left b)) ∈ₛ ⁅ b ⁆s ⟩)
               → pr (left b) (sndExtract (⟪ b ⟫↪ (p .fst)) (left b)) ≡ b
          pr≡b p = SetPackage.classification (SingletonPackage b)
            (pr (left b) (sndExtract (⟪ b ⟫↪ (p .fst)) (left b))) .fst (p .snd)
      sub₂ : ⟨ ∅ ⊆ rightSlice b ⟩
      sub₂ w h = Empty.rec (∅-empty w h)

opaque
  ⋂-member-in-all : (b c w : V ℓ) → ⟨ c ∈ₛ ⋂ b ⟩ → ⟨ w ∈ₛ b ⟩ → ⟨ c ∈ₛ w ⟩
  ⋂-member-in-all b c w c∈⋂ w∈b = PT.rec (snd (c ∈ₛ w)) go
    (∈∈ₛ {a = c} {b = ⋂ b} .snd c∈⋂)
    where
    go : Σ[ p ∈ Σ[ m ∈ ⟪ b ⟫ ] ((k : ⟪ b ⟫) → ⟨ ⋃ (⟪ b ⟫↪ m) ∈ₛ ⟪ b ⟫↪ k ⟩) ]
           (⋃ (⟪ b ⟫↪ (p .fst)) ≡ c)
       → ⟨ c ∈ₛ w ⟩
    go (p , q) = subst (λ t → ⟨ c ∈ₛ t ⟩) (fw .snd)
      (subst (λ t → ⟨ t ∈ₛ ⟪ b ⟫↪ (fw .fst) ⟩) q (p .snd (fw .fst)))
      where
      fw : Σ[ m ∈ ⟪ b ⟫ ] (⟪ b ⟫↪ m ≡ w)
      fw = fibre b w w∈b

opaque
  left-⋂-collapse : (b c : V ℓ) → ⟨ c ∈ₛ ⋂ b ⟩ → left b ≡ c
  left-⋂-collapse b c c∈⋂ = subst (λ t → t ≡ c) (sym (left-compute b))
    (cong ⋃_ (⋂-collapse b c c∈⋂) ∙ ⋃singl c)
    where
    ⋂-collapse : (b c : V ℓ) → ⟨ c ∈ₛ ⋂ b ⟩ → ⋂ b ≡ ⁅ c ⁆s
    ⋂-collapse b c c∈⋂ = extensionality (⋂ b) (⁅ c ⁆s) (sub₁ , sub₂)
      where
      sub₁ : ⟨ ⋂ b ⊆ ⁅ c ⁆s ⟩
      sub₁ d d∈⋂ = SetPackage.classification (SingletonPackage c) d .snd
        (sym (⋂-single b c d c∈⋂ d∈⋂))
      sub₂ : ⟨ ⁅ c ⁆s ⊆ ⋂ b ⟩
      sub₂ d d∈singl = subst (λ t → ⟨ t ∈ₛ ⋂ b ⟩) (sym (∈singl d∈singl)) c∈⋂

opaque
  left-⋂-empty : (b : V ℓ) → ((c : V ℓ) → ⟨ c ∈ₛ ⋂ b ⟩ → Empty.⊥) → left b ≡ ∅
  left-⋂-empty b ne = subst (λ t → t ≡ ∅) (sym (left-compute b))
    (cong ⋃_ (⋂-empty b ne) ∙ ⋃∅)
    where
    ⋂-empty : (b : V ℓ) → ((c : V ℓ) → ⟨ c ∈ₛ ⋂ b ⟩ → Empty.⊥) → ⋂ b ≡ ∅
    ⋂-empty b ne = extensionality (⋂ b) ∅ (sub₁ , sub₂)
      where
      sub₁ : ⟨ ⋂ b ⊆ ∅ ⟩
      sub₁ c c∈⋂ = Empty.rec (ne c c∈⋂)
      sub₂ : ⟨ ∅ ⊆ ⋂ b ⟩
      sub₂ c c∈∅ = Empty.rec (∅-empty c c∈∅)
```
