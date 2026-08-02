# The rud operations

<!--en-->
The rud trunk opens its operations layer. The constructible hierarchy of Part 4
will be rebuilt as the S-hierarchy of Schindler-Zeman, whose one-step operator
applies a finite list of set operations to the previous level. This chapter
defines the first eight of those operations, F0 to F7, together with F9, each
as an operation on the cumulative hierarchy `V`{.Agda} of Part 3, and each with
its extension specification: the exact membership characterization of the image,
stated as the two directions of an iff. Everything later in the trunk consumes
these specifications and nothing else.

Two families of facts enter. First, several operations already exist in the
tree in another guise, and they are wrapped under their F-names rather than
redefined: pairing is the hierarchy's unordered pair, union is the hierarchy's
union, and the ordered pair is the Kuratowski pair of the coding chapter.
Second, the genuinely new operations are built as images of small index types,
the `sett`{.Agda} constructor of the cumulative hierarchy, and their
membership specifications are proved from the library's classification laws.
<!--zh-->
rud 主干从运算层开篇。第四部的可构造层级将被重建为 Schindler-Zeman 的 S-层级，其后继算子把一张有限的集合运算清单施于前一层级。本章定义其中头八个运算 F0 至 F7，外加 F9：每一个都是第三部累积层级 `V`{.Agda} 上的运算，并各带一条外延规格，即像的精确隶属刻画，陈述为双向 iff。主干此后的一切只消费这些规格，别无其他。

有两族事实进场。其一，若干运算在树中已以别的面目存在，这里只以 F 名包装而不再定义：配对即层级的无序对，并即层级的并，有序对即编码章的 Kuratowski 对。其二，真正的新运算都是小索引类型之像，即累积层级的 `sett`{.Agda} 构造子，其隶属规格从库的分类定律证出。
<!--/-->

```agda
{-# OPTIONS --cubical --safe --guardedness #-}

open import Base.Prelude
open import Base.Truth

module L.Rud.Ops {ℓ : Level} where

open import FOL.ZFStructure using ( module hPropStructure )
open import V.Hierarchy {ℓ} using ( 𝒮ᵥ )
open import V.Coding {ℓ} using ( pr )
open import Cubical.Data.Bool using ( true; false )
import Cubical.Functions.Logic as Logic
open import Cubical.HITs.CumulativeHierarchy.Base using ( V; _∈_; sett )
open import Cubical.HITs.CumulativeHierarchy.Properties
  using ( _∈ₛ_; ∈∈ₛ; ⟪_⟫; ⟪_⟫↪; ∈ₛ⟪_⟫↪_; ∈-asFiber; _≡ₕ_ )
open import Cubical.HITs.CumulativeHierarchy.Constructions
  using ( ⁅_,_⁆; ⁅_⁆s; pairing-ax; ⋃_; union-ax )
import Cubical.HITs.PropositionalTruncation as PT
open PT using ( ∣_∣₁ )

open TruthAlgebra (hPropAlgebra (ℓ-suc ℓ))
open hPropStructure 𝒮ᵥ
```

<!--en-->
## The basis and the tuple convention
<!--zh-->
## 基与三元组约定
<!--/-->

<!--en-->
The full SZ basis has sixteen entries, F0 to F15; the trunk splits the list
across sibling modules, and this one carries F0 to F7 and F9. Every operation
is binary, and the ones whose mathematical content is unary simply ignore
their second argument. The ordered pair is the coding chapter's Kuratowski
pair `pr`{.Agda}, and triples nest to the right: `<u,z,v>` means
`<u,<z,v>>`, that is `pr u (pr z v)`. F3 and F4 read their pairs out of their
second argument, and F6 out of its first; a pair in a set keeps both of its
components inside the double union of that set, which is how those operations
are indexed.
<!--zh-->
SZ 基全长十六项，F0 至 F15；主干把清单拆给平行模块，本章携带 F0 至 F7 与 F9。每个运算都是二元的，数学内容为一元的那些忽略第二参数。有序对即编码章的 Kuratowski 对 `pr`{.Agda}，三元组向右嵌套：`<u,z,v>` 即 `<u,<z,v>>`，也就是 `pr u (pr z v)`。F3、F4 从第二参数中读出对，F6 从第一参数中读出对；集合中的一对，其两个分量都留在该集合的二重并之内，这正是这些运算的索引方式。
<!--/-->

```agda
private
  -- the unordered pair {u,v} is the second member of the Kuratowski pair pr u v
  u-v∈pr : (u v : V ℓ) → ⟨ ⁅ u , v ⁆ ∈ₛ pr u v ⟩
  u-v∈pr u v = ∈∈ₛ {a = ⁅ u , v ⁆} {b = pr u v} .fst
    ∣ lift true , refl ∣₁

  -- a member of {u,v} sits in the double union of any set holding pr u v
  pair-member-in-⋃⋃ : (y w u v : V ℓ) → ⟨ pr u v ∈ˢ y ⟩ → ⟨ w ∈ˢ ⁅ u , v ⁆ ⟩
                    → ⟨ w ∈ˢ (⋃ (⋃ y)) ⟩
  pair-member-in-⋃⋃ y w u v h w∈ = ∈∈ₛ {a = w} {b = ⋃ (⋃ y)} .snd
    (union-ax (⋃ y) w .snd
      ∣ ⁅ u , v ⁆ , (⁅u,v⁆∈ₛ⋃y) , (∈∈ₛ {a = w} {b = ⁅ u , v ⁆} .fst w∈) ∣₁)
    where
    ⁅u,v⁆∈ₛ⋃y : ⟨ ⁅ u , v ⁆ ∈ₛ ⋃ y ⟩
    ⁅u,v⁆∈ₛ⋃y = union-ax y (⁅ u , v ⁆) .snd
      ∣ pr u v , (∈∈ₛ {a = pr u v} {b = y} .fst h) , u-v∈pr u v ∣₁

  -- the left component of a pair in y lies in the double union of y
  prL-in-⋃⋃ : (y u v : V ℓ) → ⟨ pr u v ∈ˢ y ⟩ → ⟨ u ∈ˢ (⋃ (⋃ y)) ⟩
  prL-in-⋃⋃ y u v h = pair-member-in-⋃⋃ y u u v h ∣ lift false , refl ∣₁

  -- the right component likewise
  prR-in-⋃⋃ : (y u v : V ℓ) → ⟨ pr u v ∈ˢ y ⟩ → ⟨ v ∈ˢ (⋃ (⋃ y)) ⟩
  prR-in-⋃⋃ y u v h = pair-member-in-⋃⋃ y v u v h ∣ lift true , refl ∣₁
```

<!--en-->
## F0, the unordered pair
<!--zh-->
## F0，无序对
<!--/-->

<!--en-->
F0 is the hierarchy's own unordered pair, wrapped. Its extension
specification is the library's pairing law, restated in the large membership
of the structure: a member of `F0 a b` is equal to `a` or to `b`, and nothing
else.
<!--zh-->
F0 即层级自己的无序对，原样包装。其外延规格就是库的配对定律，改用结构的宽隶属陈述：`F0 a b` 的成员等于 `a` 或等于 `b`，且别无其他。
<!--/-->

```agda
F0 : V ℓ → V ℓ → V ℓ
F0 a b = ⁅ a , b ⁆

F0-spec : (a b x : V ℓ)
        → (⟨ x ∈ˢ F0 a b ⟩ → ⟨ (x ≡ₕ a) ⊔ (x ≡ₕ b) ⟩)
        × (⟨ (x ≡ₕ a) ⊔ (x ≡ₕ b) ⟩ → ⟨ x ∈ˢ F0 a b ⟩)
F0-spec a b x = fwd , bwd
  where
  fwd : ⟨ x ∈ˢ F0 a b ⟩ → ⟨ (x ≡ₕ a) ⊔ (x ≡ₕ b) ⟩
  fwd h = pairing-ax a b x .fst (∈∈ₛ {a = x} {b = F0 a b} .fst h)
  bwd : ⟨ (x ≡ₕ a) ⊔ (x ≡ₕ b) ⟩ → ⟨ x ∈ˢ F0 a b ⟩
  bwd h = ∈∈ₛ {a = x} {b = F0 a b} .snd (pairing-ax a b x .snd h)
```

<!--en-->
## F1, set difference
<!--zh-->
## F1，差
<!--/-->

<!--en-->
F1 separates the members of `a` that fail to belong to `b` and collects them
as a new set. The specification is the shape every later chapter reads:
`x` lies in `F1 a b` exactly when it lies in `a` and does not lie in `b`.
The index is a subtype of the small member type of `a`, so no universe is
spent.
<!--zh-->
F1 把 `a` 中不属于 `b` 的成员分离出来，收拢为新集合。规格即此后各章读取的形状：`x` 属于 `F1 a b`，当且仅当它属于 `a` 且不属于 `b`。索引是 `a` 的小成员类型的子类型，分文不花宇宙。
<!--/-->

```agda
opaque
  -- perf: P-c: the image is a sett over a member-type subtype; sealed so membership in it never unfolds downstream
  F1 : V ℓ → V ℓ → V ℓ
  F1 a b = sett (Σ[ m ∈ ⟪ a ⟫ ] ⟨ Logic.¬_ (⟪ a ⟫↪ m ∈ₛ b) ⟩) (λ p → ⟪ a ⟫↪ (p .fst))

  F1-spec : (a b x : V ℓ)
          → (⟨ x ∈ˢ F1 a b ⟩ → ⟨ (x ∈ˢ a) ⊓ (¬ (x ∈ˢ b)) ⟩)
          × (⟨ (x ∈ˢ a) ⊓ (¬ (x ∈ˢ b)) ⟩ → ⟨ x ∈ˢ F1 a b ⟩)
  F1-spec a b x = fwd , bwd
    where
    fwd : ⟨ x ∈ˢ F1 a b ⟩ → ⟨ (x ∈ˢ a) ⊓ (¬ (x ∈ˢ b)) ⟩
    fwd h = PT.rec (snd ((x ∈ˢ a) ⊓ (¬ (x ∈ˢ b)))) go h
      where
      go : Σ[ p ∈ Σ[ m ∈ ⟪ a ⟫ ] ⟨ Logic.¬_ (⟪ a ⟫↪ m ∈ₛ b) ⟩ ]
             (⟪ a ⟫↪ (p .fst) ≡ x)
         → ⟨ (x ∈ˢ a) ⊓ (¬ (x ∈ˢ b)) ⟩
      go (p , q) = x∈a , x∉b
        where
        m : ⟪ a ⟫
        m = p .fst
        h¬ : ⟨ Logic.¬_ (⟪ a ⟫↪ m ∈ₛ b) ⟩
        h¬ = p .snd
        x∈a : ⟨ x ∈ˢ a ⟩
        x∈a = subst (λ t → ⟨ t ∈ˢ a ⟩) q
              (∈∈ₛ {a = ⟪ a ⟫↪ m} {b = a} .snd (∈ₛ⟪ a ⟫↪ m))
        x∉b : ⟨ ¬ (x ∈ˢ b) ⟩
        x∉b k = h¬ (subst (λ t → ⟨ t ∈ₛ b ⟩) (sym q) (∈∈ₛ {a = x} {b = b} .fst k))
    bwd : ⟨ (x ∈ˢ a) ⊓ (¬ (x ∈ˢ b)) ⟩ → ⟨ x ∈ˢ F1 a b ⟩
    bwd (x∈a , x∉b) = ∣ ((m , h¬) , q) ∣₁
      where
      fx : Σ[ m ∈ ⟪ a ⟫ ] (⟪ a ⟫↪ m ≡ x)
      fx = ∈-asFiber {a = x} {b = a} x∈a
      m : ⟪ a ⟫
      m = fx .fst
      q : ⟪ a ⟫↪ m ≡ x
      q = fx .snd
      h¬ : ⟨ Logic.¬_ (⟪ a ⟫↪ m ∈ₛ b) ⟩
      h¬ k = x∉b (subst (λ t → ⟨ t ∈ˢ b ⟩) q (∈∈ₛ {a = ⟪ a ⟫↪ m} {b = b} .snd k))
```

<!--en-->
## F2, the product
<!--zh-->
## F2，积
<!--/-->

<!--en-->
F2 forms the cartesian product of two sets, the set of Kuratowski pairs of a
member of `x` with a member of `y`. The index is the product of the two small
member types, which is why `sett` accepts it. Its specification quantifies
over the members themselves: a member of `F2 x y` is merely a pair of a
member of `x` and a member of `y`.
<!--zh-->
F2 造两个集合的笛卡尔积，即一个 `x` 成员与一个 `y` 成员的 Kuratowski 对之集。索引是两个小成员类型之积，`sett` 因此接纳它。其规格对成员本身量化：`F2 x y` 的成员仅仅是一个 `x` 成员与一个 `y` 成员之对。
<!--/-->

```agda
opaque
  -- perf: the product image is a sett whose index is a product of member types; sealed so consumers see only F2-spec
  F2 : V ℓ → V ℓ → V ℓ
  F2 x y = sett (⟪ x ⟫ × ⟪ y ⟫) (λ p → pr (⟪ x ⟫↪ (p .fst)) (⟪ y ⟫↪ (p .snd)))

  F2-RHS : (x y t : V ℓ) → hProp (ℓ-suc ℓ)
  F2-RHS x y t = ⋁ (V ℓ) (λ u → ⋁ (V ℓ) (λ v →
                   (u ∈ˢ x) ⊓ (v ∈ˢ y) ⊓ (t ≡ₕ pr u v)))

  F2-spec : (x y t : V ℓ)
          → (⟨ t ∈ˢ F2 x y ⟩ → ⟨ F2-RHS x y t ⟩)
          × (⟨ F2-RHS x y t ⟩ → ⟨ t ∈ˢ F2 x y ⟩)
  F2-spec x y t = fwd , bwd
    where
    RHS : hProp (ℓ-suc ℓ)
    RHS = F2-RHS x y t
    fwd : ⟨ t ∈ˢ F2 x y ⟩ → ⟨ RHS ⟩
    fwd h = PT.rec (snd RHS) go h
      where
      go : Σ[ p ∈ ⟪ x ⟫ × ⟪ y ⟫ ] (pr (⟪ x ⟫↪ (p .fst)) (⟪ y ⟫↪ (p .snd)) ≡ t)
         → ⟨ RHS ⟩
      go (p , q) = ∣ u , (∣ v , (u∈x , v∈y , t≡) ∣₁) ∣₁
        where
        u : V ℓ
        u = ⟪ x ⟫↪ (p .fst)
        v : V ℓ
        v = ⟪ y ⟫↪ (p .snd)
        u∈x : ⟨ u ∈ˢ x ⟩
        u∈x = ∈∈ₛ {a = u} {b = x} .snd (∈ₛ⟪ x ⟫↪ (p .fst))
        v∈y : ⟨ v ∈ˢ y ⟩
        v∈y = ∈∈ₛ {a = v} {b = y} .snd (∈ₛ⟪ y ⟫↪ (p .snd))
        t≡ : ⟨ t ≡ₕ pr u v ⟩
        t≡ = subst (λ w → ⟨ t ≡ₕ w ⟩) (sym q) refl
    bwd : ⟨ RHS ⟩ → ⟨ t ∈ˢ F2 x y ⟩
    bwd = PT.rec (snd (t ∈ F2 x y)) go₀
      where
      go₁ : (u : V ℓ) → Σ[ v ∈ V ℓ ] ⟨ (u ∈ˢ x) ⊓ (v ∈ˢ y) ⊓ (t ≡ₕ pr u v) ⟩
          → ⟨ t ∈ F2 x y ⟩
      go₁ u (v , (u∈x , v∈y , t≡)) = ∣ ((m , n) , path) ∣₁
        where
        m : ⟪ x ⟫
        m = ∈-asFiber {a = u} {b = x} u∈x .fst
        qu : ⟪ x ⟫↪ m ≡ u
        qu = ∈-asFiber {a = u} {b = x} u∈x .snd
        n : ⟪ y ⟫
        n = ∈-asFiber {a = v} {b = y} v∈y .fst
        qv : ⟪ y ⟫↪ n ≡ v
        qv = ∈-asFiber {a = v} {b = y} v∈y .snd
        path : pr (⟪ x ⟫↪ m) (⟪ y ⟫↪ n) ≡ t
        path = cong₂ pr qu qv ∙ sym t≡
      go₀ : Σ[ u ∈ V ℓ ] ⟨ ⋁ (V ℓ) (λ v → (u ∈ˢ x) ⊓ (v ∈ˢ y) ⊓ (t ≡ₕ pr u v)) ⟩
          → ⟨ t ∈ F2 x y ⟩
      go₀ (u , h₁) = PT.rec (snd (t ∈ F2 x y)) (go₁ u) h₁
```

<!--en-->
## F3, the middle insertion
<!--zh-->
## F3，中间插入
<!--/-->

<!--en-->
F3 reads the pairs out of `y`, opens each one, and sandwiches a member of `x`
between its two components. The image element for `z ∈ x` and `<u,v> ∈ y` is
`<u,z,v>`, which the tuple convention reads as `pr u (pr z v)`. Because the
components of a pair in `y` lie in `⋃⋃ y`, the index ranges over the small
member types of `⋃⋃ y` and `x`, with the pair-in-`y` condition attached; the
specification itself quantifies over arbitrary `u`, `z`, `v`.
<!--zh-->
F3 从 `y` 中读出对，把每一对拆开，再把 `x` 的成员夹进两个分量之间。对 `z ∈ x` 与 `<u,v> ∈ y`，像元是 `<u,z,v>`，按三元组约定读作 `pr u (pr z v)`。由于 `y` 中一对的两个分量落在 `⋃⋃ y` 内，索引遍历 `⋃⋃ y` 与 `x` 的小成员类型，并挂上「对在 `y` 中」的条件；规格本身则对任意的 `u`、`z`、`v` 量化。
<!--/-->

```agda
opaque
  -- perf: P-c: the index carries a ⋃-tower (members of the double union of the second argument); sealed at birth
  F3 : V ℓ → V ℓ → V ℓ
  F3 x y = sett idx fam
    where
    idx : Type ℓ
    idx = Σ[ u ∈ ⟪ ⋃ (⋃ y) ⟫ ] Σ[ z ∈ ⟪ x ⟫ ] Σ[ v ∈ ⟪ ⋃ (⋃ y) ⟫ ]
          ⟨ pr (⟪ ⋃ (⋃ y) ⟫↪ u) (⟪ ⋃ (⋃ y) ⟫↪ v) ∈ₛ y ⟩
    fam : idx → V ℓ
    fam (u , z , v , _) = pr (⟪ ⋃ (⋃ y) ⟫↪ u) (pr (⟪ x ⟫↪ z) (⟪ ⋃ (⋃ y) ⟫↪ v))

  F3-RHS : (x y t : V ℓ) → hProp (ℓ-suc ℓ)
  F3-RHS x y t = ⋁ (V ℓ) (λ u → ⋁ (V ℓ) (λ z → ⋁ (V ℓ) (λ v →
                   (z ∈ˢ x) ⊓ (pr u v ∈ˢ y) ⊓ (t ≡ₕ pr u (pr z v)))))

  F3-spec : (x y t : V ℓ)
          → (⟨ t ∈ˢ F3 x y ⟩ → ⟨ F3-RHS x y t ⟩)
          × (⟨ F3-RHS x y t ⟩ → ⟨ t ∈ˢ F3 x y ⟩)
  F3-spec x y t = fwd , bwd
    where
    RHS : hProp (ℓ-suc ℓ)
    RHS = F3-RHS x y t
    fwd : ⟨ t ∈ˢ F3 x y ⟩ → ⟨ RHS ⟩
    fwd h = PT.rec (snd RHS) go h
      where
      go : Σ[ p ∈ Σ[ u ∈ ⟪ ⋃ (⋃ y) ⟫ ] Σ[ z ∈ ⟪ x ⟫ ] Σ[ v ∈ ⟪ ⋃ (⋃ y) ⟫ ]
              ⟨ pr (⟪ ⋃ (⋃ y) ⟫↪ u) (⟪ ⋃ (⋃ y) ⟫↪ v) ∈ₛ y ⟩ ]
             (pr (⟪ ⋃ (⋃ y) ⟫↪ (p .fst))
                 (pr (⟪ x ⟫↪ (p .snd .fst))
                     (⟪ ⋃ (⋃ y) ⟫↪ (p .snd .snd .fst))) ≡ t)
         → ⟨ RHS ⟩
      go (p , q) = ∣ u , (∣ z , (∣ v , (z∈x , pr-uv∈y , t≡) ∣₁) ∣₁) ∣₁
        where
        u : V ℓ
        u = ⟪ ⋃ (⋃ y) ⟫↪ (p .fst)
        z : V ℓ
        z = ⟪ x ⟫↪ (p .snd .fst)
        v : V ℓ
        v = ⟪ ⋃ (⋃ y) ⟫↪ (p .snd .snd .fst)
        z∈x : ⟨ z ∈ˢ x ⟩
        z∈x = ∈∈ₛ {a = z} {b = x} .snd (∈ₛ⟪ x ⟫↪ (p .snd .fst))
        pr-uv∈y : ⟨ pr u v ∈ˢ y ⟩
        pr-uv∈y = ∈∈ₛ {a = pr u v} {b = y} .snd (p .snd .snd .snd)
        t≡ : ⟨ t ≡ₕ pr u (pr z v) ⟩
        t≡ = subst (λ w → ⟨ t ≡ₕ w ⟩) (sym q) refl
    bwd : ⟨ RHS ⟩ → ⟨ t ∈ˢ F3 x y ⟩
    bwd = PT.rec (snd (t ∈ F3 x y)) go₀
      where
      go₂ : (u z : V ℓ) → Σ[ v ∈ V ℓ ]
              ⟨ (z ∈ˢ x) ⊓ (pr u v ∈ˢ y) ⊓ (t ≡ₕ pr u (pr z v)) ⟩
          → ⟨ t ∈ F3 x y ⟩
      go₂ u z (v , (z∈x , pruv∈y , t≡)) = ∣ ((mᵤ , (m_z , (mᵥ , cond))) , path) ∣₁
        where
        mᵤ : ⟪ ⋃ (⋃ y) ⟫
        mᵤ = ∈-asFiber {a = u} {b = ⋃ (⋃ y)} (prL-in-⋃⋃ y u v pruv∈y) .fst
        qu : ⟪ ⋃ (⋃ y) ⟫↪ mᵤ ≡ u
        qu = ∈-asFiber {a = u} {b = ⋃ (⋃ y)} (prL-in-⋃⋃ y u v pruv∈y) .snd
        mᵥ : ⟪ ⋃ (⋃ y) ⟫
        mᵥ = ∈-asFiber {a = v} {b = ⋃ (⋃ y)} (prR-in-⋃⋃ y u v pruv∈y) .fst
        qv : ⟪ ⋃ (⋃ y) ⟫↪ mᵥ ≡ v
        qv = ∈-asFiber {a = v} {b = ⋃ (⋃ y)} (prR-in-⋃⋃ y u v pruv∈y) .snd
        m_z : ⟪ x ⟫
        m_z = ∈-asFiber {a = z} {b = x} z∈x .fst
        qz : ⟪ x ⟫↪ m_z ≡ z
        qz = ∈-asFiber {a = z} {b = x} z∈x .snd
        cond : ⟨ pr (⟪ ⋃ (⋃ y) ⟫↪ mᵤ) (⟪ ⋃ (⋃ y) ⟫↪ mᵥ) ∈ₛ y ⟩
        cond = subst (λ w → ⟨ w ∈ₛ y ⟩) (cong₂ pr (sym qu) (sym qv))
                 (∈∈ₛ {a = pr u v} {b = y} .fst pruv∈y)
        path : pr (⟪ ⋃ (⋃ y) ⟫↪ mᵤ)
                 (pr (⟪ x ⟫↪ m_z) (⟪ ⋃ (⋃ y) ⟫↪ mᵥ)) ≡ t
        path = cong₂ pr qu (cong₂ pr qz qv) ∙ sym t≡
      go₁ : (u : V ℓ) → Σ[ z ∈ V ℓ ] ⟨ ⋁ (V ℓ) (λ v →
              (z ∈ˢ x) ⊓ (pr u v ∈ˢ y) ⊓ (t ≡ₕ pr u (pr z v))) ⟩
          → ⟨ t ∈ F3 x y ⟩
      go₁ u (z , h₂) = PT.rec (snd (t ∈ F3 x y)) (go₂ u z) h₂
      go₀ : Σ[ u ∈ V ℓ ] ⟨ ⋁ (V ℓ) (λ z → ⋁ (V ℓ) (λ v →
              (z ∈ˢ x) ⊓ (pr u v ∈ˢ y) ⊓ (t ≡ₕ pr u (pr z v)))) ⟩
          → ⟨ t ∈ F3 x y ⟩
      go₀ (u , h₁) = PT.rec (snd (t ∈ F3 x y)) (go₁ u) h₁
```

<!--en-->
## F4, the right append
<!--zh-->
## F4，右端接续
<!--/-->

<!--en-->
F4 is the mirror image of F3: the member of `x` is appended at the right of
the opened pair, so the image of `z ∈ x` and `<u,v> ∈ y` is `<u,v,z>`, read
as `pr u (pr v z)`. The index and the specification are F3's with the two
middle coordinates exchanged.
<!--zh-->
F4 是 F3 的镜像：`x` 的成员被接在拆开之对的右端，于是 `z ∈ x` 与 `<u,v> ∈ y` 的像是 `<u,v,z>`，读作 `pr u (pr v z)`。索引与规格都是 F3 的，只把两个中间坐标对调。
<!--/-->

```agda
opaque
  -- perf: P-c: the index carries a ⋃-tower (members of the double union of the second argument); sealed at birth
  F4 : V ℓ → V ℓ → V ℓ
  F4 x y = sett idx fam
    where
    idx : Type ℓ
    idx = Σ[ u ∈ ⟪ ⋃ (⋃ y) ⟫ ] Σ[ v ∈ ⟪ ⋃ (⋃ y) ⟫ ] Σ[ z ∈ ⟪ x ⟫ ]
          ⟨ pr (⟪ ⋃ (⋃ y) ⟫↪ u) (⟪ ⋃ (⋃ y) ⟫↪ v) ∈ₛ y ⟩
    fam : idx → V ℓ
    fam (u , v , z , _) = pr (⟪ ⋃ (⋃ y) ⟫↪ u) (pr (⟪ ⋃ (⋃ y) ⟫↪ v) (⟪ x ⟫↪ z))

  F4-RHS : (x y t : V ℓ) → hProp (ℓ-suc ℓ)
  F4-RHS x y t = ⋁ (V ℓ) (λ u → ⋁ (V ℓ) (λ v → ⋁ (V ℓ) (λ z →
                   (z ∈ˢ x) ⊓ (pr u v ∈ˢ y) ⊓ (t ≡ₕ pr u (pr v z)))))

  F4-spec : (x y t : V ℓ)
          → (⟨ t ∈ˢ F4 x y ⟩ → ⟨ F4-RHS x y t ⟩)
          × (⟨ F4-RHS x y t ⟩ → ⟨ t ∈ˢ F4 x y ⟩)
  F4-spec x y t = fwd , bwd
    where
    RHS : hProp (ℓ-suc ℓ)
    RHS = F4-RHS x y t
    fwd : ⟨ t ∈ˢ F4 x y ⟩ → ⟨ RHS ⟩
    fwd h = PT.rec (snd RHS) go h
      where
      go : Σ[ p ∈ Σ[ u ∈ ⟪ ⋃ (⋃ y) ⟫ ] Σ[ v ∈ ⟪ ⋃ (⋃ y) ⟫ ] Σ[ z ∈ ⟪ x ⟫ ]
              ⟨ pr (⟪ ⋃ (⋃ y) ⟫↪ u) (⟪ ⋃ (⋃ y) ⟫↪ v) ∈ₛ y ⟩ ]
             (pr (⟪ ⋃ (⋃ y) ⟫↪ (p .fst))
                 (pr (⟪ ⋃ (⋃ y) ⟫↪ (p .snd .fst))
                     (⟪ x ⟫↪ (p .snd .snd .fst))) ≡ t)
         → ⟨ RHS ⟩
      go (p , q) = ∣ u , (∣ v , (∣ z , (z∈x , pr-uv∈y , t≡) ∣₁) ∣₁) ∣₁
        where
        u : V ℓ
        u = ⟪ ⋃ (⋃ y) ⟫↪ (p .fst)
        v : V ℓ
        v = ⟪ ⋃ (⋃ y) ⟫↪ (p .snd .fst)
        z : V ℓ
        z = ⟪ x ⟫↪ (p .snd .snd .fst)
        z∈x : ⟨ z ∈ˢ x ⟩
        z∈x = ∈∈ₛ {a = z} {b = x} .snd (∈ₛ⟪ x ⟫↪ (p .snd .snd .fst))
        pr-uv∈y : ⟨ pr u v ∈ˢ y ⟩
        pr-uv∈y = ∈∈ₛ {a = pr u v} {b = y} .snd (p .snd .snd .snd)
        t≡ : ⟨ t ≡ₕ pr u (pr v z) ⟩
        t≡ = subst (λ w → ⟨ t ≡ₕ w ⟩) (sym q) refl
    bwd : ⟨ RHS ⟩ → ⟨ t ∈ˢ F4 x y ⟩
    bwd = PT.rec (snd (t ∈ F4 x y)) go₀
      where
      go₂ : (u v : V ℓ) → Σ[ z ∈ V ℓ ]
              ⟨ (z ∈ˢ x) ⊓ (pr u v ∈ˢ y) ⊓ (t ≡ₕ pr u (pr v z)) ⟩
          → ⟨ t ∈ F4 x y ⟩
      go₂ u v (z , (z∈x , pruv∈y , t≡)) = ∣ ((mᵤ , (mᵥ , (m_z , cond))) , path) ∣₁
        where
        mᵤ : ⟪ ⋃ (⋃ y) ⟫
        mᵤ = ∈-asFiber {a = u} {b = ⋃ (⋃ y)} (prL-in-⋃⋃ y u v pruv∈y) .fst
        qu : ⟪ ⋃ (⋃ y) ⟫↪ mᵤ ≡ u
        qu = ∈-asFiber {a = u} {b = ⋃ (⋃ y)} (prL-in-⋃⋃ y u v pruv∈y) .snd
        mᵥ : ⟪ ⋃ (⋃ y) ⟫
        mᵥ = ∈-asFiber {a = v} {b = ⋃ (⋃ y)} (prR-in-⋃⋃ y u v pruv∈y) .fst
        qv : ⟪ ⋃ (⋃ y) ⟫↪ mᵥ ≡ v
        qv = ∈-asFiber {a = v} {b = ⋃ (⋃ y)} (prR-in-⋃⋃ y u v pruv∈y) .snd
        m_z : ⟪ x ⟫
        m_z = ∈-asFiber {a = z} {b = x} z∈x .fst
        qz : ⟪ x ⟫↪ m_z ≡ z
        qz = ∈-asFiber {a = z} {b = x} z∈x .snd
        cond : ⟨ pr (⟪ ⋃ (⋃ y) ⟫↪ mᵤ) (⟪ ⋃ (⋃ y) ⟫↪ mᵥ) ∈ₛ y ⟩
        cond = subst (λ w → ⟨ w ∈ₛ y ⟩) (cong₂ pr (sym qu) (sym qv))
                 (∈∈ₛ {a = pr u v} {b = y} .fst pruv∈y)
        path : pr (⟪ ⋃ (⋃ y) ⟫↪ mᵤ)
                 (pr (⟪ ⋃ (⋃ y) ⟫↪ mᵥ) (⟪ x ⟫↪ m_z)) ≡ t
        path = cong₂ pr qu (cong₂ pr qv qz) ∙ sym t≡
      go₁ : (u : V ℓ) → Σ[ v ∈ V ℓ ] ⟨ ⋁ (V ℓ) (λ z →
              (z ∈ˢ x) ⊓ (pr u v ∈ˢ y) ⊓ (t ≡ₕ pr u (pr v z))) ⟩
          → ⟨ t ∈ F4 x y ⟩
      go₁ u (v , h₂) = PT.rec (snd (t ∈ F4 x y)) (go₂ u v) h₂
      go₀ : Σ[ u ∈ V ℓ ] ⟨ ⋁ (V ℓ) (λ v → ⋁ (V ℓ) (λ z →
              (z ∈ˢ x) ⊓ (pr u v ∈ˢ y) ⊓ (t ≡ₕ pr u (pr v z)))) ⟩
          → ⟨ t ∈ F4 x y ⟩
      go₀ (u , h₁) = PT.rec (snd (t ∈ F4 x y)) (go₁ u) h₁
```

<!--en-->
## F5, the union
<!--zh-->
## F5，并
<!--/-->

<!--en-->
F5 is the hierarchy's union, wrapped, with its second argument ignored. The
specification restates the library's union law: a member of `F5 x` lies in
some member of `x`, merely.
<!--zh-->
F5 即层级的并，原样包装，第二参数被忽略。规格重述库的并定律：`F5 x` 的成员仅仅落在 `x` 的某个成员之中。
<!--/-->

```agda
F5 : V ℓ → V ℓ → V ℓ
F5 x y = ⋃ x

F5-RHS : (x t : V ℓ) → hProp (ℓ-suc ℓ)
F5-RHS x t = ⋁ (V ℓ) (λ v → (v ∈ˢ x) ⊓ (t ∈ˢ v))

F5-spec : (x y t : V ℓ)
        → (⟨ t ∈ˢ F5 x y ⟩ → ⟨ F5-RHS x t ⟩)
        × (⟨ F5-RHS x t ⟩ → ⟨ t ∈ˢ F5 x y ⟩)
F5-spec x y t = fwd , bwd
  where
  fwd : ⟨ t ∈ˢ F5 x y ⟩ → ⟨ F5-RHS x t ⟩
  fwd h = PT.map go (union-ax x t .fst (∈∈ₛ {a = t} {b = F5 x y} .fst h))
    where
    go : Σ[ v ∈ V ℓ ] (⟨ v ∈ₛ x ⟩ × ⟨ t ∈ₛ v ⟩)
       → Σ[ v ∈ V ℓ ] ⟨ (v ∈ˢ x) ⊓ (t ∈ˢ v) ⟩
    go (v , (v∈x , t∈v)) = v , (∈∈ₛ {a = v} {b = x} .snd v∈x
                               , ∈∈ₛ {a = t} {b = v} .snd t∈v)
  bwd : ⟨ F5-RHS x t ⟩ → ⟨ t ∈ˢ F5 x y ⟩
  bwd = PT.rec (snd (t ∈ F5 x y)) go
    where
    go : Σ[ v ∈ V ℓ ] ⟨ (v ∈ˢ x) ⊓ (t ∈ˢ v) ⟩ → ⟨ t ∈ F5 x y ⟩
    go (v , (v∈x , t∈v)) = ∈∈ₛ {a = t} {b = F5 x y} .snd
      (union-ax x t .snd
        ∣ v , (∈∈ₛ {a = v} {b = x} .fst v∈x , ∈∈ₛ {a = t} {b = v} .fst t∈v) ∣₁)
```

<!--en-->
## F6, the domain
<!--zh-->
## F6，定义域
<!--/-->

<!--en-->
F6 takes the domain of a relation: the set of left components of the pairs in
its first argument. A component of a pair in `x` lies in `⋃⋃ x`, so the index
runs over the small member types of that double union. The specification says
a member of `F6 x` is a left component of a pair in `x`, merely.
<!--zh-->
F6 取关系的定义域：其第一参数中对的左分量之集。`x` 中对的一个分量落在 `⋃⋃ x` 内，故索引跑遍该二重并的小成员类型。规格说：`F6 x` 的成员仅仅是一个 `x` 中对的左分量。
<!--/-->

```agda
opaque
  -- perf: P-c: the index carries a ⋃-tower (members of the double union of the first argument); sealed at birth
  F6 : V ℓ → V ℓ → V ℓ
  F6 x y = sett idx fam
    where
    idx : Type ℓ
    idx = Σ[ u ∈ ⟪ ⋃ (⋃ x) ⟫ ] Σ[ v ∈ ⟪ ⋃ (⋃ x) ⟫ ]
          ⟨ pr (⟪ ⋃ (⋃ x) ⟫↪ u) (⟪ ⋃ (⋃ x) ⟫↪ v) ∈ₛ x ⟩
    fam : idx → V ℓ
    fam (u , v , _) = ⟪ ⋃ (⋃ x) ⟫↪ u

  F6-RHS : (x t : V ℓ) → hProp (ℓ-suc ℓ)
  F6-RHS x t = ⋁ (V ℓ) (λ u → ⋁ (V ℓ) (λ v → (pr u v ∈ˢ x) ⊓ (t ≡ₕ u)))

  F6-spec : (x y t : V ℓ)
          → (⟨ t ∈ˢ F6 x y ⟩ → ⟨ F6-RHS x t ⟩)
          × (⟨ F6-RHS x t ⟩ → ⟨ t ∈ˢ F6 x y ⟩)
  F6-spec x y t = fwd , bwd
    where
    RHS : hProp (ℓ-suc ℓ)
    RHS = F6-RHS x t
    fwd : ⟨ t ∈ˢ F6 x y ⟩ → ⟨ RHS ⟩
    fwd h = PT.rec (snd RHS) go h
      where
      go : Σ[ p ∈ Σ[ u ∈ ⟪ ⋃ (⋃ x) ⟫ ] Σ[ v ∈ ⟪ ⋃ (⋃ x) ⟫ ]
              ⟨ pr (⟪ ⋃ (⋃ x) ⟫↪ u) (⟪ ⋃ (⋃ x) ⟫↪ v) ∈ₛ x ⟩ ]
             (⟪ ⋃ (⋃ x) ⟫↪ (p .fst) ≡ t)
         → ⟨ RHS ⟩
      go (p , q) = ∣ u , (∣ v , (pr-uv∈x , t≡) ∣₁) ∣₁
        where
        u : V ℓ
        u = ⟪ ⋃ (⋃ x) ⟫↪ (p .fst)
        v : V ℓ
        v = ⟪ ⋃ (⋃ x) ⟫↪ (p .snd .fst)
        pr-uv∈x : ⟨ pr u v ∈ˢ x ⟩
        pr-uv∈x = ∈∈ₛ {a = pr u v} {b = x} .snd (p .snd .snd)
        t≡ : ⟨ t ≡ₕ u ⟩
        t≡ = subst (λ w → ⟨ t ≡ₕ w ⟩) (sym q) refl
    bwd : ⟨ RHS ⟩ → ⟨ t ∈ˢ F6 x y ⟩
    bwd = PT.rec (snd (t ∈ F6 x y)) go₀
      where
      go₁ : (u : V ℓ) → Σ[ v ∈ V ℓ ] ⟨ (pr u v ∈ˢ x) ⊓ (t ≡ₕ u) ⟩
          → ⟨ t ∈ F6 x y ⟩
      go₁ u (v , (pruv∈x , t≡)) = ∣ ((mᵤ , (mᵥ , cond)) , path) ∣₁
        where
        mᵤ : ⟪ ⋃ (⋃ x) ⟫
        mᵤ = ∈-asFiber {a = u} {b = ⋃ (⋃ x)} (prL-in-⋃⋃ x u v pruv∈x) .fst
        qu : ⟪ ⋃ (⋃ x) ⟫↪ mᵤ ≡ u
        qu = ∈-asFiber {a = u} {b = ⋃ (⋃ x)} (prL-in-⋃⋃ x u v pruv∈x) .snd
        mᵥ : ⟪ ⋃ (⋃ x) ⟫
        mᵥ = ∈-asFiber {a = v} {b = ⋃ (⋃ x)} (prR-in-⋃⋃ x u v pruv∈x) .fst
        qv : ⟪ ⋃ (⋃ x) ⟫↪ mᵥ ≡ v
        qv = ∈-asFiber {a = v} {b = ⋃ (⋃ x)} (prR-in-⋃⋃ x u v pruv∈x) .snd
        cond : ⟨ pr (⟪ ⋃ (⋃ x) ⟫↪ mᵤ) (⟪ ⋃ (⋃ x) ⟫↪ mᵥ) ∈ₛ x ⟩
        cond = subst (λ w → ⟨ w ∈ₛ x ⟩) (cong₂ pr (sym qu) (sym qv))
                 (∈∈ₛ {a = pr u v} {b = x} .fst pruv∈x)
        path : ⟪ ⋃ (⋃ x) ⟫↪ mᵤ ≡ t
        path = qu ∙ sym t≡
      go₀ : Σ[ u ∈ V ℓ ] ⟨ ⋁ (V ℓ) (λ v → (pr u v ∈ˢ x) ⊓ (t ≡ₕ u)) ⟩
          → ⟨ t ∈ F6 x y ⟩
      go₀ (u , h₁) = PT.rec (snd (t ∈ F6 x y)) (go₁ u) h₁
```

<!--en-->
## F7, the membership relation
<!--zh-->
## F7，隶属关系
<!--/-->

<!--en-->
F7 collects the membership relation restricted to `x`: the pairs `<u,v>` of
members of `x` with `u` a member of `v`. Its index is the product of `x` with
itself, cut to the pairs whose first component belongs to the second. The
specification is the definition read twice, once in each direction.
<!--zh-->
F7 收集限制到 `x` 上的隶属关系：`x` 的成员对 `<u,v>`，其中 `u` 属于 `v`。其索引是 `x` 与自身之积，截到第一分量属于第二分量的那些对上。规格就是把定义正反各读一遍。
<!--/-->

```agda
opaque
  -- perf: the image is a sett over a product of member types cut by a membership condition; sealed so consumers see only F7-spec
  F7 : V ℓ → V ℓ → V ℓ
  F7 x y = sett idx fam
    where
    idx : Type ℓ
    idx = Σ[ p ∈ ⟪ x ⟫ × ⟪ x ⟫ ] ⟨ ⟪ x ⟫↪ (p .fst) ∈ₛ ⟪ x ⟫↪ (p .snd) ⟩
    fam : idx → V ℓ
    fam (p , _) = pr (⟪ x ⟫↪ (p .fst)) (⟪ x ⟫↪ (p .snd))

  F7-RHS : (x t : V ℓ) → hProp (ℓ-suc ℓ)
  F7-RHS x t = ⋁ (V ℓ) (λ u → ⋁ (V ℓ) (λ v →
                 (u ∈ˢ x) ⊓ (v ∈ˢ x) ⊓ (u ∈ˢ v) ⊓ (t ≡ₕ pr u v)))

  F7-spec : (x y t : V ℓ)
          → (⟨ t ∈ˢ F7 x y ⟩ → ⟨ F7-RHS x t ⟩)
          × (⟨ F7-RHS x t ⟩ → ⟨ t ∈ˢ F7 x y ⟩)
  F7-spec x y t = fwd , bwd
    where
    RHS : hProp (ℓ-suc ℓ)
    RHS = F7-RHS x t
    fwd : ⟨ t ∈ˢ F7 x y ⟩ → ⟨ RHS ⟩
    fwd h = PT.rec (snd RHS) go h
      where
      go : Σ[ p ∈ Σ[ q ∈ ⟪ x ⟫ × ⟪ x ⟫ ]
              ⟨ ⟪ x ⟫↪ (q .fst) ∈ₛ ⟪ x ⟫↪ (q .snd) ⟩ ]
             (pr (⟪ x ⟫↪ (p .fst .fst)) (⟪ x ⟫↪ (p .fst .snd)) ≡ t)
         → ⟨ RHS ⟩
      go (p , q) = ∣ u , (∣ v , (u∈x , v∈x , u∈v , t≡) ∣₁) ∣₁
        where
        u : V ℓ
        u = ⟪ x ⟫↪ (p .fst .fst)
        v : V ℓ
        v = ⟪ x ⟫↪ (p .fst .snd)
        u∈x : ⟨ u ∈ˢ x ⟩
        u∈x = ∈∈ₛ {a = u} {b = x} .snd (∈ₛ⟪ x ⟫↪ (p .fst .fst))
        v∈x : ⟨ v ∈ˢ x ⟩
        v∈x = ∈∈ₛ {a = v} {b = x} .snd (∈ₛ⟪ x ⟫↪ (p .fst .snd))
        u∈v : ⟨ u ∈ˢ v ⟩
        u∈v = ∈∈ₛ {a = u} {b = v} .snd (p .snd)
        t≡ : ⟨ t ≡ₕ pr u v ⟩
        t≡ = subst (λ w → ⟨ t ≡ₕ w ⟩) (sym q) refl
    bwd : ⟨ RHS ⟩ → ⟨ t ∈ˢ F7 x y ⟩
    bwd = PT.rec (snd (t ∈ F7 x y)) go₀
      where
      go₁ : (u : V ℓ) → Σ[ v ∈ V ℓ ]
              ⟨ (u ∈ˢ x) ⊓ (v ∈ˢ x) ⊓ (u ∈ˢ v) ⊓ (t ≡ₕ pr u v) ⟩
          → ⟨ t ∈ F7 x y ⟩
      go₁ u (v , (u∈x , v∈x , u∈v , t≡)) = ∣ (((m , n) , cond) , path) ∣₁
        where
        m : ⟪ x ⟫
        m = ∈-asFiber {a = u} {b = x} u∈x .fst
        qu : ⟪ x ⟫↪ m ≡ u
        qu = ∈-asFiber {a = u} {b = x} u∈x .snd
        n : ⟪ x ⟫
        n = ∈-asFiber {a = v} {b = x} v∈x .fst
        qv : ⟪ x ⟫↪ n ≡ v
        qv = ∈-asFiber {a = v} {b = x} v∈x .snd
        cond : ⟨ ⟪ x ⟫↪ m ∈ₛ ⟪ x ⟫↪ n ⟩
        cond = subst (λ w → ⟨ w ∈ₛ ⟪ x ⟫↪ n ⟩) (sym qu)
                 (subst (λ w → ⟨ u ∈ₛ w ⟩) (sym qv) (∈∈ₛ {a = u} {b = v} .fst u∈v))
        path : pr (⟪ x ⟫↪ m) (⟪ x ⟫↪ n) ≡ t
        path = cong₂ pr qu qv ∙ sym t≡
      go₀ : Σ[ u ∈ V ℓ ] ⟨ ⋁ (V ℓ) (λ v →
              (u ∈ˢ x) ⊓ (v ∈ˢ x) ⊓ (u ∈ˢ v) ⊓ (t ≡ₕ pr u v)) ⟩
          → ⟨ t ∈ F7 x y ⟩
      go₀ (u , h₁) = PT.rec (snd (t ∈ F7 x y)) (go₁ u) h₁
```

<!--en-->
## F9, the ordered pair
<!--zh-->
## F9，有序对
<!--/-->

<!--en-->
F9 is the pair producer: its value at `x` and `y` is the ordered pair
`<x,y>`, the coding chapter's Kuratowski pair. As a set, that pair has two
members, the singleton of `x` and the unordered pair of `x` and `y`, and the
specification is exactly that.
<!--zh-->
F9 是对的产生者：它在 `x`、`y` 处的值就是有序对 `<x,y>`，即编码章的 Kuratowski 对。作为集合，该对有两个成员，`x` 的单点集与 `x`、`y` 的无序对，规格正是如此。
<!--/-->

```agda
F9 : V ℓ → V ℓ → V ℓ
F9 x y = pr x y

F9-spec : (x y t : V ℓ)
        → (⟨ t ∈ˢ F9 x y ⟩ → ⟨ (t ≡ₕ ⁅ x ⁆s) ⊔ (t ≡ₕ ⁅ x , y ⁆) ⟩)
        × (⟨ (t ≡ₕ ⁅ x ⁆s) ⊔ (t ≡ₕ ⁅ x , y ⁆) ⟩ → ⟨ t ∈ˢ F9 x y ⟩)
F9-spec x y t = fwd , bwd
  where
  fwd : ⟨ t ∈ˢ F9 x y ⟩ → ⟨ (t ≡ₕ ⁅ x ⁆s) ⊔ (t ≡ₕ ⁅ x , y ⁆) ⟩
  fwd h = pairing-ax (⁅ x ⁆s) (⁅ x , y ⁆) t .fst
    (∈∈ₛ {a = t} {b = F9 x y} .fst h)
  bwd : ⟨ (t ≡ₕ ⁅ x ⁆s) ⊔ (t ≡ₕ ⁅ x , y ⁆) ⟩ → ⟨ t ∈ˢ F9 x y ⟩
  bwd h = ∈∈ₛ {a = t} {b = F9 x y} .snd
    (pairing-ax (⁅ x ⁆s) (⁅ x , y ⁆) t .snd h)
```

<!--en-->
## Recap
<!--zh-->
## 小结
<!--/-->

<!--en-->
The operations layer is open. F0, F5, and F9 wrap machinery the tree already
had, and their specifications are the library's pairing and union laws
restated in the structure's membership; F1, F2, F3, F4, F6, and F7 are built
as images of small index types and sealed opaque, so their consumers see only
the specifications proved here. F3 and F4 read pairs out of their second
argument and re-emit them with a member of the first inserted or appended,
under the right-nested triple convention; F6 reads the domains; F7 collects
the membership relation inside its argument. Nothing here is classical, and
nothing unfolds into the nested brace expressions the coding chapter warned
against.
<!--zh-->
运算层开张。F0、F5、F9 包装树中已有的机制，其规格即库的配对与并定律改用结构隶属陈述；F1、F2、F3、F4、F6、F7 则作为小索引类型之像新建并封以 opaque，消费者只看见此处证出的规格。F3 与 F4 从第二参数中读出对，把第一参数的成员插入或接续其中，遵循右嵌套的三元组约定；F6 取定义域；F7 收集参数内的隶属关系。此处没有任何经典逻辑，也没有任何展开成编码章所警戒的嵌套花括号表达式之处。
<!--/-->
