# Which ordinals appear at which stage

<!--en-->
One question about the tower is still open, and it is the one the axiom of
infinity turns on: given a stage, exactly which ordinals have appeared by then?
The answer is as clean as it could be. The ordinals in `Lset α` are precisely
the members of `α`, so the tower's index and its ordinal content agree, level
for level, and an ordinal first appears at the stage after itself.

Both halves are real work. One direction says an ordinal cannot appear early:
if it is in `Lset α` then it is a member of `α`. That is the harder one, and it
goes through rank, which is why the previous chapter built rank at all. A set in
`Lset α` is a definable subset of some earlier stage, its members therefore have
rank below that stage by induction, and so its own rank is bounded; being an
ordinal, it is its own rank.

The other direction says an ordinal cannot appear late: every member of `α` is
already in `Lset α`. That one is a straight induction, given that an ordinal
appears at the stage after itself, which is the theorem being proved. The
circularity is only apparent: the induction hypothesis supplies the statement
for the members, and the members are the only thing needed.

With both halves the ordinals of a stage are carved out of it by a single
formula, "is an ordinal", which is Δ₀ because transitivity can be said with
bounded quantifiers alone. So `α` is a definable subset of `Lset α`, and the
previous chapter's closure engine finishes the job.
<!--zh-->
关于塔还有一个问题悬而未决，而无穷公理正系于此：给定一个阶段，到那时为止究竟出现了哪些序数？答案再干净不过。`Lset α` 中的序数恰是 `α` 的成员，故塔的索引与它的序数内容逐层一致，而序数首次现身于自身之后的那个阶段。

两半都是真功夫。一个方向说序数不会提前现身：若它在 `Lset α` 中，则它是 `α` 的成员。这是较难的一半，要经过秩，而这正是上一章造出秩的原因。`Lset α` 中的集合是某个更早阶段的可定义子集，依归纳其成员的秩低于那个阶段，故它自身的秩有界；而作为序数，它就是自身的秩。

另一个方向说序数不会迟到：`α` 的每个成员都已在 `Lset α` 中。那一半是直截的归纳，前提是序数现身于自身之后的阶段，而那正是正在证的定理。这个循环只是表象：归纳假设为诸成员供应该陈述，而所需的恰只是诸成员。

两半齐备，一个阶段中的序数便由单一公式「是序数」从中刻出，该公式是 Δ₀ 的，因为传递性只用有界量词就说得出来。于是 `α` 是 `Lset α` 的可定义子集，上一章的收尾引擎随即收工。
<!--/-->

```agda
{-# OPTIONS --cubical --safe --guardedness #-}

open import Base.Prelude
open import Base.Truth
open import Base.Classical using ( LEM )

module L.Ordinal.Stages {ℓ : Level} (lem : LEM (ℓ-suc ℓ)) where

open import FOL.ZFStructure using ( module hPropStructure )
open import FOL.Syntax using ( Formula; var; _∈̇_; _∧̇_; ∀̇∈ )
open import FOL.LevyHierarchy using ( Δ₀; δ-∈; δ-∧; δ-∀∈ )
open import FOL.Manipulation.Relabelling using ( mapFo )
open import V.Hierarchy {ℓ} using ( 𝒮ᵥ; ∈-induction; ∈-irrefl )
open import V.Model {ℓ} using ( ∈sucV-elim; ∈sucV-inl; self∈sucV )
open import L.Definability {ℓ} using ( module DefOf )
open import L.Constructible {ℓ}
  using ( IsOrd; isTransV; Lset; Lset-layer; Lset-compute; layer-trans
        ; 𝒟ₒ; 𝒟ₒ-intro; 𝒟ₒ-inv; Lset-mono )
open import L.Ordinal {ℓ} using ( mem-ord; suc-ord; numeral-ord; #∈ω )
open import L.Ordinal.Linear {ℓ} lem using ( ord-tri )
open import L.Rank {ℓ} using ( rank; rank-compute; rank-ord; rank-fix )

open import Cubical.Data.Sum as Sum using ( _⊎_; inl; inr )
import Cubical.Data.Empty as Empty
import Cubical.HITs.PropositionalTruncation as PT
open PT using ( ∣_∣₁ )
open import Cubical.HITs.CumulativeHierarchy.Base using ( sett )
open import Cubical.HITs.CumulativeHierarchy.Properties
  using ( _∈ₛ_; ∈∈ₛ; ∈-asFiber; ⟪_⟫; ⟪_⟫↪; ∈ₛ⟪_⟫↪_; extensionality; _⊆_ )
open import Cubical.HITs.CumulativeHierarchy.Constructions
  using ( ⋃_; union-ax; module InfinitySet )
open InfinitySet using ( sucV; #_; ω )

open TruthAlgebra (hPropAlgebra (ℓ-suc ℓ))
open hPropStructure 𝒮ᵥ
```

<!--en-->
## Comparison, twice
<!--zh-->
## 两次比较
<!--/-->

<!--en-->
Two consequences of trichotomy, both about successors. First, inclusion between
ordinals puts the smaller inside the successor of the larger: compare them, and
the third case, where the larger belongs to the smaller, contradicts inclusion
by way of no set belonging to itself.

Each branch is pulled out as a named helper with its conclusion written down.
That is not decoration: the conclusion is a heavy membership type, and left
inline in a case split it would be normalized in every branch. Naming it keeps
it neutral. The same discipline governs every later case split in this chapter.
<!--zh-->
三歧的两个推论，都是关于后继的。其一，序数之间的包含把较小者放进较大者的后继里：比较二者，而第三种情形 (较大者属于较小者) 经「没有集合属于自身」与包含关系矛盾。

每个分支都抽成写明结论的具名辅助件。这不是装饰：结论是重型的隶属类型，若内联在分情形里，每个分支都会把它归一化。命名使它保持中性。本章此后每次分情形都遵守同一纪律。
<!--/-->

```agda
private
  ∈-case : (a b : S) → ⟨ a ∈ˢ b ⟩ → ⟨ a ∈ˢ sucV b ⟩
  ∈-case a b a∈b = ∈sucV-inl a∈b

  ≡-case : (a b : S) → a ≡ b → ⟨ a ∈ˢ sucV b ⟩
  ≡-case a b a≡b = subst (λ w → ⟨ w ∈ˢ sucV b ⟩) (sym a≡b) (self∈sucV b)

  wit-case : (a b : S) → ((y : S) → ⟨ y ∈ˢ a ⟩ → ⟨ y ∈ˢ b ⟩)
           → ⟨ b ∈ˢ a ⟩ → ⟨ a ∈ˢ sucV b ⟩
  wit-case a b a⊆b b∈a = Empty.rec (∈-irrefl b (a⊆b b b∈a))

⊆→∈suc : (a b : S) → IsOrd a → IsOrd b
       → ((y : S) → ⟨ y ∈ˢ a ⟩ → ⟨ y ∈ˢ b ⟩) → ⟨ a ∈ˢ sucV b ⟩
⊆→∈suc a b orda ordb a⊆b = Sum.rec
  (∈-case a b)
  (Sum.rec (≡-case a b) (wit-case a b a⊆b))
  (ord-tri a orda b ordb)
```

<!--en-->
Second, a member's successor does not overshoot: if `β` belongs to `α`, then
`sucV β` belongs to `α` or is `α` itself. Compare `sucV β` with `α`; the
remaining case has `α` inside `sucV β`, hence `α` a member of `β` or equal to
it, and either way `α` belongs to itself.
<!--zh-->
其二，成员的后继不会越过头：若 `β` 属于 `α`，则 `sucV β` 属于 `α`，或就是 `α`。比较 `sucV β` 与 `α`；余下的情形把 `α` 放进 `sucV β`，于是 `α` 或是 `β` 的成员、或与之相等，两种情形都推出 `α` 属于自身。
<!--/-->

```agda
private
  Out : S → S → Type (ℓ-suc ℓ)
  Out β α = ⟨ sucV β ∈ˢ α ⟩ ⊎ (sucV β ≡ α)

  overshoot : (β α : S) → IsOrd α → ⟨ β ∈ˢ α ⟩ → ⟨ α ∈ˢ sucV β ⟩ → Out β α
  overshoot β α ordα β∈α α∈sβ = Empty.rec*
    (∈sucV-elim {A = β} {x = α} {P = Empty.⊥* {ℓ-suc ℓ}} Empty.isProp⊥* α∈sβ
      (λ α∈β → lift (∈-irrefl α (ordα .fst α∈β β∈α)))
      (λ α≡β → lift (∈-irrefl α (subst (λ w → ⟨ w ∈ˢ α ⟩) (sym α≡β) β∈α))))

suc∈or≡ : (β α : S) → IsOrd β → IsOrd α → ⟨ β ∈ˢ α ⟩
        → ⟨ sucV β ∈ˢ α ⟩ ⊎ (sucV β ≡ α)
suc∈or≡ β α ordβ ordα β∈α = go (ord-tri (sucV β) (suc-ord ordβ) α ordα)
  where
  go : (⟨ sucV β ∈ˢ α ⟩ ⊎ ((sucV β ≡ α) ⊎ ⟨ α ∈ˢ sucV β ⟩)) → Out β α
  go (inl s∈α)        = inl s∈α
  go (inr (inl s≡α))  = inr s≡α
  go (inr (inr α∈sβ)) = overshoot β α ordα β∈α α∈sβ
```

<!--en-->
And the cumulation lemma it exists for: an ordinal that has appeared at its own
successor stage has appeared at every later stage, where later means the index
is above it.
<!--zh-->
以及它为之而生的累积引理：在自身后继阶段现身过的序数，在此后每个阶段都已现身，其中「此后」指索引在其之上。
<!--/-->

```agda
private
  cumul-∈ : (β α : S) → ⟨ sucV β ∈ˢ α ⟩ → ⟨ β ∈ˢ Lset (sucV β) ⟩
          → ⟨ β ∈ˢ Lset α ⟩
  cumul-∈ β α s∈α = Lset-mono {α = α} {β = sucV β} s∈α {x = β}

  cumul-≡ : (β α : S) → sucV β ≡ α → ⟨ β ∈ˢ Lset (sucV β) ⟩ → ⟨ β ∈ˢ Lset α ⟩
  cumul-≡ β α s≡α = subst (λ w → ⟨ β ∈ˢ Lset w ⟩) s≡α

Lset-cumul : (β α : S) → IsOrd β → IsOrd α → ⟨ β ∈ˢ α ⟩
           → ⟨ β ∈ˢ Lset (sucV β) ⟩ → ⟨ β ∈ˢ Lset α ⟩
Lset-cumul β α ordβ ordα β∈α β∈Lsβ =
  Sum.rec (λ s∈α → cumul-∈ β α s∈α β∈Lsβ)
          (λ s≡α → cumul-≡ β α s≡α β∈Lsβ)
          (suc∈or≡ β α ordβ ordα β∈α)
```

<!--en-->
## Nothing appears before its rank
<!--zh-->
## 没有东西早于自身的秩现身
<!--/-->

<!--en-->
The harder half. By induction on the stage index: a set in `Lset α` lies in the
definable subsets of `Lset β` for some `β` in `α`, so it is a subset of
`Lset β`; each of its members therefore has rank in `β` by the inductive
hypothesis; so its own rank, which is the union of the successors of those
ranks, is included in `β`; comparison puts it inside the successor of `β`, and
that is inside `α`.
<!--zh-->
较难的那一半。沿阶段索引归纳：`Lset α` 中的集合落在某个 `β ∈ α` 的 `Lset β` 的可定义子集里，故它是 `Lset β` 的子集；于是依归纳假设它的每个成员的秩都在 `β` 中；故它自身的秩，即那些秩的后继之并，包含于 `β`；比较把它放进 `β` 的后继里面，而那在 `α` 里面。
<!--/-->

```agda
rank-Lset : (α : S) → IsOrd α → (x : S) → ⟨ x ∈ˢ Lset α ⟩ → ⟨ rank x ∈ˢ α ⟩
rank-Lset = ∈-induction
  {P = λ α → IsOrd α → (x : S) → ⟨ x ∈ˢ Lset α ⟩ → ⟨ rank x ∈ˢ α ⟩} step
  where
  step : (α : S)
       → (∀ β → β ∈ᵗ α → IsOrd β → (x : S) → ⟨ x ∈ˢ Lset β ⟩ → ⟨ rank x ∈ˢ β ⟩)
       → IsOrd α → (x : S) → ⟨ x ∈ˢ Lset α ⟩ → ⟨ rank x ∈ˢ α ⟩
  step α IH ordα x x∈Lα = PT.rec (snd (rank x ∈ˢ α)) fromUnion x∈⋃
    where
    s : ⟪ α ⟫ → S
    s m = 𝒟ₒ (Lset (⟪ α ⟫↪ m))

    x∈⋃ = union-ax (sett ⟪ α ⟫ s) x .fst
      (∈∈ₛ {a = x} {b = ⋃ (sett ⟪ α ⟫ s)} .fst
        (subst (λ w → ⟨ x ∈ˢ w ⟩) (Lset-compute α) x∈Lα))

    fromUnion : Σ[ v ∈ S ] (⟨ v ∈ₛ sett ⟪ α ⟫ s ⟩ × ⟨ x ∈ₛ v ⟩) → ⟨ rank x ∈ˢ α ⟩
    fromUnion (v , (v∈ₛsett , x∈ₛv)) = PT.rec (snd (rank x ∈ˢ α)) fromFiber
      (∈∈ₛ {a = v} {b = sett ⟪ α ⟫ s} .snd v∈ₛsett)
      where
      fromFiber : Σ[ m ∈ ⟪ α ⟫ ] (s m ≡ v) → ⟨ rank x ∈ˢ α ⟩
      fromFiber (m , sm≡v) = rankx∈α
        where
        β = ⟪ α ⟫↪ m
        β∈α : ⟨ β ∈ˢ α ⟩
        β∈α = ∈∈ₛ {a = β} {b = α} .snd (∈ₛ⟪ α ⟫↪ m)
        ordβ : IsOrd β
        ordβ = mem-ord {A = α} ordα β β∈α
        x∈𝒟ₒLβ : ⟨ x ∈ˢ 𝒟ₒ (Lset β) ⟩
        x∈𝒟ₒLβ = ∈∈ₛ {a = x} {b = 𝒟ₒ (Lset β)} .snd
          (subst (λ w → ⟨ x ∈ₛ w ⟩) (sym sm≡v) x∈ₛv)
        x⊆Lβ : (y : S) → ⟨ y ∈ˢ x ⟩ → ⟨ y ∈ˢ Lset β ⟩
        x⊆Lβ = DefOf.Def∋⊆A (Lset β) x (𝒟ₒ-inv (Lset β) x x∈𝒟ₒLβ)
        ry∈β : (y : S) → ⟨ y ∈ˢ x ⟩ → ⟨ rank y ∈ˢ β ⟩
        ry∈β y y∈x = IH β β∈α ordβ y (x⊆Lβ y y∈x)

        rankx⊆β : (z : S) → ⟨ z ∈ˢ rank x ⟩ → ⟨ z ∈ˢ β ⟩
        rankx⊆β z z∈rx = PT.rec (snd (z ∈ˢ β)) viaUnion
          (union-ax (sett ⟪ x ⟫ g) z .fst
            (∈∈ₛ {a = z} {b = ⋃ (sett ⟪ x ⟫ g)} .fst
              (subst (λ w → ⟨ z ∈ˢ w ⟩) (rank-compute x) z∈rx)))
          where
          g : ⟪ x ⟫ → S
          g i = sucV (rank (⟪ x ⟫↪ i))
          viaUnion : Σ[ w ∈ S ] (⟨ w ∈ₛ sett ⟪ x ⟫ g ⟩ × ⟨ z ∈ₛ w ⟩) → ⟨ z ∈ˢ β ⟩
          viaUnion (w , (w∈ₛsett , z∈ₛw)) = PT.rec (snd (z ∈ˢ β)) viaFib
            (∈∈ₛ {a = w} {b = sett ⟪ x ⟫ g} .snd w∈ₛsett)
            where
            viaFib : Σ[ i ∈ ⟪ x ⟫ ] (g i ≡ w) → ⟨ z ∈ˢ β ⟩
            viaFib (i , gi≡w) =
              ∈sucV-elim {A = rank yᵢ} {x = z} (snd (z ∈ˢ β))
                (∈∈ₛ {a = z} {b = sucV (rank yᵢ)} .snd
                  (subst (λ W → ⟨ z ∈ₛ W ⟩) (sym gi≡w) z∈ₛw))
                (λ z∈ryᵢ → ordβ .fst z∈ryᵢ (ry∈β yᵢ yᵢ∈x))
                (λ z≡ryᵢ → subst (λ w → ⟨ w ∈ˢ β ⟩) (sym z≡ryᵢ) (ry∈β yᵢ yᵢ∈x))
              where
              yᵢ = ⟪ x ⟫↪ i
              yᵢ∈x : ⟨ yᵢ ∈ˢ x ⟩
              yᵢ∈x = ∈∈ₛ {a = yᵢ} {b = x} .snd (∈ₛ⟪ x ⟫↪ i)

        rankx∈α : ⟨ rank x ∈ˢ α ⟩
        rankx∈α = ∈sucV-elim {A = β} {x = rank x} (snd (rank x ∈ˢ α))
          (⊆→∈suc (rank x) β (rank-ord x) ordβ rankx⊆β)
          (λ rx∈β → ordα .fst rx∈β β∈α)
          (λ rx≡β → subst (λ w → ⟨ w ∈ˢ α ⟩) (sym rx≡β) β∈α)
```

<!--en-->
For an ordinal the conclusion simplifies, because rank fixes it: an ordinal in
`Lset α` is a member of `α`.
<!--zh-->
对序数，结论简化，因为秩固定它：`Lset α` 中的序数是 `α` 的成员。
<!--/-->

```agda
ord∈Lset→∈ : (α : S) → IsOrd α → (x : S) → IsOrd x → ⟨ x ∈ˢ Lset α ⟩
           → ⟨ x ∈ˢ α ⟩
ord∈Lset→∈ α ordα x ordx x∈Lα =
  subst (λ w → ⟨ w ∈ˢ α ⟩) (rank-fix x ordx) (rank-Lset α ordα x x∈Lα)
```

<!--en-->
## Being an ordinal, said with bounded quantifiers
<!--zh-->
## 用有界量词说「是序数」
<!--/-->

<!--en-->
The predicate is two clauses, and both are already bounded: a set is transitive
when every member of every member of it is a member of it, and its members are
transitive when the same holds one level down. No unbounded quantifier appears,
so the formula is Δ₀, and no constant appears either, which spares the whole
relabelling apparatus.

The indices are de Bruijn: each bounded quantifier binds a fresh variable `0`
and pushes the earlier ones outward, so after two binders the candidate ordinal
is at index 2.
<!--zh-->
这个谓词是两条子句，而两条都已有界：集合传递，指其成员之成员皆是其成员；成员皆传递，指同一条在低一层成立。没有无界量词出现，故公式是 Δ₀；也没有常元出现，这省掉了整套重标机器。

索引采用 de Bruijn：每个有界量词约束一个新的变元 `0`，把先前的向外推，故两层约束之后，候选序数位于索引 2。
<!--/-->

```agda
φ-ord : ∀ {ℓk} {K : Type ℓk} → Formula K 1
φ-ord =
  (∀̇∈ (var zero) (∀̇∈ (var zero) (var zero ∈̇ var (suc (suc zero)))))
  ∧̇
  (∀̇∈ (var zero)
    (∀̇∈ (var zero) (∀̇∈ (var zero) (var zero ∈̇ var (suc (suc zero))))))

φ-ord-Δ₀ : ∀ {ℓk} {K : Type ℓk} → Δ₀ (φ-ord {K = K})
φ-ord-Δ₀ = δ-∧ (δ-∀∈ (δ-∀∈ δ-∈)) (δ-∀∈ (δ-∀∈ (δ-∀∈ δ-∈)))
```

<!--en-->
## The ordinals of a stage
<!--zh-->
## 一个阶段中的序数
<!--/-->

<!--en-->
Fix a stage. Read through the previous chapter's bridge, satisfaction of the
formula in the ambient hierarchy unfolds to exactly the two clauses of the
ordinal predicate, so the two are interchangeable by reshuffling arguments.
Then the definable subset it carves is `α` itself: a member of it is an ordinal
of the stage, hence a member of `α` by the rank half; and a member of `α` is an
ordinal that has already appeared, by cumulation, so it satisfies the formula.

Cumulation needs, for each member of `α`, that it appears at its own successor
stage. That is the theorem itself, so it enters here as a hypothesis, and the
induction below is what supplies it.
<!--zh-->
固定一个阶段。经上一章那道桥读出来，公式在环境层级中的满足恰好展开成序数谓词的两条子句，故二者只需重排参数即可互换。然后它刻出的可定义子集就是 `α` 自身：其成员是该阶段的序数，故经秩那一半是 `α` 的成员；而 `α` 的成员是已经现身过的序数，经累积引理，故满足该公式。

累积引理需要 `α` 的每个成员都在自身的后继阶段现身。那正是本定理自身，故它在此作为假设进入，而下面的归纳正是供应它的东西。
<!--/-->

```agda
module OrdAt (α : S) (ordα : IsOrd α) where
  private
    A = Lset α
    Atrans = layer-trans (Lset-layer α)
    module DefA = DefOf A
    module RefA = DefA.Refine Atrans
    open RefA.Abs using ( _⊨ᵛ_ )

    φ : Formula ⟪ A ⟫ 1
    φ = φ-ord {K = ⟪ A ⟫}

  ⊨ᵛ→ord : (m : ⟪ A ⟫) → ⟨ (⟪ A ⟫↪ m ∷ []) ⊨ᵛ (mapFo DefA.ι φ) ⟩
         → IsOrd (⟪ A ⟫↪ m)
  ⊨ᵛ→ord m sat = transB , memTransB
    where
    B = ⟪ A ⟫↪ m
    transB : isTransV B
    transB {x} {y} y∈x x∈B = sat .fst x x∈B y y∈x
    memTransB : (x : S) → ⟨ x ∈ˢ B ⟩ → isTransV x
    memTransB x x∈B {y} {z} z∈y y∈x = sat .snd x x∈B y y∈x z z∈y

  ord→⊨ᵛ : (m : ⟪ A ⟫) → IsOrd (⟪ A ⟫↪ m)
         → ⟨ (⟪ A ⟫↪ m ∷ []) ⊨ᵛ (mapFo DefA.ι φ) ⟩
  ord→⊨ᵛ m ord = c1 , c2
    where
    B = ⟪ A ⟫↪ m
    c1 : (x : S) → ⟨ x ∈ˢ B ⟩ → (y : S) → ⟨ y ∈ˢ x ⟩ → ⟨ y ∈ˢ B ⟩
    c1 x x∈B y y∈x = ord .fst y∈x x∈B
    c2 : (x : S) → ⟨ x ∈ˢ B ⟩ → (y : S) → ⟨ y ∈ˢ x ⟩
       → (z : S) → ⟨ z ∈ˢ y ⟩ → ⟨ z ∈ˢ x ⟩
    c2 x x∈B y y∈x z z∈y = ord .snd x x∈B z∈y y∈x

  defSet-φ-ord : ((β : S) → ⟨ β ∈ˢ α ⟩ → ⟨ β ∈ˢ A ⟩) → DefA.defSet φ ≡ α
  defSet-φ-ord α⊆A = extensionality (DefA.defSet φ) α (sub₁ , sub₂)
    where
    sub₁ : ⟨ DefA.defSet φ ⊆ α ⟩
    sub₁ y y∈ₛ = ∈∈ₛ {a = y} {b = α} .fst
      (y∈α (∈∈ₛ {a = y} {b = DefA.defSet φ} .snd y∈ₛ))
      where
      y∈α : ⟨ y ∈ˢ DefA.defSet φ ⟩ → ⟨ y ∈ˢ α ⟩
      y∈α y∈def = ord∈Lset→∈ α ordα y ordy y∈A
        where
        y∈A = DefA.defSet⊆A φ y y∈def
        fib = ∈-asFiber {a = y} {b = A} y∈A
        m = fib .fst
        q = fib .snd
        sat : ⟨ (⟪ A ⟫↪ m ∷ []) ⊨ᵛ (mapFo DefA.ι φ) ⟩
        sat = subst ⟨_⟩ (RefA.abs-defSet φ φ-ord-Δ₀ m)
                (subst (λ w → ⟨ w ∈ˢ DefA.defSet φ ⟩) (sym q) y∈def)
        ordy : IsOrd y
        ordy = subst IsOrd q (⊨ᵛ→ord m sat)

    sub₂ : ⟨ α ⊆ DefA.defSet φ ⟩
    sub₂ y y∈ₛ = ∈∈ₛ {a = y} {b = DefA.defSet φ} .fst
      (y∈def (∈∈ₛ {a = y} {b = α} .snd y∈ₛ))
      where
      y∈def : ⟨ y ∈ˢ α ⟩ → ⟨ y ∈ˢ DefA.defSet φ ⟩
      y∈def y∈α = subst (λ w → ⟨ w ∈ˢ DefA.defSet φ ⟩) q
        (subst ⟨_⟩ (sym (RefA.abs-defSet φ φ-ord-Δ₀ m)) sat)
        where
        ordy = mem-ord {A = α} ordα y y∈α
        y∈A = α⊆A y y∈α
        fib = ∈-asFiber {a = y} {b = A} y∈A
        m = fib .fst
        q = fib .snd
        sat : ⟨ (⟪ A ⟫↪ m ∷ []) ⊨ᵛ (mapFo DefA.ι φ) ⟩
        sat = ord→⊨ᵛ m (subst IsOrd (sym q) ordy)
```

<!--en-->
## An ordinal appears at its successor
<!--zh-->
## 序数现身于其后继
<!--/-->

<!--en-->
The induction. The hypothesis gives, for every member of `α`, that it appears at
its own successor stage; cumulation raises each of them into `Lset α`, which is
the inclusion the previous section asked for; the formula then carves `α` out of
`Lset α`; and one branch of the union at the next stage delivers it.
<!--zh-->
归纳。假设给出 `α` 的每个成员都在自身的后继阶段现身；累积引理把它们逐一抬进 `Lset α`，那正是上一节所索取的包含关系；公式随即从 `Lset α` 中刻出 `α`；而下一阶段那个并的一支把它交付。
<!--/-->

```agda
private
  𝒟ₒ→Lset-suc : (α : S) → ⟨ α ∈ˢ 𝒟ₒ (Lset α) ⟩ → ⟨ α ∈ˢ Lset (sucV α) ⟩
  𝒟ₒ→Lset-suc α α∈𝒟ₒ =
    subst (λ w → ⟨ α ∈ˢ w ⟩) (sym (Lset-compute (sucV α)))
      (∈∈ₛ {a = α} {b = ⋃ (sett ⟪ sucV α ⟫ s)} .snd
        (union-ax (sett ⟪ sucV α ⟫ s) α .snd
          ∣ 𝒟ₒ (Lset α) , (𝒟ₒLα∈ₛsett , α∈ₛ𝒟ₒLα) ∣₁))
    where
    s : ⟪ sucV α ⟫ → S
    s m = 𝒟ₒ (Lset (⟪ sucV α ⟫↪ m))
    fib = ∈-asFiber {a = α} {b = sucV α} (self∈sucV α)
    m = fib .fst
    p : ⟪ sucV α ⟫↪ m ≡ α
    p = fib .snd
    𝒟ₒLα∈ₛsett : ⟨ 𝒟ₒ (Lset α) ∈ₛ sett ⟪ sucV α ⟫ s ⟩
    𝒟ₒLα∈ₛsett = ∈∈ₛ {a = 𝒟ₒ (Lset α)} {b = sett ⟪ sucV α ⟫ s} .fst
      ∣ m , cong (λ b → 𝒟ₒ (Lset b)) p ∣₁
    α∈ₛ𝒟ₒLα : ⟨ α ∈ₛ 𝒟ₒ (Lset α) ⟩
    α∈ₛ𝒟ₒLα = ∈∈ₛ {a = α} {b = 𝒟ₒ (Lset α)} .fst α∈𝒟ₒ

ord∈Lset-suc : (α : S) → IsOrd α → ⟨ α ∈ˢ Lset (sucV α) ⟩
ord∈Lset-suc = ∈-induction
  {P = λ α → IsOrd α → ⟨ α ∈ˢ Lset (sucV α) ⟩} step
  where
  step : (α : S) → (∀ β → β ∈ᵗ α → IsOrd β → ⟨ β ∈ˢ Lset (sucV β) ⟩)
       → IsOrd α → ⟨ α ∈ˢ Lset (sucV α) ⟩
  step α IH ordα = 𝒟ₒ→Lset-suc α α∈𝒟ₒ
    where
    α⊆A : (β : S) → ⟨ β ∈ˢ α ⟩ → ⟨ β ∈ˢ Lset α ⟩
    α⊆A β β∈α = Lset-cumul β α ordβ ordα β∈α (IH β β∈α ordβ)
      where
      ordβ = mem-ord {A = α} ordα β β∈α
    α∈𝒟ₒ : ⟨ α ∈ˢ 𝒟ₒ (Lset α) ⟩
    α∈𝒟ₒ = 𝒟ₒ-intro (Lset α) α
      ∣ φ-ord {K = ⟪ Lset α ⟫} , OrdAt.defSet-φ-ord α ordα α⊆A ∣₁
```

<!--en-->
## The numerals at ω
<!--zh-->
## ω 处的数码
<!--/-->

<!--en-->
The stage theorem has one limit instance the next chapter spends: every
numeral appears in `Lset ω`. The proof climbs the tower's monotonicity
along the successor chain. The successor stage of a numeral lies inside
`Lset ω`, since the numeral's successor is a member of `ω`; and the
numeral appears at that successor stage, by `ord∈Lset-suc`.
<!--zh-->
本章的阶段定理有一个下一章将花掉的极限实例：每个数码都现身于 `Lset ω`。证明沿后继链攀爬塔的单调性。数码的后继阶段落在 `Lset ω` 内，因为数码的后继是 `ω` 的成员；而数码现身于那个后继阶段，经由 `ord∈Lset-suc`。
<!--/-->

```agda
nk : ℕ → S
nk k = # k

numeral∈Lsetω : (k : ℕ) → ⟨ nk k ∈ˢ Lset ω ⟩
numeral∈Lsetω k = Lset-mono {α = ω} {β = sucV (nk k)} (#∈ω (suc k))
  (ord∈Lset-suc (nk k) (numeral-ord k))
```

<!--en-->
## Recap
<!--zh-->
## 小结
<!--/-->

<!--en-->
`ord∈Lset-suc`{.Agda} says an ordinal appears at the stage after itself, and
`ord∈Lset→∈`{.Agda} says it appears no earlier. Together the ordinals of
`Lset α` are exactly the members of `α`. The chapter is classical, through the
two comparisons of its first section, and everything else it uses was
constructive. The next chapter spends the result once, on `ω`, and the axiom of
infinity closes.
<!--zh-->
`ord∈Lset-suc`{.Agda} 说序数现身于自身之后的那个阶段，`ord∈Lset→∈`{.Agda} 说它不会更早现身。二者合起来，`Lset α` 中的序数恰是 `α` 的成员。本章是经典的，经由第一节那两次比较，而它用到的其余一切都是构造性的。下一章把这个结果花掉一次，用在 `ω` 上，无穷公理随之合龙。
<!--/-->
