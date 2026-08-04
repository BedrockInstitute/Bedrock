# Counting formulas

<!--en-->
Part 1 built the object language; this chapter counts it. A formula over a constant
domain `K`{.Agda} is a finite tree whose leaves are drawn either from `K` (the
constants) or from the finitely many free variables, and the question is how many
formulas of a given shape there can be. The answer has two halves, and both are
injections rather than equalities. The first half is the **shape-count**: for each
arity `k`, the parameter-free formulas, the formulas over the empty constant domain
`⊥*`{.Agda}, inject into the natural numbers, per arity. The second half is the
**count**: every formula with one free variable over an arbitrary domain `K` injects
into the disjoint union over `k` of the parameter-free formulas of arity `k` paired
with a tuple of `k` constants; a formula is a shape plus a tuple, and the two halves
together say the shapes are countable. A later chapter of Part 4 composes these two
injections; this chapter stops at them. Nothing here is about constructibility: the
objects being counted are the syntax of Part 1, and the counting needs nothing beyond
the natural numbers, vectors and lists, which is why the chapter reads under
`FOL`{.Agda} rather than under the constructible universe.
<!--zh-->
第一部构造了对象语言，本章来数它。常量域 `K`{.Agda} 上的公式是一棵有限树，叶子要么取自 `K` (常量)，要么取自有限的自由变量；问题是给定形状的公式能有多少。答案分两半，且两半都是单射而非相等。前半是**形状计数**：对每个元数 `k`，无参公式，即空常量域 `⊥*`{.Agda} 上的公式，按元数单射地落入自然数。后半是**计数**：任意常量域 `K` 上带一个自由变量的每条公式，单射地落入「对 `k` 的 `k` 元无参公式配上 `k` 个常量的元组」之无交并；公式即形状加元组，而两半合起来说的是形状可数。第四部稍后的章节将复合这两条单射；本章止步于此。这里没有任何可构造性的事：被数的对象是第一部的语法，计数所需的不过是自然数、向量与表，故本章归在 `FOL`{.Agda} 名下，而非可构造宇宙名下。
<!--/-->

```agda
{-# OPTIONS --cubical --safe --guardedness #-}

open import Base.Prelude
open import FOL.Syntax using
  ( Term; con; var; Formula; _∈̇_; _≐_; _∧̇_; _∨̇_; _⇒̇_; ¬̇_; ⊤̇; ⊥̇; ∃̇_; ∀̇_; ∀̇∈; ∃̇∈ )
open import FOL.Manipulation.Relabelling using ( mapTm; mapFo )
open import FOL.Manipulation.Parameters using ( countTm; countFo; constantsTm; constantsFo )
open import Cubical.Data.Nat using ( _+_; _·_; snotz; +-comm; +-suc; ·-comm; ·-suc; inj-m+ )
open import Cubical.Data.Nat.Order
  using ( _<_; _≤_; ≤-trans; ≤-k+; ≤-sucℕ; zero-≤; suc-≤-suc
        ; Trichotomy; _≟_; isProp≤; ¬m<m; ≤<-trans; <≤-trans; ≤-·k; <-·sk )
open Trichotomy
open import Cubical.Data.FinData using ( toℕ; fromℕ'; toℕ<n; toFromId' )
open import Cubical.Data.FinData.Properties using ( inj-toℕ )
open import Cubical.Data.Vec using () renaming ( _++_ to _++ᵥ_ )
open import Cubical.Data.List using ( List; []; _∷_; _++_ )
open import Cubical.Foundations.Prelude using ( J; transportRefl )
import Cubical.Data.Empty as Empty

module FOL.Count {ℓ : Level} where
```

<!--en-->
## The shape-count
<!--zh-->
## 形状计数
<!--/-->

<!--en-->
The smaller half first, and its new raw material. Fix the arity `k` and look at the
formulas whose constant domain is empty: a term over `⊥*`{.Agda} is a de Bruijn
variable and nothing else, since the constant constructor is uninhabited, so a
parameter-free formula is a finite tree with twelve constructors whose leaves are
variables from `Fin k`{.Agda}, and per arity there are countably many such trees.
The counting is by **code**: each formula is mapped to a natural number, constructor
by constructor. The coding chapter already codes formulas as sets, tagging a
constructor index onto the codes of the parts; the same scheme works over the natural
numbers, and the only genuinely new raw material is an injective pairing on `ℕ`: the
development's own pairing is the set-theoretic Kuratowski one, which lives in the
hierarchy. The pairing comes first.
<!--zh-->
先看较小的一半，以及它唯一的新原料。固定元数 `k`，看常量域为空的公式：`⊥*`{.Agda} 上的词项除了 de Bruijn 变量别无他物，因为常量构造子无人居住，于是无参公式是十二个构造子的有限树，叶子是从 `Fin k`{.Agda} 取的变量；每个元数之下，这样的树只有可数多棵。计数靠**码**：每条公式按构造子逐层映射到一个自然数。编码章已经以集合为公式编码，把构造子序号贴在各部分的码上；同一方案在自然数上照样成立，而唯一真正的新原料是 `ℕ` 上的单射配对：本书自己的配对是层级里的库拉托夫斯基集合配对。先看配对。
<!--/-->

<!--en-->
The pairing is the square scheme, `pair a b = (a + b)² + a`. Its value lies in the
level interval `[s², s² + s]` where `s = a + b`, and consecutive intervals are
disjoint, so equal values force equal sums, and then equal components. The proof is
the interval argument itself: the four arithmetic lemmas locate the value in its
interval, `sq-lemma` recovers the sum from an equation, and `pair-inj` splits the
equation into its two components. Injectivity is all the coding needs; no bijection
is required.
<!--zh-->
配对取平方方案：`pair a b = (a + b)² + a`。其值落在级区间 `[s², s² + s]` 内，其中 `s = a + b`，相邻区间不相交，故值相等迫使和相等，再迫使分量相等。证明即区间论证本身：四条算术引理把值定位在所属区间，`sq-lemma` 从等式还原出和，`pair-inj` 再把等式拆成两个分量。编码只需要单射；无需双射。
<!--/-->

```agda
pair : ℕ → ℕ → ℕ
pair a b = (a + b) · (a + b) + a

≤+ : (a b : ℕ) → a ≤ a + b
≤+ a b = b , +-comm b a

ss+1 : (s : ℕ) → s · s + s ≡ s · suc s
ss+1 s = +-comm (s · s) s ∙ sym (·-suc s s)

sq-lt : (s t : ℕ) → s < t → s · s + s < t · t
sq-lt s t s<t = <≤-trans
  (subst (λ w → w < t · suc s) (sym (ss+1 s)) (<-·sk {m = s} {n = t} {k = s} s<t))
  (subst (λ z → z ≤ t · t) (·-comm (suc s) t) (≤-·k {m = suc s} {n = t} {k = t} s<t))

lt-chain : (s t a c : ℕ) → a ≤ s → c ≤ t → s < t → s · s + a < t · t + c
lt-chain s t a c a≤s c≤t s<t =
  <≤-trans (≤<-trans (≤-k+ a≤s) (sq-lt s t s<t)) (c , +-comm c (t · t))

gt-chain : (s t a c : ℕ) → a ≤ s → c ≤ t → t < s → t · t + c < s · s + a
gt-chain s t a c a≤s c≤t t<s =
  <≤-trans (≤<-trans (≤-k+ c≤t) (sq-lt t s t<s)) (a , +-comm a (s · s))

sq-lemma : (s t a c : ℕ) → a ≤ s → c ≤ t → s · s + a ≡ t · t + c → s ≡ t
sq-lemma s t a c a≤s c≤t e with s ≟ t
... | eq s≡t = s≡t
... | lt s<t = Empty.rec (¬m<m {t · t + c}
                  (subst (λ w → w < t · t + c) e (lt-chain s t a c a≤s c≤t s<t)))
... | gt t<s = Empty.rec (¬m<m {s · s + a}
                  (subst (λ w → w < s · s + a) (sym e) (gt-chain s t a c a≤s c≤t t<s)))

pair-inj : (a b c d : ℕ) → pair a b ≡ pair c d → (a ≡ c) × (b ≡ d)
pair-inj a b c d p = go (sq-lemma (a + b) (c + d) a c (≤+ a b) (≤+ c d) p)
  where
  go : a + b ≡ c + d → (a ≡ c) × (b ≡ d)
  go s≡t =
    let a≡c = inj-m+ (subst (λ z → z · z + a ≡ (c + d) · (c + d) + c) s≡t p)
        b≡d = inj-m+ (cong (_+ b) (sym a≡c) ∙ s≡t)
    in a≡c , b≡d
```

<!--en-->
With the pairing in hand, the coding is a straight transplant of the coding chapter's
scheme to `ℕ`{.Agda}. Terms first: over the empty domain a term is a variable, coded
by its index `toℕ`; the two empty cases are there because the constant constructor is
uninhabited, and `tcode-inj` is the injectivity, from the injectivity of
`toℕ`{.Agda}. The formula code then tags: constructor 0 for membership, 1 for
equality, 2 through 4 for the three binary connectives, 5 for negation, 6 and 7 for
the two constants, 8 and 9 for the two quantifiers, 10 and 11 for the two bounded
quantifiers, and the payload is the codes of the parts, paired where there are two.
The tag alone separates the twelve constructors, since it sits outside the payload.
<!--zh-->
配对到手，编码就是把编码章的方案直搬到 `ℕ`{.Agda} 上。先看词项：空域上的词项就是变量，以索引 `toℕ` 编码；两个空情形为常量构造子无人居住而设，`tcode-inj` 是从 `toℕ`{.Agda} 的单射性得到的单射性。公式码随后打标签：0 号构造子是成员，1 号是等词，2 至 4 号是三个二元联结词，5 号是否定，6、7 号是两个常量，8、9 号是两个量词，10、11 号是两个有界量词；载荷是各部分的码，有两部分处配成对。标签单独即可区分十二个构造子，因为它坐在载荷之外。
<!--/-->

```agda
tcode : ∀ {k} → Term (⊥* {ℓ}) k → ℕ
tcode (con x) = Empty.rec* {A = ℕ} x
tcode (var i) = toℕ i

tcode-inj : ∀ {k} (t u : Term (⊥* {ℓ}) k) → tcode t ≡ tcode u → t ≡ u
tcode-inj (con x) _ _ = Empty.rec* {A = con x ≡ _} x
tcode-inj _ (con y) _ = Empty.rec* {A = _ ≡ con y} y
tcode-inj (var i) (var j) p = cong var (inj-toℕ p)

code : ∀ {k} → Formula (⊥* {ℓ}) k → ℕ
code (t ∈̇ u)  = pair 0 (pair (tcode t) (tcode u))
code (t ≐ u)  = pair 1 (pair (tcode t) (tcode u))
code (a ∧̇ b)  = pair 2 (pair (code a) (code b))
code (a ∨̇ b)  = pair 3 (pair (code a) (code b))
code (a ⇒̇ b)  = pair 4 (pair (code a) (code b))
code (¬̇ a)    = pair 5 (code a)
code ⊤̇        = pair 6 0
code ⊥̇        = pair 7 0
code (∃̇ a)    = pair 8 (code a)
code (∀̇ a)    = pair 9 (code a)
code (∀̇∈ t a) = pair 10 (pair (tcode t) (code a))
code (∃̇∈ t a) = pair 11 (pair (tcode t) (code a))
```

<!--en-->
Injectivity needs to recover the constructor from the code, and the trick is the
coding chapter's own: the constructor is computed from the tag, so neither side of
the equation has to be matched against the other. `tagOf` and `payOf` split a
formula's code into the two halves, and `shape` says the split is definitional.
<!--zh-->
单射性要从码还原构造子，而办法正是编码章自己的：从标签算出构造子，等式两侧便无须互相对着匹配。`tagOf` 与 `payOf` 把公式的码拆成两半，`shape` 说这个拆分是定义性的。
<!--/-->

```agda
tagOf : ∀ {k} → Formula (⊥* {ℓ}) k → ℕ
tagOf (t ∈̇ u)  = 0
tagOf (t ≐ u)  = 1
tagOf (a ∧̇ b)  = 2
tagOf (a ∨̇ b)  = 3
tagOf (a ⇒̇ b)  = 4
tagOf (¬̇ a)    = 5
tagOf ⊤̇        = 6
tagOf ⊥̇        = 7
tagOf (∃̇ a)    = 8
tagOf (∀̇ a)    = 9
tagOf (∀̇∈ t a) = 10
tagOf (∃̇∈ t a) = 11

payOf : ∀ {k} → Formula (⊥* {ℓ}) k → ℕ
payOf (t ∈̇ u)  = pair (tcode t) (tcode u)
payOf (t ≐ u)  = pair (tcode t) (tcode u)
payOf (a ∧̇ b)  = pair (code a) (code b)
payOf (a ∨̇ b)  = pair (code a) (code b)
payOf (a ⇒̇ b)  = pair (code a) (code b)
payOf (¬̇ a)    = code a
payOf ⊤̇        = 0
payOf ⊥̇        = 0
payOf (∃̇ a)    = code a
payOf (∀̇ a)    = code a
payOf (∀̇∈ t a) = pair (tcode t) (code a)
payOf (∃̇∈ t a) = pair (tcode t) (code a)

shape : ∀ {k} (φ : Formula (⊥* {ℓ}) k) → code φ ≡ pair (tagOf φ) (payOf φ)
shape (t ∈̇ u)  = refl
shape (t ≐ u)  = refl
shape (a ∧̇ b)  = refl
shape (a ∨̇ b)  = refl
shape (a ⇒̇ b)  = refl
shape (¬̇ a)    = refl
shape ⊤̇        = refl
shape ⊥̇        = refl
shape (∃̇ a)    = refl
shape (∀̇ a)    = refl
shape (∀̇∈ t a) = refl
shape (∃̇∈ t a) = refl
```

<!--en-->
What remains is the case analysis, and it is indexed by two things that the tag
already relates. `Match` states what having a given tag looks like: a witness that
the formula is built by that constructor, with the parts named. `matches` produces
the witness for the formula's own tag, twelve clauses each. Then the equation's
tag halves are compared by `pair-inj`, the witness moves the second formula to the
first constructor, and `peel` opens the payloads, recursing on the parts. The grid of
twelve by twelve is never written.
<!--zh-->
剩下的是情形分析，而它由两个东西索引，且那个标签已经把它们关联起来。`Match` 陈述「带某个标签」长什么样：一条见证，说明该公式由那个构造子建成、各部分有名可指。`matches` 为公式自己的标签造出见证，两边各十二条子句。随后用 `pair-inj` 比较等式的两半标签，见证把第二条公式搬到第一个构造子上，`go` 再逐层剥开载荷，对部分递归。十二乘十二的网格从未写下来。
<!--/-->

```agda
Match : ∀ {k} → ℕ → Formula (⊥* {ℓ}) k → Type ℓ
Match {k} 0  φ = Σ[ t ∈ Term (⊥* {ℓ}) k ] (Σ[ u ∈ Term (⊥* {ℓ}) k ] (φ ≡ (t ∈̇ u)))
Match {k} 1  φ = Σ[ t ∈ Term (⊥* {ℓ}) k ] (Σ[ u ∈ Term (⊥* {ℓ}) k ] (φ ≡ (t ≐ u)))
Match {k} 2  φ = Σ[ a ∈ Formula (⊥* {ℓ}) k ] (Σ[ b ∈ Formula (⊥* {ℓ}) k ] (φ ≡ (a ∧̇ b)))
Match {k} 3  φ = Σ[ a ∈ Formula (⊥* {ℓ}) k ] (Σ[ b ∈ Formula (⊥* {ℓ}) k ] (φ ≡ (a ∨̇ b)))
Match {k} 4  φ = Σ[ a ∈ Formula (⊥* {ℓ}) k ] (Σ[ b ∈ Formula (⊥* {ℓ}) k ] (φ ≡ (a ⇒̇ b)))
Match {k} 5  φ = Σ[ a ∈ Formula (⊥* {ℓ}) k ] (φ ≡ (¬̇ a))
Match     6  φ = φ ≡ ⊤̇
Match     7  φ = φ ≡ ⊥̇
Match {k} 8  φ = Σ[ a ∈ Formula (⊥* {ℓ}) (suc k) ] (φ ≡ (∃̇ a))
Match {k} 9  φ = Σ[ a ∈ Formula (⊥* {ℓ}) (suc k) ] (φ ≡ (∀̇ a))
Match {k} 10 φ = Σ[ t ∈ Term (⊥* {ℓ}) k ] (Σ[ a ∈ Formula (⊥* {ℓ}) (suc k) ] (φ ≡ ∀̇∈ t a))
Match {k} 11 φ = Σ[ t ∈ Term (⊥* {ℓ}) k ] (Σ[ a ∈ Formula (⊥* {ℓ}) (suc k) ] (φ ≡ ∃̇∈ t a))
Match     _  _ = Empty.⊥*

matches : ∀ {k} (φ : Formula (⊥* {ℓ}) k) → Match (tagOf φ) φ
matches (t ∈̇ u)  = t , (u , refl)
matches (t ≐ u)  = t , (u , refl)
matches (a ∧̇ b)  = a , (b , refl)
matches (a ∨̇ b)  = a , (b , refl)
matches (a ⇒̇ b)  = a , (b , refl)
matches (¬̇ a)    = a , refl
matches ⊤̇        = refl
matches ⊥̇        = refl
matches (∃̇ a)    = a , refl
matches (∀̇ a)    = a , refl
matches (∀̇∈ t a) = t , (a , refl)
matches (∃̇∈ t a) = t , (a , refl)

code-inj : ∀ {k} (φ ψ : Formula (⊥* {ℓ}) k) → code φ ≡ code ψ → φ ≡ ψ

private
  peel : ∀ {k} (φ ψ : Formula (⊥* {ℓ}) k) → Match (tagOf φ) ψ → payOf φ ≡ payOf ψ → φ ≡ ψ
  peel (t ∈̇ u) ψ (t' , (u' , q)) p =
    cong₂ _∈̇_ (tcode-inj t t' (pair-inj (tcode t) (tcode u) (tcode t') (tcode u') (p ∙ cong payOf q) .fst))
              (tcode-inj u u' (pair-inj (tcode t) (tcode u) (tcode t') (tcode u') (p ∙ cong payOf q) .snd)) ∙ sym q
  peel (t ≐ u) ψ (t' , (u' , q)) p =
    cong₂ _≐_ (tcode-inj t t' (pair-inj (tcode t) (tcode u) (tcode t') (tcode u') (p ∙ cong payOf q) .fst))
              (tcode-inj u u' (pair-inj (tcode t) (tcode u) (tcode t') (tcode u') (p ∙ cong payOf q) .snd)) ∙ sym q
  peel (a ∧̇ b) ψ (a' , (b' , q)) p =
    cong₂ _∧̇_ (code-inj a a' (pair-inj (code a) (code b) (code a') (code b') (p ∙ cong payOf q) .fst))
              (code-inj b b' (pair-inj (code a) (code b) (code a') (code b') (p ∙ cong payOf q) .snd)) ∙ sym q
  peel (a ∨̇ b) ψ (a' , (b' , q)) p =
    cong₂ _∨̇_ (code-inj a a' (pair-inj (code a) (code b) (code a') (code b') (p ∙ cong payOf q) .fst))
              (code-inj b b' (pair-inj (code a) (code b) (code a') (code b') (p ∙ cong payOf q) .snd)) ∙ sym q
  peel (a ⇒̇ b) ψ (a' , (b' , q)) p =
    cong₂ _⇒̇_ (code-inj a a' (pair-inj (code a) (code b) (code a') (code b') (p ∙ cong payOf q) .fst))
              (code-inj b b' (pair-inj (code a) (code b) (code a') (code b') (p ∙ cong payOf q) .snd)) ∙ sym q
  peel (¬̇ a) ψ (a' , q) p = cong ¬̇_ (code-inj a a' (p ∙ cong payOf q)) ∙ sym q
  peel ⊤̇ ψ q p = sym q
  peel ⊥̇ ψ q p = sym q
  peel (∃̇ a) ψ (a' , q) p = cong ∃̇_ (code-inj a a' (p ∙ cong payOf q)) ∙ sym q
  peel (∀̇ a) ψ (a' , q) p = cong ∀̇_ (code-inj a a' (p ∙ cong payOf q)) ∙ sym q
  peel (∀̇∈ t a) ψ (t' , (a' , q)) p =
    cong₂ ∀̇∈ (tcode-inj t t' (pair-inj (tcode t) (code a) (tcode t') (code a') (p ∙ cong payOf q) .fst))
             (code-inj a a' (pair-inj (tcode t) (code a) (tcode t') (code a') (p ∙ cong payOf q) .snd)) ∙ sym q
  peel (∃̇∈ t a) ψ (t' , (a' , q)) p =
    cong₂ ∃̇∈ (tcode-inj t t' (pair-inj (tcode t) (code a) (tcode t') (code a') (p ∙ cong payOf q) .fst))
             (code-inj a a' (pair-inj (tcode t) (code a) (tcode t') (code a') (p ∙ cong payOf q) .snd)) ∙ sym q

code-inj φ ψ e = peel φ ψ
  (subst (λ k → Match k ψ) (sym (tp .fst)) (matches ψ)) (tp .snd)
  where
  tp = pair-inj (tagOf φ) (payOf φ) (tagOf ψ) (payOf ψ) (sym (shape φ) ∙ e ∙ shape ψ)
```

<!--en-->
The packaged target states exactly what the composition in Part 4 will consume: for
each arity `k`, an injection of the parameter-free formulas of that arity into the
natural numbers, with injectivity proved. The arity is carried by the statement
itself, and the consumer carries it separately, so no code on the whole disjoint
union is needed.
<!--zh-->
打包后的目标陈述的正是第四部那场复合将要消费的东西：对每个元数 `k`，该元数无参公式到自然数的一个单射，单射性已证。元数由陈述自己携带，消费方另携一份，故无须在整个无交并上编码。
<!--/-->

```agda
shape-count-inj : Σ[ f ∈ ((k : ℕ) → Formula (⊥* {ℓ}) k → ℕ) ]
                    (∀ {k} {φ ψ : Formula (⊥* {ℓ}) k} → f k φ ≡ f k ψ → φ ≡ ψ)
shape-count-inj = (λ k φ → code φ) , (λ {k} {φ} {ψ} p → code-inj φ ψ p)
```

<!--en-->
## The count
<!--zh-->
## 计数
<!--/-->

<!--en-->
The main half. Fix the constant domain `K` and look at the formulas with one free
variable. The target: these formulas inject into the disjoint union over `k` of the
parameter-free formulas of arity `k` paired with `k`-tuples of constants. The
injection is an encoding with a decode and a reconstruction: `encode` maps a formula
to a shape and a tuple, `decode-total` maps any shape-plus-tuple back to a formula,
and `encode-decode` says the round trip returns where it started, which yields
`encode-inj` and the packaged `count-inj`. The reading is the point. A formula is a
tree; the encoding keeps every variable as itself, a de Bruijn index, and turns each
constant occurrence into a designated **marker variable** inside the shape. The shape
is parameter-free, as it must be, and it remembers, by the marker's position, where
each constant occurrence sat. The tuple lists the constants in traversal order, left
to right, and the decode walks the shape, keeping variables below the marker and
turning the marker into the next constant from the list. The marker slot is shared by
every constant occurrence, so the tuple carries one padding copy of the first
constant at its end. The count of occurrences, not their value, decides the tuple's
length, and the parameters chapter's `countFo`{.Agda} and `constantsFo`{.Agda}
already count and collect by occurrence, so this chapter reuses them rather than
rewriting them.
<!--zh-->
主半场。固定常量域 `K`，看带一个自由变量的公式。目标：这些公式单射地落入「对 `k` 的 `k` 元无参公式配上 `k` 个常量的元组」之无交并。这条单射是一个带解码与还原的编码：`encode` 把公式映射成形状加元组，`decode-total` 把任何形状加元组映回公式，`encode-decode` 说往返回到原处，由此得到 `encode-inj` 与打包的 `count-inj`。读法是要点。公式是一棵树；编码把每个变量原样保留为 de Bruijn 索引，把每次常量出现变成形状里一个指定的**标记变量**。形状如其所必须是无参的，它靠标记的位置记住每次常量出现坐落在哪。元组按遍历次序自左而右列出常量，末尾再装一份首常量副本。决定元组长度的是出现次数而非取值，而参数章的 `countFo`{.Agda} 与 `constantsFo`{.Agda} 已经逐次出现地计数与收集，本章复用之，不重写。
<!--/-->

```agda
module Count (K : Type ℓ) where

  -- The encoding is generic in five numbers: s the shape's constant bound, m the
  -- marker slot, n the arity, and e, e' the binders' contribution (only e' grows,
  -- under a quantifier; e is carried for the symmetry of the index arithmetic).
  +-mono : (x y z : ℕ) → y < z → x + y < x + z
  +-mono x y z p = subst (λ w → w ≤ x + z) (+-suc x y) (≤-k+ {k = x} p)

  n<s→n≤s : {n s : ℕ} → n < s → n ≤ s
  n<s→n≤s {n} {s} p = ≤-trans (≤-sucℕ {n}) p

  +-suc-l : (e' e s : ℕ) → (suc e') + e + s ≡ suc (e' + e + s)
  +-suc-l e' e s = refl

  fit-suc : {n e' e s : ℕ} → n ≤ e' + e + s → suc n ≤ (suc e') + e + s
  fit-suc {n} {e'} {e} {s} p =
    subst (λ w → suc n ≤ w) (sym (+-suc-l e' e s)) (suc-≤-suc p)

  fit-suc2 : {n e e' m : ℕ} → n ≤ (e + e') + m → suc n ≤ (e + (suc e')) + m
  fit-suc2 {n} {e} {e'} {m} p =
    subst (λ w → suc n ≤ w) (sym (cong (λ x → x + m) (+-suc e e'))) (suc-≤-suc p)

  -- The marker's index, (e + e') + m, sits strictly below the shape's arity.
  marker-bound : (e e' s : ℕ) → (e + e') + s ≡ e' + e + s
  marker-bound e e' s = cong (λ w → w + s) (+-comm e e')

  marker-lt : (e e' m s : ℕ) → m < s → (e + e') + m < e' + e + s
  marker-lt e e' m s m<s =
    subst (λ w → (e + e') + m < w) (marker-bound e e' s) (+-mono (e + e') m s m<s)
```

<!--en-->
The vector-and-list plumbing that carries the constants. `constantsTm` and
`constantsFo` deliver the occurrences as vectors (imported from the parameters
chapter; the library's vector append `_++ᵥ_` stands in for a hand-written copy),
`head` and `snoc` supply the padding copy, `vecToList` flattens a vector for the
decode's list, and the three lemmas say the flattening respects append, snoc and
transport.
<!--zh-->
搬运常量的向量与表机件。`constantsTm` 与 `constantsFo` 把出现以向量交付 (自参数章导入；库的向量拼接 `_++ᵥ_` 顶替手写的一份)，`head` 与 `snoc` 供给垫付的副本，`vecToList` 把向量摊平成解码所用的表，三条引理说摊平尊重拼接、snoc 与搬运。
<!--/-->

```agda
  head : {n : ℕ} → Vec K (suc n) → K
  head (a ∷ _) = a

  snoc : {n : ℕ} → Vec K n → K → Vec K (suc n)
  snoc [] a = a ∷ []
  snoc (x ∷ xs) a = x ∷ snoc xs a

  vecToList : {n : ℕ} → Vec K n → List K
  vecToList [] = []
  vecToList (x ∷ xs) = x ∷ vecToList xs

  vecToList-++ : {a b : ℕ} (xs : Vec K a) (ys : Vec K b)
               → vecToList (xs ++ᵥ ys) ≡ vecToList xs ++ vecToList ys
  vecToList-++ [] ys = refl
  vecToList-++ (x ∷ xs) ys = cong (x ∷_) (vecToList-++ xs ys)

  vecToList-snoc : {n : ℕ} (xs : Vec K n) (a : K)
                 → vecToList (snoc xs a) ≡ vecToList xs ++ (a ∷ [])
  vecToList-snoc [] a = refl
  vecToList-snoc (x ∷ xs) a = cong (x ∷_) (vecToList-snoc xs a)

  vecToList-subst : {n m : ℕ} (q : n ≡ m) (xs : Vec K n)
                  → vecToList (subst (Vec K) q xs) ≡ vecToList xs
  vecToList-subst {n} {m} q xs =
    J (λ m q → vecToList (subst (Vec K) q xs) ≡ vecToList xs)
      (cong vecToList (transportRefl xs)) q

  ++-assoc : (xs ys zs : List K) → (xs ++ ys) ++ zs ≡ xs ++ (ys ++ zs)
  ++-assoc [] ys zs = refl
  ++-assoc (x ∷ xs) ys zs = cong (x ∷_) (++-assoc xs ys zs)
```

<!--en-->
The encoding itself, terms and formulas. A constant becomes the marker variable at
index `(e + e') + m`; a variable keeps its index, carried into the larger shape by
the bound. The formula clauses mirror the syntax: each binary constructor encodes
its two parts, each unary one its one part, and the quantifiers and bounded
quantifiers descend one binder, re-establishing the bound with `fit-suc`. Nothing
else changes: the shape is the formula with constants replaced by marker variables.
<!--zh-->
编码本身，词项与公式。常量变成标记槽 `(e + e') + m` 处的标记变量；变量保留自己的索引，由界带入更大的形状。公式子句镜像语法：每个二元构造子编码两部分，每个一元构造子编码一部分，量词与有界量词深入一个约束子，用 `fit-suc` 重立界。其余一切不动：形状就是把常量换成标记变量的公式。
<!--/-->

```agda
  encTm : (s m n e e' : ℕ) → m < s → n ≤ e' + e + s → Term K n → Term (⊥* {ℓ}) (e' + e + s)
  encTm s m n e e' m<s n≤s' (con _) =
    var (fromℕ' (e' + e + s) ((e + e') + m) (marker-lt e e' m s m<s))
  encTm s m n e e' m<s n≤s' (var i) =
    var (fromℕ' (e' + e + s) (toℕ i) (≤-trans (toℕ<n i) n≤s'))

  enc : (s m n e e' : ℕ) → m < s → n ≤ e' + e + s → Formula K n → Formula (⊥* {ℓ}) (e' + e + s)
  enc s m n e e' m<s n≤s' (t ∈̇ u)  = encTm s m n e e' m<s n≤s' t ∈̇ encTm s m n e e' m<s n≤s' u
  enc s m n e e' m<s n≤s' (t ≐ u)  = encTm s m n e e' m<s n≤s' t ≐ encTm s m n e e' m<s n≤s' u
  enc s m n e e' m<s n≤s' (φ ∧̇ ψ)  = enc s m n e e' m<s n≤s' φ ∧̇ enc s m n e e' m<s n≤s' ψ
  enc s m n e e' m<s n≤s' (φ ∨̇ ψ)  = enc s m n e e' m<s n≤s' φ ∨̇ enc s m n e e' m<s n≤s' ψ
  enc s m n e e' m<s n≤s' (φ ⇒̇ ψ)  = enc s m n e e' m<s n≤s' φ ⇒̇ enc s m n e e' m<s n≤s' ψ
  enc s m n e e' m<s n≤s' (¬̇ φ)    = ¬̇ enc s m n e e' m<s n≤s' φ
  enc s m n e e' m<s n≤s' ⊤̇        = ⊤̇
  enc s m n e e' m<s n≤s' ⊥̇        = ⊥̇
  enc s m n e e' m<s n≤s' (∃̇ φ) =
    let body = enc s m (suc n) e (suc e') m<s (fit-suc {n = n} {e' = e'} {e = e} {s = s} n≤s') φ
    in ∃̇ body
  enc s m n e e' m<s n≤s' (∀̇ φ) =
    let body = enc s m (suc n) e (suc e') m<s (fit-suc {n = n} {e' = e'} {e = e} {s = s} n≤s') φ
    in ∀̇ body
  enc s m n e e' m<s n≤s' (∀̇∈ t φ) =
    ∀̇∈ (encTm s m n e e' m<s n≤s' t) (enc s m (suc n) e (suc e') m<s (fit-suc {n = n} {e' = e'} {e = e} {s = s} n≤s') φ)
  enc s m n e e' m<s n≤s' (∃̇∈ t φ) =
    ∃̇∈ (encTm s m n e e' m<s n≤s' t) (enc s m (suc n) e (suc e') m<s (fit-suc {n = n} {e' = e'} {e = e} {s = s} n≤s') φ)
```

<!--en-->
The decode walks the shape with the constant list in hand, and every step is the
inverse of the corresponding encoding step. A variable whose index is the marker's
becomes a constant, consuming the head of the list; a variable below the marker is
kept, provided it is below the arity. The two remaining cases are unreachable for
shapes the encoding produces, and the decode returns a dummy variable there, so that
the function is total. Under a binder the decode descends with the bound and the
marker inequality re-established, mirroring the encoding.
<!--zh-->
解码手持常量清单沿形状行走，每一步都是对应编码步骤之逆。索引恰为标记的变量变成常量，消耗清单头部；标记以下的变量被保留，只要它在元数之下。其余两情形对编码产出的形状不可达，解码在那里返回一个哑变量，使函数保持全函数。在量词之下，解码带着重立的界与标记不等式深入，与编码镜像相对。
<!--/-->

```agda
  decodeTm : (s m n e e' : ℕ) → m < s → m ≤ n → 1 ≤ n → Term (⊥* {ℓ}) (e' + e + s) → List K
           → Term K n × List K
  decodeTm s m n e e' m<s m≤n n≥1 (var i) cs with toℕ i ≟ ((e + e') + m)
  decodeTm s m n e e' m<s m≤n n≥1 (var i) [] | eq _ = var (fromℕ' n 0 n≥1) , []
  decodeTm s m n e e' m<s m≤n n≥1 (var i) (a ∷ cs) | eq _ = con a , cs
  decodeTm s m n e e' m<s m≤n n≥1 (var i) cs | lt _ with toℕ i ≟ n
  decodeTm s m n e e' m<s m≤n n≥1 (var i) cs | lt _ | lt q =
    var (fromℕ' n (toℕ i) q) , cs
  decodeTm s m n e e' m<s m≤n n≥1 (var i) cs | lt _ | _ = var (fromℕ' n 0 n≥1) , cs
  decodeTm s m n e e' m<s m≤n n≥1 (var i) cs | gt _ = var (fromℕ' n 0 n≥1) , cs
  decodeTm s m n e e' m<s m≤n n≥1 (con x) cs = Empty.rec* {A = Term K n × List K} x

  decode : (s m n e e' : ℕ) → m < s → m ≤ n → 1 ≤ n → Formula (⊥* {ℓ}) (e' + e + s) → List K
         → Formula K n × List K
  decode s m n e e' m<s m≤n n≥1 (t ∈̇ u) cs =
    let (t' , cs₁) = decodeTm s m n e e' m<s m≤n n≥1 t cs
        (u' , cs₂) = decodeTm s m n e e' m<s m≤n n≥1 u cs₁
    in t' ∈̇ u' , cs₂
  decode s m n e e' m<s m≤n n≥1 (t ≐ u) cs =
    let (t' , cs₁) = decodeTm s m n e e' m<s m≤n n≥1 t cs
        (u' , cs₂) = decodeTm s m n e e' m<s m≤n n≥1 u cs₁
    in t' ≐ u' , cs₂
  decode s m n e e' m<s m≤n n≥1 (φ ∧̇ ψ) cs =
    let (φ' , cs₁) = decode s m n e e' m<s m≤n n≥1 φ cs
        (ψ' , cs₂) = decode s m n e e' m<s m≤n n≥1 ψ cs₁
    in φ' ∧̇ ψ' , cs₂
  decode s m n e e' m<s m≤n n≥1 (φ ∨̇ ψ) cs =
    let (φ' , cs₁) = decode s m n e e' m<s m≤n n≥1 φ cs
        (ψ' , cs₂) = decode s m n e e' m<s m≤n n≥1 ψ cs₁
    in φ' ∨̇ ψ' , cs₂
  decode s m n e e' m<s m≤n n≥1 (φ ⇒̇ ψ) cs =
    let (φ' , cs₁) = decode s m n e e' m<s m≤n n≥1 φ cs
        (ψ' , cs₂) = decode s m n e e' m<s m≤n n≥1 ψ cs₁
    in φ' ⇒̇ ψ' , cs₂
  decode s m n e e' m<s m≤n n≥1 (¬̇ φ) cs =
    let (φ' , cs₁) = decode s m n e e' m<s m≤n n≥1 φ cs
    in ¬̇ φ' , cs₁
  decode s m n e e' m<s m≤n n≥1 ⊤̇ cs = ⊤̇ , cs
  decode s m n e e' m<s m≤n n≥1 ⊥̇ cs = ⊥̇ , cs
  decode s m n e e' m<s m≤n n≥1 (∃̇ φ) cs =
    let (φ' , cs₁) = decode s m (suc n) e (suc e') m<s (≤-trans m≤n (≤-sucℕ {n}))
                      (suc-≤-suc zero-≤) φ cs
    in ∃̇ φ' , cs₁
  decode s m n e e' m<s m≤n n≥1 (∀̇ φ) cs =
    let (φ' , cs₁) = decode s m (suc n) e (suc e') m<s (≤-trans m≤n (≤-sucℕ {n}))
                      (suc-≤-suc zero-≤) φ cs
    in ∀̇ φ' , cs₁
  decode s m n e e' m<s m≤n n≥1 (∀̇∈ t φ) cs =
    let (t' , cs₁) = decodeTm s m n e e' m<s m≤n n≥1 t cs
        (φ' , cs₂) = decode s m (suc n) e (suc e') m<s (≤-trans m≤n (≤-sucℕ {n}))
                      (suc-≤-suc zero-≤) φ cs₁
    in ∀̇∈ t' φ' , cs₂
  decode s m n e e' m<s m≤n n≥1 (∃̇∈ t φ) cs =
    let (t' , cs₁) = decodeTm s m n e e' m<s m≤n n≥1 t cs
        (φ' , cs₂) = decode s m (suc n) e (suc e') m<s (≤-trans m≤n (≤-sucℕ {n}))
                      (suc-≤-suc zero-≤) φ cs₁
    in ∃̇∈ t' φ' , cs₂
```

<!--en-->
Two lemmas pin down what the decode does on the two kinds of variable it can meet,
and both are needed by the reconstruction. `decodeTm-marker` says the marker variable
decodes to the head constant, whatever list follows; `decodeTm-kept` says a variable
below the marker decodes to itself, whatever list follows. In the unreachable cases
the two lemmas refute the trichotomy with `¬m<m`.
<!--zh-->
两条引理钉死解码在它可能遇见的两种变量上的行为，二者都是还原所需。`decodeTm-marker` 说标记变量解码为首常量，与后续清单无关；`decodeTm-kept` 说标记以下的变量解码为其自身，与后续清单无关。不可达情形里，两条引理用 `¬m<m` 反驳三分律。
<!--/-->

```agda
  decodeTm-marker : (s m n e e' : ℕ) → (m<s : m < s) → (m≤n : m ≤ n) → (n≥1 : 1 ≤ n)
                 → (i : Fin (e' + e + s)) → toℕ i ≡ (e + e') + m
                 → (a : K) (l : List K)
                 → decodeTm s m n e e' m<s m≤n n≥1 (var i) (a ∷ l) ≡ (con a , l)
  decodeTm-marker s m n e e' m<s m≤n n≥1 i q a l with toℕ i ≟ ((e + e') + m)
  decodeTm-marker s m n e e' m<s m≤n n≥1 i q a l | eq _ = refl
  decodeTm-marker s m n e e' m<s m≤n n≥1 i q a l | lt r =
    Empty.rec (¬m<m {toℕ i} (subst (λ w → suc (toℕ i) ≤ w) (sym q) r))
  decodeTm-marker s m n e e' m<s m≤n n≥1 i q a l | gt r =
    Empty.rec (¬m<m {toℕ i} (subst (λ w → suc w ≤ toℕ i) (sym q) r))

  decodeTm-kept : (s m n e e' : ℕ) → (m<s : m < s) → (m≤n : m ≤ n) → (n≥1 : 1 ≤ n)
               → (i : Fin (e' + e + s)) → (q1 : toℕ i < (e + e') + m) → (q2 : toℕ i < n)
               → (l : List K)
               → decodeTm s m n e e' m<s m≤n n≥1 (var i) l
                 ≡ (var (fromℕ' n (toℕ i) q2) , l)
  decodeTm-kept s m n e e' m<s m≤n n≥1 i q1 q2 l with toℕ i ≟ ((e + e') + m)
  decodeTm-kept s m n e e' m<s m≤n n≥1 i q1 q2 l | lt _ with toℕ i ≟ n
  decodeTm-kept s m n e e' m<s m≤n n≥1 i q1 q2 l | lt _ | lt r =
    cong₂ _,_
      (cong (λ q → var {K = K} (fromℕ' n (toℕ i) q)) (isProp≤ r q2)) refl
  decodeTm-kept s m n e e' m<s m≤n n≥1 i q1 q2 l | lt _ | eq r =
    Empty.rec (¬m<m {toℕ i} (subst (λ w → suc (toℕ i) ≤ w) (sym r) q2))
  decodeTm-kept s m n e e' m<s m≤n n≥1 i q1 q2 l | lt _ | gt r =
    Empty.rec (¬m<m {toℕ i} (≤-trans (≤-trans q2 (≤-sucℕ {n})) r))
  decodeTm-kept s m n e e' m<s m≤n n≥1 i q1 q2 l | eq r =
    Empty.rec (¬m<m {toℕ i} (subst (λ w → suc (toℕ i) ≤ w) (sym r) q1))
  decodeTm-kept s m n e e' m<s m≤n n≥1 i q1 q2 l | gt r =
    Empty.rec (¬m<m {toℕ i}
      (≤-trans (≤-trans q1 (≤-sucℕ {(e + e') + m})) r))
```

<!--en-->
The reconstruction, by induction on the formula, proves the round trip at the level
of the parts: `decodeTm-inv` says that decoding the encoding of a term with the
term's own constants in hand returns the term, and `decode-inv` says the same for
formulas. The binary clauses split the list with the associativity lemma; the binder
clauses pass the arithmetic lemmas and recurse. This is the largest block in the
chapter: every clause is a congruence over the corresponding decode clause.
<!--zh-->
还原对公式归纳，在部分的层面证明往返：`decodeTm-inv` 说手头握着词项自己的常量时，解码词项编码的产物还原该词项；`decode-inv` 对公式说同样的话。二元子句用结合律引理分清单；量词子句递过算术引理再递归。这是全章最大的一块证明：每条子句都是对应解码子句上的一则同余。
<!--/-->

```agda
  decodeTm-inv : (s m n e e' : ℕ) → (m<s : m < s) → (n≤s' : n ≤ e' + e + s)
              → (m≤n : m ≤ n) → (n≤m : n ≤ (e + e') + m) → (n≥1 : 1 ≤ n)
              → (t : Term K n) (l : List K)
              → decodeTm s m n e e' m<s m≤n n≥1 (encTm s m n e e' m<s n≤s' t)
                  (vecToList (constantsTm t) ++ l) ≡ (t , l)
  decodeTm-inv s m n e e' m<s n≤s' m≤n n≤m n≥1 (con a) l =
    let idx = fromℕ' (e' + e + s) ((e + e') + m) (marker-lt e e' m s m<s)
    in decodeTm-marker s m n e e' m<s m≤n n≥1 idx
         (toFromId' (e' + e + s) ((e + e') + m) (marker-lt e e' m s m<s)) a l
  decodeTm-inv s m n e e' m<s n≤s' m≤n n≤m n≥1 (var i) l =
    let p = ≤-trans (toℕ<n i) n≤s'
        idx = fromℕ' (e' + e + s) (toℕ i) p
        t = toFromId' (e' + e + s) (toℕ i) p
        q1 = subst (λ w → w < (e + e') + m) (sym t)
               (≤-trans (toℕ<n i) n≤m)
        q2 = subst (λ w → w < n) (sym t) (toℕ<n i)
    in decodeTm-kept s m n e e' m<s m≤n n≥1 idx q1 q2 l
       ∙ cong (λ w → var w , l)
           (inj-toℕ (toFromId' n (toℕ idx) q2 ∙ t))

  decode-inv : (s m n e e' : ℕ) → (m<s : m < s) → (n≤s' : n ≤ e' + e + s)
             → (m≤n : m ≤ n) → (n≤m : n ≤ (e + e') + m) → (n≥1 : 1 ≤ n)
             → (φ : Formula K n) (l : List K)
             → decode s m n e e' m<s m≤n n≥1 (enc s m n e e' m<s n≤s' φ)
                 (vecToList (constantsFo φ) ++ l) ≡ (φ , l)
  decode-inv s m n e e' m<s n≤s' m≤n n≤m n≥1 (t ∈̇ u) l =
    cong (λ w → decode s m n e e' m<s m≤n n≥1 (encTm s m n e e' m<s n≤s' t ∈̇ encTm s m n e e' m<s n≤s' u) (w ++ l))
         (vecToList-++ (constantsTm t) (constantsTm u))
    ∙ cong (λ w → decode s m n e e' m<s m≤n n≥1 (encTm s m n e e' m<s n≤s' t ∈̇ encTm s m n e e' m<s n≤s' u) w)
         (++-assoc (vecToList (constantsTm t)) (vecToList (constantsTm u)) l)
    ∙ go
    where
    go : decode s m n e e' m<s m≤n n≥1
           (encTm s m n e e' m<s n≤s' t ∈̇ encTm s m n e e' m<s n≤s' u)
           (vecToList (constantsTm t) ++ (vecToList (constantsTm u) ++ l))
         ≡ (t ∈̇ u , l)
    go = let p = decodeTm-inv s m n e e' m<s n≤s' m≤n n≤m n≥1 t (vecToList (constantsTm u) ++ l)
             q = decodeTm-inv s m n e e' m<s n≤s' m≤n n≤m n≥1 u l
         in cong₂ _,_
              (cong₂ _∈̇_ (cong fst p)
                (cong fst (cong (decodeTm s m n e e' m<s m≤n n≥1 (encTm s m n e e' m<s n≤s' u)) (cong snd p) ∙ q)))
              (cong snd (cong (decodeTm s m n e e' m<s m≤n n≥1 (encTm s m n e e' m<s n≤s' u)) (cong snd p) ∙ q))
  decode-inv s m n e e' m<s n≤s' m≤n n≤m n≥1 (t ≐ u) l =
    cong (λ w → decode s m n e e' m<s m≤n n≥1 (encTm s m n e e' m<s n≤s' t ≐ encTm s m n e e' m<s n≤s' u) (w ++ l))
         (vecToList-++ (constantsTm t) (constantsTm u))
    ∙ cong (λ w → decode s m n e e' m<s m≤n n≥1 (encTm s m n e e' m<s n≤s' t ≐ encTm s m n e e' m<s n≤s' u) w)
         (++-assoc (vecToList (constantsTm t)) (vecToList (constantsTm u)) l)
    ∙ go
    where
    go : decode s m n e e' m<s m≤n n≥1
           (encTm s m n e e' m<s n≤s' t ≐ encTm s m n e e' m<s n≤s' u)
           (vecToList (constantsTm t) ++ (vecToList (constantsTm u) ++ l))
         ≡ (t ≐ u , l)
    go = let p = decodeTm-inv s m n e e' m<s n≤s' m≤n n≤m n≥1 t (vecToList (constantsTm u) ++ l)
             q = decodeTm-inv s m n e e' m<s n≤s' m≤n n≤m n≥1 u l
         in cong₂ _,_
              (cong₂ _≐_ (cong fst p)
                (cong fst (cong (decodeTm s m n e e' m<s m≤n n≥1 (encTm s m n e e' m<s n≤s' u)) (cong snd p) ∙ q)))
              (cong snd (cong (decodeTm s m n e e' m<s m≤n n≥1 (encTm s m n e e' m<s n≤s' u)) (cong snd p) ∙ q))
  decode-inv s m n e e' m<s n≤s' m≤n n≤m n≥1 (φ ∧̇ ψ) l =
    cong (λ w → decode s m n e e' m<s m≤n n≥1 (enc s m n e e' m<s n≤s' φ ∧̇ enc s m n e e' m<s n≤s' ψ) (w ++ l))
         (vecToList-++ (constantsFo φ) (constantsFo ψ))
    ∙ cong (λ w → decode s m n e e' m<s m≤n n≥1 (enc s m n e e' m<s n≤s' φ ∧̇ enc s m n e e' m<s n≤s' ψ) w)
         (++-assoc (vecToList (constantsFo φ)) (vecToList (constantsFo ψ)) l)
    ∙ go
    where
    go : decode s m n e e' m<s m≤n n≥1
           (enc s m n e e' m<s n≤s' φ ∧̇ enc s m n e e' m<s n≤s' ψ)
           (vecToList (constantsFo φ) ++ (vecToList (constantsFo ψ) ++ l))
         ≡ (φ ∧̇ ψ , l)
    go = let p = decode-inv s m n e e' m<s n≤s' m≤n n≤m n≥1 φ (vecToList (constantsFo ψ) ++ l)
             q = decode-inv s m n e e' m<s n≤s' m≤n n≤m n≥1 ψ l
         in cong₂ _,_
              (cong₂ _∧̇_ (cong fst p)
                (cong fst (cong (decode s m n e e' m<s m≤n n≥1 (enc s m n e e' m<s n≤s' ψ)) (cong snd p) ∙ q)))
              (cong snd (cong (decode s m n e e' m<s m≤n n≥1 (enc s m n e e' m<s n≤s' ψ)) (cong snd p) ∙ q))
  decode-inv s m n e e' m<s n≤s' m≤n n≤m n≥1 (φ ∨̇ ψ) l =
    cong (λ w → decode s m n e e' m<s m≤n n≥1 (enc s m n e e' m<s n≤s' φ ∨̇ enc s m n e e' m<s n≤s' ψ) (w ++ l))
         (vecToList-++ (constantsFo φ) (constantsFo ψ))
    ∙ cong (λ w → decode s m n e e' m<s m≤n n≥1 (enc s m n e e' m<s n≤s' φ ∨̇ enc s m n e e' m<s n≤s' ψ) w)
         (++-assoc (vecToList (constantsFo φ)) (vecToList (constantsFo ψ)) l)
    ∙ go
    where
    go : decode s m n e e' m<s m≤n n≥1
           (enc s m n e e' m<s n≤s' φ ∨̇ enc s m n e e' m<s n≤s' ψ)
           (vecToList (constantsFo φ) ++ (vecToList (constantsFo ψ) ++ l))
         ≡ (φ ∨̇ ψ , l)
    go = let p = decode-inv s m n e e' m<s n≤s' m≤n n≤m n≥1 φ (vecToList (constantsFo ψ) ++ l)
             q = decode-inv s m n e e' m<s n≤s' m≤n n≤m n≥1 ψ l
         in cong₂ _,_
              (cong₂ _∨̇_ (cong fst p)
                (cong fst (cong (decode s m n e e' m<s m≤n n≥1 (enc s m n e e' m<s n≤s' ψ)) (cong snd p) ∙ q)))
              (cong snd (cong (decode s m n e e' m<s m≤n n≥1 (enc s m n e e' m<s n≤s' ψ)) (cong snd p) ∙ q))
  decode-inv s m n e e' m<s n≤s' m≤n n≤m n≥1 (φ ⇒̇ ψ) l =
    cong (λ w → decode s m n e e' m<s m≤n n≥1 (enc s m n e e' m<s n≤s' φ ⇒̇ enc s m n e e' m<s n≤s' ψ) (w ++ l))
         (vecToList-++ (constantsFo φ) (constantsFo ψ))
    ∙ cong (λ w → decode s m n e e' m<s m≤n n≥1 (enc s m n e e' m<s n≤s' φ ⇒̇ enc s m n e e' m<s n≤s' ψ) w)
         (++-assoc (vecToList (constantsFo φ)) (vecToList (constantsFo ψ)) l)
    ∙ go
    where
    go : decode s m n e e' m<s m≤n n≥1
           (enc s m n e e' m<s n≤s' φ ⇒̇ enc s m n e e' m<s n≤s' ψ)
           (vecToList (constantsFo φ) ++ (vecToList (constantsFo ψ) ++ l))
         ≡ (φ ⇒̇ ψ , l)
    go = let p = decode-inv s m n e e' m<s n≤s' m≤n n≤m n≥1 φ (vecToList (constantsFo ψ) ++ l)
             q = decode-inv s m n e e' m<s n≤s' m≤n n≤m n≥1 ψ l
         in cong₂ _,_
              (cong₂ _⇒̇_ (cong fst p)
                (cong fst (cong (decode s m n e e' m<s m≤n n≥1 (enc s m n e e' m<s n≤s' ψ)) (cong snd p) ∙ q)))
              (cong snd (cong (decode s m n e e' m<s m≤n n≥1 (enc s m n e e' m<s n≤s' ψ)) (cong snd p) ∙ q))
  decode-inv s m n e e' m<s n≤s' m≤n n≤m n≥1 (¬̇ φ) l =
    go
    where
    go : decode s m n e e' m<s m≤n n≥1 (¬̇ enc s m n e e' m<s n≤s' φ)
           (vecToList (constantsFo φ) ++ l) ≡ (¬̇ φ , l)
    go = let p = decode-inv s m n e e' m<s n≤s' m≤n n≤m n≥1 φ l
         in cong₂ _,_ (cong ¬̇_ (cong fst p)) (cong snd p)
  decode-inv s m n e e' m<s n≤s' m≤n n≤m n≥1 ⊤̇ l = refl
  decode-inv s m n e e' m<s n≤s' m≤n n≤m n≥1 ⊥̇ l = refl
  decode-inv s m n e e' m<s n≤s' m≤n n≤m n≥1 (∃̇ φ) l =
    go
    where
    go : decode s m n e e' m<s m≤n n≥1 (∃̇ enc s m (suc n) e (suc e') m<s (fit-suc {n = n} {e' = e'} {e = e} {s = s} n≤s') φ)
           (vecToList (constantsFo φ) ++ l) ≡ (∃̇ φ , l)
    go = let p = decode-inv s m (suc n) e (suc e') m<s (fit-suc {n = n} {e' = e'} {e = e} {s = s} n≤s') (≤-trans m≤n (≤-sucℕ {n}))
                   (fit-suc2 {n = n} {e = e} {e' = e'} {m = m} n≤m) (suc-≤-suc zero-≤) φ l
         in cong₂ _,_ (cong ∃̇_ (cong fst p)) (cong snd p)
  decode-inv s m n e e' m<s n≤s' m≤n n≤m n≥1 (∀̇ φ) l =
    go
    where
    go : decode s m n e e' m<s m≤n n≥1 (∀̇ enc s m (suc n) e (suc e') m<s (fit-suc {n = n} {e' = e'} {e = e} {s = s} n≤s') φ)
           (vecToList (constantsFo φ) ++ l) ≡ (∀̇ φ , l)
    go = let p = decode-inv s m (suc n) e (suc e') m<s (fit-suc {n = n} {e' = e'} {e = e} {s = s} n≤s') (≤-trans m≤n (≤-sucℕ {n}))
                   (fit-suc2 {n = n} {e = e} {e' = e'} {m = m} n≤m) (suc-≤-suc zero-≤) φ l
         in cong₂ _,_ (cong ∀̇_ (cong fst p)) (cong snd p)
  decode-inv s m n e e' m<s n≤s' m≤n n≤m n≥1 (∀̇∈ t φ) l =
    cong (λ w → decode s m n e e' m<s m≤n n≥1 (∀̇∈ (encTm s m n e e' m<s n≤s' t) (enc s m (suc n) e (suc e') m<s (fit-suc {n = n} {e' = e'} {e = e} {s = s} n≤s') φ)) (w ++ l))
         (vecToList-++ (constantsTm t) (constantsFo φ))
    ∙ cong (λ w → decode s m n e e' m<s m≤n n≥1 (∀̇∈ (encTm s m n e e' m<s n≤s' t) (enc s m (suc n) e (suc e') m<s (fit-suc {n = n} {e' = e'} {e = e} {s = s} n≤s') φ)) w)
         (++-assoc (vecToList (constantsTm t)) (vecToList (constantsFo φ)) l)
    ∙ go
    where
    go : decode s m n e e' m<s m≤n n≥1
           (∀̇∈ (encTm s m n e e' m<s n≤s' t) (enc s m (suc n) e (suc e') m<s (fit-suc {n = n} {e' = e'} {e = e} {s = s} n≤s') φ))
           (vecToList (constantsTm t) ++ (vecToList (constantsFo φ) ++ l))
         ≡ (∀̇∈ t φ , l)
    go = let p = decodeTm-inv s m n e e' m<s n≤s' m≤n n≤m n≥1 t (vecToList (constantsFo φ) ++ l)
             q = decode-inv s m (suc n) e (suc e') m<s (fit-suc {n = n} {e' = e'} {e = e} {s = s} n≤s') (≤-trans m≤n (≤-sucℕ {n}))
                   (fit-suc2 {n = n} {e = e} {e' = e'} {m = m} n≤m) (suc-≤-suc zero-≤) φ l
         in cong₂ _,_
              (cong₂ ∀̇∈ (cong fst p)
                (cong fst (cong (decode s m (suc n) e (suc e') m<s (≤-trans m≤n (≤-sucℕ {n}))
                  (suc-≤-suc zero-≤) (enc s m (suc n) e (suc e') m<s (fit-suc {n = n} {e' = e'} {e = e} {s = s} n≤s') φ)) (cong snd p) ∙ q)))
              (cong snd (cong (decode s m (suc n) e (suc e') m<s (≤-trans m≤n (≤-sucℕ {n}))
                  (suc-≤-suc zero-≤) (enc s m (suc n) e (suc e') m<s (fit-suc {n = n} {e' = e'} {e = e} {s = s} n≤s') φ)) (cong snd p) ∙ q))
  decode-inv s m n e e' m<s n≤s' m≤n n≤m n≥1 (∃̇∈ t φ) l =
    cong (λ w → decode s m n e e' m<s m≤n n≥1 (∃̇∈ (encTm s m n e e' m<s n≤s' t) (enc s m (suc n) e (suc e') m<s (fit-suc {n = n} {e' = e'} {e = e} {s = s} n≤s') φ)) (w ++ l))
         (vecToList-++ (constantsTm t) (constantsFo φ))
    ∙ cong (λ w → decode s m n e e' m<s m≤n n≥1 (∃̇∈ (encTm s m n e e' m<s n≤s' t) (enc s m (suc n) e (suc e') m<s (fit-suc {n = n} {e' = e'} {e = e} {s = s} n≤s') φ)) w)
         (++-assoc (vecToList (constantsTm t)) (vecToList (constantsFo φ)) l)
    ∙ go
    where
    go : decode s m n e e' m<s m≤n n≥1
           (∃̇∈ (encTm s m n e e' m<s n≤s' t) (enc s m (suc n) e (suc e') m<s (fit-suc {n = n} {e' = e'} {e = e} {s = s} n≤s') φ))
           (vecToList (constantsTm t) ++ (vecToList (constantsFo φ) ++ l))
         ≡ (∃̇∈ t φ , l)
    go = let p = decodeTm-inv s m n e e' m<s n≤s' m≤n n≤m n≥1 t (vecToList (constantsFo φ) ++ l)
             q = decode-inv s m (suc n) e (suc e') m<s (fit-suc {n = n} {e' = e'} {e = e} {s = s} n≤s') (≤-trans m≤n (≤-sucℕ {n}))
                   (fit-suc2 {n = n} {e = e} {e' = e'} {m = m} n≤m) (suc-≤-suc zero-≤) φ l
         in cong₂ _,_
              (cong₂ ∃̇∈ (cong fst p)
                (cong fst (cong (decode s m (suc n) e (suc e') m<s (≤-trans m≤n (≤-sucℕ {n}))
                  (suc-≤-suc zero-≤) (enc s m (suc n) e (suc e') m<s (fit-suc {n = n} {e' = e'} {e = e} {s = s} n≤s') φ)) (cong snd p) ∙ q)))
              (cong snd (cong (decode s m (suc n) e (suc e') m<s (≤-trans m≤n (≤-sucℕ {n}))
                  (suc-≤-suc zero-≤) (enc s m (suc n) e (suc e') m<s (fit-suc {n = n} {e' = e'} {e = e} {s = s} n≤s') φ)) (cong snd p) ∙ q))
```

<!--en-->
The boundary case the exact shape forces. When the formula has no constants, there
is nothing to pad the tuple with, so the shape cannot keep the free variable open at
the marker; the encoding closes it instead. `erase` removes the constants, which is
to say it maps the formula into the parameter-free formulas (the constant cases are
uninhabited), and `erase-inv` says that re-entering any constant domain through
`mapFo Empty.rec*` recovers the formula. The two `plus-zero` lemmas split the zero
count across a binary constructor.
<!--zh-->
精确形状所迫的边界情形。当公式没有常量时，元组无从填充，形状便不能在标记处保持自由变量敞开；编码改为把它闭合。`erase` 去掉常量，也就是把公式映进无参公式 (常量情形无人居住)，`erase-inv` 说经 `mapFo Empty.rec*` 重进任意常量域即还原公式。两条 `plus-zero` 引理把零计数跨二元构造子分解。
<!--/-->

```agda
  plus-zero-l : {a b : ℕ} → a + b ≡ 0 → a ≡ 0
  plus-zero-l {zero} {b} p = refl
  plus-zero-l {suc a} {b} p = Empty.rec (snotz p)

  plus-zero-r : {a b : ℕ} → a + b ≡ 0 → b ≡ 0
  plus-zero-r {zero} {b} p = p
  plus-zero-r {suc a} {b} p = Empty.rec (snotz p)

  eraseTm : {n : ℕ} (t : Term K n) → countTm t ≡ 0 → Term (⊥* {ℓ}) n
  eraseTm (con a) p = Empty.rec {A = Term (⊥* {ℓ}) _} (snotz p)
  eraseTm (var i) _ = var i

  erase : {n : ℕ} (φ : Formula K n) → countFo φ ≡ 0 → Formula (⊥* {ℓ}) n
  erase (t ∈̇ u) p = eraseTm t (plus-zero-l p) ∈̇ eraseTm u (plus-zero-r p)
  erase (t ≐ u) p = eraseTm t (plus-zero-l p) ≐ eraseTm u (plus-zero-r p)
  erase (φ ∧̇ ψ) p = erase φ (plus-zero-l p) ∧̇ erase ψ (plus-zero-r p)
  erase (φ ∨̇ ψ) p = erase φ (plus-zero-l p) ∨̇ erase ψ (plus-zero-r p)
  erase (φ ⇒̇ ψ) p = erase φ (plus-zero-l p) ⇒̇ erase ψ (plus-zero-r p)
  erase (¬̇ φ) p = ¬̇ erase φ p
  erase ⊤̇ _ = ⊤̇
  erase ⊥̇ _ = ⊥̇
  erase (∃̇ φ) p = ∃̇ erase φ p
  erase (∀̇ φ) p = ∀̇ erase φ p
  erase (∀̇∈ t φ) p = ∀̇∈ (eraseTm t (plus-zero-l p)) (erase φ (plus-zero-r p))
  erase (∃̇∈ t φ) p = ∃̇∈ (eraseTm t (plus-zero-l p)) (erase φ (plus-zero-r p))

  eraseTm-inv : {n : ℕ} (t : Term K n) (p : countTm t ≡ 0)
              → mapTm Empty.rec* (eraseTm t p) ≡ t
  eraseTm-inv (con a) p = Empty.rec (snotz p)
  eraseTm-inv (var i) _ = refl

  erase-inv : {n : ℕ} (φ : Formula K n) (p : countFo φ ≡ 0)
            → mapFo Empty.rec* (erase φ p) ≡ φ
  erase-inv (t ∈̇ u) p =
    cong₂ _∈̇_ (eraseTm-inv t (plus-zero-l p)) (eraseTm-inv u (plus-zero-r p))
  erase-inv (t ≐ u) p =
    cong₂ _≐_ (eraseTm-inv t (plus-zero-l p)) (eraseTm-inv u (plus-zero-r p))
  erase-inv (φ ∧̇ ψ) p =
    cong₂ _∧̇_ (erase-inv φ (plus-zero-l p)) (erase-inv ψ (plus-zero-r p))
  erase-inv (φ ∨̇ ψ) p =
    cong₂ _∨̇_ (erase-inv φ (plus-zero-l p)) (erase-inv ψ (plus-zero-r p))
  erase-inv (φ ⇒̇ ψ) p =
    cong₂ _⇒̇_ (erase-inv φ (plus-zero-l p)) (erase-inv ψ (plus-zero-r p))
  erase-inv (¬̇ φ) p = cong ¬̇_ (erase-inv φ p)
  erase-inv ⊤̇ _ = refl
  erase-inv ⊥̇ _ = refl
  erase-inv (∃̇ φ) p = cong ∃̇_ (erase-inv φ p)
  erase-inv (∀̇ φ) p = cong ∀̇_ (erase-inv φ p)
  erase-inv (∀̇∈ t φ) p =
    cong₂ ∀̇∈ (eraseTm-inv t (plus-zero-l p)) (erase-inv φ (plus-zero-r p))
  erase-inv (∃̇∈ t φ) p =
    cong₂ ∃̇∈ (eraseTm-inv t (plus-zero-l p)) (erase-inv φ (plus-zero-r p))
```

<!--en-->
The packaged code and its total decode. `strip∃` reads a closed shape: if it is the
encoding's `∃̇`-closed shape, strip the quantifier and re-enter the domain; the
other closed shapes are not produced by the encoding, and the dummy `⊤̇` keeps the
function total. `codeByCount` splits on the count: zero constants close the shape,
a positive count opens it with the marker at slot 1 and pads the tuple with one copy
of the first constant; `code` starts the split at the formula's own count.
`decode-total` reads any shape-plus-tuple back, closing or opening according to the
length.
<!--zh-->
打包后的码及其全函数解码。`strip∃` 读闭合形状：若是编码产出的 `∃̇` 闭合形状，剥掉量词再重进常量域；其余闭合形状非编码所产，哑值 `⊤̇` 使函数保持全函数。`codeByCount` 按计数分叉：零常量把形状闭合，正计数在槽 1 处打开形状，并用首常量的一份副本把元组补齐；`code` 从公式自己的计数起分。`decode-total` 把任何形状加元组读回，按长度决定闭合或打开。
<!--/-->

```agda
  strip∃ : Formula (⊥* {ℓ}) 0 → Formula K 1
  strip∃ (∃̇ φ) = mapFo Empty.rec* φ
  strip∃ _ = ⊤̇

  one<s : (s : ℕ) → 1 < suc (suc s)
  one<s s = suc-≤-suc (suc-≤-suc (zero-≤ {s}))

  codeByCount : (φ : Formula K 1) (n : ℕ) → (p : countFo φ ≡ n) → Σ[ k ∈ ℕ ] (Formula (⊥* {ℓ}) k × Vec K k)
  codeByCount φ zero p = 0 , (∃̇ erase φ p , [])
  codeByCount φ (suc m) p = suc (suc m)
    , (enc (suc (suc m)) 1 1 0 0 (one<s m) (n<s→n≤s (one<s m)) φ
    , snoc (subst (Vec K) p (constantsFo φ)) (head (subst (Vec K) p (constantsFo φ))))

  encode : Formula K 1 → Σ[ k ∈ ℕ ] (Formula (⊥* {ℓ}) k × Vec K k)
  encode φ = codeByCount φ (countFo φ) refl

  decode-total : Σ[ k ∈ ℕ ] (Formula (⊥* {ℓ}) k × Vec K k) → Formula K 1
  decode-total (zero , (φ , _)) = strip∃ φ
  decode-total (suc zero , _) = ⊤̇
  decode-total (suc (suc k) , (φ , cs)) =
    decode (suc (suc k)) 1 1 0 0 (one<s k) (suc-≤-suc zero-≤) (suc-≤-suc zero-≤)
      φ (vecToList cs) .fst
```

<!--en-->
The reconstruction of the packaged code and its two consequences. `encode-decode` runs
the round trip on the packaged code: the zero case is `erase-inv`, the positive case
flattens the padded tuple and applies `decode-inv`. Injectivity follows: two
formulas with the same code decode to the same formula, hence are equal. The
packaged `count-inj` states the target in the exact shape the composition in Part 4
consumes, generic in the constant domain `K`.
<!--zh-->
打包码的还原及其两条推论。`encode-decode` 在打包码上跑往返：零情形即 `erase-inv`，正情形摊平补齐后的元组再施用 `decode-inv`。单射性随之而来：码相同的两条公式解码到同一条公式，故相等。打包的 `count-inj` 以第四部那场复合消费的精确形状陈述目标，对常量域 `K` 泛型。
<!--/-->

```agda
  encode-decode : (φ : Formula K 1) → decode-total (encode φ) ≡ φ
  encode-decode φ = go (countFo φ) (refl {x = countFo φ})
    where
    go : (n : ℕ) → (p : countFo φ ≡ n) → decode-total (codeByCount φ n p) ≡ φ
    go zero p = erase-inv φ p
    go (suc m) p =
      cong fst (cong (λ w → decode (suc (suc m)) 1 1 0 0 (one<s m) (suc-≤-suc zero-≤)
                          (suc-≤-suc zero-≤)
                          (enc (suc (suc m)) 1 1 0 0 (one<s m) (n<s→n≤s (one<s m)) φ) w)
               (vecToList-snoc (subst (Vec K) p (constantsFo φ))
                 (head (subst (Vec K) p (constantsFo φ)))
                ∙ cong (λ w → w ++ (head (subst (Vec K) p (constantsFo φ)) ∷ []))
                    (vecToList-subst p (constantsFo φ))))
      ∙ cong fst (decode-inv (suc (suc m)) 1 1 0 0 (one<s m)
               (n<s→n≤s {n = 1} {s = suc (suc m)} (one<s m))
               (suc-≤-suc zero-≤) (suc-≤-suc zero-≤) (suc-≤-suc zero-≤)
               φ (head (subst (Vec K) p (constantsFo φ)) ∷ []))

  encode-inj : {φ ψ : Formula K 1} → encode φ ≡ encode ψ → φ ≡ ψ
  encode-inj {φ} {ψ} p =
    sym (encode-decode φ) ∙ cong decode-total p ∙ encode-decode ψ

  count-inj : Σ[ f ∈ (Formula K 1 → Σ[ k ∈ ℕ ] (Formula (⊥* {ℓ}) k × Vec K k)) ]
                (∀ {φ ψ} → f φ ≡ f ψ → φ ≡ ψ)
  count-inj = encode , encode-inj
```

<!--en-->
## Recap
<!--zh-->
## 小结
<!--/-->

<!--en-->
Two injections, delivered. The shape-count codes the parameter-free formulas of each
arity into `ℕ` (per arity, exactly what the composition needs), on the strength of
the new square pairing. The count splits any unary formula over `K` into a
parameter-free shape and a tuple of constants, with a decode and a reconstruction
proving the split injective, generic in `K`. Both are constructive and need no
classical principles. This is the combinatorics the cardinal chapter stands on: it
will compose the two injections, and everything it adds on top of them is that
chapter's business, not this one's.
<!--zh-->
两条单射，交付完毕。形状计数把每个元数的无参公式编入 `ℕ` (逐元数，恰是复合所需)，靠的是新的平方配对。计数把 `K` 上任何一元公式拆成无参形状加常量元组，以解码与还原证明拆分单射，对 `K` 泛型。两者都构造性，不借任何经典原则。这就是基数章立足的组合学：它将复合这两条单射，而在此之上再添的一切，都归那章，不归本章。
<!--/-->
