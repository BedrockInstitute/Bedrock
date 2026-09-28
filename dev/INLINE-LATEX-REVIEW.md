# Inline LaTeX review inventory

54 paragraphs containing 115 inline LaTeX occurrences outside figures and standalone display math.
One review item covers one source paragraph, including all its formulas. Language variants and separate list items remain separate.
This is an inventory, not an approval. IDs are report-local paragraph IDs and replace the previous formula-level IDs; approval keys still bind exact source occurrences.
Figure-reference paragraphs are mechanically allowed by the localized fixed wording; this is separate from human approval and never extends to neighboring paragraphs.
Temporary chapter allowances are separate from permanent approvals: edits remain allowed while human_reviewed is false; setting it to true ends the allowance.
Re-run the inventory after editing prose. Only an explicit human decision may update the approval registry.

| Source | Paragraphs |
| --- | ---: |
| `src/Base/Choice.lagda.md` | 12 |
| `src/Base/Classical.lagda.md` | 3 |
| `src/Base/Prelude.lagda.md` | 9 |
| `src/FOL/LevyHierarchy.lagda.md` | 3 |
| `src/FOL/Manipulation/ParameterAbstraction.lagda.md` | 6 |
| `src/FOL/Semantics.lagda.md` | 3 |
| `src/FOL/ZFModel.lagda.md` | 3 |
| `src/L/Choice/FiniteStageOrders.lagda.md` | 3 |
| `src/V/CantorBernstein.lagda.md` | 12 |

## M001: src/Base/Choice.lagda.md:335 (en)

Allowed by figure-reference convention. 1 inline LaTeX occurrence(s).

Context:

```text
In the figure, write $e$ for `quotientPath≃P`{.Agda}: its forward map sends a path to a proof of `P`{.Agda}, and its inverse sends a proof to a path. The following panels show the consequences of a proof or a refutation of `P`{.Agda}, without presuming that either has already been obtained.
```

Formulas, in source order:

```latex
$e$
```

Exact approval keys, in the same order:

- `d4ac3cace4ec8af60eeef85cfd4a708c04f44772881128fb203b56abb7bcf659` (figure-reference convention)

## M002: src/Base/Choice.lagda.md:337 (zh)

Allowed by figure-reference convention. 1 inline LaTeX occurrence(s).

Context:

```text
图中的 $e$ 简记 `quotientPath≃P`{.Agda}：正向映射把路径变为 `P`{.Agda} 的证明，逆向映射把证明变为路径。下面分别展示有 `P`{.Agda} 的证明或反驳时的情形，并不预先断定我们已经取得了其中一种。
```

Formulas, in source order:

```latex
$e$
```

Exact approval keys, in the same order:

- `6fe13c78aa6c85f90db4ae6826653931caf89a9a5fb06f8dcf4421b85a490bee` (figure-reference convention)

## M003: src/Base/Choice.lagda.md:339 (ja)

Allowed by figure-reference convention. 1 inline LaTeX occurrence(s).

Context:

```text
図中の $e$ は `quotientPath≃P`{.Agda} の略記である。順方向の写像はパスを `P`{.Agda} の証明へ、逆方向の写像は証明をパスへ送る。以下は `P`{.Agda} の証明または反証があるときの帰結を示すもので、どちらかがすでに得られているとは仮定しない。
```

Formulas, in source order:

```latex
$e$
```

Exact approval keys, in the same order:

- `547edd6f3bd3aac304e174c88a4faff6dfd59aa32aa4fff29bc7d9e1dae551bb` (figure-reference convention)

## M004: src/Base/Choice.lagda.md:510 (en)

Allowed by figure-reference convention. 2 inline LaTeX occurrence(s).

Context:

```text
- `agree→P`{.Agda} If `q : b₀ ≡ b₁`{.Agda}, the certificates stored in `g`{.Agda} connect this agreement back to the quotient. Write $s_0$ and $s_1$ in the figure for `g [ true ] .snd`{.Agda} and `g [ false ] .snd`{.Agda}. The first certificate points from `[ b₀ ]`{.Agda} to `[ true ]`{.Agda}, so the composite must use `sym`{.Agda} there.
```

Formulas, in source order:

```latex
$s_0$
$s_1$
```

Exact approval keys, in the same order:

- `1cc41184c40dc584d5a400a75decee176272be8fe80a45648ba90b222c65fa2f` (figure-reference convention)
- `f9435dafd2e04320c6189b8b91b884382c8f764a8e372f3a83856271b9696934` (figure-reference convention)

## M005: src/Base/Choice.lagda.md:511 (en)

Allowed by figure-reference convention. 1 inline LaTeX occurrence(s).

Context:

```text
- `P→agree`{.Agda} Conversely, a proof `p : ⟨ P ⟩`{.Agda} gives the path `invEq quotientPath≃P p`{.Agda}, written $e^{-1}(p)$ in the figure. The ordinary function `λ x → g x .fst`{.Agda} sends that path to `b₀ ≡ b₁`{.Agda}. Taking the first component makes the codomain the fixed type `Bool`{.Agda}, so `cong`{.Agda} suffices.
```

Formulas, in source order:

```latex
$e^{-1}(p)$
```

Exact approval keys, in the same order:

- `30bf0edce00080a01f792a487e932d3cd2ec3de54f275eef45c3c2d196abb085` (figure-reference convention)

## M006: src/Base/Choice.lagda.md:515 (zh)

Allowed by figure-reference convention. 2 inline LaTeX occurrence(s).

Context:

```text
- `agree→P`{.Agda} 若有 `q : b₀ ≡ b₁`{.Agda}，`g`{.Agda} 中保存的证书就把这条相等接回商中。图中的 $s_0$、$s_1$ 分别简记 `g [ true ] .snd`{.Agda} 与 `g [ false ] .snd`{.Agda}。第一份证书从 `[ b₀ ]`{.Agda} 到 `[ true ]`{.Agda}，因此复合时要先用 `sym`{.Agda} 反向。
```

Formulas, in source order:

```latex
$s_0$
$s_1$
```

Exact approval keys, in the same order:

- `3648f9f5b102f9dad42310ff7d156c9e718e0b97bdb6f4c2a501c73e65d778b1` (figure-reference convention)
- `9b88720ac770e16434b4467d748b80cb8c95a39821338bc1f4f9c782c49a398e` (figure-reference convention)

## M007: src/Base/Choice.lagda.md:516 (zh)

Allowed by figure-reference convention. 1 inline LaTeX occurrence(s).

Context:

```text
- `P→agree`{.Agda} 反过来，证明 `p : ⟨ P ⟩`{.Agda} 经逆映射给出路径 `invEq quotientPath≃P p`{.Agda}，即图中的 $e^{-1}(p)$。普通函数 `λ x → g x .fst`{.Agda} 把它送到 `b₀ ≡ b₁`{.Agda}。取第一分量后，值域是固定的 `Bool`{.Agda}，因此只需使用 `cong`{.Agda}。
```

Formulas, in source order:

```latex
$e^{-1}(p)$
```

Exact approval keys, in the same order:

- `3945589ccb6c6170a2d2054215eed653b780af1da563960709f47078c0f22276` (figure-reference convention)

## M008: src/Base/Choice.lagda.md:520 (ja)

Allowed by figure-reference convention. 2 inline LaTeX occurrence(s).

Context:

```text
- `agree→P`{.Agda} `q : b₀ ≡ b₁`{.Agda} があれば、`g`{.Agda} に含まれる証明によって、この一致を商のパスへ結び付けられる。図中の $s_0$、$s_1$ は、それぞれ `g [ true ] .snd`{.Agda} と `g [ false ] .snd`{.Agda} の略記である。最初の証明は `[ b₀ ]`{.Agda} から `[ true ]`{.Agda} へ向かうため、合成には `sym`{.Agda} で逆にしたものを使う。
```

Formulas, in source order:

```latex
$s_0$
$s_1$
```

Exact approval keys, in the same order:

- `13f4042de944e68bc8422cff641cef3d9448d307ed23266275c3963a82fd68cc` (figure-reference convention)
- `3c407e5895c5687e8f3f19fcd510924a4a0ddd9c14c2acccf206fcc059041701` (figure-reference convention)

## M009: src/Base/Choice.lagda.md:521 (ja)

Allowed by figure-reference convention. 1 inline LaTeX occurrence(s).

Context:

```text
- `P→agree`{.Agda} 逆に `p : ⟨ P ⟩`{.Agda} からは、逆写像によってパス `invEq quotientPath≃P p`{.Agda} が得られる。図中の $e^{-1}(p)$ はこのパスを表す。通常の関数 `λ x → g x .fst`{.Agda} はこのパスを `b₀ ≡ b₁`{.Agda} へ送る。第一成分を取れば終域は固定された型 `Bool`{.Agda} なので、`cong`{.Agda} で十分である。
```

Formulas, in source order:

```latex
$e^{-1}(p)$
```

Exact approval keys, in the same order:

- `67abd25b956c5d75c4bc152f7b041f52b149080dcaf1e28b25e33703ab8af3ed` (figure-reference convention)

## M010: src/Base/Choice.lagda.md:664 (en)

Allowed by figure-reference convention. 1 inline LaTeX occurrence(s).

Context:

```text
The same factorization through truncation that appeared in the Prelude now closes the proof. In the figure, $G$ abbreviates the type `(x : Glued) → Pick x`{.Agda}. The map `decide`{.Agda} is defined on actual functions, while `rec₁ decideIsProp decide`{.Agda} accepts their mere existence.
```

Formulas, in source order:

```latex
$G$
```

Exact approval keys, in the same order:

- `e782f53e3467b1663c354dbf4674e128e4af80734029139bbceb3ee1165e63d2` (figure-reference convention)

## M011: src/Base/Choice.lagda.md:666 (zh)

Allowed by figure-reference convention. 1 inline LaTeX occurrence(s).

Context:

```text
《基础词汇》中经由截断的分解，在这里完成证明。图中的 $G$ 简记类型 `(x : Glued) → Pick x`{.Agda}。`decide`{.Agda} 以实际函数为输入，`rec₁ decideIsProp decide`{.Agda} 则可以接收它们的仅仅存在。
```

Formulas, in source order:

```latex
$G$
```

Exact approval keys, in the same order:

- `f370141b4772738beba726a3e9508ce25037ae38c690ee6db08f57e9e9f3fef6` (figure-reference convention)

## M012: src/Base/Choice.lagda.md:668 (ja)

Allowed by figure-reference convention. 1 inline LaTeX occurrence(s).

Context:

```text
「基礎語彙」で見た、切り詰めを経由する分解がここで証明を完成させる。図中の $G$ は型 `(x : Glued) → Pick x`{.Agda} の略記である。`decide`{.Agda} は実際の関数を受け取り、`rec₁ decideIsProp decide`{.Agda} はその単なる存在を受け取る。
```

Formulas, in source order:

```latex
$G$
```

Exact approval keys, in the same order:

- `cf9dba94a79d8eea29aa1a296cff00c7090d50600bdee8b44884875cbe437a49` (figure-reference convention)

## M013: src/Base/Classical.lagda.md:405 (en)

Allowed by figure-reference convention. 3 inline LaTeX occurrence(s).

Context:

```text
The two round-trip laws close the two triangles in the figure below. Fix `lem : LEM ℓ₁`{.Agda}, abbreviate the code type `Lift {ℓ-zero} {ℓ₂} Bool`{.Agda} by $B$, and write $E(P) := \operatorname{encodeB}\,P\,(\operatorname{lem}\,P)$ and $D := \operatorname{decodeB}$. Each round trip returns a point connected to its starting point by the indicated path.
```

Formulas, in source order:

```latex
$B$
$E(P) := \operatorname{encodeB}\,P\,(\operatorname{lem}\,P)$
$D := \operatorname{decodeB}$
```

Exact approval keys, in the same order:

- `5209a418452f20bf13add950db9c4f2d9041337a9be46dc0384dd246699ae836` (figure-reference convention)
- `8f8956f3f0a881d99055075a9b89bb96fc4772cd0b633b1690d270b991e5a053` (figure-reference convention)
- `0ee9cf5b007aeac60abad0fa59ac7eed3e2848eede96f1b18f88ddddf0688f01` (figure-reference convention)

## M014: src/Base/Classical.lagda.md:407 (zh)

Allowed by figure-reference convention. 3 inline LaTeX occurrence(s).

Context:

```text
下图中的两个三角形分别由两条往返律闭合。固定 `lem : LEM ℓ₁`{.Agda}，把编码类型 `Lift {ℓ-zero} {ℓ₂} Bool`{.Agda} 简写为 $B$，并记 $E(P) := \operatorname{encodeB}\,P\,(\operatorname{lem}\,P)$、$D := \operatorname{decodeB}$。每次往返所得的点，都由标出的路径与出发点相连。
```

Formulas, in source order:

```latex
$B$
$E(P) := \operatorname{encodeB}\,P\,(\operatorname{lem}\,P)$
$D := \operatorname{decodeB}$
```

Exact approval keys, in the same order:

- `806eeab5709b4f213e478d0d6b4810b4b2f837fadde906f6b8f69645cb2dd1ee` (figure-reference convention)
- `9666138b6b87d147450c46a0a106d78debfe3e913065496725400cf72a0c94c9` (figure-reference convention)
- `3f85eef5a6380e8368420cd4e6cf367379de8ccc3f039a3e96bfd5e4d5cb6ec4` (figure-reference convention)

## M015: src/Base/Classical.lagda.md:409 (ja)

Allowed by figure-reference convention. 3 inline LaTeX occurrence(s).

Context:

```text
図中の二つの三角形は、それぞれ二つの往復則によって閉じる。`lem : LEM ℓ₁`{.Agda} を固定し、符号の型 `Lift {ℓ-zero} {ℓ₂} Bool`{.Agda} を $B$ と略記し、$E(P) := \operatorname{encodeB}\,P\,(\operatorname{lem}\,P)$、$D := \operatorname{decodeB}$ と書く。各往復で得られる点は、示したパスによって出発点と結ばれる。
```

Formulas, in source order:

```latex
$B$
$E(P) := \operatorname{encodeB}\,P\,(\operatorname{lem}\,P)$
$D := \operatorname{decodeB}$
```

Exact approval keys, in the same order:

- `3d7d7154e5218a3203e797a546424f001acc31b8074a234c88b3f9411ede726e` (figure-reference convention)
- `43586c33c7f62b94c3841ef5ab4576a74d3b8299e8f8f4cb8b003b59d0243d38` (figure-reference convention)
- `92b3d9ca6f2b687fdefc1768b953b54792046bf7e8dfba3120e713f6a4283004` (figure-reference convention)

## M016: src/Base/Prelude.lagda.md:480 (en)

Approved. 1 inline LaTeX occurrence(s).

Context:

```text
In ordinary mathematics, $x = y$ asserts that two objects are equal. Here we write this assertion as `x ≡ y`{.Agda}: for two elements `x`{.Agda} and `y`{.Agda} of `A`{.Agda}, it is a type whose elements are proofs of their equality.
```

Formulas, in source order:

```latex
$x = y$
```

Exact approval keys, in the same order:

- `7f34fd1f1790e831941c7c1a40237d5f134b1be3ba4e9776002c719dbaade1bb` (approved)

## M017: src/Base/Prelude.lagda.md:482 (en)

Approved. 2 inline LaTeX occurrence(s).

Context:

```text
We reserve `=`{.Agda} for **[judgmental equality]{.term-intro #judgmental-equality}**, where the type system identifies two expressions by its definition and computation rules, as in `id x = x`{.Agda}. In a defining equation, this `=`{.Agda} plays the role often written $\mathrel{:=}$; judgmental equality also includes the consequences of computation. It is a judgment made by the type system, not itself a type in which we must supply a proof. By contrast, `x ≡ y`{.Agda} is a type, and `p : x ≡ y`{.Agda} supplies a proof of equality, playing the role of a proved $x = y$ in ordinary mathematics. When `x`{.Agda} and `y`{.Agda} are judgmentally equal, the constant path `refl`{.Agda} introduced below proves `x ≡ y`{.Agda}; a path between them does not in general make them judgmentally equal.
```

Formulas, in source order:

```latex
$\mathrel{:=}$
$x = y$
```

Exact approval keys, in the same order:

- `0d9bafa3d595386587b334f8db5dc7783a92780337d8cd0dd571a623d8cb3766` (approved)
- `98f249a73c865bbc90a8535ccc8da05a9560c228df845fc6d8049722ce91329e` (approved)

## M018: src/Base/Prelude.lagda.md:486 (zh)

Approved. 1 inline LaTeX occurrence(s).

Context:

```text
在通常的数学中，$x = y$ 断言两个对象相等。本书把这个断言写作 `x ≡ y`{.Agda}：对 `A`{.Agda} 中的两个元素 `x`{.Agda} 和 `y`{.Agda}，它是一个类型，其中的元素就是二者相等的证明。
```

Formulas, in source order:

```latex
$x = y$
```

Exact approval keys, in the same order:

- `676d8958802ff4871d471a013c91709763138920ff35889fa7709a0af4784f42` (approved)

## M019: src/Base/Prelude.lagda.md:488 (zh)

Approved. 2 inline LaTeX occurrence(s).

Context:

```text
我们把 `=`{.Agda} 留给**[判断相等]{.term-intro #judgmental-equality}** (judgmental equality)，即类型系统依据定义与计算规则把两个表达式认作相同，例如 `id x = x`{.Agda}。在给出定义时，这个 `=`{.Agda} 相当于通常写的 $\mathrel{:=}$；判断相等也包括计算所得到的相等。它是类型系统作出的判断，本身并不是一个需要我们提供证明的类型。相比之下，`x ≡ y`{.Agda} 是一个类型，`p : x ≡ y`{.Agda} 给出其中的相等证明，对应于通常数学中需要证明的 $x = y$。若 `x`{.Agda} 与 `y`{.Agda} 判断相等，下面介绍的常值路径 `refl`{.Agda} 就能证明 `x ≡ y`{.Agda}；反过来，二者之间有路径，一般并不意味着它们判断相等。
```

Formulas, in source order:

```latex
$\mathrel{:=}$
$x = y$
```

Exact approval keys, in the same order:

- `4d15bcb07be9100c3a65ef8685d08ce5d16c4ae6f0e013546bf4d31c2854d71a` (approved)
- `7d2c5118b55a4d1fb52dd4b88555df805f718cac36f61c1f83c234e125592601` (approved)

## M020: src/Base/Prelude.lagda.md:492 (ja)

Approved. 1 inline LaTeX occurrence(s).

Context:

```text
通常の数学では、$x = y$ は二つの対象が等しいという主張である。本書ではこれを `x ≡ y`{.Agda} と書く。`A`{.Agda} の二つの要素 `x`{.Agda} と `y`{.Agda} に対して、これは両者の等しさの証明を要素とする型である。
```

Formulas, in source order:

```latex
$x = y$
```

Exact approval keys, in the same order:

- `8c5db56774e52e715e1ccfe5b119c4a36e5d5ff479a9ca6b6bfa256e080cf0e0` (approved)

## M021: src/Base/Prelude.lagda.md:494 (ja)

Approved. 2 inline LaTeX occurrence(s).

Context:

```text
`=`{.Agda} は**[判断的等しさ]{.term-intro #judgmental-equality}** (judgmental equality) に用いる。これは型システムが定義と計算の規則に従って二つの式を同じものと認めることであり、`id x = x`{.Agda} がその例である。定義を与える式では、この `=`{.Agda} は通常の $\mathrel{:=}$ に相当するが、判断的等しさには計算から得られる等しさも含まれる。これは型システムが下す判断であって、それ自体が証明を与えるべき型なのではない。一方、`x ≡ y`{.Agda} は型であり、`p : x ≡ y`{.Agda} はその等しさの証明を与え、通常の数学で証明する $x = y$ に対応する。`x`{.Agda} と `y`{.Agda} が判断的に等しければ、以下で紹介する定値パス `refl`{.Agda} によって `x ≡ y`{.Agda} を証明できるが、両者の間にパスがあっても、一般には判断的に等しいとは限らない。
```

Formulas, in source order:

```latex
$\mathrel{:=}$
$x = y$
```

Exact approval keys, in the same order:

- `a1ee00de70add53c5b10ef1e97458a3cd845284a085b5b7ffa8b71975a768a90` (approved)
- `1bacad27d1adc9e326ff9a7b277bb447b37e27261f6ebe104e230ec7a8973089` (approved)

## M022: src/Base/Prelude.lagda.md:2387 (en)

Allowed by figure-reference convention. 1 inline LaTeX occurrence(s).

Context:

```text
For the length-three vector in the figure below, the labels $0,1,2$ abbreviate the `Fin 3`{.Agda} constructors `zero`{.Agda}, `suc zero`{.Agda}, and `suc (suc zero)`{.Agda}.
```

Formulas, in source order:

```latex
$0,1,2$
```

Exact approval keys, in the same order:

- `5871f94e6da0760c7e8d03b8209b79b6b2cb054dd6d6830a5399ec8054388bd4` (figure-reference convention)

## M023: src/Base/Prelude.lagda.md:2389 (zh)

Allowed by figure-reference convention. 1 inline LaTeX occurrence(s).

Context:

```text
下面取一个长度为三的向量；图中的 $0,1,2$ 分别简写 `Fin 3`{.Agda} 的构造子 `zero`{.Agda}、`suc zero`{.Agda}、`suc (suc zero)`{.Agda}。
```

Formulas, in source order:

```latex
$0,1,2$
```

Exact approval keys, in the same order:

- `c0d563bc01bf9528a33815bef558a6adbb60d981606010e6156134e4583ee790` (figure-reference convention)

## M024: src/Base/Prelude.lagda.md:2391 (ja)

Allowed by figure-reference convention. 1 inline LaTeX occurrence(s).

Context:

```text
下図では長さ三のベクトルを取る。図中の $0,1,2$ は `Fin 3`{.Agda} の構成子 `zero`{.Agda}、`suc zero`{.Agda}、`suc (suc zero)`{.Agda} の略記である。
```

Formulas, in source order:

```latex
$0,1,2$
```

Exact approval keys, in the same order:

- `d8003dc03c1b6affab875ab999a7164083bfa77a4ec6a952d82f4bb6b9af103a` (figure-reference convention)

## M025: src/FOL/LevyHierarchy.lagda.md:22 (en)

Temporarily allowed until this chapter is human-reviewed. 2 inline LaTeX occurrence(s).

Context:

```text
A first-order formula can quantify in two ways: boundedly, as in "for all $x$ in $t$", or unboundedly, over the whole universe. The Lévy hierarchy measures a formula's syntactic complexity by its unbounded quantifiers: **Δ₀** formulas use only bounded quantifiers, Σ₁ formulas prefix a block of unbounded existentials to a Δ₀ core, and Π₁ formulas prefix a block of unbounded universals. Membership in these classes matters because later chapters prove Δ₀-absoluteness and run definability arguments over the constructible universe by structural induction on quantifier shape. Rather than inspect formulas over and over, this chapter turns the classification itself into data: a **witness** is an inductive datum indexed by a formula, available for any constant domain `K`, so a formula can carry proof of its own complexity class alongside its syntax. The chapter builds the Δ₀ witness, a Boolean checker that recognizes bounded formulas, and the extension to every finite level Σₙ/Πₙ.
```

Formulas, in source order:

```latex
$x$
$t$
```

Exact approval keys, in the same order:

- `7ee03540f2278521d286fab8af21a49188d5b8f551052c68bf3d9adee781090b` (temporarily allowed)
- `fb00382957bb18edbb683e68442c4f68a1fb19dc3ae92266966cb870ba2db79e` (temporarily allowed)

## M026: src/FOL/LevyHierarchy.lagda.md:25 (zh)

Temporarily allowed until this chapter is human-reviewed. 2 inline LaTeX occurrence(s).

Context:

```text
一阶公式有两种量化方式：有界的，如「对所有 $x$ 属于 $t$」；以及在整个宇宙上取量的无界量化。Lévy 层级按无界量词衡量公式的语法复杂度：**Δ₀** 公式只用有界量词，Σ₁ 公式在 Δ₀ 核心之前加一段无界存在量词，Π₁ 公式则加一段无界全称量词。这些类的归属之所以重要，是因为后面的章节要证明 Δ₀ 绝对性，并在可构造宇宙上按量词形状做结构归纳的可定义性论证。与其反复去检查公式，本章干脆把分类本身做成数据：**见证**是以公式为下标的归纳数据，对任意常元域 `K` 都可用，于是一个公式可以在语法之外同时携带其复杂度类的证明。本章构造 Δ₀ 见证、一个识别有界公式的布尔检查器，以及推广到每个有限层级 Σₙ/Πₙ 的分类。
```

Formulas, in source order:

```latex
$x$
$t$
```

Exact approval keys, in the same order:

- `11ec361a8a1f5662fb4c410a7967d4e02fc7b4e04c2cc0eb748de7c7cd3191e4` (temporarily allowed)
- `5369196f9c22f69372ea8c0e330187baf4d205935ae5cc9f431afa926c52fe32` (temporarily allowed)

## M027: src/FOL/LevyHierarchy.lagda.md:28 (ja)

Temporarily allowed until this chapter is human-reviewed. 2 inline LaTeX occurrence(s).

Context:

```text
一階論理式には二つの量化の仕方がある。「$t$ に属するすべての $x$ について」という有界な量化と、宇宙全体にわたる非有界な量化である。Lévy 階層は、論理式の構文的な複雑さを非有界量化子で測る。**Δ₀** 論理式は有界量化子しか使わず、Σ₁ 論理式は Δ₀ の核の前に非有界な存在量化子の列を、Π₁ 論理式は非有界な全称量化子の列を前置する。これらのクラスへの所属が重要なのは、後の章で Δ₀ 絶対性を証明し、構成可能宇宙上で量化子の形に関する構造的帰納による定義可能性の議論を進めるからである。論理式をそのたびに調べる代わりに、本章では分類そのものをデータにする。**証拠**とは論理式で添字付けられた帰納的なデータであり、任意の定数域 `K` に対して使えるので、論理式は自分の構文とともに複雑さのクラスの証明を帯同できる。本章は Δ₀ の証拠、有界論理式を認識するブール判定器、そしてすべての有限レベル Σₙ/Πₙ への拡張を構成する。
```

Formulas, in source order:

```latex
$t$
$x$
```

Exact approval keys, in the same order:

- `0e6add26875940250c6b49398964eb2fec010283579911cd75ad652f66492ed4` (temporarily allowed)
- `08e6dce927c3a041daf0e7896261721656fd0eef6844dfbcb0f79cdaa61e475d` (temporarily allowed)

## M028: src/FOL/Manipulation/ParameterAbstraction.lagda.md:44 (en)

Temporarily allowed until this chapter is human-reviewed. 2 inline LaTeX occurrence(s).

Context:

```text
Chapter introductions of formulas often need constants: to say that a set $a$ is definable from parameters, one writes a formula mentioning $a$ by name. For coding arguments, however, it is convenient to work with parameter-free formulas only. Parameter abstraction is the translation that makes this possible: replace each constant occurrence by a fresh variable, and record the constants in a vector that the environment will supply.
```

Formulas, in source order:

```latex
$a$
$a$
```

Exact approval keys, in the same order:

- `7643dacc0123728b18a7c24733ff68984b982be9099197ffaf7d0fe3ee294133` (temporarily allowed)
- `b80916d19d7ca59e40c7d9c293e699b1797df6f80ba3896f2c03486eb540670a` (temporarily allowed)

## M029: src/FOL/Manipulation/ParameterAbstraction.lagda.md:46 (en)

Temporarily allowed until this chapter is human-reviewed. 1 inline LaTeX occurrence(s).

Context:

```text
The replacement works occurrence by occurrence, not constant by constant. If the constant $c$ appears twice, it is recorded twice and receives two variables. Recording occurrences this way means the translation never has to decide whether two names are equal, so the alphabet `K` needs no decidable equality; the positional count from the chapter on constant occurrences does all the bookkeeping.
```

Formulas, in source order:

```latex
$c$
```

Exact approval keys, in the same order:

- `2358fbd8bdc80d5a9ca5976bb952a4c019f3e36fc31aba5a411129e476061fe5` (temporarily allowed)

## M030: src/FOL/Manipulation/ParameterAbstraction.lagda.md:48 (zh)

Temporarily allowed until this chapter is human-reviewed. 2 inline LaTeX occurrence(s).

Context:

```text
公式的章首引言常常需要常元：要说集合 $a$ 可由参数定义，人们会写下提到 $a$ 的公式。但对编码论证而言，只使用无参公式会更方便。参数抽象正是使这成为可能的翻译：把每次常元出现换成新变量，并把诸常元记录在一个向量中，交给环境供给。
```

Formulas, in source order:

```latex
$a$
$a$
```

Exact approval keys, in the same order:

- `88f27984360de9880060fe8eb06bef072c09a2cbd8d7caa3dad7b04b5e07e521` (temporarily allowed)
- `ae9666d538285cab380129fe622a062b3b993af475e5529017b2e6f192cfc021` (temporarily allowed)

## M031: src/FOL/Manipulation/ParameterAbstraction.lagda.md:50 (zh)

Temporarily allowed until this chapter is human-reviewed. 1 inline LaTeX occurrence(s).

Context:

```text
这个替换按出现逐一进行，而不是按常元本身。若常元 $c$ 出现两次，它就被记录两次、获得两个变量。按出现记录意味着翻译无须判断两个名字是否相等，因此字母表 `K` 不需要可判定相等；常元出现一章的位置计数完成了全部簿记。
```

Formulas, in source order:

```latex
$c$
```

Exact approval keys, in the same order:

- `e0aa1dd5c9a08ba0660e7c780fe3442a0206370ec7bad5af8eb792ce4d961f95` (temporarily allowed)

## M032: src/FOL/Manipulation/ParameterAbstraction.lagda.md:52 (ja)

Temporarily allowed until this chapter is human-reviewed. 2 inline LaTeX occurrence(s).

Context:

```text
論理式を使う議論では定数が要る。集合 $a$ がパラメータ付きで定義可能だと言うには、$a$ を名前で言及する論理式を書くからである。しかし符号化の議論では、パラメータを持たない論理式だけを扱えると便利である。パラメータ抽象はそれを可能にする翻訳である。定数の各出現を新しい変数に置き換え、定数をベクトルに記録して環境から供給できるようにする。
```

Formulas, in source order:

```latex
$a$
$a$
```

Exact approval keys, in the same order:

- `ce8d4e61dd3f64c4cb86fa2bfe8df243e8e78c4e5344e42d05316ce3a8c90eb0` (temporarily allowed)
- `b38c09054a501932cd4cc9bf89700294acc0c01190542246d9934c1a3bf4957a` (temporarily allowed)

## M033: src/FOL/Manipulation/ParameterAbstraction.lagda.md:54 (ja)

Temporarily allowed until this chapter is human-reviewed. 1 inline LaTeX occurrence(s).

Context:

```text
この置き換えは定数ごとではなく、出現ごとに行われる。定数 $c$ が二度現れれば、二度記録され、二つの変数を受け取る。出現単位で記録するため、翻訳は二つの名前が等しいかを判定する必要がなく、アルファベット `K` に可判定な等式は要らない。定数の出現を数える章の位置的な数え上げが簿記のすべてを担う。
```

Formulas, in source order:

```latex
$c$
```

Exact approval keys, in the same order:

- `b3517020d8785b8e0eec2ad978014913c3b501274a95b59c3dba65a9a80b53b0` (temporarily allowed)

## M034: src/FOL/Semantics.lagda.md:83 (en)

Temporarily allowed until this chapter is human-reviewed. 1 inline LaTeX occurrence(s).

Context:

```text
The type of an environment is written `S ^ n`{.Agda}, matching the traditional superscript $S^n$; `_^_`{.Agda} reads "power" and is pure notation. It is defined as `Vec A n`, an ordered vector whose length is part of its type. Here a dependent type does real work: the arity of a formula and the length of an environment cannot disagree, for a mismatch would not be a well-formed combination at all. The operation `lookup` returns the entry at a position in `Fin n`{.Agda}, and `x ∷ γ` prepends one entry, moving the previous ones to the successor positions.
```

Formulas, in source order:

```latex
$S^n$
```

Exact approval keys, in the same order:

- `fe5a048bc6d89d60121bd40eb89b9d6c81f28ec1b059776648338f018f53b228` (temporarily allowed)

## M035: src/FOL/Semantics.lagda.md:85 (zh)

Temporarily allowed until this chapter is human-reviewed. 1 inline LaTeX occurrence(s).

Context:

```text
环境的类型记作 `S ^ n`{.Agda}，对应传统的上标 $S^n$；`_^_`{.Agda} 读作「幂」，纯粹是记号。它定义为 `Vec A n`，即长度写进类型的有序向量。这里依赖类型真正发挥了作用：公式的元数与环境的长度不可能不一致，不匹配时连合法的组合都构不成。运算 `lookup` 返回 `Fin n`{.Agda} 中某位置上的分量，`x ∷ γ` 在最前面加入一个分量，原有分量顺次移到后继位置。
```

Formulas, in source order:

```latex
$S^n$
```

Exact approval keys, in the same order:

- `8590c84919398a58486a2616c2280d81126c709d3a86c1bb75ef778629e0f286` (temporarily allowed)

## M036: src/FOL/Semantics.lagda.md:87 (ja)

Temporarily allowed until this chapter is human-reviewed. 1 inline LaTeX occurrence(s).

Context:

```text
環境の型は `S ^ n`{.Agda} と表記し、伝統的な上付きの $S^n$ に対応させる。`_^_`{.Agda} は「冪」と読むが、単なる記法である。その定義は `Vec A n`、すなわち長さが型の一部になっている順序付きベクトルである。ここでは依存型が実際の仕事を担っている。論理式のアリティと環境の長さは食い違いようがなく、不一致ならそもそも正しい組み合わせが成立しない。演算 `lookup` は `Fin n`{.Agda} の位置にある成分を返し、`x ∷ γ` は先頭に一つ成分を付け加え、それまでの成分を後続の位置へ移す。
```

Formulas, in source order:

```latex
$S^n$
```

Exact approval keys, in the same order:

- `91c678ad8350d277df24ea1036bcfe12e1d3e3ee2a0497e53814bb85845a355c` (temporarily allowed)

## M037: src/FOL/ZFModel.lagda.md:303 (en)

Temporarily allowed until this chapter is human-reviewed. 1 inline LaTeX occurrence(s).

Context:

```text
Every other axiom speaks either the object language or plain membership; regularity alone reaches for the host's notion of well-foundedness. The classical reason is that **no first-order sentence expresses external well-foundedness**: by the **compactness theorem** of classical model theory, any sentence true in exactly the well-founded structures would also hold in a structure carrying an infinite descending ∈-chain, since every finite fragment of the extended theory (a fresh constant chain $a_{n+1} \in a_n$) has a model. The book tells this argument but does not depend on it, and compactness is not developed here. The practical reason, visible in the type `WellFounded _∈ᵗ_` itself, is what this interface buys: well-foundedness as explicit data supports recursion and induction along membership. What is surrendered is that the condition is no longer visible to first-order formulas; this chapter makes no claim about how much that matters beyond what is proved below.
```

Formulas, in source order:

```latex
$a_{n+1} \in a_n$
```

Exact approval keys, in the same order:

- `e58539b323e913d04cd703e5f86acd8bf198b6d2b7000029a5b07a5db49a25cc` (temporarily allowed)

## M038: src/FOL/ZFModel.lagda.md:313 (zh)

Temporarily allowed until this chapter is human-reviewed. 1 inline LaTeX occurrence(s).

Context:

```text
其余公理说的要么是对象语言，要么是单纯的成员关系；唯独正则公理要借助宿主的良基概念。经典理由是：**没有任何一阶句子能表达外部良基性**。由经典模型论的**紧致性定理**，一个恰好在良基结构中成立的句子，也会在带有无穷下降 ∈-链的结构中成立，因为扩充理论 (新常元链 $a_{n+1} \in a_n$) 的每个有限片段都有模型。本书讲述这个论证但不依赖它，紧致性也不在本书展开。实践理由直接写在类型 `WellFounded _∈ᵗ_` 里：良基性作为显式数据，支持沿成员关系的递归与归纳。付出的代价是这个条件不再被一阶公式看见；除了下文证明的内容之外，本章不对这损失有多大作任何断言。
```

Formulas, in source order:

```latex
$a_{n+1} \in a_n$
```

Exact approval keys, in the same order:

- `24c5b46185a108185333f2e1d735c1d79feb0a2b91113e97fe9817e6aa52af35` (temporarily allowed)

## M039: src/FOL/ZFModel.lagda.md:323 (ja)

Temporarily allowed until this chapter is human-reviewed. 1 inline LaTeX occurrence(s).

Context:

```text
他の公理はいずれも対象言語か単純な所属で語るが、正則性公理だけはホストの整礎性の概念に頼る。古典的な理由は、**外部の整礎性を表現する一階の文は存在しない**ことである。古典的モデル理論の**コンパクト性定理**により、ちょうど整礎な構造で成り立つ文は、無限降下の ∈-列をもつ構造でも成り立つ。拡張された理論 (新しい定数の列 $a_{n+1} \in a_n$) の各有限断片はモデルを持つからである。本書はこの議論を語るが、これに依存せず、コンパクト性も展開しない。実用的な理由は型 `WellFounded _∈ᵗ_` そのものに見える。整礎性を明示的なデータとして持てば、所属に沿った再帰と帰納が使える。代償は、この条件が一階の論理式からは見えなくなることである。その損失がどのほど重要かについて、本章は以下で証明する範囲を超えて何も主張しない。
```

Formulas, in source order:

```latex
$a_{n+1} \in a_n$
```

Exact approval keys, in the same order:

- `e87717c5d637a2914824728314c072f49f908c05c894304735f2cbf72f0ffe57` (temporarily allowed)

## M040: src/L/Choice/FiniteStageOrders.lagda.md:19 (en)

Temporarily allowed until this chapter is human-reviewed. 1 inline LaTeX occurrence(s).

Context:

```text
The setting is the constructible universe built over the ambient cumulative hierarchy $V$. Excluded middle enters here as an explicit hypothesis: the module is parameterized by a decision `lem` for every proposition at level `ℓ-suc ℓ`. This one level is all the chapter asks for, and every construction below is allowed to call this single fixed decision; nothing is claimed for propositions at other levels beyond what the displayed theorems actually prove.
```

Formulas, in source order:

```latex
$V$
```

Exact approval keys, in the same order:

- `21cb89f9606e5bf111728af9b96bfd97c89dc51837c4f17f01fdf159c41a9f86` (temporarily allowed)

## M041: src/L/Choice/FiniteStageOrders.lagda.md:21 (zh)

Temporarily allowed until this chapter is human-reviewed. 1 inline LaTeX occurrence(s).

Context:

```text
讨论的舞台是建立在累积层级 $V$ 之上的可构造宇宙。排中律在这里作为显式假设出现：整个模块由一个参数 `lem` 给出，它对层级 `ℓ-suc ℓ` 上的每个命题作出判定。本章需要的正是这一个层级，下文的所有构造都可以使用这一固定判定；对于其他层级上的命题，除已证明的定理所述内容外，不作任何论断。
```

Formulas, in source order:

```latex
$V$
```

Exact approval keys, in the same order:

- `82a266f4b38bec78a688e6afb425b91918674e12fb8cab13e9659b0a6c3f900b` (temporarily allowed)

## M042: src/L/Choice/FiniteStageOrders.lagda.md:23 (ja)

Temporarily allowed until this chapter is human-reviewed. 1 inline LaTeX occurrence(s).

Context:

```text
舞台となるのは、周囲の累積階層 $V$ の上に構成される構成可能宇宙である。排中律はここで明示的な仮定として現れる。モジュールは、階層 `ℓ-suc ℓ` のすべての命題に対する判定を与えるパラメータ `lem` を受け取る。本章が必要とするのはこの一つの階層だけで、以下の構成はどれもこの固定された判定を用いる。表示されている定理が実際に証明する範囲を超えて、他の階層の命題については何も主張しない。
```

Formulas, in source order:

```latex
$V$
```

Exact approval keys, in the same order:

- `7acc7f3b1986e86159ed92ab39ebc22a9d9ec1706063855b55bd2bae41c5278e` (temporarily allowed)

## M043: src/V/CantorBernstein.lagda.md:34 (en)

Temporarily allowed until this chapter is human-reviewed. 5 inline LaTeX occurrence(s).

Context:

```text
The classical Cantor–Schröder–Bernstein theorem says that injections $f : A → B$ and $g : B → A$ yield a bijection $A → B$. In this chapter the two types share one universe level ℓ, and the only extra assumption is excluded middle at that level: for every proposition living at level ℓ, a proof or a refutation. The argument itself belongs to the index types $A$ and $B$, not to the sets of the cumulative hierarchy, which is precisely what later lets it be replayed on the member types of arbitrary small presentations. The proof needs to form some propositions by truncation and then to decide them; the setup below therefore fixes both the classical hypothesis and the proposition-valued vocabulary it will be applied to.
```

Formulas, in source order:

```latex
$f : A → B$
$g : B → A$
$A → B$
$A$
$B$
```

Exact approval keys, in the same order:

- `55df5495c6e37887dec55ddaedf8c0fce654417019de0a4c1582050b4b1644fb` (temporarily allowed)
- `3f8b30d153f8f895a256cebe056a2cfd5bf352903caa328f3c0b782b95037586` (temporarily allowed)
- `83d7d9fb5cf29657514a19fd6fd2d8fbcf2a9656ae187691aaedfc40e34ad9d6` (temporarily allowed)
- `79282dee74f599a60d622cc2f104c268a98e613197ceee71a47def64351ae692` (temporarily allowed)
- `67479063f9c2f7d4d4fca6373e264f6fbe62137ad98f5c09962e5a3d82f64c18` (temporarily allowed)

## M044: src/V/CantorBernstein.lagda.md:39 (zh)

Temporarily allowed until this chapter is human-reviewed. 5 inline LaTeX occurrence(s).

Context:

```text
经典的 Cantor–Schröder–Bernstein 定理说，单射 $f : A → B$ 与 $g : B → A$ 给出双射 $A → B$。本章中两个类型共享同一个宇宙层级 ℓ，而唯一的额外假设是该层级上的排中律：对住在层级 ℓ 的每个命题，给出证明或反驳。论证本身属于指标类型 $A$ 与 $B$，而不属于累积层级中的集合；正因如此，后面才能把它原样搬到任意小呈现的成员类型上。证明需要用命题截断造出一些命题，然后对它们作判定；下面的设置因此同时固定了经典假设，以及将要施加于其上的命题值词汇。
```

Formulas, in source order:

```latex
$f : A → B$
$g : B → A$
$A → B$
$A$
$B$
```

Exact approval keys, in the same order:

- `e5838588b4c35235683de6804f17b674a2f9fb1eff6c3a5c056180a44132f0af` (temporarily allowed)
- `7ddbc549d43be6afafff06226603fae5c4619e18157bbbb0bddc7487b1c87f45` (temporarily allowed)
- `e6174d968e1135c7ffa9714d129f02063d9a730c6b672fff2cfc1a746206f56d` (temporarily allowed)
- `7fcba32b99640f309b44d216f6f7d8a588184f65cf4d7abffba089843b41945d` (temporarily allowed)
- `819cd8f59aab5d6ba6dcdb20595d4b02d440bc7f143672298766998c945964cf` (temporarily allowed)

## M045: src/V/CantorBernstein.lagda.md:44 (ja)

Temporarily allowed until this chapter is human-reviewed. 5 inline LaTeX occurrence(s).

Context:

```text
古典的な Cantor–Schröder–Bernstein の定理は、単射 $f : A → B$ と $g : B → A$ から全単射 $A → B$ が得られるというものである。この章では二つの型が同一の宇宙レベル ℓ を共有し、追加の仮定はそのレベルでの排中律、すなわちレベル ℓ に住む各命題に対する証明か反証かだけである。議論そのものは累積階層の集合ではなく指標型 $A$ と $B$ に属する。まさにそのおかげで、後で任意の小さな提示のメンバー型へそのまま再生できるのである。証明は命題を命題的切り詰めで作り、それを判定する必要があるため、以下の設定ではその古典的仮定と、それを適用する命題値の語彙の両方を固定する。
```

Formulas, in source order:

```latex
$f : A → B$
$g : B → A$
$A → B$
$A$
$B$
```

Exact approval keys, in the same order:

- `1da251f7fadf5e8e5166a9db64b4642d8c39d024eac112dab94a8212c3b5e52b` (temporarily allowed)
- `7b7b331971443009ab10871c58b080888b754b1ccdbf721e14e72bbd43c7aedc` (temporarily allowed)
- `77799529e02ea07f20d8b8980f2628855e53f28f117235a92f14cc066243fcea` (temporarily allowed)
- `1492f65a57e9d21890f31ca4aa823e4342e6ce8be0ce9d98edcf78db53c384f8` (temporarily allowed)
- `6610da91a2969abf8da8d2b21ddc16c072e96db1f2f49d7f2149722b8bea083a` (temporarily allowed)

## M046: src/V/CantorBernstein.lagda.md:76 (en)

Temporarily allowed until this chapter is human-reviewed. 8 inline LaTeX occurrence(s).

Context:

```text
Two injections, one each way, give one bijection. This section proves that for two types $A$ and $B$ at the same universe level, with $A$ an h-set, under excluded middle at that level. The construction classifies each element of $A$ as bad or good: the bad elements are those reachable by a finite alternating preimage chain that starts outside the image of $g$. A bad element is sent forward through $f$, a good element back along a chosen inverse of $g$. Excluded middle enters twice, once to decide the badness proposition `C` and once to extract a chosen preimage from the truncated image statement; the chain itself is the predicate family `Cₙ`, and the only structural fact it needs is that $x ↦ g (f x)$ preserves badness.
```

Formulas, in source order:

```latex
$A$
$B$
$A$
$A$
$g$
$f$
$g$
$x ↦ g (f x)$
```

Exact approval keys, in the same order:

- `e683ec348e31ff5eb33561fcd5f42a860fa78c2b537a70f189b329116bfeae69` (temporarily allowed)
- `7a9ba485bcf8abacddd73e43c63032e931ea7dfe4be87b6d11142e06b3d4ab1b` (temporarily allowed)
- `61693038edb38bbba075424e4b5cfe9eb9eeddf7dd53be1c6b08b12d34d2075c` (temporarily allowed)
- `5f995129f1738a56bfac5fab80b6ea7d9fdd07a7bc0d2d4417d69993aafdda0e` (temporarily allowed)
- `eb717cbe8de85d33e61cbe31e981237fb5bee40884aefecd67cc99a04cf5d33b` (temporarily allowed)
- `51353b99ee748ab4418e99492d2178b4f046342af2b7599d7c50beff18566104` (temporarily allowed)
- `fd078a7e064b033bbdd4c294e1b50c0c2b2a7e7c0926511b865b24f1b66a171f` (temporarily allowed)
- `8c0b0f4916ed052e8e19fb953240e02d79d98c02486c60dc2cbc2fdb717d88a3` (temporarily allowed)

## M047: src/V/CantorBernstein.lagda.md:78 (zh)

Temporarily allowed until this chapter is human-reviewed. 6 inline LaTeX occurrence(s).

Context:

```text
两个方向各一条单射，给出一个双射。本节在层级 ℓ 的排中律下，对同一宇宙层级的两个类型 $A$ 与 $B$(其中 $A$ 是 h-集合) 证明这一点。构造把 $A$ 的每个元素分为坏的或好的：坏元素是那些可由一条从 g 的像之外出发的有限交错原像链到达的元素。坏元素经 $f$ 向前送，好元素沿 g 的选定逆像送回。排中律进入两次：一次判定坏性命题 `C`，一次从命题截断的像陈述中提取选定的原像；链本身是谓词族 `Cₙ`，它唯一需要的结构事实是 $x ↦ g (f x)$ 保持坏性。
```

Formulas, in source order:

```latex
$A$
$B$
$A$
$A$
$f$
$x ↦ g (f x)$
```

Exact approval keys, in the same order:

- `f7aeea929a93b5289f973d3634ffaa626ec7b6ca5202924e16f459b32213e984` (temporarily allowed)
- `70f863f6c79aa7a43016e2e1cdc8af14aca27b88b75793a5db9e7d8994558442` (temporarily allowed)
- `080bc932a6b7df44cd52e9d7af4d7afca55492004d16d952f84075b2aac23f0d` (temporarily allowed)
- `b71e817f29547283f5111965b92256026c57d078f28452926ea5376aa27299c8` (temporarily allowed)
- `832e4fa0e37f5a6d6497b31cf59d532418ddce4f531d63550e8ae904c948d914` (temporarily allowed)
- `97d1363badce368ee17614d91e19d6f5c520d09e305874ccc3ff1e34c25ff145` (temporarily allowed)

## M048: src/V/CantorBernstein.lagda.md:80 (ja)

Temporarily allowed until this chapter is human-reviewed. 5 inline LaTeX occurrence(s).

Context:

```text
互いに逆向きの二つの単射から、ひとつの全単射が得られる。この節は、同一の宇宙レベルにある二つの型 $A$ と $B$($A$ は h-集合) について、そのレベルの排中律の下でこれを証明する。構成は $A$ の各元を悪いか良いかに分類する。悪い元とは、g の像の外から始まる有限の交互の原像の鎖で到達できる元のことである。悪い元は f で前へ送り、良い元は g の選ばれた逆像に沿って送り戻す。排中律は二度使われる。一度は悪さの命題 `C` を判定するため、もう一度は命題的切り詰めされた像の主張から選ばれた原像を取り出すためである。鎖そのものは述語族 `Cₙ` であり、必要な構造的事実は $x ↦ g (f x)$ が悪さを保つことだけである。
```

Formulas, in source order:

```latex
$A$
$B$
$A$
$A$
$x ↦ g (f x)$
```

Exact approval keys, in the same order:

- `873d33682df7aea78a478adbb3069b672be7a5d73a1e17fb2e84b747207a10e2` (temporarily allowed)
- `5a380ce3d22bdc20b1b087767f480bdcddadc12c6f5c81cedbb8044465c3a0ec` (temporarily allowed)
- `2f1389048711275ad1d6b07980a18a69319bf5b274632d2cd87b3cfdce004f7a` (temporarily allowed)
- `643ca4218f499a8e2246a8d979375fe639c3f667f66f8f87aee53518069824d3` (temporarily allowed)
- `38ae42d9477759c014785fa104dda205b5811b1b9afc42b6cfcb2ae44b88b892` (temporarily allowed)

## M049: src/V/CantorBernstein.lagda.md:84 (en)

Temporarily allowed until this chapter is human-reviewed. 3 inline LaTeX occurrence(s).

Context:

```text
The construction is packaged in a module `Bernstein`{.Agda} taking exactly the classical data: the two types, the h-set structure of $A$, and the two injections, each given as a function together with its injectivity proof. Its first ingredient is the image predicate `imG x`, which asserts merely that some $y ∈ B$ satisfies $g y ≡ x$. No preimage is chosen here; the truncation ∥ ⋯ ∥₁ erases the witness and leaves a proposition, and `squash₁` is the certificate of that propositionhood.
```

Formulas, in source order:

```latex
$A$
$y ∈ B$
$g y ≡ x$
```

Exact approval keys, in the same order:

- `f15863dfe3e257a89599b0d230b66cfb35be4b21dda7b00b4b0ee56d55dd3066` (temporarily allowed)
- `bcaeae8467f10718901519efc556301be18030cfd475e2fc500ced3b8021cdec` (temporarily allowed)
- `40adcd322904957442675dd1bf1e4acedde27ee51dc5cfb9e3f42171a548b769` (temporarily allowed)

## M050: src/V/CantorBernstein.lagda.md:86 (zh)

Temporarily allowed until this chapter is human-reviewed. 3 inline LaTeX occurrence(s).

Context:

```text
整个构造被打包进模块 `Bernstein`{.Agda}，它恰好接受经典的数据：两个类型、$A$ 的 h-集合结构，以及两条单射，每条由函数与其单射性证明共同给出。第一个成分是像谓词 `imG x`，它仅仅断言存在某个 $y ∈ B$ 使 $g y ≡ x$。这里不选定任何原像；命题截断 ∥ ⋯ ∥₁ 抹去见证而留下一个命题，`squash₁` 就是该命题性的证书。
```

Formulas, in source order:

```latex
$A$
$y ∈ B$
$g y ≡ x$
```

Exact approval keys, in the same order:

- `f1f1492bb38a3f1ce72459bb86dd390c7d53636efff55510b0695b5078a1ffc6` (temporarily allowed)
- `b2b06d7bbe165077206f27007cc5e2f9c994e71ab3c530a11bb250987287029b` (temporarily allowed)
- `610bf2dc4b9fa67a44b3d272a64f430ffb6adc858015049f03503c7299b2263e` (temporarily allowed)

## M051: src/V/CantorBernstein.lagda.md:88 (ja)

Temporarily allowed until this chapter is human-reviewed. 3 inline LaTeX occurrence(s).

Context:

```text
構成はモジュール `Bernstein`{.Agda} にまとめられ、受け取るのはまさに古典的なデータである。二つの型、$A$ の h-集合としての構造、そして二つの単射で、各々は関数とその単射性の証明の組として与えられる。最初の材料は像の述語 `imG x` で、ある $y ∈ B$ が $g y ≡ x$ を満たすことを単に (単に) 主張する。ここで原像は選ばれない。命題的切り詰め ∥ ⋯ ∥₁ が証人を消して命題だけを残し、`squash₁` がその命題性の証明書になる。
```

Formulas, in source order:

```latex
$A$
$y ∈ B$
$g y ≡ x$
```

Exact approval keys, in the same order:

- `1c510aae6bd6ac74cfc15209e38bff5e53bd0d72bd7b40476e686ee3fea0e32b` (temporarily allowed)
- `599999166058c8e30dacecc6cbde63263f4b9923962526c86258603b8a03a5cd` (temporarily allowed)
- `4dfd812d5abf03d5007e54c983d76e76295cfe6fdbdb8fa887d77796f0a612f8` (temporarily allowed)

## M052: src/V/CantorBernstein.lagda.md:107 (en)

Temporarily allowed until this chapter is human-reviewed. 4 inline LaTeX occurrence(s).

Context:

```text
The base of the badness hierarchy says that x is bad at level zero when it is not in the image of g at all. Since a refutation of `imG x` is a map from `⟨ imG x ⟩` into the empty type, `C₀ x` is a function type, and it is a proposition because a function into a proposition is one. The step `C₊ C x` then says that x is reachable from a bad element by one backward step: merely there are $y ∈ B$ and $z ∈ A$ with $g y ≡ x$, $f z ≡ y$, and z already bad for C. Applying this operator iteratively from `C₀` gives `Cₙ`, so an inhabitant of `Cₙ n x` records an alternating chain x = g y, y = f z, z bad one level down, of length n.
```

Formulas, in source order:

```latex
$y ∈ B$
$z ∈ A$
$g y ≡ x$
$f z ≡ y$
```

Exact approval keys, in the same order:

- `38e55dafe5801be20c0a928f201e40a2ccc9d58bbd843d9bc0d53776f2e69276` (temporarily allowed)
- `3fede2e35e8ceeeaa022b6e10ee9304b733ce19cd3e16c0f97fa9d68edc43207` (temporarily allowed)
- `40aea4c44887736b448d9f7f9129499a8fae5e87a99f8661038fe3a92a1787f4` (temporarily allowed)
- `9839bb195f8d111bfc3c7439a69b3e77418d583586d8240f95b721b63ba83c98` (temporarily allowed)

## M053: src/V/CantorBernstein.lagda.md:109 (zh)

Temporarily allowed until this chapter is human-reviewed. 4 inline LaTeX occurrence(s).

Context:

```text
坏性层级的基础说：当 x 完全不在 g 的像中时，x 在第零层是坏的。由于 `imG x` 的反驳是从 `⟨ imG x ⟩` 到空类型的映射，`C₀ x` 是函数类型；因为映入命题的函数仍是命题，所以它是命题。步进算子 `C₊ C x` 说：x 可从某个坏元素经一步后退到达，即仅仅存在 $y ∈ B$ 与 $z ∈ A$ 使 $g y ≡ x$、$f z ≡ y$、且 z 对 C 已经是坏的。从 `C₀` 出发迭代该算子得到 `Cₙ`，于是 `Cₙ n x` 的一个元记录了一条长为 n 的交错链：x = g y，y = f z，而 z 在低一层已是坏的。
```

Formulas, in source order:

```latex
$y ∈ B$
$z ∈ A$
$g y ≡ x$
$f z ≡ y$
```

Exact approval keys, in the same order:

- `5714af28a2c7806f7f2bbcb5ce3d3b984772506961fa684ff42cb700c35d85ab` (temporarily allowed)
- `2f5f88d3e395e164b53387cdaf01227dc86a35f92ed3fe9b565138eab393350d` (temporarily allowed)
- `b91f237b0c63065b9c966dc0c53b97eaab8a6855e3322526fea45f80b0a3ecb9` (temporarily allowed)
- `09e78302bd6f1c688fdc39a06c72755516841ac32521bb4fafd3149172ee889c` (temporarily allowed)

## M054: src/V/CantorBernstein.lagda.md:111 (ja)

Temporarily allowed until this chapter is human-reviewed. 4 inline LaTeX occurrence(s).

Context:

```text
悪さの階層の底辺は、x が g の像にまったく属さないとき x がレベル 0 で悪いと言う。`imG x` の反証とは `⟨ imG x ⟩` から空型への写像なので `C₀ x` は関数型であり、命題への写像はふたたび命題であるため、これは命題である。ステップ演算 `C₊ C x` は、x がどこかの悪い元から一段後退りで到達できること、つまり $g y ≡ x$、$f z ≡ y$、かつ z が C に対してすでに悪いような $y ∈ B$ と $z ∈ A$ が単に存在することを言う。`C₀` からこの演算を繰り返して `Cₙ` が得られ、したがって `Cₙ n x` の元は、x = g y、y = f z、z は一段下で悪い、という長さ n の交互の鎖を記録する。
```

Formulas, in source order:

```latex
$g y ≡ x$
$f z ≡ y$
$y ∈ B$
$z ∈ A$
```

Exact approval keys, in the same order:

- `dc2c871dc7751f0e33d3d544f9e8fab4b8781c7fe6070df846fadc19396ffb42` (temporarily allowed)
- `465912b265dc40c06ff2007702a7bdbc5197c4a145ec2b175d40363023c3dab3` (temporarily allowed)
- `ce8b6b4226b8eac97fce354970adfd9b4937da2ee07a38d097f29a20b41de691` (temporarily allowed)
- `cda77f0b974a80102cb91a72f4f80f1f9e568cf64947b4f64275eb139d21e82e` (temporarily allowed)
