<!--en-->
# The alphabet of formula codes
<!--zh-->
# 公式码的字母表
<!--ja-->
# 論理式符号のアルファベット
<!--/-->

<!--en-->
For a constructible set `W`, the module `Alphabet W` uses the members of `W` as
the constants of a first-order language. It embeds those constants into the
ambient hierarchy and defines the term code `ct` and formula code `cd` obtained
after that embedding; these constants are distinct from the ten constructor-tag
slots used by the closed code domain.
<!--zh-->
给定可构造集合 `W`，模块 `Alphabet W` 以 `W` 的成员作为一阶语言的常元。它把这些常元嵌入周遭层级，并定义嵌入后所得的词项码 `ct` 与公式码 `cd`；这里的常元不同于封闭码定义域所用的十个构造子标签槽位。
<!--ja-->
構成可能集合 `W` に対し、モジュール `Alphabet W` は `W` の要素を一階言語の定数として用いる。それらの定数を周囲の階層へ埋め込み、埋め込み後の項の符号 `ct` と論理式の符号 `cd` を定義する。ここでの定数は、閉じた符号の定義域が使う十個の構成子タグのスロットとは別のものである。
<!--/-->

```agda
{-# OPTIONS --cubical --safe --guardedness #-}

open import Base.Prelude
open import Base.Truth

module L.Coding.CodeAlphabet {ℓ : Level} where

open import FOL.ZFStructure using ( module hPropStructure )
open import FOL.Syntax using ( Formula; Term )
open import FOL.Manipulation.ConstantMapping using ( mapFo; mapTm )
open import V.Coding {ℓ} using ( module VCode )
open import L.Constructible {ℓ} using ( 𝒮ʟ )

open import Cubical.Foundations.Prelude using ( J; substRefl )
open import Cubical.HITs.CumulativeHierarchy.Base using ( V; _∈_ )
open import Cubical.HITs.CumulativeHierarchy.Properties using
  ( ∈∈ₛ; ⟪_⟫; ⟪_⟫↪; ∈ₛ⟪_⟫↪_ )

open hPropStructure 𝒮ʟ using ( S )
```

<!--en-->
## Embedding constants and coding syntax
<!--zh-->
## 嵌入常元并编码语法
<!--ja-->
## 定数を埋め込んで構文を符号化する
<!--/-->

<!--en-->
`Ab` is the type of members of `W`, and `ι` sends each such member to its
underlying set together with the proof `ι∈` that it lies in `W`. Mapping terms
and formulas along `ι` before applying the hierarchy coding gives `ct` and `cd`;
`cd-subst` shows that transporting an arity does not change the resulting code.
<!--zh-->
`Ab` 是 `W` 的成员类型，`ι` 把每个成员送到它的底层集合，而 `ι∈` 证明该集合属于 `W`。先沿 `ι` 映射词项与公式，再施以层级编码，便得到 `ct` 与 `cd`；`cd-subst` 表明搬运元数不会改变所得公式码。
<!--ja-->
`Ab` は `W` の要素の型であり、`ι` は各要素をその台となる集合へ送り、`ι∈` はその集合が `W` に属することを示す。項と論理式を `ι` に沿って写してから階層の符号化を施すことで `ct` と `cd` を得る。`cd-subst` はアリティを移送しても得られる論理式符号が変わらないことを示す。
<!--/-->

```agda
module Alphabet (W : S) where
  Ab : Type ℓ
  Ab = ⟪ fst W ⟫

  ι : Ab → V ℓ
  ι = ⟪ fst W ⟫↪

  ι∈ : (q : Ab) → ⟨ ι q ∈ fst W ⟩
  ι∈ q = ∈∈ₛ {a = ι q} {b = fst W} .snd (∈ₛ⟪ fst W ⟫↪ q)

  cd : ∀ {n} → Formula Ab n → V ℓ
  cd ψ = VCode.⌜ mapFo ι ψ ⌝

  ct : ∀ {n} → Term Ab n → V ℓ
  ct t = VCode.⌜ mapTm ι t ⌝ᵗ

  cd-subst : ∀ {n n'} (e : n ≡ n') (ψ : Formula Ab n) → cd (subst (Formula Ab) e ψ) ≡ cd ψ
  cd-subst {n} e ψ = J (λ n' e' → cd (subst (Formula Ab) e' ψ) ≡ cd ψ)
    (cong cd (substRefl {B = Formula Ab} ψ)) e
```

<!--en-->
## Recap
<!--zh-->
## 小结
<!--ja-->
## まとめ
<!--/-->

<!--en-->
`Alphabet W` turns the members of a constructible set into syntax constants and
provides their ambient term and formula codes through `ct` and `cd`.
<!--zh-->
`Alphabet W` 把一个可构造集合的成员变成语法常元，并通过 `ct` 与 `cd` 给出相应的周遭词项码和公式码。
<!--ja-->
`Alphabet W` は構成可能集合の要素を構文の定数とし、`ct` と `cd` によって周囲の項の符号と論理式の符号を与える。
<!--/-->
