# Hello, World

<!--en-->
Bedrock's minimal literate module: reflexivity gives a path from any point to itself,
checked by the same toolchain this site is built with.
<!--zh-->
Bedrock 的最小文学化模块：自反性给出从任意一点到其自身的道路，由构建本站点的同一套工具链检查。
<!--/-->

```agda
{-# OPTIONS --cubical --safe --guardedness #-}
module HelloWorld where

open import Cubical.Foundations.Prelude

hello : {ℓ : Level} {A : Type ℓ} (x : A) → x ≡ x
hello x = refl
```
