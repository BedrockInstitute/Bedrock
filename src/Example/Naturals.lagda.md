# Naturals

<!--en-->
A hand-rolled type of natural numbers, with addition by recursion on the first argument.
This module exists to demonstrate the rendering framework; it is not part of the
mathematical development.
<!--zh-->
手工定义的自然数类型，加法对第一个参数递归。本模块用于演示渲染框架，并非数学开发的一部分。
<!--/-->

## The type

<!--en-->
`Nat`{.Agda} is the usual inductive type with two constructors, `zero`{.Agda} and
`suc`{.Agda}.
<!--zh-->
`Nat`{.Agda} 是常规的归纳类型，带有两个构造子 `zero`{.Agda} 与 `suc`{.Agda}。
<!--/-->

```agda
{-# OPTIONS --cubical --safe --guardedness #-}
module Example.Naturals where

open import Cubical.Foundations.Prelude using ( Type )

data Nat : Type where
  zero : Nat
  suc  : Nat → Nat
```

## Addition

<!--en-->
Addition `_+_`{.Agda} recurses on the first argument, so that $0 + m = m$ and
$(1 + n) + m = 1 + (n + m)$ hold definitionally.
<!--zh-->
加法 `_+_`{.Agda} 对第一个参数递归，故 $0 + m = m$ 与 $(1 + n) + m = 1 + (n + m)$ 在定义上成立。
<!--/-->

```agda
_+_ : Nat → Nat → Nat
zero  + m = m
suc n + m = suc (n + m)
```
