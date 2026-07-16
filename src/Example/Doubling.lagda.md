# Doubling

<!--en-->
Doubling, defined via addition. This module exists to demonstrate cross-module hyperlinks,
inline references, and math in the rendering framework.
<!--zh-->
通过加法定义的加倍。本模块用于演示渲染框架中的跨模块超链接、行内引用与数学公式。
<!--/-->

## Definition

<!--en-->
Here `_+_`{.Agda} is the addition from the previous module, so `double`{.Agda} adds a number
to itself.
<!--zh-->
此处 `_+_`{.Agda} 是上一模块中的加法，故 `double`{.Agda} 将一个数与其自身相加。
<!--/-->

```agda
{-# OPTIONS --cubical --safe --guardedness #-}
module Example.Doubling where

open import Example.Naturals using ( Nat; _+_ )

double : Nat → Nat
double n = n + n
```

## A property

<!--en-->
By definition, doubling satisfies $\mathrm{double}(n) = n + n$.
<!--zh-->
根据定义，加倍满足 $\mathrm{double}(n) = n + n$。
<!--/-->

$$
\mathrm{double}(n) = n + n
$$
