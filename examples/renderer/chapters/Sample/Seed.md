```agda
{-# OPTIONS --cubical --safe --guardedness #-}
module Sample.Seed where
```

<!--en-->
# A small input
<!--zh-->
# 一个小输入
<!--ja-->
# 小さな入力
<!--/-->

<!--en-->
Our [marker]{.term-intro #marker} is a value with one constructor. The example supplies real definition links and signatures without importing a mathematical library.

## The marker type

The declaration below specifies its only constructor.

**Definition** (`Marker`{.Agda}) The type contains the constructor `mark`{.Agda}.
<!--zh-->
这里的[标记]{.term-intro #marker}是只有一个构造子的值。本例无需导入数学库，就能提供真实的定义链接和类型签名。

## 标记类型

下面的声明指定唯一的构造子。

**定义** (`Marker`{.Agda}) 该类型具有构造子 `mark`{.Agda}。
<!--ja-->
ここでの[印]{.term-intro #marker}は一つの構成子を持つ値である。数学ライブラリを導入せず，実際の定義リンクと型を提供する。

## 印の型

次の宣言で唯一の構成子を指定する。

**定義** (`Marker`{.Agda}) この型は構成子 `mark`{.Agda}を持つ。
<!--/-->

```agda
data Marker : Set where
  mark : Marker
```

∎

<!--en-->
## Returning an input

The next function returns the supplied marker unchanged.

**Definition** (`keep`{.Agda}) The result is the input.
<!--zh-->
## 返回输入

下一个函数原样返回给定的标记。

**定义** (`keep`{.Agda}) 结果就是输入。
<!--ja-->
## 入力を返す

次の関数は与えられた印をそのまま返す。

**定義** (`keep`{.Agda}) 結果は入力そのものである。
<!--/-->

```agda
keep : Marker → Marker
keep value = value
```

∎
