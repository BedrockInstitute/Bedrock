```agda
{-# OPTIONS --cubical --safe --guardedness #-}
module Sample.Use where
```

<!--en-->
# Using the input
<!--zh-->
# 使用输入
<!--ja-->
# 入力の利用
<!--/-->

```agda
open import Sample.Seed using ( Marker ; keep )
```

<!--en-->
We apply the earlier function twice. The [marker]{.term-ref #marker} link returns to its introduction.

## Two applications

The nested application exercises semantic expression selection.

**Definition** (`twice`{.Agda}) Two uses of `keep`{.Agda} still return the supplied value.
<!--zh-->
这里连续使用前面的函数两次。[标记]{.term-ref #marker}链接返回正式引入处。

## 两次应用

嵌套应用用于检验语义表达式的选择。

**定义** (`twice`{.Agda}) 两次使用 `keep`{.Agda}仍返回给定的值。
<!--ja-->
前の関数を二回適用する。[印]{.term-ref #marker}のリンクは導入箇所に戻る。

## 二回の適用

入れ子の適用で式の選択機能を検査する。

**定義** (`twice`{.Agda}) `keep`{.Agda}を二回用いても与えられた値が返る。
<!--/-->

```agda
twice : Marker → Marker
twice value = keep (keep value)
```

∎

<!--en-->
The ordinary [earlier chapter](Sample.Seed.html) link remains a normal page link.
<!--zh-->
普通的[前章](Sample.Seed.html)链接仍然直接跳转页面。
<!--ja-->
通常の[前章](Sample.Seed.html)リンクはページへ移動する。
<!--/-->
