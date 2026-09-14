<!--en-->
# Cantor–Schröder–Bernstein inside L

Suppose two constructible sets admit coded injections in both directions. Their member types then admit a bijection, merely as an existence statement. This is the internal form of the Cantor–Schröder–Bernstein theorem used here: the hypotheses are expressed in the language of `L`, while the resulting bijection compares the ordinary types presenting the two sets.

The argument passes through two levels. A set of `L` carries an underlying set in the ambient cumulative hierarchy. Its members form an ordinary type, written `⟪ fst a ⟫`; coded injections belong to the object theory, whereas functions between these member types belong to the metatheory.
<!--zh-->
# L 内部的 Cantor–Schröder–Bernstein 定理

设两个可构造集合之间存在双向的编码单射，那么它们的成员类型之间仅仅存在一个双射。这是本章采用的 Cantor–Schröder–Bernstein 定理的内部形式：假设用 `L` 的语言表述，所得双射则比较这两个集合对应的普通类型。

论证在两个层面之间进行。`L` 的集合带有外围累积层级中的底层集合，其成员组成普通类型 `⟪ fst a ⟫`。编码单射属于对象理论，而这些成员类型之间的函数属于元理论。
<!--ja-->
# L の内部における Cantor–Schröder–Bernstein の定理

二つの構成可能集合の間に、両方向の符号化された単射があるとします。このとき、それらの要素型の間には全単射が単に存在します。これが本章で用いる Cantor–Schröder–Bernstein の定理の内部版です。仮定は `L` の言語で述べられ、得られる全単射は二つの集合を提示する通常の型を比較します。

議論は二つの層にまたがります。`L` の集合は周囲の累積階層に基礎となる集合をもち、その要素は通常の型 `⟪ fst a ⟫` をなします。符号化された単射は対象理論に属し、これらの要素型の間の関数はメタ理論に属します。
<!--/-->

```agda
{-# OPTIONS --cubical --safe --guardedness #-}

open import Base.Prelude
open import Base.Classical using ( LEM; lowerLEM )

module L.CantorBernstein {ℓ : Level} (lem : LEM (ℓ-suc ℓ)) where

open import FOL.ZFStructure using ( module hPropStructure )
```

<!--en-->
To apply the type-level theorem, each member type must be an h-set. The cumulative hierarchy already supplies this property: paths between two members carry no additional higher information. Thus `setPL` provides exactly the h-set certificate required for every presentation.
<!--zh-->
要使用类型层的定理，每个成员类型都必须是h-集合。累积层级已经保证这一性质：两个成员之间的路径不再含有更高层的额外信息。因此，`setPL` 为每个呈现给出所需的h-集合证书。
<!--ja-->
型の定理を適用するには、各要素型がh-集合でなければなりません。累積階層はすでにこの性質を備えており、二つの要素の間のパスにはそれ以上の高次情報がありません。したがって `setPL` は、各提示に必要なh-集合の証明を与えます。
<!--/-->

```agda
open import V.CantorBernstein {ℓ} (lowerLEM lem)
  using ( small-set; module MutualInj )
open import L.Constructible {ℓ} using ( 𝒮ʟ )
open import L.Cardinal {ℓ} lem using ( InjCode; InjL )
open import L.Coding.Injection {ℓ} lem using ( module Small )
```

<!--en-->
An injection code consists of a constructible graph together with three satisfaction facts and one value-range condition. They say that the graph is single-valued, has the prescribed domain, is injective, and sends every input into the prescribed codomain. These conditions contain precisely the information needed to recover a metatheoretic injection.
<!--zh-->
一个单射码由一个可构造图、三条满足事实和一条值域条件组成。它们分别说明该图是单值的、具有指定定义域、满足单射性，并把每个输入送入指定陪域。这些条件恰好足以恢复一条元理论中的单射。
<!--ja-->
単射の符号は、構成可能なグラフ、三つの充足事実、および一つの値域条件からなります。それらは、グラフが一価であり、指定された定義域をもち、単射的であり、各入力を指定された終域へ送ることを述べます。これらの条件から、メタ理論の単射をちょうど復元できます。
<!--/-->

```agda
open import Cubical.HITs.CumulativeHierarchy.Properties using ( ⟪_⟫ )
import Cubical.HITs.PropositionalTruncation as PT
open PT using ( ∥_∥₁ )

open hPropStructure 𝒮ʟ using ( S )
setPL : (a : S) → isSet (⟪ fst a ⟫)
```

<!--en-->
The function `readL` performs this passage. Given a coded graph from `a` to `b`, it returns an actual function from the members of `a` to the members of `b`, together with a proof that equal outputs have equal inputs. The construction itself is supplied by the preceding analysis of coded injections.
<!--zh-->
函数 `readL` 完成这一转换。给定从 `a` 到 `b` 的编码图，它返回一个从 `a` 的成员到 `b` 的成员的实际函数，并证明输出相等必有输入相等。这一构造来自前面对编码单射的分析。
<!--ja-->
関数 `readL` がこの移行を行います。`a` から `b` への符号化されたグラフを受け取り、`a` の要素から `b` の要素への実際の関数と、出力が等しければ入力も等しいという証明を返します。この構成は、先に行った符号化単射の解析から得られます。
<!--/-->

```agda
setPL a = small-set (fst a)
readL : (a b : S) → Σ[ F ∈ S ] InjCode F a b
      → Σ[ f ∈ (⟪ fst a ⟫ → ⟪ fst b ⟫) ]
          ((x y : ⟪ fst a ⟫) → f x ≡ f y → x ≡ y)
readL a b (F , sv , dm , ij , ran) = SM.small , SM.small-inj
```

<!--en-->
The abstract Cantor–Schröder–Bernstein argument can now be instantiated with constructible sets as objects, their member types as presentations, and coded graphs as injections. The h-set certificates and `readL` verify its two structural requirements. The same instantiation provides both a version for explicit witnesses and a version for merely existing witnesses.
<!--zh-->
现在可以把抽象的 Cantor–Schröder–Bernstein 论证应用于这一情形：对象取可构造集合，呈现取其成员类型，单射取编码图。h-集合证书与 `readL` 验证了所需的两项结构条件。同一次实例化既给出使用显式见证的版本，也给出仅仅假定见证存在的版本。
<!--ja-->
これで抽象的な Cantor–Schröder–Bernstein の議論を具体化できます。対象を構成可能集合、提示をその要素型、単射を符号化されたグラフとします。h-集合の証明と `readL` が、必要な二つの構造条件を満たします。同じ具体化から、明示的な証人を用いる版と、証人が単に存在する版の両方が得られます。
<!--/-->

```agda
  where
  module SM = Small F a b sv dm ij ran

module MutualInjL = MutualInj S (λ a → ⟪ fst a ⟫)
  (λ a b → Σ[ F ∈ S ] InjCode F a b) setPL readL
mutual-inj→bijection : (a b : S) → InjL a b → InjL b a
```

<!--en-->
The public theorem uses the second form because `InjL` records only the propositional truncation of an injection code. From the two truncated hypotheses it therefore derives a truncated bijection. Excluded middle is used inside the underlying type-level proof to separate the Cantor–Schröder–Bernstein construction into its cases; unique preimages are recovered from injectivity and the h-set condition, rather than from any choice principle.
<!--zh-->
公开的定理采用后一种形式，因为 `InjL` 只保留单射码的命题截断。因此，两个截断的假设导出一个截断的双射。排中律在底层类型论证明中用来区分 Cantor–Schröder–Bernstein 构造的各种情形；唯一原像由单射性与h-集合条件恢复，并不依赖任何选择原理。
<!--ja-->
公開される定理は後者を用います。`InjL` は単射の符号の命題的切り詰めだけを記録するからです。したがって、二つの切り詰められた仮定から、切り詰められた全単射が導かれます。排中律は基礎となる型の証明で Cantor–Schröder–Bernstein 構成の場合分けに用いられます。一意な逆像は単射性とh-集合の条件から復元され、選択原理には依存しません。
<!--/-->

```agda
  → ∥ Σ[ h ∈ (⟪ fst a ⟫ → ⟪ fst b ⟫) ]
       (((x y : ⟪ fst a ⟫) → h x ≡ h y → x ≡ y)
     × ((y : ⟪ fst b ⟫) → ∥ Σ[ x ∈ ⟪ fst a ⟫ ] (h x ≡ y) ∥₁)) ∥₁
mutual-inj→bijection = MutualInjL.∃bijection
```
