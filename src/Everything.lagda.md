# Bedrock

<!--en-->
*Laying the groundwork for the metaphysics of V.*

A machine-checked development, in Cubical Agda, of the set theory underlying contemporary
questions about the universe of sets: forcing, inner models, and the structure of V. The
immediate target is a full mechanization of `L` ⊨ GCH, with the cumulative hierarchy `V`
realised as a higher inductive type. The full treatment is in the
[Charter](https://github.com/BedrockInstitute/Bedrock/blob/main/docs/en/CHARTER.md).

This site is generated from literate Agda; this page is the book's **reading
catalog**: the table of contents in learning order, which the chapter-end
navigation also follows. For the structural view, by namespace, use the module
tree in the sidebar. The mathematics proper is under construction: the groundwork,
logic, and model parts are in place, and the parts on the cumulative hierarchy
and the constructible universe follow.
<!--zh-->
*为 V 的形而上学奠基。*

一项在 Cubical Agda 中的机器验证工作，针对当代集合宇宙问题背后的那部分集合论：力迫、内模型，以及 V 的结构。当前目标是完整机械化 `L` ⊨ GCH，其中累积层级 `V` 以高阶归纳类型实现。完整论述见 [纲领](https://github.com/BedrockInstitute/Bedrock/blob/main/docs/zh/CHARTER.md)。

本站点由文学化 Agda 生成；本页是全书的**阅读目录**：按学习顺序排列，每章页尾的导航循此顺序。按知识结构浏览，请用侧边栏按命名空间分组的模块树。数学本体正在施工中：奠基、逻辑与模型诸部已就位，累积层级与可构造宇宙两部随后。
<!--/-->

```agda
{-# OPTIONS --cubical --safe --guardedness #-}
module Everything where
```

<!--en-->
## Landmarks: where the book ends up

- `Landmarks`{.Agda}: the trophy case, displayed at the entrance: the milestone
  theorems restated as self-contained signatures with their full assumption
  bills, `V⊨ZF`{.Agda} (and its classical redemption), `V⊨ZFC`{.Agda}, and the
  frontier-conditional `L⊨ZFC`{.Agda}, each hypothesis spelled in the name.
  Read it first to see the destination; understanding the signatures is what
  the rest of the book is for.
<!--zh-->
## 地标：本书的终点

- `Landmarks`{.Agda}：奖杯陈列室，摆在入口处：里程碑定理以自足签名重述，假设账单全额陈列：`V⊨ZF`{.Agda} (及其精确价格版 `V⊨ZF-impredicative`{.Agda})、单凭选择的 `V⊨ZFC`{.Agda}，与带前沿条件的 `L⊨ZFC`{.Agda}。先读它，看清目的地；至于读懂这些签名，正是全书其余部分的任务。
<!--/-->

```agda
import Landmarks
```

<!--en-->
## Part 0: the groundwork

- `Base.Prelude`{.Agda}: the curated host vocabulary (universes, paths, h-levels,
  `hProp`{.Agda}, pairs, the indexing data), and the traceability discipline that
  governs how the book is read.
- `Base.Truth`{.Agda}: the truth algebra `TruthAlgebra`{.Agda}, a law-free operation
  signature that is the book's sole source of logic symbols, with its canonical
  instance `hPropAlgebra`{.Agda}.
- `Base.Impredicativity`{.Agda}: the size vocabulary: `isSmall`{.Agda},
  resizing as "every proposition is small" (`Resizing`{.Agda}), the small
  classifier `HPropSmallness`{.Agda}, and their packing
  `Impredicativity`{.Agda}; interfaces only, nothing assumed.
- `Base.Classical`{.Agda}: the classical boundary: excluded middle as the parameter
  interface `LEM`{.Agda}, and the impredicativity interfaces redeemed from it
  (`lem→resizing`{.Agda}, `lem→hPropSmallness`{.Agda},
  `lem→impredicativity`{.Agda}).
- `Base.Choice`{.Agda}: the boundary's second interface: set-level choice
  `SetChoice`{.Agda}, stated levelwise like `LEM`{.Agda}, with Diaconescu's
  theorem mechanized at once: choice proves the excluded middle
  (`choice→lem`{.Agda}).
<!--zh-->
## 第零部：奠基

- `Base.Prelude`{.Agda}：精选的宿主词汇 (宇宙、路径、h-层级、`hProp`{.Agda}、依值对与索引数据)，以及决定本书读法的可溯源纪律。
- `Base.Truth`{.Agda}：真值代数 `TruthAlgebra`{.Agda}，零定律的运算签名，全书逻辑符号的唯一来源；附典范实例 `hPropAlgebra`{.Agda}。
- `Base.Impredicativity`{.Agda}：尺寸词汇：`isSmall`{.Agda}；降层即「任意命题皆小」(`Resizing`{.Agda})；小分类器 `HPropSmallness`{.Agda}；及其打包 `Impredicativity`{.Agda}。只有接口，无所假设。
- `Base.Classical`{.Agda}：经典边界：排中律作为参数接口 `LEM`{.Agda}，与从它赎回的非直谓性诸接口 (`lem→resizing`{.Agda}、`lem→hPropSmallness`{.Agda}、`lem→impredicativity`{.Agda})。
- `Base.Choice`{.Agda}：边界的第二个接口：集合层选择 `SetChoice`{.Agda}，与 `LEM`{.Agda} 同款逐层级陈述；Diaconescu 定理当场机器化：选择证明排中律 (`choice→lem`{.Agda})。
<!--/-->

```agda
import Base.Prelude
import Base.Truth
import Base.Impredicativity
import Base.Classical
import Base.Choice
```

<!--en-->
## Part 1: first-order logic as an object of study

- `FOL.Syntax`{.Agda}: the object language: a deeply embedded `Formula`{.Agda} with
  the constant domain as a parameter, intrinsic scoping, and every constructor
  primitive.
- `FOL.ZFStructure`{.Agda}: the structures formulas talk about: carrier, equality,
  and membership, valued in a truth algebra; transitive classes and the
  restriction `↾`.
- `FOL.Semantics`{.Agda}: environments `S ^ n`, then evaluation `⟦_⟧`{.Agda} and
  satisfaction `_⊨_`{.Agda} by
  structural recursion, each clause exactly its truth-algebra operation.
- `FOL.LevyHierarchy`{.Agda}: the Levy hierarchy as inductive witnesses: the
  absence of unbounded quantifiers is Δ₀; above it, Σ₁/Π₁ and the alternating
  Σₙ/Πₙ tower.
- `FOL.Absoluteness`{.Agda}: the Δ₀ absoluteness theorem `abs₀`{.Agda} over a
  transitive class; Σ₁ transfers up, Π₁ down.
<!--zh-->
## 第一部：作为研究对象的一阶逻辑

- `FOL.Syntax`{.Agda}：对象语言：深嵌入的 `Formula`{.Agda}，常量域作参数，作用域内蕴，构造子全原语。
- `FOL.ZFStructure`{.Agda}：公式所谈论的结构：载体、等词与成员，取值于真值代数；传递类与限制 `↾`。
- `FOL.Semantics`{.Agda}：环境 `S ^ n`，与结构递归给出的求值 `⟦_⟧`{.Agda} 与满足 `_⊨_`{.Agda}，每条子句恰是对应的真值代数运算。
- `FOL.LevyHierarchy`{.Agda}：作为归纳见证的 Lévy 层级：无界量词的缺席即 Δ₀，其上是 Σ₁/Π₁ 与交替的 Σₙ/Πₙ 之塔。
- `FOL.Absoluteness`{.Agda}：传递类上的 Δ₀ 绝对性定理 `abs₀`{.Agda}；Σ₁ 向上、Π₁ 向下。
<!--/-->

```agda
import FOL.Syntax
import FOL.ZFStructure
import FOL.Semantics
import FOL.LevyHierarchy
import FOL.Absoluteness
```

<!--en-->
## Part 2: what a model of ZF is

- `FOL.ZFModel`{.Agda}: the axioms as a record: `isZFModel`{.Agda} with extensionality,
  meta-level regularity (the compactness ceiling), unique existence discharged by
  the description operator `℩`, separation and replacement consuming the book's
  own formulas, and strong infinity through the numeral chain; `isZFCModel`{.Agda}
  adds choice as an extension.
<!--zh-->
## 第二部：何谓 ZF 模型

- `FOL.ZFModel`{.Agda}：公理作为 record：`isZFModel`{.Agda} 含外延公理、元层面的正则公理 (紧致性天花板)、经摹状词算子 `℩` 兑现的唯一存在、消费本书自家公式的分离与替换，以及经数码链的强无穷；`isZFCModel`{.Agda} 以扩展形式添加选择公理。
<!--/-->

```agda
import FOL.ZFModel
```

<!--en-->
## Part 3: the cumulative hierarchy realizes ZF(C)

- `V.Hierarchy`{.Agda}: the library's higher inductive type `V`{.Agda}: sets as
  images of small families, extensional equality as a path constructor; the
  structure `𝒮ᵥ`{.Agda} assembled directly, with extensionality and regularity
  banked free.
- `V.Smallness`{.Agda}: the smallness toolkit: atoms compress through the
  library, connectives and bounded quantifiers pass smallness witnesses along,
  `separateFromSmall`{.Agda} is the one pipe to sets; `Δ₀-small`{.Agda} makes Δ₀
  separation an axiom-free theorem (`separateΔ₀`{.Agda}).
- `V.Model`{.Agda}: the summit: stock sets reshaped, replacement and strong
  infinity for free, Part 0's `Impredicativity`{.Agda} pricing full separation
  and power set; `V⊨ZF-impredicative`{.Agda} at that exact price, the headline
  `V⊨ZF`{.Agda} from the excluded middle, and by Diaconescu `V⊨ZFC`{.Agda} from
  choice alone.
<!--zh-->
## 第三部：累积层级实现 ZF(C)

- `V.Hierarchy`{.Agda}：库的高阶归纳类型 `V`{.Agda}：集合是小族的像，外延相等是路径构造子；结构 `𝒮ᵥ`{.Agda} 径直装配，外延与正则免费入账。
- `V.Smallness`{.Agda}：小性工具链：原子经库压缩，联结词与有界量词传递小性见证，`separateFromSmall`{.Agda} 是通往集合的唯一水管；`Δ₀-small`{.Agda} 让 Δ₀ 分离成为零公理定理 (`separateΔ₀`{.Agda})。
- `V.Model`{.Agda}：本部之巅：库存换形，替换与强无穷白得，第零部的 `Impredicativity`{.Agda} 为全分离与幂集标价；`V⊨ZF-impredicative`{.Agda} 以此精确价格合龙，主打的 `V⊨ZF`{.Agda} 由排中律赎回，经 Diaconescu 的 `V⊨ZFC`{.Agda} 则单凭选择。
<!--/-->

```agda
import V.Hierarchy
import V.Smallness
import V.Model
```

<!--en-->
## Part 4: the constructible universe

- `FOL.Manipulation.Relabelling`{.Agda}: the constant-domain kit, three altitudes at once:
  functorial `mapFo`{.Agda}, the parameter-free entrance `embed`{.Agda},
  meaning untouched (`⊨-map`{.Agda},
  `embed-⊨`{.Agda}), Levy witnesses carried along (`mapΔ₀`{.Agda} and the
  tower).
- `FOL.Manipulation.Bounding`{.Agda}: relabelling when the map is only partial:
  `BoundedFo`{.Agda} certifies, occurrence by occurrence, that a formula's
  constants satisfy a predicate, `BoundedFo-mono`{.Agda} weakens it, and
  `Relabel`{.Agda} spends it: the certificate is the licence to relabel along a
  partial map, with meaning and Levy witness both carried across.
- `FOL.Coding`{.Agda}: syntax as sets: `⌜_⌝`{.Agda} tags a constructor index
  onto the codes of the parts (constants coding themselves), and the inductive
  relation `Codes`{.Agda} is the interface, keeping code values out of the
  equations a typechecker has to normalize.
- `V.Coding`{.Agda}: the hierarchy discharges both coding parameters: numerals
  are injective (`#-inj`{.Agda}) and Kuratowski pairs are injective
  (`pr-inj`{.Agda}), so formulas over `V` become sets of `V`.
- `L.Definability`{.Agda}: the single step: `Def A`, the definable subsets of
  `A` with parameters from `A`: syntax as index set, inner satisfaction for
  meaning, essential smallness footing the bill; `A ∈ Def A` always, and
  `A ⊆ Def A` under transitivity.
- `L.Constructible`{.Agda}: the tower `Lset`{.Agda} by membership recursion,
  one equation for zero, successors, and limits; the layer predicate
  `isLayer`{.Agda} with `layer-trans`{.Agda}; the class `isL`{.Agda} and the
  structure `𝒮ʟ`{.Agda}.
- `L.Ordinal`{.Agda}: the supply of ordinals the closure arguments need: zero,
  successors and small unions are ordinals, and `boundingOrd`{.Agda} bounds any
  small family by a single ordinal. No comparison, hence no classical logic.
- `L.Rank`{.Agda}: von Neumann rank by membership recursion, valued in the
  hierarchy itself: `rank-ord`{.Agda} makes it a measurement in ordinals and
  `rank-fix`{.Agda} certifies it as the canonical index.
- `L.Ordinal.Linear`{.Agda}: trichotomy `ord-tri`{.Agda}, and with it the L
  side's classical boundary: closure never had to decide anything, comparison
  does, so this chapter takes the excluded middle as a module parameter.
- `L.Ordinal.Stages`{.Agda}: the ordinals of `Lset α` are exactly the members of
  `α`: `rank-Lset`{.Agda} and `ord∈Lset→∈`{.Agda} say none appears early,
  `ord∈Lset-suc`{.Agda} says none appears late.
- `L.WellOrder.Base`{.Agda}: strict well-orders as a bundle (`SWO`{.Agda}), and
  the least element of a non-empty subset (`leastOf`{.Agda}), unique by
  trichotomy: the choosing device both reflection and choice will take.
- `L.Coding.Base`{.Agda}: reading codes from inside: `allCodes`{.Agda} gathers
  every parameter-free formula's code into one nameable set, and
  `prAt`{.Agda} / `tagAt`{.Agda} destructure a Kuratowski pair and a tag in
  bounded form, Δ₀ and adequate.
- `L.Coding.Environment`{.Agda}: environments as their graphs, functional by
  `lookup-spec`{.Agda}; `memPairAt`{.Agda} reads a value, `sucAt`{.Agda}
  recognizes the index shift under a quantifier, and `seqSet`{.Agda} collects
  all finite sequences over a set.
- `L.Coding.Tagged`{.Agda}: codes carrying their arity, so a clause for a
  quantifier can speak about its subformula's arity; `tagPairAt`{.Agda} matches
  the shape every binary constructor's code has.
- `L.Coding.Length`{.Agda}: the guard tying a certificate's arity component to
  the length of its environment; `lenAt-len`{.Agda} pins the number that would
  otherwise be free, which is what keeps junk out of the certificates.
- `L.Coding.Entry`{.Agda}: the single form `tripleInT`{.Agda} for "this arity,
  code and environment are recorded in this certificate", which every clause
  reads and writes its entries through.
- `L.Stage`{.Agda}: the least ordinal satisfying any property of ordinals, by
  well-founded descent and unique by trichotomy; the earliest stage containing a
  constructible set is its first instance, sealed so the descent never reaches a
  later conversion problem.
- `L.Axioms.Basic`{.Agda}: the first five model fields. Extensionality and
  regularity descend along transitivity; uniqueness then comes free; and the
  empty set, pairing and union are each carved out of one stage by one formula.
  `finSetL`{.Agda} generalizes the pairing argument to any finite family drawn
  from a stage, which is how a recursion's table of values reaches `L`.
- `L.Axioms.Separation`{.Agda}: separation and replacement for Δ₀ formulas, at a
  stage holding the argument and the formula's constants; the content is that
  membership in the carved set is satisfaction in the model.
- `L.Reflect`{.Agda}: Montague's argument, answering a class-sized existential
  inside a set. A **ladder** is an ascending chain of ordinals; if each rung's
  environments have their answering stages on the next, its limit reflects the
  existential for every tuple of parameters it contains. `Single`{.Agda} is the
  ladder for one matrix. Taking the least stage rather than the least witness is
  what keeps the well-ordering of L out of it.
- `L.ReflectFo`{.Agda}: the same for a whole formula, by structural induction. A
  jointly built ladder answers for every matrix of a formula at once, and
  `mkReflect`{.Agda} then names a stage at which the formula agrees with its
  relativization to it, trading arbitrary complexity for Δ₀ and a stage.
- `L.Axioms.Infinity`{.Agda}: the numeral chain inside `L`, pinned to the
  hierarchy's numerals by projection equations for the model's own pairing,
  union and successor.
<!--zh-->
## 第四部：可构造宇宙

- `FOL.Manipulation.Relabelling`{.Agda}：常量变换，一次三个海拔：函子式 `mapFo`{.Agda}，无参公式的入口 `embed`{.Agda}，含义纹丝不动 (`⊨-map`{.Agda}、`embed-⊨`{.Agda})，Lévy 见证随行 (`mapΔ₀`{.Agda} 及其塔)。
- `FOL.Manipulation.Bounding`{.Agda}：映射只是部分函数时的重标：`BoundedFo`{.Agda} 逐次出现地证明公式的常元满足某谓词，`BoundedFo-mono`{.Agda} 放宽它，而 `Relabel`{.Agda} 花掉它：证书就是沿部分映射重标的许可，含义与 Lévy 见证一并带过。
- `FOL.Coding`{.Agda}：语法作为集合：`⌜_⌝`{.Agda} 把构造子序号贴在各部分的码上 (常量编码自身)，而归纳关系 `Codes`{.Agda} 是接口，使码值不出现在类型检查器必须归一化的等式里。
- `V.Coding`{.Agda}：层级兑现编码的两组参数：数码单射 (`#-inj`{.Agda})、Kuratowski 对单射 (`pr-inj`{.Agda})，于是 `V` 上的公式成为 `V` 的集合。
- `L.Definability`{.Agda}：那一步：`Def A`，带 `A` 中参数可定义的 `A` 的子集之集：语法当索引集，内层满足给含义，本质小性买单；`A ∈ Def A` 恒成立，传递性下 `A ⊆ Def A`。
- `L.Constructible`{.Agda}：沿成员递归的塔 `Lset`{.Agda}，一条方程通吃零、后继与极限；层谓词 `isLayer`{.Agda} 与 `layer-trans`{.Agda}；类 `isL`{.Agda} 与结构 `𝒮ʟ`{.Agda}。
- `L.Ordinal`{.Agda}：闭包论证所需的序数供给：零、后继、小并皆序数，而 `boundingOrd`{.Agda} 以单一序数界住任一小族。不含比较，故不花费经典逻辑。
- `L.Rank`{.Agda}：沿成员递归的 von Neumann 秩，取值于层级自身：`rank-ord`{.Agda} 使它成为以序数进行的度量，`rank-fix`{.Agda} 认证它为典范索引。
- `L.Ordinal.Linear`{.Agda}：三歧 `ord-tri`{.Agda}，以及随之而来的 L 侧经典边界：闭包从不需要判定什么，比较则需要，故本章把排中律取作模块参数。
- `L.Ordinal.Stages`{.Agda}：`Lset α` 中的序数恰是 `α` 的成员：`rank-Lset`{.Agda} 与 `ord∈Lset→∈`{.Agda} 说无一提前现身，`ord∈Lset-suc`{.Agda} 说无一迟到。
- `L.WellOrder.Base`{.Agda}：作为束的严格良序 (`SWO`{.Agda})，与非空子集的极小元 (`leastOf`{.Agda})，经三歧唯一：反射与选择都会取用的那件选取装置。
- `L.Coding.Base`{.Agda}：从内部读码：`allCodes`{.Agda} 把每条无参公式的码汇成一个可命名的集合，而 `prAt`{.Agda} / `tagAt`{.Agda} 以有界形式解构 Kuratowski 对与标签，皆 Δ₀ 且适足。
- `L.Coding.Environment`{.Agda}：环境即其图，经 `lookup-spec`{.Agda} 而函数性；`memPairAt`{.Agda} 查出一个值，`sucAt`{.Agda} 认出量词之下的序号移位，`seqSet`{.Agda} 汇集一个集合上的全部有穷序列。
- `L.Coding.Tagged`{.Agda}：携带元数的码，使量词的子句能谈论其子公式的元数；`tagPairAt`{.Agda} 匹配每个二元构造子的码所具有的形状。
- `L.Coding.Length`{.Agda}：把证书的元数分量与其环境长度系住的守卫；`lenAt-len`{.Agda} 钉死那个本来自由的数，正是它把垃圾挡在诸证书之外。
- `L.Coding.Entry`{.Agda}：「这个元数、码与环境记录在这份证书里」的唯一形式 `tripleInT`{.Agda}，诸子句都经它读写自己的条目。
- `L.Stage`{.Agda}：满足任意序数性质的最小序数，经良基下降得到、经三歧而唯一；包含可构造集的最早阶段是它的头一个实例，已封印，故那次下降永不抵达日后的转换问题。
- `L.Axioms.Basic`{.Agda}：头五个模型字段。外延与正则沿传递性下降；唯一性随即白拿；空集、配对与并则各由一条公式从一个阶段中刻出。`finSetL`{.Agda} 把配对的论证推广到取自某阶段的任意有穷族，递归的取值表正是这样抵达 `L` 的。
- `L.Axioms.Separation`{.Agda}：Δ₀ 公式的分离与替换，在装下实参与公式全部常元的阶段上；其内容是「属于刻出的集合就是在模型中满足」。
- `L.Reflect`{.Agda}：Montague 的论证，在一个集合之内回答真类大小的存在量词。**梯**是上升的序数链；若每一级的环境其作答阶段都落在下一级上，则它的极限为自己包含的每个参数元组反射那个存在量词。`Single`{.Agda} 是单矩阵的梯。取最小阶段而非最小见证，正是把 L 的良序挡在门外的那一手。
- `L.ReflectFo`{.Agda}：整条公式的同一件事，经结构归纳。联合造出的梯一举为公式的每个矩阵作答，而 `mkReflect`{.Agda} 随即点名一个阶段，公式在其上与它到该阶段的相对化一致：以 Δ₀ 加一个阶段，换下任意的复杂度。
- `L.Axioms.Infinity`{.Agda}：`L` 内的数码链，经模型自家配对、并与后继的投影等式，钉在层级的数码上。
<!--/-->

```agda
import FOL.Manipulation.Relabelling
import FOL.Manipulation.Bounding
import FOL.Coding
import V.Coding
import L.Definability
import L.Constructible
import L.Ordinal
import L.Rank
import L.Ordinal.Linear
import L.Ordinal.Stages
import L.WellOrder.Base
import L.Coding.Base
import L.Coding.Environment
import L.Coding.Tagged
import L.Coding.Length
import L.Coding.Entry
import L.Stage
import L.Axioms.Basic
import L.Axioms.Separation
import L.Reflect
import L.ReflectFo
import L.Axioms.Full
import L.Absoluteness
import L.Coding.Model
import L.Recursion
import L.Axioms.Infinity
```

<!--en-->
The root, stated today and finished over the remaining parts:

- `L.Axioms.Full`{.Agda}: separation and replacement for arbitrary formulas, by
  reflecting the formula and applying the bounded instrument to its
  relativization; the confinement atom is what keeps replacement's image from
  escaping the stage.
- `L.Absoluteness`{.Agda}: the bridge between the two object languages. A Δ₀
  formula about the hierarchy whose constants are constructible is carried into
  the language of `L` by `liftFo`{.Agda}, and `transferFo`{.Agda} says the two
  say the same thing; the coding chapters stay on the hierarchy side and are
  quoted from here.
- `L.Coding.Model`{.Agda}: the readers quoted on the far side. `prAtL`{.Agda} says
  in the model's own language that one set is the ordered pair of two others,
  obtained by quoting rather than re-proving; the crossing costs one induction on
  environments and nothing else.
- `L.Recursion`{.Agda}: a function on a set of `L` whose graph is expressible has
  its table in `L`. A corollary of general-formula replacement, not a theorem: the
  usual absoluteness discipline exists to make a table readable *inside a stage*,
  and nothing here reads inside a stage. The recursion stays in the meta-language
  where it was written; `smallDom`{.Agda} supplies the domain for any small family,
  and `Definition`{.Agda} reduces an instance to a defining formula with its
  adequacy.
- `L.Frontier`{.Agda}: the debt registry, opened at eleven fields and down to
  two, each the verbatim
  statement of a model field at `𝒮ʟ`; proven fields get deleted, and the book
  is done when the record is empty.
- `L.Model`{.Agda}: the root chapter: the honest relative-consistency framing;
  extensionality and regularity descend along transitivity; `L⊨ZF`{.Agda} and
  `L⊨ZFC`{.Agda} assembled from the frontier.
<!--zh-->
根，今日陈述，余部完成：

- `L.Axioms.Full`{.Agda}：任意公式的分离与替换，办法是反射那条公式，再把有界的器械施于它的相对化；那个禁闭原子正是使替换的像逃不出阶段的东西。
- `L.Absoluteness`{.Agda}：两门对象语言之间的桥。常元可构造的、关于层级的 Δ₀ 公式，经 `liftFo`{.Agda} 运进 `L` 的语言，而 `transferFo`{.Agda} 说两者说的是同一件事；编码诸章留在层级一侧，从此处被引用。
- `L.Coding.Model`{.Agda}：诸读式在彼岸的引用。`prAtL`{.Agda} 用模型自己的语言说「这个集合是那两个的有序对」，由引用而非重证得来；这次过河只花一次关于环境的归纳，别无他物。
- `L.Recursion`{.Agda}：`L` 的集合上，图可表达的函数，其表在 `L` 中。这是任意公式替换的推论，而非定理：通常那套绝对性纪律是为了让一张表在**某个阶段之内**可读，而此处没有任何东西在阶段之内读。递归留在它被写下的元语言里；`smallDom`{.Agda} 为任意小族供给定义域，而 `Definition`{.Agda} 把一个实例归约为一条定义公式连同它的适足性。
- `L.Frontier`{.Agda}：债务登记簿，开张十一个字段，如今剩两个，每个都是模型字段在 `𝒮ʟ` 处的原文陈述；字段证毕即删，簿清则书成。
- `L.Model`{.Agda}：根章：诚实的相对一致性表述；外延与正则沿传递性下降；`L⊨ZF`{.Agda} 与 `L⊨ZFC`{.Agda} 由前沿合龙。
<!--/-->

```agda
import L.Frontier
import L.Model
```

<!--en-->
## Tools in waiting

Chapters with, as of today, no consumer anywhere in the trunk; their first
consumers arrive with Part 4's deeper machinery, and they read late so the main
line stays unbroken.

- `FOL.Manipulation.Renaming`{.Agda}: the book's entire variable calculus: `renameFo`{.Agda} on
  syntax, and the one correctness theorem `⊨-rename`{.Agda} covering weakening,
  exchange, and contraction.
- `FOL.Manipulation.Relativize`{.Agda}: tightening unbounded quantifiers to a constant bound,
  Δ₀ witness included, with the correctness equation.
<!--zh-->
## 候用的工具

这几章至今在主干上没有任何消费者；它们的首批消费者随第四部的深层机器到来，读在靠后，好让主线不断。

- `FOL.Manipulation.Renaming`{.Agda}：变量变换，本书全部的变量演算：语法上的 `renameFo`{.Agda}，与一条通吃弱化、交换、收缩的正确性定理 `⊨-rename`{.Agda}。
- `FOL.Manipulation.Relativize`{.Agda}：把无界量词收紧到常量界，Δ₀ 见证随附，并给出正确性等式。
<!--/-->

```agda
import FOL.Manipulation.Renaming
import FOL.Manipulation.Relativize
```

<!--en-->
## The reification framework (in waiting)

The formula factory proper: manufacture, from a host predicate, a formula
certified to mean it. Nothing in the trunk consumes the line yet; it closes the
catalog, ready for the chapters that will run it at scale.

- `FOL.Reification.Base`{.Agda}: representation, the bridge: a formula paired with
  its adequacy certificate; `translate`{.Agda} and `adequacy`{.Agda} as the only
  exits.
- `FOL.Reification.Combinators`{.Agda}: the assembly line: one combinator per
  constructor, every certificate a single congruence.
- `FOL.Reification.Certified`{.Agda}: the graded tier: representations carrying a
  Δ₀ witness alongside adequacy (`RepΔ₀`{.Agda}), the graded combinators,
  and `transfer`{.Agda}, composing adequacy with absoluteness into the
  framework's working currency.
<!--zh-->
## Reification 框架 (候用)

公式工厂本尊：从宿主谓词制造经认证与之同义的公式。主干至今没有消费这条线；它收束全目录，静候将来大规模开动它的章节。

- `FOL.Reification.Base`{.Agda}：表示，即那座桥：公式配上其适足性证书；`translate`{.Agda} 与 `adequacy`{.Agda} 是仅有的出口。
- `FOL.Reification.Combinators`{.Agda}：流水线：一构造子一组合子，每张证书一次同余。
- `FOL.Reification.Certified`{.Agda}：分级层：Δ₀ 见证与适足性并肩的表示 (`RepΔ₀`{.Agda})、分级组合子，与把适足性同绝对性复合成框架流通货币的 `transfer`{.Agda}。
<!--/-->

```agda
import FOL.Reification.Base
import FOL.Reification.Combinators
import FOL.Reification.Certified
```

