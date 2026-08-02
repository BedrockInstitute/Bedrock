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
  bills, `V⊨ZF`{.Agda} (and its classical redemption), `V⊨ZFC`{.Agda}, and
  `L⊨ZFC`{.Agda}, each hypothesis spelled in the name.
  Read it first to see the destination; understanding the signatures is what
  the rest of the book is for.
<!--zh-->
## 地标：本书的终点

- `Landmarks`{.Agda}：奖杯陈列室，摆在入口处：里程碑定理以自足签名重述，假设账单全额陈列：`V⊨ZF`{.Agda} (及其精确价格版 `V⊨ZF-impredicative`{.Agda})、单凭选择的 `V⊨ZFC`{.Agda}，与 `L⊨ZFC`{.Agda}。先读它，看清目的地；至于读懂这些签名，正是全书其余部分的任务。
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
- `FOL.Manipulation.Parameters`{.Agda}: constants out of the syntax and into the
  environment. They are counted (`countFo`{.Agda}) and collected
  (`constantsFo`{.Agda}) **by occurrence, not by value**, which is what makes a
  decidable equality on the constant domain unnecessary; `placeFo`{.Agda} puts
  each occurrence at the variable a placement names, in one pass and with no
  weakening lemma, and `absFo`{.Agda} instantiates it to the abstraction proper,
  raising the arity by the occurrence count and returning a parameter-free
  formula. `⊨-abs`{.Agda} certifies that the trade costs no meaning, and
  `⊨-abs₁`{.Agda} with `asPure₁`{.Agda} spend it at the arity a subset is carved
  by: a definable subset is carved by a parameter-free formula at a parameter
  vector, read in the inner semantics the definable powerset is defined by.
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
  trichotomy: the choosing device the axiom of choice takes. Reflection was
  expected to be a second consumer and is not, so there is exactly one, and it is
  `L.Choice.Transversal`{.Agda}, the last chapter of the book.
- `L.WellOrder.Tree`{.Agda}: a classical well-order, generic: the finite
  labelled trees over a well-ordered alphabet, by shortlex. The size and
  length gates are load-bearing, since the pure pointwise order on lists of
  unequal length admits an infinite descent, and well-foundedness runs by
  strong induction on size with nested accessibility inductions inside each
  size class.
- `L.Coding.Base`{.Agda}: reading codes from inside: `allCodes`{.Agda} gathers
  every parameter-free formula's code into one nameable set, and
  `prAt`{.Agda} / `tagAt`{.Agda} destructure a Kuratowski pair and a tag in
  bounded form, Δ₀ and adequate.
- `L.Coding.Environment`{.Agda}: environments as their graphs, functional by
  `lookup-spec`{.Agda}; `memPairAt`{.Agda} reads a value, `sucAt`{.Agda}
  recognizes the index shift under a quantifier, and `seqSet`{.Agda} collects
  all finite sequences over a set.
- `L.Stage`{.Agda}: the least ordinal satisfying any property of ordinals, by
  well-founded descent and unique by trichotomy; the earliest stage containing a
  constructible set is its first instance, sealed so the descent never reaches a
  later conversion problem.
- `L.Axioms.Basic`{.Agda}: the first five model fields. Extensionality and
  regularity descend along transitivity; uniqueness then comes free; and the
  empty set, pairing and union are each carved out of one stage by one formula.
  `finSetL`{.Agda} generalizes the pairing argument to any finite family drawn
  from a stage, which is how a recursion's table of values reaches `L`.
  `Lset-suc`{.Agda} identifies the successor stage with the definable powerset
  of its predecessor, which is what puts that powerset in `L` as `𝒟ₒS`{.Agda}.
  Pairing's carving is stated on its own as a fact about the tower:
  `pair∈Lset-suc`{.Agda} puts the unordered pair of two members of a stage in
  the next stage, and `pr∈Lset-suc`{.Agda} the ordered pair two stages up, which
  is what places anything written with ordered pairs at a stage at all.
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
- `L.Axioms.Numerals`{.Agda}: the numeral chain inside `L`, pinned to the
  hierarchy's numerals by projection equations. Entirely constructive, which is
  why it is separate: the excluded middle enters infinity only at the collection
  step.
- `L.Axioms.Infinity`{.Agda}: the numeral chain inside `L`, pinned to the
  hierarchy's numerals by projection equations for the model's own pairing,
  union and successor.
<!--zh-->
## 第四部：可构造宇宙

- `FOL.Manipulation.Relabelling`{.Agda}：常量变换，一次三个海拔：函子式 `mapFo`{.Agda}，无参公式的入口 `embed`{.Agda}，含义纹丝不动 (`⊨-map`{.Agda}、`embed-⊨`{.Agda})，Lévy 见证随行 (`mapΔ₀`{.Agda} 及其塔)。
- `FOL.Manipulation.Bounding`{.Agda}：映射只是部分函数时的重标：`BoundedFo`{.Agda} 逐次出现地证明公式的常元满足某谓词，`BoundedFo-mono`{.Agda} 放宽它，而 `Relabel`{.Agda} 花掉它：证书就是沿部分映射重标的许可，含义与 Lévy 见证一并带过。
- `FOL.Manipulation.Parameters`{.Agda}：把常量请出语法、请进环境。它们**按出现而非按取值**计数 (`countFo`{.Agda}) 并收集 (`constantsFo`{.Agda})，这正是常量域上的可判定相等变得不必要的原因；`placeFo`{.Agda} 把每次出现放到安置所点名的变量处，只走一趟，也不需要弱化引理，而 `absFo`{.Agda} 把它实例化为名副其实的抽象：按出现次数抬高元数，交出一条无参公式。`⊨-abs`{.Agda} 认证这笔交易不花含义，`⊨-abs₁`{.Agda} 与 `asPure₁`{.Agda} 则在「子集被刻出时所用的元数」处把它花掉：可定义子集由一条无参公式在一个参数向量处刻出，且读在可定义幂集据以定义的那套内层语义中。
- `FOL.Coding`{.Agda}：语法作为集合：`⌜_⌝`{.Agda} 把构造子序号贴在各部分的码上 (常量编码自身)，而归纳关系 `Codes`{.Agda} 是接口，使码值不出现在类型检查器必须归一化的等式里。
- `V.Coding`{.Agda}：层级兑现编码的两组参数：数码单射 (`#-inj`{.Agda})、Kuratowski 对单射 (`pr-inj`{.Agda})，于是 `V` 上的公式成为 `V` 的集合。
- `L.Definability`{.Agda}：那一步：`Def A`，带 `A` 中参数可定义的 `A` 的子集之集：语法当索引集，内层满足给含义，本质小性买单；`A ∈ Def A` 恒成立，传递性下 `A ⊆ Def A`。
- `L.Constructible`{.Agda}：沿成员递归的塔 `Lset`{.Agda}，一条方程通吃零、后继与极限；层谓词 `isLayer`{.Agda} 与 `layer-trans`{.Agda}；类 `isL`{.Agda} 与结构 `𝒮ʟ`{.Agda}。
- `L.Ordinal`{.Agda}：闭包论证所需的序数供给：零、后继、小并皆序数，而 `boundingOrd`{.Agda} 以单一序数界住任一小族。不含比较，故不花费经典逻辑。
- `L.Rank`{.Agda}：沿成员递归的 von Neumann 秩，取值于层级自身：`rank-ord`{.Agda} 使它成为以序数进行的度量，`rank-fix`{.Agda} 认证它为典范索引。
- `L.Ordinal.Linear`{.Agda}：三歧 `ord-tri`{.Agda}，以及随之而来的 L 侧经典边界：闭包从不需要判定什么，比较则需要，故本章把排中律取作模块参数。
- `L.Ordinal.Stages`{.Agda}：`Lset α` 中的序数恰是 `α` 的成员：`rank-Lset`{.Agda} 与 `ord∈Lset→∈`{.Agda} 说无一提前现身，`ord∈Lset-suc`{.Agda} 说无一迟到。
- `L.WellOrder.Base`{.Agda}：作为束的严格良序 (`SWO`{.Agda})，与非空子集的极小元 (`leastOf`{.Agda})，经三歧唯一：选择公理将要取用的那件选取装置。反射本来预期是第二个消费方，结果不是，故恰有一个，那就是本书的最后一章 `L.Choice.Transversal`{.Agda}。
- `L.WellOrder.Tree`{.Agda}：一个经典良序，且泛型：良序字母表上的有穷带标签树，按 shortlex。尺寸门与长度门是承重的，因为变长表上的纯逐点序容许无穷下降；良基性对尺寸作强归纳，每个尺寸类内部再嵌可及性归纳。
- `L.Coding.Base`{.Agda}：从内部读码：`allCodes`{.Agda} 把每条无参公式的码汇成一个可命名的集合，而 `prAt`{.Agda} / `tagAt`{.Agda} 以有界形式解构 Kuratowski 对与标签，皆 Δ₀ 且适足。
- `L.Coding.Environment`{.Agda}：环境即其图，经 `lookup-spec`{.Agda} 而函数性；`memPairAt`{.Agda} 查出一个值，`sucAt`{.Agda} 认出量词之下的序号移位，`seqSet`{.Agda} 汇集一个集合上的全部有穷序列。
- `L.Stage`{.Agda}：满足任意序数性质的最小序数，经良基下降得到、经三歧而唯一；包含可构造集的最早阶段是它的头一个实例，已封印，故那次下降永不抵达日后的转换问题。
- `L.Axioms.Basic`{.Agda}：头五个模型字段。外延与正则沿传递性下降；唯一性随即白拿；空集、配对与并则各由一条公式从一个阶段中刻出。`finSetL`{.Agda} 把配对的论证推广到取自某阶段的任意有穷族，递归的取值表正是这样抵达 `L` 的。`Lset-suc`{.Agda} 把后继阶段与前一阶段的可定义幂集认同，正是这一点把那个幂集作为 `𝒟ₒS`{.Agda} 放进 `L`。配对那次雕刻也单独陈述为关于塔的事实：`pair∈Lset-suc`{.Agda} 把一个阶段的两个成员的无序对放进下一个阶段，`pr∈Lset-suc`{.Agda} 把有序对放到高两个阶段处，而这也正是以有序对写成的任何东西根本得以安置在某个阶段上的原因。
- `L.Axioms.Separation`{.Agda}：Δ₀ 公式的分离与替换，在装下实参与公式全部常元的阶段上；其内容是「属于刻出的集合就是在模型中满足」。
- `L.Reflect`{.Agda}：Montague 的论证，在一个集合之内回答真类大小的存在量词。**梯**是上升的序数链；若每一级的环境其作答阶段都落在下一级上，则它的极限为自己包含的每个参数元组反射那个存在量词。`Single`{.Agda} 是单矩阵的梯。取最小阶段而非最小见证，正是把 L 的良序挡在门外的那一手。
- `L.ReflectFo`{.Agda}：整条公式的同一件事，经结构归纳。联合造出的梯一举为公式的每个矩阵作答，而 `mkReflect`{.Agda} 随即点名一个阶段，公式在其上与它到该阶段的相对化一致：以 Δ₀ 加一个阶段，换下任意的复杂度。
- `L.Axioms.Numerals`{.Agda}：`L` 之内的数码链，经投影等式钉在层级的数码上。全然构造性，这正是它独立成章的理由：排中律只在收集那一步进入无穷公理。
- `L.Axioms.Infinity`{.Agda}：`L` 内的数码链，经模型自家配对、并与后继的投影等式，钉在层级的数码上。
<!--/-->

```agda
import FOL.Manipulation.Relabelling
import FOL.Manipulation.Bounding
import FOL.Manipulation.Parameters
import FOL.Coding
import V.Coding
import L.Definability
import L.Constructible
import L.Ordinal
import L.Rank
import L.Ordinal.Linear
import L.Ordinal.Stages
import L.WellOrder.Base
import L.WellOrder.Tree
import L.Coding.Base
import L.Coding.Environment
import L.Stage
import L.Axioms.Basic
import L.Axioms.Separation
import L.Reflect
import L.ReflectFo
import L.Axioms.Full
import L.Axioms.Power
import L.Absoluteness
import L.Coding.Model
import L.Coding.InL
import L.Coding.Closed
import L.Recursion
import L.Godel.Operations
import L.Godel.Definable
import L.Godel.Tuples
import L.Godel.Satisfaction
import L.Godel.Terms
import L.Godel.NormalForm
import L.Godel.InL
import L.Godel.Codes
import L.Godel.Table
import L.Godel.Name
import L.Godel.Step
import L.Godel.Tower
import L.Godel.Closure
import L.Godel.Levels
import L.Coding.EnvSet
import L.Coding.Sat
import L.Coding.Bridge
import L.Coding.Table
import L.Coding.Sound
import L.Coding.Unique
import L.Coding.Slot
import L.Coding.Descent
import L.Coding.Shape
import L.Coding.Recover
import L.Coding.CodeSet
import L.Coding.Graph
import L.Coding.Uniform
import L.Coding.Powerset
import L.Coding.Sequence
import L.Hierarchy
import L.Axioms.Numerals
import L.Axioms.Infinity
import L.Choice.Stage
import L.Choice.Finite
import L.Choice.Name
import L.Choice.Step
import L.Choice.Internal
import L.Choice.Table
import L.Choice.Faithful
import L.Choice.Adequate
import L.Choice.Limit
import L.Choice.Before
import L.Choice.Order
import L.Choice.Transversal
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
- `L.Coding.Model`{.Agda}: the object language over the model. What "function"
  means (`prAtL`{.Agda}, `appAt`{.Agda}, `svAt`{.Agda}, `domAt`{.Agda}), the pair
  on the value side, the tag readers, environments, and `extAt`{.Agda}, the frame
  every set-valued clause is written in, whose two readings are its two
  projections. Constant-free readers are quoted through the bridge; readers naming
  a numeral are written fresh, since unbounded is now free.
- `L.Coding.InL`{.Agda}: every code is an element of `L`, by one induction over
  the constructors with nothing in it. That is what lets a code be named as a
  constant of the model's object language, and a family of codes be the domain of
  an internalized recursion. The set of *all* codes is deliberately not proved to
  be one, and is not needed here. Also `closure`{.Agda}, the finite set of a
  formula's subformula keys, `closure-inv`{.Agda} reading it back, and
  `byTag`{.Agda}, which matches the twelve constructors against the eight demands
  a closedness predicate makes, once rather than twelve times eight.
- `L.Coding.Closed`{.Agda}: the closure satisfies the object language's
  closedness predicate, and is the least set that does. Eight instances of four
  readers, then one induction; the hypothesis a recursion over the subcodes of a
  formula needs about its index set, and the reason its value is unique. The eight
  clauses never look at a formula, so they are proved once for any set that
  **peels** (`Peel`{.Agda}: a member is merely the key of a formula whose own
  closure sits inside), and `closureClosed`{.Agda} is `closedOf`{.Agda} at a
  closure with `closure-inv`{.Agda} as its peeling. Generality is free because
  `byTag`{.Agda} was already written against an arbitrary target set.
- `L.Godel.Operations`{.Agda}: a finite stock of set operations, each a single
  set former with its two membership directions, and none of it owing the
  excluded middle: product and membership graph, the direct-former union and
  the difference, the two selections at parameter keys, and the extension and
  shift of recorded assignments. Later chapters compose them where formulas
  would otherwise be spent.
- `L.Godel.Definable`{.Agda}: the operations, described. One frame turns a body
  and two semantic conversions into an identity between a slot and an
  operation's value; eleven descriptions pass through it (the Boolean stock,
  product and the membership graph, the two selections at singleton keys, the
  values, the tuple family at an arity slot, and the two graph movers), each
  read in both directions at variable slots and a variable environment.
- `L.Godel.Tuples`{.Agda}: assignments as graph sets, and their algebra against
  the operations: extension is the graph extension, dropping the head is the
  shift, entrywise injectivity reads one graph against the other's lookup, and
  the family of all assignments over a carrier steps by the family extension.
- `L.Godel.Satisfaction`{.Agda}: satisfaction as a set, case by case. The
  satisfaction set of a formula is one set former over the assignments
  satisfying it, and each delivered case is an extensional identity with an
  operation composition: falsity and truth, conjunction, disjunction and
  negation against the Boolean stock, the two-variable membership atom
  against one selection, and the existential against the shift.
- `L.Godel.Terms`{.Agda}: the combinator terms, the syntax the tower will
  quantify. A term mirrors a formula constructor for constructor but means
  through one set operation per node, with no binders; soundness reads every
  term back as the satisfaction set of its mirror by the case equations run
  backward, and completeness assigns every formula a term through the
  reductions, under the one classical assumption.
- `L.Godel.NormalForm`{.Agda}: the normal form. Every satisfaction set over a
  carrier is denoted by a finite composition term over the carrier and its
  members: one induction, each case a case equation of the satisfaction
  chapter read off, the atoms assembled as leaves through the reductions,
  and the one classical assumption entering only where it already had to.
- `L.Godel.InL`{.Agda}: fed constructible arguments, the operations return
  constructible sets, capped by `denoteL`{.Agda}: every denotation of every
  combinator term over a constructible carrier is constructible. One engine
  throughout: a stage holding the arguments, one Δ₀ defining formula per
  operation read at the outer world through absoluteness, and the
  definable-subset door back into the class; the two movers first climb a
  fixed count of stages.
- `L.Godel.Codes`{.Agda}: the syntax as data the model holds. Subterm
  enumeration with arities packed in, then a hereditarily finite code per
  term as a tag-and-pair tower over the sealed numeral chain, an element of
  `L` by construction, with one unfolding equation per constructor and the
  tag discrimination helpers the recorded law prescribes.
- `L.Godel.Table`{.Agda}: the denotation table's clauses, one per constructor:
  the code has this tag and payload, the children's entries are present, and
  the value is the operation of the children's values, every conjunct read
  through the descriptions and pair readers already in stock. Each clause
  carries a meta shape and both readings; the binary nodes share one frame.
- `L.Godel.Name`{.Agda}: names for the members of a stage, as arity-one terms.
  Denotation is evaluation followed by taking values, completeness spends the
  terms chapter's identification as one transport, and the well-order is
  assembled rather than invented: a label alphabet by the combinators, trees
  ordered shortlex, and the tree order pulled back along a picture whose
  injectivity is a left inverse rather than a discrimination matrix. The
  exported interface matches the internalized route's chapter member for
  member.
- `L.Godel.Step`{.Agda}: deliberate scaffolding, said so in place. The choice
  step's spine, line for line, with its naming import re-pointed at the term
  names, so that both routes stay green side by side while the term route's
  internal side is built against this one; at the final rewire one copy
  retires.
- `L.Godel.Tower`{.Agda}: the tower's step, described from the inside. A naked
  existential over approximation tables admits junk, so the step quantifies
  certified tables: eight local branch shapes pin tags by sealed numerals,
  payloads into ω or the carrier, children into the main table, and
  annotations into one functional table. Honesty reads every certified pair
  back as the code of an honest term, on the transitive closure of
  membership; the fill certifies the honest pair of tables by the
  approximation's own recursion, with functionality exactly the fact that a
  code determines its arity; and the step body's two laws read the arity-one
  entries' values into `𝒟ₒ` of the carrier and fill them back, so the tower's
  step is internally describable, both ways, over codes and tables.
- `L.Godel.Closure`{.Agda}: the closure, opened. The meta groundwork the
  kinded closure tower will spend: the values generalization at every positive
  arity, the two selection equations reading a selection over a satisfaction
  set as one more conjunction, the renaming law saying a satisfaction set
  survives a shift of all variables, the forward pinning inclusion cutting the
  full extension down to the constant's singleton, and the singleton family,
  the one operation the stock was missing, with its membership laws. The
  closure recursion itself is the next chapter's work.
- `L.Godel.Levels`{.Agda}: the levels, internalized. The internal face of the
  shelves is a finite prefix table: one set of entries `pr (pr #n #k) S` up to
  a bound, determined shelf by shelf. The layer description spells the step's
  full nine-clause set over slots, with direction-paired readers; the prefix
  table description adds functionality, the two base clauses, the successor
  clause (the entry at `suc n` is the entry at `n` joined with the layer), and
  domain adequacy. The pinning theorem excludes junk by meta-induction: any
  satisfying table's entries are the meta `slice` values, so no certificate is
  needed. The fill packs the meta prefix table as an `L`-set, and the step is
  describable both ways over the prefix table.
- `L.Coding.EnvSet`{.Agda}: the environments over a set of `L` at a fixed length
  form a set of `L`, which is what the clauses that take a complement take it in.
  A small index type, one stage, one separation, and no recursion.
- `L.Coding.Sat`{.Agda}: for a formula of the meta-language and a carrier, the set
  of environments satisfying it, by recursion on the formula. Nothing internal:
  each step names the previous steps' sets as constants, so each is one
  separation off the ambient set, and the internal clauses become identities
  rather than definitions. Exports the twelve values and their membership
  equations, and nothing else.
- `L.Coding.Bridge`{.Agda}: what that value **is**. At every environment over the
  carrier, membership in it is satisfaction in the world `(B, ∈)`, which is the
  notion the definable powerset is defined by; without the statement an internal
  `Def` read off the recursion would provably agree with nothing. The right-hand
  side is the inner semantics, not the ambient reading of the relativization,
  because only the inner one guards a bounded quantifier twice, as the condition
  does. `defSet-Sat`{.Agda} spends it on `L.Definability`{.Agda} directly. The
  registered coherence risk does not fire: indexing the bridge by the inner
  environment vector makes a quantifier's extension consing on the underlying
  family, so the coherence is two `refl`{.Agda} branches shared by all four
  quantifier clauses, and the truncated recovery is confined to the corollary
  that a member is nothing but an environment.
- `L.Coding.Table`{.Agda}: the entries, one per subformula, and the two things a
  recursion wants of them: every member is an entry, and a key determines its
  value. The second is where the code equation's injectivity is spent, and the
  arity is eliminated by path induction so the equation is used at the single
  arity where it holds. Everything is an element of the model by construction,
  since the codes are the model's own.
- `L.Coding.Sound`{.Agda}: the table satisfies the clauses, one at a time. Each
  verification is four moves and three are already built; what is left is a set
  identity, and those are cheap because the meta-level recursion defined its
  value by the very condition the identity reads back.
- `L.Coding.Unique`{.Agda}: a table satisfying the twelve clauses over a
  subcode-closed index records at each key the value the recursion built there,
  which is what makes the graph single-valued. Stated against the canonical value
  and with the index a variable, because a key substituted into a satisfaction
  does not typecheck in any reasonable time.
- `L.Coding.Slot`{.Agda}: the slot a formula's recursion is indexed by satisfies
  the object language's closedness predicate, which is the hypothesis the
  satisfaction graph states about its index set. The closure chapter's theorem
  again, on the model's own coding.
- `L.Coding.Descent`{.Agda}: how a recursion on codes gets from a code to its
  parts, which membership will not do: Kuratowski's pair puts a part four
  membership steps down and the sets in between are not codes. Rank increases
  strictly along membership, so the four steps compose by transitivity of
  ordinals and the recursion runs on the rank instead.
- `L.Coding.Shape`{.Agda}: the half of "is a code" that closedness does not say.
  Closedness is eight implications keyed by tag, so a member with no recognized
  tag satisfies all eight vacuously; `shapedAt`{.Agda} says every member is an
  arity-tagged pair whose tag is one of the twelve, with the payload that tag
  calls for. Two frames carry the twelve, because twelve tags have two payload
  shapes between them; what else a tag demands is a relation the frame carries,
  and `isTmAt`{.Agda} is the one such demand that is not about a formula code.
  Shapedness is stated at **two** slots, the set and a carrier, because a term
  has two things to bound and they are different: a variable's index by the
  arity numeral, a constant by membership in the carrier. The second is what
  makes a member the key of a formula over that carrier rather than over the
  model, and it is written at a slot rather than as a constant so that nothing
  below is re-indexed. `isTmAt-decode`{.Agda} recovers the term over any
  alphabet, which is the first decode and the only one needing no induction; its
  constant clause needs one thing the predicate cannot supply, that the carrier's
  members are the alphabet's image, and takes it as a hypothesis.
  `Peel.peel`{.Agda} is the two halves meeting: shapedness says which
  of the twelve a member is and hands back its parts, closedness says those
  parts are members too at the arity the tag calls for, and neither alone is a
  step of a recursion. The other direction is owed as well, since a predicate
  written to be consumed proves nothing until something satisfies it:
  `shaped-in`{.Agda} builds the twelve-fold disjunction from one choice per
  member, and `closureShaped`{.Agda} spends it on the closure of a formula,
  which is the second hypothesis the decode's first caller owes. A measurement
  worth keeping: the two disjuncts of `isTmAt`{.Agda} are read by two named
  lemmas, and inlined as two clauses of one function the chapter does not finish
  in ten minutes, because a branch whose type is inferred is solved against the
  whole disjunction rather than against its own disjunct.
- `L.Coding.Recover`{.Agda}: the decode. In a set that is closed and shaped at a
  carrier, a member handed over as a key at a stated arity is the key of a
  formula **over that carrier**, and `Decode.recover`{.Agda} produces it. The
  alphabet is a parameter and the target is stated over it, because the consumer
  indexes by the formulas over one carrier and a formula over the model would be
  useless to it. That also makes the six frames *shorter*: over the model each
  had to bridge the model's coding to the hierarchy's before comparing a code
  with a payload, and over the alphabet the code already is an element of the
  hierarchy. That *every* member is such a key is not
  proved here and is owed by whoever builds the set, since shapedness puts no
  condition on the arity component it binds. The recursion runs on the rank of the code, not on the code and not on
  the key: not on the code because membership does not descend into a
  Kuratowski pair, not on the key because rank arithmetic on a pair is a fact
  nobody has proved. The arity rides alongside as a natural number, which is what
  lets the induction come back at the larger one a quantifier raises it to; the
  carrier is not quantified over at all, being a slot fixed before the induction
  starts. Six
  frames carry the twelve cases, and each takes its constructor's coding equation
  as a hypothesis, because with the constructor a variable the coding function
  does not reduce and finding that equation is the whole cost. Over the alphabet
  those twelve equations are still `refl`{.Agda}, since relabelling commutes with
  every constructor definitionally.
- `L.Coding.CodeSet`{.Agda}: the codes at a carrier, as sets of `L`, one at arity
  one and one at every arity. `smallDom`{.Agda} contains the keys in a stage and
  general-formula separation cuts them back, so the chapter is two object-language
  predicates that differ in one conjunct. The shared conjunct, "there merely is a
  carrier equal to `A` and a closed set shaped at it holding this", is unbounded
  existentials and free here; the carrier is a **slot** in `hasWitnessAt`{.Agda}
  and becomes a constant only one binder up, in `hasWitness`{.Agda}, which pins it
  with `var zero ≐ con A`{.Agda}. That split is forced by the consumer: the
  internal hierarchy binds its stage, and a set enters a formula only by being
  named, so a predicate that names its carrier cannot be spoken under that binder
  at all. The conjunct that
  differs says the member is a pair whose first component is a numeral, and it
  exists because `recover`{.Agda} takes its argument **as a key at a stated arity**
  while neither `closedAt`{.Agda} nor `shapedAt`{.Agda} constrains the arity slot:
  shapedness binds it existentially with no condition, so the set must pin it from
  outside. `isCode`{.Agda} names the numeral one; `isCodeAny`{.Agda} binds the
  arity and asks only that it lie in `ωʟ`{.Agda}, which reads back without an
  induction because `ω-specL`{.Agda} is an equation and the numeral chain projects.
  **`Codes-spec`{.Agda} and `AllCodes-spec`{.Agda} close both round trips**: a
  member is *exactly* a key of a formula over the carrier, at arity one and at some
  arity respectively, so both sets are characterized rather than caught between two
  statements. The all-arity set exists for the class it characterizes: a recursion
  over codes answers at a code's subcodes, a quantifier's subformula lives one
  arity up, and the arity-one class does not contain it, so it cannot be a domain.
- `L.Coding.Uniform`{.Agda}: satisfaction as an internalized recursion over
  **the codes at a stage**,
  which is the domain every consumer wants: one formula's slot gives a table per
  formula, and a consumer arrives holding a code, not a formula it is a subcode
  of. `AllCodes`{.Agda} is the domain, and nothing else moves, because the graph
  binds its table
  **existentially**: `funct`{.Agda} need only exhibit *some* admissible table
  holding the member, and the smallest is the subformula slot of the member's own
  formula. So `Table`{.Agda}, `Slot`{.Agda}, `Sound`{.Agda} and `Unique`{.Agda}
  are applied at their existing types and the registered re-indexing at
  (carrier, key) never happens. The one new thing bridges the two codings, the
  hierarchy's over the stage's alphabet and the model's over the model's
  language: `codeBridge`{.Agda}, written for this and unused until now, plus
  functoriality of relabelling. `val-at`{.Agda} reads the value out at a member
  given as a key, `val-sat`{.Agda} says that value **is** satisfaction over the
  carrier, and `val-defSet`{.Agda} lands it on the definable powerset at arity
  one. The code carrier and the environment carrier stay independent parameters,
  and are pinned together only where satisfaction has a meaning. Every reading
  takes the member as a **variable** with its key equation beside it, and the
  name a consumer would write instead, `keyIn`{.Agda}, is sealed where it is
  built: written out, the key's construction lands inside a satisfaction and no
  length of proof elaborates.
- `L.Coding.Graph`{.Agda}: what the satisfaction recursion's graph says. Three
  existentials over the index set, the table and the carrier, guarded by
  closedness, totality and the twelve clauses, with the value read off the table.
  Everything is bound because a graph may not name a table it has not been given,
  which is the one thing the internalization theorem forbids. One frame with two
  instances, because the pinning clause is the frame's parameter:
  `satGraphAt`{.Agda} takes the carrier as a **slot**, for a consumer whose carrier
  is itself a bound variable, and `satGraph`{.Agda} pins it to a constant, at the
  type and the witness tuple it always had.
- `L.Coding.Powerset`{.Agda}: the definable powerset described in the object
  language at a carrier that is a **slot**, and the step the whole route exists
  for. The internal hierarchy binds its stage, so a description that names its
  carrier cannot be spoken there at all; `DefAt`{.Agda} names nothing. It says
  that `u` is the set of exactly those `x` for which there merely are a code `c`
  over the carrier and a value `v`, with `v` what the satisfaction recursion
  records at `c` and `x` the set of members of the carrier whose one-entry
  environment lies in `v`. The two existentials are **adjacent**, which is a
  correction a probe forced: separated by a conjunct, the code hypothesis and the
  satisfaction hypothesis land at different environments and the route acquires a
  weakening lemma it otherwise never needs. `DefinesAt`{.Agda} is the third
  conjunct alone and `envOneAt`{.Agda} the one-entry environment, one line
  because a graph of length one is a single pair. `DefAt-in`{.Agda} says the
  operator satisfies the description and `DefAt-out`{.Agda} that nothing else
  does, the second under `DefOK`{.Agda}: every existential in the description
  ranges over `L` and can reach only what lives there, so the description is
  adequate exactly where the carrier's definable subsets are constructible. That
  side condition is a hypothesis of the elimination alone, since the
  introduction's own hypothesis implies it, and at a stage it is discharged for
  good by the successor identity, leaving `DefAt-stage`{.Agda}: an equation of
  truth values saying the description holds of `𝒟ₒS`{.Agda} and of nothing else.
- `L.Coding.Sequence`{.Agda}: the hierarchy said as a **sequence**, which is the
  only shape a graph for it may take. A graph may not name the object it defines
  and the tower at a stage is built from the tower below it, so what is written
  instead is what an *approximation* is. `StepAt`{.Agda} is the step at an
  argument: one `extAt`{.Agda} over three adjacent existentials, the argument,
  the value the approximation records there, and its definable powerset, the last
  bound rather than named because the previous chapter delivers a description of
  it and not a term for it. One `extAt`{.Agda} rather than a hand-made pair of
  inclusions, because a pair would duplicate the three existentials and hand
  every reading back in two halves that are not each other's inverse. One side
  condition `PowOK`{.Agda} serves both directions, since a definable powerset
  that is an element of `L` is one whose members are constructible.
  `ApproxAt`{.Agda} is two conjuncts and no more: `f` is defined exactly on the
  argument's members, and every value it records is the step there computed from
  `f` itself. It is a membership **equivalence** rather than a one-directional
  collection, which keeps the coming induction's motive a proposition and removes
  an internal function-extensionality lemma from the route; and it carries **no
  single-valuedness conjunct**, because the step condition already pins every
  value recorded at an argument, so single-valuedness is a corollary rather than
  three universal quantifiers under a satisfaction. `LsetGraph`{.Agda} binds the
  approximation over the two. **The chapter's entire price was conversion**: its
  two graph readings stated at concrete slots cost 98 seconds of 130, and each
  place where a hypothesis wrote an environment out while the application named
  it behind an abbreviation cost 15 more. Written so that the two sides are the
  same expression it checks in under two seconds, which extends the
  variable-argument law from a substitution to a **statement**.
- `L.Hierarchy`{.Agda}: the graph of the last chapter proved against the tower
  the book actually built, and the **internal hierarchy** it is proved with.
  A *table* is a set of ordered pairs; it is correct on a set when every value it
  records below that set is the meta tower there, and complete when it records
  one at every argument below. `step-Lset`{.Agda} reads a satisfied step off a
  correct table and gets the tower back, `step-table`{.Agda} writes the step from
  it, and the previous chapter's side condition is discharged inside both, since
  a recorded value is the tower at an ordinal and the definable powerset of a
  stage is constructible. `approx-val`{.Agda} is one membership induction on the
  argument whose motive quantifies over **all** recorded values, so
  single-valuedness is never a hypothesis and `approx-uniq`{.Agda} falls out in
  three lines. `Lset-only`{.Agda} and `Lset-defines`{.Agda} are the graph's two
  directions, and `hierL`{.Agda} is what the second is built from: the set of
  pairs of an ordinal with the tower's value at it, collected by replacement over
  a *pair graph*, with ordinality of each index taken from `mem-ord`{.Agda}
  untruncated and functionality filled through `mereFunct`{.Agda}. Its
  specification is a **membership equivalence**, which makes it unique and the
  induction's motive a proposition, and it is sealed where it is built. Two
  measurements, both about a name: the pair graph entering as a variable carrying
  its own equation, rather than as the closed sentence, is worth 85 seconds; and
  the set argument of `mem-ord`{.Agda} must be explicit at every use, since
  `IsOrd`{.Agda} unfolds to a quantified membership and determines nothing. This
  chapter is what an internal definition of `L` is made of, and the internal
  well-order is read off it.
- `L.Axioms.Power`{.Agda}: the power-set field, by bounding the constructible
  subsets and carving one stage. **Condensation is not used and is not needed**:
  the axiom asks that the constructible subsets form a set, not that they appear
  early.
- `L.Recursion`{.Agda}: a function on a set of `L` whose graph is expressible has
  its table in `L`. A corollary of general-formula replacement, not a theorem: the
  usual absoluteness discipline exists to make a table readable *inside a stage*,
  and nothing here reads inside a stage. The recursion stays in the meta-language
  where it was written; `smallDom`{.Agda} supplies the domain for any small family,
  and `Definition`{.Agda} reduces an instance to a defining formula with its
  adequacy. `witnessInModel`{.Agda} records the one rule a graph must obey: an
  object-language existential ranges over `L`, so a graph may not describe an
  object by asserting that object's existence.
- `L.Choice.Stage`{.Agda}: where a set of `L` first has a member, which is what
  replaces a well-ordering of `L`. `μ`{.Agda} is the earliest stage meeting it,
  one instance of the least-ordinal operator and sealed like `stage`{.Agda};
  `meet-suc`{.Agda} makes that stage a **successor**, because a set enters the
  tower only by being carved out of the stage below, and `defStage`{.Agda} is
  the stage it succeeds, a function because a successor determines what it
  succeeds among ordinals (`ord-suc-inj`{.Agda}). `Lset-μ`{.Agda} identifies the
  stage of first appearance with the definable powerset over the definition
  stage, so a first member carries a name written over **one fixed stage**, and
  that is what the choosing device compares. `stageBound`{.Agda} is the ordinal
  the bookkeeping runs in: above a set's own stage, hence above its members and
  theirs by transitivity, and above `ω`{.Agda}, where the names themselves live.
  No relation on `L` is stated here and no recursion is run.
- `L.Choice.Finite`{.Agda}: the finite stages are finite, and each carries a
  well-order. `Tally`{.Agda} is the whole finiteness vocabulary, a finite family
  hitting every member, with neither injectivity nor decidable equality asked
  for; `powerTally`{.Agda} raises one to the definable powerset by enumerating
  the bit vectors over it, since every subset of a tallied stage is definable
  (`finSet∈𝒟ₒ`{.Agda}), and `stageOrder`{.Agda} runs that step along the
  numerals. `precedes`{.Agda} compares two subsets at the **earliest point where
  they disagree**: irreflexive for free, transitive by comparing two witnesses,
  trichotomous by the excluded middle with the base's smallest elements. Its
  well-foundedness is no property of the comparison at all, and would fail over
  an infinite base; it is bought from the tally through `Search`{.Agda}, where a
  scan of a finite family returns a smallest element of any inhabited property
  and the classical step turns that into accessibility. `limitOrder`{.Agda}
  assembles `Lset ω`{.Agda} with the **level as the primary key**, because the
  earliest-disagreement orders do not extend one another and with the level in
  front they do not have to; it is the first exercise of
  `L.WellOrder.Base`{.Agda}, twice over, since the levels are ordered there too.
- `L.Choice.Name`{.Agda}: a member of a successor stage, written down. A
  `Name`{.Agda} is an arity, a parameter-free formula of one more variable, and
  a vector of parameters from the stage below; `denote`{.Agda} is the subset it
  carves, read in the inner semantics `Def`{.Agda} is defined by
  (`denote-mem`{.Agda}) and in the internalized table (`denote-table`{.Agda}),
  and `names-complete`{.Agda} says every member of the successor stage has a
  name. `code∈limit`{.Agda} puts a parameter-free code in `Lset ω`{.Agda},
  because it is built from numerals and pairs and nothing else, and
  `code-inj`{.Agda} makes it faithful by erasing the constants back out.
  `_≺ₙ_`{.Agda} is the three-key lexicographic comparison written out, code then
  arity then parameters, with all four `SWO`{.Agda} laws and `leastName`{.Agda},
  the least name of a non-empty family.
- `L.Choice.Step`{.Agda}: one order at every stage, as a family. `birth`{.Agda}
  is the ordinal a constructible set is carved over, one below the earliest stage
  containing it, and it exists for the reason the choice-stage chapter gave for a
  cell: a set enters the tower only by being carved out. `stepAt`{.Agda} is the
  step, from a well-order of `Lset δ`{.Agda} to one of `Lset (sucV δ)`{.Agda}, in
  **one branch**: the order is by **least name** everywhere, the previous
  chapter's three-key comparison pulled back along a map that is a function
  precisely because the stage below is well-ordered. A first draft guarded a
  second branch below the limit stage; measured, it was surplus, and what it
  really contributed was a normalization barrier that the `opaque`{.Agda} seal
  gives more cheaply. `pullOrder`{.Agda} moves a well-order along an injection
  and is the only transfer written: the step uses it, and so does
  `carry`{.Agda}, the presentation of a stage's members as the index type the
  naming chapter takes. Three definitions and two readings say what the pulled-back
  order is for a caller outside: `denotesAt`{.Agda}, a set's names;
  `IsLeastName`{.Agda}, the well-order chapter's `IsLeast`{.Agda} **at** that
  family and never a re-spelling of it (16 s against nothing, because a
  comparison at a computed name opens the code order); `leastNameOf`{.Agda}, the
  search; and `stepAt-fill`{.Agda}/`stepAt-read`{.Agda}, the step against the name
  order at any two names the caller has shown least, proved inside the telescope
  the seal lives in, since restating either at top level costs 39 s.
  No order on dependent sums is built. `orderAt`{.Agda} is the family itself, all
  four `SWO`{.Agda} laws at every ordinal, by membership induction, and it is
  sealed, since an unsealed order unfolds into a recursion over the hierarchy.
  Its comparison takes the **birth as the primary key**, which is why
  `endExtension`{.Agda} then costs nothing: a comparison never mentions the stage
  it is read at, so the order at a large stage restricted to a small one is a
  **path** to the order there, not merely an equivalence, and the only work is
  the proof-irrelevance of constructibility and of ordinal-hood.
- `L.Choice.Internal`{.Agda}: the same order, described in the object language,
  so that the model's own separation can carve it out. `InLimitAt`{.Agda} is the
  skeleton's **stage** condition, and it is one membership atom in the limit
  stage, said through `LsetGraphAt`{.Agda} at the constant `ωʟ`{.Agda}: a
  parameter-free code is hereditarily finite, so the recursion that would have
  decided constant-freeness from inside is never written. It is not
  constant-freeness, though, since a hereditarily finite code may name
  hereditarily finite constants; `FreeAt`{.Agda} is, and it is one membership
  atom too, in the code set **at the empty alphabet**, resting on the fact that a
  parameter-free formula has the same code at either alphabet
  (`freeCode-in`{.Agda}, `freeCode-out`{.Agda}). Read at slots
  (`codeFree-out`{.Agda}) the skeleton slot holds exactly the codes of the
  parameter-free formulas of one more variable than the arity, which is exactly a
  meta name's formula, and `codeFree-limit`{.Agda} derives the stage condition
  from it. `NameAt`{.Agda} is a name at slots, a skeleton in the limit stage and
  free of constants, a parameter sequence over the carrier whose domain is the
  arity, and a denotation written as **one** `extAt`{.Agda} whose condition reads
  the value `satGraphAt`{.Agda} assigns at the key the arity and the skeleton
  make; two code sets reach it as slots, the one at the carrier, without which
  the graph's existentially bound table pins nothing, and the one at the empty
  alphabet, without which the skeleton is not a meta name's. `≺At`{.Agda} runs **no recursion of its
  own**: a membership atom against the order-so-far for the code, a membership
  atom between numerals for the arity, and a bounded lexicographic quantification
  for the parameters, with both orders reaching the description as slots.
  `StepAt`{.Agda} is one step of the family, by least names, with **one** branch,
  so the min-difference formula the plan once wanted is not needed.
  `order-in`{.Agda} and `order-out`{.Agda} are the two adequacy halves, at
  variable slots in a variable environment: with each relation slot carrying the
  hypothesis that says which order it holds, the formula holds of two names' data
  exactly when `_≺ₙ_`{.Agda} holds of the names, the parameter key bridged by an
  induction identifying a first difference with the naming chapter's recursion on
  vectors.
- `L.Choice.Table`{.Agda}: that order, turned from a description into an
  **object**, one at every ordinal. `Related`{.Agda} is the class realized, the
  pairs of two members of a stage the order there relates, carrying the
  comparison **truncated** because a strict well-order is not known to be
  proposition-valued, and `strict`{.Agda} takes the truncation off again for
  every such order at once by splitting on trichotomy before eliminating
  anything. `ApproxAt`{.Agda} and `GraphAt`{.Agda} are the approximation and its
  graph, shaped as in `L.Coding.Sequence`{.Agda} but generic in the step
  condition, which enters as a parameter in two forms with one meaning, at slots
  because the graph must bind the table it consults and at constants because
  separation carves with a formula of one free variable.
  `approx-val`{.Agda} pins every value an approximation records by one
  membership induction on the argument, with no single-valuedness hypothesis
  anywhere, and `approx-uniq`{.Agda} is the corollary. `tableAt`{.Agda} is the
  construction, sealed where it is built, and it carries **two** things at every
  ordinal, unlike the hierarchy chapter's: the table of relations below it,
  collected by replacement through `mereFunct`{.Agda}, and the relation at it,
  separated out of a bound, because the order at a stage has no meta-language
  term to exhibit. That bound costs one appeal, since the pairs of two members of
  a stage are a **small** family of elements of `L`, so `smallDom`{.Agda} confines
  them all at once. `rel-fill`{.Agda}, `rel-rep`{.Agda}, `ixRel-fill`{.Agda} and
  `ixRel-rep`{.Agda} read the membership of **any** set that realizes the class,
  at the two shapes a member of a stage comes in, the second of which is what a
  separation and the naming chapter's parameter order both consume; stating them
  of any realizing set is what puts them a stage **earlier** than the
  construction, where the naming machinery needs them, and `relL-fill`{.Agda},
  `relL-rep`{.Agda}, `ix-fill`{.Agda} and `ix-rep`{.Agda} are those four at the
  set this chapter builds. What is left open is the step condition's own adequacy,
  which is the previous chapter's `StepAt`{.Agda} against the meta step, named
  here as the two hypotheses of `Described`{.Agda}.
- `L.Choice.Faithful`{.Agda}: the description made faithful, and the frame's two
  hypotheses discharged down to one. `BirthAt`{.Agda} is the **birth stage** said in
  the object language, and it names no constant and needs no successor operation:
  the tower at the slot does not hold the set while the definable powerset of that
  tower does, which `Lset-suc`{.Agda} makes equivalent to being one below the least
  stage containing it, spent only on the meta side. `BirthAt-out`{.Agda} and
  `BirthAt-in`{.Agda} are its two readings at variable slots with ordinality the
  only hypothesis, soundness being a trichotomy against the least stage written as
  a named helper. `isCodeAnyAt`{.Agda} is the code predicate at **any** arity over a
  carrier held in a slot, and it is an **instantiation and not a construction**: the
  arity-bound conjunct and the witness conjunct both already existed, and only their
  meeting is new; `CodesAt`{.Agda} is the set they cut out, one `extAt`{.Agda}, whose
  two readings pin the slot to the code set over the carrier, so the naming
  description's code-set slot is pinned by description rather than by an outside
  equation. `order-unfold`{.Agda} is the order family's defining equation at a
  stage, one `cong`{.Agda} over the recursion's computation rule; `bornIn`{.Agda} is
  the converse of `birth-in`{.Agda}, and it buys the description one binder less;
  `stepMoved`{.Agda} carries a step comparison along an equality of carriers, rebuilt
  locally rather than reached for in another module. `CondCore`{.Agda} is the order
  at a stage described in full, birth-primary, generic in the step condition: it
  binds four sets, takes the stage as a **term** so that the constant form costs no
  binder, and is **sealed where it is built**. `Cond`{.Agda}, `Cond₀`{.Agda},
  `cond-spec`{.Agda} and `cond₀-spec`{.Agda} are the two forms the previous chapter's
  frame asked for together with their meanings, so `Described`{.Agda} applies and
  everything it proves is available, conditional on the step parameter and on
  nothing else. Four measurements are recorded in the chapter because each is a law
  and not a preference: the two elements a birth description is satisfied at must be
  sealed (178 s against 2 s), an environment must be spelled out rather than
  abbreviated (207 s against 3 s), a two-way split concluding in a satisfaction must
  be a named helper and never a `with`{.Agda} (past 300 s), and a description read at
  constants must be sealed where it is built (160 s per reading). What is not here is
  the step's own adequacy, `L.Choice.Internal`{.Agda}'s `StepAt`{.Agda} against
  `stepAt`{.Agda}, which enters as the parameter `Stp`{.Agda} with `stp-out`{.Agda}
  and `stp-in`{.Agda} as its meaning: the first takes the table's correctness at
  **every** value recorded at the carrier, since the condition it reads may bind a
  value of its own, and the second takes a single value that realizes the order
  there, since that is what it has to put in.
- `L.Choice.Limit`{.Agda}: the order on the members of the limit stage, as an
  element of `L`, which is what the internalization frame's **code slot** has been
  asking for. `LevelAt`{.Agda} is the level said in the object language, three
  conjuncts and no constant but `ω`: the slot holds a member of `ω`, the tower
  there holds the set, and no smaller numeral's tower does. Both readings stand at
  variable slots, with the level arriving as a **variable numeral** carrying its
  own defining equation, which is the difference between 145 s and 1.8 s, since
  the level is a classical accessibility recursion and conversion at a slot forces
  it open. `PrecedesAt`{.Agda} is one step of the earliest-disagreement comparison
  with nothing concrete in it: the base relation and the base stage are held in
  slots, so the description can stand where the relation is the value of a
  recursion, and the base relation's membership is reached by `appAt`{.Agda},
  since a pair is described and not named. `strictLimit`{.Agda} takes the
  truncation off a comparison by splitting on trichotomy first.
  `LimitOrdAt`{.Agda} joins the two keys as a disjunction whose first disjunct
  binds two levels and compares them by membership and whose second binds
  **one**, so an equation between levels never enters the object language.
  `pairsBound`{.Agda} confines every pair the order could relate by
  `smallDom`{.Agda}, and `codeOrder`{.Agda} is the separation out of it, sealed
  where it is built; `codeOrder-fill`{.Agda} and `codeOrder-rep`{.Agda} are the
  two representation lemmas, and `CodeKeys.AtParams`{.Agda} is
  `Adequacy.Keys`{.Agda} with its code slot filled by them, at the same two
  arguments and with no adapter. All of it is conditional on **one** hypothesis,
  `BeforeAt`{.Agda} with its two readings against `before`{.Agda}, which is the
  earliest-disagreement family along the numerals said inside: a recursion whose
  values are relations, so an approximation, cheaper than the tower because the
  index is a member of `ωʟ`{.Agda} and the step is already written. Two
  measurements, each an old law in a new place: a case split whose scrutinee is a
  **bundle's** comparison and whose conclusion is a satisfaction does not finish,
  and written on an explicit sum with named branches it costs nothing (past 300 s
  against 2.4 s); and the composed description must be **sealed where it is
  built**, since the separation's condition unfolds it under two binders (past
  300 s against 2.7 s).
- `L.Choice.Before`{.Agda}: the earliest-disagreement family, internalized, which
  discharges the one hypothesis the previous chapter was left standing on.
  `relAt`{.Agda} is the relation at each numeral as an element of `L`, a
  separation over the pairs of that finite stage carved with the previous
  chapter's step description, whose two slots are bound and **pinned to constants
  by the object equality**, so one description serves both the separation and the
  graph; `relAt-out`{.Agda} and `relAt-in`{.Agda} are its two readings, proved
  together by induction on the numeral, each spending the other at the
  predecessor because the previous relation is consulted only inside the
  agreement clause, and `precedes-map`{.Agda} carries that comparison
  contravariantly. `RelBodyAt`{.Agda} is the step, generic in the member, the
  index and the approximation, with the predecessor said as the `∈`-**maximal**
  member of the index, so no object equality is needed and the step is empty at
  zero exactly where the recursion is. `RelStepAt`{.Agda}, `ApproxAt`{.Agda} and
  `RelGraphAt`{.Agda} follow `L.Coding.Sequence`{.Agda} with no single-valuedness
  conjunct; `step-rel`{.Agda} and `rel-step`{.Agda} are the bridge to the
  meta-language, `approx-val`{.Agda} pins every value an approximation records by
  one well-founded induction with single-valuedness nowhere a hypothesis, and
  `rel-only`{.Agda} is the graph's determinacy. `approxSet`{.Agda} is the
  approximation exhibited and costs **no formula at all**, since the
  approximation below a numeral is finite and `finSetL`{.Agda} spans it once
  `smallStage`{.Agda} puts its members in one stage; `beforeFam`{.Agda} is the
  family, one replacement along `ωʟ`{.Agda}, sealed where it is built, with its
  two directions stated against the recursion and against no formula.
  `BeforeAt`{.Agda} reads the family at the numeral held in a slot, with
  `appAtC`{.Agda} for application at a constant and the two compared sets left
  **unconfined**, and with it `Described`{.Agda} is instantiated, so
  `codeOrder`{.Agda} and `CodeKeys`{.Agda} are unconditional. One measurement, the
  largest in this part: the four descriptions must be **sealed where they are
  built**, since unsealed each satisfaction at a concrete environment normalizes a
  formula carrying two copies of the whole hierarchy description (376 s against
  3.8 s, ninety-nine fold), and the frame that builds the family obeys the same
  law one level up by handing back a triple in which no formula appears.
- `L.Choice.Order`{.Agda}: the step described, and the order table made
  unconditional. `Stp`{.Agda} is that description: a **sealed** formula binding
  six sets and pinning two constants. The six are the tower at the stage, reached
  through `L.Coding.Sequence`{.Agda}'s `LsetGraphAt`{.Agda}; its definable subsets
  through `L.Coding.Powerset`{.Agda}'s `DefAt`{.Agda}, with the two compared sets
  required to lie in it, which is how the step's two membership components arrive
  without a lemma nobody has; the table's value at the stage through
  `appAt`{.Agda}, which is what keeps the description reading against whatever
  table the caller holds; and the code set over the tower through
  `L.Choice.Faithful`{.Agda}'s `CodesAt`{.Agda}, written for exactly this slot.
  The two pinned by an object equality are `L.Choice.Limit`{.Agda}'s
  `codeOrder`{.Agda} and the code set at the empty alphabet, because a slot holds
  a variable and those two are particular sets. The body at those seven slots is
  `L.Choice.Internal`{.Agda}'s `StepAt`{.Agda}. `Slots`{.Agda} supplies all six
  arguments of the step adequacy, generic in the six sets with their equations as
  hypotheses: the code side unconditional from the limit and family chapters, the
  carrier side from `L.Choice.Table`{.Agda}'s readings at the bound value, which
  is the step parameter's own hypothesis and the only input taken from outside.
  `stp-out`{.Agda} and `stp-in`{.Agda} are unpack and pack over the six binders,
  composed with `L.Choice.Adequate`{.Agda}'s step readings and
  `L.Choice.Step`{.Agda}'s two, and they carry the frame's asymmetry: soundness
  quantifies over every value the table records there, completeness takes the
  single value the caller realizes with. One line then opens
  `L.Choice.Faithful.Ordered`{.Agda}, and with it the whole of the table becomes
  unconditional: `CondCore`{.Agda}, `Cond`{.Agda}, `Cond₀`{.Agda} and their two
  specifications, and, from `L.Choice.Table`{.Agda}, `StepAt`{.Agda},
  `ApproxAt`{.Agda}, `GraphAt`{.Agda}, `approx-val`{.Agda}, `graph-only`{.Agda},
  `graph-table`{.Agda}, `tableAt`{.Agda}, `relL`{.Agda}, `relL-spec`{.Agda} and
  all four representation lemmas. One measurement, a law at a new place: **the
  type a frame concludes in is sealed where it is built**, since instantiating
  that frame at the concrete elements the description binds normalizes it, and
  unsealed that does not finish (over 200 s against 7 s for the whole chapter).
  `Bound`{.Agda} is the shape the last chapter separates with: the bounding
  ordinal of a set of `L`, the order on the members of the tower there as an
  element of the model, and its two representation lemmas.
- `L.Choice.Transversal`{.Agda}: choice, and the frontier emptied. The axiom in
  the **transversal** form the model record states it: a set whose members are
  inhabited and pairwise disjoint has a set meeting each member in exactly one
  point. No well-order of `L` is used, because none exists here; a set is small,
  so `L.Choice.Stage`{.Agda}'s bounding ordinal holds the family, its members and
  their members at once, and `L.Choice.Order`{.Agda}'s `Bound`{.Agda} supplies the
  order on the tower there as an element of the model. `Pick`{.Agda} is the
  description, one free variable and two constants: some member of the family
  contains this set and nothing in that member precedes it, with the order pinned
  to a slot by an object equality because the atom for a pair in a relation reads
  the relation from a slot. `pick-in`{.Agda} and `pick-out`{.Agda} are its two
  readings against `L.WellOrder.Base`{.Agda}'s `IsLeast`{.Agda}, every truncation
  payload named. `transversalSet`{.Agda} is the model's own separation by it over
  the tower, and `transversal`{.Agda} counts the intersection with each member:
  existence from `leastOf`{.Agda}, the least-element search that had waited
  without a consumer since it was written, and uniqueness from pairwise
  disjointness, which nothing else in the book uses, through
  `isPropLeastOf`{.Agda}. The dependence on the supplied ZF model is one
  transport along the intersection's specification. `hasChoiceL`{.Agda} is the
  model's choice field, so the registry is empty and `L.Frontier` is deleted with
  the root chapter's second parameter. One measurement, and it is a law declining
  to bite: a description read at constants is sealed where it is built, worth
  ninety-nine fold where it was found and nothing here (2.3 s either way), since
  this description carries no coded syntax; the seal stays and the number is
  recorded, because the law is about what a description contains.
- `L.Model`{.Agda}: the root chapter: the honest relative-consistency framing;
  extensionality and regularity descend along transitivity; `L⊨ZF`{.Agda} and
  `L⊨ZFC`{.Agda} assembled, with the excluded middle as the only hypothesis. The
  debt registry `L.Frontier` that this chapter took as its second parameter is
  gone: it opened at eleven fields, shrank six times, and was deleted with the
  chapter that emptied it.
<!--zh-->
根，今日陈述，余部完成：

- `L.Axioms.Full`{.Agda}：任意公式的分离与替换，办法是反射那条公式，再把有界的器械施于它的相对化；那个禁闭原子正是使替换的像逃不出阶段的东西。
- `L.Absoluteness`{.Agda}：两门对象语言之间的桥。常元可构造的、关于层级的 Δ₀ 公式，经 `liftFo`{.Agda} 运进 `L` 的语言，而 `transferFo`{.Agda} 说两者说的是同一件事；编码诸章留在层级一侧，从此处被引用。
- `L.Coding.Model`{.Agda}：模型之上的对象语言。「函数」的含义 (`prAtL`{.Agda}、`appAt`{.Agda}、`svAt`{.Agda}、`domAt`{.Agda})、取值一侧的对、标签读式、环境，以及 `extAt`{.Agda}：每条集值子句的写作框架，其两种读法就是它的两个投影。无常元的读式经桥引用；点名数码的读式直接写，因为无界如今免费。
- `L.Coding.InL`{.Agda}：每个码都是 `L` 的元素，沿构造子的一次归纳，里面什么也没有。正是它使一个码可被点名为模型对象语言的常元，使一族码可充当已内化递归的定义域。**全体**码之集刻意未证，此处也不需要。另有 `closure`{.Agda}，一条公式的诸子公式键构成的有穷集；`closure-inv`{.Agda} 把它读回来；以及 `byTag`{.Agda}，它把十二个构造子与封闭性谓词提出的八项要求对上一次，而非对上十二乘八次。
- `L.Coding.Closed`{.Agda}：闭包满足对象语言的封闭性谓词，且是满足它的最小者。四个读式的八个实例，再加一次归纳；前者是「对一条公式的诸子码作递归」关于其索引集所需的那条假设，后者是它的取值唯一的理由。那八条子句从不看一条公式，故只对任意可**剥开**的集合证一次 (`Peel`{.Agda}：一个成员仅仅是某条公式的键，而那条公式自己的闭包坐落于内)，而 `closureClosed`{.Agda} 就是 `closedOf`{.Agda} 落在闭包处、以 `closure-inv`{.Agda} 充当剥开。此处的一般性免费，因为 `byTag`{.Agda} 本就是对着任意目标集写的。
- `L.Godel.Operations`{.Agda}：一批有穷的集合运算，每个都是带两个隶属方向的单个集合形成子，且无一欠排中律：积与隶属图、直接形成子版的并与差、参数键处的两个选择，以及被记录赋值的扩张与移位。后面的章将在本要花公式的地方复合它们。
- `L.Godel.Definable`{.Agda}：运算，被描述出来。一个框架把一个体与两个语义转换变成「槽位与运算取值之间的等同」；十一条描述经它而过 (布尔存货、积与隶属图、单点键处的两个选择、取值集、元数槽位处的元组族、两个图移位运算)，每条都在变元槽位与变元环境处双向读出。
- `L.Godel.Tuples`{.Agda}：赋值作为图集合，及其对着运算的代数：扩张就是图扩张，弃首就是移位，逐条目单射性把一个图对着另一个图的查值规格去读，而载体之上全体赋值的族按族扩张走步。
- `L.Godel.Satisfaction`{.Agda}：满足关系作为集合，逐情形。公式的满足集是「满足它的诸赋值」上的单个集合形成子，而已交付的每个情形都是与某个运算复合的外延等同：假与真、合取、析取与否定对着布尔存货，两变元隶属原子对着一次选择，存在量词对着移位。
- `L.Godel.Terms`{.Agda}：组合子项，塔将要量化的语法。项与公式逐构造子镜像对应，却经每节点一个集合运算获得含义，且没有绑定子；可靠性以反向运行的情形等式把每个项读回为其镜像的满足集，完备性经诸化归给每条公式指派一个项，立于那一份经典假设之下。
- `L.Godel.NormalForm`{.Agda}：范式。载体之上的每个满足集，都由载体与其成员之上的一个有穷复合项所指称：一次归纳，每个情形读出满足关系那一章的一条情形等式，原子经诸化归装配为叶子，而那一份经典假设只在它本来就必须进场之处进场。
- `L.Godel.InL`{.Agda}：喂给可构造的实参，诸运算返回可构造的集合，以 `denoteL`{.Agda} 封顶：可构造载体上每个组合子项的每个指称都可构造。全程一台引擎：装下实参的一个阶段、每运算一条经绝对性在外层世界读出的 Δ₀ 定义公式，再经可定义子集之门收回类中；两个移位运算先爬固定级数的阶段。
- `L.Godel.Codes`{.Agda}：语法成为模型装得下的数据。先是元数打包的子项枚举，然后每项一个遗传有穷的码，即封印数码链上的标签对塔，按构造是 `L` 的元素；每构造子一条展开等式，外加在案定律规定的标签判别件。
- `L.Godel.Table`{.Agda}：指称表的诸子句，每构造子一条：码带此标签与此载荷、孩子的条目在场、取值是孩子取值上的那个运算，每条合取都经存货中的描述与对读式读出。每条子句携带元层形状与双向读式；二元节点共用一个框架。
- `L.Godel.Name`{.Agda}：以元数一的项作阶段成员的名字。指称是求值后取值，完备性把项那一章的等同当作一次搬运花掉，良序是组装而非发明的：标签字母表用组合子，树按 shortlex 排序，再沿一幅画拉回，其单射性是一个左逆、而非一张判别矩阵。导出的接口与内化路线那一章逐一对应。
- `L.Godel.Step`{.Agda}：有意为之的脚手架，且在原处明说。选取步进的骨架逐行同源，唯把命名导入改指项名字，好让两条路线并排全绿、项路线的内部侧对着这一份陈述；到最终重接线时两份之一退役。
- `L.Godel.Tower`{.Agda}：塔的一步，从内部描述。对诸逼近表的裸存在量词会接纳垃圾，故步量化受证的表：八个局部分支形状把标签钉进封印数码、载荷钉进 ω 或载体、孩子钉进主表、注解钉进一张函数性的表。诚实性在成员关系的传递闭包上把每个受证的对读回为诚实项的码；填充以逼近族自己的递归使诚实的一对表受证，其函数性恰是「码决定元数」这一事实；步本体的两条定律把元数一条目的取值读进载体的 `𝒟ₒ` 又填回来，于是塔的一步在码与表之上两个方向皆可内部描述。
- `L.Godel.Closure`{.Agda}：闭包，被开启。带种类闭包塔将要花掉的元层地基：每个正元数处的取值泛化，把满足集上的一次选择读作一次合取的两条选择等式，说满足集经全体变元移位而存活的变量变换律，把整个扩张裁到常元单点集的正向钉住包含，以及单例族，即存货缺掉的那一个运算，连同它的隶属定律。闭包递归本身是下一章的工作。
- `L.Godel.Levels`{.Agda}：层级，被内化。架子内部的面孔是一张有限前缀表：直到某个界的一张条目集 `pr (pr #n #k) S`，逐架确定。层描述把步进的整套九子句集写到槽上，配双向读式；前缀表描述补上函数性、两条基子句、后继子句 (在 `suc n` 处的条目是 `n` 处条目并上那一层)，以及定义域充分性。钉住定理以元归纳排除垃圾：任何满足的表，其条目就是元层 `slice` 取值，故无需证书。填充把元前缀表打成 `L` 集，而步进在前缀表之上两个方向皆可描述。
- `L.Coding.EnvSet`{.Agda}：落在 `L` 某集合之上、给定长度的诸环境构成 `L` 的一个集合，而那正是取补集的诸子句在其中取补的东西。一个小索引类型、一个阶段、一次分离，不用递归。
- `L.Coding.Sat`{.Agda}：给定元语言的一条公式与一个载体，满足它的诸环境之集，沿公式递归造出。没有任何内部的东西：每一步把前几步的集合以常元点名，故每一步只是在周遭集合上作一次分离，而内部诸子句因此成为**等式**而非定义。只导出十二个取值与它们的成员等式。
- `L.Coding.Bridge`{.Agda}：那个取值**是什么**。在载体之上的每个环境处，「属于它」就是「在世界 `(B, ∈)` 中被满足」，而后者正是可定义幂集据以定义的概念；没有这条陈述，从那场递归读出的内部 `Def` 可证地与任何东西都不相符。右端取内层语义，不取相对化在周遭的读法，因为只有内层那种像那个条件一样对有界量词设两道防。`defSet-Sat`{.Agda} 把它直接花在 `L.Definability`{.Agda} 上。登记在案的那份相干性风险没有引爆：把这座桥以内层环境向量为索引之后，量词的扩张就是底族上的前置，于是相干性只剩四条量词子句共享的两条 `refl`{.Agda} 分支，而带截断的那次恢复被关进「一个成员无非就是一个环境」那条推论里。
- `L.Coding.Table`{.Agda}：诸条目，每条子公式一个；以及递归向它们索取的两件事：每个成员都是一个条目，且键决定它的取值。后者正是花掉码等式单射性的地方，而元数由道路归纳消掉，好让那条等式在它唯一成立的那个元数处使用。此处一切按构造都是模型的元素，因为诸码就是模型自己的。
- `L.Coding.Sound`{.Agda}：那张表满足诸子句，一条一条地。每次验证是四步，其中三步已经造好；剩下的是一条集合等式，而它们便宜，因为元语言的递归当初正是用那条等式所读回的那个条件来定义它的取值的。
- `L.Coding.Unique`{.Agda}：一张在子码封闭的索引上满足十二条子句的表，在每个键处记录的就是递归在那里造出的取值，而正是这一点使那个图单值。对着典范取值陈述，且索引取作变元，因为把键代进一个满足关系里，在任何合理时间内都不会通过类型检查。
- `L.Coding.Slot`{.Agda}：一条公式的递归所索引的那个槽，满足对象语言的封闭性谓词，而那正是满足关系那个图对它的索引集所陈述的假设。是闭包那一章的定理再来一遍，落在模型自己的编码上。
- `L.Coding.Descent`{.Agda}：一场跑在码上的递归如何从一条码走到它的诸部件，而成员关系办不到这件事：Kuratowski 的对把一个部件放在四个成员步之下，而中间那些集合不是码。秩沿成员关系严格增长，故那四步经序数的传递性合成，递归改跑在秩上。
- `L.Coding.Shape`{.Agda}：「是一个码」中封闭性没有说出的那一半。封闭性是八条以标签为键的蕴含，故一个没有可辨标签的成员平凡地满足全部八条；`shapedAt`{.Agda} 说的是每个成员都是一个带元数标签的对，其标签属于那十二个之一，且载荷是该标签所要求的那种。两个框架承载那十二条，因为十二个标签之间只有两种载荷形状；标签的其余要求是框架所携带的一条关系，而 `isTmAt`{.Agda} 是其中唯一与公式码无关的那一条。成形性是在**两位**上陈述的，即那个集合与一个载体，因为一个词项有两样东西要界住，而两者不同：变元的序号由元数数码界住，常元由「属于载体」界住。第二样使一个成员成为该载体之上、而非模型之上某条公式的键，而它写作一位、不写作常元，好让下面的一切都不被重新索引。`isTmAt-decode`{.Agda} 在任意字母表上把词项还原出来，它是第一个解码，也是唯一一个不需要归纳的；它的常元那一支需要一样谓词供不出的东西，即载体的诸成员就是字母表的像，于是把它取作一条假设。`Peel.peel`{.Agda} 是两半的会合：形状说出一个成员是十二者中的哪一个并交回它的部件，封闭性说那些部件在该标签所要求的元数上也是成员，而两半各自都不是递归的一步。另一个方向同样欠着，因为一条为了被消费而写下的谓词，在有东西满足它之前什么也没证明：`shaped-in`{.Agda} 由「每个成员一次选择」造出那个十二重析取，而 `closureShaped`{.Agda} 把它花在一条公式的闭包上，那正是解码的第一个调用方所欠的第二条假设。一条值得留存的测量：`isTmAt`{.Agda} 的两个析取支由两条点了名的引理去读，而写成一个函数的两条子句时，本章十分钟内跑不完，因为类型靠推断的分支是对着整个析取、而不是对着它自己那一支求解的。
- `L.Coding.Recover`{.Agda}：解码。在一个于某载体上既封闭又成形的集合里，一个以「某个已言明元数处的键」的形式递交过来的成员，就是**该载体之上**某条公式的键，而 `Decode.recover`{.Agda} 把它造出来。字母表是一个参数，目标在它之上陈述，因为消费方以单个载体之上的诸公式为索引，模型之上的公式对它毫无用处。这也使那六个框架**更短**：在模型之上，每个框架比较码与载荷之前先得把模型的编码搭桥到层级的编码；在字母表之上，码本来就是层级的元素。「**每个**成员都是这样一个键」此处未予证明，欠这笔账的是造那个集合的人，因为形状对它所绑定的元数分量不加任何条件。递归跑在码的秩上，不跑在码上、也不跑在键上：不跑在码上，是因为成员关系不下降进 Kuratowski 的对；不跑在键上，是因为「对的秩的算术」是一条没人证过的事实。元数作为一个自然数在旁边带着，正是这一点让归纳得以在量词把它抬升到的那个更大的元数上回来；载体则压根不被量化，它是归纳开跑前就已固定的一位。六个框架承载那十二个情形，而每个框架都把自己那个构造子的编码等式作为假设收下，因为构造子若是变元，编码函数便不化简，寻找那条等式的代价就是全部代价。在字母表之上，那十二条等式仍是 `refl`{.Agda}，因为常量变换按定义与每个构造子交换。
- `L.Coding.CodeSet`{.Agda}：某载体处的诸码，作为 `L` 的集合，一个落在元数一、一个落在每个元数。`smallDom`{.Agda} 把诸键装进一个阶段，任意公式的分离再把它们切回来，故本章是两条只差一个合取项的对象语言谓词。共享的那个合取项「仅仅存在一个等于 `A` 的载体、以及一个在它上面成形的封闭集装着它」是若干无界存在，在此处免费；载体在 `hasWitnessAt`{.Agda} 里是**一位**，只在高一层绑定处、即 `hasWitness`{.Agda} 里，才由 `var zero ≐ con A`{.Agda} 钉成常元。这样一拆是消费方逼出来的：内部层级把自己的阶段绑定起来，而集合进入公式的唯一方式是被点名，故一条点名了自己载体的谓词，在那层绑定之下压根说不出口。相异的那个合取项说那个成员是第一分量为数码的对，而它之所以存在，是因为 `recover`{.Agda} 收下实参的形式是**某个已言明元数处的键**，而 `closedAt`{.Agda} 与 `shapedAt`{.Agda} 都不约束元数那一位：形状把它存在量化且不加条件，故那个集合必须从外面把它钉住。`isCode`{.Agda} 把数码一点名；`isCodeAny`{.Agda} 把元数绑定，只要求它属于 `ωʟ`{.Agda}，而读回来无须归纳，因为 `ω-specL`{.Agda} 是一条等式，且数码链有投影。**`Codes-spec`{.Agda} 与 `AllCodes-spec`{.Agda} 闭合了两趟往返**：一个成员**恰是**载体之上某条公式的键，分别落在元数一处与某个元数处，故两个集合都是被刻画的，而不是被两条陈述夹住的。全元数那个集合的存在，是为了它所刻画的那一类：对码的递归要在一个码的诸子码处作答，而量词的子公式住在高一级的元数上，一元那一类装不下它，故它当不了定义域。
- `L.Coding.Uniform`{.Agda}：作为已内化递归的满足关系，跑在**某阶段处的诸码**之上，而那才是每个消费方想要的定义域：以一条公式的槽为索引，就是一条公式一张表，而消费方到场时手里握着的是一个码、而非「它是其子码」的某条公式。`AllCodes`{.Agda} 作定义域，而索引集那笔债由成员自己那条公式的槽偿付，其余一概不动，因为那个图把自己的表**存在**绑定：`funct`{.Agda} 只需拿出**某张**装着该成员的合格的表，而最小的一张就是该成员自己那条公式的子公式槽。故 `Table`{.Agda}、`Slot`{.Agda}、`Sound`{.Agda} 与 `Unique`{.Agda} 都按既有类型施用，而登记在案的那次「在载体与键之对处重新索引」从未发生。唯一新的东西，是把两套编码接起来：层级的编码落在该阶段的字母表之上，模型的编码落在模型的语言之上；用的是 `codeBridge`{.Agda} (为此而写、至今未用) 加上重标的函子性。`val-at`{.Agda} 在一个以键的形式给出的成员处读出取值，`val-sat`{.Agda} 说那个取值**就是**载体之上的满足关系，而 `val-defSet`{.Agda} 把它落到元数一处的可定义幂集上。码载体与环境载体保持为彼此独立的参数，只在满足关系有含义之处被钉在一起。每条读式都把成员取作**变元**、把它的键等式放在旁边，而消费方本会改写的那个名字 `keyIn`{.Agda} 在它被造出之处封印：一旦把键写开，那个构造就落进一个满足关系里面，而无论证明写多长都展开不了。
- `L.Coding.Graph`{.Agda}：满足关系那个递归的图说了什么。三个存在量词分别管索引集、表与载体，由封闭性、全性与十二条子句设防，取值则从表上读出。一切都被绑定，因为一个图不可以点名一张尚未交给它的表，而那是内化定理唯一禁止的事。一个框架带两个实例，因为那条用来钉住的子句就是框架的参数：`satGraphAt`{.Agda} 把载体取作**一位**，供载体本身就是被绑定变元的消费方使用；而 `satGraph`{.Agda} 把它钉在一个常元上，按它一贯的类型与见证元组交付。
- `L.Coding.Powerset`{.Agda}：可定义幂集在对象语言中、落在一个作为**槽位**的载体上的描述，也是整条路线为之存在的那一步。内部层级把自己的阶段绑定起来，故一条点名了自己载体的描述在那里压根说不出口；`DefAt`{.Agda} 什么也不点名。它说的是：`u` 恰是那些 `x` 之集，对它们仅仅存在载体之上的一个码 `c` 与一个取值 `v`，使得 `v` 就是满足关系那场递归在 `c` 处所记录的东西，而 `x` 是「其单条目环境落在 `v` 中」的那些载体成员之集。两个存在量词**相邻**，而这是一次探针逼出的更正：若被一个合取项隔开，码那条假设与满足关系那条假设就落到不同的环境上，于是这条路线会平白背上一条它本来永远用不着的弱化引理。`DefinesAt`{.Agda} 是单拿出来的第三个合取项，`envOneAt`{.Agda} 是单条目环境，只有一行，因为长度为一的图只是一个对。`DefAt-in`{.Agda} 说这个算子满足那条描述，`DefAt-out`{.Agda} 说别的东西都不满足，后者在 `DefOK`{.Agda} 之下：描述里的每个存在量词都在 `L` 上取值，只够得着住在其中的东西，故这条描述恰在「载体的诸可定义子集皆可构造」之处适足。那个旁条件只是消去那一半的假设，因为引入自己的假设已蕴含它；而在一个阶段处，它由后继恒等式一劳永逸地解除，剩下 `DefAt-stage`{.Agda}：一条真值之间的等式，说这条描述对 `𝒟ₒS`{.Agda} 成立、对别的什么都不成立。
- `L.Coding.Sequence`{.Agda}：把层级说成一条**序列**，而这是为它写图时唯一可取的形状。一个图不可以点名它所定义的对象，而塔在某个阶段处是由该阶段以下的塔造出来的，故写下来的改为「*逼近*是什么」。`StepAt`{.Agda} 是某个实参处的那一步：一次 `extAt`{.Agda} 罩住三个相邻的存在量词，即那个实参、逼近在其处所记录的取值，以及它的可定义幂集；最后一样被绑定而不被点名，因为上一章交付的是关于它的一条描述、而不是指称它的一个词项。用一次 `extAt`{.Agda} 而不用手写的一对包含，因为一对包含会把那三个存在量词复制一份，并把每一种读法拆成互非逆的两半交回来。一个旁条件 `PowOK`{.Agda} 服务两个方向，因为一个「是 `L` 的元素」的可定义幂集，也就是一个「诸成员皆可构造」的可定义幂集。`ApproxAt`{.Agda} 是两个合取项、再无其他：`f` 恰好定义在那个实参的诸成员上，且它所记录的每个取值都是「在那里、由 `f` 自身算出的那一步」。它是一条隶属**等价**、而非一个单向的收集，这使即将到来的那场归纳的动机保持为命题，并把一条内部的函数外延性引理从路线上移除；且它**不带单值性合取项**，因为步进条件已经把「在一个实参处记录的每个取值」钉住了，故单值性是一条推论，而不是三个置于满足关系之下的全称量词。`LsetGraph`{.Agda} 把逼近绑定在两者之上。**本章的全部代价都出在转换上**：两条图读法陈述在具体位上，花掉了 130 秒中的 98 秒；而每一处「假设把环境写开、应用却把它藏在一个缩写背后」，再各花 15 秒。写成两侧是同一个表达式之后，它在两秒之内检查完毕，而这把「变元实参」那条规矩从一次代换推广到一条**陈述**。
- `L.Hierarchy`{.Agda}：上一章那个图，被对着本书真正造出的那座塔证明，以及用来证明它的那个**内部层级**。**表**是有序对之集；它在某个集合上正确，指它在该集合以下所记录的每个取值都是元层面的塔在那里的取值；它完备，指它在以下的每个实参处都记录了一个。`step-Lset`{.Agda} 从一张正确的表上读出一个被满足的步进、把塔取回来，`step-table`{.Agda} 则由它写出那一步，而上一章那个旁条件在两者之内一并解除，因为被记录的取值是塔在某个序数处的值，而阶段的可定义幂集可构造。`approx-val`{.Agda} 是在实参上的一次沿成员的归纳，其动机对**一切**被记录的取值作量化，故单值性从不作为假设，而 `approx-uniq`{.Agda} 三行落地。`Lset-only`{.Agda} 与 `Lset-defines`{.Agda} 是那个图的两个方向，而 `hierL`{.Agda} 是后者据以造出的东西：由「序数与塔在它那里的取值」所成之对的集合，经在一个**成对的图**上作替换而收拢，每个索引的序数性取自 `mem-ord`{.Agda} 且不加截断，函数性经 `mereFunct`{.Agda} 偿付。它的规格是一条**隶属等价**，这使它唯一、也使归纳的动机是命题，而它在被造出之处封印。两次测量，都关乎一个名字：成对的那个图以变元身份进场、随身带着它自己的等式，而不是以那个闭句子的身份进场，价值 85 秒；以及 `mem-ord`{.Agda} 的那个集合实参必须在每次使用时显式给出，因为 `IsOrd`{.Agda} 展开成一条带量词的隶属关系、什么也确定不了。本章正是 `L` 的内部定义的材料，而内部良序就从它上面读出。
- `L.Axioms.Power`{.Agda}：幂集字段，经「界住诸可构造子集、雕出一个阶段」证得。**未用凝聚，也不需要**：公理索取的是「诸可构造子集构成一个集合」，而非「它们现身得早」。
- `L.Recursion`{.Agda}：`L` 的集合上，图可表达的函数，其表在 `L` 中。这是任意公式替换的推论，而非定理：通常那套绝对性纪律是为了让一张表在**某个阶段之内**可读，而此处没有任何东西在阶段之内读。递归留在它被写下的元语言里；`smallDom`{.Agda} 为任意小族供给定义域，而 `Definition`{.Agda} 把一个实例归约为一条定义公式连同它的适足性。`witnessInModel`{.Agda} 记下图必须遵守的那一条规矩：对象语言的存在量词在 `L` 上取值，故一个图不可以靠断言被描述者本身存在来描述它。
- `L.Choice.Stage`{.Agda}：`L` 的一个集合最先在何处拥有成员，而这正是取代 `L` 的良序的东西。`μ`{.Agda} 是与它相交的最早阶段，是最小序数算子的一个实例，按 `stage`{.Agda} 那样封印；`meet-suc`{.Agda} 使那个阶段成为**后继**，因为集合进入塔的唯一途径是从它下面那个阶段中被雕出，而 `defStage`{.Agda} 是它所后继的那个阶段，之所以是函数，是因为在序数之内后继决定它所后继的东西 (`ord-suc-inj`{.Agda})。`Lset-μ`{.Agda} 把首次现身的那个阶段与定义阶段之上的可定义幂集认同，于是一个最先成员带着一个写在**单一固定阶段**之上的名字，而那正是选取装置所比较的东西。`stageBound`{.Agda} 是记账所在的序数：在一个集合自身的阶段之上，从而经传递性在它的成员及其成员之上，也在 `ω`{.Agda} 之上，而诸名字自身正住在那里。此处不陈述 `L` 上的任何关系，也不跑任何递归。
- `L.Choice.Finite`{.Agda}：有穷诸阶段确是有穷的，且各自带有一个良序。`Tally`{.Agda} 就是全部的有穷性词汇，即一个命中每个成员的有穷族，既不要求单射，也不要求可判定的相等；`powerTally`{.Agda} 靠枚举其上的位向量把它抬到可定义幂集上，因为已清点阶段的每个子集都可定义 (`finSet∈𝒟ₒ`{.Agda})，而 `stageOrder`{.Agda} 沿诸数码跑完这一步。`precedes`{.Agda} 在两个子集**最先分歧之处**比较它们：非自反性白得，传递性由比较两个见证得到，三歧由排中律连同基底的最小元得到。它的良基性压根不是这个比较自身的性质，且在无穷基底上会失效；它是经 `Search`{.Agda} 从点名册买来的，即扫过一个有穷族即得任一非空性质的最小元，再由那一步经典推理把它变成可及性。`limitOrder`{.Agda} 以**层号为主键**装配 `Lset ω`{.Agda}，因为按最先分歧处的诸序并不互相延拓，而把层号放在前面就不必延拓；这也是 `L.WellOrder.Base`{.Agda} 头一回被使唤，且一使唤就是两次，因为层号也在那里被排序。
- `L.Choice.Name`{.Agda}：把后继阶段的成员写下来。一个 `Name`{.Agda} 是一个元数、一条多一个变量的无参公式，以及一个取自下面那个阶段的参数向量；`denote`{.Agda} 是它刻出的子集，既读在 `Def`{.Agda} 据以定义的那套内层语义中 (`denote-mem`{.Agda})，也读在已内化的表中 (`denote-table`{.Agda})，而 `names-complete`{.Agda} 说后继阶段的每个成员都有名字。`code∈limit`{.Agda} 把无参的码放进 `Lset ω`{.Agda}，因为它由数码与对造成、别无他物，而 `code-inj`{.Agda} 靠把诸常量抹回去使它忠实。`_≺ₙ_`{.Agda} 是写开了的三键字典序比较，先码、再元数、后参数，连同 `SWO`{.Agda} 的全部四条定律与 `leastName`{.Agda}，即非空族中最小的名字。
- `L.Choice.Step`{.Agda}：每个阶段一个序，作为一族。`birth`{.Agda} 是一个可构造集据以被雕出的那个序数，比包含它的最早阶段低一级；它之所以存在，理由正是选取阶段那一章为一格给出的那条：集合进入塔的唯一途径是被雕出。`stepAt`{.Agda} 是步进，由 `Lset δ`{.Agda} 上的良序到 `Lset (sucV δ)`{.Agda} 上的良序，只有**一支**：处处按**最小名字**给出，即上一章的三键比较沿一个映射拉回，而那个映射之所以是函数，恰恰是因为下面那个阶段已被良序化。初稿曾在极限阶段以下守着第二支；实测下来它是多余的，而它真正贡献的是一道归一化屏障，`opaque`{.Agda} 封印以更低的代价给出同样的屏障。`pullOrder`{.Agda} 沿一个单射搬运良序，是本章写下的唯一一次搬运：步进用它，`carry`{.Agda} 也用它，即把一个阶段的诸成员表示成命名那一章所取用的那个索引类型。有三个定义与两条读式为外面的调用方说清那个拉回的序是什么：`denotesAt`{.Agda}，即一个集合的诸名字；`IsLeastName`{.Agda}，即良序那一章的 `IsLeast`{.Agda} **架在**那一族上，绝不另写一遍 (16 秒对分文不花，因为在算出来的名字处的一次比较会把码之序打开)；`leastNameOf`{.Agda}，即那场搜寻；以及 `stepAt-fill`{.Agda} 与 `stepAt-read`{.Agda}，即那一步对着名字之序读在「调用方已证为最小的任意两个名字」处，且证在封印所在的那条模块序列之内，因为把任一条在顶层重述都要花 39 秒。依值和上的序一概未造。`orderAt`{.Agda} 就是那一族本身，`SWO`{.Agda} 的四条定律在每个序数处齐备，沿成员归纳造出，且被封印，因为未封印的序会展开成一场遍历层级的递归。它的比较以**诞生阶段为主键**，而正因如此 `endExtension`{.Agda} 分文不花：一次比较从不提到它是在哪个阶段处被读的，故大阶段处的序限制到小阶段上，与那里的序之间是一条**路径**、而不仅仅是一个等价，唯一要干的活是可构造性与序数性的证明无关性。
- `L.Choice.Internal`{.Agda}：同一个序，用对象语言描述出来，使模型自家的分离能把它雕出来。`InLimitAt`{.Agda} 是骨架的**阶段**条件，而它是一个「属于极限阶段」的隶属原子，经 `LsetGraphAt`{.Agda} 在常元 `ωʟ`{.Agda} 处说出：无参的码是遗传有穷的，故那场本会从内部判定无参性的递归压根不必写。但它并不是无参性，因为遗传有穷的码可以点名遗传有穷的常量；`FreeAt`{.Agda} 才是，而它同样是一个隶属原子，落在**空字母表处**的码集中，所倚的事实是一条无参公式在两个字母表上有同一个码 (`freeCode-in`{.Agda}、`freeCode-out`{.Agda})。读在诸位上 (`codeFree-out`{.Agda})，骨架那一位所持有的恰是「比元数多一个变量的诸无参公式」的诸码，而那正是元层面一个名字的公式，`codeFree-limit`{.Agda} 则由它推出那条阶段条件。`NameAt`{.Agda} 是落在诸位上的名字，即一个落在极限阶段且不带常量的骨架、一个定义域为元数的载体之上参数序列，以及一个写成**单次** `extAt`{.Agda} 的指称，其条件读的是 `satGraphAt`{.Agda} 在「由元数与骨架造出的键」处所指派的取值；有两个码集以位的身份抵达它：载体处那一个，没有它，图那张作存在绑定的表什么也钉不住；以及空字母表处那一个，没有它，那个骨架就不是元层面某个名字的骨架。`≺At`{.Agda} **不跑自己的递归**：码用一个对着既有之序的隶属原子，元数用一个数码之间的隶属原子，参数用一次有界字典序量化，而那两个序都以位的身份抵达这条描述。`StepAt`{.Agda} 是这一族的一步，按最小名字给出，只有**一**支，故计划当初想要的最小差公式并不需要。`order-in`{.Agda} 与 `order-out`{.Agda} 是那两半适足性，落在变元环境的变元位上：只要每个关系位都带着「它持有的是哪个序」这条假设，那条公式对两个名字的数据成立，当且仅当 `_≺ₙ_`{.Agda} 对那两个名字成立；参数那个键由一次归纳架桥，把首次相异与命名那一章对向量的递归认同起来。
- `L.Choice.Table`{.Agda}：那个序，由描述变成**对象**，每个序数处一个。`Related`{.Agda} 是所实现的那个类，即一个阶段的两个成员所成的、被那里的序所关联的诸对；那次比较是截断着携带的，因为严格良序并不已知是命题值的，而 `strict`{.Agda} 一举为每一个这样的序把截断脱下来，办法是在消去任何东西之前先按三歧分情形。`ApproxAt`{.Agda} 与 `GraphAt`{.Agda} 是逼近与它的图，形状取自 `L.Coding.Sequence`{.Agda}，但对那条步进条件保持通用；该条件以参数身份取两种形式、只有一个含义进场：落在诸位上，因为图必须绑定它所查阅的那张表；以及落在常元上，因为分离是用单自由变量的公式去雕的。`approx-val`{.Agda} 靠在实参上的一次沿成员的归纳，把逼近所记录的每个取值钉住，任何地方都没有单值性假设，而 `approx-uniq`{.Agda} 是那条推论。`tableAt`{.Agda} 是那个构造，在它被造出之处封印，且与层级那一章不同，它在每个序数处携带**两**样东西：其以下诸关系的表，经 `mereFunct`{.Agda} 由替换收拢；以及它那里的关系，从一个界上分离出来，因为阶段处的序没有可供当场拿出的元语言词项。那个界只花一次诉诸，因为一个阶段的两个成员所成的诸对是 `L` 元素的一个**小**族，故 `smallDom`{.Agda} 一举把它们全部禁闭。`rel-fill`{.Agda}、`rel-rep`{.Agda}、`ixRel-fill`{.Agda} 与 `ixRel-rep`{.Agda} 把**任何**实现该类的集合的隶属，读在「阶段的成员到场时的两种形状」上，其中第二种正是分离与命名那一章的参数序共同消费的那一种；把它们陈述为「任何实现该类的集合」，正是使它们比那个构造**早**一个阶段可用之处，而命名那套机器要的就是那里；`relL-fill`{.Agda}、`relL-rep`{.Agda}、`ix-fill`{.Agda} 与 `ix-rep`{.Agda} 则是那四条在本章所造的集合处的实例。留待解决的是那条步进条件自身的适足性，即上一章的 `StepAt`{.Agda} 对着元层面那一步，此处以 `Described`{.Agda} 的两条假设之名点出。
- `L.Choice.Faithful`{.Agda}：把描述做成忠实的，并把那个框架的两条假设解除到只剩一条。`BirthAt`{.Agda} 是**诞生阶段**在对象语言中的说法，它不点名任何常元，也不需要后继运算：那一位处的塔不装这个集合，而那座塔的可定义幂集装它，而 `Lset-suc`{.Agda} 使这两条等价于「比包含它的最小阶段低一级」，且只花在元层面一侧。`BirthAt-out`{.Agda} 与 `BirthAt-in`{.Agda} 是它落在变元位上的两条读式，唯一的假设是序数性，其中可靠性是一次对着最小阶段的三歧分情形，写成一个具名辅助。`isCodeAnyAt`{.Agda} 是**任意**元数处、落在一位所持载体上的码谓词，而它是**实例化、不是构造**：元数绑定那个合取项与见证那个合取项都早已存在，新的只是它们的会合；`CodesAt`{.Agda} 是它们雕出的那个集合，一次 `extAt`{.Agda}，其两条读式把那一位钉在该载体之上的码集上，于是命名描述的码集那一位由描述钉住、而不由外部的一条等式钉住。`order-unfold`{.Agda} 是序之族在一个阶段处的定义方程，即在递归的计算规则上作的一次 `cong`{.Agda}；`bornIn`{.Agda} 是 `birth-in`{.Agda} 的逆，它为这条描述省下一层绑定；`stepMoved`{.Agda} 沿载体之间的一条等式搬运一次步进比较，是就地重建、而不是伸手去另一个模块里够。`CondCore`{.Agda} 是阶段处的序被完整描述出来，以诞生阶段为主键，对步进条件保持通用：它绑定四个集合，把阶段取作**词项**，使得常元那一形式不花绑定，且**在被造出之处封印**。`Cond`{.Agda}、`Cond₀`{.Agda}、`cond-spec`{.Agda} 与 `cond₀-spec`{.Agda} 是上一章那个框架所索取的两种形式连同它们的含义，于是 `Described`{.Agda} 可以施用，它所证的一切都可取用，条件只有那个步进参数、别无其他。本章记下四条实测，因为每一条都是定律、不是偏好：诞生描述所满足于其上的那两个元素必须封印 (178 秒对 2 秒)、环境必须写全而不可缩写 (207 秒对 3 秒)、结论落在满足关系上的两路分情形必须是具名辅助而绝不可用 `with`{.Agda} (超过 300 秒)、以及读在诸常元上的描述必须在被造出之处封印 (每条读式 160 秒)。不在此处的，是那一步自身的适足性，即 `L.Choice.Internal`{.Agda} 的 `StepAt`{.Agda} 对着 `stepAt`{.Agda}，它以参数 `Stp`{.Agda} 的身份进场，`stp-out`{.Agda} 与 `stp-in`{.Agda} 是它的含义：前者取用表在该载体处所记录的**每一个**取值上的正确性，因为它所读的那条条件可能自己绑定了一个取值；后者取用「实现那里的序」的单个取值，因为那正是它要塞进去的东西。
- `L.Choice.Adequate`{.Agda}：那一步自身的适足性，对着命名那一章的比较。`paramSeq-in`{.Agda} 与 `paramSeq-out`{.Agda} 是参数那个合取项的两个方向：载体之上的一个向量，就是它之上一个定义域为元数的环境；而任何这样的环境都能被读回成一个向量，且**不带截断**，因为某个序号处的条目是命题，而一个取值的索引是一条纤维，故一分有穷选择也不花。`envAt`{.Agda}、`numAt`{.Agda}、`keyAt`{.Agda} 与 `valAt`{.Agda} 是指称那个合取项所满足于其上的四个元素，在被造出之处封印；`codeEl`{.Agda} 与 `envEl`{.Agda} 是另外两个，供最小名字描述所携带的那个全称使用。`Named.Body.denote-fill`{.Agda} 与 `Named.Body.denote-read`{.Agda} 是指称的两个方向，长四环：扩张后的环境是被推到诸参数前面的那个成员，它的长度是元数加一，键是那个长度与骨架之对，而图在那里的取值就是载体之上的满足关系。`NameAt-fill`{.Agda} 与 `NameAt-read`{.Agda} 把五个合取项装配成一个元层面名字、又拆回来；`Least.Min.LeastAt-fill`{.Agda} 与 `Least.Min.LeastAt-read`{.Agda} 对最小名字做同样的事，那个全称在「一个名字自己的三样数据」处实例化；而 `Least.Step.StepAt-fill`{.Agda} 与 `Least.Step.StepAt-read`{.Agda} 是那一步，即两个最小名字加一次比较。`leastPin`{.Agda} 靠最小元的唯一性，把「这条描述称作最小」的那个名字与 `leastName`{.Agda} 交回的那个认同起来。这一切都站在上一章留下的那个框架里：每个关系位都带着「它持有的是哪个序」这条假设。三次实测，每一条都是在新地方遇上的旧规矩：适足性等式的**复合**无法由「对着写出来的类型」的一次代换交割，任何实参都不行、变元也不行 (`denote-table`{.Agda} 400 秒跑不完，而它的两个因子 `denote-mem`{.Agda} 与 `val-sat`{.Agda} 各自 2.4 秒交割)，故复合逐因子消费；六层绑定那一块要求它的环境被写开，不可用 `where`{.Agda} 缩写 (超过 400 秒对 20 秒)；而六重存在的载荷经 `StepOf`{.Agda} 读出，绝不经手写的 Σ。在 `L.Choice.Table`{.Agda} 的结果成为无条件之前仍然缺席的东西，本章据实点名：那个框架里为**诸码**所设的关系位，要的是作为 `L` 之元素的 `limitOrder`{.Agda}，而至今无人造出它。
- `L.Choice.Limit`{.Agda}：极限阶段诸成员上的序，作为 `L` 的一个元素，而这正是内化那个框架里**为诸码所设的位**一直索取的东西。`LevelAt`{.Agda} 是层号在对象语言中的说法，三个合取项，且除 `ω` 外不点名任何常元：那一位持有 `ω` 的一个成员、那里的塔装着这个集合、而没有更小数码的塔装它。两条读式都站在变元位上，而层号以**变元数码**的身份到场、携带它自己的定义等式，这正是 145 秒与 1.8 秒之差，因为层号是一场经典可及性递归，而槽位处的转换检查把它撬开。`PrecedesAt`{.Agda} 是最先分歧处那次比较的单独一步，其中不含任何具体之物：基底关系与基底阶段被握在槽位里，故这条描述能站在「关系是某场递归之取值」的地方；而基底关系的那次隶属经 `appAt`{.Agda} 抵达，因为对是被描述的、不是被点名的。`strictLimit`{.Agda} 先按三歧分情形，把一次比较上的截断脱下来。`LimitOrdAt`{.Agda} 把两个键接成一个析取，第一支绑两个层号并按隶属比较它们，第二支绑**一个**，于是层号之间的等式根本不进对象语言。`pairsBound`{.Agda} 经 `smallDom`{.Agda} 把那个序可能关联的每一个对都禁闭起来，而 `codeOrder`{.Agda} 是从它上面分离出来的、在造出之处封印；`codeOrder-fill`{.Agda} 与 `codeOrder-rep`{.Agda} 是两条表示引理，而 `CodeKeys.AtParams`{.Agda} 就是 `Adequacy.Keys`{.Agda}，其为诸码所设的位由它们填上，实参相同，中间不设转接。这一切都以**一条**假设为条件，即 `BeforeAt`{.Agda} 连同它对着 `before`{.Agda} 的两条读式，也就是沿诸数码的那族最先分歧之序在内部的说法：一场取值为关系的递归，故要说的是逼近；它比塔便宜，因为索引是 `ωʟ`{.Agda} 的成员，而那一步已经写好。两次实测，每一条都是在新地方遇上的旧规矩：一次分情形，若其被检者是某个**束**的比较、而其结论是一个满足关系，就跑不完，而写在一个显式的和上、诸支具名，则不花分文 (超过 300 秒对 2.4 秒)；以及那条接合起来的描述必须**在造出之处封印**，因为分离的那条条件会在两层绑定之下把它展开 (超过 300 秒对 2.7 秒)。
- `L.Choice.Before`{.Agda}：最先分歧之序的那一族，内化，它兑现了上一章赖以立足的那条唯一假设。`relAt`{.Agda} 是每个数码处的那个关系，作为 `L` 的一个元素，即在那个有穷阶段的诸对之上、用上一章那条步进描述雕出的一次分离，而那条描述的两个槽位被绑定、并**用对象等词钉在诸常元上**，于是一条描述同时服务于那次分离与那个图；`relAt-out`{.Agda} 与 `relAt-in`{.Agda} 是它的两条读式，对数码作归纳一并证出，每个方向都在前趋处花掉另一个，因为上一个关系只在一致性子句内部被查阅，而 `precedes-map`{.Agda} 反变地搬运那次比较。`RelBodyAt`{.Agda} 是那一步，对成员、索引与逼近保持通用，其中前趋说成索引的 `∈`-**极大**成员，故不需要对象等词，而那一步恰好在这场递归为空之处 (零处) 为空。`RelStepAt`{.Agda}、`ApproxAt`{.Agda} 与 `RelGraphAt`{.Agda} 照 `L.Coding.Sequence`{.Agda} 而来，不带单值性合取项；`step-rel`{.Agda} 与 `rel-step`{.Agda} 是通往元语言的那座桥，`approx-val`{.Agda} 靠一次良基归纳把逼近所记录的每个取值钉住、且单值性在任何地方都不是假设，而 `rel-only`{.Agda} 是那个图的确定性。`approxSet`{.Agda} 是当场拿出来的那个逼近，**根本不花任何公式**，因为某个数码以下的逼近是有穷的，只要 `smallStage`{.Agda} 把它的诸成员放进同一个阶段，`finSetL`{.Agda} 就把它张出来；`beforeFam`{.Agda} 是那一族，沿 `ωʟ`{.Agda} 的一次替换，在造出之处封印，而它的两个方向陈述成对着这场递归、不对着任何公式。`BeforeAt`{.Agda} 在某个槽位所持的数码处读出那一族，其中在常元处的应用用 `appAtC`{.Agda}，而被比较的那两个集合**不加禁闭**；有了它，`Described`{.Agda} 便被实例化，于是 `codeOrder`{.Agda} 与 `CodeKeys`{.Agda} 是无条件的。一次实测，本部最大的一次：四条描述必须**在造出之处封印**，因为不封印时，每一次在具体环境上的满足关系都要把一条内部装着两份完整层级描述的公式正规化 (376 秒对 3.8 秒，九十九倍)；而造出那一族的那个框架在高一层遵守同一条定律，办法是交回一个其中不出现任何公式的三元组。
- `L.Choice.Order`{.Agda}：那一步被描述出来，序之表随之变成无条件的。`Stp`{.Agda} 就是那条描述：一条**被封印**的公式，绑定六个集合并钉住两个常量。六个是：阶段处的塔，经 `L.Coding.Sequence`{.Agda} 的 `LsetGraphAt`{.Agda} 抵达；它的可定义子集，经 `L.Coding.Powerset`{.Agda} 的 `DefAt`{.Agda} 抵达，并要求被比较的那两个集合落在其中，那一步的两个隶属分量就是这样到场的，而不必动用谁也没有的一条引理；表在该阶段的取值，经 `appAt`{.Agda} 抵达，正是这一点使那条描述始终读在调用方所持的任意一张表上；以及塔之上的码集，经 `L.Choice.Faithful`{.Agda} 的 `CodesAt`{.Agda} 抵达，而那条描述当初就是为这个槽位写的。用对象等词钉住的两个是 `L.Choice.Limit`{.Agda} 的 `codeOrder`{.Agda} 与空字母表处的码集，因为槽位持有变元，而那两样是特定的集合。落在那七个槽位上的主体就是 `L.Choice.Internal`{.Agda} 的 `StepAt`{.Agda}。`Slots`{.Agda} 供给那一步的适足性的全部六个实参，对那六个集合保持通用、以它们的等式为假设：码那一侧由极限与族两章无条件给出，载体那一侧由 `L.Choice.Table`{.Agda} 在所绑定取值处的诸读式给出，而那正是步进参数自己的假设，也是从外面取的唯一输入。`stp-out`{.Agda} 与 `stp-in`{.Agda} 是对那六个绑定的拆开与装回，与 `L.Choice.Adequate`{.Agda} 的诸步进读式及 `L.Choice.Step`{.Agda} 的两条复合而成，且它们承接了框架的那份不对称：可靠性对表在那里记录的每一个取值作全称，完备性取的是调用方据以实现的那单个取值。随后一行打开 `L.Choice.Faithful.Ordered`{.Agda}，整张表随之变成无条件的：`CondCore`{.Agda}、`Cond`{.Agda}、`Cond₀`{.Agda} 连同它们的两条规格，以及出自 `L.Choice.Table`{.Agda} 的 `StepAt`{.Agda}、`ApproxAt`{.Agda}、`GraphAt`{.Agda}、`approx-val`{.Agda}、`graph-only`{.Agda}、`graph-table`{.Agda}、`tableAt`{.Agda}、`relL`{.Agda}、`relL-spec`{.Agda} 与全部四条表示引理。一次实测，一条定律在新地方的现身：**一个框架所结论于其中的类型，要在它被造出之处封印**，因为把那个框架实例化到描述所绑定的具体元素上会把它正规化，而不封印时那件事跑不完 (超过 200 秒，对全章的 7 秒)。`Bound`{.Agda} 是最后一章据以分离的那个形状：`L` 的一个集合的界层序数、那里的塔的诸成员上的序作为模型的一个元素，以及它的两条表示引理。
- `L.Choice.Transversal`{.Agda}：选择，以及前沿清空。公理取模型 record 陈述它时所用的**横截**形式：成员非空且两两不交的集合，有一个与它每个成员恰交于一点的集合。全程不用 `L` 的良序，因为此处根本没有；集合是小的，故 `L.Choice.Stage`{.Agda} 的界层序数一举装下该族、它的成员与它们的成员，而 `L.Choice.Order`{.Agda} 的 `Bound`{.Agda} 供应那里的塔上的序作为模型的一个元素。`Pick`{.Agda} 是那条描述，一个自由变元与两个常量：该族的某个成员含有这个集合，且那个成员中没有任何东西排在它之前；那个序用对象等词钉在一个槽位上，因为「一个对属于某个关系」这条原子是从槽位取那个关系的。`pick-in`{.Agda} 与 `pick-out`{.Agda} 是它对着 `L.WellOrder.Base`{.Agda} 的 `IsLeast`{.Agda} 的两条读式，每个截断载荷都有名字。`transversalSet`{.Agda} 是模型自家的分离据它在那座塔之上雕出的东西，而 `transversal`{.Agda} 数清它与每个成员之交：存在性来自 `leastOf`{.Agda}，即那场自写下之日起一直没有消费方的极小元搜索；唯一性来自两两不交，而全书别无他处用到它，经 `isPropLeastOf`{.Agda} 得出。对所供给的那个 ZF 模型的依赖，只是沿交的规格的一次搬运。`hasChoiceL`{.Agda} 就是模型的选择字段，于是登记簿清空，`L.Frontier` 连同根章的第二个参数一并删除。一次实测，且是一条定律偏偏没有咬人：读在常元上的描述要在被造出之处封印，这条定律在被发现之处值九十九倍，在此处则一文不值 (封印与否都是 2.3 秒)，因为这条描述不携带任何已编码的语法；封印仍然保留，而那个数字被记下来，因为这条定律关乎的是一条描述装着什么。
- `L.Model`{.Agda}：根章：诚实的相对一致性表述；外延与正则沿传递性下降；`L⊨ZF`{.Agda} 与 `L⊨ZFC`{.Agda} 合龙，唯一假设是排中律。本章曾以第二个参数收下的债务登记簿 `L.Frontier` 已不复存在：它开张十一个字段，缩过六次，随着清空它的那一章一并删去。
<!--/-->

```agda
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
## The rud trunk (under construction)

The `[L3.31]` build: the rudimentary-functions architecture adopted by the
L3.30 ruling, growing alongside the delivered routes until the coexistence
measurement. Wired chapter by chapter as the wave batches land.

- `L.Rud.OrdArith`{.Agda}: the ordinal case structure the S-recursion consumes:
  successor and limit predicates, the classical trichotomy, successor
  injectivity on ordinals.
- `L.Rud.Ops`{.Agda}: the basis operations F0-F7 and F9 with their two-direction
  extension specifications, sealed at birth.
<!--zh-->
## rud 主干 (在建)

`[L3.31]` 建设：L3.30 裁决采纳的 rud 函数架构，与既有路线并存生长，直至共存测量。各波次批落地时逐章接线。

- `L.Rud.OrdArith`{.Agda}：S-递归所消费的序数分情形结构：后继与极限谓词、经典三分、序数上的后继单射性。
- `L.Rud.Ops`{.Agda}：基底运算 F0-F7 与 F9，带双向外延规格，出生即封印。
<!--/-->

```agda
import L.Rud.OrdArith
import L.Rud.Ops
```
