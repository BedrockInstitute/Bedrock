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
  trichotomy: the choosing device the axiom of choice will take. Reflection was
  expected to be a second consumer and is not; nothing imports this chapter yet.
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
  `Lset-suc`{.Agda} identifies the successor stage with the definable powerset
  of its predecessor, which is what puts that powerset in `L` as `𝒟ₒS`{.Agda}.
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
- `FOL.Coding`{.Agda}：语法作为集合：`⌜_⌝`{.Agda} 把构造子序号贴在各部分的码上 (常量编码自身)，而归纳关系 `Codes`{.Agda} 是接口，使码值不出现在类型检查器必须归一化的等式里。
- `V.Coding`{.Agda}：层级兑现编码的两组参数：数码单射 (`#-inj`{.Agda})、Kuratowski 对单射 (`pr-inj`{.Agda})，于是 `V` 上的公式成为 `V` 的集合。
- `L.Definability`{.Agda}：那一步：`Def A`，带 `A` 中参数可定义的 `A` 的子集之集：语法当索引集，内层满足给含义，本质小性买单；`A ∈ Def A` 恒成立，传递性下 `A ⊆ Def A`。
- `L.Constructible`{.Agda}：沿成员递归的塔 `Lset`{.Agda}，一条方程通吃零、后继与极限；层谓词 `isLayer`{.Agda} 与 `layer-trans`{.Agda}；类 `isL`{.Agda} 与结构 `𝒮ʟ`{.Agda}。
- `L.Ordinal`{.Agda}：闭包论证所需的序数供给：零、后继、小并皆序数，而 `boundingOrd`{.Agda} 以单一序数界住任一小族。不含比较，故不花费经典逻辑。
- `L.Rank`{.Agda}：沿成员递归的 von Neumann 秩，取值于层级自身：`rank-ord`{.Agda} 使它成为以序数进行的度量，`rank-fix`{.Agda} 认证它为典范索引。
- `L.Ordinal.Linear`{.Agda}：三歧 `ord-tri`{.Agda}，以及随之而来的 L 侧经典边界：闭包从不需要判定什么，比较则需要，故本章把排中律取作模块参数。
- `L.Ordinal.Stages`{.Agda}：`Lset α` 中的序数恰是 `α` 的成员：`rank-Lset`{.Agda} 与 `ord∈Lset→∈`{.Agda} 说无一提前现身，`ord∈Lset-suc`{.Agda} 说无一迟到。
- `L.WellOrder.Base`{.Agda}：作为束的严格良序 (`SWO`{.Agda})，与非空子集的极小元 (`leastOf`{.Agda})，经三歧唯一：选择公理将要取用的那件选取装置。反射本来预期是第二个消费方，结果不是；本章目前无人 import。
- `L.Coding.Base`{.Agda}：从内部读码：`allCodes`{.Agda} 把每条无参公式的码汇成一个可命名的集合，而 `prAt`{.Agda} / `tagAt`{.Agda} 以有界形式解构 Kuratowski 对与标签，皆 Δ₀ 且适足。
- `L.Coding.Environment`{.Agda}：环境即其图，经 `lookup-spec`{.Agda} 而函数性；`memPairAt`{.Agda} 查出一个值，`sucAt`{.Agda} 认出量词之下的序号移位，`seqSet`{.Agda} 汇集一个集合上的全部有穷序列。
- `L.Coding.Tagged`{.Agda}：携带元数的码，使量词的子句能谈论其子公式的元数；`tagPairAt`{.Agda} 匹配每个二元构造子的码所具有的形状。
- `L.Coding.Length`{.Agda}：把证书的元数分量与其环境长度系住的守卫；`lenAt-len`{.Agda} 钉死那个本来自由的数，正是它把垃圾挡在诸证书之外。
- `L.Coding.Entry`{.Agda}：「这个元数、码与环境记录在这份证书里」的唯一形式 `tripleInT`{.Agda}，诸子句都经它读写自己的条目。
- `L.Stage`{.Agda}：满足任意序数性质的最小序数，经良基下降得到、经三歧而唯一；包含可构造集的最早阶段是它的头一个实例，已封印，故那次下降永不抵达日后的转换问题。
- `L.Axioms.Basic`{.Agda}：头五个模型字段。外延与正则沿传递性下降；唯一性随即白拿；空集、配对与并则各由一条公式从一个阶段中刻出。`finSetL`{.Agda} 把配对的论证推广到取自某阶段的任意有穷族，递归的取值表正是这样抵达 `L` 的。`Lset-suc`{.Agda} 把后继阶段与前一阶段的可定义幂集认同，正是这一点把那个幂集作为 `𝒟ₒS`{.Agda} 放进 `L`。
- `L.Axioms.Separation`{.Agda}：Δ₀ 公式的分离与替换，在装下实参与公式全部常元的阶段上；其内容是「属于刻出的集合就是在模型中满足」。
- `L.Reflect`{.Agda}：Montague 的论证，在一个集合之内回答真类大小的存在量词。**梯**是上升的序数链；若每一级的环境其作答阶段都落在下一级上，则它的极限为自己包含的每个参数元组反射那个存在量词。`Single`{.Agda} 是单矩阵的梯。取最小阶段而非最小见证，正是把 L 的良序挡在门外的那一手。
- `L.ReflectFo`{.Agda}：整条公式的同一件事，经结构归纳。联合造出的梯一举为公式的每个矩阵作答，而 `mkReflect`{.Agda} 随即点名一个阶段，公式在其上与它到该阶段的相对化一致：以 Δ₀ 加一个阶段，换下任意的复杂度。
- `L.Axioms.Numerals`{.Agda}：`L` 之内的数码链，经投影等式钉在层级的数码上。全然构造性，这正是它独立成章的理由：排中律只在收集那一步进入无穷公理。
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
import L.Axioms.Power
import L.Absoluteness
import L.Coding.Model
import L.Coding.InL
import L.Coding.Closed
import L.Recursion
import L.Coding.Recursion
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
import L.Coding.Satisfaction
import L.Coding.Uniform
import L.Coding.Powerset
import L.Coding.Sequence
import L.Hierarchy
import L.Axioms.Numerals
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
- `L.Coding.Satisfaction`{.Agda}: the instance. The slot is the domain, the graph
  is the previous chapter's, and the two halves meet in `funct`{.Agda}: existence
  hands the graph the objects already built, uniqueness pins any table the graph
  accepts against the one the meta-level recursion built.
- `L.Coding.Uniform`{.Agda}: the same satisfaction over **the codes at a stage**,
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
- `L.Coding.Recursion`{.Agda}: the first instance of the internalization theorem.
  Its graph says "the least closed set containing this key", because an object
  language with no table to hold subvalues cannot say "built from the values at
  the subcodes"; least makes the value unique by antisymmetry, so uniqueness
  costs one extensionality and no induction, and `funct`{.Agda} is filled through
  `mereFunct`{.Agda}.
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
- `L.Frontier`{.Agda}: the debt registry, opened at eleven fields and down to
  one, the verbatim
  statement of a model field at `𝒮ʟ`; proven fields get deleted, and the book
  is done when the record is empty.
- `L.Model`{.Agda}: the root chapter: the honest relative-consistency framing;
  extensionality and regularity descend along transitivity; `L⊨ZF`{.Agda} and
  `L⊨ZFC`{.Agda} assembled from the frontier.
<!--zh-->
根，今日陈述，余部完成：

- `L.Axioms.Full`{.Agda}：任意公式的分离与替换，办法是反射那条公式，再把有界的器械施于它的相对化；那个禁闭原子正是使替换的像逃不出阶段的东西。
- `L.Absoluteness`{.Agda}：两门对象语言之间的桥。常元可构造的、关于层级的 Δ₀ 公式，经 `liftFo`{.Agda} 运进 `L` 的语言，而 `transferFo`{.Agda} 说两者说的是同一件事；编码诸章留在层级一侧，从此处被引用。
- `L.Coding.Model`{.Agda}：模型之上的对象语言。「函数」的含义 (`prAtL`{.Agda}、`appAt`{.Agda}、`svAt`{.Agda}、`domAt`{.Agda})、取值一侧的对、标签读式、环境，以及 `extAt`{.Agda}：每条集值子句的写作框架，其两种读法就是它的两个投影。无常元的读式经桥引用；点名数码的读式直接写，因为无界如今免费。
- `L.Coding.InL`{.Agda}：每个码都是 `L` 的元素，沿构造子的一次归纳，里面什么也没有。正是它使一个码可被点名为模型对象语言的常元，使一族码可充当已内化递归的定义域。**全体**码之集刻意未证，此处也不需要。另有 `closure`{.Agda}，一条公式的诸子公式键构成的有穷集；`closure-inv`{.Agda} 把它读回来；以及 `byTag`{.Agda}，它把十二个构造子与封闭性谓词提出的八项要求对上一次，而非对上十二乘八次。
- `L.Coding.Closed`{.Agda}：闭包满足对象语言的封闭性谓词，且是满足它的最小者。四个读式的八个实例，再加一次归纳；前者是「对一条公式的诸子码作递归」关于其索引集所需的那条假设，后者是它的取值唯一的理由。那八条子句从不看一条公式，故只对任意可**剥开**的集合证一次 (`Peel`{.Agda}：一个成员仅仅是某条公式的键，而那条公式自己的闭包坐落于内)，而 `closureClosed`{.Agda} 就是 `closedOf`{.Agda} 落在闭包处、以 `closure-inv`{.Agda} 充当剥开。此处的一般性免费，因为 `byTag`{.Agda} 本就是对着任意目标集写的。
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
- `L.Coding.Satisfaction`{.Agda}：那个实例。槽作定义域、图取自上一章，而两半在 `funct`{.Agda} 处会合：存在性把已经造好的对象递给那个图，唯一性把图所接受的任意一张表对着元语言递归造出的那个钉死。
- `L.Coding.Uniform`{.Agda}：同一个满足关系，跑在**某阶段处的诸码**之上，而那才是每个消费方想要的定义域：以一条公式的槽为索引，就是一条公式一张表，而消费方到场时手里握着的是一个码、而非「它是其子码」的某条公式。`AllCodes`{.Agda} 作定义域，而索引集那笔债由成员自己那条公式的槽偿付，其余一概不动，因为那个图把自己的表**存在**绑定：`funct`{.Agda} 只需拿出**某张**装着该成员的合格的表，而最小的一张就是该成员自己那条公式的子公式槽。故 `Table`{.Agda}、`Slot`{.Agda}、`Sound`{.Agda} 与 `Unique`{.Agda} 都按既有类型施用，而登记在案的那次「在载体与键之对处重新索引」从未发生。唯一新的东西，是把两套编码接起来：层级的编码落在该阶段的字母表之上，模型的编码落在模型的语言之上；用的是 `codeBridge`{.Agda} (为此而写、至今未用) 加上重标的函子性。`val-at`{.Agda} 在一个以键的形式给出的成员处读出取值，`val-sat`{.Agda} 说那个取值**就是**载体之上的满足关系，而 `val-defSet`{.Agda} 把它落到元数一处的可定义幂集上。码载体与环境载体保持为彼此独立的参数，只在满足关系有含义之处被钉在一起。每条读式都把成员取作**变元**、把它的键等式放在旁边，而消费方本会改写的那个名字 `keyIn`{.Agda} 在它被造出之处封印：一旦把键写开，那个构造就落进一个满足关系里面，而无论证明写多长都展开不了。
- `L.Coding.Graph`{.Agda}：满足关系那个递归的图说了什么。三个存在量词分别管索引集、表与载体，由封闭性、全性与十二条子句设防，取值则从表上读出。一切都被绑定，因为一个图不可以点名一张尚未交给它的表，而那是内化定理唯一禁止的事。一个框架带两个实例，因为那条用来钉住的子句就是框架的参数：`satGraphAt`{.Agda} 把载体取作**一位**，供载体本身就是被绑定变元的消费方使用；而 `satGraph`{.Agda} 把它钉在一个常元上，按它一贯的类型与见证元组交付。
- `L.Coding.Powerset`{.Agda}：可定义幂集在对象语言中、落在一个作为**槽位**的载体上的描述，也是整条路线为之存在的那一步。内部层级把自己的阶段绑定起来，故一条点名了自己载体的描述在那里压根说不出口；`DefAt`{.Agda} 什么也不点名。它说的是：`u` 恰是那些 `x` 之集，对它们仅仅存在载体之上的一个码 `c` 与一个取值 `v`，使得 `v` 就是满足关系那场递归在 `c` 处所记录的东西，而 `x` 是「其单条目环境落在 `v` 中」的那些载体成员之集。两个存在量词**相邻**，而这是一次探针逼出的更正：若被一个合取项隔开，码那条假设与满足关系那条假设就落到不同的环境上，于是这条路线会平白背上一条它本来永远用不着的弱化引理。`DefinesAt`{.Agda} 是单拿出来的第三个合取项，`envOneAt`{.Agda} 是单条目环境，只有一行，因为长度为一的图只是一个对。`DefAt-in`{.Agda} 说这个算子满足那条描述，`DefAt-out`{.Agda} 说别的东西都不满足，后者在 `DefOK`{.Agda} 之下：描述里的每个存在量词都在 `L` 上取值，只够得着住在其中的东西，故这条描述恰在「载体的诸可定义子集皆可构造」之处适足。那个旁条件只是消去那一半的假设，因为引入自己的假设已蕴含它；而在一个阶段处，它由后继恒等式一劳永逸地解除，剩下 `DefAt-stage`{.Agda}：一条真值之间的等式，说这条描述对 `𝒟ₒS`{.Agda} 成立、对别的什么都不成立。
- `L.Coding.Sequence`{.Agda}：把层级说成一条**序列**，而这是为它写图时唯一可取的形状。一个图不可以点名它所定义的对象，而塔在某个阶段处是由该阶段以下的塔造出来的，故写下来的改为「*逼近*是什么」。`StepAt`{.Agda} 是某个实参处的那一步：一次 `extAt`{.Agda} 罩住三个相邻的存在量词，即那个实参、逼近在其处所记录的取值，以及它的可定义幂集；最后一样被绑定而不被点名，因为上一章交付的是关于它的一条描述、而不是指称它的一个词项。用一次 `extAt`{.Agda} 而不用手写的一对包含，因为一对包含会把那三个存在量词复制一份，并把每一种读法拆成互非逆的两半交回来。一个旁条件 `PowOK`{.Agda} 服务两个方向，因为一个「是 `L` 的元素」的可定义幂集，也就是一个「诸成员皆可构造」的可定义幂集。`ApproxAt`{.Agda} 是两个合取项、再无其他：`f` 恰好定义在那个实参的诸成员上，且它所记录的每个取值都是「在那里、由 `f` 自身算出的那一步」。它是一条隶属**等价**、而非一个单向的收集，这使即将到来的那场归纳的动机保持为命题，并把一条内部的函数外延性引理从路线上移除；且它**不带单值性合取项**，因为步进条件已经把「在一个实参处记录的每个取值」钉住了，故单值性是一条推论，而不是三个置于满足关系之下的全称量词。`LsetGraph`{.Agda} 把逼近绑定在两者之上。**本章的全部代价都出在转换上**：两条图读法陈述在具体位上，花掉了 130 秒中的 98 秒；而每一处「假设把环境写开、应用却把它藏在一个缩写背后」，再各花 15 秒。写成两侧是同一个表达式之后，它在两秒之内检查完毕，而这把「变元实参」那条规矩从一次代换推广到一条**陈述**。
- `L.Hierarchy`{.Agda}：上一章那个图，被对着本书真正造出的那座塔证明，以及用来证明它的那个**内部层级**。**表**是有序对之集；它在某个集合上正确，指它在该集合以下所记录的每个取值都是元层面的塔在那里的取值；它完备，指它在以下的每个实参处都记录了一个。`step-Lset`{.Agda} 从一张正确的表上读出一个被满足的步进、把塔取回来，`step-table`{.Agda} 则由它写出那一步，而上一章那个旁条件在两者之内一并解除，因为被记录的取值是塔在某个序数处的值，而阶段的可定义幂集可构造。`approx-val`{.Agda} 是在实参上的一次沿成员的归纳，其动机对**一切**被记录的取值作量化，故单值性从不作为假设，而 `approx-uniq`{.Agda} 三行落地。`Lset-only`{.Agda} 与 `Lset-defines`{.Agda} 是那个图的两个方向，而 `hierL`{.Agda} 是后者据以造出的东西：由「序数与塔在它那里的取值」所成之对的集合，经在一个**成对的图**上作替换而收拢，每个索引的序数性取自 `mem-ord`{.Agda} 且不加截断，函数性经 `mereFunct`{.Agda} 偿付。它的规格是一条**隶属等价**，这使它唯一、也使归纳的动机是命题，而它在被造出之处封印。两次测量，都关乎一个名字：成对的那个图以变元身份进场、随身带着它自己的等式，而不是以那个闭句子的身份进场，价值 85 秒；以及 `mem-ord`{.Agda} 的那个集合实参必须在每次使用时显式给出，因为 `IsOrd`{.Agda} 展开成一条带量词的隶属关系、什么也确定不了。本章正是 `L` 的内部定义的材料，而内部良序就从它上面读出。
- `L.Coding.Recursion`{.Agda}：内化定理的第一个实例。它的图说的是「含有此键的最小封闭集」，因为没有一张表托着诸子取值的对象语言说不出「由诸子码处的取值造出」；「最小」经反对称性使取值唯一，故唯一性只花一次外延、不花归纳，而 `funct`{.Agda} 经 `mereFunct`{.Agda} 交付。
- `L.Axioms.Power`{.Agda}：幂集字段，经「界住诸可构造子集、雕出一个阶段」证得。**未用凝聚，也不需要**：公理索取的是「诸可构造子集构成一个集合」，而非「它们现身得早」。
- `L.Recursion`{.Agda}：`L` 的集合上，图可表达的函数，其表在 `L` 中。这是任意公式替换的推论，而非定理：通常那套绝对性纪律是为了让一张表在**某个阶段之内**可读，而此处没有任何东西在阶段之内读。递归留在它被写下的元语言里；`smallDom`{.Agda} 为任意小族供给定义域，而 `Definition`{.Agda} 把一个实例归约为一条定义公式连同它的适足性。`witnessInModel`{.Agda} 记下图必须遵守的那一条规矩：对象语言的存在量词在 `L` 上取值，故一个图不可以靠断言被描述者本身存在来描述它。
- `L.Frontier`{.Agda}：债务登记簿，开张十一个字段，如今只剩一个，是模型字段在 `𝒮ʟ` 处的原文陈述；字段证毕即删，簿清则书成。
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

