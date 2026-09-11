# Owner's exploration note on the rud route (reference material)

Current Bedrock status (2026-09-06): `L⊨ZFC` and `L⊨GCH` are proved and
registered in [Milestones](../../src/Milestones.lagda.md). The research and route
assessments below are historical; they do not describe open Bedrock proof goals.

Provenance: the owner's own exploration in a separate Claude chat, recorded
2026-08-02 as reference input to `[L3.30-D1]` (the digestion document) and
`[L3.30-M]` (the design memo). Recorded verbatim except for repository-mandated
punctuation fixes (em dashes and full-width parentheses are banned repo-wide).
`[L3.30-D1]` must verify the mathematical claims here against the primary sources like
any other input; where this note and a primary source disagree, the source
wins and the discrepancy is reported.

---

## 简短结论

**是**，Gandy–Jensen 定理让 rud 成为哥德尔运算的规范形态；**AC、GCH、精细结构**都能且应当建立在其上。**但地质学不行**：那是正交的另一套基础设施，rud 在那里几乎不提供杠杆。

## rud 是不是「正统形态」

Gandy–Jensen：$F$ 是 rud $\iff$ $F$ 是哥德尔运算的复合。这把「随手挑的十个运算」提升为一个有内在刻画的函数类 ($\Delta_0$ 可计算)，现代文献 (Devlin、Zeman、Schindler、Jech 后期章节) 确实一律用 rud 表述。

但要注意「rud」实际上是一族东西，做基础设施时必须一开始就分清：

- **rud 函数**本身；
- **rud 闭包** $\mathrm{rud}(X)$，及关键引理 $\mathrm{rud}(X)\cap\mathcal P(X)=\mathrm{Def}(X)$ ($X$ 传递)；
- **$\mathrm{rud}_A$**：带谓词的相对化版本，$J_\alpha^A$ 与 extender model 必需；
- **simple functions** (Jensen)：保持 $\Sigma_n$ 可定义性的更强类，$\Sigma^*$-理论要用；
- **$S$-层级**：$S_{\nu+1}=S_\nu\cup\{S_\nu\}\cup\bigcup_i G_i{}''(S_\nu\times S_\nu)$，$J_\alpha=S_{\omega\alpha}$。

最后一项常被忽略但是枢纽：$\mathrm{rud}(X)$ 作为「闭包」本身不是逐步的，而 $S$ 把生成过程摊成 $\omega$ 步，于是「$y=S_\nu$」是**一致 $\Sigma_1$** 的。所有后续可定义性红利都从这里出。

## AC: rud 恰好是对的工具

正是「有限多个生成元」这一点使 $<_L$ 成为纯代数构造：给定 $<_\nu$ 良序 $S_\nu$，由

$$x <_{\nu+1} y \iff \langle i, \text{参数对}\rangle_x <_{\text{lex}} \langle i,\text{参数对}\rangle_y$$

递归地延拓，$i$ 跑遍 9 或 10 个下标，不需要良序公式集，不需要语法编码。$S$-层级保证这个递归是 $\Sigma_1$ 的，于是 $<_L$ 一致 $\Sigma_1$，这既给出 $L\models\mathrm{AC}$，也是后面 $\Sigma^1_2$ 良序 $\mathbb R^L$ 的来源。

对形式化尤其友好：$\mathrm{Con}(\mathrm{AC})$ 这条线上你可以完全不碰满足关系。

## GCH：需要 $J$ 而不只是 rud

凝聚引理 $X\prec_{\Sigma_1}J_\alpha \Rightarrow$ 坍缩 $\cong J_\beta$，依赖三件事：

1. $J_\alpha$ rud 闭 ($L_{\beta+1}=\mathrm{Def}(L_\beta)$ 连配对都不封闭)；2.「$y=J_\beta$」一致 $\Sigma_1$ (来自 $S$-层级)；
3. $J$-结构有一致可定义的 $\Sigma_1$ Skolem 函数 ($\Sigma_1$ 一致化在 rud 闭的可修正结构上成立)。

拿到凝聚后 GCH 是标准的 Skolem 包-坍缩论证。$|J_\alpha|=|\alpha|$ ($\alpha\ge\omega$) 让基数计算干净。

## 精细结构：这就是它的存在理由

$\rho_n^\alpha$、master code $A_n$、standard parameter、$\square_\kappa$、morass、$K$ 的构造，全部预设 $J$ 层级。核心机制：

- **可修正性 (amenability)** $(J_\alpha,A)$，需要 $\mathrm{rud}_A$；
- **master code 技巧**把 $J_\alpha$ 上的 $\Sigma_n$ 归约为 $(J_{\rho_n},A_n)$ 上的 $\Sigma_1$。

第二点值得单独指出，因为它对形式化有直接影响：它意味着你**不需要一个对 $n$ 一致的 $\Sigma_n$ 满足关系**，只需要 $\Sigma_1$ 满足关系加上对 $n$ 的外层递归。这是 Jensen 设计里最省力的一步。

一个必须提的警告：Devlin《Constructibility》第一章对 rud/$J$ 基本性质的处理有已知缺陷 (Mathias, *Weak systems of Gandy, Jensen and Devlin*，问题出在弱系统中哪些公理实际可用)，第六章 $\Sigma^*$ 部分也有 Stanley 发现的错误。**不要把 Devlin 当作形式化时的逐行蓝本**；Zeman 的 *Inner Models and Large Cardinals* 第 1–2 章、以及 Mathias 的修正版本更可靠。

## 地质学：rud 帮不上忙

Laver–Woodin 可定义性定理的实际内容是：

- Hamkins 的 **$\delta$-approximation / $\delta$-cover** 性质及**唯一性定理** (若 $W,W'$ 都有这两条性质、$\mathcal P(\delta)^W=\mathcal P(\delta)^{W'}$、$(\delta^+)^W=(\delta^+)^{W'}$，则 $W=W'$)；
- 由此得到基底族 $\{W_r\}$ 的一致可定义 (Fuchs–Hamkins–Reitz)，进而幔 $\mathbb M$ 可定义；
- Usuba 的 sDDG 与 hyperhuge $\Rightarrow$ bedrock 存在。

这些论证是**组合的 + 力迫的**，没有一处用到 rud 闭包、凝聚或投影。它们要的基础设施是另一套：力迫关系 $\Vdash$ 的可定义性、名字与赋值、Levy 层级与反射。

值得区分的一点是：真正的语法负担在**力迫本身**，不在地质学。$\Vdash_\varphi$ 是对公式递归定义的，这一步逃不掉内部 `Formula` 类型 (或者布尔值模型路线，但 $\check{}$ 与真值赋值仍要对公式递归)。而唯一性定理与 $W_r$ 的定义本身，只用到「$M\models\mathrm{ZFC}$」这个模式，原则上可以逐条公理地陈述。所以在 Bedrock 里，力迫层一旦建好，地质学部分反而不会额外增加语法开销。

## 形式化上的具体建议

| 目标 | 基础设施 | 是否需要内部语法 |
|---|---|---|
| $L$ 的定义、绝对性、$L\models\mathrm{ZF}$ | 10 个 $G_i$ + $S$-层级 | 否 (逐条公理) |
| $L\models\mathrm{AC}$ | $S$-层级 + 词项枚举 | 否 |
| 凝聚、$L\models\mathrm{GCH}$ | $J$ + $\Sigma_1$ Skolem | 需要 $\Sigma_1$ 片段 |
| 精细结构 | $\mathrm{rud}_A$、可修正、master code | $\Sigma_1$ 片段 + 对 $n$ 递归 |
| 力迫、地质学 | $\Vdash$、approximation/cover | 是，完整 |

在 Cubical Agda 里，rud 的一个实质好处是它天然是**归纳类型**而非模式：签名有限，所以

```
data Term : ℕ → Type
eval : Term n → (Fin n → V) → V
```

是内部对象，$\Delta_0$ 正规形式引理从「元语言归纳模式」变成一条内部定理 `Δ₀Formula → Σ[ t ∈ Term n ] ...`。这比满足关系路线省一大截。

两个可能的坑：一是 $<_L$ 的**线性性**需要 $\in$ 的可判定性，构造性元理论里过不去，得显式 postulate LEM (Bedrock 已假设经典逻辑就无所谓)；二是 $J_\alpha=S_{\omega\alpha}$ 这类等式在 HIT 表示的累积层级上，序数递归的良基性证明会比纸上冗长，值得早点把 $S$ 的递归与序数算术分离成独立模块。
