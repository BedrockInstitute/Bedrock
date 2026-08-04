# Glossary review: the 119 pre-protocol entries

Deliverable of [L3.32-T41], `tier: codex (default)`. Review of every entry in
`dev/glossary.toml` that predates the terminology-dossier protocol, to the
standard of `dev/literature/terms-2026-08.md` ([L3.32-T38]). Written
incrementally, block by block: set theory first, then type theory, then logic
and philosophy plus other. The fourteen terms settled by the 2026-08-05
ruling are not re-litigated; each is marked skipped.

## Method

Per `dev/ORCHESTRATION.md` section 7: for each entry, the Chinese literature
was searched for the established rendering first; only where it is silent is
the entry marked IDIOM, NO LITERATURE, and that is said plainly rather than
manufacturing a source. Each entry carries one of four verdicts:

- **CONFIRMED**: an established rendering, and the entry matches it; the
  source is given.
- **CONFIRMED WITH A BETTER SOURCE**: the rendering is right but the note
  cites nothing or something weak; a source is supplied.
- **CHALLENGED**: the literature says something else, the rendering collides
  with another glossary term, or it reads as a different concept. The
  established rendering, the collision, and the recommended `avoid` change are
  given.
- **IDIOM, NO LITERATURE**: the project's own coinage or a metaphor, with no
  source to find; internally consistent or not is noted.

Two cross-cutting flags are reported separately: (i) `avoid` lists that ban a
word with innocent uses, following the ground ruling of 2026-08-05 (an
over-broad ban fires on prose that never meant the term); (ii) Japanese
renderings that look like kanji transliterations or calques rather than the
term Japanese mathematics actually uses.

## The verdicts at a glance

### CHALLENGED (summary; full entries in the block sections)

| Term | Entry | Established / recommended | Collision |
|---|---|---|---|
| bounding ordinal | 上界序数 | 上界序数 | 界层 = boundary layer; zero hits |
| end extension | 尾节扩张 | 尾节扩张 | 尾节扩张 unattested；郝兆宽 school uses 尾节扩张 |
| adequacy | 充分性 | 充分性 | 充分性 zero hits；充分性 = PLFA-zh and dictionaries |
| Gödel numbering | 哥德尔数 | 哥德尔配数 | number vs numbering conflation |
| renaming | 改名 | 改名 / 换名 | reads as variable transformation; ja 変数変換 = change of variables |
| relabelling | 常量改名 | 常量改名 (no literature; consistency with renaming) | 定数変換 calque；変換 = transformation |
| proof assistant | 证明助手 | 证明助手 | 助理 reads as office assistant |

### Over-broad avoid lists (flagged)

| Entry | Banned word | Why over-broad |
|---|---|---|
| ground / ground model | zh：基础模型 | extremely common phrase (foundation model; basic model) |
| rudimentary function | zh：初等函数 | the established rendering of "elementary function" |
| sentence | zh：语句 | common word for statement/sentence |
| parameter-free | zh：无参数 | common "without parameters" in prose |
| relabelling | zh：改换 | ordinary verb "to change/replace" |
| machine-checked development | zh：机械验证 | real term "mechanical verification" |
| renaming | zh：重命名 | common computing word for rename |

### Japanese calque / transliteration flags (flagged)

| Entry | ja rendering | Note |
|---|---|---|
| renaming | 変数変換 | 変数変換 is "change of variables" in Japanese math |
| relabelling | 定数変換 | same pattern; no Japanese source |
| canonical | 典範 | Japanese math uses 正準 / 標準的；正準 already used by canonical well-ordering |
| condensation | 凝縮 | no Japanese source found for 凝縮補題；guess |
| rudimentary function | 初歩的関数 | no Japanese source found; guess |

## Block 1: Set theory (58 entries; 6 settled, 52 reviewed)

### Settled (skipped)

initial segment, order type, canonical well-ordering, square law,
equinumerous, initial ordinal. Ruled 2026-08-05 from
`dev/literature/terms-2026-08.md`; not re-litigated.

### Reviewed

#### producer

zh 生产者 / ja 生成者，avoid zh：生成者. The book's own name for SZ p. 11's
nameless minimal triple (i, u, v), per the entry's note and
`src/L/Rud/Order.lagda.md:11`. No mathematical literature names this notion
because no literature has it. **IDIOM, NO LITERATURE.** Internally consistent:
the avoid ban on zh 生成者 matches the ja rendering (generator), and the
zh/ja split 生产者/生成者 is deliberate. ja is tentative in the note; no
Japanese source exists either, so it stays a guess.

#### stage-bounded

zh 循阶的 / ja 段階有界，avoid zh：扎根的，grounded. The producer-tree
argument bound (`src/L/Rud/Order.lagda.md:268`). No literature. **IDIOM, NO
LITERATURE.** The avoid ban on "grounded" is not over-broad here: the English
word in CJK prose would only ever be this term (the ban's scope is the CJK
docs), and the note explains the renaming from grounded precisely because the
logic tradition uses "grounded" for well-founded. 循阶的 is a reasonable
coinage (循 the tower's stages). ja tentative.

#### coherence

zh 相容 / ja 整合，avoid zh：融贯. The sense is "restriction-compatibility of
the level orders", so the zh 相容 (= compatible) is semantically exact, not a
translation of the philosophical "coherence". Chinese math renders
compatibility as 相容性 (e.g. forcing-compatibility of conditions is 相容；相容条件 is standard in Chinese forcing literature, e.g. 百度百科力迫条件：「利用力迫条件间的相容性关系确定模型性质」). **CONFIRMED WITH A BETTER SOURCE:**
the note cites only the owner ruling; the source is the standard Chinese
forcing vocabulary, where two conditions are 相容 (compatible) and a coherent
family is 相容的. The ban on 融贯 is well-aimed：融贯 is the Chinese rendering
of coherentism in philosophy, a different concept. ja 整合 is the ordinary
Japanese word for coherence/integration and fine, though 整合性 is the more
technical form; not a challenge, but the note's "ja tentative" can be dropped
once 整合性 is chosen or kept as 整合.

#### key

zh 键 / ja 鍵. "The least-producer key the order pulls back along"
(`src/L/Rud/Order.lagda.md:22`). No literature; book-specific device. **IDIOM,
NO LITERATURE.** Internally consistent with the producer/stage-bounded family.
Note that zh 键 is a standard computing word (key of a map/dictionary), which
is why it reads naturally here, but no Chinese math text uses "key" this way.

#### rudimentary function

zh 初步函数 / ja 初歩的関数，avoid zh：初等函数，zh：初始函数，zh:rud 函数，presence. Rudimentary functions are Jensen's class from fine structure theory
(the smallest class containing the pairing/union projections closed under
composition and bounded separation). **CONFIRMED WITH A BETTER SOURCE (zh);
ja flagged tentative; over-broad avoid flag.** The pattern source in the note
is real: the 数学辞典 entry renders "rudimentary set" as 初步集 (合)，so 初步函数
follows the same dictionary pattern. Chinese fine-structure material is thin;
the only other Chinese rendering found is 基本，in the banana-space
Kripke-Platek lecture notes (「基本 (Rudimentary)」)，a different register, so
初步函数 remains the best-documented choice. **But the avoid list bans zh
初等函数，the established Chinese rendering of「elementary function」(初等函数，calculus texts and dictionaries): an over-broad ban that fires on any innocent
mention of elementary functions.** Recommend dropping zh 初等函数 from the
avoid list (leave to review, per the ground ruling) and keeping 初始函数 and
rud 函数. **Japanese flag：** 初歩的関数 is the natural Japanese compound but I
found no Japanese source fixing it; the note's "tentative" should stay until a
Japanese fine-structure source is checked.

#### forcing / forcing extension

zh 力迫 / ja 強制；力迫扩张 / 強制拡大. Established: Chinese set theory
renders forcing as 力迫 (力迫法，科普中国s 力迫法 entry；百度百科力迫方法；PKU logic course "introduction to forcing"), and Japanese renders it 強制
(強制法，e.g. Fuchinos 強制法 lecture slides and the Kobe forcing-modal-logic
notes). Forcing extension：科普中国s 力迫法 entry uses 力迫扩张 explicitly
(「力迫扩张 (forcing …)」) and 郝兆宽 et al. 集合论导引第二卷 writes 科恩的力迫扩张模型；強制拡大 is confirmed by the Kobe forcing notes. **CONFIRMED.** The
deliberate zh/ja split is exactly right.

#### ground / ground model / ground-model definability

zh 基模型 / ja 基礎モデル，avoid zh：基底模型，zh：基础模型. Established:
Chinese set-theoretic literature renders the ground model as 基模型 (e.g. the
百度百科兼纳扩充：「M称为兼纳扩充的基模型」；杨睿之s multiverse text: "沿着力迫扩张的逆关系
(即基模型关系) 向下挖掘"；孙修远s thesis on 基模型的可定义性)，and Japanese uses
基礎モデル (standard; also グラウンドモデル in transliteration). **CONFIRMED,
with a strengthened source.** **Over-broad avoid flag:** banning zh 基础模型
machine-wide is exactly the 2026-08-05 mistake the ground ruling warns about:
基础模型 is an extremely common phrase meaning "foundation model" / "basic
model" / "underlying model" (and, since 2023, the AI "foundation model"), and
the docs may use it innocently in other senses. The entrys own note
acknowledges the lesson for 地基 but keeps 基础模型 on the ban. Recommend
dropping zh 基础模型 from the avoid list and leaving it to review, keeping
基底模型 (基底 = base, the tempting wrong form for ground). 基模型的可定义性 /
基礎モデルの定義可能性 composes the above; the ground-model definability
theorem (Laver–Woodin) has no separate Chinese literature beyond the same
vocabulary. **CONFIRMED.**

#### multiverse / universism / multiversism

zh 多宇宙 / ja 多宇宙；单宇宙观 / 単一宇宙観；多宇宙观 / 多宇宙観. **All three
CONFIRMED.** The Chinese philosophy-of-mathematics literature on Hamkins uses
exactly this vocabulary：集合论单宇宙观 (set-theoretic universism) and 集合论多宇宙观 (multiversism), e.g. 湖南科技大学学报 (社会科学版) 2025 no. 2，「一种新的集合论哲学立场：实在论多宇宙观」(「提出了一种与集合论单宇宙观对立的哲学立场，称为实在论多宇宙观)，and 自然辩证法研究 2022 no. 12，」哈姆金斯的集合论多宇宙观及其辩护策略」；杨睿之s text at logic.fudan.edu.cn/doc/_yrz/multi.pdf is
headed 集合论多宇宙观简介. The zh pair matches this literature. Japanese 多宇宙
is the standard Japanese word for multiverse (多宇宙論 is the ordinary physics
term; Hamkinss Japanese philosophy-of-science readers use the same word);
単一宇宙観 / 多宇宙観 are natural Japanese compounds, no source found, kept
tentative by analogy with the zh side.

#### ultrapower

zh 超幂 / ja 超冪. Established: Chinese set theory uses 超幂 (超幂*R模型，Chinese Wikipedia and 百度百科；超幂非标准模型，陕西师范大学学报 2010; Bohrium
超幂 keyword), Japanese uses 超冪 (反復超冪 = iterated ultrapower, Kobe
logic-workshop slides). **CONFIRMED.**

#### set-theoretic geology

zh 集合论地质学 / ja 集合論の地質学，presence. The name is a translation of
Hamkins's set-theoretic geology；集合论地质学 is attested in Chinese
set-theory writing (孙修远s thesis works explicitly in 集合论地质学，and the
Chinese multiverse/geology literature around Hamkins uses the same name).
**CONFIRMED.** Japanese 集合論の地質学 is the literal Japanese translation;
fine.

#### mantle

zh 地幔 / ja マントル. The mantle is the intersection of all grounds; the
Chinese rendering follows the geology metaphor (地幔 = the Earths mantle,
standard Chinese geology word). **CONFIRMED WITH A BETTER SOURCE：** 孙修远，「非常大的基数和宇宙的基模型数量」works in 集合论地质学，proves its two basic
theorems 基模型的可定义性 and SDDG, and speaks of δ-地幔，confirming 地幔 as
the Chinese set-theoretic-geology term. (The note cites nothing.)
Japanese マントル is the Japanese geology word, not an ad-hoc transliteration;
fine.

#### generic absoluteness

zh 脱殊绝对性 / ja ジェネリック絶対性. Established：脱殊 is the standard
Chinese rendering of "generic" in forcing (科普中国脱殊集 entry; zhihu forcing
notes 脱殊力迫；百度百科兼纳集「又称脱殊集」)，and 绝对性 is the glossary's own
absoluteness. **CONFIRMED.** ja ジェネリック絶対性 is the standard Japanese
transliteration (ジェネリック = generic); fine.

#### independence results

zh 独立性结果 / ja 独立性の結果. Ordinary established phrase (独立性 =
independence of CH etc.；结果 = result). **CONFIRMED** (no single source
needed; it composes standard words).

#### axiom of infinity

zh 无穷公理 / ja 無限公理. Established in both languages (Chinese：无穷公理 in
the standard ZF axiom list of 科普中国/百度百科集合论公理系统；Japanese:
無限公理 in the standard axiom lists, alongside 対の公理 and 和集合の公理).
**CONFIRMED.** The note "also infinity axiom" is fine.

#### regularity

zh 正则公理 / ja 正則性公理. Established: the axiom of regularity is 正则公理
in Chinese (also 基础公理 in older texts；正则公理 is the standard modern
form), and 正則性公理 in Japanese. **CONFIRMED.** Note「zh also 正则性」is a
useful flag; the book uses the 公理 form.

#### standard model

zh 标准模型 / ja 標準モデル. Established ordinary phrase (标准模型 of ZF; the
term is standard in model theory Chinese; note it collides with the
particle-physics 标准模型，irrelevant here). **CONFIRMED.**

#### infinite descent

zh 无穷下降 / ja 無限降下. Established：无穷下降 (链) = infinite descending
(chain), standard in Chinese set theory (无穷下降链，e.g. regularity
discussions); Japanese 無限降下 standard (無限降下列). **CONFIRMED.**

#### constructible hierarchy / constructible universe

zh 可构造层级 / 可构造宇宙，ja 構成可能階層 / 構成可能宇宙，presence.
**CONFIRMED WITH A BETTER SOURCE, with a collision note.** 可构造 is the
modern mainstream Chinese rendering: the Chinese Wikipedia 集合论 template
lists 可构造全集 for Constructible universe and the 钻石原则 article says
哥德尔可构造全集 (L)；Bohrium's keyword page is titled 可构造宇宙；百度百科 has
可构造集全域 (universe of constructible sets)；科普中国 uses 可构造模型 /
可构造性公理；郝兆宽 et al. 集合论导引第二卷 describes the canonical inner
model as 哥德尔可构造集论域. The alternative 可构成 (可构成集合，可构成性) also
circulates (e.g. Bohrium's 凝聚引理 page writes 哥德尔可构成宇宙)，so the
entry is right but the note should be strengthened with these sources and
should record the 可构成 variant. **Collision to document：** 可构造性 is also
the Chinese word for constructivity, so a reader meeting 可构造宇宙 could
briefly read "constructive universe"; the note should say the rendering
follows the Chinese set-theory convention, not the constructive one. Japanese
構成可能 is established (構成可能集合 = constructible set, e.g. Glosbe's
Japanese rendering of univers constructible de Gödel)；構成可能宇宙 /
構成可能階層 are the standard Japanese compounds. No change recommended; the
collision is worth a note, not a change.

#### cumulative hierarchy

zh 累积层级 / ja 累積階層，presence. Established：累积层级 (cumulative
hierarchy, the V hierarchy) is the standard Chinese rendering (Bohrium keyword
pages：「这种被称为累积层级的构造」in the 遗传有限集 entry and「累积层级 (V)」in
the 超限递归 entry); Japanese 累積階層 is the standard compound (累積的階層).
**CONFIRMED.** Note the entry says the zh rendering is already in use in
Everything.lagda.md, consistent with the hierarchy entries.

#### condensation

zh 凝聚 / ja 凝縮，presence. Established: the condensation lemma is 凝聚引理 in
Chinese (Bohrium 凝聚引理 keyword page：「凝聚引理是集合论中的一个基本原理，它断定哥德尔可构成宇宙 (L) 的任何初等子结构都会坍缩为 L 自身的一个较小的初始段」；also in
the Chinese textbook 公理化集合论). **CONFIRMED (zh).** Japanese flag: I could
not find 凝縮補題 in the searched Japanese literature；凝縮 is the natural
Japanese word for condensation but the note's ja should stay tentative until a
Japanese set-theory source (e.g. 松原洋集合論の発展) is checked. The deliberate
zh/ja split is otherwise right.

#### absoluteness

zh 绝对性 / ja 絶対性. Established：绝对性 is the standard Chinese rendering
(Shoenfield absoluteness = 肖恩菲尔德绝对性定理；绝对性 for absoluteness is
standard), Japanese 絶対性 standard. **CONFIRMED**; consistent with generic
absoluteness.

#### relative consistency

zh 相对一致性 / ja 相対無矛盾性，presence. Established：相对一致性 (relative
consistency) is the standard Chinese phrase (相对一致性证明)；Japanese
相対無矛盾性 standard (無矛盾性 = consistency). **CONFIRMED.** The deliberate
zh 一致性 vs ja 無矛盾性 split matches the consistency entry.

#### well-order

zh 良序 / ja 整列順序. Established：良序 (良序集 = well-ordered set) is the
standard Chinese rendering; Japanese 整列順序 standard (整列集合). **CONFIRMED.**
The noun/participle note is helpful.

#### axiom of choice

zh 选择公理 / ja 選択公理，presence. Established in both languages. **CONFIRMED.**

#### inner model

zh 内模型 / ja 内部モデル，presence. Established：内模型 (inner model, e.g. 内模型理论 = inner model theory) standard Chinese; Japanese 内部モデル standard
(内部モデル理論). **CONFIRMED.**

#### transitive class / transitive set

zh 传递类 / 传递集，ja 推移的クラス / 推移的集合. Established：传递集 (transitive
set) and 传递类 standard Chinese (传递 = transitive in set theory); Japanese
推移的集合 standard (推移的). **CONFIRMED.** The pair is internally consistent.

#### axiom of extensionality

zh 外延公理 / ja 外延性公理. Established：外延公理 standard Chinese (also
外延性公理；both circulate，外延公理 the common short form); Japanese
外延性公理 standard. **CONFIRMED.** The note's property-only form 外延性 matches.

#### axiom of separation

zh 分离公理 / ja 分出公理. Established：分离公理 standard Chinese (分离公理模式，also 分出公理 in some texts; both attested); Japanese 分出公理 standard.
**CONFIRMED.** Note the zh/ja split is deliberate and correct.

#### axiom of replacement

zh 替换公理 / ja 置換公理. Established：替换公理 standard Chinese (替换公理模式)；Japanese 置換公理 standard. **CONFIRMED.**

#### axiom of pairing

zh 配对公理 / ja 対の公理. Established：配对公理 standard Chinese; Japanese
対の公理 standard (also ペアの公理). **CONFIRMED.**

#### axiom of union

zh 并公理 / ja 和集合の公理. Established：并公理 / 并集公理 both standard
Chinese; Japanese 和集合の公理 standard. **CONFIRMED.**

#### power set

zh 幂集 / ja 冪集合. Established in both languages (幂集公理 / 冪集合公理).
**CONFIRMED.**

#### empty set

zh 空集 / ja 空集合. Established. **CONFIRMED.**

#### successor

zh 后继 / ja 後者. Established：后继 (后继序数 = successor ordinal) standard
Chinese; Japanese 後者 (後者順序数) standard. **CONFIRMED.**

#### numeral

zh 数码 / ja 数項. The sense is the von Neumann numerals inside a model.
**CONFIRMED WITH A BETTER SOURCE, both languages.** Chinese renders the formal
digits/numerals as 数码 (the school-mathematics convention 数字是写数用的符号，也叫数码；and 数码 is the established word for the numeral terms of a formal
language in Chinese logic/computability texts). 数字 also circulates; the
entry's choice is one of the two attested forms. **Flag：** 数码 is the everyday
Chinese word for「digital」(数码相机 = digital camera), so the note should
record that the term means the formal numerals, not "digital"; no avoid list
exists, so the risk is confined to review. **Japanese：数項 is confirmed, not a
calque** ,  Kobe University logic-workshop notes (Kurahashi, SS2024) write「n から n の数項のゲーデル数」，and the same notes (LWS2) write「理論 R₀ や R は各数項に関する無限個の公理を持っていた」，i.e. 数項 is the Japanese logic word for the
numeral terms of the object language. The entry's ja is right; the note's
absence of a source can be filled.

#### choice set

zh 选择集 / ja 選択集合. Established: the choice set formulation of AC (one
point per member of a disjoint family) is 选择集 in Chinese (选择集 for the
choice set; AC 的等价形式 including 选择集 standard); Japanese 選択集合 standard.
**CONFIRMED.**

#### class

zh 类 / ja クラス. Established：类 (proper class = 真类) standard Chinese;
Japanese クラス standard. **CONFIRMED.**

#### well-founded

zh 良基 / ja 整礎. Established：良基 (良基关系 = well-founded relation，良基性
= well-foundedness) standard Chinese; Japanese 整礎 (整礎関係) standard.
**CONFIRMED.**

#### ordinal

zh 序数 / ja 順序数. Established in both languages. **CONFIRMED.**

#### definable subset

zh 可定义子集 / ja 定義可能部分集合. Established ordinary phrase (可定义子集 =
definable subset, standard). **CONFIRMED.**

#### bounding ordinal

zh 上界序数 / ja 上界順序数. The concept: a single ordinal containing every
member of a small family (`boundingOrd`, `src/L/Ordinal.lagda.md:154-156`),
used to bound the stages of a family. **CHALLENGED (zh).** 界层 is not a
Chinese mathematical word: it reads as "boundary layer" (the fluid-dynamics
word is 边界层，界层 a rare variant) and does not compose to "bounding
ordinal". The natural rendering is 上界序数，attested in the Chinese literature
for the ordinal bound of a family of ordinals (banana-space 经典数学基础 lecture
notes，序数 chapter：「定理 5.1.3 (上界序数). 一集序数的并还是个序数. 我们称这序数为这集序数的上确界」). **Recommended change:** zh 上界序数 → 上界序数，with avoid
zh：上界序数 if the owner accepts (coined, zero hits). 上界 already appears in
the Japanese rendering, so zh/ja align. ja 上界順序数 is a plausible Japanese
compound; no Japanese source found, kept tentative.

#### birth stage

zh 诞生阶段 / ja 誕生段階. The ordinal a constructible set is carved over
(L.Choice.Step). No literature; the book's own metaphor. **IDIOM, NO
LITERATURE.** Internally consistent: zh 阶段/ja 段階 match the prose's rendering
of "stage", against 階層 reserved for hierarchy (the note says this; it
matches the constructible/cumulative hierarchy entries, which use 层级/階層).
Fine as a guess; the note's owner delegation is recorded.

#### end extension

zh 尾节扩张 / ja 端拡大. End extension is a standard model-theoretic term
(extending a model without adding new elements below existing ones); here, the
order at a larger L-stage restricted to a smaller one.
**CHALLENGED (zh) / CONFIRMED (ja).** The established Chinese rendering in the
literature this project's own textbooks belong to is 尾节扩张：郝兆宽、杨睿之、杨跃《递归论：算法与随机性基础》(复旦大学出版社) describes「递归论中经典的构造技巧，，尾节扩张 (算术力迫)，and a PKU logic colloquium report says」非标准模型都是标准模型的尾节扩张」；a 2024 lecture report on arithmetic model theory also uses
尾节扩张(end extension）alongside 共尾扩张 and 极小扩张. 尾节扩张 returns no
model-theoretic attestation in the searched literature. **Recommended change:**
zh 尾节扩张 → 尾节扩张，with avoid zh：尾节扩张 (the current rendering, unattested),
unless the owner prefers a transparent coinage and accepts the note's claim
being corrected to "no zh attestation found". Japanese 端拡大 is confirmed:
Tsukuba University lecture notes (Tsuboi, logic09.pdf) define「N が M の端拡大 (end extension) であるとは…」. Keep ja 端拡大.

#### layer

zh 层 / ja 層. "A stage of the L tower" (`isLayer`, the tower's closure
predicate). No literature uses "layer" this way for L; the L hierarchy is
階層/层级 in the literature, and 层/層 here is the book's own name for the
stage-predicate. **IDIOM, NO LITERATURE.** Internally consistent with the
hierarchy entries (层级/階層 are the hierarchy nouns；层/層 the predicate),
though a reader could confuse 层 with a hierarchy level; the note documents
the sense, which is the best available guard.

#### set-level choice

zh 集合层选择 / ja 集合レベルの選択. SetChoice: truncation commutes with
products over an h-set of indices. No Chinese or Japanese literature for this
type-theoretic formulation; the compound 集合层选择 is a coinage on the
glossary's own 层/层级 pattern. **IDIOM, NO LITERATURE.** Internally
consistent (层 = level, matching the book's use of 层 for levels).

### Sources for the standard Block 1 confirmations

The following sources were verified by search for the entries above that
report CONFIRMED without an inline citation (the ZF axiom list, the standard
terms, and the Japanese side):

- Chinese ZF axiom list：科普中国 / 百度百科集合论公理系统：「非逻辑公理有：外延公理、空集公理、无序对公理、并集公理、幂集公理、无穷公理、分离公理模式、替换公理模式、正则公理，再加上选择公理」. This confirms 外延公理，无穷公理，并集公理，幂集公理，分离公理，替换公理，正则公理，选择公理；the glossary's
  配对公理 (against 无序对公理) and 并公理 (against 并集公理) are the shorter
  common variants, both attested in Chinese textbooks; the notes should record
  the longer forms.
- Japanese ZF axioms: Keio (Mukai) and Tohoku (Obata) lecture notes give 対の公理；Tsukuba (Tsuboi) notes give 対の公理 and the 内包性公理 family; Fuchino,
  introduction to set theory and constructibility gives 分出公理 and 置換公理
  explicitly (「置換公理は、分出公理の拡張になっており」)；the same notes give
  推移的な集合 and 整列順序 (整列順序集合). 外延性公理 and 正則性公理 are the
  standard Japanese names (wikibook 數學證明與數學原理，基礎公理 sometimes used
  for 正則性公理). 無限公理 / 冪集合の公理 / 空集合 / 順序数 / 後者 are the
  standard Japanese terms in the same literature (数学基礎論増補版 defines
  順序数 as a 推移的 set fully ordered by ∈).
- 良序 / 良基：科普中国 and 百度百科良序关系，良序定理，良基关系，and 降链
  entries (「一个偏序关系称为是良基的…如果这个序还是全序，那么此时称这个序为良序」).
- 内模型：科普中国内模型法 (method of inner model) and 郝兆宽 et al.
  集合论导引第二卷 (「具有典范作用的内模型，，哥德尔可构造集论域」).
- 累积层级：Bohrium keyword pages (累积层次，累积层级 in the 遗传有限集 and
  超限递归 entries).
- 凝聚引理：Bohrium 凝聚引理 keyword page and the Chinese textbook
  公理化集合论.
- 超幂 / 超冪，力迫 / 強制，基模型，地幔，多宇宙 family: cited inline above.

### Block 1 verdict counts

52 entries reviewed. CHALLENGED: 2 (bounding ordinal, end extension).
CONFIRMED or CONFIRMED WITH A BETTER SOURCE: 44. IDIOM, NO LITERATURE: 6
(producer, stage-bounded, key, birth stage, layer, set-level choice). Plus two
over-broad avoid-list flags (ground 基础模型，rudimentary function 初等函数)
carried as flags on confirmed entries.

## Block 2: Logic (7 entries, all settled) and Type theory (25; 1 settled, 24
reviewed)

The seven Logic entries (face, crossing, decode, count, shape count, square
pairing, pair atom) were all settled by the 2026-08-05 ruling from
`dev/literature/terms-2026-08.md`; none re-litigated. Presentation (Type
theory) is also settled; skipped.

### Reviewed

#### host language

zh 宿主语言 / ja ホスト言語. Established: host language = 宿主语言 in Chinese
computing terminology (百度百科宿主语言：「开发这些宿主环境的程序语言…被称作宿主语言 (Host Language)」；有道)，and ホスト言語 is the standard Japanese (TechDico
host-language entry；ホストプログラム in the same family). **CONFIRMED.**

#### host-language maximalism

zh 宿主语言最大化 / ja ホスト言語最大主義. The book's own thesis name
(host-language maximalism). No literature. **IDIOM, NO LITERATURE.** Internally
consistent: composes the confirmed host language with 最大化 / 最大主義；the
zh/ja split is deliberate and recorded.

#### unique existence

zh 唯一存在 / ja 一意存在. Established in both languages：唯一存在 is the
standard Chinese reading of ∃！(唯一存在的 x); Japanese 一意存在 matches the
standard 一意に存在する (uniquely exists). **CONFIRMED.**

#### definite-description operator

zh 摹状词算子 / ja 確定記述の演算子. Established: Russell's theory of
descriptions is 摹状词理论 in Chinese (限定的摹状词 = definite description,
standard in Chinese analytic-philosophy literature, e.g. 王路s 走进分析哲学；摹状词理论研究 theses), and Japanese uses 確定記述 (definite description) with
確定記述の理論 standard. The ℩ operator renders 摹状词算子 / 確定記述の演算子
composing those. **CONFIRMED.**

#### description axiom

zh 描述公理 / ja 記述公理. The books name for the axiom governing the
definite-description operator. No literature found under this name in either
language. **IDIOM, NO LITERATURE.** Internally consistent with the
definite-description operator entry. Japanese flag：記述公理 is not an
established Japanese axiom name and sits close to 記述集合論 (descriptive set
theory); the note should record that it is the project's compound, not a
standard name.

#### propositional extensionality

zh 命题外延性 / ja 命題外延性. Established in the HoTT/type-theory literature
of both languages (命题外延性 / 命題外延性，the axiom that equivalent
propositions are equal). **CONFIRMED.**

#### path equality

zh 路径等式 / ja 道の等式. The parts are established：路径 is the standard
Chinese rendering of path in HoTT materials (同伦类型论 accounts: equality is
redefined as 路径)，and 道 is the standard Japanese topology word for path
(Kumamoto topology notes：「X の 2 点 x, y に対し…全ての道からなる集合を Ω (x,y)」，closed paths 閉じた道 in Hokkaido notes). The compound "path equality" (equality
as paths) has no settled rendering in either language's literature.
**IDIOM, NO LITERATURE** for the compound, with the components confirmed. Note
the zh/ja split (路径 vs 道) is deliberate and each side is the established
word in its language. Minor flag：等式 reads「equation」；相等性 would read
"equality" more precisely if the book's sense is equality-as-path, but the
book's own usage decides, and no change is recommended without the prose
context.

#### transport

zh 传输 / ja 輸送. Transport is the standard HoTT operation; the Chinese and
Japanese HoTT communities have not fixed one rendering (Chinese materials keep
"transport" in English, e.g. the banana-space type-theory discussion of
transport vs subst; Japanese materials likewise). 传输 is the ordinary Chinese
word for transport and 輸送 the ordinary Japanese one; both are natural
translations, but neither is a sourced rendering. **IDIOM, NO LITERATURE** (the
English term is established; the renderings are the book's choice). Internally
consistent with the structure-transport (SIP) sense in the note. Keep the
notes' deliberate split; the entry should be marked as a guess until a Chinese
or Japanese HoTT source fixes it.

#### inductive type / inductive predicate

zh 归纳类型 / 归纳谓词，ja 帰納型 / 帰納的述語. Established：归纳类型 is the
standard Chinese rendering of inductive type, and 帰納型 is standard Japanese
(Kaken project summary：「帰納型とは、リスト、木などの再帰データに対する型の一般化であり、最小不動点により定義される」；Japanese MLTT lectures). Inductive
predicate composes the same words. **CONFIRMED.**

#### structural recursion

zh 结构递归 / ja 構造的再帰. Established ordinary CS/logic vocabulary in both
languages. **CONFIRMED.**

#### deep embedding

zh 深嵌入 / ja 深い埋め込み. Established: deep/shallow embedding is 深嵌入/浅嵌入 in Chinese PL literature (MXNet's Chinese docs contrast 深嵌入 with
command-style embedding; Rosette discussions use 深层嵌入/浅层嵌入)，and
深い埋め込み / 浅い埋め込み is the standard Japanese pair. **CONFIRMED.**

#### reflection / reification

zh 反射，ja 反射；reification kept in English in all languages. Reflection is
established in both languages (reflection = 反射 in Chinese and Japanese
logic/CS). Reification: the book deliberately keeps the English word (note:
"do not translate"); Chinese CS would normally say 具体化 and Japanese
具体化/実体化，so the entry is a ruling, not a literature question.
**CONFIRMED (reflection); reification IDIOM, NO LITERATURE by explicit ruling**
,  internally consistent, and the note already records the decision.

#### adequacy

zh 充分性 / ja 妥当性，presence. **CHALLENGED (zh) / CONFIRMED (ja) with a
collision note.** The Chinese type-theory/PL literature renders "adequacy" as
充分性：the Chinese translation of Programming Language Foundations in Agda
(PLFA-zh, agda-zh.github.io) titles the chapter「Adequacy：指称语义相对于操作语义的充分性」，and Chinese dictionaries give adequacy = 充分性 (三度漢語網；linguistics 充分性 for adequacy in generative grammar). 充分性 returns zero
attestation in Chinese mathematics or logic; its only familiar Chinese use is
the finance term 资本充分性 (capital adequacy). **Recommended change:** zh
充分性 → 充分性，with avoid zh：充分性 if the owner accepts. The collision to
record：充分性 also renders「sufficiency」(充分条件)，so the note should say
the term means adequacy here and the sufficiency homonym is a review matter,
not a linter one. Japanese 妥当性 is the standard rendering of adequacy
(explanatory adequacy = 解释的妥当性 in EN–JA dictionaries), with the caveat
that Japanese logic also uses 妥当性 for validity (妥当な推論)；the note should
record the homonym.

#### representation

zh 表示 / ja 表現. Established in both languages (表示论 = representation
theory；表現論 standard Japanese). **CONFIRMED.** The pairing with reification
and adequacy in the note is the book's own structure and consistent.

#### Tarski universe

zh 塔斯基宇宙 / ja タルスキ宇宙. Established: Tarski = 塔斯基 is the standard
Chinese transliteration and タルスキ the standard Japanese one; universe
(of types) = 宇宙 in both. **CONFIRMED.**

#### truth value / truth algebra

zh 真值 / 真值代数，ja 真理値 / 真理値代数. 真值 is the standard Chinese
rendering of truth value and 真理値 the standard Japanese one. The truth
algebra is the book's own record (TruthAlgebra, Base.Truth); it composes the
confirmed 真值/真理値. **CONFIRMED (truth value); truth algebra IDIOM, NO
LITERATURE** (project vocabulary, internally consistent).

#### propositional resizing

zh 命题降层 / ja 命題リサイズ. The note marks this tentative (owner review).
No established Chinese rendering found for propositional resizing (Chinese
HoTT materials leave it in English；命题分阶 in Russell's ramified type theory
is a different concept, order not universe level). **IDIOM, NO LITERATURE** , 
and the note already says so. Internally consistent：降层 composes the
glossary's 层 for levels (matching layer and set-level choice). ja 命題リサイズ
is a transliteration, fine as a guess. The entry should stay tentative until
the owner rules.

#### smallness / small classifier

zh 小性 / 小分类器，ja 小ささ / 小分類子. No literature for either compound.
小性 (the noun smallness) is a coinage on the 性 suffix；小分类器 composes the
established 小 (small type) with 分类器 (classifier, as in 子对象分类器 =
subobject classifier in Chinese category theory). **IDIOM, NO LITERATURE
(smallness); small classifier CONFIRMED BY ANALOGY**，分类器 is established
for classifier，小 for small type; internally consistent with small = 小 in the
note. Japanese flag：小ささ is the natural Japanese noun (smallness) but
Japanese would more idiomatically write 小さいこと；小分類子 is plausible
(部分対象分類子 for subobject classifier) but unverified. Keep both tentative
in the notes.

#### set quotient

zh 集合商 / ja 集合商. The set-quotient HIT (SetQuotients). The generic
quotient set is established as 商集 in Chinese (商集、商群与商环 in algebra
teaching literature; zhihu HoTT discussions) and 商集合 in Japanese (Nagoya
lecture notes：「同値類全体の集合を…商集合とよび，X/∼ で表す」). 集合商 is the
project's compound for the HIT name, distinct from the generic 商集/商集合.
**CONFIRMED BY ANALOGY, with a note:** the entry's own note already records
the related 按关系取商；add 商集/商集合 as the ordinary forms so a reader
recognizes the HIT name as the compound. No change recommended.

#### impredicativity

zh 非直谓性 / ja 非可述性. Established：非直谓性 is the standard Chinese
rendering (Chinese Wikipedia 直觉类型论：「先是非直谓性的而后是直谓性的」；banana-space 非直谓性 page), and 非可述的/非可述性 is the standard Japanese
(非可述的定義，impredicative definition). **CONFIRMED.**

### Block 2 verdict counts

24 type-theory entries reviewed (7 Logic entries all settled, skipped).
CHALLENGED: 1 (adequacy, zh only). CONFIRMED or CONFIRMED BY ANALOGY: 15.
IDIOM, NO LITERATURE: 8 (host-language maximalism, description axiom, path
equality, transport, reification-by-ruling, truth algebra, propositional
resizing, smallness).

## Block 3: Logic and philosophy (37) and Other (6)

### Reviewed: Logic and philosophy

#### abstraction / occurrence / placement

zh 抽象 / 出现 / 安置，ja 抽象 / 出現 / 配置. Abstraction (of parameters) is
the standard logic word 抽象 (抽象运算 = abstraction, lambda-calculus usage);
occurrence 出现 is the standard model-theoretic word (free/bound occurrence =
自由出现/约束出现；the glossary's own note explains the positional sense);
placement 安置 is the book's own map from constant occurrences to variable
slots. **CONFIRMED (abstraction, occurrence); placement IDIOM, NO LITERATURE**
(no source names this map; internally consistent with occurrence). ja 抽象 and
出現 are standard Japanese；配置 for placement is a plausible Japanese word
(configuration/assignment), fine as a guess.

#### Levy hierarchy

zh Lévy 层级 / ja Lévy 階層，avoid zh：列维层级，zh：分级证书，zh:Levy 层级. The
surname kept in Latin matches Chinese practice for untransliterated names
(the note cites Diaconescu as the book's pattern, and the Diaconescu entry
below does the same). The Δ₀/Σₙ/Πₙ hierarchy is standard; Chinese logic
material on the Lévy hierarchy uses the Latin surname. **CONFIRMED.** The avoid
list is well-aimed：列维层级 is the transliteration drift form, and 分级证书
intrudes on the reserved 证书 (adequacy certificate); neither has innocent
uses here. ja Lévy 階層 fine.

#### relativization

zh 相对化 / ja 相対化. Established: relativization is 相对化 in Chinese logic
(相对化枚举定理，相对算术关系 in 科普中国/百度百科 recursion theory) and 相対化
in Japanese. **CONFIRMED.**

#### satisfaction

zh 满足关系 / ja 充足関係. Established: satisfaction relation is 满足关系 in
Chinese model theory (Chinese Wikipedia 結構 (數理邏輯)：「每個一階邏輯結構都有一個滿足關係」；zhihu accounts of Tarski's 满足关系). Japanese 充足関係 is the
standard rendering of Tarski's satisfaction relation in Japanese model theory,
but this review's searches did not return a direct attestation; mark it
confirmed-by-standard-usage with the note's ja left as it stands, pending a
Japanese model-theory source if the owner wants one. **CONFIRMED (zh);
ja unverified-but-standard.** The deliberate zh/ja split is right.

#### arithmetization

zh 算术化 / ja 算術化. Established: arithmetization (of syntax) is 算术化 in
Chinese (百度百科算术化：「算术化 (arithmetization) 又称哥德尔编码」；科普中国；赵希顺简明数理逻辑：「元数学的算术化」) and 算術化 in Japanese. **CONFIRMED.**

#### Gödel numbering

zh 哥德尔数 / ja ゲーデル数化. **CHALLENGED (zh).** The established Chinese
rendering of "Gödel numbering" (the scheme) is 哥德尔配数 / 哥德尔配数法：科普中国 has a dedicated 哥德尔配数 entry; Bohrium's keyword page is titled
哥德尔配数法；知网 (xuewen.cnki.net) glosses 哥德尔数 as 亦称哥德尔配数、哥德尔码数. 哥德尔数 is the number assigned (the noun), and the entry's
English is "Gödel numbering" (the scheme). **Recommended change:** zh 哥德尔数
→ 哥德尔配数 for the numbering entry, with a note that 哥德尔数 is the single
assigned number (and a candidate avoid zh：哥德尔数 only if the book never
means the noun; the glossary may prefer two entries). ja ゲーデル数化 is the
standard Japanese (ゲーデル数化，numbering; the number itself is ゲーデル数)，confirmed by the Japanese incompleteness literature. No change on ja.

#### first-order definability

zh 一阶可定义性 / ja 一階定義可能性. Established ordinary compound (一阶可定义
= first-order definable, standard). **CONFIRMED.**

#### bi-implication

zh 双向蕴含 / ja 双条件. Established：双向蕴含 is attested in Chinese logic for
the biconditional (百度百科充分必要条件假言判断：「其本质特征体现为双向蕴含」；discrete-math materials：「双条件语句 p↔q … 也称双向蕴含」)，and 双条件 is the
standard Japanese (biconditional). **CONFIRMED.** The note's warning against
the calque 双方向含意 is right: Japanese logic says 双条件，not 双方向含意.

#### proof-theoretic reduction

zh 证明论归约 / ja 証明論的還元. Established: proof-theoretic reduction is
证明论归约 in Chinese (归约 = reduction, standard in logic/CS) and
証明論的還元 in Japanese (還元 = reduction in proof theory). **CONFIRMED.**

#### classical principles

zh 经典原理 / ja 古典原理. The book's shorthand for LEM and AC. No literature
names LEM+AC「经典原理」as a fixed compound. **IDIOM, NO LITERATURE** (project
vocabulary; internally consistent, and the note lists the members LEM, AC so a
reader cannot misread it). ja 古典原理 is the ordinary Japanese word
(classical principles), fine.

#### metatheory

zh 元理论 / ja メタ理論. Established：元理论 is the standard Chinese rendering
(Bohrium 元理论 keyword page；赵希顺简明数理逻辑：「元语言与元理论」) and
メタ理論 standard Japanese. The note's 元层 / メタレベル for meta-level is
consistent. **CONFIRMED.**

#### metaphysics / determinate

zh 形而上学 / 确定，ja 形而上学 / 確定. Established in both languages
(metaphysics = 形而上学 / 形而上学；determinate = 确定 / 確定，ordinary).
**CONFIRMED.**

#### canonical

zh 典范 / ja 典範. Established: canonical is 典范 in Chinese mathematics
(典范同构 = canonical isomorphism, Chinese Wikipedia 音乐同构 entry；典范同态
in algebra notes；郝兆宽 et al. 集合论导引 uses 典范作用 for the canonical
inner model). **CONFIRMED (zh). Japanese flag：** 典範 (てんぱん) is not the
Japanese mathematical word for canonical: Japanese math uses 正準 (canonical,
e.g. 正準同型) or 標準的，and the glossary's own settled canonical well-ordering
entry uses ja 正準整列順序. The two entries now disagree on the ja rendering of「canonical」(典範 vs 正準). **Recommended change:** ja 典範 → 正準的 (or
standardize on 正準 to match canonical well-ordering), and record the choice
in both notes.

#### falsifiable

zh 可证伪 / ja 反証可能. Established: falsifiability is 可证伪性 in Chinese
(科普中国可证伪性，Popper's criterion; the entry's 可证伪 is the adjective
form) and 反証可能性 in Japanese (反証可能 the adjective). **CONFIRMED.**

#### rigor

zh 严格性 / ja 厳密さ. Established ordinary word in both languages. **CONFIRMED.**

#### finitism

zh 有穷主义 / ja 有限主義. Established：有穷主义 is attested in Chinese
philosophy of mathematics (严格有穷主义 in a Wuhan University lecture;
数学哲学谱系：逻辑主义、有穷主义和直觉主义；当代科学哲学问题研究：有穷主义数学)，and 有限主义 is the alternative form (欧路词典：finitism = 有限主义)；both
circulate，有穷主义 is the mathematically paired form (有穷 vs 无穷).
**CONFIRMED**, note the 有限主义 variant. ja 有限主義 is standard.

#### neutral ground / groundwork / bedrock

zh 中立的地基 / 奠基 / 基岩，ja 中立的な地盤 / 基盤 / 岩盤. The geology family.
中立的地基 is the book's metaphor for the neutral common ground (the ground
entry explicitly keeps 地基 off its avoid list for exactly this entry);
奠基 is the established Chinese word for foundation-laying (Kant's
Grundlegung = 奠基)，and 基岩 is the standard geology word. **IDIOM, NO
LITERATURE for the phrase neutral ground** (the metaphor is the project's);
**CONFIRMED (groundwork, bedrock)** as ordinary words. Internally consistent:
the family is deliberately separated from the forcing ground (基模型) per the
2026-08-05 ruling, and the three entries read distinctly in both languages.

#### term / formula / sentence

zh 词项 / 公式 / 句子，ja 項 / 論理式 / 文. Term = 词项 is established in
Chinese logic (词项逻辑 = term logic, standard textbook chapter) with 項 the
standard Japanese; formula = 公式 (zh) and 論理式 (ja) are both established;
sentence = 句子 is attested in Chinese logic (闭公式 or 句子/语句 for closed
formulas, e.g. 有道s closed-formula gloss 不含有自由出现的变量符号的公式称为闭公式，也称为句子 (语句，sentence)；百度百科s 合式公式 entry says 不含量词、自由变元的合式公式分别称为开公式和闭公式，后者又称语句). **CONFIRMED, with an 
avoid flag:** the avoid list bans zh 语句，which is both the majority Chinese
logic rendering of sentence (一阶语句，语句集合 in standard texts) and an
ordinary prose word (a sentence/statement of text). Machine-wide, the ban
fires on innocent uses. **Recommended change:** drop zh：语句 from the avoid
list and leave the choice to review, recording in the note that 语句 is the
more common Chinese logic form and 句子 the book's attested choice. ja 文 is
the standard Japanese (文 = sentence in logic), no issue.

#### parameter-free / constant domain

zh 无参 / 常量域，ja 無パラメータ / 定数域. No literature for either compound
under these exact names (parameter-free formulas = 无参数公式 / 无参公式 both
circulate in logic prose; the constant domain K is the book's own parameter).
**IDIOM, NO LITERATURE for constant domain** (internally consistent with the
syntax's K parameter and the environment entry); **CONFIRMED (parameter-free
rendering) with an over-broad avoid flag:** the avoid list bans zh 无参数，the
longer ordinary form of the same compound, which is common prose ("without
parameters"); recommend dropping zh：无参数 from the avoid list and keeping
无参 as canonical by review, not by linter. Japanese flag：定数域 could be
misread as the constant-domain semantics term (constant-domain semantics =
常域意味論 in Japanese modal logic); the note should record that the sense is
the book's set-of-constants parameter, not the modal-logic notion. 無パラメータ
is standard Japanese (無パラメータの式). ja tentative as the notes say.

#### bounded quantifier

zh 有界量词 / ja 有界量化子. Established: bounded quantifier = 有界量词 in
Chinese (有道 math glossary: bounded quantifier 有界量词，bounded existential
quantifier 有界存在量词) and 有界量化子 in Japanese. **CONFIRMED.**

#### environment / structure / carrier

zh 环境 / 结构 / 载体，ja 環境 / 構造 / 台. Environment (an assignment to free
variables) is the standard word 环境 in both languages (also 赋值 = valuation,
the more common logic word; the note should record that 环境 is the book's
term for the assignment and 赋值 is the established alternative). Structure =
结构 / 構造 standard. Carrier = 载体 is established in Chinese algebra (分析与代数原理，HEP, uses 载体 and 子载体 for carrier/subcarrier), with 论域 (domain)
the model-theoretic alternative；台 is the standard Japanese (台集合 = carrier
set). **CONFIRMED.** Note the 赋值 alternative for environment.

#### renaming / relabelling

zh 改名 / 常量改名，ja 変数変換 / 定数変換，avoid zh：重命名 (renaming),
zh：重标记，zh：改换 (relabelling). **CHALLENGED (both entries).** The Chinese
logic literature's established word for renaming (of bound variables, exactly
the FOL.Renaming sense) is 改名 / 换名 / 更名：百度百科自由变量 introduces the
改名规则 for bound variables；谓词变元代入规则 says 先将大小代入式都改名 (参见改名)；discrete-math materials speak of 约束变元更名规则 and 换名；the
α-conversion principle (重命名 bound variables) is 重命名 in Bohrium's
α-变换 entry. 改名 is "variable transformation" (change of variables),
a different concept, and 変数変換 is exactly the Japanese word for
change-of-variables in calculus (変数変換 = u-substitution). **Recommended
change:** zh 改名 → 改名 (with 换名 as the attested variant), ja 変数変換 →
改名 (or 束縛変数の改名 for bound-variable renaming；リネーミング in CS); add
avoid zh：改名 / ja：変数変換 only if the owner accepts, since the current
renderings are the wrong concept, not a variant. For relabelling (renaming
constants), no established Chinese literature exists; for internal
consistency with the renaming change, recommend zh 常量改名 / ja 定数の改名，keeping the pair 改名/定数改名 visibly parallel, with the note updated from
the 2026-07-18 ruling. **Over-broad avoid flags:** zh：重命名 (renaming) is the
ordinary computing word for rename and should be left to review once the
canonical is 改名；zh：改换 (relabelling) is an ordinary verb (to change/
replace) that will fire innocently; drop both bans, keep 重标记 (rare,
harmless).

#### consistency / excluded middle / compactness

zh 一致性 / 排中律 / 紧致性，ja 無矛盾性 / 排中律 / コンパクト性. Established in
both languages：一致性 = consistency (zh)，無矛盾性 (ja)，排中律 = excluded
middle (both)，紧致性定理 / コンパクト性定理 = compactness theorem (both).
**CONFIRMED.** The consistency note's "no presence check, the English word is
too common" is the right call and consistent with the ground ruling's
discipline.

#### Diaconescu's theorem

zh Diaconescu 定理 / ja ディアコネスクの定理. Established: Diaconescu's theorem
(choice implies excluded middle) is standard in both languages; keeping the
surname in Latin in zh matches the book's practice and the Levy hierarchy
entry. **CONFIRMED.**

### Reviewed: Other

#### charter

zh 纲领 / ja 綱領，avoid zh：宪章，ja：憲章. The project's founding document.
纲领 is the established Chinese word for a programme/platform/manifesto; the
avoid ban on 宪章/憲章 targets the standard rendering of "charter" in other
contexts (联合国宪章 = UN Charter), which is the tempting wrong form here.
**IDIOM, NO LITERATURE** (the project's own document name), deliberate and
internally consistent. The ban is low-risk in this corpus (the docs are
unlikely to mention charters innocently), so it stays.

#### prose

zh 文稿 / ja 文章，avoid 散文. The book's term for written body text.
文稿 (manuscript/draft) and 文章 (writing) are ordinary words; the ban on 散文
(the essay genre, and the dictionary rendering of "prose") is deliberate and
well-aimed: in this corpus 散文 would only ever be the wrong genre word.
**IDIOM, NO LITERATURE** (project vocabulary), internally consistent.

#### proof assistant

zh 证明助手 / ja 証明支援系，presence. **CHALLENGED (zh).** The established
Chinese rendering is 证明助手：Chinese Wikipedia's article is titled 證明助手
(Proof assistant), and Chinese materials on Coq/Lean/Isabelle consistently
use 证明助手 (v2ex gloss：「证明助手：一种用于形式化编写、检查与 (半) 自动化构造数学证明的计算机软件系统」). 证明助手 is unattested：助理 in Chinese reads as
office assistant (经理助理). Related but distinct：定理证明器 (theorem prover).
**Recommended change:** zh 证明助手 → 证明助手，with avoid zh：证明助手 if the
owner accepts. Japanese 証明支援系 is the standard Japanese (証明支援系，proof-assistant systems in the Japanese MLTT/formalization literature);
confirmed, no change.

#### machine-checked development

zh 机器验证工作 / ja 機械検証の開発，avoid zh：机器验证开发，zh：机械验证，ja：機械検査の開発. The README tagline's phrase; book-specific compounding
(机器 = machine，验证 = checked，工作 = development) per the note's deliberate
split. **IDIOM, NO LITERATURE** (the phrase is the project's own), internally
consistent with the note's certificate/ground phrasings. **Over-broad avoid
flag:** zh：机械验证 is the natural Chinese term for "mechanical verification"
(机械 = mechanical, the standard word for mechanical procedures, e.g. 机械化证明)，so banning it machine-wide fires on prose about mechanical verification
that never meant this tagline; recommend dropping zh：机械验证 and leaving it to
review. The other bans are fine.

#### von Neumann

zh 冯·诺伊曼 / ja フォン・ノイマン. Established：冯·诺伊曼 is the standard
Chinese transliteration (冯·诺依曼 also circulates; both are used，冯·诺伊曼 the
more common in set theory)，フォン・ノイマン standard Japanese. **CONFIRMED.**

#### frontier

zh 前沿 / ja フロンティア. The book's reader-facing name for the L.Frontier
debt registry. 前沿 is the ordinary Chinese word for frontier (also "frontier
research"); no literature names this device. **IDIOM, NO LITERATURE** (project
vocabulary), internally consistent; ja フロンティア is a transliteration, fine
as a guess.

### Block 3 verdict counts

43 entries reviewed (37 logic and philosophy + 6 other). CHALLENGED: 4
(Gödel numbering zh, renaming, relabelling, proof assistant zh). CONFIRMED or
CONFIRMED BY ANALOGY: 30. IDIOM, NO LITERATURE: 9 (placement, classical
principles, neutral ground, bedrock, constant domain, charter, prose,
machine-checked development, frontier). Over-broad avoid flags carried:
sentence (语句)，parameter-free (无参数)，renaming (重命名)，relabelling (改换)，machine-checked development (机械验证)；Japanese flags carried: canonical
(典範 vs 正準)，renaming (変数変換 = change of variables), relabelling
(定数変換)，satisfaction note on 充足関係.

## Totals across all three blocks

119 entries reviewed (all pre-protocol entries; the 14 settled terms skipped).

| Block | Reviewed | CHALLENGED | CONFIRMED / better source / by analogy | IDIOM, NO LITERATURE |
|---|---|---|---|---|
| 1 Set theory | 52 | 2 | 44 | 6 |
| 2 Type theory | 24 | 1 | 15 | 8 |
| 3 Logic and philosophy + Other | 43 | 4 | 30 | 9 |
| **Total** | **119** | **7** | **89** | **23** |

The CHALLENGED list in full (the report's whole value; recommended change for
each):

1. **bounding ordinal**: zh 上界序数 → 上界序数 (avoid zh：上界序数). 界层 is
   not a Chinese math word；上界序数 is attested for the ordinal bound of a
   family (banana-space 经典数学基础序数 chapter).
2. **end extension**: zh 尾节扩张 → 尾节扩张 (avoid zh：尾节扩张). 尾节扩张 is
   the rendering in 郝兆宽 et al. 递归论 and PKU logic colloquia；尾节扩张 has
   no attestation. ja 端拡大 confirmed (Tsuboi).
3. **adequacy**: zh 充分性 → 充分性 (avoid zh：充分性). 充分性 is the rendering
   in PLFA-zh and Chinese dictionaries；充分性 has zero attestation outside
   the finance term 资本充分性. ja 妥当性 confirmed, validity homonym noted.
4. **Gödel numbering**: zh 哥德尔数 → 哥德尔配数. The scheme is 哥德尔配数 /
   哥德尔配数法 (科普中国，Bohrium，知网)；哥德尔数 is the single number.
   ja ゲーデル数化 confirmed.
5. **renaming**: zh 改名 → 改名 (ja 変数変換 → 改名 or 束縛変数の改名).
   Chinese logic uses 改名/换名/更名 for bound-variable renaming；改名 and
   ja 変数変換 both read as change-of-variables. Drop zh：重命名 from avoid.
6. **relabelling**: zh 常量改名 → 常量改名 (ja 定数変換 → 定数の改名)，for
   consistency with renaming; no literature, by analogy. Drop zh：改换 from
   avoid.
7. **proof assistant**: zh 证明助手 → 证明助手 (avoid zh：证明助手). 证明助手 is
   the established rendering (Chinese Wikipedia, Coq/Lean materials);
   助理 reads as office assistant. ja 証明支援系 confirmed.

Over-broad avoid bans to lift (per the 2026-08-05 ground ruling): zh 基础模型
(ground), zh 初等函数 (rudimentary function), zh 语句 (sentence), zh 无参数
(parameter-free), zh 改换 (relabelling), zh 机械验证 (machine-checked
development), zh 重命名 (renaming).

Japanese renderings to re-examine: canonical 典範 (use 正準，matching the
settled canonical well-ordering entry), renaming 変数変換 and relabelling
定数変換 (change-of-variables collision), and the tentative guesses 凝縮
(condensation)，初歩的関数 (rudimentary function)，上界順序数 (bounding
ordinal)，定数域 (constant domain)，小分類子 (small classifier).

## Sources

### Chinese (zh)

1. 科普中国 (kepuchina.cn)：力迫法；脱殊集；哥德尔配数；可证伪性；算术化；内模型法；集合论公理系统；正则公理；良基关系；降链；分支类型论；直觉类型论.
2. 百度百科：力迫方法；兼纳集/兼纳扩充 (generic set/extension，基模型)；正则公理；外延公理；良序关系；良序定理；序数；可构造集全域；超幂*R模型；算术化；宿主语言；充分必要条件假言判断 (双向蕴含)；自由变量 (改名规则)；谓词变元代入规则 (改名).
3. Chinese Wikipedia：證明助手 (proof assistant)；外延公理/外延性公理；可构造全集 (constructible universe)；钻石原则 (哥德尔可构造全集)；超幂*R
   模型；結構 (數理邏輯) (滿足關係)；音乐同构 (典范同构)；直觉类型论 (非直谓性)；正则公理/正则性公理.
4. 郝兆宽、杨睿之、杨跃：《递归论：算法与随机性基础》(复旦大学出版社)，尾节扩张 (end extension)；《集合论导引》第二卷 (力迫扩张模型，内模型，典范作用，哥德尔可构造集论域).
5. 数学辞典 (newdu.com): rudimentary set = 初步集 (合).
6. Bohrium / 科普中国 sciencepedia：可构造宇宙；凝聚引理；累积层级/累积层次；元理论；哥德尔配数法；超幂；初等扩张.
7. 孙修远，非常大的基数和宇宙的基模型数量 (thesis)：集合论地质学，基模型的可定义性，δ-地幔.
8. 杨睿之，集合论多宇宙观简介 (logic.fudan.edu.cn/doc/_yrz/multi.pdf):
   多宇宙观，基模型关系.
9. 湖南科技大学学报 (社会科学版) 2025 no. 2，一种新的集合论哲学立场：实在论多宇宙观；自然辩证法研究 2022 no. 12，哈姆金斯的集合论多宇宙观及其辩护策略：集合论单宇宙观，集合论多宇宙观.
10. PLFA-zh (agda-zh.github.io/PLFA-zh): Adequacy = 充分性.
11. banana-space.org：经典数学基础序数 chapter (上界序数)；KP 与可计算性
    (基本 (Rudimentary))；非直谓性.
12. 集合论导引/公理化集合论 (Chinese textbook)：凝聚引理.
13. 分析与代数原理 (高等教育出版社)：载体，子载体.
14. 词项逻辑 (Chinese logic textbooks，逻辑学导论 and 逻辑学教程 chapters):
    词项.
15. 有道/欧路/三度 dictionaries: bounded quantifier = 有界量词；adequacy =
    充分性；closed formula = 闭公式，句子 (语句，sentence)；host language =
    宿主语言；canonical isomorphism = 典范同构.
16. 赵希顺《简明数理逻辑》：元语言与元理论，元数学的算术化.
17. 王路，走进分析哲学；摹状词理论研究 (theses)：摹状词理论，限定的摹状词.

### Japanese (ja)

18. Tsukuba University lecture notes (Tsuboi): logic09.pdf (端拡大 = end
    extension；順序型)；und/14logic3.pdf (始切片；対の公理).
19. Fuchino, introduction to set theory and constructibility (fuchino.ddo.jp):
    分出公理，置換公理，推移的な集合，整列順序；強制法 lecture slides.
20. Kobe University logic-workshop notes (Kurahashi)：数項 (numerals),
    ゲーデル数；LWS2 notes：各数項に関する無限個の公理；forcing notes:
    強制拡大，強制関係；Yasuda slides：反復超冪.
21. Keio (Mukai) and Tohoku (Obata) set-theory lecture notes：対の公理，整列順序，基礎の公理.
22. 数学基礎論増補版：順序数 as a 推移的 set；後者 (successor).
23. Kumamoto and Hokkaido topology notes：道 (path)，閉じた道.
24. Nagoya lecture notes：商集合 (quotient set).
25. 証明支援系 (proof assistant): standard Japanese, e.g. Japanese
    formalization/MLTT literature.
26. Kaken project summaries：帰納型 (inductive type)；集合論 keyword lists.

### Paywalled material

No paywalled source was worked around. Where a printed book is cited (郝兆宽
et al. 递归论，数学辞典，数学基礎論増補版，王路走进分析哲学)，the citation
comes from searchable excerpts or library snippets, and the printed work is
the citation. Everything else is an open lecture note, encyclopedia entry, or
open-source project.
