# LJ-1.218 report: the wing's ratio and its net removable lines

tier: pi (deepseek-subagent-mode), model `deepseek-v4-flash`. Written
incrementally (C-22). Every negative is marked **MEASURED** or **INFERRED**.

**STATUS: COMPLETE. BOTH DELIVERABLES ARE IN. NO ABORT FIRED.** No master was
edited. Nothing was committed and nothing was pushed. I did not run `make
check`.

## 0. LEAD

**THE WING IS 1.70x THE AC SIDE TODAY, and NET REMOVABLE LINES IS 695.**

| deliverable | figure | basis |
|---|---|---|
| **the wing's ratio** | **0.0155 s/line, 1.70x the AC side, 185.41 s over 11,926 lines, n=2, aggregate spread 0.4 pc** | section 1 |
| **NET REMOVABLE LINES** | **695**, every line named at `file:line`, at the ledger caliber (non-blank lines inside fences, comments counted) | section 2 |

The ratio is re-measured because the ledger's roster comments carry stale
line counts (they say Condensation 6,451 and TwelveAgree 309; the tree says
6,676 and 494). The tree's own count is unchanged from `[LJ-1.185]` at
11,926, and the seconds fell from 192.41 to 185.41, so 1.76x became 1.70x.

The removable-lines figure is the second deliverable, and it is the one
nobody has produced before. It splits into four classes, each justified
without leaning on "no consumer", because `[LJ-1.146]` measured that the
whole chain is unconsumed for one reason: the trophy is unwritten. The four
classes are the dead-name, the duplicate-definition, the abandoned-test and
the superseded-chain classes. The biggest block (523 lines) is a closed
internal chain in Condensation that no link of the wired route imports, and
that the plan's own record shows was superseded.

## 1. THE RATIO

**MEASURED, n=2, cold, warm dependencies, `GHCRTS=-A64m -I0 -M8g`, one agda
process of mine at a time, load 5.5 to 7.0 across the series (my own agda at
99 pc of one core, plus the machine's standing background: Warp, WebKit,
GF-Trader, Bitcoin-Qt). Raw: `runs/wing-ratio-n2.log`.** The tool refused
nothing, so no sibling agda was live at any start (C-12).

| quantity | value |
|---|---:|
| wing aggregate | **0.0155 s/line** |
| wing seconds | **185.41 s** |
| wing lines | 11,926 (working tree, the same source the seconds come from) |
| multiple of the AC side | **1.70x** (module-cold, same caliber, `ac_baseline_module_rate` 0.009143) |
| bar (0.009143 x 1.15 tolerance) | 0.0105 s/line |
| **GAP TO THE BAR** | **60.0 s** (11,926 x 0.010514 = 125.39 s on-bar) |
| runs | 2, aggregate spread **0.4 pc** |
| load during the series | 1m average 4.55 to 7.03 |

**The per-module rows** (the aggregate is the judgment; a row is advice):

| master | ratio | seconds | flag |
|---|---:|---:|---|
| `src/V/Collapse.lagda.md` | 0.0031 | 1.03 | under |
| `src/L/Hull.lagda.md` | 0.0064 | 2.75 | under |
| `src/V/Presentation.lagda.md` | 0.0368 | 0.66 | OVER (18 lines) |
| `src/FOL/Count.lagda.md` | 0.0027 | 1.67 | under |
| `src/L/StageCardinal.lagda.md` | 0.0050 | 2.39 | under |
| `src/L/Condensation.lagda.md` | 0.0198 | 132.28 | OVER |
| `src/L/Ordinal/SquareLaw.lagda.md` | 0.0107 | 8.28 | OVER, **NOISE** (crosses the bar) |
| `src/L/Ordinal/StageArith.lagda.md` | 0.0126 | 0.94 | OVER |
| `src/L/BoundedSubset.lagda.md` | 0.0112 | 15.78 | OVER, **NOISE** (crosses the bar) |
| `src/L/Condensation/TwelveAgree.lagda.md` | 0.0177 | 8.77 | OVER |
| `src/L/Condensation/UpperAgree.lagda.md` | 0.0183 | 5.60 | OVER |
| `src/L/Condensation/LowerAgree.lagda.md` | 0.0172 | 5.25 | OVER |

**The distribution `[LJ-1.185]` measured still holds.** The four Condensation
masters sum 151.90 s over 7,781 lines = 0.0195 s/line, 1.9x the bar; the
other eight sum 33.5 s over 4,145 lines = 0.0081 s/line, under the bar
together. 65 pc of the lines carry 82 pc of the seconds, and the wing's cost
problem is one chapter, not a broad one.

**Against `[LJ-1.185]`: 1.76x (192.41 s) then, 1.70x (185.41 s) now.** The
7 s fall is 3.6 pc, inside the between-series band, and today's machine was
busier (5.5 to 7.0 against 3.5 to 4.4 with a sibling), so the fall is not a
finding. `[LJ-1.185]`'s deflated figure of 56 s gap was the safer one; today's
raw gap is 60.0 s. Both are upper bounds on a quiet machine.

## 2. NET REMOVABLE LINES: 695

**The figure, with every line named. Four classes.** Every block below is
first MEASURED dead (its names appear nowhere in the tree outside its own
declaration lines, by occurrence scan over all in-fence code of `src/`) or
MEASURED duplicated (byte-identical with a copy in another master). The
inference that it "did not need to be written" is marked on each class.

### 2.1 Class A: dead names with a live sibling, or a superseded variant (163 lines)

**The sibling proves the content was available; this spelling has zero
readers. MEASURED dead by occurrence count; the removal is INFERRED (I did
not delete-and-typecheck).**

| lines | site | why it did not need to be written |
|---:|---|---|
| 2 | `src/V/Collapse.lagda.md:379-380` `fixes-X` | a 2-line specialization of `fixes`; `fixes` is used by `L/BoundedSubset.lagda.md:1590,1613`, `fixes-X` by nobody |
| 92 | `src/V/Collapse.lagda.md:118-219` `module Inj (Xtr : isTrans X)` | the transitivity variant of the collapse injectivity; `[LJ-1.13]` added the extensionality variant `InjExt` (`:220-312`) which SUBSUMES it (extensionality without transitivity), and every consumer applies `InjExt` (`L/BoundedSubset.lagda.md:323,1061`), never `Inj` |
| 7 | `src/V/Collapse.lagda.md:305-312` `Mostowski`/`mostowski` inside `InjExt` | the bundled statement of the collapse; no consumer projects it (uses=4, both its own two declarations) |
| 3 | `src/L/Condensation.lagda.md:3055-3057` `memE-at` | an alternative spelling of `memE-bnd`; `memE-bnd` is used 8 times (`:3728,3822,3946,4118,4482,5107,5231,5326`), `memE-at` by nobody |
| 4 | `src/L/Condensation.lagda.md:4695-4698` `opBodyM` | the machine-side body of the impl transfer; its sibling `opBodyS` (`:4701-4704`) is the one `opBack` reads (`:4716`), `opBodyM` by nobody |
| 36 | `src/L/Hull.lagda.md:359-410` the least-witness family | `Witnessed-small` `:359-360`, `small→big` `:364-366`, `big→small` `:368-370`, `toSmall` `:372-378`, `SatAt-h` `:380-382`, `leastSearch` `:388-393`, `leastSearch-spec` `:396-401`, `leastWit` `:403-405`, `leastWit-spec` `:407-410`. The hull's witness-picking is done by the LIVE `TermAlgebra.search` (`:79-81`) through `closed`/`hull-closed`; `hull-closed` is used by `L/BoundedSubset.lagda.md:446,702,1307,1327`. This family is the same idea on the SL side, read by nobody |
| 2 | `src/L/Hull.lagda.md:412-413` `hullVal` | an alias of `fst (val c)`; the live `val-in-Hull` (`:341`) is what `L/BoundedSubset.lagda.md:373` reads |
| 2 | `src/L/Ordinal/SquareLaw.lagda.md:279-280` `f-inj` | declared, read by nobody; the file's other injectivity lemmas are used |
| 4 | `src/L/Ordinal/SquareLaw.lagda.md:959-963` `via-col-square`/`via-col-truncated` | opaque aliases of `Initial.square`/`Initial.truncated` written in the same commit, read by nobody (uses=2 each, their own declarations) |
| 2 | `src/L/BoundedSubset.lagda.md:1096-1097` `leg1` | the embedding `⟪ C.πX ⟫ ↪ ⟪ M ⟫`, read by nobody; the composite at `:1574-1575` builds the same embedding directly |
| 2 | `src/L/BoundedSubset.lagda.md:1139-1140` `leg2` | the embedding `⟪ M ⟫ ↪ ⟪ α ⟫`, read by nobody |
| 6 | `src/L/BoundedSubset.lagda.md:864-870` `reverse` | the Σ₂ reverse statement of the level-hood formula, read by nobody (the level-hood block it sits in is section 2.4's `LevelHood0`, itself unapplied) |
| 1 | `src/L/Condensation/TwelveAgree.lagda.md:302` field `envSetK` of `TFacts` | a record field never projected by any definition in the tree (uses=1, its own declaration); the `lf`/`uf` record literals in the same file omit it |

### 2.2 Class B: DD4 duplication, both copies consumed (4 lines)

**The same content written twice at two carriers; one copy did not need to be
written because the masters already share an import edge. MEASURED
byte-identical; the removal (delete one copy, open the other) is INFERRED.**

| lines | site | duplicate of |
|---:|---|---|
| 2 | `src/L/BoundedSubset.lagda.md:1043-1044` `_↪_` | `src/L/StageCardinal.lagda.md:221-222`, byte-identical `X ↪ Y = Σ[ f ∈ (X → Y) ] ((x y : X) → f x ≡ f y → x ≡ y)` |
| 2 | `src/L/BoundedSubset.lagda.md:1364-1366` `comp-inj` | `src/L/StageCardinal.lagda.md:500-502`, byte-identical, inside `module Devlin55` |

`L/BoundedSubset.lagda.md:882` already does `import L.StageCardinal`, and
`:1397` instantiates it (`module SC = L.StageCardinal {ℓ} lem α ordα sq`).
Both definitions came from the same development (`[LJ-1.20-25]` wrote
StageCardinal's copy, `[LJ-1.49]` re-derived BoundedSubset's). Both copies
have consumers; the second writing is the surplus (DD4's rule: removable even
when both copies have consumers).

### 2.3 Class C: an abandoned verification artifact (5 lines)

| lines | site | why |
|---:|---|---|
| 5 | `src/L/Condensation.lagda.md:7271-7275` `consed` | a definition whose own comment calls it "the test": it exists to prove `KFactsCons` accepts the record at the consumer's indices. Read by nobody (uses=2, its own declaration). A verification artifact left in the delivered master |

### 2.4 Class D: the superseded erase-transfer chain in Condensation (523 lines)

**A closed internal chain with ZERO application points. MEASURED: no module in
the tree applies any of it, and no link of the wired route imports any of it.
The plan's own record shows the route it belongs to was the false start.
The removal is INFERRED.**

| lines | site | what it is |
|---:|---|---|
| 4 | `src/L/Condensation.lagda.md:266-270` | `existCertAt`/`Σ₁-cert`, the exist-row certificate; its only consumer is the dead `CertTransfer` below |
| 23 | `:284-314` | `module EraseTransfer`, the σL erase-transfer template |
| 43 | `:315-360` | `module ClauseDecode`, the clause decode and its `σL-out`/`σL-in` |
| 4 | `:408-411` | `module CertTransfer` with `cert-transfer`, never applied |
| 10 | `:418-428` | `ride-only`/`ride-defines`, the tower-landing legs |
| 13 | `:1791-1803` | `module RowTransfer`, applies EraseTransfer per row |
| 9 | `:1805-1813` | `module RowDecode`, never applied |
| 417 | `:1814-2230` | the eleven `*Row` modules `BotRow` `:1814`, `TopRow` `:1845`, `NegRow` `:1880`, `ForallRow` `:1920`, `AndRow` `:1960`, `OrRow` `:2000`, `ImpRow` `:2040`, `MemRow` `:2080`, `EqRow` `:2115`, `AllInRow` `:2150`, `ExInRow` `:2190` — never applied |

**Why this is the surplus side of the no-consumer test, and not the
trophy-unwritten side.** `[LJ-1.146]` measured that the whole wing's chain is
unconsumed because the trophy is unwritten. That applies to the chain's LINKS:
TwelveAgree, the agreement modules, the hull, the collapse, the square law.
The erase-transfer chain is not a link. Nothing on the wired route imports it:
the agreement modules (`TopAgree` `:3663` and its siblings, which
`TwelveAgree` and `SatGraphAgree` consume) never mention `σL`, `EraseTransfer`,
`RowTransfer`, `RowDecode`, `ClauseDecode`, `CertTransfer`, `ride-*` or any
`*Row` name (MEASURED by occurrence scan; zero hits outside `:266-430` and
`:1791-2230`). **When the trophy lands and the chain is exercised, the
erase-transfer chain stays unexercised. Its untestedness is not explained by
the unwritten trophy; it is explained by the tree having chosen another
route.**

**The plan's own record supports the supersession.** `dev/PLAN.md:553` records
that the row content `[LJ-1.37]` built landed "DEFECTIVE... The rows are false
of the satisfaction table" and `:555` re-opened 968 of 2,141 lines;
`:561` records that the AGREEMENT route (`[LJ-1.43]`) closed the twelve-row
table; `:562-563` record the layer held "Two spellings per leaf" and was
"restated in ONE spelling" by `[LJ-1.45]`. The agreement route is the one
wired toward the consumer (`SatGraphAgree` takes `twelve-out`/`twelve-back`,
whose types match `TwelveAgree`'s output). The erase-transfer rows are the
spelling the placement went elsewhere.

**One honesty note.** The agreement route and the erase-transfer rows prove
DIFFERENT theorems (agreement out/back versus σL decode), so this is a
superseded parallel development, not a byte-duplicate. If the future trophy
wants erase-transfer content, it will have to wire this family for the first
time (C-35: a delivered block with no consumer is untested), or re-derive it
on the route that is wired. Either way, these 523 lines as written did not
need to exist in their present form.

## 3. WHAT I READ AND DID NOT CALL REMOVABLE

This half is what makes the figure trustworthy. **MEASURED dead or MEASURED
on the trophy-unwritten side, and explicitly kept out of the 695.**

| block | lines | why it stays |
|---|---|---|
| the whole `*Agree` architecture (`TwelveAgree` 494, `UpperAgree` 305, `LowerAgree` 306) | 1,105 | unconsumed, but it is the WIRED route: `TwelveAgree`'s `twelve-out`/`twelve-back` are the types `SatGraphAgree` takes as hypotheses (`src/L/Condensation.lagda.md:6812-6815,7097-7100`). `[LJ-1.146]`'s trophy-unwritten side |
| `module LevelHood` `src/L/BoundedSubset.lagda.md:74-150` and `module LevelHood0` `:840-872` | 96 | dead today (LevelHood applied only by dead LevelHood0), but a SINGLE spelling of the level-hood Σ₁ fact, not a two-spelling loser. The trophy's transfer needs the Σ₁-ness of levels, and the concept is live elsewhere (`LsetGraphAt` in `src/L/Hierarchy.lagda.md`). `[LJ-1.146]`'s side |
| `module OrderAt` `src/L/Hull.lagda.md:437-506` and its wrappers `OrderAtom` `:511-513`, `OrderAtStage` `:524-526` | 74 | dead today (nothing applies them), but a single spelling of the order-atom Σ₁ certificate that the transfer needs. `[LJ-1.146]`'s side |
| `+ω` and its family in `src/L/Ordinal/StageArith.lagda.md:27-75` (plus `_⊆_` `:20-22`) | 38 | no consumer (the AC side's `L.Coding.Bound.lagda.md:104-107` states the analogous fact as a HYPOTHESIS, `powIter`, with no supplier). The `+ω` block is the standard δ+ω bound machinery for condensation; a planned supplier, not a surplus. `[LJ-1.146]`'s side |
| `SquareLaw`'s `sq`, `square`, `truncated`, `Initial`/`InitialCore` | 250 | the chapter's own content, unconsumed because the trophy is unwritten |
| `TwelveAgree`'s `TFacts`/`LowerAgree`'s `LFacts`/`UpperAgree`'s `UFacts` | ~150 of duplicated field declarations | the three records re-declare the frame's fact fields (LFacts 37, UFacts 35, TFacts re-declares the union). Removing the duplication needs a record-of-records restructure, which `[LJ-1.210]` measured WALLS at 8 GB heap for a different record bundle. A refactor whose typecheck is unknown is not a "did not need to be written" case; reported, not counted |
| the `isNumeral` property written 63 times in types | 63 occurrences | `[LJ-1.214]` measured that removing the component recovers 7,925 ms AND un-cures 21 false fields. It is the wing's content, not surplus |
| the wing's chain content generally (`BoundedSubset`'s theorem region, the collapse, the hull, `Count`, `StageCardinal`) | — | `[LJ-1.146]` measured C-35 fires wing-wide for one cause: the trophy is unwritten. Retiring any link retires the wing |
| `StageCardinal`'s own `_↪_` | 2 | used inside `StageCardinal` (`fin-inj`, `Upper.branch`); the DUPLICATE is BoundedSubset's copy, counted in 2.2 |

## 4. DD4

**Maximize the code the two proofs share, and write it generic. One rule, two
ends, no metric and no checker.**

- **The measured duplicate in the wing is small: `_↪_` and `comp-inj`, 4
  lines, section 2.2.** The two wing masters already share an import edge and
  one copy was re-derived by `[LJ-1.49]` two tasks after `[LJ-1.20-25]` wrote
  the other.
- **The `*Agree` three-master structure is a shared-shape repetition that the
  project already factored as far as Agda allows.** The three records, the six
  module applications and the `sixB`/`sixAt`/`out`/`back` shape repeat, but
  each row's facts differ and the telescope-to-record move (`[LJ-1.158]`,
  measured 69 pc faster) is the DD4-factored form already in place. The
  remaining repetition is the record-field re-declaration, section 3, kept
  out of the figure because the restructure is unmeasured.
- **The class-generic lesson of `[LJ-1.210]`/`[LJ-1.213]` does not reach the
  wing masters.** Those measured the `L.Coding.*` chain, which is shared
  machinery below both towers. The wing's Condensation chain is about L's own
  satisfaction; the erase-transfer layer is the one place where a generic form
  might have served (the template is already parameterized by formula, `:284`),
  and it is the dead chain of section 2.4.
- **The ratio and the removable figure are independent of DD4's direction.**
  Removing the 695 lines would not flatter the ratio: the denominator would
  shrink to 11,231 while the seconds saved are unmeasured, and DD24's bar
  judges the wing as delivered. Measure 3 is a benchmark discount for
  `[LJ-2.1]`, not a licence to delete (P-q).

## 5. EVERY NEGATIVE, CLASSIFIED

| statement | class |
|---|---|
| the wing is 1.70x the AC side, 0.0155 s/line, n=2 | **MEASURED.** 185.41 s over 11,926 lines, spread 0.4 pc, load 5.5 to 7.0 |
| the gap to DD24's bar is 60.0 s | **MEASURED** as raw seconds; the 56-to-67 s band of `[LJ-1.185]` still brackets it |
| eight of twelve wing masters are under the bar together | **MEASURED.** The four Condensation masters carry 151.90 s of 185.41 |
| `fixes-X`, `memE-at`, `opBodyM`, `f-inj`, `leg1`, `leg2`, `hullVal`, `consed`, `envSetK`, `via-col-*`, `reverse` have no reader | **MEASURED** by occurrence scan over all in-fence `src/` code |
| `module Inj` is superseded by `InjExt` | **MEASURED** the consumer applies `InjExt` only; the subsumption is **INFERRED** |
| the least-witness family in Hull is redundant with `TermAlgebra.search` | **INFERRED** (the live `hull-closed` uses `search`; the family has zero readers, which is MEASURED) |
| the erase-transfer chain (523 lines) has no application point | **MEASURED.** Zero occurrences of its names outside `:266-430` and `:1791-2230`; the agreement modules never import it |
| the erase-transfer chain did not need to be written | **INFERRED** from the plan's record: `[LJ-1.37]` DEFECTIVE, `[LJ-1.38-R]` rows false, `[LJ-1.43]` the agreement route closed the table |
| the `*Agree` architecture and the LevelHood/OrderAt/`+ω` families are removable | **MEASURED FALSE** for the purpose of this figure: they are the trophy-unwritten side, `[LJ-1.146]`'s finding applies |
| any removable line here improves the ratio | **MEASURED FALSE** as a purpose. Removing 695 lines shrinks the denominator to 11,231 with unmeasured seconds; this is a report, not a licence (P-q) |
| I edited a master, committed, pushed, ran `make check` | **MEASURED FALSE**, none of these |
| I ran more than one agda process, or raised the cap | **MEASURED FALSE.** One at a time, `-A64m -I0 -M8g` |
| the machine was quiet | **MEASURED FALSE.** Load 4.5 to 7.0; every figure carries it |

## 6. CHECKERS AND THE MACHINE

| checker | result |
|---|---|
| `scripts/lint-prose.py --check` on this report | exit 0 |
| `scripts/lint-agda.py --check` | exit 0 |
| `scripts/check-probes.py` | clean, 2,059 tracked files, no probe outside `agents/tasks/` |
| `make check` | NOT RUN, the orchestrator runs it |
| agda | ONE process at a time via `check-ratio.py`, `GHCRTS=-A64m -I0 -M8g`, no heap wall |

Machine: load 4.5 to 7.0 throughout the ratio series; the background is the
standing one (Warp, WebKit renderers, GF-Trader, Bitcoin-Qt), the same
sources `dev/ledger.toml:2556-2557,2877` recorded on 2026-08-13.

## 7. LITERATURE (DD18)

Nothing in the literature governs removability.

## 8. ARCHIVE USED (DD18)

- **`agents/tasks/LJ-1-185/lj-1.185-report.md`, read WHOLE with its `runs/`.**
  **TOOK:** the 1.76x ratio and 56-to-67 s gap (`:5.1`), which section 1
  re-measures; the per-master distribution (`:5.3`), which holds unchanged;
  the load-discipline shape (load beside every figure).
- **`agents/tasks/LJ-1-214/lj-1.214-report.md`, read WHOLE.** **TOOK:** the
  7,925 ms / 21 false fields measurement, which is why the `isNumeral` 63
  occurrences stay in the tree (section 3).
- **`agents/tasks/LJ-1-209/lj-1.209-report.md`, read WHOLE.** **TOOK:** the 63
  occurrence count of the numeral property; the four-rung ladder showing the
  content and transparency are not the cost. **Used to refuse** calling the
  numeral component removable.
- **`agents/tasks/LJ-1-210/lj-1.210-report.md` and
  `agents/tasks/LJ-1-213/lj-1.213-report.md`, read WHOLE.** **TOOK:** the
  class-generic port measurements (42 lines for 1,288; 19 for 391), used in
  section 4 to bound what DD4 reaches in this wing; the record-bundle heap
  wall (`[LJ-1.210]` section 9), used in section 3 to keep the
  TFacts/LFacts/UFacts restructure out of the figure.
- **`dev/ledger.toml`**, the `[ratio]` table and the `gch_wing` roster.
  **TOOK:** the twelve masters; the bar `ac_baseline_module_rate` 0.009143 and
  the 1.15 tolerance; **the roster's stale line comments** (Condensation
  6,451 vs 6,676; TwelveAgree 309 vs 494), which is why the brief said lines
  had moved when the tree's count had not.
- **`dev/PLAN.md` DD5 measure 3 (`:262`) and DD24 (`:273`), read whole.**
  **TOOK:** measure 3's independence requirement, which this report is built
  to satisfy; DD24's bar formula.
- **`dev/PLAN.md:553-563`, the `[LJ-1.37]`-to-`[LJ-1.45]` rows.** **TOOK:**
  the DEFECTIVE/false-rows record and the two-spellings-one-spelling record,
  which justify the section 2.4 supersession classification. **What does NOT
  transfer:** those rows judged the row layer's speed; this report judges its
  existence.
- **`agents/tasks/LJ-1-146/lj-1.146-report.md`, read whole.** **TOOK:** the
  finding that C-35 fires wing-wide and that the trophy is the cause; this is
  the rule that keeps every chain link out of the figure and forces the
  section 2.4 argument to stand on supersession, not on absence of consumers.
- **`archive/dev/TASKS-archived.md`: SURVEYED, NOT USED.** **TOOK SHAPE, never
  a claim:** the archive's task records carry the pattern of a report that
  names its evidence at `file:line`; the archived route holds no removable
  lines figure, because DD5 measure 3 postdates it. **What would NOT
  transfer:** any archived line count; the retired route's masters do not
  exist in `src/`.
- `scripts/check-ratio.py`, read for the instrument's own band (`:65-85`, the
  12.8 pc between-series figure) and for the aggregate-is-the-judgment rule.

## 9. THE FILES

All under `agents/tasks/LJ-1-218/`, tracked, none near `src/`.

| file | what it is |
|---|---|
| `lj-1.218-report.md` | this report, written incrementally (C-22) |
| `deadnames.py` | the occurrence scanner: reads in-fence code of all `src/*.lagda.md`, lists every declaration of the twelve wing masters and every occurrence of each name, so a dead name is MEASURED rather than asserted |
| `runs/wing-ratio-n2.log` | the raw `check-ratio.py --runs 2` output, with the tool's own spread and noise flags |

## 10. WHAT I RECOMMEND, offered and not taken

1. **Write the 695 into `dev/ledger.toml` `lines_removable`.** It is a
   report; nothing is removed by this task (P-q).
2. **Treat the erase-transfer chain (523 lines) as the one block worth a
   decision.** It is the only big finding on the surplus side. If the owner
   disagrees with the supersession reading, the figure falls to 172 (classes
   A + B + C) and the
   four classes in section 2.1-2.3 stand on their own.
3. **Re-measure the ratio on a quiet machine before DD24 rests on the 60 s.**
   Today's run carried load 5.5 to 7.0 and is an upper bound, exactly as
   `[LJ-1.185]`'s was.
4. **Let `[LJ-2.1]` record measured, projected and removable side by side.**
   The three numbers are now all on the table: 11,926 measured, the wing's
   a-priori band from `[LJ-1.1]`, and 695 removable.
