# LJ-1.342 report: land the generic `μ` form, with its prose

tier: opus (in-harness-subagent-mode), the switch's DEFAULT row. Rewrite proposal.
It lands nothing. Written incrementally (C-22).

## LEAD LINE

**THE LANDING VERIFIES. The final line delta is MINUS 11**, measured over both
chapters whole. The proposal typechecks, all 12 consumers stay green, the check
time delta is UNMEASURABLE against a 0.79 s empty-file floor, the closure does
not move, and every delivered signature is reproduced character for character.

**ONE REFUSAL, and it is the brief's second abort row.** The Japanese is NOT
written. MEASURED: `src/` holds 96 masters and **ZERO** carry a `<!--ja-->`
marker; `Makefile:29` builds `LANGS := en,zh`. Writing Japanese here needs at
least eight renderings `dev/glossary.toml` does not have, and DD19 forbids me to
choose them. Section 6 names them. **The English and the Chinese are complete.**

## 1. THE DIFF

`agents/tasks/LJ-1-342/lj-1.342-landing.diff`, 373 lines, two files.
**`git apply --check` passes against the live tree.** The two proposed files are
`agents/tasks/LJ-1-342/Stage.proposed.lagda.md` and `Step.proposed.lagda.md`.
**They are byte-identical to the files that typechecked** (`cmp`, both files).

**`src/` is untouched.** `git status --short` shows only new files under
`agents/tasks/LJ-1-342/`.

### 1.1 What moves, in `L.Choice.Stage`

The chapter had three headed sections after `μ`. It now has three again, cut in
a different place, because `predOf` closes its truncation on `isPropPredOf` and
therefore has to sit after it.

| section | before | after |
|---|---|---|
| "A first appearance is a successor" | `IsPredOf`, `below-case`, `same-case`, `meet-suc` (29 lines) | replaced |
| "The predecessor of a least stage" (NEW heading) | | `IsPredOf`, `cycle₂`, `mem-branch`, `ord-suc-inj`, `isPropPredOf`, then `module _ (P : S → Ω)` with `Carved`, `below-case`, `same-case`, `atCarve`, `predOf`, `carveAt` |
| "A first appearance is a successor" | | `carveMeets` (4), `meet-suc` (3) |
| "The stage a first appearance is defined over" | `cycle₂`, `mem-branch`, `ord-suc-inj`, `isPropPredOf`, `thePred`, `defStage` seal | `thePred` (4), `defStage` seal (11) |

**The uniqueness chain moves UP, unedited.** `cycle₂`, `mem-branch`,
`ord-suc-inj` and `isPropPredOf` are copied character for character; only their
position changes. Their delivered prose paragraph moves with them.

### 1.2 What moves, in `L.Choice.Step`

- `decideSuc` (8 lines) and `atCarve` (12 lines) are DELETED. `theCarve` goes
  from 3 lines to 4 and calls `predOf` and `carveAt`.
- **One import edge is retired:** `open import L.Ordinal.Stages {ℓ} lem using
  ( suc∈or≡ )`, the whole line.
- Four names leave `using` lists: `Lset-out`, `𝒟ₒ` (`L.Constructible`),
  `suc-ord` (`L.Ordinal`), `isPropPredOf` (`L.Choice.Stage`).
- Two names enter one `using` list: `predOf`, `carveAt`, both from
  `L.Choice.Stage`, which the chapter already imports.

**`[LJ-1.340]:252` says Step adds THREE names, including `Carved`. MEASURED
FALSE.** `Carved` never appears in Step's text, so `lint-agda.py` rule C flags
it as an unused import. Step adds TWO.

**`L.Choice.Stage`'s import block is BYTE-IDENTICAL before and after** (`diff`,
first 40 fence lines). **This confirms `[LJ-1.340]`'s zero-new-import figure.**

## 2. THE LINE DELTA. MEASURED, whole chapters

Non-blank lines inside ` ```agda ` fences, over the WHOLE file, not a span.

| file | before | after | delta |
|---|---:|---:|---:|
| `src/L/Choice/Stage.lagda.md` | 140 | 149 | **+9** |
| `src/L/Choice/Step.lagda.md` | 362 | 342 | **-20** |
| **pair** | **502** | **491** | **-11** |

**`[LJ-1.340]` priced this at MINUS 10 and the landing gives MINUS 11.** The
extra line reconciles exactly: `[LJ-1.340]` counted the retired import edge as an
EDGE and not as a LINE. `open import L.Ordinal.Stages ...` is one physical line
inside a fence. **Argument delta MINUS 10, import line MINUS 1, total MINUS 11.**

**`meet-suc` IS KEPT**, so this is the safe figure with every delivered export
alive. **MEASURED, by `grep -rn 'meet-suc' src/`: its only hits outside its own
chapter are PROSE, at `src/Everything.lagda.md:658` and `:988`. There is no code
consumer.** Retiring it would delete `carveMeets` and `meet-suc`, save 4 more
lines, and force two edits to `src/Everything.lagda.md`, which I must not touch.
**I did not retire it, and the retirement is the orchestrator's to price (DD13).**

## 3. THE CHECK TIME. UNMEASURABLE, and the floor is stated (C-53)

**MEASURED**, one agda process, `GHCRTS="-A64m -I0 -M8g"`, cap never raised. The
slot count ran before every invocation with the brief's exact command and
returned 0 or 1 every time. Both trees are full copies of `src/` in the session
scratchpad, outside the repository, each with its own `_build`.

| | round 1 | round 2 | round 3 |
|---|---:|---:|---:|
| **delivered**, `L.Choice.Stage` then `L.Choice.Step` | 3.13 s | 2.27 s | 2.29 s |
| **proposal**, same two | 2.28 s | 2.27 s | 2.24 s |
| **empty-file floor**: Stage's exact import block, no content | 0.79 s | 0.79 s | 0.83 s |

**THE FLOOR IS 0.79 s.** The gap between the two forms is at most 0.05 s and at
median 0.01 s. **That is 16 times smaller than the floor and inside the spread
of one file, so the delta is UNMEASURABLE and not small.** The delivered round 1
figure of 3.13 s is a first-run artifact; its own next two rounds are 2.27 and
2.29.

**THE WHOLE TREE, cold, 95 masters: 299.92 s, exit 0** (the delivered copy).
**THE WHOLE TREE under the proposal, warm: 37.33 s, exit 0.** No heap
exhaustion, no wall, no run past 300 s. C-55 did not fire, for the reason
`[LJ-1.340]` gave: the property is a module parameter.

## 4. EVERY CONSUMER. ALL GREEN, and the list is mechanical

**I did not trust a grep for this.** The proposal tree was rebuilt from a warm
cache, so **the modules Agda re-checked ARE the transitive consumer cone**.

| # | module | result |
|---|---|---|
| 1 | `L.Choice.Step` | green |
| 2 | `L.Choice.Stage` | green |
| 3 | `L.Choice.Table` | green |
| 4 | `L.Choice.Faithful` | green |
| 5 | `L.Choice.Order` | green |
| 6 | `L.Cardinal` | green |
| 7 | `L.Absorption` | green |
| 8 | `L.Choice.Transversal` | green |
| 9 | `L.Model` | green |
| 10 | `Landmarks` | green |
| 11 | `L.GCH` | green |
| 12 | `L.Hull` | green |
| 13 | `L.BoundedSubset` | green |
| 14 | `Everything` | green |

**12 consumers plus the two chapters. `agda src/Everything.lagda.md` exits 0.**

**THE BRIEF'S AT-RISK PREMISE HELD, with one correction.** The premise was「the
prose is the only thing missing」. **MEASURED: no consumer breaks, because no
consumer reads a name the rewrite touches.** The five names consumers import
from Stage are `stageBound`, `bound-below₂`, `ord-suc-inj`, `IsPredOf` and
`isPropPredOf`, and all five survive unchanged. **The correction is `Carved`**
(section 1.2): the sibling's import list was wrong by one name, and it would have
gone red on `lint-agda.py` and not on Agda.

### 4.1 The public export sets

**MEASURED, mechanically.** Step's public declaration set is UNCHANGED. Stage's
gains four names and loses none: `Carved`, `predOf`, `carveAt`, `carveMeets`.

**TWELVE delivered signatures compared character for character, 0 mismatches:**
`meet-suc`, `thePred`, `defStage`, `defStage-ord`, `defStage-suc`, `IsPredOf`,
`isPropPredOf`, `ord-suc-inj`, `theCarve`, `birth`, `birth-ord`, `birth-suc`.
That is `[LJ-1.340]`'s nine plus three it did not list.

### 4.2 `src/Everything.lagda.md`. NOT touched, and NOT false

**MEASURED, by reading both entries whole** (`:655-661` and `:697-704`, with the
Chinese at `:988` and `:991`). **Nothing there becomes false.** It says
`meet-suc` makes the stage a successor, which still holds at the same type; and
it says `birth` exists「for the reason the choice-stage chapter gave for a
cell」, which the landing turns from a shared REASON into shared CODE.
**It is INCOMPLETE, not wrong: it names no `predOf` and no `carveAt`.** That is
the orchestrator's file and his call.

## 5. THE THREE CHECKS ON MY COPIES. ALL CLEAN

```
lint-prose.py --check  <both copies>   exit 0
lint-agda.py  --check  <both copies>   exit 0
weave-i18n.py --check  <both copies>   exit 0
```

**I DID NOT TRUST A GREEN EXIT.** A sanity copy with four injected defects (an em
dash, a half-width comma in Chinese, an unused import name, a `<!--fr-->` marker)
was linted at the same path shape. **All four fired.** So the green above is a
measurement of my files and not of a skipped path.

**THE TWO THINGS `weave-i18n.py` MISSES, CHECKED BY EYE AND BY SCRIPT** (the
brief names both): **no mid-line marker** and **no fence inside a language
group**, in either copy. The delivered originals are clean on the same test, so
the test is calibrated.

## 6. THE JAPANESE. A REFUSAL, and what has to happen first

**THE BRIEF ORDERS THREE LANGUAGES. I DELIVER TWO, AND HERE IS THE
MEASUREMENT.**

1. **`src/` has 96 masters and ZERO carry `<!--ja-->`.** MEASURED, by
   `grep -rl '<!--ja-->' src/ --include='*.lagda.md'`.
2. **`Makefile:29` reads `LANGS := en,zh`.** The site does not build Japanese.
3. **`dev/STYLE-i18n.md:33` states the state of play**:「The initial rollout is
   bilingual (`en` + `zh`); `ja` is pre-supported.」
4. **`dev/STYLE-i18n.md:29-31`:** a group with no `<!--ja-->` falls back to
   English and the page is flagged「not yet translated」. So Japanese in 5 of
   Stage's 15 groups and 3 of Step's 24 would render a MIXED page, which is worse
   than a uniform English fallback.

**AND DD19 IS THE HARD STOP.** The new prose needs renderings for these, and
`dev/glossary.toml` has an entry for NONE of them. MEASURED, by reading the
file's complete `en =` list:

| concept | Chinese, FIXED by delivered prose | Japanese |
|---|---|---|
| predecessor (of an ordinal) | 前一阶段, `src/L/Choice/Stage.lagda.md:223` | **MISSING** |
| cell | 格, `Stage.lagda.md:28` | **MISSING** |
| carve | 雕出, `Stage.lagda.md:30` | **MISSING** |
| truncation | 截断, `Stage.lagda.md:90` | **MISSING** |
| seal | 封印, `Stage.lagda.md:119` | **MISSING** |
| least stage | 最小阶段, `Stage.lagda.md:74` | **MISSING** |
| module parameter | 模块参数, `Step.lagda.md:322` | **MISSING** |
| generic | 泛型, `Stage.lagda.md:89` | **MISSING** |

**The Chinese cost me no choice: every rendering above is already in the two
chapters I am rewriting.** The Japanese would cost me eight choices, and the
brief says「STOP and name it; do not invent one」. **I stopped. The eight are
named.**

**WHAT I RECOMMEND, and it is one question for the owner, not eight:** rule
first on whether `src/` takes Japanese at all. If the answer is no, the landing
is complete as delivered. If it is yes, the job is 96 masters and DD19's pipeline
for a glossary that is far larger than eight terms, and it is not this task.

## 7. THE PROSE. What it now says, and the sentence that was wrong

**Authored in English first, then translated, then cross-checked** (`AGENTS.md`).
**The Chinese and the Japanese were NOT cross-checked against each other, because
there is no Japanese.** I state that rather than claim a check I did not run.
**The English and the Chinese WERE cross-checked against each other**, clause by
clause, on both chapters: same claims, same order, same emphasis marks, and every
`{.Agda}` span present in both.

### 7.1 The delivered sentence that was measurably wrong

`src/L/Choice/Step.lagda.md:90` said:

> The argument applies verbatim to a single set, and for the same reason.

**REPLACED.** The new text says all three things `[LJ-1.340]` measured:

> ... A cell is met by *some* member, so the choice-stage chapter has a
> truncation to strip before it can hand the argument a witness; a set is its own
> witness, and there is nothing to strip. The application there is eleven lines
> and the one here is four. What this chapter used to claim, that the argument
> applies verbatim to a single set, was true of the split and of the carve and
> false of the interface: `meet-suc`{.Agda} asks for a cell that is met, and a
> single set cannot supply one, so the reuse it named was never available until
> the argument itself was written over the property.

That covers: the truncation layer, the direction (Step is the SIMPLE setting),
and「direct reuse was never available」. The Chinese says the same three things.

### 7.2 What the prose says about the shape

- **Stage, new section "The predecessor of a least stage".** Says what `Carved`,
  `predOf` and `carveAt` are; says WHY they are one operation and not two
  (「`carveAt` builds exactly what `predOf` takes, and no site has ever wanted
  one of them alone」); says the property is a parameter because the argument
  never reads it.
- **Stage, "A first appearance is a successor".** Says what the cell's
  application does: one truncation, and nothing else.
- **Stage, "The stage a first appearance is defined over".** Unchanged in
  substance; one sentence rewired, because the extraction now happens inside
  `predOf`.
- **Step, "The stage a set is carved at".** Says what Step's application does,
  and carries the correction of 7.1.
- **Both recaps** name `predOf` and `carveAt` and state which instance is which.

**THE THIRD SITE IS NOT MENTIONED.** `src/L/Reflect.lagda.md:175` is a capability
with no consumer. The brief said「mention it only if it reads naturally」, and in
a chapter recap that names only delivered consumers it would not.
**I claim no line for it, as `[LJ-1.340]` did not.**

## 8. DD9: IS THE NEW SHAPE CHEAPER TO READ? YES AT STEP, NEUTRAL AT STAGE

**This is the brief's third abort row and I answer it honestly, not with the
line count.**

**CHEAPER, and these are the reasons that are not the 10 lines.**

1. **The argument exists once.** A reader who asks「why is a least stage a
   successor」today reads two proofs of 31 and 23 lines and cannot tell whether
   they are the same proof. **`[LJ-1.340]` needed a whole dispatch to answer
   that.** After the landing the answer is in the source.
2. **One name stops meaning two things.** `atCarve` is a name in BOTH chapters
   today and it denotes DIFFERENT functions: `Stage.lagda.md:185` takes a member
   and its membership, `Step.lagda.md:115` takes a carve triple. After the
   landing there is one `atCarve`, private, inside the generic module.
3. **Step loses 20 lines of proof and an import edge**, and its prose stops
   explaining a split it no longer contains.

**THE ONE HONEST DEBIT.** Step's `theCarve` writes the property lambda
`(λ σ → x ∈ˢ Lset σ)` TWICE in four lines. **I priced the named alternative and
it typechecks** (`alt` tree, 3.08 s):

```agda
theCarve x p = predOf inTower (stage x p) (stage-ord x p) (stage-earliest x p)
  (carveAt inTower (stage x p) x (stage-mem x p) (λ δ hz → hz))
  where
  inTower : S → Ω
  inTower σ = x ∈ˢ Lset σ
```

**It costs PLUS 2 lines, so the delta becomes MINUS 9.** I did not take it: the
brief funds the form `[LJ-1.340]` measured, and this is a taste call at 2 lines.
**It is yours, priced.**

**NEUTRAL AT STAGE, stated plainly.** Stage grows 9 lines and gains one
`module _ (P : S → Ω)` layer, so a reader of that chapter meets an abstract
property before meeting the cell. **What it loses is `meet-suc`'s 20-line body
with two nested `where` blocks, which becomes 3 lines.** I judge that a wash, and
I do not claim Stage got easier.

**SO: NO REFUSAL ON DD9.** The pair is cheaper to read, the gain is
concentrated at Step, and the cost is one abstraction layer at Stage.

## 9. THE CLOSURE. The axis is AC against GCH

**NAME THE AXIS (C-46): AC against GCH**, fixed at `scripts/measure/ledger.py:50`.

**MEASURED, by an import-graph walk from `src/L/Model.lagda.md` and
`src/L/GCH.lagda.md`, run over BOTH trees, with no Agda:**

| | AC | GCH | shared |
|---|---:|---:|---:|
| delivered | 73 | 48 | 43 |
| **proposal** | **73** | **48** | **43** |

**NOTHING MOVES. Zero new masters at either end, zero masters lost.** My walker
reproduces `[LJ-1.339]:326-327` and `[LJ-1.340]:403-407` exactly, which
cross-checks three tools.

**THE RETIRED EDGE COSTS NO MASTER, and I checked why:**
`L.Ordinal.Stages` stays in both closures because `src/L/Choice/Stage.lagda.md:51`
imports it too. **MEASURED in both trees.**

**BOTH CHAPTERS ARE IN BOTH CLOSURES. MEASURED.** So all 29 generic lines are
shared code by construction, at both ends.

**THE GCH FIGURE UNDERSTATES, AND I MARK IT.** `dev/ledger.toml:204` records that
the GCH closure is read from a STATEMENT whose proof is not wired. **My 48
carries that understatement unchanged. I did not correct it and I could not.**

**THE REFUSED EDGE STAYS REFUSED.** `Lset-out′` at
`src/L/Coding/Bound.lagda.md:120` would cut `carveAt` from 7 lines to 5 and add 2
masters to BOTH closures. **I did not take it. `carveAt` is local.**

## 10. THE ABORT CRITERION, ANSWERED ROW BY ROW (D-1)

| the brief's row | outcome |
|---|---|
| **THE LANDING VERIFIES** | **TAKEN.** Diff, times, 12 green consumers, English and Chinese |
| **A GLOSSARY TERM IS MISSING** | **TAKEN, for Japanese only.** Section 6 names eight. The Chinese needed none |
| **THE PROSE CANNOT DESCRIBE THE NEW SHAPE HONESTLY** | **NOT TAKEN.** Section 8 |
| **A CHECK GOES RED** | **NOT TAKEN.** Agda exit 0, three linters exit 0 |

## 11. WHAT I DID NOT SETTLE

1. **Whether `src/` takes Japanese.** Owner's call. Section 6.
2. **Whether `meet-suc` should be retired.** No code consumer, MEASURED. It costs
   two `src/Everything.lagda.md` edits and saves 4 lines. DD13 prices it from the
   rewrite side and I did not price that rewrite.
3. **Whether `src/Everything.lagda.md` should name `predOf` and `carveAt`.**
   Nothing there is false. Section 4.2.
4. **The named-property variant at Step.** Priced at plus 2 lines, typechecked,
   not taken. Section 8.
5. **The third site at `src/L/Reflect.lagda.md:175`.** Untouched. No consumer
   asks for it and I claim no line.
6. **The whole-tree cold time under the proposal.** I measured the tree cold ONCE
   (delivered, 299.92 s) and warm under the proposal (37.33 s). **P-l forbids me
   from calling the proposal's cold time 300 s by analogy. I did not measure it.**

## 12. ARCHIVE USED (DD18), ONE LINE READ PER FILE

- **`agents/tasks/LJ-1-340/lj-1.340-report.md`, READ WHOLE.** Line read `:164`:
  「**IT SAVES 10 LINES with every delivered export kept. MEASURED.**」
  **TOOK: the generic form verbatim from `ProbeGeneric.agda:54-88`, the
  `meet-suc`-kept application from `ProbeThird.agda:54-66`, the refused
  `Lset-out′` edge, and the wrong-prose finding of its section 7.**
  **CORRECTED TWO THINGS: the saving is 11 and not 10** (the retired import line,
  section 2), **and Step adds TWO imported names and not three** (`Carved` is
  never used there, section 1.2).
- **`agents/tasks/LJ-1-339/lj-1.339-report.md`**, READ `:39`, `:104`,
  `:145-147`, `:153`, `:155`, `:326-327`. Line read `:104`:「`defStage` and
  `birth` are the same construction under two names」. **TOOK: that measurement
  as the DD9 argument of section 8, and the closure figures at `:326-327`, which
  my own walker reproduces exactly on both trees.**
- **`archive/dev/TASKS-archived.md`, SHAPE ONLY, never a claim.** Line read
  `:243` (L3.32-T239):「Make the limit clause carrier-generic, as the successor
  clause already is | GREEN, net **+26** at the first site」. **TOOK, SHAPE ONLY:
  the retired route landed a generic rewrite that came out net PLUS lines, so a
  generic form is not a saving by nature and the count decides. My count is minus
  11. WHAT WOULD NOT TRANSFER: that dispatch landed code and no prose, and its
  chapter was mono-lingual on the retired route; my two chapters carry 39
  language groups between them, so its line figure prices nothing here and I
  quote none of it as a comparable.**

## 13. LITERATURE USED (DD18)

**No mathematical literature bears on writing an operation generic or on
describing it in prose.** The question is a code-sharing question about this tree
and a house-style question about this repository. **I read no source and I cite
none. WHY NOT: there is nothing to cite.**

## 14. DD4, STATED AND ANSWERED

**DD4: maximize the code the two proofs share, and write it generic.** One rule,
two ends, no metric and no checker.

**ANSWERED, and this landing IS the rule.** 54 lines of argument at two sites
become 29 lines written once plus 15 lines of application. **Both sites return
AC=True and GCH=True (section 9), so every one of the 29 lines is shared code by
construction at both ends.** The form costs zero new masters, zero new imports,
and it retires one import edge.

## 15. PROHIBITIONS, ANSWERED

- **Writes: `agents/tasks/LJ-1-342/` only.** Four files: this report, the two
  `.proposed.lagda.md` copies, and `lj-1.342-landing.diff`. **Nothing in `src/`,
  nothing in `dev/`, no `AGENTS.md`, no `.claude/`, no other task directory.**
  The two tree copies and the sanity-lint copy sit in the session scratchpad,
  outside the repository.
- **I LANDED NOTHING.** `git status --short` shows only untracked files under
  `agents/tasks/`.
- **No commit, no push, no `make check`.** No `git checkout`, `stash`, `reset`
  or `clean`.
- **Every agda run: ONE process, `GHCRTS="-A64m -I0 -M8g"`, cap NEVER raised.**
  The slot count ran before every invocation with the brief's exact command and
  **never returned 2**.
- **I did not take the refused import edge.** Section 9.
- **I did not retire `meet-suc`.** Section 2.
- **I did not edit `agents/tasks/LJ-1-340/`.** I READ its four probes and re-read
  two of them into this proposal.
- `.venv/bin/python scripts/dispatch/rules.py --for rewrite`: run, every
  statement read. I opened the full `dev/LESSONS.md` entries for C-12, C-22 and
  P-l.
- **MEASURED: no em dash in this file, and none in either proposed chapter**
  (`lint-prose.py`, exit 0).
