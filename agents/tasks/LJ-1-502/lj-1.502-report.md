# `[LJ-1.502]` report: the consumer's formula survives `t0 := N0`

## 1. THE VERDICT

**GO.** `agents/tasks/LJ-1-502/Probe502.agda` typechecks at exit 0, median
**3.07 s** and peak RSS **705,724,416** bytes on three forced rechecks of the
full file. The obligation
`agents/tasks/LJ-1-502/Probe502.agda::twelveB-at-identified` is at `:164-169`.

**`SatGraphB.twelveB` elaborates at `t0 := N0` and `t1 := N1`, and the
downstream row lemmas still apply in BOTH directions.** Nothing landed in
`src/`. No `TFacts` value was built, and the `envK-*` family and the code
readers were not touched.

**THE IDENTIFICATION COSTS THE CONSUMER NOTHING.** It removes two proof
obligations rather than adding one, because two record fields become one
statement.

## 2. WHAT THE IDENTIFICATION COSTS

One row per affected row of `twelveB`. The role column says what `t0` and
`t1` do INSIDE the row, and the last column says whether the row survives.

| Row | Call site | Role of `t0` | Role of `t1` | Slot shared with `N`? | Survives |
|---|---|---|---|---|---|
| `memBndAt` | `src/L/Condensation.lagda.md:2241` | comparison operand, the constant-term tag, at `:516` | comparison operand, the variable-term tag, at `:513` | **YES.** `N := N0` and `t0 := N0` | **YES** |
| `eqBndAt` | `src/L/Condensation.lagda.md:2244` | same, through `bodyE` at `:1353` | same, through `bodyE` at `:1353` | **YES.** `N := N1` and `t1 := N1` | **YES** |
| `allInBndAt` | `src/L/Condensation.lagda.md:2255` | same, through `bndBodyAll` at `:1055` | same, through `bndBodyAll` at `:1056` | NO. `N := N10` | **YES** |
| `exInBndAt` | `src/L/Condensation.lagda.md:2258` | same, through `bndBodyEx` at `:1073` | same, through `bndBodyEx` at `:1074` | NO. `N := N11` | **YES** |

**THE POSITION WHERE A COLLISION WOULD SHOW, NAMED BEFORE THE ELABORATION
(D-10).** In all four rows `t0` and `t1` reach `tmValB` (`:510-517`) and
occur there ONLY as the right operand of a `≐`: `t1` at `:513`, `t0` at
`:516`. In all four rows `N` reaches `arTagPairB` (`:464-473`) and occurs
there ONLY as the right operand of a `≐`, at `:469`. **So the shared position
is the same kind of position: a tag compared for equality.** Two rows put `N`
and one of `t0`, `t1` on ONE slot:

- `memBndAt` (`:1338` takes `arTagPairB N K`, `:1335` takes `atomBodyB t0 t1 K`).
  With `N := N0 = t0`, the slot must satisfy `tagEq0` and `t0eq` at once.
  Both ask for `numeralL 0` (`src/L/Condensation/TwelveAgree.lagda.md:133`
  and `:181`). **The two demands are the same statement.**
- `eqBndAt` (`:1356` and `:1353`). With `N := N1 = t1`, the slot must satisfy
  `tagEq1` and `t1eq` at once. Both ask for `numeralL 1`
  (`TwelveAgree.lagda.md:134` and `:182`). **The same again.**

**WHY THE TAGS LINE UP, AND WHY THIS IS NOT LUCK.** `t0` IS the tag-0 index
and `t1` IS the tag-1 index of `tmValB`; `N0` IS the tag-0 index and `N1` IS
the tag-1 index of the twelve-row table. The two families count the same
numerals, so the forced identification puts equal demands on the shared slots.
It is proved at `KValue`'s own frame by `slot0-serves-both` (`Probe502.agda:217-221`)
and `slot1-serves-both` (`:224-228`): one `refl` stands in both field positions.

**THE THIRTY-FIELD ACCOUNT OF `[LJ-1.495]` AND `[LJ-1.501]` STANDS AT THIS
FRAME.** The fourteen-slot `Kenv` is sound for the record's consumer, so the
frame that `[LJ-1.499]` and `[LJ-1.500]` are building on while this task ran
is the right frame, and neither has to be re-read.

## 3. WHAT WAS BUILT, AND HOW EACH TERM IS DECISIVE

**W3 FIRST AND ALONE** (`Probe502.agda:103-112`). `memBndAt-at-identified`
takes the row lemma `MemAgree` (`src/L/Condensation.lagda.md:4412`) at the
IDENTIFIED indices, and SPLICES its conclusion into the first conjunct
position of the consumer's real `SatGraphB.twelveB`. The call at `:93-102` is
`src/L/Condensation/LowerAgree.lagda.md:255-260` with `t0` replaced by `N0`
and `t1` by `N1`, and nothing else changed.

**THE NEGATIVE CONTROL, BECAUSE A TEST THAT PASSES VACUOUSLY PROVES NOTHING.**
Two controls were run against a copy and then reverted, and the working tree
holds neither. Control A gave the row lemma `t1 := N2` and left the consumer at
`N1`: exit 42, `UnequalTerms N1 != N2`, at the `t1eq` argument. Control B left
the row lemma correct and moved ONLY the consumer's `t1` to `N2`: exit 42,
`UnequalTerms N1 != N2` **at `M.out hc`, the splice itself**. **So the splice
is the collision detector the brief asked for, and its green result is
substantive.**

**THE Δ₀ CERTIFICATE** (`Probe502.agda:126-131`). The brief calls it the
cheapest witness that the shape is unhurt. It is green. **It is also the
weakest of the three terms and the report must say so**: `twelveB` and
`Δ₀-twelveB` (`src/L/Condensation.lagda.md:2239`, `:2262`) are TOTAL functions
of their sixteen `Fin (5 + n)` arguments, so no assignment of those arguments
can make either fail. **A formula that elaborates was never going to be the
deliverable here, and the Δ₀ term measures the shape, not the identification.**

**THE OBLIGATION** (`Probe502.agda:164-169`, with `:173-178` for the other
direction). `twelveB-at-identified` is `AbstractFrame.twelve-out`
(`src/L/Condensation/TwelveAgree.lagda.md:527-531`) at `t0 := N0`, `t1 := N1`.
`AbstractFrame` (`:337`) is the tree's own composer: it drives `LowerAgree`
(`src/L/Condensation/LowerAgree.lagda.md:226`) and `UpperAgree`, which apply
`MemAgree`, `EqAgree`, `AllInAgree` and `ExInAgree`, that is ALL FOUR affected
rows, and it concludes at `SatGraphB.twelveB`. **One instantiation therefore
puts the identification through every downstream row lemma at once**, and
`twelveB-at-identified-back` (`:173-178`) does the same for `twelve-back`
(`TwelveAgree.lagda.md:533-537`). A one-way survival would not have settled
the question.

**WHAT IS A HYPOTHESIS AND NOT A BUILD.** `LFacts` (`Probe502.agda:79`) and
`TFacts` (`:155`) are taken as module parameters at the identified indices.
**Instantiating the RECORD TYPE at `t0 := N0` is where an unsatisfiable
telescope would appear**, which is the failure `[LJ-1.71]` measured on this
same module: "The telescope's tagEq is uninhabited at EVERY frame,
machine-checked. The module is vacuous."
(`archive/dev/LJ-dispatch-index.md:135`). That failure does not recur here,
and section 2 gives the arithmetic for why.

## 4. THE MEASUREMENTS

Wide caliber, `GHCRTS="-A64m -I0 -M8g"`, set on the pane by the program and
untouched. ONE Agda process per run. Every run below deleted
`_build/2.8.0/agda/agents/tasks/LJ-1-502/Probe502.agdai` first, so each is a
forced recheck of this file against cached dependencies.

**W3 ALONE, the file at 104 lines with the other eleven rows omitted.**
Median **2.75 s**, peak RSS **664,764,416** bytes.

| Run | Wall (s) | Peak RSS (bytes) |
|---|---:|---:|
| `runs/w3-r0.time` | 2.75 | 664764416 |
| `runs/w3-r1.time` | 2.75 | 664748032 |
| `runs/w3-r2.time` | 2.84 | 664780800 |

**THE FULL FILE, 231 lines.** Median **3.07 s**, peak RSS **705,724,416** bytes.

| Run | Wall (s) | Peak RSS (bytes) |
|---|---:|---:|
| `runs/final-0.time` | 3.14 | 705724416 |
| `runs/final-1.time` | 3.07 | 705708032 |
| `runs/final-2.time` | 3.04 | 705724416 |

**I FUNDED THESE AGAINST NOTHING.** The brief warned against funding W3
against `[LJ-1.501]`'s 2.37 s. That figure is `[LJ-1.501]`'s FULL-FILE median
(`agents/tasks/LJ-1-501/lj-1.501-report.md:6`); its W3 median was 2.32 s
(`:113`). Neither was used. Both my numbers are above both of `[LJ-1.501]`'s,
and **the difference is not evidence about the identification**: this file
imports `L.Condensation.TwelveAgree` and `L.Condensation.LowerAgree` on top of
`L.Condensation`, and the import is most of what the clock measures.

**THE OTHER RUN FILES ARE KEPT AND ARE NOT THE HEADLINE.** `runs/w3-0.*` is
the first W3 attempt, exit 42, `NoParseForApplication` from a missing `_∈_`
import; it is a scope error and not a mathematical result. `runs/w3-1.*` is
the same file green before the timing series. `runs/full-0.*` to
`runs/full-r2.*` are the full file before the import tidy at `:32-33`;
`runs/full-final.*` is the first run after it. `runs/final-3.*` (3.02 s,
705,708,032 bytes) confirms the file green after one COMMENT was corrected at
`:90`; it changes no term and it is not part of the timing series above.
**No heap wall occurred at any point.**

## 5. THE GATES I RAN

`check-probes`, `lint-agda`, `lint-prose`, `weave-i18n`, `ledger` and
`check-spec-surface` all pass on this tree. `check-probes` reports "clean
(5037 tracked files, no probe outside `agents/tasks/` and no generated file)".

**I DID NOT COMPLETE `check-ratio`.** It ran past five minutes and I stopped
it. **The ratio bar cannot fire on this scope**: the write scope is one raw
`.agda` probe, one report and the run files, and none carries an ` ```agda `
fence, so the divisor is 0 in-fence lines. `check-spec-surface` confirms the
in-fence total is unchanged at 499 lines. **`make check` is the gate before a
commit and the program commits, not me.**

The one file this task added under `_build/` is
`_build/2.8.0/agda/agents/tasks/LJ-1-502/Probe502.agdai`. Its lifecycle is
already declared: `dev/build-manifest.toml:117-120` gives `2.8.0/**` the class
`toolchain`. No manifest entry was added.

## 6. W2

The obligation is written ONCE at a generic carrier and instantiated.

`module W3` (`Probe502.agda:76-81`), `Δ₀-twelveB-at-identified` (`:126-131`)
and `module Twelve` (`:150-159`) are all generic in `n`, in the twelve `N`
indices, in `K`, in `w` and in the environment. **None of them names a
carrier, a bound or a frame.** Only `module AtKValue` (`:208-228`) names
`KValue`, and it holds two `refl`s and nothing else. A second frame with the
same fourteen-slot shape reuses everything above `:208` unchanged.

## 7. WHAT THE NEXT BRIEF NEEDS

**WHAT COST NOTHING.** The identification. It is free at the syntax and free
at the record: two fields become one statement, so a frame at fourteen slots
pays LESS than a frame with sixteen would.

**WHAT I DID NOT MEASURE, AND IT IS THE NEXT QUESTION ON THIS FRONT.** I
proved that `TFacts` at the identified indices is CONSISTENT at the two shared
slots. **I did not build the value, so I did not measure that the remaining
`TFacts` fields are all reachable at `KValue`'s frame.** `[LJ-1.499]` and
`[LJ-1.500]` hold the `envK-*` family and the code readers, and twenty nine of
the fifty nine fields are still unaccounted after the thirty this task
confirms. **The frame is sound; the field count is not yet closed.**

**I VERIFIED THE FIFTY-NINE RATHER THAN QUOTING IT.** `record TFacts`
(`src/L/Condensation/TwelveAgree.lagda.md:129`) declares 59 fields between
`:133` and `:332`, counted from the file. The brief's figure is right. **Four
of those 59 are the fields `[LJ-1.501]` paid** (`t0eq` at `:181`, `t1eq` at
`:182`, `t0K` at `:183-184`, `num1K` at `:185`), **and two of the four are the
ones this task showed collapse into `tagEq0` and `tagEq1` under the
identification.** So the honest reading of the thirty is that at this frame it
is thirty POSITIONS filled by twenty eight distinct proofs.

**ONE SHAPE I MET AND DID NOT SWEEP (C-42).** `Kenv`'s fourteen slots force
`t0 := N0` because no slot is spare. **I did not count how many OTHER frames
in the tree instantiate `SatGraphB` or `TFacts` with a fixed slot list**, and
a frame with a different list could point `t0` at a slot that does not hold
`numeralL 0`. The measurement here is `KValue`'s frame and it does not extend
by analogy. The sweep is one grep for `SatGraphB.twelveB` and `TFacts` call
sites, and it is cheap, but it is a mathematical judgement about scope and it
is not mine to make.

**NOTHING WAS COMMITTED AND NOTHING WAS PUSHED.**

## ARCHIVE USED

- `archive/dev/LJ-dispatch-index.md`. **READ AND USED.** At `:135`:
  "| LJ-1.71 | Consume TwelveAgree, which nothing consumed | CONVICTS c21b417 | The telescope's tagEq is uninhabited at EVERY frame, machine-checked. The module is vacuous. The LJ-1.55 slot fix HOLDS |".
  This is the failure mode section 3 tests for, on this same module. At
  `:104`:
  "| LJ-1.55 | The agreements' slot convention | PARTIAL, half closing | Fix is every slot, not K alone. Master green, line-neutral. TwelveAgree composes. WitnessAgree blocked on oneSameB |".
  "Fix is every slot, not K alone" is why this task instantiated the whole
  composer and not one row.
- `archive/dev/JOURNAL.md`. **NOT READ.** Declined: the two facts I needed
  from the campaign history were in the dispatch index in table form, and a
  journal sweep would have cost more than the whole probe.
- `archive/dev/JOURNAL-archived.md`. **NOT READ.** Declined for the same
  reason, and it is the older of the two journals.
- `archive/dev/DD-archived.md`. **OPENED, NOT USED.** It is the archived `DD`
  ruling series (`:1`), and this task turns on slot arithmetic, not on a
  ruling.
- `archive/dev/DECISIONS-archived.md`. **OPENED, NOT USED.** It is the `D`
  series, archived 2026-08-09 (`:3`), and nothing in it is live.

## LITERATURE USED

- `dev/literature/level-formula-slot-roles.md`. **READ AND USED as context,
  and it did not decide anything.** At `:11`:
  "digest is the outside view beside that measurement." The file is the
  outside view on which slots a level-hood formula binds and which stay free.
  **It does not cover the question this task asked**, which is whether one
  free slot may carry two syntactic roles; its table (`:23-31`) records arity
  and role but no source reuses a slot. **So the literature has no opinion
  here and the answer came from the tree.**
- `dev/literature/devlin-II5.md`. **NOT READ.** Declined: it carries Devlin's
  Condensation chain and its complexity requirements, and this task measured
  an Agda telescope, not a mathematical claim.
- `dev/literature/digest.md`. **NOT READ.** Declined: it pins the orthodox rud
  route, which this task does not touch.
- `dev/literature/truncation-and-selection.md`. **NOT READ.** Declined: it is
  about picking a witness, and no witness is picked here.
- `dev/literature/terms-2026-08.md`. **NOT READ.** Declined: it is a
  terminology dossier and this task names no new term.
