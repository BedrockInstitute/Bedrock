# LJ-1.223 report: the ten remaining suppliers, split thin from thick

tier: pi (deepseek-subagent-mode), model `deepseek-v4-pro`. Written
incrementally (C-22). No master edited. No brief edited. No other report
edited. No commit, no push. **NO AGDA RAN.** Every negative is MEASURED or
INFERRED, in those words.

## 0. THE TWO NUMBERS

**Two of the ten are THIN. The chain's total port price is 2,670 written
lines.** That number is the sum of the delivered non-blank Agda lines of the
eight THICK suppliers. The two THIN suppliers need no dispatch. MEASURED for
the line counts; INFERRED for the split, from reading each definition.

A correction to the brief's list. The brief says ten remain and names `Graph`
among them. `L.Coding.Graph` is already ported. `agents/tasks/LJ-1-210/GenGraph.agda`
is the class-generic Graph, and `lj-1.210-report.md:90` records exit 0. So of
the ten names, `Graph` needs no dispatch for a second reason: it is already
done. The true remaining count is NINE, and of those nine, ONE (`Recover`) is
thin and EIGHT are thick. MEASURED.

## 1. THE TABLE

One row per supplier. Line counts use the ledger caliber: non-blank lines
inside ` ```agda ` fences. My counts match the `[LJ-1.210]` census at
`lj-1.210-report.md:248-270` for every module.

| name | home | delivered lines | verdict | generic supplier that covers it |
|---|---:|---|---|---|
| `Recover` | `src/L/Coding/Recover.lagda.md:112-116` | 190 (2 relevant) | **THIN** | `GenModel.agda:16-17,193-199,215` |
| `CodeSet` | `src/L/Coding/CodeSet.lagda.md:135-148,240-241,263-310` | 168 | **THICK** | none |
| `Graph` | `src/L/Coding/Graph.lagda.md:94-95,191-218` | 111 | **THIN** | `GenModel.agda` clause names; `GenGraph.agda` already green |
| `Table` | `src/L/Coding/Table.lagda.md:82-83,103-107,244-266` | 246 | **THICK** | none |
| `Slot` | `src/L/Coding/Slot.lagda.md:262-263` | 187 | **THICK** | none |
| `Sat` | `src/L/Coding/Sat.lagda.md:142-143` | 179 | **THICK** | none |
| `Sound` | `src/L/Coding/Sound.lagda.md:1099-1106` | 850 | **THICK** | none |
| `Unique` | `src/L/Coding/Unique.lagda.md:104,884-893` | 630 | **THICK** | none |
| `Bridge` | `src/L/Coding/Bridge.lagda.md:124-125,519-531,621-624` | 294 | **THICK** | none |
| `Uniform` | `src/L/Coding/Uniform.lagda.md:180-182` | 116 | **THICK** | none |

THICK sum: 168 + 246 + 187 + 179 + 850 + 630 + 294 + 116 = **2,670**.
THIN sum: 190 + 111 = **301**. All ten: **2,971**.

### 1.1 The two THIN suppliers, in the template of `[LJ-1.221]`

`Recover` supplies `keyOf` and `keyOf-fst`, two one-liners at
`src/L/Coding/Recover.lagda.md:112-116`. Both bodies use `prʟ`, `prʟ-fst`,
`numeralL`, `numeralL-fst`. All four sit generically in `GenModel.agda` at
`:16-17` and `:193-199`. `GenModel.agda:215` (`tagBridge`) is the body of
`keyOf-fst` character for character. The repair is two names in a `using`
list. MEASURED.

`Graph` supplies `satGraphAt`, `GraphWitAt`, `graphAt-in`, `graphAt-out`.
Every one is built from the Model clause names `closedAt`, `domAt`, `appAt`,
`appAt-adequate` and the twelve clause names. `GenModel.agda` exports all of
them. `GenGraph.agda` already applies `GenModel` and takes the same names.
MEASURED.

### 1.2 The eight THICK suppliers, and what each carries

`CodeSet`. `keyArityAtL` and its two readers (`:135-148`) are thin, built from
`tagAtL` and `tagAtL-adequate`, both in `GenModel`. The other five consumer
names are not. `hasWitnessAt` (`:240-241`) names `shapedAt` from
`L.Coding.Shape`, which is not generic. `codeS` and `keyS` (`:263-270`) use
`codeL` and `keyL` from `L.Coding.InL`. `witnessAt-in` and `witnessAt-out`
(`:280-310`) call `clo`, `closureClosed`, `closureShaped`, `key∈closure` and
`Decode.recover`. None of those is in `GenModel`. THICK. MEASURED by reading
the imports at `:126-140`.

`Table`. `keyʟ` (`:82-83`) is thin, built from `prʟ`, `numeralL` and `LCode`.
`slot`, `satTable`, `total`, `inSlot`, `entry-in` are not. They build the
finite table from `sglʟ` and `cupʟ` of `L.Coding.InL`, and from `Sat` of
`L.Coding.Sat`. THICK. MEASURED at `:76-80` and `:103-107`.

`Slot`. `slotClosed` (`:262-263`) proves the slot is closed, eight clauses. It
uses `keyʟ`, `keyʟ-shape`, `slot`, `slot-inv`, `module Parts` from `Table`,
and the closure machinery from `Model`. THICK. MEASURED at `:70-76`.

`Sat`. `Sat` (`:142-143`) is the meta-level satisfaction function, twelve
clauses, one separation per constructor. It uses `envSet` from
`L.Coding.EnvSet` and `hasSeparationL` from `L.Axioms.Full`. THICK. MEASURED
at `:70-82` and `:142-177`.

`Sound`. `soundness` (`:1099-1106`) is the twelve-clause existence half. Its
module is 850 delivered lines. It uses `Sat`, `EnvSet`, and `Table`. THICK.
MEASURED.

`Unique`. `module Good` (`:104`) and `Good.pinned` (`:884-893`) are the
twelve-clause uniqueness half, 630 delivered lines. They use `Sound`,
`Sat`, and `Table`. THICK. MEASURED.

`Bridge`. `asConst` (`:124-125`) is two lines. `defSet-Sat` (`:621-624`) is a
four-rewrite theorem, but it rests on `Sat-spec` (`:519-531`), the
twelve-clause adequacy proof that fills the middle of this 294-line module.
THICK. MEASURED.

`Uniform`. `keyBridge` (`:180-182`) is a five-line proof. It cannot be
supplied alone. It needs `keyS` from `CodeSet`, `keyʟ` from `Table`, and
`asConst` from `Bridge`. THICK, because its dependencies are thick. MEASURED
at `:172-186`.

## 2. THE THREE DD4 NUMBERS FOR THE CHAIN

The ten suppliers are tower-neutral. None of them names `isL` or `isJ`. They
speak only of the carrier `S`, the numerals, the pairs, and the successor.
`GenModel.agda` already takes all of those as parameters. So the whole coding
chain ports as shared code.

| DD4 number | figure | basis |
|---|---:|---|
| SHARED | **2,971 lines** | the ten suppliers' delivered body, all tower-neutral |
| PLUMBING | **about 200 lines** | the telescope and module application, written once |
| PER-TOWER RESIDUAL | **0 lines** in the ten | no tower-specific content sits in the coding chain |

The shared figure is MEASURED for the line counts. The zero residual is
INFERRED: no second tower was built. The plumbing figure is INFERRED from
`[LJ-1.210]`, which measured 42 lines at Model and 23 at Graph, and
`[LJ-1.213]`, which measured 12 at Powerset.

**The shared half still dominates when the plumbing is paid ten more times.**
Ten modules at about 20 plumbing lines is about 200 lines. That is 200 against
2,971 shared, a ratio of about 1 to 15. Even paying the plumbing once more for
a second tower does not approach the shared body. MEASURED for the shared
count; INFERRED for the plumbing.

The real per-tower content is not in these ten. `[LJ-1.213]` found the
residual at the body: `DefAt-stage`, 8 lines, which spends `LsetS` and
`𝒟ₒ→isL`. The literature says the per-tower content is exactly two objects,
the level-hood certificate and the definable well-order. Both live above the
coding chain, not inside it.

## 3. THE BOUNDARY: what reading cannot judge

No supplier could not be judged by reading. Every verdict above is a reading
judgment. One thing reading cannot settle, and it is not a supplier: whether a
THICK supplier's body carries verbatim at the class. That is the width
question, which `[LJ-1.220]` measures with Agda. I did not run it and I do not
answer it. The price here is the delivered content, not the exit code.

## 4. NEGATIVES, CLASSIFIED

| negative | class |
|---|---|
| the chain is a using-list problem (all ten thin) | **MEASURED FALSE.** Eight of ten carry real content |
| the port is free (thin) | **MEASURED FALSE for eight of ten.** The thick content is 2,670 lines |
| the brief's list of ten is exact | **MEASURED FALSE.** `Graph` is already ported at `GenGraph.agda` |
| `Environment` needs porting | **MEASURED FALSE.** `env` has type `(Fin n → V ℓ) → V ℓ` at `Environment.lagda.md:84-85`. It names no structure |
| `Recover` is a brick | **MEASURED FALSE.** Two one-line names, all four ingredients generic |
| `Graph` is a brick | **MEASURED FALSE.** All names from `GenModel` clause names; `GenGraph.agda` is green |
| the thick suppliers are the two per-tower objects | **MEASURED FALSE.** They are tower-neutral substrate, not level-hood or well-order |
| the port costs more than the fixed chain is worth | **MEASURED FALSE.** 2,670 thick lines sit inside a 5,822-line fixed chain, and all of them are shared |

## 5. ARCHIVE USED (DD18)

- `agents/tasks/LJ-1-221/lj-1.221-report.md`, read WHOLE, FIRST. TOOK the
  template of section 4, the corrected count of section 5.4, and the
  thin-thick split of section 6.4.
- `agents/tasks/LJ-1-219/JoinAtAmbient.agda:24-39`. TOOK the twelve import
  lists and the exact names of each supplier.
- `agents/tasks/LJ-1-219/lj-1.219-report.md`. TOOK the supplier list and the
  `Recover` leak.
- `agents/tasks/LJ-1-213/lj-1.213-report.md`, read WHOLE. TOOK the 389 / 12 /
  8 split, the 17-module and 5,822-line figures, and `DefAt-stage`.
- `agents/tasks/LJ-1-210/lj-1.210-report.md`, read at `:240-290`, `:325-397`.
  TOOK the 17-module census, the 5,822 total, the 125-line class surface, and
  the measured ports of Model (42 lines) and Graph (23 lines).
- `agents/tasks/LJ-1-210/GenModel.agda`, read WHOLE. TOOK the supply list:
  `prʟ` `:193-194`, `prʟ-fst` `:196-199`, `numeralL` `:16`, `numeralL-fst`
  `:17`, `tagBridge` `:215`, and the clause names.
- `agents/tasks/LJ-1-210/GenGraph.agda`, read WHOLE. **The finding that Graph
  is already ported.**
- The ten suppliers under `src/L/Coding/`, read at their consumer names.
  TOOK every definition priced in section 1.
- `archive/src/2026-08-09-rud-route/L/Rud/ClassJ.lagda.md:57,95,118-119`.
  **TOOK the warning.** `isJ`, `isJ-trans`, `𝒮ⱼ` are declared. The only
  importer, `L/Rud/Bridge.lagda.md:58`, takes `isJ` and `Jset→isJ` and never
  `𝒮ⱼ` or `isJ-trans`. The second class was built and never instantiated.
- `archive/dev/TASKS-archived.md:161,243,257,273`. Read for shape. The retired
  route's StepStory was carrier-generic and grew by about 26 lines at its
  second site. **FIGURE NOT TAKEN.** That axis is the carrier, not the class,
  and P-l forbids carrying the number.

## 6. LITERATURE USED (DD18)

- `dev/literature/devlin-II5.md:370-383`. **USED.** The table has twelve rows:
  eight EITHER and four PER-TOWER. The word "nine" does not occur in the file.
- `dev/literature/devlin-II5.md:387-389`. **USED, and no brief before this
  chain used it.** "The per-tower content is exactly two objects: the
  level-hood certificate (Step C) and the definable well-order (Steps D, G)."
- **The thick list does not match those two objects.** The eight thick
  suppliers are the satisfaction-internalization chain. They are tower-neutral
  machinery. The two per-tower objects sit above them, outside the ten.
  MEASURED that the ten never name `isL` or `isJ`; INFERRED that the two
  objects are separate.
- `dev/literature/devlin-II5.md:301-303`. **USED.** "The proof does not pin
  the presentation." This is why the coding chain is tower-neutral.
