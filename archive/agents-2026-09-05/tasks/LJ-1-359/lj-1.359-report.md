# LJ-1.359 report: land the CSB corollary at the trophy's own `InjL`

Written incrementally from the first five minutes (C-22). Every Agda run
used one process under `GHCRTS="-A64m -I0 -M8g"`. The cap was never raised.
The slot count was read before every invocation with the brief's exact
command. It read 0 every time (C-12). The floor was measured beside every
seconds figure (C-53 as extended).

## VERDICT

**IT LANDS GREEN.** The master holds **17 code lines of content, 19 with
comments, against the probe's 21** (the brief's "about 15" was a figure for
a smaller block than the probe's own content). The whole master is **34
non-blank code-fence lines**. First check was green: **1.74 s**. Four more
checks ran at 1.62 s, 2.25 s, 2.29 s and 2.32 s. The floor was **0.72 s** (one
reading read 0.05 s, straight after the library index warmed; the 0.72 s
reading is the honest one). The master sits about **0.9 to 1.6 s past the
floor**. The one edit between first green and final was forced by
`lint-agda`, not by mathematics.

## 0. Findings against the brief's premises, measured before writing

- **"`Small` gets its first consumer outside its own master here" is
  FALSE, MEASURED.** `src/L/Absorption.lagda.md:504` holds
  `module Sm = Small G D C sv dm ij ran`, and consumes `Sm.small` and
  `Sm.small-inj` at `src/L/Absorption.lagda.md:508-511`. It entered at
  commit `9d7288c` (`[LJ-1.284]`), which precedes `c370161` (`[LJ-1.355]`).
  My master is the first consumer at the GCH end, and the second outside
  the coding master.
- **"`src/L/Coding/Injection.lagda.md:103`" is stale, MEASURED.** The
  `Small` module starts at `:123`; `small` sits at `:144` and `small-inj`
  at `:147`. Line 103 falls inside `Extract`. The four `InjCode` conjuncts
  that the readback consumes sit at `src/L/Cardinal.lagda.md:223-228`, as
  cited.
- **"`InjL` at `src/L/GCH.lagda.md:38`" re-derived, MEASURED.** The type
  is at `:37` and the defining equation at `:38`. Correct as cited.
- **"about 15 code lines" was LOW for the probe itself, MEASURED.** The
  probe's own content block, `setPL` through `csb-corollary`, counts 21
  non-blank lines, not 15. The master's 17 code lines sit BELOW the probe
  figure: the probe paid its own comment lines, and the master renamed
  nothing onto more lines. The brief's fear of "+2 over the probe" did not
  materialise for the content; the header, OPTIONS line, imports and
  bilingual prose cost 15 more lines, as predicted.

## 1. The site and its verification

**The master is `src/L/CantorBernstein.lagda.md`, module
`L.CantorBernstein`.**

The cycle claim was re-derived and CONFIRMED. `src/L/GCH.lagda.md:16`
imports `L.Cardinal`. A grep for `GCH` over `src/L/Cardinal.lagda.md` and
`src/L/Cardinal/` returns nothing. So `Cardinal` cannot host the corollary:
it would need `InjL` from `GCH`, and `GCH` already imports `Cardinal`. The
ruling stands on measured structure.

`GCH.lagda.md` stays a pure statement. `[LJ-1.323]` restated the trophy so
that it carries no proof obligation. A corollary inside the same file would
put mathematics back into the statement chapter. The ruling stands.

**Why this name.** The substrate chapter is `V.CantorBernstein`. It holds
the theorem and calls every use of it a "reading". This master IS the
reading at the L end, so the mirror name says where Cantor-Schroeder-
Bernstein meets the L tower. The retired route kept its L-side CSB in its
own `L/Cardinal.lagda.md` (`module CSB` and `csb`,
`archive/src/2026-08-09-rud-route/L/Cardinal.lagda.md:89`), so an L chapter
that carries the L end of CSB has a precedent in shape.

**A third site exists and loses.** `src/L/InjChain.lagda.md` imports no
cardinal chapter, and `Cardinal` does not import `InjChain`, so its tail
could host the corollary without a cycle. It loses on weight: the corollary
would drag the whole `GCH` cone into every `InjChain` consumer, and
`L.Absorption.lagda.md` imports `InjChain` today. `InjChain` also has its
own subject. The new master adds weight to no other chapter.

## 2. The master

Four blocks: bilingual intro, imports, wiring, corollary. The imports trim
the probe's list to what the body uses: `Base.Prelude`,
`Base.Classical`, `FOL.ZFStructure`, `V.CantorBernstein`, `L.Constructible`,
`L.Cardinal`, `L.Coding.Injection`, `L.GCH`, `⟪_⟫` and `∥_∥₁`. The probe
also imported `𝒮ᵥ`, `Base.Truth`, `V`, `setIsSet`, `⟪_⟫↪`, `isEmb⟪_⟫↪`,
`Embedding-into-isSet→isSet`, `∣_∣₁` and `squash₁`; the master omits them,
because `lint-agda` checks import necessity.

Checks, all green, with exit codes read: `lint-prose.py --check` 0,
`lint-agda.py --check` 0, `weave-i18n.py --check` 0. `make check` was not
run; the orchestrator runs it.

## 3. What did NOT transfer from the probe

- **The export name.** The probe's `csb-corollary` cannot land: `csb` is an
  unregistered abbreviation, and `[LJ-1.355]` retired that very name for
  style. The export is `mutual-inj→bijection`. The helpers `setPL` and
  `readL` transferred verbatim; `readL` matches the `prAtL` precedent in
  `L.Coding.Model`, and `setPL` mirrors `MutualInj`'s own `setP` parameter
  (`src/V/CantorBernstein.lagda.md:235`).
- **The bare open.** The probe opened `V.CantorBernstein` bare. The master
  paid one lint violation for that, `[bare-open]` at its line 38, and the
  fix added `using ( small-set; module MutualInj )`. This was the one edit
  between first green and final. MEASURED.
- **The free imports.** See section 2. A probe imports freely; a master
  pays for necessity.
- **The mathematics transferred whole.** Every proof line of the probe
  re-derived and landed unchanged. Nothing new was proved, and nothing
  failed to transfer. The task stayed assembly, as the brief priced it.

## 4. The negative control

`agents/tasks/LJ-1-359/Neg.agda` holds the master's content verbatim, with
ONE corruption: `readL` passes `dm` where `sv` is expected, so the second
and third components of the `InjCode` tuple reach the `Small` readback
swapped. Agda refused: **exit 42**, `[UnequalTerms]`, at
`Neg.agda:35.27-29`. The error names both satisfaction types: the given
type is the `domAt` satisfaction shape, and the expected type is
`⟨ (F ∷ a ∷ []) ⊨ L.Coding.Model.svAt zero ⟩`. The full error is saved at
`agents/tasks/LJ-1-359/neg-error.txt`. The green run is real: the wiring
consumes the four conjuncts in their given order, and the machine checked
that order.

## 5. Consumers, and the closure for both ends

**Consumers in `src/` today: ZERO.** The master is new, and nothing imports
it. MEASURED: a grep for `L.CantorBernstein` over `src/` returns the master
alone. Three consumers are pending, all outside this task's write scope,
all named BEFORE any edit:

1. `src/Everything.lagda.md`: the import and the catalog rows. I never
   touch it. The orchestrator wires it.
2. `src/README.md`: the module-list entry and the symbol rows
   (`mutual-inj→bijection`, `setPL`, `readL`).
3. The GCH proof chapter, future: the consumer that reads the corollary.

**Closure, measured today** (`ledger.py --reuse`): AC closure 73 masters
17,186 lines, GCH closure 48 masters 8,878 lines, SHARED 43 masters 7,585
lines, 41.0 percent of the 18,479-line union. The closure roots are import
closures: `ac_root = src/L/Model.lagda.md` and `gch_root =
src/L/GCH.lagda.md` (`dev/ledger.toml:170` and `:218`). My master IMPORTS
the GCH root, so it enters no closure today, and `Everything` is an
uncounted index. **The wiring into `Everything` alone changes no closure
figure.** The master enters the GCH closure on the day consumer 3 imports
it, and it takes `V.CantorBernstein` with it, as the first thing to pull
that chapter in. Projection: GCH closure 50 masters, 8,878 + 34 + 118 =
9,030 lines; SHARED unchanged. Read beside `dev/ledger.toml:200-206`: the
GCH closure is statement-rooted and understates by about 1,027 lines, and
these 152 lines are part of the same understatement until the proof
chapter lands.

## 6. DD4

**Axis (C-46), fixed at `scripts/measure/ledger.py:50`: what the AC and GCH
closures share.** The honest split: **the generic half is ALL of the
mathematics, and none of it is mine.** `V.CantorBernstein` (118 lines,
`[LJ-1.355]`) states the construction at two abstract types and the
corollary at an abstract carrier, relation and readback. Its import list
is `Base.Prelude`, `Base.Classical` and cubical only, so the AC tower can
read it for free. **My 34 lines are L-only by necessity**: they name
`InjL`, `InjCode` and `𝒮ʟ`, and a line that names `InjL` cannot serve the
AC end. The adapter SHAPE, one set-ness lemma, one readback, one module
application, is the template an AC-side instantiation would rebuild at its
own carrier. Could the L half be written at a shape the AC end also reads?
No: that shape already exists, and it is `MutualInj`. This task SPENDS the
rare win: the GCH tower reads 152 lines of shared substrate through a
34-line L-only adapter, and the AC end may do the same later at its own
types.

## Term renderings (DD19)

No new rendering was chosen, so no pipeline ran. The zh prose reuses only
terms already delivered in `src/`: 双射, 单射, 满射, 截断, 读回, 推论, 装配
and 地基 all appear in `src/V/CantorBernstein.lagda.md`, and 可构造集 in
`src/L/Constructible.lagda.md`. No stop was needed.

## ARCHIVE USED

One line read per archived file, code cited (C-44):

- `archive/src/2026-08-09-rud-route/L/Cardinal.lagda.md:89-190`, read
  whole: the retired `module CSB` and `csb`. **The consumer end: the
  retired route's `csb` had ZERO consumers.** MEASURED: a grep over the
  archived tree returns nothing outside the chapter. The bijection-as-pairs
  upgrade `csb-eq` was consumed once, by the hull chapter, at
  `archive/src/2026-08-09-rud-route/rud-route-src.patch:2396`. So the
  closest comparable used CSB only through a packaging this live route
  declined to port (`[LJ-1.355]` section 3), inside a chapter the route
  retired.
- `archive/src/2026-08-09-rud-route/L/CardinalPredicates.lagda.md:10`: the
  W7 ruling, equinumerosity as a bijection, taken to avoid a per-consumer
  CSB obligation. **Does the worry materialise here? In one line: yes in
  shape, no in price.** The live statement (`[LJ-1.323]`) chose mutual
  injections, so every reader of the equality owes a CSB step; that
  obligation is now discharged ONCE at the substrate and read here at 17
  lines, so no consumer re-derives it. The retired route defined the worry
  away; the live route pays it once, generically.
- `archive/dev/TASKS-archived.md:116`: row `L3.32-T81`, "CSB literature
  survey, COMPLETE (keep ours)". Read. The repaired survey story was not
  repeated. WHY NOT the neighbouring rows: none bears on assembly.
- `archive/dev/JOURNAL-archived.md:1368-1380`: the trap the ruling
  avoided, "a surjection-only or raw-injection cardinality would have
  forced every later consumer to re-derive the bijection". Read; it is the
  same lesson my section 6 states from the sharing side. WHY NOT the rest
  of the entry: it prices the retired route's own rewrite, not this
  landing.

## LITERATURE USED

- `dev/literature/truncation-and-selection.md:74-85`: HoTT Book Definition
  10.2.7, `card(A) ≤ card(B) :≡ ∥ inj(A,B) ∥`. TOOK, in one line as the
  brief asks: **the corollary's surjectivity being truncated changes
  nothing a set-theorist may conclude, because the classical cardinal
  statements are themselves truncated existentials, so a truncated
  bijection is exactly the grade the classical reading states.** WHY NOT
  the rest: the file's untruncation machinery, unique choice and sections,
  prices extracting data FROM truncations, and this task never does that.
