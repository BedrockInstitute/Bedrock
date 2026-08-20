# LJ-1.414 report: is an ambient injection between two L-elements coded in L?

slot: `coder`. Written incrementally (C-22). No commit, no push. I wrote only
in `agents/tasks/LJ-1-414/`. Agda ran under the caliber the program set on
this pane, `GHCRTS="-A64m -I0 -M8g"`, ONE Agda process at a time, no heap
event.

TARGET: build ONE term `amb-to-coded` in
`agents/tasks/LJ-1-414/Probe414.agda`. The task is to measure the implication,
not to win it.

## D-10, BEFORE ANY AGDA

The injection is a function on the fibre types of two L-elements. Nothing in
its type says it is constructible
(`src/L/Cardinal.lagda.md:47-48`, `_↪_` is a Sigma of a function and an
injectivity proof; `src/L/Cardinal.lagda.md:133`, the ambient arrow at the
least cardinal is truncated).

**Answer 3. NOT DECIDABLE in this tree.**

The statement at this generality is `∥ ⟪ fst x ⟫ ↪ ⟪ fst d ⟫ ∥₁ →
∥ Σ[ F ∈ S ] InjCode F x d ∥₁`. Three facts fix the answer:

1. The literature never codes an arbitrary ambient function. Devlin II.5.2
   produces a collapse of a Σ₁ hull (`dev/literature/devlin-II5.md:72-77`).
   That map is definable. SZ 1.16 is the same shape
   (`dev/literature/j-hierarchy.md:90-92`). Truncation-and-selection records
   that a cardinal inequality is truncated existence of an injection, and that
   a data payload does not come out of `leastOf`
   (`dev/literature/truncation-and-selection.md:75`, `:148`).
2. The Def tower carves a graph only through a `Formula`. Every site in
   `src/` that carves the graph of an ambient function supplies one (C-42
   sweep, section 5). An arbitrary element of `_↪_` is not a `Formula`.
   That is wall 2 of `[LJ-1.399]`
   (`agents/tasks/LJ-1-399/lj-1.399-report.md:83-91`).
3. A refutation would need one site where an ambient injection exists and no
   `InjCode` does. This tree has no such site, and it cannot construct the
   classical counterexample. So the statement is not proved and not refuted.

The corrected target is HALF B: `code-from-graph`. If the graph exists as an
L-element and the membership readings hold, `InjCode` follows. HALF A is the
remaining bill. It is the type `HalfA` at `Probe414.agda:65-66`.

This says the internalization route cannot untruncate the ambient square law
at a non-initial ordinal: the truncated arrow at
`src/L/Cardinal.lagda.md:133` does not become a code.

## VERDICT

**NO-GO on `amb-to-coded`. GO on HALF B.**

- `code-from-graph` is GREEN (`Probe414.agda:115-128`,
  `runs/code-from-graph.out`, exit 0, 1.64 s real, caliber
  `GHCRTS="-A64m -I0 -M8g"`, one Agda process).
- `amb-to-coded` is a hole at `Probe414.agda:139`. Agda reports
  `UnsolvedInteractionMetas` (`runs/amb-to-coded-hole.out`, exit 42,
  1.58 s). The obstruction is `review-of-amb-to-coded.md`.
- HALF A is named as the type `HalfA` (`Probe414.agda:65-66`). No
  inhabitant. No axiom, no postulate, no module parameter that asserts it.

## 1. W2

`code-from-graph`, `GraphOf` and `HalfA` are generic in `x` and `d`. No
cardinal, no site and no numeral is named in those statements. `ω` appears
only in the obligation telescope, as the brief required. W2 holds.

## 2. W3, HALF B

The brief named the four conjuncts from the two membership readings. The
probe is `code-from-graph`. GREEN at `Probe414.agda:115-128`, exit 0, 1.64 s
(`runs/code-from-graph.out`).

InclGraph derives uniqueness and injectivity from `pair-out`, because both
coordinates are equal (`src/L/InjChain.lagda.md:518-530`). A general graph is
not a diagonal, so those two laws sit beside the two readings as facts about
membership in `G`. No ambient function appears in HALF B.

MEASURED SIZE, code lines:

| piece | lines | what |
|---|---|---|
| telescope | `Probe414.agda:76-84` | the four readings |
| `sv` | `:91-92` | `svAt-in` of `uniq` |
| `ij` | `:94-95` | `injAt-in` of `inj-mem` |
| `dm` | `:97-107` | `domAt-intro` from `pair-out` and `pair-in` |
| `ran` | `:109-110` | `snd` of `pair-out` |
| `coded` | `:112-113` | the four-tuple |
| packaging | `:115-128` | `code-from-graph` |

45 code lines. The brief's estimate was about 45. Comparables of
shape, not of size: InclGraph's four conjuncts at
`src/L/InjChain.lagda.md:518-547`, and `[LJ-1.409]`'s `TrimCode` at 23 code
lines for one conjunct.

Which of the four conjuncts cost anything:

| conjunct | cost |
|---|---|
| `svAt` | none. `svAt-in` of the uniqueness reading |
| `injAt` | none. `injAt-in` of the injectivity reading |
| range | none. `snd` of `pair-out` |
| `domAt` | the only cost. `PT.rec` on `pair-out` for the forward half, `pair-in` for the backward half, 11 lines |

A first attempt reconstructed uniqueness and injectivity from `GraphOf`,
which names the ambient function `f` in the readings. That shape hung:
3 min 28 s CPU, 8.5 GB RSS, still running, killed. It was not a heap
exhaustion. The process was stopped before `-M8g` fired. The thin shape
above, with no `f` in the proof, is the one that was measured green.

## 3. HALF A, named as a type

    HalfA : (x d : S) → (⟪ fst x ⟫ ↪ ⟪ fst d ⟫) → Type _
    HalfA x d f = Σ[ G ∈ S ] GraphOf x d f G

`GraphOf` (`Probe414.agda:56-63`) is the two membership readings in the
shape `InclGraph.pair-out` / `pair-in` (`src/L/InjChain.lagda.md:494-511`):
a pair in `G` is a pair of `f`, and every fibre of `x` has its pair in `G`.

This is the single line `[LJ-2.5]` needs. The campaign's remaining bill is
this type.

The two walls it inherits:

1. `[LJ-1.399]` wall 1 (`agents/tasks/LJ-1-399/lj-1.399-report.md:41-63`).
   An ambient function does not determine the members of an L-element.
2. `[LJ-1.399]` wall 2 (`agents/tasks/LJ-1-399/lj-1.399-report.md:83-91`).
   The tree has no `Formula` for an arbitrary map. `[LJ-1.400]`
   (`agents/tasks/LJ-1-400/lj-1.400-report.md:21`) measured the same door:
   it packages a graph the code does not supply.

The Def tower pays HALF A only when the map has a `Formula`. InclGraph,
Comp.K and ShiftGraph are those cases. An arbitrary element of `_↪_` is
not one of them. No chapter on the Def tower can pay the general type:
`hasSeparationL` and `hasReplacementL` both take a `Formula`
(`src/L/Axioms/Full.lagda.md:144`, `:277`).

## 4. THE OBLIGATION

`amb-to-coded` (`Probe414.agda:134-139`) is the brief's type. It is a hole.
HALF A has no producer, so the implication has no term. The hole is red by
design, as `[LJ-1.409]` left `place-code` (`Probe409.agda:190`).

No invented hypothesis. The truncated injection does not become a code.

## 5. C-42 SWEEP

COUNT of sites in `src/` that carve the graph of an ambient function as an
L-element: **6**. COUNT of those sites whose map has a `Formula`: **6**.
COUNT of those sites whose map has no `Formula`: **0**.

| # | site | Formula | has Formula |
|---|---|---|---|
| 1 | `InclGraph` (`src/L/InjChain.lagda.md:575`) | `inclFo` (`:445`) | yes |
| 2 | `Comp.K` (`src/L/InjChain.lagda.md:338`) | `compFo` (`:222`) | yes |
| 3 | `Absorption.Carve` / `ShiftGraph` (`src/L/Absorption.lagda.md:385`) | `shiftFo` (`:223`) | yes |
| 4 | `Recursion.Of.table` (`src/L/Recursion.lagda.md:179`) | `Recursion.graph` (`:106`) | yes |
| 5 | `Hierarchy.hierAt` (`src/L/Hierarchy.lagda.md:536`) | `PairGraphAt` (`:543`) | yes |
| 6 | `Choice.Table.tableAt` (`src/L/Choice/Table.lagda.md:684`) | `PairGraphAt` (`:686`) | yes |

The two sites the brief named are rows 1 and 2. The other four were not
named. All six have a `Formula`. Nothing in `src/` carves the graph of an
arbitrary ambient function.

Nearby, not counted: `Choice.Before.relAt`
(`src/L/Choice/Before.lagda.md:229`) carves a well-order, not a function
graph. `Coding.Injection.rangeGraph`
(`src/L/Coding/Injection.lagda.md:158`) carves the range of an already
coded graph. `IdGraph` lives in probes, not in `src/`.

The wall at HALF A therefore extends to every site that would take an
arbitrary element of `_↪_` and return an L-element. It does not extend to
the six sites above. Those maps have a `Formula`.

## 6. W8, LITERATURE

W8 does not abort HALF B. It stops the unconditional obligation.

The shape is a theorem with a hypothesis this tree does not meet: the map
must be object-language definable. Devlin II.5.2 is the collapse of a Σ₁
hull (`dev/literature/devlin-II5.md:72-77`). SZ 1.16 is a Σ₁-preserving
embedding whose domain is a J-structure
(`dev/literature/j-hierarchy.md:90-92`). Neither source codes an arbitrary
ambient injection. Truncation-and-selection says a proof that only needs
cardinal arithmetic never needs an injection as data
(`dev/literature/truncation-and-selection.md:83-86`), and that `leastOf`
does not deliver a data payload (`:148`).

The archived cardinal predicates already spell a bijection as a `Formula`
of five clauses (`archive/src/2026-08-09-rud-route/L/CardinalPredicates.lagda.md:16-19`).
That is the same hypothesis: a graph in L is a defined relation, not an
arbitrary function on fibres.

So the unconditional `amb-to-coded` is not an assembly. It is a theorem
with an unmet hypothesis. A literature NO-GO on that statement is this
return.

## 7. THE HANG, AND WHAT WAS NOT RERUN

A first HALF B reconstructed uniqueness and injectivity from `GraphOf`,
which names `f` inside `PT.rec`. That process reached 8.5 GB RSS and 3 min
28 s CPU and was still running. It was killed. It was not a heap
exhaustion. The thin HALF B, with no `f` in the proof, is a different
shape. It was run once, green, 1.64 s.

## ARCHIVE USED

- `archive/src/2026-08-09-rud-route/L/Condensation.lagda.md`: read.
  `:5` "Devlin states it for an elementary substructure of a level: the
  substructure". Used as confirmation that the literature's embedding is a
  collapse of a hull, not an arbitrary ambient injection.
- `archive/src/2026-08-09-rud-route/L/Coding`: named. Read
  `archive/src/2026-08-09-rud-route/L/Coding/Base.lagda.md:4` "Codes are
  sets now, but a certificate living inside the model cannot use that".
  The rest of that directory was not read. It is the retired coding
  stack. This task measures the live `InjCode`.
- `archive/src/2026-08-09-rud-route/L/CardinalPredicates.lagda.md`: read.
  `:18` "that is a relation from `x` to `y`, single-valued and total on
  `x`, injective," Used: the retired chapter codes a bijection as a
  `Formula`, never from an arbitrary ambient function.
- `archive/dev/TASKS-archived.md`: declined. Grep for `InjCode` and
  `ambient injection` returned no hit. Not used.
- `archive/dev/JOURNAL-archived.md`: declined. Grep for `InjCode` and
  `ambient injection` returned no hit. Not used.
- `archive/dev/LJ-dispatch-index.md`: read `:1` "# THE `LJ` DISPATCH INDEX,
  archived 2026-08-18". Declined. It is a dispatch index. It does not bear
  on whether an ambient injection is coded.
- `dev/ARCHIVE.md`: read `:1` "# ARCHIVE.md: the archive registry".
  Declined. This task does not retire a module.

## LITERATURE USED

- `dev/literature/devlin-II5.md`: read. `:72` "> 5.2 Theorem (The
  Condensation Lemma). Let α be a limit ordinal. If". Used for D-10 and
  W8: the literature's embedding is a collapse of a hull.
- `dev/literature/j-hierarchy.md`: read. `:90` "> Let M = <J_α^A, B> be a
  J-structure, and let π : M̄ ->_Σ1 M where M̄ is". Used for W8: SZ 1.16
  is Σ₁-elementarity, not an arbitrary injection.
- `dev/literature/truncation-and-selection.md`: read. `:75` "**A cardinal
  inequality is a" and `:148` "index is a proposition. **A data payload
  does not come out.**" Used for D-10: the truncated ambient arrow does
  not yield a graph as data.
- `dev/literature/digest.md`: read. `:45` "limit α (SZ pp. 9-10, equation
  I.1). Condensation is at the Sigma-1". Used as the orthodox statement
  of the same hypothesis.
- `dev/literature/BIBLIOGRAPHY.md`: read. `:1` "# Bibliography for the rud
  route". Used as the index of what is digested. It does not contain a
  theorem that every ambient injection is constructible.

## WHAT THE NEXT BRIEF NEEDS

HALF B is paid. The four conjuncts follow from the membership readings.
The remaining type is `HalfA`. The Def tower cannot inhabit it at an
arbitrary `_↪_`. A next brief that wants a code at a named map must supply
a `Formula` for that map. A next brief that wants the truncated arrow at
`src/L/Cardinal.lagda.md:133` to become a code is asking for HALF A at
generality, and that is the bill for `[LJ-2.5]`.
