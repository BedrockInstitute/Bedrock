# LJ-1.278 report: land A1, A3, A4 as `src/L/Cardinal.lagda.md`

tier: pi (deepseek-subagent-mode), model `deepseek-v4-pro`. One Agda slot held.
A new master written. No commit, no push. Written incrementally (C-22). Every
negative is MEASURED or INFERRED, in those words. ASD-STE100 applies.

## 0. LEAD

**189 in-fence lines, 100.57 s cold (mean of 3), rate 0.532 s/line, which is
50.6x the 0.010514 bar.** MEASURED, three cold runs, load 5.5-7.4. The master
is GREEN, exit 0, `--safe`. The re-run that imports it is GREEN, exit 0. This
is a landing, not a copy (C-45).

| figure | value |
|---|---:|
| in-fence non-blank lines (ledger caliber, live) | 189 |
| cold elapsed (mean of 3) | 100.57 s |
| cold range | 100.35-100.97 s |
| rate | 0.532 s/line |
| bar | 0.010514 s/line |
| rate as a share of the bar | 50.6x |

**The rate is NOT the P-m parameterized class.** A2 was parameterized
(0.0070 s/line). This master is mixed, and the whole-master figure is carried
by A1's instantiation content, the ambient chain's own `κ-min-at` step. Section
1 bisects it. A3 and A4 are cheap; A1 is the expensive term, and it is a
payable floor (P-n), not a defect.

## 1. MACHINE AND PROCESS DISCIPLINE, AND THE BISECT

ONE agda process, `GHCRTS="-A64m -I0 -M8g"`, cap never raised, no heap
exhaustion, no kill, no run past 30 minutes.

| run | exit | cold/warm | elapsed s | 1-min load |
|---|---|---:|---:|---:|
| master, run 1 (discarded first) | 0 | cold (fresh) | 102.50 | 7.54 |
| master, run 2 | 0 | cold (deleted .agdai) | 100.97 | 7.41 |
| master, run 3 | 0 | cold (deleted .agdai) | 100.35 | 6.30 |
| master, run 4 | 0 | cold (deleted .agdai) | 100.38 | 5.47 |
| `ReRun.agda` | 0 | cold (fresh) | not timed, exit 0 | 6-7 |

Cold figure in the lead is the mean of the three kept runs, 100.57 s. The
machine was loaded throughout (5.5-7.4); the figure is an upper bound in the
loaded-machine convention.

**The bisect, done to answer C-49** (a rate can be a property of the LAYOUT
rather than the content):

| cut | lines (non-blank) | cold s | rate |
|---|---:|---:|---:|
| A1 alone (`BisectA1.agda`) | 108 | 98.24 | 0.91 s/line |
| A3+A4+SiteBound, no A1 (`BisectA34.agda`) | 119 | 2.37 | 0.020 s/line |
| whole master | 189 | 100.57 | 0.532 s/line |

**The cost is CONTENT, not layout.** A1 alone reproduces 98.24 s of the
100.57 s. This is the same term `[LJ-1.232]` measured at the probe site
("A1 mean about 100.3 s", `lj-1.232-report.md:51`), and the same cause
`[LJ-1.236]` named for the ambient comparable: `κ-min-at` runs `leastOf` over
`ordSWO (sucV α)`, whose comparison unfolds the union representation
`⟪ sucV α ⟫` (`lj-1.236-report.md` section 5). A3 and A4 avoid it because
`orderAt` is opaque (`src/L/Choice/Step.lagda.md:740-743`). C-49 is answered:
the new master's layout adds nothing; the cost is A1's content.

## 2. PREMISES, MARKED

- **VERIFIED. A3 and A4 name A2's predicate.** Both use `injAt`, imported
  from `L.Coding.Injection` (`src/L/Cardinal.lagda.md:27`). The local copies in
  `ProbeLJ1232A3.agda:73` and `ProbeLJ1236A4.agda:67` are deleted.
- **VERIFIED. A3 and A4 have no undelivered import beyond A2.** Every import
  of the master is a delivered master; `lint-agda.py --check` exits 0, which is
  the master necessity check.
- **REFUTED. A4's probe is a minimal core, not the master.** `[LJ-1.253]`
  section 1 already dissolved this gap, and my master confirms it: A4 landed as
  the probe content verbatim (`InjCode`, `IsCardinalL`, `InternalLeastCard`),
  minus the 11-line probe-only `Atω` guard. A4 is NOT larger than 43; it is
  smaller once the shared device and the probe-only guard are accounted
  (section 3).
- **VERIFIED. The three blocks belong in one file.** A1 is the ambient face,
  A3 and A4 the internal faces, and the internal faces share one device
  (`SiteBound`). One master is right. Nothing would split.
- **VERIFIED with the caliber correction the brief predicted.** The prices are
  54, 26, 43 in the NARROW caliber; the ledger caliber (DD5's, the only
  admissible source) counts non-blank lines inside fences. Delivered 189
  against the priced 123, ratio 1.54x. The brief said expect more than 123;
  189 is what landed.

## 3. ORDER AND EXPORTS

**The order in the file, and why.** `_↪_` first (the shared ambient atom), then
A1 (wave 0, no A2 dependency), then the shared `SiteBound`, then A3, then A4
(wave 1, both name A2's `injAt`). A1 is the ambient-injection face and does not
need the internal coding atoms; the two internal faces share `SiteBound` and
the `orderAt` well-order, so they sit together after it. Inside A4 the
dependency order is `InjCode`, then `IsCardinalL`, then `InternalLeastCard`.

**What each block exports, with its consumer.**

| export | block | consumer | evidence |
|---|---|---|---|
| `_↪_` | shared atom | A7's `SqShape`/`AbsorbsShape`/`SuccCardL` use the injection shape | `ProbeLJ1236A7.agda:120-145` |
| `module LeastCardInjL` | A1 | the future GCH proof (no A-block names it) | no block names it; MEASURED |
| `module SiteBound` | shared device | A3, A4, and the future GCH proof | internal |
| `module Canonical` | A3 | the future GCH proof (no A-block names it) | MEASURED |
| `InjCode` | A4 | **A7** | `ProbeLJ1236A7.agda:91` |
| `IsCardinalL` | A4 | **A7** | `ProbeLJ1236A7.agda:103` |
| `module InternalLeastCard` | A4 | the future GCH proof | no A-block names it; MEASURED |

**What the three downstream consumers need from THIS master** (the brief's
question):

- **A5 row 1: nothing.** It consumes `L.Coding.Injection` only (`injAt`,
  `injAt-out`, `injAt-in`, `Extract`, `Small`), per `ProbeLJ1264A.agda`.
- **A6: nothing.** It consumes `L.Coding.Injection` only
  (`injAt; injAt-in; module Small`), per `ProbeLJ1217A.agda:239-240`.
- **A7: `InjCode` and `IsCardinalL`.** Its S1/S2 copies at
  `ProbeLJ1236A7.agda:91` and `:103` become imports from this master. It does
  NOT import `LeastCardInjL`, `Canonical` or `InternalLeastCard`; those are the
  proof's future supplies, not the statement's.

**Delivered sizes per block.** The narrow caliber (non-comment in-fence) reads
A1 = 54, A3 = 19, A4 = 28, the shared `SiteBound` = 7, the shared `_↪_` = 2.
A1 matches its price exactly (54). A3 and A4 are below their narrow prices (26
and 43) because the β/oβ/up device moved into `SiteBound` (7 shared lines) and
A3's unused `ω∈β` and both probe-only `Atω` guards were dropped. In the LEDGER
caliber the whole master is 189 lines, and that is the figure that binds.

**One signature kept against the probe.** `InternalLeastCard` keeps its
`(oκ : IsOrd (fst κ))` parameter even though the delivered body does not use
it. It is the hypothesis the theorem is ABOUT (κ is an L-ordinal), and the
future proof that the selected δ is a cardinal will consume it. Kept, not
trimmed, per the brief's "do not trim to meet a number".

## 4. THE `src/Everything.lagda.md` LINE

**`import L.Cardinal`**, to be inserted **after line 365 (`import L.Choice.Step`),
before line 366 (`import L.Choice.Internal`)**. Derived from the master's own
imports: its latest dependency in reading order is `L.Choice.Step` (line 365);
its other dependencies sit at 317, 318, 321, 323, 324, 335, 336, 362, all ≤ 365.
Its consumer A7 (`L.GCH`) is not yet in the catalog. I did NOT touch
`Everything.lagda.md`; the orchestrator wires it after audit.

## 5. THE RE-RUN (C-45)

**`agents/tasks/LJ-1-278/ReRun.agda`, exit 0.** It imports the master and uses
each export at the real ordinal ω:

- `LeastCardInjL aω ω-ord` fully instantiated, and `L1.κ`, `L1.κ-inj`,
  `L1.oκ`, `L1.up` used (the least cardinal above ω is produced, not assumed);
- `Canonical aω aω` instantiated, `C3.Good` used in a type;
- `InternalLeastCard aω ω-ord` instantiated, `ILC.Good` used in a type;
- `InjCode` and `IsCardinalL` used in consumer-shaped types;
- `SiteBound.β/.oβ/.up` and `_↪_` used directly.

A copy that compiles is not a landing; this re-run proves the master is a
supply. The `Canonical` and `InternalLeastCard` `chosen`/`Selected` submodules
stay uninstantiated because their nonempty witness is A2's `lid`, A5's
deliverable, not A4's (per `lj-1.253-report.md` section 1).

## 6. EVERY EXISTING MASTER I DID NOT EDIT

**MEASURED: zero tracked files modified.** `git diff --stat` over tracked files
is empty; `git status --short` shows no ` M` entry. All 90 tracked masters are
unedited. The four over-the-bar Condensation masters are untouched:
`src/L/Condensation.lagda.md`, `src/L/Condensation/LowerAgree.lagda.md`,
`src/L/Condensation/UpperAgree.lagda.md`,
`src/L/Condensation/TwelveAgree.lagda.md`. The sibling's files
(`src/L/InjChain.lagda.md`, `agents/tasks/LJ-1-279/`) and today's
`src/L/Coding/Injection.lagda.md` and `src/L/Coding/EnvSupply.lagda.md` were
not touched. `[LJ-1.268]`'s claim holds: no existing master gains a line.

## 7. DD4, ON THE AC-AGAINST-GCH AXIS

**Axis named (C-46): DD4's own axis is AC-against-GCH**, fixed in code at
`scripts/ledger.py:50` (the AC closure against the GCH closure).

**On that axis this master lands on the GCH side alone.** MEASURED. The AC
root's import list at `src/L/Model.lagda.md:46-57` reaches 73 masters, and
`src/L/Cardinal.lagda.md` is NOT among them (my own closure computation over
`scripts/ledger.py`'s `import_graph`/`closure`). Two of its dependencies
(`L.Choice.Stage`, `L.Choice.Step`) ARE in the AC closure, so it reuses shared
infrastructure; `L.Ordinal.SquareLaw` and `L.Coding.Injection` are NOT in the
AC closure. The GCH root (`L.GCH`, A7) will import `InjCode`/`IsCardinalL`, so
the day it lands, this master enters the GCH closure.

**On the phase's proxy axis (Def-against-J), A1, A3 and A4 are all per-tower**
(`[LJ-1.227]`), so this master is the per-tower half of A-prime, exactly where
DD4's cost sits. **What a J instantiation would have to rewrite:** the
level-hood certificate in A1 (`isL`, `Lset→isL`, `ord∈Lset-suc`, `isL-trans`,
the `S = Σ[ x ∈ V ] isL x` carrier) becomes J's level-hood predicate and its
crossing; the definable well-order in A3/A4 (`stageBound`, `orderAt`, `Mem`,
`Lset`, `Lset→isL`) becomes J's structural order (`<^A`, `devlin-II5.md`
section 4). The either-tower machinery transfers verbatim: `_↪_`, `⟪_⟫`,
`sucV`, `ordSWO`, `leastOf`, `member`, `fiber`, `self∈sucV`, and A2's coding
atoms `injAt`/`svAt`/`domAt` (swapped for J's coding atoms with the same
adequacy interfaces).

## 8. ARCHIVE USED (DD18)

One line read named per archived file.

- **`agents/tasks/LJ-1-232/ProbeLJ1232A1.agda`, read WHOLE.** Line read `:116`,
  `hSucα = Lset→isL (sucV (sucV (fst α))) ...`. TAKEN: the whole A1 content,
  which became the master's A1 verbatim.
- **`agents/tasks/LJ-1-232/ProbeLJ1232A3.agda`, read WHOLE.** Line read `:125`,
  `Good A = ((up A ∷ D ∷ []) ⊨ svAt zero) ...`. TAKEN: the whole A3 content.
- **`agents/tasks/LJ-1-236/ProbeLJ1236A4.agda`, read WHOLE.** Line read `:84`,
  `InjCode F a b = ...`. TAKEN: the whole A4 content.
- **`agents/tasks/LJ-1-236/lj-1.236-report.md:154` and `:283`.** TAKEN: A4's
  43-line figure and the "minimal core" wording, the premise to test (REFUTED
  here, section 2).
- **`agents/tasks/LJ-1-268/lj-1.268-report.md:23-48`.** TAKEN: the landing
  order (A1 in wave 0, A3/A4 in wave 1, one master).
- **`agents/tasks/LJ-1-277/lj-1.277-report.md`, read WHOLE.** TAKEN: the
  landing method (new master, trimmed using lists, re-run the consumer against
  the master), copied here.
- **`agents/tasks/LJ-1-253/lj-1.253-report.md:12-21`.** TAKEN: the three
  prices and the caliber note.
- **`archive/dev/TASKS-archived.md:10`.** TAKEN, SHAPE ONLY: "The 264 rows
  below record every dispatch made on the retired route".
- **`archive/src/2026-08-09-rud-route/L/CardinalPredicates.lagda.md:536-537`.**
  TAKEN, SHAPE ONLY: the retired route held the internal predicates in one
  master. **WHAT WOULD NOT TRANSFER:** the retired `cardFo` is the BIJECTION
  form (`bijFo`, `eqFo`, `cardFo` at `:330-385`); A-prime's `IsCardinalL` is
  the INJECTION form over A2's coding atoms. The one-master shape transfers;
  the body does not.

## 9. LITERATURE USED (DD18)

**`dev/literature/devlin-II5.md:365-395`, read directly.** TAKEN: the
twelve-row step table and the per-tower verdict at `:387-389`.

**Which rows A1, A3 and A4 serve:**

- **A1 serves row D/G** (the hull with least witnesses / the well-order
  transfer): it runs `leastOf` over the ambient `ordSWO` well-order, the
  either-tower least-witness device, with the per-tower level-hood certificate
  (row C) inside the crossing `up`.
- **A3 serves row D** (the definable well-order): the canonical selection
  `leastOf (orderAt β oβ)` is exactly the least-witness step, with the
  per-tower order supplied by `stageBound`/`orderAt`.
- **A4 serves row D applied to cardinality, plus row F's cardinal-comparison
  shape**: `InternalLeastCard` selects the least L-element admitting a code, the
  internal form of the cardinal comparison row F concludes (`|L_α| = |α|`),
  stated over A2's internal injections instead of Devlin's subset containment.

**`[LJ-1.273]` mapped row E to counting; check it.** VERIFIED, with the one
correction this master does not serve row E. Row E is the counting
`|ℒ_X| = max(|X|, ω)` (`devlin-II5.md:357-360` in the digest's section 2.5),
which is either-tower cardinal arithmetic. A1/A3/A4 do not count formulas; they
select least witnesses. Row E's content lands elsewhere in A-prime (A5/A6's
readbacks and the stage-bound machinery). So the mapping holds for the route;
it does not pass through this master.

## 10. THE NEGATIVES, CLASSIFIED

- **MEASURED FALSE. The master fails to typecheck.** exit 0, `--safe`, three
  cold runs, one discarded first run.
- **MEASURED FALSE. An import is not delivered.** `lint-agda.py --check` exits
  0, the master necessity check.
- **MEASURED FALSE. A wall.** Max single run 102.50 s, far under 30 minutes;
  no heap exhaustion, cap never raised.
- **MEASURED FALSE. A4 is much larger than 43.** A4 landed at 28 non-comment
  lines (31 non-blank), below its narrow price, not above it.
- **MEASURED FALSE. The three blocks do not belong together.** A1 is the
  ambient face, A3/A4 the internal faces, and they share `_↪_` and `SiteBound`.
- **MEASURED FALSE. I touched an existing master or `Everything.lagda.md`.**
  `git diff --stat` empty; only new files written.
- **MEASURED FALSE. I touched `L.Choice.Name` or `agents/tasks/LJ-1-279/`.**
  Neither appears in my writes; my write territory was
  `src/L/Cardinal.lagda.md` and `agents/tasks/LJ-1-278/` only.
- **MEASURED. The master is NOT in A2's parameterized class.** 0.532 s/line
  against A2's 0.0070; the bisect pins the cost to A1's `κ-min-at` (98.24 s),
  an instantiation term (P-m/P-n), while A3+A4 check at 0.020 s/line.
- **INFERRED. `module LeastCardInjL`, `module Canonical` and
  `module InternalLeastCard` stay public with no current A-block consumer.**
  They are the proof's future supplies; no block names them today (MEASURED),
  and exporting them is the placement decision.

## 11. WORKING TREE, AS MY REPORT DESCRIBES IT

Five files written, all new:

- `src/L/Cardinal.lagda.md` — the new master, 189 in-fence lines, GREEN.
- `agents/tasks/LJ-1-278/ReRun.agda` — the re-run, GREEN.
- `agents/tasks/LJ-1-278/BisectA1.agda` — the A1-only bisect, GREEN (98.24 s).
- `agents/tasks/LJ-1-278/BisectA34.agda` — the A3/A4 bisect, GREEN (2.37 s).
- `agents/tasks/LJ-1-278/lj-1.278-report.md` — this file.

No master, brief or report edited. No commit, no push, no `git checkout .`,
stash, reset or clean. The sibling directory `agents/tasks/LJ-1-279/` and the
sibling master `src/L/InjChain.lagda.md` were not touched.

`scripts/lint-agda.py --check` and `scripts/lint-prose.py --check` both exit 0
on the master.
