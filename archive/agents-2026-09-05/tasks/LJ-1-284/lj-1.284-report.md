# [LJ-1.284] report: LAND A6 and A5 row 3, the last two A-prime blocks

tier: opus (in-harness-subagent-mode). One Agda slot held, one process at a
time, `GHCRTS="-A64m -I0 -M8g"`, cap never raised. No commit, no push. Written
incrementally (C-22). Every negative is MEASURED or INFERRED, in those words.
ASD-STE100 applies.

## 0. LEAD

Both blocks land green. The re-site onto A2 works. A6 DISCHARGES A7's second
hypothesis on the nose, and the typechecker says so.

| figure | A6, `src/L/Absorption.lagda.md` | A5 row 3, `src/L/InjChain.lagda.md` |
|---|---:|---:|
| in-fence non-blank lines (ledger caliber, live tree) | **525** (new master) | **502** (was 343) |
| cold elapsed, mean of 3 kept | **5.75 s** | **3.62 s** |
| cold range | 5.68 to 5.81 s | 3.54 to 3.69 s |
| 1-minute load beside each run | 5.09 to 5.36 | 5.90 to 6.15 |
| rate, s per line | 0.01095 | 0.00721 |
| against the 0.010514 bar | **1.04x** | **0.69x** |

A6 is 1.04x the bar. That is an overage and it is recorded plainly (DD8). It
is not trimmed to a number.

Row 3's own marginal cost is **INFERRED, not MEASURED**: the master went from
343 lines at 3.05 s (`[LJ-1.279]`, load 11.24) to 502 lines at 3.62 s (mine,
load 5.90 to 6.15), so 159 lines cost about 0.57 s, which is 0.0036 s per
line. The two figures come from two machine states, and I did not re-measure
the pre-edit file, so this is an inference and not a price.

## 1. MACHINE AND PROCESS DISCIPLINE

ONE agda process at a time. `GHCRTS="-A64m -I0 -M8g"` on every run, cap never
raised. One warm-up discarded per master, `.agdai` deleted before every kept
run (`_build/2.8.0/agda/src/L/*.agdai`).

**MEASURED FALSE: a heap exhaustion.** **MEASURED FALSE: a wall.** The longest
single invocation in this task is 16.13 s, which is the A6 probe. No run came
near 30 minutes. No kill, no interrupt.

The sibling `agents/tasks/LJ-1-283/` was live for part of the task, so the
load is not idle. Every absolute figure above carries its load.

## 2. THE ABORT CRITERION, FIXED BEFORE THE RUN (D-1)

- **BOTH LAND GREEN.** This fires. Both masters, both timings, the Everything
  line and the PairBound answer are below. STOP.
- **THE RE-SITE FAILS.** Does not fire. Section 3.
- **A6 IS MUCH LARGER THAN 399.** Does not fire. 525 is 1.32x the narrow
  price, inside the 1.28x to 1.5x band the brief named.
- **A6 CAN DISCHARGE ONE OF A7's HYPOTHESES.** THIS ALSO FIRES, and it is the
  most valuable outcome. Section 5. **I stopped before touching
  `src/L/GCH.lagda.md`.**
- **A WALL.** Does not fire.

## 3. THE RE-SITE ONTO A2. IT WORKS.

Both probes opened `ProbeLJ1134A`, which no longer exists. Both now open the
delivered A2 master, with the same three names.

- `agents/tasks/LJ-1-176/ProbeLJ1176A.agda:73-77`: was
  `open import ProbeLJ1134A {ℓ} lem using ( injAt; injAt-in; module Small )`,
  now `open import L.Coding.Injection {ℓ} lem using (...)`.
  **exit 0, 1.69 s, load 4.70.**
- `agents/tasks/LJ-1-217/ProbeLJ1217A.agda:239-243`: the same change.
  **exit 0, 15.33 s, load 4.70.**

**MEASURED: the gap is empty.** A2 supplies every name the deleted probe
supplied for these two files. The three names sit before A2's `private` block:
`injAt` at `src/L/Coding/Injection.lagda.md:44`, `injAt-in` at `:72`,
`module Small` at `:123`; the private range machinery starts at `:156`.
`Small` also re-exports `module E = Extract` at `:130`, and both probes reach
into it through `Sm.E.toFun` and `Sm.E.toFun-graph`. `Extract` is public at
`:80`.

**I did NOT reconstruct the deleted probe.** The two edits are three comment
lines and one import line each.

## 4. WHAT LANDED

**A6 into `src/L/Absorption.lagda.md`, NEW, 525 lines.** Five parts:

| part | what it is | line |
|---|---|---:|
| 1 | `module ShiftAbs`, the ambient three-case shift with four readback lemmas and `shift-inj` | `:73` |
| 2 | `val`, `shiftCase1..3`, `shiftRel`, `shiftFo`, `module ShiftFo`: the description, ONE place, and its two-way reading | `:207`, `:223`, `:228` |
| 3 | `module Carve`, the graph by separation. **Not one `hasReplacementL`** | `:385` |
| 4 | `module ShiftGraph`, the L instantiation | `:538` |
| 5 | `absorbs`, A6's conclusion, uniform over the infinite L-ordinals | `:613` |

**A5 row 3 into `src/L/InjChain.lagda.md`, 343 to 502 lines.** Row 3 is
`inclFo` (`:445`), `module InclFo` (`:448`), `module Carve` (`:468`),
`module InclGraph` (`:575`) and `module OrdIncl` (`:604`). The shared
`module StageBound` also lands, at `:75`, at the head of the file, because
three sites now consume it.

The C-38 guards for both blocks are in the re-run, not in the masters, which
is `[LJ-1.279]`'s landing method.

## 5. A6 DISCHARGES A7's `absorbs` HYPOTHESIS

**YES, on the nose, with no adapter.** The evidence is not a reading of two
types. It is a green typecheck of two lines at
`agents/tasks/LJ-1-284/ReRun.agda:92-93`:

```
absorbsShape : AbsorbsShape
absorbsShape = absorbs
```

`AbsorbsShape` is imported from the delivered `src/L/GCH.lagda.md:49-53`.
`absorbs` is imported from the delivered `src/L/Absorption.lagda.md:613-618`.
There is no `subst`, no eta-expansion and no wrapper between them. The file
exits 0 and is `--safe`.

The type, at `src/L/Absorption.lagda.md:613-615`:

```
absorbs : (γ : S) → IsOrd (fst γ) → (⟨ fst γ ∈ ω ⟩ → Empty.⊥)
        → ((k : ℕ) → ⟨ # k ∈ fst γ ⟩)
        → ⟪ sucV (fst γ) ⟫ ↪ ⟪ fst γ ⟫
```

against `src/L/GCH.lagda.md:50-53`:

```
AbsorbsShape =
  (γ : S) → IsOrd (fst γ) → (⟨ fst γ ∈ˢ ω ⟩ → Empty.⊥)
          → ((k : ℕ) → ⟨ # k ∈ fst γ ⟩)
          → ⟪ sucV (fst γ) ⟫ ↪ ⟪ fst γ ⟫
```

The two membership forms agree because `𝒮ᵥ`'s membership field IS `_∈_`
(`src/V/Hierarchy.lagda.md:83`). `_↪_` is one name in both files: A6 imports
it from `src/L/Cardinal.lagda.md:47-48`, which is where A7 gets it.

**I did NOT edit `src/L/GCH.lagda.md`.** The decision is the orchestrator's.
What it would take: add `open import L.Absorption {ℓ} lem using ( absorbs )`
to `src/L/GCH.lagda.md`, and delete the `(absorbs : AbsorbsShape) →` line at
`src/L/GCH.lagda.md:69`. `L.Absorption` must then sit before `L.GCH` in the
catalog, which is where section 7 puts it.

**A7's OTHER hypothesis, `sq : SqShape`, is NOT discharged by this task.**
MEASURED: `SqShape` (`src/L/GCH.lagda.md:42-45`) is the square law uniform
over ALL infinite L-ordinals, and `src/L/InjChain.lagda.md` supplies only the
BASE at ω (`squareω : sq ω`, `:146`). The uniform statement needs the
square-law chain, which no master carries today.

## 6. THE PairBound DUPLICATION IS GONE

`module PairBound` rebuilt its own bounding machinery because the shared
`StageBound` was not delivered (`[LJ-1.279]` section 3, premise 5). It now
names the shared device.

| block | before | after | delta |
|---|---:|---:|---:|
| `module PairBound`, with its header comment | 42 | 33 | **-9** |

**MEASURED: 9 lines removed.** What went: the private `stg` and `b`, and the
`opaque` block's `β`, `oβ` and `bnd`, and the `Lset-mono`/`stage-mem` body of
`below`. What stays: the index type, the two coercions, the pair family, and
the `subst` that turns the family's index into the consumer's pair.

The `bnd` alias points at a SEALED name, so it stays an atom. **R-38 is not
triggered**: `SB.bnd` is opaque by delivery, not transparent, so the alias is
not a birth site.

The `Lset` import became unnecessary and was dropped
(`src/L/InjChain.lagda.md:21`). `lint-agda.py --check` exits 0, which is the
import-necessity check.

**Three sites now share ONE bound**, and the shared block costs 27 lines once:
`PairBound` (row 1, `src/L/InjChain.lagda.md:276`), `InclGraph` (row 3, `:575`)
and `ShiftGraph` (A6, `src/L/Absorption.lagda.md:538`). Before this task there
was one delivered copy plus a private copy inside each of the two probes.

Net for the master: 343 to 502 lines is **+159**, which is row 3's 141 plus
the shared `StageBound`'s 27 plus three import and module lines, minus the 9
removed and minus the 4-line row-3 marker that row 3 replaced.

## 7. THE `src/Everything.lagda.md` LINE

**`import L.Absorption`, to be inserted AFTER line 366 (`import L.Cardinal`)
and BEFORE line 367 (`import L.GCH`).**

Derived from its own imports and its consumer. Every direct dependency is
earlier in the fence: `L.Constructible` (317), `L.Ordinal` (318),
`L.Ordinal.SquareLaw` (323), `L.WellOrder.Base` (324), `L.Axioms.Basic` (328),
`L.Axioms.Full` (332), `L.Coding.Model` (335), `L.Coding.Injection` (336),
`L.InjChain` (337), `L.Axioms.Numerals` (360), `L.Axioms.Infinity` (361),
`L.Choice.Finite` (363), `L.Cardinal` (366). The deepest is `L.Cardinal` at
366, so 367 is the first admissible position. It is also the RIGHT position by
first consumption: the consumer is `L.GCH` at 367, which is where `absorbs`
discharges a hypothesis.

`L.InjChain` is already wired at line 337 and needs no move: row 3 adds no
import that sits later than `L.Coding.Injection` (336).

**I did NOT touch `src/Everything.lagda.md`.**

## 8. THE RE-RUNS THAT PROVE BOTH LANDINGS (C-45, C-40)

**exit 0 of a master is not a supply.** Each landing is proved by a file that
IMPORTS the master and uses what it exports.

`agents/tasks/LJ-1-284/ReRun.agda`, exit 0, `--safe`, cold, 10.75 s, load 4.82:

- **PART 1, A6's C-38 guard at the concrete ordinal ω.**
  `module SG = ShiftGraph ωʟ ω-ord (∈-irrefl ω) (λ k → #∈ω k)`; `zero∈D` puts
  0 into the domain `sucV ω`; `inG` shows the carved graph HOLDS the pair
  `<0, shift 0>`, so nothing above is vacuous; `theShift`/`theShift-inj` show
  it runs as an honest injection `⟪sucV ω⟫ ↪ ⟪ω⟫`; `theShift-val0` shows the
  value IS the shift's value, not some other injection's.
- **PART 2, the A7 question.** `absorbsShape : AbsorbsShape` (section 5).
- **PART 3, row 3's C-38 guard at two real ordinals of L**, the numerals 1
  and 2: `module J = OrdIncl two oTwo one one∈two`, `inG` holds `<0,0>`,
  `theIncl`/`theIncl-inj` run, and `theIncl-val` says the value is the same
  SET. Row 5 is re-asserted through the edited master as `squareω-again`,
  `pairω-runs` and `pairω-inj-again`.

**C-40, every consumer of the edited `src/L/InjChain.lagda.md`, re-run.**
MEASURED by grep over `src` and `agents` for `L.InjChain`: there are exactly
three, plus the catalog line.

| consumer | exit | cold elapsed | load |
|---|---|---:|---:|
| `src/L/Absorption.lagda.md` (imports `module StageBound`) | 0 | 5.75 s (mean of 3) | 5.09-5.36 |
| `agents/tasks/LJ-1-279/ReRun.agda` (imports `module Comp`, `pairω`, `squareω`) | 0 | 1.73 s | 4.98 |
| `agents/tasks/LJ-1-284/ReRun.agda` (imports `module OrdIncl`, `pairω`, `squareω`) | 0 | 10.75 s | 4.82 |

`agents/tasks/LJ-1-279/ReRun.agda` is the one that matters for the PairBound
rewrite: it builds a CONCRETE composite through `module Comp`, which is
`PairBound`'s only consumer. It is green after the rewrite.

Both re-sited probes were also re-run at the final tree state: exit 0 each
(section 3).

`lint-agda.py --check`, `lint-prose.py --check` and `weave-i18n.py --check`
all exit 0 on both masters. `check-probes.py` is clean over 2,299 tracked
files. `ledger.py --check` exits 0: `standing 31,792 lines measured over 93
masters`, declaration clean. **I did NOT touch `dev/ledger.toml`.**

## 9. DD4, WITH ITS AXIS

### 9.1 The AC-against-GCH axis, which is DD4's own (C-46)

The axis is fixed in code at `scripts/ledger.py:50` and read by
`ledger.py --reuse`. The report resolves every file through
`git show HEAD:<path>` (`scripts/ledger.py:119-123`, `:377-388`), so **it
cannot see this task at all**: nothing is committed. The published figure is
unchanged at **41.1 percent shared, 7,596 of 18,495 lines**.

I re-ran the same closure computation over the LIVE tree, with both new
masters added to the file set. **MEASURED: the figure does not move.**

| state | AC closure | GCH closure | SHARED | union | share |
|---|---:|---:|---:|---:|---:|
| live tree, `L.GCH` unedited (today) | 73m / 17,197 | 48m / 8,894 | 43m / 7,596 | 18,495 | 41.1% |
| after `L.GCH` imports `L.Absorption` | 73m / 17,197 | 51m / 9,957 | 44m / 7,632 | 19,522 | **39.1%** |

**MEASURED: neither master is in either closure today.** `L.GCH` is the
declared `gch_root` and it imports `L.Cardinal`, which does not import
`L.InjChain`. So landing these 1,027 lines changes no closure figure until the
discharge in section 5 is taken.

**When the discharge is taken, three masters enter the GCH closure:**

| master | lines | where it lands |
|---|---:|---|
| `src/L/Absorption.lagda.md` | 525 | GCH only |
| `src/L/InjChain.lagda.md` | 502 | GCH only |
| `src/L/Axioms/Infinity.lagda.md` | 36 | **SHARED** (already in the AC closure) |

**So 36 of the 1,063 new GCH-closure lines land in the shared intersection,
and 1,027 do not.** The share falls from 41.1 to 39.1 percent. That is what a
GCH-side endpoint does to this ratio, and it is stated rather than hidden: DD4
has no gate by ruling, and a share defended by refusing to land GCH content
would be the failure the no-gate ruling protects against.

### 9.2 The Def-against-J axis, and row 3's tower status

This is the axis `[LJ-1.248]`'s 146-to-196-line band lives on, and its band
EXCLUDED A5. Here is A5's contribution, MEASURED over the delivered master by
counting the CODE lines that name a tower atom (`hasSeparationL`,
`hasReplacementL`, `StageBound`, `stage`, `LsetS`, `boundingOrd`, `LsetS`,
`numeralL`, `ωʟ`, `∅ʟ`, `sucʟ`, `isL`, `𝒮ʟ`).

| block | non-blank lines | tower-atom code lines |
|---|---:|---:|
| row 5 (`pairω`, `squareω`) | 75 | **0** |
| row 1 (`appC`, `compFo`, `PairBound`, `Comp`) | 207 | 6 |
| **row 3** (`inclFo`, `InclFo`, `Carve`, `InclGraph`, `OrdIncl`) | **141** | **3** |
| shared `StageBound` | 27 | 5 |
| A5 as delivered | 450 | **14** |

**Row 3 is TOWER-NEUTRAL IN SHAPE.** Its `module Carve`
(`src/L/InjChain.lagda.md:468`, 87 lines) names **ZERO** tower atoms: the
bound, the subset witness and the separation field are all module parameters.
All 3 of row 3's tower-atom lines sit in `InclGraph` plus `OrdIncl`
(`:575`, 28 lines together), and they are exactly `StageBound`,
`hasSeparationL` and one `isL-trans` coercion. The J tower re-instantiates the
other 113 lines.

**A6's per-tower surface, MEASURED the same way:**

| part | non-blank lines | tower-atom code lines |
|---|---:|---:|
| `ShiftAbs` (ambient) | 115 | **0** |
| `ShiftFo` | 158 | 1 (an `isL-trans` coercion) |
| `Carve` | 135 | 1 (an `isL-trans` coercion) |
| **`ShiftGraph`** | **57** | **10** |
| `absorbs` | 11 | **0** |

**A6's per-tower half is `module ShiftGraph`, 57 lines**, and nothing else.
The J tower re-instantiates the other 468, including the whole ambient shift
and the whole carve.

**This closes `[LJ-1.248]`'s A5 gap**, in the unit that report used: counting
whole modules that a J tower would rewrite, A5's per-tower half is
`StageBound` (27) plus `PairBound` (33) plus `InclGraph` (22), which is **82
lines**, plus two `hasSeparationL` lines inside `Comp`. A6 adds **57**. Both
sit below the 146-to-196 band the survey gave for the rest of A-prime.

**The DD4 win of this task, stated plainly:** one `StageBound`, three carves,
in two masters. Before today the device existed once in a delivered master and
once inside each of two probes.

## 10. EVERY NEGATIVE, CLASSIFIED

- **MEASURED FALSE. A master fails to typecheck.** Both exit 0, `--safe`,
  three kept cold runs each plus a re-run each.
- **MEASURED FALSE. The re-site fails.** Both probes exit 0 against A2.
- **MEASURED FALSE. The re-site needed a reconstructed `ProbeLJ1134A`.** The
  change is one import line per probe.
- **MEASURED FALSE. A wall or a heap exhaustion.** Longest run 16.13 s.
- **MEASURED FALSE. An import is not delivered.** `lint-agda.py --check`
  exits 0 on both masters, which is the import-necessity check.
- **MEASURED FALSE. I touched `src/Everything.lagda.md`, `src/L/GCH.lagda.md`,
  `dev/ledger.toml`, `dev/PLAN.md`, `src/L/Choice/Name.lagda.md`,
  `src/L/Cardinal.lagda.md` or `agents/tasks/LJ-1-283/`.** `git status
  --short` shows my writes as exactly: `src/L/InjChain.lagda.md` (modified),
  `src/L/Absorption.lagda.md` (new), the two probes (modified),
  `agents/tasks/LJ-1-284/` (new). Every other entry belongs to the
  orchestrator or a sibling.
- **MEASURED FALSE. A6 needs a `hasReplacementL`.** The name occurs ONCE in
  `src/L/Absorption.lagda.md`, at `:377`, and that occurrence is a section
  comment saying the carve does not use it. The graph is carved by ONE
  separation, at `:412` through the `sep` parameter, and the parameter is
  supplied as `hasSeparationL` at `:605`.
- **MEASURED FALSE. Either master enters a trophy closure today.** Section 9.1.
- **INFERRED. Row 3's marginal cost is 0.0036 s per line.** Two machine
  states, and the pre-edit file no longer exists to re-measure.
- **INFERRED. A6's 1.04x rate is the parameterized content class (P-m).** The
  master is 468 of 525 lines under module telescopes, and P-m puts
  parameterized content near 0.01 s per line. I did not profile the file, so
  the class assignment is a reading of the rate and the shape, not a
  measurement of where the seconds went.

## 11. ARCHIVE USED (DD18)

One line read named per file.

- **`agents/tasks/LJ-1-217/ProbeLJ1217A.agda`, read WHOLE, FIRST.** TAKEN: the
  whole A6 content, all five parts. Line read `:504`,
  `G = fst (fst (sep bnd (shiftFo D γ ω z)))`, the one separation that carries
  the block.
- **`agents/tasks/LJ-1-176/ProbeLJ1176A.agda`, read WHOLE.** TAKEN: the whole
  row-3 content, and the `StageBound` module that became the shared device.
  Line read `:103`, `inclFo D = ∃̇∈ (con D) (prAtL (suc zero) zero zero)`, the
  one-place description whose codomain does not appear.
- **`agents/tasks/LJ-1-268/lj-1.268-report.md:23-48`, read.** TAKEN: the
  wave-3 order and the re-site instruction. Line read `:36-38`,
  "Wave 3 (after A2, after a re-site): A5 row 3 (inclusion) -> src/L/InjChain
  .lagda.md; A6 -> src/L/Absorption.lagda.md (new)".
- **`agents/tasks/LJ-1-279/lj-1.279-report.md`, read WHOLE.** TAKEN: where row
  3 goes, the PairBound duplication, and the export boundary A2 keeps. Line
  read `:126-130`, "Row 3's place. It lands at the end of this file, where the
  closing comment marks it".
- **`agents/tasks/LJ-1-282/lj-1.282-report.md`, read section 0 and 1.** TAKEN:
  today's landing and measuring method, which is one warm-up discarded and
  three kept cold runs per arm with the load beside each figure. Line read the
  section 1 sentence "ONE agda process at a time. `GHCRTS="-A64m -I0 -M8g"` on
  every run." I did NOT take its seal technique: `[LJ-1.282]` sealed a
  transparent `w` on `src/L/Cardinal.lagda.md`, and P-l forbids transferring a
  measured cure by analogy. My two masters are at 1.04x and 0.69x, so there is
  no 50x wall to cure.
- **`archive/dev/TASKS-archived.md:81`.** TAKEN, SHAPE ONLY:
  "L3.32-T46 | Cardinal chapter's counting side | DELIVERED". The retired
  route also ended these ordinal injections in a counting chapter, which is
  where row F consumes them. **WHAT WOULD NOT TRANSFER:** the route itself
  (Rud), its module layout, and every figure in that table.
- **`archive/src/2026-08-09-rud-route/L/Ordinal/SquareLaw.lagda.md:686-694`.**
  TAKEN, SHAPE ONLY: the retired route already had the three-case shift, with
  the same `shift-dec` split into `inl v∈ω`, `inr` with `inl v≡γ`, and `inr`
  with `inr`. That is evidence the three-case split is the right shape, not
  evidence for a price. **WHAT WOULD NOT TRANSFER:** the archived shift is
  AMBIENT, inside `SquareLaw`, over `⟪ sucV γ ⟫` in V, with `#+1∈γ` and `∅∈γ`
  as hypotheses. It never built the graph as an ELEMENT of L, which is the
  whole of A6's parts 2 to 5 and 410 of the 525 lines. The line counts do not
  transfer either (P-l).

## 12. LITERATURE USED (DD18)

**`dev/literature/devlin-II5.md`, read `:145-170` (the 5.5 to 5.8 chain),
`:375-395` (the twelve-row table and the DD4 verdict) and `:411-418` (the
II.1.1(vii) row).**

**Which of the twelve rows A6 and A5 row 3 serve: ROW F**, "5.5 |
condensation (i)(ii), |L_α| = |α|, initial ordinals" (`:382`), reached through
the counting half **II.1.1(vii)**, which `:411-418` records as "BEARS, as the
counting half of 5.5 and 5.6" and calls "generic cardinal arithmetic over the
level-size equation". A6's successor absorption and row 3's ordinal inclusion
are two steps of that arithmetic: 5.5's proof concludes `|γ| = |M| = |α| < κ`,
and 5.6 applies 5.5 at `κ⁺` with `α = κ` (`:157-164`). Row F's tower verdict
in the table is EITHER tower, which agrees with section 9.2's measurement that
row 3 and A6 are tower-neutral in shape.

**WHY NOT the other eleven rows.** Rows A, B, C3, C4, C5, C6 are elementarity,
the collapse, Σ₀ absoluteness, the Σ₁ transfer and ordinal bookkeeping; none
consumes an injection between the small types of two ordinals. Rows C1 and C2
are the level-hood certificate, which is the Def-tower engine and not cardinal
arithmetic. Rows D and G are the definable well-order. Row E is the hull
counting `|ℒ_X| = max(|X|, ω)`, which is over the HULL and not over an ordinal
successor; A6 would serve the `max(·, ω)` normalization only after the hull
step, which is not what either block states.

**Does the literature state either step? NO. MEASURED** over the digest: II.5
never writes a successor absorption or an ordinal inclusion as a step. It
invokes 1.1(vii) as a finished fact (`:413-415`). Both blocks are therefore
the project's own internalization of what Devlin leaves to the metatheory,
which is the same finding `[LJ-1.279]` section 10 recorded for row 1's
composition. The consequence for a brief: no literature page prices these two
blocks, so the only admissible prices are this project's own measurements.

## 13. WORKING TREE, AS THIS REPORT DESCRIBES IT

My writes, and nothing else:

- `src/L/Absorption.lagda.md`, NEW, the A6 master.
- `src/L/InjChain.lagda.md`, MODIFIED: the shared `StageBound` added at `:75`,
  `PairBound` rewritten over it at `:276`, row 3 added at `:436-607`, three
  import and module lines added, the `Lset` import dropped at `:21`.
- `agents/tasks/LJ-1-176/ProbeLJ1176A.agda`, MODIFIED: one import re-sited.
- `agents/tasks/LJ-1-217/ProbeLJ1217A.agda`, MODIFIED: one import re-sited.
- `agents/tasks/LJ-1-284/`, NEW: this report, the pinned brief `LJ-1.284.md`,
  and `ReRun.agda`.

No commit, no push, no `git checkout .`, no stash, no reset, no clean. No
`make check`; the orchestrator runs it.
