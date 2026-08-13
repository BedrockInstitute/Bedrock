# LJ-1.152 report: can two L-graphs compose without a second `hasReplacementL`?

**STATUS: COMPLETE against the abort criterion.** Two named gaps remain and
section 12 states both. Written incrementally (C-22). The machine was
restarted by the owner after the last run in section 4; no run was cut off
and no Agda process was killed.

## 0. LEAD FINDING

**GO, against the criterion fixed before the run.**

**Two L-graphs compose with ONE `hasSeparationL` and NO replacement at all.
The whole composite elaborates in 2.50 s cold, at load 4.4, over four runs
with the warm-up discarded. The criterion asked for "nearer 3.51 than 254".
2.50 s is BELOW the 3.51 s that `[LJ-1.136]` charged to the four conjuncts
alone.**

`agents/tasks/LJ-1-152/ProbeLJ1152E.agda`, `--safe`, exit 0, zero postulates,
zero holes, zero heap walls. It composes two L-graphs, proves all four
conjuncts for the composite, reads the composite back as an honest injection,
and instantiates the whole interface at `[LJ-1.134]`'s concrete graph, where
the composite is shown INHABITED.

**A SECOND FINDING, and it closes a question the brief did not ask.** The
254 s is the replacement's OWN elaboration. Sealing it does not cure it.
Probe C is `src/ProbeLJ1136A.agda` verbatim; Probe D is Probe C with `G` and
`G-spec` sealed `opaque`, one change and nothing else. **C ran 260.37 and
270.53 s; D ran 247.60 s. The gap is inside the machine's own spread on the
identical file. MEASURED: the seal is not the cure here.** So composition is
not one cure among several. It is the only one measured to work.

**A THIRD FINDING, and it is the ratio.** One `hasSeparationL` costs **under
0.1 s, below this machine's resolution**. One `hasReplacementL` costs **about
259 to 269 s**. MEASURED, both, at this site today. **A factor of at least
2,500.**

## 1. THE ABORT CRITERION, restated before the run (D-1)

Copied from the brief, `agents/tasks/LJ-1-152/LJ-1.152.md:51-61`, and fixed
before the first line of probe code:

- **GO** if the composite elaborates **without a second `hasReplacementL`**,
  and its cold seconds are nearer 3.51 than 254.
- **NO-GO** if composition needs its own replacement. A5 is then six
  replacements and about 25 minutes, and the price is a DD24 question.
- **STOP** if the composite does not elaborate at all. That is a wall and it
  re-prices A-prime.

A second criterion was fixed before Probe B, inside the file
(`agents/tasks/LJ-1-152/ProbeLJ1152B.agda:17-24`): **if one `hasSeparationL`
costs on the order of the 250 s replacement, composition by separation buys
nothing whatever the mathematics says, and the task answers NO-GO on seconds
with a 30-line file.** That criterion was written before Probe B ran and it
is why separation was priced alone and first. D-1: the cheapest step that
could have ended the task.

**VERDICT: GO on both.**

## 2. MACHINE STATE, and it was NOT quiet throughout

**16 cores, 64 GB, macOS 25.5.0. No sibling Agda process ran at any point.**
`[LJ-1.151]`'s probes were not running; `_build/tools/agda-watchdog.sh` was
the only other project process. **ONE agda process at a time, always
`GHCRTS="-A64m -I0 -M8g"`, cap never raised.**

**The machine was contended by the operating system, not by the project.**
Load at 20:35 was 6.32. At 20:45, during the first control run, three
`siriactionsd` processes and `WindowServer` drove the one-minute load average
to 208. MEASURED, `ps aux` at 20:46: three `siriactionsd` at 70 to 170
percent each, `WindowServer` at 94 percent.

**Consequence, stated plainly.** The first control run carries a load spike
that the rest do not. It is reported anyway, with its load, and the control
was RE-RUN after the spike cleared. **Every figure below carries the load it
was taken at.** `[LJ-1.148]`'s fixed first-run penalty of about 0.9 s per
series reproduced exactly: Probe F's first run was 1.88 s and its next three
were 0.94 to 1.01 s. **Every series below discards its warm-up.**

## 3. THE DESIGN, and why it is the cheapest decisive one

### 3.1 Separation was priced FIRST, alone

`[LJ-1.136]` section 17.5 proposed composing "by separation over a product
already in L". **If separation cost what replacement costs, the cure bought
nothing.** So `ProbeLJ1152B.agda` instantiates ONE `hasSeparationL` and
nothing else, and `ProbeLJ1152F.agda` is the same file with the separation
removed. The difference is one separation and nothing else.

### 3.2 The bound, and NO replacement builds it

Separation carves a subset out of a set already in L. The composite lives in
the product of the two end sets, and **no delivered field gives that
product**. A STAGE gives it instead:

- the composite's pairs form a family indexed by `⟪ fst D ⟫ × ⟪ fst C ⟫`,
  which is SMALL;
- `boundingOrd` bounds any small family of ordinals
  (`src/L/Ordinal.lagda.md:154-155`);
- a stage is an element of L (`src/L/Axioms/Basic.lagda.md:160-161`).

**This is `hasPowerL`'s own device** (`src/L/Axioms/Power.lagda.md:143-190`)
**with the resizing dropped**, because a pair of L-elements is constructible
by construction and needs no resized statement. `hasPowerL` needs the
resizing because "this subset is constructible" lives one universe too high;
a pair built by `prʟ` carries its own constructibility.
`agents/tasks/LJ-1-152/ProbeLJ1152E.agda:195-249`.

### 3.3 The one piece that was not delivered, and it is 20 lines

`appAt f x y` reads the graph out of the CONTEXT
(`src/L/Coding/Model.lagda.md:160-161`). **Separation takes a formula of ONE
place, so a composite condition cannot keep two graphs in the context.** The
probe adds `appC`, the same reader with the graph as a delivered CONSTANT
term, and its adequacy proof is `appAt-adequate` (`:163-187`) with the
constant in place of the lookup. The delivered precedent for a constant is
`subFo` (`src/L/Axioms/Power.lagda.md:108`).

**20 non-comment lines, and it is the only new object-language content the
composition needed.** `agents/tasks/LJ-1-152/ProbeLJ1152E.agda:94-118`.

## 4. THE MEASUREMENTS

**All runs cold: the interface file was deleted before every run. All under
`GHCRTS="-A64m -I0 -M8g"`. Load is the one-minute average at the start of the
run.**

### 4.1 The cheap series, four runs each, warm-up discarded

| probe | what it is | runs kept | seconds | load |
|---|---|---:|---|---:|
| `ProbeLJ1152F` | Probe B's control, separation removed | 3 of 4 | 0.96, 1.01, 0.94 | 4.34 |
| `ProbeLJ1152B` | **one `hasSeparationL`** and nothing else | 3 of 4 | 0.92, 0.91, 0.89 | 4.51 |
| `ProbeLJ1152A` | ProbeLJ1136A's import block, no body | 3 of 4 | 1.16, 1.21, 1.18 | 4.56 |
| `ProbeLJ1152E` | **THE COMPOSITION, whole file** | 3 of 4 | 2.50, 2.52, 2.49 | 4.4 |

**ONE `hasSeparationL` COSTS UNDER 0.1 s.** B minus F is 0.91 minus 0.97,
which is negative. **MEASURED: the separation is below this machine's
resolution.** The honest statement is an upper bound: under 0.1 s.

**The import baseline is 1.18 s.** `[LJ-1.136]`'s bisection never subtracted
it (`agents/tasks/LJ-1-136/lj-1.136-report.md:1063-1069`), so its 250.71 s
was an upper bound on the replacement. **The correction is 1.2 s on 250. The
bisection stands.**

### 4.2 The expensive series, and the seal that did not cure

| probe | what it is | seconds | load at start | load at end |
|---|---|---:|---:|---:|
| `ProbeLJ1152C` run 1 | `src/ProbeLJ1136A.agda` VERBATIM | 260.37 | 4.20 | **173.67** |
| `ProbeLJ1152C` run 2 | same file, after the spike cleared | 270.53 | 4.00 | 18.30 |
| `ProbeLJ1152D` | **same file, `G` and `G-spec` sealed `opaque`** | 247.60 | 7.95 | 4.90 |
| `[LJ-1.136]`'s own figure | same file, 2026-08-13 | 254.22 | 5.83 | n/a |

**MEASURED: the identical file ran 254.22, 260.37 and 270.53 s on three
occasions today. The spread on ONE file is 6.4 percent. The seal moved the
figure by 4.9 percent against the mean of the three. The seal is inside the
noise and it is NOT the cure.**

**So the 254 s is the replacement's own elaboration, not the conversion cost
of letting consumers look inside it.** That is the opposite of what
`[LJ-1.136]` measured for `injOf`, where a seal turned a heap exhaustion at
98.42 s into 1.27 s green (report section 16.4). **A measured cure did not
transfer, and P-l is why I measured it rather than assumed it.**

### 4.3 The two numbers the task turns on

| | seconds | basis |
|---|---:|---|
| one `hasReplacementL`, net of imports | **259 to 269** | C minus A, both runs of C |
| one `hasSeparationL`, net of imports | **under 0.1** | B minus F, below resolution |
| **the whole composition**, four conjuncts and readback and witness | **2.50** | Probe E, 3 runs |

**Ratio: at least 2,500 to 1. MEASURED, at this site, today.**

### 4.4 The lines

Counted as non-blank non-comment lines in the probe file, the ledger's
in-fence caliber applied to a `.agda` probe.

| part of `ProbeLJ1152E.agda` | lines | what it is |
|---|---:|---|
| header and imports | 37 | |
| Part 1, `appC` and its adequacy | 20 | the only new object-language content |
| Part 2, `compFo` and both readings | 41 | the composite condition |
| Part 3, `PairBound` | 38 | the bound, no replacement |
| Part 4, `Comp`, four conjuncts and readback | 99 | the composite itself |
| Part 5, the C-38 witness | 16 | |
| **whole file** | **251** | |

**The composer proper is Parts 1 to 4: 198 lines.** Parts 1 to 3 are
one-time content that every later composition reuses; **Part 4 alone, 99
lines, is what a second composition site costs.**

## 5. A5 RE-PRICED

### 5.1 Which of the six compose and which must build

`[LJ-1.136]` section 3.1 lists six objects the chain builds
(`agents/tasks/LJ-1-136/lj-1.136-report.md:206-215`).

| built object | verdict | classification |
|---|---|---|
| **composition of two injections** | **COMPOSES.** One separation, 2.50 s | **MEASURED**, Probe E |
| `Incl`, the inclusion `β ↪ κ` | carves by separation from a stage, no replacement | **INFERRED** |
| `ShiftAbs` / `Shiftω`, `sucV γ ↪ γ` | carves by separation from a stage | **INFERRED** |
| `pairω`, the pairing on `ω` | carves by separation from a stage | **INFERRED** |
| the column square `pair` | carves by separation from a stage | **INFERRED** |
| the `CSB` bijection | **UNPRICED. I did not price it and I will not guess it** | **NOT MEASURED** |

**Why the four inferences are short steps and still inferences.** Probe E's
Part 3 shows the device: any graph whose pairs are indexed by a SMALL type
has a stage that bounds it, and a stage is an element of L. Each of the four
is a graph of that kind. **But P-l says a measured cure does not transfer by
analogy, and each of the four has its own 1-ary description to write. The
device is measured; the four instances are not.**

**Why CSB is different and why I stopped.** CSB's graph is not defined from
the two input graphs by a first-order condition on pairs. It is defined by a
back-and-forth on chains, which is a recursion. **Whether that recursion has
a 1-ary description over the two graphs is an open question I did not open.**
`[LJ-1.136]` already measured that CSB exists nowhere in `src/`
(`agents/tasks/LJ-1-136/lj-1.136-report.md:217-219`), so nothing delivered
settles it either.

### 5.2 The seconds, restated

`[LJ-1.136]` INFERRED A5 at "six replacements, about 25 minutes"
(`agents/tasks/LJ-1-136/lj-1.136-report.md:1117-1121`) and marked the
multiplication as not a price.

**That inference is now refuted at its own weakest link. MEASURED: one of the
six is not a replacement at all, and it costs 2.50 s rather than 254.**

**What I will state as a price, and it is one number with its basis (DD8):**
**A5's replacement count falls from six to at most one, and that one is
CSB.** The basis is Probe E for composition and Probe E's Part 3 device for
the four carvings. **I will not multiply 2.50 by five.** The honest form is:
**the 25-minute figure has lost its premise, and A5's seconds are UNPRICED
again rather than priced low.** What re-prices it is five short probes, one
per remaining object, and the CSB question first because it is the only one
that could put a replacement back.

### 5.3 The one measurement I would run next

**Carve the IDENTITY graph by separation instead of replacement.** Probe E's
Part 3 already bounds the pairs of any two sets; the identity graph on `a` is
the pairs `<x,x>` for `x` in `a`, and the 1-ary description is shorter than
`compFo`. **If that lands near 2.5 s, then `[LJ-1.136]`'s 254 s construction
was never necessary and the whole write direction is cheap.** One file, the
shape of Probe E's Parts 3 and 4, and it is the highest-value hour left in
A5. **I name it rather than guess it (C-34); the wall that stopped me is
budget and a machine restart, not mathematics.**

## 6. SEALS, and what P-y said

**ZERO heap walls. No run exhausted the 8g heap at any point. The cap was
never raised.** MEASURED, six probe files, sixteen runs.

**Three seals are in Probe E, and all three were applied PRE-EMPTIVELY, on
the brief's instruction, before any wall appeared.**

| seal | site | why |
|---|---|---|
| `β`, `oβ`, `bnd`, `below` | `ProbeLJ1152E.agda:213-249` | the bound is an atom to every consumer |
| `K`, `K-spec` | `:276-284` | the separation is an atom to the four conjuncts |
| `compFun`, `compFun-inj` | `:379-386` | `[LJ-1.136]`'s `injOf` pattern exactly |

**P-y prices a seal by the definitions that look INSIDE, not the ones that
name it. Counted:**

- `PairBound`'s block: **ONE** definition looks inside, `below`. Everything
  else names `bnd` and never opens it.
- `K`'s block: **ONE**, `K-spec`, whose own type names `K`.
- `compFun`'s block: **ZERO**. Nothing looks inside.

**The seal's whole measured cost was two type signatures.** Agda never infers
a type inside an `opaque` block, so the two `where`-bound fibres in `below`
had to be named. That was the only error the seal produced, and the file was
green on the next run. `ProbeLJ1152E.agda:237-241`.

**THE HONEST NEGATIVE, and I mark it. NOT MEASURED: whether removing the
three seals would exhaust the heap.** I sealed first and never ran the
unsealed variant. `[LJ-1.136]` measured that an unsealed `Small` application
exhausts an 8g heap, and Probe E applies `Small` once
(`ProbeLJ1152E.agda:376-377`), so the third seal is the one with delivered
evidence behind it. **The first two rest on the brief's instruction, not on a
measurement of mine.** The run that would settle it is 2.5 s.

## 7. DD4, ANSWERED AS THE RULE REQUIRES

**Maximize the code the two proofs share, and write it generic. No stop-line
made me write fixed.**

**Every one of the four parts is a FUNCTION or a parameterized module over
its data, not a module applied per site.** That is P-w, and P-w is the
difference `[LJ-1.136]` measured between an exhausted heap and two seconds.

| part | what it is generic in | shareable? |
|---|---|---|
| `appC` | the graph, as a plain argument of type `S` | **YES**, verbatim |
| `compFo` and `CompFo` | both graphs | **YES**, verbatim |
| `PairBound` | both end sets | **YES**, verbatim |
| `Comp` | five sets and eight facts, all parameters | **YES**, verbatim |

**Is the composer template content both towers use? YES in shape, NOT YET in
letter, and the gap is exactly two names.** Probe E imports L's own
`hasSeparationL` (`src/L/Axioms/Full.lagda.md:144`) and L's stage device
(`LsetS`, `stage`, `boundingOrd`). **Nothing else in the file knows it is
about L.** The four conjuncts, the composite condition, the pair bound and
the readback are all statements about an arbitrary model with a separation
field and a stage hierarchy.

**The concrete recommendation, and it costs nothing to take now.** When A5
lands in a master, take the separation field and the stage-bound device as
MODULE PARAMETERS rather than imports. Then the J tower re-instantiates the
same file with J's separation field and J's stages, and the shared code is
the whole composer rather than its shape. **Written fixed, it would be 198
lines the J tower has to write again.**

## 8. THE NEGATIVES, EACH CLASSIFIED

- **MEASURED. Composition needs no `hasReplacementL`.** The string
  `hasReplacementL` appears in `ProbeLJ1152E.agda` only inside comments, four
  times, and the file is green with `--safe` and exit 0.
- **MEASURED. Sealing the replacement does not cure its 254 s.** Probe D
  against Probe C, one change, 247.60 against 260.37 and 270.53.
- **MEASURED. One `hasSeparationL` is below this machine's resolution**, so
  the cost is bounded above by 0.1 s and not resolved further.
- **MEASURED. No delivered field gives the product of two L-sets.**
  `hasSeparationL` and `hasReplacementL` are the model's only two
  comprehension fields (`src/L/Axioms/Full.lagda.md:350`), and no `prodL`,
  `productL` or `hasProduct` exists anywhere in `src/`. Zero hits.
- **MEASURED. `appAt` cannot serve a one-place formula.** It takes the graph
  from the context (`src/L/Coding/Model.lagda.md:160-161`), and separation's
  formula has one place. That is why `appC` exists.
- **MEASURED. Zero heap exhaustions across sixteen runs at the 8g cap.**
- **INFERRED. Four of the remaining five built objects carve by separation.**
  The device is measured; the four instances are not. P-l.
- **NOT MEASURED. Whether CSB's graph has a one-place description.** It is
  the only object that could put a replacement back into A5.
- **NOT MEASURED. Whether Probe E's three seals were necessary.** Sealed
  pre-emptively; the unsealed variant was never run.
- **NOT MEASURED. Peak heap for any run.** No exhaustion is not a heap
  figure.

## 9. LITERATURE (DD18)

**Nothing in the literature governs elaboration cost.** That is one line and
it is the whole of it: Devlin, Jech and Kunen price proofs in pages, and no
source prices a cubical Agda elaboration.

**Does Devlin's square-law argument need six separate constructions or reuse
one?** **It reuses one.** The Gödel pairing on ordinals is defined once, and
the square law is proved by induction on that one ordering; the injections
that appear in the induction steps are COMPOSITES of that one pairing with
order isomorphisms and inclusions, not six independent constructions.
**Devlin never builds six objects because in an informal proof a composite
costs nothing to name.** The six appear in `[LJ-1.136]`'s table because a
formal chain must EXHIBIT each composite as an object of the model, and that
is exactly the cost Probe E removes. **CAUTION: this is my reading of the
standard argument, not a citation I verified against a text in this
repository. `dev/literature/` was not consulted before the machine restart.**

## 10. ARCHIVE USED (DD18)

- `agents/tasks/LJ-1-136/lj-1.136-report.md:1125-1140`, section 17.5, which
  states this measurement. **Taken: the whole task, and its framing.**
- `agents/tasks/LJ-1-136/lj-1.136-report.md:1057-1075`, the 254.22 s figure
  and the free bisection. **Taken: the control's target, and the fact that
  the bisection never subtracted imports.**
- `agents/tasks/LJ-1-136/lj-1.136-report.md:954-990`, the heap-wall table.
  **Taken: the seal discipline, applied pre-emptively at three sites.**
- `agents/tasks/LJ-1-136/lj-1.136-report.md:197-224`, section 3.1's six
  built objects. **Taken: the table re-priced in section 5.1.**
- `src/ProbeLJ1136A.agda:1-170`, read WHOLE. **Taken: copied verbatim as
  Probe C, the control.**
- `src/ProbeLJ1136B.agda:129-170`, the `injOf` seal and `agree-generic`.
  **Taken: the seal pattern for `compFun`, and the private-module shape.**
- `src/ProbeLJ1134A.agda:299-329`, `module Small`. **Taken: the readback,
  used unchanged.**
- `src/ProbeLJ1134A.agda:190-291`, `module Concrete`. **Taken: the C-38
  witness graph.**
- `src/L/Axioms/Power.lagda.md:143-190`, `module Bound` and `hasPowerL`.
  **Taken: the stage-bound device, with the resizing dropped.**
- `src/L/Axioms/Full.lagda.md:144-170`, `hasSeparationL`, and `:277-330`,
  `hasReplacementL`. **Taken: the two fields, and why one is cheap.**
- `src/L/Coding/Model.lagda.md:160-187`, `appAt` and its adequacy. **Taken:
  the proof, adapted verbatim to a constant.**
- `src/L/Coding/Model.lagda.md:586-636`, `tagAtL`. **Taken: the idiom for
  reading a nested object-language existential.**
- `src/L/Ordinal.lagda.md:154-160`, `boundingOrd`. **Taken: the bound.**
- `dev/LESSONS.md`, P-l, P-w, P-y, C-12, C-22, D-1, C-38 as extended, read
  through `scripts/rules.py --for probe`.

**`archive/dev/TASKS-archived.md`, `JOURNAL-archived.md`,
`DECISIONS-archived.md` and `STATUS-archived.md` were NOT read.** The task is
a measurement of today's tree under today's rules, and the retired route has
no `hasSeparationL`. **I record the omission rather than claim a survey.**

## 11. WORKING TREE, as my report describes it

**Seven new files, all in `agents/tasks/LJ-1-152/`. No master touched. No
file under `src/` touched. Nothing committed, nothing pushed. No Agda process
was killed and none is running.**

| file | lines, non-comment | state |
|---|---:|---|
| `ProbeLJ1152A.agda` | 30 | green, exit 0 |
| `ProbeLJ1152B.agda` | 27 | green, exit 0 |
| `ProbeLJ1152C.agda` | 98 | green, exit 0 |
| `ProbeLJ1152D.agda` | 99 | green, exit 0 |
| `ProbeLJ1152E.agda` | **251** | green, exit 0, `--safe` |
| `ProbeLJ1152F.agda` | 25 | green, exit 0 |
| `lj-1.152-report.md` | n/a | this file |

**Interface files under `_build/` were deleted repeatedly to force cold runs.
That is a build directory and nothing tracked changed.**

## 12. WHAT IS NOT DONE, named rather than hidden

1. **`.venv/bin/python scripts/ledger.py` was NOT used for the line counts.**
   The counts in sections 4.4 and 11 are `grep -c` of non-blank non-comment
   lines, which is the fence caliber applied by hand to a `.agda` file.
   **They are consistent within this report and they are not ledger figures.**
2. The five measurements named in sections 5.1 and 5.3 are not run.
3. The unsealed variant of Probe E is not run, so section 6's first two seals
   are unpriced.
4. `dev/literature/` was not consulted, so section 9's second paragraph is a
   reading and says so.

**What IS run, after the last Agda run and before this line:**
`scripts/lint-prose.py --check` on this report, exit 0;
`scripts/lint-agda.py --check` on all six probes, exit 0 on each;
`scripts/check-probes.py --check`, clean over 1,645 tracked files.
**`make check` was NOT run; the brief reserves it to the orchestrator.**

**None of the four gaps touches the abort criterion. GO stands on Probe E
alone.**
