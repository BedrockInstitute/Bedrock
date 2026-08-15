# [LJ-1.292] report: sweep `Key.lagda.md` for the mixed spelling `[LJ-1.287]` flagged

STATUS: COMPLETE against the abort criterion's FOURTH branch, with the second
branch's number attached by measurement. Every negative is marked MEASURED or
INFERRED, in those words. ASD-STE100 applies. Written incrementally (C-22).

Machine at start: load 4.64 4.57 5.06 at 16:46. `ps aux | grep -c "[a]gda"`
returned 2 at start, MEASURED. Both processes belonged to the sibling
`[LJ-1.289]`, mid-series on `EnvSupply.lagda.md`. None of them was mine. I ran
ONE agda process at a time, `GHCRTS="-A64m -I0 -M8g"`, cap never raised. Every
figure carries its own load pair.

## LEAD

**`Key.lagda.md` IS ALREADY CHEAP. Cold total 3,974 ms by agda's own
`--profile=definitions` Total**, wall 4.95 s, load 4.77 to 4.55
(`agents/tasks/LJ-1-292/runs/k1.out:2`). Three kept cold runs mean **4.84 s
wall** (4.95, 5.23, 4.34). `[LJ-1.263]` had already timed this master cold at
5.17 s (`agents/tasks/LJ-1-263/lj-1.263-report.md:29`), and commit `0abbcaa`,
that task's landing, is the file's last commit, so the two figures corroborate
each other on the same bytes.

**The profile's top charge is NOT the flagged site.** It is
`KeyOver._.pair∈` at `src/L/Coding/Key.lagda.md:118-119`, **261 ms, 6.6
percent**, a bounded-formula membership climb with no `sucIter` mismatch in
it. **`Land.σ∈α` at `:427-429`, the definition the brief names, IS NOT CHARGED
AT ALL. MEASURED:** it does not appear in the profile, so its cost is below
the profiler's reporting threshold. The whole `Land` module shows 138 ms
across four charged definitions.

**AND THE BISECT SAYS WHY, WITH NUMBERS.** The shape that cost 476 s at the
first site is a FULL EXPLICIT `sucV` CHAIN against a NUMERAL `sucIter`
ITERATE. This master never writes that shape. Every conversion at the site
compares `sucV (sucIter (n-1) σ)` against `sucIter n σ`, ONE `sucV` directly
over an iterate. The bisect prices both spellings under the bare membership:

| spelling at the conversion | depth 1 | depth 2 | depth 3 | depth 4 |
|---|---:|---:|---:|---:|
| full chain against iterate | not charged | 219 ms | 9,286 ms | **419,218 ms** |
| one `sucV` over the iterate | not charged | not charged | not charged | **not charged** |

**So there is no cure to fund and NO TREATED ARM.** The clock of record is
agda's own `--profile` Total, cross-checked by `time.time()` wall.
**DD4, axis AC-against-GCH:** `Key.lagda.md` is in NEITHER closure, MEASURED,
so its seconds are paid zero times on that axis, and the profile's one charged
wing, `KeyOver`, is tower-neutral by construction.

## 0. THE CLOCK

Agda's own `--profile=definitions` Total is the figure of record. The wall
figure from `measure.sh` uses `time.time()`, the wall-clock epoch, comparable
across processes. `time.monotonic()` is NOT comparable on this machine
(`[LJ-1.283]` section 8). The harness is `[LJ-1.287]`'s `measure.sh` copied
with the directory changed.

## 1. PREMISES, VERIFIED OR REFUTED

| the brief's premise | verdict |
|---|---|
| `Key.lagda.md:424-429` carries `sucIter` at depths 1 to 3 | **VERIFIED by my own read (C-44).** `α = sucIter 3 σ` at `:424`, and `σ∈α` at `:427-429` |
| nobody has profiled `Key.lagda.md` | **VERIFIED with one refinement, MEASURED by grep over the reports.** No report holds a `--profile=definitions` breakdown of this master. `[LJ-1.263]` DID time it cold, 5.17 s real and 4.17 s user at `lj-1.263-report.md:29`, so a total was on record and this task was cheaper than a blind profile, as the brief said to check |
| the suppliers are `∈sucV-inl` and `self∈sucV` | **VERIFIED.** `src/V/Model.lagda.md:230-233` and `:236-239` |
| `sucIter` climbs by one `sucV` per numeral step | **VERIFIED by my own read.** `src/L/Ordinal/StageArith.lagda.md:33-35` |
| `Lset` is opaque upstream | **VERIFIED by my own read.** `src/L/Constructible.lagda.md:221-223` |
| the cure at the first site was to climb by a module parameter | **MOOT, INFERRED from the absence of a charge.** Nothing here needs curing, so the ingredient question never opened |
| the cost may be small or absent (P-l) | **CONFIRMED. MEASURED.** Sections 2 and 3 |
| `Key.lagda.md` is in the GCH closure | **REFUTED. MEASURED.** My own import walk reproduces the ledger's closure counts exactly, 73 AC masters, 51 GCH masters, 44 shared, and places `Key.lagda.md` in NEITHER. Only `KeyRead.lagda.md` and `EnvSupply.lagda.md` import it in `src/`, and neither sits under either root. The 39.1 percent shared figure is real, `scripts/ledger.py --reuse`, but this master is outside it |
| the brief's `I-5` is the probes-never-in-`src/` rule | **NOT AS STATED.** `dev/LESSONS.md:1213` styles `I-5` as truncation-branch types. The probe-location rule is D-1's standing rule, `dev/LESSONS.md:1062-1070`. The substance is unchanged and I obeyed it: everything I wrote lives in `agents/tasks/LJ-1-292/` |

## 2. THE CONTROL AND THE PROFILE

`ControlKey.lagda.md` is `src/L/Coding/Key.lagda.md` copied with the module
renamed to `LJ-1-292.ControlKey`. `diff` after the name substitution is EMPTY,
so the copy is the master verbatim, 690 non-blank in-fence lines. The copy
reuses the shared `_build` interfaces of the master's dependencies and writes
only its own. So the sibling's warm interfaces, including `L.Coding.Key`'s
own, were never touched. Running the master in place would have rebuilt that
interface under the sibling's feet. I did not.

Each run is cold in the module and warm in its dependencies.

| run | wall s | exit | load before to after | agda Total |
|---|---:|---:|---|---:|
| k1, profiled | **4.95** | 0 | 4.77 to 4.55 | **3,974 ms** |
| c2 | 5.23 | 0 | 4.91 to 5.16 | not profiled |
| c3 | 4.34 | 0 | 5.16 to 4.91 | not profiled |

**THE PROFILE, `agents/tasks/LJ-1-292/runs/k1.out`. MEASURED.**

| definition | site | ms | share |
|---|---|---:|---:|
| Miscellaneous | | 2,417 | 60.8 percent |
| **`KeyOver._.pair∈`** | `src/L/Coding/Key.lagda.md:118-119` | **261** | **6.6** |
| `Δ₀-prAtLK` | `:62-63` | 125 | 3.1 |
| `Carve.bddEnvFoB` | `:258-285` | 83 | |
| `Join.outSet` | `:286-380` | 69 | |
| `Join._.prs` | `:375-380` | 63 | |
| `Land.out` | `:452-460` | 58 | |
| `FiniteSup._.memTr` | `:615-772` | 54 | |
| `Land.into` | `:462-476` | 54 | |
| `Join.slots` | `:286-380` | 49 | |
| `Land.landed` | `:478-479` | 14 | |
| `Land.fibL` | `:449-451` | 12 | |
| **`Land.σ∈α`** | **`:427-429`** | **not charged** | |

"Not charged" means the definition does not appear in the profile at all, so
its cost is below the profiler's own reporting threshold. `Land.hBα` and
`Land.hdα`, the site's two neighbours, are also not charged. **MEASURED.**

## 3. THE MECHANISM, and it is a spelling the master never writes

### 3.1 THE BISECT, one run, eight definitions

`Bisect.lagda.md`, 62 non-blank in-fence lines, `--profile=definitions`, one
run, wall **857.99 s**, exit 0, load 5.59 to 5.36, agda Total **856,881 ms**
(`agents/tasks/LJ-1-292/runs/b1.out`).

| name | what it isolates | ms | share |
|---|---|---:|---:|
| `w4` | full chain against iterate, depth 4, BARE membership, no `Lset` | **419,218** | 48.9 |
| `l4` | `[LJ-1.287]`'s `v4` VERBATIM, the anchor, `Lset` wrapper on | **418,031** | 48.8 |
| `s3` | the site's member, base and depth, full chain, `p = p` | 9,330 | 1.1 |
| `w3` | full chain against iterate, depth 3 | 9,286 | 1.1 |
| `w2` | full chain against iterate, depth 2 | 219 | |
| `w1`, `s0`, `m3` | see below | **not charged** | |
| Miscellaneous | | 794 | |

- **THE ANCHOR HOLDS. MEASURED.** `l4` reproduces `[LJ-1.287]`'s 438,043 ms
  within 4.6 percent under a different load regime. My harness sees the
  disease, so the negatives below are not instrument blindness.
- **THE `Lset` WRAPPER IS NOT REQUIRED. MEASURED.** `w4` is `l4` minus the
  `Lset`, and it costs the same, 419,218 against 418,031 ms, 1.2 percent
  apart in one run. The disease lives in the bare membership too. The first
  site's cost was never about `Lset` opacity.
- **THE LADDER IS SUPER-LINEAR. MEASURED.** Depth 2 to 3 multiplies by 42,
  depth 3 to 4 by 45. R-40's curve shape holds here with new constants.
- **`s0`, THE SITE VERBATIM, IS NOT CHARGED. MEASURED.** The two applications
  of `:428-429` elaborate below the threshold, in the same run that charges
  `s3` 9,330 ms. `s3` is the site's own conversion with the chain spelled out
  in full, and it is the ONLY difference.
- **`m3`, the matched-spelling control, is not charged. MEASURED.**

### 3.2 THE SECOND BISECT, and it names the discriminator

The visible difference between `s0` and `s3` is the spelling of the supplier
side. The site's conversions all put ONE `sucV` directly over an iterate:
`sucV (sucIter 2 σ)` against `sucIter 3 σ` at the outer step,
`sucV (sucIter 1 σ)` against `sucIter 2 σ` at the middle step, and `sucV σ`
against `sucIter 1 σ` at the inner step. `s3` instead spells the full chain
`sucV (sucV (sucV σ))`. `Bisect2.lagda.md`, 34 in-fence lines, one run, wall
0.96 s, exit 0, load 6.00 flat, agda Total 845 ms
(`agents/tasks/LJ-1-292/runs/b2.out`):

| name | the conversion | ms |
|---|---|---:|
| `d2` | `sucV (sucIter 1 σ)` against `sucIter 2 σ` | **not charged** |
| `d3` | `sucV (sucIter 2 σ)` against `sucIter 3 σ`, the site's own | **not charged** |
| `d4` | `sucV (sucIter 3 δ)` against `sucIter 4 δ` | **not charged** |

**`d4` AGAINST `w4` IS THE CONTROLLED PAIR. MEASURED.** Same member, same
base, same depth, same bare membership, one run each. The types differ in the
spelling of the domain level alone. Full chain: 419,218 ms. One `sucV` over
the iterate: not charged. **The costly shape is precisely a fully explicit
`sucV` chain against a numeral iterate.**

### 3.3 WHY ONE DEEP IS FREE. INFERRED.

One delta step unfolds `sucIter n σ` into `sucV (sucIter (n-1) σ)`. The two
sides then agree syntactically, head and argument, so the checker closes
without opening the `sucV` payload. A full chain instead agrees with the
unfolded iterate only at the head, and the argument comparison repeats down
the chain. Why THAT comparison costs super-linearly stays INFERRED, on
`[LJ-1.287]` section 2.5's reading: the payload comparison builds the deep
monic presentation on both sides. I did not read Agda's conversion checker,
and neither did `[LJ-1.287]`. The discrimination above is measured; the
internal path is not.

### 3.4 WHAT THIS DOES TO THE LAW `[LJ-1.287]` PROPOSED

`[LJ-1.287]` section 9 proposed: never let a supplier state one spelling and
a consumer the other. **The measurement here refines that to a sharper law.**
A `sucV` directly over an iterate IS a mixed spelling, and it is FREE at every
depth measured. What costs is the FULL CHAIN against the iterate. So the rule
for a build brief becomes: **never spell a level as an explicit `sucV` chain
of depth two or more while the other side of the conversion carries the
numeral iterate.** Climb by `∈sucV-inl` over the iterate, as this master's
`fromω` already does at `src/L/Coding/Key.lagda.md:95-103`, one `sucV` per
step, and every conversion the climb forces is one deep. That climb is
charged 19 ms, MEASURED, at `runs/k1.out`.

The orchestrator assigns any ID. The ladder and the `w4` against `d4` pair
are the measurement.

## 4. THE TREATED ARM, OR WHY THERE IS NONE

**There is none, because the profile does not justify one.** The definition
the brief names is not charged. The top charge in the whole master is 261 ms.
C-50: a candidate with no seconds behind it is a change for nothing. The
control stands at three kept cold runs, section 2. P-y never opened, because
no seal has a cost to move here.

## 5. DD4, WITH ITS AXIS

**AXIS NAMED (C-46): AC-against-GCH**, the axis `scripts/ledger.py` computes
from `ac_root` and `gch_root` at `dev/ledger.toml:170` and `:203`. It is not
Devlin's Def-against-J.

**`Key.lagda.md` IS IN NEITHER CLOSURE. MEASURED.** I walked the import graph
from both roots over `src/`. The walk reproduces the ledger's own counts
exactly, 73 AC masters, 51 GCH masters, 44 shared, so it is the ledger's
closure computation. It places `Key.lagda.md` outside both: only
`KeyRead.lagda.md` and `EnvSupply.lagda.md` import it in `src/`, and neither
reaches either root. The brief's premise that it sits in the GCH closure is
REFUTED, and with it the framing that this master's seconds are already paid
once on the axis. They are paid ZERO times today. This matches
`[LJ-1.287]`'s verdict for `EnvSupply.lagda.md`, the master that imports this
one.

**The one wing the profile charges, `KeyOver`, is tower-neutral by
construction.** The module takes `(T : S → S)` with five facts as parameters,
and the master's own comment says "Nothing here names a tower"
(`src/L/Coding/Key.lagda.md:78-81`). When a closure grows to include this
master, `pair∈`'s 261 ms are paid once, not per tower.

**My probe adds no shared code and cures nothing, so the 39.1 percent figure
does not move.** The finding of this task is a spelling law, which costs zero
lines in delivered masters: the delivered tree already spells the site the
free way.

## 6. THE ABORT CRITERION, ANSWERED BRANCH BY BRANCH

| branch fixed before the run | verdict |
|---|---|
| the shape is here and it costs | **DID NOT FIRE. MEASURED.** `σ∈α` is not charged. The costly spelling, full chain against iterate, is not written at `:424-429` |
| the shape is here and costs nearly nothing | **FIRED AS THE SUBSTANCE.** The weak mixed spelling is here and costs below the profiler's threshold, MEASURED. The number the branch asks for: the site verbatim elaborates inside the 845 ms of a run that prices three beside it, and the same conversion with the chain spelled out would cost 9,330 ms, so the free spelling is measured, not lucky |
| the seconds are somewhere else | **DID NOT FIRE.** The top charge is `KeyOver._.pair∈`, 261 ms of 3,974 ms. Nothing in the master carries seconds |
| **`Key.lagda.md` is already cheap** | **FIRED. THIS IS THE VERDICT.** Cold total 3,974 ms, corroborated by `[LJ-1.263]`'s 5.17 s on the same bytes. There is nothing to cure and the sweep closes |
| a wall | **DID NOT FIRE. MEASURED.** Longest run 857.99 s, exit 0, under the 30-minute line. No heap exhaustion, cap never raised |

## 7. THE SWEEP, AND WHAT THE PROJECT SHOULD DO WITH IT

C-42: this task measured ONE flagged site. The site is clean, and the reason
it is clean generalises better than the original flag did.

- **The costly shape is now measured precisely:** a full explicit `sucV`
  chain against a numeral iterate, with or without `Lset`, super-linear from
  depth 2. Any future sweep should grep for THAT, not for `sucIter` alone.
  `[LJ-1.287]`'s own sweep note at
  `agents/tasks/LJ-1-287/lj-1.287-report.md:402` flagged this file on the
  weak reading, `sucIter` beside `sucV`. The strong reading clears it.
- **The delivered tree's other known full-chain site was
  `EnvSupply.lagda.md:223`, and `[LJ-1.289]` is landing its cure now.**
  MEASURED count of further full-chain sites in `src/`: I did not sweep the
  whole tree, and I say so plainly. This task's scope was this master.
- **No change to any master is proposed.** The master already spells the site
  the free way, and its whole profile sums to 3,974 ms.

## ARCHIVE USED (DD18)

- **`agents/tasks/LJ-1-287/lj-1.287-report.md`, read WHOLE as the brief
  requires.** ONE line: `:402`, "`src/L/Coding/Key.lagda.md:424-429` CARRIES
  THE SHAPE. UNMEASURED." **TAKEN:** the flagged site, the bisect method, and
  the anchor definition `v4`, which I re-measured as `l4` rather than quoting.
  **NOT TAKEN:** its 438,043 ms as a price for this site. P-l forbids carrying
  it, and my `w4` shows the figure transfers only because the spelling, not
  the file, is the site.
- **`agents/tasks/LJ-1-263/lj-1.263-report.md`.** ONE line: `:29`, the
  `src/L/Coding/Key.lagda.md` row, cold 5.17 s real and 4.17 s user, exit 0.
  **TAKEN:** the recorded cold total, and the fact that commit `0abbcaa` is
  the file's last, so the figure describes the delivered bytes. It corroborates
  my control without a fourth run.
- **`archive/dev/TASKS-archived.md`, SHAPE ONLY and never a claim.** ONE
  line: `:189`, `[L3.32-T154]`, "FOUND, one wall: the depth-6 ordinal
  witness; cured 631 s to 59 s in harness." **TAKEN AS SHAPE:** a
  successor-depth wall is cured by restating the witness, never by sealing
  it. **WHAT WOULD NOT TRANSFER:** the 631 s and 59 s price a retired tree at
  depth 6 under a different head. P-l forbids carrying them. I carried none.

## LITERATURE USED (DD18)

Nothing in the literature governs elaboration cost.

## WORKING TREE, AS THIS REPORT DESCRIBES IT

Everything I wrote is in `agents/tasks/LJ-1-292/`:

- `LJ-1.292.md`, the pinned brief, written by the orchestrator before me.
- `lj-1.292-report.md`, this file.
- `ControlKey.lagda.md`, the control, the master verbatim with the module
  renamed. GREEN, exit 0, three cold runs.
- `Bisect.lagda.md`, eight definitions, the ladder and the anchor. GREEN,
  exit 0, 857.99 s.
- `Bisect2.lagda.md`, three one-deep conversions, the discriminator. GREEN,
  exit 0, 0.96 s.
- `measure.sh`, `timings.csv`, `runs/`.

No master edited. No `src/` path written. No `src/Everything.lagda.md`, no
`dev/PLAN.md`, no `dev/ledger.toml`, no `src/L/Choice/Name.lagda.md`, no
`src/L/Coding/EnvSupply.lagda.md`, whose sibling edit I never touched. No
commit, no push, no `git checkout .`, no stash, no reset, no clean. I did not
run `make check`. `scripts/lint-prose.py --check` and
`scripts/lint-agda.py --check` exit 0 on everything I wrote, and
`scripts/check-probes.py --check` is clean.

The tree moved around me while I ran: commits through `dae620c` landed
mid-session, including the sibling `[LJ-1.289]`'s cure. None of them is mine
and none touched `src/L/Coding/Key.lagda.md`, whose last commit remains
`0abbcaa` with an empty working-tree diff. So the control I copied at the
start matches the delivered master byte for byte at close. The untracked
paths `agents/tasks/LJ-1-223/` and `agents/tasks/LJ-1-290/` are not mine.
