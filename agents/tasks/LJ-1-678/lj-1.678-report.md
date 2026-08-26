# LJ-1.678 report: KValue, the adequate K both directions wait on

## HEAD
head_slot: coder
machine: shared
agda_tier: wide
task: LJ-1.678
obligation: agents/tasks/LJ-1-678/Probe678.agda::k-value
verdict: **GO.** `k-value` is `KValue.facts` at the probe-local
ω-block above a generic ordinal. Suc-closure and `∅∈λ` are terms.
The `HullStage` telescope is not taken.

The witness meter reads `0 UNRESOLVED of 1, 2.86 s, probe_red=False`
(`runs/meter-obligation.out:2`). The probe is green and carries no
hole (`runs/p-1.out`, `EXIT=0`, 2.14 s, peak 546,652,160 bytes).
W3 is green (`runs/w3-2.out`, `EXIT=0`, 1.12 s, peak 285,507,584
bytes).

Written as a skeleton before any Agda beyond the predecessor read
and filled as each answer landed (C-22). No commit, no push. I wrote
only inside `agents/tasks/LJ-1-678/`. Agda ran under the caliber the
program set on this pane, `GHCRTS="-A64m -I0 -M2g"`, the WIDE tier,
ONE Agda process at a time. I did not set `GHCRTS`. Nothing is
postulated, every delivered file carries `--safe`, the delivered
probe carries no hole, and nothing lands in `src/`. The probe is a
raw `.agda` file, so it carries no fence, counts 0 in-fence lines,
and the ratio bar cannot fire on it.

**NO HEAP WALL WAS MET ANYWHERE IN THIS TASK.** The highest peak of
any run is 546,930,688 bytes against the 2,147,483,648-byte wide
cap (`runs/floor-1.out`). That is 25 percent of it. The longest
Agda run is 2.86 s on the witness meter.

The standing direction (`dev/pod/direction.md:37`) says one SRC
collection after LJ-1, not after `[LJ-2.5]`. This task is still LJ-1
work. It does not start that collection and it does not start phase 3.
No Boundary clause is in conflict.

**EVERY NUMBER BELOW IS MEASURED WITH A WARM `src/` INTERFACE CACHE.**
No number here is a cold-cache number, and this report does not bound
one.

## 1. THE PREDECESSOR QUESTION, ANSWERED BEFORE ANY AGDA

`[LJ-1.672]` closed **NO-GO on `same-as-graph`**
(`agents/tasks/LJ-1-672/lj-1.672-report.md:9-11`). That NO-GO is not
a stop here. The report does not name `SameAsGraph` FALSE. It names
the type uninhabited, and it funds an adequate `K` first (`:174-179`).
The critic of that return upheld the stop
(`agents/tasks/LJ-1-672/review-of-LJ-1-672-1.md:8`) and named the
cure this task takes: a probe-local ω-block with `succλ` and `∅∈λ`,
with no edit under `src/` (`:110-118`).

The types I take are the types the predecessors DELIVERED:

| piece | type | site | verdict |
|---|---|---|---|
| `KValue` | one `KFacts` at `Lset λ` | `src/L/Condensation.lagda.md:7380-7434` | GO in `src/`; needs `succλ` and `∅∈λ` |
| `SameAsGraph` | both directions, one env | `Probe520.agda:192-195` | TYPE, green; not this obligation |
| `W3.Pins.pins` | pins at the numerals | `LJ-1-672/runs/W3.agda` | GO; not re-dispatched |
| `Bound.PowIter` | `𝒟ₒ`-climb | `src/L/Coding/Bound.lagda.md:147-152` | hypothesis; a sibling prices it |
| `suc∈or≡` | successor does not overshoot | `src/L/Ordinal/Stages.lagda.md:137-144` | GO, in `src/` |

**W2.** The ω-block is written once at a generic ordinal
(`runs/W3.agda:122-132`, module `Block`). `KValue` instantiates that
carrier (`Probe678.agda:27-32`). No fixed form (`lam = ω` only) is
required. There is no deadline conflict.

## 2. D-10, BEFORE THE PROOF IS PRICED

The target is suc-closure of a limit above the approximation, plus
`∅` in that limit, so `KValue` instantiates.

I did not find a Tarskian or cardinality obstruction. `suc∈or≡`
(`src/L/Ordinal/Stages.lagda.md:137-144`) already says a member's
successor lands in the ordinal or equals it. A union of finite
successors is therefore suc-closed from that lemma. The live `+ω`
is sealed and has no out-lemma
(`src/L/Ordinal/StageArith.lagda.md:39-42`). The probe-local block
is the same mathematics with the out-lemma exported
(`runs/W3.agda:80-89`).

D-10's correction: prove suc-closure at a probe-local ω-block.
Do not take a `HullStage` telescope if that proof lands. It landed.

## 3. THE FLOOR

The standing coder clause orders a floor before a heavy object. I
ran it. `runs/FLOOR.agda.txt` is W3 plus `KValue`, with a HOLE where
the term goes.

**THE FRAME COSTS 2.32 s AND 547 MB, AND IT DOES NOT WALL.**
`runs/floor-1.out`: exit 42 at 2.32 s, peak 546,930,688 bytes, the
designed hole (`[UnsolvedInteractionMetas]` at `FLOOR.agda:31`).
**The obligation TYPE is well-formed.** Importing `KValue` on top
of W3 is not a wall.

The import trim is: `src/` plus `runs/W3.agda`. That is the trim
the floor and the probe measured.

## 4. W3, WHETHER A LIMIT ABOVE THE APPROXIMATION CARRIES SUC-CLOSURE

The brief names it. Estimate 100 to 220 lines, basis
`agents/tasks/LJ-1-672/lj-1.672-report.md:1`. The critic of that
return estimated 40 to 70 lines for the probe-local block
(`review-of-LJ-1-672-1.md:116-118`).

**GO ON SUC-CLOSURE. GO ON `∅∈λ`.**

`runs/W3.agda` builds `ωBlock` as the union of `sucIter (suc n) u`,
sealed at birth (`:50-52`). It exports `ωBlock-out` (`:80-89`),
`ωBlock-succ` (`:92-108`) by `suc∈or≡`, and `ωBlock-∅` (`:111-118`)
by trichotomy against the base ordinal. Module `Block` packages
`lam`, `ordλ`, `succλ`, `∅∈λ` and `γ∈λ` at a generic ordinal
(`:122-132`). First green run: **exit 0 at 1.12 s, peak
285,507,584 bytes** (`runs/w3-2.out`).

The estimate was 100 to 220 lines. W3 is 132 lines. The critic's
40 to 70 priced the block without `suc∈or≡` already in `src/`.
The extra lines are the out-lemma, the suc-closure, and the empty
membership.

A first packing of `ωBlock-∅` inferred the equality the wrong way
(`runs/w3-1.out`, `[UnequalTerms]` at `W3.agda:117`, 1.31 s, peak
283,262,976 bytes). The three cases named (`:114-118`) closed it.
That is not a heap wall and not a stop on the mathematics.

## 5. WHAT THE SHAPE RESISTED

- **What it cost.** W3 132 lines, green at 1.12 s, 286 MB. Floor
  2.32 s, 547 MB. Probe 32 lines, green at 2.14 s, 547 MB. Witness
  2.86 s, 0 UNRESOLVED. Highest peak 0.55 GB against a 2 GB cap,
  no heap wall.
- **What the shape resisted.** The live `+ω` is an atom and has no
  out-lemma, so suc-closure cannot be proved from the export list
  of `StageArith`. The probe-local block with `ωBlock-out` closed.
- **What I had to weaken.** Nothing of the obligation. I did not
  take a `HullStage` telescope. I did not instantiate only at `ω`.
- **What I could not close.** Nothing of `k-value`. `powIter` stays
  a hypothesis (`src/L/Coding/Bound.lagda.md:147-152`). It is not
  this obligation. `SameAsGraph` is not inhabited here.

## 6. WHAT THE NEXT BRIEF NEEDS

1. **Do not re-dispatch pins at the numerals.** `[LJ-1.672]` already
   has `W3.Pins.pins` and `W3.Reverse.hpins` green.
2. **Do not re-dispatch `k-value`.** `Probe678.agda:32` is
   `KValue.facts` at `ωBlock gam` for a generic ordinal `gam`.
   `succλ` and `∅∈λ` are terms (`runs/W3.agda:127-130`).
3. **The reverse of `SameAsGraph` can now choose this `K`.** It
   still needs `powIter` (a sibling is pricing it), then
   `graphBndAt` against `LsetGraphAt`, then packing with an
   explicit formula argument (`agents/tasks/LJ-1-672/lj-1.672-report.md:180-185`).
   Do not expect `k-value` to discharge `powIter`.
4. **The first conjunct still cannot read `KFacts` off `transK`
   and pins.** The canonical bound now exists as a term. The
   formula still closes `K` by a bare existential
   (`dev/literature/level-formula-slot-roles.md:60-63`). Those
   remain different statements.
5. **THIS FRAME RUNS WIDE.** Highest peak 0.55 GB against a 2 GB
   cap. The heavy tier is not needed.
6. This task changed nothing in `src/`. A later dispatch that wants
   `ωBlock-out` in `src/` is an edit of `StageArith`, not a new `K`.

## 7. GATES

Run individually while the work was live, as the Boundary requires.

| run | file | exit | seconds | peak bytes | what it is |
|---|---|---:|---:|---:|---|
| w3-1 | `runs/W3.agda` | 42 | 1.31 | 283,262,976 | equality the wrong way |
| w3-2 | `runs/W3.agda` | 0 | 1.12 | 285,507,584 | suc-closure at ω-block |
| floor-1 | `runs/FLOOR.agda.txt` | 42 | 2.32 | 546,930,688 | designed hole |
| p-1 | `Probe678.agda` | 0 | 2.14 | 546,652,160 | delivered probe |
| meter | `Probe678.agda::k-value` | 0 | 2.86 | (witness) | 0 UNRESOLVED |

One Agda process at a time. `GHCRTS="-A64m -I0 -M2g"` on every run,
read back from the pane, never set here. The witness row has no
peak: `scripts/pod/witness.py` does not print resident set size.

## ARCHIVE USED

- `archive/dev/ORCHESTRATION.md`: not read. The task inhabits a
  type in a live module. The archived orchestration is not that type.
- `archive/dev/DD-archived.md`: not read. The live rulings sit in
  `dev/pod/rulings.toml`. This task does not reopen a retired DD.
- `archive/dev/PLAN-archived.md`: not read. The standing status is
  the screen. An archived plan is not the obligation.
- `archive/dev/STATUS-archived.md`: not read. The screen is the only
  standing status.
- `archive/dev/TASKS-archived.md`: not read. The live task home is
  `agents/tasks/LJ-1-678/`.

## LITERATURE USED

- `dev/literature/level-formula-slot-roles.md`: read. `:60` quotes

      Devlin's `∃w` carries the conjunct `K(w,u)`, "which says `w = K(u)`"

  That is what "adequate `K`" means here: the canonical bound, not a
  bare existential. The predecessor already recorded the difference
  (`agents/tasks/LJ-1-672/lj-1.672-report.md:105-109`). This task
  funds that bound.
- `dev/literature/glossary-review-2026-08.md`: declined. No glossary
  term is added. The Boundary forbids a self-chosen entry.
- `dev/literature/primary-sources.md`: not used. The slot-roles
  digest already carries the Devlin locator this D-10 spends.
- `dev/literature/devlin-errata.md`: not used. `[LJ-1.520]` already
  checked the errata against the formula
  (`lj-1.520-report.md:102-113`). A measured cure does not transfer
  by analogy.
- `dev/literature/BIBLIOGRAPHY.md`: not used. No new source is cited.
