# LJ-1.672 report: the two readings of the level graph agree

## HEAD
head_slot: coder
machine: shared
agda_tier: wide
task: LJ-1.672
obligation: agents/tasks/LJ-1-672/Probe672.agda::same-as-graph
verdict: **NO-GO on the obligation. The twelve tag witnesses
are the numerals, and pins holds of them. Neither direction of
SameAsGraph inhabits at the type [LJ-1.520] named.**

The obligation term is not written. The probe is green and carries
no hole (`runs/p-final-1.out`, `EXIT=0`, 2.14 s, peak 623,640,576
bytes). W3 is green (`runs/w3-final.out`, `EXIT=0`, 2.85 s, peak
657,522,688 bytes). The stated NO-GO is
`agents/tasks/LJ-1-672/review-of-same-as-graph.md`. That file is the
critic's input and it does not close the task.

**THIS IS NOT A REFUTATION OF `SameAsGraph`.** I did not build a
term of its negation.

Written as a skeleton before any Agda beyond the predecessor read
and filled as each answer landed (C-22). No commit, no push. I wrote
only inside `agents/tasks/LJ-1-672/`. Agda ran under the caliber the
program set on this pane, `GHCRTS="-A64m -I0 -M2g"`, the WIDE tier,
ONE Agda process at a time. I did not set `GHCRTS`. Nothing is
postulated, every delivered file carries `--safe`, the delivered
probe carries no hole, and nothing lands in `src/`. The probe is a
raw `.agda` file, so it carries no fence, counts 0 in-fence lines,
and the ratio bar cannot fire on it.

**NO HEAP WALL WAS MET ANYWHERE IN THIS TASK.** The highest peak of
any run is 885,325,824 bytes against the 2,147,483,648-byte wide
cap (the failed packing attempt under W3), which is 41 % of it. The
longest Agda run is 4.46 s on that same failed packing. Every green
run is under 3.4 s.

The standing direction (`dev/pod/direction.md:37`) says one SRC
collection after LJ-1, not after `[LJ-2.5]`. This task is still LJ-1
work. It does not start that collection and it does not start phase 3.
No Boundary clause is in conflict.

**EVERY NUMBER BELOW IS MEASURED WITH A WARM `src/` INTERFACE CACHE.**
No number here is a cold-cache number, and this report does not bound
one.

## 1. THE PREDECESSOR QUESTION, ANSWERED BEFORE ANY AGDA

`[LJ-1.520]` closed **GO on `levelFo-Σ₁`**
(`agents/tasks/LJ-1-520/lj-1.520-report.md:3-6`). `SameAsGraph` is a
TYPE in that green module (`Probe520.agda:192-195`). The report does
not name `SameAsGraph` FALSE. It names both halves uninhabited
(`:289-291`). This task takes that type.

`[LJ-1.667]` closed **NO-GO on `witnessed-lset`**
(`agents/tasks/LJ-1-667/lj-1.667-report.md:9-11`). That NO-GO is not
a stop here. It names `SameAsGraph` as the first item to fund
(`:303-306`), and it does not name the type FALSE.

The type I take is the type the predecessor delivered:

| piece | type | site | verdict |
|---|---|---|---|
| `SameAsGraph` | both directions, one env | `Probe520.agda:192-195` | TYPE, green; not inhabited |
| `levelFo-Σ₁` | Σ₁ formula, two free slots | `Probe520.agda:171-172` | GO |
| `LsetGraphAt` | ungraded graph | `src/L/Coding/Sequence.lagda.md:349` | GO, in `src/` |
| `Matrix` | `transK ∧ pins ∧ graphBndAt` | `Probe520.agda:53-128` | GO, syntax |
| `KValue` | one `KFacts` at `Lset λ` | `src/L/Condensation.lagda.md:7380-7434` | GO, needs HullStage |
| `Bound.PowIter` | `𝒟ₒ`-climb | `src/L/Coding/Bound.lagda.md:147-152` | hypothesis, not a term |

**W2.** The mathematics is written once at a generic arity and
generic slots, the same carrier `[LJ-1.520]` used. `Pins` and
`Reverse` instantiate that carrier. No fixed form is required. There
is no deadline conflict.

## 2. D-10, BEFORE THE PROOF IS PRICED

The target is `SameAsGraph` at an arbitrary environment, with no
`IsOrd` and no limit `λ` (`Probe520.agda:192-195`).

I did not find a Tarskian or cardinality obstruction that refutes
the statement. I did find that the type as stated does not carry
the hypotheses the tree uses to inhabit the two sides.

1. **First conjunct, Σ₁ to graph.** The formula produces a
   transitive `K` and twelve tag slots (`transK` and `pins`,
   `Probe520.agda:95-128`). `KFacts.numK0` through `numK11`
   (`src/L/Condensation.lagda.md:6094-6105`) ask for the numerals
   as members of `K`. pins does not say that. `LeafAgree`
   (`:7224-7305`) still takes `witK`, `wCodesK`, `pow`-style
   entry facts, and `twelve-out` / `twelve-back` as parameters.
   `powK` is the `𝒟ₒ` bound `[LJ-1.162]` measured as missing from
   `src/` (`agents/tasks/LJ-1-162/lj-1.162-report.md:141-167`).
   `Bound.PowIter` still takes it as a hypothesis
   (`src/L/Coding/Bound.lagda.md:147-149`).
2. **Second conjunct, graph to Σ₁.** The reverse must choose an
   adequate `K`. The tree's one supply is `KValue`
   (`src/L/Condensation.lagda.md:7369-7373`), `Lset λ` at a limit
   above the carrier, with `HullStage`'s three hypotheses. SameAsGraph
   has none of them. `+ω` (`src/L/Ordinal/StageArith.lagda.md:41-42`)
   builds an ω-block. Suc-closure of `+ω` is not a delivered term.
3. **The literature.** `dev/literature/level-formula-slot-roles.md:60`:

       Devlin's `∃w` carries the conjunct `K(w,u)`, "which says `w = K(u)`"

   The brief's formula closes `K` by a bare existential. Devlin
   determines the bound. Those are different statements
   (`:62-63`).

D-10's correction: do not price a proof of SameAsGraph at this
generality. Price an adequate `K` first, or determine the bound.

## 3. THE FLOOR

The standing coder clause orders a floor before a heavy object. I
ran it. `runs/FLOOR.agda.txt` is the obligation's whole type,
`Probe520` imported, and a HOLE where the term goes.

**THE FRAME COSTS 2.62 s AND 604 MB, AND IT DOES NOT WALL.**
`runs/floor-5.out`: exit 42 at 2.62 s, peak 604,471,296 bytes, one
error and it is the designed hole (`[UnsolvedInteractionMetas]` at
`FLOOR.agda:36`). **The obligation TYPE is well-formed.** Importing
`Probe520` is not a wall.

The import trim is: `src/` plus `Probe520` plus `runs/W3.agda`. That
is the trim the floor and W3 measured.

## 4. W3, THE DIRECTION FROM THE GRAPH BACK TO THE Σ₁ READING

The brief names it. Estimate 100 to 220 lines, basis `[LJ-1.520]`
reached the statement inside its own probe
(`agents/tasks/LJ-1-520/Probe520.agda:192`).

**GO ON THE TAG WITNESSES. NO-GO ON PRODUCING AN ADEQUATE `K`.**

`runs/W3.agda` proves pins at `numeralL 0` through `numeralL 11`, by
`numeralL-fst` and `sucAtL-adequate`. Module `Pins` instantiates
`Matrix` at a dummy tail. Module `Reverse` instantiates `Matrix` at
the thirteen-slot environment `[LJ-1.520]`'s `Slots` uses, with `K`
a parameter, and `Reverse.hpins` is green. First green run of the
pins file: **exit 0 at 2.22 s, peak 629,145,600 bytes**. The final
green run is `runs/w3-final.out`, exit 0 at 2.85 s, peak
657,522,688 bytes.

The estimate was 100 to 220 lines. W3 is 158 lines. The new
mathematics is the numeral pins. Adequacy of `K`, `graphBndAt` from
`LsetGraphAt`, and packing of the thirteen existentials are not in
that count because they are not written as terms. Packing was
attempted. `pack1`'s implicit formula did not infer through a
where-chain (unsolved `_φ` metas, peak 885,325,824 bytes, 4.46 s).
That is plumbing. A next dispatch can annotate the formula.

## 5. WHAT THE SHAPE RESISTED

- **What it cost.** W3 158 lines, median green run about 2.5 s,
  highest peak 0.89 GB against a 2 GB cap, no heap wall. Floor
  2.62 s, 604 MB. Probe 47 lines, green at 2.14 s, 624 MB.
- **What the shape resisted.** The type wants both directions at an
  arbitrary environment. The tree inhabits the leaf agreement only
  under `KFacts` plus a limit. transK and pins do not produce
  `KFacts`. `+ω` does not come with suc-closure. `powIter` is still
  a hypothesis.
- **What I had to weaken.** Nothing of the obligation. I did not
  inhabit a smaller type and call it `same-as-graph`.
- **What I could not close.** `same-as-graph`, both conjuncts, at
  the named type. Packing of the thirteen existentials, as a
  separate plumbing fact.

## 6. WHAT THE NEXT BRIEF NEEDS

1. **Do not re-dispatch pins at the numerals.** `W3.Pins.pins` and
   `W3.Reverse.hpins` are green.
2. **Fund an adequate `K` before either direction.** For the reverse,
   that is `KValue` at a limit above the approximation, including
   suc-closure of `+ω` or a `HullStage` telescope, plus `powIter`.
   For the first conjunct, either determine the bound as Devlin
   does, or take `KFacts` as extra hypotheses. Do not expect transK
   and pins to discharge them.
3. **Then fund `graphBndAt` against `LsetGraphAt`, both ways.**
   `[LJ-1.162]` already has `Graph.up` as a module with site-fact
   parameters (`ProbeLJ1162A.agda:208-222`). The reverse needs the
   matching `down`, plus `f ∈ K`.
4. **Packing needs an explicit formula argument.** Do not leave `φ`
   implicit in a thirteen-step where-chain.
5. **THIS FRAME RUNS WIDE.** Highest peak 0.89 GB against a 2 GB cap.
   The heavy tier is not needed.
6. This task changed nothing in `src/`.

## 7. GATES

Run individually while the work was live, as the Boundary requires.

| run | file | exit | seconds | peak bytes | what it is |
|---|---|---:|---:|---:|---|
| floor-5 | `runs/FLOOR.agda.txt` | 42 | 2.62 | 604,471,296 | designed hole |
| w3-final | `runs/W3.agda` | 0 | 2.85 | 657,522,688 | pins at numerals |
| p-final-1 | `Probe672.agda` | 0 | 2.14 | 623,640,576 | delivered probe |

One Agda process at a time. `GHCRTS="-A64m -I0 -M2g"` on every run,
read back from the pane, never set here.

## ARCHIVE USED

- `archive/dev/ORCHESTRATION.md`: not read. The task inhabits or
  stops on a type in a live probe. The archived orchestration is
  not that type.
- `archive/dev/DD-archived.md`: not read. The live rulings sit in
  `dev/pod/rulings.toml`. This task does not reopen a retired DD.
- `archive/dev/PLAN-archived.md`: not read. The standing status is
  the screen. An archived plan is not the obligation.
- `archive/dev/STATUS-archived.md`: not read. The screen is the only
  standing status.
- `archive/dev/TASKS-archived.md`: not read. The live task home is
  `agents/tasks/LJ-1-672/`.

## LITERATURE USED

- `dev/literature/level-formula-slot-roles.md`: read. `:60` quotes

      Devlin's `∃w` carries the conjunct `K(w,u)`, "which says `w = K(u)`"

  That is D-10's load-bearing line: the brief's bound is a bare
  existential, Devlin's bound is determined.
- `dev/literature/glossary-review-2026-08.md`: declined. No glossary
  term is added. The Boundary forbids a self-chosen entry.
- `dev/literature/primary-sources.md`: not used. The slot-roles
  digest already carries the Devlin locator this D-10 spends.
- `dev/literature/devlin-errata.md`: not used. `[LJ-1.520]` already
  checked the errata against this formula
  (`lj-1.520-report.md:102-113`). A measured cure does not transfer
  by analogy. The present stop is about the bound's determination,
  not about Sat's uniformity.
- `dev/literature/BIBLIOGRAPHY.md`: not used. No new source is cited.
