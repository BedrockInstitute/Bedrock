# LJ-1.695 report: the bridge, bounded to unbounded

## HEAD
head_slot: coder
machine: shared
agda_tier: wide
task: LJ-1.695
obligation: agents/tasks/LJ-1-695/Probe695.agda::bnd-to-unbnd
verdict: **GO.** `bnd-to-unbnd` is the bounded-to-unbounded direction
of `[LJ-1.681]`'s bridge. It is `Graph.up` at `[LJ-1.681]`'s generic
carrier. The outer existential bound is discharged. The inner
`extAt` frames and the approximation universals remain hypotheses.

The witness meter reads `0 UNRESOLVED of 1, 2.26 s, probe_red=False`
(`runs/meter-obligation.out:2`). The probe is green and carries no
hole (`runs/p-1.out`, `EXIT=0`, 13.50 s, peak 686,096,384 bytes).
The floor is the designed hole (`runs/floor-1.out`, `EXIT=42`,
2.31 s, peak 598,474,752 bytes, `[UnsolvedInteractionMetas]` at
`FLOOR.agda:78`).

Written as a skeleton before any Agda beyond the predecessor read
and filled as each answer landed (C-22). No commit, no push. I wrote
only inside `agents/tasks/LJ-1-695/`. Agda ran under the caliber the
program set on this pane, `GHCRTS="-A64m -I0 -M2g"`, the WIDE tier,
ONE Agda process at a time. I did not set `GHCRTS`. Nothing is
postulated, every delivered file carries `--safe`, the delivered
probe carries no hole, and nothing lands in `src/`. The probe is a
raw `.agda` file, so it carries no fence, counts 0 in-fence lines,
and the ratio bar cannot fire on it.

**NO HEAP WALL WAS MET ANYWHERE IN THIS TASK.** The highest peak of
any run is 686,096,384 bytes against the 2,147,483,648-byte wide
cap (`runs/p-1.out`). That is 32 percent of it. The longest Agda
run is 13.50 s on the delivered probe.

The standing direction (`dev/pod/direction.md:37`) says one SRC
collection after LJ-1, not after `[LJ-2.5]`. This task is still LJ-1
work. It does not start that collection and it does not start phase 3.
No Boundary clause is in conflict.

**W2.** `∃∈-up` is written once at a generic arity, a generic bound,
and generic formulas (`Probe695.agda:58-61`). The graph term
instantiates that carrier at generic `{n}` `(w b K : Fin n)`, the
same carrier `[LJ-1.681]` used (`Probe695.agda:70-71`). No fixed
form is required. There is no deadline conflict.

**W4.** No module is retired. Nothing moves to `archive/`.

## 1. THE PREDECESSOR QUESTION, ANSWERED BEFORE ANY AGDA

`[LJ-1.681]` closed **GO on `bnd-vs-unbnd`**, unbounded to bounded
(`agents/tasks/LJ-1-681/lj-1.681-report.md:5-10`). The report names
the other direction and says `Graph.up` is where to start (`:139-140`).
That report is not NO-GO and it does not name the reverse FALSE.

`Graph.up` is delivered at
`agents/tasks/LJ-1-162/ProbeLJ1162A.agda:218-222`:

    up : ⟨ γ ⊨ GraphB.graphBndAt {m} ψs ψa w b K ⟩ → ⟨ γ ⊨ LsetGraphAt w b ⟩

`[LJ-1.162]`'s own report is NO-GO on PRICE for Leg 3
(`agents/tasks/LJ-1-162/lj-1.162-report.md:30`), not on this type.
The type typechecked. I take that type. I do not rebuild `Graph.up`.
I instantiate it at `[LJ-1.681]`'s generic carrier. I fill its two
hypotheses from the delivered `extAtB→extAt`
(`src/L/Condensation.lagda.md:2514-2518`) and from `[LJ-1.162]`'s
`Approx.up` (`ProbeLJ1162A.agda:201-204`). I do not import
`ProbeLJ1162A`: that file also carries Leaf, Step, and Leg 3, which
this obligation does not use, and the standing coder clause trims
imports to the facts the rows use.

`[LJ-1.678]` closed **GO on `k-value`**. Its next-brief row says the
`SameAsGraph` reverse still needs `powIter`, then
`graphBndAt` against `LsetGraphAt`, then packing
(`agents/tasks/LJ-1-678/lj-1.678-report.md:150-154`).

`[LJ-1.685]` is not a file in this worktree. The sibling worktree
`LJ-1-685` has `Probe685.agda:71`, which inhabits the reverse
conjunct of `SameAsGraph` and takes the DOWN bridge as a hypothesis
(`Probe685.agda:66-69`). That reverse spends DOWN, not UP. This
obligation is the other direction of the bridge.

The types I take are the types the predecessors DELIVERED:

| piece | type | site | verdict |
|---|---|---|---|
| `bnd-vs-unbnd` | unbounded to bounded | `Probe681.agda:67-95` | GO; not this obligation |
| `Graph.up` | bounded to unbounded | `ProbeLJ1162A.agda:218-222` | GO, delivered; this obligation |
| `extAtB→extAt` | frame transfer plus `inK` | `src/L/Condensation.lagda.md:2514-2518` | GO, in `src/` |
| `k-value` | `KValue.facts` at ω-block | `Probe678.agda:32` | GO; not this obligation |

## 2. D-10, BEFORE THE PROOF IS PRICED

The target is the bounded-to-unbounded direction of `[LJ-1.681]`'s
bridge, at one environment.

I did not find a Tarskian or cardinality obstruction. `Graph.up`
already inhabits the target (`ProbeLJ1162A.agda:218-222`). The outer
existential bound is discharged for free: a bounded existential
reaches the unbounded one by throwing the membership away. The
inner `extAt` frames still need `inK`, because `extAt` is an
extensionality (`lj-1.162-report.md:48-53`). The approximation's
two universals still need `entryK`, because a bounded `∀̇∈` is
weaker than an unbounded `∀̇`. Those site facts stand as
hypotheses, the same way `[LJ-1.681]` stood `fK` and the leaf rows
as hypotheses.

D-10's correction: none. The recorded target is true at the
intended generality, given those site facts.

## 3. THE FLOOR

The standing coder clause orders a floor before a heavy object. I
ran it. `runs/FLOOR.agda.txt` is the obligation TYPE, with a HOLE
where the term goes.

**THE FRAME COSTS 2.31 s AND 598 MB, AND IT DOES NOT WALL.**
`runs/floor-1.out`: exit 42 at 2.31 s, peak 598,474,752 bytes, the
designed hole (`[UnsolvedInteractionMetas]` at `FLOOR.agda:78`).
**The obligation TYPE is well-formed.** Importing `StepB`,
`ApproxB`, `GraphB`, and `extAtB→extAt` on this carrier is not a
wall.

The import trim is the `src/` modules the rows use. I did not
import `ProbeLJ1162A`. That is the trim the floor and the probe
measured.

## 4. W3, WHETHER THE BOUND CAN BE DISCHARGED RATHER THAN INTRODUCED

The brief names it. Estimate 120 to 260 lines, basis
`agents/tasks/LJ-1-681/lj-1.681-report.md:1`.

**GO ON THE OUTER EXISTENTIAL. NO ON THE INNER FRAMES WITHOUT SITE FACTS.**

The outer bound is discharged. `∃∈-up` (`Probe695.agda:58-61`) maps
a bounded existential to an unbounded one by throwing the
membership away. `bnd-to-unbnd` is that kit instantiated at
`GraphB.graphBndAt` (`Probe695.agda:105-111`). That body is
`Graph.up` (`ProbeLJ1162A.agda:219-222`). I did not rebuild it.

The inner frames do not discharge. `extAt` is an extensionality, so
the delivered `extAtB→extAt` (`src/L/Condensation.lagda.md:2514-2518`)
consumes `fwd`, `bwd`, AND `inK`. The two step clauses pay that
cost as `stepK` and `apxStepK` (`Probe695.agda:94-99`, used at
`:124` and `:138`). `[LJ-1.681]`'s DOWN used `extAt→extAtB`, which
does not take `inK` (`src/L/Condensation.lagda.md:2524-2530`). That
is the asymmetry.

The approximation universals do not discharge either. Bounded
`∀̇∈` is weaker than unbounded `∀̇`. `approxUp`
(`Probe695.agda:143-148`) is `[LJ-1.162]`'s `Approx.up` at this
carrier: `entryK` turns an application into the two memberships
the bounded universals demand. `[LJ-1.681]` recorded the other
side of this: the unbounded approximation step is stronger, so
those memberships went unused (`lj-1.681-report.md:97-100`).

`fK` is not a hypothesis here. DOWN needed it to introduce the
outer bound. UP throws that membership away.

The estimate was 120 to 260 lines. The probe is 148 lines, 94
non-blank non-comment code lines, measured from the file this run
landed. The estimate priced a rebuild of the inner Leaf and Step
frames. The landing is below that floor because those frames stay
hypotheses, as they did for DOWN.

## 5. WHAT THE SHAPE RESISTED

- **What it cost.** Floor 2.31 s, 598 MB, designed hole. Probe 148
  lines, green at 13.50 s, 686 MB. Witness 2.26 s, 0 UNRESOLVED.
  Highest peak 0.69 GB against a 2 GB cap, no heap wall.
- **What the shape resisted.** A one-directional discharge of the
  inner `extAt` frames. The outer existential is free. The inner
  equalities are not. The approximation universals are not.
- **What I had to weaken.** Nothing of the obligation. I did not
  inhabit a smaller type. I did not rebuild `Graph.up`. I did not
  import `ProbeLJ1162A`.
- **What I could not close.** Nothing of `bnd-to-unbnd`. The leaf
  rows, `domBack`, `stepK`, `apxStepK`, and `entryK` stay
  hypotheses. They are the same class of site fact `[LJ-1.681]`
  left standing, plus the three memberships this direction pays
  and DOWN did not.

## 6. WHAT THE NEXT BRIEF NEEDS

1. **Do not re-dispatch `bnd-to-unbnd`.** `Probe695.agda:78-104` is
   the bounded-to-unbounded direction at `[LJ-1.681]`'s carrier.
   `Graph.up` is not rebuilt.
2. **Do not re-dispatch `bnd-vs-unbnd`.** `[LJ-1.681]` already has
   the unbounded-to-bounded direction.
3. **The two directions are not symmetric in their site facts.**

   | fact | DOWN (`bnd-vs-unbnd`) | UP (`bnd-to-unbnd`) |
   |---|---|---|
   | outer witness in K | `fK`, required | discarded by `∃∈-up` |
   | domain transfer | `domOut` | `domBack` |
   | leaf rows both ways | `stepBwd`/`stepFwd`, `apxStepBwd`/`apxStepFwd` | the same |
   | satisfiers in K | unused | `stepK`, `apxStepK` |
   | application in K | unused | `entryK` |

4. **The `SameAsGraph` reverse spends DOWN, not UP.** `[LJ-1.685]`
   takes `LsetGraphAt → graphBndAt` as a hypothesis. The remaining
   half of the equivalence, graph-from-Σ₁, is the one that wants
   this term: from a bounded graph, reach the unbounded graph, then
   `Lset-only`. Do not expect this term to pack a formula or to
   discharge `powIter`.
5. **The leaf rows remain the open cost.** They are the `DefAt`
   against `DefBodyB` tie. `[LJ-1.346]` and the `LeafAgree`
   machinery measure that separately. This bridge does not.
6. **THIS FRAME RUNS WIDE.** Highest peak 0.69 GB against a 2 GB
   cap. The heavy tier is not needed.
7. This task changed nothing in `src/`. A later dispatch that wants
   `∃∈-up` in `src/` is an edit of `Condensation`, not a new bridge.

## 7. GATES

Run individually while the work was live, as the Boundary requires.

| run | file | exit | seconds | peak bytes | what it is |
|---|---|---:|---:|---:|---|
| floor-1 | `runs/FLOOR.agda.txt` | 42 | 2.31 | 598,474,752 | designed hole |
| p-1 | `Probe695.agda` | 0 | 13.50 | 686,096,384 | delivered probe |
| meter | `Probe695.agda::bnd-to-unbnd` | 0 | 2.26 | (witness) | 0 UNRESOLVED |

One Agda process at a time. `GHCRTS="-A64m -I0 -M2g"` on every run,
read back from the pane, never set here. The witness row has no
peak: `scripts/pod/witness.py` does not print resident set size.

The floor was the first Agda process this task started. The probe
and the witness ran after it. I do not report a cold-cache bound.

Broken files are named `.agda.txt`, never `.agda`. The only `.agda`
under the task home is `Probe695.agda`, which typechecks. The floor
is `agents/tasks/LJ-1-695/runs/FLOOR.agda.txt`.

I commit nothing and push nothing.

## ARCHIVE USED

- `archive/dev/ORCHESTRATION.md`: not read. The task inhabits a
  type in a live probe. The archived orchestration is not that type.
- `archive/dev/DD-archived.md`: not read. The live rulings sit in
  `dev/pod/rulings.toml`. This task does not reopen a retired DD.
- `archive/dev/PLAN-archived.md`: not read. The standing status is
  the screen. An archived plan is not the obligation.
- `archive/dev/STATUS-archived.md`: not read. The screen is the only
  standing status.
- `archive/dev/TASKS-archived.md`: not read. The live task home is
  `agents/tasks/LJ-1-695/`.

## LITERATURE USED

- `dev/literature/glossary-review-2026-08.md`: declined. No glossary
  term is added. The Boundary forbids a self-chosen entry.
- `dev/literature/primary-sources.md`: not used. The bridge is a
  term-level transport, not a sourced mathematical claim.
- `dev/literature/devlin-errata.md`: not used. This reverse uses no
  rud-route error class.
- `dev/literature/level-formula-slot-roles.md`: not used. Slot
  arithmetic is taken from `StepB`/`ApproxB`/`GraphB` as
  `[LJ-1.681]` did, not from this digest.
- `dev/literature/BIBLIOGRAPHY.md`: not used. No new source is cited.
