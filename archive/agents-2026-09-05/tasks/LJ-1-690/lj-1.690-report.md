# LJ-1.690 report: the forward direction, now that the reverse is delivered

## HEAD
head_slot: coder
machine: shared
agda_tier: wide
task: LJ-1.690
obligation: agents/tasks/LJ-1-690/Probe690.agda::same-as-graph-forward
verdict: **GO.** `same-as-graph-forward` is the first conjunct of
`SameAsGraph` (`Probe520.agda:194`), at the k-value telescope,
with `powIter` and the UP bridge as HYPOTHESES. The body unpacks
thirteen existentials, reads `graphBndAt` off the sealed matrix,
applies the hypothesized UP, and drops thirteen front slots.

The witness meter reads `0 UNRESOLVED of 1, 1.71 s, probe_red=False`
(`runs/meter-obligation.out:4`). The probe is green and carries no
hole (`runs/p-2.out`, `EXIT=0`, 1.65 s, peak 598,147,072 bytes).
W3 is green (`runs/w3-1.out`, `EXIT=0`, 0.71 s, peak 269,434,880
bytes).

**I DID NOT write `review-of-same-as-graph-forward.md`.** The
obligation is inhabited. A `review-of-*.md` is how a coder states
a NO-GO. This return is GO.

Written as a skeleton before any Agda beyond the predecessor read
and filled as each answer landed (C-22). No commit, no push. I wrote
only inside `agents/tasks/LJ-1-690/`. Agda ran under the caliber the
program set on this pane, `GHCRTS="-A64m -I0 -M2g"`, the WIDE tier,
ONE Agda process at a time. I did not set `GHCRTS`. Nothing is
postulated, every delivered file carries `--safe`, the delivered
probe carries no hole, and nothing lands in `src/`. The probe is a
raw `.agda` file, so it carries no fence, counts 0 in-fence lines,
and the ratio bar cannot fire on it. The only `{!!}` is the designed
hole in `runs/FLOOR.agda.txt:86`.

**NO HEAP WALL WAS MET ANYWHERE IN THIS TASK.** The highest peak of
any run is 817,938,432 bytes against the 2,147,483,648-byte wide
cap (`runs/p-1.out`). That is 38 percent of it. The longest Agda
run is 31.29 s on the first check of the delivered probe
(`runs/p-1.out`). The warm recheck is 1.65 s (`runs/p-2.out`).

The standing direction (`dev/pod/direction.md:37`) says one SRC
collection after LJ-1, not after `[LJ-2.5]`. This task is still LJ-1
work. It does not start that collection and it does not start phase 3.
No Boundary clause is in conflict. W4 does not apply: no module is
retired.

**EVERY NUMBER BELOW IS MEASURED WITH A WARM `src/` INTERFACE CACHE.**
`runs/p-1.out` is the first check of `Probe690.agda` itself. No
number here is a cold-cache number for `src/`, and this report does
not bound one.

## 1. THE PREDECESSOR QUESTION, ANSWERED BEFORE ANY AGDA

`[LJ-1.672]` closed **NO-GO on `same-as-graph`**
(`agents/tasks/LJ-1-672/lj-1.672-report.md:9-11`). That NO-GO is not
a stop here. The report does not name `SameAsGraph` FALSE. It names
both directions uninhabited at the type `[LJ-1.520]` wrote.

`[LJ-1.678]` closed **GO on `k-value`**
(`agents/tasks/LJ-1-678/lj-1.678-report.md:9-10`). The type that
predecessor delivered is `KValue.facts` at `ωBlock gam`
(`agents/tasks/LJ-1-678/Probe678.agda:32`).

`[LJ-1.685]` built `same-as-graph-reverse-at`. This worktree has no
`agents/tasks/LJ-1-685/` directory. I opened the sibling worktree
and the parent path
`/Users/alsg/Agentic/Bedrock/agents/tasks/LJ-1-685/Probe685.agda`.
The term sits at `:71-89`. The report file there still says
IN PROGRESS (`lj-1.685-report.md:9-10`). The critic overturned that
line (`review-of-LJ-1-685-1.md:8-16`): the term is green, obligations
delta -1 with 0 open. That report does not name the reverse FALSE.
The reverse telescope is `PowIterHyp → IsOrd → Bridge → graph → Σ₁`
with Bridge DOWN (`Probe685.agda:66-76`).

`[LJ-1.681]` is a sibling. This worktree has no
`agents/tasks/LJ-1-681/` directory. `[LJ-1.684]` restated the
bridge as a HYPOTHESIS, DOWN, at one environment
(`agents/tasks/LJ-1-684/Probe684.agda:69-72`). UP is already
`Graph.up` (`agents/tasks/LJ-1-162/ProbeLJ1162A.agda:218-222`)
and is not rebuilt (`agents/tasks/LJ-1-684/lj-1.684-report.md:25-27`).

The types I take are the types the predecessors DELIVERED:

| piece | type | site | verdict |
|---|---|---|---|
| `SameAsGraph` forward | Σ₁ to graph | `Probe520.agda:192-194` | TYPE, green; this obligation |
| `k-value` | `KValue.facts` at ω-block | `Probe678.agda:32` | GO; reverse spent the block, not `facts` |
| reverse | graph to Σ₁ | sibling `Probe685.agda:71-76` | GO as a term; report line stale |
| `Bound.PowIter` | `𝒟ₒ`-climb | `src/L/Coding/Bound.lagda.md:147-152` | hypothesis |
| `Bridge` DOWN | `LsetGraphAt → graphBndAt` | `Probe684.agda:69-72` | hypothesis; reverse spends it |
| `Graph.up` | `graphBndAt → LsetGraphAt` | `ProbeLJ1162A.agda:218-222` | GO, with site-fact parameters |

**W2.** The forward is written once at a generic arity and generic
slots, the same carrier `[LJ-1.520]` used (`Probe690.agda:51-54`).
Unpacking is written once at a generic formula (`runs/UNPACK.agda:70-86`)
and instantiated at the sealed matrix (`runs/UNPACKAT.agda:32-49`).
No fixed form (`n = 0`, `lam = ω` only) is required. There is no
deadline conflict.

## 2. D-10, BEFORE THE PROOF IS PRICED

The target is the forward conjunct of `SameAsGraph`
(`agents/tasks/LJ-1-520/Probe520.agda:194`):

    ⟨ γ ⊨ fst (levelFo-Σ₁ w b) ⟩ → ⟨ γ ⊨ LsetGraphAt w b ⟩

with `powIter` and the graph-against-bound bridge as hypotheses,
at `[LJ-1.678]`'s k-value telescope.

I did not find a Tarskian or cardinality obstruction. The formula
is a prenex of thirteen existentials over `transK ∧ pins ∧ graphBndAt`
(`Probe520.agda:124-164`). The forward UNPACKS those witnesses.
It does not choose them. The reverse chose the numerals and the
ω-block K. That is the first asymmetry.

The hypothesized bridge the reverse spent is DOWN
(sibling `Probe685.agda:66-69`). The forward needs UP at the
unpacked environment. `[LJ-1.684]` already recorded that UP is
`Graph.up` and is not rebuilt (`lj-1.684-report.md:25-27`). I take
UP as a HYPOTHESIS at the same shape the reverse took DOWN
(`Probe690.agda:67-70`), so this dispatch does not wait on
`LeafAgree` or `powK`. That is the second asymmetry.

`k-value` is not spent: the unpacked K is an arbitrary witness,
not the ω-block (`Probe690.agda:52-53`, `:78` binds `IsOrd` as `_`).
`powIter` is not spent: the hypothesized UP already carries
`graphBndAt` to `LsetGraphAt` (`Probe690.agda:44-46`, `:78` binds
it as `_`). Taking a mandated hypothesis and not spending it is
the same act `[LJ-1.685]` took with `powIter`.

C-42 does not fire. This is not a refutation of a site.

## 3. THE FLOOR

The standing coder clause orders a floor before a heavy object. I
ran it. `runs/FLOOR.agda.txt` is the obligation's whole type, with
a HOLE where the term goes.

**THE FRAME COSTS 2.24 s AND 608 MB, AND IT DOES NOT WALL.**
`runs/floor-1.out`: exit 42 at 2.24 s, peak 608,387,072 bytes, the
designed hole (`[UnsolvedInteractionMetas]` at `FLOOR.agda:86`).
**The obligation TYPE is well-formed.** Importing `Probe520` is not
a wall.

The import trim is: `src/` plus `Probe520` plus the task-local
`runs/` modules. That is the trim the floor and the probe measured.

## 4. W3, THE FORWARD DIRECTION'S PACKING

The brief names it. Estimate 110 to 240 lines, basis
`agents/tasks/LJ-1-685/lj-1.685-report.md:1`. The work is UNPACKING,
the dual of the reverse's pack.

**GO ON UNPACKING. GO ON THE DROP.**

`runs/UNPACK.agda` unpacks thirteen existentials at a generic
formula. `φ` is an argument at every `unpack∃` (`:28-30`).
`unpack13` (`:70-86`) returns a truncated `Wit` record. First
green run: **exit 0 at 0.81 s, peak 277,954,560 bytes**
(`runs/unpack-2.out`). A first packing missed `squash₁` in the
open list (`runs/unpack-1.out`, `[NotInScope]` at `UNPACK.agda:33`,
0.70 s). That is plumbing. It is not a heap wall and not a stop
on the mathematics.

`runs/UNPACKAT.agda` seals `Matrix.matrix` (`:32-34`) and
instantiates. `from-levelFo` (`:38-42`) is `subst` along `refl`
under `unfolding mat`. `to-graph` (`:44-46`) reads the third
conjunct. Green at 1.77 s, peak 610,385,920 bytes
(`runs/unpackat-1.out`).

`runs/RENAME3.agda` is the `renameFo` commute for `LsetGraphAt`,
copied from `[LJ-1.685]` because this worktree has no that module.
Green at 6.33 s, peak 388,497,408 bytes (`runs/rename-1.out`).

`runs/DROP.agda` is the inverse of `[LJ-1.685]` `lift13`. P-l: it
does not import `Probe520`. Green at 14.62 s, peak 583,041,024
bytes (`runs/drop-1.out`). That run is the first check of the
rename commute plus the drop. It is not a heap wall.

`runs/W3.agda` is a thin re-export of `UNPACK`, the shape
`[LJ-1.685]` landed on after its wall restructure. Green at
0.71 s (`runs/w3-1.out`).

The estimate was 110 to 240 lines. UNPACK is 88 lines, DROP is 50,
RENAME3 is 21, UNPACKAT is 49. That is 208 lines of plumbing.
The probe that composes them is 95 lines.

## 5. WHAT THE SHAPE RESISTED

- **What it cost.** Floor 2.24 s, 608 MB. First probe check 31.29 s,
  818 MB. Warm probe 1.65 s, 598 MB. Witness 1.71 s, 0 UNRESOLVED.
  Highest peak 0.82 GB against a 2 GB cap, no heap wall.
- **What the shape resisted.** The same three input NAMES as the
  reverse do not spend the same way. The reverse chooses witnesses
  and spends DOWN. The forward unpacks witnesses and spends UP.
  `k-value` is not a supplier for the unpacked K. DOWN does not
  inhabit the first conjunct.
- **What I had to weaken.** Nothing of the obligation's conclusion.
  I did not inhabit a smaller type and call it `same-as-graph-forward`.
  The hypothesized bridge is UP, not the DOWN `[LJ-1.684]` restated.
  That is the dual of the reverse's hypothesis, not a weakening of
  the `SameAsGraph` conjunct.
- **What I could not close.** The UP bridge as a TERM. It stays a
  hypothesis. `Graph.up` already has it, with site-fact parameters
  (`ProbeLJ1162A.agda:218-222`). `powIter` stays a hypothesis.
  `KValue.facts` is not consumed.

## 6. WHAT THE NEXT BRIEF NEEDS

1. **Do not re-dispatch this forward.** `Probe690.agda:95` is
   `same-as-graph-forward`. The witness is 0 UNRESOLVED.
2. **Do not re-dispatch the reverse.** `[LJ-1.685]` already has
   `same-as-graph-reverse-at`. Its report line is stale. Its term
   is green.
3. **The two directions do not share one Bridge.** Reverse spends
   DOWN (`LsetGraphAt → graphBndAt`). Forward spends UP
   (`graphBndAt → LsetGraphAt`). A consumer that wants both
   conjuncts of `SameAsGraph` at one environment must take BOTH
   hypotheses, or inhabit both bridges. DOWN is `[LJ-1.681]`'s
   remaining debt (`HierInK` plus the leaf rows `[LJ-1.684]` named).
   UP is `Graph.up` plus the site facts `[LJ-1.162]` took
   (`powK`, `LeafAgree`).
4. **Do not expect `k-value` to pick the forward's K.** The formula
   is a bare existential. The unpacked K is arbitrary. Devlin
   determines the bound (`dev/literature/level-formula-slot-roles.md:60`).
   Those remain different statements.
5. **Do not expect `powIter` to be spent by either direction at
   this hypothesized strength.** Both bodies bind it as `_`.
6. **Assembling the pair `SameAsGraph` is not this obligation.**
   The named type (`Probe520.agda:192-195`) has no extra hypotheses.
   Both delivered halves still carry three extra inputs, and the
   bridge input is not the same type.
7. **THIS FRAME RUNS WIDE.** Highest peak 0.82 GB against a 2 GB
   cap. The heavy tier is not needed.
8. This task changed nothing in `src/`.

## 7. GATES

Run individually while the work was live, as the Boundary requires.

| run | file | exit | seconds | peak bytes | what it is |
|---|---|---:|---:|---:|---|
| floor-1 | `runs/FLOOR.agda.txt` | 42 | 2.24 | 608,387,072 | designed hole |
| rename-1 | `runs/RENAME3.agda` | 0 | 6.33 | 388,497,408 | rename commute |
| drop-1 | `runs/DROP.agda` | 0 | 14.62 | 583,041,024 | drop thirteen slots |
| unpack-1 | `runs/UNPACK.agda` | 42 | 0.70 | 267,354,112 | `squash₁` not in scope |
| unpack-2 | `runs/UNPACK.agda` | 0 | 0.81 | 277,954,560 | generic unpack13 |
| unpackat-1 | `runs/UNPACKAT.agda` | 0 | 1.77 | 610,385,920 | sealed matrix |
| w3-1 | `runs/W3.agda` | 0 | 0.71 | 269,434,880 | thin re-export |
| p-1 | `Probe690.agda` | 0 | 31.29 | 817,938,432 | first check of the probe |
| p-2 | `Probe690.agda` | 0 | 1.65 | 598,147,072 | warm recheck |
| meter | `Probe690.agda::same-as-graph-forward` | 0 | 1.71 | (witness) | 0 UNRESOLVED |

One Agda process at a time. `GHCRTS="-A64m -I0 -M2g"` on every run,
read back from the pane, never set here. The witness row has no
peak: `scripts/pod/witness.py` does not print resident set size.
This worktree has no `.venv`. The meter ran as
`/Users/alsg/Agentic/Bedrock/.venv/bin/python scripts/pod/witness.py`.
I did not add a dependency and I did not create a local `.venv`.

**THE RATIO BAR CANNOT FIRE ON THIS RETURN.** The write scope holds
no `.lagda.md` and no fence, so the in-fence divisor is 0. Nothing
landed in `src/`.

## ARCHIVE USED

- `archive/dev/ORCHESTRATION.md`: not read. The task inhabits a
  type in a live probe. The archived orchestration is not that type.
- `archive/dev/DD-archived.md`: not read. The live rulings sit in
  `dev/pod/rulings.toml`. This task does not reopen a retired DD.
- `archive/dev/PLAN-archived.md`: not read. The standing status is
  the screen. An archived plan is not the obligation.
- `archive/dev/TASKS-archived.md`: not read. The live task home is
  `agents/tasks/LJ-1-690/`.
- `archive/dev/STATUS-archived.md`: not read. The screen is the only
  standing status.

## LITERATURE USED

- `dev/literature/level-formula-slot-roles.md`: read. `:60` quotes

      Devlin's `∃w` carries the conjunct `K(w,u)`, "which says `w = K(u)`"

  That is what "adequate `K`" still means: the canonical bound, not a
  bare existential. The forward unpacks a bare existential. It does
  not determine the bound. The predecessor already recorded the
  difference (`agents/tasks/LJ-1-672/lj-1.672-report.md:105-109`).
- `dev/literature/glossary-review-2026-08.md`: declined. No glossary
  term is added. The Boundary forbids a self-chosen entry.
- `dev/literature/primary-sources.md`: not used. The slot-roles
  digest already carries the Devlin locator this D-10 spends.
- `dev/literature/devlin-errata.md`: not used. `[LJ-1.520]` already
  checked the errata against the formula
  (`agents/tasks/LJ-1-520/lj-1.520-report.md:102-113`). A measured
  cure does not transfer by analogy.
- `dev/literature/BIBLIOGRAPHY.md`: not used. No new source is cited.
