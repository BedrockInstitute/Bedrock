# LJ-1.684 report: adequacy at the bounded graph, bridge as hypothesis

## HEAD
head_slot: coder
machine: shared
agda_tier: wide
task: LJ-1.684
obligation: agents/tasks/LJ-1-684/Probe684.agda::adequacy-bnd
verdict: **GO. `adequacy-bnd` is `Lset-defines` composed with
`[LJ-1.681]`'s bridge as a HYPOTHESIS, DOWN. The value equation is
consumed at the unbounded graph. The bound is the hypothesized
bridge. The equation is not rewritten.**

The obligation is green and metered (`runs/meter-obligation.out`,
`pass exit=0 2.18 s`, `0 UNRESOLVED of 1`, `probe_red=False`). The
delivered probe is green (`runs/p-1.out`, EXIT=0, 2.04 s).

**READ THESE FIVE SENTENCES BEFORE YOU QUEUE ANYTHING.**

1. **THE TERM IS THE COMPOSITION, NOT THE BRIDGE.** `adequacy-bnd`
   (`Probe684.agda:91`, body at `:83`) takes `Bridge` and returns
   `⟨γ ⊨ graphBndAt⟩` from `IsOrd` and `v ≡ Lset γ`. It does not
   inhabit `Bridge`. That is `[LJ-1.681]`'s obligation.
2. **THE DIRECTION IS DOWN.** Adequacy spends
   `LsetGraphAt → graphBndAt`. `[LJ-1.162]` already has UP
   (`ProbeLJ1162A.agda:218-222`). A hypothesized UP would not
   compose with `Lset-defines`.
3. **W2 IS THE DELIVERED `Lset-defines` AND THE DELIVERED `GraphB`,
   NOT A NEW LEMMA.** `src/L/Hierarchy.lagda.md:645-648` already
   quantifies over `n`, `w`, `b`. `src/L/Condensation.lagda.md:2486-2493`
   is already generic in the two leaves. The probe instantiates
   both. The body is one line (`Probe684.agda:83`). A deadline does
   not force a fixed-`n` copy and does not force `DefBodyB`.
4. **`ApproxInK` STAYS UNINHABITED.** `[LJ-1.532]` refuted it
   (`Probe532.agda:206-209`). This file does not take that type.
   The hypothesized `Bridge` is at ONE environment, `K` a slot of
   `GraphB` (`src/L/Condensation.lagda.md:2488`). A BARE `∀K` form
   is false if `K` may be empty.
5. **681 STILL OWES `HierInK`, NOT `ApproxInK`.** The corrected
   membership is `hierL β ∈ Lset α` (`Probe532.agda:274-277`), plus
   the inner approx and step agreements `[LJ-1.162]` took as site
   facts (`ProbeLJ1162A.agda:211-216`) and `powK` (`:140-141`).
   This file does not discharge them.

Written as a skeleton before any Agda beyond the predecessor read
and filled as each answer landed (C-22). No commit, no push. I wrote
only inside `agents/tasks/LJ-1-684/`. Agda ran under the caliber the
program set on this pane, `GHCRTS="-A64m -I0 -M2g"`, the WIDE tier,
ONE Agda process at a time. I did not set `GHCRTS`. Nothing is
postulated, the delivered probe carries `--safe` and no hole, and
nothing lands in `src/`. The probe is a raw `.agda` file, so it
carries no ` ```agda ` fence, counts 0 in-fence lines, and the
ratio bar cannot fire on it.

The standing direction (`dev/pod/direction.md:37`) says one SRC
collection after LJ-1, not after `[LJ-2.5]`. This task is still LJ-1
work. It does not start that collection and it does not start phase 3.
No Boundary clause is in conflict. W4 does not apply: no module is
retired.

**EVERY NUMBER BELOW IS MEASURED WITH A WARM `src/` INTERFACE CACHE**
(the Hierarchy interface was already present under `_build/` at the
start of the floor run). No number here is a cold-cache number, and
this report does not bound one.

**NO HEAP WALL WAS MET ANYWHERE IN THIS TASK.** The highest peak of
any run is 608,894,976 bytes against the 2,147,483,648-byte wide cap
(`runs/floor-1.out`), which is 28 percent of it. The longest Agda
run is 2.40 s (`runs/floor-1.out`) against the 300 s floor cap and
the 600 s default. The caps are wall-clock caps enforced by a perl
alarm (`runs/run.sh`).

## 1. THE PREDECESSOR QUESTION, ANSWERED BEFORE ANY AGDA

The standing coder clause says: take the type from the probe that
typechecked, and the verdict from the report. If the report is NO-GO,
or names the statement FALSE, do not inhabit that type.

`[LJ-1.681]` is a sibling, not a closed predecessor. This worktree
has no `agents/tasks/LJ-1-681/` directory and no 681 probe. The
queue names 681 as that bridge (`dev/pod/queue.toml:6737`). The 684
brief names that sibling and says to take the bridge as a
HYPOTHESIS so this file does not wait
(`agents/tasks/LJ-1-684/LJ-1.684.md:12`, `:43`).

The type I take for the hypothesis is the reverse of the direction
`[LJ-1.162]` delivered, at the same generic carrier.

| piece | type | site | verdict |
|---|---|---|---|
| `Graph.up` | `graphBndAt → LsetGraphAt` | `ProbeLJ1162A.agda:218-222` | GO, site-fact telescope |
| `Lset-defines` | `IsOrd` and `v ≡ Lset γ` to `LsetGraphAt` | `src/L/Hierarchy.lagda.md:646-648` | GO, in `src/` |
| `LeafAgree` | `DefBodyB` against `DefBody` | `src/L/Condensation.lagda.md:7224` | GO, in `src/`; not ridden here |
| `kernel-sat` | class-carrier Σ₁ transfer, arity `4 + n` | `Probe676.agda:97-101` | GO; not rebuilt |
| `ApproxInK` | every `ApproxAt` witness lies in `K` | `Probe532.agda:108-117` | **FALSE** (`:206-209`). Not inhabited. |
| `HierInK` | `hierL β ∈ Lset α` | `Probe532.agda:274-277` | TYPE, green; not inhabited. 681's debt. |
| `sat-at-level` | `[LJ-1.666]` | `Probe666.agda:26` | NO-GO. Not inhabited. |
| `sound-at-arity4` | `[LJ-1.669]` | `Probe669.agda:8-9` | NO-GO. Not inhabited. |

None of those reports names this composition FALSE. The one FALSE
type is `ApproxInK`, which is a different statement. This file
inhabits the composition, not the membership.

The brief's premise 3 cites `src/L/Condensation.lagda.md:2492` as
`LeafAgree`. That line is `graphBndAt`. `LeafAgree` is at `:7224`.
I take the type from `:7224` and I do not ride it.

## 2. D-10, BEFORE THE PROOF IS PRICED

The recorded residue is adequacy at the bounded graph, named by
`[LJ-1.676]` as what its own file does not close
(`lj-1.676-report.md:208-214`).

The target, given the bridge, is composition of `Lset-defines` with
that bridge. I did not find a Tarskian or cardinality obstruction
to the COMPOSITION. The bridge type itself is 681's target.

`ApproxInK` is false (`Probe532.agda:206-209`). A BARE
`∀ K. LsetGraphAt → graphBndAt` is also false if `K` may be empty:
`LsetGraphAt` does not mention `K`. The hypothesis is at ONE
environment, `K` a slot of `GraphB`
(`src/L/Condensation.lagda.md:2488`). I do not quantify over every
`K`.

The schematic type in this brief omitted `IsOrd`. `Lset-defines`
requires it (`src/L/Hierarchy.lagda.md:646`). I added it. That is
not a weakening of the conclusion.

Corrected remaining target beside this GO: 681 still owes `HierInK`
(`Probe532.agda:274-277`), not `ApproxInK`, plus the inner approx
and step agreements `[LJ-1.162]` took as site facts
(`ProbeLJ1162A.agda:211-216`) and `powK` (`:140-141`). Instantiation
at `DefBodyB` / `LevelHood` is a later consumer, not this file.

C-42 does not fire. This is not a refutation of a site. No false
shape was counted.

## 3. THE FLOOR, MEASURED BEFORE ANY PROOF

Coder clause, owner 2026-08-23: price the frame before the term. The
floor is the obligation TYPE with a hole where the body stands. It
is `.agda.txt` and not `.agda`, because every `.agda` under a task
home is a verification target.

**THE FRAME COSTS 2.40 s AND 609 MB, AND IT DOES NOT WALL.**
`runs/floor-1.out`: exit 42 at 2.40 s, peak 608,894,976 bytes, one
error and it is the designed hole (`[UnsolvedInteractionMetas]` at
`FLOOR.agda:63`). **The obligation TYPE is well-formed.** No import
trim beyond `src/` was required. Predecessor probes were not
imported: the types they delivered are restated, each cited at the
line they were read.

P-l is observed: the type names `GraphB.graphBndAt` at generic
leaves, so the twelve-row table does not unfold. The 662 wall was
the chapter's `LevelHood` matrix, which this file does not name.

The repair of the hole is the one-line composition
`br γ (Lset-defines w b γ ob q)` (`Probe684.agda:83`). That is a
new shape, not a rerun of the floor file.

| run | file | exit | wall s | peak bytes |
|---|---|---:|---:|---:|
| `floor-1` | `runs/FLOOR.agda.txt` as `.agda`, then restored | 42 | 2.40 | 608,894,976 |
| `p-1` | delivered probe | 0 | 2.04 | 608,026,624 |
| meter | `witness.py --brief` | 0 | 2.18 | 599,097,344 |

## 4. W3, THE WIDEST UNMEASURED TERM

The brief names it: whether the value equation survives the bound.
Estimate 100 to 220 lines, basis `[LJ-1.676]`
(`lj-1.676-report.md:1`).

**GO. THE VALUE EQUATION IS CONSUMED BEFORE THE BOUND.**
`Lset-defines` takes `IsOrd` and `v ≡ Lset γ` and returns
`⟨γ ⊨ LsetGraphAt w b⟩` (`src/L/Hierarchy.lagda.md:646-648`). The
hypothesized `Bridge` then carries that to `graphBndAt`
(`Probe684.agda:83`). The equation does not mention `K`. The bound
is 681's problem, not a rewrite of the equation.

The estimate is void for a rebuilt lemma: there is none. The
delivered probe is 91 lines, 36 code. The new mathematics is the
telescope at generic `m` and the one-line composition.

**WHAT THIS TERM IS NOT.** It is not the bridge. It is not
`ApproxInK`. It is not `⟨δ ⊨ levelHoodB⟩`. `[LJ-1.676]` already
has the Σ₁ transfer of `levelHoodB` (`Probe676.agda:97-101`). This
file closes the inner graph conjunct of that matrix, conditionally
on the bridge, at generic leaves. Instantiation at `DefBodyB` is
not in this count because it is not written.

## 5. W2 ANSWER

W2: write the mathematics once at a generic carrier and instantiate it.

`Lset-defines` already does that (`src/L/Hierarchy.lagda.md:645`).
`GraphB` already does that (`src/L/Condensation.lagda.md:2486`).
This probe instantiates both at generic `m`, `ψs`, `ψa`, `w`, `b`,
`K`. Instantiation at `n = 0` is the same term. Instantiation at
`DefBodyB` is LevelHood's instance
(`src/L/BoundedSubset.lagda.md:81-105`) and a later consumer.

A deadline does not apply. There is no conflict with a fixed form.
Do not fund a second copy at `n = 0`. Do not fund the composition
again at `LevelHood`.

## 6. WHAT THE SHAPE RESISTED

- **What it cost.** Floor 2.40 s, 609 MB. Probe 2.04 s, 608 MB.
  Witness 2.18 s, 599 MB. File 91 lines, 36 code. No heap wall.
- **What the shape resisted.** Nothing of the composition. The
  schematic type omitted `IsOrd`; `Lset-defines` requires it, so
  the telescope carries it. The schematic type named `graphBndAt`
  without `K`; `K` is a slot of `GraphB` and sits in the
  environment.
- **What I had to weaken.** Nothing of the obligation. I did not
  inhabit a smaller type and call it `adequacy-bnd`.
- **What I could not close.** The bridge itself. `HierInK`. The
  `DefBodyB` instance. The full `levelHoodB` packing
  `∃̇∈ K (graphBndAt ∧̇ v ≐ w)`.

## 7. WHAT THE NEXT BRIEF NEEDS

- **If the consumer is this composition.** `adequacy-bnd` is
  delivered at generic leaves, arity `m`, `K` a slot, DOWN
  (`Probe684.agda:77-83`, lifted at `:91`). Apply it. Do not
  rebuild it.
- **If the consumer is 681's bridge.** Take DOWN at one
  environment. Do not inhabit `ApproxInK`. The corrected
  membership is `HierInK` (`Probe532.agda:274-277`). The inner
  frames are `[LJ-1.162]`'s `approx-up` / `step-up` and their
  reverses, plus `powK` (`ProbeLJ1162A.agda:140-141`, `:211-216`).
  UP is already `Graph.up` (`:218-222`).
- **If the consumer is `⟨δ ⊨ levelHoodB⟩`.** This file closes the
  inner graph conjunct, conditionally. The outer packing is
  `∃̇∈ K (graphBndAt ∧̇ v ≐ w)`
  (`src/L/BoundedSubset.lagda.md:108-111`) and still needs `v ∈ K`
  after the value equation. `[LJ-1.676]` already has the Σ₁
  transfer of that matrix. Do not rebuild the transfer.
- **If the consumer instantiates at `DefBodyB`.** That is
  LevelHood's instance. This file stayed generic in the leaves on
  purpose. Instantiation is one module application.
- **Do not re-dispatch this composition.** The 100-to-220-line
  estimate was for a rebuilt lemma about the value equation. There
  is none.
- This task changed nothing in `src/`.

## 8. PRICE

| item | measured |
|---|---|
| floor (imports + type; designed hole) | 2.40 s, 608,894,976 bytes, EXIT=42 |
| delivered probe | 2.04 s, 608,026,624 bytes, EXIT=0 |
| witness meter | 2.18 s, 599,097,344 bytes, 0 UNRESOLVED of 1, `probe_red=False` |
| file lines / code lines | 91 / 36 |
| brief estimate | 100 to 220 lines |
| in-fence lines | 0 (raw `.agda`) |
| caliber | `-A64m -I0 -M2g`, never set here |
| heap wall | none |
| `src/` edits | none |

The estimate was high because the value equation does not have to
survive the bound as a rewritten lemma. `Lset-defines` consumes it
at the unbounded graph. The probe is the instantiation plus the
one-line composition. Nothing of 100 to 220 lines was needed, and
nothing of that length was written.

## ARCHIVE USED

- `archive/dev/ORCHESTRATION.md:1` `# ORCHESTRATION: the orchestrator's operating rules`. Declined: not used. This dispatch composes a live `src/` term with a hypothesized sibling bridge, not archived dispatch rules.
- `archive/dev/DD-archived.md:1` `# THE `DD` RULING SERIES, archived in full 2026-08-18`. Declined: not used. The live W2 home is the coder slot file, not this archive.
- `archive/dev/PLAN-archived.md:1` `# ARCHIVED 2026-08-20`. Declined: not used.
- `archive/dev/STATUS-archived.md:1` `# STATUS-archived: the goal table of the internalization route`. Declined: not used.
- `archive/dev/TASKS-archived.md:1` `# Archived task index: the `L3.32-T` series`. Declined: not used.

## LITERATURE USED

- `dev/literature/level-formula-slot-roles.md:35` `### 2.1 The free pair is the VALUE and the ORDINAL, in every source`. Read. Adequacy is the value equation at those two slots. `K` is the bound, not a free pair.
- `dev/literature/level-formula-slot-roles.md:60` `Devlin's `∃w` carries the conjunct `K(w,u)`, "which says `w = K(u)`"`. Read. The hypothesized `Bridge` is at ONE environment, `K` a slot. That matches a determined bound better than a BARE `∀K` form, which is false if `K` may be empty.
- `dev/literature/devlin-errata.md:1` `# Devlin errata: documented error classes (do-not-repeat checklist)`. Declined: not used. The term is a live composition, not a Devlin erratum.
- `dev/literature/glossary-review-2026-08.md:1` `# Glossary review: the 119 pre-protocol entries`. Declined: not used.
- `dev/literature/primary-sources.md:1` `# Primary sources, second round: Jensen manuscript, Devlin, Jech`. Declined: not used. Slot roles already cite those sources.
- `dev/literature/BIBLIOGRAPHY.md:1` `# Bibliography for the rud route`. Declined: not used.
