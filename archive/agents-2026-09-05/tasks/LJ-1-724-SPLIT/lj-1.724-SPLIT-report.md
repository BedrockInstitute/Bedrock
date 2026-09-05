# LJ-1.724-SPLIT report: the corrected-scope `table-sat` probe

**NO-GO at the SPLIT scope, and the file is now fully green.** The obligation
`table-sat` is **not inhabitable at `ω ≤ γ`, `x + 2 < γ`**: the Step conjunct's
`DefAt` membrane demands its code, graph, index set and table inside
`A = Lset γ`, and the rank chain through them forces `rank z + 6 < γ` for every
`z ∈ᴬ Lset x` the Step's `extAt` clause reaches. At `γ = sucV (sucV (sucV x))`
with `x ≥ ω` all three hypotheses of the brief hold and the reading is false.
The refutation, the counterexample shape, and the scope the chain actually
demands (`ω ≤ γ`, `x + 6 ≤ γ`, or a limit-bounded frame) are in
`review-of-table-sat.md`, every link at its in-tree anchor. The obligation name
is absent from the probe on purpose; nothing lands in `src/`.

This return also REPAIRS the dispatch's own tooling debt and corrects one
false claim of the outgoing report (see "Corrections", below).

## Verdict, five sentences

1. The SPLIT scope fixed exactly what `[LJ-1.724]` measured: the pair and the
   table now fit under `A` (`pair-in-Lσ` is the leg 724's scope could not
   give: the pair's rank is `x+2` at the top, `sucV (sucV x) ∈ˢ γ` places it
   in `Lset γ`, and `γ ∈ˢ σ` reads off the bounding certificate's first
   constant via `ord∈Lset→∈`, `src/L/Ordinal/Stages.lagda.md:265-267`).
2. What fails is the membrane: `DefAt u w = extAt u (∃̇ ∃̇ (DefBody w))`
   (`src/L/Coding/Powerset.lagda.md:442-443`) binds its code and graph at
   `con A` once relativized (`src/FOL/Manipulation/Relativize.lagda.md:55-56`),
   `DefinesAt`'s ∧̇-form (`src/L/Coding/Powerset.lagda.md:217-220`) forces
   `envOne(z)` into the graph, and the witness record's clause
   `pr (fst (lookup x γ)) (fst (lookup y γ)) ∈ fst T`
   (`src/L/Coding/Graph.lagda.md:145`) forces `pr(code, graph)` into the table,
   with the table itself `∈ᴬ A`.
3. The rank chain is therefore `rank(graph) ≥ rank z + 3`,
   `rank(table) ≥ rank z + 6`, `rank(table) < γ` (`rank-Lset`,
   `src/L/Ordinal/Stages.lagda.md:190-191`), so `rank z + 6 < γ` for every
   `z ∈ᴬ w` the Step's `extAt` clause reaches, and `Lset x` has members of
   every rank below `x`.
4. At `γ = x+3`, `x ≥ ω`, the brief's three hypotheses hold and members of
   rank `> x−4` exist in `Lset x`: the reading is false there, so
   `pr x (Lset x) ∉ᴬ carved` at that `γ`.
5. The probe's door (`to-reading`/`from-reading` at the pair's own
   environment, both directions, both green in
   `runs/q-1.out`) reduces the obligation to the `A`-bounded reading of the
   recording exactly, so a future GO at the widened scope (`ω ≤ γ`,
   `x + 6 ≤ γ`) re-enters through `from-reading`; at a limit frame,
   `BoundOver` (`src/L/Coding/Bound.lagda.md:33-45`) is the in-tree closure
   engine the witnesses need, and whether `Lset` instantiates its five tower
   facts is a separate probe, not an analogy.

## Corrections to the outgoing report

- **"the Frame-only floor `runs/devframe.agda` at 3.1 s, completed clean" was
  false or unreproducible.** No `.out` for that run was kept, and this return
  re-ran the same file three times under the pane caliber: all three wall
  (`runs/devframe-t1.out` to `devframe-t3.out`, 2.03 GB at the 19 s sweep
  kills). The true reason is the leg below.
- **The wall was never (only) the box.** Every walling full-file run of this
  task inherited ONE broken leg: `pair-in-Lγ`. Measured pieces:
  - its second `Sum.rec` branch transported the goal along `sym eq`, the
    wrong direction: the isolated branch errors fast with `[UnequalTerms]`
    (`runs/devZp5-r1.out`);
  - `suc∈or≡`'s branches are `suc³x ∈ˢ γ` and `suc³x ≡ γ`, not `suc²x`
    (`runs/devZs4-r1.out`), so the equality branch is exact and the transport
    direction is `eq`;
  - with the direction fixed, the leg still walled (`runs/devZq-r2.out`,
    `runs/devZq2-r2.out`): leaving `Lset-mono`'s implicit `{α} {β} {x}` to
    inference under `Sum.rec` sends the unifier into the nested-singleton
    `sucV` encodings. Naming the implicits cures it: the isolated leg is
    green at 1.97 s (`runs/devZs5-r2.out`).
- The box story stands beside this, and it is real: the main-tree watchdog's
  swap-spiral trigger (`swap ≥ 8192 MB`) has killed the biggest agda every
  ~20 s sweep since 2026-08-28 22:32, at a sticky 8773-8781 MB swapused, and
  it killed the outgoing dispatch's runs, this return's first ~30 runs, and
  the other slot's runs in the same window. Runs are atomic (no interface
  survives a kill), so a check needs one <20 s gap between sweeps. The final
  green run took 27.42 s and survived because the other slot's process was
  the bigger agda at two intervening sweeps. That is luck, not a method; the
  swap state is owner tooling and only the owner can clear it.

## Deliverables

| Item | Location | Status |
|---|---|---|
| `dφ : Δ₀ φᵣ`, `γ ∈ˢ σ`, `Lset-self` | `Probe724Split.agda` (`Frame`) | green (`runs/q-1.out`) |
| `pair-in-Lγ` at the SPLIT scope, repaired | `Probe724Split.agda` (`Frame`) | green, same run |
| `pair-in-Lσ` | `Probe724Split.agda` (`Frame`) | green, same run |
| fiber `m`/`qm`/`xL`, `pairS`/`u`/`qenv` | `Probe724Split.agda` (`Frame.AtPair`) | green, same run |
| door `to-reading`/`from-reading`, both directions | `Probe724Split.agda` (`Frame.AtPair`) | green, same run |
| Obligation `table-sat` | `Probe724Split.agda` | **absent on purpose**: false at the SPLIT scope; `review-of-table-sat.md` carries the refutation |
| Review (NO-GO, chain, widened scope) | `review-of-table-sat.md` | filed, anchors re-verified |

## Runs

Harness: `runs/run.sh <file> <out> <cap>`; every `.out` records the pane
caliber (`GHCRTS=[-A64m -I0 -M2g]`, never set by the slot), start and end
stamps, `EXIT=` and max RSS.

| Run | Result | Notes |
|---|---|---|
| `runs/p-1.out` … `runs/p-10.out` (outgoing dispatch) | scope-error fixes | green commands, 26.18 s, 803 MB; body never checked |
| `runs/devframe-t1.out` … `-t3` | **wall** | the outgoing "3.1 s green floor" does not reproduce; 2.03 GB |
| `runs/devZ0-r2.out` | green 2.05 s, 626 MB | bare `Carved` application: the frame's floor |
| `runs/devZd-r1.out`, `runs/devZs-r1.out`, `runs/devZp1-r2.out`, `runs/devZp2-r1.out`, `runs/devZp4-r2.out`, `runs/devZs1-r1.out`, `runs/devZs2-r1.out` | green 1.9–3.3 s | leg pieces and statement types, each cheap alone |
| `runs/devZp-r2.out`, `runs/devZq-r2.out`, `runs/devZq2-r2.out` | **wall** 2.03 GB | `pair-in-Lγ` before the repair |
| `runs/devZp5-r1.out` | `[UnequalTerms]` 2.4 s | `sym eq` is the wrong transport direction |
| `runs/devZs4-r1.out` | `[UnequalTerms]` 2.1 s | `suc∈or≡`'s branches are `suc³x`, not `suc²x` |
| `runs/devZs5-r2.out` | **green 1.97 s, 626 MB** | the repaired leg, isolated |
| `runs/devZt-r2.out` | green 2.93 s, 607 MB | frame + fiber, no door |
| `runs/devZv-r1.out` | green 3.31 s, 612 MB | + `AtStage`/`AbsL` opens + `pairS`/`u`/`qenv`, no door terms |
| `runs/devZu-r1.out` … `-r4` | killed 16.3–19.2 s, 748 MB | fiber-stated door: memory fine, time over the sweep window |
| `runs/q-1.out` | **green 27.42 s, 755 MB** | THE FULL FILE: frame, fiber, door both directions |

One Agda process at a time throughout; ~60 measured runs in `runs/`, kept.

## What the next brief needs

- The statement is false at the SPLIT scope; do not re-queue it as stated.
- The corrected scope the chain demands is `ω ≤ γ` **and `x + 6 ≤ γ`**: the
  +4 over the SPLIT scope are the membrane's graph and table stages. At that
  scope GO is live and re-enters through `from-reading`.
- The frame alternative (limit `λ ≥ x + ω`, `A := Lset λ`) must first measure
  `Lset` against `BoundOver`'s five tower facts (`T-out`, `T-mono`, `T-pr`,
  `T-trans`, `T-ord`, `src/L/Coding/Bound.lagda.md:33-45`); none of the five
  is instantiated for `Lset` in the tree today, and each is its own probe.
- The full-file check is ~27 s and 755 MB at the wide caliber. It fits the
  caliber comfortably but NOT a 20 s window between swap-spiral sweeps. Until
  the box's swap state clears, any dispatch whose check exceeds ~19 s should
  expect sweeps to kill most attempts; a green run is obtainable but lucky.
- `⊨-transport` on relativized recordings was dropped in the outgoing
  dispatch for a 2 GB wall (`runs/p-11.out`); the shipped door transports
  environments by `subst` on the carrier pair (`qenv`) instead. That choice
  stands.

## W3, answered

The brief's W3 asked whether `T_x` as approximation inhabits the A-bounded
recording at `ω ≤ γ`, `x + 2 < γ`, estimate 80 to 160 lines. **NO at that
scope**: the approximation inhabits it, the Step conjunct's own shape is
satisfiable, and the membranes are what fail; the estimate was right for the
attack's size, and the attack is the review's chain plus the probe's legs.
The formal negative (deciding witness non-existence through the opaque
`carve`) was not attempted, on the same price grounds as 724's.

## Key evidence

- `src/L/Axioms/Separation.lagda.md:163-168`: `carveSat`, the door's engine;
  `:219-229`: `imageOut`/`imageIn`, the in-tree door the probe applies.
- `src/FOL/Manipulation/Relativize.lagda.md:55-56`: raw quantifiers bound at
  `con A`; `:142-148`: `relativize-correct`.
- `src/L/Coding/Powerset.lagda.md:217-220,437-443`: `DefinesAt`'s ∧̇-form,
  `DefBody`, `DefAt`.
- `src/L/Coding/Graph.lagda.md:140-147`: the witness shape: index set, table,
  carrier, and the record pair `pr(...) ∈ fst T`.
- `src/L/Ordinal/Stages.lagda.md:190-191`: `rank-Lset`; `:265-267`:
  `ord∈Lset→∈`.
- `src/L/Coding/Sequence.lagda.md:119-120`: `StepAt`; `src/L/Coding/Model.lagda.md:662-673`:
  `extAt` and its reading, the clause that reaches every `z ∈ᴬ w`.
- `src/L/Coding/Bound.lagda.md:33-45`: `BoundOver`, the limit-frame route.
- `src/L/Definability.lagda.md:178`: `defSet ⊤̇ ≡ A`; `src/L/Axioms/Basic.lagda.md:196`:
  `Lset-suc`.

## Notes

- The wide caliber was the program's (`GHCRTS=[-A64m -I0 -M2g]`, in every
  `.out` header); I never set it. One Agda process at a time.
- W2: no generic carrier was written here; the probe re-measures 724's frame
  legs at the new scope and adds the scope arithmetic. The refusal to build
  the limit-frame version on analogy is the W2-relevant fact: the cure does
  not transfer without measuring `Lset` against `BoundOver`'s five facts.
- The scratch bisection files (`runs/dev*.agda`) are probe-run artifacts under
  `runs/`, kept because they are the price measurements the next heavy
  dispatch at this frame will want.
- The watchdog is the main tree's process (`/Users/alsg/Agentic/Bedrock/
  scripts/ops/agda-watchdog.sh`, newer than the worktree's copy); its log is
  `_build/tools/agda-watchdog.log` there. I did not rename, alias or shield
  the agda process.

## ARCHIVE USED

Every candidate was opened for this return. This return is a target
refutation and a scope measurement inside one probe, built from live `src/`
and `agents/tasks/` files only, so each archived record is declined with the
reason.

- `archive/dev/ORCHESTRATION.md:1`: "# ORCHESTRATION: the orchestrator's
  operating rules": read. It governs dispatch and landing of work; this
  return makes no dispatch or landing decision of its own. Declined.
- `archive/dev/DD-archived.md:1`: "# THE `DD` RULING SERIES, archived in
  full 2026-08-18": read. The frozen DD rows are superseded by
  `dev/pod/rulings.toml`, and no row of them is cited here. Declined.
- `archive/dev/PLAN-archived.md:1`: "# ARCHIVED 2026-08-20": read. The live
  plan is `dev/pod/screen.toml` and `dev/pod/queue.toml`; the archived plan
  adds nothing to a scope refutation. Declined.
- `archive/dev/STATUS-archived.md:1`: "# STATUS-archived: the goal table of
  the internalization route": read. That route left the tree on 2026-08-09,
  before the `Carved` frame existed. Declined.
- `archive/dev/TASKS-archived.md:1`: "# Archived task index: the `L3.32-T`
  series": read. The retired `L3.32-T` series predates the `LJ-1` campaign
  this task belongs to. Declined.

## LITERATURE USED

Every candidate was opened for this return. The refutation reads the tree's
own coding and stage machinery, so the external-account notes are out of
scope here.

- `dev/literature/devlin-errata.md:1`: "# Devlin errata: documented error
  classes (do-not-repeat checklist)": read. The checklist covers external
  accounts of constructibility; the obstruction here is measured inside the
  tree's own frame. Declined.
- `dev/literature/glossary-review-2026-08.md:1`: "# Glossary review: the
  119 pre-protocol entries": read. This return adds no term to
  `dev/glossary.toml` and cites none. Declined.
- `dev/literature/rudimentary-functions.md:1`: "# Rudimentary functions,
  closure, and the comprehension theorem": read. The rud-route closure facts
  play no role in the rank chain or the membrane reading. Declined.
- `dev/literature/level-formula-slot-roles.md:1`: "# The level-hood
  formula: arity, what it binds, what stays free": read. The level formula's
  slots bear on no step of the chain; the graph here is `PairGraphAt`, not
  the level formula. Declined.
- `dev/literature/primary-sources.md:1`: "# Primary sources, second round:
  Jensen manuscript, Devlin, Jech": read. The fetched texts back external
  claims; this return asserts only what the tree's own files prove.
  Declined.
