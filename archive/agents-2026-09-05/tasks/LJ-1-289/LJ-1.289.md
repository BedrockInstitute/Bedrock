# LJ-1.289: land the `sucV∈` respelling, about 476 seconds

tier: opus (in-harness-subagent-mode), model `opus`. I ran scripts/dispatch_policy.py before dispatching: in-harness-subagent-mode is IN FORCE, clock-selected, PEAK, Beijing window 14:00 to 18:00.

## GOAL

Land the cure [LJ-1.287] measured. `src/L/Coding/EnvSupply.lagda.md` costs about 480 s and the cure takes it to about 4 s for three lines.

**This is the largest single lever this project has measured.**

## THE FINDING, and it overturned three diagnoses including the orchestrator's

[LJ-1.287] bisected the cost six ways in one run and charged everything to ONE conversion:

| arm | ms |
|---|---:|
| `v3` shallow-index generic form instantiated deep (R-35, R-40's cure) | 454,449 |
| **`v4` `sucIter 4 δ` against `sucV (sucV (sucV (sucV δ)))`, body `p = p`** | **438,043** |
| `v1`, `v2`, `v5`, `v6` | not charged |

**438 seconds for an identity function.** Depth is free. **The MIXED SPELLING of the level is what costs.** The in-file control proves it: `envSetK` at `src/L/Coding/EnvSupply.lagda.md:143-146` has depth 4, ONE spelling, and 11 ms. I verified both sites myself.

**THE CURE, three lines:** delete `sucIter` from `sucK`'s `step` and climb by `succλ`, which is already a module parameter at `src/L/Coding/EnvSupply.lagda.md:108`. **`sucV∈`'s BODY does not change. Only its declared level does.**

## PREMISES

- Control n=3 mean 480.25 s, spread 2.3 percent; treated n=4 mean 4.10 s, best 3.65 s. Three cycles, the third with the treated arm FIRST. At `agents/tasks/LJ-1-287/lj-1.287-report.md`. **RE-DERIVE the control on the master before you edit**, and use agda's own `--profile` Total as [LJ-1.287] did, with wall time as a cross-check only.
- `sucV∈` vanishes from the profile after the cure: `grep -c` returns 0 on both profiled treated runs. The new climb costs 18 ms. VERIFY.
- `succλ` is a module parameter at `:108` and is tower-neutral. VERIFY it is in scope at `sucK`.
- `sucK` is a REQUIRED `EnvClosure` field at `src/L/Coding/Key.lagda.md:568`, so the field cannot be dropped, only respelled. Its statement never mentions a chain, so the respelling is free at the interface. VERIFY, because this is what makes the cure landable rather than a redesign.

## THE ABORT CRITERION, fixed BEFORE the run (D-1)

- **IT LANDS AND THE MASTER DROPS.** Report your control, the treated time, the delta, and the profile showing `sucV∈` gone. STOP.
- **A CONSUMER NEEDS THE OLD SPELLING.** C-40. Name it at `file:line`. `src/L/Coding/EnvSupply.lagda.md` is a leaf by [LJ-1.287]'s grep, with only its own header and `src/Everything.lagda.md:382` naming it, but CHECK rather than trust that (C-44).
- **THE INTERFACE FIELD WILL NOT TAKE THE NEW SPELLING.** Then `Key.lagda.md:568` constrains it and the cure is a redesign. Say so and stop; do not edit `Key.lagda.md`.
- **THE DELTA IS SMALLER ON THE MASTER THAN ON THE PROBE.** Report both. A probe is not a master and P-l binds even between two spellings of the same file.
- **A WALL.** The control alone is about 480 s. **A single agda invocation past 30 MINUTES is a wall**: interrupt, report elapsed seconds, bisect. Report a heap exhaustion as a wall and NEVER raise the cap.

## CONSTRAINTS

- ONE agda process at a time, always `GHCRTS="-A64m -I0 -M8g"`. The cap is C-12's and is NEVER raised. Report the machine load beside every absolute figure, discard a warm-up, take at least three kept cold runs per arm with the interface deleted between them, and REVERSE the order in one cycle.
- Your write territory is `src/L/Coding/EnvSupply.lagda.md` and `agents/tasks/LJ-1-289/`. NOTHING else under `src/`.
- **Do not edit `src/L/Coding/Key.lagda.md`.** It is delivered and it holds the interface.
- Never `src/Everything.lagda.md`, never `dev/ledger.toml`, never `dev/PLAN.md`, never `src/L/Choice/Name.lagda.md` (DD23 blocks a pending change).
- **A SIBLING MAY BE LIVE** in another `agents/tasks/` directory. Touch only your own.
- C-45: `exit 0` is not a supply. Prove the landing by re-running something that IMPORTS the master, as [LJ-1.277], [LJ-1.279] and [LJ-1.282] all did.
- Create `agents/tasks/LJ-1-289/lj-1.289-report.md` in your first five minutes and fill it incrementally (C-22).
- Never commit, never push, never git checkout ., git stash, git reset --hard, git clean. Do not run make check.
- Run `.venv/bin/python scripts/lint-prose.py --check` and `scripts/lint-agda.py --check` on what you write. NO EM DASH in any language. DD23 freezes mathematical prose: code and its own comments only.
- Count with `.venv/bin/python scripts/ledger.py`, the only admissible source for a size figure.
- Evidence is `file:line`. Write ASD-STE100. Mark every negative MEASURED or INFERRED, in those words.
- Run `.venv/bin/python scripts/rules.py --for build` and read every statement; open the full entry for any law you act on.

## THE TWO LAWS THIS CHAIN JUST WROTE, and they bear directly

**C-50, written today: profile before you cure.** [LJ-1.287] obeyed it and that is the only reason this cure exists. **Three diagnoses were refuted by the profile**, including R-35 and R-40's shallow-index restatement, which is `v3` at 454,449 ms and does NOT cure, and including the orchestrator's own pre-measurement reading.

**AND THE SEAL'S BLIND SPOT WAS MEASURED.** [LJ-1.287] replayed [LJ-1.283]'s void seal arm under the profiler: 467.53 s with 462,830 ms, 99.25 percent, charged to `lev4-mem d x h = h`, **which is `v4` verbatim**. The seal cleared `sucV∈` completely and paid the identical bill inside the read lemma that made it usable. **A seal moves a cost; it does not remove one.** Keep that in mind if you are tempted to seal anything here.

**C-42, the sweep, and it is NOT yours to run but you must not disturb it:** [LJ-1.287] flagged `src/L/Coding/Key.lagda.md:424-429` as carrying the same mixed spelling at depths 1 to 3, never profiled. That is a CANDIDATE for a later task. Do not touch it.

## DD4

Maximize the code the two proofs share, and write it generic. One rule, two ends, no metric and no checker.

[LJ-1.287] measured this master a LEAF in neither trophy closure, so the cure moves DD4's ratio by ZERO and must not be justified by it. On REUSE the cure removes a supplier and adds none, resting the step on the module's own tower-neutral `succλ`. **Say whether that holds after your edit**, and NAME YOUR AXIS (C-46): DD4's own axis is AC-against-GCH, fixed at `scripts/ledger.py:50`.

Separately, [LJ-1.287] measured `union∈Lset-suc` duplicated 55 lines across `src/L/Coding/Key.lagda.md:504-560` and `src/L/Coding/EnvSupply.lagda.md:148-202`. **That is a LINE lever worth under 100 ms and it is NOT this task.** P-q: a line lever and a seconds lever are different levers. Do not bundle it.

## ARCHIVE (DD18)

`agents/tasks/LJ-1-287/lj-1.287-report.md` read WHOLE, the bisect and the cure; `agents/tasks/LJ-1-287/`'s arm files, so you land the arm that was measured and not a re-derivation of it; `agents/tasks/LJ-1-283/lj-1.283-report.md`, the void seal whose bill was later located; `agents/tasks/LJ-1-276/lj-1.276-report.md`, how this master was landed; `archive/dev/TASKS-archived.md`, taking SHAPE and never a claim. Return an ARCHIVE USED section naming ONE line read per archived file.

## LITERATURE (DD18)

Nothing in the literature governs elaboration cost. Say so in one line and return a LITERATURE USED section.

## SCOPE (read)

`agents/tasks/LJ-1-287/lj-1.287-report.md` FIRST, whole.

## SCOPE (write)

`src/L/Coding/EnvSupply.lagda.md` and `agents/tasks/LJ-1-289/` only.

## RETURN

Lead with your own control, the treated cold seconds, the delta, and the new whole-file rate against the 0.010514 bar. Then the profile showing `sucV∈` gone. Then each premise VERIFIED or REFUTED at `file:line`. Then the re-run that PROVES the landing. Then every consumer you checked. Then the DD4 answer with its axis. Mark every negative MEASURED or INFERRED.

End your final message with: your control, the treated time, the delta, and whether any consumer needed the old spelling.
