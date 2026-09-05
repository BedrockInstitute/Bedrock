# Review of `chain-upper`

slot: `coder`. This file states the NO-GO that the brief's branch
`no-go-stated` asks for. Evidence is `file:line` throughout. No Agda
was written.

## THE STATEMENT, AS THE BRIEF NAMES IT

    chain-upper :
        AmbToCoded
      → (δ : V ℓ) → IsOrd δ → ⟨ δ ∈ˢ sucV α₀ ⟩ → (⟨ δ ∈ˢ ω ⟩ → Empty.⊥)
      → ⟪ Lset δ ⟫ ↪ ⟪ δ ⟫

The named file is `src/L/StageBound.lagda.md`. The named hypothesis is
`AmbToCoded` at the type `[LJ-1.414]` delivered
(`agents/tasks/LJ-1-414/Probe414.agda:134-139`).

I did not inhabit `chain-upper`. I did not inhabit `AmbToCoded`. I did
not postulate either. I did not write `src/L/StageBound.lagda.md`.

## THE STOP

The brief's first gate (`agents/tasks/LJ-1-444/LJ-1.444.md:27-29`) is:

    READ agents/tasks/LJ-1-442/lj-1.442-report.md BEFORE ANYTHING ELSE.
    IF THAT FILE DOES NOT EXIST, OR ITS VERDICT IS NOT GO, OR
    src/L/StageBound.lagda.md IS NOT IN THE TREE, WRITE NOTHING AND STOP.

Two of those three held in this worktree.

1. `agents/tasks/LJ-1-442/lj-1.442-report.md` is not in this tree.
   `ls agents/tasks/LJ-1-442` fails. `git ls-files` has no
   `LJ-1-442` path and no `src/L/StageBound.lagda.md`.
2. `src/L/StageBound.lagda.md` is not in this tree.
   `ls src/L/StageBound.lagda.md` fails. `src/Everything.lagda.md:393`
   imports `L.BoundedSubset` and the next import is
   `L.Choice.Transversal`. There is no `import L.StageBound`.

The third conjunct (verdict of 442) cannot be read from this tree,
because the report file is absent.

I wrote nothing under `src/`. I did not invent the master the brief
said `[LJ-1.442]` creates.

## WHAT A DESCENDANT COMMIT HOLDS, AND WHY IT IS NOT THIS TREE

This worktree is detached at `e41c233`
(`pod: admit LJ-1.444`). Commit `a983bb7`
(`pod: LJ-1.442 done, row task-lj-1-442-go`) is a descendant of that
HEAD. `git merge-base --is-ancestor HEAD a983bb7` holds.
`git merge-base --is-ancestor a983bb7 HEAD` fails.

`a983bb7` contains both files the gate asked for, including
`src/L/StageBound.lagda.md` (103 lines added) and
`agents/tasks/LJ-1-442/lj-1.442-report.md` (248 lines added). That
report's VERDICT line, read with `git show` and not from this tree,
opens `**GO.**`. The master in that commit lands
`bounded-from-trunc`, not `chain-upper`.

I did not check those files out. I did not merge `a983bb7`. The
brief's stop is on THIS tree. Copying a successor commit into this
worktree would invent the premise the gate said to refuse.

## D-10 ON THE HYPOTHESIS, DONE WITH NO AGDA

`[LJ-1.420]` is GO
(`agents/tasks/LJ-1-420/lj-1.420-report.md:53`).
`[LJ-1.414]` is **NO-GO on `amb-to-coded`**
(`agents/tasks/LJ-1-414/lj-1.414-report.md:51`).
That is why `AmbToCoded` enters the chapter as a PARAMETER and never
as a term.

The two types match projection for projection. See
`lj-1.444-report.md` section D-10. No mismatch. The stop is not a
type gap.

## WHAT WAS NOT DONE

No axiom. No postulate. No module parameter that asserts
`AmbToCoded`. No term `chain-upper` in `src/`. No edit of
`dev/ledger.toml`. No edit of `src/Everything.lagda.md`.

This is not a refutation of `chain-upper`. The type is the consumer's
own `stage-card-upper`
(`src/L/StageCardinal.lagda.md:564-565`), reached in a probe under
exactly one hypothesis (`agents/tasks/LJ-1-420/Probe420.agda:97-99`).
The obstruction is that the master the brief names is not in this
tree.
