# Review of `bounded-modulo-collect`

slot: `coder`. Instance 2. This file states the STOP that the brief's
branch `stop-stated` asks for. Evidence is `file:line` throughout.
I did not inhabit the obligation. I did not claim `SqCollect` is false.

## THE STATEMENT, AS THE BRIEF NAMES IT

    bounded-modulo-collect : SqCollect α → ⟨ x ∈ˢ Lset κ ⟩

with

    SqCollect : S → Type (ℓ-suc ℓ)
    SqCollect α =
        ((δ : S) → ⟨ δ ∈ˢ sucV α ⟩ → (⟨ δ ∈ˢ ω ⟩ → Empty.⊥) → ∥ sq δ ∥₁)
      → ∥ SqFam α ∥₁

The body the brief names feeds `L.SquareLawClosed`'s `sq-trunc-closed`
into that hypothesis, then hands the result to
`src/L/StageBound.lagda.md:100-101`.

## VERDICT

**STOP.** The named obligation is already inhabited on the campaign
tree. `[LJ-1.453]` closed at `a7978f4` with row
`sys-obligations-satisfied`
(`agents/tasks/LJ-1-449/runs/campaign-commits.out:8` and
`agents/tasks/LJ-1-449/runs/campaign-453-stat.out:5`). Its brief
supersedes this task
(`agents/tasks/LJ-1-449/runs/campaign-453-brief.out:7`). Its report
verdict is GO
(`agents/tasks/LJ-1-449/runs/campaign-453-verdict.out:3`). The term
stands at `agents/tasks/LJ-1-449/runs/campaign-stagebound.out:11`:

    bounded-modulo-collect : SqCollect α → ⟨ x ∈ˢ Lset κ ⟩

Writing the same term into this stale fork would duplicate that GO
and would fight the campaign chapter on merge.

## THIS WORKTREE'S GATE, RECORDED AND NOT THE VERDICT

The brief at `agents/tasks/LJ-1-449/LJ-1.449.md:31-33` still fails
test 2 inside this worktree:

- `agents/tasks/LJ-1-449/runs/gate-check-2.out:12`:
  `ls: agents/tasks/LJ-1-445/lj-1.445-report.md: No such file or directory`
- `agents/tasks/LJ-1-449/runs/gate-check-2.out:13`:
  `ls: src/L/SquareLawClosed.lagda.md: No such file or directory`

HEAD is `706a6e2` (`agents/tasks/LJ-1-449/runs/gate-check-2.out:3`).
Instance 1 stopped on that gate. Two critic returns overturned it
(`agents/tasks/LJ-1-449/review-of-LJ-1-449-1.md:6`,
`agents/tasks/LJ-1-449/review-of-LJ-1-449-2.md:6`). This instance
re-measured the campaign branch. Test 2 fails only in the fork. On
`pod-cutover` both gates pass, and the obligation is already landed.

The first gate still passes here.
`agents/tasks/LJ-1-442/lj-1.442-report.md:55` opens the verdict with
`**GO.**`. `src/L/StageBound.lagda.md:10` is the module line.
`src/Everything.lagda.md:394` imports it.

## WHAT THIS DOES NOT SAY

This STOP is not a NO-GO on `SqCollect`. The brief at
`agents/tasks/LJ-1-449/LJ-1.449.md:121` forbids that claim. Nothing in
this tree refutes `SqCollect`. The type is in the campaign chapter at
`agents/tasks/LJ-1-449/runs/campaign-stagebound.out:5`.

W3 in this task is GO. `agents/tasks/LJ-1-449/Probe449.agda:42` is the
identity, exit 0, median 1.14 s. The two spellings meet with no
repackaging.

## WHAT WAS NOT DONE

No import of `L.SquareLawClosed` in this worktree.
No `SqCollect` added to this chapter.
No `bounded-modulo-collect` added to this chapter.
No postulate.
No axiom.
No `--safe`-off escape.
No change to `src/`.
No change to `dev/ledger.toml`.
