# Review of `sq-trunc-closed`

The obligation is not inhabited. This file is the obstruction, for the
branch `no-go-stated`.

## THE STATEMENT THE BRIEF NAMED

```
sq-trunc-closed :
    (α₀ : V ℓ) → IsOrd α₀
  → (δ : V ℓ) → ⟨ δ ∈ sucV α₀ ⟩ → (⟨ δ ∈ ω ⟩ → Empty.⊥)
  → ∥ sq δ ∥₁
```

It is `agents/tasks/LJ-1-440/LJ-1.440.md:11-15`. The brief names the home
`src/L/SquareLawClosed.lagda.md` (`LJ-1.440.md:9`) and one supplier:
`agents/tasks/LJ-1-437/lj-1.437-report.md` (`LJ-1.440.md:19-20`).

## THE PREMISE IS NOT IN THIS TREE

The named supplier file does not exist. Command:

    ls agents/tasks/LJ-1-437/lj-1.437-report.md

returns `No such file or directory`. The directory `agents/tasks/LJ-1-437/`
is also absent. `git ls-files 'agents/tasks/LJ-1-437/**'` is empty at this
worktree's HEAD `ea04f35`.

The brief's own stop rule is at `LJ-1.440.md:19-20`:

    READ `agents/tasks/LJ-1-437/lj-1.437-report.md` BEFORE ANYTHING ELSE.
    IF THAT FILE DOES NOT EXIST, OR ITS VERDICT IS NOT `GO`, WRITE
    NOTHING AND STOP.

Which of the two happened: **the file does not exist**. I did not reach a
verdict line. I did not inhabit the type. I did not write
`src/L/SquareLawClosed.lagda.md`. I did not edit `src/Everything.lagda.md`.
I did not edit `dev/ledger.toml`.

## THIS IS NOT A REFUTATION OF THE TYPE

I did not prove the named type false. I did not build a term of its
negation. I did not run Agda on the obligation. The obstruction is the
missing supplier report in the tree this task was given.

The independent audit named the same class of defect at
`dev/pod/audit-2026-08-20.md:34` (`F1 / F2. LJ-1.398 GO is hollow`) and at
`:40-42` (`the brief, not the result`). A landing built on a report that
this worktree cannot open is that defect.

## WHAT THE NEXT BRIEF NEEDS

Re-dispatch the landing on a tree that contains
`agents/tasks/LJ-1-437/lj-1.437-report.md` at the named path. Open that
report, quote its VERDICT at `file:line`, and quote the type the probe
inhabited. If that verdict is not `GO`, stop. If the type differs from
`LJ-1.440.md:11-15`, stop. Do not repair a mismatch by weakening the
obligation.
