# Review of `bounded-modulo-collect`

The obligation is not inhabited. This file is the obstruction, for the
branch `no-go-stated`.

## THE STATEMENT THE BRIEF NAMED

```
bounded-modulo-collect : SqCollect α → ⟨ x ∈ˢ Lset κ ⟩
```

with

```
SqCollect : S → Type (ℓ-suc ℓ)
SqCollect α =
    ((δ : S) → ⟨ δ ∈ˢ sucV α ⟩ → (⟨ δ ∈ˢ ω ⟩ → Empty.⊥) → ∥ sq δ ∥₁)
  → ∥ SqFam α ∥₁
```

It is `agents/tasks/LJ-1-443/LJ-1.443.md:11` and `:16-19`. The brief names
the home `src/L/StageBound.lagda.md` (`LJ-1.443.md:9`) and two suppliers:

- `agents/tasks/LJ-1-442/lj-1.442-report.md` (`LJ-1.443.md:29-31`)
- `agents/tasks/LJ-1-440/lj-1.440-report.md` (`LJ-1.443.md:32-34`)

## WHICH OF THE TESTS FAILED

The brief's stop rule is at `LJ-1.443.md:27-34`:

    READ TWO REPORTS BEFORE ANYTHING ELSE, AND STOP IF EITHER FAILS
    THE TEST.

Both tests failed. Command:

    test -f agents/tasks/LJ-1-442/lj-1.442-report.md
    test -f agents/tasks/LJ-1-440/lj-1.440-report.md
    test -f src/L/StageBound.lagda.md
    test -f src/L/SquareLawClosed.lagda.md

Each returns absent. `git ls-files` of those four paths is empty at this
worktree. I did not reach a VERDICT line on either named report. I did
not inhabit the type in `src/`. I did not write `src/L/StageBound.lagda.md`.
I did not edit `src/Everything.lagda.md`. I did not edit `dev/ledger.toml`.

## AGDA OVER THE NAMED HOME

`agents/tasks/LJ-1-443/Probe443NoGo.agda:16` is the import

    open import L.StageBound

`agda --safe` exits 42. Quote of `runs/nogo-1.out:5`:

    /Users/alsg/Agentic/Bedrock/.pod-state/worktrees/LJ-1-443/agents/tasks/LJ-1-443/Probe443NoGo.agda:16.1-25: error: [FileNotFound]

Wall 0.22 s, peak RSS 116883456 bytes, caliber `-A64m -I0 -M8g`. No heap
event. This is the runner fact the branch `no-go-stated` keys on
(`LJ-1.443.md:227-229`, `exit_code = 42`).

## W3, NOT THE OBSTRUCTION

`domains-meet` typechecks as the identity
(`agents/tasks/LJ-1-443/Probe443.agda:37-40`, exit 0, median 1.29 s).
The supply spelling and the consumer spelling meet. The join is not the
reason the obligation is uninhabited.

## THIS IS NOT A REFUTATION OF THE TYPE

I did not prove `SqCollect` false. I did not prove
`bounded-modulo-collect` false. I did not run Agda on the obligation in
`src/`. The obstruction is the missing supplier reports and the missing
masters in the tree this task was given. The FileNotFound is that
absence, as a typecheck.

The independent audit named the same class of defect at
`dev/pod/audit-2026-08-20.md:34` (`F1 / F2. LJ-1.398 GO is hollow`) and
at `:40-42` (`the brief, not the result`). A landing built on a report
that this worktree cannot open is that defect.

## WHAT THE NEXT BRIEF NEEDS

Re-dispatch the join on a tree that contains all four named paths:

- `agents/tasks/LJ-1-442/lj-1.442-report.md`
- `src/L/StageBound.lagda.md`
- `agents/tasks/LJ-1-440/lj-1.440-report.md`
- `src/L/SquareLawClosed.lagda.md`

Open each report, quote its VERDICT at `file:line`, and quote the type
the predecessor inhabited. If either verdict is not `GO`, stop. If either
master is absent, stop. If a delivered type differs from
`LJ-1.443.md:11` or `:16-19`, stop. Do not repair a mismatch by
weakening the obligation. Do not hide a repackaging inside a `subst`.
W3 already says the family telescope needs no `subst`.
