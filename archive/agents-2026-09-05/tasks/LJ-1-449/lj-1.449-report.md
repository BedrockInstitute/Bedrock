# LJ-1.449 report: state the truncated route's one open statement

slot: `coder`. Instance 2 of this task. Written early as a skeleton and
filled as the gate and the W3 probe landed (C-22). No commit, no push.
I did not set `GHCRTS`. One Agda process at a time. No heap event.

TARGET: land ONE term in `src/L/StageBound.lagda.md`:

    bounded-modulo-collect : SqCollect α → ⟨ x ∈ˢ Lset κ ⟩

with `SqCollect` stated once in that chapter, generic in `α`.

## THE GATES, BEFORE ANY AGDA

The brief at `agents/tasks/LJ-1-449/LJ-1.449.md:27-33` names two tests
and says: write nothing and stop if either fails.

**Test 1, `[LJ-1.442]`, PASSES in this worktree.**

The file `agents/tasks/LJ-1-442/lj-1.442-report.md` exists
(`agents/tasks/LJ-1-449/runs/gate-check-2.out:8`). Its VERDICT line is
`agents/tasks/LJ-1-442/lj-1.442-report.md:55`:

    **GO.** The obligation typechecks at

`src/L/StageBound.lagda.md` is in the tree
(`agents/tasks/LJ-1-449/runs/gate-check-2.out:9`). The module line is
`src/L/StageBound.lagda.md:10`. The consumer term is
`src/L/StageBound.lagda.md:100-101`. `src/Everything.lagda.md:394`
imports the master.

**Test 2, `[LJ-1.445]`, FAILS in this worktree.**

The file `agents/tasks/LJ-1-445/lj-1.445-report.md` does not exist
(`agents/tasks/LJ-1-449/runs/gate-check-2.out:12`):

    ls: agents/tasks/LJ-1-445/lj-1.445-report.md: No such file or directory

`src/L/SquareLawClosed.lagda.md` is not in the tree
(`agents/tasks/LJ-1-449/runs/gate-check-2.out:13`):

    ls: src/L/SquareLawClosed.lagda.md: No such file or directory

This worktree is detached at `706a6e2`
(`agents/tasks/LJ-1-449/runs/gate-check-2.out:3`). Instance 1 of this
task stopped on that same test. Two critic returns overturned that
stop, at `agents/tasks/LJ-1-449/review-of-LJ-1-449-1.md:6` and
`agents/tasks/LJ-1-449/review-of-LJ-1-449-2.md:6`, both
`verdict: overturned`. They ordered a re-measure against the campaign
branch. This instance did that measure. It did not repeat the instance 1
stop as the verdict.

## D-10, THE CAMPAIGN TREE

`pod-cutover` stands 27 commits past this HEAD
(`agents/tasks/LJ-1-449/runs/campaign-commits.out:2`).

`[LJ-1.445]` closed at `ee7ef37`
(`agents/tasks/LJ-1-449/runs/campaign-commits.out:5`):

    ee7ef373c29deb88999600d1694145ef56b3197d 2026-08-21 10:02:17 +0800 pod: LJ-1.445 done, row task-lj-1-445-go

That commit's report verdict is
`agents/tasks/LJ-1-449/runs/campaign-445-verdict.out:3`:

    **GO.** The obligation typechecks at the delivered type

The supply master is in that commit at
`agents/tasks/LJ-1-449/runs/campaign-squarelawclosed.out:1` and `:3`:

    module L.SquareLawClosed {ℓ : Level} (lem : LEM (ℓ-suc ℓ))
    sq-trunc-closed :

`[LJ-1.453]` closed at `a7978f4`
(`agents/tasks/LJ-1-449/runs/campaign-commits.out:8`):

    a7978f472c99b1670141d1006d33a13730392803 2026-08-21 11:42:02 +0800 pod: LJ-1.453 done, row sys-obligations-satisfied

The commit subject is the same at
`agents/tasks/LJ-1-449/runs/campaign-453-stat.out:5`:

    pod: LJ-1.453 done, row sys-obligations-satisfied

That task names the same obligation. Its brief says it supersedes this
one, at `agents/tasks/LJ-1-449/runs/campaign-453-brief.out:7`:

    **THIS TASK SUPERSEDES `[LJ-1.443]` AND `[LJ-1.449]`, WHICH NAME THE SAME

Its report verdict is
`agents/tasks/LJ-1-449/runs/campaign-453-verdict.out:3`:

    **GO.** The obligation typechecks at

The campaign chapter holds the term this brief names, at
`agents/tasks/LJ-1-449/runs/campaign-stagebound.out:11`:

    bounded-modulo-collect : SqCollect α → ⟨ x ∈ˢ Lset κ ⟩

`SqCollect` is at `agents/tasks/LJ-1-449/runs/campaign-stagebound.out:5`:

    SqCollect : S → Type (ℓ-suc ℓ)

The catalog on that commit has the supply before the consumer:
`agents/tasks/LJ-1-449/runs/campaign-everything.out:1`
`import L.SquareLawClosed`, and
`agents/tasks/LJ-1-449/runs/campaign-everything.out:9`
`import L.StageBound`.

## VERDICT

**STOP.** The named obligation is already inhabited on the campaign
tree by `[LJ-1.453]`, which supersedes this task. The obstruction is
`agents/tasks/LJ-1-449/review-of-bounded-modulo-collect.md`.

This is not a NO-GO on `SqCollect`. The brief at
`agents/tasks/LJ-1-449/LJ-1.449.md:121` forbids that claim.
Nothing in this tree refutes `SqCollect`. The statement is in the
campaign chapter. Writing it again in this fork would duplicate a
committed GO at `a7978f4` and would fight that chapter on merge.

This worktree still lacks `L.SquareLawClosed`, so an import of that
module cannot resolve here. That is the instance 1 gate. It is not
the reason for this stop. The reason is the campaign landing.

The standing direction says one SRC collection after LJ-1, not after
`[LJ-2.5]` (`dev/pod/direction.md:37`). This task is still LJ-1 work.
It does not start that collection. It does not start phase 3. No
Boundary clause is in conflict. The prose freeze did not conflict:
I wrote no mathematical prose and no narrative section in a master.

## 1. What was built

- `agents/tasks/LJ-1-449/Probe449.agda`, the W3 identity.
- `agents/tasks/LJ-1-449/runs/gate-check-2.out`, the live `ls` of both
  tests in this worktree.
- `agents/tasks/LJ-1-449/runs/campaign-*.out`, the `git show` record of
  the campaign landing.
- `agents/tasks/LJ-1-449/runs/w3-1.out` through `w3-4.out` and the
  matching `.time` files.
- `agents/tasks/LJ-1-449/review-of-bounded-modulo-collect.md`, the STOP
  the branch `stop-stated` reads.
- This report.

`SqFam` is already in this chapter at
`src/L/StageBound.lagda.md:33-37`. `bounded-from-trunc` is already in
this chapter at `src/L/StageBound.lagda.md:100-101`. I did not add
`SqCollect`. I did not add `bounded-modulo-collect`. I did not change
`src/`. I did not change `dev/ledger.toml`.

## D-10 ON THE TWO SPELLINGS

Supply type, still only in a probe in this worktree,
`agents/tasks/LJ-1-437/Probe437.agda:345-348`:

    sq-trunc-closed :
        (δ : V ℓ) → ⟨ δ ∈ sucV α₀ ⟩ → (⟨ δ ∈ ω ⟩ → Empty.⊥)
      → ∥ sq δ ∥₁

That probe's report is GO (`agents/tasks/LJ-1-437/lj-1.437-report.md:17`).

Consumer family, in this chapter, `src/L/StageBound.lagda.md:33-37`:

    SqFam : S → Type (ℓ-suc ℓ)
    SqFam α =
      (δ : S) → ⟨ δ ∈ˢ sucV α ⟩ → (⟨ δ ∈ˢ ω ⟩ → Empty.⊥)
      → Σ[ f ∈ (⟪ δ ⟫ × ⟪ δ ⟫ → ⟪ δ ⟫) ]
          ((u v : ⟪ δ ⟫ × ⟪ δ ⟫) → f u ≡ f v → u ≡ v)

`S` of `𝒮ᵥ` is `V ℓ` (`src/V/Hierarchy.lagda.md:80`).
`_∈ˢ_` of `𝒮ᵥ` is `_∈_` (`src/V/Hierarchy.lagda.md:83`).
`sq` is the Sigma (`src/L/Ordinal/SquareLaw.lagda.md:685-687`).

Whether those two telescopes are the same type, definitionally, is W3.
The probe is the identity. The measured answer is below. I do not hide
a gap in a `subst`.

## W2 (DD4)

The brief asks for `SqCollect` once, generic in `α`, with no band,
no numeral, and no site. I wrote no `SqCollect` in this tree. The
campaign chapter already holds that generic form at
`agents/tasks/LJ-1-449/runs/campaign-stagebound.out:5`. The W3 probe
is generic in `{ℓ}` and `(α : V ℓ)`
(`agents/tasks/LJ-1-449/Probe449.agda:23-24`). No band, no numeral,
no site. There is no conflict with a deadline.

W4 does not fire: no module was retired.

## W3, THE WIDEST UNMEASURED TERM

`domains-meet` as the identity, in
`agents/tasks/LJ-1-449/Probe449.agda:39-42`. Obligation omitted from
the chapter. Body is `domains-meet z = z`. Caliber `-A64m -I0 -M8g`,
one Agda process at a time, from the repository root. I did not set
`GHCRTS`. The pane already had `GHCRTS=-A64m -I0 -M8g`
(`agents/tasks/LJ-1-449/runs/gate-check-2.out:5`).

**GO. The identity typechecks.** Every run printed `Checking`. Exit 0
every time. No heap event. The two landed telescopes are the same type
definitionally. The join is free.

First check:

| run | wall s | peak RSS (bytes) |
|---|---|---|
| `runs/w3-1.out` | 1.40 | 348323840 |

Three forced rechecks, interface removed before each run:

| run | wall s | peak RSS (bytes) |
|---|---|---|
| `runs/w3-2.out` | 1.13 | 348241920 |
| `runs/w3-3.out` | 1.14 | 348241920 |
| `runs/w3-4.out` | 1.17 | 348241920 |

Median wall of the three rechecks **1.14 s**. Median peak RSS
**348241920** bytes. Each printed
`Checking LJ-1-449.Probe449`
(`agents/tasks/LJ-1-449/runs/w3-2.out:1`).

The W3 estimate was three lines and under one second on top of the
chapter's own cost. The probe is 42 lines and the median is 1.14 s.
That is the measured number, not the guess. It is not a factor of two
against one second, and it is not a chapter cost. The probe does not
import `L.StageBound`.

`[LJ-1.453]` measured the same identity as GO at
`agents/tasks/LJ-1-449/runs/campaign-453-w3.out:8`. A measured cure
does not transfer by analogy. This task re-measured at its own site.

## WHAT THE JOIN COST

Nothing. The identity is the join. No repackaging. No `subst`. The
supply spelling `(δ : V ℓ)` with `∈` and the consumer spelling
`(δ : S)` with `∈ˢ` convert by the two record fields of `𝒮ᵥ` named
above. On the campaign tree, `sq-trunc-closed` applies to `SqCollect`'s
hypothesis as a function argument
(`agents/tasks/LJ-1-449/runs/campaign-stagebound.out:13`).

## THE RATIO

Measured seconds on the chapter: none. I did not change
`src/L/StageBound.lagda.md`. In-fence line count added: 0.
The bar is 0.0123 seconds per in-fence line. A raw `.agda` probe
carries no fence and counts 0. There is no chapter rate to report.
The probe median is 1.14 s, recorded above.

## WHAT IS LEFT

`[LJ-1.447]` and `[LJ-1.448]` state the same counting-leg residue as
a statement about two ordinals, not as a choice principle. This task
does not rank the two routes.

`SqCollect` is already one type in the campaign tree for `[LJ-2.5]`
to rule on. It is not inhabited. This fork does not hold that type.

## make check

I did not run `make check`. I did not change a master under `src/`.
The brief asks for `make check` before and after chapter changes.
There were no chapter changes.

`scripts/measure/ledger.py --brief` is the standing size source. I
did not change `dev/ledger.toml`.

## ARCHIVE USED

- `archive/dev/LJ-dispatch-index.md:1`. Quote: `# THE `LJ` DISPATCH INDEX, archived 2026-08-18`. Declined, not used. It is the retired dispatch index. This task stopped on a live campaign landing.
- `archive/dev/JOURNAL.md:1`. Quote: `# ARCHIVED 2026-08-20`. Declined, not used. The per-episode journal is retired. The history of this task is this directory.
- `archive/dev/ORCHESTRATION.md:1`. Quote: `# ORCHESTRATION: the orchestrator's operating rules`. Declined, not used. The live operating rules are `AGENTS.md` and the slot file.
- `archive/dev/DD-archived.md:1`. Quote: `# THE `DD` RULING SERIES, archived in full 2026-08-18`. Declined, not used. The live clauses that bind this slot are W2 and W4.
- `archive/dev/DECISIONS-archived.md:1`. Quote: `# Archived decisions: the D series`. Declined, not used. The live decision list is not this gate.

## LITERATURE USED

- `dev/literature/truncation-and-selection.md:158`. Quote: `A type X has a constant endomap if and only if it has split`. Used: that is the Kraus criterion the brief names as premise 9. `SqCollect` is the collection type, not an endomap, and this task does not pay the endomap.
- `dev/literature/devlin-II5.md:1`. Quote: `# Devlin II.5: the Condensation Lemma and the GCH in L`. Declined, not used. This task did not land a condensation step.
- `dev/literature/digest.md:1`. Quote: `# Digest: the orthodox form of the rud route, pinned from the collected literature`. Declined, not used. No rud-route step is consulted.
- `dev/literature/geology.md:1`. Quote: `# Geology dossier: set-theoretic geology sources and the five questions`. Declined, not used. Geology is not this join.
- `dev/literature/terms-2026-08.md:1`. Quote: `# The terminology dossier: fourteen renderings for the owner's ruling`. Declined, not used. No glossary term is at issue.

## WHAT I DID NOT DO

- I did not commit. I did not push.
- I did not set `GHCRTS`.
- I did not start a second Agda process.
- I did not change `src/L/StageBound.lagda.md`.
- I did not change `src/Everything.lagda.md`.
- I did not change `dev/ledger.toml`.
- I did not inhabit `SqCollect`.
- I did not postulate `SqCollect`.
- I did not claim `SqCollect` is false.
- I did not read `[LJ-1.443]`'s brief.
- I did not take a type from `[LJ-1.443]`.
- I did not pad a chapter. I wrote no chapter line.
