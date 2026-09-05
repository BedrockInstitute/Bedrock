# LJ-1.722 report: completeness-from-ambient, at the heavy cap

STATUS: **NO-GO, BY HEAP WALL AT HEAVY.** The term is built, complete
in shape, and transcribed byte-exact from `[LJ-1.717]`'s delivered
shape; its elaboration exceeds the heavy caliber's 4 GB cap, and so
does the BARE BRIDGE ALONE with everything else deleted. The brief's
GO branch is unreachable at every admissible caliber. Delivered as
`Probe722.agda.txt` (the naming rule: a file that cannot typecheck is
never `.agda`), with the NO-GO stated in
`review-of-completeness-from-ambient.md`. `obligations` stays at 0.

## The obligation

`completeness-from-ambient : AmbientAt-at-hier → HierInStage →
Completeness` in `agents/tasks/LJ-1-722/Probe722.agda.txt`, the
delivered shape of `[LJ-1.717]` (Probe717.agda.txt), which 717 named
as reopenable at a heavier tier. The brief bars a new bridge; none was
invented. Nothing landed in `src/`.

## Transcription fidelity

The body (first import line to EOF) diffs against Probe717.agda.txt's
body in EXACTLY ONE line: the module name (`LJ-1-717.Probe717` →
`LJ-1-722.Probe722`). Checked by `diff` after the fill; the header
comment is new prose outside the body.

## Measured, all at the pane caliber (heavy, `-A64m -I0 -M4g`, never
## set by this agent; one Agda process per run; every record carries
## GHCRTS, stamps and EXIT=)

| run | shape | result |
|---|---|---|
| runs/floor.out | the frame: every type ascribed, both `⊨ᵐ` satisfaction ascriptions included, all four proof bodies holed | GREEN AT HOLES: 130.94 s, 1.86 GB; unsolved metas ONLY at the four designed holes (runs/floor.out:12-18) |
| runs/full.out | the delivered shape, verbatim | WALL: 868.86 s, `agda: Heap exhausted; Current maximum heap size is 4294967296 bytes (4096 MB)` (runs/full.out:4-5), EXIT=251 (runs/full.out:25) |
| runs/b1-bridge.out | `matrix-mapped-at` and the term holed: amb application + atL subst at the real witness triple, alone | WALL: 821.29 s, heap exhausted, EXIT=251 (runs/b1-bridge.out:25) |
| runs/b2-bridgebare.out | the BARE bridge: general-vector `atL-backwards` (subst at `sym (Cy.atL P667.Δ₀-matrix₃ v)`), ONE ambient application at the hier triple, the membership subst; the term's witness triple, transport and assembly are all absent (the only Code-typed residue is the membership subst's own signature, as delivered) | WALL: 790.94 s, heap exhausted, EXIT=251 (runs/b2-bridgebare.out:25) |

B1 and B2 are new probes of this dispatch, built per the heap-wall
clause (owner's ruling 2026-08-23: restructure or narrow, and TEST the
new shape under the same cap, before reporting a wall). Their sources
are `runs/B1-bridge.agda.txt` (B1 cut from the delivered file, module
renamed) and `runs/B2-bridgebare.agda.txt` (reconstruction of 717's
stage8, whose source was not delivered; rebuilt from the stage8 record
at `.pod-state/worktrees/LJ-1-717/agents/tasks/LJ-1-717/lj-1.717-report.md:72`).
Both are red by design or by wall, so both are named `.agda.txt`.

## What the numbers say

1. **The frame is not the wall.** The floor holds every ascription,
   including both big satisfaction types, and is green at 1.86 GB.
2. **The bridge is the wall, and it is alone sufficient.** B2 walls at
   790.94 s with the whole term deleted; the full shape walls at
   868.86 s. The rest of the term adds about 10 percent on top of the
   bridge's cost. No term-level split can fit, because the surviving
   fragment already exceeds the cap, and splitting definitions does
   not reclaim memory (717's p-4/p-5/stage7: 2.68/2.62/2.62 GB).
3. **The brief's premise 2 is measured FALSE at this site.** The
   overage at wide was ~25-30 percent over 2 GB (peak 2.62 GB), so the
   brief estimated heavy fits. The same shape exceeds 4 GB under
   `-M4g`. The heap a shape needs is CAP-DEPENDENT: under the bigger
   cap the runtime collects later, and the live set at abort was over
   4 GB, not 2.6 GB. A price measured under one cap does not transfer
   to another. This is a new measured law candidate for
   `dev/LESSONS.md`, and it invalidates the tier-escalation estimate
   that 717's "next brief needs" item 1 rested on.
4. **W3, answered NO.** The brief's W3 asked whether the amb-to-atL
   bridge checks at `-M4g`. It does not: the bare bridge walls. GO
   required the term at a cap the bridge fits; no admissible cap fits
   the bridge.

## What the shape resisted

Nothing new at the shape level: 717's five shapes plus this
dispatch's two narrowed shapes cover the split space, and the wall
survives with everything holed around the bridge. The remaining cure
is not a shape. It is 717's option 3 (an AbsL-side ambient hypothesis
that deletes the `atL` bridge), which is the mathematician's call and
the next brief's move
(`.pod-state/worktrees/LJ-1-717/agents/tasks/LJ-1-717/lj-1.717-report.md:151-153`).
A heavier cap is not available: superheavy is not a task tier no brief
can reach (`dev/pod/heads.toml:340-341`), and setting GHCRTS is never
the coder's act.

## W2

Written once at the generic frame: the term is 717's, living in
`Spend` with its telescope verbatim, and every supplier it reads
(`atL`, `BoundInStage`, `HierInStage`, `matrix₃`, `Δ₀-matrix₃`) is
imported, not copied. The transcription's only deltas are the module
name and the header prose. Instantiation is trivial: this file is the
only instance and nothing lands in `src/`.

## W4

No module is retired by this task. Nothing moves to `archive/`; no
`dev/ARCHIVE.md` row is owed. The probes of this dispatch stay beside
the report in `runs/`, tracked and never deleted (that is the rule at
`dev/ARCHIVE.md:118`: "a probe beside its report. Nothing else sends a
probe to `archive/`.").

## P-l

`AmbientAt-at-hier` is about the concrete triple `(Lset δ, δ, hierL δ)`
but its TYPE quantifies over `δ : CS.S` abstractly, as at 717. B2's
`atL-backwards` quantifies over `v : F.HS.ASt.SL ^ 3` abstractly. No
`⟪ sucV … ⟫`-style transparent presentation is named in any statement
type here.

## D-10

The target's truth is not the finding; the budget is. The pins were
settled at 717 (premise 3 of this brief: the pins never read a code
backwards, `val` is never inverted) and are not reopened. The
hypothesis is consumed without needing to be satisfiable. Supplying a
stage triple where matrix₃ holds stays the mathematician's side.

## For the next brief

1. **The AbsL-side ambient hypothesis (717's option 3).** It deletes
   the single most expensive ingredient. With it, the term reduces to
   717's stage4-plus-pins shape, which was green at 1.72 GB even at
   wide.
2. **Do not re-escalate the caliber for this shape.** Measured here:
   the requirement grows with the cap, so "one tier up" is not a price
   anyone can promise. If the owner ever prices superheavy for THIS
   shape, the estimate needs a fresh measurement AT that cap, not an
   extrapolation.
3. The bare-bridge probe (`runs/B2-bridgebare.agda.txt`) is the
   reusable isolation harness: any replacement hypothesis can be
   priced against it before a full term is attempted.

## Survey check

Command: `.venv/bin/python scripts/pod/check-survey-quotes.py LJ-1-722`
(run with the main checkout's pinned interpreter; this worktree has no
`.venv`, as at 717). Output, pasted:

```text
check-survey-quotes: LJ-1-722 clean (0 note(s), 0 defect(s))
CHECKER-EXIT=0
```

## ARCHIVE USED

- `archive/dev/DD-archived.md` -- declined, not read. This dispatch
  needed only this task's runs, the 717 task home, and live `src/`
  facts; no archived ruling was opened.
- `archive/dev/ORCHESTRATION.md` -- declined, not read.
- `archive/dev/PLAN-archived.md` -- declined, not read.
- `archive/dev/TASKS-archived.md` -- declined, not read.
- `archive/dev/STATUS-archived.md` -- declined, not read.
- `dev/ARCHIVE.md` (read, not an injected candidate) -- one row bears
  on where this dispatch's probes may live: `dev/ARCHIVE.md:118`
  carries, verbatim: "a probe beside its report. Nothing else sends a
  probe to `archive/`."

## LITERATURE USED

- `dev/literature/level-formula-slot-roles.md` -- READ. It is the one
  literature line that fixes the slot roles the bridge's three
  existential witnesses fill; the NO-GO is a verification-budget
  verdict and reopens nothing about that arithmetic.
  `dev/literature/level-formula-slot-roles.md:26` carries, verbatim:
  "| 4 | Devlin 5.2 (a) | `Φ(z,v,γ)` with `∀v∀γ [v = L_γ ↔ ∃z
  Φ(z,v,γ)]` | 3 in `Φ`, ONE closed | `z` at position 0 | `v` at 1,
  `γ` at 2 | **VALUE, ORDINAL** |
  `_build/literature/dev2.txt:1186-1191` |". The witness slot is the
  one closed by an existential: exactly the slot the term's outer
  witness fills with the table.
- `dev/literature/primary-sources.md` -- declined, not read.
- `dev/literature/glossary-review-2026-08.md` -- declined, not read.
- `dev/literature/BIBLIOGRAPHY.md` -- declined, not read.
- `dev/literature/devlin-errata.md` -- declined, not read.
