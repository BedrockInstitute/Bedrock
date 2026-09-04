# Review of `completeness-from-ambient` (LJ-1.722): NO-GO AT HEAVY

Verdict: **NO-GO**. The term
`completeness-from-ambient : AmbientAt-at-hier → HierInStage → Completeness`
is built, complete in shape, and transcribed byte-exact from
`[LJ-1.717]`'s delivered shape (the body diffs in exactly one line, the
module name). It does not typecheck at the heavy caliber. The file is
delivered as `agents/tasks/LJ-1-722/Probe722.agda.txt` (the naming
rule: a file that cannot typecheck is never `.agda`).

## The measurement

All runs at the pane caliber `-A64m -I0 -M4g` (heavy), one Agda
process per run, never set by the agent. Each record carries GHCRTS,
stamps and `EXIT=`.

| record | shape | result |
|---|---|---|
| `runs/full.out` | the delivered shape, verbatim | 868.86 s, `agda: Heap exhausted; Current maximum heap size is 4294967296 bytes (4096 MB)` (runs/full.out:4-5), `EXIT=251` (runs/full.out:25) |
| `runs/b1-bridge.out` | `matrix-mapped-at` and the term holed: the amb application + atL subst at the real witness triple, alone | 821.29 s, heap exhausted, `EXIT=251` (runs/b1-bridge.out:25) |
| `runs/b2-bridgebare.out` | the BARE bridge, everything of the term deleted: general-vector `atL-backwards`, one ambient application at the hier triple, the membership subst | 790.94 s, heap exhausted, `EXIT=251` (runs/b2-bridgebare.out:25) |
| `runs/floor.out` | the frame: every type ascribed (both `⊨ᵐ` satisfaction ascriptions included), all four proof bodies holed | GREEN AT HOLES: 130.94 s, 1.86 GB peak, unsolved metas only at the four designed holes (runs/floor.out:12-18) |

## Why this is a NO-GO and not a shape problem

The heap-wall clause (owner's ruling 2026-08-23) was honored before
this verdict: two narrowed shapes were built and tested under the same
cap, not the delivered shape alone.

1. B1 deletes the formula transport and the final assembly. It walls.
2. B2 deletes EVERYTHING except the bridge. It walls, at nearly the
   same price (790.94 s vs 868.86 s).
3. The floor, which holds every ascription including both big
   satisfaction types, is green at 1.86 GB: the frame is not the wall.

So the wall is the elaboration of the bridge itself, a single `subst`
at `sym (Cy.atL P667.Δ₀-matrix₃ …)` applied to one ambient
application. No term-level split can fit, because the surviving
fragment already exceeds the cap. This reproduces 717's stage8
isolation at the new cap: at wide the bridge alone exceeded 2.55 GB
(`.pod-state/worktrees/LJ-1-717/agents/tasks/LJ-1-717/lj-1.717-report.md:72`),
and here the same fragment exceeds 4 GB.

The brief's premise 2 (overage ≈25-30 percent over 2 GB, so heavy
fits) is measured FALSE at this site: the same shape that peaked at
2.62 GB under `-M2g` (717 `runs/p-5.out`) exceeds 4 GB under `-M4g`.
The heap a shape needs is cap-dependent: the runtime collects later
under the bigger cap and the live set at abort was over 4 GB, not
2.6 GB. A price measured under one cap does not transfer to another.

## What is NOT reopened

The 717 W3 pins stand (premise 3 of the brief): the pins never read a
code backwards; `val` is read only code-to-value; the packing is TRUE
at this frame. This NO-GO is a verification-budget verdict, not a
refutation. The mathematics of the delivered shape is exactly as 717
left it; what is new is the measured fact that no admissible caliber
carries it.

## What reopens it

717's option 3, unchanged: an AbsL-side ambient hypothesis, stated as
AbsL satisfaction at the triple, which deletes the `atL` bridge, the
single most expensive ingredient
(`.pod-state/worktrees/LJ-1-717/agents/tasks/LJ-1-717/lj-1.717-report.md:151-153`).
That is a mathematician's call and the next brief's move. Not a third
wide attempt, and not a heavier cap: superheavy is not a task tier
(`dev/pod/heads.toml:340-341`).
