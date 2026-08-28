# LJ-1.733 report: `defat-fill-in-bound`, the bounded DefAt fill

(This skeleton was written before the first Agda run and filled as the
runs landed; see C-22, `dev/LESSONS.md:2307`.)

## HEAD

head_slot: coder
machine: shared
agda_tier: wide
task: LJ-1.733
obligation: agents/tasks/LJ-1-733/Probe733.agda::defat-fill-in-bound
verdict: **NO-GO, STATED.** The obligation's type is stated, not
inhabited, and the clause of `dev/pod/instructions/coder.md` (a module
hypothesis taken from a predecessor) is what forbids the inhabitant:
two of the three module hypotheses carry NO-GO reports naming the
statement FALSE, and the third has no delivered type from any probe.
The premise set is INCONSISTENT, machine-checked at this file's own
restated type: `envSet-hypothesis-closes-bottom`
(agents/tasks/LJ-1-733/Probe733.agda:311, chain at :236-309) closes
`Empty.⊥` from one hypothesis alone, so the obligation's type is
vacuous (Probe733.agda:308-311, chain at :229-301).
review-of-defat-fill-in-bound.md is the NO-GO's home. The
file is green, EXIT=0 (`runs/p-2.out`), under
`--cubical --safe --guardedness`, no postulate, no hole. Nothing lands
in `src/`. The names `stage-read` and the unbounded `fill` appear in
comments only.

## 0. THE PREDECESSOR QUESTION

The coder clause binds every module hypothesis to the type its
predecessor delivered and to the verdict that predecessor's report
records. The brief rests the obligation on three module hypotheses.
Their state in the tree, measured this dispatch:

| hypothesis | predecessor's delivery | verdict there |
|---|---|---|
| `keyS-in-carrier-stage` | agents/tasks/LJ-1-729/Probe729.agda, Section 5 (the type, stated) | NO-GO, the type is FALSE at the stated generality; corrected scope `keyS-in-carrier-lim` under `closedω γ` is INHABITED (agents/tasks/LJ-1-729/review-of-keyS-in-carrier-stage.md, HEAD) |
| `envSet-in-carrier-stage` | agents/tasks/LJ-1-730/Probe730.agda:116 (the type, stated) | NO-GO, the type is FALSE, machine-checked by `envSet-in-carrier-stage-false` (agents/tasks/LJ-1-730/Probe730.agda:208; runs/p-11.out EXIT=0) |
| `Sat-in-carrier-stage` | NOTHING. LJ-1.731 has no probe, no report and no review in any worktree; its worktree carries only the brief (`.pod-state/worktrees/LJ-1-731/agents/tasks/LJ-1-731/LJ-1.731.md`) | none exists |

The clause says: if the report is NO-GO or names the statement FALSE,
stop and say so with `file:line`, and do not inhabit the brief's type.
Two of the three hypotheses are in that case, and the third has no
delivered type from any probe. So this task is a stop, stated in
review-of-defat-fill-in-bound.md.

No predecessor verdict is contradicted: 730's review explicitly owed
the sweep of the false shape across the sibling sites (its section
"The sweep, owed before the next GO price"), and Section 3 of the probe
is that sweep's second measurement.

## 1. WHAT WAS BUILT

1. The three hypothesis types, RESTATED, not imported
   (`Probe733.agda:123-162`): hypothesis 1 verbatim from the 729 probe's
   Section 5, hypothesis 2 verbatim from the 730 probe, hypothesis 3
   transcribed from the 731 BRIEF's obligation block, the only source
   in any worktree, and labelled as such in the file.
2. The obligation's TYPE, stated with no inhabitant
   (`Probe733.agda:176-190`), the brief's glyphs verbatim up to the two
   resolutions recorded in the file's header: the V-level membership
   renamed `∈ˢᵥ` (the 725-SPLIT disambiguation), and the
   Powerset-local `toS`/`DA` resolved at top level (`toS A ψ`,
   `DefOf.defSet (fst A) ψ`). The landed `DefBody` is imported from
   `src/L/Coding/Powerset.lagda.md` -- the obligation is about the
   landed formula, so restating it would drift.
3. The W3 measurement (`Probe733.agda:192-311`): 730's counterexample
   objects and rank chain, rebuilt here from landed masters only --
   the Boundary's rule that a measured result is re-measured at its
   own site -- and exported eating the HYPOTHESIS FUNCTION:
   `envSet-hypothesis-closes-bottom : envSet-in-carrier-stage →
   Empty.⊥` instantiates the restated hypothesis at
   `(γ₂, oγ₂, ω∈γ₂, Ace, hA₂, 1)` and closes `Empty.⊥` by the four
   `rank-mono` links, `rank-Lset`, the two `∈sucV-elim` descents and
   `∈-irrefl`.

## 2. THE FLOOR AND THE RUNS

Per the heavy-object rule the floor was priced first: p-1 is the whole
frame -- the import cone through `L.Coding.Powerset`, all four stated
types -- with the membrane absent. It is green at 1.97 s, so the frame
is not the cost. p-2 is the verdict run on the delivered bytes. One
Agda process per run, GHCRTS `-A64m -I0 -M2g`, the wide caliber, set
on the pane by the program and never touched here. Peak RSS is
instrumented (`/usr/bin/time -l`). No heap wall was met: the largest
peak, 398,458,880 B (p-2), is 18.6 percent of the 2,147,483,648-byte
wide cap. No run timed out and no failing run was repeated; there were
no failing runs.

## 3. WHAT THE NEXT BRIEF NEEDS

1. **Rule the corrected scope first.** The bound family's false shape
   is now measured at TWO sites (keyS external verdict, envSet
   machine-checked twice); the third site, `Sat-in-carrier-stage`, is
   UNMEASURED -- its probe was never built. The corrected shapes that
   would make the family true are on record (730 review, "The
   corrected target, for ruling": limit `γ ≥ ω`, `closedω γ`, or a
   per-instance rank headroom) but none is ruled, and a ruling is the
   mathematician's call, not this probe's.
2. **Close or retire [LJ-1.731].** A brief that cites "the type of
   [LJ-1.731]" as a module hypothesis cites a delivery the tree does
   not carry. Until 731 returns a probe and a report, the third
   hypothesis has no predecessor type and no verdict.
3. **Then re-brief the bounded fill at the ruled scopes.** The
   hypotheses must be restated from DELIVERED probes only:
   `keyS-in-carrier-lim`'s closedω form, the ruled envSet bound, the
   delivered Sat bound. The assembly itself was not attempted here --
   with two hypotheses false and one undelivered, inventing corrected
   shapes would be inventing a specification. What the assembly then
   consumes per conjunct is on record: the relativized `DefBody`'s two
   existentials want the `Sat` value and the key inside `Lset γ`
   (the brief's premise 2), which is exactly what the corrected bounds
   must give. Price after the ruling, not before.
4. **Do not re-fund**: unbounded `fill`, `relativize-correct`, the 730
   rank chain (now green at a second site, this probe), and
   `keyS-in-carrier-lim`.
5. **A vacuous inhabitant is not a GO.** With hypothesis 2 present the
   obligation's type is inhabited by absurdity elimination; the clause
   forbids writing that term, and any future return that inhabits a
   type resting on `envSet-in-carrier-stage` at `ω ∈ˢ γ` should be
   read as this vacuity, not as a membrane crossing.

## 4. PRICE

| item | value |
|---|---|
| Agda wall, verdict run | 1.75 s (`runs/p-2.out`) |
| peak, verdict run | 398,458,880 B, 18.6 percent of cap |
| floor run (frame, membrane absent) | 1.97 s (`runs/p-1.out`) |
| runs this dispatch | p-1, p-2 |
| in-file / in-fence lines | 311 / 0 (raw `.agda`) |
| brief estimate (W3) | 40 to 100 lines |
| caliber | `-A64m -I0 -M2g`, never set here |

The W3 estimate named the ASSEMBLY; the assembly was not built, so the
estimate is not met or missed -- the clause fired before the attempt.
The delivered probe is 311 lines, of which the re-measured membrane is
about 135.

## ARCHIVE USED

All five injected archive candidates are DECLINED, not used. The stop
rests on two predecessor reports, one undelivered brief, and landed
masters, all cited at `file:line` in sections 0 to 2.

- archive/dev/DD-archived.md: declined, not read; no design decision
  bears on a clause-driven stop built from machine-checked
  predecessors.
- archive/dev/ORCHESTRATION.md: declined, not read; the pod loop's
  history does not touch the membrane or the hypothesis family.
- archive/dev/PLAN-archived.md: declined, not read; retired plans name
  no bounded-fill obligation.
- archive/dev/STATUS-archived.md: declined, not read; standing status
  lives in `dev/pod/screen.toml`, and this task's record is in its own
  runs directory.
- archive/dev/TASKS-archived.md: declined, not read; the predecessor
  reports this task needed (LJ-1.729, LJ-1.730, LJ-1.725-SPLIT) are
  live files named by the brief and were read at the paths cited in
  section 0.

## LITERATURE USED

All five injected literature candidates are DECLINED, not used. The
measurement quotes no book: every step is an in-tree lemma cited at
`file:line` in sections 1 and 2.

- dev/literature/glossary-review-2026-08.md: declined, not used; a
  terminology review names no stage arithmetic.
- dev/literature/devlin-errata.md: declined, not used; it collects
  rud-route error classes, and this stop is in-tree verification, not
  a do-not-repeat checklist item.
- dev/literature/level-formula-slot-roles.md: declined, not used; the
  level formula plays no part in this membrane.
- dev/literature/BIBLIOGRAPHY.md: declined, not used; no source beyond
  the tree was consulted for this dispatch.
- dev/literature/primary-sources.md: declined, not used; no primary
  source is quoted in this return.
