# LJ-1.717 report: completeness-from-ambient

STATUS: NO-GO, BY HEAP WALL. The term is built and is complete in shape,
but its elaboration exceeds the wide caliber's 2 GB heap cap in every
shape tried. Five shapes were built and measured under the same cap
(owner's ruling 2026-08-23, heap-wall clause); every shape containing
the amb-to-atL bridge walls. The term is delivered as
`agents/tasks/LJ-1-717/Probe717.agda.txt` (the brief's naming rule: a
file that cannot typecheck is never `.agda`). `obligations` stays at 0.

## The obligation

`completeness-from-ambient : AmbientAt-at-hier → HierInStage → Completeness`,
with `Completeness` taken from `A = P679.At`
(agents/tasks/LJ-1-679/Probe679.agda:73-78), not restated.
`AmbientAt-at-hier` is the brief's missing input of [LJ-1.700]: the
ambient 3-slot reading of `P667.matrix₃` at `(Lset δ, δ, hierL δ)`,
stated over the same telescope `HierInStage` carries (`δ : CS.S`,
`IsOrd (fst δ)`, `fst δ ∈ˢ Lset lam`), as a HYPOTHESIS
(Probe717.agda.txt, `AmbientAt-at-hier`).

Premise 1 honored: `completeness-from-hier` is not defined here and no
refuted inhabitant is copied; `SameAsGraph` is not read anywhere. The
packing lemmas of Probe700.agda:57-74 are restated with EXPLICIT
codomains (premise on the brief's face): `toL`, `table`, `hier-at-code`
-- the last is exactly the cure the [LJ-1.700] review named first
(review-of-LJ-1-700-1.md:150-153).

## What the term does (the mathematical content is settled)

`BoundInStage ca cp` is three existentials over `SL` on `mapFo val
(inBound ca cp)`: value, parameter, witness. The term

1. witnesses the WITNESS slot with `table cp ocp` packed by
   `hier-at-code` (this is where `HierInStage` is spent);
2. witnesses the PARAMETER slot with `(fst (val cp) , snd (val cp))`,
   so the parameter pin closes by `refl`;
3. witnesses the VALUE slot with `(Lset (fst (val cp)) , lset-val-mem
   ...)` where `lset-val-mem` moves the value code's own membership
   onto the tower value along `eq` with the MEMBERSHIP ATOM as motive
   (the smallest family available), so the value pin closes by
   `sym eq`;
4. discharges the matrix conjunct by firing `amb` DIRECTLY at
   `toL (val cp)` -- `map fst` of the witness triple reduces to amb's
   own reading vector, so no ambient satisfaction type is ever
   restated -- and moving the reading to the AbsL embed-side by
   `Cy.atL` read backwards, then to the mapped side by
   `val-matrix-embed` (the `mapFo-comp` + absurd-eliminator idiom of
   Probe652.agda's `embed-map`).

`eq : fst (val ca) ≡ Lset (fst (val cp))` is spent twice, both times
in tiny positions (the membership motive and the value pin), never as
a satisfaction-level transport. The satisfaction-level transport that
walled the first shape is GONE from this shape -- see below; the wall
moved, it did not stay put.

## Measured, all at the pane caliber (wide, `-A64m -I0 -M2g`, never
## set by this agent; every record carries GHCRTS and EXIT=)

| run | shape | result |
|---|---|---|
| runs/floor-1.out | floor, cold import chain | 114.99 s, 1.81 GB, scope-check abort (`module CS` shadowed Probe679's public CS; renamed away) |
| runs/floor-2.out | floor, all types, term and transport holed | GREEN-AT-HOLES: 7.86 s, 1.43 GB; unsolved metas ONLY at the two designed holes |
| runs/stage1.out | + `val-matrix-embed` real | 32.96 s, 1.79 GB (designed hole red only) |
| runs/stage2.out | first term, where-block real, assembly holed | WALL: 333.13 s, 2.63 GB, heap exhausted, EXIT=251 |
| runs/stage3.out | same, `mconj` holed, assembly real | WALL: 335.78 s, 2.58 GB |
| runs/stage4.out | only witnesses + Γ + assembly + pins real | GREEN-AT-HOLES: 80.79 s, 1.72 GB |
| runs/p-2.out | full first term | WALL: 337.17 s, 2.60 GB |
| runs/p-4.out | restructured: no ambient satisfaction transport, `lset-val-mem` route, top-level lemmas | WALL: 208.16 s, 2.68 GB |
| runs/p-5.out | further split: `matrix-embed-at` + `matrix-mapped-at` as separate defs (the delivered shape) | WALL: 221.51 s, 2.62 GB |
| runs/stage7.out | existential levels `lvl0..lvl3` each its own def | WALL: 223.90 s, 2.62 GB |
| runs/stage8.out | THE BRIDGE ALONE: general-vector atL-backwards lemma, one ambient application, the membership subst; everything else holed | WALL: 198.20 s, 2.55 GB |

Reading of the table: every shape WITHOUT the amb-to-atL bridge is
green at or under 1.79 GB; every shape WITH it walls at or over
2.55 GB, whatever the split. The bridge's live-set delta is about
0.8-1.0 GB on top of the stage4 baseline, and Agda does not release it
between top-level definitions, so no split boundary fits. stage8 is
the decisive isolation: the minimal bridge, with the whole term holed,
already exceeds the cap.

## What the shape resisted

1. The ambient satisfaction type is expensive to normalize: one
   ascription of `⟨ _ ⊨ₚ matrix₃ ⟩` costs tens of seconds and hundreds
   of MB (stage1 33 s vs floor 7.9 s; stage4 80 s vs stage1).
2. `subst` whose motive restates a satisfaction type under a binder
   multiplies that cost (the first shape's `amb-read`: stage2/3).
3. Replacing the satisfaction-level transport by the pin-side route
   (`lset-val-mem`, `sym eq`) removed one class of sites entirely, and
   still walls: the remaining cost is in `amb`'s codomain at the
   application and in `Cy.atL`'s equation type, both unavoidable in
   any shape that applies the hypothesis and bridges through `atL`.
4. Splitting definitions does not reclaim the memory (p-4 vs p-5 vs
   stage7: 2.68 / 2.62 / 2.62 GB).

The earlier suspicion that the where-block or the final assembly was
the wall is DISPROVEN by stage2-4: the assembly with its two `refl`/
`sym eq` pins is green (stage4).

## W3 (the brief's named term), answered by construction

"Whether ambient matrix₃ at a stage triple packs to BoundInStage at
the codes, or whether the ≐ pins demand a code that val does not
invert." The pins never read a code backwards. `val` is read only in
the code-to-value direction (`con (val c)` under the semantics is the
constant itself); the value pin is closed by `sym eq` against the
tower value `Lset (fst (val cp))`, not by inverting `val`. The packing
is TRUE at this frame; what fails is the verification budget, not the
mathematics.

## W2

Written once at the generic frame: the term lives in `Spend` with
Probe700's telescope verbatim, and every supplier it reads
(`atL`, `BoundInStage`, `HierInStage`, `matrix₃`, `Δ₀-matrix₃`) is
imported, not copied. The file-local definitions are the packing
lemmas the brief orders restated, the hypothesis type, the bridge
lemmas, and the term. Instantiation is trivial: this file is the only
instance and nothing lands in `src/`.

## W4

No module is retired by this task. Nothing moves to `archive/`; no
`dev/ARCHIVE.md` row is owed.

## P-l

`AmbientAt-at-hier` is about the concrete triple `(Lset δ, δ, hierL δ)`
but its TYPE quantifies over `δ : CS.S` abstractly; `hierL` appears
applied to bound variables inside a membership proposition, not as a
transparent presentation of a concrete stage. No `⟪ sucV … ⟫`-style
presentation is named in any statement here.

## D-10

The target's truth is not the risk; the budget is. The hypothesis
`AmbientAt-at-hier` is consumed without needing to be satisfiable, and
the goal side was already priced green-with-hole at [LJ-1.700]
(premise 2). Supplying a stage triple where matrix₃ holds is the
mathematician's side and stays outside this dispatch.

## What the next brief needs

1. A caliber decision: the term as delivered should verify at a
   heavier tier (the measured overage is ~25-30 percent over the 2 GB
   cap; `-M4g` was the wide tier before the 2026-08-23 second ruling).
2. OR a smaller matrix: the deep normal forms all flow through
   `W3.erased`'s satisfaction; any shrinking of the erased matrix
   shrinks every site at once.
3. OR an AbsL-side ambient hypothesis: a hypothesis stated as AbsL
   satisfaction at the triple would delete the `atL` bridge, the
   single most expensive ingredient. That is a mathematician's call,
   not mine.

## Survey check

Command: `.venv/bin/python scripts/pod/check-survey-quotes.py LJ-1-717`
(run with the main checkout's pinned interpreter; this worktree has no
`.venv`). Final state: PASS, with the duty answered by the ARCHIVE USED
and LITERATURE USED blocks below.

## ARCHIVE USED

- `archive/dev/DD-archived.md` -- declined, not read. This task used only
  live `src/` definitions and live probes; no archived ruling was opened.
- `archive/dev/ORCHESTRATION.md` -- declined, not read.
- `archive/dev/PLAN-archived.md` -- declined, not read.
- `archive/dev/TASKS-archived.md` -- declined, not read.
- `archive/dev/STATUS-archived.md` -- declined, not read.

## LITERATURE USED

- `dev/literature/level-formula-slot-roles.md` -- READ.
  `dev/literature/level-formula-slot-roles.md:26` carries, verbatim:
  "| 4 | Devlin 5.2 (a) | `Φ(z,v,γ)` with `∀v∀γ [v = L_γ ↔ ∃z Φ(z,v,γ)]`
  | 3 in `Φ`, ONE closed | `z` at position 0 | `v` at 1, `γ` at 2 |
  **VALUE, ORDINAL** |". It confirms the slot arithmetic the packing
  transports: matrix₃'s three slots are value, ordinal, witness, with
  the witness the one closed by an existential -- exactly the roles the
  term's three existential witnesses take.
- `dev/literature/BIBLIOGRAPHY.md` -- declined, not read.
- `dev/literature/rudimentary-functions.md` -- declined, not read.
- `dev/literature/primary-sources.md` -- declined, not read.
- `dev/literature/devlin-errata.md` -- declined, not read.
