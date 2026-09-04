# Review of lset-grounded-from-reading

**NO-GO.** `lset-grounded-from-reading` cannot be assembled at
`-M4g` in this frame under this brief's prohibitions. The route this
brief names stops. The statement is not pronounced false; the frame
has no legal producer for the term.

## What the brief ordered, and what the frame supplies

The brief orders: use SPLIT-SPLIT's `grounded-from-complete`
(Probe767SplitSplit.agda:148) for the reading at code coordinates;
no second real factor under its two `PT.rec` binders; no subst of the
reading along `fst (val ca) ≡ Lset δ` or `fst (val cp) ≡ δ`; no
ascribed `conv0`; no hypothesised `Convert`; no inhabitant of
`conv-at-Lδ`; no restored `mkWit` codomain; `Completeness` a
hypothesis (LJ-1.768.md:19).

The target is the pinned Sigma of `LsetGrounded` at matrix3
(Probe652.agda:261-264): a hull member `z`, `⟨ z ∈ˢ HS.M ⟩`,
`⟨ Lset δ ∈ˢ HS.M ⟩`, and `⟨ (Lset δ ∷ δ ∷ z ∷ []) ⊨ₚ matrix₃ ⟩`.

## Ground one: the pinned reading has no legal producer

Every producer of an ambient matrix3 reading in this frame lands at
CODE VALUES:

- `hull-convert`, the constructed conversion, is hard-typed to output
  `⟨ (fst (val ca) ∷ fst (val cp) ∷ fst a ∷ []) ⊨ₚ φ ⟩`
  (Probe689.agda:52-63; its instance `Convert`, Probe673.agda:116-123).
- The SPLIT-SPLIT export packs the reading at
  `(fst (val ca) ∷ fst (val cp) ∷ z)` and nothing else
  (Probe767SplitSplit.agda:106-112). Its output scope carries no
  equation naming `ca` or `cp` at `Lset δ` or `δ`, and no hull
  membership for `z`.
- Codes name their values only up to a propositional equation:
  membership in the hull IS `∥ Σ[ c ∈ Code ] (fst (val c) ≡ x) ∥₁`
  (runs/Frame768.agda:112-114, `codeOf`), and `val` never reduces to
  a given set (src/L/Hull.lagda.md:72-90, 106). No obtainable code
  has `fst (val c)` definitionally `Lset δ` or `δ`.

The gap between code coordinates and the pinned coordinates is
exactly the transport the brief forbids (LJ-1.768.md:19). Measured,
the elaborator says so itself. `runs/Mismatch768.agda.txt`, the
producer applied at the pinned codomain on a minimal chassis, fails
in 8.44 s at 1.04 GB (runs/mismatch768.out:9,10,27) with:

```text
δ != fst (HS.H.T.val cp) of type V ℓ
when checking that the expression conv0 ca cp a sat has type
⟨ (Lset δ ∷ δ ∷ fst a ∷ []) ⊨ₚ matrix₃ ⟩
```

(runs/mismatch768.out:4-9). The producer's second coordinate is a
code value; the goal's second coordinate is `δ`. The same failure
blocks the first coordinate (`Lset δ` against `fst (HS.H.T.val ca)`).

The transport itself is not merely forbidden; it is measured
unaffordable. `amb`, 765's transport body that moves both code
coordinates, heap-exhausts the cap ALONE in its own file (765 report
HEAD: `runs/amb-1.out:4,7,8,25`, 1454.50 s, peak RSS 5247418368 B;
basis restated at LJ-1.768.md premise 4). This dispatch did not
restore it, per the brief.

## Ground two: the witness assembly walls at the cap

Suppose a producer existed. The route to a hull member whose reading
content could be true still walls. Three restructurings were built
and run under the same cap in this dispatch, per the heap-wall law:

| instrument | packed tuple | exit | time | peak RSS |
|---|---|---|---|---|
| runs/MinPieces768.agda.txt | `δ , δ∈M , Lδ∈M , hole` | 42, designed | 5.53 s | 854261760 B |
| runs/RecVars768.agda.txt | rec over codeOf; variables + hole | 42, designed | 5.94 s | 1003798528 B |
| runs/ValHull768.agda.txt | `fst (val ca) , val-in-Hull ca , Lδ∈M , hole` | 124, WALL | 1800.03 s | 1500692480 B |
| runs/GapPieces768.agda.txt | `fst a , a∈H , Lδ∈M , hole` via hullClosed | 124, WALL | 1800.11 s | 4708302848 B |

(runs/minpieces768.out, runs/recvars768.out, runs/valhull768.out,
runs/gappieces768.out; each row's exit, time and RSS are at the
`.out`'s EXIT, real and maximum-resident lines.)

The reading-off:

- The obligation's own TYPE is cheap: every instrument whose packed
  terms are variables or a hole greens to the designed hole in the
  5 to 6 s class. The goal type is not the wall.
- The rec over `codeOf` into the pinned goal is cheap (RecVars,
  5.94 s, the equation bound and unused).
- The wall tracks a REAL membership term packed at the goal's
  membership slot. `val-in-Hull ca`, the cheapest membership producer
  in the frame (one application, no search), walls on TIME at 1.5 GB
  (valhull768). The hull half's witness `a∈H` walls harder, at
  4.7 GB (gappieces768). The only membership proofs that do not wall
  are the hypothesis variables `δ∈M` and `Lδ∈M` themselves, and they
  pin `z := δ`, a site whose reading content no producer reaches
  anyway (ground one).

So: the route dies twice. The reading has no legal producer at any
price (ground one), and every assembly that would put a REAL hull
member beside the reading slot walls at the cap before the reading
could even stand (ground two). This is the brief's NO-GO class "the
pinned Sigma cannot be filled" (LJ-1.768.md, WHAT GO AND NO-GO EACH
EARN), and it stops the route.

## What was NOT done, per the brief

- The supplier's transcription is verbatim and green at this site
  (runs/gfc768.out: rc 0, 213.23 s; its two `PT.rec` binders untouched).
- No second real factor was packed under the supplier's binders.
- No subst of any reading along either code equation stands anywhere
  in the tree this dispatch touched.
- `conv0` is never ascribed (runs/ConvApp768.agda.txt keeps the
  vendor's meta codomain; its application inside the full assembly
  walls, runs/convapp768.out, 1800.06 s, 4636246016 B).
- `Convert` is not hypothesised; `conv-at-Lδ` is not inhabited;
  `mkWit`'s spelled codomain is not restored; `Completeness` is never
  inhabited; `amb` is not restored.
- No file in `src/` was touched.

## What would reopen the route

- A producer of `⟨ (Lset δ ∷ δ ∷ z ∷ []) ⊨ₚ matrix₃ ⟩` whose output
  type names the pinned coordinates directly, priced at its own site.
- A cheap membership producer whose output is `HS.M`-shaped by
  CONSTRUCTION (not by a Hull-to-M bridge), which would move ground
  two; ground one would still stand.
- A ruling that permits the transport along the code equations,
  with a new price measured at this site (the transport's own price
  is measured unaffordable at this cap in 765's `amb` row; a
  restructured transport would need its own measurement).

The deliverables: `agents/tasks/LJ-1-768/Probe768.agda.txt` (the
obligation's type, the brief's estimated assembly, ONE designed hole
at the pinned filling; exit 42, one diagnostic,
runs/probe768-1.out), the goal-type instrument
(runs/ExportGoal768.agda.txt, runs/exportgoal768.out:10-15: the hole's goal
spelled as the pinned Sigma), and the full price table in
lj-1.768-report.md.
