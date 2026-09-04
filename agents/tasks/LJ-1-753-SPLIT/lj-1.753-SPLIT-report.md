# LJ-1.753-SPLIT report: bound-in-stage-from-mirror, erase-cong at the localized wall

## HEAD
head_slot: coder
machine: shared
agda_tier: wide

**Disposition: GO.** The obligation term `bound-in-stage-from-mirror` typechecks
in `agents/tasks/LJ-1-753-SPLIT/Probe753Split.agda` at the brief's exact
signature: rc 0, 147.28 s, peak RSS 1,885,126,656 B under the 2g wide cap
(`runs/probe753split-29.out`; warm recheck rc 0 in 3.25 s,
`runs/probe753split-30.out`). No hole, nothing postulated, `GraphAt`,
`Completeness` and `AT.read` never appear (0 occurrences), and `src/` is
untouched (`git status --short src/` empty). `review-of-*.md` is not written:
there is no NO-GO to state.

## The obligation and what the term does

The term is LJ-1.753's deepest-checking state re-anchored at the domB site
with the brief's ordered cure. The 673 `At` telescope is taken as leading
arguments; Amb7 is imported beside PT and EraseIrr; `StepKilledGen` is
consumed vacuously through the ∅-slot kills (the finding 753 reported). The
three existential witnesses, `env15`, `isOrd₁/₂`, `transK`, `pins` and the
twelve-pin block are the predecessor's, verbatim in shape.

## The cure, and what the wall actually was

Two things were wrong with the grounding term, and only one was the chain.

1. **The row-slot abstraction level.** The demand's domB and tail row slots
   are FUNCTIONS INTO FOLDED readings: the domB slot is
   `(x : S AbsL.𝒮M) → ⟨ x ∈ n 12 ⟩ → ⟨ (x ∷ genv16) AbsL.⊨ᵐ erased domBf ⟩`
   with BOTH implications folded inside one satisfaction proposition, and the
   tail slot similarly folds `∀̇∈ (var 16) (appAt ⇒̇ S.stepBndAt)`. The
   predecessor's `ab`/`ba` ascriptions hand-decomposed the readings two
   levels down to leaf-implication Πs and paired them with `approx = ab , ba`;
   that shape never slot-fit. This was invisible until now because the
   predecessor's antecedent-type elaboration grounded BEFORE any slot-fit ran
   (the 15.16 s bisect reached the body of a DUMMY-ascribed piece, so no row
   was ever compared against its slot). Measured: the full slot prints are in
   `runs/slotprobe-5.out` (domB) and `runs/probe753split-18.out` (tail).
2. **The chain spelling.** The predecessor spelled the demand's 21-node chain
   with INFERRED plus-implicits; the unifier then decomposed meta-headed
   pluses against Def-headed `countFo` applications (`countFo three` at the
   chain's base), the failure mode PT measured at its own site
   (runs/PT.agda:12-16). This file names its formulas once
   (`domBf`, `tailf` — CONSTRUCTOR-headed), takes `refl` over them as the
   ORIGINAL spelling (`countDom`, `countTail`), builds the SPLIT spelling as
   short explicit-implicit chains over refl-anchored subformula counts
   (`pDom` over `countAppDom`, `pTail` over `countAppDom` and
   `countTailStep` — `countFo W3.Mx.G.A.S.stepBndAt ≡ 0` is `refl`), and
   carries the row between the spellings by the brief's ordered transport,
   `IrrC.erase-cong domBf countDom pDom` and
   `IrrC.erase-cong tailf countTail pTail` (`domB-split`, `tail-split`;
   EraseIrr.agda:56, PT's approx-split shape, runs/PT.agda:72-78). The step
   row is the predecessor's pair, restored verbatim once its slot printed.

No name in the file has a Def-headed `countFo` under it; `W3.count-three` is
never referenced; and the slot-fit conversion of the readings never compares
count proofs, because each `⊨ᵐ` application whnf's its formula argument
first and `eraseTm`'s var clauses ignore their proof argument
(src/FOL/Count.lagda.md:594-610).

## Floor (before proof, owner's ruling 2026-08-23)

`runs/Floor753Split.agda.txt`: this probe's exact import block, module
header, At telescope, and the obligation with a holed body; run as a
temporary same-stem `.agda` copy, deleted after (Agda 2.8.0 rejects the
`.agda.txt` extension, as 746-SPLIT-SPLIT measured).

| run | rc | wall | peak RSS | evidence |
|---|---|---|---|---|
| floor, cold cone | 42 designed | 214.98 s | 1,793,687,552 B | runs/floor753split-1.out |
| floor, warm | 42 designed | 3.08 s | 639,778,816 B | runs/floor753split-2.out |
| **PROBE, green** | **0** | **147.28 s** | **1,885,126,656 B** | runs/probe753split-29.out |
| probe, warm recheck | 0 | 3.25 s | 742,866,944 B | runs/probe753split-30.out |

ONE Agda process at a time, sequential, never two. `GHCRTS=-A64m -I0 -M2g`
was read from the pane at every run and never set by this task. The green
run's peak sits under the 2g cap; no heap wall was hit, and none is reported.

## Iteration record (all in runs/)

The route to green, each run one process: -10 are parse and scope rounds
(paren balance in the spelled chains, the `IrrC`/`pA` shadowing against PT's
exports, `countFo`'s home module, `(λ`-glue layout); 11-13 are the first
slot-fit contacts; `slotprobe-5.out` and `probe753split-18.out` are the two
diagnostic runs (`Vec SL 0` ascriptions) that printed the true domB and tail
slot shapes; 19-28 walk the row rewrites through their meta-cleanups. The
decidable lessons for the next brief:

1. **Row slots fold their connectives.** A row slot is a function into a
   folded `⟨ _ ⊨ᵐ φ ⟩`; the term re-derives the pair/Π by whnf. Do not
   hand-decompose a reading one level deeper than the slot prints.
2. **`appAt`'s implicit is named `n`, not `m`**, and must be spelled at
   standalone positions (`{n = 18}` at the domB leaf env). `countFo`,
   `countTm` and `var` implicits (`{K}`, `{n}`) must be spelled wherever a
   chain argument's type is otherwise a meta.
3. **`PT.rec`'s `Empty.isProp⊥*` needs its level spelled**:
   `PT.rec (Empty.isProp⊥* {ℓ-suc ℓ})` — otherwise `Empty.rec*`'s
   `⊥* {ℓ = ℓ'}` argument leaves ℓ' unsolvable inside folded row types.
4. **Where-name pieces must be pairs of ascribed functions, never
   `λ x → A , B`** — Agda's λ swallows the comma and the inferred type
   becomes a wrapped Π (`probe753split-14.out` shows the shape).
5. **A step-slot diagnostic trick**: ascribing a not-yet-understood slot with
   `Vec SL 0 = []` forces an UnequalTerms print that shows the slot in full,
   in one ~15 s run. Both slot prints this task measured came from that move.

## W3, the widest unmeasured term

The brief asked: whether `erase-cong` at the domB-annotation converts at
wide. **YES — measured.** The erase-cong transports sit in the delivered
term (`domB-split`, `tail-split`), the whole file converts at wide in
147.28 s at 1.89 GB peak, and the inline 21-node chain is gone from the tree
at this site. The NO-GO question "whether the inline form is required" is
answered: it is not; the refl-over-named-formula spelling plus the short
split chains plus the transport is sufficient.

## W2 answer

Honored by reuse. `BoundInStage`, `Code`, `val`, `inBound` are 673's; the
numerals, kills and pin-shapes are 732's `Num` content at the restricted
carrier; `StepKilledGen` and the erase-cong machinery are Amb7's and
EraseIrr's; `S.stepBndAt` and `witB` are consumed BY NAME from `W3.Mx.G`
(`W3.Mx.G.A.S.stepBndAt`, `W3.Mx.G.S.witB`), never re-spelled. This dispatch
wrote no second formula and no duplicate statement.

## Files

- `Probe753Split.agda` — the obligation, GREEN (stays `.agda`; it
  typechecks).
- `runs/Floor753Split.agda.txt` — the floor instrument.
- `runs/SlotProbe.agda.txt` — the slot-print diagnostic (`.agda.txt`: it
  cannot typecheck by design; run as a temp copy, deleted after).
- `runs/*.out` — every run record cited above (floor753split-1/2,
  slotprobe-1..5, probe753split-1..30).

## Ratio bar

The deliverable `Probe753Split.agda` is a raw `.agda` probe: no
` ```agda ` fence, 0 in-fence lines. The bar cannot fire.

## Mandated paste

    $ .venv/bin/python scripts/pod/check-survey-quotes.py LJ-1-753-SPLIT
    check-survey-quotes: LJ-1-753-SPLIT clean (0 note(s), 0 defect(s))

    exit 0. (The worktree carries no .venv; the main tree's interpreter
    ran the script against THIS worktree, as in the 753 and
    746-SPLIT-SPLIT returns.)

## ARCHIVE USED

- archive/dev/DD-archived.md: declined, not read. The cures this task
  re-measured come from the predecessors' live reports at their own sites.
- archive/dev/ORCHESTRATION.md: declined, not read. The loop operation is
  fixed by the standing files; no question about it arose.
- archive/dev/PLAN-archived.md: declined, not read. No plan-level question
  arose for a one-term obligation.
- archive/dev/TASKS-archived.md: declined, not read. Closed task history is
  not evidence for an elaboration wall; the live predecessor report is.
- archive/dev/STATUS-archived.md: declined, not read. The screen is the only
  standing status and no status question arose.

## LITERATURE USED

- dev/literature/glossary-review-2026-08.md: declined, not read. No
  translation term was chosen or queried.
- dev/literature/level-formula-slot-roles.md: declined, not read. The slot
  roles are fixed by the imported modules and the demand's own prints.
- dev/literature/devlin-errata.md: declined, not read. No Devlin citation is
  under test; the mathematics is the tree's own empty instance.
- dev/literature/primary-sources.md: declined, not read. This is a code-only
  task and cites no primary source.
- dev/literature/BIBLIOGRAPHY.md: declined, not read. Nothing bibliographic
  is claimed.
