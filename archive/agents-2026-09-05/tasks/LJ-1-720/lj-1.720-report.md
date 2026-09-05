# LJ-1.720 report: the three stage lemmas, packed, each codomain explicit

## HEAD
head_slot: coder
machine: shared
agda_tier: wide
task: LJ-1.720
obligation: agents/tasks/LJ-1-720/Probe720.agda::pack-stage
verdict: **GO.** `pack-stage` is defined and green
(`runs/p-3.out:22`, EXIT=0): 1350.11 s cold, 2,591,981,568 bytes
maximum resident (`runs/p-3.out:4-5`), no heap kill. Warm, the
delivered file re-checks in 2.74 s at 779,468,800 bytes
(`runs/p-final.out:3-4,21`). W3 is answered YES: the explicit
codomain sits under the wide cap.

Written only inside `agents/tasks/LJ-1-720/`. No commit, no push.
Agda under the caliber the program set on this pane,
`GHCRTS="-A64m -I0 -M2g"` (recorded in every `.out`'s first line),
the WIDE tier, ONE Agda process at a time. I did not set `GHCRTS`.
Nothing lands in `src/`. Nothing is postulated, the delivered probe
carries `--safe` and no hole (`Probe720.agda:1`). The probe is a raw
`.agda` file, so it carries no fence, counts 0 in-fence lines, and
the ratio bar cannot fire on it.

Scope note. `review-of-pack-stage.md` was in the write scope and is
NOT written, on purpose: it is the NO-GO vehicle (the slot clause),
the outcome is GO, and this report is the record of a GO.

The standing direction (`dev/pod/direction.md:37`) says one SRC
collection after LJ-1, not after `[LJ-2.5]`. This task is still LJ-1
work. It does not start that collection and it does not start phase 3.
No Boundary clause is in conflict.

## 1. THE PREDECESSOR QUESTION, ANSWERED BEFORE ANY AGDA

The bodies I took are the bodies the predecessor WROTE, verbatim:

| piece | taken from | status at the predecessor |
|---|---|---|
| `toL` | `Probe700.agda:57-58` | written, never verified: the bodies "live only in a comment of a file that no run ever typechecked" (review-of-LJ-1-700-1.md:104-107) |
| `same-at-codes` | `Probe700.agda:61-66` | same |
| `hier-at-code`, body | `Probe700.agda:74` | same |
| `hier-at-code`, codomain `_` | `Probe700.agda:73` | THE WALL: the likeliest single cause of the 2.3 GB kills (review-of-LJ-1-700-1.md:138-144) |

`[LJ-1.700]` is NO-GO on the closed term `completeness-from-hier`,
not on these three lemmas
(review-of-LJ-1-700-1.md:167-183). The critic named the explicit
codomain "the first move nobody has tested"
(review-of-LJ-1-700-1.md:183). This task tested it and it holds.

Types the packing stands on, all delivered and green:

- `SameHyp`, `SameAsGraph`: `Probe679.agda:44-49`.
- `HierInStage`, `Code`, `val`: `Probe679.agda:84-88` and the public
  re-export at `Probe679.agda:71`.
- `Lset→isL`: `src/L/Constructible.lagda.md:405-406`.
- `SL`: `src/L/Hull.lagda.md:155-156`, `AbsL.SM`, the stage pairs.
- `hierL`: `src/L/Hierarchy.lagda.md:621-622`. Imported
  (`Probe720.agda:34`) for the explicit codomain only;
  `HierInStage`'s own type already names it.

## 2. D-10, THE TRUTH OF THE TARGET BEFORE ITS PROOF

The recorded residue this task discharges is the critic's cure
(review-of-LJ-1-700-1.md:138-144). Its target: one term packing the
three lemmas, each codomain explicit. Truth check before the proof:
no cardinality or Tarskian obstruction is possible, because the
statement is a conjunction of three applications of already-typed
pieces and introduces no new quantifier.

The check caught a real defect, and D-10's corrected target is
recorded in code. The packing type as FIRST drafted typed its third
component at the STAGE pair (`IsOrd (fst (val cp))` with
`pack (val cp) .snd` as hierL's second argument). At the binder that
is false: a bound application does not reduce, so
`pack (val cp) .fst` is not definitionally `fst (val cp)`
(`runs/floor-1.out:12-13`). The corrected target states components 2
and 3 at the binder's own projections
(`Probe720.agda:98-108`); at the delivered term the component IS
`toL`, and `toL (val cp) .fst` reduces to `fst (val cp)`, so the
components are `[LJ-1.700]`'s own types there. The floor priced this
before any body was written, which is what the floor is for.

## 3. THE FLOOR

`runs/floor-1.out`. The file was the delivered shape with all four
bodies holed and the packing type at its first form; the snapshot is
`runs/FLOOR720.agda.txt`, inert. The run paid the cold probe cone
(`runs/floor-1.out:4-11`: Probe652, Probe641, Probe679, Probe673,
Probe667, both W3 files, Probe520) and aborted at the packing type's
component 3: 118.64 s, 1,780,547,584 bytes maximum resident
(`runs/floor-1.out:17-18`), EXIT=42 with the UnequalTerms above
(`runs/floor-1.out:12-13,35`).

Read as a price: the frame, the telescope and every explicit type
except the last elaborated in 118.64 s under 1.8 GB. The floor did
its other job too: it refused the first packing type before any body
was checked against it.

## 4. W3, WHETHER THE EXPLICIT CODOMAIN SITS UNDER THE WIDE CAP

**YES.** The brief estimated 40 to 90 lines on
review-of-LJ-1-700-1.md:138-144; the delivered probe is 115 lines
including its comment block. The measured answer:

- The site the critic named is FREE. p-1 held `hier-at-code`'s body
  as a hole and p-2 filled it; the cost was 879.38 s to 884.11 s
  (`runs/p-1.out:8`, `runs/p-2.out:7`), a +4.73 s delta, and the
  memory peak did not move (2,538,340,352 to 2,593,718,272 bytes).
  The explicit codomain's conversion is definitional
  (`Probe720.agda:77-78`) and costs nothing.
- The full shape is green with no kill: `runs/p-3.out:4-5,22`.
- Honesty about margin: 2.59 GB maximum resident sits ABOVE the
  2.3 GB band where `[LJ-1.700]`'s three runs were killed. None of
  my five runs was killed: no `Heap overflow` abort appears in any
  `.out`, and the kills at `[LJ-1.700]` were abnormal terminations.
  The cap `-M2g` binds the GHC heap; `/usr/bin/time`'s maximum
  resident set size is the whole process. The delivered shape fits;
  its margin is not measured beyond EXIT=0.

## 5. W2

Answered in code, not in prose: the probe writes no new mathematics.
The three bodies are the predecessor's, byte for byte
(`Probe720.agda:62-84`); the one new piece is `PackStage`, a type,
written once at the `Pack` telescope and instantiated by the single
term `pack-stage` (`Probe720.agda:110-111`). Nothing is copied into
a second form. No deadline conflict.

## 6. W4, AND P-l

W4: no module is retired here. Nothing moves to `archive/`.

P-l (`dev/LESSONS.md:2367`): a statement may be ABOUT a concrete
stage without dragging that stage's PRESENTATION into its type. The
explicit codomain does name `hierL` and the packed pair, a
transparent presentation, and the measured price of that naming is
zero: the p-1 to p-2 delta above is +4.73 s. The `_` was not cheap
either; it moved the work into inference, and the inference is where
`[LJ-1.700]` died. What the floor caught is the P-l lesson's other
half: the FIRST packing type dragged the presentation in the WRONG
direction, typing a component at a reduction the binder cannot do.
The delivered type names the packed pair only through the binder's
own projections, which is the honest form at a variable.

## 7. THE LAWS IN THE BUNDLE

- **D-10** (`dev/LESSONS.md:1375`). Section 2: the corrected target
  is recorded beside the original, in code.
- **C-22** (`dev/LESSONS.md:2307`). This file was written as a
  skeleton before any Agda and filled after each run; the five run
  records landed in section 8 as they finished.
- **P-l** (`dev/LESSONS.md:2367`). Section 6.
- **D-26** (`dev/LESSONS.md:1735`). Does not bind: no well-founded
  key is built here.
- **C-42** (`dev/LESSONS.md:3762`). No refutation landed. The floor's
  UnequalTerms is a refutation of a TYPE DRAFT at one site, and the
  sweep question it raises is answered by construction: the same
  defect class would need a dependent type stating a component at a
  projection of a bound function application, and the only site in
  this task's scope was the one fixed.

## 8. RUNS

One Agda process at a time, sequential, caliber from the pane
(`GHCRTS=[-A64m -I0 -M2g]` is every `.out`'s first line).

| run | state checked | time | max resident | exit | record |
|---|---|---|---|---|---|
| floor-1 | all bodies holed, first packing type | 118.64 s | 1,780,547,584 | 42 | `runs/floor-1.out:17-18,35`, cold cone at `:4-11` |
| p-1 | toL + same-at-codes filled, hier + pack holed | 879.38 s | 2,538,340,352 | 42 | `runs/p-1.out:8-9,26` |
| p-2 | p-1 plus hier-at-code's body | 884.11 s | 2,593,718,272 | 42 | `runs/p-2.out:7-8,25` |
| p-3 | the delivered file, complete | 1350.11 s | 2,591,981,568 | 0 | `runs/p-3.out:4-5,22` |
| p-final | the delivered file, warm cache | 2.74 s | 779,468,800 | 0 | `runs/p-final.out:3-4,21` |

The check ladder honors "one lemma at a time": p-1 isolates toL and
same-at-codes, p-2 adds hier-at-code, p-3 assembles. The interface
is written (`_build/2.8.0/agda/agents/tasks/LJ-1-720/Probe720.agdai`
exists after p-3), so the acceptance re-check should run at the warm
price.

## 9. PRICE

- The delivered probe: 115 lines, of which 0 are in-fence (raw
  `.agda`, no fence), so the ratio bar divisor is 0 and cannot fire.
- Cold price of the obligation, wide caliber: 1350.11 s and
  2,591,981,568 bytes maximum resident (`runs/p-3.out:4-5`).
- Warm price: 2.74 s and 779,468,800 bytes (`runs/p-final.out:3-4`).
- Whole dispatch, all five Agda processes: 3235 s of wall time.
- The brief's estimate for the term was 40 to 90 lines
  (review-of-LJ-1-700-1.md:138-144 basis); 115 landed, the extra
  being the comment block and the honest component-3 form.

## 10. WHAT THE SHAPE RESISTED

1. The dependent packing type resisted its own first form. Typed at
   the stage pair, it is not well-formed at a bound `pack`; the
   floor refused it (`runs/floor-1.out:12-13`). The cure is the
   binder-projection form (`Probe720.agda:98-108`).
2. The types at a CONCRETE `toL` carry the cost, not the bodies.
   floor-1 (holes) ran 118.64 s; p-1 (two one-line bodies filled)
   ran 879.38 s. Filling hier-at-code's body, the critic's named
   site, cost +4.73 s (section 4). The expensive pass is the
   elaboration of the ascriptions that carry
   `P679.SameAsGraph` at concrete packed vectors, together with
   `PackStage`. I did not spend a run isolating which of the two
   dominates; nothing in the obligation lets either be removed.
3. The `_` attribution is refined, not overturned. `[LJ-1.700]`'s
   three kills were real and this shape does not reproduce them; but
   this shape carries the same three bodies with an explicit
   codomain and still sits at 2.59 GB resident. The wall at 700 was
   the shape it had; the cure is measured here at 700's own lemmas.
   Re-running the `_` form to A/B it would be the forbidden rerun of
   the predecessor's code, and was not done.

## 11. WHAT THE NEXT BRIEF NEEDS

- `pack-stage` is delivered at
  `agents/tasks/LJ-1-720/Probe720.agda::pack-stage`, inside
  `module Pack`, whose telescope is Probe700.Spend's: `lam`, `ordλ`,
  `succλ`, `X`, `X⊆Lλ`, `∅∈λ`, `elem`. A consumer opens the module
  at its own telescope or imports and instantiates it.
- Consumption: `fst pack-stage` is the packing function (it is
  `toL`, by computation); `fst (snd pack-stage)` is
  `same-at-codes`; `snd (snd pack-stage)` is `hier-at-code`. The
  components' types are stated at the binder's own projections
  (`Probe720.agda:98-108`); at the delivered term they reduce to
  `[LJ-1.700]`'s types.
- `SameHyp` and `HierInStage` remain HYPOTHESES of the components.
  Nothing here discharges them, and `Completeness` is still not
  inhabited: `pack-stage` does not reach `BoundInStage`, and the
  obstruction argument of `Probe700.agda:76-79` stands unrefuted.
- Any file that states the codomain explicitly needs the
  `L.Hierarchy` import (`Probe720.agda:34`).
- Prices to budget: cold re-check 1350.11 s / 2.59 GB resident on
  the wide caliber; warm 2.74 s / 0.78 GB. A consumer that adds the
  packed lemmas to a heavier file should expect the resident set to
  sit close to the 700 band and should floor its own frame first.
- The tracked supply this GO creates: `[LJ-1.717]` may consume the
  packing lemma instead of restating the three bodies.

## 12. GATES

`make check` is not run here: the task lands no `src/` file and no
commit; the program gates the return. The brief's mandatory check
was run and its output is pasted verbatim below.

```
$ /Users/alsg/Agentic/Bedrock/.venv/bin/python scripts/pod/check-survey-quotes.py LJ-1-720
check-survey-quotes: LJ-1-720 clean (0 note(s), 0 defect(s))
rc=0
```

Note on the interpreter path: this worktree carries no `.venv`
(git-ignored, not copied into worktrees), so the project's pinned
venv interpreter at the main checkout ran the checker. The checker
resolves the repository root from the script's own location, so the
clean verdict above is this worktree's report.

## ARCHIVE USED

- **`archive/dev/DD-archived.md` DECLINED.** Line 1 reads, verbatim:
  `# THE \`DD\` RULING SERIES, archived in full 2026-08-18`. Not
  used: W2 is live in the slot file and this task adds no ruling.
- **`archive/dev/ORCHESTRATION.md` DECLINED.** Line 1 reads,
  verbatim: `# ORCHESTRATION: the orchestrator's operating rules`.
  Not used: the dispatch process is not consulted by a probe.
- **`archive/dev/PLAN-archived.md` DECLINED.** Line 1 reads,
  verbatim: `# ARCHIVED 2026-08-20`. Not used: the live status is
  `dev/pod/screen.toml`, which this return does not restate.
- **`archive/dev/TASKS-archived.md` DECLINED.** Line 1 reads,
  verbatim: `# Archived task index: the \`L3.32-T\` series`. Not
  used: that series is not a predecessor of this packing task.
- **`archive/dev/STATUS-archived.md` DECLINED.** Line 1 reads,
  verbatim: `# STATUS-archived: the goal table of the internalization
  route`. Not used: the goal table of a closed route names no stage
  lemma and no caliber.

## LITERATURE USED

- **`dev/literature/glossary-review-2026-08.md` DECLINED.** Line 1
  reads, verbatim: `# Glossary review: the 119 pre-protocol entries`.
  Not used: no term is proposed and no glossary question arose.
- **`dev/literature/primary-sources.md` DECLINED.** Line 1 reads,
  verbatim: `# Primary sources, second round: Jensen manuscript,
  Devlin, Jech`. Not used: the packing cites no source; the
  mathematics is the tree's own, taken from Probe700 and Probe679.
- **`dev/literature/BIBLIOGRAPHY.md` DECLINED.** Line 1 reads,
  verbatim: `# Bibliography for the rud route`. Not used: this
  report adds no citation.
- **`dev/literature/rudimentary-functions.md` DECLINED.** Line 1
  reads, verbatim: `# Rudimentary functions, closure, and the
  comprehension theorem`. Not used: no rudimentary function or
  comprehension step is proved here; the obligation is a type-level
  packing of delivered lemmas.
- **`dev/literature/devlin-errata.md` DECLINED.** Line 1 reads,
  verbatim: `# Devlin errata: documented error classes
  (do-not-repeat checklist)`. Not used: no scanned quote and no
  Devlin reading is under test.
