# LJ-1.719 report: soundness of matrix₃ at stage members

## HEAD
head_slot: coder
machine: shared
agda_tier: wide
task: LJ-1.719
obligation: agents/tasks/LJ-1-719/Probe719.agda::soundness-at-SL
verdict: **NO-GO on the obligation, UPHELD by the adversarial review
(review-of-LJ-1-719-1.md, `verdict: upheld`). Bridge 1 (carrier) and
bridge 3 (IsOrd) retire at SL, both demonstrated by green terms. Bridge
2 (bounded to unbounded) still bites, and the bite is now located
exactly: its leaf leg is placed (`LeafAgree`) but parameterized by a
site-fact block whose `pairK` field holds only at a STAGE bound;
`KValue` supplies it there and nowhere else. At the obligation's own
generality (`z` any member of `Lset lam`) `pairK` is false, and no
delivered module discharges the leaf from the matrix reading alone.**

The obligation name is WRITTEN and DELIBERATELY OPEN:
`Probe719.agda:225-231` states it with a hole body, the measured idiom
for a stated NO-GO (`agents/tasks/LJ-1-408/Probe408.agda:64`,
`[LJ-1.394]`, `[LJ-1.396]`). The stated NO-GO is
`agents/tasks/LJ-1-719/review-of-soundness-at-SL.md`.

## 0. THE SECOND DISPATCH (lint-back-to-author)

The first return failed acceptance conjunct 6, `error_class lint`:
the survey duty was never discharged and the SURVEY QUOTES section
claimed the opposite. `review-LJ-1-719-1.md` is the critic's record of
that failure and of the two numeric defects it found here; both are
fixed in place in this file (section 7's run table and the meter row).
The mathematics was not reopened: the review's verdict is `upheld`, and
its section 1 confirms the probe green at 3.11 s.

This dispatch changes one thing in the tree and re-measures it: the
obligation name now stands at `Probe719.agda:225-231` with a hole. The
reason is routing, not mathematics. With `review-of-LJ-1-719-1.md` in
the tree, the brief's `stop-stated` row is unreachable (its
`changed_files_none` names `review-of-LJ-*-*.md`), and a green probe
would read `exit_code 0` with `obligations_delta 0`, which no branch
of this brief matches: the upheld NO-GO would strand in the no-match
dead zone (the shape measured on `[LJ-1.419]`, recorded at
`scripts/pod/pod.py:5275`). The hole makes the probe exit 42
`unsolved_meta`, which is what `no-go-stated` keys on. Nothing is
postulated, `--safe` holds, nothing lands in `src/`, and the three
green terms are untouched.

## 1. THE PREDECESSOR QUESTION, ANSWERED BEFORE ANY AGDA

`[LJ-1.667]` closed NO-GO on `witnessed-lset`
(`agents/tasks/LJ-1-667/lj-1.667-report.md:5-9`): the syntax of the
witness slot is green, the ambient soundness is not. This brief takes
that syntax (`matrix₃`, `Δ₀-matrix₃`) as delivered
(`agents/tasks/LJ-1-667/Probe667.agda:72-76`), exactly as its premise 2
basis says. No predecessor report names `matrix₃` FALSE, so the stop
clause for a NO-GO predecessor does not fire.

Types taken from predecessors, each the type the predecessor
delivered:

| piece | type | site | verdict |
|---|---|---|---|
| `matrix₃`, `Δ₀-matrix₃` | 3-slot erased Δ₀ matrix + ordinal conjunct | `Probe667.agda:60-76` | GO, syntax |
| `W3.three`, `count-three`, `Δ₀-erased` | the wrapped bounded matrix, erased | `runs/W3.agda:63-97` (LJ-1-667) | GO, syntax |
| `_⊨ₚ_` | the V reading at raw slots | `Probe652.agda:50-51` | GO |
| `Lset-only` | graph determines the value at 𝒮ʟ | `src/L/Hierarchy.lagda.md:334-336` | GO |
| `SameAsGraph` (both directions) | CONDITIONAL: needs PowIterHyp, IsOrd, UP bridge, DOWN bridge | `Probe709.agda:47-67` | GO at its own telescope |
| `Graph.up` (bounded graph to unbounded) | needs approx-up and step-up frames | `agents/tasks/LJ-1-162/ProbeLJ1162A.agda:210-222` | GO as a frame |
| `LeafAgree` | DefBodyB rows to machine clauses, both directions | `src/L/Condensation.lagda.md:7220-7227` | GO |
| `KValue` | ONE `KFacts` value, bound = `Lset lam` | `src/L/Condensation.lagda.md:7363-7435` | GO at a stage bound |
| `KFactsCons` | builds a `KFacts` only FROM a `KFacts` | `src/L/Condensation.lagda.md:6122-6129` | GO, supplies nothing |

## 2. WHAT THIS TASK MEASURED, AND WHERE IT DIFFERS FROM 667

667 named three bridges and none delivered. Between 667 and this
dispatch the tree moved: `LeafAgree`, `SatGraphAgree`, `DefinesAgree`
and `KValue` are now placed under `src/L/Condensation.lagda.md`
(:6953, :7220, :7363). The 709 probe delivered `SameAsGraph` at the
union telescope. This task re-measured the bridge chain at SL and
found the residue moved: it is no longer "the leaf is unplaced" and it
is no longer "SameAsGraph is uninhabited". The residue is the
SITE-FACT BLOCK of the placed leaf.

The chain, with every leg's status at SL:

1. **Carrier (bridge 1). Retired, demonstrated.** The hypothesis
   reading at raw slots converts to the 𝒮ʟ reading at packed slots by
   `abs₀` at `AtStage lam ordλ`'s own `AbsL`, plus `Cnt.erase-inv`.
   The term is `from-V` in the probe. Premise 4 of the brief is
   confirmed by a typechecking term, not by analogy.
2. **Bounded to unbounded (bridge 2). Still bites; located.**
   - The prenex half (twelve bounded existentials to the prenex
     block) is mechanical and 690-class; it is NOT the residue.
   - `SameAsGraph` forward (690) spends the UP bridge
     (`agents/tasks/LJ-1-690/Probe690.agda:67-72`). 709 inhabited the
     conjunction of both directions FROM the two bridges
     (`agents/tasks/LJ-1-709/Probe709.agda:47-67`); it did not pay
     them.
   - The UP bridge's content decomposes, by 162's `Graph` frame
     (`agents/tasks/LJ-1-162/ProbeLJ1162A.agda:210-222`), into
     `approx-up` and `step-up`, whose forward halves run through
     `leaf-up`: the bounded leaf `StepB.leafB`
     (`src/L/Condensation.lagda.md:2407-2413`) must yield the story
     leaf. The leaf leg is PLACED as `LeafAgree.back`
     (`src/L/Condensation.lagda.md:7350-7354`) - but its telescope
     takes a `KFacts` site block plus per-site ties.
   - **THE BITE.** The `KFacts` block contains `pairK`
     (`src/L/Condensation.lagda.md:7425-7427`: pairing closure of the
     bound) and the tagged forms. `KValue.facts`
     (`src/L/Condensation.lagda.md:7414-7431`) supplies the block ONLY
     at the bound `Lset lam`, a stage, via `Bound.prʟ∈λ`. The
     obligation quantifies `z` over ALL members of `Lset lam`.
     Transitivity of `z` (the matrix's own `transK` conjunct) does not
     give pairing closure: `z = { ∅ , ∅ }` is transitive and
     constructible and `pr ∅ ∅ = {{∅}} ∉ z`. So the placed leaf cannot
     be instantiated at the obligation's generality, and no delivered
     module discharges the leaf from the matrix reading alone.
   - The frames that would carry the wiring,
     `[LJ-1.52]`'s StepAgree / ApproxAgree / GraphAgree, are still
     absent from `src/` (`src/L/Condensation.lagda.md:5477-5480`).
3. **IsOrd (bridge 3). Retired, demonstrated.** The hypothesis gives
   `IsOrd (fst p)` and `Lset-only` takes exactly that. The reduction
   term `soundness-with-graph` in the probe is the whole proof of the
   obligation FROM the gap, and it is green.

## 3. W3, ANSWERED

The brief asks: does `φ₃` plus `SameAsGraph` yield `LsetGraphAt` at
the packed triple, or is `isOrd-at-p` the only conjunct that reads?

**`isOrd-at-p` is NOT the only conjunct that reads.** `φ₃` reads as
far as the 𝒮ʟ reading of the wrapped bounded matrix at the packed
triple (`from-V`, green). What stops is one named implication,
`Gap` in the probe, and its content is bridge 2's leaf leg under the
`pairK` obstruction of section 2.

## 4. W2

Nothing is proved twice. The read lemma is `[LJ-1.652]`'s
`AtTrans.read` re-instantiated at `AtStage`'s own `AbsL` (the original
is trapped inside `Frame652`, whose telescope this obligation does not
carry); the probe credits it in place. `Lset-only`, `LeafAgree`,
`KValue`, the 162 frames and 690's forward are imported or cited, not
copied. No deadline forced a fixed form; the conflict to report is
section 2's price, not W2.

## 5. W4, AND P-l

**W4: not applicable.** No module was retired, nothing under `src/`
changed, and `dev/ARCHIVE.md` takes no row from this task.

**P-l: obeyed.** No type in the probe names a stage presentation. The
statements quantify over `S`, `Lset` of a variable, and `AtStage`'s
carrier. `⟪ Lset lam ⟫` appears nowhere.

## 6. THE LAWS IN THE BUNDLE

- **D-10** (`dev/LESSONS.md:1375`). The target's truth was priced
  before its proof: `domB` is a both-directions clause
  (`src/L/Condensation.lagda.md:1749-1756`) and `extAtB`'s reading
  carries the K-payload direction (`:103-109`), so the bounded matrix
  is totality-carrying and NOT refutable by a vacuous `h = ∅` model.
  A refutation was priced and rejected; the residue is a proof
  obstruction, not a false target.
- **C-22** (`dev/LESSONS.md:2307`). This report was written as a
  skeleton before any Agda ran and filled as each answer landed.
- **P-l** (`dev/LESSONS.md:2367`). Section 5.
- **D-26** (`dev/LESSONS.md:1735`). Did not bind. No well-founded key
  was built.
- **C-42** (`dev/LESSONS.md:3762`). No refutation landed, so no sweep
  is owed. The obstruction is measured at ONE site: the
  `pairK`-at-non-stage-bound instance of `LeafAgree`'s telescope. The
  sweep question the next brief may want: how many live obligations
  quantify a leaf bound over non-stage members of a stage. That count
  is not measured here.

## 7. RUNS

Caliber `-A64m -I0 -M2g`, the wide caliber, read off the pane and
untouched here. One Agda process at a time. All runs from the
repository root with `/usr/bin/time -l agda`.

| run | what | wall s | peak RSS bytes | exit |
|---|---|---:|---:|---|
| `runs/p-1.out` | first build, `module B` clash (cold import tree) | 15.73 | 1,755,070,464 | 42 |
| `runs/p-2.out` | `SemVᵃ` clash, warm imports | 2.57 | 831,700,992 | 42 |
| `runs/p-3..8` | scope/import plumbing, each under 13 s | 2.6-12.8 | ≤ 871 M | 42 |
| `runs/p-9.out` | full term, `cong fst` family: HEAP WALL | 213.24 | 2,594,734,080 | 251 |
| `runs/p-10.out` | bisect: without the reduction: still walls | 199.74 | 2,823,274,496 | 251 |
| `runs/p-11.out` | bisect: without Gap: still walls | 200.41 | 2,554,855,424 | 251 |
| `runs/p-14.out` | bisect: carrier transport alone: still walls | 198.99 | 2,706,915,328 | 251 |
| `runs/p-15..18` | leg split, generic sigma projector errors | 2.6-12.4 | ≤ 870 M | 42 |
| `runs/p-19.out` | explicit-lambda families, legs separate: GREEN | 97.13 | 1,950,531,584 | 0 |
| `runs/p-20..21` | pipeline composed: HEAP WALL again | 215-216 | ≥ 2,602 M | 251 |
| `runs/p-23..28` | pipeline/spelling variants: walls | 203.9-300.2 | ≥ 2,602 M | 251 |
| `runs/p-26.out` | legs + Gap, pipeline dropped: GREEN | 99.85 | 1,947,402,240 | 0 |
| `runs/p-29.out` | consolidated single file, `Legs.packed` scope | 2.95 | 853,770,240 | 42 |
| `runs/p-30.out` | **delivered shape, clean module interface** | **105.82** | **1,960,001,536** | **0** |
| `runs/p-final-1..3` | forced rechecks, warm interface | 2.79-2.81 | 770,097,152 | 0 |
| `runs/meter-obligation.out` | the obligation, first dispatch | 2.93 | not taken | 1 (the meter's own exit; the Agda rc inside it is 42, MISSING) |
| `runs/no-go-1.out` | **second dispatch: the obligation stated with the hole** | **101.15** | **1,637,875,712** | **42, `unsolved_meta`** |
| `runs/no-go-2.out` | repeat of the delivered state: same 42, `UnsolvedInteractionMetas` at :231 | 99.11 | 1,637,892,096 | 42 |
| `runs/meter-no-go.out` | **second dispatch: the meter on the hole** | **97.85** | not taken | 1 (the meter's own exit; PROBE-RED, `probe_red=True`) |

Two rows the first delivery of this table omitted, found by the review
(`review-of-LJ-1-719-1.md`, section 3.1) and measured from the files:

| run | what | wall s | peak RSS bytes | exit |
|---|---|---:|---:|---|
| `runs/p-12.out` | bisect, inside the p-9..p-14 window: HEAP WALL | 201.12 | 2,609,397,760 | 251 |
| `runs/legs-1.out` | `runs/Legs719.agda`, a scratch leg file: `[ShadowedModule]`, duplicate `module AL` | 2.71 | 830,783,488 | 42 |
| `runs/legs-2.out` | Legs719 again: HEAP WALL | 217.13 | 2,655,485,952 | 251 |

Legs719.agda itself was deleted before delivery: a dead scratch
fragment with no consumer, under the module-granular W4 clause. Its
run files stay; they are part of the measured record.

Median of the three forced rechecks **2.80 s**. The delivered shape's
clean-interface elaboration is **105.82 s at 1,960,001,536 bytes**, 91 %
of the 2 GiB wide cap. Witness meter, first dispatch:
`1 UNRESOLVED of 1, 2.93 s, probe_red=False`, the name MISSING
(`runs/meter-obligation.out`) - the obligation deliberately open and
the probe red-free. Witness meter, second dispatch, on the hole:
`probe-red exit=42, 1 UNRESOLVED of 1, 97.85 s, probe_red=True`
(`runs/meter-no-go.out`) - the name is now stated, and the red is the
stated NO-GO itself.

**HEAP WALL, MET AND ROUTED AROUND IN THIS DISPATCH.** The first
complete term walled (p-9). Three restructurings were tested under the
same cap, each with its own run: the explicit-lambda transport families
(p-19, green), dropping the composed pipeline and spelling leg 1's
result at the raw triple (p-26, p-28), and the single-file
consolidation with the leg interfaces matched (p-30, green, delivered).
The delivered shape does not wall, so no heap-wall finding is reported
against the term; the trigger is recorded in section 9 for the next
coder at this frame. **Counted:** 13 wall-class runs in `runs/`,
twelve of Probe719 (p-9, p-10, p-11, p-12, p-14, p-20, p-21, p-23,
p-24, p-25, p-27, p-28) plus Legs719's legs-2; the first delivery of
this section said seven, which was the count of the bisect window
alone and wrong.

## 8. PRICE

Non-blank non-comment lines counted by
`awk 'NF' file | grep -cv '^[[:space:]]*--'`. Re-measured at the
second dispatch on the delivered file.

| what | lines | code lines | at `file:line` |
|---|---:|---:|---|
| the probe, whole | 231 | 96 | `Probe719.agda` |
| obligation type | 4 | 4 | `Probe719.agda:94-97` |
| packing and read lemma | 37 | 21 | `Probe719.agda:105-141` |
| the three legs | 27 | 23 | `Probe719.agda:153-179` |
| Gap | 5 | 5 | `Probe719.agda:195-199` |
| the reduction | 4 | 4 | `Probe719.agda:208-211` |
| the stated obligation, with its banner | 17 | 7 | `Probe719.agda:215-231` |

The brief estimated 70 to 170 lines. The delivered probe is 96 code
lines, inside the estimate; the price the estimate did not carry is
the heap-wall restructuring, 13 wall-class runs at 199 to 301 s each
before the delivered shape went green.

## 9. WHAT THE SHAPE RESISTED

- **What it cost.** 96 code lines; clean-interface 105.82 s at 1.96 GB;
  warm rechecks 2.8 s; the second dispatch added 7 code lines for the
  stated obligation and re-elaborated cold at 101.15 s. 13 heap-wall
  runs on the way.
- **What the shape resisted.** Three measured triggers, all in the
  satisfaction-typed transports: (1) a `cong fst` family over the
  absoluteness equality - the elaborator whnfs the family endpoints
  into the goal's truncated existentials and exhausts the cap
  (p-9..p-14); the fix is the family written as an explicit lambda
  (p-19). (2) A generic sigma projector at the conjunction split - the
  metavariable digs into the truncated existentials of the goal; the
  fix is the annotated `snd-of-∧` (p-15..p-18). (3) Composing the
  three legs under one term, or spelling leg 1's result through
  `map fst (packed …)` - both re-fire the same whnf (p-23..p-28); the
  delivered shape keeps the legs separate and the result spelling at
  the raw triple.
- **What I had to weaken.** Nothing of the obligation's statement. The
  pipeline term `from-V` is not delivered as one name; the legs are,
  and their composition is immediate. [LJ-1.718]'s consumer applies
  them in sequence.
- **What I could not close.** `soundness-at-SL` itself, and `Gap`:
  bridge 2's leaf leg at the obligation's generality, under the
  `pairK` obstruction of section 2.

## 10. WHAT THE NEXT BRIEF NEEDS

1. **FUND soundness-at-SL AT THE STAGE-BOUND REDUCTION.** Restrict the
   witness slot to stage bounds (`z = Lset κ`, `κ ∈ˢ lam`, so
   `z ∈ˢ Lset lam` by cumulativity) or hand `[LJ-1.718]` the hypothesis
   with that restriction. There `KValue.facts`
   (`src/L/Condensation.lagda.md:7414-7431`) applies and the route
   closes through `LeafAgree.back`, the 162 frames, 690's forward and
   `Lset-only`. Priced here at 250 to 400 lines of site-fact wiring,
   one dispatch, basis: the telescope sizes in section 2.
2. **OR FUND THE LEAF AT THE WEAK TELESCOPE.** A variant of
   `DefinesAgree.back` that threads the rows' own `∈ K` proofs instead
   of demanding `pairK` closure. That is `src/` work, one module, and
   it would also serve `[LJ-1.52]`'s absent frames.
3. **DO NOT RE-DISPATCH THE FULL-GENERALITY soundness-at-SL.** The
   `pairK` obstruction is not plumbing; it is a false instance of the
   site-fact block at the stated generality
   (`review-of-soundness-at-SL.md`, section 3).
4. **DO NOT FUND THE PRENEX HALF ALONE.** It is mechanical and 690's
   `UA.At` already carries its shape
   (`agents/tasks/LJ-1-690/Probe690.agda:33-35`).

## SURVEY QUOTES

The first return claimed compliance here and its file carried none:
`review-of-LJ-1-719-1.md`, section 6, is the correction of record.
This return discharges the duty and pastes the checker's own output,
run as the brief commands (this worktree has no own venv; the main
checkout's interpreter runs it, as the review recorded):

```sh
.venv/bin/python scripts/pod/check-survey-quotes.py LJ-1-719
```

check-survey-quotes: LJ-1-719 clean (0 note(s), 0 defect(s))
(exit code 0; run 2026-08-28 against this file at the second dispatch,
re-run after this paste: same output)

The two USED sections follow; the pasted output is the run against
this exact file state.

## ARCHIVE USED

- archive/dev/DD-archived.md: not read. Every ruling this return
  applies is live (AGENTS.md, the coder slot file, the brief's own law
  bundle); no question here turns on a retired design decision.
- archive/dev/ORCHESTRATION.md: not read. Why not: the routing this
  return relies on (exit 42 versus 0) is read from the live
  scripts/pod/accept.py, scripts/pod/pod.py and the brief's branch
  table, not from the retired orchestration record.
- archive/dev/PLAN-archived.md: not read. The live program is the LJ-4
  memo and the queue; no plan clause is cited by this return.
- archive/dev/STATUS-archived.md: not read. The only standing status
  is the screen; a retired status file has no work here.
- archive/dev/TASKS-archived.md: not read. This task's predecessor
  chain lives in agents/tasks/LJ-1-719/ and agents/tasks/LJ-1-667/,
  both read directly; a retired task index adds nothing to them.

## LITERATURE USED

- dev/literature/level-formula-slot-roles.md:26 "Devlin 5.2 (a)":
  READ. Row 4 of its table is matrix₃'s own source, and it fixes the
  slot roles the obligation uses: one closed bound at position 0, the
  value and the ordinal free, the pair the probe reads as (a, p, z).
  Its section 2.3, the bound is DETERMINED and not chosen, is why the
  witness slot cannot be quietly re-rolled into a stage bound: that is
  a different statement, and the stage-bound reduction stays route 1
  of the NO-GO's section 4, for the mathematician to fund.
- dev/literature/devlin-errata.md:125 "2.3 Errors in Chapter II (WS
  pp. 62-63)": READ. Its Chapter II classes are amenability (p. 45),
  the false uniform-Δ₁ claim for Sat over amenable sets (p. 65) and a
  Σ^KPI_1 claim (p. 66). None touches 5.2 or this route: the probe's
  Δ₀ absoluteness leg is measured green in the tree (`read-at-SL`,
  `Probe719.agda:133-141`), not taken from Devlin's Sat claims, and
  the NO-GO sits in the `pairK` site-fact block. No documented Devlin
  error bears on the target's truth.
- dev/literature/BIBLIOGRAPHY.md: not read. No citation question is
  open: the matrix's source is fixed by 667's own comment
  (`agents/tasks/LJ-1-667/Probe667.agda:71-73`) and by the digest
  above.
- dev/literature/glossary-review-2026-08.md: not read. This return
  raises no naming question and proposes no glossary term.
- dev/literature/primary-sources.md: not used, same reason as the
  bibliography: no provenance question in this return reaches past
  the task tree.
