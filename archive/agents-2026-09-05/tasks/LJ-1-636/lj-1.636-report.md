# [LJ-1.636] At which delta is the `sq` parameter actually applied

**GO.** The census is built and green. `sq-demand` is one term at
`agents/tasks/LJ-1-636/Probe636.agda:422-428`. It has no hole and no
postulate. Four green runs: `runs/final-3.out` at 4.11 s,
`runs/final-4.out` at 3.49 s, `runs/final-5.out` at 3.67 s after the
last comment edit, and, at the 2026-08-27 re-dispatch,
`runs/revalidate-1.out` at 4.54 s with a 695 MB peak. All `EXIT=0`,
under the caliber the program set.

**THE TREE'S FINAL STATE IS GREEN AND THERE IS NO STANDING HEAP WALL.**
One wall occurred in the middle of this dispatch, and I routed around it
and tested the new shape under the same cap, as the standing clause
orders. Section 5 reports it as a finding. `runs/final-1.out` and
`runs/final-2.out` are that wall; they are the superseded shape, not the
deliverable.

Nothing landed in `src/`. `git status --porcelain` shows only
`?? agents/tasks/LJ-1-636/`.

## 0. THE RE-DISPATCH, AND WHY THE FIRST RETURN PARKED

The first return of this task parked, and the park was NOT about the
deliverable. The acceptance record `runs/accept-1.out` shows both facts:

- `run agents/tasks/LJ-1-636/Probe636.agda rc 0 seconds 3.32` and
  `obligations delta -1`. The deliverable was green at acceptance.
- `run agents/tasks/LJ-1-636/runs/Bisect1.agda rc 251 seconds 25.39`:
  the harness also re-ran the STALE bisection artifact from the section 5
  wall hunt, which still carried the `.agda` extension then. That file is
  the superseded wall shape kept as evidence; re-running it walls by
  construction. It set `heap_wall: true`, failed conjunct 1, and the
  return took the `heap-wall-park` branch.

Between that acceptance (`runs/accept-1.out` started 2026-08-26 01:38:34)
and this re-dispatch, every `runs/*.agda` artifact except the probe was
renamed to `*.agda.txt` (`runs/` directory mtime 2026-08-27 10:43 local;
the `.txt` files' own mtimes are unchanged, so it was a rename and not a
rewrite). `find agents/tasks/LJ-1-636 -name '*.agda'` now returns only
`Probe636.agda`. Nothing was deleted; the evidence files are all present.

This re-dispatch changed NOTHING in `Probe636.agda` (mtime 2026-08-26
01:36) and nothing in sections 1 to 7 below, so the parked dispatch's
evidence carries over unchanged. What it added is exactly two things:
this section, and the live re-validation `runs/revalidate-1.out`
(`EXIT=0`, 4.54 s, `GHCRTS=[-A64m -I0 -M2g]`, one Agda process). A stale
run artifact, not the term, caused the park; the term itself never
walled after the section 5 restructuring, and it walls nothing now.

## 1. THE ANSWER

**Every application site RANGES OVER BOTH. No site is forced to `ω`, and
no site is forced strictly above `ω`.**

| # | Site | The delta | Verdict |
|---|---|---|---|
| A | `src/L/StageCardinal.lagda.md:293` | `LimitStep`'s own `α` | ranges over both |
| B | `src/L/BoundedSubset.lagda.md:1526` | the ambient `α₀`, which is `BoundedSubsetAt`'s own `α` | ranges over both |
| B' | the same site with the cardinal side carried | the same `α₀` | ranges over both |

The verdict is not a label. `Evidence`
(`agents/tasks/LJ-1-636/Probe636.agda:143-148`) computes the evidence type
from the verdict, so `ranges-over-both` costs two witnesses AND the
refutation of the other two verdicts. All three rows pay it.

**BUT THE TABLE IS NOT THE USEFUL PART OF THIS MEASUREMENT.** Section 6 of
the probe sharpens it, and this is what re-plans the campaign:

> **The two sites read their delta from the SAME ambient `α₀`, and one
> fact decides the whole demand: whether `α₀` is `ω`.**

- **At `α₀ ≡ ω` the parameter is already delivered, WHOLE.**
  `param-at-ω : SqParam ω` (`Probe636.agda:391-392`) is built from
  `squareω` and nothing else. `δ ∈ sucV ω` with `δ ∉ ω` forces `δ ≡ ω`
  (`collapse-at-ω`, `Probe636.agda:377-381`), so `squareω` transports to
  every delta the domain admits. **The residue at ambient `ω` is empty.**
- **At `ω ∈ α₀` both sites reach `α₀` itself, strictly above `ω`**
  (`reaches-above`, `Probe636.agda:396-402`).
- **There is no third case.** `control` (`Probe636.agda:407-416`) splits
  every admissible ambient by trichotomy and returns one of the two.

## 2. THE CENSUS IS EXHAUSTIVE, AND I RE-DERIVED IT

The brief said its grep was a claim. I ran my own:
`grep -rn '\bsq\b' src/ --include='*.lagda.md'`. The full disposition is
written into the probe's header (`Probe636.agda:17-39`).

- **BINDERS, 4**: `src/L/StageCardinal.lagda.md:17`,
  `src/L/BoundedSubset.lagda.md:1388`, `src/L/BoundedSubset.lagda.md:1748`,
  `src/L/StageBound.lagda.md:67`.
- **FORWARDINGS, 4**: `src/L/BoundedSubset.lagda.md:1397` and `:1751`,
  `src/L/StageBound.lagda.md:75` and `:115`. A forwarding applies no
  argument to `sq`, so it is not an application.
- **APPLICATIONS, 2**: `src/L/StageCardinal.lagda.md:293` and
  `src/L/BoundedSubset.lagda.md:1526`.
- Unrelated names that carry the letters: `sq-lt` and `sq-lemma` at
  `src/FOL/Count.lagda.md:38-60`, the bound variable at
  `src/L/Hierarchy.lagda.md:508`, `sqκ` at
  `src/L/SquareLawClosed.lagda.md:317`, `squash₁` throughout, and the
  square-law PREDICATE at `src/L/Ordinal/SquareLaw.lagda.md:685`.

**THE BRIEF'S PREMISE 3 STANDS. There is no third site.**

## 3. THE PREMISES, ONE BY ONE

1. **TRUE.** The parameter is at `src/L/StageCardinal.lagda.md:17-20`. It
   is untruncated, and its clause `(⟨ δ ∈ ω ⟩ → Empty.⊥)` excludes
   `δ ∈ ω` and admits `δ ≡ ω`.
2. **TRUE, AND CHECKED BY THE MACHINE.** `delivered-at-ω : Sq ω`
   (`Probe636.agda:100-101`) is `squareω`. It typechecks only because the
   parameter's value type at `ω` and `src/L/Ordinal/SquareLaw.lagda.md:685-687`
   are the same type on the nose.
3. **TRUE.** See section 2.
4. **THE CITATION IS TRUE, AND THE OLD VERDICT IS HALF TRUE TODAY.**
   `archive/dev/LJ-dispatch-index.md:192` reads
   `| LJ-1.116 | At which alpha does Upper need sq? | ONLY AT OMEGA, AT THE SITE | Generic demand is every infinite ordinal below alpha; the site is omega. Init is false at omega and at successors |`.
   Its FIRST half survives: the generic demand is every infinite ordinal
   in `sucV α₀`, which my site A row measures again at the site it names,
   as C-42 requires. Its SECOND half, "the site is omega", **does not
   describe today's tree**. Measured: `src/` instantiates neither
   `L.StageCardinal` nor `Devlin55.BoundedSubsetAt` at a closed ordinal.
   The only instantiation of the chapter is
   `src/L/BoundedSubset.lagda.md:1397`, at the free parameter `α`.
   `L.StageBound` is imported only by `src/Everything.lagda.md:396`, and
   its two entry points, `bounded-from-data`
   (`src/L/StageBound.lagda.md:130-133`) and `bounded-modulo-collect`
   (`src/L/StageBound.lagda.md:137-139`), both take the family as an
   argument. **No site in `src/` pins `α₀` at all today.**

## 4. W3. THE WIDEST UNMEASURED TERM

The brief named it: whether `α` at `src/L/StageCardinal.lagda.md:293` is
forced to `ω` by its own binders. The brief estimated 60 to 120 lines.

**ANSWER: NO, AND THE BINDERS DO NOT EVEN TRY.** The application reads
`α∈suc` and `infα` only. The reach is not one delta: `LimitStep` is
entered from `limit-step` (`src/L/StageCardinal.lagda.md:406-413`), which
is entered from `Upper.step` (`:571-572`), which is
`Upper.stage-card-upper = ∈-induction step` (`:574-576`). So the
∈-induction reaches the site at EVERY ordinal in `sucV α₀` outside `ω`.

`reach-A` (`Probe636.agda:226-227`) proves this and does not argue it:
`stage-card-upper` accepts every member of `H-A` and asks for nothing
more, so `H-A` is the reachable set and not an approximation to it.

**PRICE: 192 non-comment lines for the whole probe**, of which section 3
(site A, with the reach) is 33. The estimate of 60 to 120 lines was for
the binder analysis alone, and the binder analysis came out cheaper than
the frame around it.

## 5. THE HEAP WALL, AND THE SHAPE THAT CURED IT

**ONE HEAP WALL OCCURRED. I ROUTED AROUND IT IN THIS DISPATCH AND TESTED
THE NEW SHAPE UNDER THE SAME CAP.** It is reported here as a finding, not
as a stop.

The census row was first an Agda `record` with four fields: `hyps`,
`applies`, `verdict`, `evidence`. It exhausted the 2 GB caliber twice, at
`runs/final-1.out` (50.01 s) and `runs/final-2.out` (25.98 s).

I first suspected the elaboration frame, and I measured it before I
proved anything, as the standing clause orders. The frame is NOT the
problem:

| Run | What it holds | Result |
|---|---|---|
| `runs/floor-1.out` | the frame alone: `L.StageCardinal` instantiated | 1.61 s, `EXIT=0` |
| `runs/bisect-5.out` | the probe's imports alone | 1.17 s, `EXIT=0` |
| `runs/bisect-6.out` | plus section 0 | 1.11 s, `EXIT=0` |

`runs/final-1.out` also rebuilt three chapters inside the probe's own
process, because `L.BoundedSubset`'s interface was older than its own
dependency `L.StageCardinal`'s. I warmed them one chapter per process
(`runs/warm-1.out` at 3.10 s, `runs/warm-2.out` at 3.21 s). The wall
survived that (`runs/final-2.out`), which proved the cost was mine.

Bisection then put the wall on ONE FIELD:

| Run | Shape | Result |
|---|---|---|
| `runs/bisect-8.out` | `Hyp`, `Verdict`, the four predicates, `Evidence`. No container | 1.18 s, `EXIT=0` |
| `runs/bisect-d.out` | a record with `hyps` only | 1.12 s, `EXIT=0` |
| `runs/bisect-e.out` | a record with `hyps`, `verdict`, `evidence` | 1.15 s, `EXIT=0` |
| `runs/bisect-f.out` | a record with `hyps` and `applies` only | **WALL** |
| `runs/bisect-c.out` | `Applies` as a top-level definition, `Site` as a nested `Σ` | 1.30 s, `EXIT=0` |
| `runs/bisect-b.out` | the four-field record, `no-eta-equality` | **WALL** |

**THE SHAPE, STATED AT THE SITE IT WAS MEASURED AT.** A record field
whose type quantifies over the `sq` family, that is over
`(δ : S) → ⟨ δ ∈ˢ sucV α₀ ⟩ → (⟨ δ ∈ˢ ω ⟩ → Empty.⊥) → Sq δ`, exhausts
2 GB. The identical type as a top-level definition costs 1.30 s inside
the same file. `no-eta-equality` does not help. The dependent field
`evidence : Evidence hyps verdict`, a stuck match on another field, is
NOT the cause: `runs/bisect-e.out` carries it and is green.

**This is a candidate for `dev/LESSONS.md` and I do not write it there.**
It is one measurement at one site. It says a record is the expensive
container for a field of that shape; it does not say why, and a measured
cure does not transfer by analogy.

## 6. WHAT THE NEXT BRIEF NEEDS

**THE RESIDUE IS NOT WHERE THE SITES ARE. IT IS AT ONE TYPE.** The two
sites consume the family exactly as the parameter offers it. Nothing
narrows. So there is no site-level cure to buy.

The whole gap between what is delivered and what is demanded is
`SqCollect`, at `src/L/StageBound.lagda.md:44-47`:

    SqCollect α =
        ((δ : S) → ⟨ δ ∈ˢ sucV α ⟩ → (⟨ δ ∈ˢ ω ⟩ → Empty.⊥) → ∥ sq δ ∥₁)
      → ∥ SqFam α ∥₁

Its own comment at `src/L/StageBound.lagda.md:42` says `Not inhabited.`
The truncated half of it is ALREADY DELIVERED: `SLC.sq-trunc-closed`
(`src/L/SquareLawClosed.lagda.md:325-328`) gives `∥ sq δ ∥₁` for every
infinite `δ` in the band, and `bounded-modulo-collect`
(`src/L/StageBound.lagda.md:137-139`) already routes it.

So the campaign has three moves and this measurement prices them:

1. **PIN THE AMBIENT AT `ω`.** Then `param-at-ω` (`Probe636.agda:391-392`)
   closes the parameter today, with no new mathematics. **The cost is not
   in the square law. It is in whether `BoundedSubsetAt` can be entered at
   `α ≡ ω`, and this probe does not measure that.** That is the next
   question I would put to a coder.
2. **INHABIT `SqCollect`.** This is a selection problem and not a square
   law problem. `dev/literature/truncation-and-selection.md:218` says a
   family indexed by `V ℓ`, which is a set, is out of reach of the
   standard taboo and is also not proved, so it must be ruled on.
   `archive/dev/JOURNAL.md:1366` already named the weakly constant
   endomap on `sq δ` as the widest unmeasured term for this stall, and
   step 3 of the digest's checklist (`dev/literature/truncation-and-selection.md:291-296`)
   is the one that most often has an answer. **NOBODY HAS RUN STEP 3 ON
   `sq δ` YET.** I did not run it either: this brief did not ask for it.
3. **BUILD `sq δ` UNTRUNCATED ABOVE `ω`.** This is the expensive move and
   this measurement gives no reason to prefer it over move 2.

**A WARNING FOR THE NEXT BRIEF.** Do not read row A's verdict as "the
square law is needed at every ordinal". It is needed at every ordinal
**the ambient admits**, and the ambient is free. The demand is a function
of one choice nobody has made yet.

## 7. CLAUSES

- **W2 (generic carrier).** Answered and not violated. This task writes no
  mathematics into `src/`. The probe itself is generic: `Hyp`, `Applies`,
  `Evidence`, `Site`, `no-force-ω`, `no-force-above` and `both` are stated
  once over an arbitrary hypothesis family, and all three census rows
  instantiate them. No row repeats a proof.
- **W4 (retirement).** No module was retired and `dev/ARCHIVE.md` needs no
  row.
- **RATIO BAR.** Not applicable. `Probe636.agda` is a raw `.agda` file and
  carries no ` ```agda ` fence, so its in-fence line count is 0.
- **CALIBER.** `GHCRTS=[-A64m -I0 -M2g]`, set by the program on this pane.
  I did not set it. Every `.out` records it. One Agda process at a time
  throughout.
- **PROBE LOCATION.** `agents/tasks/LJ-1-636/Probe636.agda`, with its runs
  in `agents/tasks/LJ-1-636/runs/`. Nothing in `src/`.

## ARCHIVE USED

- `archive/dev/LJ-dispatch-index.md` **READ.** `archive/dev/LJ-dispatch-index.md:192`:
  `| LJ-1.116 | At which alpha does Upper need sq? | ONLY AT OMEGA, AT THE SITE | Generic demand is every infinite ordinal below alpha; the site is omega. Init is false at omega and at successors |`.
  This is the brief's premise 4. Section 3 above measures it again at the
  site it names.
- `archive/dev/JOURNAL.md` **READ.** `archive/dev/JOURNAL.md:1366`:
  `  pricing. **That endomap on `sq δ` is now the widest unmeasured term, and`.
  It names the weakly constant endomap on `sq δ` as the open term for the
  truncation stall. Section 6 above carries it forward.
- `archive/dev/JOURNAL-archived.md` **NOT READ, DECLINED.** I searched it
  for `LJ-1.116`, `LJ-1.117` and `StageCardinal` and it returned nothing,
  so it holds no record of this parameter.
- `archive/dev/ORCHESTRATION.md` **NOT READ, DECLINED.** It is the archived
  process document. This task measures a type in `src/` and no process
  question arose.
- `dev/ARCHIVE.md` **NOT READ, DECLINED.** No module was retired by this
  task, so it has no row to check and no row to add.

## LITERATURE USED

- `dev/literature/truncation-and-selection.md` **READ.**
  `dev/literature/truncation-and-selection.md:218`:
  `supplied by univalence. A family indexed by `V ℓ`, which is a set, offers no`.
  This is the exact shape of `SqCollect`, and section 6 above cites it and
  its checklist at `:291-296`.
- `dev/literature/devlin-II5.md` **NOT READ, DECLINED.** This task measures
  where an Agda module parameter is applied. No source question about
  Devlin's II.5 arose, and the classical text says nothing about which
  ordinal an Agda binder ranges over.
- `dev/literature/terms-2026-08.md` **NOT READ, DECLINED.** It is a
  terminology file. This task names no new term.
- `dev/literature/digest.md` **NOT READ, DECLINED.** The one digest this
  task needed is the selection one above, and I read that directly.
- `dev/literature/glossary-review-2026-08.md` **NOT READ, DECLINED.** No
  glossary entry was proposed or needed.
