# LJ-1.477 report: does the collapse commute with the stage operation

slot: `coder`. Written early as a skeleton and filled as runs landed
(C-22). No commit, no push. I wrote only in `agents/tasks/LJ-1-477/`.
Agda ran under the caliber the program set on this pane,
`GHCRTS="-A64m -I0 -M8g"`, ONE Agda process at a time. I did not set
`GHCRTS`. No heap event.

TARGET: build ONE term in `agents/tasks/LJ-1-477/Probe477.agda`:

    piCommuteLset : (y : S) → ⟨ y ∈ˢ M ⟩ → C.π (Lset y) ≡ Lset (C.π y)

where `M` is the definable hull and `C = Collapse M`, copied from
`src/L/BoundedSubset.lagda.md:903-916`. Nothing lands in `src/`.

The standing direction (`dev/pod/direction.md:37`) says one SRC
collection after LJ-1, not after `[LJ-2.5]`. This task is still LJ-1
work. It does not start that collection. It does not start phase 3.
No Boundary clause is in conflict.

## PREDECESSOR VERDICT, BEFORE ANY AGDA

`[LJ-1.462]` verdict at `agents/tasks/LJ-1-462/lj-1.462-report.md:75`:

    **NO-GO at D-10 step 3, and it is not `[LJ-1.451]`'s absence.**

The critic upheld that return
(`agents/tasks/LJ-1-462/review-of-LJ-1-462-1.md:6`). The report does
not name `πCommuteLset` FALSE. The type is at
`agents/tasks/LJ-1-462/Probe462.agda:140-142`:

    πCommuteLset : Type (ℓ-suc ℓ)
    πCommuteLset =
      (y : S) → ⟨ y ∈ˢ M ⟩ → C.π (Lset y) ≡ Lset (C.π y)

and the comment at `:144` says "Step 4. Absoluteness. Same type as
πCommuteLset. Unbuilt." The gate in the brief is met. I take that
type. I do not stop. I do not inhabit `[LJ-1.462]`'s failed step 3.
I do not build `levelIn`, `lset-codes` or `lset-code`.

## D-10, BEFORE ANY AGDA

The two computation laws, at `file:line`.

1. Collapse, `src/V/Collapse.lagda.md:47-48` and `:58-59`:

       step : (x : S) → (∀ y → y ∈ᵗ x → S) → S
       step x rec = sett (Fiber x) (λ p → rec (⟪ x ⟫↪ (p .fst)) (member x (p .fst)))

       π-compute : (x : S) → π x ≡ step x (λ y _ → π y)

   `Fiber x` is the small members of `x` that also lie in the carrier
   (`src/V/Collapse.lagda.md:44-45`).

2. Stage, `src/L/Constructible.lagda.md:215-216` and `:227-228`:

       LsetStep : (α : S) → (∀ β → β ∈ᵗ α → S) → S
       LsetStep α rec = ⋃ (sett ⟪ α ⟫ (λ m → 𝒟ₒ (rec (⟪ α ⟫↪ m) (mem m))))

       Lset-compute : (α : S) → Lset α ≡ LsetStep α (λ β _ → Lset β)

One line. The collapse's `step` at `Lset y` builds a `sett` of `π`
images of members of `Lset y` that lie in `M`. `LsetStep` at `C.π y`
builds a `⋃` of `𝒟ₒ` of `Lset` at members of `C.π y`. The two
constructors do not match. `step` does not send the members of
`Lset y` to the members of `Lset (C.π y)` by those two laws alone.

The type of `piCommuteLset` does not mention `⟨ Lset y ∈ˢ M ⟩`. Both
sides are well-typed because `π` (`src/V/Collapse.lagda.md:53-54`)
and `Lset` (`src/L/Constructible.lagda.md:222-223`) are total on `S`.
Step 4 can be stated without step 2. I do not take `HullClosedLset`
as a module hypothesis. I do not stop.

Without `HullClosedLset`, the left side applies `π` to a value that
may lie outside `M`. The statement is about a `π` value outside the
hull whenever step 2 fails. This task does not build step 2.

The predecessor type has no `IsOrd`. Devlin 5.2 at
`dev/literature/devlin-II5.md:72` is the condensation of an
elementary submodel of a limit stage. I do not add `IsOrd`. I take
the predecessor type.

I do not add an absoluteness hypothesis. Absoluteness of `Lset`
under the collapse is what this task measures.

## W2 (DD4)

The mathematics is written once at a generic carrier. The module is
generic in `ℓ`. `lam`, `X` and the limit hypotheses stay parameters.
No ordinal is fixed. No second copy at a concrete stage. The conflict
the clause names did not arise.

## W4 (DD13)

Nothing was retired. No module moved to `archive/`.

## VERDICT

**NO-GO at the join of the two computation laws.** Both laws spend.
Their right-hand sides do not meet. The obligation term
`piCommuteLset` is not written. Witness meter: 1 UNRESOLVED of 1,
`probe_red=False` (`runs/witness.out:1-2`).

This is an obstruction of the computation-law route. It is not a
refutation of `piCommuteLset`. I did not build a term of the
negation.

The NO-GO is stated in
`agents/tasks/LJ-1-477/review-of-piCommuteLset.md`. That file is the
critic's input. It does not close the task.

## 1. What was built

All in `agents/tasks/LJ-1-477/Probe477.agda`, module
`LJ-1-477.Probe477 {ℓ} (lem)`.

- Telescope `HullStage` (`:45-57`), copied from
  `src/L/BoundedSubset.lagda.md:903-916`. The module keyword is at
  `:903`. Line `:916` is `module Condense`, and it is not copied.
  `M = H.T.Hull`. `module C = Collapse M`.
- W3 inhabited: `both-compute` (`:68-69`) is `C.π-compute (Lset y)`.
  The hole in the type fills with
  `C.step (Lset y) (λ z _ → C.π z)`. The seal on `π` does not open.
- The other law inhabited: `after-L` (`:81-82`) is
  `Lset-compute (C.π y)`. The seal on `Lset` does not open.
- The join as a type: `JoinSteps` (`:90-93`). Unbuilt.
- Predecessor type restated: `PiCommuteLset` (`:100-102`). Unbuilt.
  No term named `piCommuteLset`.

Measured non-blank non-comment lines: 35. Total lines: 102. The
brief estimate was about 150 lines, of which the obligation is about
40. Nothing is funded against the estimate.

## STEP ONE, W3

**The exported law spends at `Lset y` without unfolding the seal.**
`both-compute` (`Probe477.agda:68-69`) is the brief's W3, stated
with the obligation omitted. Three forced rechecks, `_build`
interface removed before each, dependencies warm, caliber
`-A64m -I0 -M8g`, one Agda process. Exit 0 every time. Each printed
`Checking`.

| run | wall s | peak RSS bytes |
|---|---|---|
| `runs/w3-1.out` / `w3-1.time` | 1.97 | 473563136 |
| `runs/w3-2.out` / `w3-2.time` | 1.97 | 473563136 |
| `runs/w3-3.out` / `w3-3.time` | 2.07 | 473563136 |

Median wall **1.97 s**. Median peak RSS **473563136 bytes**. No heap
event. The first W3-only check `runs/w3-0.out` was 1.99 s and
473546752 bytes, also exit 0, also printed `Checking`. It is not
one of the three forced rechecks. The brief estimate for W3 was
about 10 lines and under 20 seconds. The measured median is under
that estimate.

The brief named the heap-cost shape `[LJ-1.398]` measured at 8 GB
on a different seal. That shape did not fire. The type of
`π-compute` is visible without `unfolding π`. Applying the law at
`Lset y` does not open the seal.

## STEP TWO, THE OBLIGATION

Both laws spent. The join is unbuilt.

`after-L` (`Probe477.agda:81-82`) applies `Lset-compute` at
`C.π y`. Together with `both-compute`, the two computation laws
are now terms at one argument. Closing `piCommuteLset` then needs

    C.step (Lset y) (λ z _ → C.π z)
  ≡ LsetStep (C.π y) (λ β _ → Lset β)

That type is `JoinSteps` (`Probe477.agda:90-93`). A diagnostic
inhabitant `join-refl y = refl` failed with `[UnequalTerms]`
(`runs/join-refl.out:2` and `:30-31`):

    when checking that the expression refl has type
    C.step (Lset y) (λ z _ → C.π z) ≡ LsetStep (C.π y) (λ β _ → Lset β)

The `refl` was then removed. The green file does not contain it.
Exit of that diagnostic was 42. It is not one of the kept full
rechecks.

I did not inhabit `JoinSteps` by an extra hypothesis. The brief
forbids an absoluteness hypothesis. `HullClosedLset` does not
change either constructor, so it does not close `JoinSteps`. I did
not take it.

I did not prove the type false. A non-ordinal `y ∈ M` whose
members lie outside `M` is a candidate obstruction at this
generality, because `Lset-out` witnesses need not lie in the hull.
I did not build that counterexample.

## 2. Runs, floor, witness

Caliber `-A64m -I0 -M8g`, set on the pane by the program and
untouched here. One Agda process at a time, every dependency warm,
from the repository root. The probe interface was deleted before
every kept run.

- W3, three forced rechecks: see the table above. Median **1.97 s**,
  **473563136 bytes**. Exit 0.
- Full file, three forced rechecks. Both laws are in the file. The
  obligation is omitted.

| run | wall s | peak RSS bytes |
|---|---|---|
| `runs/full-recheck-1.out` / `full-recheck-1.time` | 1.94 | 472678400 |
| `runs/full-recheck-2.out` / `full-recheck-2.time` | 1.95 | 472662016 |
| `runs/full-recheck-3.out` / `full-recheck-3.time` | 1.95 | 472678400 |

Median wall **1.95 s**. Median peak RSS **472678400 bytes**. Exit 0
every time. Each printed `Checking`. No heap event. The first full
check after the join types were added, `runs/full-0.out`, was
1.94 s and 472662016 bytes, also exit 0. It is not one of the
three forced rechecks.

- Witness meter, one obligation: 1 UNRESOLVED of 1, 1.93 s,
  `probe_red=False` (`runs/witness.out:1-2`). The name
  `piCommuteLset` is not in scope. That is the intended NO-GO
  reading. This worktree has no `.venv`. The meter ran as
  `/Users/alsg/Agentic/Bedrock/.venv/bin/python scripts/pod/witness.py --brief agents/tasks/LJ-1-477/LJ-1.477.md`.
  I did not add a dependency. I did not create a local `.venv`.

## WHAT LEVELIN STILL OWES

The four steps of `[LJ-1.462]`, as types, and which are built.

1. Collapse membership. BUILT. Type and term at
   `agents/tasks/LJ-1-462/Probe462.agda:129-134`, equal to
   `C.πX-member` at `src/V/Collapse.lagda.md:78-79`. This task does
   not re-inhabit it.

2. Hull closed under `Lset`. UNBUILT.

       HullClosedLset :
           (y : S) → ⟨ y ∈ˢ M ⟩ → ⟨ Lset y ∈ˢ M ⟩

   Site: `agents/tasks/LJ-1-462/Probe462.agda:136-138`. This task
   did not take it as a module hypothesis and did not build it.

3. Definability of `Lset` in the hull language. UNBUILT.

       lset-code :
           (c : Code) → Σ[ d ∈ Code ] (fst (val d) ≡ Lset (fst (val c)))

   Site: `agents/tasks/LJ-1-462/Probe462.agda:109-111`. This task
   did not touch it. `[LJ-1.474]` is that work.

4. Absoluteness, same type as `πCommuteLset`. UNBUILT. Restated at
   `agents/tasks/LJ-1-477/Probe477.agda:100-102`. The join of the
   two computation laws is `JoinSteps` at `:90-93`, also unbuilt.

The join into `levelIn`, priced as a composition and not claimed.
If step 2 and step 4 were inhabited, the consumer at
`src/L/BoundedSubset.lagda.md:917` is:

    levelIn δ oδ δ∈πX =
      PT.rec (snd (Lset δ ∈ˢ C.πX)) go (C.πX-member δ δ∈πX)
      where
      go (y , y∈M , e) =
        subst (λ z → ⟨ Lset z ∈ˢ C.πX ⟩) e
          (subst (λ w → ⟨ w ∈ˢ C.πX ⟩) (piCommuteLset y y∈M)
            (C.πX-intro (Lset y) (HullClosedLset y y∈M)))

That composition uses steps 1, 2 and 4. It does not use step 3.
Step 3 is a producer for 2 and 4, not a conjunct of this join.
I do not claim `levelIn`. I do not claim this composition
typechecks. `IsOrd δ` is unused in it, and `y` need not be an
ordinal.

## 3. What NO-GO earns, and what is still owed

NO-GO names the join of `π-compute` at `Lset y` with
`Lset-compute` at `C.π y`. Both terms exist. `JoinSteps` does not.
A `refl` between those right-hand sides is `[UnequalTerms]`.

`cover` is untouched. `levelIn` stays an unpaid hypothesis of
`module Condense`.

What this task does not settle:

- It does not inhabit `piCommuteLset`.
- It does not inhabit `JoinSteps`.
- It does not inhabit `HullClosedLset`.
- It does not inhabit `lset-code`.
- It does not inhabit `levelIn`.
- It does not refute `piCommuteLset`.
- It does not pay `cover`.
- It does not edit `src/`.
- It does not touch step 3.

C-42: this is not a refutation. The sweep that law names does not
fire. The same unbuilt type already sits at
`agents/tasks/LJ-1-462/Probe462.agda:140-142` and
`agents/tasks/LJ-1-451/Probe451.agda:77-79`. I did not count live
`src/` occurrences of a false shape, because no false shape was
proved.

## 4. What the next brief needs

- Do not order `piCommuteLset` from the two computation laws
  again. They spend, and they do not join. The measurement is
  `runs/join-refl.out:2` (`[UnequalTerms]`) against
  `JoinSteps` at `Probe477.agda:90-93`.
- Do not order an unfolding of `π` in order to spend `π-compute`
  at `Lset y`. W3 measured that the exported law spends without
  opening the seal. Median 1.97 s, 473563136 bytes.
- Do not take `HullClosedLset` as a way to close `JoinSteps`.
  Closure of the hull under `Lset` does not change `step` or
  `LsetStep`.
- A proof of the commutation at this site needs more than the two
  laws: it needs `π` to commute with `𝒟ₒ`, and it needs
  `Lset-out` witnesses to lie in `M`. The hull is not transitive
  (`agents/tasks/LJ-1-160/lj-1.160-report.md:248-250`). Those needs
  are elementarity plus the level formula, which is step 3, or they
  are the collapse-image route that same report measured.
- Devlin 5.2 identifies the collapse image with a level by Φ and
  Σ₁ elementarity (`dev/literature/devlin-II5.md:95-106`). It
  does not commute the collapse with the stage operation. That
  reading was already measured at
  `agents/tasks/LJ-1-160/lj-1.160-report.md:261`.
- Step 3 remains independent. This return does not change its
  brief.
- What the statement cost: 35 non-blank non-comment lines, W3
  median 1.97 s, full median 1.95 s, peak RSS 473563136 bytes on
  the kept rechecks. What the shape resisted: the two constructors
  `sett` of filtered `π`-images against `⋃` of `𝒟ₒ` of `Lset`.
  What I had to weaken: nothing of the obligation. What I could
  not close: `JoinSteps`, `piCommuteLset`.

## ARCHIVE USED

- `archive/dev/LJ-dispatch-index.md`: read at `:1`. Quote:
  `# THE `LJ` DISPATCH INDEX, archived 2026-08-18`. Declined, not
  used. It is the retired dispatch index. This task measures a
  live chapter.
- `archive/dev/JOURNAL-archived.md`: read at `:1`. Quote:
  `# Archived journal: the retired route`. Declined, not used.
  Retired-route journal. The consumer is the live `BoundedSubset`
  chapter.
- `archive/dev/JOURNAL.md`: read at `:1`. Quote: `# ARCHIVED 2026-08-20`.
  Declined, not used. The per-episode journal is retired. The
  history of this task is this directory.
- `dev/ARCHIVE.md`: read at `:29`. Quote:
  `- **Module.** The module's name as it was known in the live tree, e.g.`
  Declined as not used for the term. No module is retired by this
  task.
- `archive/dev/DD-archived.md`: read at `:1`. Quote:
  `# THE `DD` RULING SERIES, archived in full 2026-08-18`. Declined,
  not used. The live clauses that bound this slot are W2 and W4.
  W4 did not fire: nothing was retired.

## LITERATURE USED

- `dev/literature/devlin-II5.md`: read at `:72`. Quote:
  `> 5.2 Theorem (The Condensation Lemma). Let α be a limit ordinal. If`
  Also read at `:95`. Quote:
  `> By 2.7 there is a Σ₀ formula Φ(z, v, γ) of LST such that`
  Also read at `:102`. Quote:
  `The chain (c) to (q) then runs: for each ordinal γ of the collapse, the Σ₁`
  Used: 5.2 is the literature form of condensation, and its engine
  is Φ plus Σ₁ transfer, not a commutation of `π` with `Lset`. The
  predecessor type has no `IsOrd` and no limit hypothesis. I did
  not add them. I did not take 5.2 as a proof of `piCommuteLset`.
- `dev/literature/truncation-and-selection.md`: read at `:1`. Quote:
  `# Truncation and selection: how the two literatures pick a witness`.
  Declined, not used. W3 is a computation law at one argument. It
  is not a truncation question.
- `dev/literature/terms-2026-08.md`: read at `:1`. Quote:
  `# The terminology dossier: fourteen renderings for the owner's ruling`.
  Declined, not used. No glossary term is at issue.
- `dev/literature/digest.md`: read at `:1`. Quote:
  `# Digest: the orthodox form of the rud route, pinned from the collected literature`.
  Declined, not used. No rud-route step is consulted.
- `dev/literature/glossary-review-2026-08.md`: read at `:1`. Quote:
  `# Glossary review: the 119 pre-protocol entries`.
  Declined, not used. No glossary entry is at issue.

## WHAT I DID NOT DO

- I did not commit. I did not push.
- I did not set `GHCRTS`.
- I did not start a second Agda process.
- I did not write in `src/`.
- I did not inhabit `piCommuteLset`, `JoinSteps` or `levelIn`.
- I did not take `HullClosedLset` as a module hypothesis.
- I did not postulate. I did not add an absoluteness hypothesis.
- I did not unfold the seal on `π` or on `Lset`.
- I did not touch step 3.
- I did not pay `cover`.
- I did not hide the constructor gap in a `subst`.

## WORKING TREE, AS THIS REPORT DESCRIBES IT

Nothing committed, nothing pushed. No master edited. `src/`
untouched.

New files, all in `agents/tasks/LJ-1-477/`:

- `lj-1.477-report.md`, this report
- `Probe477.agda`, W3 and the unbuilt join
- `review-of-piCommuteLset.md`, the stated NO-GO
- `runs/`, the Agda transcripts named above
