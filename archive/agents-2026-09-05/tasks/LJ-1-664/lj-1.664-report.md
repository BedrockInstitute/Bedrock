# LJ-1.664 report: is the hull closed under the definable powerset

## HEAD
slot: `coder`. Written early as a skeleton and filled as runs landed
(C-22). No commit, no push. I wrote only in `agents/tasks/LJ-1-664/`.
Agda ran under the caliber the program set on this pane,
`GHCRTS="-A64m -I0 -M2g"`, the wide caliber, ONE Agda process at a time.
I did not set `GHCRTS`. No heap event: the largest peak of any run is
689,176,576 bytes against the 2,147,483,648-byte cap.

TARGET: build ONE term in `agents/tasks/LJ-1-664/Probe664.agda`:

    DeeInHull : (y : S) → ⟨ y ∈ˢ M ⟩ → ⟨ 𝒟ₒ y ∈ˢ M ⟩

Nothing lands in `src/`. That type is `[LJ-1.652]`'s, copied from its
report (`agents/tasks/LJ-1-652/lj-1.652-report.md:32-33` and
`Probe652.agda:280-281`).

The standing direction (`dev/pod/direction.md:37`) says one SRC
collection after LJ-1, not after `[LJ-2.5]`. This task is LJ-1 work. It
does not start that collection and it does not start phase 3. No
Boundary clause is in conflict.

## VERDICT

**NO-GO on the closed term. GO on the search's map.**

- **NO-GO.** `DeeInHull` is not inhabited as a closed term. The witness
  meter reads `1 UNRESOLVED of 1, 2.70 s, probe_red=False`
  (`runs/meter-obligation.out:2`). The stated NO-GO is
  `agents/tasks/LJ-1-664/review-of-dee-in-hull.md`. That file is the
  critic's input and it does not close the task.
- **GO, unasked, on the consumer.** `At.dee-from-code`
  (`Probe664.agda:115-118`) delivers the brief's type from
  `DeeCode∥`. It is `[LJ-1.647]`'s `hull-closed-op∥` at `F = 𝒟ₒ`.
  Meter: `0 UNRESOLVED of 4` on the nested names
  (`runs/meter-consumer.out:5`).

The probe is green and carries no hole (`runs/p-final.out:4`,
`EXIT=0` at `runs/p-final.out:23`). Three forced rechecks,
`runs/recheck-1.out` through `recheck-3.out`, each `EXIT=0`.
Two other delivered names at the probe module,
`census-DefAt` and `defAt-bound`, meter `0 UNRESOLVED of 2`
(`runs/meter-names.out:3`).

**This is not a refutation of `DeeInHull`.** I did not build a term of
its negation. The statement is true of an elementary hull of a limit
stage.

## THE PREDECESSOR QUESTION, ANSWERED BEFORE ANY AGDA

`[LJ-1.652]` delivered `DeeInHull` as a TYPE, not as a term. Its report
is a stated NO-GO at `picommute-D-from-elem` and a GO at clause (iii)'s
`Commute` (`agents/tasks/LJ-1-652/lj-1.652-report.md:27-40`). The type
this brief copies is the residue Agda printed
(`agents/tasks/LJ-1-652/runs/residue-1.out:4`):

    when checking that the expression y∈M has type ⟨ 𝒟ₒ y ∈ˢ F.HS.M ⟩

I take that type. I do not inhabit a type the predecessor named FALSE:
the predecessor named no refutation of `DeeInHull`
(`agents/tasks/LJ-1-652/lj-1.652-report.md:48-49`).

`[LJ-1.651]` delivered `lset-formula : Formula Code 2` and the
arity-1 reading `inF` (`agents/tasks/LJ-1-651/lj-1.651-report.md:29-30`).
That is the closest analogue, and it does not cover `𝒟ₒ`. I take the
type that predecessor delivered. I do not treat it as a `𝒟ₒ` formula.

`[LJ-1.647]` delivered `hull-closed-op∥`, generic in the operation
(`agents/tasks/LJ-1-647/Probe647.agda:135-148`). I import that module
and instantiate it. I do not rewrite the proof.

## D-10, BEFORE ANY AGDA

D-10 says to price the truth of the target before pricing its proof.

1. The target. `DeeInHull` is true of an elementary hull of a limit
   stage: a definable operation on a hull member is again a hull
   member, once the stage holds the value and the language can name
   the operation. I did not find a cardinality or Tarskian obstruction.
2. The hypothesis the closed term would spend. Two suppliers are
   unpaid in the tree, and either one stops the term. `PowIter` is a
   named hypothesis with no supplier
   (`src/L/Coding/Bound.lagda.md:147-152`). A `Formula Code 1` for
   `𝒟ₒ y` is not delivered: `DefAt` is a `Formula S 2` with 166
   constants (`Probe664.agda:62-63`).
3. The corrected target beside the original, as D-10 asks:
   `dee-from-code : DeeCode∥ → (y : S) → ⟨ y ∈ˢ M ⟩ → ⟨ 𝒟ₒ y ∈ˢ M ⟩`
   (`Probe664.agda:115-118`). Same conclusion, one named hypothesis.

## THE FLOOR, AND HOW IT WAS TAKEN

The standing clause asks for the frame to be priced before the proof.

- **The floor was priced first.** `runs/FLOOR.agda.txt`: the trimmed
  frame, the obligation in full, and a HOLE where the term goes. Its
  run is `runs/floor-1.out`: **exit 42 at 2.40 s, peak 445,038,592
  bytes**, with `[UnsolvedInteractionMetas]` at the one designed hole
  (`:5-7`) and no other error.
- **The trim is why the frame is cheap.** The statement names `M`,
  `𝒟ₒ` and hull membership, and nothing else, so the floor drops
  Collapse, Formula, `mapFo` and CloseSyntax. Every later green run
  stayed inside 530 MB. The close-syntax slice peaked at 689 MB
  because it imports `L.BoundedSubset`. No restructuring was needed
  and no heap wall was met.

**THE SLICE IS DELIVERED WITH A `.txt` SUFFIX, ON PURPOSE.** It is red
by design. The close-syntax slice is `.agda.txt` for the same reason.
`find agents/tasks/LJ-1-664 -name '*.agda'` returns `Probe664.agda`
and nothing else.

## W3, THE CODE MAP, AND THE BRIEF'S PREMISE 2 IS SPLIT

The brief names W3 as "the code map at `A.SM`" at 100 to 220 lines,
basis `[LJ-1.651]`'s 156-line probe.

**TWO MAPS WERE CONFLATED. THEY ARE NOT THE SAME OBJECT.**

**Map A, `f : A.SM → Code`.** This is what `HullElemDown.WithCode`
takes (`src/L/BoundedSubset.lagda.md:681-682`). **It is already in
the tree.** `hedF` at `src/L/BoundedSubset.lagda.md:1648-1652`,
instantiated as `module HEDC = HED.WithCode hedF hedF-spec` (`:1660`).
The brief's premise 2 priced this map as missing. It is not missing.
It lives inside `Devlin55` and is not available from a HullStage-only
telescope. I did not rebuild it.

**Map B, the operation map `DeeCode∥`.** This is what the consumer
spends (`Probe664.agda:108-110`). It is not built. This is the object
`[LJ-1.647]` closed as a *consumer* for `Lset` and left as
`[LJ-1.646]`'s keystone to *produce*. For `𝒟ₒ` there is no producer.

**The grade does not behave as it did for `Lset`.**
`census-DefAt` (`Probe664.agda:62-63`) is `countFo (DefAt u w) ≡ 166`,
green by `refl`, seal opened on `satGraphAt`. `[LJ-1.651]`'s
`lset-formula` has `countFo ≡ 0` (`Probe651.agda:115-116`). The cheap
Σ₀ matrix with a dummy `mapFo` slide does not exist for `𝒟ₒ`. Kunen
never writes one (`dev/literature/level-formula-slot-roles.md:79`).

**`defAt-bound` (`Probe664.agda:69-71`) re-measures `[LJ-1.514]`'s
instrument at `DefAt`:** `mkBoundedFo` is total
(`src/L/Axioms/Separation.lagda.md:449`). The 166 constants all lie
in some stage. That transports `DefAt` to a STAGE alphabet. It does
not produce a `Formula Code`.

**`CloseSyntax.close` cannot then close a parameter at `Code`.**
`runs/CLOSE.agda.txt` asks Agda at a dummy `Type ℓ`. Agda prints
`[UnequalSorts] Type ℓ != Type (ℓ-suc ℓ)` (`runs/close-1.out:5-7`).
That is `[LJ-1.652]`'s universe mismatch, now a run and not an
argument.

Line count: 140 total, 56 non-blank non-comment (`Probe664.agda`).
The brief estimated 100 to 220 for building the map. This file did
not build Map B. It measured why Map B is not the Lset job.

## WHAT WAS BUILT

All in `agents/tasks/LJ-1-664/Probe664.agda`, module
`LJ-1-664.Probe664 {ℓ} (lem)`. The telescope `At` is `[LJ-1.647]`'s
`HullStage`, which is `[LJ-1.462]`'s minus Collapse.

**Top level.**

- `census-DefAt` (`:62-63`). `countFo (DefAt u w) ≡ 166`.
- `defAt-bound` (`:69-71`). `mkBoundedFo (DefAt u w)`.

**Module `At`.**

- `hull-mem-is-code` (`:96-98`). `refl`, the same identity
  `[LJ-1.647]` pinned.
- `DeeCode∥` (`:108-110`). The operation map, named, not inhabited.
- `dee-from-code` (`:115-118`). The consumer. W2.
- `DeeInHull` (`:125-126`). The brief's type, as a type, not lifted
  to the probe module. The witness reads `Target.DeeInHull` at the
  probe module (`scripts/pod/witness.py:278`) and does not find it.
- `PowIter` (`:134-136`). Verbatim
  `src/L/Coding/Bound.lagda.md:151-152`, named, not inhabited.

## W2 (DD4)

The mathematics is written once at a generic operation and
instantiated. `hull-closed-op∥` is `[LJ-1.647]`'s term. This file
imports it and supplies `F = 𝒟ₒ` and `P = Unit*`. No line of that
proof is rewritten. The deadline conflict the clause names did not
arise: generic was cheaper than a second copy.

`census-DefAt` and `defAt-bound` are not instances of that term.
They are measurements of a different object, the delivered formula.

## W4 (DD13)

Nothing was retired. No module moved to `archive/`. No dead fragment
was deleted. `dev/ARCHIVE.md` gains no row from this task.

## C-42

No refutation was produced, so the sweep this law demands does not
fire. I did not count live `src/` occurrences of a false shape,
because no false shape was proved. Premise 2 of this brief is false
as a claim that Map A is missing; that is a false premise of a
brief, not a false statement in the tree, and I did not run the
sweep.

## RUNS

Caliber `-A64m -I0 -M2g`, set on the pane by the program and
untouched here. One Agda process at a time, from the worktree root.
The probe interface was deleted before every forced recheck
(`_build/2.8.0/agda/agents/tasks/LJ-1-664/Probe664.agdai`).

Build history, in order:

| run | contents | exit | wall s | peak RSS bytes |
|---|---|---|---|---|
| `floor-1` | `FLOOR.agda.txt`, designed hole | 42 | 2.40 | 445,038,592 |
| `p-1` | first probe, `Code` not exported by `HullStage` | 42 | 2.28 | 507,002,880 |
| `p-2` | consumer plus census | 0 | 2.38 | 529,383,424 |
| `p-3` | plus `defAt-bound`, `V` not in scope | 42 | 2.45 | 451,985,408 |
| `p-4` | `V` imported, first full green | 0 | 4.35 | 528,318,464 |
| `close-1` | `CLOSE.agda.txt`, universe mismatch | 42 | 2.90 | 689,176,576 |

`p-1` is `[NotInScope]` for `Code`: `[LJ-1.647]` opens `Code` inside
`HullStage` without `public`. One `open HS.H.T` line. `p-3` is
`[NotInScope]` for `V`. No restructuring, and no heap event at any
point.

Three forced rechecks of the delivered file, probe interface removed
each time:

| run | exit | wall s | peak RSS bytes |
|---|---|---|---|
| `runs/recheck-1.out` | 0 | 4.49 | 528,367,616 |
| `runs/recheck-2.out` | 0 | 4.51 | 528,367,616 |
| `runs/recheck-3.out` | 0 | 4.50 | 528,318,464 |

Median wall **4.50 s**. Median peak RSS **528,367,616 bytes**. Exit 0
every time.

`runs/p-final.out` is the last check, after the unused `Formula`
import was dropped: exit 0, 5.55 s, 397,623,296 bytes.

Meters, this worktree has no `.venv`, so they ran as
`/Users/alsg/Agentic/Bedrock/.venv/bin/python scripts/pod/witness.py`.
I did not add a dependency and I did not create a local `.venv`.

- Obligation: `1 UNRESOLVED of 1, 2.70 s, probe_red=False`
  (`runs/meter-obligation.out:2`).
- Top-level names: `0 UNRESOLVED of 2, 2.27 s, probe_red=False`
  (`runs/meter-names.out:3`).
- Nested consumer names: `0 UNRESOLVED of 4, 2.43 s, probe_red=False`
  (`runs/meter-consumer.out:5`).

Gates run while working: `scripts/gate/lint-agda.py --check` on
`Probe664.agda` exit 0, `scripts/gate/check-probes.py --check` clean,
10144 tracked files.

## WHAT THE NEXT BRIEF NEEDS

1. **DO NOT RE-DISPATCH `DeeInHull` AS A CLOSED TERM.** It still owes
   a supplier. The consumer is paid (`dee-from-code`). Map A is paid
   in `src/` (`hedF`). Map B is not.
2. **THE BINDING DEBT IS `PowIter`, AND IT IS A TOWER FACT.**
   `src/L/Coding/Bound.lagda.md:147-149` already says nothing in
   `src/` proves it. `hull-closed` cannot fire without
   `⟨ 𝒟ₒ y ∈ˢ Lset lam ⟩`, and `Hull⊆L` makes the same fact
   necessary for the conclusion. Price its truth as "the limit stage
   is closed under `𝒟ₒ` at an arbitrary member", not as a hull
   search.
3. **A `Formula Code 1` FOR `𝒟ₒ` IS A SECOND DEBT, NOT A SUBSTITUTE
   FOR `PowIter`.** `DefAt` has 166 constants. `mkBoundedFo` sends it
   to a stage alphabet. CloseSyntax cannot close a parameter at
   `Code`. The Lset dummy-slide does not apply. `[LJ-1.651]`'s `inF`
   is not this object.
4. **CLAUSE (iii)'s `Commute` STAYS CLOSED.** This task did not
   re-attack it. `[LJ-1.652]`'s `commute-641` still stands.
5. **WHAT THE STATEMENT COST.** 56 non-blank non-comment lines,
   median 4.50 s, median peak 528,367,616 bytes, three red runs
   (floor, one import, one name), no heap event. **WHAT THE SHAPE
   RESISTED.** The closed term. The shape that worked is the
   consumer-from-code-map, and that is `[LJ-1.647]`'s shape at a
   new `F`. **WHAT I HAD TO WEAKEN.** The obligation, from a closed
   term to a term from `DeeCode∥`. **WHAT I COULD NOT CLOSE.**
   `DeeInHull`, `DeeCode∥`, `PowIter`, and a `Formula Code 1` for
   `𝒟ₒ`.

## ARCHIVE USED

- `archive/dev/ORCHESTRATION.md`: read at `:1`. Quote:
  `# ORCHESTRATION: the orchestrator's operating rules`
  Declined, not used. It is the archived operating document. The
  rules that bind this slot are `AGENTS.md` and
  `dev/pod/instructions/coder.md`.
- `archive/dev/DD-archived.md`: read at `:1`. Quote:
  `# THE `DD` RULING SERIES, archived in full 2026-08-18`
  Declined, not used. W2 and W4 are live clauses of the slot file.
  The archived DD series is not the source for this term.
- `archive/dev/PLAN-archived.md`: read at `:1`. Quote:
  `# ARCHIVED 2026-08-20`
  Declined, not used. The live status is `dev/pod/screen.toml`. This
  obligation is on the live hull, not on the archived plan.
- `archive/dev/STATUS-archived.md`: read at `:1`. Quote:
  `# STATUS-archived: the goal table of the internalization route`
  Declined, not used. The internalization-route goal table is not
  the source for `DeeInHull`.
- `archive/dev/TASKS-archived.md`: read at `:1`. Quote:
  `# Archived task index: the `L3.32-T` series`
  Declined, not used. The predecessors this task reads are live
  task homes under `agents/tasks/`.

## LITERATURE USED

- `dev/literature/devlin-errata.md`: read at `:1`. Quote:
  `# Devlin errata: documented error classes (do-not-repeat checklist)`
  Declined, not used. No Devlin erratum bears on hull closure under
  `𝒟ₒ`.
- `dev/literature/level-formula-slot-roles.md`: **USED.** Read at
  `:79`. Quote:
  `Kunen defines the definable powerset as a SET (Definition VI 1.1, printed page`
  Also read at `:1`. Quote:
  `# The level-hood formula: arity, what it binds, what stays free`
  This is why the cheap Σ₀ twin of `levelHoodB` is not sitting in
  the literature for `𝒟ₒ`: Kunen writes no object-level formula for
  the definable powerset. The tree's `DefAt` is a construction, not
  a textbook matrix.
- `dev/literature/glossary-review-2026-08.md`: read at `:1`. Quote:
  `# Glossary review: the 119 pre-protocol entries`
  Declined, not used. No glossary term is at issue and I added no
  `dev/glossary.toml` entry.
- `dev/literature/primary-sources.md`: read at `:1`. Quote:
  `# Primary sources, second round: Jensen manuscript, Devlin, Jech`
  Declined, not used. The slot-role note above is the source that
  decided the formula question.
- `dev/literature/BIBLIOGRAPHY.md`: read at `:1`. Quote:
  `# Bibliography for the rud route`
  Declined, not used. It is the index over the corpus. The specific
  note `level-formula-slot-roles.md` carries the fact this task
  used.

## WHAT I DID NOT DO

- I did not commit. I did not push.
- I did not set `GHCRTS`. I did not start a second Agda process.
- I did not write in `src/`.
- I did not inhabit `DeeInHull` as a closed term.
- I did not inhabit `DeeCode∥` or `PowIter`.
- I did not build `wit` at `absFo DefAt`. That is the route
  `[LJ-1.646]` refused for `LsetGraph`, and `DefAt` is a component
  of that graph.
- I did not refute `DeeInHull`.
- I did not postulate. I left no hole in `Probe664.agda`.
- I did not leave a red `.agda` under this task home: the two files
  that cannot typecheck are `runs/FLOOR.agda.txt` and
  `runs/CLOSE.agda.txt`.
- I did not add a dependency and I did not create a local `.venv`.
- I did not re-attack clause (iii)'s `Commute`.

## WORKING TREE, AS THIS REPORT DESCRIBES IT

Nothing committed, nothing pushed. No master edited. `src/` untouched.

New files, all in `agents/tasks/LJ-1-664/`:

- `Probe664.agda`, the search, green
- `lj-1.664-report.md`, this report
- `review-of-dee-in-hull.md`, the stated NO-GO
- `runs/`, the Agda transcripts and the two `.agda.txt` slices named
  above
