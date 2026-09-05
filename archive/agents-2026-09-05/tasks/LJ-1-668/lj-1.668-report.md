# LJ-1.668 report: is the limit stage closed under the definable powerset

## HEAD
slot: `coder`. Written early as a skeleton and filled as runs landed
(C-22). No commit, no push. I wrote only in `agents/tasks/LJ-1-668/`.
Agda ran under the caliber the program set on this pane,
`GHCRTS="-A64m -I0 -M2g"`, the wide caliber, ONE Agda process at a time.
I did not set `GHCRTS`. No heap event: the largest peak of any run is
332,529,664 bytes against the 2,147,483,648-byte cap.

TARGET: build ONE term in `agents/tasks/LJ-1-668/Probe668.agda`:

    powiter-status : the limit stage is closed under `𝒟ₒ` at an
                     arbitrary member, or a refutation at a member
                     the frame admits

Nothing lands in `src/`. That type is `[LJ-1.664]`'s unpaid tower fact,
copied from its report (`agents/tasks/LJ-1-664/lj-1.664-report.md:261-267`)
and from the tree's own hypothesis
(`src/L/Coding/Bound.lagda.md:151-152`), read at the limit as
`Bound.Iter.pow∈λ` (`src/L/Coding/Bound.lagda.md:109-110`).

The standing direction (`dev/pod/direction.md:37`) says one SRC
collection after LJ-1, not after `[LJ-2.5]`. This task is LJ-1 work. It
does not start that collection and it does not start phase 3. No
Boundary clause is in conflict.

## VERDICT

**NO-GO on the closed term. GO on the truth of two members, and GO
on the consumer.**

- **NO-GO.** `powiter-status` is not inhabited as a closed term. The
  witness meter reads `1 UNRESOLVED of 1, 1.14 s, probe_red=False`
  (`runs/meter-obligation.out:2`). The stated NO-GO is
  `agents/tasks/LJ-1-668/review-of-powiter-status.md`. That file is the
  critic's input and it does not close the task.
- **GO, unasked, on two members the frame admits.** `dee-empty`
  (`Probe668.agda:85-86`) is `𝒟ₒ ∅ ≡ sucV ∅`. `At.dee-empty∈limit`
  (`Probe668.agda:153-158`) puts it in `Lset lam`.
  `At.dee-stage∈limit` (`Probe668.agda:139-143`) puts `𝒟ₒ (Lset δ)`
  in `Lset lam` whenever `sucV δ ∈ lam`. Meter: `0 UNRESOLVED of 5`
  on the nested names (`runs/meter-consumer.out:6`).
- **GO, unasked, on the consumer.** `At.from-iter`
  (`Probe668.agda:169-173`) delivers the brief's type from `PowIter`.
  It is `Bound.Iter.pow∈λ` at `D = 𝒟ₒ`. W2.

The probe is green and carries no hole (`runs/p-final.out:4`,
`EXIT=0` at `runs/p-final.out:23`). Three forced rechecks,
`runs/recheck-1.out` through `recheck-3.out`, each `EXIT=0`.
Two other delivered names at the probe module, `A∈𝒟ₒ` and
`dee-empty`, meter `0 UNRESOLVED of 2` (`runs/meter-names.out:3`).

**This is not a refutation of `powiter-status`.** I did not build a
term of its negation. The statement is true at the members I named.
A refutation would have been the brief's most valuable return. It
did not exist at `∅` or at a stage.

## THE PREDECESSOR QUESTION, ANSWERED BEFORE ANY AGDA

`[LJ-1.664]` delivered `PowIter` as a TYPE, not as a term
(`agents/tasks/LJ-1-664/Probe664.agda:134-136`). Its report is a stated
NO-GO on `DeeInHull` as a closed term, and a GO on the consumer
`dee-from-code` (`agents/tasks/LJ-1-664/lj-1.664-report.md:26-37`). The
verdict does not name `PowIter` FALSE
(`agents/tasks/LJ-1-664/review-of-dee-in-hull.md:15-18`). I take that
type. I do not inhabit a type the predecessor named FALSE.

The type at the limit is `Bound.Iter.pow∈λ`
(`src/L/Coding/Bound.lagda.md:109-110`):

    (y : S) → ⟨ y ∈ˢ Lset lam ⟩ → ⟨ 𝒟ₒ y ∈ˢ Lset lam ⟩

That is the brief's "limit stage is closed under `𝒟ₒ` at an arbitrary
member". I take it. The general-`δ` form `PowIter` stays the named
hypothesis that the consumer spends.

## D-10, BEFORE ANY AGDA

D-10 says to price the truth of the target before pricing its proof.

1. The target. The limit stage is closed under `𝒟ₒ` at an arbitrary
   member. Devlin asserts this and proves nothing.
   `[LJ-1.167]` quoted the scan
   (`agents/tasks/LJ-1-167/lj-1.167-report.md:170-172`): "if lim (α)
   and α > ω, the set Lα is closed under the function Def". His extra
   `α > ω` is a proof-route constraint. It is not a truth constraint.
2. The hypothesis the closed term would spend. `Describes`
   (`agents/tasks/LJ-1-169/ProbeLJ1169A.agda:80-82`) is unpaid.
   `PowIter` is unpaid (`src/L/Coding/Bound.lagda.md:147-152`). A
   `Formula Code 1` for `𝒟ₒ` is a second debt. The brief forbids
   funding it here.
3. The corrected target beside the original, as D-10 asks: the same
   type. It is true. The consumer `from-iter` is that type
   conditional on `PowIter`. I did not find a cardinality or Tarskian
   obstruction. Rank of `𝒟ₒ y` is at most the rank of `y` plus one,
   so a limit does not lose the value by rank.

## THE FLOOR, AND HOW IT WAS TAKEN

The standing clause asks for the frame to be priced before the proof.

- **The floor was priced first.** `runs/FLOOR.agda.txt`: the trimmed
  frame, the obligation in full, and a HOLE where the term goes. Its
  run is `runs/floor-1.out`: **exit 42 at 1.35 s, peak 270,811,136
  bytes**, with `[UnsolvedInteractionMetas]` at the one designed hole
  (`:5-7`) and no other error.
- **The trim is why the frame is cheap.** The statement names `Lset`,
  `IsOrd`, `𝒟ₒ`, `sucV` and `∅`, and nothing else, so the floor drops
  Bound, Formula, DefAt, Hull and CloseSyntax. Every later green run
  stayed inside 333 MB. No restructuring was needed and no heap wall
  was met.

**THE SLICE IS DELIVERED WITH A `.txt` SUFFIX, ON PURPOSE.** It is red
by design. `find agents/tasks/LJ-1-668 -name '*.agda'` returns
`Probe668.agda` and nothing else.

## W3, THE CODE MAP, AND WHAT THE UNION REACHES

The brief names W3 as "whether the limit stage's own union reaches
`𝒟ₒ` of an arbitrary member" at 90 to 200 lines, basis `[LJ-1.664]`.

**THE UNION REACHES TWO CLASSES OF MEMBERS. IT DOES NOT REACH AN
ARBITRARY MEMBER.**

**Class 1, a stage.** `Lset δ ∈ Lset lam` whenever `δ ∈ lam`
(`lset∈limit`, `Probe668.agda:132-133`). `𝒟ₒ (Lset δ) ≡ Lset (sucV δ)`
by `Lset-suc` (`src/L/Axioms/Basic.lagda.md:196`), and that next
stage is a member of the limit whenever `sucV δ ∈ lam`
(`dee-stage∈limit`, `Probe668.agda:139-143`). These are the members
the tower itself applies `𝒟ₒ` to.

**Class 2, the empty set.** `𝒟ₒ ∅ ≡ sucV ∅` (`dee-empty`,
`Probe668.agda:85-86`). The empty set is a member of the limit
(`empty∈limit`, `Probe668.agda:147-148`). `𝒟ₒ ∅` is a member of the
limit (`dee-empty∈limit`, `Probe668.agda:153-158`).

**Arbitrary `y`.** The only introduction into `𝒟ₒ` is `𝒟ₒ-intro`
(`src/L/Constructible.lagda.md:301-304`). To place `𝒟ₒ y` in a
successor stage one must exhibit `Describes`. Nothing in `src/`
supplies it. `[LJ-1.169]` named that gap and this task re-measured
that it is still unpaid.

Line count: 186 total, 90 non-blank non-comment (`Probe668.agda`).
The brief estimated 90 to 200. This file did not inhabit the
arbitrary case. It measured why two named members do not refute it.

## WHAT WAS BUILT

All in `agents/tasks/LJ-1-668/Probe668.agda`, module
`LJ-1-668.Probe668 {ℓ} (lem)`. The telescope `At` is Bound's own
(`src/L/Coding/Bound.lagda.md:130-132`).

**Top level.**

- `A∈𝒟ₒ` (`:79-80`). `(A : S) → ⟨ A ∈ˢ 𝒟ₒ A ⟩`.
- `dee-empty` (`:85-86`). `𝒟ₒ ∅ ≡ sucV ∅`.

**Module `At`.**

- `lset∈limit` (`:132-133`).
- `dee-stage∈limit` (`:139-143`).
- `empty∈limit` (`:147-148`).
- `dee-empty∈limit` (`:153-158`).
- `PowIter` (`:162-164`). Verbatim
  `src/L/Coding/Bound.lagda.md:151-152`, named, not inhabited.
- `from-iter` (`:169-173`). The consumer. W2.
- `powiter-status` (`:181-182`). The brief's type, as a type, not
  lifted to the probe module. The witness reads
  `Target.powiter-status` at the probe module
  (`scripts/pod/witness.py:278`) and does not find it.

## W2 (DD4)

The mathematics is written once at a generic operator and
instantiated. `Bound.Iter.pow∈λ` is the tree's term, generic in `D`
(`src/L/Coding/Bound.lagda.md:105-116`). This file imports `Bound`
and supplies `D = 𝒟ₒ` through `B.PowIter`. No line of that proof is
rewritten. The deadline conflict the clause names did not arise:
generic was cheaper than a second copy.

`A∈𝒟ₒ` and `dee-empty` are not instances of that term. They are
measurements of two members the frame admits.

## W4 (DD13)

Nothing was retired. No module moved to `archive/`. No dead fragment
was deleted. `dev/ARCHIVE.md` gains no row from this task.

## C-42

No refutation was produced, so the sweep this law demands does not
fire. I did not count live `src/` occurrences of a false shape,
because no false shape was proved.

## RUNS

Caliber `-A64m -I0 -M2g`, set on the pane by the program and
untouched here. One Agda process at a time, from the worktree root.
The probe interface was deleted before every forced recheck
(`_build/2.8.0/agda/agents/tasks/LJ-1-668/Probe668.agdai`).

Build history, in order:

| run | contents | exit | wall s | peak RSS bytes |
|---|---|---|---|---|
| `floor-1` | `FLOOR.agda.txt`, designed hole | 42 | 1.35 | 270,811,136 |
| `p-1` | first probe, `Empty.rec` not in scope | 42 | 2.19 | 330,366,976 |
| `p-2` | `Empty` imported, subst on `Lset-suc` ran the wrong way | 42 | 2.14 | 332,267,520 |
| `p-3` | subst direction fixed, first full green | 0 | 1.64 | 332,480,512 |

`p-1` is `[NotInScope]` for `Empty.rec`: `Base.Prelude` re-exports
only `⊥*` and `isProp⊥*` from `Cubical.Data.Empty`
(`src/Base/Prelude.lagda.md:220-221`). One `import Cubical.Data.Empty
as Empty` line. `p-2` is `[UnequalTerms]` `Lset (sucV δ) != 𝒟ₒ (Lset δ)`
at `dee-stage∈limit`: `Lset-suc δ` already has the direction
`Lset (sucV δ) ≡ 𝒟ₒ (Lset δ)`, and `sym` reversed it. No
restructuring, and no heap event at any point.

Three forced rechecks of the delivered file, probe interface removed
each time:

| run | exit | wall s | peak RSS bytes |
|---|---|---|---|
| `runs/recheck-1.out` | 0 | 1.67 | 332,480,512 |
| `runs/recheck-2.out` | 0 | 1.31 | 332,529,664 |
| `runs/recheck-3.out` | 0 | 1.29 | 332,496,896 |

Median wall **1.31 s**. Median peak RSS **332,496,896 bytes**. Exit 0
every time.

`runs/p-final.out` is the last check, the same bytes as
`recheck-3.out`: exit 0, 1.29 s, 332,496,896 bytes.

Meters, this worktree has no `.venv`, so they ran as
`/Users/alsg/Agentic/Bedrock/.venv/bin/python scripts/pod/witness.py`.
I did not add a dependency and I did not create a local `.venv`.

- Obligation: `1 UNRESOLVED of 1, 1.14 s, probe_red=False`
  (`runs/meter-obligation.out:2`).
- Top-level names: `0 UNRESOLVED of 2, 1.16 s, probe_red=False`
  (`runs/meter-names.out:3`).
- Nested consumer names: `0 UNRESOLVED of 5, 1.15 s, probe_red=False`
  (`runs/meter-consumer.out:6`).

Gates run while working: `scripts/gate/lint-agda.py --check` on
`Probe668.agda` exit 0, `scripts/gate/check-probes.py --check` clean,
10333 tracked files.

## WHAT THE NEXT BRIEF NEEDS

1. **DO NOT RE-DISPATCH `powiter-status` AS A CLOSED TERM.** It still
   owes a supplier. The consumer is paid (`from-iter`). The
   stage-member case is paid. The empty set is paid.
2. **THE BINDING DEBT IS `Describes`, AND IT IS A TOWER FACT.**
   `[LJ-1.169]` named it
   (`agents/tasks/LJ-1-169/ProbeLJ1169A.agda:80-82`). `PowIter` is
   that fact collected over a finite iterate, and `from-iter` is
   Bound's reduction of the limit-stage closure to it. Price a
   supplier for `Describes` at a stage that already holds `y`, not
   a hull search, and not a `Formula Code 1` unless a later brief
   funds that second debt on purpose.
3. **THE TARGET IS TRUE.** D-10. Devlin's `α > ω` is not a
   correction of the target. `∅` is MEASURED closed. A stage is
   MEASURED closed. A counterexample would have to be a
   non-stage member of small rank whose definable powerset is not
   a definable subset of any earlier stage. I did not find one.
4. **A `Formula Code 1` FOR `𝒟ₒ` STAYS A SECOND DEBT.** The brief
   forbade funding it. `[LJ-1.664]`'s census of `DefAt` at 166
   constants still stands.
5. **WHAT THE STATEMENT COST.** 90 non-blank non-comment lines,
   median 1.31 s, median peak 332,496,896 bytes, three red runs
   (floor, one import, one subst direction), no heap event. **WHAT
   THE SHAPE RESISTED.** The closed term at an arbitrary member.
   The shape that worked is Bound's consumer-from-`PowIter`, plus
   two named members. **WHAT I HAD TO WEAKEN.** The obligation, from
   a closed term to a term from `PowIter`, and to two special
   members. **WHAT I COULD NOT CLOSE.** `powiter-status`, `PowIter`,
   `Describes`, and a `Formula Code 1` for `𝒟ₒ`.

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
  obligation is on the live tower, not on the archived plan.
- `archive/dev/STATUS-archived.md`: read at `:1`. Quote:
  `# STATUS-archived: the goal table of the internalization route`
  Declined, not used. The internalization-route goal table is not
  the source for `powiter-status`.
- `archive/dev/TASKS-archived.md`: read at `:1`. Quote:
  `# Archived task index: the `L3.32-T` series`
  Declined, not used. The predecessors this task reads are live
  task homes under `agents/tasks/`.

## LITERATURE USED

- `dev/literature/level-formula-slot-roles.md`: **USED.** Read at
  `:79`. Quote:
  `Kunen defines the definable powerset as a SET (Definition VI 1.1, printed page`
  Also read at `:1`. Quote:
  `# The level-hood formula: arity, what it binds, what stays free`
  Kunen writes `𝒟` as a set, not as an object-level formula. That is
  why a `Formula Code 1` for `𝒟ₒ` is a second debt and not a
  substitute for the tower fact.
- `dev/literature/glossary-review-2026-08.md`: read at `:1`. Quote:
  `# Glossary review: the 119 pre-protocol entries`
  Declined, not used. No glossary term is at issue and I added no
  `dev/glossary.toml` entry.
- `dev/literature/devlin-errata.md`: read at `:1`. Quote:
  `# Devlin errata: documented error classes (do-not-repeat checklist)`
  Declined, not used. No Devlin erratum bears on limit-stage closure
  under `𝒟ₒ`. The Devlin sentence this task uses is the assertion
  `[LJ-1.167]` already quoted from the scan, not an erratum.
- `dev/literature/primary-sources.md`: read at `:1`. Quote:
  `# Primary sources, second round: Jensen manuscript, Devlin, Jech`
  Declined, not used. The slot-role note above is the source that
  decided the formula question. The Devlin closure sentence is in
  `[LJ-1.167]`'s report, cited to the scan.
- `dev/literature/BIBLIOGRAPHY.md`: read at `:1`. Quote:
  `# Bibliography for the rud route`
  Declined, not used. It is the index over the corpus. The specific
  note `level-formula-slot-roles.md` carries the fact this task
  used.

## WHAT I DID NOT DO

- I did not commit. I did not push.
- I did not set `GHCRTS`. I did not start a second Agda process.
- I did not write in `src/`.
- I did not inhabit `powiter-status` as a closed term.
- I did not inhabit `PowIter` or `Describes`.
- I did not fund a `Formula Code 1` for `𝒟ₒ`.
- I did not refute `powiter-status`.
- I did not postulate. I left no hole in `Probe668.agda`.
- I did not leave a red `.agda` under this task home: the one file
  that cannot typecheck is `runs/FLOOR.agda.txt`.
- I did not add a dependency and I did not create a local `.venv`.
- I did not re-attack `DeeInHull` or clause (iii)'s `Commute`.

## WORKING TREE, AS THIS REPORT DESCRIBES IT

Nothing committed, nothing pushed. No master edited. `src/` untouched.

New files, all in `agents/tasks/LJ-1-668/`:

- `Probe668.agda`, the search, green
- `lj-1.668-report.md`, this report
- `review-of-powiter-status.md`, the stated NO-GO
- `runs/`, the Agda transcripts and the one `.agda.txt` slice named
  above
