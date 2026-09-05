# LJ-1.683 report: describes, at a generic non-stage member

## HEAD
slot: `coder`. Written early as a skeleton and filled as runs landed
(C-22). No commit, no push. I wrote only in `agents/tasks/LJ-1-683/`.
Agda ran under the caliber the program set on this pane,
`GHCRTS="-A64m -I0 -M2g"`, the wide caliber, ONE Agda process at a time.
I did not set `GHCRTS`. No heap event: the largest peak of any run is
285,327,360 bytes against the 2,147,483,648-byte cap.

TARGET: build ONE term in `agents/tasks/LJ-1-683/Probe683.agda`:

    describes-generic : `Describes σ y` for a GENERIC non-stage
                        member `y` of `Lset σ`, not at one named pair

Nothing lands in `src/`. Do not re-dispatch `Describes` at
`(sucV δ, Lset δ)`. `[LJ-1.674]` paid it
(`agents/tasks/LJ-1-674/Probe674.agda:72-74`). Do not re-dispatch
`Describes` at `(σ₃, ⁅ sucV ∅ ⁆s)` or the generic singleton
`describes-sgl`. `[LJ-1.677]` paid both
(`agents/tasks/LJ-1-677/Probe677.agda:159-164` and `:203-204`).

The standing direction (`dev/pod/direction.md:37`) says one SRC
collection after LJ-1, not after `[LJ-2.5]`. This task is LJ-1 work.
It does not start that collection and it does not start phase 3. No
Boundary clause is in conflict.

## VERDICT

**NO-GO on the closed term. GO on the generic formula, and GO on
the consumer.**

- **NO-GO.** `describes-generic` is not inhabited as a closed term.
  The witness meter reads `1 UNRESOLVED of 1, 0.89 s, probe_red=False`
  (`runs/meter-obligation.out:2`). The stated NO-GO is
  `agents/tasks/LJ-1-683/review-of-describes-generic.md`. That file is
  the critic's input and it does not close the task.
- **GO, unasked, on the generic formula.** `subsetFo`
  (`Probe683.agda:71-72`) is `∀̇∈ (var zero) (var zero ∈̇ con m_y)`
  over `⟪ Lset σ ⟫`. It is the formula "x ⊆ y" at a generic member
  of a generic stage. W2.
- **GO, unasked, on the consumer.** `from-hyps`
  (`Probe683.agda:147-150`) delivers `Describes σ y` from
  `Dee⊆stage` and `StagePowDef`. Meter of the five top-level names:
  `0 UNRESOLVED of 5, 0.90 s, probe_red=False`
  (`runs/meter-names.out:6`).

The probe is green and carries no hole (`runs/p-final.out:4`,
`EXIT=0` at `runs/p-final.out:23`). Three forced rechecks,
`runs/recheck-1.out` through `recheck-3.out`, each `EXIT=0`.

**This is not a refutation of `describes-generic`.** I did not build
a term of its negation. The statement is true at every pair the
predecessors named. A refutation would have been the brief's most
valuable return. It does not exist at a pair I named.

**This does not inhabit `Describes` at an arbitrary member.** The
subset formula carves the members of the stage that are subsets of
`y`. That equals `𝒟ₒ y` only under the two hypotheses. The brief's
GO-earns line ("completes `Describes`, then `PowIter`") is stronger
than this term. See WHAT THE NEXT BRIEF NEEDS.

## THE PREDECESSOR QUESTION, ANSWERED BEFORE ANY AGDA

`[LJ-1.169]` delivered `Describes` as a TYPE, not as a term
(`agents/tasks/LJ-1-169/ProbeLJ1169A.agda:80-82`). Its report names
`powIter` NOT false and INFERRED TRUE
(`agents/tasks/LJ-1-169/lj-1.169-report.md:21-23`). It does not name
`Describes` FALSE. I take that type.

`[LJ-1.674]` inhabited `describes-status` at `(sucV δ, Lset δ)`
(`agents/tasks/LJ-1-674/Probe674.agda:72-74`). Verdict GO
(`agents/tasks/LJ-1-674/lj-1.674-report.md:27`). It does not name
`Describes` FALSE. I take the type. I do not re-inhabit the pair
that predecessor paid.

`[LJ-1.677]` inhabited `describes-nonstage` at ONE pair
`(σ₃, ⁅ sucV ∅ ⁆s)` (`agents/tasks/LJ-1-677/Probe677.agda:203-204`)
and, unasked, the generic singleton `describes-sgl` (`:159-164`).
Verdict GO at that pair
(`agents/tasks/LJ-1-677/lj-1.677-report.md:29`). It names the
remaining debt as `Describes` at a non-singleton non-stage member
(`:281-284`). It does not name `Describes` FALSE. I take the type.
I do not re-inhabit the named pair. I do not re-inhabit
`describes-sgl`.

`[LJ-1.668]` named `Describes` as the binding debt behind `PowIter`
(`agents/tasks/LJ-1-668/lj-1.668-report.md:255-262`). Its verdict is
a stated NO-GO on `powiter-status` as a closed term, and a GO on two
members and on the consumer
(`agents/tasks/LJ-1-668/lj-1.668-report.md:30-37`). The verdict does
not name `Describes` FALSE
(`agents/tasks/LJ-1-668/review-of-powiter-status.md:16-20`). I take
the type. I do not inhabit a type the predecessor named FALSE.

## D-10, BEFORE ANY AGDA

D-10 says to price the truth of the target before pricing its proof.

1. The target. `Describes σ y` asks for one formula over
   `⟪ Lset σ ⟫` whose `defSet` equals `𝒟ₒ y`
   (`agents/tasks/LJ-1-169/ProbeLJ1169A.agda:80-82`). A necessary
   condition is `𝒟ₒ y ⊆ Lset σ`, because `defSet⊆A`
   (`src/L/Definability.lagda.md:137`). The brief asks for a generic
   member `y` of `Lset σ`, not a named pair.
2. What the pairing formula reaches. `[LJ-1.677]` measured that
   `pair∈𝒟ₒ` carves `{∅, y}`, and that this equals `𝒟ₒ y` only when
   `y` is a singleton (`agents/tasks/LJ-1-677/lj-1.677-report.md:150-166`).
   A two-element `y` has four subsets. The extra two are not a
   pairing identity.
3. What the tautology reaches. `[LJ-1.674]` measured that `⊤̇`
   carves the whole stage, and that this equals `𝒟ₒ y` only at
   `(sucV δ, Lset δ)` (`agents/tasks/LJ-1-674/lj-1.674-report.md:113-126`).
4. The generic formula that remains. "x ⊆ y", with `y` a constant
   from the stage. It does not list members. It is LEM-free. Its
   `defSet` is the members of `Lset σ` that are subsets of `y`. That
   equals `𝒟ₒ y` if and only if `Dee⊆stage` and `StagePowDef` hold.
   No Tarskian or cardinality obstruction at the type. The
   obstruction is a missing supplier for those two hypotheses.
5. The corrected target beside the original, as D-10 asks: the
   same type. It is not closed. The consumer `from-hyps` is that
   type conditional on the two hypotheses. The arbitrary-member
   closed form, and a `Formula Code 1` for `𝒟ₒ`, are different
   targets. I did not price their proofs.

## THE FLOOR, AND HOW IT WAS TAKEN

The standing clause asks for the frame to be priced before the proof.

- **The floor was priced first.** `runs/FLOOR.agda.txt`: the trimmed
  frame, the obligation in full, and a HOLE where the term goes. Its
  run is `runs/floor-1.out`: **exit 42 at 1.16 s, peak 269,844,480
  bytes**, with `[UnsolvedInteractionMetas]` at the one designed hole
  (`runs/floor-1.out:5-7`) and no other error.
- **The trim is why the frame is cheap.** The statement names `Lset`,
  `𝒟ₒ`, `Formula`, `DefOf.defSet`, `Describes` and membership in a
  stage, and nothing else, so the floor drops Bound, Hull,
  CloseSyntax, StageArith, LEM, `sucV` and a `Formula Code 1`. P-l
  did not bite: the type names no transparent `sucV`. Every later
  green run stayed inside 286 MB. No restructuring was needed and
  no heap wall was met.

**THE SLICE IS DELIVERED WITH A `.txt` SUFFIX, ON PURPOSE.** It is red
by design. `find agents/tasks/LJ-1-683 -name '*.agda'` returns
`Probe683.agda` and nothing else.

## W3, THE CODE MAP, AND WHAT THE SUBSET FORMULA REACHES

The brief names W3 as "the formula at a generic non-stage `y`" at
130 to 280 lines, basis `[LJ-1.677]`.

**THE SUBSET FORMULA REACHES THE MEMBERS OF THE STAGE THAT ARE
SUBSETS OF `y`. IT DOES NOT REACH `𝒟ₒ y` AT A GENERIC MEMBER.**

The formula is `subsetFo` (`Probe683.agda:71-72`):
`∀̇∈ (var zero) (var zero ∈̇ con m_y)`. `Carve.sat→⊆` and
`Carve.⊆→sat` (`:99-130`) identify inner satisfaction of that
formula with host `⊆`. `from-hyps` (`:147-167`) rewrites the
carved set to `𝒟ₒ y` from `Dee⊆stage` and `StagePowDef`.

**Arbitrary `y`.** The pairing formula is paid and too small. The
tautology is paid and too big. The subset formula is the remaining
object-language shape that mentions `y` as a constant and does not
list `y`'s members. Equality with `𝒟ₒ y` still owes the two
hypotheses. Nothing in `src/` supplies them at a generic member. A
`Formula Code 1` for `𝒟ₒ` stays a second debt.

Line count: 181 total, 105 non-blank non-comment (`Probe683.agda`).
The brief estimated 130 to 280. The estimate assumed a formula that
equals `𝒟ₒ y`. This file wrote the subset formula and did not
inhabit the equality at a generic member.

## WHAT WAS BUILT

All in `agents/tasks/LJ-1-683/Probe683.agda`, module
`LJ-1-683.Probe683 {ℓ}`. No LEM. No nested telescope at the
obligation.

- `Describes` (`:66-68`). Verbatim
  `agents/tasks/LJ-1-169/ProbeLJ1169A.agda:80-82`.
- `subsetFo` (`:71-72`). The subset formula at a generic carrier.
  W2.
- `Dee⊆stage` (`:75-76`). Named, not inhabited.
- `StagePowDef` (`:79-81`). Named, not inhabited.
- `module Carve` (`:85-143`). Inner satisfaction of `subsetFo`
  against host `⊆`, both ways.
- `from-hyps` (`:147-167`). The consumer. W2.
- `module At` (`:175-177`). `describes-generic` as a type, not
  lifted to the probe module. The witness reads
  `Target.describes-generic` at the probe module
  (`scripts/pod/witness.py:278`) and does not find it.

## W2 (DD4)

The mathematics is written once at a generic carrier and
instantiated. `subsetFo` is "x ⊆ y" at an arbitrary stage `σ` and
an arbitrary member `y`. `from-hyps` consumes that one formula. No
line of `pair∈𝒟ₒ` is rewritten. No line of `defSet⊤≡A` is
rewritten. The deadline conflict the clause names did not arise:
generic was cheaper than a second copy of either paid special case.

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
(`_build/2.8.0/agda/agents/tasks/LJ-1-683/Probe683.agdai`).

Build history, in order:

| run | contents | exit | wall s | peak RSS bytes |
|---|---|---|---|---|
| `floor-1` | `FLOOR.agda.txt`, designed hole | 42 | 1.16 | 269,844,480 |
| `p-1` | first probe, `sat` applied at the wrong sort | 42 | 1.30 | 275,316,736 |
| `p-2` | inner `_∈ˢ_` qualified as `DefC.∈ˢ` | 42 | 1.24 | 272,613,376 |
| `p-3` | `∈∈ₛ .snd` on a value that was already `∈ˢ` | 42 | 1.50 | 248,807,424 |
| `p-4` | membership directions fixed, first full green | 0 | 1.11 | 285,294,592 |

`p-1` is `[UnequalTerms]` at `sat→⊆`: `sat` takes an inner-structure
member, and the first draft passed a host set (`runs/p-1.out:5-26`).
`p-2` is `[NotInScope]` for `DefC.∈ˢ`: InnerSmall does not re-export
`_∈ˢ_` under that qualifier (`runs/p-2.out:5-14`). The inner
membership is ambient `_∈ˢ_` on first projections, by `_↾_`
(`src/FOL/ZFStructure.lagda.md:145-149`). `p-3` is `[UnequalTerms]`
`∈ˢ != ∈ₛ` at `mem→subseteq` (`runs/p-3.out:5-16`): `∈∈ₛ .snd`
expects `∈ₛ`, and `x∈` was already `∈ˢ`, which for a `sett` is the
truncated fibre `PT.rec` consumes. No restructuring, and no heap
event at any point.

Three forced rechecks of the delivered file, probe interface removed
each time:

| run | exit | wall s | peak RSS bytes |
|---|---|---|---|
| `runs/recheck-1.out` | 0 | 1.08 | 285,294,592 |
| `runs/recheck-2.out` | 0 | 1.07 | 285,327,360 |
| `runs/recheck-3.out` | 0 | 0.96 | 285,245,440 |

Median wall **1.07 s**. Median peak RSS **285,294,592 bytes**. Exit 0
every time.

`runs/p-final.out` is a copy of `recheck-3.out`: exit 0, 0.96 s,
285,245,440 bytes.

Meters, this worktree has no `.venv`, so they ran as
`/Users/alsg/Agentic/Bedrock/.venv/bin/python scripts/pod/witness.py`.
I did not add a dependency and I did not create a local `.venv`.

- Obligation: `1 UNRESOLVED of 1, 0.89 s, probe_red=False`
  (`runs/meter-obligation.out:2`).
- Top-level names: `0 UNRESOLVED of 5, 0.90 s, probe_red=False`
  (`runs/meter-names.out:6`).

Gates run while working: `scripts/gate/lint-agda.py --check` on
`Probe683.agda` exit 0, `scripts/gate/check-probes.py --check` clean,
10568 tracked files. `scripts/gate/lint-prose.py --check` on this
report and on `review-of-describes-generic.md` exit 0.

## WHAT THE NEXT BRIEF NEEDS

1. **DO NOT RE-DISPATCH `Describes` AT `(sucV δ, Lset δ)`.** It
   remains paid by `[LJ-1.674]`
   (`agents/tasks/LJ-1-674/Probe674.agda:72-74`).
2. **DO NOT RE-DISPATCH `Describes` AT `(σ₃, ⁅ sucV ∅ ⁆s)`.** It
   remains paid by `[LJ-1.677]`
   (`agents/tasks/LJ-1-677/Probe677.agda:203-204`). The generic
   singleton identity remains paid (`dee-singleton`, `:107-108`).
   The generic singleton supplier remains paid (`describes-sgl`,
   `:159-164`).
3. **DO NOT RE-DISPATCH `describes-generic` AS A CLOSED TERM.** It
   still owes a supplier. The consumer is paid (`from-hyps`). The
   subset formula is paid (`subsetFo`).
4. **THIS NO-GO DOES NOT COMPLETE `Describes`, AND IT DOES NOT
   COMPLETE `PowIter`.** The brief's GO-earns line is too strong.
   What is paid is the generic formula "x ⊆ y" and the consumer
   from two hypotheses. `PowIter` is `Describes` collected over a
   finite iterate
   (`agents/tasks/LJ-1-169/ProbeLJ1169A.agda:91-96`). The consumer
   `from-iter` still waits on a supplier for the rest
   (`agents/tasks/LJ-1-668/lj-1.668-report.md:255-262`).
5. **THE REMAINING DEBT IS `StagePowDef` AND `Dee⊆stage` AT A
   GENERIC MEMBER, OR A `Formula Code 1` FOR `𝒟ₒ`.** `StagePowDef`
   says every subset of `y` that sits in the stage is definable
   over `y`. That holds for a finite `y` under LEM by listing
   elements, which is the shape `[LJ-1.677]` paid at a singleton
   and which does not list a generic `y`. `Dee⊆stage` says
   `𝒟ₒ y ⊆ Lset σ`. It is necessary by `defSet⊆A`. I did not
   inhabit either at a generic member.
6. **A `Formula Code 1` FOR `𝒟ₒ` STAYS A SECOND DEBT.** This task
   did not fund it. `[LJ-1.664]`'s census of `DefAt` at 166
   constants still stands.
7. **WHAT THE STATEMENT COST.** 105 non-blank non-comment lines,
   median 1.07 s, median peak 285,294,592 bytes, four red runs (the
   floor, three membership mismatches), no heap event. **WHAT THE
   SHAPE RESISTED.** The closed term at an arbitrary member. The
   shape that worked is the subset formula plus the consumer from
   two hypotheses. **WHAT I HAD TO WEAKEN.** The obligation, from a
   closed term to a term from `Dee⊆stage` and `StagePowDef`. **WHAT
   I COULD NOT CLOSE.** `describes-generic`, `StagePowDef` at a
   generic member, `Dee⊆stage` at a generic member, `PowIter` at an
   arbitrary member, and a `Formula Code 1` for `𝒟ₒ`.

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
  the source for `describes-generic`.
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
  why `Describes` is a set-identity against `defSet`, and why a
  `Formula Code 1` for `𝒟ₒ` is a second debt. At a generic member
  the set-identity is not `Lset-suc` and is not `dee-singleton`, so
  the subset formula is the remaining object-language shape.
- `dev/literature/glossary-review-2026-08.md`: read at `:1`. Quote:
  `# Glossary review: the 119 pre-protocol entries`
  Declined, not used. No glossary term is at issue and I added no
  `dev/glossary.toml` entry.
- `dev/literature/devlin-errata.md`: read at `:1`. Quote:
  `# Devlin errata: documented error classes (do-not-repeat checklist)`
  Declined, not used. No Devlin erratum bears on `subsetFo` or on
  `from-hyps`.
- `dev/literature/primary-sources.md`: read at `:1`. Quote:
  `# Primary sources, second round: Jensen manuscript, Devlin, Jech`
  Declined, not used. The slot-role note above is the source that
  decided the formula question. The identities the consumer spends
  are in the live tree.
- `dev/literature/BIBLIOGRAPHY.md`: read at `:1`. Quote:
  `# Bibliography for the rud route`
  Declined, not used. It is the index over the corpus. The specific
  note `level-formula-slot-roles.md` carries the fact this task
  used.

## WHAT I DID NOT DO

- I did not commit. I did not push.
- I did not set `GHCRTS`. I did not start a second Agda process.
- I did not write in `src/`.
- I did not inhabit `describes-generic` as a closed term.
- I did not inhabit `StagePowDef` or `Dee⊆stage` at a generic member.
- I did not inhabit `PowIter`.
- I did not fund a `Formula Code 1` for `𝒟ₒ`.
- I did not refute `Describes`.
- I did not re-inhabit `describes-status`, `describes-nonstage` or
  `describes-sgl`.
- I did not postulate. I left no hole in `Probe683.agda`.
- I did not leave a red `.agda` under this task home: the one file
  that cannot typecheck is `runs/FLOOR.agda.txt`.
- I did not add a dependency and I did not create a local `.venv`.
- I did not re-attack `powiter-status` or `DeeInHull`.

## WORKING TREE, AS THIS REPORT DESCRIBES IT

Nothing committed, nothing pushed. No master edited. `src/` untouched.

New files, all in `agents/tasks/LJ-1-683/`:

- `Probe683.agda`, the search, green
- `lj-1.683-report.md`, this report
- `review-of-describes-generic.md`, the stated NO-GO
- `runs/`, the Agda transcripts and the one `.agda.txt` slice named
  above
