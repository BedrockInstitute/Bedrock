# LJ-1.674 report: does a stage describe the definable powerset of its members

## HEAD
slot: `coder`. Written early as a skeleton and filled as runs landed
(C-22). No commit, no push. I wrote only in `agents/tasks/LJ-1-674/`.
Agda ran under the caliber the program set on this pane,
`GHCRTS="-A64m -I0 -M2g"`, the wide caliber, ONE Agda process at a time.
I did not set `GHCRTS`. No heap event: the largest peak of any run is
282,886,144 bytes against the 2,147,483,648-byte cap.

TARGET: build ONE term in `agents/tasks/LJ-1-674/Probe674.agda`:

    describes-status : either `Describes σ y` at the stage and member
                       the tower reaches, or a refutation at a pair
                       the frame admits

Nothing lands in `src/`. `Describes` is `[LJ-1.169]`'s type
(`agents/tasks/LJ-1-169/ProbeLJ1169A.agda:80-82`).

The standing direction (`dev/pod/direction.md:37`) says one SRC
collection after LJ-1, not after `[LJ-2.5]`. This task is LJ-1 work.
It does not start that collection and it does not start phase 3. No
Boundary clause is in conflict.

## VERDICT

**GO.** `describes-status` is inhabited at the pair the tower reaches.

- **GO.** `describes-status` (`Probe674.agda:72-74`) has type
  `(δ : S) → Describes (sucV δ) (Lset δ)`. The formula is `⊤̇`. The
  witness meter reads `0 UNRESOLVED of 1, 0.98 s, probe_red=False`
  (`runs/meter-obligation.out:2`). The probe is green and carries no
  hole (`runs/p-final.out:4`, `EXIT=0` at `runs/p-final.out:23`).
  Three forced rechecks, `runs/recheck-1.out` through
  `recheck-3.out`, each `EXIT=0`.
- **GO, unasked, on the generic carrier.** `carve-self`
  (`Probe674.agda:66-68`) is `defSet⊤≡A` at an arbitrary `A`. Meter
  of the three top-level names: `0 UNRESOLVED of 3, 0.95 s,
  probe_red=False` (`runs/meter-names.out:4`).

**This is not a refutation of `Describes`.** I did not build a term of
its negation. The pair `(sucV δ, Lset δ)` is the pair `Lset-suc`
names (`src/L/Axioms/Basic.lagda.md:196`). A refutation would have
been the brief's most valuable return. It does not exist at that pair.

**This does not inhabit `Describes` at an arbitrary member.** The
tautology carves the whole stage. It pays the pair where `𝒟ₒ y` is
the stage, and nothing else.

## THE PREDECESSOR QUESTION, ANSWERED BEFORE ANY AGDA

`[LJ-1.169]` delivered `Describes` as a TYPE, not as a term
(`agents/tasks/LJ-1-169/ProbeLJ1169A.agda:80-82`). Its report names
`powIter` NOT false and INFERRED TRUE
(`agents/tasks/LJ-1-169/lj-1.169-report.md:21-23`). It does not name
`Describes` FALSE. I take that type.

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
   (`src/L/Definability.lagda.md:137`).
2. The pair the tower reaches. The tower applies `𝒟ₒ` to earlier
   stages: `Lset (sucV δ) ≡ 𝒟ₒ (Lset δ)`
   (`src/L/Axioms/Basic.lagda.md:196`). At `σ = sucV δ` and
   `y = Lset δ` the two sides of `Describes` are the same set, and
   `defSet⊤≡A` (`src/L/Definability.lagda.md:178`) carves the whole
   carrier. So the target is TRUE at that pair. No Tarskian or
   cardinality obstruction.
3. The corrected target beside the original, as D-10 asks: the same
   type, at the pair `(sucV δ, Lset δ)`. It is true. It is closed.
   The arbitrary-member form is a different target. I did not price
   its proof.

## THE FLOOR, AND HOW IT WAS TAKEN

The standing clause asks for the frame to be priced before the proof.

- **The floor was priced first.** `runs/FLOOR.agda.txt`: the trimmed
  frame, the obligation in full, and a HOLE where the term goes. Its
  run is `runs/floor-1.out`: **exit 42 at 1.26 s, peak 268,730,368
  bytes**, with `[UnsolvedInteractionMetas]` at the one designed hole
  (`runs/floor-1.out:5-7`) and no other error.
- **The trim is why the frame is cheap.** The statement names `Lset`,
  `𝒟ₒ`, `sucV`, `Formula` and `DefOf.defSet`, and nothing else, so
  the floor drops Bound, Hull, CloseSyntax, StageArith, LEM and a
  `Formula Code 1`. Every later green run stayed inside 283 MB. No
  restructuring was needed and no heap wall was met.

**THE SLICE IS DELIVERED WITH A `.txt` SUFFIX, ON PURPOSE.** It is red
by design. `find agents/tasks/LJ-1-674 -name '*.agda'` returns
`Probe674.agda` and nothing else.

## W3, THE CODE MAP, AND WHAT THE TAUTOLOGY REACHES

The brief names W3 as "whether one formula over `⟪ Lset σ ⟫` can
carve `𝒟ₒ y` for a member `y`" at 100 to 220 lines, basis
`[LJ-1.668]`.

**THE TAUTOLOGY REACHES THE PAIR THE TOWER FEEDS TO `𝒟ₒ`. IT DOES
NOT REACH AN ARBITRARY MEMBER.**

The pair is `σ = sucV δ` and `y = Lset δ`. `Lset-suc`
(`src/L/Axioms/Basic.lagda.md:196`) identifies `Lset (sucV δ)` with
`𝒟ₒ (Lset δ)`. `carve-self` at `Lset (sucV δ)` identifies
`defSet ⊤̇` with that stage. Those two identities inhabit
`Describes (sucV δ) (Lset δ)` (`Probe674.agda:72-74`).

**Arbitrary `y`.** The tautology carves the whole of `Lset σ`. It
equals `𝒟ₒ y` only when `𝒟ₒ y` is that whole stage. That is the
stage-member case, and not a general member of `Lset σ`. Nothing in
`src/` supplies a formula that carves `𝒟ₒ y` from a strictly larger
stage. A `Formula Code 1` for `𝒟ₒ` stays a second debt.

Line count: 74 total, 28 non-blank non-comment (`Probe674.agda`).
The brief estimated 100 to 220. The estimate assumed a real formula.
The tower pair did not need one.

## WHAT WAS BUILT

All in `agents/tasks/LJ-1-674/Probe674.agda`, module
`LJ-1-674.Probe674 {ℓ}`. No LEM. No nested telescope.

- `Describes` (`:60-62`). Verbatim
  `agents/tasks/LJ-1-169/ProbeLJ1169A.agda:80-82`.
- `carve-self` (`:66-68`). `defSet⊤≡A` at a generic carrier. W2.
- `describes-status` (`:72-74`). The obligation. One `PT.map` off
  `carve-self` and `Lset-suc`.

## W2 (DD4)

The mathematics is written once at a generic carrier and
instantiated. `carve-self` is `defSet⊤≡A`
(`src/L/Definability.lagda.md:178`) at an arbitrary `A`.
`describes-status` instantiates it at `Lset (sucV δ)` and composes
with `Lset-suc`. No line of `defSet⊤≡A` is rewritten. The deadline
conflict the clause names did not arise: generic was cheaper than a
second copy.

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
(`_build/2.8.0/agda/agents/tasks/LJ-1-674/Probe674.agdai`).

Build history, in order:

| run | contents | exit | wall s | peak RSS bytes |
|---|---|---|---|---|
| `floor-1` | `FLOOR.agda.txt`, designed hole | 42 | 1.26 | 268,730,368 |
| `p-1` | first probe, full term | 0 | 1.02 | 282,853,376 |

No red run after the floor. No import miss. No subst to reverse.

Three forced rechecks of the delivered file, probe interface removed
each time:

| run | exit | wall s | peak RSS bytes |
|---|---|---|---|
| `runs/recheck-1.out` | 0 | 1.02 | 282,853,376 |
| `runs/recheck-2.out` | 0 | 0.94 | 282,886,144 |
| `runs/recheck-3.out` | 0 | 0.93 | 282,820,608 |

Median wall **0.94 s**. Median peak RSS **282,853,376 bytes**. Exit 0
every time.

`runs/p-final.out` is a copy of `recheck-3.out`: exit 0, 0.93 s,
282,820,608 bytes.

Meters, this worktree has no `.venv`, so they ran as
`/Users/alsg/Agentic/Bedrock/.venv/bin/python scripts/pod/witness.py`.
I did not add a dependency and I did not create a local `.venv`.

- Obligation: `0 UNRESOLVED of 1, 0.98 s, probe_red=False`
  (`runs/meter-obligation.out:2`).
- Top-level names: `0 UNRESOLVED of 3, 0.95 s, probe_red=False`
  (`runs/meter-names.out:4`).

Gates run while working: `scripts/gate/lint-agda.py --check` on
`Probe674.agda` exit 0, `scripts/gate/check-probes.py --check` clean,
10403 tracked files. `scripts/gate/lint-prose.py --check` on this
report exit 0.

## WHAT THE NEXT BRIEF NEEDS

1. **DO NOT RE-DISPATCH `Describes` AT `(sucV δ, Lset δ)`.** It is
   paid (`describes-status`, `Probe674.agda:72-74`). The generic
   tautology is paid (`carve-self`, `:66-68`).
2. **THE REMAINING DEBT IS `Describes σ y` AT A NON-STAGE MEMBER.**
   The tautology carves the whole of `Lset σ`. A member `y` of
   `Lset σ` whose `𝒟ₒ y` is a proper subset of the stage still owes
   a formula. That is the supplier `[LJ-1.668]` asked for at a stage
   that already holds `y`, once `y` is not itself a stage
   (`agents/tasks/LJ-1-668/lj-1.668-report.md:255-262`).
3. **A `Formula Code 1` FOR `𝒟ₒ` STAYS A SECOND DEBT.** This task
   did not fund it. `[LJ-1.664]`'s census of `DefAt` at 166
   constants still stands.
4. **`PowIter` AT AN ARBITRARY MEMBER STAYS UNPAID.** This task pays
   the description at stage members. `[LJ-1.668]` already paid
   membership at stage members and at `∅`. The consumer `from-iter`
   still waits on a supplier for the rest.
5. **WHAT THE STATEMENT COST.** 28 non-blank non-comment lines,
   median 0.94 s, median peak 282,853,376 bytes, one red run (the
   floor), no heap event. **WHAT THE SHAPE RESISTED.** Nothing at
   this pair. The two identities fitted. **WHAT I HAD TO WEAKEN.**
   Nothing of the named obligation. I did not inhabit the
   arbitrary-member form, which the brief did not name as this
   term. **WHAT I COULD NOT CLOSE.** `Describes` at a non-stage
   member, `PowIter` at an arbitrary member, and a `Formula Code 1`
   for `𝒟ₒ`.

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
  the source for `describes-status`.
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
  `Formula Code 1` for `𝒟ₒ` is a second debt. At the tower pair the
  set-identity is `Lset-suc`, so the tautology closes it.
- `dev/literature/glossary-review-2026-08.md`: read at `:1`. Quote:
  `# Glossary review: the 119 pre-protocol entries`
  Declined, not used. No glossary term is at issue and I added no
  `dev/glossary.toml` entry.
- `dev/literature/devlin-errata.md`: read at `:1`. Quote:
  `# Devlin errata: documented error classes (do-not-repeat checklist)`
  Declined, not used. No Devlin erratum bears on `defSet⊤≡A` or on
  `Lset-suc`.
- `dev/literature/primary-sources.md`: read at `:1`. Quote:
  `# Primary sources, second round: Jensen manuscript, Devlin, Jech`
  Declined, not used. The slot-role note above is the source that
  decided the formula question. The two identities this term spends
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
- I did not inhabit `Describes` at an arbitrary member.
- I did not inhabit `PowIter`.
- I did not fund a `Formula Code 1` for `𝒟ₒ`.
- I did not refute `Describes`.
- I did not postulate. I left no hole in `Probe674.agda`.
- I did not leave a red `.agda` under this task home: the one file
  that cannot typecheck is `runs/FLOOR.agda.txt`.
- I did not add a dependency and I did not create a local `.venv`.
- I did not re-attack `powiter-status` or `DeeInHull`.
- I did not write `review-of-describes-status.md`. The obligation
  resolved. That file is the critic's input on a NO-GO, and this
  return is a GO.

## WORKING TREE, AS THIS REPORT DESCRIBES IT

Nothing committed, nothing pushed. No master edited. `src/` untouched.

New files, all in `agents/tasks/LJ-1-674/`:

- `Probe674.agda`, the search, green
- `lj-1.674-report.md`, this report
- `runs/`, the Agda transcripts and the one `.agda.txt` slice named
  above
