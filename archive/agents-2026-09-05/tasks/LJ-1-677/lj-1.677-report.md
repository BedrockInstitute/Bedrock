# LJ-1.677 report: describes, at a member that is not a stage

## HEAD
slot: `coder`. Written early as a skeleton and filled as runs landed
(C-22). No commit, no push. I wrote only in `agents/tasks/LJ-1-677/`.
Agda ran under the caliber the program set on this pane,
`GHCRTS="-A64m -I0 -M2g"`, the wide caliber, ONE Agda process at a time.
I did not set `GHCRTS`. No heap event: the largest peak of any run is
292,667,392 bytes against the 2,147,483,648-byte cap.

TARGET: build ONE term in `agents/tasks/LJ-1-677/Probe677.agda`:

    describes-nonstage : `Describes σ y` where `y` is a member of
                         `Lset σ` that is NOT itself a stage, so that
                         `𝒟ₒ y` is a proper subset of the stage

Nothing lands in `src/`. Do not re-dispatch `Describes` at
`(sucV δ, Lset δ)`. `[LJ-1.674]` paid it
(`agents/tasks/LJ-1-674/Probe674.agda:72-74`). The generic tautology
`carve-self` is paid too (`:66-68`).

The standing direction (`dev/pod/direction.md:37`) says one SRC
collection after LJ-1, not after `[LJ-2.5]`. This task is LJ-1 work.
It does not start that collection and it does not start phase 3. No
Boundary clause is in conflict.

## VERDICT

**GO.** `describes-nonstage` is inhabited at the first non-stage
member of `L`.

- **GO.** `describes-nonstage` (`Probe677.agda:203-204`) has type
  `Describes σ₃ y₀` with `σ₃ = sucV (sucV (sucV ∅))` and
  `y₀ = ⁅ sucV ∅ ⁆s`. The formula is `pair∈𝒟ₒ`'s disjunction of
  equalities. The witness meter reads `0 UNRESOLVED of 1, 1.51 s,
  probe_red=False` (`runs/meter-obligation.out:2`). The probe is
  green and carries no hole (`runs/p-final.out:4`, `EXIT=0` at
  `runs/p-final.out:23`). Three forced rechecks,
  `runs/recheck-1.out` through `recheck-3.out`, each `EXIT=0`.
- **GO, unasked, on the generic singleton.** `dee-singleton`
  (`Probe677.agda:107-108`) is `𝒟ₒ (⁅ a ⁆s) ≡ ⁅ ∅ , ⁅ a ⁆s ⁆`.
  `describes-sgl` (`:159-164`) is `Describes σ (⁅ a ⁆s)` from
  `∅ ∈ Lset σ` and `⁅ a ⁆s ∈ Lset σ`. Meter of the four top-level
  names: `0 UNRESOLVED of 4, 1.63 s, probe_red=False`
  (`runs/meter-names.out:5`).

**This is not a refutation of `Describes`.** I did not build a term
of its negation. The pair `(σ₃, ⁅ sucV ∅ ⁆s)` is a pair the frame
admits. A refutation would have been the brief's most valuable
return. It does not exist at that pair.

**This does not inhabit `Describes` at an arbitrary non-stage
member.** The pairing formula carves `{∅, y}` from a stage that
already holds both. That equals `𝒟ₒ y` when `y` is a singleton,
and nowhere else. The brief's GO-earns line ("completes
`Describes`, then `PowIter`") is stronger than this term. See
WHAT THE NEXT BRIEF NEEDS.

## THE PREDECESSOR QUESTION, ANSWERED BEFORE ANY AGDA

`[LJ-1.169]` delivered `Describes` as a TYPE, not as a term
(`agents/tasks/LJ-1-169/ProbeLJ1169A.agda:80-82`). Its report names
`powIter` NOT false and INFERRED TRUE
(`agents/tasks/LJ-1-169/lj-1.169-report.md:21-23`). It does not name
`Describes` FALSE. I take that type.

`[LJ-1.674]` inhabited `describes-status` at `(sucV δ, Lset δ)`
(`agents/tasks/LJ-1-674/Probe674.agda:72-74`). Verdict GO
(`agents/tasks/LJ-1-674/lj-1.674-report.md:27`). It does not name
`Describes` FALSE. It names this non-stage case as the remaining
debt (`:214-219`). I take the type. I do not re-inhabit the pair
that predecessor paid.

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
   (`src/L/Definability.lagda.md:137`). The brief asks for a member
   `y` that is not a stage, so that `𝒟ₒ y` is a proper subset of
   `Lset σ`.
2. The first non-stage. `y = ⁅ sucV ∅ ⁆s` is `{{∅}}`. Stages are
   transitive (`layer-trans`, `src/L/Constructible.lagda.md:183`).
   `{{∅}}` is not: `{∅} ∈ {{∅}}` and `∅ ∈ {∅}` but `∅ ∉ {{∅}}`.
   It first appears as a definable subset of `L₂ = {∅, {∅}}`, so
   as a member of `L₃ = Lset (sucV (sucV (sucV ∅)))`. The
   membership is inhabited (`y₀∈σ₃`, `Probe677.agda:196-199`).
3. What `𝒟ₒ y` is, classically. `y` is a singleton, so its subsets
   are `∅` and `y`, both definable (`⊥̇` and `⊤̇`). So
   `𝒟ₒ y ≡ ⁅ ∅ , y ⁆` (`dee-singleton`, `Probe677.agda:107-108`).
   Both members already sit in `L₃` (`∅∈σ₃` `:191-194`, `y₀∈σ₃`
   `:196-199`), and the pairing formula of `pair∈𝒟ₒ`
   (`src/L/Axioms/Basic.lagda.md:547-549`) carves that pair from
   `L₃`. That is `Describes` at `σ₃` and `y`. `{∅, y}` has two
   members of a four-member stage, so it is a proper subset. I did
   not inhabit a term of the inequality.
4. Constructive caveat. Identifying `𝒟ₒ (⁅ a ⁆s)` with
   `⁅ ∅ , ⁅ a ⁆s ⁆` decides, for an arbitrary member of `𝒟ₒ`,
   whether `a` belongs to it. That is an `hProp`. It needs `LEM`
   (`Probe677.agda:35`, used at `:111`). Without `LEM` I do not
   have a formula, and I do not have a refutation. The two chapters
   that assume `powIter` already sit in the classical cone
   (`src/L/Coding/Bound.lagda.md:10`). No Tarskian or cardinality
   obstruction at this pair.
5. The corrected target beside the original, as D-10 asks: the
   same type, at the pair `(σ₃, ⁅ sucV ∅ ⁆s)`, under `LEM`. It is
   true. It is closed. The arbitrary-member form, and the LEM-free
   form, are different targets. I did not price their proofs.

## THE FLOOR, AND HOW IT WAS TAKEN

The standing clause asks for the frame to be priced before the proof.

- **The floor was priced first.** `runs/FLOOR.agda.txt`: the trimmed
  frame, the obligation in full, and a HOLE where the term goes. Its
  run is `runs/floor-1.out`: **exit 42 at 1.97 s, peak 234,209,280
  bytes**, with `[UnsolvedInteractionMetas]` at the one designed hole
  (`runs/floor-1.out:5-7`) and no other error.
- **The trim is why the frame is cheap.** The statement names `Lset`,
  `𝒟ₒ`, `sucV`, `Formula`, `DefOf.defSet`, `Describes` and the
  singleton of `sucV ∅`, and nothing else, so the floor drops Bound,
  Hull, CloseSyntax, StageArith, LEM and a `Formula Code 1`. Every
  later green run stayed inside 293 MB. No restructuring was needed
  and no heap wall was met.
- **P-l did not bite.** The type names `sucV` three times as an
  index of opaque `Lset`. The floor at 1.97 s is the same order as
  `[LJ-1.674]`'s 1.26 s floor at one `sucV`.

**THE SLICE IS DELIVERED WITH A `.txt` SUFFIX, ON PURPOSE.** It is red
by design. `find agents/tasks/LJ-1-677 -name '*.agda'` returns
`Probe677.agda` and nothing else.

## W3, THE CODE MAP, AND WHAT THE PAIRING FORMULA REACHES

The brief names W3 as "one formula over `⟪ Lset σ ⟫` carving `𝒟ₒ y`
for a non-stage `y`" at 120 to 260 lines, basis `[LJ-1.674]`.

**THE PAIRING FORMULA REACHES A SINGLETON. IT DOES NOT REACH AN
ARBITRARY NON-STAGE MEMBER.**

The pair is `σ = sucV³ ∅` and `y = ⁅ sucV ∅ ⁆s`. `dee-singleton`
identifies `𝒟ₒ y` with `⁅ ∅ , y ⁆`. `pair∈𝒟ₒ` at that pair
(`src/L/Axioms/Basic.lagda.md:547-549`) supplies a formula over
`⟪ Lset σ₃ ⟫` whose `defSet` is the pair. Those two identities
inhabit `Describes σ₃ y₀` (`Probe677.agda:203-204`). The tautology
of `[LJ-1.674]` is not spent: `𝒟ₒ y` is a proper subset, not the
whole stage.

**Arbitrary non-stage `y`.** The pairing formula carves `{∅, y}`.
That equals `𝒟ₒ y` only when every definable subset of `y` is `∅`
or `y`, i.e. when `y` is a singleton. Nothing in `src/` supplies a
formula that carves `𝒟ₒ y` from a strictly larger stage at a
member with two or more elements. A `Formula Code 1` for `𝒟ₒ`
stays a second debt.

Line count: 204 total, 134 non-blank non-comment (`Probe677.agda`).
The brief estimated 120 to 260. The estimate assumed a real
formula. The pairing formula was already in the tree. The cost is
the singleton identity, which needs `LEM`.

## WHAT WAS BUILT

All in `agents/tasks/LJ-1-677/Probe677.agda`, module
`LJ-1-677.Probe677 {ℓ} (lem)`. No nested telescope. `LEM` is a
module parameter, used by `dee-singleton` only.

- `Describes` (`:70-72`). Verbatim
  `agents/tasks/LJ-1-169/ProbeLJ1169A.agda:80-82`.
- `empty∈dee` (`:86-87`). `defSet ⊥̇ ≡ ∅` at a generic carrier. W2.
- `A∈𝒟ₒ` (`:102-103`). Copied from
  `agents/tasks/LJ-1-668/Probe668.agda:79-80`.
- `dee-singleton` (`:107-108`). The singleton identity. W2. Needs
  `LEM`.
- `describes-sgl` (`:159-164`). `Describes` at a singleton, from
  `pair∈𝒟ₒ` and `dee-singleton`. W2. Does not rewrite `pair∈𝒟ₒ`.
- `sucV∅≡sgl` (`:167-168`). `sucV ∅ ≡ ⁅ ∅ ⁆s`.
- `y₀∈σ₃` (`:196-199`). The first non-stage is a member of `L₃`.
- `describes-nonstage` (`:203-204`). The obligation. One
  instantiation of `describes-sgl`.

## W2 (DD4)

The mathematics is written once at a generic singleton and
instantiated. `dee-singleton` is `𝒟ₒ (⁅ a ⁆s) ≡ ⁅ ∅ , ⁅ a ⁆s ⁆`
at an arbitrary `a`. `describes-sgl` is `Describes σ (⁅ a ⁆s)`
from `∅ ∈ Lset σ` and `⁅ a ⁆s ∈ Lset σ`, spending `pair∈𝒟ₒ`
(`src/L/Axioms/Basic.lagda.md:547-549`) and not rewriting it.
`describes-nonstage` instantiates at `a = sucV ∅` and
`σ = sucV³ ∅`. No line of `pair∈𝒟ₒ` is rewritten. The deadline
conflict the clause names did not arise: generic was cheaper than
a second copy.

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
(`_build/2.8.0/agda/agents/tasks/LJ-1-677/Probe677.agdai`).

Build history, in order:

| run | contents | exit | wall s | peak RSS bytes |
|---|---|---|---|---|
| `floor-1` | `FLOOR.agda.txt`, designed hole | 42 | 1.97 | 234,209,280 |
| `p-1` | first probe, `_⊎_` not in scope | 42 | 1.27 | 284,180,480 |
| `p-2` | `Cubical.Data.Sum._⊎_` imported, first full green | 0 | 1.21 | 292,618,240 |

`p-1` is `[NotInScope]` for `⊎`: the import named `inl` and `inr`
and not the type (`runs/p-1.out:5-10`). One name in the `using`
clause. No restructuring, and no heap event at any point.

Three forced rechecks of the delivered file, probe interface removed
each time:

| run | exit | wall s | peak RSS bytes |
|---|---|---|---|
| `runs/recheck-1.out` | 0 | 1.18 | 292,634,624 |
| `runs/recheck-2.out` | 0 | 1.16 | 292,667,392 |
| `runs/recheck-3.out` | 0 | 1.17 | 292,667,392 |

Median wall **1.17 s**. Median peak RSS **292,667,392 bytes**. Exit 0
every time.

`runs/p-final.out` is a copy of `recheck-3.out`: exit 0, 1.17 s,
292,667,392 bytes.

Meters, this worktree has no `.venv`, so they ran as
`/Users/alsg/Agentic/Bedrock/.venv/bin/python scripts/pod/witness.py`.
I did not add a dependency and I did not create a local `.venv`.

- Obligation: `0 UNRESOLVED of 1, 1.51 s, probe_red=False`
  (`runs/meter-obligation.out:2`).
- Top-level names: `0 UNRESOLVED of 4, 1.63 s, probe_red=False`
  (`runs/meter-names.out:5`).

Gates run while working: `scripts/gate/lint-agda.py --check` on
`Probe677.agda` exit 0, `scripts/gate/check-probes.py --check` clean,
10469 tracked files. `scripts/gate/lint-prose.py --check` on this
report exit 0.

## WHAT THE NEXT BRIEF NEEDS

1. **DO NOT RE-DISPATCH `Describes` AT `(σ₃, ⁅ sucV ∅ ⁆s)`.** It is
   paid (`describes-nonstage`, `Probe677.agda:203-204`). The generic
   singleton identity is paid (`dee-singleton`, `:107-108`). The
   generic singleton supplier is paid (`describes-sgl`, `:159-164`).
2. **DO NOT RE-DISPATCH `Describes` AT `(sucV δ, Lset δ)`.** It
   remains paid by `[LJ-1.674]`
   (`agents/tasks/LJ-1-674/Probe674.agda:72-74`).
3. **THIS GO DOES NOT COMPLETE `Describes`, AND IT DOES NOT COMPLETE
   `PowIter`.** The brief's GO-earns line is too strong. What is
   paid is one singleton, plus the generic singleton form. A member
   with two or more elements still owes a formula. `PowIter` is
   `Describes` collected over a finite iterate
   (`agents/tasks/LJ-1-169/ProbeLJ1169A.agda:91-96`). The consumer
   `from-iter` still waits on a supplier for the rest
   (`agents/tasks/LJ-1-668/lj-1.668-report.md:255-262`).
4. **THE REMAINING DEBT IS `Describes σ y` AT A NON-SINGLETON
   NON-STAGE MEMBER.** The pairing formula carves `{∅, y}`. That is
   `𝒟ₒ y` only for a singleton. A two-element `y` has four
   subsets, and the extra two are not a pairing identity.
5. **A `Formula Code 1` FOR `𝒟ₒ` STAYS A SECOND DEBT.** This task
   did not fund it. `[LJ-1.664]`'s census of `DefAt` at 166
   constants still stands.
6. **`LEM` IS THE PRICE OF THE SINGLETON IDENTITY.**
   `dee-singleton` decides membership of `a` in an arbitrary member
   of `𝒟ₒ (⁅ a ⁆s)`. Bound already takes `LEM`
   (`src/L/Coding/Bound.lagda.md:10`). A LEM-free `Describes` at
   this pair was not priced.
7. **WHAT THE STATEMENT COST.** 134 non-blank non-comment lines,
   median 1.17 s, median peak 292,667,392 bytes, two red runs (the
   floor, one import), no heap event. **WHAT THE SHAPE RESISTED.**
   Nothing at this pair once `LEM` and `pair∈𝒟ₒ` were in scope.
   The two identities fitted. **WHAT I HAD TO WEAKEN.** The
   obligation, from an arbitrary non-stage member to a singleton,
   and from LEM-free to `LEM` on the module. **WHAT I COULD NOT
   CLOSE.** `Describes` at a non-singleton non-stage member,
   `PowIter` at an arbitrary member, a LEM-free singleton identity,
   and a `Formula Code 1` for `𝒟ₒ`.

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
  the source for `describes-nonstage`.
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
  `Formula Code 1` for `𝒟ₒ` is a second debt. At a singleton the
  set-identity is `dee-singleton`, so `pair∈𝒟ₒ` closes it.
- `dev/literature/glossary-review-2026-08.md`: read at `:1`. Quote:
  `# Glossary review: the 119 pre-protocol entries`
  Declined, not used. No glossary term is at issue and I added no
  `dev/glossary.toml` entry.
- `dev/literature/devlin-errata.md`: read at `:1`. Quote:
  `# Devlin errata: documented error classes (do-not-repeat checklist)`
  Declined, not used. No Devlin erratum bears on `dee-singleton` or
  on `pair∈𝒟ₒ`.
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
- I did not inhabit `Describes` at an arbitrary non-stage member.
- I did not inhabit `Describes` at a non-singleton.
- I did not inhabit `PowIter`.
- I did not fund a `Formula Code 1` for `𝒟ₒ`.
- I did not refute `Describes`.
- I did not prove `y₀ ≢ Lset δ` as a closed term. The transitivity
  argument is in this report, not in the probe.
- I did not inhabit a term of "`𝒟ₒ y₀` is a proper subset of
  `Lset σ₃`". The identity `dee-singleton` supplies the two-element
  set; the inequality is inferred.
- I did not postulate. I left no hole in `Probe677.agda`.
- I did not leave a red `.agda` under this task home: the one file
  that cannot typecheck is `runs/FLOOR.agda.txt`.
- I did not add a dependency and I did not create a local `.venv`.
- I did not re-attack `describes-status`, `powiter-status` or
  `DeeInHull`.
- I did not write `review-of-describes-nonstage.md`. The obligation
  resolved. That file is the critic's input on a NO-GO, and this
  return is a GO.

## WORKING TREE, AS THIS REPORT DESCRIBES IT

Nothing committed, nothing pushed. No master edited. `src/` untouched.

New files, all in `agents/tasks/LJ-1-677/`:

- `Probe677.agda`, the search, green
- `lj-1.677-report.md`, this report
- `runs/`, the Agda transcripts and the one `.agda.txt` slice named
  above
