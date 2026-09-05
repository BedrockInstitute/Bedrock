# LJ-1.696 report: describes at the family the iterate actually reaches

## HEAD
slot: `coder`. Written early as a skeleton and filled as runs landed
(C-22). No commit, no push. I wrote only in `agents/tasks/LJ-1-696/`.
Agda ran under the caliber the program set on this pane,
`GHCRTS="-A64m -I0 -M2g"`, the wide caliber, ONE Agda process at a time.
I did not set `GHCRTS`. No heap event: the largest peak of any run is
397,180,928 bytes against the 2,147,483,648-byte cap.

TARGET: build ONE term in `agents/tasks/LJ-1-696/Probe696.agda`:

    describes-at-n3 : `Describes σ n3` where
                      `n3 = sucV (sucV (sucV ∅))`, the three-element
                      ordinal

Nothing lands in `src/`. Do not re-dispatch `Describes` at
`(sucV δ, Lset δ)`. `[LJ-1.674]` paid it
(`agents/tasks/LJ-1-674/Probe674.agda:72-74`). Do not re-dispatch
`Describes` at `(σ₃, ⁅ sucV ∅ ⁆s)` or the generic singleton
`describes-sgl`. `[LJ-1.677]` paid both
(`agents/tasks/LJ-1-677/Probe677.agda:159-164` and `:203-204`).
Do not re-dispatch `describes-generic` as a closed term.
`[LJ-1.683]` stated that NO-GO
(`agents/tasks/LJ-1-683/review-of-describes-generic.md:9-10`).
Do not re-dispatch `describes-supplier` at a pair.
`[LJ-1.687]` paid it
(`agents/tasks/LJ-1-687/Probe687.agda:253-263`).
Do not re-dispatch `iterate-from-families`.
`[LJ-1.694]` named the missing family
(`agents/tasks/LJ-1-694/Probe694.agda:174-181`).

The standing direction (`dev/pod/direction.md:37`) says one SRC
collection after LJ-1, not after `[LJ-2.5]`. This task is LJ-1 work.
It does not start that collection and it does not start phase 3. No
Boundary clause is in conflict.

## VERDICT

**GO.** `describes-at-n3` is inhabited at `n3`, closed at
`σ₄ = sucV n3`.

- **GO.** `describes-at-n3` (`Probe696.agda:457-460`) has type
  `Describes σ₄ n3`. It spends `[LJ-1.683]`'s consumer `from-hyps`
  (`agents/tasks/LJ-1-683/Probe683.agda:147-150`), not a second
  copy. The witness meter reads `0 UNRESOLVED of 1, 1.18 s,
  probe_red=False` (`runs/meter-obligation.out:2`). The probe is
  green and carries no hole (`runs/p-final.out:4`, `EXIT=0` at
  `runs/p-final.out:23`). Three forced rechecks,
  `runs/recheck-1.out` through `recheck-3.out`, each `EXIT=0`.
- **GO, unasked, on the generic pair formula.** `pair∈dee`
  (`Probe696.agda:84-85`) is `⁅ c , d ⁆ ∈ 𝒟ₒ A` from `c ∈ A` and
  `d ∈ A`. W2.
- **GO, unasked, on the three-element classifier.** `classify3`
  (`Probe696.agda:251-263`) is the eight-way split of a subset of
  a three-element set, under `LEM`. W2.
- **GO, unasked, on the generic three-element supplier.**
  `describes-triple` (`Probe696.agda:373-389`) is `Describes σ y`
  at any three-element member. The obligation instantiates it at
  `y = n3`. Meter of the five top-level names:
  `0 UNRESOLVED of 5, 1.16 s, probe_red=False`
  (`runs/meter-names.out:6`).

**This is not a refutation of `Describes`.** I did not build a term
of its negation. The three-element family is a family the frame
admits.

**This does not inhabit `Describes` at an arbitrary member.** The
classifier lists the eight subsets of a three-element set. That
equals `𝒟ₒ y` when `y` has exactly three members, and nowhere
else. **FINDING:** the proof generalises to a three-element
member (`describes-triple`). It does not generalise to a member
of arbitrary finite size. The obligation is `n3` alone, and it
is paid.

**This does not close `PowIter`.** GO moves `PowIter` past the
first shape its iterate misses. A member with four or more
elements still sits further up the same iterate.

## THE PREDECESSOR QUESTION, ANSWERED BEFORE ANY AGDA

`[LJ-1.169]` delivered `Describes` as a TYPE, not as a term
(`agents/tasks/LJ-1-169/ProbeLJ1169A.agda:80-82`). Its report names
`powIter` NOT false and INFERRED TRUE
(`agents/tasks/LJ-1-169/lj-1.169-report.md:21-23`). It does not name
`Describes` FALSE. I take that type.

`[LJ-1.668]` named `PowIter` as `Describes` collected over a finite
iterate (`agents/tasks/LJ-1-668/lj-1.668-report.md:255-262`). Verdict
is a stated NO-GO on `powiter-status` as a closed term, and a GO on
two members and on the consumer
(`agents/tasks/LJ-1-668/lj-1.668-report.md:30-37`). The verdict does
not name `PowIter` FALSE
(`agents/tasks/LJ-1-668/review-of-powiter-status.md:16-20`). I take
the type. I do not inhabit a type the predecessor named FALSE.

`[LJ-1.674]` inhabited `describes-status` at `(sucV δ, Lset δ)`
(`agents/tasks/LJ-1-674/Probe674.agda:72-74`). Verdict GO
(`agents/tasks/LJ-1-674/lj-1.674-report.md:27`). It does not name
`Describes` FALSE. I take the type. I do not re-inhabit the pair
that predecessor paid.

`[LJ-1.677]` inhabited `describes-nonstage` at ONE pair
`(σ₃, ⁅ sucV ∅ ⁆s)` (`agents/tasks/LJ-1-677/Probe677.agda:203-204`)
and, unasked, the generic singleton `describes-sgl` (`:159-164`).
Verdict GO at that pair
(`agents/tasks/LJ-1-677/lj-1.677-report.md:29`). It does not name
`Describes` FALSE. I take the type. I do not re-inhabit the named
pair. I do not re-inhabit `describes-sgl`.

`[LJ-1.683]` is NO-GO on the closed term and GO on the generic
formula and GO on the consumer
(`agents/tasks/LJ-1-683/lj-1.683-report.md:30-46`). The stated
NO-GO is `agents/tasks/LJ-1-683/review-of-describes-generic.md:9-10`.
It does not name `Describes` FALSE
(`agents/tasks/LJ-1-683/review-of-describes-generic.md:17-22`).
I take the consumer `from-hyps`. I do not inhabit the closed term
that predecessor named unpaid.

`[LJ-1.687]` inhabited `describes-supplier` at the pair family
(`agents/tasks/LJ-1-687/Probe687.agda:253-263`). Verdict GO
(`agents/tasks/LJ-1-687/lj-1.687-report.md:32-34`). It does not name
`Describes` FALSE. I take the type. I do not re-inhabit the pair
family.

`[LJ-1.694]` named the missing family as `n3`
(`agents/tasks/LJ-1-694/Probe694.agda:174-181`). Verdict GO
(`agents/tasks/LJ-1-694/lj-1.694-report.md:35-38`). It does not name
`Describes` FALSE. It does not inhabit `Describes` at `n3`
(`agents/tasks/LJ-1-694/lj-1.694-report.md:74-76`). I take the
witness `n3`. I inhabit the family that predecessor named.

## D-10, BEFORE ANY AGDA

D-10 says to price the truth of the target before pricing its proof.

1. The target. `Describes σ n3` at the three-element ordinal
   `n3 = sucV³ ∅`. `[LJ-1.683]` paid the consumer `from-hyps` from
   `Dee⊆stage` and `StagePowDef`
   (`agents/tasks/LJ-1-683/Probe683.agda:147-150`).
2. What a three-element set carries. `n3` has three distinct
   members `∅`, `sucV ∅` and `sucV² ∅`
   (`agents/tasks/LJ-1-694/Probe694.agda:124-149`). Under `LEM`, a
   subset of `n3` is one of eight. `empty∈dee` and `A∈𝒟ₒ` put the
   first and the last in `𝒟ₒ n3`. `eq∈dee` puts each singleton in
   `𝒟ₒ n3`. The disjunction of two equalities puts each pair in
   `𝒟ₒ n3`. So `StagePowDef` is true at `n3`. No Tarskian or
   cardinality obstruction.
3. What the stage must already hold. `Dee⊆stage` at `n3` is
   membership of those eight in `Lset σ`. At `σ = sucV n3`, the
   tree already places ordinals, singletons and pairs one stage
   up (`ord∈Lset-suc`, `sgl∈Lset-suc`, `pair∈Lset-suc`). D-26:
   a three-element set carries generation data (its three
   elements).
4. The corrected target beside the original, as D-10 asks: the
   same type, at `n3`, under `LEM`, closed at `σ = sucV n3`. It
   is true. A generic `n`-element family for `n ≥ 4`, `PowIter`
   as a closed term, and a `Formula Code 1` for `𝒟ₒ`, are
   different targets. I did not price their proofs.

## THE FLOOR, AND HOW IT WAS TAKEN

The standing clause asks for the frame to be priced before the proof.

- **The floor was priced first.** `runs/FLOOR.agda.txt`: the trimmed
  frame, the obligation in full, and a HOLE where the term goes. Its
  run is `runs/floor-1.out`: **exit 42 at 0.83 s, peak 269,746,176
  bytes**, with `[UnsolvedInteractionMetas]` at the one designed hole
  (`runs/floor-1.out:5-7`) and no other error.
- **The trim is why the frame is cheap.** The statement names `Lset`,
  `sucV`, empty, `Formula`, `DefOf.defSet`, `Describes` and
  membership in a stage, and nothing else, so the floor drops Bound,
  Hull, CloseSyntax, StageArith, Stages, LEM, Probe683, pairing,
  singleton and a `Formula Code 1`. P-l: `n3` and `σ₄` are named
  first, so the type does not mention a nested `sucV` chain. Every
  later green run stayed inside 398 MB. No restructuring of the
  term was needed after the first green, and no heap wall was met.

**THE SLICE IS DELIVERED WITH A `.txt` SUFFIX, ON PURPOSE.** It is red
by design. `find agents/tasks/LJ-1-696 -name '*.agda'` returns
`Probe696.agda` and nothing else.

## W3, THE CODE MAP, AND WHAT THE THREE-ELEMENT FORMULA REACHES

The brief names W3 as "the formula at a three-element member" at
110 to 240 lines, basis `[LJ-1.687]`.

**THE THREE-ELEMENT FORMULA REACHES A THREE-ELEMENT MEMBER. IT DOES
NOT REACH AN ARBITRARY MEMBER.**

`pair∈dee` (`Probe696.agda:84-85`) puts `{c, d}` in `𝒟ₒ A` from
`c ∈ A` and `d ∈ A`, by `(var zero ≐ con m_c) ∨̇ (var zero ≐ con m_d)`.
`classify3` (`:251-263`) splits a subset of a three-element set
into the eight subsets, under `LEM`. `triple-spd` (`:303-308`) is
`StagePowDef` at a three-element set from that split.
`triple-dee⊆` (`:337-350`) is `Dee⊆stage` at a three-element set
from the eight stage-memberships. `describes-triple` (`:373-389`)
spends `from-hyps` on those two. `describes-at-n3` (`:457-460`)
instantiates that supplier at `y = n3` and `σ = sucV n3`, spending
`ord∈Lset-suc`, `sgl∈Lset-suc` and `pair∈Lset-suc` for the eight
memberships.

**Arbitrary `y`.** The pairing formula is paid and too small. The
tautology is paid and too big. The subset formula is paid and still
owes the two hypotheses at a generic member. The three-element
supplier pays those hypotheses when `y` has exactly three members
and the stage already holds the eight subsets. A member with four
or more elements still owes a classifier. A `Formula Code 1` for
`𝒟ₒ` stays a second debt.

Line count: 460 total, 377 non-blank non-comment (`Probe696.agda`).
The brief estimated 110 to 240. The estimate assumed the formula
at a three-element member. The eight-way split is why the file
is larger than the four-way split at `[LJ-1.687]`.

## WHAT WAS BUILT

All in `agents/tasks/LJ-1-696/Probe696.agda`, module
`LJ-1-696.Probe696 {ℓ} (lem)`. `LEM` is a module parameter, used
by `classify3` and by `L.Ordinal.Stages`. No nested telescope at
the obligation.

- `Describes`, `Dee⊆stage`, `StagePowDef`, `from-hyps`
  (`:47-48`). Imported from
  `agents/tasks/LJ-1-683/Probe683.agda`. W2. Not rewritten.
- `empty∈dee`, `A∈𝒟ₒ`, `eq∈dee` (`:49-50`). Imported from
  `agents/tasks/LJ-1-687/Probe687.agda`. W2. Not rewritten.
- `pair∈dee` (`:84-85`). The disjunctive equality formula at a
  generic carrier. W2.
- `classify3` (`:251-263`). The eight-way split. W2. Needs `LEM`.
- `triple-spd` (`:303-308`). `StagePowDef` at a three-element set.
- `triple-dee⊆` (`:337-350`). `Dee⊆stage` at a three-element set.
- `describes-triple` (`:373-389`). The generic supplier. One call
  of `from-hyps`.
- `n3`, `σ₄` (`:393-397`). Named first (P-l).
- `describes-at-n3` (`:457-460`). The obligation. One call of
  `describes-triple`.

## W2 (DD4)

The mathematics is written once at a generic carrier and
instantiated. `pair∈dee` is `{c, d} ∈ 𝒟ₒ A` at an arbitrary
carrier. `classify3` is the eight-way split at an arbitrary
three-element set. `describes-triple` is `Describes` at an
arbitrary three-element member. `from-hyps` is imported from
`[LJ-1.683]` and is not rewritten. `empty∈dee`, `A∈𝒟ₒ` and
`eq∈dee` are imported from `[LJ-1.687]` and are not rewritten.
`describes-at-n3` instantiates those at `y = n3`. No line of
`describes-supplier` is rewritten. No line of `from-hyps` is
rewritten. The deadline conflict the clause names did not arise:
generic was cheaper than a second copy of the consumer or of the
pair supplier.

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
(`_build/2.8.0/agda/agents/tasks/LJ-1-696/Probe696.agdai`).

Build history, in order:

| run | contents | exit | wall s | peak RSS bytes |
|---|---|---|---|---|
| `floor-1` | `FLOOR.agda.txt`, designed hole | 42 | 0.83 | 269,746,176 |
| `p-1` | first probe, remap implicits unsolved | 42 | 2.39 | 397,180,928 |
| `p-2` | remaps explicit, first full green | 0 | 2.24 | 362,053,632 |

`p-1` is `[UnsolvedMetaVariables]` at the four remap call sites
(`runs/p-1.out:34-47`). The implicit carrier of `Mem3` did not
solve. The remaps now take `a b c x` as explicit arguments. One
shape change. No heap event at any point.

Three forced rechecks of the delivered file, probe interface removed
each time:

| run | exit | wall s | peak RSS bytes |
|---|---|---|---|
| `runs/recheck-1.out` | 0 | 1.84 | 362,053,632 |
| `runs/recheck-2.out` | 0 | 2.73 | 321,372,160 |
| `runs/recheck-3.out` | 0 | 1.78 | 362,086,400 |

Median wall **1.84 s**. Median peak RSS **362,053,632 bytes**. Exit 0
every time.

`runs/p-final.out` is a copy of `recheck-3.out`: exit 0, 1.78 s,
362,086,400 bytes.

Meters, this worktree has no `.venv`, so they ran as
`/Users/alsg/Agentic/Bedrock/.venv/bin/python scripts/pod/witness.py`.
I did not add a dependency and I did not create a local `.venv`.

- Obligation: `0 UNRESOLVED of 1, 1.18 s, probe_red=False`
  (`runs/meter-obligation.out:2`).
- Top-level names: `0 UNRESOLVED of 5, 1.16 s, probe_red=False`
  (`runs/meter-names.out:6`).

Gates run while working: `scripts/gate/lint-agda.py --check` on
`Probe696.agda` exit 0, `scripts/gate/check-probes.py --check` clean,
10709 tracked files. `scripts/gate/lint-prose.py --check` on this
report exit 0.

## WHAT THE NEXT BRIEF NEEDS

1. **DO NOT RE-DISPATCH `Describes` AT `(sucV δ, Lset δ)`.** It
   remains paid by `[LJ-1.674]`
   (`agents/tasks/LJ-1-674/Probe674.agda:72-74`).
2. **DO NOT RE-DISPATCH `Describes` AT `(σ₃, ⁅ sucV ∅ ⁆s)`.** It
   remains paid by `[LJ-1.677]`
   (`agents/tasks/LJ-1-677/Probe677.agda:203-204`). The generic
   singleton identity remains paid (`dee-singleton`). The generic
   singleton supplier remains paid (`describes-sgl`, `:159-164`).
3. **DO NOT RE-DISPATCH `describes-generic` AS A CLOSED TERM.** It
   still owes a supplier at a generic member. The consumer remains
   paid (`from-hyps`). The subset formula remains paid (`subsetFo`).
4. **DO NOT RE-DISPATCH `describes-supplier` AT A PAIR.** It is
   paid (`describes-supplier`, `agents/tasks/LJ-1-687/Probe687.agda:253-263`).
5. **DO NOT RE-DISPATCH `iterate-from-families`.** The missing
   family remains named (`agents/tasks/LJ-1-694/Probe694.agda:174-181`).
6. **DO NOT RE-DISPATCH `describes-at-n3`.** It is paid
   (`Probe696.agda:457-460`). The generic pair formula is paid
   (`pair∈dee`, `:84-85`). The three-element classifier is paid
   (`classify3`, `:251-263`). `StagePowDef` at a three-element set
   is paid (`triple-spd`, `:303-308`). `Dee⊆stage` at a
   three-element set is paid (`triple-dee⊆`, `:337-350`). The
   generic three-element supplier is paid (`describes-triple`,
   `:373-389`).
7. **THIS GO DOES NOT COMPLETE `PowIter`.** What is paid is the
   three-element family, plus the consumer from `[LJ-1.683]`. A
   member with four or more elements still owes a classifier.
   `PowIter` is `Describes` collected over a finite iterate
   (`agents/tasks/LJ-1-169/ProbeLJ1169A.agda:91-96`). The consumer
   `from-iter` still waits on a supplier for the rest
   (`agents/tasks/LJ-1-668/lj-1.668-report.md:255-262`).
8. **THE REMAINING DEBT IS `Describes σ y` AT A MEMBER OF SIZE
   FOUR OR MORE, AND AT A GENERIC MEMBER.** The three-element
   classifier lists eight subsets. A four-element `y` has sixteen
   subsets, and that split is not this term. A generic `y` still
   carries no generation data (D-26).
9. **A `Formula Code 1` FOR `𝒟ₒ` STAYS A SECOND DEBT.** This task
   did not fund it. `[LJ-1.664]`'s census of `DefAt` at 166
   constants still stands.
10. **`LEM` IS THE PRICE OF THE THREE-ELEMENT CLASSIFIER.**
    `classify3` decides membership of `a`, of `b` and of `c` in
    an arbitrary subset. Bound already takes `LEM`
    (`src/L/Coding/Bound.lagda.md:10`). A LEM-free `Describes` at
    `n3` was not priced. Stages takes `LEM` for `ord∈Lset-suc`.
11. **WHAT THE STATEMENT COST.** 377 non-blank non-comment lines,
    median 1.84 s, median peak 362,053,632 bytes, two red runs (the
    floor, one unsolved implicit), no heap event. **WHAT THE SHAPE
    RESISTED.** The first remap left the carrier of `Mem3`
    unsolved. Explicit arguments closed it. Nothing at `n3` once
    `LEM`, `from-hyps` and the eight identities were in scope.
    **WHAT I HAD TO WEAKEN.** Nothing on the obligation: the brief
    asked for `Describes` at `n3`, and the term is closed at
    `σ = sucV n3`. I did not inhabit `Describes` at an arbitrary
    member. **WHAT I COULD NOT CLOSE.** `Describes` at a member of
    size four or more, `PowIter` at an arbitrary member, a LEM-free
    three-element classifier, and a `Formula Code 1` for `𝒟ₒ`.

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
  the source for `describes-at-n3`.
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
  why `Describes` is a set-identity against `defSet`. At a
  three-element member the set-identity is the eight subsets, so
  `from-hyps` closes it from `StagePowDef` and `Dee⊆stage`.
- `dev/literature/glossary-review-2026-08.md`: read at `:1`. Quote:
  `# Glossary review: the 119 pre-protocol entries`
  Declined, not used. No glossary term is at issue and I added no
  `dev/glossary.toml` entry.
- `dev/literature/devlin-errata.md`: read at `:1`. Quote:
  `# Devlin errata: documented error classes (do-not-repeat checklist)`
  Declined, not used. No Devlin erratum bears on `pair∈dee` or on
  `classify3`.
- `dev/literature/primary-sources.md`: read at `:1`. Quote:
  `# Primary sources, second round: Jensen manuscript, Devlin, Jech`
  Declined, not used. The slot-role note above is the source that
  decided the formula question. The identities the supplier spends
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
- I did not inhabit `Describes` at an arbitrary member.
- I did not inhabit `Describes` at a four-element member.
- I did not inhabit `PowIter`.
- I did not fund a `Formula Code 1` for `𝒟ₒ`.
- I did not refute `Describes`.
- I did not re-inhabit `describes-status`, `describes-nonstage`,
  `describes-sgl` or `describes-supplier`.
- I did not rewrite `from-hyps`.
- I did not postulate. I left no hole in `Probe696.agda`.
- I did not leave a red `.agda` under this task home: the one file
  that cannot typecheck is `runs/FLOOR.agda.txt`.
- I did not add a dependency and I did not create a local `.venv`.
- I did not re-attack `powiter-status` or `describes-generic`.
- I did not write `review-of-describes-at-n3.md`. The obligation
  resolved. That file is the critic's input on a NO-GO, and this
  return is a GO.

## WORKING TREE, AS THIS REPORT DESCRIBES IT

Nothing committed, nothing pushed. No master edited. `src/` untouched.

New files, all in `agents/tasks/LJ-1-696/`:

- `Probe696.agda`, the search, green
- `lj-1.696-report.md`, this report
- `runs/`, the Agda transcripts and the one `.agda.txt` slice named
  above
