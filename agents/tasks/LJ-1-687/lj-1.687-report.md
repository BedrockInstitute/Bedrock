# LJ-1.687 report: the supplier the generic describes still owes

## HEAD
slot: `coder`. Written early as a skeleton and filled as runs landed
(C-22). No commit, no push. I wrote only in `agents/tasks/LJ-1-687/`.
Agda ran under the caliber the program set on this pane,
`GHCRTS="-A64m -I0 -M2g"`, the wide caliber, ONE Agda process at a time.
I did not set `GHCRTS`. No heap event: the largest peak of any run is
299,204,608 bytes against the 2,147,483,648-byte cap.

TARGET: build ONE term in `agents/tasks/LJ-1-687/Probe687.agda`:

    describes-supplier : the SUPPLIER `describes-generic` still owes,
                         at the shape `[LJ-1.683]` left, with its
                         consumer `from-hyps` taken as delivered

Nothing lands in `src/`. Do not re-dispatch `Describes` at
`(sucV δ, Lset δ)`. `[LJ-1.674]` paid it
(`agents/tasks/LJ-1-674/Probe674.agda:72-74`). Do not re-dispatch
`Describes` at `(σ₃, ⁅ sucV ∅ ⁆s)` or the generic singleton
`describes-sgl`. `[LJ-1.677]` paid both
(`agents/tasks/LJ-1-677/Probe677.agda:159-164` and `:203-204`).
Do not re-dispatch `describes-generic` as a closed term.
`[LJ-1.683]` stated that NO-GO
(`agents/tasks/LJ-1-683/review-of-describes-generic.md:9-10`).

The standing direction (`dev/pod/direction.md:37`) says one SRC
collection after LJ-1, not after `[LJ-2.5]`. This task is LJ-1 work.
It does not start that collection and it does not start phase 3. No
Boundary clause is in conflict.

## VERDICT

**GO.** `describes-supplier` is inhabited at the pair family.

- **GO.** `describes-supplier` (`Probe687.agda:253-263`) has type
  `(σ a b : S) → ⟨ ⁅ a , b ⁆ ∈ˢ Lset σ ⟩ → ⟨ ∅ ∈ˢ Lset σ ⟩ →
  ⟨ ⁅ a ⁆s ∈ˢ Lset σ ⟩ → ⟨ ⁅ b ⁆s ∈ˢ Lset σ ⟩ →
  Describes σ (⁅ a , b ⁆)`. It spends `[LJ-1.683]`'s consumer
  `from-hyps` (`agents/tasks/LJ-1-683/Probe683.agda:147-150`), not
  a second copy. The witness meter reads `0 UNRESOLVED of 1, 1.33 s,
  probe_red=False` (`runs/meter-obligation.out:2`). The probe is
  green and carries no hole (`runs/p-final.out:4`, `EXIT=0` at
  `runs/p-final.out:23`). Three forced rechecks,
  `runs/recheck-1.out` through `recheck-3.out`, each `EXIT=0`.
- **GO, unasked, on the generic equality formula.** `eq∈dee`
  (`Probe687.agda:110-111`) is `⁅ c ⁆s ∈ 𝒟ₒ A` from `c ∈ A`. W2.
- **GO, unasked, on the pair classifier.** `classify`
  (`Probe687.agda:144-148`) is the four-way split of a subset of a
  pair, under `LEM`. Meter of the five top-level names:
  `0 UNRESOLVED of 5, 0.91 s, probe_red=False`
  (`runs/meter-names.out:6`).

**This is not a refutation of `Describes`.** I did not build a term
of its negation. The pair family is a family the frame admits. A
refutation would have been the brief's most valuable return. It does
not exist at a pair.

**This does not inhabit `Describes` at an arbitrary member.** The
classifier lists the four subsets of a pair. That equals `𝒟ₒ y`
when `y` is a pair, and nowhere else. The brief's GO-earns line
("completes `Describes`, then `PowIter`") is stronger than this
term. See WHAT THE NEXT BRIEF NEEDS.

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

`[LJ-1.683]` is NO-GO on the closed term and GO on the generic
formula and GO on the consumer
(`agents/tasks/LJ-1-683/lj-1.683-report.md:30-46`). The stated
NO-GO is `agents/tasks/LJ-1-683/review-of-describes-generic.md:9-10`.
It does not name `Describes` FALSE
(`agents/tasks/LJ-1-683/review-of-describes-generic.md:17-22`).
The type that predecessor delivered is `from-hyps`
(`agents/tasks/LJ-1-683/Probe683.agda:147-150`): `Describes σ y`
from `Dee⊆stage` and `StagePowDef`. I take that consumer. I do not
inhabit the closed term that predecessor named unpaid.

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
   (`agents/tasks/LJ-1-169/ProbeLJ1169A.agda:80-82`). `[LJ-1.683]`
   paid the consumer `from-hyps` from `Dee⊆stage` and `StagePowDef`
   (`agents/tasks/LJ-1-683/Probe683.agda:147-150`). The supplier
   this brief names is those two hypotheses, beyond the singleton
   family.
2. What a pair carries. A pair `y = ⁅ a , b ⁆` carries its two
   elements. Under `LEM`, a subset of `y` is one of four: `∅`,
   `{a}`, `{b}`, `{a, b}`. `empty∈dee` and `A∈𝒟ₒ` put the first and
   the last in `𝒟ₒ y`. `eq∈dee` puts each singleton in `𝒟ₒ y` by
   the equality formula over `⟪ y ⟫`. So `StagePowDef` is true at
   every pair. No Tarskian or cardinality obstruction.
3. What the stage must already hold. `Dee⊆stage` at a pair is
   membership of those four in `Lset σ`. It is true exactly when
   the four hypotheses of `describes-supplier` hold. D-26: a pair
   carries generation data (its two elements). A generic member of
   a definable power carries none, and that is why the closed
   generic case stayed unpaid at `[LJ-1.683]`.
4. The corrected target beside the original, as D-10 asks: the
   same type, at the pair family, under `LEM`, from the four
   stage-memberships. It is true. It is closed. The
   arbitrary-member form, a three-element family, and a
   `Formula Code 1` for `𝒟ₒ`, are different targets. I did not
   price their proofs.

## THE FLOOR, AND HOW IT WAS TAKEN

The standing clause asks for the frame to be priced before the proof.

- **The floor was priced first.** `runs/FLOOR.agda.txt`: the trimmed
  frame, the obligation in full, and a HOLE where the term goes. Its
  run is `runs/floor-1.out`: **exit 42 at 0.95 s, peak 269,860,864
  bytes**, with `[UnsolvedInteractionMetas]` at the one designed hole
  (`runs/floor-1.out:5-7`) and no other error.
- **The trim is why the frame is cheap.** The statement names `Lset`,
  `𝒟ₒ`, `Formula`, `DefOf.defSet`, `Describes`, pairing, singleton
  and membership in a stage, and nothing else, so the floor drops
  Bound, Hull, CloseSyntax, StageArith, LEM, `sucV`, Probe683 and a
  `Formula Code 1`. P-l did not bite: the type names no transparent
  `sucV`. Every later green run stayed inside 300 MB. No
  restructuring was needed and no heap wall was met.

**THE SLICE IS DELIVERED WITH A `.txt` SUFFIX, ON PURPOSE.** It is red
by design. `find agents/tasks/LJ-1-687 -name '*.agda'` returns
`Probe687.agda` and nothing else.

## W3, THE CODE MAP, AND WHAT THE PAIR SUPPLIER REACHES

The brief names W3 as "the supplier beyond the singleton family" at
120 to 250 lines, basis `[LJ-1.683]`.

**THE PAIR SUPPLIER REACHES A TWO-ELEMENT MEMBER. IT DOES NOT REACH
AN ARBITRARY MEMBER.**

`eq∈dee` (`Probe687.agda:110-111`) puts `{c}` in `𝒟ₒ A` from
`c ∈ A`, by `var zero ≐ con m_c`. `classify` (`:144-148`) splits a
subset of `{a, b}` into the four subsets, under `LEM`. `pair-spd`
(`:220-221`) is `StagePowDef` at a pair from that split.
`pair-dee⊆` (`:235-241`) is `Dee⊆stage` at a pair from the four
stage-memberships. `describes-supplier` (`:253-263`) spends
`from-hyps` on those two.

**Arbitrary `y`.** The pairing formula is paid and too small. The
tautology is paid and too big. The subset formula is paid and still
owes the two hypotheses at a generic member. The pair supplier pays
those hypotheses when `y` is a pair and the stage already holds the
four subsets. A member with three or more elements still owes a
classifier. A `Formula Code 1` for `𝒟ₒ` stays a second debt.

Line count: 263 total, 195 non-blank non-comment (`Probe687.agda`).
The brief estimated 120 to 250. The estimate assumed a supplier
beyond the singleton family. The pair family fitted.

## WHAT WAS BUILT

All in `agents/tasks/LJ-1-687/Probe687.agda`, module
`LJ-1-687.Probe687 {ℓ} (lem)`. No nested telescope at the
obligation. `LEM` is a module parameter, used by `classify` only.

- `Describes`, `Dee⊆stage`, `StagePowDef`, `from-hyps`
  (`:42-43`). Imported from
  `agents/tasks/LJ-1-683/Probe683.agda`. W2. Not rewritten.
- `empty∈dee` (`:89-90`). Copied from
  `agents/tasks/LJ-1-677/Probe677.agda:86-98`. W2.
- `A∈𝒟ₒ` (`:105-106`). Copied from
  `agents/tasks/LJ-1-668/Probe668.agda:79-80`. W2.
- `eq∈dee` (`:110-111`). The equality formula at a generic
  carrier. W2.
- `classify` (`:144-148`). The four-way split. W2. Needs `LEM`.
- `pair-spd` (`:220-221`). `StagePowDef` at a pair.
- `pair-dee⊆` (`:235-241`). `Dee⊆stage` at a pair.
- `describes-supplier` (`:253-263`). The obligation. One call of
  `from-hyps`.

## W2 (DD4)

The mathematics is written once at a generic carrier and
instantiated. `eq∈dee` is `{c} ∈ 𝒟ₒ A` at an arbitrary carrier.
`classify` is the four-way split at an arbitrary pair.
`from-hyps` is imported from `[LJ-1.683]` and is not rewritten.
`describes-supplier` instantiates those at `y = ⁅ a , b ⁆`. No line
of `pair∈𝒟ₒ` is rewritten. No line of `from-hyps` is rewritten.
The deadline conflict the clause names did not arise: generic was
cheaper than a second copy of the consumer or of the singleton
identity.

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
(`_build/2.8.0/agda/agents/tasks/LJ-1-687/Probe687.agdai`).

Build history, in order:

| run | contents | exit | wall s | peak RSS bytes |
|---|---|---|---|---|
| `floor-1` | `FLOOR.agda.txt`, designed hole | 42 | 0.95 | 269,860,864 |
| `p-1` | first probe, `subst₂` not in scope | 42 | 1.16 | 288,948,224 |
| `p-2` | `subst₂` dropped, first full green | 0 | 1.19 | 299,204,608 |
| `p-3` | unused `ιfst`, `sgl∈` and `Σ-syntax` removed | 0 | 1.52 | 297,058,304 |

`p-1` is `[NotInScope]` for `subst₂` (`runs/p-1.out:6-13`). The
equality `fst (ι k) ≡ ⟪ A ⟫↪ k` is definitional, so the path
composition does not need `subst₂`. One name dropped. No
restructuring, and no heap event at any point.

Three forced rechecks of the delivered file, probe interface removed
each time:

| run | exit | wall s | peak RSS bytes |
|---|---|---|---|
| `runs/recheck-1.out` | 0 | 1.21 | 297,058,304 |
| `runs/recheck-2.out` | 0 | 1.29 | 297,091,072 |
| `runs/recheck-3.out` | 0 | 1.26 | 297,091,072 |

Median wall **1.26 s**. Median peak RSS **297,091,072 bytes**. Exit 0
every time.

`runs/p-final.out` is a copy of `recheck-3.out`: exit 0, 1.26 s,
297,091,072 bytes.

Meters, this worktree has no `.venv`, so they ran as
`/Users/alsg/Agentic/Bedrock/.venv/bin/python scripts/pod/witness.py`.
I did not add a dependency and I did not create a local `.venv`.

- Obligation: `0 UNRESOLVED of 1, 1.33 s, probe_red=False`
  (`runs/meter-obligation.out:2`).
- Top-level names: `0 UNRESOLVED of 5, 0.91 s, probe_red=False`
  (`runs/meter-names.out:6`).

Gates run while working: `scripts/gate/lint-agda.py --check` on
`Probe687.agda` exit 0, `scripts/gate/check-probes.py --check` clean,
10607 tracked files. `scripts/gate/lint-prose.py --check` on this
report exit 0.

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
   still owes a supplier at a generic member. The consumer remains
   paid (`from-hyps`). The subset formula remains paid (`subsetFo`).
4. **DO NOT RE-DISPATCH `describes-supplier` AT A PAIR.** It is
   paid (`describes-supplier`, `Probe687.agda:253-263`). The generic
   equality formula is paid (`eq∈dee`, `:110-111`). The pair
   classifier is paid (`classify`, `:144-148`). `StagePowDef` at a
   pair is paid (`pair-spd`, `:220-221`). `Dee⊆stage` at a pair is
   paid (`pair-dee⊆`, `:235-241`).
5. **THIS GO DOES NOT COMPLETE `Describes`, AND IT DOES NOT
   COMPLETE `PowIter`.** The brief's GO-earns line is too strong.
   What is paid is the pair family, plus the consumer from
   `[LJ-1.683]`. A member with three or more elements still owes a
   classifier. `PowIter` is `Describes` collected over a finite
   iterate
   (`agents/tasks/LJ-1-169/ProbeLJ1169A.agda:91-96`). The consumer
   `from-iter` still waits on a supplier for the rest
   (`agents/tasks/LJ-1-668/lj-1.668-report.md:255-262`). Two
   chapters still assume `powIter` under other names
   (`src/L/Coding/Bound.lagda.md:147`).
6. **THE REMAINING DEBT IS `Describes σ y` AT A NON-PAIR
   NON-SINGLETON NON-STAGE MEMBER.** The pair classifier lists four
   subsets. A three-element `y` has eight subsets, and that split
   is not this term. A generic `y` still carries no generation
   data (D-26).
7. **A `Formula Code 1` FOR `𝒟ₒ` STAYS A SECOND DEBT.** This task
   did not fund it. `[LJ-1.664]`'s census of `DefAt` at 166
   constants still stands.
8. **`LEM` IS THE PRICE OF THE PAIR CLASSIFIER.** `classify`
   decides membership of `a` and of `b` in an arbitrary subset.
   Bound already takes `LEM`
   (`src/L/Coding/Bound.lagda.md:10`). A LEM-free `Describes` at a
   pair was not priced.
9. **WHAT THE STATEMENT COST.** 195 non-blank non-comment lines,
   median 1.26 s, median peak 297,091,072 bytes, two red runs (the
   floor, one name not in scope), no heap event. **WHAT THE SHAPE
   RESISTED.** Nothing at a pair once `LEM` and `from-hyps` were in
   scope. The four identities fitted. **WHAT I HAD TO WEAKEN.**
   The obligation, from a supplier at an arbitrary family to the
   pair family, and from LEM-free to `LEM` on the module. **WHAT I
   COULD NOT CLOSE.** `Describes` at a non-pair non-singleton
   non-stage member, `PowIter` at an arbitrary member, a LEM-free
   pair classifier, and a `Formula Code 1` for `𝒟ₒ`.

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
  the source for `describes-supplier`.
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
  `Formula Code 1` for `𝒟ₒ` is a second debt. At a pair the
  set-identity is the four subsets, so `from-hyps` closes it from
  `StagePowDef` and `Dee⊆stage`.
- `dev/literature/glossary-review-2026-08.md`: read at `:1`. Quote:
  `# Glossary review: the 119 pre-protocol entries`
  Declined, not used. No glossary term is at issue and I added no
  `dev/glossary.toml` entry.
- `dev/literature/devlin-errata.md`: read at `:1`. Quote:
  `# Devlin errata: documented error classes (do-not-repeat checklist)`
  Declined, not used. No Devlin erratum bears on `eq∈dee` or on
  `from-hyps`.
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
- I did not inhabit `Describes` at a three-element member.
- I did not inhabit `PowIter`.
- I did not fund a `Formula Code 1` for `𝒟ₒ`.
- I did not refute `Describes`.
- I did not re-inhabit `describes-status`, `describes-nonstage` or
  `describes-sgl`.
- I did not rewrite `from-hyps`.
- I did not postulate. I left no hole in `Probe687.agda`.
- I did not leave a red `.agda` under this task home: the one file
  that cannot typecheck is `runs/FLOOR.agda.txt`.
- I did not add a dependency and I did not create a local `.venv`.
- I did not re-attack `powiter-status` or `DeeInHull`.
- I did not write `review-of-describes-supplier.md`. The obligation
  resolved. That file is the critic's input on a NO-GO, and this
  return is a GO.

## WORKING TREE, AS THIS REPORT DESCRIBES IT

Nothing committed, nothing pushed. No master edited. `src/` untouched.

New files, all in `agents/tasks/LJ-1-687/`:

- `Probe687.agda`, the search, green
- `lj-1.687-report.md`, this report
- `runs/`, the Agda transcripts and the one `.agda.txt` slice named
  above
