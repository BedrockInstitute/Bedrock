# LJ-1.554 report: can a formula describe an assignment it was not built with

## HEAD
head_slot: coder
machine: shared
verdict: STOP. NEITHER `no-generic-link` NOR THE GENERIC `Link`.

The report was written as a skeleton before any Agda and filled as each answer
landed (C-22). No commit, no push. I wrote only inside
`agents/tasks/LJ-1-554/`. Agda ran under the caliber the program set on this
pane, `GHCRTS="-A64m -I0 -M8g"`, ONE Agda process at a time. I did not set
`GHCRTS`. No heap event. Nothing is postulated. The probe is a raw `.agda`
file, so it carries no ` ```agda ` fence, counts 0 in-fence lines, and the
ratio bar cannot fire on it.

## VERDICT

**THE BRIEF SAID "One of the two is true and the task is to find out which."
THAT IS TRUE ABOUT TRUTH AND IT IS NOT TRUE ABOUT THIS TREE.** Neither half is
reachable here, and the reason is a type argument and not a failed search. The
stop is `agents/tasks/LJ-1-554/review-of-no-generic-link.md`.

**THE PROBE IS GREEN, EXIT 0, THREE RUNS.**
`agents/tasks/LJ-1-554/Probe554.agda`, `runs/final-1.out` to `runs/final-3.out`.
It carries no hole and no postulate. That is deliberate: a hole would make every
reduction in it a claim, and green makes each one a measurement. Nothing lands in
`src/`.

**THE RESULT IN ONE LINE.** The generic `Link` and the constructibility of the
assignment's ambient graph are the SAME REQUEST, measured in both directions, and
that request is the ambient-to-coded crossing the tree has already recorded as
INDEPENDENT rather than false.

THREE findings.

1. **D-10. THE COUNTING THE BRIEF OFFERED DOES NOT FIRE.** `Formula S 3` takes
   its constants from `S` itself, so the formulas are not a set. The book says so
   in its own prose (`src/FOL/Syntax.lagda.md:138`) and `nameOf-inj`
   (`Probe554.agda:147-148`) measures it.
2. **`Link` AND THE CODED GRAPH ARE ONE REQUEST.** `link→graph`
   (`Probe554.agda:198-211`) and `graph→link` (`:232-265`). The converse costs
   less than the forward direction: it takes no `κ`, no `⊆ˢ`, and no injectivity.
3. **THE ONE MISSING PROPERTY IS `⟨ isL (grV δ s) ⟩`**, one proposition about one
   named ambient set (`constructible-graph→link`, `Probe554.agda:307-309`). No
   term of `src/` and no term of any live probe refutes `isL` of anything: the
   grep count is **0**.

## WHICH WAY IT WENT

**THE GENERIC `Link` DOES NOT EXIST IN THIS TREE, AND IT IS NOT REFUTABLE IN THIS
TREE EITHER, SO THE ASSIGNMENT AND ITS FORMULA MUST BE BUILT IN ONE TASK.** The
probe measures the equivalence that settles it: a `Link` for `s` gives an
L-element whose members are exactly the pairs of `s` (`link→graph`,
`Probe554.agda:198-211`), and such an L-element gives a `Link` back
(`graph→link`, `:232-265`), so nothing separates the two. A `Link` therefore
cannot be ADDED to an assignment that was produced without one, because producing
it is producing the assignment's graph as a constructible object, and an ambient
function does not carry that (`agents/tasks/LJ-1-414/review-of-amb-to-coded.md:41`,
"no producer for this type at an arbitrary ambient injection"). **The consequence
for `[LJ-1.552]`'s successor is exact: a brief that takes `[LJ-1.552]`'s
assignment and then asks a later task for its formula is asking for a term that
this tree cannot produce and cannot refute, so the successor must produce the
assignment TOGETHER with the L-element that is its graph, and derive the formula
from that L-element by `graph→link`, which is nineteen lines and needs no side
condition.**

## WHAT A NON-GENERIC LINK WOULD NEED

A `Link` needs exactly one extra property of `s`, and it is not definability of
`s` as a formula, not a bound, and not a Levy grade: it is `⟨ isL (grV δ s) ⟩`,
the constructibility of the one ambient set `grV δ s` that section 1 of the probe
builds from `s` with no hypothesis at all (`Probe554.agda:160-161`,
`constructible-graph→link` at `:307-309`). The bound is already free, because
`smallDom` confines the whole table from `s` alone
(`agents/tasks/LJ-1-549/Probe549.agda:289-290`), and the grade is not in question,
because no term in this reduction is graded. I did not build a `Link` for any
assignment: `constructible-graph→link` is a reduction whose hypothesis is the
missing input, in the `[LJ-1.533]` discipline that a green term makes a statement
a measurement rather than a claim.

## D-10

**I RAN D-10 BEFORE ANY OTHER AGDA, AS THE BRIEF REQUIRED, AND IT FIRED AGAINST
THE BRIEF'S OWN ARGUMENT.**

The brief said: "Say at `file:line` how many `Formula S 3` there are and how many
assignments `⟪ fst δ ⟫ → S` there are. **If the formulas are a set and the
assignments are a function space into a proper carrier, say so**: that is the
whole argument and the rest is writing it down."

**THE FORMULAS ARE NOT A SET.** `Formula K n` draws its constants from `K`
(`src/FOL/Syntax.lagda.md:43`, `con : K → Term K n`), and the `K` in
`Formula S 3` is `S`, the L-carrier. The book states the consequence itself,
`src/FOL/Syntax.lagda.md:138`:

> a syntax whose constants are all sets is too big to be
> counted or coded

**THE BRIEF'S PREMISE 7 IS TRUE AND DOES NOT CARRY THE ARGUMENT.** "`Formula` is
a set of syntax, not a function space" is right about the SHAPE of the type. It
says nothing about its width, and the width is what a counting argument needs.

**MEASUREMENT 1.** `nameOf` (`Probe554.agda:144-145`) sends every L-set to a
formula, and `nameOf-inj` (`:147-148`) proves the map injective. So `Formula S 3`
is at least as wide as `S`.

**MEASUREMENT 2, AND IT IS THE SHAPE OF THE WHOLE ANSWER.** The graph of the
assignment is ALREADY an ambient set with no hypothesis. `grV`
(`Probe554.agda:160-161`) is one `sett` over `⟪ fst δ ⟫`, which is small by
construction, and membership in it is definitional, so `grV-in` (`:163-165`) is
`∣ k , refl ∣₁` and `grV-out` (`:167-170`) is the identity function.

**SO NOTHING IS MISSING AMBIENTLY, AND NOTHING IS MISSING BY COUNT. WHAT IS
MISSING IS `isL`.** `isL` is membership in some stage of the tower
(`src/L/Constructible.lagda.md:376-377`) and it is not a size condition.

**I CHECKED BEFORE I BELIEVED THE TREE LACKS THE FACT, AS THE BRIEF ORDERED.**
`[LJ-1.526]` overturned an archived cardinal claim by measurement, so I measured
rather than read. The grep for `isL` as the antecedent of a `⊥`, over
`src/` and `agents/tasks/` with `--include="*.agda" --include="*.lagda.md"`,
returns **0 hits**. And `[LJ-1.526]` records the identical gap at its own site,
`agents/tasks/LJ-1-526/Probe526.agda:110-116`: the converse of the cardinal
readback is "STATED AND NOT inhabited", because it "would need every ambient
injection between two L-elements to be coded by an L-element, which is the
definability direction of the readback".

**THE ESCAPE CLAUSE FIRES AND I TOOK IT.** The brief said: "IF THE REFUTATION
NEEDS A CARDINALITY FACT THE TREE DOES NOT HAVE, SAY SO AND STOP." It does. I
imported none and postulated none.

## W3

**W3 IS GO, ON THE FIRST RUN.** The arity-3 reading forms away from
`[LJ-1.549]`'s frame with nothing else in scope: no `powL`, no `prAtL`, no
assignment, no `[LJ-1.549]` import.

`agents/tasks/LJ-1-554/runs/W3.agda`, module `LJ-1-554.runs.W3`, exit 0,
`runs/w3-1.out` to `runs/w3-3.out`.

**WHAT IT MEASURED BEYOND FORMING.** `Reading-isProp` (`runs/W3.agda:59-60`) is
that the reading is a PROPOSITION. `[LJ-1.549]`'s `Residue` needs that silently:
its `link-out` eliminates a truncated satisfaction into a path, and that is legal
only at a proposition-valued goal
(`dev/literature/truncation-and-selection.md:143`). The main probe spends the same
rule twice, at `graph→link`'s `lout` (`Probe554.agda:251-265`) and at
`grL-isGraph`'s `gout` (`:294-305`).

**COST: 0.76 s, 69 lines, 22 of them code.** The brief estimated about 12 lines
and under 60 seconds. The line estimate was low because the file is mostly the
comment that says what the slice proves, and the time estimate was right.

## THE SWEEP (C-42)

The shape is "a residue that asks an L-element to describe an object the tree has
only as an ambient function". **THE COUNT OF RECORDED STOPS IS SIX, AND THIS TASK
IS THE SIXTH.** The table is at `Probe554.agda:404-417`.

| row | where the stop is recorded | what it names |
|---|---|---|
| `[LJ-1.414]` | `agents/tasks/LJ-1-414/review-of-amb-to-coded.md:34` | HALF A, the generic crossing |
| `[LJ-1.441]` | `agents/tasks/LJ-1-441/review-of-amb-to-coded-at-least.md:3` | the same wall at one named map |
| `[LJ-1.526]` | `agents/tasks/LJ-1-526/Probe526.agda:110-116` | the cardinal readback's converse |
| `[LJ-1.533]` | `agents/tasks/LJ-1-533/review-of-StageCountedCoded.md:1` | B9 |
| `[LJ-1.549]` | `agents/tasks/LJ-1-549/review-of-succ-into-subsets.md:63` | B10, two missing inputs |
| `[LJ-1.554]` | this task | B10's `Link` half |

**TWO NEIGHBOURS THAT LOOK LIKE THE SHAPE AND ARE NOT, BOTH CHECKED.**

- `[LJ-1.535]` (`agents/tasks/LJ-1-535/review-of-stage-card-upper-coded.md:8-14`)
  BUILT its Formula-carrying restatement and it is green. Its block is that the
  formula does not reach the injection's VALUE. That is a statement about where a
  DELIVERED formula travels, not about a formula with no producer.
- `[LJ-1.329]` (`archive/dev/LJ-dispatch-index.md:384`) is recorded as
  "WRONG-OBJECT. THERE IS NO SUCH OBJECT", and its note says the consumer
  "wants a TOTAL MAP OUT of sq, not a point of it". That is a mismatch between
  consumer and producer, not this wall.

**WHAT THE SWEEP DOES NOT MEASURE, STATED AS A LIMIT.** I counted RECORDED stops,
which is what the tree can show me. I did not count the rows of the campaign that
will meet this wall and have not been dispatched, because that count is not in the
tree.

## THE ONE DEPARTURE FROM THE BRIEF, DECLARED

**THE BRIEF SAID "Do not build it" ABOUT THE NON-GENERIC `Link`. I BUILT THE
REDUCTION TO IT, AND I SAY SO HERE RATHER THAN LETTING IT PASS.**

`graph→link` (`Probe554.agda:232-265`) and `constructible-graph→link` (`:307-309`)
build a `Link` from a hypothesis. They build one for no assignment this tree has.

**WHY I JUDGED IT IN SCOPE.** The verdict is "neither half is reachable", and that
verdict needs BOTH arrows. The forward arrow alone would only say the generic
`Link` is at least as strong as an unprovable statement; it would leave
`no-generic-link` open. The converse arrow is what closes it: it shows the generic
`Link` is no STRONGER either, so a refutation of it would refute
`GenericConstructible`, and that is where the stop lands. Without the converse the
report's central claim is prose, and the Boundary asks for `file:line`.

**WHAT I DID NOT DO WITH IT.** No assignment is built, B10 is not discharged, no
term lands in `src/`, and `## WHAT A NON-GENERIC LINK WOULD NEED` is three
sentences as the brief ordered.

## WHAT THE NEXT BRIEF SHOULD KNOW

**1. THE SUCCESSOR OF `[LJ-1.552]` MUST ASK FOR THE ASSIGNMENT AND ITS L-ELEMENT
GRAPH TOGETHER, NOT IN TWO TASKS.** The obligation to write is

    Σ[ s ∈ (⟪ fst δ ⟫ → S) ] Σ[ G ∈ S ]
      ( sub × inj × IsGraphOf δ s G )

with `IsGraphOf` at `Probe554.agda:190-195`. `graph→link` then delivers the
`Link` for nothing, and `[LJ-1.549]`'s `residue-suffices` and `residue-pays-B10`
(`agents/tasks/LJ-1-549/Probe549.agda:679-689`) close B10 from there. **A brief
that asks for `s` first and `Link` second is asking a later task for a term that
cannot be produced and cannot be refuted.**

**2. `[LJ-1.552]` IS NOT IN THIS WORKTREE AND I TOOK NO HYPOTHESIS FROM IT.**
`agents/tasks/LJ-1-552/` does not exist here and
`git log --all -- 'agents/tasks/LJ-1-552*'` is empty. My clause says a module
hypothesis taken from a predecessor is the type that predecessor delivered; I
took none, so the clause binds nothing here. **If `[LJ-1.552]` returned an
assignment whose graph is NOT an L-element, point 1 is the whole of what its
successor can do.**

**3. THE TRIANGLE HAS A MISSING SIDE AND IT IS NAMED.**
`GenericGraph → GenericConstructible` is NOT built and I do not claim it, because
`IsGraphOf δ s G` constrains only the PAIR members of `G`, so a witness may carry
other members and need not be `grV δ s` on the nose
(`Probe554.agda:325-329`). Nothing in this report spends that arrow.

**4. WHAT WOULD REOPEN THIS.** One term of the shape `⟨ isL a ⟩ → Empty.⊥`, for
any `a`. The tree has none today, count 0. Anything that lands one makes
`no-generic-link` a live target again, and the same term would settle
`[LJ-1.414]`, `[LJ-1.441]` and `[LJ-1.526]` at the same time.

**5. THE ROUTE THIS DOES NOT KILL.** Nothing here says B10 is unreachable. It says
B10 is not reachable THROUGH an ambient assignment produced without its graph.
`archive/dev/LJ-dispatch-index.md:207` records that `[LJ-1.131]` once priced the
V = L route against the ambient one at "760 TO 1,320" and that `[LJ-1.136]`
superseded it on price. I did not re-price either and I do not recommend either:
that is a mathematician's call.

## W2 AND W4, ANSWERED

**W2 (from DD4).** The probe is generic in `ℓ`, generic in `δ` and `κ`, and
generic in the assignment. No numeral, no fixed ordinal, and no named site
appears anywhere in it. `LinkFo` (`Probe554.agda:228-230`) is written once at an
arbitrary `G : S` and every consumer instantiates it. The mathematics is written
at the generic carrier and there is nothing to instantiate twice. No deadline
conflict arose.

**W4 (from DD13).** No module was retired and none is proposed for retirement.
The probe lands nothing in `src/`, so `dev/ARCHIVE.md` gains no row. The ideal
form of this file written fresh today is the file as it stands: it was written in
five stages, each typechecked before the next, and no stage was rewritten.

## MEASUREMENTS

Caliber `-A64m -I0 -M8g`, read off the pane, never set by me. One Agda process at
a time. No heap event and no WALL.

| run | what | real | peak RSS | rc |
|---|---|---|---|---|
| `runs/w3-1.out` | the W3 slice ALONE, TYPE ONLY, interface deleted first | 0.76 s | 0.27 GB | 0 |
| `runs/w3-2.out` | same | 0.77 s | 0.27 GB | 0 |
| `runs/w3-3.out` | same | 0.75 s | 0.27 GB | 0 |
| cold | stage A, building `LJ-1-549.Probe549`, `LJ-1-546.Probe546`, `L.CodedShift`, `L.Absorption` | 7.14 s | not captured | 0 |
| `runs/final-1.out` | the FINAL file, interface deleted first, dependencies warm | 1.93 s | 0.44 GB | 0 |
| `runs/final-2.out` | same | 1.93 s | 0.44 GB | 0 |
| `runs/final-3.out` | same | 1.94 s | 0.44 GB | 0 |

`_build/2.8.0/agda/agents/tasks/LJ-1-554/Probe554.agdai` was deleted before each
of the three final runs, so each measures this file's own elaboration against warm
dependencies. Each `final-*.out` carries the file's `sha256`,
`f34de03e4b28958077209dbe424270f648bd58a15d63729d326a19dbafc3b464`. No run reports
an error, an unsolved metavariable or a hole.

**THE FILE.** `Probe554.agda`, 431 lines, 382 non-blank, **185 code lines**
(non-blank and not a comment), of which 30 are the import and open block. The rest
is comment, because a stop's value is in what it says about the tree.

**THE GATES, RUN INDIVIDUALLY AS THE BOUNDARY ASKS.** Reported in
`## THE GATES` below. All clean.

## ESTIMATE AGAINST MEASURED

| item | brief's estimate | measured |
|---|---|---|
| the probe | about 120 lines, obligation about 30 | 431 lines, 185 code lines, obligation NOT written |
| W3 | about 12 lines, under 60 s | 69 lines, 22 code lines, 0.76 s |
| the obligation | GO or a refutation | NEITHER, and the reason is a type argument |

**THE COMPARABLE WAS SOUND ABOUT SHAPE AND WRONG ABOUT THE ANSWER.**
`[LJ-1.533]` made a type argument of this kind and this file is of that shape.
What the estimate could not price is that the type argument here lands on an
INDEPENDENT statement rather than a false one, which costs both directions of an
equivalence instead of one refutation.

## WHAT I DID NOT DO

- I did not inhabit `no-generic-link`, and I did not inhabit the generic `Link`.
- I did not build `s`, and I did not discharge B10.
- I did not import a cardinality fact and I did not postulate one.
- I did not build `GenericGraph → GenericConstructible`. See point 3 above.
- I did not touch `src/`, and I added no axiom and no module parameter that
  asserts a missing input. `GenericLink`, `GenericGraph` and
  `GenericConstructible` appear ONLY as hypotheses of reductions.
- I did not re-price the V = L route or the ambient one.
- I did not commit and I did not push.

## THE GATES

`AGENTS.md:12` says to run every `python3` command as `.venv/bin/python`. **This
worktree has no `.venv`.** I used the main checkout's pinned interpreter,
`/Users/alsg/Agentic/Bedrock/.venv/bin/python`, with this worktree as the working
directory. I installed nothing and I created no venv here. `[LJ-1.533]` declared
the same departure for the same reason.

**ALL CLEAN, EACH RUN INDIVIDUALLY.**

| gate | result |
|---|---|
| `lint-prose --check` | rc 0 |
| `lint-agda --check` | rc 0 |
| `check-probes --check` | rc 0, "clean (6315 tracked files, no probe outside agents/tasks/ and no generated file)" |
| `check-closure --check closure` | rc 0, "clean (102 masters; closure, archive)" |
| `check-fences --check` | rc 0, "clean (102 masters, run threshold 3)" |
| `check-spec-surface --check` | rc 0, "clean (8 surface file(s), 201 declaration(s), 7 guarded rule home(s), 499 in-fence lines)" |
| `check-glossary --check` | rc 0 |
| `check-rule-ids` | rc 0, "clean (56 files, 165 lessons, 68 decisions, dev/rules.toml)" |
| `ledger --check` | rc 0, "declaration clean; standing 33,523 lines measured over 100 masters" |
| `weave-i18n --check` | rc 0 |
| `reuse lint` | compliant, 6129 / 6129 files |

**I DID NOT RUN `make typecheck`.** It checks `src/Everything.lagda.md` and this
task changed no file under `src/`.

**`_build` NEEDS NO NEW MANIFEST ROW.** The only files this task created there are
Agda interfaces under `_build/2.8.0/`, and `dev/build-manifest.toml:117-118`
already declares the glob `2.8.0/**`.

## ARCHIVE USED

- `archive/dev/LJ-dispatch-index.md`: **READ AND USED.** `:384` is
  "| LJ-1.329 | Code ONE ambient function as a member of an L-set | WRONG-OBJECT. THERE IS NO SUCH OBJECT | pullOrder wants a TOTAL MAP OUT of sq, not a point of it. The convergence was on a NAME |",
  and it is the second neighbour in `## THE SWEEP (C-42)`: I checked it against
  the shape and excluded it. `:207` is
  "| LJ-1.131 | Price the V = L route against the ambient one | ROUTE A-PRIME, 760 TO 1,320 | The tree already owns the order; V=L buys its DOMAIN. Superseded on price by LJ-1.136 |",
  and it is point 5 of `## WHAT THE NEXT BRIEF SHOULD KNOW`.
- `archive/dev/JOURNAL.md`: **DECLINED.** `:1` is "# ARCHIVED 2026-08-20". The
  per-episode journal is retired in favour of `agents/tasks/<CODE>/`, and every
  predecessor this task needed was in those task directories, where I read it.
  Not used.
- `archive/dev/JOURNAL-archived.md`: **DECLINED.** `:1` is
  "# Archived journal: the retired route". B10 is on the live route. Not used.
- `archive/dev/ORCHESTRATION.md`: **DECLINED.** `:1` is
  "# ORCHESTRATION: the orchestrator's operating rules". It is the archived
  operating document of a flow the program replaced on 2026-08-18. This task
  needed no operating rule that the five-file preamble does not carry. Not used.
- `archive/dev/DD-archived.md`: **DECLINED.** `:1` is
  "# THE `DD` RULING SERIES, archived in full 2026-08-18". No `DD` number is
  cited anywhere in this task. Not used.
- `dev/ARCHIVE.md`: **DECLINED.** It is the registry of retired MODULES and this
  task retires none, so it has no row to give and gains none. Not used.

## LITERATURE USED

- `dev/literature/truncation-and-selection.md`: **READ AND USED.** `:143` is
  "the reason: \"a proposition-valued goal absorbs the truncation\"", which is
  the rule that makes three eliminations in this task legal: `Reading-isProp`
  in the W3 slice (`runs/W3.agda:59-60`), `lout` in `graph→link`
  (`Probe554.agda:251-265`), and `gout` in `grL-isGraph` (`:294-305`). Each
  eliminates a truncated satisfaction into a path in a set.
- `dev/literature/devlin-II5.md`: **READ AND USED.** `:159` is
  "> 5.6 Theorem. V = L implies GCH.". It is the source's own record that this
  family of questions is decided by `V = L` and not by a count, which is what
  `## D-10` measures inside the tree and what
  `dev/memos/2026-08-16-pause.md:515-518` records about this exact crossing.
- `dev/literature/geology.md`: **READ AND USED, WITH A NARROW BEARING.** `:5` is
  "for mantle, grounds, Hamkins, Usuba, Laver, approximation across all 13,645",
  the record that the in-repo primary corpus had ZERO hits for the forcing and
  ground-model vocabulary. That is the measured reason the tree cannot exhibit
  the Levy collapse that `dev/memos/2026-08-16-pause.md:517` names as the side
  on which this crossing is FALSE. **I claim nothing more from it**: the dossier
  is about ground models of set-forcing extensions, not about `V = L`, and no
  step of the probe rests on it.
- `dev/literature/digest.md`: **DECLINED.** `:1` is
  "# Digest: the orthodox form of the rud route, pinned from the collected literature".
  It pins the rud route. Nothing in this task touches a rud term. Not used.
- `dev/literature/terms-2026-08.md`: **DECLINED.** `:1` is
  "# The terminology dossier: fourteen renderings for the owner's ruling".
  It is translation provenance for a glossary ruling. This task names no new
  term and adds no glossary entry. Not used.

