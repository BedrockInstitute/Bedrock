# LJ-1.598 report: clause (i) of the level-hood certificate, in a frame under the cap

## HEAD
head_slot: coder
machine: shared
verdict: NO-GO on `defines-level`; the clause is priced by two landed reductions, and its index hypothesis is wrong for every level formula the tree has

Written as a skeleton before any Agda beyond W3 and filled as each answer landed
(C-22). No commit, no push. I wrote only inside `agents/tasks/LJ-1-598/`. Agda
ran under the caliber the program set on this pane, `GHCRTS="-A64m -I0 -M2g"`,
ONE Agda process at a time. I did not set `GHCRTS`. Nothing is postulated, the
probe carries `--safe`, the final probe is green and carries no hole, and
nothing lands in `src/`. The probe is a raw `.agda` file, so it carries no
` ```agda ` fence, counts 0 in-fence lines, and the ratio bar cannot fire on it.

**A HEAP WALL WAS HIT AND ROUTED AROUND IN THIS DISPATCH, NOT PARKED.** The
first floor run walled inside the import chain (`runs/floor-1.out`, exit 251).
The restructure the standing clause orders was built and tested under the same
cap: the chain was elaborated module by module and the probe was cut to
`src/`-only imports. The final probe is green at 3.07 s and 696,614,912 bytes
peak (`runs/p-final.out`), a forced recheck of the delivered file.

## VERDICT

**THE OBLIGATION IS NOT INHABITED.** The meter says so:
`agents/tasks/LJ-1-598/Probe598.agda::defines-level` returns
`missing exit=42 ... [NotInScope]`, `1 UNRESOLVED of 1`, `probe_red=False`
(witness run, 2.27 s). The stop is stated at
`agents/tasks/LJ-1-598/review-of-defines-level.md`.

**THE PROBE IS GREEN AND ALL SIXTEEN DECLARED NAMES LAND** (`runs/p-final.out`,
`EXIT=0`, forced recheck of the delivered file, 3.07 s). Every one of the
sixteen was metered by name and returns `pass`, 2.33 s to 2.57 s per run:

| what | `Probe598.agda` | conditional on |
|---|---|---|
| W3, uniqueness alone, TYPE | `:87` | nothing |
| W3 is VACUOUSLY inhabited: the conjunct alone is free | `:104` | nothing |
| clause (i) restated text for text from `[LJ-1.578]` | `:118` | nothing |
| the body identity: `Body` is clause (i) per code | `:134` | nothing |
| the equation formula and its two readings | `:157`, `:160`, `:163` | nothing |
| clause (i) from a NAMED level | `:171` | `CodedLevels` (`:167`) |
| clause (i) at an ordinal-valued code from a graph formula | `:220` | `Det` and `Wit` (`:209`, `:213`) |
| clause (i) from the graph route plus the index bridge | `:261` | `Det`, `Wit`, `PreimageOrd` (`:257`) |

**WHY THE NAME IS ABSENT, IN THREE SENTENCES.** Every route to a formula that
uniquely defines `Lset δ` at the stage's inner world needs one of two things
the tree does not have: a code naming the level (section 3, circular for the
certificate, because that is Fact A's own conclusion), or a level formula read
at the stage with determination at an ORDINAL index (section 4, which is
`GraphAgree` plus `Lset-only` at the inner world, marked "not built anywhere"
by `[LJ-1.578]` at `lj-1.578-report.md:96-100`). And the type as stated does
not even give the ordinal index: it hypothesizes `IsOrd` of the COLLAPSE of
the index, and at a non-ordinal index the tree's own graph formula is
satisfied by a set that is not the level there (section D-10 below). So no
term of the stated type can be built from the delivered machinery, and the
two reductions plus the bridge type are what this dispatch delivers instead.

## THE FLOOR

**THE FIRST FLOOR WALLS, AND THE WALL IS THE IMPORT FRAME.** The brief ordered
`defines-level` stated with a hole in the smallest import set that holds it.
The smallest import set I first tried was `[LJ-1.578]` itself, because the
obligation names that probe's own type. `runs/FLOOR.agda` is that slice:
the frame, the import `LJ-1-578.Probe578`, and the obligation with a hole.
It exhausted the cap while the import chain was still elaborating:
`runs/floor-1.out`, **exit 251 at 57.90 s, peak 1,907,834,880 bytes**, with
`agda: Heap exhausted; Current maximum heap size is 2147483648 bytes`, the
last module under check being `LJ-1-570.Probe570`.

**THE RESTRUCTURE, TESTED UNDER THE SAME CAP.** The chain was elaborated one
module per Agda process, so no process holds two probe elaborations at once:
`runs/chain-550.out` 2.70 s and 764,854,272 bytes, `runs/chain-558.out`
1.41 s, `runs/chain-564.out` 2.76 s, `runs/chain-570.out` 2.84 s, all exit 0.
Then `[LJ-1.578]`'s OWN FILE walled on its own account with every dependency
interface warm: `runs/chain-578.out`, **exit 251 at 15.92 s, peak
1,901,936,640 bytes**. **So the certificate's own statement file cannot be
checked under the standing wide cap at all.** That is a fact about the frame,
not about clause (i), and it is the same fact `[LJ-1.541]` and `[LJ-1.547]`
measured on other obligations (my standing clause, from
`dev/pod/instructions/coder.md`): every partial pulled in facts its own rows
did not use.

**THE TRIMMED FLOOR, MEASURED.** The probe was cut to `src/`-only imports and
clause (i) taken by RESTATEMENT (section 2 of the probe, with the reason in
its comment). `runs/FLOOR2.agda` states `defines-level` with a hole in that
trimmed frame: **2.48 s, peak 723,271,680 bytes, exit 42 with
`[UnsolvedInteractionMetas]` at the one designed hole** (`runs/floor2-1.out`).
**The floor is 0.35 GiB against the 2 GiB cap. The statement costs nothing;
the frame was the whole cost.**

**THE FINISHED PROBE.** The final probe is green with the sixteen names above:
forced recheck of the delivered file `runs/p-final.out`, **3.07 s, peak
696,614,912 bytes**.
Three forced rechecks of the version without section 1's vacuity term gave
2.77 s, 2.63 s, 2.62 s (`runs/p-2-forced.out` to `runs/p-4-forced.out`), each
carrying its own `Checking` line, so the number is a recheck and not an
interface reuse. `runs/p-1.out` (exit 42) and `runs/p-2.out` (exit 0, 2.70 s)
are the two runs of the first full draft, kept: `p-1` is a path direction
error in `graph-gives-level`'s uniqueness composition, fixed in `p-2`.
`runs/p-5.out` (3.06 s) is the first green run of the final version. Every
run in `runs/` carries its caliber line `GHCRTS=[-A64m -I0 -M2g]`.

## THE FORMULA AND ITS UNIQUENESS

**TWO FORMULAS, BOTH LANDED, AND EACH NAMES ITS OWN PRICE.**

**THE EQUATION FORMULA** (`Probe598.agda:157`): `eqF d = var zero ≐ con d`.
Uniqueness is FREE and this is not a trick of the site: equality at the
restricted structure is path equality on the projections
(`src/FOL/ZFStructure.lagda.md:148` on top of `:82`), so a satisfied equation
IS the wanted path, and `eq-uniq d a h = h` typechecks as such (`:163`).
Existence is free at the code's own value (`eq-sat`, `:160`). **So the whole
price of this route is one hypothesis: a code `d` with
`fst (T.val d) ≡ Lset (fst (T.val c))`.** That hypothesis is `CodedLevels`
(`:167`), `coded-gives-level` (`:171`) buys clause (i) from it outright, and
`clause-i-from-body` (`:134`) is the identity that says the body is clause (i).
**THE ROUTE IS CIRCULAR FOR THE CERTIFICATE AND THE PROBE SAYS SO IN ITS OWN
COMMENT**: a code naming `Lset δ` is `Facts.HasLevels`'s conclusion
(`agents/tasks/LJ-1-578/Probe578.agda:120-122`), which clause (i) exists to
buy through `cert-gives-A` (`:254-273`). What the term measures is that
NOTHING ELSE is owed on this route: not one line of syntax beyond the code.

**THE GRAPH FORMULA** (`inF`, `Probe598.agda:217`):
`inF ψ c = ∃̇ (ψ ∧̇ (var zero ≐ con c))`, with `ψ` a two-slot formula over
codes, INDEX in slot 0 and VALUE in slot 1. **This answers the one open
question `[LJ-1.595]` left**: whether clause (i) needs "the index substituted
by a constant, a renaming this task did not price"
(`agents/tasks/LJ-1-595/review-of-defines-cover.md`, item 2 of "THE TWO
THINGS THE NEXT BRIEF SHOULD DECIDE"). It does not. Binding the index with
the existential and equating it with the code needs no renaming and no
substitution, the same shape `Shared` used for clause (ii)
(`agents/tasks/LJ-1-595/Probe595.agda:495`). **Uniqueness then costs exactly
`Det`** (`:209`): every satisfaction of `ψ` at an ORDINAL index pins the value
to the tower. That is the inner-world reading of what `Lset-only` proves at
the class `L` (`src/L/Hierarchy.lagda.md:334-337`, demanding `IsOrd` of the
argument at `:334-335`), and `ride-only` is that same lemma re-exported
(`src/L/Condensation.lagda.md:422`, `:425`). **Existence costs exactly
`Wit`** (`:213`): the formula is satisfied at every ordinal of the inner
world. Neither is built anywhere: `GraphAgree`, the bounded-to-machine
transfer that would carry them to the stage, is a HYPOTHESIS in
`[LJ-1.570]` (`agents/tasks/LJ-1-570/Probe570.agda:289`) and its parts are
"terms in five probes, none in `src/`" (`lj-1.570-report.md:96-100`).
`graph-gives-level` (`:220`) is the implication in full, at every
ordinal-valued code, and `preimage-gives-level` (`:261`) composes it with the
index bridge below.

**UNIQUENESS IS THE HARD HALF, AND THE BRIEF'S SPLIT OF IT IS WRONG BY ONE
CONJUNCT.** The brief named "uniqueness, not existence" as the widest
unmeasured term. W3 measured the uniqueness conjunct ALONE and it is FREE BY
VACUITY: an unsatisfiable formula is vacuously unique, satisfaction of `⊥̇`
is the algebra's `⊥` (`src/FOL/Semantics.lagda.md:99`), and `⟨ ⊥ ⟩` is
`⊥*` (`src/Base/Truth.lagda.md:121`), so `only-level-vacuous` (`:104`)
inhabits the W3 type for every code. The content of clause (i) is uniqueness
UNDER A SATISFIABLE formula, which is the conjunction and not the conjunct.
The brief's W3 estimate ("about 15 lines") was right for the type and wrong
for the difficulty.

## D-10, BEFORE ANY AGDA: THE INDEX HYPOTHESIS IS WRONG FOR THE TREE'S FORMULA

**THE TARGET AS STATED.** `Cert.DefinesLevel` hypothesizes
`IsOrd (HS.C.π (fst (T.val c)))`, the ordinal-hood of the COLLAPSE of the
code's value, and concludes `fst a ≡ Lset (fst (T.val c))`, at the value
itself (`agents/tasks/LJ-1-578/Probe578.agda:236-240`).

**EVERY DELIVERED DETERMINATION DEMANDS THE INDEX'S OWN ORDINAL-HOOD.**
`Lset-only` (`src/L/Hierarchy.lagda.md:334-335`) and `ride-only`
(`src/L/Condensation.lagda.md:422`) both take `IsOrd` of the argument. Devlin
is the same: his (b), the brief's own premise 4
(`dev/literature/devlin-II5.md:99`), is
`(∀γ < α)(∀v)[v = L_γ ↔ ...]`, and `γ < α` ranges over ORDINALS.

**AT A NON-ORDINAL INDEX THE TREE'S GRAPH GIVES THE WRONG SET, AND HERE IS
THE READING.** This is a reading of two definitions and not a machine-checked
term; it is short enough to check by eye. Take `δ = {{∅}}`. An approximation
`f` on `δ` is defined exactly on the members of `δ`, so on `{{∅}}`'s one
member `{∅}` (`ApproxAt` is `domAt`, `src/L/Coding/Sequence.lagda.md:286`).
The step at an argument collects only over records whose argument is a MEMBER
of that argument (`StepOf`, `src/L/Coding/Sequence.lagda.md:126-131`), so the
step condition forces the record at `{∅}` to be `∅`, because `{∅}`'s one
member `∅` is not in `f`'s domain. The graph's value at `δ` then collects
over the records at members of `δ`: one record, value `∅`, so the value is
`𝒟ₒ ∅ = {∅}`, the ordinal `1`. The tower's own value at `δ` is
`Lset δ = ⋃_{τ ∈ δ} 𝒟ₒ (Lset τ)` (`Lset-compute`,
`src/L/Constructible.lagda.md:227`), which is
`𝒟ₒ (𝒟ₒ ∅) = {∅, {∅}}`, the ordinal `2`. **Graph value `1`, tower value
`2`.** And `δ = {{∅}}` is a code value in every hull: it is the unique
satisfier of a closed formula over the code algebra, and the algebra's
`search` lands unique satisfiers (`src/L/Hull.lagda.md:79-90`); its collapse
is `{π {∅}} = {∅} = 1` whenever `∅` is in the hull, and `∅` always is,
because the algebra's junk value is `∅` (`src/L/Hull.lagda.md:90`). So the
hypothesis of clause (i) holds at such a code, and the tree's graph formula
answers with a set that is not the level. **The natural supplier cannot meet
the type at the codes the type admits, and no repair of the READING closes
that gap.**

**WHAT THE GAP LEAVES OPEN, STATED AS A TYPE.** `PreimageOrd`
(`Probe598.agda:257`) is the bridge from the type's hypothesis to the index
every determination needs. It is not built anywhere, and I did not try to
build it: a term of that type would have to show that a code whose collapse
is an ordinal has an ordinal value, and the hull gives no route to that which
I could see. **THE CORRECTED TARGET for the next brief is clause (i) with
`IsOrd (fst (T.val c))` in the hypothesis**, which matches `Lset-only`'s own
demand and makes section 4's reduction the whole residue. The correction
lands on the certificate's other preindex statements too (C-42 below).

## W3, THE WIDEST UNMEASURED TERM

**GO, AND THE ANSWER CORRECTS THE QUESTION.** The slice is
`agents/tasks/LJ-1-598/runs/W3.agda` (57 lines, 31 code lines including the
frame and imports; the type itself is 5), written first
and typechecked alone: `runs/w3-1.out` is exit 42 at 2.56 s, a conjunct I
dropped from my own telescope when I wrote the slice, kept as the record of
the failure; `runs/w3-2.out` is **exit 0 at 2.82 s, peak 598,622,208 bytes**.
The type is `Probe598.agda:87` letter for letter. The brief estimated about
15 lines; the type is 5 and the slice that holds it is 31 code lines, most
of it the frame the type needs. **But the widest unmeasured term is not this
one**: the uniqueness conjunct alone is vacuously inhabited
(`only-level-vacuous`, `:104`), so the measurement moves the weight to the
conjunction, as `## THE FORMULA AND ITS UNIQUENESS` says.

## PRICE

**EVERY NUMBER IS MINE, MEASURED UNDER `GHCRTS=[-A64m -I0 -M2g]`, ONE AGDA
PROCESS PER RUN.** Non-blank non-comment lines counted by
`awk 'NF' file | grep -cv '^\s*--'`.

| what | lines | code lines | at `file:line` |
|---|---:|---:|---|
| the probe, whole | 264 | 103 | `Probe598.agda` |
| header and imports | 66 | 30 | `:1-66` |
| the frame | 10 | 3 | `:67-76` |
| S1 W3 and its vacuity | 31 | 8 | `:77-107` |
| S2 clause (i) taken by restatement | 31 | 12 | `:108-138` |
| S3 the equation route | 41 | 16 | `:139-179` |
| S4 the graph route | 62 | 24 | `:180-241` |
| S5 the index bridge | 23 | 5 | `:242-264` |
| W3 slice | 57 | 31 | `runs/W3.agda` |
| floor slices | 44, 60 | 24, 40 | `runs/FLOOR.agda`, `runs/FLOOR2.agda` |

| measurement | wall | peak RSS | basis |
|---|---:|---:|---|
| W3 alone, exit 0 | 2.82 s | 598,622,208 | `runs/w3-2.out` |
| floor, IMPORT frame | 57.90 s (WALL, exit 251) | 1,907,834,880 | `runs/floor-1.out` |
| `[LJ-1.578]` checked alone, deps warm | 15.92 s (WALL, exit 251) | 1,901,936,640 | `runs/chain-578.out` |
| chain modules one per process | 2.70, 1.41, 2.76, 2.84 s | at most 795,279,360 | `runs/chain-*.out` |
| floor, TRIMMED frame, hole | 2.48 s | 723,271,680 | `runs/floor2-1.out` |
| final probe, forced recheck of the delivered file | 3.07 s | 696,614,912 | `runs/p-final.out` |
| name meter, one name | 2.25 to 2.57 s | not taken | witness runs, sixteen names |

**THE ESTIMATE WAS ABOUT 200 LINES WITH ABOUT 50 FOR THE OBLIGATION.** The
file is 264 lines and 103 code lines, and the obligation is absent: the two
reductions that PRICE it are 45 code lines (`:139-179` and `:180-264`). The
overrun against 200 is comments, and the probe's own header says why: the
restructure and the D-10 reading are part of the deliverable. **The heap, not
the line count, was the risk, exactly as the brief said, and the floor
measurement is what found it: the import frame walls, the trimmed frame costs
2.48 s.**

**NOTHING IN `runs/` IS UNEXPLAINED.** `w3-1` (exit 42, my dropped conjunct),
`p-1` (exit 42, one path direction), `p-2` (exit 0, first green full draft),
`p-2-forced` to `p-4-forced` (forced rechecks of the pre-vacuity version),
`p-5` and `p-6-forced` (green runs of the version with the vacuity term),
`p-final` (the forced recheck of the delivered file, after the last comment
correction), `floor-1` (the wall), `floor2-1` (the trimmed floor),
`chain-550/558/564/570/578` (the module-by-module chain). Every `.out`
carries `GHCRTS=`, a start stamp, an end stamp and `EXIT=`.

## C-42, THE SWEEP

The stop names one site: clause (i)'s index hypothesis. The shape swept for
is "concludes at `Lset` of an index while hypothesizing only the COLLAPSE's
ordinal-hood". The command is
`grep -rn "IsOrd (HS.C.π" agents/ src/`, plus a manual pass over each hit's
conclusion.

| site | statement | at `file:line` |
|---|---|---|
| 1 | `Facts.HasLevels` | `agents/tasks/LJ-1-578/Probe578.agda:120-122` |
| 2 | `Facts.LevelsCommute` | `:126-128` |
| 3 | `Cert.DefinesLevel`, clause (i) | `:236-240` |
| 4 | `Cert.DefinesLevelAcross`, clause (iii) | `:503-510` |

**FOUR STATEMENTS IN ONE FILE AND NOTHING IN `src/`.** The other
`IsOrd (HS.C.π ...)` hits conclude ordinal-hood of a witness or discharge it
from an external one (`[LJ-1.595]`'s clause-(ii) family), and
`Facts.Covered` (`:131-136`) concludes only a MEMBERSHIP at `Lset γ`, which
`[LJ-1.595]` already showed is payable without the index being an ordinal
(`factC-from-hull`, `agents/tasks/LJ-1-595/Probe595.agda:439`). **So the cure
the next brief should price is one edit to four statements in one file, or
the `PreimageOrd` bridge, and not a sweep of the tree.**

## W2, THE GENERIC CARRIER

**Nothing is written twice and nothing needed a second instantiation.** The
probe's one frame is `[LJ-1.578]`'s own `HullStage` frame, and both routes are
stated at it once. The equation route's content is generic already: `eqF`,
`eq-sat` and `eq-uniq` live in the code algebra's own terms and use nothing
of this hull beyond `val`, and `TermAlgebra` is the generic carrier
(`src/L/Hull.lagda.md:47`). The graph route is parametric in `ψ`, so the two
probes' matrix (`[LJ-1.595]`'s `Shared`) and this task's `Det`/`Wit` can
share one formula when one is built. No deadline forced a fixed form and
there is no conflict to report.

## W4, AND P-l

W4: not applicable. No module was retired, nothing under `src/` changed, and
`dev/ARCHIVE.md` takes no row from this task.

P-l: obeyed and not re-measured. No type in the probe names a stage
presentation: `OnlyLevel`, `ClauseI`, `Body`, `Det`, `Wit`, `CodedLevels` and
`PreimageOrd` quantify over codes, `SL` and `S`, and `⟪ Lset lam ⟫` appears
nowhere in the probe.

## WHAT THE SHAPE RESISTED

- **What it cost.** 103 code lines for a green probe that prices the whole
  clause, 3.07 s and 696,614,912 bytes at the final forced recheck, and one
  routed-around heap wall whose cure (module-per-process elaboration,
  `src/`-only imports) is now measured at this site.
- **What the shape resisted.** One thing only, and it is the finding: the
  distance between `IsOrd (π δ)` and `IsOrd δ`. Everything else assembled on
  the first attempt (`p-2` after one path direction error in `p-1`), which
  matches `[LJ-1.578]`'s own "almost nothing resisted": the plumbing fits,
  the formula's meaning is the cost.
- **What I had to weaken.** Nothing. No term assumes an unbuilt statement as
  a premise except the two reductions, whose hypotheses are NAMED TYPES
  (`CodedLevels`, `Det`, `Wit`, `PreimageOrd`) and not hidden postulates, and
  the obligation itself is absent rather than faked.
- **What I could not close.** `Det` and `Wit` at any `ψ` (that is
  `GraphAgree` plus the stage reading of `Lset-only`), `CodedLevels` (that is
  Fact A), and `PreimageOrd`. The brief forbade clauses (ii) and (iii) and
  neither was attempted.

## WHAT THE NEXT BRIEF NEEDS

1. **DECIDE THE INDEX BEFORE FUNDING ANY SUPPLIER.** Either restate clause
   (i) (and Fact A, Fact B, clause (iii)) at `IsOrd (fst (T.val c))`, which
   makes `graph-gives-level` the exact shape of the residue, or fund
   `PreimageOrd` knowing the graph gives a non-level at non-ordinal indices
   and no reading repair closes that.
2. **THE SUPPLIER'S FRAME CANNOT BE THE IMPORT FRAME.** `[LJ-1.578]`'s own
   file walls under the standing wide cap with warm dependencies
   (`runs/chain-578.out`). A supplier task must either take its clause by
   restatement, as this probe does, or the program must set the heavy tier.
   `[LJ-1.582]`'s wall is consistent with this measurement and is now
   PARTLY EXPLAINED by it: any frame that imported the certificate inherited
   a floor above the wide cap.
3. **THE ONE FORMULA TO BUILD IS TWO-SLOT, INDEX AT 0, VALUE AT 1.** With
   `Det` and `Wit` at that `ψ`, clause (i) at ordinal codes is section 4 of
   this probe, 24 code lines, already written. `[LJ-1.595]`'s substitution
   worry is void (`inF` binds and equates).
4. **DO NOT FUND UNIQUENESS ALONE.** It is vacuous (`only-level-vacuous`).
   Fund uniqueness under a satisfiable formula, which is the conjunction.
5. **A CODE PREMISE DID NOT RESOLVE.** The brief's premise 1 cites
   `dev/pod/transitions/2026-08.jsonl:3418` for the `[LJ-1.582]` park. That
   file has 157 lines in this worktree and no `LJ-1.582` row anywhere in it.
   The park is attested by the brief's own branch id
   `task-lj-1-582-heap-wall-park`, and `agents/tasks/LJ-1-582/` does not
   exist here, so nothing of that task was reused. The owner may want the
   citation repaired at the source.

## SCOPE

I wrote only inside `agents/tasks/LJ-1-598/`. Gates run:
`check-probes.py --check` clean (7421 tracked files), `lint-agda.py --check`
exit 0, `check-fences.py --check` clean. I did not run `make check`: I commit
nothing. No commit, no push.

## ARCHIVE USED

- `archive/dev/LJ-dispatch-index.md`: **READ, one row.** `:142` reads
  `| LJ-1.75 | Give each partial only the facts its rows use | 43 of 69; 122.45 s | Better than proportional: 41.6 pc cheaper for a 37.7 pc smaller telescope. Two partials plus composer, 273.88 s |`.
  TOOK the METHOD only (trim the frame to what the rows use), as the brief's
  premise 11 allows; **no number in this report is funded against that row**,
  and the restructure here was measured at its own site (`runs/floor-1.out`
  against `runs/floor2-1.out`), as the Boundary demands.
- `archive/dev/JOURNAL-archived.md`: **declined, not read beyond its first
  line.** `:1` reads `# Archived journal: the retired route`. A history, and
  nothing here needed one.
- `archive/dev/JOURNAL.md`: **declined, not read beyond its first line.**
  `:1` reads `# ARCHIVED 2026-08-20`. Same reason.
- `archive/dev/ORCHESTRATION.md`: **declined, not read beyond its first
  line.** `:1` reads `# ORCHESTRATION: the orchestrator's operating rules`.
  The live rules are the five files the program cats.
- `archive/dev/PLAN-archived.md`: **declined, not surveyed.** Its own header
  marks it archived and nothing current; no clause of this task rests on it.

## LITERATURE USED

- `dev/literature/devlin-II5.md`: **READ, and it decided the D-10 finding.**
  `:99` reads

      > (b) (∀γ < α)(∀v)[v = L_γ ↔ v ∈ L_α ∧ L_α ⊨ ∃z φ(z, v, γ)].

  Devlin's `γ` is an ORDINAL below `α`. The tree's clause (i) hypothesizes
  the collapse's ordinal-hood instead, which is what opened the index gap.
- `dev/literature/level-formula-slot-roles.md`: **READ, whole file.** `:9`
  reads

      arithmetic**, and a port that numbers its variables needs the slot arithmetic.

  TOOK the table's row 5, which fixes clause (i)'s free pair as VALUE and
  ORDINAL with the witness bound, and the law at section 2.2 that ONE bound
  binds all unbounded quantifiers. `inF` obeys both: one existential, the
  index equated and not bound a second time. `[LJ-1.595]`'s report asked the
  next brief to check its slot order against this file: its `Φ(z, v, γ)`
  order and this file's row 4 agree, and `Det`/`Wit` state the index in slot
  0 and the value in slot 1, which is row 5's free pair in binding order.
- `dev/literature/truncation-and-selection.md`: **READ, one line.** `:17`
  reads

      LEAST witness under a definable well-order, and all three write leastness with

  TOOK the reminder that the classical sources buy uniqueness by LEASTNESS
  under a definable order. Clause (i) demands uniqueness outright, and the
  hull's `search` already selects least witnesses
  (`src/L/Hull.lagda.md:79-81`), so a `ψ` built as "the least level at the
  index" would inherit both `Det` and `Wit` from one construction.
- `dev/literature/digest.md`: **not used.** `dev/literature/devlin-II5.md`
  carries the chain in full and the digest is the fetch record for it.
- `dev/literature/terms-2026-08.md`: **not used.** No naming question arose
  and no glossary entry is proposed.
