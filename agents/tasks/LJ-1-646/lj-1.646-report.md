# LJ-1.646 report: name Lset in the hull's language, at an ordinal code

slot: `coder`. Written early as a skeleton and filled as runs landed (C-22).
No commit, no push. I wrote only in `agents/tasks/LJ-1-646/`. Agda ran under
the caliber the program set on this pane, `GHCRTS="-A64m -I0 -M2g"`, the wide
caliber, ONE Agda process at a time. I did not set `GHCRTS`.

TARGET: build ONE term in `agents/tasks/LJ-1-646/Probe646.agda`:

    lset-code-ord : (c : Code) → IsOrd (fst (val c))
                  → Σ[ d ∈ Code ] (fst (val d) ≡ Lset (fst (val c)))

Land nothing in `src/`. I landed nothing in `src/`.

The standing direction (`dev/pod/direction.md:37`) says one SRC collection after
LJ-1, not after `[LJ-2.5]`. This task is LJ-1 work. It does not start that pass
and it does not start phase 3. No Boundary clause is in conflict.

## ADDENDUM OBEYED

The mid-pane rule from `pod-math`: a file that cannot typecheck takes
`.agda.txt`. My task home holds exactly ONE `.agda` file, `Probe646.agda`, and it
typechecks (`runs/final-0.out`, exit 0). The two shapes that walled are kept as
`runs/SHAPE-A-inline.agda.txt` and `runs/SHAPE-B-concrete.agda.txt`. The `.out`
and `.time` logs are unchanged.

## VERDICT

**NO-GO, stated.** The obligation term is not written. The probe is GREEN.
Witness meter: `1 UNRESOLVED of 1`, `probe_red=False` (`runs/witness.out:1-2`).
The NO-GO is stated in `agents/tasks/LJ-1-646/review-of-lset-code-ord.md`. That
file is the critic's input. It does not close the task.

This is NOT a refutation. I did not build a term of the negation, and the target
is plausible. It is an obstruction of the `wit`-at-`absFo LsetGraph` route, and
the obstruction is a GRADE fact, not a hypothesis fact.

## THE BRIEF'S THREE PREMISES, CHECKED

**PREMISE 2 IS HALF TRUE.** It says obstacle one "is already cleared and nobody
went back", citing `[LJ-1.474]`'s `lset-codes`. The TYPE is filled. The MEANING
is not, and `[LJ-1.474]` wrote that down itself:

> - It does not prove `fst (val (ck (tagOf s))) ≡ fst s`.

Basis: `agents/tasks/LJ-1-474/lj-1.474-report.md:253`. `⊨-abs`
(`src/FOL/Manipulation/Parameters.lagda.md:421-422`) reads the abstraction at
`γ ++ map ι (constantsFo φ)` and at nothing else, so a `Vec Code` of the right
LENGTH is not enough: its values must BE the constants. `[LJ-1.474]` says so at
`:271-273`: "A later brief that needs the values, not only the codes, must prove
the decoder, or replace it."

**PREMISE 3 IS WRONG.** It says obstacle two "is exactly this brief's added
hypothesis". `[LJ-1.474]` listed THREE facts the equality still needs, not two,
at `agents/tasks/LJ-1-474/lj-1.474-report.md:190-200`. The added `IsOrd` is its
fact 3. Its fact 1 is the decoder above. Its fact 2 is:

> 2. `Lset-only` at `src/L/Hierarchy.lagda.md:334-335` reads `wit`'s
>    satisfaction of `absFo LsetGraph`. `[LJ-1.462]` measured that this
>    meeting is unmeasured

Fact 2 is the real obstacle, and it is a CARRIER fact. `Lset-only` is stated at
the constructible-class carrier (`open hPropStructure 𝒮ʟ`,
`src/L/Hierarchy.lagda.md:73`, satisfaction from
`FOL.Absoluteness.Single 𝒮ᵥ isL isL-trans`, `:78-79`). `wit`'s satisfaction is
at the STAGE carrier (`src/L/Hull.lagda.md:153`, `:323`). `IsOrd` does not join
two carriers.

**AND `[LJ-1.642]` MEASURED THAT ONE TASK BEFORE THIS BRIEF WAS WRITTEN**
(`agents/tasks/LJ-1-642/lj-1.642-report.md:190-195`):

> Without a Levy certificate the stage-to-class transfer (`σ₁-up`,
> `src/FOL/Absoluteness.lagda.md:182-184`) does not apply, so no reading
> of a stage satisfaction reaches `Lset-only`

## THE THIRD OBSTACLE, WHICH IS WHAT NO-GO EARNS

**IT IS NOT THAT A LEVY CERTIFICATE FOR `LsetGraph` IS UNBUILT. IT IS THAT ONE
CANNOT EXIST.** The archive holds the machine-checked measurement:

> `LsetGraph` weighs 169,683 syntax nodes with
> 2,287 unbounded ∃̇ and 2,159 unbounded ∀̇ interleaved, so NO delivered transfer
> theorem applies and the crossing means re-instantiating a 6,219-line,
> 134-reading cone monomorphic in 𝒮ʟ

Basis: `archive/dev/JOURNAL-archived.md:631-634`.

`FOL.Absoluteness` delivers exactly three transfers and each asks for a Levy
certificate: `abs₀` for `Δ₀` (`src/FOL/Absoluteness.lagda.md:122`), `σ₁-up` for
`Σ₁` (`:182`), `π₁-down` for `Π₁` (`:187`). A formula with 2,287 unbounded
existentials interleaved with 2,159 unbounded universals is in none of the three
classes. So `feed` at `absFo LsetGraph` is dead at ANY hypothesis, and the
brief's "join of two delivered things" is not available at that vehicle.

**THE VEHICLE DEVLIN'S OWN LIST NAMES IS A Σ₀ MATRIX, AND THE TREE HAS ONE.**
`dev/literature/devlin-II5.md:224` states requirement 3:

> 3. Σ₀ absoluteness for the matrix: 1.9.15 moves L_α's (or M's) satisfaction

The tree's Σ₀ matrix for level-hood is `levelHoodB`
(`src/L/BoundedSubset.lagda.md:108`) with `Δ₀-levelHoodB` beside it (`:113`),
and the bounded graph it is built over is `GraphB.graphBndAt`
(`src/L/Condensation.lagda.md:2492-2493`) with `Δ₀-graphBndAt` (`:2495`). What
that matrix lacks is a READING. `levelHood` occurs in `src/` at TWELVE lines,
all inside `src/L/BoundedSubset.lagda.md`, and every one is a definition or a
Levy certificate. The delivered bounded-to-machine agreement arrows are FOUR and
all four are leaf rows: `extAtB→extAt` (`src/L/Condensation.lagda.md:2514`),
`extAt→extAtB` (`:2524`), `emptyB→emptyAt` (`:2724`), `emptyAt→emptyB`
(`:2729`). Nothing lifts the agreement to `approxBndAt`, `stepBndAt` or
`graphBndAt`. The chapter says the same in prose: "the level-hood instantiation
at the hull is the priced residue" (`src/L/BoundedSubset.lagda.md:901-902`).

## WHAT WAS BUILT, AND IT IS GREEN

All in `agents/tasks/LJ-1-646/Probe646.agda`, module
`LJ-1-646.Probe646 {ℓ} (lem)`, inside `HullStage` at the six slots copied from
`src/L/BoundedSubset.lagda.md:903-905`.

1. **`code-ord-mem`** (`:97-98`). An ordinal code's value is a member of `lam`,
   not only of `Lset lam`. One line, from `ord∈Lset→∈`
   (`src/L/Ordinal/Stages.lagda.md:265-268`). This closes the gap `[LJ-1.479]`
   stopped at: it asked for `IsOrd` FROM hull membership and found no source
   (`agents/tasks/LJ-1-479/lj-1.479-report.md:84-88`). The brief GIVES `IsOrd`,
   and the converse is then free.
2. **`Lset-code-in-stage`** (`:105-107`) and **`LsetAt`** (`:110-111`). The
   target VALUE lives in the stage carrier. **This is taken from `[LJ-1.642]`,
   not rebuilt**: `level-in-stage` is `agents/tasks/LJ-1-642/Probe642.agda:327-334`
   and `level-of-code-in-stage` is `:336-338`. I first rebuilt it, measured it
   green (`runs/step4-0.time`, 20.53 s), then replaced my copy by the import
   (`runs/step5-0.time`, 20.58 s), because a copy is a second measurement of one
   object.
3. **`Wit.wit-sat`** (`:123-127`). The value of a `wit` code satisfies the code's
   own formula, as soon as the stage has any witness. GENERIC in the formula.
   This is the whole of what `wit` gives, and it was not written anywhere before.
4. **`Reduce`** (`:136-168`). The obligation reduced to TWO residues, and the
   reduction typechecked: `join` at `:164-168`. Also
   `StageHolds` (`:156-158`) and `holds→sat` (`:160-161`), which restate residue one in Devlin's own shape:
   because `LsetAt` supplies the value, the debt is the WITNESS and not the
   value.
5. **`Feed646`** (`:172`) and **`feed≡`** (`:179-180`). The predecessor's
   instance named, and the identification MACHINE-CHECKED by `refl`: the code the
   reduction returns is `[LJ-1.474]`'s `feed`. Three separate module applications
   of `AtStage.Hull` at these six parameters, `[LJ-1.474]`'s copied telescope,
   `[LJ-1.642]`'s through `src` `HullStage`, and this file's, are ONE alphabet.
   That was a reading before this run and it is a fact now.

## THE TWO RESIDUES, NAMED

At `Feed646` these are the whole debt:

- **`StageSat` / `StageHolds`** (`Probe646.agda:142-143`, `:156-158`). The stage
  believes the packaged graph at the code. This is Devlin's requirement 2,
  "witnessed inside the carrier" (`dev/literature/devlin-II5.md:220-222`). Its
  value half is DELIVERED by item 2 above. Its witness half is `[LJ-1.642]`'s
  wall 4 and nothing in `src/` builds it.
- **`ReadOff`** (`Probe646.agda:148-151`). A stage witness of the packaged graph
  IS the tower. This is `Lset-only`'s conclusion asked at the stage carrier, and
  the grade measurement above says no transfer reaches it.

A THIRD residue sits under `StageSat` and `ReadOff` both, and it is
`[LJ-1.474]`'s fact 1: `vals lset-codes` is not proved to be the constant vector
of `LsetGraph`.

## W3, THE WIDEST UNMEASURED TERM

The brief names it: "Whether `Lset-only`'s `γ` and `lookup` slots line up with
`val` at a `Code` without a further translation", estimate 60 to 140 lines.

**NO-GO, and the question is answered by a CARRIER fact, not a slot fact.** The
slots do not line up and `lookup` is not why. `Lset-only`'s `γ : S ^ n` is over
the constructible-class carrier; `val`'s codomain is the stage carrier
(`src/L/Hull.lagda.md:88-91` at `AbsL.𝒮M`, `:323`). No `lookup` reindexing
crosses that.

**AND THE SLOT ORDER IS ALSO NOT ONE CONVENTION, WHICH THE NEXT BRIEF MUST
KNOW.** `LsetGraph = LsetGraphAt zero (suc zero)`
(`src/L/Coding/Sequence.lagda.md:354`), so the VALUE is slot 0 and the ORDINAL is
slot 1, and `feed` agrees because `wit` puts its witness at slot 0.
`[LJ-1.642]`'s `Det` and `Wit` put the ordinal at slot 0 and the value at slot 1
(`agents/tasks/LJ-1-642/Probe642.agda:91-97`). A bridge between the two
spellings must transpose. I did not build that bridge.

**THE PRICE THE BRIEF GUESSED IS NOT THE PRICE.** 60 to 140 lines is the price of
a translation. The measured price of the crossing is re-instantiating a
6,219-line, 134-reading cone monomorphic in `𝒮ʟ`
(`archive/dev/JOURNAL-archived.md:632-634`). I report the number the archive
measured, not the number the brief guessed, and I did not attempt the cone.

## W2 (DD4)

The rule: write the mathematics once at a generic carrier and instantiate it, so
both proofs share the maximum code. **Answered, and it is the load-bearing
decision of this probe.** Every row is generic: `Wit` is generic in the arity,
the formula and the code vector; `Reduce` is generic in the same three. The
graph enters ONCE, at the module application `Feed646` (`:171`). The module is
generic in `ℓ`, and `lam`, `X` and the stage hypotheses stay parameters of
`HullStage`. No ordinal is fixed and there is no second copy at a concrete stage.
No deadline conflict arose.

**AND W2 WAS NOT ONLY A RULE HERE, IT WAS THE CURE.** See the heap section.

## W4 (DD13)

Nothing was retired. No module moved to `archive/`. No fragment was deleted.

## THE HEAP WALL, AND THE RESTRUCTURE IN THE SAME DISPATCH

**TWO SHAPES WALLED AND THE THIRD IS GREEN. I did not report the wall as a
finding, because a restructuring cleared it.**

- **SHAPE A**, the read-off written inline at the concrete packaged graph, with
  the equality composed as `cong fst (val-wit ...) ∙ read ...`. Still running at
  5 minutes 01 seconds and 1,628,176 KB resident and climbing, then killed;
  `runs/step1-1.time` is empty because the process never reached
  `/usr/bin/time`'s report. Kept at
  `runs/SHAPE-A-inline.agda.txt`.
- **SHAPE B**, the same rows with the composition removed but the residues still
  stated at the concrete `Q.packaged`. Still running at 6 minutes 12 seconds
  with resident size pinned at 2,045,552 KB, at the `-M2g` ceiling and
  garbage-collecting rather than progressing, then killed. Kept at
  `runs/SHAPE-B-concrete.agda.txt`.
- **SHAPE C**, every row generic in the formula, the graph entering only through
  a module application. GREEN at 12.18 s and 1,835,958,272 bytes peak
  (`runs/step3-1.time`).

**THE CAUSE IS P-l AT ITS OWN SITE, AND THE MEASUREMENT IS NEW.** `dev/LESSONS.md`
P-l says naming a transparent construction in a statement's TYPE is what costs.
Here the construction is `absFo LsetGraph` and the type is `Sat k ψ vs`, which
unfolds to a satisfaction of it. Shape B put a 169,683-node formula under
`_⊨₀_` and the elaborator traversed it; shape C keeps `ψ` a variable, so the
formula is an atom and nothing unfolds. **The same file, the same obligation, the
same caliber: over 372 seconds and a wall, against 12.18 seconds.** The generic
row is not a style preference on this object. It is the difference between green
and a wall.

I did not rerun the same code hoping for a different result. Each of the three
shapes is a different file, and each was tested under the same caliber.

## PRICE

**EVERY NUMBER IS MINE, MEASURED UNDER `GHCRTS="-A64m -I0 -M2g"`, THE WIDE
CALIBER, ONE AGDA PROCESS PER RUN, WITH A WARM `src/` INTERFACE CACHE.**
`[LJ-1.642]`'s numbers were taken at `-M4g` and are NOT comparable with these.

| run | what | exit | seconds | peak bytes | log |
|---|---|---:|---:|---:|---|
| pred-474-0 | `[LJ-1.474]`'s probe, green in this tree | 0 | 6.09 | 1,128,611,840 | `runs/pred-474-0.time` |
| pred-642-0 | `[LJ-1.642]`'s probe, green in this tree | 0 | 3.30 | 639,991,808 | `runs/pred-642-0.time` |
| floor-0 | the frame, obligation as a type only | 0 | 2.90 | 519,798,784 | `runs/floor-0.time` |
| step1-1 | SHAPE A, killed | killed | over 301 | 1,628,176 KB rising | `runs/step1-1.time` (empty) |
| step1-2 | frame plus generic `Wit` | 0 | 2.78 | 592,281,600 | `runs/step1-2.time` |
| step3-0 | SHAPE B, killed at the ceiling | killed | over 372 | 2,045,552 KB pinned | `runs/step3-0.time` (empty) |
| step3-1 | SHAPE C, generic `Reduce` plus `Feed646` | 0 | 12.18 | 1,835,958,272 | `runs/step3-1.time` |
| step4-0 | plus the level in the stage, rebuilt | 0 | 20.53 | 2,332,966,912 | `runs/step4-0.time` |
| step5-0 | the same, imported from `[LJ-1.642]` | 0 | 20.58 | 2,375,122,944 | `runs/step5-0.time` |
| final-0 | plus `feed≡`, the whole file cold | 0 | 30.53 | 2,376,204,288 | `runs/final-0.time` |
| final-1 | the same file again | 0 | 2.84 | 592,953,344 | `runs/final-1.time` |

**`final-1` IS AN INTERFACE LOAD, NOT A SECOND ELABORATION.** The source did not
change after `final-0`, so Agda read the `.agdai` it had just written. The
honest elaboration cost of the whole file is **`final-0`, 30.53 s**. I state this
because a 2.84 s figure quoted as a recheck would be a number the evidence does
not give.

`feed≡` alone costs about 10 s of that: 30.53 s with it against 20.58 s without
(`runs/final-0.time` against `runs/step5-0.time`).

Probe size: **180 lines total, 76 non-blank non-comment lines**, counted
`awk 'NF' agents/tasks/LJ-1-646/Probe646.agda | grep -cv '^[[:space:]]*--'`.

**THE RATIO BAR CANNOT FIRE ON THIS RETURN.** The divisor is in-fence lines of
the write scope, counted inside ` ```agda ` fences. A raw `.agda` probe carries
no fence and counts 0, and this task's whole write scope is probe, report,
review and `runs/`. Nothing here is a `.lagda.md` master.

## WHAT THE NEXT BRIEF NEEDS

1. **DO NOT RE-DISPATCH `feed` AT `absFo LsetGraph`.** The grade wall is
   arithmetic, not effort: 2,287 unbounded `∃̇` and 2,159 unbounded `∀̇`
   (`archive/dev/JOURNAL-archived.md:631-632`). No added hypothesis moves it.
2. **THE OBJECT TO FUND IS A READING OF `levelHoodB`** at two slots, then its
   instantiation at the hull's code alphabet. `join` in this probe is generic in
   the formula, so it accepts a Σ₀ matrix on the same three lines. That is
   `[LJ-1.642]`'s wall 2 (the arity, the bound `K` as a fourth slot) and wall 3
   (the carrier slide) restated at the code level.
3. **THE VALUE HALF OF DEVLIN 2.6(ii) IS PAID AND SHOULD NOT BE RE-BOUGHT.**
   `LsetAt` gives the stage element outright, from `[LJ-1.642]`'s theorem. The
   open half is the witness `z`.
4. **`[LJ-1.474]`'s DECODER IS STILL OWED** if any route reads the abstraction
   back through `⊨-abs`: `fst (val (ck (tagOf s))) ≡ fst s`, unproved at
   `agents/tasks/LJ-1-474/lj-1.474-report.md:253`. A Σ₀ route that carries its
   parameters in slots rather than constants would not need it at all, and that
   is a reason to prefer one.
5. **THE SLOT ORDER DIFFERS between `LsetGraph`/`feed` and `[LJ-1.642]`'s
   `Det`/`Wit`.** Any bridge transposes. See W3 above.
6. **`[LJ-1.642]`'s D-10 FINDING STILL STANDS AND THIS TASK DID NOT SETTLE IT:**
   the frame admits `lam = ω`, and Devlin's clause (b) is stated at limit
   `α > ω` (`agents/tasks/LJ-1-642/lj-1.642-report.md:234-241`). My six slots are
   the same six.
7. **WRITE THE NEXT PROBE GENERIC IN THE FORMULA FROM LINE ONE.** Measured above:
   the concrete graph in a satisfaction type is a wall at this caliber, and the
   same content generic is 12 seconds.

C-42: this is not a refutation, so the sweep C-42 orders is not owed here. I did
not search the tree for a false shape, and I did not build a term of any
negation.

## ARCHIVE USED

- **`archive/dev/JOURNAL-archived.md`**: READ, and it carries this report's
  central measurement. `archive/dev/JOURNAL-archived.md:631` reads
  "machine-checked measurements: `LsetGraph` weighs 169,683 syntax nodes with".
- **`archive/dev/LJ-dispatch-index.md`**: READ, for the `levelIn` history that
  put this obligation on the route. `archive/dev/LJ-dispatch-index.md:101` reads
  "| LJ-1.52 | The level-hood adequacy at the hull | PINNED, not discharged | The chain is assembled and machine-checked. Three named leaves remain, each written as the term not written |".
- **`archive/dev/JOURNAL.md`**: READ, for why the level story must run through
  codes at all. `archive/dev/JOURNAL.md:410` reads
  "level-hood must run through codes and satisfaction, and those leaves are".
- **`dev/ARCHIVE.md`**: NOT READ, declined. I searched it for `lset-code`,
  `levelIn`, `LsetGraph`, `level-hood` and `levelHood` and it returned no line.
  It records what left the tree and why, and nothing in this task retires a
  module.
- **`archive/dev/ORCHESTRATION.md`**: NOT READ, declined. It is the archived loop
  document, superseded by the program. This task is one dispatch inside the
  program and takes no rule from it.

## LITERATURE USED

- **`dev/literature/devlin-II5.md`**: READ, and it settles the grade question.
  `dev/literature/devlin-II5.md:224` reads
  "3. Σ₀ absoluteness for the matrix: 1.9.15 moves L_α's (or M's) satisfaction".
  I also read `:220-222` for requirement 2, the witness inside the carrier.
- **`dev/literature/digest.md`**: NOT READ for this task, declined. It is the
  index over the literature, and `[LJ-1.642]` already spent its section 10 check
  on the same object one task ago (`agents/tasks/LJ-1-642/lj-1.642-report.md:252-262`).
  This task certifies NO leaf as bounded, so the false-Δ₀-claims inventory has
  nothing to bite on here.
- **`dev/literature/terms-2026-08.md`**: NOT READ, declined. It is terminology
  provenance. This task names no new term and adds no glossary entry.
- **`dev/literature/truncation-and-selection.md`**: NOT READ, declined. The one
  truncation in this probe is `Sat`'s own `∥_∥₁`, used and reintroduced with
  `∣_∣₁` in `holds→sat`, and no selection principle is spent anywhere.
- **`dev/literature/geology.md`**: NOT READ, declined. Set-theoretic geology is
  not on this route; the obligation is a hull code at a stage.
