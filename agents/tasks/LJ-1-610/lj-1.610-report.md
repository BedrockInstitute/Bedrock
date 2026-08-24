# LJ-1.610 report: face G+, the stage's inner world at the tower's own values

## HEAD
head_slot: coder
machine: shared
verdict: NO-GO on `graph-stage`; the face is priced by ONE landed reduction at an
ordinal-guarded machine-grade matrix, and the residue it names is the campaign's
oldest wall reached from a third side: the Sigma-one witness must live INSIDE the
stage, and the tree has no construction of it

Written as a skeleton before any Agda beyond W3 and filled as each answer
landed (C-22). No commit, no push. I wrote only inside
`agents/tasks/LJ-1-610/`. Agda ran under the caliber the program set on this
pane, `GHCRTS="-A64m -I0 -M2g"`, ONE Agda process at a time. I did not set
`GHCRTS`. Nothing is postulated, the probe carries `--safe`, the delivered
probe is green and carries no hole, and nothing lands in `src/`. The probe is
a raw `.agda` file, so it carries no ` ```agda ` fence, counts 0 in-fence
lines, and the ratio bar cannot fire on it.

**NO HEAP WALL WAS MET ANYWHERE IN THIS TASK.** The highest peak of any run is
849,887,232 bytes against the 2,147,483,648-byte cap (`runs/floor-1.out`), and
the longest run is 9.29 s against the caps I set (120 s for W3, 300 s for the
probe and the floor). The caps are WALL-CLOCK caps enforced by a perl alarm
(`runs/run.sh` carries the mechanism), because this macOS has no `timeout`
(`runs/w3-1.out`, exit 127, no Agda process started; the same absence is
recorded by `[LJ-1.602]`).

## W3, THE WIDEST UNMEASURED TERM

**GO, AND IT IS THE SIGMA-ONE CLOSURE ITSELF, EXACTLY AS THE BRIEF ORDERED IT
STATED.** The slice is `agents/tasks/LJ-1-610/runs/W3.agda` (106 lines, 55
code lines), written FIRST and typechecked ALONE: `runs/w3-11-final.out` is
**exit 0 at 3.38 s, peak 668,647,424 bytes**, under the two-minute cap. The
type is `Σ₁Closure` at `runs/W3.agda:103-106`: at every STAGE pair whose
value IS the tower's value at the index, the stage's inner world satisfies the
existential closure of the graph matrix, the witness inside the carrier. The
brief estimated about 15 lines; the type is 4 and the slice that holds it is
55 code lines, of which 22 are the CARRIER SLIDE (`numSL`, section 1), the
piece the brief's estimate could not have known about: the tree's graph
formulas do not live at the stage's carrier, and moving them there is a real
cost, recorded below as WALL 2. **The widest unmeasured term is therefore
measured: its STATEMENT costs 3.38 s and 0.62 GiB, plus a carrier slide nobody
had priced, and its weight is in the witness.**

## D-10, BEFORE ANY AGDA: THE LITERATURE STEP

**DEVLIN'S (b) SUPPLIES AN EQUIVALENCE AND ASSUMES ITS WITNESS.** The clause
is quoted in the digest at `dev/literature/devlin-II5.md:217-223`; at `:219`
it reads

> v = L_γ iff v ∈ L_α and L_α ⊨ ∃z φ(z, v, γ)

and at `:220-222` the digest says the forward half "needs the witnessing z to
live inside L_α; that is 2.6(ii), the sequence (L_δ | δ ≤ γ) ∈ L_α for
γ < α", with the strength clause at `:222`: **"the Σ₁ form is 'witnessed
inside the carrier', not merely in V."**

WHAT IT GIVES: at ORDINAL indices below the stage, level-hood is equivalent to
stage-satisfaction of the Sigma-one closure, and the witness can be taken in
the carrier, because 2.6(ii) hands over the initial segment of the tower as a
member of the stage.

WHAT IT ASSUMES AND LEAVES TO THE READER: (i) the index discipline
`(∀γ < α)` over ordinals, which the face's type does not carry (WALL 4
below); (ii) the sequence's CONSTRUCTION, cited from 2.6(ii) and not
re-proved, which is exactly the term the tree does not have (WALL 1); (iii)
that the stage's index is a limit above the witness's index, which the face's
six slots do not state. The errata carry NOTHING about (b): their Chapter II
entries are the amenability and Sat-uniformity errors at Devlin pp. 45, 65, 66
(`dev/literature/devlin-errata.md:125-142`), none touching 5.2 or II.2.7.

## THE `Adeq` SHAPE, AND WHY IT DOES NOT INSTANTIATE

`[LJ-1.570]`'s shape is at `agents/tasks/LJ-1-570/Probe570.agda:319-322`:

    Adeq : SL.S → Type (ℓ-suc ℓ)
    Adeq m =
      ∥ Σ[ K' ∈ SL.S ] Σ[ u' ∈ SL.S ] Σ[ v' ∈ SL.S ]
        (⟨ v' SL.∈ˢ K' ⟩ × ⟨ (u' ∷ v' ∷ m ∷ K' ∷ []) AbsL.⊨ᵐ LH0.matrix ⟩) ∥₁

WHAT IT DOES: it existentially closes the bound `K'`, the unused slot `u'`,
and the value `v'` over the four-slot bounded matrix, leaving the parameter
`m`, and it is stated at the CLASS carrier (`AbsL` there is
`FOL.Absoluteness.Single 𝒮ᵥ isL isL-trans`, `Probe570.agda:48-49`). It is the
witness-in-a-bound form of the same adequacy.

**IT DOES NOT INSTANTIATE AT G+'s FRAME, THREE WAYS, AND IT WAS NEVER
INHABITED ANYWAY.** (1) Carrier: `Adeq`'s inner world is the whole class `L`;
G+'s is the stage `Lset lam`. (2) Arity: `Adeq` reads a FOUR-slot matrix with
the bound as a variable; G+ demands `Formula CI.I.SM 3`, three slots and no
bound slot. (3) Currency: `[LJ-1.570]` built only the DECODERS
`matrix-decode` and `adeq-decode` (`Probe570.agda:300-335`), implications FROM
the shape; `Adeq` itself was never inhabited, and `[LJ-1.570]`'s report says
the bounded-to-machine transfer `GraphAgree` is a hypothesis there
(`agents/tasks/LJ-1-570/Probe570.agda:289`, echoed at
`agents/tasks/LJ-1-598/lj-1.598-report.md:138-140`). So the nearest built
thing is a decoder of a shape one carrier, one arity and one construction
away. **This task may be short only if the reader mistakes a decoder for a
witness; it is not.**

## THE OBLIGATION, STATED

**THE FACE, RESTATED LETTER FOR LETTER** (`agents/tasks/LJ-1-610/Probe610.agda`
`:177-180`, from `agents/tasks/LJ-1-606/Probe606.agda:156-159`, at `DR.SM` for
`CI.I.SM`: the two are judgmentally the same sigma over `H.T.Hull`,
`src/L/BoundedSubset.lagda.md:917-918` against `:167` and `:364-365`):

    GraphStage ψ =
      (q γ : SM) → fst q ≡ Lset (fst γ)
      → ⟨ map inL (q ∷ γ ∷ []) ⊨ᵐ mapFo inL (∃̇ ψ) ⟩

**IS IT INHABITED? NO.** `graph-stage` is deliberately absent from the probe;
the meter reports `missing exit=42`, `[NotInScope]` anchored at the witness
file, `1 UNRESOLVED of 1`, `probe_red=False`, 2.71 s
(`runs/meter-2.out`, and `runs/meter-1.out` at 3.36 s before the last comment
edit). The stop is stated at
`agents/tasks/LJ-1-610/review-of-graph-stage.md`. The brief's premise 1
(`[LJ-1.606]` is GO) was honoured: the predecessor's types were taken, and
nothing here reads a discharge into an unbuilt face.

## WHERE THE Σ₁ IS DISCHARGED

**IT IS NOT DISCHARGED ANYWHERE IN THIS TREE.** The unbounded constructor is
`σ-∃` (`src/FOL/LevyHierarchy.lagda.md:75`), and the face's `∃̇` at the
stage's inner world ranges over the stage's members only
(`src/FOL/Semantics.lagda.md:99`, the `⋁` clause; `⋁` is the truncated
existential, `src/Base/Truth.lagda.md:124-125`). So a discharge would have to
EXHIBIT a stage member z with `(z, q, γ)` satisfying the graph matrix, at
every level pair. The suppliers such a discharge could call on, each checked:
the table route needs a COMPLETE CORRECT TABLE below the index as a stage
member (`graph-table` takes the table as input,
`src/L/Hierarchy.lagda.md:382-388`; nothing in `src/` builds one); the code
route needs `Wit`, "the formula is satisfied at every ordinal of the inner
world", marked "not built anywhere"
(`agents/tasks/LJ-1-598/lj-1.598-report.md:138-140`); the classical route is
Devlin 2.6(ii), whose construction the literature step above shows is assumed,
not given. **In this task's own currency the residue is named: `WitStage`
(`Probe610.agda:235-238`), the witness-in-carrier at the ordinal pairs, is
exactly the undischarged `σ-∃`.**

## THE WALLS, EACH AT file:line

The full statement with all four walls is
`agents/tasks/LJ-1-610/review-of-graph-stage.md`; one line each here:

1. **WITNESS**: no sequence/table-in-stage construction exists anywhere
   (`[LJ-1.598]`'s `Wit`, `lj-1.598-report.md:138-140`; `[LJ-1.578]`'s "not
   built anywhere"); Devlin assumes it from 2.6(ii)
   (`dev/literature/devlin-II5.md:220-221`).
2. **CARRIER**: the graph formulas live at the class carrier
   (`src/L/Coding/Model.lagda.md:70`); the face demands the hull carrier; the
   only constants are numerals (`src/L/Coding/Model.lagda.md:585-586`), whose
   hull-membership is not delivered; the stage-side slide `numSL`
   (`Probe610.agda:131-143`) is this task's own new bridge, priced at 22 code
   lines.
3. **GRADE**: the machine matrix is not Delta-zero (`domAt`/`extAt` unbounded,
   `src/L/Coding/Model.lagda.md:278`, `:662`); the Delta-zero matrix carries
   its bound as a fourth slot (`src/L/BoundedSubset.lagda.md:109-111`);
   arity 3 hosts no kit-grade matrix, so a landed machine-grade G+ still would
   not assemble into `Crossing` without an arity ruling.
4. **INDEX**: the face is all-index; Devlin's (b) is at ordinals
   (`dev/literature/devlin-II5.md:219`); at non-ordinal indices graph and
   tower disagree (`[LJ-1.598]`'s `{{∅}}` reading), so an unguarded
   graph-grade face is refutable at frames carrying the bad pair; the guard
   `isOrdAt` is delivered and Delta-zero
   (`src/L/BoundedSubset.lagda.md:795-803`) and is retargeted at slot 2 by
   `guardSL` (`Probe610.agda:194-202`).

## WHAT WAS LANDED

**ONE GREEN REDUCTION AND FIVE NAMED PIECES, ALL IN THE PROBE.**

| what | at `file:line` | status |
|---|---|---|
| the carrier slide `numSL` | `Probe610.agda:131-143` | green; numerals into the stage, junk elsewhere, correct on every constant the matrix carries |
| the machine matrix and its stage twin | `Probe610.agda:155-160` | green; the body of `LsetGraphAt` at slots (z, v, γ) |
| the face restated | `Probe610.agda:177-180` | green as a TYPE; uninhabited |
| the ordinal guard, Delta-zero, with its `out` lemma | `Probe610.agda:194-216` | green; `guardSL-out` goes through `abs₀` (`src/FOL/Absoluteness.lagda.md:123`) |
| the residue `WitStage` | `Probe610.agda:235-238` | named, unbuilt: Devlin (b)'s forward half at ordinals |
| `graph-stage-from-wit : WitStage → GraphStageAt ψ₀` | `Probe610.agda:243-252` | green; the face's stage twin at the guarded matrix costs EXACTLY `WitStage` plus guard vacuity |

The reduction's content: at an ORDINAL index the residue's witness serves
(the implication algebra needs no guard-reading there: `⟨P ⇒ Q⟩` IS
`⟨P⟩ → ⟨Q⟩`, `Cubical/Functions/Logic.agda:76-77`); at a NON-ordinal index
the guard cannot hold in the stage's inner world, by `guardSL-out`, and the
implication is vacuous at the stage's empty member. **So the whole distance
from G+ to the wall is one guard and one vacuity, and the wall is 2.6(ii).**

## PRICE

**EVERY NUMBER IS MINE, MEASURED UNDER `GHCRTS=[-A64m -I0 -M2g]`, ONE AGDA
PROCESS PER RUN.** Non-blank non-comment lines counted by
`awk 'NF' file | grep -cv '^\s*--'`.

| what | lines | code lines | at `file:line` |
|---|---:|---:|---|
| the probe, whole | 262 | 106 | `Probe610.agda` |
| header, imports and the frame | 115 | 29 | `:1-115` |
| S1 the carrier slide | 29 | 16 | `:117-143` |
| S2 the matrices and Σ₁Closure | 22 | 10 | `:145-165` |
| S3 the face restated | 14 | 5 | `:167-180` |
| S4 the guard and its out lemma | 30 | 13 | `:182-216` |
| S5 the reduction | 35 | 18 | `:218-252` |
| S6 the status | 10 | 0 | `:254-262` |
| W3 slice | 106 | 55 | `runs/W3.agda` |
| floor slice | 262 | 106 | `runs/FLOOR.agda` (the probe with one hole) |

| measurement | wall | peak RSS | basis |
|---:|---:|---:|---|
| W3 first attempt, `timeout` absent, NOT a measurement | 0.00 s | 1,048,576 | `runs/w3-1.out`, exit 127 |
| W3, import failures and parse fixes, five runs | 2.62-2.92 s | ~711 MB | `runs/w3-2.out` to `runs/w3-8.out`, each recorded |
| W3 alone, green | 2.89 s | 668,663,808 | `runs/w3-9.out` |
| W3 alone, forced recheck | 2.86 s | 693,682,176 | `runs/w3-10-forced.out` |
| W3 alone, delivered file, final | 3.38 s | 668,647,424 | `runs/w3-11-final.out` |
| floor, exit 42 at the ONE designed hole | 9.29 s | 849,887,232 | `runs/floor-1.out`, task peak |
| probe, first green | 3.22 s | 710,688,768 | `runs/p-5.out` |
| probe, forced recheck | 3.00 s | 737,771,520 | `runs/p-6-forced.out` |
| probe, delivered file, final | 2.97 s | 710,606,848 | `runs/p-7-final.out` |
| witness meter, obligation MISSING | 2.71 s | not taken | `runs/meter-2.out`, `probe_red=False` |

**THE ESTIMATE WAS ABOUT 200 LINES WITH ABOUT 50 FOR THE OBLIGATION.** The
file is 262 lines and 106 code lines; the reduction and its guard are 31 code
lines. The overrun against 200 is comments, and the header carries the four
walls they record. **THE FLOOR IS 9.29 s WITH THE HOLE OPEN against 2.97 s
closed: the open meta against this target is THREE TIMES the closed term, so
the frame was never in danger and the heap was never the story.** The failed
runs are all recorded with their causes: `w3-1` (no `timeout` on this macOS),
`w3-2` to `w3-4` (a missing `sucV` import, `Sum`'s export shape, two parse
shapes at `∥_∥₁`), `w3-5` to `w3-8` (a subst direction in `numSL`, the
`rec→Set` argument order, the `Sum.rec` motive shape), `p-1` to `p-4` (a
missing `∀̇∈` import, a guard slot over-shift, the `Sum.rec` motive again,
`rec*` against the lifted empty), `p-5` first green.

## C-42, THE SWEEP

The shape swept for is "a level-graph adequacy face whose supplier is named
and absent". The command is
`grep -rn "WitStage\|GraphStage\|Adeq\b\|Wit \|Det " agents/tasks --include="*.agda"`
plus `grep -rln "level-hood adequacy\|graph adequacy" agents/`.

| site | statement | at `file:line` |
|---|---|---|
| 1 | `[LJ-1.52]`'s adequacy, pinned not discharged | `archive/dev/LJ-dispatch-index.md:101` |
| 2 | `[LJ-1.570]`'s `Adeq`, decoders only | `agents/tasks/LJ-1-570/Probe570.agda:319-335` |
| 3 | `[LJ-1.578]`'s `DefinesLevel`, at codes | `agents/tasks/LJ-1-578/Probe578.agda:234-242` |
| 4 | `[LJ-1.598]`'s `Det`/`Wit`, hypotheses | `agents/tasks/LJ-1-598/Probe598.agda:209-214` |
| 5 | `[LJ-1.606]`'s `GraphStage`, this face | `agents/tasks/LJ-1-606/Probe606.agda:156-159` |
| 6 | this task's `WitStage`, the residue named | `agents/tasks/LJ-1-610/Probe610.agda:235-238` |

**SIX SITES IN THE TASK RECORDS, NOTHING IN `src/`, AND THE COUNT HAS NOT
MOVED SINCE `[LJ-1.52]`.** No false shape was proved here and no site carries
one, so the cure question does not arise; what the sweep measures is that the
wall has ONE supplier-shaped hole, in task currency since the archived
adequacy was pinned, and `WitStage` is its name at today's frame.

## W2, THE GENERIC CARRIER

**The mathematics is written once, at the generic carrier, and the carrier
slide is the evidence it was needed.** The probe is generic in `ℓ` and the six
hull slots; the frame instantiates the down-reflection module and the bound
module once; the matrix, the guard, the residue and the reduction are stated
at that one instance, and `numSL` is the single bridge between the class
carrier the tree writes at and the stage carrier the face reads at. No
deadline forced a fixed form; there is no conflict to report.

## W4

Not applicable. No module was retired, nothing under `src/` changed, and
`dev/ARCHIVE.md` takes no row from this task.

## WHAT THE SHAPE RESISTED

- **What it cost.** 106 code lines for a green probe that names the residue
  and reduces the guarded face to it, 2.97 s and 710,606,848 bytes at the
  final run, and no heap event at any point.
- **What the shape resisted.** The reduction itself was almost free (first
  green run after four one-line shape errors, three of them library-interface
  shapes: `Sum`'s export list, `Sum.rec`'s motive-less signature, `rec*`
  against the lifted empty). What resisted was the CARRIER: the graph
  formulas live at the class carrier and the face reads at the stage, and the
  bridge `numSL` had to be built LEM-cased on numeral-recognition because no
  total correct relabelling exists. That bridge is the task's own new
  measurement, and it is WALL 2 made constructible.
- **What I had to weaken.** The currency, twice, both stated: the face is
  restated and left uninhabited (the obligation is NO-GO), and the reduction
  stands at the STAGE-side twin `GraphStageAt` of the guarded matrix, not at
  the face's own hull-carrier type, because WALL 2 stops the hull-side
  relabelling (numerals-into-hull is not delivered).
- **What I could not close.** `WitStage`: the sequence-in-stage construction
  (Devlin 2.6(ii)), which no dispatch has ever built, at any frame, in any
  currency. And the three rulings the review names: the carrier, the arity,
  the index discipline.

## WHAT THE NEXT BRIEF NEEDS

1. **THE WALL HAS ONE RESEARCH OBJECT: THE SEQUENCE INSIDE THE STAGE.** Every
   route to G+ (and to clause (i)'s `Wit`, and to the `Adeq` shape) needs a
   complete correct table below the index, as a STAGE MEMBER. A supplier
   funded for 2.6(ii) at the six-slot frame pays `WitStage`
   (`Probe610.agda:235-238`) directly, and `graph-stage-from-wit` carries it
   to the guarded face for free.
2. **THE FACE'S TYPE NEEDS THREE RULINGS BEFORE IT CAN BE SUPPLIED.** The
   carrier (hull vs stage: the stage-side twin already typechecks here), the
   arity (3 vs 4 with a bound slot: the Delta-zero matrix needs 4), and the
   index discipline (all-index vs ordinal-guarded: the guard is delivered and
   retargeted). The cheapest package is `GraphStageAt ψ₀` as written; the
   strongest is an arity-4 kit. That choice is the owner's, and
   `review-of-graph-stage.md` states it.
3. **DO NOT FUND ANOTHER FACE RESTATEMENT.** The face's statement is measured
   (W3), its floor is measured, and its residue is named. The next spend on
   this row is 2.6(ii) or the rulings, not the type.

## SCOPE

I wrote only inside `agents/tasks/LJ-1-610/`. Gates run:
`check-probes.py --check` clean (7725 tracked files), `lint-agda.py --check`
exit 0, `check-fences.py --check` clean (102 masters). The witness meter
reports the obligation MISSING with `probe_red=False` (`runs/meter-2.out`).
One environment note, recorded rather than hidden: this worktree carries no
`.venv`, so the meter ran under the main repository's pinned
`/Users/alsg/Agentic/Bedrock/.venv/bin/python`, the same interpreter and
pin set `requirements-dev.txt` prescribes; the note is in both meter `.out`
files. I did not run `make check`: I commit nothing. No commit, no push.
`git status` shows only `agents/tasks/LJ-1-610/` untracked; nothing in
`src/` moved.

## ARCHIVE USED

- `archive/dev/LJ-dispatch-index.md`: **READ, two rows.** `:101` reads
  `| LJ-1.52 | The level-hood adequacy at the hull | PINNED, not discharged | The chain is assembled and machine-checked. Three named leaves remain, each written as the term not written |`
  and `:236` reads
  `| LJ-1.160 | Read the 845-line level substrate against levelIn and cover | THE WALL IS BYPASSED, 16 LINES | Both hypotheses from one crossing face at the collapse image. The wall term is absent |`.
  TOOK the AGE of the wall only: the adequacy's supplier has been the named
  term since `[LJ-1.52]`, and the C-42 sweep's count of six sites rests on
  that row. **No number in this report is funded against either row**, and
  the wall was re-measured at its own site here, as the Boundary demands.
- `archive/dev/JOURNAL-archived.md`: **declined, not read beyond its first
  line.** `:1` reads `# Archived journal: the retired route`. A history, and
  nothing here needed one.
- `archive/dev/JOURNAL.md`: **declined, not read beyond its first line.**
  `:1` reads `# ARCHIVED 2026-08-20`. Same reason.
- `archive/dev/DECISIONS-archived.md`: **declined, not read beyond its first
  line.** `:1` reads `# Archived decisions: the D series`. The live rulings
  are the five files the program cats; no D-series rule was consulted.
- `dev/ARCHIVE.md`: **declined, not read beyond its first two lines.**
  `:1-2` read `# ARCHIVE.md: the archive registry` / `The registry of
  Bedrock's retired modules. One entry per module, written at`. Nothing was
  retired in this task and no row is owed.

## LITERATURE USED

- `dev/literature/devlin-II5.md`: **READ, the (b) clause and its chain, in
  the D-10 pass and in the design of the residue.** `:219` reads

      > v = L_γ iff v ∈ L_α and L_α ⊨ ∃z φ(z, v, γ)

  `:220-222` read

      > live inside L_α; that is 2.6(ii), the sequence (L_δ | δ ≤ γ) ∈ L_α for
      > γ < α. Strength: the Σ₁ form is "witnessed inside the carrier", not

  and `:223` reads `merely in V.`. TOOK the whole D-10 reading: what (b)
  supplies (the equivalence at ordinal indices), what it assumes (2.6(ii)'s
  sequence, the ordinal discipline), and what it leaves to the reader (the
  sequence's construction). `:95` and `:104-105` were read in the same pass
  for the transfer chain's shape, as `[LJ-1.606]` already recorded them.
- `dev/literature/devlin-errata.md`: **READ, the Chapter II section, for the
  brief's errata question.** `:125` reads
  `### 2.3 Errors in Chapter II (WS pp. 62-63)` and the entries there
  (`:127-142`) are Devlin pp. 45, 65, 66: amenability, Sat-uniformity, and
  the Σ-over-L_λ claim. **The errata record NOTHING about (b) of 5.2 or
  II.2.7's level formula.**
- `dev/literature/level-formula-slot-roles.md`: **READ, the question and the
  corpus claim.** `:1` reads
  `# The level-hood formula: arity, what it binds, what stays free` and
  `:11-12` read
  `Task [LJ-1.312] refuted a Bedrock formula's slot roles by machine, and this`
  / `digest is the outside view beside that measurement.` TOOK the warning
  into the port: this task's slot arithmetic (the matrix at (z, v, γ), the
  guard retargeted at slot 2) was re-derived at this site and then
  machine-checked, not copied from `[LJ-1.570]`'s; one over-shift WAS caught
  by the checker (`runs/p-2.out`, the guard's second conjunct) before it
  could become a wrong wall.
- `dev/literature/digest.md`: **not used.** `:1` reads
  `# Digest: the orthodox form of the rud route, pinned from the collected
  literature`; the rud route is not at issue in a carrier and guard question.
- `dev/literature/truncation-and-selection.md`: **not used.** `:1` reads
  `# Truncation and selection: how the two literatures pick a witness`; this
  task's truncations are the algebra's own `⋁` and the guard's vacuity, and
  no leastness is selected.
- `dev/literature/geology.md`: **not used.** `:1` reads
  `# Geology dossier: set-theoretic geology sources and the five questions`;
  geology has no bearing on the condensation graph at a hull of a level.
