# LJ-1.602 report: clause (iii) of the level-hood certificate, the read in the collapse

## HEAD
head_slot: coder
machine: shared
verdict: NO-GO on `defines-level-across`; the clause is an EQUIVALENCE, both directions landed as terms: it is the CONDENSATION COMMUTE dressed in syntax, and no formula is owed on it at all

Written as a skeleton before any Agda beyond W3 and filled as each answer
landed (C-22). No commit, no push. I wrote only inside
`agents/tasks/LJ-1-602/`. Agda ran under the caliber the program set on this
pane, `GHCRTS="-A64m -I0 -M2g"`, ONE Agda process at a time. I did not set
`GHCRTS`. Nothing is postulated, the probe carries `--safe`, the final probe
is green and carries no hole, and nothing lands in `src/`. The probe is a
raw `.agda` file, so it carries no ` ```agda ` fence, counts 0 in-fence
lines, and the ratio bar cannot fire on it.

**NO HEAP WALL WAS MET ANYWHERE IN THIS TASK.** The highest peak of any run
is 1,102,168,064 bytes against the 2,147,483,648-byte cap
(`runs/p-1.out`). One run was KILLED at my own 200 s time-box
(`runs/floor-1.out`, no Agda exit line): the first floor slice put the hole
under a lambda with a where-definition, a shape Agda did not finish with,
and the restructure the standing clause orders was built and tested in the
same dispatch: the hole as a BARE META at the named type, the exact shape
`[LJ-1.598]` used. That shape costs 2.81 s (`runs/floor-2.out`). The killed
shape is recorded and not priced.

## VERDICT

**THE OBLIGATION IS NOT INHABITED.** The meter says so:
`agents/tasks/LJ-1-602/Probe602.agda::defines-level-across` returns
`missing exit=42 ... [NotInScope]`, `1 UNRESOLVED of 1`, `probe_red=False`
(witness run, 2.50 s). The stop is stated at
`agents/tasks/LJ-1-602/review-of-defines-level-across.md`.

**THE PROBE IS GREEN AND ALL FOURTEEN DECLARED NAMES LAND**
(`runs/p-5-forced.out`, `EXIT=0`, forced recheck of the delivered file,
11.82 s). Every one of the fourteen was metered by name and returns
`0 UNRESOLVED of 1`, 2.61 s to 2.75 s per run.

**WHY THE NAME IS ABSENT, IN THREE SENTENCES.** Clause (iii)
(`agents/tasks/LJ-1-578/Probe578.agda:503-510`) is EQUIVALENT, at its own
hypotheses, to the condensation commute
`HS.C.π (Lset δ) ≡ Lset (HS.C.π δ)`: any inhabitant yields the commute by
applying its uniqueness conjunct at the image of the certified level
(`across-gives-commute`, `Probe602.agda:189-197`), and the commute buys the
clause outright at the EQUATION formula, whose satisfaction and uniqueness
are free (`commute-gives-across`, `:212-219`). The commute is not built
anywhere: `[LJ-1.477]` stopped at the join of the two computation laws on a
MORE GENERAL type (`agents/tasks/LJ-1-477/lj-1.477-report.md`, `## VERDICT`
at `:97`), and `grep -rn "LevelsCommute" src/` returns nothing. So the
clause's whole price is one set-level statement, no formula is owed, and no
term of the stated type can be built from the delivered machinery.

## D-10, BEFORE ANY AGDA: THE TWO PREDECESSORS, AND WHAT REACHES (iii)

**`[LJ-1.598]`, clause (i), NO-GO** (`lj-1.598-report.md:6`). It measured
two things: (1) the equation route is whole but CIRCULAR for the
certificate (a code naming the level is Fact A's own conclusion), and (2)
the graph route needs `Det`/`Wit` at the inner world plus an index bridge,
because the type's hypothesis `IsOrd (HS.C.π (fst (T.val c)))` does not
make the index ordinal and at a non-ordinal index the tree's graph formula
answers with a non-level (the `δ = {{∅}}` reading, graph value `1`, tower
value `2`, `lj-1.598-report.md`, D-10 section). **What reaches (iii): the
VACUITY LESSON, and it reaches INTACT.** Clause (iii)'s W3, its uniqueness
conjunct alone, is vacuously inhabited by `⊥̇`
(`only-across-vacuous`, `Probe602.agda:120-121`), machine-checked here as
it was measured there (`only-level-vacuous`, `Probe598.agda:104`): an
unsatisfiable formula is vacuously unique in the collapse reading too
(`mapFo CI.I.g ⊥̇` is `⊥̇`, `src/FOL/Manipulation/Relabelling.lagda.md:63`).
**What does NOT reach (iii): the index gap.** Clause (iii) concludes at
`Lset (HS.C.π δ)` with `IsOrd (HS.C.π δ)` hypothesized, an ORDINAL index by
construction; the graph's misbehavior at non-ordinal indices never touches
this conclusion, and no graph formula is needed anyway (section 3 of the
probe). **And the equation route reaches (iii) BETTER THAN IT REACHED (i)**:
at the collapse, the constant the clause certifies is `(Lset δ , Lδ∈M)`
itself, so the route's missing premise is not `CodedLevels` but the
COMMUTE.

**`[LJ-1.595]`, clause (ii), NO-GO** (`review-of-defines-cover.md:3-5`). It
measured that the covering ordinal EXISTS free at the inner world
(`covering-ordinal`, `Probe595.agda:289`) but no delivered formula SELECTS
it, and that Fact C needs no formula at all because it is truncated
(`factC-from-hull`, `Probe595.agda:439`). **What reaches (iii): the
MORAL, and here it becomes a THEOREM.** `[LJ-1.595]` suspected the
certificate's clauses hide set-level statements in formula clothing; for
clause (iii) this is now machine-checked: the hidden statement is the
commute, and the clothing costs nothing (section 3). Its open question
("does clause (i) fall out of the matrix the way clause (ii) does") stays
where `[LJ-1.598]` left it; this task did not touch clauses (i) or (ii).

**NEITHER NO-GO CLOSES (iii), AND THE CHECK COST ONE READ.** Both are about
the FORMULA side; clause (iii) has no formula side left once the equation
route is paid. What closes (iii) is the commute, and that is a different,
unbuilt object.

## WHAT THE COLLAPSE CHANGES

**GIVES: a TRANSITIVE carrier, and nothing else that bears on this clause.**
The collapse's carrier `πX` is transitive by construction (`πX-trans`,
`src/V/Collapse.lagda.md:89`; named at this site as `image-trans`,
`Probe602.agda:264-265`). The hull's carrier `M` carries no delivered
transitivity anywhere (`HullStage`, `src/L/BoundedSubset.lagda.md:903-916`,
delivers the hull, its codes, its closure, and the `Condense` module, none
of it a transitivity of `M`). Transitivity is the precondition the
absoluteness machine demands of a set carrier, and `[LJ-1.160]` measured
that `FOL.Absoluteness.Single` opens at `πX` in one line
(`agents/tasks/LJ-1-160/ProbeLJ1160A.agda:49-51`); the collapse also sends
ordinals to ordinals for any carrier (`π-ord`,
`agents/tasks/LJ-1-595/Probe595.agda:145`). **This is the difference the
next supplier of the commute will have to spend, and `[LJ-1.160]`'s
`crossOut` hypothesis (`:71-72`) is its unbuilt heart.**

**TAKES AWAY: the READING, entirely.** For MAPPED formulas the collapse
decides exactly what the hull decides, both directions delivered
(`iso-inv` and `iso-inv-bwd`, `src/L/BoundedSubset.lagda.md:195` and
`:250`), instantiated at this site as `iso-inv-at-the-site`
(`Probe602.agda:237-240`) and `collapse-satisfiers-lift` (`:247-260`):
every satisfier of the collapse reading IS the image of a satisfier of the
hull reading (`surj'`, `src/L/BoundedSubset.lagda.md:175`). And the
constants the collapse reading can name are `π`-images only (`g`,
`:167`), so the level an EQUATION can pin in the collapse is
`π (Lset δ)`, never `Lset (π δ)`, unless the commute holds. **Net: the
collapse changes the carrier's properties and not the formula's content,
and that is WHY clause (iii) is the commute: its satisfaction conjunct
certifies the constant, its uniqueness conjunct forces that constant's
image to be the tower's level at the collapsed index.**

**THE `[LJ-1.562]` RE-MEASURE: THE QUESTION DOES NOT ARISE HERE, AND THAT
IS THE MEASUREMENT.** `[LJ-1.562]` paid both `AtStage` hypotheses at a
different formula (`lj-1.562-report.md:3-8`), because that task's formula
had constants that needed bounding by a stage. Clause (iii)'s formula side
is the EQUATION `var zero ≐ con (Lset δ , Lδ∈M)`: one constant, the one
the clause itself certifies, satisfaction `refl`, uniqueness path equality
(`eq-sat`, `eq-uniq`, `Probe602.agda:203-210`). No `AtStage` bridge is
wanted anywhere in this probe, a measured cure does not transfer by
analogy (`AGENTS.md:45`), and here there is nothing to transfer it TO: the
residue is set-level. `AtStage`'s five-step path
(`src/L/Axioms/Separation.lagda.md:119`) is the inner-to-outer machinery a
GRAPH route would need; the equation route does not open it.

## IS THE CERTIFICATE ONE OBJECT OR THREE

The three stops share one root, the absence of any crossing from an inner
world to the ambient tower, but they priced three different objects:
clause (i) the stage reading of the level formula (`Det`/`Wit` plus the
index bridge, `agents/tasks/LJ-1-598/Probe598.agda:209-257`), clause (ii)
the same matrix with a free index or nothing at all if the truncated
`Facts.Covered` replaces it (`review-of-defines-cover.md`, "THE TWO THINGS
THE NEXT BRIEF SHOULD DECIDE", item 1), and clause (iii) NO formula at all
but the set-level commute (`Probe602.agda`, section 3). Clause (iii) is
the strongest of the three in the certificate's own currency: it implies
the commute outright at its hypotheses (`across-gives-commute`), the
commute gives it back at the free equation formula
(`commute-gives-across`), and neither (i) nor (ii) implies it, since
`[LJ-1.578]` needed clause (iii) AND Fact A to buy Fact B
(`Probe578.agda:513-514`). For pricing row 3 that means the "one formula,
three readings" shape is dead as a pricing unit: two of the three clauses
are now priced as set-level statements and only clause (i) still wants a
formula, and the next brief should price row 3 from those objects, which I
do not do here.

## W3, THE WIDEST UNMEASURED TERM

**GO, AND THE ANSWER REPEATS `[LJ-1.598]`'S, SO THE WEIGHT MOVES TO THE
CONJUNCTION.** The slice is `agents/tasks/LJ-1-602/runs/W3.agda` (58 lines,
35 code lines), written FIRST and typechecked ALONE: `runs/w3-2.out` is
**exit 0 at 3.12 s, peak 675,217,408 bytes**, under the two-minute cap the
brief set. `runs/w3-1.out` is the record of a run that never started: this
macOS has no `timeout` binary and the wrapper exited 127 before any Agda
process launched; the cap that binds is the pane's heap guard plus my own
time-box, and `run.sh` says so. The type is `Probe602.agda:112-118` letter
for letter. The brief estimated about 15 lines; the type is 7 and the
slice that holds it is 35 code lines, most of it the frame. The uniqueness
conjunct ALONE is vacuously inhabited (`only-across-vacuous`, `:120-121`),
exactly as the sibling clause's was (`Probe598.agda:104`), so the widest
unmeasured term is the CONJUNCTION, and the conjunction turned out to be
the commute.

## THE FLOOR

**MEASURED BEFORE ANY PROOF, ON A TRIMMED FRAME, AND THE FRAME IS
AFFORDABLE.** `runs/FLOOR.agda` states the obligation at a bare hole in the
probe's own frame: `src/`-only imports (the import of `[LJ-1.578]` itself
walls under the standing wide cap with warm dependencies, `[LJ-1.598]`,
`runs/chain-578.out`, exit 251), clause (iii) taken by RESTATEMENT text for
text from `Probe578.agda:503-510`. Result: `runs/floor-2.out`, **2.81 s,
peak 727,351,296 bytes, exit 42 at the one designed hole**
(`[UnsolvedInteractionMetas]`, `FLOOR.agda:68`). **The floor is 0.68 GiB
against the 2 GiB cap. The statement costs nothing; nothing in this task
approached the wall.**

## PRICE

**EVERY NUMBER IS MINE, MEASURED UNDER `GHCRTS=[-A64m -I0 -M2g]`, ONE AGDA
PROCESS PER RUN.** Non-blank non-comment lines counted by
`awk 'NF' file | grep -cv '^\s*--'`.

| what | lines | code lines | at `file:line` |
|---|---:|---:|---|
| the probe, whole | 281 | 113 | `Probe602.agda` |
| header and imports | 92 | 32 | `:1-92` |
| S1 W3 and its vacuity | 30 | 9 | `:93-122` |
| S2 clause (iii) by restatement | 33 | 19 | `:123-155` |
| S3 the equivalence, both directions | 66 | 32 | `:156-221` |
| S4 what the collapse changes, as terms | 45 | 21 | `:222-266` |
| S5 the residue, named | 15 | 0 | `:267-281` |
| W3 slice | 58 | 35 | `runs/W3.agda` |
| floor slice | 68 | 38 | `runs/FLOOR.agda` |

| measurement | wall | peak RSS | basis |
|---|---:|---:|---|
| W3 alone, exit 0 | 3.12 s | 675,217,408 | `runs/w3-2.out` |
| W3 wrapper failure, no Agda run | 0.00 s | 1,048,576 | `runs/w3-1.out` (exit 127, no `timeout` binary) |
| floor, KILLED at my 200 s time-box | (killed) | (none taken) | `runs/floor-1.out`, no EXIT line |
| floor, TRIMMED frame, bare hole | 2.81 s | 727,351,296 | `runs/floor-2.out` |
| probe, exit 42 (subst direction) | 11.28 s | 1,102,168,064 | `runs/p-1.out` |
| probe, exit 42 (wrong transfer leg) | 11.65 s | 1,101,152,256 | `runs/p-2.out` |
| probe, exit 42 (subst orientation) | 11.56 s | 1,102,168,064 | `runs/p-3.out` |
| probe, first green | 12.11 s | 1,101,414,400 | `runs/p-4.out` |
| final probe, forced recheck of the delivered file | 11.82 s | 1,101,414,400 | `runs/p-5-forced.out` |
| obligation witness | 2.50 s | not taken | `missing exit=42`, `probe_red=False` |
| name meter, one name | 2.61 to 2.75 s | not taken | fourteen names, all `0 UNRESOLVED of 1` |

**THE ESTIMATE WAS ABOUT 200 LINES WITH ABOUT 50 FOR THE OBLIGATION.** The
file is 281 lines and 113 code lines, and the obligation is absent: the
EQUIVALENCE that prices it is 32 code lines (section 3), and the collapse
facts that make the equivalence meaningful are 21 more (section 4). The
overrun against 200 is comments, and the probe's own header says why: the
restructures and the D-10 readings are part of the deliverable. **The heap
was watched as the brief ordered and it never became the story: the
statement's floor is 0.68 GiB, the elaborated probe 1.03 GiB, both under
the 2 GiB cap, and the only killed run was my own time-box on a hole shape
I then restructured and re-measured.**

**NOTHING IN `runs/` IS UNEXPLAINED.** `w3-1` (wrapper exit 127, no Agda
run), `w3-2` (W3 green), `floor-1` (killed at the 200 s time-box, the
lambda-plus-where hole shape, no Agda exit), `floor-2` (the restructured
floor), `p-1` to `p-3` (three shape errors in ONE term, each one line:
subst direction, then the forward transfer used where the backward was
wanted, then the subst orientation again), `p-4` (first green), `p-5-forced`
(forced recheck of the delivered file, interface deleted first, its own
`Checking` line). Every `.out` carries `GHCRTS=`, a start stamp, an end
stamp and `EXIT=` except `floor-1`, which is the killed run and says so by
having none.

## C-42, THE SWEEP

The stop names one site: clause (iii)'s formula clothing. The shape swept
for is "a certificate clause equivalent to a set-level statement". The
command is `grep -rn "DefinesLevelAcross\|LevelsCommute" agents/ src/`.

| site | statement | at `file:line` |
|---|---|---|
| 1 | `Facts.LevelsCommute`, the commute | `agents/tasks/LJ-1-578/Probe578.agda:126-128` |
| 2 | `BChain.DefinesLevelAcross`, clause (iii) | `:503-510` |
| 3 | `b-from-across`, the one-directional version | `:513-514` |
| 4 | `Certificate`'s third row | `:534` |
| 5 | `certificate-gives-remainder`'s use | `:540` |

**FIVE SITES IN ONE FILE AND NOTHING IN `src/`.** My `Commute`
(`Probe602.agda:178-181`) differs from site 1 in ONE way: it carries the
clause's own hypothesis `Lδ∈M`, so the equivalence is exact at the clause's
hypotheses. The cure the next brief should consider is one edit to one file
(replace clause (iii) by the commute), or fund the commute itself; no
tree-wide sweep is owed.

## W2, THE GENERIC CARRIER

**Nothing is written twice and nothing needed a second instantiation.** The
probe is generic in `ℓ` and in the frame's six parameters, and the
equivalence terms are stated ONCE at the generic hull. The equation route's
content is generic already: `eqA`, `eq-sat` and `eq-uniq` live in the
collapse iso's own terms and use nothing of this hull beyond `g` and the
restricted structures, and `IsoInv` is the generic carrier
(`src/L/BoundedSubset.lagda.md:152`). No deadline forced a fixed form and
there is no conflict to report.

## W4, AND P-l

W4: not applicable. No module was retired, nothing under `src/` changed,
and `dev/ARCHIVE.md` takes no row from this task.

P-l: obeyed and not re-measured. No type in the probe names a stage
presentation: `OnlyAcross`, `DefinesLevelAcross`, `Body`, `Commute` and the
three residue types quantify over `SV.S`, `CI.I.SM` and `CI.I.SPM`, and
`⟪ Lset lam ⟫` appears nowhere in the probe.

## WHAT THE SHAPE RESISTED

- **What it cost.** 113 code lines for a green probe that prices the whole
  clause, 11.82 s and 1,101,414,400 bytes at the final forced recheck, and
  no heap event at any point.
- **What the shape resisted.** One term, three one-line shape errors in it
  (`collapse-satisfiers-lift`, runs `p-1` to `p-3`): the backward transfer
  leg wants `iso-inv-bwd` and a `sym`, and I wrote the forward leg twice
  before reading the error messages properly. Everything else assembled on
  the first attempt, which matches the siblings' finding: the plumbing
  fits, the MEANING is the cost, and here the meaning is one equation.
- **What I had to weaken.** Nothing. No term assumes an unbuilt statement
  as a premise; the two directions of the equivalence take each OTHER as
  inputs, and the obligation itself is absent rather than faked.
- **What I could not close.** `Commute` (`Probe602.agda:178-181`), and it
  is the whole residue: `[LJ-1.477]`'s join
  (`agents/tasks/LJ-1-477/Probe477.agda:90-93`), `[LJ-1.160]`'s `crossOut`
  at the transitive image (`agents/tasks/LJ-1-160/ProbeLJ1160A.agda:71-72`),
  or any other route to `π (Lset δ) ≡ Lset (π δ)` at ordinal collapse. The
  brief forbade clauses (i) and (ii) and neither was attempted.

## WHAT THE NEXT BRIEF NEEDS

1. **DECIDE THE CERTIFICATE'S SHAPE BEFORE FUNDING ANY SUPPLIER.** Two of
   its three clauses are now priced as set-level statements (clause (ii) as
   the truncated `Facts.Covered` per `[LJ-1.595]`, clause (iii) as the
   commute per this task). The "one formula, three readings" pricing unit
   is dead. Row 3 is: clause (i)'s formula (`Det`/`Wit`, `[LJ-1.598]`),
   Fact C's statement, and the commute.
2. **THE COMMUTE IS THE OBJECT, AND IT HAS THREE MEASURED FACES.** The
   computation-law join (`[LJ-1.477]`, NO-GO at the more general type),
   the crossing at the transitive image (`[LJ-1.160]`'s `crossOut`,
   hypothesis only), and the certificate clause (this task: equivalent,
   exactly, at the clause's hypotheses). A supplier should be priced
   against the STATEMENT, not against any one face.
3. **THE CLAUSE'S HYPOTHESES ARE THE RIGHT ONES, UNLIKE CLAUSE (i)'s.**
   `IsOrd (HS.C.π δ)` excludes `[LJ-1.477]`'s candidate obstruction
   (non-ordinal collapse) by construction, and `Lδ∈M` is what the equation
   route consumes. If the commute is funded at this frame, clause (iii)
   comes free in 8 code lines (`commute-gives-across`).
4. **THE VACUITY WARNING IS NOW MEASURED TWICE.** Uniqueness conjuncts
   alone are free at both readings (inner world, `Probe598.agda:104`;
   collapse, `Probe602.agda:120-121`). No brief should fund one again.

## SCOPE

I wrote only inside `agents/tasks/LJ-1-602/`. Gates run:
`check-probes.py --check` clean (7627 tracked files), `lint-agda.py
--check` exit 0, `check-fences.py --check` clean (102 masters). I did not
run `make check`: I commit nothing. No commit, no push. `git status` shows
only `agents/tasks/LJ-1-602/` untracked; nothing in `src/` moved.

## ARCHIVE USED

- `archive/dev/LJ-dispatch-index.md`: **READ, one row.** `:100` reads
  `| LJ-1.51 | Discharge the five hypotheses | 2 of 5, plus the sq master | fin-inj and Mext DISCHARGED. SquareLaw lands as a 775-line master. cover and levelIn survive on the hull adequacy |`.
  TOOK the AGE of the commute wall only: `[LJ-1.160]`'s probe header says
  `[LJ-1.51]` could not write `π (Lset m') ≡ Lset (π m')`
  (`agents/tasks/LJ-1-160/ProbeLJ1160A.agda:22-23`), and this row is that
  task's dispatch record. **No number in this report is funded against
  that row**, and the commute was re-measured at its own site here, as the
  Boundary demands.
- `archive/dev/JOURNAL-archived.md`: **declined, not read beyond its first
  line.** `:1` reads `# Archived journal: the retired route`. A history,
  and nothing here needed one.
- `archive/dev/JOURNAL.md`: **declined, not read beyond its first line.**
  `:1` reads `# ARCHIVED 2026-08-20`. Same reason.
- `dev/ARCHIVE.md`: **declined, not read beyond its header.** `:1` reads
  `# ARCHIVE.md: the archive registry`. W4 did not fire: no module was
  retired and no row is owed.
- `archive/dev/ORCHESTRATION.md`: **declined, not read beyond its first
  line.** `:1` reads `# ORCHESTRATION: the orchestrator's operating rules`.
  The live rules are the five files the program cats.

## LITERATURE USED

- `dev/literature/devlin-II5.md`: **READ, the condensation chapter.** `:72-73`
  reads

      > 5.2 Theorem (The Condensation Lemma). Let α be a limit ordinal. If
      > X ≺₁ L_α, then there are unique π and β such that β ≤ α and:

  and `:95-99` carries the (a)/(b) level-hood chain `[LJ-1.598]` priced
  clause (i) against. TOOK one fact for the D-10 reading: Devlin's theorem
  states the collapse as an ISO onto a level (`:73`, part (i)) and never
  states the tree's commute `π (L_δ) = L_{πδ}` as such; the tree's
  `Facts.LevelsCommute` is the tree's own crossing, which is why no
  literature statement discharges it and why `[LJ-1.160]` had to hypothesize
  `crossOut`.
- `dev/literature/truncation-and-selection.md`: **READ, one passage.**
  `:15-17` read

      **No classical source at this step uses choice.** Three of them select the
      LEAST witness under a definable well-order, and all three write leastness with
      the same universal guard.

  TOOK the contrast: the classical sources buy uniqueness by LEASTNESS, and
  clause (iii) needs NO selection at all, because the equation formula is
  unique for free and the clause's price is the commute. A leastness route
  would price the commute too, by `across-gives-commute`.
- `dev/literature/level-formula-slot-roles.md`: **READ, then declined at
  this clause.** `:3-5` read

      **The question.** How does each author state "`v` is the `γ`-th level of `L``
      as a formula? How many slots does the formula use? Which does it bind? Which

  The slot arithmetic binds formulas with BINDERS. Clause (iii)'s formula
  is an equation at one constant: one slot, value role, nothing bound, and
  the file's tables were not needed. `[LJ-1.598]` used them for the graph
  formula; that use stands and was not re-checked here.
- `dev/literature/digest.md`: **not used.** It is the fetch record for the
  rud route's orthodox form; the commute is not a rud-route question and
  the digest carries no statement about collapses.
- `dev/literature/geology.md`: **not used.** `:1` reads
  `# Geology dossier: set-theoretic geology sources and the five questions`;
  geology (mantles, grounds, Hamkins) has no bearing on the condensation
  commute at a hull of a level.
