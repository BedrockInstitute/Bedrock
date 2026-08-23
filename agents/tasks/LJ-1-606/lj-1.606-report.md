# LJ-1.606 report: the crossing from an inner world to the ambient tower

## HEAD
head_slot: coder
machine: shared
verdict: the OBLIGATION IS DELIVERED in the brief's second form, "the term
naming precisely what it lacks": `inner-to-ambient` is a GREEN term whose
type names the three faces the commute lacks; the OUTRIGHT commute is NOT
inhabited, and the stop is stated at
`agents/tasks/LJ-1-606/review-of-inner-to-ambient.md`

Written as a skeleton before any Agda beyond W3 and filled as each answer
landed (C-22). No commit, no push. I wrote only inside
`agents/tasks/LJ-1-606/`. Agda ran under the caliber the program set on
this pane, `GHCRTS="-A64m -I0 -M2g"`, ONE Agda process at a time. I did
not set `GHCRTS`. Nothing is postulated, the probe carries `--safe`, the
delivered file has no hole, and nothing lands in `src/`. **NO HEAP WALL
WAS MET ANYWHERE IN THIS TASK**: the highest peak of any run is
777,961,472 bytes against the 2,147,483,648-byte cap
(`runs/p-3-forced.out`), and the longest run is 4.97 s against the caps I
set (two minutes for W3, two hundred seconds for everything else). The
probe is a raw `.agda` file, so it carries no ` ```agda ` fence, counts 0
in-fence lines, and the ratio bar cannot fire on it.

## W3, THE WIDEST UNMEASURED TERM

**GO, AND IT IS THE COMMUTE ITSELF, EXACTLY AS THE BRIEF ORDERED IT
RESTATED.** The slice is `agents/tasks/LJ-1-606/runs/W3.agda` (50 lines,
26 code lines), written FIRST and typechecked ALONE: `runs/w3-2.out` is
**exit 0 at 2.41 s, peak 600,702,976 bytes**, under the two-minute cap.
`runs/w3-1.out` is the same slice one comment-edit earlier, exit 0 at
2.47 s and 600,637,440 bytes; the edit fixed a typo in a comment and the
delivered file carries its own green run. The type is
`agents/tasks/LJ-1-606/runs/W3.agda:46-51`, letter for letter
`[LJ-1.602]`'s `Commute` (`agents/tasks/LJ-1-602/Probe602.agda:178-181`).
The brief estimated about 15 lines; the type is 4 and the slice that
holds it is 26 code lines, most of it the frame. The widest unmeasured
term is therefore measured: its STATEMENT costs 2.41 s and 0.56 GiB, and
its weight is not in the statement.

## D-10, BEFORE ANY AGDA

**THE TARGET IS TRUE AT THIS FRAME, AND THE TREE CANNOT SUPPORT IT WITHOUT
THE GRAPH.** The commute `π (Lset δ) ≡ Lset (π δ)` at the four hypotheses
is Devlin 5.2's core, and the classical proof is the transfer chain the
digest records: the level graph as a Σ₁ statement with a Σ₀ matrix
(`dev/literature/devlin-II5.md:95`), moved from the stage to the
submodel by elementarity and along the collapse
(`dev/literature/devlin-II5.md:104-105`), with the matrix absolute at the
transitive image and the (a)-half decoding the witness as the level. So
no Tarskian obstruction exists, and the refutation route the brief
offered is closed: I did not refute the commute, because classically it
holds and the obstruction `[LJ-1.477]` named (a non-ordinal collapse) is
excluded by the clause's own `IsOrd (HS.C.π δ)`.

**THE PREMISE CHECK PASSED ON ALL THIRTEEN.** `[LJ-1.602]`'s section 3
was precise enough to restate: `Probe602.agda:178-181` is the type, and
the equivalence to clause (iii) is at `:189-219` there. `[LJ-1.578]`'s
clause (iii) is at `agents/tasks/LJ-1-578/Probe578.agda:503-510`, the
three-clause remainder at `:525` and following, `CoHyps` is the pair at
`src/L/BoundedSubset.lagda.md:1555-1556`, `𝒟ₒ-intro` at
`src/L/Constructible.lagda.md:301`, `defSet` at
`src/L/Definability.lagda.md:111`.

**AND THE D-10 READING FOUND ONE GAP THE CERTIFICATE'S CURRENCY HIDES.**
`Commute`'s telescope does NOT hypothesize `IsOrd δ`, so the crossing must
run at NON-ORDINAL hull indices too. The classical chain does this
through a graph that internalizes the ∈-recursion at every index; the
tree's graph formula is ordinal-indexed and answers with a NON-level at a
non-ordinal index, measured by `[LJ-1.598]` (the `δ = {{∅}}` reading,
`agents/tasks/LJ-1-598/lj-1.598-report.md`). So the graph face G+ below
is stated at all indices, and a supplier has two roads: an all-index
graph, or `IsOrd δ` added to clause (iii)'s currency. That choice is not
mine to make; it is named in the review file.

## THE FLOOR

**MEASURED BEFORE ANY PROOF, ON THE PROBE'S OWN TRIMMED FRAME.**
`runs/FLOOR.agda` is the frame, the faces and the syntax legs with the
obligation at a BARE META (`runs/FLOOR.agda:108`). Result:
`runs/floor-2.out`, **exit 42 at the one designed hole
(`[UnsolvedInteractionMetas]`), 3.56 s, peak 656,900,096 bytes**. The
floor is 0.61 GiB against the 2 GiB cap: the frame is affordable and
nothing in this task approached the wall. `runs/floor-1.out` is a SYNTAX
failure and not a measurement: the import list carried `_⇒_` for `_⇒̇_`
and the absoluteness import used the wrong pattern; both are fixed in the
delivered files and neither is priced.

## THE COMMUTE, STATED

**THE TYPE, IN FULL** (`agents/tasks/LJ-1-606/Probe606.agda:127-130`,
restated alone first at `runs/W3.agda:46-51`):

    Commute =
      (δ : SV.S) (δ∈M : ⟨ δ ∈ˢ HS.M ⟩) → IsOrd (HS.C.π δ)
      → (Lδ∈M : ⟨ Lset δ ∈ˢ HS.M ⟩)
      → HS.C.π (Lset δ) ≡ Lset (HS.C.π δ)

at the frame `Probe606.agda:104-115`: one hull stage `HS` at a limit
index `lam`, its extensionality `HE`, its collapse iso `CI`, its
down-reflection module `DR`, and the absoluteness machine `AbsπX` at the
transitive collapse image. This is `[LJ-1.602]`'s `Commute` letter for
letter, and that task measured it EQUIVALENT to clause (iii) at exactly
these hypotheses (`Probe602.agda:189-219`, both directions as terms).

**IS IT INHABITED? NOT OUTRIGHT.** No term of type `Commute` without
further hypotheses exists in this task, and none exists in the tree
(`grep -rn "LevelsCommute" src/` returns nothing). What is inhabited is
the brief's other form:

    inner-to-ambient
      : (the six hull slots)
      → ElemDownAt → Crossing → Commute

at `agents/tasks/LJ-1-606/Probe606.agda:303-313`, green under the forced
recheck `runs/p-10-final.out` (exit 0, 4.77 s, 726,712,320 bytes), and
metered `pass exit=0`, `0 UNRESOLVED of 1`, `probe_red=False`, 3.14 s.

## WHAT THE TERM NAMES: THE FACES

Three faces, each one named type, each consumed by the term and by
nothing else:

| face | statement | at `file:line` | status |
|---|---|---|---|
| E `ElemDownAt` | elementarity down at the hull, all arities; `DownReflect.ElemDown` (`src/L/BoundedSubset.lagda.md:410`) | `Probe606.agda:147-149` | UNBUILT at six slots; DELIVERED at `[LJ-1.570]`'s seventeen (`agents/tasks/LJ-1-578/Probe578.agda:413-427`) |
| G+ `GraphStage` | the stage's inner world satisfies the Σ₁ closure of the graph matrix at the tower's own values | `Probe606.agda:156-159` | UNBUILT; Devlin (b)'s witness-in-carrier (`dev/literature/devlin-II5.md:222`); the `Adeq` shape of `[LJ-1.570]` (`agents/tasks/LJ-1-570/Probe570.agda:319-322`) |
| G- `GraphAmbient` | any ambient witness of the carried matrix at an ORDINAL index pins the tower's level | `Probe606.agda:168-172` | UNBUILT; Devlin (a); `[LJ-1.160]`'s `crossOut` made concrete (`agents/tasks/LJ-1-160/ProbeLJ1160A.agda:71-72`) |

`Crossing` (`Probe606.agda:178-180`) bundles the graph matrix `ψ` with
`Δ₀ ψ` and both faces. **THE KIT CANNOT BE FILLED WITH JUNK, BOTH WAYS,
AS TERMS** (`Probe606.agda:260-285`): a TRUE matrix fails G- outright
(`⊤-fails-G-`, `:262`), because at the ordinal `∅` it would force every
set to be `Lset ∅` and so `∅ ≡ sucV ∅`; a FALSE matrix fails G+ at any
genuine level-pair (`⊥-fails-G+`, `:275`), because the stage's reading of
its existential closure detonates on its own witness. So `Crossing` is
inhabited exactly when the level-graph adequacy holds at this site.

**THE TERM IS ONE TRANSFER, AND THAT IS THE FINDING.** The five legs
(`Probe606.agda:217-247`): G+ puts the graph statement in the stage's
inner world at the hull's own level pair (`gst`); E reads it into the
hull (`ed`); the DELIVERED collapse iso carries it to the image
(`CI.I.iso-inv`, `src/L/BoundedSubset.lagda.md:195`); the DELIVERED Σ₁
lift reads it out to the ambient at the collapsed constants
(`AbsπX.σ₁-up`, `src/FOL/Absoluteness.lagda.md:182-185`, which
`[LJ-1.160]` measured opens at `πX` in one line); G- decodes it there at
the ordinal index (`gamb`). **No induction on the tower, no Fact A below
`δ`, no def-hood lifting.** `[LJ-1.578]`'s `b-from-across` needed
`HasLevels` and clause (iii); this term needs neither, because the
clause's own `Lδ∈M` hypothesis puts the level pair inside the hull, and
the statement that moves is the graph, not the level construction. The
syntax legs `mapFo-Δ₀` (`Probe606.agda:188-199`) and `Σ₁-carried`
(`:201-204`) carry the Δ₀ witness and the Σ₁ closure across the
relabelling; they are pure syntax and cost the floor run nothing extra.

## DOES IT PAY ALL THREE CLAUSES

**NO, NOT OUTRIGHT, AND NOTHING BELOW READS A DISCHARGE INTO AN UNBUILT
FACE.** The honest accounting, clause by clause:

- **CLAUSE (iii): PAID ABOVE THE FACES, AND ONLY ABOVE THEM.** Compose
  this term with `[LJ-1.602]`'s `commute-gives-across`
  (`Probe602.agda:212-219`): the faces give `Commute`, and `Commute`
  gives clause (iii) at the free equation formula. That task proved the
  converse too (`across-gives-commute`, `:189-197`), so clause (iii) and
  the faces-plus-elementarity are INTERCHANGEABLE currency at this frame.
  With no faces supplied, clause (iii) is as open as it was at
  `[LJ-1.602]`'s close.
- **CLAUSE (i): THE FACES ARE ITS OWN RESIDUE, SO PAYING THEM PAYS THE
  SAME CONTENT, BUT I DID NOT PAY THEM AND DID NOT BUILD ITS FORMULA.**
  G+ and G- are the two halves of the level-graph adequacy;
  `[LJ-1.578]`'s clause (i) is the graph read at the STAGE
  (`Cert.DefinesLevel`, `Probe578.agda:234-242`), and `[LJ-1.598]`
  priced that clause NO-GO on the formula side. I did not inhabit
  `DefinesLevel`, did not build `Det`/`Wit`, and did not reach for
  `𝒟ₒ-intro` or `hasSeparationL` anywhere: the brief's warning did not
  fire, because the term's suppliers are set-level faces and not formula
  machinery inside the obligation.
- **CLAUSE (ii): NOT TOUCHED, AND ALREADY TRUNCATED AWAY.**
  `[LJ-1.595]` reduced it to the truncated `Facts.Covered`
  (`agents/tasks/LJ-1-595/review-of-defines-cover.md:3-5`); nothing here
  changes that.

**NET FOR THE CAMPAIGN: row 3 is ONE WALL, AND THE WALL IS THE GRAPH
ADEQUACY PLUS ONE WIDENABLE FACE.** The three stops of `[LJ-1.582]`,
`[LJ-1.598]`, `[LJ-1.595]` and `[LJ-1.602]`'s now sit above a single
named object: the level-graph adequacy at the hull site (G+ and G-) and
the elementarity face E, which is already delivered one frame wider. The
"A GO may pay all three clauses at once" of the brief's branch table
would require the faces; this GO does not have them and does not claim
them.

## VERDICT

**THE CROSSING IS REDUCED, NOT BUILT.** The obligation is delivered in
the brief's sanctioned second form and the meter passes it; the outright
commute stays open, its residue is THREE named faces, two of which are
one object (the level-graph adequacy), and the third is delivered at a
wider frame. The stop is stated at
`agents/tasks/LJ-1-606/review-of-inner-to-ambient.md`.

## PRICE

**EVERY NUMBER IS MINE, MEASURED UNDER `GHCRTS=[-A64m -I0 -M2g]`, ONE
AGDA PROCESS PER RUN.** Non-blank non-comment lines counted by
`awk 'NF' file | grep -cv '^\s*--'`.

| what | lines | code lines | at `file:line` |
|---|---:|---:|---|
| the probe, whole | 313 | 134 | `Probe606.agda` |
| header and imports | 100 | 28 | `:1-100` |
| S1 W3, the commute restated | 13 | 5 | `:118-130` |
| S2 the faces and the kit | 48 | 16 | `:134-181` |
| S3 the syntax legs | 23 | 16 | `:183-205` |
| S4 the term, five legs | 41 | 23 | `:207-247` |
| S5 no degenerate kit | 36 | 18 | `:249-284` |
| S6 the hoisted obligation | 22 | 11 | `:285-313` |
| W3 slice | 50 | 26 | `runs/W3.agda` |
| floor slice | 108 | 74 | `runs/FLOOR.agda` |

| measurement | wall | peak RSS | basis |
|---|---:|---:|---|
| W3 alone, exit 0 | 2.47 s | 600,637,440 | `runs/w3-1.out` |
| W3 alone, delivered file | 2.41 s | 600,702,976 | `runs/w3-2.out` |
| floor, SYNTAX failure, not a measurement | 2.87 s | 588,709,888 | `runs/floor-1.out` (`_⇒_` for `_⇒̇_`) |
| floor, exit 42 at the designed hole | 3.56 s | 656,900,096 | `runs/floor-2.out` |
| probe, first green (term at the frame) | 4.04 s | 753,860,608 | `runs/p-1.out` |
| probe, forced recheck (pre-hoist) | 4.42 s | 753,926,144 | `runs/p-2-forced.out` |
| probe, forced recheck (post-hoist) | 4.13 s | 777,961,472 | `runs/p-3-forced.out`, task peak |
| witness meter, MISSING (name under `Frame`) | 2.61 s | not taken | the meter's dotted-name rule |
| witness meter, PASS (post-hoist) | 2.95 s | not taken | `0 UNRESOLVED of 1` |
| probe, exit 42 (path order in `e₁ ∙ sym e₂`) | 3.64 s | 582,647,808 | `runs/p-4.out` |
| probe, exit 42 (subst orientation) | 4.15 s | 582,664,192 | `runs/p-5.out` |
| probe, exit 42 (`∈ₛ` is an hProp, misused) | 4.21 s | 582,631,424 | `runs/p-6.out` |
| probe, exit 42 (`refl` at the junk member) | 4.27 s | 583,696,384 | `runs/p-7.out`, restructured |
| probe, green with both refutations | 4.97 s | 726,728,704 | `runs/p-8.out` |
| forced recheck after S5 | 4.48 s | 726,728,704 | `runs/p-9-forced.out` |
| final probe, forced recheck of the delivered file | 4.77 s | 726,712,320 | `runs/p-10-final.out` |
| final witness meter, PASS | 3.14 s | not taken | `0 UNRESOLVED of 1` |

**THE ESTIMATE WAS ABOUT 190 LINES WITH ABOUT 45 FOR THE OBLIGATION.**
The file is 313 lines and 134 code lines; the obligation's two parts
(section 4 and the hoist) are 34 code lines. The overrun against 190 is
comments, and the probe's header carries the finding they record. The
heap was watched as the brief ordered, by `/usr/bin/time -l` on every
run, and it never became the story: task peak 0.72 GiB against the 2 GiB
cap.

**NOTHING IN `runs/` IS UNEXPLAINED.** `w3-1`/`w3-2` (W3 green, before
and after a comment typo fix), `floor-1` (syntax failure, recorded and
not priced), `floor-2` (the designed-hole floor), `p-1`/`p-2-forced`
(first green and its forced recheck, before the hoist), `p-3-forced`
(post-hoist recheck, task peak), `p-4` to `p-7` (four one-line shape
errors in the non-degeneracy section: path order, then subst
orientation, then `∈ₛ` used as a type where it is an hProp, then `refl`
ascribed at the junk member, which was a DESIGN error and was
restructured into the pair-parameterised statement rather than patched),
`p-8` (first green with both refutations), `p-9-forced` (forced recheck
after section 5), `p-10-final` (final forced recheck of the delivered
file after the last comment edit, interface deleted first, its own
`Checking` line). Every `.out` carries `GHCRTS=`, a start stamp, an end
stamp and `EXIT=`.

## C-42, THE SWEEP

The shape swept for is "the set-level collapse-levels commute". The
command is `grep -rn "LevelsCommute\|PiCommuteLset\|πCommuteLset"
agents/ src/`.

| site | statement | at `file:line` |
|---|---|---|
| 1 | `Facts.LevelsCommute`, the commute as Fact B | `agents/tasks/LJ-1-578/Probe578.agda:126-128` |
| 2 | `b-from-across`, clause (iii) + Fact A give it | `:513-514` |
| 3 | `[LJ-1.602]`'s `Commute`, the equivalence | `agents/tasks/LJ-1-602/Probe602.agda:178-181` |
| 4 | `[LJ-1.477]`'s more general unbuilt type | `agents/tasks/LJ-1-477/Probe477.agda:100-102` |
| 5 | `[LJ-1.462]`'s same type, step 4 | `agents/tasks/LJ-1-462/Probe462.agda:140-142` |

**FIVE SITES IN THE TASK RECORDS AND NOTHING IN `src/`.** My term is the
first object in the tree that DECOMPOSES the commute instead of
restating it, so the cure question C-42 asks about does not arise: no
false shape was proved and no site carries one. The reduction is new
only at sites 1-3's currency: the faces E, G+ and G-
(`Probe606.agda:147-172`) are the replacement pricing unit.

## W2, THE GENERIC CARRIER

**The mathematics is written once, at the generic carrier, and nothing
needed a second instantiation.** The probe is generic in `ℓ` and in the
six hull slots; the frame instantiates the hull machinery, the collapse
iso, the down-reflection module and the absoluteness machine once, and
both the reduction and the non-degeneracy refutations are stated at that
one instance. No deadline forced a fixed form; there is no conflict to
report.

## W4

Not applicable. No module was retired, nothing under `src/` changed, and
`dev/ARCHIVE.md` takes no row from this task.

## WHAT THE SHAPE RESISTED

- **What it cost.** 134 code lines for a green probe that reduces the
  crossing to three named faces and refutes both degenerate fillings,
  4.77 s and 726,712,320 bytes at the final forced recheck, and no heap
  event at any point.
- **What the shape resisted.** Almost nothing in the obligation itself:
  the five-leg term was green on its FIRST run (`runs/p-1.out`), because
  it composes delivered legs whose readings agree definitionally, with
  no `subst` anywhere. All four type errors of the task were in the small
  SIDE terms: three one-line shape errors in `⊤-fails-G-` (path order,
  subst orientation, the `∈ₛ` hProp), and one design error in
  `⊥-fails-G+` (a `refl` ascribed at the junk member, which is not a
  tower fixed point; the statement was restructured to take any genuine
  level-pair). This matches the siblings' finding: the plumbing fits,
  the meaning is the cost, and here the meaning is the graph.
- **What I had to weaken.** The obligation's currency, in the sense the
  brief itself sanctions: the delivered term takes the three faces as
  arguments instead of inhabiting the commute outright. No term assumes
  an unbuilt statement as a premise beyond the three faces, and each
  face is individually named and priced.
- **What I could not close.** The faces: E at this frame (the code count
  needs the square law that lives at `[LJ-1.570]`'s seventeen slots), G+
  and G- (the level-graph adequacy, clause (i)'s residue). And the
  index ruling: whether G+ must be all-index or clause (iii) gains
  `IsOrd δ` is a choice the owner must hear, not one I make.

## WHAT THE NEXT BRIEF NEEDS

1. **ROW 3 HAS ONE PRICE LEFT: THE GRAPH ADEQUACY AT THE HULL SITE.**
   With `[LJ-1.602]`'s equivalence and this reduction, clauses (i) and
   (iii) both sit above G+ and G-; clause (ii) is truncated away. A
   supplier funded for the graph adequacy at the `Formula CI.I.SM 3`
   reading (the faces carry `mapFo CI.I.g` themselves) pays the crossing
   by composition with this term, at either frame.
2. **E IS A FRAME-WIDENING, NOT A RESEARCH PROBLEM.** It is delivered at
   `[LJ-1.570]`'s seventeen slots (`agents/tasks/LJ-1-578/Probe578.agda:413-427`).
   A supplier working there imports it; a supplier at six slots must
   first widen, and the widening needs the code count, which needs the
   square law.
3. **THE INDEX RULING IS THE OWNER'S.** G+ as stated is all-index; the
   tree's graph is measured to be ordinal-indexed
   (`[LJ-1.598]`, the `{{∅}}` reading). Either rebuild the graph on the
   ∈-recursion, or add `IsOrd δ` to clause (iii)'s currency and shrink G+
   to ordinal indices. The second is cheaper; the first is stronger.
4. **DO NOT FUND A FOURTH CLAUSE OR ANOTHER COMMUTE RESTATEMENT.** The
   commute is now the cheapest currency in the row and its suppliers are
   named; the next spend should be on a face, not on the statement.

## SCOPE

I wrote only inside `agents/tasks/LJ-1-606/`. Gates run:
`check-probes.py --check` clean (7676 tracked files), `lint-agda.py
--check` exit 0, `check-fences.py --check` clean (102 masters). The
witness meter passes (`pass exit=0`, 3.14 s). I did not run
`make check`: I commit nothing. No commit, no push. `git status` shows
only `agents/tasks/LJ-1-606/` untracked; nothing in `src/` moved.

## ARCHIVE USED

- `archive/dev/LJ-dispatch-index.md`: **READ, one row.** `:236` reads
  `| LJ-1.160 | Read the 845-line level substrate against levelIn and cover | THE WALL IS BYPASSED, 16 LINES | Both hypotheses from one crossing face at the collapse image. The wall term is absent |`.
  TOOK the AGE of the crossing face only: the crossing has been the
  named-but-absent term since `[LJ-1.160]`, and this task is the first
  to price its suppliers. **No number in this report is funded against
  that row**, and the crossing was re-measured at its own site here, as
  the Boundary demands.
- `archive/dev/JOURNAL-archived.md`: **declined, not read beyond its
  first line.** `:1` reads `# Archived journal: the retired route`. A
  history, and nothing here needed one.
- `archive/dev/JOURNAL.md`: **declined, not read beyond its first
  line.** `:1` reads `# ARCHIVED 2026-08-20`. Same reason.
- `archive/dev/DECISIONS-archived.md`: **declined, not read beyond its
  first line.** `:1` reads `# Archived decisions: the D series`. The
  live rulings are the five files the program cats; no D-series rule was
  consulted.
- `archive/dev/ORCHESTRATION.md`: **declined, not read beyond its first
  line.** `:1` reads `# ORCHESTRATION: the orchestrator's operating
  rules`. The live rules are the five files the program cats.

## LITERATURE USED

- `dev/literature/devlin-II5.md`: **READ, the condensation chapter's
  chain, in the D-10 pass and in the design of the five legs.** `:95`
  reads

      > By 2.7 there is a Σ₀ formula Φ(z, v, γ) of LST such that

  and `:104-105` reads

      > downward) and along the collapse to M; 1.9.15 converts M's satisfaction of
      > the Σ₀ matrix into ambient Φ; (a) turns Φ into "v = L_γ", giving

  TOOK the whole route: the transfer chain those lines record IS the
  term's five legs, with the delivered `σ₁-up` playing 1.9.15 and G-
  playing (a). `:222` ("witnessed inside the carrier") is G+'s strength
  requirement, and `:228` ("Transfer along elementarity and the
  collapse") is legs E and iso. The tree's `GraphB` is the candidate Φ;
  its adequacy is unbuilt, which is the residue this task prices.
- `dev/literature/digest.md`: **not used.** `:1` reads `# Digest: the
  orthodox form of the rud route, pinned from the collected literature`;
  the crossing is not a rud-route question and the digest carries no
  statement about collapses.
- `dev/literature/truncation-and-selection.md`: **not used.** `:1`
  reads `# Truncation and selection: how the two literatures pick a
  witness`; the term selects nothing, and the non-degeneracy refutations
  need no leastness.
- `dev/literature/terms-2026-08.md`: **not used.** `:1` reads `# The
  terminology dossier: fourteen renderings for the owner's ruling`; no
  glossary term is at issue.
- `dev/literature/geology.md`: **not used.** `:1` reads `# Geology
  dossier: set-theoretic geology sources and the five questions`;
  geology has no bearing on the condensation commute at a hull of a
  level.
