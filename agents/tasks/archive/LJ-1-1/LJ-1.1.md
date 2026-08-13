# LJ-1.1: recon, the GCH route on the internalization tower

tier: codex (default)

## GOAL

Say how `L ⊨ GCH` is proved on the delivered internalization tree, as a block
plan a build campaign can execute, and name the one term whose cost nobody has
measured.

## CWD

`/Users/alsg/Agentic/Bedrock`, on branch `two-tower-bridge`.

## CONTEXT

Bedrock proves Goedel's constructible universe results in cubical Agda. `src/`
today is the **internalization tree**: the L hierarchy built as a Def tower,
with satisfaction internalized as coded formulas over the model. It delivers
`L ⊨ ZF` and `L ⊨ ZFC` (`src/L/Model.lagda.md`). It is 75 masters and 17,492
non-blank in-fence lines, and it typechecks cold in 133.19 s.

**It has never proved GCH.** Phase 1 of the live plan builds that wing, and
your recon is its first step. `[LJ-1.2]` then probes what you name; `[LJ-1.3]`
to `[LJ-1.8]` build it.

**No prose.** DD23 freezes mathematical prose until both trophies land. The
wing is code and nothing else, and your block plan should assume that.

## THE MATHEMATICS, so you can start from the right shape

The textbook route to `L ⊨ GCH` runs through **condensation**. Sketch, and you
should correct it where the delivered tree makes a different shape natural:

1. **A Skolem hull.** For a set `X` inside a stage, take a `Σ₁`-elementary
   substructure of that stage containing `X`, of the same cardinality.
2. **The Mostowski collapse.** The hull is extensional and well-founded, so it
   is isomorphic to a transitive set.
3. **Condensation.** That transitive set IS an earlier stage of the L
   hierarchy. This is the load-bearing step.
4. **Stage cardinality.** Each infinite stage has the cardinality of its index.
5. **Subsets appear early.** A subset of a stage `L_α` lies in some `L_β` with
   `β` not much larger than `α`, by (3) and (4).
6. **GCH.** Count the subsets of an infinite cardinal at the right stage.

## YOUR JOB

**1. READ THE DELIVERED TREE FIRST.** The wing rides what is already there,
and what is already there is unusual: satisfaction is INTERNALIZED as coded
formulas, which is exactly the machinery a `Σ₁`-elementary submodel argument
needs. Say what each of these gives the wing, at `file:line`:

- `src/L/Coding/*` (24 masters). The coded-formula tower: `Model`, `Sat`,
  `Sound`, `Unique`, `Bridge`, `Powerset`, `Uniform`, `CodeSet`, `Closed`.
  **`Bridge` and `Powerset` matter most**: they connect coded satisfaction to
  the definable powerset the tower is built from.
- `src/FOL/LevyHierarchy.lagda.md` and `src/FOL/Absoluteness.lagda.md`. If a
  `Σ₁` notion already exists, the hull step may be far cheaper than a fresh
  build.
- `src/L/Hierarchy.lagda.md`, `src/L/Stage.lagda.md`, `src/L/Rank.lagda.md`,
  `src/L/Ordinal/*`. The tower and its indices.
- `src/L/Reflect.lagda.md` and `src/L/ReflectFo.lagda.md`. Reflection is
  half of a hull argument; say how much of it is reusable.
- `src/V/Smallness.lagda.md` and `src/L/WellOrder/Base.lagda.md`.

**Answer explicitly: what does the internalization tree ALREADY give the GCH
wing that a fresh tower would not?** That is the question that decides the
wing's price, and no document answers it today.

**2. WRITE THE BLOCK PLAN.** One block per deliverable chapter. For each:
what it states, what it depends on, which delivered modules it rides, and a
size estimate with its basis. Map the blocks onto `[LJ-1.3]` to `[LJ-1.8]`,
and say where the plan disagrees with those rows. **The rows are a sketch
written before anyone read the tree; disagreeing with them is a result, not a
problem.** In particular say whether `[LJ-1.6]`, stage cardinality, really is
independent of the condensation chain, since the row claims it runs in
parallel.

**3. NAME THE WIDEST UNMEASURED TERM, and the probe that measures it.** DD8:
a build brief that cannot name both is not ready to send. `[LJ-1.2]` runs
exactly the probe you specify, so specify it concretely: which file, which
statement, what counts as GO and what counts as NO-GO, and roughly what it
costs. One term, the widest. If you believe there are two, rank them and say
why the second is not the first.

**4. GIVE ONE BEST-EFFORT SIZE PROJECTION FOR THE WHOLE WING, AND NAME ITS
BASIS** (DD8). One number or one band, not two calibers: the two-caliber rule
is REVOKED. The basis is what a reader needs, and it is one of three: a probe,
a delivered comparable, or a survey. **Say which, per block.** A projection
resting on a delivered comparable is worth more than one resting on a survey,
and the reader must be able to tell them apart.

**Be accurate rather than safe.** A projection padded against being wrong
later is worse than a wrong one, because it cannot be corrected by evidence:
nobody can tell a cautious number from a real one. If a block is genuinely
unpriceable, say UNPRICED and say what would price it. `dev/LESSONS.md` P-s:
if the budget will not stretch to timing the piece whole, report the slice as
a slice and refuse to divide.

## DD4, WHICH GOES IN EVERY BRIEF

**Maximize the code the two proofs share, and write it generic.** One rule,
two ends. It has NO metric and no checker by the owner's ruling, so it is
stated in every brief and answered in every return; the repetition is its only
enforcement.

**For you, and it is a first-class part of the deliverable.** For every block,
ask whether the content can be written ONCE at a generic carrier and
instantiated, and price BOTH shapes. **A recon that returns only the
fixed-carrier shape has not finished.** The default is generic. A stop-line is
never a reason to write fixed: say so and stop for a re-price.

This matters more here than usual. `L ⊨ AC` is already proved on this tree,
and a GCH wing that shares its machinery is cheaper twice over. Say which
delivered modules the wing should GENERALIZE rather than copy, and which it
should leave alone. The one measured exception is `dev/LESSONS.md` P-r: a fold
over a clause list whose result type every consumer must unfold costs about 3x
the hand-written conjunction.

## ARCHIVE

Per DD18. **The retired rud route built most of this wing already**, on the
OTHER tower, and then the route was replaced. That code is reference, never a
shortcut: DD13 prices a port against a fresh write, and `dev/LESSONS.md` P-l
holds, a measured cure does not transfer by analogy. Read these and say, per
module, whether it is portable, adaptable in shape only, or dead:

| Archived module | Lines | Why it may bear |
|---|---|---|
| `archive/rud-route/src/L/Condensation.lagda.md` | 751 | The load-bearing step, done once |
| `archive/rud-route/src/L/Hull.lagda.md` | 388 | The Skolem hull |
| `archive/rud-route/src/V/Collapse.lagda.md` | 357 | The Mostowski collapse |
| `archive/rud-route/src/L/Cardinal.lagda.md` | 409 | Stage cardinality |
| `archive/rud-route/src/L/CardinalPredicates.lagda.md` | 547 | Its predicates |
| `archive/rud-route/src/L/CardinalCount.lagda.md` | 301 | The counting half |
| `archive/rud-route/src/FOL/Count.lagda.md` | 837 | Finite and infinite counting |

That is about 3,590 lines of directly relevant retired work. **The central
question of this recon is how much of it survives the change of tower**, and a
number you assert without reading the file is worthless.

Also required:

- `archive/rud-route/README.md`. Four things worth knowing, including which
  modules carried the generic machinery.
- `archive/dev/TASKS-archived.md`. 265 rows. `[T9]` was a cardinal gate that
  returned RED; find it and say what it hit. Grep for condensation, hull and
  cardinal rows.
- `archive/dev/DECISIONS-archived.md` when a row's rationale is unclear.
- `dev/LESSONS.md` is NOT archived and still binds. **P-m, P-n, P-t and P-q
  bear directly on your price**: a rate certifies a content class,
  parameterized work runs near 0.01 s per line and instantiation near 0.22,
  and a line lever is not a seconds lever.

Your report carries an **ARCHIVE USED** section: what you read, and what you
took from each, at `file:line`. "I looked at the archive" is not a return.

## MANDATORY RULES FOR A RECON

From `python3 scripts/rules.py --for recon`. These bind this task.

- **D-10. Price the truth of a recorded residue before pricing its proof.** A
  residue names a TARGET, and a target can be false; check the truth at the
  intended generality before pricing the proof, because a Tarskian or
  cardinality obstruction is the usual killer. **For you this is central and
  it is not theoretical: this campaign already lost a bridge kernel to a
  hypothesis that was classically FALSE** (Devlin VI.2.4). Condensation on
  this tower is exactly the kind of statement that can fail at the shape you
  assume. State the condensation lemma you intend to prove, precisely, and say
  what makes you believe it is TRUE of the Def tower.
- **C-22. Write the deliverable incrementally, never at the end.** Create the
  report in your first minutes as a skeleton and fill it as answers land. An
  agent that reads for its whole budget and writes at the end returns nothing.
- **P-l. A statement may be ABOUT a concrete stage without dragging that
  stage's PRESENTATION into its type.** Naming a transparent construction in a
  statement's TYPE is what costs, not being about a concrete position. **This
  is a design instruction for your block plan**, not background: state the
  wing's lemmas at abstract carriers with the stage opaque, and the elaborator
  never unfolds them.
- **D-26. A well-founded key on a tower needs generation data, or it needs
  syntax.** Ask what a stage's members CARRY. A stage built as the values of
  finitely many total operations carries its own generation data. **A stage
  built as a definable power carries NOTHING**, and the Def tower is exactly
  that. This is why the internalized coding exists, and it is the reason the
  wing must ride it rather than route around it.

## SCOPE (read)

In this order: `src/L/Coding/*`, `src/FOL/LevyHierarchy.lagda.md`,
`src/FOL/Absoluteness.lagda.md`, `src/L/{Hierarchy,Stage,Rank,Reflect,
ReflectFo,Model}.lagda.md`, `src/L/Ordinal*`, `src/V/Smallness.lagda.md`.
Then the archived modules above. Then `dev/LESSONS.md`, `dev/PLAN.md`
sections 0, 3 and 11, and `dev/ledger.toml`'s `[ratio]` block.

## SCOPE (write)

`_build/lj-1.1-recon.md` and nothing else. **Write no master.** You may not
touch `src/`, and `src/Everything.lagda.md` is the orchestrator's alone.

## CONSTRAINTS

- **Read-only on the tree.** No edits outside your report. No commit, no push.
- **You may run `agda` on a SINGLE existing master to read its cost**, under
  `GHCRTS=-M8g`, one process, never the whole tree. Say so if you do. Do not
  run `make check`: a full typecheck is the orchestrator's to schedule.
- **Evidence is `file:line`.** A claim about the tree that names no location
  cannot be checked and will be rejected at audit.
- **Separate what you READ from what you INFER.** Both are welcome; confusing
  them is not.
- **A stop is a deliverable.** If the wing cannot be built on this tree, or
  the condensation lemma is false at the shape the plan needs, give the
  evidence and STOP. A refutation is this project's most valuable return class
  and several have landed.
- Write ASD-STE100 Simplified Technical English: active voice, one instruction
  per sentence, 20 words or fewer for an instruction, no em dash.

## RETURN

Write `_build/lj-1.1-recon.md` INCREMENTALLY, skeleton first. Structure:

1. **VERDICT.** Can `L ⊨ GCH` be built on this tree, and what is the shape of
   the route. One paragraph.
2. **WHAT THE DELIVERED TREE ALREADY GIVES**, module by module, at
   `file:line`. This is the section that decides the price.
3. **THE CONDENSATION LEMMA, STATED PRECISELY**, with why you believe it true
   of the Def tower (D-10).
4. **THE BLOCK PLAN.** One block per chapter: statement, dependencies,
   delivered modules it rides, generic-or-fixed with both prices (DD4), size
   estimate with its basis named as probe, comparable or survey.
5. **THE WIDEST UNMEASURED TERM AND ITS PROBE**, specified concretely enough
   for `[LJ-1.2]` to run without asking you anything.
6. **ONE BEST-EFFORT PROJECTION FOR THE WING**, with its basis. Mark any
   UNPRICED block as unpriced.
7. **WHERE I DISAGREE WITH THE `[LJ-1.x]` ROWS**, if anywhere.
8. **ARCHIVE USED**, per module, with the portable / adaptable / dead verdict.
9. **WHAT I AM NOT SURE OF**, and what evidence would close each item.
