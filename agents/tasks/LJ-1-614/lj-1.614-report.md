# LJ-1.614 report: the restated face G+, and whether the crossing accepts it

## HEAD

head_slot: coder
machine: shared
verdict: NO-GO on `graph-stage-at`, and the NO-GO is the brief's own
second outcome: **the crossing's G+ SLOT accepts the restated face at every
`inL`-image matrix, and the crossing's KIT rejects the restated matrix `ψ₀`
outright** - measured as a refutation term, not argued. The stop is stated at
`agents/tasks/LJ-1-614/review-of-graph-stage-at.md`.

Written as a skeleton before any Agda beyond W3 and filled as each answer
landed (C-22). No commit, no push. I wrote only inside
`agents/tasks/LJ-1-614/`. Agda ran under the caliber the program set on this
pane, `GHCRTS="-A64m -I0 -M2g"`, ONE Agda process at a time. I did not set
`GHCRTS`. Nothing is postulated, the probe carries `--safe`, the delivered
file is green and carries no hole, and nothing lands in `src/`. The probe is
a raw `.agda` file, so it carries no ` ```agda ` fence, counts 0 in-fence
lines, and the ratio bar cannot fire on it.

**NO HEAP WALL WAS MET ANYWHERE IN THIS TASK.** The highest peak of any run
is 970,375,168 bytes against the 2,147,483,648-byte cap (the floor run,
`runs/floor-1.out`), and the longest run is 5.16 s against the caps I set
(120 s for W3, 300 s for the floor and every probe run). No run was killed
and no run printed a heap message.

## D-10, BEFORE ANY AGDA: WHAT THE CROSSING DEMANDS OF G+

**THE DEMAND IS THREE BINDINGS, NOT ONE SLOT.** The crossing is
`Crossing` at `agents/tasks/LJ-1-606/Probe606.agda:178-180`:

    Σ[ ψ ∈ Formula CI.I.SM 3 ] ( Δ₀ ψ × GraphStage ψ × GraphAmbient ψ )

1. **The carrier.** The matrix is bound at the HULL carrier
   `Formula CI.I.SM 3` (`Probe606.agda:178`), which is `DR.SM`
   judgmentally ([LJ-1.610]'s recorded identity,
   `agents/tasks/LJ-1-610/Probe610.agda:99-101`).
2. **The grade.** The kit's first component is `Δ₀ ψ` (`:180`), and it is
   spent at leg 4: `Σ₁-carried CI.I.g ψ dψ` (`Probe606.agda:238`, the
   lemma at `:201-204`) consumes `dψ` to lift the collapsed statement to
   the ambient.
3. **The reading.** `GraphStage ψ` (`Probe606.agda:156-159`): at every
   hull level-pair, the STAGE's inner world satisfies
   `mapFo DR.inL (∃̇ ψ)` at the `inL`-image of the pair. The consumer
   spends it once, at `q = (Lset δ, _)`, `γ = (δ, _)`
   (`Probe606.agda:226-227`).

The middle legs put the same carrier on the matrix: leg 2 is face E
(`Probe606.agda:230`), whose delivered type binds `φ : Formula SM n`
(`src/L/BoundedSubset.lagda.md:410-412`), and leg 3 is the collapse
transfer (`Probe606.agda:233`), whose type binds the same
(`src/L/BoundedSubset.lagda.md:195-197`). Leg 5 decodes at the collapsed
constants (`Probe606.agda:246`).

**DOES `GraphStageAt` MEET THE DEMAND?** It meets demand 3, at image
matrices, definitionally (section DOES THE CROSSING ACCEPT IT below). It
does not meet demands 1 and 2 at the restated matrix `ψ₀`, and no hull
matrix over `ψ₀` can meet them: that is the refutation this task lands.
**So this task was a kit change and not a face build, and D-10 said so
before any Agda beyond W3 was spent.** The spend that followed was the
spend the brief itself funds ("the risk is the consumer, not the face"):
the acceptance term, the consumption term, and the refutation term.

## W3, THE WIDEST UNMEASURED TERM

**GO, AND THE SLOT DOES NOT REJECT.** The slice is
`agents/tasks/LJ-1-614/runs/W3.agda`, written FIRST and typechecked
ALONE. The type is `SlotAt` at `runs/W3.agda:59-63`: leg 1's demand with
the matrix at the stage carrier, the stage's inner satisfaction of the
Sigma-one closure at the `inL`-image of every hull level-pair,
`GraphStageAt` imported from `[LJ-1.610]` and not restated.
`runs/w3-4.out` is **exit 0 at 2.50 s, peak 784,351,232 bytes**, under
the 120-second cap the brief set. Three runs precede it
(`runs/w3-1.out`, `w3-2.out`, `w3-3.out`, all exit 42): each was a
one-line shape error in my own slice (a missing `∈ˢ` import, the outer
module not instantiated, the frame arguments mis-ordered), fixed in
place and recorded. The brief estimated about 12 lines; the type is 5
and the slice that holds it is 62 lines, most of it the frame and the
import. The slot's acceptance as a TERM is `slot-accepts` in the probe,
and it is one definitional line, so W3's 2.50 s prices the whole
question the brief called widest.

## THE FLOOR

Measured before the proof, as the owner ruled on 2026-08-23.
`runs/FLOOR.agda` is the probe's frame with my seven term bodies at
designed holes; `runs/floor-1.out` is **exit 42 at exactly those holes,
5.16 s, peak 970,375,168 bytes**. The frame, with both predecessors'
frames instantiated at the six slots, costs about 5.2 s. The full probe
then ran FASTER than the holed floor (3.71 s first green, 3.84 s forced
cold), so my terms add no measurable cost; the elaboration frame is the
whole price. The imports were trimmed to the rows my own code uses: the
probe carries 16 `open import` and `import` lines against `[LJ-1.606]`'s 19, and
pulls none of `L.Coding.Model`'s or `L.Ordinal`'s set theory, only the
two predecessor probes and the syntax modules.

## DOES THE CROSSING ACCEPT IT

**AT THE SLOT, YES, AND THE CROSSING ITSELF THEN CONSUMES THE RESTATED
FACE.** `slot-accepts` (`agents/tasks/LJ-1-614/Probe614.agda:129-132`)
inhabits

    (ψ : Formula DR.SM 3) → GraphStageAt (mapFo DR.inL ψ) → GraphStage ψ

in ONE line with NO transport: `map DR.inL (q ∷ γ ∷ [])` is
`DR.inL q ∷ DR.inL γ ∷ []`, `mapFo DR.inL (∃̇ ψ)` is
`∃̇ mapFo DR.inL ψ` (`src/FOL/Manipulation/Relabelling.lagda.md:64`),
and `fst (DR.inL q)` is `fst q`, all definitional. The kit with its G+
component restated at the image matrix is `CrossingAt`
(`Probe614.agda:143-145`); `crossing-at→crossing` (`:148-150`) converts
it into `[LJ-1.606]`'s own `Crossing` by `slot-accepts` alone; and
`inner-to-ambient-at` (`:152-154`) is `[LJ-1.606]`'s own term applied to
the conversion. No leg was rebuilt.

**AT THE KIT, NO, AND THE REJECTION IS A TERM.** `kit-rejects-ψ₀`
(`Probe614.agda:173-178`) inhabits

    (ψ : Formula DR.SM 3) → mapFo DR.inL ψ ≡ ψ₀ → Δ₀ ψ → Empty.⊥

For any such `ψ`, `mapFo-Δ₀` (`Probe606.agda:189-199`) gives `Δ₀ ψ₀`,
the implication inversion gives `Δ₀ matrixSL`, and the conjunct
inversions reach `Δ₀ (mapFo numSL (domAt zero (suc (suc zero))))`; but
`domAt` is headed by an UNBOUNDED `∀̇` (`src/L/Coding/Model.lagda.md:278-280`),
a head for which the Delta-zero datatype has NO constructor
(`src/FOL/LevyHierarchy.lagda.md:47-58`). The absurd pattern
`no-Δ₀-matrixSL (δ-∧ (δ-∧ () _) _)` (`Probe614.agda:167-168`) is the
whole proof. **This is [LJ-1.610]'s wall 3 moved from a supply statement
to a refutation.**

**WHAT ELSE MUST MOVE.** One of exactly two things, and both are kit
changes. Either the kit's binding moves: the carrier and grade at
`Probe606.agda:178-180` become the arity-4 kit with the bound as a slot,
the stronger repair the ruling rejected. Or the middle moves: face E
(`src/L/BoundedSubset.lagda.md:410-412`, spent at `Probe606.agda:230`)
and the collapse transfer (`src/L/BoundedSubset.lagda.md:195-197`, spent
at `:233`) would have to accept stage-carrier formulas, which unpays
`[LJ-1.609]`'s delivered face E; and on my reading that repair still
owes a NEW face, because the stage-side lift `σ₁-up` carries statements
along `fst` to the ambient at the UNCOLLAPSED pair
(`src/FOL/Absoluteness.lagda.md:182-183`), while the commute's decode
needs the COLLAPSED pair `(π (Lset δ), π δ)`, which only the hull-bound
transfer reaches. That last sentence is a reading at `file:line`, not a
measured refutation, and the report marks it as one.

## WHAT THE CROSSING NOW WANTS

Of the three faces, **after this task**:

- **Face E is paid**, by `[LJ-1.609]` at these six slots
  (`agents/tasks/LJ-1-609/lj-1.609-report.md`, `elem-down-at` at
  `Probe609.agda:357-365`). Its currency binds hull formulas
  (`src/L/BoundedSubset.lagda.md:410-412`), so it serves a hull-bound
  kit and nothing else.
- **Face G+ is NOT paid.** It is REDUCED, twice over: to `WitStage` at
  the restated matrix by `[LJ-1.610]` (`graph-stage-from-wit`), and the
  same reduction is imported green here (`Probe614.agda:194-195`). The
  residue `WitStage` is wall 1, the sequence-in-stage construction,
  priced by nobody. At the kit's OWN matrix, G+ wants a
  witness-in-carrier at that matrix, and the matrix itself has no
  supplier at arity 3 (wall 3, now a refutation at the identity route).
- **Face G- is NOT paid.** `[LJ-1.611]` is a NO-GO on it and names the
  honest target there (`Honest-G-`, `Probe611.agda:175-177`).

**I read no discharge into anything I did not inhabit.** What I
inhabited this task: the acceptance, the consumption, and the
refutation. What I did not inhabit: any of the three faces, the residue
`WitStage`, and the obligation `graph-stage-at` itself, which is
deliberately absent (`runs/meter-1.out`: `missing exit=42`, `1 UNRESOLVED
of 1`, `probe_red=False`, 3.07 s).

So the crossing does NOT want "only G-". It wants G-, the kit matrix
(walls 2 and 3 at the binding), and the witness (wall 1), and this task
measured that the cheaper repair leaves exactly that wanting.

## THE PRICE

All runs under the program's caliber `GHCRTS=[-A64m -I0 -M2g]`, which I
did not set. One Agda process at a time. Caps: 120 s for W3, 300 s for
the floor and the probe.

| run | what | exit | time | peak RSS |
|---|---|---:|---:|---:|
| `runs/w3-4.out` | W3, type only, alone, first green | 0 | 2.50 s | 784,351,232 |
| `runs/floor-1.out` | frame with the seven term bodies at holes | 42 | 5.16 s | 970,375,168 |
| `runs/p-1.out` | the probe, first full green | 0 | 3.71 s | 831,307,776 |
| `runs/p-2-forced.out` | the probe, interface deleted | 0 | 3.72 s | 831,291,392 |
| `runs/p-3-final.out` | delivered file, interface deleted, after the citation fix | 0 | 3.84 s | 831,291,392 |
| `runs/meter-1.out` | the witness meter | missing 42 | 3.07 s | not metered |

The probe is 195 lines. The brief estimated about 160, of which about 40
for the obligation. The estimate is close on the file and wrong on the
split, for a measured reason: the obligation's term already sat green in
`[LJ-1.610]`'s probe, so landing it again costs two lines of import, and
the real weight, as the brief itself predicted, was the consumer.

## THE FINDING

**THE RULING'S PREMISE HALF-HELD, AND THE HALF THAT FAILED IS THE HALF
THE RULING WAS FOR.** The cheaper repair IS prototyped, and the crossing
DOES accept its face-type, at every image matrix, for one definitional
line. What the cheaper repair does not pay is the kit the crossing is:
the carrier and the grade at `Probe606.agda:178-180`. The guard that
dodged the walls inside the face's own statement does nothing at the
kit's binding, because the grade demand there is about the matrix's
SYNTAX, and the machine matrix's syntax carries unbounded quantifiers
under `mapFo`, guard or no guard. The NO-GO therefore overturns the
ruling by the measurement the brief asked for, and the two candidate
repairs are the two the ruling chose between, now with the prices this
report records.

**PREMISE CHECKS.** Premise 11's basis is BROKEN: `R-42` does not exist
anywhere in the tree (no hit for `R-42` over `dev/` and `archive/`;
`dev/LESSONS.md:4404` is the `Related` line of entry C-52, and the
respelling figures 1.74 s and 155.02 s appear nowhere in `dev/LESSONS.md`).
The instruction it was cited for, "import it, do not restate it", stands
on the brief's own ruling text and was followed. Premise 13 cites
`AGENTS.md:74` for the `make check` rule; the sentence sits at `:75`.
All other premises checked at their lines, including
`dev/literature/devlin-II5.md:222` ("witnessed inside the carrier") and
`src/FOL/LevyHierarchy.lagda.md:75` (`σ-∃`, the constructor the refutation
never gets to use).

## W2

The mathematics was written once, at generic carriers, by the
predecessors, and this task imported all of it: both frames, the
restated face `GraphStageAt`, the matrix `ψ₀`, the residue `WitStage`,
the reduction `graph-stage-from-wit`, `mapFo-Δ₀`, the whole crossing
`inner-to-ambient`, and face E's binding. Nothing was restated at a
second carrier. The new terms are single-site and generic where they
could be: `slot-accepts` is generic in the kit matrix `ψ`, the
conversion is generic in the kit, and the refutation is generic in the
hull matrix `ψ` it refutes. W4: no module was retired this task, so
nothing moved to `archive/` and no `dev/ARCHIVE.md` row is owed.

## WHAT THE NEXT BRIEF NEEDS

1. **THE CHOICE IS NOW OWNED BY ITS PRICES.** The arity-4 kit: its
   Delta-zero body exists (`levelHoodB`,
   `src/L/BoundedSubset.lagda.md:108-114`), and the kit's legs are
   arity-polymorphic AS TYPES (face E at `src/L/BoundedSubset.lagda.md:410-412`
   and the transfer at `:195-197` bind `n : ℕ`), so whether the arity
   change re-opens face E is a TERM question, measurable before the kit
   is built. The stage-carrier middle: it unpays `[LJ-1.609]` and, per
   the reading above, still owes a collapse-crossing face nothing
   delivers.
2. **DO NOT FUND A THIRD LANDING OF THE REDUCTION.** The face at `ψ₀`
   follows from `WitStage` and that fact is green in the tree twice
   (`[LJ-1.610]` and `Probe614.agda:194-195`). The next spend on G+ is
   `WitStage` itself (wall 1, the sequence-in-stage construction,
   Devlin 2.6(ii)) or nothing.
3. **WALL 3 IS NOW A TERM AT THE IDENTITY ROUTE.** Any future kit that
   keeps arity 3 and the hull carrier must either find a non-identity
   matrix (`[LJ-1.610]`'s wall 3 supply statement plus `[LJ-1.606]`'s
   `NoDegenerate` at `Probe606.agda:260-280` say none is hosted and junk
   fails G-) or overturn the refutation at `Probe614.agda:173-178`.

## SCOPE

I wrote only inside `agents/tasks/LJ-1-614/`:
`Probe614.agda`, `runs/W3.agda`, `runs/FLOOR.agda`, `runs/run.sh`,
`runs/*.out`, `lj-1.614-report.md`, `review-of-graph-stage-at.md`. Gates
run: `lint-agda.py --check` exit 0, `check-probes.py --check` clean
(7807 tracked files), `check-fences.py --check` clean (102 masters). The
witness meter returns `missing exit=42`, `1 UNRESOLVED of 1`,
`probe_red=False` (`runs/meter-1.out`, 3.07 s). I did not run
`make check`: I commit nothing. No commit, no push. `git status` shows
only `agents/tasks/LJ-1-614/` untracked; nothing in `src/` moved.

## ARCHIVE USED

- `archive/dev/LJ-dispatch-index.md`: **READ, its tail.** `:481` reads
  `| LJ-3.9 | The prose phase opens | planned | DD23. Only after LJ-3.8 passes. Chapter narrative and the trilingual exposition, nothing before |`.
  CHECKED for a predecessor row for the LJ-1.6xx probe family: none
  exists, the index predates them. **No number in this report is funded
  against that file.**
- `archive/dev/JOURNAL-archived.md`: **declined, not read beyond its
  first line.** `:1` reads `# Archived journal: the retired route`. A
  history of a retired route; this task's predecessors are live probes
  whose reports were read directly instead.
- `archive/dev/JOURNAL.md`: **declined, not read beyond its first
  line.** `:1` reads `# ARCHIVED 2026-08-20`. Same reason.
- `archive/dev/DECISIONS-archived.md`: **declined, not read beyond its
  first line.** `:1` reads `# Archived decisions: the D series`. The
  rulings that bind this task arrived in the five catted files and the
  brief, and cite their own homes.
- `archive/dev/ORCHESTRATION.md`: **declined, not read beyond its first
  line.** `:1` reads `# ORCHESTRATION: the orchestrator's operating
  rules`. Operating rules for the program's own harness; nothing in this
  task's mathematics needed them.

## LITERATURE USED

- `dev/literature/devlin-II5.md`: **READ, the (b) clause.** `:222`
  reads `   γ < α. Strength: the Σ₁ form is "witnessed inside the carrier", not`
  (the sentence continues at `:223`, "merely in V"). TOOK it as the
  truth check on what the restated face's existential demands: the
  witness must live inside the stage, which is why `WitStage` is the
  residue and why no restatement of the face dodges wall 1.
- `dev/literature/level-formula-slot-roles.md`: **READ, the bound law.**
  `:40` reads `### 2.2 ONE bound binds ALL the unbounded quantifiers`
  and `:43` reads `**MEASURED, within that corpus: no formalization writes an object-level`.
  TOOK both for the next brief's pricing: the arity-4 kit's single
  bound slot is the delivered design answer to `domAt`'s and `extAt`'s
  unbounded quantifiers, and the corpus-measured rarity of slotted
  level-hood formulas prices its risk.
- `dev/literature/digest.md`: **not used.** `:1` reads `# Digest: the
  orthodox form of the rud route, pinned from the collected literature`;
  the rud route is not on this task's stage.
- `dev/literature/truncation-and-selection.md`: **not used.** `:1`
  reads `# Truncation and selection: how the two literatures pick a
  witness`; this task truncated nothing new and selected no witness.
- `dev/literature/terms-2026-08.md`: **not used.** `:1` reads `# The
  terminology dossier: fourteen renderings for the owner's ruling`; no
  glossary term was chosen or added, so the dossier's protocol never
  opened.
