# LJ-1.598: adversarial review of the LJ-1.598#1 return

## HEAD
head_slot: mathematician_adversarial
machine: shared
verdict: upheld

The return under attack is `agents/tasks/LJ-1-598/lj-1.598-report.md`
with its stated NO-GO
`agents/tasks/LJ-1-598/review-of-defines-level.md`. The critic is not
the author of either file. I read the brief
`agents/tasks/LJ-1-598/LJ-1.598.md`, the probe
`agents/tasks/LJ-1-598/Probe598.agda`, the floor slices under
`agents/tasks/LJ-1-598/runs/`, and every `file:line` the return names.
I ran `grep -rn "IsOrd (HS.C.π" agents/ src/` and read every hit, to
test the C-42 sweep by my own search and not by its word.

## THE RECORD THE BRIEF NAMED, AND WHAT IT HOLDS

The brief told me to read every line of
`dev/pod/transitions/2026-08.jsonl` that carries `"task": "LJ-1.598"`
for `model`, `effort` and `heads_sha256`. That record does not exist.
`dev/pod/transitions/2026-08.jsonl` has 157 lines. Its last line is
dated 2026-08-19 and names another task. Quote at
`dev/pod/transitions/2026-08.jsonl:157`:
`"task": "LJ-1.399", "tier": "wide", "to": "RETURNED"`. No line of
that file names `LJ-1.598`. The brief said to say so and use the
accept arm. I do.

- The six facts are at `agents/tasks/LJ-1-598/runs/accept-1.out:26`.
  They hold `exit_code` 42, `error_class` `unsolved_meta`,
  `heap_wall` false, `lines` 0, `obligations_delta` 0,
  `obligations_open` 1, `seconds` 18.87. Line 21 of the same file
  reads `# obligations delta 0` and line 24 reads `# exit 42`.
- Line 16 reads `# run agents/tasks/LJ-1-598/Probe598.agda rc 0 seconds 2.6`.
- Line 17 reads `# run agents/tasks/LJ-1-598/runs/FLOOR.agda rc 42 seconds 18.87`.
- `heads_sha256` is at `agents/tasks/LJ-1-598/.pod:1`:
  `heads=4d3d5ee0687a34aa87be8c1cf27a492f07e6a08cfdd3054d898068f11ffe1ba5`.
- `model` and `effort` for this instance are recorded nowhere I can
  resolve. I searched `dev/pod/transitions/2026-08.jsonl` and
  `agents/tasks/LJ-1-598/`. I report the absence and proceed on the
  facts that do resolve.

The facts that do resolve agree with the return on the obligation:
delta 0, one obligation still open, the delivered probe green, the
name `defines-level` absent. The dispatch to this slot came from a
stated NO-GO with `review-of-defines-level.md`.

## QUESTION 1: DOES THE VERDICT LINE MATCH THE BODY

The verdict line is at `agents/tasks/LJ-1-598/lj-1.598-report.md:6`:
`verdict: NO-GO on `defines-level`; the clause is priced by two landed reductions, and its index hypothesis is wrong for every level formula the tree has`.
Read with the VERDICT section at `:25-28` and the stop at
`agents/tasks/LJ-1-598/review-of-defines-level.md:5-16`, it claims
three things: the obligation is not inhabited; two reductions price
it; the index hypothesis does not match the tree's level formula.
I checked each claim against the body and against the tree.

- The obligation is not inhabited. No declaration
  `defines-level` stands in `agents/tasks/LJ-1-598/Probe598.agda`.
  The probe says so at `:29-31`. The accept arm records
  `obligations_delta` 0 and `obligations_open` 1 at
  `agents/tasks/LJ-1-598/runs/accept-1.out:26`. The stop file
  records the meter result at `:7-8`:
  `missing exit=42 ... [NotInScope]`.
- Two reductions landed and typecheck. `coded-gives-level` is at
  `Probe598.agda:171`. `graph-gives-level` is at `:220`.
  `preimage-gives-level` composes the second with the bridge at
  `:261-264`. The delivered file is green:
  `agents/tasks/LJ-1-598/runs/p-final.out:3` and `:22` read
  `Checking LJ-1-598.Probe598` and `EXIT=0`. The accept arm
  rechecked the same file at 2.6 s, rc 0
  (`accept-1.out:16`).
- The graph cannot meet the type as stated. `Cert.DefinesLevel`
  at `agents/tasks/LJ-1-578/Probe578.agda:236-237` hypothesizes
  `IsOrd (HS.C.π (fst (T.val c)))` and concludes
  `fst a ≡ Lset (fst (T.val c))` at `:240`. `Lset-only` at
  `src/L/Hierarchy.lagda.md:334-335` spends `IsOrd` of the
  argument itself:
  `Lset-only : ⟨ γ ⊨ LsetGraphAt w b ⟩ → IsOrd (fst (lookup b γ))`.
  `graph-gives-level` at `Probe598.agda:221` therefore asks
  `IsOrd (fst (T.val c))`, which is not the type's hypothesis.
  The restated `ClauseI` at `Probe598.agda:118-124` matches
  `DefinesLevel` letter for letter.

One sentence of the line is wider than the body. The line says
the index hypothesis is wrong "for every level formula the tree
has". The body names two routes, not every conceivable formula.
The equation route at `Probe598.agda:157-177` does not spend
`IsOrd` of the index at all: `eq-uniq` at `:163-165` is the
path `h`. The stop file is the precise statement, at
`review-of-defines-level.md:12-16`: this is a NO-GO of supply
and a correction of the target. The body also says, at
`lj-1.598-report.md:54-57`, that no term of the stated type
can be built from the delivered machinery. That is a supply
claim. It is not a refutation of the type. `coded-gives-level`
at `Probe598.agda:171` inhabits `ClauseI` from `CodedLevels`,
and `cert-gives-A` at `Probe578.agda:254-255` derives
`HasLevels` from `DefinesLevel`. The two are payment of each
other. The type is unpaid, not shown false. The body itself
records this at `lj-1.598-report.md:118-122` (the equation
route is circular for the certificate). The verdict line does
not say the type was refuted. The line matches the body on
the NO-GO. The loose "every" is a wording defect. It does not
change the verdict and I do not overturn on it.

## QUESTION 2: DOES EVERY LOAD-BEARING CLAIM RESOLVE

I opened every `file:line` the return and its NO-GO file name.
The load-bearing claims that resolve today:

- `agents/tasks/LJ-1-578/Probe578.agda:234-240`, clause (i).
  Quote at `:236-237`:
  `(c : T.Code) → IsOrd (HS.C.π (fst (T.val c)))`.
- `Probe578.agda:120-122`, `HasLevels`. Quote at `:121-122`:
  `HasLevels = (δ : SV.S) → ⟨ δ ∈ˢ HS.M ⟩ → IsOrd (HS.C.π δ)`.
- `Probe578.agda:254-255`, `cert-gives-A`:
  `cert-gives-A : DefinesLevel → F.HasLevels`.
- `src/L/Hierarchy.lagda.md:334-335`, `Lset-only`, quoted
  above. The same `IsOrd` is spent by `step-Lset` at
  `src/L/Hierarchy.lagda.md:191`:
  `step-Lset : ⟨ γ ⊨ StepAt v b f ⟩ → IsOrd (fst (lookup b γ))`.
- `src/L/Condensation.lagda.md:422-425`, `ride-only` as
  `Lset-only` re-exported.
- `agents/tasks/LJ-1-570/Probe570.agda:289-294`, `GraphAgree`,
  a type, not a term.
- `agents/tasks/LJ-1-570/lj-1.570-report.md:96`:
  `| 1 | `GraphAgree`, one direction of row six | `Probe570.agda:289-294` | parts are TERMS in five tracked probes, NONE in `src/` |`.
- `src/FOL/Semantics.lagda.md:99`, `γ ⊨ ⊥̇        = ⊥`.
- `src/Base/Truth.lagda.md:121`:
  `so `⟨ ⊥ ⟩` **is** `⊥*`{.Agda}.`. The vacuity term
  `only-level-vacuous` at `Probe598.agda:104-105` is
  `only-level-vacuous c = ⊥̇ , λ a h → Empty.rec* h`.
  The accept arm records `unbound_vacuous: true` at
  `accept-1.out:26`. The W3 finding is measured, not argued.
- `src/L/Constructible.lagda.md:227`, `Lset-compute`.
- `src/L/Coding/Sequence.lagda.md:126-131`, `StepOf`, and
  `:286-289`, `ApproxAt` as `domAt` plus the step condition.
- `src/L/Hull.lagda.md:79-90`, `search` and `val`.
- `src/L/Hull.lagda.md:47`, `TermAlgebra`.
- `dev/literature/devlin-II5.md:99`:
  `> (b) (∀γ < α)(∀v)[v = L_γ ↔ v ∈ L_α ∧ L_α ⊨ ∃z φ(z, v, γ)].`
- `agents/tasks/LJ-1-595/review-of-defines-cover.md:83-85`,
  the open substitution question. `inF` at
  `Probe598.agda:217-218` binds the index and equates it with
  the code. That answers the question the sibling stop left.
- Floor wall, first slice:
  `agents/tasks/LJ-1-598/runs/floor-1.out:15-16` and `:36`,
  heap exhausted at 2147483648 bytes, `EXIT=251`, 57.90 s,
  last module `LJ-1-570.Probe570` at `:14`.
- Certificate file alone, dependencies warm:
  `runs/chain-578.out:4-6` and `:25`, heap exhausted,
  `EXIT=251`, 15.92 s, peak 1901936640.
- Trimmed floor: `runs/floor2-1.out:4-6` and `:8`,
  `[UnsolvedInteractionMetas]`, 2.48 s, peak 723271680,
  `EXIT=42`.
- W3 slice: `runs/w3-2.out:3` and `:5` and `:22`, exit 0,
  2.82 s, peak 598622208. The type at
  `runs/W3.agda:52-57` is letter for letter
  `Probe598.agda:87-92`.
- Chain peaks at most 795279360 for the four green modules:
  `runs/chain-564.out:4` is 795279360. The other three are
  764854272, 399753216, 713506816.
- Whole-probe line count. The return's own method at
  `lj-1.598-report.md:225-226` is
  `awk 'NF' file | grep -cv '^\s*--'`. On
  `Probe598.agda` that count is 103 of 264, as the PRICE
  table says at `:230`.

The following load-bearing citations do not resolve to the
content the return assigns them, or the number is wrong.

1. `lj-1.578-report.md:96-100`, first use, at
   `lj-1.598-report.md:51-53`. Those lines of the 578 report
   are the W3 paragraph on `cover`, quote at `:93`:
   `**IT IS `cover`, AND THE MARK IS `[LJ-1.570]`'s OWN.**`
   They are not a GraphAgree mark. The GraphAgree mark in
   that file is at `lj-1.578-report.md:50`, and it points at
   `lj-1.570-report.md:96-100`, which does resolve. The
   later use at `lj-1.598-report.md:143` cites the 570
   report and is correct. The first use is a wrong pointer
   to the right fact.
2. `src/FOL/ZFStructure.lagda.md:148` "on top of `:82`",
   at `lj-1.598-report.md:111`. Line 148 is the restriction
   equality
   `; _≈ˢ_   = λ a b → fst a ≈ˢ fst b`.
   Line 82 of the same file is prose about `_∈ᵗ_`, not
   equality. Path equality of the V structure is
   `src/V/Hierarchy.lagda.md:82`:
   `; _≈ˢ_   = λ x y → (x ≡ y) , setIsSet x y`.
   The claim that a satisfied equation is the wanted path
   is still measured: `eq-uniq d a h = h` typechecks at
   `Probe598.agda:165` and the probe is green. The citation
   is off by file. The fact is not.
3. `runs/FLOOR.agda` line count. The PRICE table at
   `lj-1.598-report.md:239` says 44 lines. The file has 40.
   The code-line count 24 is right under the named method.
4. Per-section code counts in the same table. They sum to
   98, not to the whole-file 103 that the same table states
   and that the named method reproduces. I measure
   `:1-66` as 20, not 30; `:67-76` as 7, not 3;
   `:108-138` as 16, not 12; `:139-179` as 17, not 16;
   `:180-241` as 28, not 24; `:242-264` as 7, not 5.
   The two-reduction "45 code lines" at `:253` inherits
   those undercounts. The whole-file 103 is the figure that
   survives.
5. `lj-1.598-report.md:89`, "The floor is 0.35 GiB against
   the 2 GiB cap." The byte figure 723271680 is
   `floor2-1.out:8` and is sound. 723271680 / 1073741824
   is about 0.67 GiB, not 0.35 GiB. 723271680 / 2147483648
   is about 0.34 of the 2 GiB cap. The sentence writes the
   ratio as a GiB figure. The byte number is the one to
   keep.
6. `agents/tasks/LJ-1-595/Probe595.agda:495`, at
   `lj-1.598-report.md:132`. Line 495 is a comment. The
   clause-(ii) formula `coverFo` is at `:498-499`. The
   shape is the one the return describes. The line is off
   by four.
7. The sixteen-name meter. The return at
   `lj-1.598-report.md:31-33` says each of sixteen names
   returns `pass`, 2.33 s to 2.57 s per run. I count
   sixteen declarations in `Probe598.agda` (`OnlyLevel`
   through `preimage-gives-level`). No per-name `.out`
   file exists under `runs/`. The group is green by
   `p-final.out` and by `accept-1.out:16`. The per-name
   times are not in the tree.

The D-10 reading's displayed collapse equation does not
resolve, and the ordinal-hood claim does not survive in
the case the hull the certificate uses would actually
build. `lj-1.598-report.md:189-191` writes
`its collapse is `{π {∅}} = {∅} = 1``.
`π-compute` at `src/V/Collapse.lagda.md:58` is
`π x ≡ step x (λ y _ → π y)`, and `step` at `:47-48`
collects `π` of the members of `x` that lie in the
carrier. For `δ = {{∅}}` that is `{ π({∅}) }` if `{∅}`
is in the hull, else the empty set. `π({∅}) = {∅}`
when `∅` is in the carrier, so `π({{∅}}) = {{∅}}` when
`{∅}` is in the hull. The displayed equation is
`π({∅})`, one rank too low. `IsOrd` at
`src/L/Constructible.lagda.md:141-142` is
`IsOrd A = isTransV A × ((x : S) → ⟨ x ∈ˢ A ⟩ → isTransV x)`.
`{{∅}}` is not transitive, so it is not `IsOrd`.
Therefore:

- If `{∅}` is in the hull, `π({{∅}}) = {{∅}}` is not
  an ordinal, the hypothesis of clause (i) fails at
  this code, and the example does not apply.
- If `{∅}` is not in the hull, `π({{∅}}) = ∅` is an
  ordinal, the hypothesis holds, and the graph/tower
  mismatch the return computes from `StepOf` and
  `Lset-compute` would apply.

The return says at `lj-1.598-report.md:187-188` that
`δ = {{∅}}` is a code value in every hull, as a unique
satisfier. The hull is the term algebra at
`src/L/Hull.lagda.md:72-91`. Both `{∅}` and `{{∅}}`
are unique satisfiers of closed formulas at a stage
that contains the hereditarily finite sets, so a hull
that lands one by `search` lands the other. That is
the first bullet, where the hypothesis does not fire.
The example is a reading, as the return says at
`:174-175`. It is not a verified code at which
`DefinesLevel` is required and the graph disagrees.
The structural supply fact that remains is independent
of this example: `Lset-only` spends `IsOrd` of the
preimage, the type gives `IsOrd` of the collapse, and
no delivered term fills the distance.

The accept arm and the floor logs disagree on one point the
return treats as closed. `accept-1.out:17` ran the current
`runs/FLOOR.agda` (the Probe578 import and a hole, at
`FLOOR.agda:28` and `:40`) to rc 42 in 18.87 s, with
`heap_wall` false at `:26`. The worker's own
`floor-1.out` and `chain-578.out` are heap walls under the
same stated caliber. Both records stand. The sentence at
`lj-1.598-report.md:77-78` that the certificate's own
file "cannot be checked under the standing wide cap at
all" is stronger than the accept arm. The conservative
advice not to import that file as a supplier frame remains
supported by the two wall logs. It is not supported as an
absolute.

None of these citation defects removes the supply NO-GO.
The obligation name is absent, the probe is green, the two
reductions are the terms the body describes, and
`Lset-only` does spend `IsOrd` of the argument.

## QUESTION 3: IS THE PREDECESSOR'S ENUMERATION COMPLETE

The C-42 sweep searched `IsOrd (HS.C.π` in `agents/` and
`src/`. I ran the same command. Hits in
`agents/tasks/LJ-1-578/Probe578.agda` are `HasLevels` at
`:121`, `LevelsCommute` at `:127`, `Covered` at `:135`,
`DefinesLevel` at `:236`, `DefinesCover` at `:250`,
internal uses in `cert-gives-A` at `:261-262`, and
`DefinesLevelAcross` at `:505`. Nothing in `src/` matches.
The return names four of those as the shape, at
`lj-1.598-report.md:277-283`, and excludes the clause-(ii)
family as concluding ordinal-hood of a witness. That
exclusion matches `DefinesCover` at `:250`. `Covered` is
handled separately at `:287-289` and matches
`factC-from-hull` at `agents/tasks/LJ-1-595/Probe595.agda:439`.
The grep enumeration of the shape in that one file is
complete.

My attack found four additions. The first two strengthen
the NO-GO. The third corrects the recommended cure and
does not supply the obligation. The fourth is a skip the
brief asked for and the D-10 stop makes honest.

First addition. `PreimageOrd` at `Probe598.agda:257-259`
is unbuilt, and the return did not try to build it, at
`lj-1.598-report.md:199-201`. Item 1 of
`WHAT THE NEXT BRIEF NEEDS` at `:337-341` still offers
to fund it as an alternative to restatement. The
`{{∅}}` reading does not kill the bridge in the hull
the term algebra actually builds, because that hull
lands `{∅}` as well and then `IsOrd (π {{∅}})` fails
(Question 2). A next brief that funds `PreimageOrd`
must first exhibit one code at which the hypothesis
of clause (i) holds and the preimage is not an
ordinal. The return did not exhibit one that survives
the collapse definition. The structural obstruction
that does survive is that the graph route as priced
still needs that bridge or a restatement: `Det` at
`Probe598.agda:210` spends `IsOrd (fst b)` of the
preimage, and `Lset-only` does the same.

Second addition. Uniqueness alone is vacuous, as the
return measured at `Probe598.agda:104-105`. The brief
named that conjunct as W3 at `LJ-1.598.md:106`. A GO on
the conjunct would not have been a GO on the obligation.
The return's correction of W3 is right and it is
machine-checked.

Third addition. The recommended cure, restating all four
C-42 sites at `IsOrd (fst (T.val c))` or `IsOrd δ`, is
the wrong default for the family, even though it is the
shape that makes `graph-gives-level` match `ClauseI`.

- Clause (iii) uniqueness is already at the collapse.
  `DefinesLevelAcross` at `Probe578.agda:510` concludes
  `fst b ≡ Lset (HS.C.π δ)`. The index of `Lset` there
  is the ordinal the hypothesis names. Grouping clause
  (iii) with clause (i)'s preimage mismatch is a
  misclassification.
- `HasLevels` and `LevelsCommute` hypothesise
  `IsOrd (HS.C.π δ)` because the consumer's preimage is
  not an ordinal. `levelIn-from` at
  `Probe578.agda:140-150` takes `IsOrd δ` of a point of
  `πX`, finds `γ` in the hull with `HS.C.π γ ≡ δ`, and
  spends `HasLevels` at that `γ` with
  `oγ : IsOrd (HS.C.π γ)` obtained by transport at
  `:149-150`. Restating `HasLevels` at `IsOrd δ` would
  leave `levelIn-from` unable to apply it at `γ`. The
  hull is not transitive. Pseudo-ordinals are the
  reason the certificate used the collapse in the
  hypothesis. Devlin's (b) at
  `dev/literature/devlin-II5.md:99` ranges over ordinals
  `γ < α` of a transitive level. The tree's hull is not
  that level.
- The equation route would inhabit clause (i) at a
  pseudo-ordinal if a code for `Lset δ` existed. That
  is exactly `HasLevels`. The graph is the wrong
  supplier for the type as stated. It is not a proof
  that the type's hypothesis is the wrong hypothesis
  for Fact A.

So the supply NO-GO stands: from delivered machinery,
neither `Det`/`Wit` nor `CodedLevels` is in hand, and
the tree's graph formula cannot meet `DefinesLevel` at
the codes the type admits. The next brief must not treat
"restate the four" as the measured cure. The cheap next
measurement is whether Fact A is still wanted at
preimages of ordinals. If it is, clause (i) keeps
`IsOrd (π _)` and the graph is not its supplier.

Fourth addition. The brief at `LJ-1.598.md:87-88` ordered
a re-measurement of Δ₀-ness and the `AtStage` hypotheses
at this formula, citing `[LJ-1.562]`. The return does
not do that measurement. Given the D-10 stop on the
supplier, the skip is honest: there is no formula here
to re-measure. It is an unanswered brief item, not a
missed inhabitant.

On the brief as cause. The brief mandated one term
`defines-level` at `LJ-1.598.md:9-13`. It also priced a
NO-GO with a measured floor as a result, at `:116-118`.
It named uniqueness, not existence, as W3, at `:106`.
That W3 did not cause the NO-GO. It caused a vacuity
the return caught. Premise 4 at `LJ-1.598.md:51` says
clause (i) is Devlin's (b). Devlin's (b) quantifies over
ordinals. The type at `Probe578.agda:236` does not.
The brief did not forbid a GO, and it did not write a
false type into the obligation by itself: the obligation
is `[LJ-1.578]`'s clause, and that clause is the thing
D-10 tested. The brief did not foreclose a true
inhabitant that the return then refused. No term of
`Cert.DefinesLevel` is in the delivered tree. I looked
for one. The two natural suppliers are the two the
return priced, and both are blocked for the reasons
above.

W2 is answered at `lj-1.598-report.md:293-303`. One
frame, both routes stated once, the graph parametric in
`ψ`. W3 named the term and the slice
`runs/W3.agda`, then corrected the term after the
vacuity. W4 does not apply. W7 is not at issue: the
probe quantifies over `T.Code`. W8: the literature
block was read, Devlin's (b) is not an axiom with no
condition this tree meets, and a literature NO-GO was
not the right abort.

## VERDICT

**Upheld.** The verdict line matches the body on the
NO-GO. The obligation `defines-level` is not inhabited.
The probe that prices the two reductions is green. The
graph route as priced still needs `IsOrd` of the
preimage, which the type does not give, and neither
`CodedLevels` nor `Det`/`Wit` is delivered. Several
citations are off by line, by file, or by a converted
size figure. The D-10 `{{∅}}` reading has a collapse
equation one rank too low, and it does not fire at a
hull that lands both `{∅}` and `{{∅}}`. Those are
defects in the record. They are not a missing
inhabitant. The enumeration of C-42 sites in
`Probe578.agda` is complete as a grep. It is not
complete as a cure: restating `HasLevels`,
`LevelsCommute` and clause (iii) at the preimage's
ordinal-hood would break `levelIn-from` at
`Probe578.agda:140-150`, and `PreimageOrd` is not yet
a refuted statement. The obligation stays open. With
this file and exit 0, row `sys-critic-upheld-no-go`
closes the task.

## ARCHIVE USED

- `archive/dev/JOURNAL.md`: read at `:1`. Quote:
  `# ARCHIVED 2026-08-20`. Declined, not used. It is the
  retired per-episode journal. This review measures a
  live-tree NO-GO whose history is the task directory.
- `archive/dev/ORCHESTRATION.md`: read at `:1`. Quote:
  `# ORCHESTRATION: the orchestrator's operating rules`.
  Declined, not used. The live rules are the five files
  the program cats. No orchestration question is at
  issue.
- `archive/dev/DD-archived.md`: read at `:35`. Quote:
  `The questions are: is the refusal correct on its own numbers; is the measurement sound; did the BRIEF cause the outcome; and is there a cure the return missed.`
  Used. Those four are the lens this slot attacks with.
  They are not restated as the written answers.
- `archive/dev/PLAN-archived.md`: read at `:1`. Quote:
  `# ARCHIVED 2026-08-20`. Declined, not used. Retired
  construction registry. Nothing current in it bears on
  clause (i).
- `dev/ARCHIVE.md`: read at `:1`. Quote:
  `# ARCHIVE.md: the archive registry`. Declined, not
  used. No module was retired by LJ-1.598, so no row
  was owed.

## LITERATURE USED

- `dev/literature/devlin-II5.md`: read at `:99`. Quote:
  `> (b) (∀γ < α)(∀v)[v = L_γ ↔ v ∈ L_α ∧ L_α ⊨ ∃z φ(z, v, γ)].`
  Used. Devlin's `γ` ranges over ordinals below `α`.
  That agrees with `Lset-only` spending `IsOrd` of the
  argument, and it agrees with the return that the
  graph determines a level at an ordinal. It does not
  agree with a blanket restatement of `HasLevels` at
  `IsOrd δ` of a hull preimage, because Devlin's `α` is
  a transitive level and the hull is not.
- `dev/literature/BIBLIOGRAPHY.md`: read at `:1`. Quote:
  `# Bibliography for the rud route`. Declined, not
  used. No source beyond Devlin II.5 was needed for
  this review.
- `dev/literature/digest.md`: read at `:1`. Quote:
  `# Digest: the orthodox form of the rud route, pinned from the collected literature`.
  Declined, not used. The chain in full is in
  `devlin-II5.md`, which I read.
- `dev/literature/geology.md`: read at `:1`. Quote:
  `# Geology dossier: set-theoretic geology sources and the five questions`.
  Declined, not used. Stratigraphy of a different
  literature. Not relevant to clause (i).
- `dev/literature/devlin-errata.md`: read at `:1`. Quote:
  `# Devlin errata: documented error classes (do-not-repeat checklist)`.
  Declined, not used. The lemma I used, Devlin II.5 by
  2.7, is not on an errata path that would change the
  NO-GO.
