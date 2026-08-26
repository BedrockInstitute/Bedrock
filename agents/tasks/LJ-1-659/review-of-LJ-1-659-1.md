# review-of-LJ-1-659-1: the STOP of LJ-1.659#1 is UPHELD

## HEAD
head_slot: mathematician_adversarial
machine: shared
task: LJ-1.659, review of LJ-1.659#1
attacked return: agents/tasks/LJ-1-659/lj-1.659-report.md with its stop
agents/tasks/LJ-1-659/review-of-lset-formula-to-level.md
verdict: upheld
invariant: the critic is not the author. This head did not write the return,
the stop statement, the probe, the floor, or the residue. A21: this
review writes no `.agda` file.

## WHAT THIS REVIEW DECIDES

The predecessor stopped on the named obligation and wrote
`agents/tasks/LJ-1-659/review-of-lset-formula-to-level.md`. The name
`lset-formula-to-level` is not in `Probe659.agda`. The probe is
green. One obligation stays open. I attack that return on the three
questions of this brief. Result: the verdict line and the body
agree. Every load-bearing citation that carries the STOP resolves
today, with named neighbourhood pointers and one off-by-two archive
line recorded below. The census of the obligation is complete. The
class-carrier pair `Lset-only` / `Lset-defines` is named more
sharply here than in the return. It does not inhabit the
obligation. The STOP is UPHELD.

I attacked the return, not the task. I re-opened every load-bearing
cite. I re-ran no Agda. The accept arm already re-ran the probe
today. I named no new probe as a file. A21: if a later dispatch
needs a measurement, the coder writes it.

The four-question lens is DD25 at `archive/dev/DD-archived.md:35`.
Quote:
`The questions are: is the refusal correct on its own numbers; is the measurement sound; did the BRIEF cause the outcome; and is there a cure the return missed.`
The three questions below are the written answers. Those four are
DD25's, not section 6.6's list.

## 0. THE INSTANCE RECORD

The worktree copy of `dev/pod/transitions/2026-08.jsonl` carries one
line with `"task": "LJ-1.659"`. It is line 4268, seq 4267, attempt
0, `to: READY`, `heads_sha256` `cd49070c`, stamp
`2026-08-26T06:09:55Z`. `model` and `effort` are null. The file
ends at that line. The instance that wrote the return is not on the
worktree record. I report the absence. I take the six facts from
the accept arm, as the brief requires, and I infer no fact that arm
does not carry.

`agents/tasks/LJ-1-659/runs/accept-1.out:10-24` and the JSON facts
at `:26`:

- probe run: `agents/tasks/LJ-1-659/Probe659.agda` rc 0, 3.35 s (`:16`)
- floor run: `agents/tasks/LJ-1-659/runs/Floor659.agda` rc 0, 2.73 s (`:17`)
- conjuncts 1 to 6 held (`:10-15`)
- `exit_code` 0, `error_class` null (`:23-24`, `:26`)
- `obligations_delta` 0, `obligations_open` 1 (`:21`, `:26`)
- `heap_wall` false, `lines` 0 (`:26`)
- `agda_vacuous` false, `unbound_vacuous` true (`:26`)
- caliber `-A64m -I0 -M2g`, tier wide (`:5-6`)
- 16 changed files, all under `agents/tasks/LJ-1-659/` (`:18-19`, `:26`)
- `changed_files_refused` empty (`:26`)

`unbound_vacuous: true` here means conjunct 4 saw no `src/` master
change. It does not mean a hole in the live probe. Grep of
`Probe659.agda` finds `lset-formula-to-level` only in comments
(`:5`, `:16`). `--safe` is on (`Probe659.agda:1`). The keyword
`postulate` occurs only in a comment (`:32`). That is the machine
state of a stated STOP: the probe is green, the name is absent, one
obligation stays open.

The worker's own meters match the files I opened:

- obligation: `1 UNRESOLVED of 1, 2.97 s, probe_red=False`
  (`runs/meter-obligation.out:2`)
- twenty-seven delivered names: `0 UNRESOLVED of 27, 3.71 s, probe_red=False`
  (`runs/meter-names.out:28`)
- final check: `EXIT=0` (`runs/p-final.out:23`)

Row `sys-critic-upheld-no-go` wants `obligations_open_min = 1`
(`dev/pod/table.toml:4321`). The accept arm records
`obligations_open: 1` (`accept-1.out:26`). An upheld stop of this
shape matches that row.

## 1. QUESTION ONE: DOES THE VERDICT LINE MATCH ITS OWN BODY

**Yes. The line names both halves, and the body keeps both halves.**

The line is `agents/tasks/LJ-1-659/lj-1.659-report.md:9-11`:

> **STOP ON THE OBLIGATION AS WRITTEN, AND THE STOP IS
> `review-of-lset-formula-to-level.md`. THE CORRECTED ARROW IS BUILT AND
> GREEN, AND IT COSTS ONE RENAMING.**

The stop file says the same at
`review-of-lset-formula-to-level.md:3-13`. The body carries each
part of that line:

- The obligation term is not written. The meter names it missing
  at `runs/meter-obligation.out:1-2`. Accept re-measured the green
  file today: rc 0, 3.35 s (`runs/accept-1.out:16`), delta 0,
  open 1 (`:21`, `:26`).
- The hypothesis is syntax. `[LJ-1.651]` delivered
  `lset-formula : Formula Code 2`
  (`agents/tasks/LJ-1-651/Probe651.agda:141-142`). The probe
  inhabits that type with `⊤̇` (`trivial`, `Probe659.agda:121-122`).
  `obligation-is-the-target` (`:141-143`) is the pair of
  `level-from-obligation` (`:127-128`) and
  `obligation-from-level` (`:134-135`). `level-from-nothing`
  (`:130-131`) applies the same arrow at `⊤̇`.
- The return does not refute `LevelFormula`. It says so at
  `lj-1.659-report.md:92-94` and at
  `review-of-lset-formula-to-level.md:69-74`.
- The corrected arrow is `level-from-laws`
  (`Probe659.agda:199-214`). The meter lists that name as pass
  (`runs/meter-names.out:16`).

This is not the defect class the project measured on 2026-08-16.
A line that said GO while the body left the obligation open, or a
line that said the obligation was missing while the meter closed
it, would be that class. Here the line states both facts the body
measures.

**The refusal is correct on its own numbers.** The brief's
obligation is one term
(`LJ-1.659.md:11-15`, `LJ-1.659.md:23`). The type in the probe is
`LsetFormulaToLevel = LsetFormula → LevelFormula`
(`Probe659.agda:109-110`), and `LsetFormula = Formula Code 2`
(`:92-93`). That is the predecessor's delivered type taken as a
module hypothesis. `Formula Code 2` is inhabited in the syntax
chapter (`⊤̇`). An inhabited type as a hypothesis names no fact, so
the arrow is interderivable with `LevelFormula`. The brief itself
records `LevelFormula` as "a type nothing inhabits"
(`LJ-1.659.md:50`). A dispatch that funds the arrow funds the
target under another name.

The worker's run table matches the `.out` files I opened:

| run | claimed | file |
|---|---|---|
| `floor-1` | exit 0, 5.82 s, 857,849,856 | `runs/floor-1.out:5-6`, `:24` |
| `p-1` | exit 42, 3.33 s, 611,631,104 | `runs/p-1.out:10-11`, `:28` |
| `p-2` | exit 0, 4.46 s, 838,664,192 | `runs/p-2.out:5-6`, `:23` |
| `p-3` | exit 0, 4.73 s, 763,379,712 | `runs/p-3.out:5-6`, `:23` |
| `p-4` | exit 0, 5.68 s, 734,789,632 | `runs/p-4.out:5-6`, `:23` |
| `nolaws-1` | exit 42, 3.18 s, 693,878,784 | `runs/nolaws-1.out:8-9`, `:26` |
| `floor-final` | exit 0, 4.98 s, 537,296,896 | `runs/floor-final.out:5-6`, `:23` |
| `p-final` | exit 0, 4.39 s, 787,546,112 | `runs/p-final.out:5-6`, `:23` |
| `meter-obligation` | 42, 2.97 s | `runs/meter-obligation.out:1-2` |
| `meter-names` | 0, 3.71 s | `runs/meter-names.out:1`, `:28` |

The highest peak claimed is 857,849,856 bytes, 40 percent of
2,147,483,648. 857,849,856 / 2,147,483,648 is 0.399. No run in
that table walled. The one count that does not match its own list
is defect D1 below. It does not carry the STOP.

**The measurement is sound.** Accept re-checked both `.agda` files
today (rc 0). The file that cannot typecheck is named
`runs/NO-LAWS.agda.txt`, as the brief ordered
(`LJ-1.659.md:17-20`). The `[UnequalTerms]` block in
`review-of-lset-formula-to-level.md:56-58` occurs identically in
`runs/nolaws-1.out:5-7`. `LsetFormulaWithLaws → LevelFormula` is
inhabited (`level-from-laws`). `Formula Code 2 → LevelFormula` is
not, except by assuming `LevelFormula`. Those are different types.
The probe restates `LevelFormula` from
`agents/tasks/LJ-1-650/Probe650.agda:322-328` at
`Probe659.agda:100-106`, and restates `CodedCover` from
`Probe650.agda:88-92` at `Probe659.agda:333-337`. Both restatements
match. W2 is answered: the 650 frame is not imported, and the
reason is that frame's own heap wall
(`lj-1.650-report.md:64-67`). The theorem enters as a hypothesis
(`laws-to-coded-cover`, `Probe659.agda:339-341`).

**Did the brief cause the outcome. PARTLY, AND THE BRIEF FUNDED THE
STOP.** Premise 3 guessed the arrow runs the other way
(`LJ-1.659.md:40-43`). The return measured that it runs neither
way at the delivered type, because the hypothesis is empty. That
is a true reading of the obligation as written, not a failure of
the worker. The brief itself priced the missing-piece deliverable
(`LJ-1.659.md:15-16`): "If it does not follow, the deliverable is
the term naming what the two-variable form has that the one-variable
form does not." The worker built that term as `Sound` and
`Complete` (`Probe659.agda:155-161`). The brief did not foreclose
the answer it asked for. What the brief's NO-GO *branch* would do
with `[LJ-1.651]` is a different question. The return is right that
retiring the syntax is the wrong queue action
(`lj-1.659-report.md:242-247`). `[LJ-1.651]` delivered the first
component of `LevelFormula`. The STOP is on the arrow from that
component alone.

**A missed cure. NONE THAT OVERTURNS.** The strongest untried
attack is to inhabit `Sound delivered` and `Complete delivered` by
riding the class-carrier theorems `Lset-only` and `Lset-defines`
(`src/L/Hierarchy.lagda.md:334-336` and the defines direction at
`:386`) along `[LJ-1.651]`'s four steps onto `_⊨c_`. That is the
hull adequacy `[LJ-1.651]` left open
(`agents/tasks/LJ-1-651/lj-1.651-report.md:180`) and that
`archive/dev/LJ-dispatch-index.md:101` records as PINNED at
`[LJ-1.52]`. It does not inhabit `lset-formula-to-level` in this
dispatch: the accept arm left that name missing, and NO-LAWS shows
that satisfaction of a bare formula is not the equality. The return
already named the residue as `Sound delivered × Complete delivered`
and refused to measure it here (`lj-1.659-report.md:223-225`). That
restraint is correct. A cure that is a new campaign is not a missed
cure of this return.

## 2. QUESTION TWO: IS EVERY LOAD-BEARING CLAIM BACKED BY A `file:line` THAT RESOLVES TODAY

**Yes, with the named defects in section 5. None of them carries
the STOP.**

I opened these cites today. They resolve:

- `agents/tasks/LJ-1-651/Probe651.agda:141-142` (`lset-formula : Formula Code 2`).
- `Probe651.agda:149-150` (`inF c = ∃̇ (lset-formula ∧̇ (var zero ≐ con c))`).
- `Probe651.agda:53-57` (`AtStage` then `Hull` then `Code`).
- `src/L/BoundedSubset.lagda.md:33` (BoundedSubset takes `AtStage` from `L.Hull`).
- `src/L/BoundedSubset.lagda.md:108-111` (`levelHoodB`), `:113-139` (`Δ₀-levelHoodB`), `:145-146` (`Σ₁-levelHood`).
- `src/L/Condensation.lagda.md:2492-2497` (`graphBndAt` and `Δ₀-graphBndAt`).
- `src/FOL/LevyHierarchy.lagda.md:47-57` (ten `Δ₀` constructors, no `∃̇`), `:73-75` (`σ-Δ₀` and `σ-∃` only).
- `src/FOL/Absoluteness.lagda.md:182-183` (`σ₁-up` has premise `Σ₁ φ`).
- `src/L/Hull.lagda.md:415-417` (`hull-closed` takes a bare `Formula Code 1`).
- `src/FOL/Manipulation/Renaming.lagda.md:7` ("no substitution, no weakening"), `:43-44` (renaming moves only variables), `:127-129` (`⊨-rename`).
- `agents/tasks/LJ-1-650/Probe650.agda:322-328` (`LevelFormula`), `:88-92` (`CodedCover`).
- `agents/tasks/LJ-1-650/lj-1.650-report.md:64-67` (the 595-import wall), `:180-189` (binder difference; the brief's own premise 2 cited `:5`, which is `agda_tier: wide`; the claim lives here).
- `agents/tasks/LJ-1-651/lj-1.651-report.md:3` (GO), `:15` (156 lines), `:180` (adequacy residue).
- `agents/tasks/LJ-1-595/lj-1.595-report.md:167-169` (index substitution unpriced).
- `archive/dev/LJ-dispatch-index.md:101` (PINNED hull adequacy).
- `archive/dev/JOURNAL.md:410-411` (level-hood through codes, unbounded).
- `dev/literature/devlin-II5.md:96` (the biconditional), `:219` (the stage reading).
- `src/FOL/ZFStructure.lagda.md:46-48` (fields `S`, `isSetS`, `_≈ˢ_`, `_∈ˢ_`; there is no `setIsSet`), `:91-92` (`hPropStructure` re-exports those fields).
- `src/V/Hierarchy.lagda.md:82` (`_≈ˢ_` at `𝒮ᵥ` is the path, `setIsSet` is the isProp).
- `runs/nolaws-1.out:5-7` matches the stop file's error quote.
- `runs/p-1.out:5-8` is `[NotInScope]` on `SV.setIsSet`, as the report's section 6 states.
- Probe length: 341 lines, 144 non-blank non-comment. Section 5 at
  `Probe659.agda:217-322` is 39 non-blank non-comment. The
  renaming block `module RS` through `level-from-laws`
  (`:183-214`) is 25 non-blank non-comment.

Grep of `src/` for `levelHood|graphBndAt` returns only
`src/L/BoundedSubset.lagda.md` and `src/L/Condensation.lagda.md`,
as the return claimed. Grep of `Probe659.agda` for the obligation
name finds no binding. The 27 meter names are the 27 names in the
report's section 3 table.

Failing or neighbourhood cites are D1 to D4 below. The STOP does
not rest on them.

## 3. QUESTION THREE: IS THE PREDECESSOR'S ENUMERATION COMPLETE

**In substance yes, with one case covered but not named.**

The return enumerates:

- the obligation's absence, metered missing;
- the degenerate arrow, in both directions, and at `⊤̇`;
- Agda's own `[UnequalTerms]` on the only reading a bare formula
  allows (`runs/NO-LAWS.agda.txt:56-60`, `so v γ h = h`);
- the two missing laws, as types, at `[LJ-1.651]`'s slot order;
- the corrected arrow, one renaming;
- that `[LJ-1.651]` is the first component and is not to be retired;
- W3 on the index binder: free on the two laws, fatal for the
  tree's `Σ₁` certificate of `inF`;
- C-42, not run, and named as a recon dispatch;
- the `[LJ-1.52]` PINNED record as the price of the residue.

The unnamed case is the class-carrier adequacy already in `src/`.
`Lset-only` at `src/L/Hierarchy.lagda.md:334-336` is

> `⟨ γ ⊨ LsetGraphAt w b ⟩ → IsOrd (fst (lookup b γ)) → fst (lookup w γ) ≡ Lset (fst (lookup b γ))`

and `ride-only` at `src/L/Condensation.lagda.md:422-425` re-exports
it. `Lset-defines` is the other direction (`Hierarchy.lagda.md:386`).
The return's search was `levelHood|graphBndAt`. Those names have
grade certificates and no adequacy. `LsetGraphAt` is a different
formula, at the class carrier `S`, not at `Code`, and not under
`_⊨c_`. So the search as written is true, and the stronger English
in the stop ("nothing in the tree connects them",
`review-of-lset-formula-to-level.md:61`) is true of `_⊨c_` of the
delivered formula. It is incomplete if read as "the tree has no
Lset-adequacy for any graph formula". The missing name does not
inhabit the obligation. It is the starting point of the residue
the return already told the next brief to fund. This is an
addition, not an overturn.

The grade census is complete for the shape it names. `inF c` is
`∃̇ (lset-formula ∧̇ ...)`. `Σ₁` has two constructors. `σ-Δ₀` of an
`∃̇` is impossible (`no-Δ₀-∃`). `σ-∃` demands `Σ₁` of a conjunction,
which is only `σ-Δ₀ (δ-∧ _ _)`, and the left conjunct is not `Δ₀`
(`no-Σ₁-inF`, `no-Σ₁-mapped-inF`). There is no `σ-∃` clause on a
conjunction. The five absurd patterns cover the datatype. The
textbook gap (no prenexing, so no `σ-∧`) is stated as machinery
(`lj-1.659-report.md:201-203`) and is not claimed as mathematics.

## 4. WHY THE STOP STANDS

Three measured facts, each checked today:

1. The obligation name is absent from the green probe, and the
   meter and the accept arm both leave one obligation open
   (`runs/meter-obligation.out:2`, `runs/accept-1.out:26`).
2. The hypothesis type is `Formula Code 2`. That type is inhabited
   without `[LJ-1.651]`. The arrow from it is `LevelFormula` under
   another name (`Probe659.agda:127-143`).
3. Adding the two semantic laws makes the arrow the brief wanted,
   for one renaming (`level-from-laws`, `:199-214`). Those laws are
   not in the tree at `_⊨c_` of `delivered`. Class-carrier adequacy
   of `LsetGraphAt` does not close that gap.

The return does not claim the obligation's TYPE is false, and says
so in the stop's section 3. That restraint is correct:
`level-from-laws` shows the type closes from the two laws.

W3 of the attacked return named the index binder and specified the
measurement in the probe the coder wrote. A21 is satisfied on that
side: the mathematician of that dispatch was the brief, the coder
built the probe. The binder is free on `Sound` and `Complete`
(`ix-sound`, `ix-complete`) and it is `inF` by `refl`
(`bindIx-is-inF`, `:234-235`). The estimate 60 to 130 was high:
section 5 is 39 non-blank non-comment lines.

## 5. DEFECTS FOUND IN THE RETURN

- **D1, a wrong count of the grade negatives.**
  `lj-1.659-report.md:183-185` says "Four machine-checked
  negatives" and then lists `no-Δ₀-∃`, `no-Σ₁-∃∧`,
  `no-Σ₁-bindIx`, "and the two concrete ones", `no-Σ₁-inF` and
  `no-Σ₁-mapped-inF`. That is five names. The probe comment at
  `Probe659.agda:277-279` says "Three machine-checked negatives"
  and then defines the same five. The meter lists all five as
  pass (`runs/meter-names.out:21-25`). The finding stands. The
  count in the prose does not.

- **D2, an off-by-two archive line.** The return's ARCHIVE USED
  cites `archive/dev/JOURNAL-archived.md:3988` for
  "NEEDED**; parameters enter as an environment rather than by
  substitution." That sentence is at `:3986`. Line 3988 is
  "consumes `AllCodes`, not `Codes`. Estimate 1,900 to 3,150,
  point about 2,400,". The claim is true. The citation does not
  back it.

- **D3, a neighbourhood pointer on `⊨-rename`.**
  `Probe659.agda:179` cites
  `src/FOL/Manipulation/Renaming.lagda.md:157-159`. Those lines
  are the prose after the code fence. The term is at `:127-129`.
  The stop file has the right range
  (`review-of-lset-formula-to-level.md:95-96`). The claim is
  true.

- **D4, a neighbourhood pointer on `Code`.** The report identifies
  the two `Code` types at `src/L/BoundedSubset.lagda.md:907-909`
  against `Probe651.agda:53-57`. `:907-909` is `AtStage` and
  `Hull`. `Code` is opened on the 651 side at `:57` and on the
  659 side at `Probe659.agda:73`. The modules meet because
  BoundedSubset imports `AtStage` from `L.Hull` (`:33`) and
  `delivered = P.lset-formula` typechecks at `Formula Code 2`.
  The identification is machine-checked. The cited range is the
  hull, not the `Code` field.

- **D5, in the dispatch, not the return.** This review brief cites
  the three questions at
  `dev/memos/LJ-4-pod-program-design.md:2853-2858`. That range
  carries other text today. The list is at `:2984-2988`. Recorded
  for the program. No action from this slot.

None of D1 to D4 changes the verdict. D1 and D2 are the kind of
defect the Boundary's evidence rule exists for, and the next brief
that copies those lines inherits them.

## 6. WHAT THE QUEUE KEEPS

- Restate the obligation as `Sound delivered × Complete delivered`,
  copied from `Probe659.agda:155-161`. Everything downstream of
  that pair is already built in this probe: `level-from-laws`
  reaches `LevelFormula`, `laws-to-coded-cover` reaches
  `CodedCover` through `[LJ-1.650]`'s theorem as a hypothesis.
- Do not retire `[LJ-1.651]`. Cite `lset-formula` as syntax. The
  brief's NO-GO branch (`LJ-1.659.md:69-70`) is the wrong action
  on this measurement.
- Price the residue against `archive/dev/LJ-dispatch-index.md:101`,
  not against this task's 39 lines. Start the ride from
  `Lset-only` / `Lset-defines`, which this return did not name.
- The C-42 sweep remains a recon dispatch. This task measured one
  site, `inF`. It did not count the others.
- Write the slot order down once. `[LJ-1.651]` is ordinal 0, value
  1. `[LJ-1.650]` is value 0, ordinal 1. `transpose` at
  `Probe659.agda:193-195` is the conversion. Literature
  (`dev/literature/level-formula-slot-roles.md:37-38`) says the
  free pair is the value and the ordinal. It does not fix the
  numbering. Both probes have the right roles.

## 7. MY OWN W3 AND W4

**W3, A21 form: the mathematician names, the coder writes.** The
widest unmeasured term in THIS dispatch is whether `Sound delivered`
and `Complete delivered` follow by transporting `Lset-only` and
`Lset-defines` along `[LJ-1.651]`'s four steps (`∃̇`, `renameFo rot`,
`∃̇`, `renameFo swap`, then `mapFo slide`) onto `_⊨c_`. The probe
the coder should write is a tracked file under the next task's home
in `agents/tasks/<CODE>/`, never under `src/`, never deleted: it
imports no probe chain, it hypothesises or rides
`Lset-only` / `Lset-defines` at
`src/L/Hierarchy.lagda.md:334-336` and `:386`, and it records
which of the four steps is the first that does not transport. It
does not land in `src/`. Estimate: not 25 lines. Basis: the
delivered comparable `[LJ-1.52]`, PINNED, three named leaves
remaining (`archive/dev/LJ-dispatch-index.md:101`). I wrote and
touched no `.agda` file myself.

**W2.** This review proves nothing, so it duplicates nothing.

**W4.** Nothing retires in this review. No `dev/ARCHIVE.md` row is
owed. The attacked return recommends against a retirement the brief
contemplated. I agree.

**W7, W8.** The hull stays indexed by `Code`. The literature does
not show the obligation's shape to be an axiom with no condition
this tree meets. Devlin's biconditional is a theorem of
constructibility, and the missing piece is a derivation this tree
has not funded, not an axiom.

## 8. THE TREE, LEFT AS FOUND

I wrote one file, this one, and changed nothing else. No commit, no
push. `agents/tasks/LJ-1-659/review-LJ-1-659-1.md` holds a copy of
this dispatch's brief text. It is not in the acceptance arm's 16
changed files. I did not create or change it.

## ARCHIVE USED

- `archive/dev/ORCHESTRATION.md`: **DECLINED.** It is the archived
  operating document, superseded by
  `dev/memos/LJ-4-pod-program-design.md`. This review turns on
  types, runs and citations, not on how the loop is operated.
- `archive/dev/DD-archived.md`: **READ.**
  `archive/dev/DD-archived.md:35` reads "The questions are: is the
  refusal correct on its own numbers; is the measurement sound; did
  the BRIEF cause the outcome; and is there a cure the return
  missed." That is the four-question lens this review attacked
  with, and its home is the DD25 row.
- `archive/dev/PLAN-archived.md`: **DECLINED, not used.** It is the
  superseded construction registry. The live plan is the queue and
  the screen. This review decides one return and re-plans nothing.
- `archive/dev/measurements/README.md`: **DECLINED.** It is the
  register of retired timing records. This review re-opened the
  task's own `runs/` files and did not need a historical meter.
- `archive/dev/README.md`: **DECLINED.** It is the index of the
  retired route's developer records. The STOP is a type fact in a
  live probe, not a question about the internalization archive.

## LITERATURE USED

- `dev/literature/BIBLIOGRAPHY.md`: **DECLINED.** It is the fetch
  record. No bibliographic question arises. The Devlin use was
  checked against the chapter file and against the slot-roles
  digest.
- `dev/literature/level-formula-slot-roles.md`: **READ, to attack
  the return's "both slot orders are right".**
  `dev/literature/level-formula-slot-roles.md:37` reads "Rows 3, 4,
  5, 6, 8 and 9 agree. **A level-hood formula leaves exactly the two"
  The attack fails: both probes leave exactly those two slots.
  `[LJ-1.651]` numbers them ordinal then value. `[LJ-1.650]`
  numbers them value then ordinal. Row 4 of the same table (`:23`)
  records Devlin's Φ as value at 1 and ordinal at 2 after the
  bound, which is `[LJ-1.650]`'s numbering, not a ruling that
  `[LJ-1.651]` is wrong. `transpose` converts them. The return
  stands.
- `dev/literature/devlin-errata.md`: **READ, to attack the return's
  Devlin use.** `dev/literature/devlin-errata.md:60` reads
  "- Levels-of-language ambiguity. WS p. 56-57: "There is an
  ambiguity over the". The erratum warns that Devlin's two readings
  of Σ0 are not equivalent in weak systems. It does not touch this
  return: `Sound` and `Complete` are stated as types
  (`Probe659.agda:155-161`), not as Devlin's equivalence. The
  attack fails and the return stands.
- `dev/literature/primary-sources.md`: **DECLINED.** It is the
  second-round fetch log. This review needed the digested slot
  arithmetic and the II.5 biconditional, and those already live in
  `level-formula-slot-roles.md` and `devlin-II5.md`.
- `dev/literature/glossary-review-2026-08.md`: **DECLINED.** It is
  a review of `dev/glossary.toml` entries. This review adds no
  glossary entry and proposes none.
