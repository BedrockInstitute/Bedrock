# LJ-1.494 report: the level graph at the stage world

slot: `coder`. Written early as a skeleton and filled as runs landed (C-22).
No commit, no push. I wrote only in `agents/tasks/LJ-1-494/`. Agda ran
under the caliber the program set on this pane, `GHCRTS="-A64m -I0 -M8g"`,
ONE Agda process at a time. I did not set `GHCRTS`. No heap event.

TARGET: build ONE term in `agents/tasks/LJ-1-494/Probe494.agda`:

    GraphSatAtStage :
        (δ : S) → IsOrd (fst δ) → ⟨ fst δ ∈ˢ Lset α ⟩
      → ⟨ ((Lset-at δ) ∷ δ ∷ []) AbsL.⊨ᵐ LsetGraphAt zero (suc zero) ⟩

the defines direction of the level graph at `AbsL.𝒮M`. Land nothing
in `src/`.

W3 first, the type the brief names, obligation omitted:

    hier-in-stage : (δ : S) → IsOrd (fst δ) → ⟨ fst δ ∈ˢ Lset α ⟩
                  → ⟨ hierL (fst δ) _ _ ∈ˢ Lset α ⟩

The standing direction (`dev/pod/direction.md:37`) says one SRC
collection after LJ-1, not after `[LJ-2.5]`. This task is still LJ-1
work. It does not start that collection. It does not start phase 3.
No Boundary clause is in conflict.

## WHICH PREMISE MOVED

`[LJ-1.492]` is a critic-upheld NO-GO. Heading `## VERDICT` at
`agents/tasks/LJ-1-492/lj-1.492-report.md:133`. Quote at `:133-137`:

> **NO-GO at CoverWitnessesInHull, after W3 closed and `closed` opened.**
> W3 is GO: the formula at arity one typechecks. `closed` is applied
> at that formula. The conversion from `ambient-level` to STAGE
> satisfaction of `coverFo` is unbuilt. The obligation term is not
> written.

I did not inhabit `CoverWitnessesInHull`. I did not inhabit `cover`.
I did not rebuild `coverFo`, `code-of` or `ambient-level`. I did not
open `closed`. I opened the graph side the critic named.

The critic's named object is adequacy of `LsetGraphAt` at `AbsL.𝒮M`
in both directions (`agents/tasks/LJ-1-492/review-of-LJ-1-492-1.md:163-166`).
This task takes the defines direction. It does not attempt the only
direction.

## D-10, BEFORE ANY AGDA

`GraphAt w b` is `∃̇ (ApproxAt zero (suc b) ∧̇ Step (suc w) (suc b) zero)`
(`src/L/Coding/Sequence.lagda.md:291-292`). The witness of that
existential at `𝒮ʟ` is `hierL δ` (`src/L/Hierarchy.lagda.md:656`).
`AbsL.𝒮M` is `𝒮ᵥ` restricted to one stage (`src/L/Hull.lagda.md:153`).
Its carrier is `Σ[ x ∈ S ] ⟨ x ∈ˢ Lset α ⟩` (`src/FOL/ZFStructure.lagda.md:146`).
The witness must be a member of `Lset α`.

`hierL` returns an element of `𝒮ʟ` (`src/L/Hierarchy.lagda.md:621-622`).
It is built by `hasReplacementL` (`src/L/Hierarchy.lagda.md:595`).
`hasReplacementL` exports a set of `𝒮ʟ` and no stage bound
(`src/L/Axioms/Full.lagda.md:277-280`). Its proof builds `βimg` and
`img∈βimg` (`src/L/Axioms/Full.lagda.md:225-231`) and does not export
them.

`stage-mem` (`src/L/Stage.lagda.md:188-189`) places a constructible
set in some stage. It does not place it in `Lset α`.

**Is `hierL δ` a member of `Lset α` when `δ` is?** The tree does not
bound `hierL δ` by `α`. MEASURED: no master states
`⟨ fst (hierL …) ∈ˢ Lset … ⟩`. `[LJ-1.230]` recorded the same gap
(`agents/tasks/LJ-1-230/lj-1.230-report.md:75-79`). `[LJ-1.233]`
corrected the gap to a missing named bound, not a missing landing
(`agents/tasks/LJ-1-233/lj-1.233-report.md:287-291`). I did not
postulate the bound. I did not add a reflection hypothesis.

The brief's spelling `⟨ hierL (fst δ) _ _ ∈ˢ Lset α ⟩` does not form.
`hierL` returns `CS.S`. `𝒮ᵥ`'s `∈ˢ` takes `S`
(`src/FOL/ZFStructure.lagda.md:48`). The intended type uses `fst`.
That intended type forms. See W3.

The brief's `GraphSatAtStage` does not form as a type, for a second
reason. `Lset-at` is not a name in live `src/`. `LsetGraphAt` is
`Formula CS.S n` (`src/L/Coding/Sequence.lagda.md:349`). `AbsL.⊨ᵐ`
takes `Formula SL n` (`src/L/Hull.lagda.md:153-156`). A map
`CS.S → SL` is a total map from `L` into `Lset α`. No such map.
The brief forbids a reflection hypothesis.

C-42: this is a missing fact at one site, not a refutation of a
false type. Sweep of the shape `hierL` against `Lset` in live `src/`:
zero delivered membership lemmas. `hasReplacementL` has five call
sites (`src/L/Hierarchy.lagda.md:595`, `src/L/Recursion.lagda.md:177`,
`src/L/Choice/Table.lagda.md:751`, `src/L/Choice/Before.lagda.md:1214`,
`src/L/Model.lagda.md:91`). None of the five exports a stage bound.

D-26: a stage built as a definable power carries no generation data.
Members of `Lset α` are sets. They do not carry the approximation
`hierL` was built from. Replacement in `L` produces an element of
`L`. It does not place that element in this stage.

P-l: the W3 type mentions `Lset α`, which is opaque
(`src/L/Constructible.lagda.md:221-223`). It does not mention a
transparent presentation of the stage.

## W8, LITERATURE, BEFORE ANY AGDA

The orthodox covering transfer (`dev/literature/devlin-II5.md:107-108`)
moves a Σ₁ covering statement by elementarity. It does not place an
internal hierarchy, built by replacement, inside a named stage. I do
not stop as a literature NO-GO before W3.

## PREDECESSOR TYPES

- `[LJ-1.492]` is NO-GO at `CoverWitnessesInHull`
  (`agents/tasks/LJ-1-492/lj-1.492-report.md:133`). The statement is
  not named FALSE. This task does not inhabit that type.
- The type this brief names is new. No predecessor probe delivered
  `GraphSatAtStage`. I take no inhabited type from a predecessor.
- `[LJ-1.230]` is NO-GO on placing `hierL` in `Lset`
  (`agents/tasks/LJ-1-230/lj-1.230-report.md:79`). Quote:
  `There is no `hierL b ∈ Lset …` fact.`
- `[LJ-1.233]` measured that `hierL` lands in some stage by
  `stage-mem`, and that a bound in terms of the argument is absent
  (`agents/tasks/LJ-1-233/lj-1.233-report.md:287-291`).

## VERDICT

**NO-GO at GraphSatAtStage, at W3.** W3 as a type is GO: the
intended membership typechecks. W3 as a term is unbuilt. The tree
does not bound `hierL δ` by `α`. The brief's `GraphSatAtStage` does
not form as a type. The obligation term is not written. Witness
meter: 1 UNRESOLVED of 1, `probe_red=False`
(`runs/witness.out:1-2`).

This is an obstruction of stage membership, not a refutation of the
membership type. I did not build a term of the negation. The NO-GO
is stated in `agents/tasks/LJ-1-494/review-of-GraphSatAtStage.md`.
That file is the critic's input. It does not close the task.

**The stage does not contain its own approximations, as far as the
tree can say.** `Lset-defines` is the defines direction at `𝒮ʟ`.
`AbsL.𝒮M` is one stage. Those worlds do not meet at `hierL`.

## THE ONLY DIRECTION, PRICED NOT BUILT.

I did not attempt it. AD12 gives this brief one obligation.

The reverse reading at `AbsL.𝒮M`, as a type, would be:

```agda
GraphOnlyAtStage :
    (δ : SL) (v : SL)
  → IsOrd (fst δ)
  → ⟨ (v ∷ δ ∷ []) AbsL.⊨ᵐ LsetGraphAt zero (suc zero) ⟩
  → fst v ≡ Lset (fst δ)
```

That type does not form either. It uses `AbsL.⊨ᵐ` at `LsetGraphAt`,
so it meets the same `Formula CS.S` / `Formula SL` wall.

Its source at `𝒮ʟ` is `Lset-only` (`src/L/Hierarchy.lagda.md:334-335`),
not `graph-table` (`:382-386`). `graph-table` is the defines engine.
`Lset-defines` (`:646-648`) applies `graph-table` to `hierL`.
`Lset-only` reads a satisfaction out to a meta equality.

The same stage-membership question does **not** govern it. `Lset-only`
unpacks `LsetGraph-out` (`src/L/Hierarchy.lagda.md:337-338`). If the
satisfaction already lives at `𝒮M`, the witness already lives in
`SL`. The universals of `ApproxAt` then range over the stage.
Transitivity `Ltr` (`src/L/Hull.lagda.md:150-151`) plus `δ : SL`
puts members of `δ` in the stage. That is not "place `hierL` in
`Lset α`". I did not fund it. I did not build it.

## WHAT L.CHOICE.ORDER PAID.

I read `src/L/Choice/Order.lagda.md` before I priced the probe.

Its satisfaction world is the class, not a stage:

```
module AbsL = FOL.Absoluteness.Single 𝒮ᵥ isL isL-trans
open AbsL renaming ( _⊨ᵐ_ to _⊨_ )
```

at `:85-86`. The carrier of that world is `𝒮ʟ`. `hierL` is an
element of `𝒮ʟ` by construction (`src/L/Hierarchy.lagda.md:621`).

The graph appears as a conjunct of the step description:

```
One tw = ⟨ (tw ∷ γ) ⊨ LsetGraphAt zero (suc d) ⟩
```

at `:267`. The hypothesis form is at `:372`. The inhabited term is
at `:462-463`:

```
hg : ⟨ (towerS δ od ∷ γ) ⊨ LsetGraphAt zero (suc d) ⟩
hg = Lset-defines zero (suc d) (towerS δ od ∷ γ) od (towerS-fst δ od)
```

That term is `Lset-defines` at the class world. One line. The
witness `hierL` is supplied inside `Lset-defines`
(`src/L/Hierarchy.lagda.md:656`). Order does not place it in a
stage.

The chapter's own measured seal cost sits at `:230-232`. Quote at
`:232`: `-- binds does not finish (over 200 s against 7 s for the whole
chapter)`. That price is the step frame, not the graph transfer. I
did not recompile Order. One Agda process was reserved for this
probe. Local count of non-blank in-fence lines of
`src/L/Choice/Order.lagda.md`: 359. That is not a standing figure.
`ledger.py --brief` is the only standing source, and I do not quote
it.

**The shape is not available at this telescope.** Order restates
graph satisfaction at `𝒮ʟ`. This telescope asks for `AbsL.𝒮M`.
A measured cure does not transfer by analogy. Re-measured: the
class-world term typechecks because `hierL` lives in `𝒮ʟ`. The
stage-world term needs `hierL` in `Lset α`, which the tree does not
give.

## W2 (DD4)

The mathematics of the defines direction is already written once, at
the generic class carrier `𝒮ʟ`, as `Lset-defines`
(`src/L/Hierarchy.lagda.md:646-648`). Instantiating that statement
at `AbsL.𝒮M` is the transfer this brief named. I did not write a
second copy at a fixed ordinal. I did not write a fixed-form
duplicate under a deadline. The W3 type is generic in the stage `α`.
The conflict the clause names did not arise, because the obligation
did not land.

A generic-carrier form that both `isL` and `∈ˢ Lset α` would
instantiate is not delivered. `Lset-defines` is not generic in the
absoluteness class. That is a missing generalisation, not a second
copy I wrote.

## W4 (DD13)

Nothing was retired. No module moved to `archive/`.

## 1. What was built

All in `agents/tasks/LJ-1-494/Probe494.agda`, module
`LJ-1-494.Probe494 {ℓ} (lem)`.

- Telescope `StageWorld` (`:35`), one stage `α` with `IsOrd α`.
  `AtStage` is opened for `SL`. `levelIn` is not a hypothesis.
  `cover` is not a hypothesis.
- W3 as a type: `hier-in-stage` (`:49-53`). The brief's spelling
  does not form. The intended membership uses `fst`. Uninhabited.
- Obligation name: `GraphSatAtStage` (`:67-68`), equal to the W3
  type, because the brief's type does not form. Uninhabited.
- Checked imports: `LsetGraphAt` as `Formula CS.S 2` (`:75-76`),
  `SL` as the stage carrier (`:77-78`). Neither is applied to a
  satisfaction.

Measured non-blank non-comment lines: 30. Total lines: 78. The
brief estimate was about 160 lines, of which the obligation is
about 45. Nothing is funded against the estimate.

## STEP ONE, W3

**The intended membership type forms. The term does not.**
`hier-in-stage` (`Probe494.agda:49-53`) is the brief's W3, with
`fst` on `hierL` so the type is well-formed. The obligation is
omitted as a term in the W3-only file. No postulate. No
`stage-mem` applied at the wrong stage.

This is not `[LJ-1.230]`'s decode probe and not `[LJ-1.233]`'s
audit. C-42: a comment that the fact is missing is not this type,
and this run does not fund against those reports' times.

Three forced rechecks of the W3-only file (`hier-in-stage` only,
obligation omitted, Hull and Sequence not yet imported), `_build`
interface removed before each, dependencies warm, caliber
`-A64m -I0 -M8g`, one Agda process. Exit 0 every time. Each printed
`Checking`.

| run | wall s | peak RSS bytes |
|---|---|---|
| `runs/w3-1.out` / `w3-1.time` | 1.94 | 403013632 |
| `runs/w3-2.out` / `w3-2.time` | 1.93 | 403079168 |
| `runs/w3-3.out` / `w3-3.time` | 1.87 | 403013632 |

Median wall **1.93 s**. Median peak RSS **403013632 bytes**. No heap
event. The first green W3-only check `runs/w3-0.out` was 2.20 s and
403030016 bytes, also exit 0. It is not one of the three forced
rechecks. The brief estimate for W3 was about 25 lines and under
30 seconds. The measured median is under that estimate.

## STEP TWO, THE OBLIGATION

Omitted as a term. `GraphSatAtStage` is a `Type` at
`Probe494.agda:67-68`, equal to `hier-in-stage`. The brief's type
does not form. A truncated conclusion was not written from an
unbuilt membership. `levelIn` was not added as a hypothesis.
`cover` was not added as a hypothesis. `hull-closed` was not
applied. I did not rebuild `coverFo`, `code-of` or `ambient-level`.

## 2. Runs, floor, witness

Caliber `-A64m -I0 -M8g`, set on the pane by the program and
untouched here. One Agda process at a time, every dependency
warm, from the repository root. The probe interface was deleted
before every kept run.

- W3, three forced rechecks: see the table above. Median
  **1.93 s**, **403013632 bytes**. Exit 0.
- Full file, three forced rechecks. W3, the obligation name as a
  type, `AtStage`/`SL`, and `LsetGraphAt` as `Formula CS.S 2` are
  in the file. The obligation is omitted as a term.

| run | wall s | peak RSS bytes |
|---|---|---|
| `runs/full-recheck-1.out` / `full-recheck-1.time` | 2.38 | 482885632 |
| `runs/full-recheck-2.out` / `full-recheck-2.time` | 2.38 | 482852864 |
| `runs/full-recheck-3.out` / `full-recheck-3.time` | 2.39 | 482852864 |

Median wall **2.38 s**. Median peak RSS **482852864 bytes**.
Exit 0 every time. Each printed `Checking`. No heap event.
The first green full check `runs/full-0.out` was 2.47 s and
482869248 bytes, also exit 0. It is not one of the three forced
rechecks.

- Witness meter, one obligation: 1 UNRESOLVED of 1, 2.49 s,
  `probe_red=False` (`runs/witness.out:1-2`). The name
  `GraphSatAtStage` is a `Type` inside `StageWorld`. That is
  the intended NO-GO reading. The worktree has no `.venv`. The
  meter ran under `/Users/alsg/Agentic/Bedrock/.venv/bin/python`.

## 3. What NO-GO earns, and what is still owed

NO-GO names what the defines direction lacks at the stage world.
The W3 type forms. The tree does not inhabit it. The existential
of `GraphAt` cannot be witnessed inside `Lset α` from delivered
facts. That is the first measurement of the graph side, as a
membership, at this telescope.

A NO-GO at W3 says the stage does not contain its own
approximations, as far as the tree can say. That is one fact
behind the condensation stops this campaign has recorded. It
tells the mathematician to re-price `cover` and `levelIn`
together, instead of one at a time. I do not claim that every
other site carries this gap. C-42: one site.

What this task does not settle:

- It does not inhabit `GraphSatAtStage` as the brief spelled it.
- It does not inhabit `hier-in-stage`.
- It does not inhabit `CoverWitnessesInHull`.
- It does not inhabit `cover`.
- It does not inhabit `levelIn`.
- It does not refute `hier-in-stage`.
- It does not apply `hull-closed`.
- It does not edit `src/`.

## 4. What the next brief needs

- Do not order `GraphSatAtStage` until `hier-in-stage` is
  delivered, or until a brief names a different witness than
  `hierL`.
- Do not postulate the bound. Do not add a reflection
  hypothesis. `[LJ-1.230]` and `[LJ-1.233]` already named the
  gap. This task wrote the type and typechecked it.
- The Formula-carrier wall is a second blocker. `LsetGraphAt`
  is `Formula CS.S`. `AbsL.⊨ᵐ` takes `Formula SL`. A next brief
  that wants satisfaction at `𝒮M` must name a formula whose
  constants live in `SL`, or name a delivered map `CS.S → SL`,
  which does not exist.
- `Lset-at` is not a name. Packing `Lset (fst δ)` as an `SL`
  needs `⟨ Lset (fst δ) ∈ˢ Lset α ⟩`. That is a sibling
  membership, closer to `levelIn` at the stage than to `hierL`.
  It is not W3. I did not inhabit it.
- Do not order the only direction yet. Its source at `𝒮ʟ` is
  `Lset-only` (`src/L/Hierarchy.lagda.md:334`). It does not need
  `hier-in-stage`. It shares the Formula-carrier wall. See
  `## THE ONLY DIRECTION, PRICED NOT BUILT.`
- Do not order `coverFo`, `code-of` or `ambient-level` again.
  `[LJ-1.492]` forbids re-ordering them
  (`agents/tasks/LJ-1-492/lj-1.492-report.md:337-342`).
- Do not take `levelIn` as a hypothesis of a `cover` probe.
- `L.Choice.Order` is not a cure. Its graph term is
  `Lset-defines` at `𝒮ʟ` (`src/L/Choice/Order.lagda.md:462-463`).
- What the statement cost: 30 non-blank non-comment lines, W3
  median 1.93 s, full median 2.38 s, peak RSS 482885632 bytes
  on the kept rechecks. What the shape resisted: stage
  membership of `hierL`. What I had to weaken: the obligation
  type, because it does not form; the name `GraphSatAtStage` is
  the W3 type. What I could not close: `GraphSatAtStage` as
  the brief spelled it, and `hier-in-stage` as a term.

## ARCHIVE USED

- `archive/dev/LJ-dispatch-index.md`: read at `:1`. Quote:
  `# THE `LJ` DISPATCH INDEX, archived 2026-08-18`. Declined, not used.
  It is the retired dispatch index. This task measures a live chapter.
- `archive/dev/JOURNAL.md`: read at `:1`. Quote: `# ARCHIVED 2026-08-20`.
  Declined, not used. The per-episode journal is retired. The history
  of this task is this directory.
- `archive/dev/JOURNAL-archived.md`: read at `:1`. Quote:
  `# Archived journal: the retired route`. Declined, not used.
  Retired-route journal. The consumer is the live hull and hierarchy.
- `dev/ARCHIVE.md`: read at `:29`. Quote:
  `- **Module.** The module's name as it was known in the live tree, e.g.`
  Declined as not used for the term. No module is retired by this task.
- `archive/dev/DECISIONS-archived.md`: read at `:1`. Quote:
  `# Archived decisions: the D series`. Declined, not used. The live
  clauses that bound this slot are W2 and W4. W4 did not fire:
  nothing was retired.

## LITERATURE USED

- `dev/literature/devlin-II5.md`: read at `:107`. Quote:
  `The reverse inclusion M ⊆ ⋃_{γ<β} L_γ runs the same transfer on the`.
  Also read at `:108`. Quote:
  `statement "∃γ∃v∃z(φ(z,v,γ) ∧ x ∈ v)" (`dev2.txt:1245-1290`). Finally`.
  Used: the orthodox covering transfer is Σ₁-elementarity of a
  covering statement. W3 is not that statement. W3 is stage
  membership of the internal hierarchy, built by replacement.
  Devlin does not place `hierL` in a named stage.
- `dev/literature/truncation-and-selection.md`: read at `:1`. Quote:
  `# Truncation and selection: how the two literatures pick a witness`.
  Declined, not used. W3 is a membership. It is not a truncation
  question.
- `dev/literature/digest.md`: read at `:1`. Quote:
  `# Digest: the orthodox form of the rud route, pinned from the collected literature`.
  Declined, not used. No rud-route step is consulted.
- `dev/literature/geology.md`: read at `:1`. Quote:
  `# Geology dossier: set-theoretic geology sources and the five questions`.
  Declined, not used. Geology is not this membership.
- `dev/literature/terms-2026-08.md`: read at `:1`. Quote:
  `# The terminology dossier: fourteen renderings for the owner's ruling`.
  Declined, not used. No glossary term is at issue.

## WHAT I DID NOT DO

- I did not commit. I did not push.
- I did not set `GHCRTS`.
- I did not start a second Agda process.
- I did not write in `src/`.
- I did not inhabit `GraphSatAtStage` as the brief spelled it.
- I did not inhabit `hier-in-stage`.
- I did not inhabit `CoverWitnessesInHull` or `cover`.
- I did not take `levelIn` as a hypothesis.
- I did not postulate a stage bound.
- I did not add a reflection hypothesis.
- I did not rebuild `coverFo`, `code-of` or `ambient-level`.
- I did not attempt the only direction.
- I did not import a probe.
- I did not recompile `L.Choice.Order`.

## WORKING TREE, AS THIS REPORT DESCRIBES IT

Nothing committed, nothing pushed. No master edited. `src/`
untouched.

New files, all in `agents/tasks/LJ-1-494/`:

- `lj-1.494-report.md`, this report
- `Probe494.agda`, W3 as a type, obligation name as that type
- `review-of-GraphSatAtStage.md`, the stated NO-GO
- `runs/`, the Agda transcripts named above
