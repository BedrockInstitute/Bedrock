# LJ-1.517 report: a witness other than `hierL`

**VERDICT: NO-GO on `approx-in-stage`, and the door `[LJ-1.494]` left open
does NOT close the way the brief expected it to close.** The probe is GREEN,
exit 0 (`agents/tasks/LJ-1-517/runs/full-1.out`). The witness meter reads
`1 UNRESOLVED of 1, 2.29 s, probe_red=False`
(`agents/tasks/LJ-1-517/runs/witness.out:2`). The NO-GO is stated in
`agents/tasks/LJ-1-517/review-of-approx-in-stage.md`. That file is the
critic's input and it does not close the task.

Nothing landed in `src/`. Nothing is committed.

## 1. THE HEADLINE, IN THREE SENTENCES

`hierL` is NOT the only approximation the tree builds, and the witness slot
is already generic, so the census does not close the door.

The door closes anyway, because **every** witness in the stage pays the same
price, and that price is machine checked here: it forces `levelIn` below
`δ`, and in fact it forces the tower's value TWO membership steps below `α`.

The literature says the brief asked for the wrong thing: the orthodox
statement needs a **limit hypothesis on `α`**, not a second witness
(`dev/literature/devlin-II5.md:218`).

## 2. EVERY APPROXIMATION THE TREE BUILDS

**This section is the deliverable the brief demanded, and it is the W3
census.** Each row is a name from `src/`, re-declared in the probe at the
type this census claims for it, so a row that typechecks is checked evidence
and not a comment. All seven rows are green
(`agents/tasks/LJ-1-517/runs/w3-1.out`, exit 0).

| # | The set, or the slot | `file:line` | What it approximates | Bounded by a stage? |
|---|---|---|---|---|
| 1 | `hierL α`, the internal hierarchy | `src/L/Hierarchy.lagda.md:621` | the L-tower below `α` | **NO.** Its specification `IsHier` (`src/L/Hierarchy.lagda.md:502`) is a membership equivalence, not a bound. `[LJ-1.494]` measured this (`agents/tasks/LJ-1-494/lj-1.494-report.md:127`) |
| 2 | `graph-table`, the witness SLOT | `src/L/Hierarchy.lagda.md:382` | any correct, complete, domain-pinned table | **N/A.** It is a parameter `h : S`. **The slot is already generic** |
| 3 | `Lset-defines`, the one call site for the L-tower | `src/L/Hierarchy.lagda.md:646` | the L-tower | **NO.** Its witness is `hierL` (`src/L/Hierarchy.lagda.md:656`) |
| 4 | the induction hypothesis's table, inside `hierAt` | `src/L/Hierarchy.lagda.md:560` | the L-tower below `c` | **NO.** It is `hierAt` of the predecessor, the same family |
| 5 | `approxSet k` | `src/L/Choice/Before.lagda.md:1035` | the `relAt` recursion below a NUMERAL, not the L-tower | **YES, and this is the census's one positive answer.** `finSetL` spans it from a family that `smallStage` placed in one stage |
| 6 | `smallStage`, the placement lemma row 5 uses | `src/L/Choice/Before.lagda.md:1013` | n/a | **It RETURNS the ordinal.** It never bounds a family by an ordinal given in advance |
| 7 | `L.Choice.Table`'s `graph-table` and `tableAt` | `src/L/Choice/Table.lagda.md:511`, `:715` | the ordering recursion, not the L-tower | **NO.** Same generic slot, filled by the induction hypothesis |

**THE ANSWER TO THE BRIEF'S STOP CONDITION.** The brief said: if `hierL` is
the only approximation the tree ever builds, stop and say so. **`hierL` is
NOT the only one.** Row 5 is a real, delivered, stage-bounded approximation
that is not `hierL`. So the census does NOT close the door, and this task
does not stop there.

**BUT ROW 5 DOES NOT TRANSFER, AND THE REASON IS EXACT.** Row 5 approximates
a different recursion, it is finite because its index is a numeral, and its
stage is CHOSEN by `smallStage` rather than given. The obligation gives `α`
in advance. A measured cure does not transfer by analogy (AGENTS.md
Boundary), and I did not transfer it.

## 3. WHAT I BUILT INSTEAD, AND WHY IT ANSWERS THE BRIEF

The obligation term is not built. Two other terms are, and they settle the
question the obligation was asked to settle.

### 3.1 `witness-forces-levelIn` (`agents/tasks/LJ-1-517/Probe517.agda:181`)

    (δ f : S) → IsOrd (fst δ) → Approximates δ f → ⟨ fst f ∈ Lset α ⟩
  → (c : S) → ⟨ fst c ∈ fst δ ⟩ → ⟨ Lset (fst c) ∈ Lset α ⟩

Any approximation of the tower below `δ` that lies in `Lset α` forces the
tower's value at every argument below `δ` into the same stage. The proof is
three steps: `ApproxAt-value` plus `approx-val` put the pair
`pr c (Lset c)` inside `f` (`src/L/Coding/Sequence.lagda.md:298`,
`src/L/Hierarchy.lagda.md:274`), then transitivity of the stage
(`src/L/Constructible.lagda.md:183`, `:246`) walks the Kuratowski pair down
twice (`src/V/Coding.lagda.md:175`).

**The conclusion is `levelIn` below `δ`, and `levelIn` is a HYPOTHESIS at
every site in the live tree**: `src/L/BoundedSubset.lagda.md:917` and
`src/L/BoundedSubset.lagda.md:1555` both take it as a module parameter.

`obligation-gives-levelIn` (`agents/tasks/LJ-1-517/Probe517.agda:191`)
states the same fact against the brief's own type, so no inhabitant of
`ApproxInStage` escapes it, `hierL` or not.

### 3.2 `witness-forces-two-below` (`agents/tasks/LJ-1-517/Probe517.agda:204`)

    ... → ∥ Σ[ β ∈ V ℓ ] Σ[ γ ∈ V ℓ ]
             (⟨ β ∈ α ⟩ × ⟨ γ ∈ β ⟩ × ⟨ Lset (fst c) ∈ Lset γ ⟩) ∥₁

Unfolding the stage twice (`src/L/Constructible.lagda.md:340`, `:313`) says
the tower's value at `c` sits at a stage `γ` with `γ ∈ β ∈ α`. **The witness
does not want room in `Lset α`. It wants room two membership steps below
`α`.** This is the number the next brief needs.

## 4. THE OBLIGATION TYPE

`ApproxInStage` (`agents/tasks/LJ-1-517/Probe517.agda:144`) FORMS. It is
written exactly as the brief spells it, with one spelling note recorded in
the file: `𝒮ᵥ`'s `∈ˢ` IS the base `_∈_` (`src/V/Hierarchy.lagda.md:83`), and
this file has `𝒮ʟ`'s `∈ˢ` open, so V-level membership is spelled `_∈_`.

"`f` approximates the tower below `δ`" is spelled as the delivered `ApproxAt`
at a two-slot environment (`src/L/Coding/Sequence.lagda.md:286`).

The type is not inhabited. `--safe` is on, so there is no postulate and no
hole.

## 5. WHAT THE LITERATURE SAYS, AND IT CORRECTS THE BRIEF

`dev/literature/devlin-II5.md:221` states Devlin 2.6(ii): the sequence
`(L_δ | δ ≤ γ)` is in `L_α` for `γ < α`. `dev/literature/devlin-II5.md:218`
states the hypothesis that carries it: **uniform Δ₁ at limit `α > ω`**.

Two consequences, and both matter for the next brief.

1. **The orthodox witness IS the level sequence.** "The witness `z` bundles
   the level sequence and its bound" (`dev/literature/devlin-II5.md:216`).
   That is `hierL`. **The orthodox argument has no second witness, so the
   brief's search had no target in the literature either.**
2. **What is missing is a hypothesis on `α`, not a witness.** With `α` a
   limit above `ω`, the statement is orthodox and true.

**And the machine-checked price agrees with the hypothesis exactly.**
`witness-forces-two-below` asks for two membership steps of headroom inside
`α`. A limit `α` always has them. An arbitrary `α` with `δ ∈ Lset α` does
not.

## 6. THE HISTORY OF `levelIn`, READ FROM THE ARCHIVE

`archive/dev/LJ-dispatch-index.md:254` records `[LJ-1.178]`: "Build levelIn
and cover" returned "BUILT, THEOREM DOES NOT DERIVE", and "the debt moves to
the STAGE". **The live tree still carries `levelIn` as a module parameter**
(`src/L/BoundedSubset.lagda.md:917`), so whatever was built then does not
stand at that site today. I did not re-open that history; the live tree is
the authority and the archive is the pointer.

## 7. PRICE

**One Agda process per run. `GHCRTS="-A64m -I0 -M8g"`, the wide caliber, set
on the pane by the program and untouched by me. Three FORCED rechecks each,
forced by deleting `Probe517.agdai` before every run, because `touch` alone
does NOT force a recheck on this tree: runs 2 and 3 of a `touch`-only attempt
produced a zero-byte log. No heap wall. No rerun of a walled run.**

| Measurement | Median wall | Median peak RSS | Evidence |
|---|---|---|---|
| W3, the census alone | 2.21 s | 417,808,384 bytes | `runs/w3-1.time`, `runs/w3-2.time`, `runs/w3-3.time` |
| full file | 2.44 s | 427,933,696 bytes | `runs/full-1.time`, `runs/full-2.time`, `runs/full-3.time` |
| witness meter | 2.29 s | not measured | `runs/witness.out:1` |

W3 wall times: 2.20 s, 2.21 s, 2.27 s. Full file wall times: 2.44 s, 2.43 s,
2.49 s.

**The brief estimated about 130 lines in the probe, of which the obligation
was about 35. MEASURED: 230 lines, 128 non-blank non-comment, of which the
obligation block is 66.** The overrun is in the census, which the brief
priced as reading only: seven rows written as checked type ascriptions cost
62 non-blank non-comment lines instead of zero. **That was my choice, and I
state it: a census in a comment is not evidence.**

The brief also priced W3 at "under 30 seconds of Agda" and warned against
funding it against `[LJ-1.514]`'s census run. MEASURED at 2.21 s. The brief's
ceiling held.

## 8. WHAT THE STATEMENT COST, WHAT RESISTED, WHAT I WEAKENED

**What it cost.** 128 non-blank non-comment lines, 2.44 s median for the full
file, 417 to 428 MB peak RSS.

**What resisted.** Nothing in the elaborator. The whole file typechecked on
the first attempt after one missing import. **The resistance was entirely
mathematical**: the obligation has no term, and finding out WHY needed the
reduction rather than an attempt at the term.

**What I had to weaken.** The obligation, completely. I built no witness. I
replaced it with two theorems about what any witness would cost.

**What I could not close.** `approx-in-stage` as a term. `hier-in-stage`. The
converse of section 3.1: whether `levelIn` below `δ` plus a limit `α` gives
the witness back. That converse needs the collection to happen INSIDE the
stage, and the tree's only in-stage collector is the definable power set at a
successor (`src/L/Constructible.lagda.md:301`). **I did not price it, and it
is the first thing the next brief should price.**

## 9. WHAT THE NEXT BRIEF NEEDS

- **Do not order another "different witness" task.** The census says the
  witness slot is generic (`src/L/Hierarchy.lagda.md:382`) and the literature
  says the orthodox witness is the level sequence
  (`dev/literature/devlin-II5.md:216`). There is no second witness to find.
- **Order the limit hypothesis instead.** `hier-in-stage` at limit `α > ω` is
  Devlin 2.6(ii) (`dev/literature/devlin-II5.md:218`, `:221`). That is the
  statement with a source. The current spelling, at an arbitrary `α` with
  `δ ∈ Lset α`, has none.
- **Take the price from section 3.2, not from section 3.1.** A brief that
  budgets only `levelIn` will under-price the task. The witness needs the
  tower's value two membership steps below `α`.
- **`GraphSatAtStage` depends on `hier-in-stage`, and now that dependency is
  measured rather than assumed.** `[LJ-1.494]` said "or until a brief names a
  different witness than `hierL`"
  (`agents/tasks/LJ-1-494/lj-1.494-report.md:358`). **That clause can be
  retired.**
- **Do not order `Bounding` at this site.** The brief forbade it and the
  forbidding was right. I did not import it.
- **Do not order `cover` or `levelIn` again on the strength of this task.**
  `[LJ-1.492]` forbids re-ordering `coverFo`
  (`agents/tasks/LJ-1-492/lj-1.492-report.md:336`), and `code-of` and
  `ambient-level` (`agents/tasks/LJ-1-492/lj-1.492-report.md:337`). This task
  adds no ground to re-open any of them.
- **The converse in section 8 is the next real question**, and it is a
  pricing task, not a build task.

## 10. WHAT THIS TASK DOES NOT SETTLE

- It does not inhabit `approx-in-stage`.
- It does not inhabit or refute `hier-in-stage`.
- It does not build a term of the negation of `ApproxInStage`. This is an
  obstruction, not a refutation.
- It does not attempt `GraphSatAtStage`, `cover` or `levelIn`. AD12 gives
  this brief one obligation.
- It does not re-measure `hierL`'s bound. `[LJ-1.494]` settled that and the
  brief forbade re-opening it.
- It does not edit `src/`.
- It does not commit and it does not push.

## W2 (from DD4)

**Answered: W2 did not bind this task, and here is why.** W2 asks that the
mathematics be written once at a generic carrier and instantiated. This task
wrote no mathematics into `src/`. Every term is in a probe under
`agents/tasks/`. **The one place where W2's shape is visible is census row 2**:
`graph-table` is ALREADY written at a generic witness
(`src/L/Hierarchy.lagda.md:382`), and this task's finding is that the
genericity does not help, because the price is paid by the witness type and
not by the witness. No conflict with a deadline arose, so no stop under W2.

## W4 (from DD13)

**Answered: W4 did not fire.** No module was retired, so there is no
`archive/` move and no `dev/ARCHIVE.md` row. The probe is tracked and is
never deleted, as the coder instruction requires.

## ARCHIVE USED

- `archive/dev/LJ-dispatch-index.md`: **READ AND USED.** Read at `:254`.
  Quote: `| LJ-1.178 | Build levelIn and cover | BUILT, THEOREM DOES NOT DERIVE | Two of three facts discharged and the debt moves to the STAGE. New wall: Devlin's (a) at the AMBIENT carrier |`
  Used in section 6: it is the pointer to `levelIn`'s history, and it is why
  I checked the live tree rather than trusting the archive.
- `archive/dev/JOURNAL-archived.md`: read at `:1`. Quote:
  `# Archived journal: the retired route`. **DECLINED, not used.** It is the
  retired route's journal. This task measures the live hierarchy chapter.
- `archive/dev/JOURNAL.md`: read at `:1`. Quote: `# ARCHIVED 2026-08-20`.
  **DECLINED, not used.** The per-episode journal is retired. The history of
  this task is this directory.
- `archive/dev/DECISIONS-archived.md`: read at `:1`. Quote:
  `# Archived decisions: the D series`. **DECLINED, not used.** The live
  clauses that bind this slot are W2 and W4, and both are answered above.
- `dev/ARCHIVE.md`: read at `:1`. Quote: `# ARCHIVE.md: the archive registry`.
  **DECLINED, not used for the term.** W4 did not fire, so no row is owed.

## LITERATURE USED

- `dev/literature/devlin-II5.md`: **READ AND USED, and it is the finding of
  section 5.** Read at `:216`. Quote:
  `   The witness z bundles the level sequence and its bound.`
  Read at `:218`. Quote:
  `2. Uniform Δ₁ at limit α > ω (`dev2.txt:674-686`, 2.6-2.7): for γ < α,`
  Read at `:221`. Quote:
  `   live inside L_α; that is 2.6(ii), the sequence (L_δ | δ ≤ γ) ∈ L_α for`
  Used: the orthodox witness IS the level sequence, so no second witness
  exists to find; and the hypothesis the orthodox statement carries is that
  `α` is a limit above `ω`, which the brief's spelling does not have.
- `dev/literature/truncation-and-selection.md`: read at `:1`. Quote:
  `# Truncation and selection: how the two literatures pick a witness`.
  **DECLINED for the finding.** The obligation's failure is not a selection
  failure. `ApproxAt-value` returns a truncation and the probe eliminates it
  into an `hProp` without difficulty
  (`agents/tasks/LJ-1-517/Probe517.agda:168`). Nothing here needed a choice
  principle.
- `dev/literature/digest.md`: read at `:1`. Quote:
  `# Digest: the orthodox form of the rud route, pinned from the collected literature`.
  **DECLINED, not used.** It pins the `rud` route. This task is on the `Def`
  side, at the hierarchy chapter.
- `dev/literature/terms-2026-08.md`: read at `:1`. Quote:
  `# The terminology dossier: fourteen renderings for the owner's ruling`.
  **DECLINED, not used.** Terminology. This task adds no term and writes no
  prose for `docs/`.
- `dev/literature/glossary-review-2026-08.md`: read at `:1`. Quote:
  `# Glossary review: the 119 pre-protocol entries`. **DECLINED, not used.**
  Same reason. No `dev/glossary.toml` entry is proposed.
