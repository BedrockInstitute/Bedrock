# LJ-1.484 report: the hypothesis nobody has taken as an obligation

slot: `coder`. Written early as a skeleton and filled as runs landed (C-22).
No commit, no push. I wrote only in `agents/tasks/LJ-1-484/`. Agda ran
under the caliber the program set on this pane, `GHCRTS="-A64m -I0 -M8g"`,
ONE Agda process at a time. I did not set `GHCRTS`. No heap event.

TARGET: build ONE term in `agents/tasks/LJ-1-484/Probe484.agda`:

    cover : (y : S) → ⟨ y ∈ˢ M ⟩
          → ∥ Σ[ γ ∈ S ] (IsOrd γ × ⟨ γ ∈ˢ C.πX ⟩ × ⟨ C.π y ∈ˢ Lset γ ⟩) ∥₁

W3 first, the type the brief names:

    code-of : (y : S) → ⟨ y ∈ˢ M ⟩ → ∥ Σ[ c ∈ Code ] (fst (val c) ≡ y) ∥₁

The standing direction (`dev/pod/direction.md:37`) says one SRC
collection after LJ-1, not after `[LJ-2.5]`. This task is still LJ-1
work. It does not start that collection. It does not start phase 3.
No Boundary clause is in conflict.

## WHICH PREMISE MOVED

No predecessor delivered `cover`. The sibling `levelIn` is
`[LJ-1.462]`, NO-GO at D-10 step 3
(`agents/tasks/LJ-1-462/lj-1.462-report.md:77`). I did not inhabit
`levelIn`. I did not take it as a hypothesis.

`[LJ-1.160]` measured that the hull is not transitive
(`agents/tasks/LJ-1-160/lj-1.160-report.md:248`). That measurement
still stands. It is the bite on the walk from a hull member to its
stage index.

## D-10, BEFORE ANY AGDA

The brief's first cut, corrected. Written here before any term.

1. Hull membership is a truncated code. Delivered.

       hull-member :
           (x : S) → ⟨ x ∈ˢ Hull ⟩
         → ∥ Σ[ c ∈ Code ] (fst (val c) ≡ x) ∥₁

   Site: `src/L/Hull.lagda.md:337-339`. This is W3.

2. A Code does not bound a stage. The brief's step 2 is the wrong
   shape. `Code` has constructors `base` and `wit` only
   (`src/L/Hull.lagda.md:72-74`). `base` names a seed of `X`.
   `wit` names a formula and parameter codes. Neither constructor
   carries an ordinal.

3. Ambient covering at the stage. Delivered as tower decomposition,
   and it does not put the index in `M`.

       Lset-out :
           (α x : S) → ⟨ x ∈ˢ Lset α ⟩
         → ∥ Σ[ δ ∈ S ] (⟨ δ ∈ˢ α ⟩ × ⟨ x ∈ˢ 𝒟ₒ (Lset δ) ⟩) ∥₁

   Site: `src/L/Constructible.lagda.md:336-337`. Combined with
   `Hull⊆L` at `src/L/Hull.lagda.md:330-331`. The index is a
   member of `lam`. The hull is not transitive
   (`agents/tasks/LJ-1-160/lj-1.160-report.md:248`). So the
   index need not be a member of `M`.

4. Witnesses inside the hull. Unbuilt. This is the literature step.
   Devlin transfers `∃γ∃v∃z(φ(z,v,γ) ∧ x ∈ v)` into the hull by
   Σ₁-elementarity (`dev/literature/devlin-II5.md:107-108`). The
   tree's Φ is `LsetGraphAt` at the class carrier
   (`src/L/Coding/Sequence.lagda.md:349`). The hull language is
   `Formula (⊥* {ℓ})` (`src/L/Hull.lagda.md:74`). Those types
   do not meet. `[LJ-1.462]` measured the same meeting for
   `levelIn` and stopped.

5. Membership along the collapse, when both ends are in `M`.
   Delivered.

       π∈-fwd :
           (x y : S) → y ∈ᵗ x → y ∈ᵗ X → ⟨ π y ∈ˢ π x ⟩

   Site: `src/V/Collapse.lagda.md:102-103`. The carrier here is `M`.

6. The index in the image, when the preimage is in `M`. Delivered.

       πX-intro : (y : S) → ⟨ y ∈ˢ X ⟩ → ⟨ π y ∈ˢ πX ⟩

   Site: `src/V/Collapse.lagda.md:86-87`.

7. Decode at the image. Unbuilt. Devlin identifies the covering
   value by Φ and Σ₀ absoluteness at the transitive collapse
   image (`dev/literature/devlin-II5.md:102-108`). Devlin does
   not commute the collapse with the stage operation. The sibling
   `levelIn` is not a hypothesis of this probe.

## W8, LITERATURE, BEFORE ANY AGDA

`cover` is the reverse inclusion of Devlin 5.2: every member of the
hull lands in some level whose index is in the collapse image
(`dev/literature/devlin-II5.md:107-108`). The literature does not
ask the tree for a hypothesis the tree fails to state. It asks for
Σ₁-elementarity and for Φ. The tree states both, at the wrong
languages. That is an obstruction of a route, not a literature
refutation of the type. I do not stop as a literature NO-GO.

## PREDECESSOR TYPES

- `[LJ-1.462]` is NO-GO at D-10 step 3 for `levelIn`
  (`agents/tasks/LJ-1-462/lj-1.462-report.md:77`). The
  statement is not named FALSE. This task does not inhabit
  `levelIn`. It does not take `levelIn` as a hypothesis.
- `[LJ-1.160]` measured that the hull is not transitive
  (`agents/tasks/LJ-1-160/lj-1.160-report.md:248`). That
  measurement still stands.

## VERDICT

**NO-GO at D-10 step 4, after W3 and the ambient covering both
closed.** Step 1 is GO. Step 2 is the wrong shape. Step 3 is GO
and does not pay `cover`: the index is in `lam`, not in `M`.
Step 4 is unbuilt. That is the literature transfer of the covering
witnesses into the hull. The obligation term `cover` is not
written. Witness meter: 1 UNRESOLVED of 1, `probe_red=False`
(`runs/witness.out:1-2`).

This is an obstruction of two routes, not a refutation of `cover`.
I did not build a term of the negation. The NO-GO is stated in
`agents/tasks/LJ-1-484/review-of-cover.md`. That file is the
critic's input. It does not close the task.

## THE DECOMPOSITION

Every step as a type. Each marked BUILT or UNBUILT. This section
is what the next brief is written from.

1. **code-of.** BUILT. W3.

       code-of : (y : S) → ⟨ y ∈ˢ M ⟩
               → ∥ Σ[ c ∈ Code ] (fst (val c) ≡ y) ∥₁

   Term: `Probe484.agda:68-69`, `code-of = H.hull-member`.
   Supplier: `src/L/Hull.lagda.md:337-339`.

2. **StageBoundOfCode.** UNBUILT. Wrong shape. The brief's step 2.

       StageBoundOfCode :
           (c : Code) → Σ[ γ ∈ S ] (IsOrd γ × ⟨ fst (val c) ∈ˢ Lset γ ⟩)

   Site: `Probe484.agda:110-112`. `Code` is `base` or `wit`
   (`src/L/Hull.lagda.md:72-74`). Neither carries an ordinal.

3. **ambient-cover and ambient-level.** BUILT. Not `cover`.

       ambient-cover : (y : S) → ⟨ y ∈ˢ M ⟩
         → ∥ Σ[ δ ∈ S ] (⟨ δ ∈ˢ lam ⟩ × ⟨ y ∈ˢ 𝒟ₒ (Lset δ) ⟩) ∥₁

       ambient-level : (y : S) → ⟨ y ∈ˢ M ⟩
         → ∥ Σ[ γ ∈ S ] (IsOrd γ × ⟨ γ ∈ˢ lam ⟩ × ⟨ y ∈ˢ Lset γ ⟩) ∥₁

   Terms: `Probe484.agda:80-82` and `:88-98`. Suppliers:
   `Lset-out` at `src/L/Constructible.lagda.md:336-337`,
   `Hull⊆L` at `src/L/Hull.lagda.md:330-331`,
   `Lset-suc` at `src/L/Axioms/Basic.lagda.md:196`,
   `suc-ord` at `src/L/Ordinal.lagda.md:96`,
   `mem-ord` at `src/L/Ordinal.lagda.md:221`,
   `succλ` from the telescope. The index is in `lam`. It is
   not in `M`. The membership is of `y`, not of `C.π y`.

   Diagnostic: `code-ambient` (`Probe484.agda:103-105`) covers
   a code value by the same ambient `Lset-out`. It does not
   read a stage off `wit`.

4. **CoverWitnessesInHull.** UNBUILT. The failing step.

       CoverWitnessesInHull :
           (y : S) → ⟨ y ∈ˢ M ⟩
         → ∥ Σ[ γ ∈ S ] (⟨ γ ∈ˢ M ⟩ × IsOrd γ × ⟨ y ∈ˢ Lset γ ⟩) ∥₁

   Site: `Probe484.agda:123-126`. This is Devlin's Σ₁ transfer
   of the covering witnesses into the hull
   (`dev/literature/devlin-II5.md:107-108`). Ambient covering
   does not give `γ ∈ M`, because the hull is not transitive
   (`agents/tasks/LJ-1-160/lj-1.160-report.md:248`). The Φ
   that would reflect those witnesses is `LsetGraphAt` at
   `src/L/Coding/Sequence.lagda.md:349`, type `Formula CS.S n`.
   `wit` takes `Formula (⊥* {ℓ}) (suc k)` at
   `src/L/Hull.lagda.md:74`. Those types do not meet.

5. **π-mem.** BUILT. Both ends must already be in `M`.

       π-mem : (x y : S) → y ∈ᵗ x → y ∈ᵗ M → ⟨ C.π y ∈ˢ C.π x ⟩

   Term: `Probe484.agda:131-132`, `π-mem = C.π∈-fwd`.
   Supplier: `src/V/Collapse.lagda.md:102-103`.

6. **index-in-image.** BUILT. The preimage must already be in `M`.

       index-in-image : (γ : S) → ⟨ γ ∈ˢ M ⟩ → ⟨ C.π γ ∈ˢ C.πX ⟩

   Term: `Probe484.agda:137-138`, `index-in-image = C.πX-intro`.
   Supplier: `src/V/Collapse.lagda.md:86-87`.

7. **CoveredAtImage.** UNBUILT. Decode at the image.

       CoveredAtImage :
           (y : S) → ⟨ y ∈ˢ M ⟩
         → ∥ Σ[ γ ∈ S ] (⟨ γ ∈ˢ M ⟩ × IsOrd (C.π γ)
                       × ⟨ C.π y ∈ˢ Lset (C.π γ) ⟩) ∥₁

   Site: `Probe484.agda:145-149`. Devlin does this by Φ and
   Σ₀ absoluteness at the transitive collapse image
   (`dev/literature/devlin-II5.md:102-108`). It does not
   commute `π` with `Lset`. `levelIn` is not a hypothesis.

8. **Cover.** UNBUILT. The consumer's obligation.

       Cover :
           (y : S) → ⟨ y ∈ˢ M ⟩
         → ∥ Σ[ γ ∈ S ] (IsOrd γ × ⟨ γ ∈ˢ C.πX ⟩
                       × ⟨ C.π y ∈ˢ Lset γ ⟩) ∥₁

   Site: `Probe484.agda:153-156`. No term named `cover`.

## 1. What was built

All in `agents/tasks/LJ-1-484/Probe484.agda`, module
`LJ-1-484.Probe484 {ℓ} (lem)`.

- Telescope `HullStage` (`:44-56`), copied from
  `src/L/BoundedSubset.lagda.md:903-914`. The brief names
  `:903-916`. Line `:916` is `module Condense`, and it is
  not copied. `M = H.T.Hull`. `module C = Collapse M`.
  `levelIn` is not a parameter.
- Step 1 inhabited: `code-of = H.hull-member` (`:68-69`).
- Step 3 inhabited: `ambient-cover` (`:80-82`),
  `ambient-level` (`:88-98`), diagnostic `code-ambient`
  (`:103-105`).
- Step 2 as type: `StageBoundOfCode` (`:110-112`). Unbuilt.
- Step 4 as type: `CoverWitnessesInHull` (`:123-126`). Unbuilt.
- Step 5 inhabited: `π-mem = C.π∈-fwd` (`:131-132`).
- Step 6 inhabited: `index-in-image = C.πX-intro` (`:137-138`).
- Step 7 as type: `CoveredAtImage` (`:145-149`). Unbuilt.
- Obligation as type: `Cover` (`:153-156`). Unbuilt. No term
  named `cover`.

The first full check failed on unsolved metas at `mem-ord`'s
implicit `{A}`. I wrote `{A = lam}` at `Probe484.agda:96`.
The kept rechecks are after that fix.

Measured non-blank non-comment lines: 69. Total lines: 157.
The brief estimate was about 150 lines, of which the obligation
or its decomposition is about 50. Nothing is funded against
the estimate.

## W2 (DD4)

The mathematics is written once at a generic carrier. The module
is generic in `ℓ`. `lam`, `X` and the limit hypotheses stay
parameters. No ordinal is fixed. No second copy at a concrete
stage. The conflict the clause names (a deadline that forces a
fixed form) did not arise.

## W4 (DD13)

Nothing was retired. No module moved to `archive/`.

## STEP ONE, W3

**Hull membership is a truncated code.** `code-of`
(`Probe484.agda:68-69`) is the brief's type, inhabited.
The obligation is omitted.

`hull-member` at `src/L/Hull.lagda.md:337-339` is
`hull-member x x∈H = x∈H`. `Hull` at
`src/L/Hull.lagda.md:114-115` is
`sett Code (λ c → toSet (val c))`. So `⟨ y ∈ˢ M ⟩` is
already `∥ Σ[ c ∈ Code ] (fst (val c) ≡ y) ∥₁`. The
brief's guess that this is immediate is GO.

Three forced rechecks, `_build` interface removed before each,
dependencies warm, caliber `-A64m -I0 -M8g`, one Agda process.
Exit 0 every time. Each printed `Checking`.

| run | wall s | peak RSS bytes |
|---|---|---|
| `runs/w3-1.out` / `w3-1.time` | 2.58 | 471498752 |
| `runs/w3-2.out` / `w3-2.time` | 2.56 | 447315968 |
| `runs/w3-3.out` / `w3-3.time` | 2.56 | 471515136 |

Median wall **2.56 s**. Median peak RSS **471498752 bytes**. No heap
event. The first W3-only check `runs/w3-0.out` was 2.63 s and
456654848 bytes, also exit 0, also printed `Checking`. It is not
one of the three forced rechecks. The brief estimate for W3 was
about 6 lines and under 15 seconds. The measured median is under
that estimate.

`Code` still has two constructors at `src/L/Hull.lagda.md:72-74`:
`base` and `wit`. I did not add a third.

## STEP TWO, THE OBLIGATION

Omitted. Step 4 failed. The obligation is not inhabited. A
truncated conclusion was not written. `levelIn` was not added
as a hypothesis.

After W3, the brief's step 2 is the wrong shape. After the
ambient covering, the index is still not in `M`. Step 7 was
not reached as a term.

## 2. Runs, floor, witness

Caliber `-A64m -I0 -M8g`, set on the pane by the program and
untouched here. One Agda process at a time, every dependency
warm, from the repository root. The probe interface was deleted
before every kept run.

- W3, three forced rechecks: see the table above. Median
  **2.56 s**, **471498752 bytes**. Exit 0.
- Full file, three forced rechecks. The D-10 types are in the
  file. The obligation is omitted.

| run | wall s | peak RSS bytes |
|---|---|---|
| `runs/full-recheck-1.out` / `full-recheck-1.time` | 2.69 | 484720640 |
| `runs/full-recheck-2.out` / `full-recheck-2.time` | 2.66 | 484737024 |
| `runs/full-recheck-3.out` / `full-recheck-3.time` | 2.66 | 450789376 |

Median wall **2.66 s**. Median peak RSS **484720640 bytes**.
Exit 0 every time. Each printed `Checking`. No heap event.
The first green full check after the `{A = lam}` fix,
`runs/full-0.out`, was 2.63 s and 484704256 bytes, also
exit 0. It is not one of the three forced rechecks.

- Witness meter, one obligation: 1 UNRESOLVED of 1, 2.70 s,
  `probe_red=False` (`runs/witness.out:1-2`). The name `cover`
  is not in scope. That is the intended NO-GO reading. The
  worktree has no `.venv`. The meter ran under
  `/Users/alsg/Agentic/Bedrock/.venv/bin/python`.

## 3. What NO-GO earns, and what is still owed

NO-GO names which of the steps fails. It is step 4,
`CoverWitnessesInHull`. W3 is not the failure. The ambient
covering is not the failure. The index of that covering is
in `lam`, not in `M`. The hull is not transitive. The Φ that
would put the index in `M` is not in the hull language.

`levelIn` stays an unpaid sibling. `cover` stays an unpaid
hypothesis of `module Condense`.

What this task does not settle:

- It does not inhabit `StageBoundOfCode`.
- It does not inhabit `CoverWitnessesInHull`.
- It does not inhabit `CoveredAtImage`.
- It does not inhabit `cover`.
- It does not refute `cover`.
- It does not re-measure the `[LJ-1.462]` formula meeting
  at this consumer.
- It does not edit `src/`.
- It does not reach a term for step 7.

C-42: this is not a refutation. The count of the unpaid shape
in live `src/` is 4 binders, 3 applied spends, 3 pass-down
spends, 0 producers. The table is in `review-of-cover.md`.
I re-counted. I did not copy `[LJ-1.462]`'s `levelIn` counts.

## 4. What the next brief needs

- Do not order `code-of` again. It is `hull-member`.
- Do not order a stage bound read off a `Code`. `Code` has
  `base` and `wit` only. `code-ambient` covers a code value
  by `Lset-out`, not by the formula.
- Do not order `ambient-cover` or `ambient-level` again.
  They are inhabited. They do not pay `cover`.
- The next unpaid object on the literature route is
  `CoverWitnessesInHull`: the covering index inside `M`.
  A brief that sends that through `LsetGraphAt` as an
  argument to `wit` must re-measure the formula meeting
  at this consumer. `[LJ-1.462]` measured it for `levelIn`.
  C-42 forbids the transfer by analogy.
- Do not commute `π` with `Lset`. Devlin does not.
  `CoveredAtImage` is the decode at the image. It is not
  `levelIn`.
- Do not take `levelIn` as a hypothesis of a `cover` probe.
- What the statement cost: 69 non-blank non-comment lines,
  W3 median 2.56 s, full median 2.66 s, peak RSS 484737024
  bytes on the kept rechecks. What the shape resisted: the
  brief's step 2, then the walk from `lam` into `M`. What
  I had to weaken: nothing of the obligation. `ambient-level`
  is a diagnostic with a weaker index. What I could not
  close: `CoverWitnessesInHull`, `CoveredAtImage`, `cover`.

## ARCHIVE USED

- `archive/dev/LJ-dispatch-index.md`: read at `:1`. Quote:
  `# THE `LJ` DISPATCH INDEX, archived 2026-08-18`. Declined, not used.
  It is the retired dispatch index. This task measures a live chapter.
- `archive/dev/JOURNAL-archived.md`: read at `:1`. Quote:
  `# Archived journal: the retired route`. Declined, not used.
  Retired-route journal. The consumer is the live `BoundedSubset`
  chapter.
- `archive/dev/JOURNAL.md`: read at `:1`. Quote: `# ARCHIVED 2026-08-20`.
  Declined, not used. The per-episode journal is retired. The history
  of this task is this directory.
- `dev/ARCHIVE.md`: read at `:29`. Quote:
  `- **Module.** The module's name as it was known in the live tree, e.g.`
  Declined as not used for the term. No module is retired by this task.
- `archive/dev/DD-archived.md`: read at `:1`. Quote:
  `# THE `DD` RULING SERIES, archived in full 2026-08-18`. Declined,
  not used. The live clauses that bound this slot are W2 and W4. W4
  did not fire: nothing was retired.

## LITERATURE USED

- `dev/literature/devlin-II5.md`: read at `:95`. Quote:
  `> By 2.7 there is a Σ₀ formula Φ(z, v, γ) of LST such that`.
  Also read at `:107`. Quote:
  `The reverse inclusion M ⊆ ⋃_{γ<β} L_γ runs the same transfer on the`.
  Also read at `:108`. Quote:
  `statement "∃γ∃v∃z(φ(z,v,γ) ∧ x ∈ v)" (`dev2.txt:1245-1290`). Finally`.
  Used: `cover` is that reverse inclusion. Φ is the LST analogue.
  The transfer needs the witnesses in the hull. Devlin does not
  commute the collapse with the stage operation.
- `dev/literature/truncation-and-selection.md`: read at `:1`. Quote:
  `# Truncation and selection: how the two literatures pick a witness`.
  Declined, not used. W3 is hull membership. It is not a truncation
  question.
- `dev/literature/terms-2026-08.md`: read at `:1`. Quote:
  `# The terminology dossier: fourteen renderings for the owner's ruling`.
  Declined, not used. No glossary term is at issue.
- `dev/literature/digest.md`: read at `:1`. Quote:
  `# Digest: the orthodox form of the rud route, pinned from the collected literature`.
  Declined, not used. No rud-route step is consulted.
- `dev/literature/glossary-review-2026-08.md`: read at `:1`. Quote:
  `# Glossary review: the 119 pre-protocol entries`.
  Declined, not used. No glossary entry is at issue.

## WHAT I DID NOT DO

- I did not commit. I did not push.
- I did not set `GHCRTS`.
- I did not start a second Agda process.
- I did not write in `src/`.
- I did not inhabit `StageBoundOfCode`, `CoverWitnessesInHull`,
  `CoveredAtImage` or `cover`.
- I did not add a `Code` constructor.
- I did not postulate. I did not weaken the conclusion.
- I did not take `levelIn` as a hypothesis.
- I did not import a probe.
- I did not hide the transitivity gap in a `subst`.

## WORKING TREE, AS THIS REPORT DESCRIBES IT

Nothing committed, nothing pushed. No master edited. `src/`
untouched.

New files, all in `agents/tasks/LJ-1-484/`:

- `lj-1.484-report.md`, this report
- `Probe484.agda`, W3 and the D-10 types
- `review-of-cover.md`, the stated NO-GO
- `runs/`, the Agda transcripts named above
