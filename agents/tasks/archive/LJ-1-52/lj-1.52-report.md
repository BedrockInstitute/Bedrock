# LJ-1.52: the level-hood adequacy at the hull

Status: COMPLETE (partial discharge). Written incrementally per C-22.
ASD-STE100. No commit. No push. No master edited. Probes:
`src/ProbeLJ152A.agda`, `src/ProbeLJ152B.agda`.

## 0. THE LEDGER (live)

Neither hypothesis is discharged. The obligation is one theorem with
three facets, and this dispatch pinned the obligation's semantic core
with two green probes, decomposed the twelve-row re-basing into its
named pieces, and proved the assembly of the graph agreement. The three
facet-pieces still stand, each with a precise survivor statement.

| hypothesis | home | status | what a survivor still needs |
|---|---|---|---|
| `levelIn` | `BoundedSubset:598`, `:1091` | SURVIVES | the `Adeq`-form adequacy at ordinal hull members (level at the parameter index), the arity-1 down-reflection (`DownReflect.ElemDown` at one parameter), the re-based decode at the hull, piece 1; see section 1 |
| `cover` | `BoundedSubset:599`, `:1092` | SURVIVES | the same adequacy (level-membership expressible in the hull), the least-delta Skolem selection, level-preservation under the collapse iso; see section 1 |

## 1. THE OBLIGATION, AS NOW PINNED

The chain for `levelIn`, with the slot reading machine-checked by Probe A:

- `levelHoodB` at env `w ∷ v ∷ γ ∷ K` means: `w = Lset γ` and `w ∈ K`
  (value slot 0, index slot 2, bound slot 3; the graph witness and the
  approximation are bounded existentials inside K and γ).
- `Σ₂` at env `[m]` therefore reads `∃γ : Lset γ ∈ m` (m contains a
  level).  The adequacy `levelIn` needs is the STRONGER parameter-index
  form `Adeq m`: `∃K' v' w' (w' ∈ K' ∧ matrix at env w' ∷ v' ∷ m ∷ K')`
  — the level AT m, witnessed inside K'.  `Adeq m` decodes to
  `w' = Lset m` (`ProbeLJ152A.agda:98-104`).  The [LJ-1.51] comment's
  "K' v' w' ∈ M of the level graph at m" is this `Adeq` form, not the
  bare `Σ₂`; the index must be the parameter m, which is why the
  elementarity must be applied to the parameter-index formula.
- The decode at the hull needs (a) the graph agreement at the class
  carrier (Probe B), (b) its re-basing to the hull's inner world, and
  (c) the elementarity down (the TV/ElemDown instance).
- `cover` needs the same adequacy for the level-MEMBERSHIP relation
  `y ∈ Lset δ` (expressible in the hull), the least-delta selection
  (a Skolem function of the hull), and `π y ∈ Lset (π δ)` under the
  collapse iso.

## 2. WHAT LANDED, AND WHAT EACH PIECE COST

### 2.1 The semantics of the level-hood matrix: PINNED (Probe A, green)

`src/ProbeLJ152A.agda` typechecks. `matrix-decode`
(`ProbeLJ152A.agda:58-61`): from `⟨ (w ∷ v ∷ γ ∷ K ∷ []) ⊨ LH0.matrix ⟩`
plus `IsOrd (fst γ)` plus the bounded-graph agreement, get
`fst w ≡ Lset (fst γ)`.  `Adeq` (`:78-81`) and `adeq-decode`
(`:98-104`) pin the adequacy statement at the parameter index and its
decode.  The only hypothesis is `GraphAgree` (`:48-51`), the bounded
graph against the machine graph.

### 2.2 The graph agreement: DECOMPOSED AND ASSEMBLED (Probe B, green)

`src/ProbeLJ152B.agda` typechecks. `graph-assembly`
(`ProbeLJ152B.agda:71-87`, PROVED) closes the bounded graph to the
machine `LsetGraphAt` from `StepAgree` (`:53-58`), `ApproxAgree`
(`:64-68`) and the site-fact bundle.  The class-carrier chain
matrix -> graphBndAt -> LsetGraphAt -> ride-only -> `w = Lset γ` is
fully assembled and machine-checked; the unbuilt content is
`StepAgree` (whose core is the `DefBodyB`/`DefBody` leaf adequacy) and
`ApproxAgree` (the `domB`/`domAt` and bound-bridging transfers).

### 2.3 Piece 3 (TV/ElemDown) and piece 1 (collapse commutes with Lset)

Neither is built.  Their precise survivor statements:

- **TV/ElemDown**: the consumer uses `DownReflect.ElemDown` only at
  arity 1 with one parameter and a code-constant formula
  (`BoundedSubset:432-437`).  The instance needs the
  parameter-to-code relabelling (each hull member's code, chosen
  classically over the stage's well-order) and the formula induction
  (`AtM.TV-thm`).  Structural, 150 to 300 lines on the delivered
  `hull-closed`, exactly the LJ-1.49 price.
- **Piece 1** `π (Lset m) = Lset (π m)`: NOT elementary.  The fixes
  route needs `Lset m ⊆ M` and `m ⊆ M`; both are the adequacy's own
  closure content, so the route is circular.  The iso route needs the
  level-hood formula's correctness at M and πM, which is the re-based
  decode plus the delivered `IsoInv`.  Piece 1 lands only after the
  adequacy; its price cannot be separated from the adequacy's.

## 3. MEASUREMENTS

Caliber: C-12 `GHCRTS="-A64m -I0 -M8g"`, USER seconds from
`/usr/bin/time -p`, cold module (own interface moved aside), deps warm,
ONE process, quiet machine.  Every figure is three completed runs; no
heap exhaustion, no interruption.

| probe | runs, user s | mean | spread | whole-file lines |
|---|---:|---:|---:|---:|
| `ProbeLJ152A` | 2.02 / 2.03 / 2.03 | 2.03 | 0.01 (0.5 pc) | 104 |
| `ProbeLJ152B` | 1.99 / 1.94 / 1.92 | 1.95 | 0.07 (3.6 pc) | 87 |

Both figures are cone-dominated: each probe's own content is about 45
non-comment lines, and the import cone (BoundedSubset plus Condensation
plus Sequence) is the quoted cost, which the ledger records as a
per-invocation interface cost (`dev/ledger.toml:2580-2586`).  No
marginal rate is quoted for content this small; the probes were built
to pin statements, not to price the unbuilt pieces.

## 4. THE WALLS, AS TERMS NOT WRITTEN

1. **The `DefBodyB`/`DefBody` leaf adequacy** (inside `StepAgree`).
   The term not written: the two-way satisfaction transfer between the
   bounded code-set description and the machine's `DefBody` at a
   common env, under the LEG D site facts.  LJ-1.7 already recorded
   that nothing proves it (`_build/lj-1.7-review.md:186-191`); this
   dispatch located it precisely as the leaf of `StepAgree`.
2. **The parameter-to-code relabelling** (inside the TV/ElemDown
   instance).  The term not written: a function `SM → Code` picking a
   canonical code for each hull member (the `CodeSelect` least-of
   pattern, delivered in `Co`), plus the satisfaction transfer between
   the parameter-in-env and the parameter-as-constant spellings
   (P-v's second-spelling family).
3. **Piece 1**.  The term not written is the fixes route's missing
   premise: `Lset m ⊆ M` for ordinal `m ∈ M`, which is the adequacy
   itself; and `m ⊆ M`, which is hull transitivity, absent because the
   Skolem hull is not transitive in general.  See section 2.3.

## 5. DD4 SPLIT

- The matrix semantics and the graph agreement (Probes A and B): the
  statements mention `LevelHood0` and `GraphB`, which are Def-side
  instantiations of generic templates.  The `graph-assembly` itself is
  template-shaped (it names only `graphBndAt`, `LsetGraphAt`,
  `StepAt`, `ApproxAt`); the J tower's analogue reuses the assembly
  with its own bounded graph.  The `DefBodyB` leaf is per-tower (D-26
  predicts it).
- `StepAgree` and `ApproxAgree`: template content once the leaf
  adequacy exists; they are LEG D shaped and mention no Def syntax in
  their types.
- The TV/ElemDown instance and the parameter coding: template content
  (generic in the hull and the well-order); the J tower instantiates
  the same machinery.
- Piece 1: template content if stated as `π (Lset m) = Lset (π m)`
  for a generic tower `Lset` and a generic collapse — but its proof
  runs through the per-tower level-hood decode, so the template
  statement is carried by a per-tower proof.
- `levelIn` and `cover` themselves: Def-side, as D-26 predicts; they
  key on the `Lset` construction.

## 6. ARCHIVE USED

- `_build/lj-1.51-report.md`, read WHOLE.  Took the survivor ledger
  (`:13-20`), the `levelIn` term structure (`:68-86`), the `cover`
  chain (`:88-97`), and the DD4 split (`:170-177`).
- `_build/lj-1.50-review.md`, read WHOLE.  Took the P-v extension
  (`:376-394`), the `EraseTransfer` route (`:2.1-2.6`), and the
  unpriced collapse-of-the-level note (`:442-443`).
- `_build/lj-1.49-report.md`, read WHOLE.  Took the hypothesis ledger
  (`:13-20`), the ElemDown bridge (`:87-94`), and the residue
  (`:96-103`).
- `_build/lj-1.48-report.md`, read WHOLE.  Took the consumer's shape
  (the transfer of ONE Sigma-1 statement, `:20-24`), the ElemDown
  residue (`:67`, `:238-240`), and the level-hood certificate class
  (`:99-107`).
- `_build/lj-1.7-review.md`, read sections 1 to 6.  Took the route
  (`:213-243`: M ≺ L, the iso, Sigma-1, upward absoluteness), the
  unbuilt adequacy and ElemDown (`:232-243`), and the DefBodyB
  adequacy absence (`:186-191`).
- `src/ProbeDD25H2.agda`, `src/ProbeDD25H3.agda`,
  `src/ProbeDD25H8.agda`, read WHOLE.  Took the `EraseTransfer`
  instantiation pattern and the Sigma-1 template.
- `src/L/BoundedSubset.lagda.md`, read WHOLE.  Took `LevelHood`
  (`:70-142`), `LevelHood0` (`:522-555`), `HullStage.Condense`
  (`:596-715`), `DownReflect` (`:350-450`), `AtHullInstance`
  (`:450-470`), `Co` (`:1077-1093`).
- `src/V/Collapse.lagda.md`, read WHOLE.  Took `Collapse` (`:40-97`),
  `πX-member` (`:78-80`), `InjExt` (`:220-312`), `fixes` (`:334-341`),
  `unique` (`:314-330`).
- `src/L/Condensation.lagda.md`, read `EraseTransfer` (`:273-294`),
  `RowTransfer`/`RowDecode` (`:1772-1806`), `SatGraphB` (`:2211-2258`),
  `DefBodyB` (`:2316-2350`), `GraphB`/`StepB`/`ApproxB`
  (`:2464-2508`), LEG D (`:2480-3430`), the row agreements
  (`:3429-3900`).
- `src/L/Hull.lagda.md`, read `TermAlgebra` (`:58-146`), `AtStage`/
  `AtM` (`:148-338`), `Hull` (`:313-425`), `hull-closed` (`:415`).
- `src/L/Hierarchy.lagda.md`, read `Lset-only` (`:334-339`),
  `Lset-defines` (`:646-649`), `approx-val` (`:251-270`).
- `src/L/Coding/Sequence.lagda.md`, read `StepAt`/`ApproxAt`/
  `GraphAt` (`:119-125`, `:286-330`), the renamings (`:349-354`).
- `src/L/Coding/Powerset.lagda.md`, read `DefBody`/`DefAt` (`:437-443`),
  `DefAt-in`/`DefAt-out` (`:645-666`).
- `archive/rud-route/src/L/Condensation.lagda.md`, read the shape only
  (the level story at both carriers).  WHY NOT more: `[LJ-1.11]` ruled
  its condensation target classically false, and the brief forbids
  taking a price from it.
- `dev/ledger.toml`: the DD24 bar (`:2590`, `:2810`), the cone note
  (`:2580-2586`).
- `dev/LESSONS.md` via `scripts/rules.py --for build`: P-h, P-k, P-l,
  P-m, P-n, P-t, P-u, P-v, R-35, R-38, R-40, I-5, C-12, C-22, C-31,
  C-32, C-33, C-34, C-35, C-36, C-37, D-10, D-26, D-29, D-30, read as
  the bundle; P-v (`:3037`), P-t (`:2601-2630`), P-u (`:2908-2940`),
  C-34 (`:3065-3092`), C-36 (`:3178-3224`), D-30 (`:3226`), C-37
  (`:3275`) read in full.

## 7. LITERATURE USED

- `_build/literature/dev2.txt:1372-1385`: Devlin 5.5's statement and
  proof chain.  TOOK: the condensation step is asserted as "By the
  Condensation Lemma, let π : M ≅ L_γ", which the formal proof must
  supply as the level-hood adequacy; nothing in the text prices it.
- `dev/literature/devlin-II5.md:209-257` (Step C): the level-hood
  strength requirement.  TOOK: level-hood at Sigma-1 with a bounded
  witness, the "witnessed inside the carrier" form, and the
  absoluteness at transitive carriers.
- The errata were NOT re-checked.  WHY NOT: `[LJ-1.14]` verified that
  Chapter II section 5 is not covered, and the brief forbids
  re-checking.
- `dev/literature/j-hierarchy.md` and the J-side digest were NOT read.
  WHY NOT: the J tower's level story does not change the statement or
  the decomposition of the L-side adequacy, which is the whole subject
  here.

Devlin's assumption, in one line: he assumes the Sigma-1 level-hood
statement is absolute at transitive carriers and that the collapse
preserves all first-order truth, and the formal proof must prove the
satisfaction transfer and the hull closure that this dispatch located
as `Adeq`, the graph agreement, and the ElemDown instance.

## 8. WHAT I AM NOT SURE OF

1. The `v` slot of the matrix (slot 1) is not read by the graph
   structure I traced; it may be read by the leaf `DefBodyB` at the
   deeper arities.  The decode does not need it, so the pin stands
   regardless, but the slot's purpose is not fully explained.
2. The `Adeq` form (parameter-index matrix) is not delivered as a
   formula in `LevelHood0`; the assembly must write it (a re-indexed
   `levelHoodB` with the index slot filled by the parameter).  Its
   Delta-0 certificate is a re-indexing of the delivered one, but the
   re-indexing is not built.
3. The `SiteFacts` bundle in Probe B is abstract; the exact conjunction
   at the graph env (tags, in-K, satisfiers) is LEG-D shaped but not
   enumerated here.
4. The outer proof that `Adeq m` holds in the stage at ordinal `m ∈ M`
   (the witness `K' = Lset (sucV m)` and the graph below m) is not
   built; it needs the level-graph construction (`graph-table`/
   `Lset-defines`) at the stage.
5. `IsOrd m` from `IsOrd (π m)` under the iso is not built; it is a
   standard absoluteness step (ordinals are Delta-0, the iso preserves
   satisfaction, πX is transitive) but the transport chain is not
   written.
6. The probes are cone-dominated; the quoted seconds are whole-file
   and the content deltas are noise at this size.
