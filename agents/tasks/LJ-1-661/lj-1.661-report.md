# LJ-1.661: pin the level-hood formula and read Lset off it

## VERDICT: NO-GO

The obligation `hoodsound-at-levelhood0` cannot be built. Its pin `φ₀` must
have TWO inputs, `Δ₀ φ₀` and `LsetOnlyAt φ₀`. No pin has both. The supplier
covers exactly one pin, `erase LsetGraph` at the class carrier, and at that
pin the Δ₀ input is uninhabited, and the pin term itself cannot be written
in the tree. The chapter's own shape, the one the brief names, is arity 4
with a free bound; its readings at arity 3 and arity 2 are Σ₁, and the
supplier does not speak of it. The mismatch the NO-GO earns is stated in
full in `review-of-hoodsound-at-levelhood0.md`.

## 1. THE TERM, AND ITS ABSENCE

The brief asks for one term: `soundP-leg2-from-pix` (agents/tasks/LJ-1-658/
Probe658.agda:317-325) instantiated at a pinned `φ₀` with both inputs
supplied. The probe `Probe661.agda` does NOT state the obligation name. A
qualified reference to an absent name is the witness meter's `[NotInScope]`,
and that reading is the NO-GO the branch table prices. The probe instead
states, green, every fact the verdict rests on:

| Fact | Site |
|---|---|
| `LsetGraph : Formula CS.S 2`, leading `∃̇` definitional | PART 1, `Probe661.agda:62-91` |
| `Δ₀-matrix : Δ₀ LH0.matrix`, arity 4 | PART 2, `Probe661.agda:105-107` |
| `Σ₁-Σ₂ : Σ₁ LH0.Σ₂`, the chapter's own grade | PART 2, `Probe661.agda:110-112` |
| `count-matrix : countFo LH0.matrix ≡ 0 = refl` | PART 2, `Probe661.agda:116-118` |
| `Σ₁-step1 : Σ₁ step1`, the arity-3 reading graded | PART 2, `Probe661.agda:122-126` |
| `step3 : Formula CS.S 2`, the arity-2 reading at the supplier's convention | PART 2, `Probe661.agda:139-143` |

## 2. SITE A: THE SUPPLIER'S PIN

The supplier is `Lset-only` (src/L/Hierarchy.lagda.md:334-335), a premise
satisfaction of `LsetGraphAt w b` at `w = zero`, `b = suc zero`. It covers
exactly one pin: `φ₀ = Cnt.erase LsetGraph p`. Two walls stand at it, one
after the other:

1. **The pin term is unstateable (measured).** Erasure needs
   `p : countFo LsetGraph ≡ 0`. The count does not compute: the recursion is
   stuck on the opaque core `satGraphAt` (src/L/Coding/Graph.lagda.md:203-205).
   Its official unfoldings are the readers `graphAt-in` / `graphAt-out`, not
   a rewrite (src/L/Coding/Graph.lagda.md:207-216). `refl` fails; the failure
   is measured in `runs/floor-1.out` (`[UnequalTerms]`, `suc (suc …)` against
   `zero`). The tree holds no zero-count lemma for this formula; its only
   successful zero-count proofs are for the chapter's normal-form matrix
   (agents/tasks/LJ-1-651/Probe651.agda:73-74, 115-116). The campaign measured
   the grade before: 2,287 unbounded `∃̇` and 2,159 unbounded `∀̇`
   (agents/tasks/LJ-1-646/lj-1.646-report.md:82).
2. **Even assuming `p`, `Δ₀ φ₀` is uninhabited (structural).**
   `LsetGraphAt w b = ∃̇ (ApproxAt zero (suc b) ∧̇ Step (suc w) (suc b) zero)`
   (src/L/Coding/Sequence.lagda.md:291-292, transparent). The leading
   constructor is the unbounded `∃̇`. `data Δ₀` has one constructor per
   allowed shape and no case for `∃̇` (src/FOL/LevyHierarchy.lagda.md:47-57).
   Erasure preserves the shape: `erase (∃̇ φ) p = ∃̇ erase φ p`
   (src/FOL/Count.lagda.md:607).

Both holes live in `Wall661.agda.txt`; the run is `runs/wall.out` (two
`[UnsolvedInteractionMetas]`, exit 42). The chapter itself grades the
statement Σ₁: its section 1 is titled "THE SIGMA-1 LEVEL-HOOD AT THE CLASS
CARRIER" (src/L/BoundedSubset.lagda.md:66).

## 3. SITE B: THE CHAPTER'S SHAPE

`LevelHood0` (src/L/BoundedSubset.lagda.md:840-860) exports the bounded
matrix at arity 4, env `w ∷ v ∷ γ ∷ K`, `K` the one free bound
(src/L/BoundedSubset.lagda.md:848-849), certified Δ₀ (src/L/BoundedSubset.
lagda.md:851-852). Its unbounded projection is `Σ₂ : Formula CS.S 1`,
certified Σ₁ by the chapter itself (src/L/BoundedSubset.lagda.md:855-859).
The three ways the shape cannot fill the arity-2 Δ₀ hole:

1. **Arity.** The hole demands arity 2; the chapter exports arity 4 and
   arity 1, never arity 2. The arity-2 reading exists (Probe661 builds it,
   `step3`), and it is Σ₁, not Δ₀.
2. **Grade.** Any arity-2 reading closes its value slot by an unbounded
   `∃̇`; no constructor of `Δ₀` matches `∃̇`
   (src/FOL/LevyHierarchy.lagda.md:47-57). Probe661 grades the arity-3
   reading green (`Σ₁-step1 = σ-∃ (σ-Δ₀ Δ₀-matrix)`). The arity-2
   certificate is stated but not built: the tree has no rename-preservation
   lemma for `Σ₁` (search of src/FOL/Manipulation/ came up empty).
3. **Slots.** The supplier reads value at slot 0, ordinal at slot 1, with no
   slot for a bound (src/L/Hierarchy.lagda.md:334-335). The matrix carries
   `K` free, and `Lset-only` has no reading of it.

The literature agrees with the tree on the shape: in every source the
arity-2 level-hood is Σ₁, and the Δ₀ form carries an extra bound (see the
LITERATURE USED section below).

## 4. W3, ANSWERED

**Question:** whether `Lset-only` instantiates at `LevelHood0`'s shape.
**Answer: no, in both directions.** `Lset-only` instantiates at its own pin,
`LsetGraphAt w b`, and the Δ₀ input there is empty and unstateable (section
2). At `LevelHood0`'s shape it has no reading at all: arity, grade and slots
all disagree (section 3). The brief's estimate of 70 to 150 lines is void:
the mismatch is a shape fact, not a price. Nothing of that length can be
wrong in a way a green check would not catch, because there is no term of
the required shape to write.

## 5. THE C-42 SWEEP

The refutation measures one site, the arity-2 Δ₀ pin. The sweep asked how
many sites carry the same false shape. Count: **1**. Search: `Δ₀ (∃̇` over
`src/` and the task homes, `LsetGraph` as a Δ₀ argument, and the `Lset-only`
readings. The shape appears once, at this pin. The chapter's Δ₀ content is
elsewhere (the matrix) and is priced there. Full record:
`review-of-hoodsound-at-levelhood0.md`, "Site count".

## 6. RUNS

One Agda process per run, wide caliber, guard 1500 s. Files under `runs/`,
convention `.out` = agda stdout, `.time` = the `/usr/bin/time -l -p` report,
`.rc` = the exit code.

| Run | What | Result |
|---|---|---|
| floor-0 | probe, first attempt | red: `FOL.Count` exports no `module Cnt` (`runs/floor-0.out`) |
| floor-1 | probe with the count pin | red: `refl` fails at `countFo LsetGraph ≡ 0`, the measured count wall (`runs/floor-1.out`) |
| floor-2 | probe, final | **green**, 3.12 s (`runs/floor-2.out`) |
| wall | `Wall661.agda.txt` via a temp copy, removed after | red: exactly the two intended holes, exit 42 (`runs/wall.out`) |

## 7. WHAT THE NEXT BRIEF NEEDS

1. **A soundness lemma reshaped to the statement's own shape.** One that
   speaks at arity 4 with `K` in the environment, takes the chapter's
   `Δ₀-matrix` (src/L/BoundedSubset.lagda.md:851-852), and whose transfer
   runs at the Σ₁ statement, not through `mapΔ₀`. That is the chapter's own
   named residue, "the level-hood instantiation at the hull"
   (src/L/BoundedSubset.lagda.md:901-904), priced at 0.0097 s per line.
2. **A rename-preservation lemma for `Σ₁`** if the arity-2 reading is to be
   graded rather than stated. `renameFo` is a variable map, so the lemma is
   structural; the tree has not built it.
3. **No route may demand `erase LsetGraph`.** The zero-count proof is
   unstateable while `satGraphAt` is opaque. Any consumer of the unbounded
   twin must work at the `GraphAt` level, or the seal must open with a price.

## 8. WORKING TREE

- `agents/tasks/LJ-1-661/Probe661.agda` — green, no hole, no obligation name.
- `agents/tasks/LJ-1-661/Wall661.agda.txt` — the red artifact, named
  `.agda.txt` per the brief; the harness copies it to a temp `.agda` for the
  wall run and removes the copy (verified absent).
- `agents/tasks/LJ-1-661/review-of-hoodsound-at-levelhood0.md` — the NO-GO.
- `agents/tasks/LJ-1-661/runs/` — the four runs, `run661.sh`, `log.md`.
- Nothing in `src/`. No generated file committed. The ratio bar is inert:
  the scope is a raw `.agda` probe with no in-fence lines.

## ARCHIVE USED

- **`dev/ARCHIVE.md` READ** (a standing source; the search did not name it).
  `dev/ARCHIVE.md:285` reads
  `The Crossing section stated the ambient-reading form of `Lset-only` at
  the class carrier.` and later on the same line
  `ambientOnly-from took 138.2 s of the chapter's 150.2 s, 92 percent of the
  profile total.` This is premise 5's basis, the measured old cost of the
  fork (b) route. Section 2 shows this dispatch does not trigger that route:
  the NO-GO is a shape fact at the pin, not a crossing.
- **`archive/dev/ORCHESTRATION.md` DECLINED.** Surveyed by grep for
  `hoodsound`, `Lset-only`, `levelhood`, `level-hood`, `leg 2`, `leg2`,
  `soundP`, `Δ₀`; zero hits. The archived process document; it carries no
  shape for this task.
- **`archive/dev/DD-archived.md` DECLINED.** Surveyed by grep, same
  keywords; zero hits in its 38 lines.
- **`archive/dev/PLAN-archived.md` DECLINED.** Surveyed; one hit,
  `archive/dev/PLAN-archived.md:139` reads
  `the first planned crossing has no Delta-0 witness, and route C's
  structural story`. That is the Phase 1 GCH-wing record, a different route,
  and a precedent in the same NO-GO family: a crossing with no Δ₀ witness.
  It confirms the family, nothing more; the standing plan is in `dev/pod/`.
- **`archive/dev/TASKS-archived.md` DECLINED.** Surveyed; its one hit,
  `archive/dev/TASKS-archived.md:268`, is the T263 desk pre-gate on sixteen
  Fof specs. Off this route.
- **`archive/dev/STATUS-archived.md` DECLINED.** Surveyed; its one hit,
  `archive/dev/STATUS-archived.md:87` reads
  `` `Lset-only`/`Lset-defines` and `hierL`; the fork was ruled 2026-07-29
  option (ii) ``. That is the DONE record of the supplier's delivery. Its
  origin is in the tree (src/L/Hierarchy.lagda.md:334-335); the record adds
  nothing to the verdict.

## LITERATURE USED

- **`dev/literature/level-formula-slot-roles.md` READ.**
  `dev/literature/level-formula-slot-roles.md:26` reads
  `| 4 | Devlin 5.2 (a) | `Φ(z,v,γ)` with `∀v∀γ [v = L_γ ↔ ∃z Φ(z,v,γ)]`
  | 3 in `Φ`, ONE closed |`, and
  `dev/literature/level-formula-slot-roles.md:28` reads
  `| 6 | Jech 13.14 | "The function `α → L_α` is Δ₁", from a Σ₁ step
  `∃W[...]` | 2 | `W`, the approximating function |`.
  **I used it to confirm the shape of the mismatch, not to price it.** Row 6
  is the arity-2 level-hood, and every source grades it Σ₁ by an unbounded
  `∃` over an approximating object: that is `LsetGraph`'s leading `∃̇`, and
  that is why site A's Δ₀ input is empty. Row 4 is the Δ₀ form, and it is
  arity 3 with one free bound, closed to arity 1: that is the chapter's
  matrix shape, and that is why site B's shape is not the hole's shape. The
  tree and the sources disagree on nothing here.
- **`dev/literature/glossary-review-2026-08.md` DECLINED.** Surveyed by
  grep, same keywords as the archive; zero hits. A glossary review; it
  settles terms, not shapes.
- **`dev/literature/BIBLIOGRAPHY.md` DECLINED.** Surveyed by grep; zero
  hits. The shelf list; the shelf is `level-formula-slot-roles.md`, which is
  read above.
- **`dev/literature/devlin-errata.md` DECLINED.** Surveyed by grep; zero
  hits. Errata for the Devlin extraction; the two rows used above are
  unaffected.
- **`dev/literature/primary-sources.md` DECLINED.** Surveyed by grep; zero
  hits. Source pointers; the rows used above carry their own locators.
