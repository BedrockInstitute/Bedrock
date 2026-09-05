# LJ-1.651: the Lset graph as a FORMULA over the hull's alphabet

## VERDICT: GO

The obligation `lset-formula` is built, typechecks, and the witness meter reads
**0 UNRESOLVED of 1** (`runs/witness-1.out`). A Σ₀ matrix over the hull's code
alphabet **can** say `Lset`: the route [LJ-1.646] named is inhabited, and the
grade wall does not recur in the Σ₀ shape (section 4 gives the count).

Nothing lands in `src/`. The working tree carries exactly one `.agda` under
this task home, and it typechecks; the runs are tracked in `runs/`.

## 1. WHAT WAS BUILT

`agents/tasks/LJ-1-651/Probe651.agda`, 156 lines, 60 of them non-blank and
non-comment. One term is the obligation; the rest are its parts.

| Name | Line | Content |
|---|---|---|
| `LH0` | `:67-69` | `LevelHood0` instantiated, all 16 Fin slot positions `zero` |
| `count-matrix` | `:73-74` | `countFo LH0.matrix ≡ 0 = refl` — the matrix has no constant |
| `step1` | `:81-82` | `∃̇ LH0.matrix`, env `v ∷ γ ∷ K` — closes the unused `u` |
| `Σ₁-step1` | `:87-88` | `σ-∃ (σ-Δ₀ LH0.Δ₀-matrix)` — the grade certificate |
| `rot`/`step2` | `:91-97` | `renameFo` rotating `K` to the front |
| `step3` | `:100-101` | `∃̇ step2`, env `v ∷ γ` — closes the bound `K` |
| `swap`/`twoSlot` | `:106-111` | consumer order: ordinal slot 0, value slot 1 |
| `count-twoSlot` | `:115-116` | `countFo twoSlot ≡ 0 = refl` — still no constant |
| `slide` | `:128-129` | the carrier slide `CS.S → Code`; `mapFo` never evaluates it |
| `lset-formula` | `:141-142` | **`mapFo slide twoSlot : Formula Code 2`** — the obligation |
| `inF` | `:149-150` | `∃̇ (lset-formula ∧̇ (var zero ≐ con c)) : Formula Code 1` — the shape `hull-closed` takes |

**THE READING.** At a fixed ordinal code `c` and value code `d`, satisfaction of
`inF c` says: there exist a bound `K`, construction data `u`, and a witness
`w ∈ K` such that `w` is a bounded construction-graph approximation of
`val d` from `u` at level `val c` (`graphBndAt`,
`src/L/Condensation.lagda.md:2492-2493`) **and** `val d ≐ w` — i.e.
`val d = Lset (val c)`. That is the tree's own bounded matrix
`levelHoodB` (`src/L/BoundedSubset.lagda.md:107-111`: "exists w in K (graph w
gamma K and v = w)"), read at the two parameter slots with the bound
existentially closed, then carried to the hull alphabet by `mapFo`.

It is Devlin 2.7(a) in the tree's notation. The literature states:
"By 2.7 there is a Σ₀ formula Φ(z, v, γ) of LST such that (a) ∀v∀γ
[v = L_γ ↔ ∃z Φ(z, v, γ)]" (`dev/literature/devlin-II5.md:95-96`). The `z`
is the triple `(K, u, w)` existentially closed here; `v` and `γ` are the two
slots.

**THE ARITY DECISION.** The brief's obligation block says `Formula Code 1`;
its constraint says "carrying its parameters in SLOTS". The two are two faces
of one term, and both are delivered: the matrix `lset-formula` is arity 2
(ordinal slot 0, value slot 1 — the slot order of [LJ-1.642]'s `Det`/`Wit`,
`agents/tasks/LJ-1-642/Probe642.agda:91-97`), and its arity-1 reading is
`inF c` (`:149-150`), the exact shape `hull-closed` takes
(`src/L/Hull.lagda.md:415`). [LJ-1.642]'s `inF` is the composition law
(`agents/tasks/LJ-1-642/Probe642.agda:158-159`); this probe applies it.
Arity 1 cannot carry both parameter roles in slots, so the 2-slot form is the
deliverable and the 1-slot form is derived from it.

## 2. THE PREMISES, CHECKED

1. **[LJ-1.648]** — verified at
   `agents/tasks/LJ-1-648/lj-1.648-report.md:245-247`: "A brief that asks
   only for" the code-level statement "throws the ingredient away"; the
   FORMULA half is what the index gap wants.
2. **`hull-closed` takes `Formula Code 1`** — verified at
   `src/L/Hull.lagda.md:415-416`: `hull-closed : (φ : Formula Code 1) → ...`.
   `inF` is built to feed it.
3. **[LJ-1.642] owes exactly a FORMULA** — its `Det`/`Wit` take
   `ψ : Formula T.Code 2` in slot order `(b ∷ a ∷ [])` = ordinal, value
   (`agents/tasks/LJ-1-642/Probe642.agda:91-97`). `lset-formula` is that `ψ`,
   in that order.
4. **[LJ-1.646] named the route** — verified at
   `agents/tasks/LJ-1-646/lj-1.646-report.md:281-285`: "THE OBJECT TO FUND IS
   A READING OF `levelHoodB` at two slots, then its instantiation at the
   hull's code alphabet ... it accepts a Σ₀ matrix on the same three lines."
   The probe is that route, executed.
5. **The decoder debt stays closed** — the matrix carries no constant
   (`count-matrix`, `count-twoSlot`), so no route reads an abstraction back
   through `⊨-abs`; [LJ-1.474]'s unproved decoder, "It does not prove
   `fst (val (ck (tagOf s))) ≡ fst s`"
   (`agents/tasks/LJ-1-474/lj-1.474-report.md:253`), is not needed. Verified
   by construction, not by re-reading.

## 3. THE ROUTE REFUSAL, HELD

`wit` at `absFo LsetGraph` was not rebuilt. The wall is arithmetic: 2,287
unbounded `∃̇` and 2,159 unbounded `∀̇` interleaved, "so NO delivered transfer
theorem applies" (`archive/dev/JOURNAL-archived.md:631-632`, quoted at
`agents/tasks/LJ-1-646/lj-1.646-report.md:82` and restated at `:278-280`).
The probe never names `LsetGraph`.

## 4. W3, ANSWERED: THE GRADE OF THE Σ₀ SHAPE

**The Σ₀ matrix over the code alphabet can say `Lset`, and the grade wall
does not recur.** The count for the shape:

- `lset-formula` is **Σ₁**: **2 unbounded `∃̇`** (the closures of `u` and `K`)
  and **0 unbounded `∀̇`** over the Δ₀ core `LH0.Δ₀-matrix`.
- The grade certificate for the first closure is in the tree itself:
  `Σ₁-levelHood = σ-∃ (σ-Δ₀ Δ₀-levelHoodB)` at
  `src/L/BoundedSubset.lagda.md:145-146`; the probe carries the twin for
  `step1` (`Σ₁-step1`, `Probe651.agda:87-88`). The transfer that applies is
  `σ₁-up : ∀ {n} {φ} → Σ₁ φ → ...` (`src/FOL/Absoluteness.lagda.md:182-184`).
- The renames (`renameFo`, `src/FOL/Manipulation/Renaming.lagda.md:58`) and
  `mapFo` (`src/FOL/Manipulation/Relabelling.lagda.md:54`) move variables and
  carriers; they add no quantifier and no constant.
- The constant count is **0** at the matrix and at the full reading
  (`count-matrix`, `count-twoSlot`, both `refl`).

Contrast: [LJ-1.646]'s route was in no delivered grade class at all
(2,287 ∃̇ interleaved with 2,159 ∀̇, `agents/tasks/LJ-1-646/lj-1.646-report.md:90-91`);
this shape is Σ₁ with zero universals. The NO-GO branch of the brief — "the
hull's language cannot name Lset at any grade" — is false, and the stop that
would have gone to the owner is not taken.

**One open note, not a wall.** The tree carries no `renameFo` grade
preservation theorem (no such lemma exists in `src/FOL/Manipulation/`); the
grade of `twoSlot` follows by construction (renames add no quantifier), and
the first-closure certificate `Σ₁-step1` is delivered. A next task that needs
the full certificate can close the two `σ-∃` steps by hand in two lines.

## 5. MEASUREMENTS

One Agda process per run, wide tier `GHCRTS="-A64m -I0 -M2g"` (set on the
pane by the program, untouched), warm interface cache (710 `.agdai` under
`_build/2.8.0/`).

| Run | Target | Result | Real | Peak RSS |
|---|---|---|---|---|
| step1-0 | probe, first attempt | exit 42, `[AmbiguousName]` on `Fin` (`runs/step1-0.out`) | — | — |
| step1-1 | probe, after dropping the redundant `Cubical.Data.Fin` import | exit 0 (`runs/step1-1.out`) | 5.19 s | — |
| recheck 1–3 | probe, forced, probe interface removed each time | exit 0 (`runs/recheck-{1,2,3}.out`) | 3.88 / 4.00 / 3.88 s | 909,918,208 / 909,869,056 / 909,869,056 B |
| final-0 | probe, after citation corrections | exit 0 (`runs/final-0.out`) | 4.96 s | 909,901,824 B |
| witness | meter over the brief's obligation | **0 UNRESOLVED of 1**, `probe_red=False` (`runs/witness-1.out`) | 2.86 s | — |

The `Fin` ambiguity was the only failure of the whole task: `Base.Prelude`
already re-exports `Cubical.Data.FinData` public, and the probe's explicit
`Cubical.Data.Fin` import made `Fin` ambiguous. The fix is one import line
removed; the recheck is green.

**Heap: no wall.** Peak RSS tops out at 909,901,824 B against the 2 g cap;
no GHC heap event in any run.

**The floor attempt, tracked.** A separate floor file (frame, obligation as
type-only) cannot typecheck: Agda reports `[MissingDefinitions]` for names
declared without defined (`runs/floor-0.out` records the failure; the dead
file was deleted rather than named `.agda.txt` because it was an intermediate
bisection arm, and this section cites it). The step1-1 row plays the floor's
role: it is the first full check of the file at its final shape.

**Line count against the estimate.** The brief estimated 120–250 lines, basis
[LJ-1.646]'s green frame (`agents/tasks/LJ-1-646/lj-1.646-report.md:29`).
The probe is 156 lines: inside the estimate, and the whole thing elaborates
in under 5 s.

## 6. WHAT GO EARNS AND WHAT REMAINS

GO unlocks the five measured consumers, each now able to name the formula:

- **clause (i)** ([LJ-1.642]): `Det`/`Wit`/`Holds` at `ψ = lset-formula`,
  slots already in their order (`b ∷ a ∷ []` = ordinal, value).
- **clause (iii)'s three gaps** ([LJ-1.648]): the arity-1 reading `inF c` is
  the argument `hull-closed` takes.
- **clause (ii)'s cover** ([LJ-1.595]): `CodedCover`
  (`agents/tasks/LJ-1-595/Probe595.agda:353-357`) is a code-level object, and
  its producer `cover-from-coded` closes the slot to a code constant exactly
  the way `inF` does (`:368-369`); the formula supplies the `Lset` half.
- **both computation-law stops**: same formula, same reading.

**What the next brief needs:**

1. **Feed `lset-formula` into [LJ-1.646]'s join** — the three lines the
   report promises (`agents/tasks/LJ-1-646/lj-1.646-report.md:281-285`).
   **Slot order at the splice:** this probe's slots are ordinal 0 / value 1
   ([LJ-1.642]'s order); [LJ-1.646]'s `Feed646` instance runs the environment
   value-first (`c ∷ P.lset-codes`, `agents/tasks/LJ-1-646/Probe646.agda:172`).
   The transpose is one `renameFo` at the splice site; this probe measured
   `renameFo` on the formula as part of a 3.88 s run, so the splice costs
   milliseconds.
2. **The adequacy derivation at the hull** stays the open residue:
   `lset-formula` holds of `Lset` at the stage element — that is
   [LJ-1.642]'s residue with the formula half now supplied.
3. **No `src/` landing is implied by this GO.** The probe lands in the task
   home; promotion is a later, separate dispatch.

## 7. WORKING TREE

- `agents/tasks/LJ-1-651/Probe651.agda` — the probe, typechecks (4.96 s, final-0).
- `agents/tasks/LJ-1-651/lj-1.651-report.md` — this report.
- `agents/tasks/LJ-1-651/runs/` — all runs, including the one failed attempt
  (step1-0) and the failed floor arm (floor-0).
- No `src/` change. No file under `_build/` authored (the interface cache
  entries are Agda's own). No `.agda` file that does not typecheck exists
  under this task home. Not committed, not pushed.

## ARCHIVE USED

- **`archive/dev/LJ-dispatch-index.md`** — not read, declined: a dispatch
  index, no bearing on the grade or the term; the brief's premises and the
  three predecessor task homes are the operative history.
- **`archive/dev/JOURNAL-archived.md`** — read at `:631-632`: "machine-checked
  measurements: `LsetGraph` weighs 169,683 syntax nodes with 2,287 unbounded
  ∃̇ and 2,159 unbounded ∀̇ interleaved, so NO delivered transfer". This is the
  grade wall this task had to route around, and the count in section 4.
- **`archive/dev/JOURNAL.md`** — not read, declined: the live journal; the
  archived entry above is the cited measurement and the three predecessor
  reports are newer and task-specific.
- **`archive/dev/DECISIONS-archived.md`** — not read, declined: no decision in
  this task's path (the route choice is [LJ-1.646]'s, cited in the report
  proper).
- **`archive/dev/ORCHESTRATION.md`** — not read, declined: operating
  documentation, no bearing on the term or the grade.

## LITERATURE USED

- **`dev/literature/devlin-II5.md`** — read at `:95-96`: "By 2.7 there is a
  Σ₀ formula Φ(z, v, γ) of LST such that (a) ∀v∀γ [v = L_γ ↔ ∃z Φ(z, v, γ)]".
  This is the statement the probe builds: the tree's `levelHoodB` is the Σ₀
  matrix, `z` is the existentially closed `(K, u, w)`, and `v`, `γ` are the
  two slots.
- **`dev/literature/digest.md`** — not read, declined: the digest of the
  corpus; the specific entry `devlin-II5.md` carries the statement directly.
- **`dev/literature/truncation-and-selection.md`** — not read, declined: no
  bearing on the level-hood matrix or its grade.
- **`dev/literature/terms-2026-08.md`** — not read, declined: terminology
  tracking; the glossary is the canonical home for term questions and this
  task introduces no new term.
- **`dev/literature/geology.md`** — not read, declined: repository history;
  the three predecessor task homes are the operative history for this task.
