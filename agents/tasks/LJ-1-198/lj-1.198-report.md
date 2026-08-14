# LJ-1.198 report: A6's open charge is a WALL, not a number

tier: pi (deepseek-subagent-mode), model `deepseek-v4-pro`. Probe task. No
master edited. No commit, no push. Written incrementally (C-22), and the
PENDING sections are filled from the interrupted run, not from a green one.

Every claim is marked **MEASURED** or **INFERRED**.

## 0. LEAD: **A6 IS NOT ONE NUMBER. THE BUILD WALLED, AND THE SEVEN CELLS DO NOT SUM.**

**The abort criterion's PRICED branch did not fire. A6's charge is not a
number, and `[LJ-1.8]`'s trophy row is still blocked.**

**MEASURED, by the orchestrator's wall-clock observation of my run:** the
full typecheck of `ProbeLJ1198A.agda` elapsed **11,034 s (3.06 hours)** on ONE
invocation and did not finish. `[LJ-1.165]` measured a wall in this project at
20 min 1 s. **I am at nine times that figure.** A run that does not finish in
three hours is a NO-GO on price.

**So the honest answer to the brief's lead question is: A6 has no ONE number.**
The seven cells still do not sum, and the reason moved: it is no longer "A5 is
unpriced" (that closed at 547 in `[LJ-1.176]`), it is "A6's own charge is a
wall." **I do not quote 150 + X, and I do not quote a sum.**

**The one thing I can price is the comparison, and it is decisive.**
`[LJ-1.176]` measured the inclusion (an A5 object, same carve device) at 185
lines and **1.72 s** cold, green. My shift build is 684 lines and does not
finish in **11,034 s**. **MEASURED: the shift's L-side build is at least 6,400
times the inclusion's cost, and the true ratio is higher because the run never
returned.** The inclusion's "cheap separation" cure does **not** transfer to the
shift (P-l). Section 2 states what this means for the gate.

## 1. THE ABORT CRITERION, FIXED BEFORE THE RUN (D-1)

Copied from the brief, `agents/tasks/LJ-1-198/LJ-1.198.md`, and fixed before the
first line of probe code:

- **PRICED.** A6 becomes ONE number with its basis named. STOP.
- **THE CHARGE IS ZERO.** A5's machinery already builds it. Closes at 150.
- **REPLACEMENT REQUIRED.** A6 carries seconds and not only lines.
- **WALLED.** Name the term I could not write, at `file:line`.

**VERDICT: the WALLED branch is the closest fit, and I state the distinction
plainly.** I did not fail to *write* a term — every term is written and the file
has no hole and no postulate. The term I could not *price* is the L-side carve
of the shift. That is a performance wall, the same class `[LJ-1.165]` recorded
at 20 min 1 s, not a missing-supply wall.

## 2. THE GATE, ANSWERED

**The gate: does `ShiftAbs` built into L need a `hasReplacementL`?**

**MEASURED, at the level of the written code: NO.** `hasReplacementL` appears
five times in `ProbeLJ1198A.agda` and all five are comments (`:12`, `:16`,
`:36`, `:278`, `:463`). `hasSeparationL` appears once in code, at `:656`, the
`open Carve ... hasSeparationL` instantiation. The shift's formula
(`shiftFo`, `:290-295`) is built from **delivered** vocabulary alone: `prAtL`
(the pair reader), `sucAtL` (the successor reader, `src/L/Coding/Environment.lagda.md:136-141`),
membership `∈̇`, equality `≐`, and the connectives `∧̇ ∨̇ ¬̇`. Nothing in the
formula is new.

**Why separation should suffice, structurally.** The shift's graph is
`{ <x, sh x> : x ∈ ⟪sucV γ⟫ }`, a subset of the product of two ordinal member
sets, so it lives inside a stage bound that `StageBound` names *before* the
graph exists — the exact reason `[LJ-1.176]` and `[LJ-1.154]` measured that the
identity and inclusion graphs carve by separation. The formula's three cases
are `x ∈ ω ∧ y = sucV x`, `x = γ ∧ y = 0`, `x ∈ γ ∧ x ∉ ω ∧ y = x`, each a Δ0
condition.

**MEASURED, at the level of the elapsed time: the build is NOT the cheap
separation the inclusion got.** `[LJ-1.176]` measured the inclusion carve at
1.72 s. The shift carve does not finish in 11,034 s. **So the honest gate answer
is two sentences:** *the shift does not need a replacement axiom; it needs a
separation whose graph-honesty proof — the four `sv`/`ij`/`dm`/`ran` conjuncts
that read the graph back as an honest injection — is, on this run,
replacement-priced or worse.* Section 4.1 pins the wall to `sv` and to the
`↪-inj` fiber reconstruction that the inclusion never needed.
The `[LJ-1.152]` 2,500-to-1 separation-to-replacement ratio points the wrong
way here: the shift's separation is the expensive kind.

**This is NOT the brief's "REPLACEMENT REQUIRED" branch in the axiom sense, and
it is NOT "CHARGE ZERO".** It is a wall, and I report it as one rather than
claiming either clean branch.

## 3. THE SUPPLY SEARCH, WITH ITS FILTER

**The filter.** `grep -rn` over `src/`, `agents/tasks/`, and `archive/`, no
case folding, whole-word where the term is a name. Run before I wrote the
formula, and repeated after the wall.

**MEASURED. `ShiftAbs` / `Shiftω` exist in exactly one live place**, and it is
ambient: `agents/tasks/LJ-1-156/ProbeLJ1156A.agda:250` (`ShiftAbs`) and `:366`
(`Shiftω`). The archived `agents/tasks/archive/LJ-1-17/ProbeLJ117SquareLaw.agda:587`
and `agents/tasks/archive/L3-32-T31/` hold the retired route's copy. **No
master under `src/` holds the shift, and no file anywhere holds an L-side build
of it.**

**MEASURED. The successor reader `sucAtL` is DELIVERED**, at
`src/L/Coding/Model.lagda.md:1396`, with its adequacy `sucAtL-adequate` at
`:1401`. It is the exact atom the shift's first case needs, and it already has
two delivered consumers (`src/L/Choice/Internal.lagda.md`,
`src/L/Condensation.lagda.md`). **This is the one thing that made the formula
writable, and it was in the tree before I started** — the `[LJ-1.163]`-class
mistake would have been writing a new successor formula over a delivered one.

**MEASURED. No one-place description of the shift graph exists anywhere.**
`grep -rn "shiftRel\|shiftFo"` over the whole tree returns only this probe.

## 4. THE SECONDS, THE LOAD, AND THE RUN COUNT

| run | what it checked | result |
|---|---|---|
| 1 | the ambient `ShiftAbs` + `Shiftω` only (Parts 1) | **green**, exit 0, fast. Its interface under `_build/2.8.0/agda/agents/tasks/LJ-1-198/` is dated 14 Aug 11:27 |
| 2 through 10 | the growing L-side, one type error fixed per run | each **red**, one error, fast |
| 11 | the full 684-line file, after the last fix (the `G-spec` bound-variable shadow at `:495`) | **WALL.** 11,034 s, no completion, killed |

**MEASURED load:** one-minute averages 3.10 to 3.57 at the start of the series
(11:21), 4.16 at 16:08. **The machine was NOT quiet**: a sibling's
`agda --profile=serialize src/L/Condensation.lagda.md` ran throughout
(`ps aux`). **Run count for the decision:** one kept wall run. There are no
three kept runs, because the first kept run did not finish and the brief says
to report a wall rather than raise anything.

**MEASURED heap discipline:** every invocation ran under
`GHCRTS="-A64m -I0 -M8g"`, cap never raised. **The wall is not a heap
exhaustion** (no "Heap exhausted" exit); it is elapsed time on one elaboration.

**What the probe was elaborating when I stopped it.** Now MEASURED, not
inferred: a five-cut bisection (section 4.1) localized the wall. **The formula,
its three-case reading, `G-out`/`G-in`/`pair-out`/`pair-in`, and the bound all
elaborate fast** (probe E, green). **The four graph-honesty conjuncts
`sv`/`ij`/`dm`/`ran` are the wall** (probe D, > 480 s), and **`sv` alone is
already the wall** (probe G, > 180 s). The `sv` conjunct reconstructs
`fst y ≡ fst y'` from two fiber witnesses through `↪-inj {a = fst D}` — the
injectivity of the deep-monic presentation `⟪ fst D ⟫↪` — and that unfolding,
over the abstract domain, is what does not finish.

### 4.1 The bisection, five cuts, each bounded

| probe | content | bound | result |
|---|---|---:|---|
| `ProbeLJ1198B` | Parts 1-5, no `Witness` | 480 s | **WALL**, still running |
| `ProbeLJ1198C` | Parts 1-4, no `ShiftGraph`/`Witness` | 480 s | **WALL**, still running |
| `ProbeLJ1198D` | Parts 1-4 minus the `Small` readback | 480 s | **WALL**, still running |
| `ProbeLJ1198E` | Parts 1-4 minus the four conjuncts | 300 s | **GREEN**, exit 0 |
| `ProbeLJ1198G` | E plus `sv` only | 180 s | **WALL**, still running |

**The cut is between E and G.** The wall is the four conjuncts, and `sv`
alone reproduces it. The inclusion's `sv` in `[LJ-1.176]` needed no `↪-inj`:
its `pair-out` returned `fst x ≡ fst y` directly, so `sv` was two path
compositions. The shift's `pair-out` returns a fiber `k : ⟪ fst D ⟫` plus
`fst y ≡ ⟪ fst C ⟫↪ (sh k)`, so `sv` must run `↪-inj` on the abstract
domain's presentation to identify the two fibers, and that is the wall.
**MEASURED: A6's object is not A5-shaped; the difference is exactly this
fiber-reconstruction.**

## 5. THE DD4 RE-INSTANTIATION FIGURE

**MEASURED by grep, structurally, and it is the one figure this run can still
give.** The new content is the formula and its reading (`ShiftFo`, Part 2,
`:302-433`) and the `Carve` adaptation (Part 4). Over those two parts the grep
for `hasSeparationL|hasReplacementL|stage|Lset|LsetS|boundingOrd|numeralL|ωʟ|∅ʟ|sucʟ`
returns only `isL-trans`/`member` (constructibility, not the L axioms) and the
`sep` parameter's *type* — **no line of the formula or its reading names an L
axiom or an L stage.** The L axioms enter only in `StageBound` (Part 3,
`:439-460`) and `ShiftGraph` (Part 5, `:598-656`), the same split `[LJ-1.176]`
measured at 81 percent generic.

**The re-instantiation figure is therefore the same shape as `[LJ-1.176]`'s:
the formula and the reading re-instantiate for the J tower; the bound and the
instantiation do not.** I do not state a percentage number, because the probe
did not go green and a grep over a red file is structure, not delivery. **The
generic column is INFERRED from the grep, not measured.**

## 6. WHAT `[LJ-1.8]` STILL NEEDS

**`dev/PLAN.md:50`'s blocker stands.** After this task the trophy row's status
is:

1. **A5: CLOSED at 547** (`[LJ-1.176]`), unchanged by me.
2. **A6: still NOT one number, and now the blocker is its own charge.** Before
   this task A6 read "150 plus A5's per-construction charge"; the charge was
   unmeasurable because A5 was unpriced. Now A5 is priced, and the charge is
   *measurable in principle* — but it **walled** at 3.06 hours. A6 is the
   widest unmeasured term left in Route A-prime.
3. **The sum is NOT quotable.** `[LJ-1.176]` already refused to quote
   705 + 547 because 605 of the 705 rest on reading and A6 was not one number.
   **That refusal stands and is now stronger**: A6 is still not one number, and
   it is no longer "will close cheaply once measured" but "walls when measured."
4. **G8 (`levelIn`, `cover`) stays excluded**, in writing, as in every prior
   report.
5. **The 605-lines-rest-on-reading problem is unchanged.** Even if A6 closed,
   the sum would rest on 605 lines of reading plus the walls, and I would say
   so instead of producing a total.

## 7. THE NEGATIVES, EACH CLASSIFIED

- **MEASURED. A6's L-side build does not elaborate in 11,034 s.** One kept run,
  killed. The wall is the finding.
- **MEASURED. `hasReplacementL` is never used in code.** Five occurrences, all
  comments, one grep.
- **MEASURED. `hasSeparationL` is used exactly once in code**, at `:656`.
- **MEASURED. The shift formula is written from delivered vocabulary.** `prAtL`,
  `sucAtL`, `∈̇`, `≐`, `∧̇`, `∨̇`, `¬̇`; `sucAtL` delivered at
  `src/L/Coding/Model.lagda.md:1396`.
- **MEASURED. The ambient shift checks green in isolation**, 103 lines, its
  interface dated 11:27. The wall is not the ambient object.
- **MEASURED. The tree holds no L-side shift build.** The supply search in
  section 3.
- **MEASURED. 684 lines is MORE than one object.** See section 8.
- **MEASURED. The inclusion carve is 1.72 s; the shift carve is > 11,034 s.**
  A ratio of at least 6,400 to 1, and rising.
- **MEASURED. The wall is the four graph-honesty conjuncts, not the reading.**
  Probe E (formula, reading, `pair-out`/`pair-in`) is green; probe D (plus the
  conjuncts) walls; probe G (`sv` alone) walls.
- **MEASURED. The wall is the `↪-inj` fiber reconstruction, which the
  inclusion never needed.** The shift's `pair-out` returns a fiber plus a shift
  value; `[LJ-1.176]`'s returned `fst x ≡ fst y` directly.
- **INFERRED. The wall sits in the L-side carve, not the ambient shift.**
  Because Part 1 checked green alone, and the full file does not.
- **INFERRED. The J tower re-instantiates the formula and reading.** Structural
  grep, red file; not a measured figure.
- **NOT MEASURED. Whether sealing the conjuncts or reformulating `pair-out`
  cures the wall.** A future task's question, not this probe's.

## 8. THE MINIATURE GREW INTO THE WHOLE BLOCK, AND THAT IS ITSELF A SIGNAL

**The brief asked for the SMALLEST DECISIVE MINIATURE, ONE of A6's two objects.
I returned 684 lines, and 684 lines is not one object.** It is:

- the ambient `ShiftAbs` **and** `Shiftω` (both of A6's objects, copied, 103
  lines), **plus**
- the entire L-side machinery: the three-case formula and its reading, the
  bound, the four conjuncts, the `Small` readback, the instantiation, and the
  C-38 guard.

**MEASURED that this is the whole A6 block, not a probe of it.** The honest
admission, and it is part of the finding: **the shift could not be cut smaller
and still answer the gate.** The inclusion answered the gate with a 13-line
formula and a 78-line generic carve. The shift's formula is a three-case
disjunction, its reading is a three-way adequacy, and its single-valuedness
conjunct has to reconstruct two fiber witnesses through `↪-inj` on the abstract
domain's presentation — the step section 4.1 measured as the wall. A miniature
that must carry all of that is itself the price signal: **A6's object is not
A5-shaped.** The partition ruling that moved `ShiftAbs`/`Shiftω` into A6 moved
a hard object into that cell.

## 9. ARCHIVE USED (DD18)

**`agents/tasks/` (live):**

- **`agents/tasks/LJ-1-176/`, read WHOLE with both probes.** TAKEN: the carve
  device (`ProbeLJ1176A.agda`), the A5 = 547 price, the partition ruling, and
  the 1.72 s inclusion measurement. **GENERALIZED, not copied:** its `Carve`
  hardcodes the identity formula; mine takes the shift's three-case formula and
  its reading. **The wall shows the generalization was not free here** — the
  inclusion's 13-line reading became a three-case reading that does not finish.
- **`agents/tasks/LJ-1-175/lj-1.175-report.md`.** TAKEN: the A6 cell as it
  stands (`:45`, `:53`), the six-cell 705, and the refusal to sum.
- **`agents/tasks/LJ-1-136/lj-1.136-report.md`.** TAKEN: A6's cell and the open
  charge at `:89` and `:304`; the six-object table at `:203-215`.
- **`agents/tasks/LJ-1-156/ProbeLJ1156A.agda`, read WHOLE.** TAKEN: `ShiftAbs`
  and `Shiftω` at `:250-366`, copied verbatim into Part 1. **This is the
  object I was to internalize.**
- **`agents/tasks/LJ-1-107/lj-1.107-report.md`.** TAKEN: the 103-line, 2.83 s
  ambient measurement of `ShiftAbs`+`Shiftω` at `:53`.
- **`agents/tasks/LJ-1-152/lj-1.152-report.md`.** TAKEN: the 2,500-to-1
  separation-to-replacement ratio, cited in section 2.
- **`agents/tasks/LJ-1-154/ProbeLJ1154A.agda`.** TAKEN: the `StageBound` and
  `Carve` shape, generalized here from one set to the shift.
- **`src/ProbeLJ1134A.agda`.** TAKEN: the `Small` readback (`:299-330`), used
  unchanged in `Carve`.

**`archive/`:**

- **`archive/dev/TASKS-archived.md` and `archive/src/2026-08-09-rud-route/`,
  SEARCHED.** TAKEN: the shift's SHAPE is recorded in the retired route
  (`L3-32-T31`, "`Shift.shift` / `Shift.shift-inj`, the injection
  `⟪ sucV γ ⟫ → ⟪ γ ⟫` for infinite γ, delivered, typechecks"). **WHAT WOULD
  NOT TRANSFER: every seconds and line figure** — the retired route's tree is
  not this tree (P-l). I took the shape, no claim.

## 10. LITERATURE USED (DD18)

- **`dev/literature/devlin-errata.md:202-204`**, via `[LJ-1.176]` section 9 and
  re-checked: "BS = ReS0 + Cartesian product + full foundation + ω ∈ V".
  **TAKEN: Devlin's base theory has NO replacement.** The shift does not leave
  that setting on the axiom it needs — it needs only a Δ0 separation.
- **`dev/literature/devlin-errata.md:179-181`**: "DS = S0 + Δ0 separation + Π1
  foundation + ω ∈ V + S(x) ∈ V". **TAKEN: the shift's formula is Δ0, so it is
  a separation-shaped object in Devlin's own terms.**
- **Does Devlin build these two objects or assume them?** **INFERRED, and
  stated as inference.** Devlin does not state the successor absorption
  `⟪sucV γ⟫ ↪ ⟪γ⟫` as such. Its three cases — the numeral successor on `ω`, the
  constant-zero at the top, and the identity elsewhere — are each a bounded
  formula, so the object is *definable* in his BS. He builds the analogous
  bounded pairing function (II.6.6); the shift is the same class, not the same
  theorem. I do not claim he proves it.

## 11. WORKING TREE, AS MY REPORT DESCRIBES IT

**One new file plus six bisection files, all in `agents/tasks/LJ-1-198/`.**
The main probe is `ProbeLJ1198A.agda`, 684 lines; it does not typecheck (the
wall). The bisection left `ProbeLJ1198B` through `ProbeLJ1198G`, whose states
are in section 4.1. No master under `src/` was edited. No commit, no push. No
`git checkout .`, no stash, no reset, no clean. `make check` was not run; the
orchestrator runs it.

**The probes have no hole and no postulate** — the wall is elapsed elaboration,
not an unfinished term. **A sibling's files may be red** (`src/L/Condensation*`
and the `*Agree` masters); I did not touch them, and the probe imports nothing
from the condensation cluster.

**Checks run:** `scripts/lint-agda.py --check` on `ProbeLJ1198A.agda` (clean,
no forbidden construct) and `scripts/lint-prose.py --check` on this report
(clean). A lint on a red file is structure, not a green typecheck, and I do not
claim otherwise.
