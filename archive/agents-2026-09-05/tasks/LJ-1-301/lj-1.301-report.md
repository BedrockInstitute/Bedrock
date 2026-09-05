# LJ-1.301 report: build `sq` by descent from `squareω`

tier: pi (pi-subagent-mode), model `glm-5.3`. A PROBE: nothing lands,
all work in `agents/tasks/LJ-1-301/`. Written incrementally (C-22). Every
negative is MEASURED or INFERRED, in those words. ASD-STE100 applies.

## 0. LEAD

**BUILDS.**

```
sq-descent : (α : V ℓ) → IsOrd α → (⟨ α ∈ˢ ω ⟩ → Empty.⊥)
           → ⟨ isL α ⟩ → ∥ sq α ∥₁
```

at `agents/tasks/LJ-1-301/Descent.agda:261-263`, **exit 0, `--safe`,
241.9 s cold at load 4.38 rising to 6.41** (own `.agdai` deleted,
dependencies warm: the project caliber). The file is 271 lines, 186
non-blank. **The recursion principle is `WF.WFI.induction regularityV`,
the same one `L.Ordinal.Linear` uses at `src/L/Ordinal/Linear.lagda.md:137`,
and it is well founded because `regularityV : WellFounded _∈ᵗ_`
(`src/V/Hierarchy.lagda.md:139`) is the ambient hierarchy's regularity,
so membership is well founded on ALL of V and the induction hypothesis
is available at every member.** Every recursive call in the step is at a
member of α.

**ONE word of care: the conclusion is TRUNCATED.** The descent delivers
the law at each ordinal as a proposition, not the untruncated function
object `SqShape`. Section 4 says why, and what the untruncated form
still owes. **`[LJ-1.8]`'s route is open under that one qualification.**

## 1. MACHINE AND PROCESS DISCIPLINE

ONE agda process at a time, `GHCRTS="-A64m -I0 -M8g"` on every run, cap
never raised. **MEASURED FALSE: a wall.** The wall criterion is 30
minutes; the longest invocation was 252 s. **MEASURED FALSE: a heap
exhaustion.** No kill, no interrupt. The machine was NOT quiet: a
sibling task held an Agda slot throughout, and the 1-minute load moved
between 4.38 and 6.41 during the kept runs. Every absolute figure
carries its load.

| run | exit | elapsed s | 1-min load |
|---|---:|---:|---:|
| first run, parse error (`_∈_` unimported) | 1 | 3.5 | 4.57 |
| shadowed-`e` error, rejected | 1 | 252.2 | 4.5 |
| subst-direction error, rejected | 1 | 246.9 | 4.5 |
| `⟨Wat⟩`-bracket error, rejected | 1 | 241.1 | 4.5 |
| unsolved metas on `mem-ord`, rejected | 1 | 247.4 | 4.5 |
| first full green | 0 | 240.1 | 4.4 |
| cold caliber, own `.agdai` deleted | **0** | **241.9** | 4.38→6.41 |

## 2. THE TERM AND ITS FOUR BRANCHES

The motive gates the law on three things only: ordinal, outside ω, in L
(`Descent.agda:139`). **NO cardinality gate.** `Init`'s fourth row
consumes the law at EVERY infinite member, and a cardinality gate on
the motive would starve it (section 5).

The step (`Descent.agda:144-258`) runs one trichotomy against ω and, in
the `ω ∈ˢ α` case, two more classical decisions. Four branches:

1. **BASE, `α ≡ ω`** (`:149`). `squareω` (`src/L/InjChain.lagda.md:184-185`),
   transported along the path.
2. **SUCCESSOR, `α = sucV γ`** (`:198-258`). A classical decision on
   "some member's successor escapes α" extracts γ with
   `sucV γ ≡ α` (the other two trichotomy cases die to `∈-irrefl`).
   Then `sq-succ` (`:94-116`): `absorbs`
   (`src/L/Absorption.lagda.md:613-618`) maps `⟪ sucV γ ⟫` into
   `⟪ γ ⟫`, the induction hypothesis pairs, and the ordinal embedding
   `ord-mem-emb` (`:80-93`, the shape of
   `L.BoundedSubset.Devlin55.ord-emb` at
   `src/L/BoundedSubset.lagda.md:1370-1378`) includes `⟪ γ ⟫` back.
3. **NON-INITIAL, some member absorbs α's index** (`:163-175`). A
   classical decision on `∥Σ δ ∈ˢ α. ⟪α⟫ ↪ ⟪δ⟫∥₁`. The positive side
   carries an injection into a member; `sq-transport` (`:118-135`)
   pairs through δ's law and includes δ back. **A finite δ is
   refuted** by `FiniteBase.finite-excl` (`:169-172`): a finite member
   cannot absorb an infinite ordinal's index.
4. **INITIAL** (`:176-197`). The negative side IS `IsCardinal α`
   (`:159-161`): ambient initiality, DERIVED classically, with no
   cardinal face named at any statement. A second decision on
   successor closure splits once more:
   - **limit**: `via-col-square α (oα , ω∈α , lim , noinj)`
     (`:183`), the fourth row built from the induction hypothesis
     (`:187-196`) exactly as `[LJ-1.300]`'s `descent-step` built it,
     with `SqBelow` now supplied by the recursion itself;
   - **successor**: branch 2.

**Nothing in the step mentions `sq α` except through the delivered
`via-col-square`.** The dependency descends; `[LJ-1.299]`'s CIRCULAR
verdict stays refuted.

## 3. EVERY PREMISE, VERIFIED OR REFUTED

1. **"The circle is NOT real, MEASURED by `[LJ-1.300]`. `Init`'s fourth
   row at `src/L/Ordinal/SquareLaw.lagda.md:696-698` quantifies over
   `β ∈ˢ α`, strictly below α. Its probe builds `sq α` from the square
   law at MEMBERS only."** **VERIFIED.** `Init`'s fourth conjunct at
   `:696-698` quantifies `β` under `⟨ β ∈ˢ α ⟩`; `descent-step`
   (`agents/tasks/LJ-1-300/StepProbe.agda:45-63`) consumes only
   `SqBelow α`. My step's fourth row (`Descent.agda:187-196`) is that
   term with the recursion supplying `SqBelow`.
2. **"The base exists and bypasses `Init` entirely. `squareω : sq ω` at
   `src/L/InjChain.lagda.md:184-185`, with `noinj²ω` VACUOUS at
   `:123-126`."** **VERIFIED.** `squareω` at `:184-185`;
   `noinj²ω` at `:123-126` reduces to `ω∉β` (`:113`), vacuous because
   no member of ω contains ω.
3. **"`SqShape` now states the real square law. I fixed a parenthesis
   defect at `src/L/GCH.lagda.md:47` two hours ago."** **VERIFIED.**
   The current file reads
   `(⟪ fst α ⟫ × ⟪ fst α ⟫) ↪ ⟪ fst α ⟫` at `:47`. `[LJ-1.300]` test 4
   proved the parenthesized body IS `L.Ordinal.SquareLaw.sq` by `refl`,
   and my `sq-shape∥` (`Descent.agda:269-271`) states the use-site
   shape through `sq` directly.
4. **"`κ-limit` is PROVED, `[LJ-1.294]`, so `Init`'s row 3 is available
   at the use site. Row 4 is what the descent must produce."**
   **VERIFIED as a statement of the record, with one finding attached:
   the descent does not NEED row 3 delivered.** The step decides
   successor closure classically (`:177-179`) and derives the limit
   case from the negative side of the successor decision
   (`:250-258`), so `κ-limit` is not on the descent's critical path.
   The successor branch inside the initial case is mathematically
   vacuous, INFERRED: an initial ordinal is never a successor. The
   proof cannot see that without cardinal arithmetic, so the branch
   stays, and it costs nothing. `κ-limit` remains delivered and
   available for the direct route (section 6).

## 4. WHY TRUNCATED, AND WHAT THE UNTRUNCATED FORM OWES

**Two of the four branches consume classical existence whose payload
is DATA: the successor branch needs the path `sucV γ ≡ α`, and the
non-initial branch needs the injection `⟪α⟫ ↪ ⟪δ⟫`.** The induction
hypothesis is likewise consumed only under propositional motives. A
truncated existence eliminates only into a proposition, so the
conclusion is stated as `∥ sq α ∥₁`.

- **The untruncated descent walls at ONE branch, MEASURED by
  construction: the non-initial one.**
  The injection from α to a member is the branch's engine, and it
  arrives only truncated. **This wall is RECORDED, not new:**
  `[LJ-1.299]` found it first at the least-cardinal route
  (`agents/tasks/LJ-1-299/lj-1.299-report.md:209-218`, "`LeastCardInjL.κ-inj`
  is TRUNCATED ... while `SqAll` is not ... Either `SqShape` is restated
  truncated or the least-cardinal chapter exports an untruncated
  witness"), and the tree records it at its own construction: `κ-inj : ∥ ⟪ fst α ⟫
  ↪ ⟪ fst κ ⟫ ∥₁` with the comment "The witness, an injection, still
  truncated, still not an hProp" (`src/L/Cardinal.lagda.md:132-133`).
  My descent hits the SAME wall at its own non-initial branch, which
  CONFIRMS the residue at a second site. The two owner options
  `[LJ-1.299]` framed stand: restate truncated, or export the
  least-cardinal injection untruncated (the `LeastCardInj` debt the
  route already prices, `[LJ-1.156]` at `dev/PLAN.md:974`).
- **The successor branch's data is recoverable without truncation**,
  INFERRED, not built here: decide `sucV (⋃ α) ≡ α` instead of the
  member-witness, and the `inl` side carries the path as data. That
  would cost a `⋃ (sucV γ) ≡ γ` lemma of about ten lines.
- **What the truncated form already buys at the use site.** The GCH
  conclusion is itself truncated
  (`∥ Σ[ δ ∈ S ] ... ∥₁`, `src/L/GCH.lagda.md:85-87`), so a proof of
  `[LJ-1.8]` whose body consumes the law under a propositional motive
  can be wrapped in ONE `PT.rec` over `∥ sq κ ∥₁` per use. Whether the
  trophy statement may be restated to consume the truncated law is the
  OWNER's ruling, not mine.

## 5. THE INDUCTION HYPOTHESIS, AND THE FINITE MEMBERS

The brief's abort criterion asked whether the induction gives the wrong
shape: `Init` needs the law at infinite members, the induction gives it
at ALL smaller ordinals. **The shape is RIGHT, and the finite members
are NOT a gap.** Row 4 quantifies only over β with `⟨ ω ∈ˢ β ⟩`, so the
hypothesis is never invoked at a finite member; the infinite gate is
discharged from `ω ∈ˢ β` itself, by `ω∉β` (`Descent.agda:195`). The
vacuity of `noinj²ω` is not needed and not used.

**The REAL shape constraint runs the other way, MEASURED by the gate
analysis in section 2: the motive must NOT be gated on cardinality.**
Row 4 at a limit cardinal α needs the law at every infinite member,
including successors and non-cardinals (`ω + 1` is a member of `ω₁`),
so a motive gated on `IsCardinal` starves its own step. The step
handles the non-cardinal and successor members by branches 2 and 3, and
that is why the four branches are not optional.

## 6. IS `Init κ` CONSTRUCTIBLE AT THE USE SITE NOW?

**By the direct route: NO, MEASURED.** `GCHStatement zf sq κ cardκ nfin`
(`src/L/GCH.lagda.md:79-87`) supplies `IsCardinalL κ`, the coded face.
Row 4 at κ needs ambient `IsCardinal κ`, and the only delivered bridge
runs ambient to coded (`amb→code`,
`agents/tasks/LJ-1-299/NoInj2.agda:103-111`); the reverse is the
ambient-to-code wall `[LJ-1.300]` section 4 re-labelled INDEPENDENT.
**What is missing is the ambient face at κ, and naming it is the
OWNER's cardinal-face ruling.**

**By the descent: the question does not arise.** `sq-descent` needs no
cardinality hypothesis at all. Its initial branch DERIVES ambient
initiality from the classical negative side (`Descent.agda:159-161`),
and its base handles κ = ω without `Init`. So `[LJ-1.8]` can consume
the law without ever constructing `Init κ`.

## 7. DD4, AND MY AXIS (C-46)

**MY AXIS IS AC-AGAINST-GCH, DD4'S OWN.** The descent names no tower
and no stage presentation: it quantifies over ordinals, members and
injections, and every ingredient (`sq`, `absorbs`, `via-col-square`,
`regularityV`) is tower-blind. Under P-k it belongs to the GCH closure:
`src/L/Ordinal/SquareLaw.lagda.md` is already in it through
`src/L/Cardinal.lagda.md:22` (`[LJ-1.300]` section 7 MEASURED this),
and the landing adds no AC-side import, so the SHARED row is the one to
read, not the share percentage. The two proofs share the descent
wholesale: AC's counting never touches ordinal pairing, and this term
is exactly the pairing.

**Genericity debts for the landing, both small:** `ord-mem-emb`
duplicates `L.BoundedSubset.Devlin55.ord-emb`
(`src/L/BoundedSubset.lagda.md:1370-1378`) and should land as a reuse
of it; the successor/limit decision is stated once and consumed once.

## 8. TIMING AND SIZE (DD24, DD8)

`Descent.agda`: 271 lines, 186 non-blank, 241.9 s cold at load
4.38→6.41. **One best-effort landing price, basis: this probe.** The
probe carries about 55 comment lines and the `ord-mem-emb` duplicate
(14 lines); the landing into the GCH closure costs **about 130
non-blank lines** plus two import widenings (`L.Absorption` for
`absorbs`, already imported by `L.GCH` at `src/L/GCH.lagda.md:17`;
`V.Model` for the `sucV` eliminator). The file typechecks under
`--safe` with `--guardedness`, the project's OPTIONS header.

## 9. THE ABORT CRITERION, FIXED BEFORE THE RUN (D-1)

- **THE DESCENT BUILDS. FIRES.** Section 0. The term, its lines and its
  cold seconds are reported, with the truncation qualification of
  section 4.
- **THE INDUCTION HYPOTHESIS IS THE WRONG SHAPE. Does not fire.**
  Section 5.
- **AMBIENT INITIALITY IS NOT AVAILABLE AT THE USE SITE. Fires for the
  DIRECT route only, and the descent dissolves it.** Section 6.
- **IT IS CIRCULAR AFTER ALL. Does not fire.** Section 3, premise 1.
- **A WALL. Does not fire.** Section 1.

## 10. WHAT I DID NOT DO

- **No master was touched.** Not `src/L/GCH.lagda.md`, not
  `src/Everything.lagda.md`, not any file under `src/`. My writes are
  confined to `agents/tasks/LJ-1-301/`.
- **The sibling `agents/tasks/LJ-1-302/` was not touched** and not
  read.
- **`make check` not run**, as the brief orders. The two named linters
  were run on my files; section 12.
- **No `dev/` figure was edited**, not `dev/ledger.toml`, not
  `dev/PLAN.md`.
- **The untruncated successor branch was priced, not built**
  (section 4), and no countermodel was built.

## 11. ARCHIVE USED (DD18)

- **`agents/tasks/LJ-1-300/lj-1.300-report.md`, read WHOLE, FIRST, as
  the brief ordered.** Line read `:143`, "So the descent has a
  delivered base and it terminates." **TAKEN: the target this task
  builds, and the base-plus-step decomposition my step follows.**
- **`agents/tasks/LJ-1-300/StepProbe.agda`, read whole.** Line read
  `:45`, `descent-step : ... → SqBelow α → sq α`. TAKEN: the one-step
  term, which my fourth row reproduces with the recursion supplying
  `SqBelow`.
- **`agents/tasks/LJ-1-299/lj-1.299-report.md`, read for the CIRCULAR
  verdict and the truncation residue.** Line read `:209-218`, the
  paragraph that finds `κ-inj` truncated against untruncated `SqAll`
  and frames the two owner options. TAKEN: the wall my section 4
  confirms at a second site, and the corrected descent plan
  (`:202-205`) whose shape this probe builds. Its CIRCULAR lead
  (`:9`) stays overturned.
- **`agents/tasks/LJ-1-294/lj-1.294-report.md`.** Line read `:12`, the
  `κ-limit` statement. TAKEN: the row-3 supply my section 3 finds
  unnecessary for the descent. Its `ω∈κ-after-split` analysis
  (`:130-147`) survives untouched.
- **`agents/tasks/LJ-1-279/lj-1.279-report.md`.** Line read `:101`,
  "`squareω : sq ω`. The three hypotheses (`ω-limit`, `noinj²ω`,".
  TAKEN: why the base bypasses `Init`.
- **`archive/dev/TASKS-archived.md`, read for SHAPE and never a
  claim.** Line read `:140`, `| L3.32-T105 | Adversarial review:
  context layering | REFUTED (diagnosis) |`. TAKEN, SHAPE ONLY: one
  index row per dispatch, verdict in the row, detail in the report.

## 12. LITERATURE USED (DD18)

- **`dev/literature/devlin-II5.md`.** `[LJ-1.300]` MEASURED that Devlin
  II.5 never states a square law (its `:281-282` records the
  cardinal facts 5.5 actually consumes). **The descent's shape comes
  from the tree, not the literature, and that does not matter:** the
  law `|β × β| = |β|` is chapter-I cardinal arithmetic the digest
  inherits and never restates, and the descent's four-branch shape
  (base, successor, non-initial transport, initial limit) is exactly
  the standard induction every textbook runs without naming. What the
  tree adds is the FACE discipline: ambient injections, not bijections
  (`[LJ-1.300]` section 8), and truncated classical existence.
- **WHY NOT the rest of the digest:** sections 3, 4, 6 and 7 are the
  engine list, the crossing map, the errata and the Jech cross-check;
  none touches ordinal cardinal arithmetic.

## 13. CHECKS RUN

- `.venv/bin/python scripts/gate/lint-prose.py --check`: exit 0.
- `.venv/bin/python scripts/gate/lint-agda.py --check`: exit 0.
- **MEASURED: no em dash in any file I wrote** (grep).

## 14. FOR THE ORCHESTRATOR

1. **The descent is built and green: 186 non-blank lines, 241.9 s cold,
   landing priced at about 130 plus two import widenings (section 8).**
2. **The truncation is the one open ruling:** `∥ sq α ∥₁` per ordinal,
   not the `SqShape` function object. The untruncated form owes the
   least-cardinal injection AS DATA, the same wall
   `src/L/Cardinal.lagda.md:132-133` records. Either `[LJ-1.8]`'s
   proof wraps its uses in `PT.rec` over the truncated law (a statement
   change, the OWNER's), or `LeastCardInj`'s data form is priced next.
3. **`κ-limit` is off the descent's critical path** (section 3,
   premise 4). Its next consumer, if any, is the direct `Init κ` route,
   which the descent makes unnecessary.
4. **The direct `Init κ` route still lacks ambient initiality at the
   use site** (section 6): the cardinal-face ruling stands exactly
   where `[LJ-1.300]` left it.
