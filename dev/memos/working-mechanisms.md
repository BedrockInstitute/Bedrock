# Working mechanisms (archived from dev/PLAN.md section 5)

> **STATUS: SUPERSEDED.** The live residue of this section moved to its enforcers: the LEM parameterization convention is dev/STYLE-agda.md section 1 (**the live ruling is DD9 in dev/PLAN.md section 3; the archived D2 is in archive/dev/DECISIONS-archived.md, and DD2 in section 3 is a DIFFERENT rule**); the two-catalog doctrine and the named-hypothesis debt form are dev/STYLE-agda.md; probes and gates are AGENTS.md and dev/LESSONS.md D-1; orchestration is dev/ORCHESTRATION.md. What remains here is the port-era mechanism history (the Frontier record, its re-cuts, construction order). Read it only when the L1-L2 port's mechanism is in question. **The record of the Frontier's deletion is the struck D8 row in archive/dev/JOURNAL-archived.md, and rows L2.4 and L4.0 of archive/dev/STATUS-archived.md.** dev/JOURNAL.md carries no D8 text, and dev/PLAN.md section 11 carries an L4.0 row but no L2.4 row.

---

## 5. Working mechanisms (D2, D8)

**The Frontier record.** Root-first construction without postulates: `L.Frontier`
held one record whose fields were the *statements* of the not-yet-ported lemmas,
and the root theorem was proven from it. The record was the cut across the
dependency tree: each ported branch deleted its fields, the field list was the
live progress board, and `make check` stayed green at every commit. **The
Frontier is empty and deleted since `[L2.4]` (2026-07-31)**: `L.Model` takes
only `(lem : LEM (ℓ-suc ℓ))` and `L⊨ZFC` is unconditional in substance.

**Frontier re-cuts were normal (D11).** A field was not a contract with the
source's interface: when an L3 reduction changed the natural statement of a
lemma, the field was replaced (a *re-cut*), provided the root still typechecked
and `make check` stayed green. Re-cuts were recorded in the §11 field count.

**LEM as a parameter.** `Base.Classical` states the interface and derives its
consequences; the packaging validated by the L0.2 spike is
`LEM : ∀ ℓ → Type (ℓ-suc ℓ)` with classical-cone modules taking
`(lem : ∀ {ℓ} → LEM ℓ)` in their telescopes (STYLE-agda §1). The entire tree,
`Everything` included, is `--safe`.

**Reading order versus structure order** (owner ruling, 2026-07-18): the book
keeps two catalogs. The **reading catalog** is `Everything.lagda.md`, the
landing page: import order = reading order, hand-maintained. The **structure
catalog** is the namespace tree, derived automatically and never
hand-maintained. Namespace membership is decided by subject, reading position
by first consumption; the two are independent.

**Construction order versus reading order.** These are deliberately different.
The build proceeds root-first (the Frontier shrank over time); the book reads
foundations-first (`Base → FOL → ZF → V → L → Landmarks`, fixed by the
`Everything` import order). Neither order constrains the other.

**The named hypothesis, and its limit** (standing since `[L3.31]`). When a
chapter cannot discharge an obligation, the obligation is stated as a named
module hypothesis and the chapter ships conditional on it, with the hypothesis
recorded in §11. This kept the tree green through a long campaign. Its limit
was learned expensively: **a named hypothesis has no defence when the
hypothesis is false**, so the truth of a residue's target is now priced before
its proof, at the chain's ROOT, against the in-repo corpus (LESSONS D-10, and
the risk row in §9).

**Probes and gates** (standing since `[L3.30]`, sharpened 2026-08-04). Before
heavy or hard-to-reverse work, the load-bearing assumption is verified cheaply:
a D-1 probe builds the smallest decisive miniature, reports GO or NO-GO with a
price extrapolation, and is KEPT: since the owner's ruling of 2026-08-13 the
probe file lives in `agents/reports/<TASK>/`, beside the report, tracked, and
is never deleted. `dev/LESSONS.md` D-1 is the canonical rule. A probe prices
only OUR departures
(what the Cubical HIT setting costs us), never feasibility the literature or
the delivered tree already settles. Since 2026-08-04 every wide unprobed
component is expected to name its gate at estimate time (§6.2), and a stop
report is a full deliverable: the two most valuable results of this campaign
were a refutation and a stop.

**Orchestration.** Batches are written by delegated agents against pinned
briefs, archived in `agents/briefs/`; the orchestrator audits every return
(report, then code, then an independent typecheck and the linters), wires
`Everything.lagda.md` (agents never touch it), and commits with the goal code.
Agents never commit and never push. Concurrency and heap caps are governed by
LESSONS C-12.
