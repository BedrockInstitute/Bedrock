# Process tensions and their resolutions (archived from dev/PLAN.md section 8)

> **STATUS: SUPERSEDED.** **D11's mechanisms are in archive/dev/DECISIONS-archived.md, NOT in dev/PLAN.md section 3.** The whole D series was archived on 2026-08-09, and section 3 now holds the DD series. **DD11 is a DIFFERENT rule, code and prose craft: the D and DD numbers do not correspond.** The live relief valves are the L0 standing track (the L0 row of dev/PLAN.md section 11), the fixed part level (archived D5, stated live in dev/PLAN.md section 4), and the L4.1 harmonization (dev/PLAN.md section 11). Read this memo when the design reasoning behind a plan mechanism is needed. Moved out of dev/PLAN.md by [L3.32-T113].

---

## 8. Process tensions and their resolutions (D11)

Known internal tensions in the L0 to L5 plan, each with its designed relief
valve. The common principle: **the plan legislates the mechanism of change,
not the impossibility of change.**

- **T1: Legislation is partly hindsight.** Some style rules can only be
  discovered by porting. Relief: L0 is a standing track; STYLE-agda rules may
  be marked *provisional*; a porter hitting an un-legislated situation opens a
  new L0.x item (or asks the owner) rather than improvising silently.
- **T2: Skeleton finality versus post-reduction insight.** Relief: only the
  part level of §4 is fixed; everything below is provisional until the
  dedicated L3.10 re-layering review; renames land as appended ledger rows.
- **T3: Pedagogical order versus dependency order.** Relief: the Frontier
  mechanism (§5) decouples them; a branch was portable the moment its cut was
  stated.
- **T4: Early prose versus whole-book coherence.** Relief: per-merge prose must
  be complete and correct, but foreshadowing and cross-references may be
  deferred; the L4.1 harmonization pass sweeps the whole book.
- **T5: L3 reduction versus already-narrated interfaces.** Relief: every L3
  memo carries an impact list on ported chapters; Frontier re-cuts (§5) are
  the sanctioned mechanism; prose residue is caught by L4.1.
- **T6: Performance scaffolding versus readability.** Relief: countermeasures
  stay in the code, annotated per L0.0 so narration can skip them; §7 budgets
  decide when a countermeasure is load-bearing (measure, do not guess).
