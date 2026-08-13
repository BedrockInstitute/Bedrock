# Risks and mitigations (archived from dev/PLAN.md section 9)

> **STATUS: SUPERSEDED.** Each mitigation is a standing rule with its own home. **The live homes are DD1 and DD5 in dev/PLAN.md section 3**, dev/LESSONS.md D-1/D-6/D-10, dev/PLAN.md section 6.0, and the return checklist in dev/ORCHESTRATION.md section 6. **The D1 and D26 this header used to name are archived**, in archive/dev/DECISIONS-archived.md. They still resolve, but section 3 no longer holds them, and the D and DD numbers do not correspond. Read this memo when the dated reasoning behind a mitigation is needed. Moved out of dev/PLAN.md by [L3.32-T113] because the table is orientation, not instruction.

---

## 9. Risks and mitigations

| Risk | Mitigation |
|---|---|
| LEM parameterization regresses check-time badly | L0.2 spike gates D2 before any mass port; documented fallback exists but needs a new owner ruling. |
| Conversion blowups resurface during rename/refactor | §7 budgets and per-module discipline; the source WORKLOG §5 playbook is the triage reference; countermeasures stay annotated and visible; the measured laws are in `dev/LESSONS.md`. |
| CI wall-clock grows past budget | §7 ceiling plus L5.1/L5.2 split gates and nightly full check; upstream M2.7 numbers bound the worst case. |
| Translation debt accumulates | A master merges only with en + zh complete (enforced by the marker checker); ja stays pre-supported. |
| Simplification scope creep | §10 register: every simplification candidate gets its own verify-then-decide entry; the default is a faithful port. |
| The thin endpoint margin closes | The naive projection passes the owner's 25k line, but the pass depends on new spend staying inside its band. Every gate that tightens the TOP of a band is margin work, not luxury (§0); the W7 cardinal gate and the two retirement gates run before the chapters they price. |
| Census-class terms re-price upward | The measured pattern of this campaign: down-corrections land on terms a probe can reach, up-corrections land on terms only a census could reach. Mitigation is the standing probe discipline (LESSONS D-1, D-6, D-10): every wide unprobed term gets its D-1 gate designed with the estimate and run before funding. |
| A residue's target turns out to be false | Happened once, expensively (the per-level identification, classically false and refuted in the literature). Mitigation now standing: the chain ROOT is truth-checked against the in-repo corpus before any link is priced (LESSONS D-10, appended 2026-08-03), and a delegated corpus dossier is mandatory for any residue stated as a named classical lemma. |
| Geology is funded before its sources are in hand | The in-repo corpus contains zero geology sources (`agents/tasks/archive/L3-31-GLPROBE/l3.31-glprobe-report.md`). Fetching Fuchs-Hamkins-Reitz, Usuba and Laver/Woodin is a mandatory gate before any geology funding, alongside the mantle size-wall design recon. |
| Statement drift toward unqualified "Con(ZFC)" | D1 fixes the framing; the root chapter and Landmarks are the canonical wording; glossary pins the translated terms. |
| Process drift (ad-hoc naming, unregistered work) | §6.0 rules: no work without a code, no backfilled registration; §11 updated in the same commit as the status change. |
