# Doc surgery report: slim PLAN, extract the lesson book, fix the pivot record

Executed 2026-08-01 against the brief at
`/private/tmp/claude-501/-Users-alsg-Agentic-Bedrock/32fd5cc7-cdf2-47c8-a038-6728849765b0/scratchpad/doc-surgery-brief.md`.
The failure mode was defined as LOSING a registry fact or a lesson; this report
is the audit trail. Every removed block of PLAN content is accounted for below
(what went where), the LESSONS entry list carries its sources, lessons that
could not be sourced are listed, and the final line counts of PLAN before and
after close the report.

## 1. Files changed

| File | Change |
|---|---|
| `dev/LESSONS.md` | new: the measured lesson book, 865 lines, 49 entries |
| `dev/memos/L3.29-b-pivot.md` | new: the pivot memo, 378 lines (within the 250-450 target), 6 sections |
| `dev/PLAN.md` | rewritten as the goal-history registry: 3,051 lines before, 1,505 lines after |
| `dev/README.md` | one listing update: the `LESSONS.md` bullet in the Contents list |
| `_build/doc-surgery-report.md` | this file |

No other file was created or modified. No git commands were run. All touched
files passed `scripts/lint-prose.py --check` (exit 0 each); `make check` was
run once at the end and is green (doc-only changes). No em dash appears in any
touched file (the linter enforces this; the report-only check passed).

## 2. Coverage accounting for removed PLAN content

`dev/PLAN.md` went from 3,051 to 1,505 lines. The rule applied per removed
block: every removed sentence must be covered by `dev/LESSONS.md`, the pivot
memo, an existing memo, or the git history of the chapter it describes. Blocks
that were compressed rather than removed kept their registry facts verbatim in
compact form; the table states which rule was applied to which block.

| Removed block (original PLAN) | Coverage rule applied |
|---|---|
| §1-§2, §2.1 narrative (theorem framing, survey detail) | Compressed in place; meaning and all registry facts (source pin, scale, assumption budget, cost-anatomy tables, the `[L3.0.3]` correction) preserved. Trimmed sentences were framing, covered by the git history of `src/` and the pinned source checkout at `../fol-reification`. |
| §3 decisions D1-D15 | Compressed in place; every ruling kept with its date. D15 gained the 2026-08-01 B pivot pointer to `dev/memos/L3.29-b-pivot.md`. |
| §4 skeleton rationale and the rename ledger | Tree kept; rationale compressed (framing). The rename ledger is preserved in full: every rename ruling, date, and zh rendering is a registry fact and none was dropped. |
| §5 working mechanisms | Kept, wording compressed; the Frontier deletion fact (2026-07-31) is recorded. |
| §6.0 coding rules | Kept in full (rules 1-6). |
| §6.1 goal entries (L0-L5 tree) | Registry facts kept: goal, title, scope, registration dates, statuses. Kill criteria kept in compact form for `[L3.0.1]`; phase list kept. The measured laws cited inside entries moved to `dev/LESSONS.md` (P-a..P-f, rules 1-20, R-21..R-30, T-1/T-2, I-1, D-1..D-4). Probe and statement substance is covered by the existing memos `memos/L3.0.3-subsumption-probe.md`, `memos/L3.0.4-theorem-statement.md`, `memos/L3.0.2-verdict.md`; per-chapter diagnosis detail is covered by the git history of the chapters named. |
| §7 build constraints | Kept in full (8 constraints). |
| §8 tensions T1-T6 | Kept, compressed to the valve sentences. |
| §9 risks | Kept; added the B-build risk row (mitigation: pivot memo §6). |
| §10 candidate register S1-S12 | Kept in full with verdicts; the post-verdict status cross-references (`[L3.4]` abandoned, `[L3.9]`/`[L3.11]`/`[L3.12]`/`[L3.13]` abandoned) are recorded in the rows. |
| §11 table rows L0-L3.27 | Each row's dated rulings and landed-batch headline numbers (chapters, line counts, check times, Frontier counts) kept in compact form. Detailed single-chapter narratives were removed and are covered by the git history of the chapters they describe, plus `dev/LESSONS.md` wherever the record itself stated a law (the ledger entries name the lesson IDs). |
| §11 row L3.28 (giant) | Kept as registry: registration date, candidate (3) deletion (−74), survey baseline 17,492, lever sums −755/−1,486, landing 16.0k-16.7k, ruling C (D15), gate transfer to `[L3.29]`. The AC-route fork and probe numbers are covered by the existing memo `memos/L3.28-ac-route.md`; the measure-before-estimating and no-statement-weakening discipline is in `dev/LESSONS.md` (D-1, rule 6). |
| §11 row L3.29 (giant) | Kept as the registry skeleton required by the brief: route C registered and active 2026-07-31; M1-M4 milestone records with dates and headline numbers; the tripwire history (11k fired, re-set 14k, fired, re-set 16.5k post-compression); the M5 rulings (order re-cut, junk-table certificate design, M5-internal skeleton/parameter re-cut, the measured 28,580/15,280 state); the M5a landing record (landed, committed `9539088`, retired by the B pivot, lessons P-g and the graft entry); the B pivot ruling with its pointer to `dev/memos/L3.29-b-pivot.md`; the CURRENT state (B development active on this branch, delivered route coexists untouched, final measurement then a fresh ruling before retirement); M6/M7 as originally registered with the B ruling's fresh-ruling clause noted. The laws P-a..P-f, the termination lessons T-1/T-2, the inference trap I-1, and the design doctrines D-2/D-3 moved to `dev/LESSONS.md`; the audits, probes, A-vs-B pricing, work plan, and open risks moved to `dev/memos/L3.29-b-pivot.md`; per-chapter line measurements are covered by the git history of the `src/L/Godel/*` chapters. |
| §11 bookkeeping dated entries (the bulk, about 1,900 lines) | Converted into the dated ledger (40+ entries). Each ledger line preserves the date, ruling, tripwire change, or landed-batch record (chapter names, headline line counts, check times). Per-record diagnosis narratives were removed and are covered by: (a) `dev/LESSONS.md` when the record itself stated a law (rules 1-20, R-21..R-30, P series, T, I, D, C entries), each with its provenance pointer back to the PLAN row; (b) the pivot memo for the five `_build/` reports' content; (c) the existing memos for `[L3.0.1]`-`[L3.0.4]` substance; (d) the git history of the chapters described for everything else. |

The completeness check applied to the ledger: every date, ruling, tripwire
change, chapter name, and headline number in the original bookkeeping was
re-read against the new dated ledger; the ledger was written from that
inventory, and the two audits whose numbers anchor the pivot (the ruled
measurement and the 16.5k tripwire re-set) were cross-checked against the
pivot memo and the order-probe report.

## 3. LESSONS entry list, with sources

`dev/LESSONS.md` holds 49 entries. Every entry has a provenance pointer inside
the file; the list below is the index with sources.

| ID | Entry | Source |
|---|---|---|
| P-a | Tag discrimination through helpers with explicit-data numeral indices | `memos/L3.28-ac-route.md` §9 (probe P2); PLAN §11 L3.29 |
| P-b | Union-free operation definitions | `memos/L3.28-ac-route.md` §9 (probe P1) |
| P-c | Seal `⋃`-tower indices opaque at birth | `memos/L3.28-ac-route.md` §9; PLAN §11 L3.29 |
| P-d | Reductions travel as direction pairs, never as hProp paths | `memos/L3.28-ac-route.md` §9; PLAN §11 L3.29 (M2, M4) |
| P-e | Presentation-parameterized data types at abstract type parameters | `memos/L3.28-ac-route.md` §9; PLAN §11 L3.29 (M2) |
| P-f | Dependent transports restated as path lambdas under one non-dependent subst | `memos/L3.28-ac-route.md` §9; PLAN §11 L3.29 (M4c) |
| P-g | No `cong` with a function lambda at concrete presentation-carrying types | `_build/m5a-report.md` Surprises 1 (committed `9539088`); PLAN §11 L3.29 M5a landing record |
| Rule 1 | Discharge adequacy substitutions at variable arguments | PLAN §11 rows L3.0.1, L3.21, L2.4, L3.23 |
| Rule 2 | Seal a construction `opaque` at the site where it is built (module application is such a site) | PLAN §11 rows L3.0.1, L2.2, L3.21, L2.4 |
| Rule 3 | Compute one side of a two-indexed case analysis from the tag | PLAN §11 rows L3.0.1, L3.20, L3.22 |
| Rule 4 | Transport a statement rather than re-parameterizing its proof | PLAN §11 rows L3.0.1 (U5b), L3.23 |
| Rule 5 | Frames generic in a constructor (or a sentence) take the defining equation as a hypothesis | PLAN §11 rows L3.21, L3.19 (RULE 9), L3.20 |
| Rule 6 | Grep what unfolds what you change before estimating | PLAN §11 bookkeeping, "Rule 6 has a boundary, found by [L3.26]" |
| Rule 8 | A `PT.rec` over an object-language existential must name its payload type | PLAN §11 row L3.27 (RULE 8) |
| Rule 9 | A named alias in a unification position is fatal; the cost is the sentence reducing at concrete slots | PLAN §11 rows L2.4 (C2/C3, faithfulness), L3.19 (RULE 9) |
| Rule 10 | Splits concluding in a membership hProp are named helpers, never `with` | PLAN §11 rows L2.4 (route audit RULE 10; faithfulness) |
| Rule 11 | A data declaration whose constructor mentions the order is fatal | PLAN §11 rows L2.4 (C2/C3, C5) |
| Rule 12 | An introduction helper with implicit arguments is fatal | PLAN §11 row L2.4 (C2/C3) |
| Rule 13 | Abstraction is not the cure for non-locality | PLAN §11 row L2.4 (C2/C3); L3.28 lever (f); compression audits |
| Rule 14 | A concrete element at a slot inside a satisfaction must be sealed (with the correction: seal the pair carrying the constructibility proof) | PLAN §11 rows L2.4 (C5; faithfulness) |
| Rule 15 | A block of binders must be a frame generic in its body | PLAN §11 row L2.4 (C5) |
| Rule 16 | An environment must be spelled out, never abbreviated | PLAN §11 row L2.4 (faithfulness) |
| Rule 20 | Composites of adequacy equations are consumed factor by factor | PLAN §11 row L2.4 (obligation (a), RULE 20) |
| R-21 | The conclusion type a frame lands in must be sealed where it is built | PLAN §11 row L2.4 (the assembly) |
| R-22 | A property of a computed least name must be the exported least-element predicate | PLAN §11 row L2.4 (the re-cut) |
| R-23 | The stage arrives as a term, not a slot | PLAN §11 row L2.4 (faithfulness) |
| R-24 | A library round-trip lemma is a conversion hazard in its own right | PLAN §11 row L3.26 |
| R-25 | Naming a module application in a TYPE re-does it | PLAN §11 row L2.4 (C0/C1) |
| R-26 | The parameter remedy and the seal are not alternatives | PLAN §11 row L2.4 (the earliest-disagreement family) |
| R-27 | The check-time predictor is induction count times truncation elimination | PLAN §11 row L3.0.1 (design ruling for satisfaction's `funct`) |
| R-28 | Witness-locality | PLAN §11 bookkeeping, reconnaissance and adjudication [L3.0.1] |
| R-29 | Seal the membership certificate where the element is built, not the element | PLAN §11 bookkeeping, conversion-blowup finding [L2.2] |
| R-30 | Rules 1 and 2 split on where the expensive construction lands | PLAN §11 row L3.23 |
| T-1 | At-pattern aliases of accessibility constructors; split the nests outer and inner | PLAN §11 row L3.29 (M5, N1) |
| T-2 | The transitive-closure accessibility pattern | PLAN §11 row L3.29 (M5, d2) |
| I-1 | `mirrorBy`-style formula metas; explicit formulas at call sites | PLAN §11 row L3.29 (M3); `memos/L3.28-ac-route.md` §9 P-d (the respect lemma) |
| D-1 | The probe doctrine | `memos/L3.28-ac-route.md` §6; PLAN §6.1 and §11 rows L3.0.3, L3.24, L3.28, L3.29 |
| D-2 | The junk-table lesson | PLAN §11 row L3.29 (M5, d); `_build/cut-probe-report.md` §2.2; `_build/order-probe-report.md` §3 |
| D-3 | The scaffold-copy pattern for coexistence | PLAN §11 row L3.29 (M5, N3); `_build/compression-audit.md` F6 |
| D-4 | The collector principle | `_build/deep-levers.md` §3.3; `_build/order-probe-report.md` §2 |
| C-1 | Two conversations must not share a worktree | PLAN §11 row L3.2 (process note; commit `7428a23`) |
| C-2 | Never sort Agda's profile output numerically without stripping the separator | PLAN §11 bookkeeping, cold-check baseline correction (2026-07-27) |
| C-3 | Prose that states an invariant is load-bearing and has to be checked like code | PLAN §11 rows L3.0.1 (twelve-clause audit), L3.16, L3.23 |
| C-4 | A shape reader that reads fewer layers than the data has is silently vacuous | PLAN §11 row L3.16 (mis-count correction) |
| C-5 | Every reader a clause consumes should carry a characterization in both directions | PLAN §11 row L3.16 (defect in delivered code) |
| C-6 | Check by perturbation rather than by reading | PLAN §11 rows L3.21, L3.19 |
| C-7 | A row's opening word is what a reader takes | PLAN §11 rows L3.17, L3.21, and the L3 status re-confirmation (2026-07-29) |
| C-8 | The gate has blind spots; name and close them | PLAN §11 rows L2.4 (C6), L3.19 (route audit), L2.4 (earliest-disagreement family) |
| C-9 | The graft entry: graft retractions as explicit projections | `_build/m5a-report.md` (Deviation in the graft equations; committed `9539088` with P-g) |

## 4. What could not be sourced

- **Rules 7, 17, 18, 19.** The PLAN and memo records never state these rule
  numbers; the source numbering has gaps. They are therefore not entered as
  lessons; the gap is documented in `dev/LESSONS.md` (entry-format section)
  and in the numbered-rule section's preamble, and is listed here so nobody
  re-derives them as if they were missing registry facts.
- **The M5a commit hash `9539088`.** The reports in `_build/` do not carry the
  hash (they refer to the "working tree" and to HEAD `a896bf2`). The brief
  supplied the hash for the M5a landing record, and it is used as instructed in
  the PLAN row and the LESSONS provenance; it was not independently verified
  from git (no git commands were permitted).
- **The exact date of the B pivot ruling.** The probes and audits are dated
  2026-08-01 in the reports and PLAN; the ruling is recorded as 2026-08-01 to
  match the same-day record. No separate ruling-date source exists in the
  `_build/` reports; the order-probe's "Final A-versus-B recommendation: build
  B" is the recorded basis.
- Everything else in LESSONS.md is traceable to a memo, PLAN row, report, or
  commit as listed in §3.

## 5. Final line counts

| File | Before | After |
|---|---:|---:|
| `dev/PLAN.md` | 3,051 | **1,505** |
| `dev/LESSONS.md` | (new) | 865 |
| `dev/memos/L3.29-b-pivot.md` | (new) | 378 |
| `dev/README.md` | 30 | 33 |

## 6. Verification

- `scripts/lint-prose.py --check` on every touched file: `dev/PLAN.md`,
  `dev/LESSONS.md`, `dev/memos/L3.29-b-pivot.md`, `dev/README.md`, and this
  report: exit 0 on each.
- `make check` once at the end: green (the changes are doc-only; the Agda
  gate, marker checks, prose lint, glossary check, and `reuse lint` all pass).
