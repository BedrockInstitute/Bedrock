# LJ-1.139 report: the memo STATUS headers

STATUS: COMPLETE. `dev/memos/` is the only tree I wrote to, and only line 3 of
seven files.

## COUNT (lead)

- **Headers checked: 9. Headers repaired: 7. Headers already correct: 2.**
- **Bad pointers found: 10, across 7 memos. EIGHT of them RESOLVE and lead to
  the wrong rule. Two are dangling.** All ten are repaired.
- **THE BRIEF'S PREMISE IS FALSE, MEASURED. `dev/memos/` holds 21 memos and
  only NINE carry a line-3 STATUS header.** Twelve carry none, **and that is
  the convention rather than a defect**: see "The twelve" below.
- **A NINTH bad pointer class stands OUTSIDE my write scope, in eight more
  places across three files.** That is the bigger finding. See "Outside my
  write scope".
- **No abort trigger. No memo holds a live rule with no other home**, MEASURED
  by the citation map below.

## THE NINE HEADERS

| Memo | What was wrong | What it says now |
|---|---|---|
| `source-material-survey.md:3` | **THE DEFECT THE BRIEF NAMES.** Claimed its measurements are "the calibration anchor for the two-caliber discipline (dev/PLAN.md section 6.2)". `dev/PLAN.md:267` says "THE TWO-CALIBER DISCIPLINE IS REVOKED". The pointer resolved to the rule's revocation. | STANDING AS EVIDENCE, purpose dead. Says the measurements stand as a pricing anchor, that the two-caliber discipline is revoked (retiring DD7), and that DD8 carries the replacement. |
| `route-tree.md:3` | Same sentence: "the two-caliber discipline is section 6.2". | Names section 6.2 by its live title and says it revoked the rule. Adds that the L3 route is itself retired and the live route is DD2's two-tower bridge. |
| `process-tensions.md:3` | (a) "D11's mechanisms are stated in the D11 row of dev/PLAN.md section 3". **Section 3 holds no D11 row; DD11 there is code and prose craft.** (b) "the L0 standing track (dev/PLAN.md section 6.0)". **Section 6.0 is the coding rules; the L0 row is in section 11.** (c) "the fixed part level (D5)" gave no live home. | Sends D11 to the archive, states that the D and DD numbers do not correspond, points the L0 track at the section 11 row, and points the part level at `dev/PLAN.md` section 4. |
| `risks-mitigations.md:3` | Named "D1, D26" as the mitigations' homes. **Both are archived. A reader looking in section 3 finds DD1 (the same rule) and DD26 (THE CATALOGS ARE NOT COUNTED, an unrelated rule).** | Names DD1 and DD5 in section 3 as the live homes, then says D1 and D26 are archived, still resolve, and do not correspond. |
| `simplification-register.md:3` | "new candidates are proposed **in the current era** under D16 and D22". **Both archived on 2026-08-09; the current era is the DD series.** | Names the live rulings DD8 and DD13 (each verified by reading, not by assuming a mapping), and keeps D16 and D22 as archived provenance. |
| `target-skeleton-d5.md:3` | "**The live part-level rule is D5 in dev/PLAN.md section 3.**" Section 3 holds no D5; **DD5 there is the two quantitative constraints, an unrelated rule.** | Points the live part-level rule at `dev/PLAN.md` section 4, warns that DD5 is a different rule, and marks D5 archived. |
| `working-mechanisms.md:3` | (a) "(ruling D2 in dev/PLAN.md section 3)". **Section 3 holds no D2; DD2 there is the endpoint and architecture ruling. The live ruling is DD9.** (b) "the record of the Frontier's deletion is dev/JOURNAL.md (D8 struck row)". **`dev/JOURNAL.md` contains zero occurrences of "D8".** (c) "dev/PLAN.md section 11 rows L2.4 and L4.0". **Section 11 has an L4.0 row and NO L2.4 row.** | Names DD9 as the live ruling and D2 as archived; sends the D8 struck row to `archive/dev/JOURNAL-archived.md` and the L2.4/L4.0 rows to `archive/dev/STATUS-archived.md`; states the two negatives so nobody re-follows them. |
| `build-constraints.md:3` | **NOTHING. All six pointers verified.** | Unchanged. |
| `L3.32-context-layering.md:3` | **NOTHING.** Verdict WRONG / NOT BUILT, cites `[L3.32-T105]` and its own section 5; both resolve. | Unchanged. |

## THE POINTERS I OPENED (MEASURED, every one)

**Resolved and correct**, so the header keeps them:

- `scripts/README.md` (build machinery, `check-tree.py` documented at `:233`);
  `scripts/check-tree.py:112` `check_closure`, whose docstring at `:10` names
  PLAN section 7 rule 3.
- `dev/ORCHESTRATION.md:115-120`, heap caps and one Agda process per agent.
- `dev/ORCHESTRATION.md:487`, "**A cold-check regression is a defect**", which
  is section 6 step 2 exactly as `build-constraints.md` claims.
- `dev/LESSONS.md:1038` D-1, `:1159` D-6, `:1316` D-10, `:2075` C-12.
- `dev/PLAN.md:36` section 0; `:197` section 6.0; `:292-303` section 7 as eight
  numbered routing rows; `:317` section 11; `:343` the L0 row; `:354` L4.0;
  `:355` L4.1.
- `dev/ledger.toml:973`, the `[[excluded]]` table, S18 in the first entry.
- `dev/STYLE-agda.md:38` section 1; `:52` the LEM parameterization; `:46-51`
  the named module hypothesis; `:108-111` the two-catalog doctrine.
- `src/README.md:110`, "## Symbol master table".
- `archive/dev/STATUS-archived.md:60` row L2.4 ("THE FRONTIER IS EMPTY AND
  DELETED"), `:113` row L4.0.
- `archive/dev/JOURNAL-archived.md:4263` and `:4275`, the struck D8 row.
- `archive/dev/DECISIONS-archived.md:29` D1, `:30` D2, `:32` D5, `:36` D11,
  `:38` D16, `:44` D22, `:47` D26, and `:25` for D8 as struck.
- `archive/dev/TASKS-archived.md:140` `[L3.32-T105]`, `:148` `[L3.32-T113]`.

**Resolved and WRONG.** The eight are in the table above. The pattern is one
thing and it is worth stating once: **every one of them names a `D` code
WITHOUT saying where it lives, and `dev/PLAN.md` section 3 now answers with a
`DD` row of the same number.** The citation is not dangling and the reader is
not warned. `D2`, `D5`, `D11` and `D26` all have `DD` twins that mean
something else.

## THE TWELVE MEMOS WITH NO HEADER, and why I wrote none

The brief says all 21 open with a STATUS header. Nine do. The twelve without
are `L3.0.2-verdict`, `L3.0.3-subsumption-probe`, `L3.0.4-theorem-statement`,
`L3.28-ac-route`, `L3.29-b-pivot`, `L3.30-rud-route`, `L3.32-ac-endgame`,
`L3.32-below-lim-design`, `L3.32-burn-the-boats`, `L3.32-endgame-status`,
`L3.32-rehome-design` and `L3.32-route-adjustment-conflicts`.

**This is the convention, not a gap, and two independent sources say so:**

1. `dev/README.md:41-47` splits `dev/memos/` in two. **Goal deliverables** are
   one file per goal code, and their status is `PLAN.md` section 11. **The
   planning sections cut from PLAN by `[L3.32-T113]`** are the ones that "each
   carries a status header and a pointer back". The twelve are all goal
   deliverables.
2. `scripts/check-dev-docs.py:276-293` is **form-when-present by design**: it
   skips a memo with no header (`continue  # no status header`) and only
   demands a verdict word from a header that exists. The gate is green today,
   MEASURED (`check-dev-docs: clean (6 subcheck(s))`).

So I wrote no new headers. Inventing twelve live-or-dead verdicts for
retired-route memos is a ruling, not a repair, and nothing asks for it.

**One inconsistency, INFERRED as an oversight rather than a decision.**
`dev/README.md:43-45` lists the PLAN-cut memos as "the target skeleton, route
tree, source survey, build constraints, process tensions, risks and
simplification register", seven items. **It omits `working-mechanisms.md`,
which `[L3.32-T113]` cut from PLAN section 5 and which carries a header.**
`dev/README.md` is outside my write scope.

## OUTSIDE MY WRITE SCOPE, and this is the bigger finding

**The same defect stands in at least eight more places, in three files the
brief forbids me to edit.** Each names a `D` code or a PLAN section that has
moved, and each resolves to something else. MEASURED, every line opened.

| Site | What it says | What is there now |
|---|---|---|
| `scripts/README.md:483` | "(D20, `dev/PLAN.md` section 3)" | **It names the location explicitly and the location is wrong.** Section 3 holds no D20; DD20 merged into DD19. The worst instance found. |
| `dev/STYLE-agda.md:73` and `:152` | "PLAN D7" for naming hygiene | **DD7 is REVOKED.** A reader who follows this into section 3 finds a revocation and can reasonably conclude the naming rule is dead. It is not: archived D7 is naming hygiene. |
| `dev/STYLE-agda.md:69` | "book parts fixed by PLAN D5" | DD5 is the two quantitative constraints. |
| `dev/STYLE-agda.md:52` | "Classical principles are module parameters, never axioms (PLAN D2)" | DD2 is the endpoint and architecture ruling. The live home is DD9, which `dev/PLAN.md:193` states. |
| `dev/STYLE-agda.md:284` | "Authoring order per PLAN D6" | DD6 merged into DD5. |
| `dev/STYLE-agda.md:11` | "(PLAN D11 ...)" | DD11 is code and prose craft. |
| `src/README.md:42` | "No postulate, per PLAN D2" | Same as above. `src/` is out of scope by the brief. |
| `src/README.md:18` and `:88` | "PLAN §5: two-catalog doctrine" | PLAN section 5 (`:191`) is now a pointer, and it says the two-catalog doctrine is in `dev/STYLE-agda.md`. |

**And two defects in `dev/PLAN.md` itself**, which I must not edit:

- **`dev/PLAN.md:193`** says the Frontier deletion is "the struck D8 row of
  `archive/dev/DECISIONS-archived.md`". MEASURED: that file names D8 only in
  the retired-decisions paragraph at `:25`. **The row's text is at
  `archive/dev/JOURNAL-archived.md:4275`.**
- **`dev/PLAN.md:307`** says "the L0 standing track (§6.0)". MEASURED: section
  6.0 is the coding rules. **The L0 standing track is the L0 row of section 11,
  `dev/PLAN.md:343`.** The memo header I repaired had inherited this error from
  PLAN.

**Not defects, checked and cleared:** `dev/STYLE-agda.md:106` and `:256` both
say "archived" beside their PLAN citation, so the reader is warned;
`scripts/README.md:297` cites "ruling D34" with no location claim, and D34 is
at `archive/dev/DECISIONS-archived.md:54`.

## WHAT THE TWO EARLIER AUDITS DID, and what they missed

The brief asks why the defect survived them.

- **`agents/reports/archive/lj-0.1-consistency.md` NEVER LOOKED AT THE MEMOS.**
  MEASURED: the file contains ZERO occurrences of the word "memo". It found the
  two-caliber contradiction inside `dev/PLAN.md` (`:174-175`) and inside
  `AGENTS.md` (`:422-434`), which is the same rule in the two files it did
  scan. The memo directory was outside its sweep.
- **`agents/reports/archive/lj-0.2-sufficiency.md` FOUND EXACTLY THE TWO THE
  BRIEF NAMES AND DOWNGRADED THEM.** At `:214-218` it wrote that
  `route-tree.md` and `source-material-survey.md` "both name the revoked
  two-caliber discipline as current", then added "**I list these under
  preferences**". At `:287-289` its recommendation is "Fix the two memo status
  headers **when next touched**".
- **So the miss is not detection. It is CLASSIFICATION.** A pointer that
  resolves to a reversed rule was filed as cosmetic staleness, which bought it
  a deferral instead of a fix.
- **And neither audit generalized from the pair.** Both stopped at the
  two-caliber sentence. **Five more headers carried the same class of defect
  and no audit named one of them**, because the two-caliber revocation was a
  known event to search for and "a `D` code that now reads as a `DD` rule" was
  not. The search was keyword-shaped, so it found the keyword.

## VERDICT CHANGES

**One.** `source-material-survey.md` moves from **STANDING** to **STANDING AS
EVIDENCE, and its stated PURPOSE is dead**.

The reason, and the brief asked for exactly this distinction. Its measurements
are unaffected by any ruling, and `dev/PLAN.md:159` still calls them "a
calibration anchor for pricing (§6.2)", so the EVIDENCE stands. The PURPOSE the
header claimed for that evidence, calibrating the two-caliber discipline, was
revoked on 2026-08-09. SUPERSEDED would be wrong, because it would tell a
reader pricing a lever not to open the file. The split verdict is the honest
one.

No other verdict moved. The seven SUPERSEDED memos are still superseded, and
`L3.32-context-layering.md` is still refuted.

## THE ABORT CRITERION: no memo holds a homeless live rule

MEASURED, by grepping every live document for every memo filename. Four
headerless memos are cited by live files, and **every citation is provenance or
a reading pointer, never a rule statement**:

- `dev/LESSONS.md:21, 47, 65, 88, 108, 129, 147, 1049` cite
  `L3.28-ac-route.md` section 9 as **Provenance** for measured laws;
  `:1176` cites `L3.29-b-pivot.md` the same way.
- `dev/ledger.toml:733` cites `L3.32-ac-endgame.md` step 4 as **provenance**
  for a booked row.
- `dev/README.md:42` cites `L3.0.3-subsumption-probe.md` as an **example** of
  the goal-deliverable naming.

`dev/PLAN.md` cites the seven PLAN-cut memos, and every one of those citations
says the live rule is elsewhere. So DD19's broken-home condition is not
triggered.

## THE TERM I COULD NOT WRITE (C-36)

**Whether `source-material-survey.md`'s figures are still true of the source
repository today: 172 modules and 70.7k lines.** I did not measure it. The
survey is dated port-era, the source is a separate repository, and nothing in
my scope reaches it. **My header keeps the figures as the memo states them and
claims nothing about their currency.** What would settle it: one line count in
that repository at a pinned commit. **Nothing depends on the answer today**,
because DD5's line benchmark is measured against the internalization route's
own endpoint rather than against this survey.

## COULD NOT SETTLE

Nothing in my write scope. Every one of the nine headers is now checked and
correct. The eleven out-of-scope defects above need the orchestrator, and eight
of them are one class with one cheap cure: **write the location beside the code,
as `dev/PLAN.md:307` already does for D11.**

## CONSTRAINTS MET

- `.venv/bin/python scripts/lint-prose.py --check dev/memos/` exit 0.
- `.venv/bin/python scripts/check-rule-ids.py`: "clean (45 files, 141 lessons,
  66 decisions)", exit 0.
- `.venv/bin/python scripts/check-dev-docs.py`: "clean (6 subcheck(s))", exit 0.
  **This is the C-40 consumer check**: `check-dev-docs.py:309` registers
  `memo-status-form` over `dev/memos/`, and `check-rule-ids.py:93` puts `memos`
  in `HISTORICAL_DIRS`.
- No `D` code renumbered to `DD`. Every `D` citation in every header I touched
  is still present, and each now says where it resolves.
- No memo body changed. `git diff --stat` touches line 3 of seven files only.
- No em dash. No commit, no push, no Agda, no `make check`.

## ARCHIVE USED (DD18)

- `archive/dev/DECISIONS-archived.md:25` (D3, D8, D10, D12, D14, D15, D25
  struck 2026-08-05), `:29` D1, `:30` D2, `:32` D5, `:33` D6, `:34` D7, `:36`
  D11, `:38` D16, `:42` D20, `:44` D22, `:47` D26, `:48` D29, `:54` D34. Taken:
  the content of each `D` code, so I could say whether the memo's claim about
  it is still true and whether its `DD` twin is a different rule.
- `archive/dev/STATUS-archived.md:55, 60, 113, 114, 132`. Taken: the L2.4 row
  is where the Frontier deletion detail lives, which fixed
  `working-mechanisms.md`.
- `archive/dev/JOURNAL-archived.md:4263, 4275`. Taken: the struck D8 row's text
  is HERE and not in `dev/JOURNAL.md`. This corrected both the memo and
  `dev/PLAN.md:193`.
- `archive/dev/TASKS-archived.md:140` `[L3.32-T105]`, `:148` `[L3.32-T113]`.
  Taken: both task codes the headers cite resolve.
- `agents/reports/archive/lj-0.1-consistency.md:170-180, 422-434`. Taken: what
  it found, and the measured absence of any memo scan.
- `agents/reports/archive/lj-0.2-sufficiency.md:205-218, 283-289`. Taken: it
  found the two-caliber pair and filed it as a preference. That is the
  classification error this task exists to correct.

## LITERATURE (DD18)

Nothing in `dev/literature/` governs a memo status header, and I read none of
it. The task is document hygiene, not mathematics.

## DD4, MAXIMUM REUSE

No code was written, so DD4's generic-or-fixed choice does not arise. **The
document-side analogue does, and I applied it.** Six of the seven repairs are
one fix written once: **name the archive beside the `D` code, and say that the
`D` and `DD` numbers do not correspond.** I used `dev/PLAN.md:307`'s existing
sentence as the shared form rather than inventing a phrasing per memo, so the
next reader learns the rule once and it reads the same in every header.
