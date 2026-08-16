# LJ-1.367 report: give the DD24 bar ONE home, and gate every restatement

## One line

**YES, MEASURED: the bar's figures now live in `dev/ledger.toml` alone (22 guarded figures, every one derived from the ledger at run time), every other live claim names the field, and `scripts/gate/check-baseline-home.py` holds them there: exit 0, 1.4 s cold, wired into `make check` as `baselinehome`.**

## Every site, classed

### LIVE (asserted what the bar IS today; converted to name the field)

- `dev/PLAN.md:144-146` (was `:145`): "55.1x the 0.010514 bar". Kept the 0.5795 landing measurement, dated the bar to its landing day with the marker, and named `ac_baseline_module_rate` x `tolerance` and the `[ratio]` table for today.
- `dev/PLAN.md:212-214` (LJ-1.277, landed 2026-08-15, `git log` MEASURED): "0.66x the 0.010514 bar". Same treatment: `0.010514 HISTORICAL(2026-08-15)`.
- `dev/ledger.toml:2599+` `[ratio]` header: ADDED seven comment lines naming the two homes, the compute site, and the gate as the enforcement point. No figure changed anywhere in the ledger (git diff shows my hunk is the comment block only; the `0.011828`/`17185` restoration is the owner's uncommitted change, verified as instructed and untouched).
- `scripts/measure/check-ratio.py:240`: "DD24's bar and its 1.15x tolerance" restated the tolerance value in a comment. Now names the fields and says "this file computes and never states them". `:46-48`: "OVER the 0.0136 bar" now says "the 0.0136 bar of that day, 2026-08-13". The `:468-478` header rule ("THE HEADER MUST ADVERTISE THE BAR THAT IS ACTUALLY APPLIED") is intact and agrees: `judged = module_rate or baseline; bar = judged * tolerance`.

### HISTORICAL (dated records; figures KEPT, marker added, nothing deleted)

- `dev/LESSONS.md:3027` (C-33, `[LJ-1.33-R]`, 2026-08-11): "DD24's 0.013193 bar" now reads "DD24's bar, 0.013193 HISTORICAL(2026-08-11) and live on the day of the measurement". The 2x2 table above it is untouched.
- `dev/LESSONS.md:3838-3846` (P-y): the fall `0.011828 to 0.009143` SURVIVES INTACT with `both HISTORICAL(2026-08-13)` on the same line, and a new paragraph records the owner's 2026-08-16 reversal: the fall is a fact about a later tree, never about the bar; the second reading is kept in `[ratio]` as a superseded record; the gate refuses its restatement as live.
- `dev/PLAN.md:1273` (LJ-1.265's row): NOT edited, per the brief. It is in the gate's `EPOCH` (see below), and the superseding row is drafted below for the owner.

### TEST

`scripts/tests/test_ratio_noise.py`. **Choice: BOTH offered options.** The fixtures now READ the ledger (`cfg = cr.config(); bar = cfg["ac_baseline_module_rate"] * cfg["tolerance"]`) and build every bar-anchored series from it (`on_bar`, `over`, `fragile_over`, `tight`), so the test can no longer drift from the figure it pins; the comment at the old `:172` arithmetic ("The bar is 0.011828 * 1.15 = 0.013602", the arithmetic spelling the brief warned about) now names the fields and holds no figure. The pure-function arguments at `:111-123` keep their historical numbers with the date added ("2026-08-13: ... the bar of that day"). Suite PASS, 0 failing checks, MEASURED.

### FROZEN BY THE GATE (out of my write scope; reported every run, never failed)

The `EPOCH` set in the gate holds 12 whole line texts: `dev/JOURNAL.md:184-185` ([LJ-0.4] entry, 2026-08-10, "inside DD24's 1.15 bar of 0.008847"); `dev/PLAN.md:502`, `:615`, `:873`, `:970`, `:1047`, `:1273`; `scripts/measure/ledger.py:272-273`; `scripts/tests/test_ratio_baseline.py:5-6`. Entries are whole-line texts, so they cannot drift with line numbers and die the moment their line is edited.

## Sites the brief missed

- **`dev/PLAN.md:502-504` is a LIVE claim quoting a SUPERSEDED baseline, and it is the biggest find.** "The quality bar that DOES bind, today (DD24) ... The delivered AC wing measures **0.007913 s/line**, from a 133.70 s mean of three cold runs over 16,897 lines" names the `[LJ-0.5]` figure of 2026-08-10. The ledger's `ac_baseline_seconds_per_line` has been 0.008793 (151.11 s, 17,185 lines) since 2026-08-13. It is frozen in `EPOCH` with a loud comment; proposed fix for the owner: "The delivered AC wing measures the `[ratio]` table's `ac_baseline_seconds_per_line` HISTORICAL(2026-08-10): 0.007913 over 16,897 then, 0.008793 over 17,185 since 2026-08-13."
- **`0.007913` and five siblings were absent from the brief's seven literals**: the whole-ledger derivation guards 22 figures (`0.007693 0.007816 0.007847 0.007904 0.007913 0.007987 0.007999 0.008102 0.008793 0.008847 0.009143 0.010514 0.011057 0.011472 0.011490 0.011828 0.012716 0.013193 0.013602 0.014367 0.016522` plus the derived product `0.010112`). Note `0.013193` lives at `dev/ledger.toml:308`, OUTSIDE `[ratio]`, so a table-only slice would have missed it; the gate reads the whole ledger.
- **Four-decimal roundings**: "the 0.0136 bar" in `check-ratio.py:46` (dated, fixed) and in ~15 task-dir records plus `runs/*.txt` machine logs (frozen). MEASURED collision: `check-ratio.py:257` records a MODULE rate "0.0136 5,355 lines 73.07 s" that is not the bar, so the 4-decimal form cannot be guarded without forcing markers on non-bar figures. Unguarded BY DESIGN, stated in the gate's docstring.
- **Ratio spellings** ("1.56x", "1.91x", "1.70x", "56.5x"): not bar figures, not guardable from the ledger alone. Stale-anchored ones the owner should re-check: `dev/PLAN.md:49` (LJ-1.9 row: "1.70x" and "gap 60.0 s" were computed against the drifted 0.009143/0.010514 pair; against the restored figures my arithmetic gives 1.31x and a 23.2 s gap, INFERRED from the recorded 185.41 s / 11,926 lines), `dev/PLAN.md:126` ("56.5x the DD24 bar to 0.76x"), `dev/PLAN.md:439-443` (the DD4-against-DD24 paragraph, 1.56x to 1.91x, anchored to the drifted baseline). All three are outside my write scope; none carries a guarded literal, so the gate is blind to them.
- **Word spelling**: no "the bar is X s/line" prose outside the sites above; `dev/JOURNAL.md` has zero hits on every spelling, MEASURED.

## The gate

- **Marker spelling** (stated in the docstring): `<figure> HISTORICAL(YYYY-MM-DD)`, the date naming the day the figure was true, on the same line as the figure. A live claim names the field instead and needs no marker.
- **Epoch**: (1) every task directory at or below `LJ-1-367` (records written once; `LJ-1-368` and any `LJ-2-*` are gated); (2) `archive/` and `agents/tasks/archive/`; (3) the 12-line `EPOCH` set above, content-keyed. The frozen scale is written in the code and the Makefile comment, never in a commit message (C-59). `.claude/` tool state is skipped with the residual stated.
- **Runtime**: 1.35 s cold, MEASURED. `make baselinehome` exit 0, read with no pipe.

## Superseding task-index row (for the owner to add; names fields, states no figure)

`| LJ-1.366 | Owner reversal: DD24's bar is not re-timed by a cure | RESTORED TO THE TROPHY-LANDING FIGURE | The applied bar is \`ac_baseline_module_rate\` x \`tolerance\`, at check-ratio.py only. Supersedes LJ-1.265, found by LJ-1.364 |`

## My false negatives

- Four-decimal roundings and verdict multiples are unguarded (designed, see above). MEASURED collision for the first; INFERRED for the second.
- A figure that appears nowhere in the ledger is invisible until its recalibration lands; then it enters the set mechanically. INFERRED.
- Files added to an already-frozen task directory (born before LJ-1.368) escape; their authors are live dispatches LJ-1.362/365 whose briefs predate the gate. INFERRED.
- An exact re-paste of an `EPOCH` line elsewhere would be forgiven once (content-keyed entries match text, not place). INFERRED.
- A marker on a line that also asserts liveness is not detected; the gate reads the statement, judgment stays with review, the same boundary `check-dd4-stated.py` states. INFERRED.

## DD4

My axis is not the two towers. The live axis IS DD24's bar: it is the instrument that reads the GCH wing against the AC wing, so the drifted bar mis-reported the DD4 relationship itself for three days (1.91x read where the ruling allows about 1.31x, my arithmetic INFERRED). **The owner should re-check every verdict anchored to 0.009143/0.010514: PLAN:49 (1.70x, 60.0 s), PLAN:126, PLAN:439.** No figure I changed is itself a DD4 verdict; I changed only how they are spelled.

## ARCHIVE USED

- `archive/dev/DECISIONS-archived.md`: READ, and it carries the strongest evidence a gate can hold. The retired route's bars drifted by ruling, repeatedly: `:50` "A first version set a projected total of 1,100 s and it was wrong ... A threshold whose pass or fail flips with which of two measurements you use is not a gate", with amendments (A) to (G) moving 7.5 min to 8.3 min to 600 s; `:59` "RAISED 2026-08-09 BY THE OWNER: the cap goes 16,000 to 20,000, and the wall gate goes 498 s to 600 s in the same ruling". TAKE: a bar restated in decisions, journals and tasks drifts even when every move is ruled; one home plus a gate is the cure, and D30's own sentence is the gate's best docstring.
- `archive/dev/JOURNAL-archived.md`: READ, bears. `:1935` "ledger drifted without anyone noticing; the +2,364 gap is the measured wave-2 delivery net (+3,512)". TAKE: the retired route measured unnoticed figure drift itself; C-28's class is not new.
- `archive/dev/TASKS-archived.md`: READ, one baseline re-measurement found. `:244` "| L3.32-T240 | Re-measure the carried sequence with the generic clause: lines AND seconds | 589 nbl / 174.62 s / 0.297 per line". TAKE: re-measurements were dispatched tasks then too, so a re-time is an act a gate must be able to refuse.
- `archive/src/2026-08-09-rud-route/`: checked its listing (Agda masters `Everything/FOL/L/V`, `README.md`, `rud-route-src.patch`) and grepped its README for baseline/bar terms: zero hits, nothing bears on a figure gate. MEASURED.

## LITERATURE USED

`dev/literature/` holds mathematics digests (Devlin errata and II5, fine structure, geology, j-hierarchy, truncation, primary sources). NOTHING bears on threshold or baseline design; this confirms `[LJ-1.356]` and `[LJ-1.357]`, which measured that nothing there bears on process mechanisms. DECLINED, one line, as the brief allowed.

## Housekeeping

- `AGENTS.md`: no diff needed, INFERRED: it already names `make check` as the commit gate, and the gate is now inside `make check`.
- `make check` was NOT run whole (12-minute typecheck, two live Agda slots); only `make baselinehome`, the noise test, and `lint-prose.py --check` on every file I touched, all exit 0, MEASURED.
- `check-ratio.py` itself was NOT run, per the brief.
