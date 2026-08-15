# LJ-1.265 report: which rate DD24 licenses, and the wing's real gap

tier: pi (deepseek-subagent-mode), model `deepseek-v4-pro`. Read-only. No Agda
ran. No slot held. No master, ledger, plan or sibling task touched. No commit,
no push. Written incrementally (C-22). Every negative is marked MEASURED or
INFERRED.

**STATUS: COMPLETE. ONE RATE IS DD24'S, ONE RATE IS DERIVED, ONE RATE IS
STALE, AND THE BUDGET IS STALE.**

## 0. LEAD: ONE RATE AND ONE GAP

**DD24's live bar, at the caliber the wing is measured, is `ac_baseline_module_rate` 0.009143 s/line times the 1.15 tolerance, which is 0.010514 s/line** (`dev/ledger.toml:2746`, `:3008`; `scripts/check-ratio.py:462-464`).

**The wing's gap to that bar, judged as delivered over 11,926 lines, is 60.0 s** (185.41 s measured minus 0.010514 x 11,926 = 125.4 s on-bar). This is `[LJ-1.218]`'s figure, and `[LJ-1.222]` reviewed it and kept it.

The three rates settle as follows:

| rate | what it is | status | file:line |
|---|---:|---|---|
| 0.007913 | DD24's whole-cone bar, DD26 re-base | **DD24'S FIGURE** | `dev/PLAN.md:268` |
| 0.009143 | the same bar re-calibrated to the module caliber | **DERIVED** | `dev/ledger.toml:2746` |
| 0.013193 | old module rate 0.011472 x 1.15 | **STALE** | `dev/ledger.toml:249` |

So ONE rate is DD24's, one is derived, one is stale. DD24's ruling words name
the whole-cone ratio, which DD26 fixed at 0.007913 over 16,897. The wing is
not measured at that caliber. It is measured at the module-slice caliber, so
its gap is judged against the derived re-calibration 0.009143 x 1.15 = 0.010514.
The gap is 60.0 s. 0.013193 is stale.

## 1. WHAT DD24 AND DD26 ACTUALLY SAY

**DD24** (`dev/PLAN.md:265`): "THE QUALITY BAR IS SECONDS PER LINE... the ratio
of cold build seconds to in-fence lines" of "that route's delivered L = AC
wing". The bar is a number, not a judgment. The wing carries no other
threshold. `dev/ledger.toml` records `ac_baseline_lines` beside the figure.

**DD26** (`dev/PLAN.md:268`): "DD24's baseline is 0.007913 over 16,897 rather
than 0.007904 over 16,916." This is the whole-cone rate: 133.70 s over 16,897
lines, stated also at `dev/PLAN.md:155-156`.

So the ruling's own figure is **0.007913 over 16,897**. That is the whole-cone
caliber: one cold build of the Landmarks cone, seconds over the lines that one
build compiles.

**The caliber split.** `dev/PLAN.md:158-160` states it in the ruling's own
document: `check-ratio.py` "times module slices and the bar is a whole-cone
rate, so it refuses until --recalibrate supplies ac_baseline_module_rate." So
0.007913 is the definitional bar, and 0.009143 is the SAME bar re-measured at
the module-slice caliber so the checker can judge one wing module. Both are
DD24. Neither is a third bar.

## 2. WHERE 0.013193 CAME FROM, AND WHY IT IS STALE

**The origin is a brief, not a ruling.** `agents/tasks/archive/LJ-1-6/LJ-1.6.md:66-70`
reads: "The bar is 0.011472 s per line at the module caliber, times 1.15, so
0.013193."

So 0.013193 = 0.011472 x 1.15. 0.011472 is the 2026-08-10 module rate over
16,897 lines. The 1.15 is DD24's tolerance. MEASURED: 0.011472 x 1.15 =
0.0131928, which reproduces 0.013193.

`[LJ-1.6-R]` then quoted 0.013193 as "DD24's bar" (`agents/tasks/archive/LJ-1-6/lj-1.6-review.md:256`, `:263`) and computed the wing's seconds budget from it (`:272-274`). The ledger froze both at `dev/ledger.toml:248-249` (the comment) and `:311` (the field).

**The staleness is from the re-measurement chain, not from DD26.** MEASURED.
`dev/ledger.toml:2903-2904`: "the 2026-08-10 figure it described, 0.011472
over 16,897 lines, had already been superseded" by 0.011057 (written by
f48ffd7, 2026-08-11). So 0.011472 already used the post-DD26 denominator of
16,897. DD26 did not re-base it. The later re-measurements superseded it:

| module rate | over | DD24 bar = rate x 1.15 | source |
|---|---:|---|---|
| 0.011472 | 16,897 | **0.013193** | `LJ-1.6.md:67-70` |
| 0.011057 | 17,081 | 0.012716 | `dev/ledger.toml:2903` |
| 0.014367 | 20,286 | 0.016522 | `dev/ledger.toml:2652, :2908-2909` |
| 0.011828 | 17,185 | 0.013602 | `dev/ledger.toml:2720` |
| 0.009143 | 17,197 | 0.010514 | `dev/ledger.toml:2746-2747` |

So 0.013193 is four re-measurements old. The live module rate is 0.009143.
0.013193 is STALE, and the ledger says so nowhere at `:248-249` or `:311`.

**A trap to name.** `0.007913 x 1.15 = 0.009100`, close to 0.009143 but NOT
equal. And `0.009143 / 0.007913 = 1.155`, also close to 1.15 but NOT equal.
Both near-equalities are coincidence. The 1.15 is a deliberate gate tolerance
(`dev/ledger.toml:3008`), not the module-to-cone caliber ratio. The ledger
records that caliber ratio as 1.45x, then 1.31x, then about 1.04x across three
trees (`dev/ledger.toml:2668-2673`, `:2744`). It is not a constant, and it
must not be used to "align" the three rates. MEASURED that the ratios are not
equal; INFERRED that any alignment on them is wrong.

## 3. THE WING'S REAL GAP, AND THE RIGHT DENOMINATOR

**The right denominator for DD24 is the delivered 11,926 lines, not the
a-priori band.** DD24 judges the wing AS DELIVERED (`dev/PLAN.md:265`: the wing
reaches the quality of the delivered AC wing). The a-priori band [7553, 11197]
is DD5 measure 2, the projection ceiling recorded before the build
(`dev/ledger.toml:241-243`). They are two different questions, exactly as the
brief says.

The gap, re-derived from the pinned figures:

- wing seconds: 185.41 s over 11,926 lines (`agents/tasks/LJ-1-218/lj-1.218-report.md:44-45`)
- bar: 0.009143 x 1.15 = 0.010514 s/line
- on-bar allowance: 0.010514 x 11,926 = 125.39 s
- gap: 185.41 - 125.39 = **60.0 s** (matches `:48`)

**The gap is 60.0 s.** It is an upper bound: `[LJ-1.222]` kept it as an upper
bound because the machine carried load 5.5 to 7.0, not a quiet machine
(`agents/tasks/LJ-1-222/lj-1.222-report.md:415`). The quiet-machine gap would
be lower. MEASURED that the gap is 60.0 s as raw seconds; INFERRED that it is
an upper bound, from the load the two reports recorded.

The other three numbers in the brief's table are all wrong for a different
reason, and each reason is now named:

- 28 s uses 0.013193: STALE bar.
- 76 s uses 0.009143 with no tolerance: drops the 1.15 the gate applies.
- 91 s uses 0.007913: whole-cone bar against a module-slice measurement, a
  caliber error. The wing's 185.41 s is module-slice seconds; it cannot be
  divided by a whole-cone rate. INFERRED for the caliber-error reading; the
  caliber mismatch is MEASURED at `dev/PLAN.md:158-160`.

**One further fact, stated not acted on.** The delivered 11,926 lines already
exceed the a-priori band's top of 11,197 by 729 lines. That is a DD5-measure-2
and DD8 overage question, not a DD24 question. This task does not re-derive
line counts, so I state it and leave it to the orchestrator. INFERRED (both
numbers are on the record, but I did not re-count them).

## 4. WHAT `dev/ledger.toml:311` SHOULD READ

`gch_wing_seconds_budget = [99.6, 147.7]` is stale. It was computed as
0.013193 x [7553, 11197]. MEASURED: 0.013193 x 7553 = 99.65, 0.013193 x 11197
= 147.72.

**It should read [79.4, 117.7]**, computed as the live bar 0.010514 x
[7553, 11197]. MEASURED: 0.010514 x 7553 = 79.41, 0.010514 x 11197 = 117.73.

The corrected field and its comment must say three things:

1. The rate is `ac_baseline_module_rate` times the 1.15 tolerance, the live
   bar, not the stale 0.013193.
2. It is a planning figure over the a-priori band (DD5 measure 2), not DD24's
   delivered-wing judgment, which uses the delivered 11,926 lines.
3. It re-prices a candidate chapter, which is what the comment at
   `dev/ledger.toml:250` claims the field is for.

If the orchestrator prefers the raw module rate with no tolerance for a
budget, the figure is [69.1, 102.4]. But the precedent included the tolerance
(0.013193 = 0.011472 x 1.15), so [79.4, 117.7] is the consistent correction.
INFERRED that the tolerance belongs; the precedent is MEASURED at
`LJ-1.6.md:67-70`.

## 5. DD24'S AXIS (DD4)

`[LJ-1.262]` section 7 fixes the two axes: Def against J is Devlin's axis;
L against the ambient class is the port's axis
(`agents/tasks/LJ-1-262/lj-1.262-report.md`, section 7, citing
`dev/literature/devlin-II5.md:375`, `:387-389`).

**DD24's bar is on the L-vs-ambient axis, the port's axis.** It is the
delivered L = AC wing's seconds per line, which is Def-tower content measured
against the ambient class. The GCH wing it judges is the SAME tower against
the SAME ambient class: its masters are `src/L/*` and `src/V/*`
(`agents/tasks/LJ-1-218/lj-1.218-report.md`, section 1 per-master rows).

So the bar is applied on the same axis it was measured on. It does NOT commit
the defect `[LJ-1.262]` found, which was applying a Def-vs-J mark to an
L-vs-ambient figure. The two axis definitions are MEASURED. The conclusion
that the bar is applied on-axis, with no mix, is INFERRED from them and from
both wings being Def-tower content.

The brief's premise "DD24's bar is an AC-side figure applied to the GCH side,
so it is a cross-tower comparison by construction" is INACCURATE. AC and GCH
are two wings of ONE tower, the internalization Def tower. The two towers are
Def and J. DD24's bar never crosses that line. INFERRED.

## 6. EVERY NEGATIVE, CLASSIFIED

| negative | class |
|---|---|
| 0.013193 is DD24's bar | MEASURED FALSE. It is 0.011472 x 1.15, four re-measurements old |
| 0.013193 was re-based by DD26 | MEASURED FALSE. 0.011472 already used the 16,897 denominator |
| the budget [99.6, 147.7] is live | MEASURED FALSE. It rests on the stale 0.013193 |
| 0.007913 is the caliber the wing is measured at | MEASURED FALSE. The wing is module-slice; 0.007913 is whole-cone |
| the three rates reduce to one another | MEASURED FALSE. 0.013193/1.15 and 0.007913x1.15 are both near but not equal to the others |
| the gap is 28 s | MEASURED FALSE as the right answer. Stale bar |
| the gap is 76 s | MEASURED FALSE as the right answer. Drops the 1.15 tolerance |
| the gap is 91 s | MEASURED FALSE as the right answer. Whole-cone bar on module-slice seconds |
| the gap is 60.0 s | MEASURED as raw seconds; an upper bound by load, INFERRED |
| the a-priori band is DD24's denominator | MEASURED FALSE. It is DD5 measure 2's projection denominator |
| DD24's bar is on the Def-vs-J axis | MEASURED FALSE. It is on the L-vs-ambient axis |
| DD24's bar commits the [LJ-1.262] axis defect | INFERRED FALSE. Both wings are one tower against ambient |
| the module-to-cone caliber ratio equals the 1.15 tolerance | MEASURED FALSE. The ledger records it at 1.45x, 1.31x, then about 1.04x |
| I ran Agda, edited a master, committed or pushed | MEASURED FALSE. None of these |

## 7. ARCHIVE USED (DD18)

One line read named per archived file.

- `agents/tasks/archive/LJ-1-6/lj-1.6-review.md` (the [LJ-1.6-R] report),
  read WHOLE. **Line read `:272-274`**, the wing budget 99.6 to 147.7 s derived
  from "DD24's bar" 0.013193. **TOOK:** where 0.013193 entered the record and
  what it was used to compute.
- `agents/tasks/archive/LJ-1-6/LJ-1.6.md`, read at `:58-80`. **Line read
  `:67-70`**, "0.011472 s per line at the module caliber, times 1.15, so
  0.013193." **TOOK:** the origin of 0.013193.
- `agents/tasks/archive/LJ-1-1/lj-1.1-recon.md`, read section 6. **Line read
  `:217`**, "Total | 7,553-11,197 | Block sum". **TOOK:** the a-priori band's
  basis, the block sum.
- `archive/dev/TASKS-archived.md`, read for SHAPE only. **Line read `:253`**,
  `[L3.32-T249]` "0.0113 s per line whole, not 0.0603 from a slice". **SHAPE
  TAKEN, no claim:** the retired task archive carries per-site rates, never a
  wing-wide quality bar. The bar's first statement is not there.
- `archive/dev/DECISIONS-archived.md`, read for SHAPE only. **Line read
  `:46`**, the retired D24 "Every rule has one home". **SHAPE TAKEN, no
  claim:** the retired D-series numbering does not correspond to the live DD
  series (noted at `dev/PLAN.md:246`). The D-series D24 is governance, not the
  quality bar. The bar's first statement is in the live DD24 row, not in the
  retired D series.

## 8. LITERATURE USED (DD18)

Nothing in the literature governs a check-cost bar; DD24 is a project ruling,
not mathematics, so no digest was read for this question.

## 9. CHECKERS

| checker | result |
|---|---|
| `scripts/lint-prose.py --check` on this report | exit 0 |
| `make check` | NOT RUN, by the brief |
| agda | NOT RUN, by the brief. Two siblings hold both slots (C-12) |
