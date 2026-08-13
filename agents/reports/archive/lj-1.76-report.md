# LJ-1.76: build the split composition as masters

Status: COMPLETE, written incrementally per C-22. No commit, no push.
ASD-STE100. This report is `_build/lj-1.76-report.md`.

## 0. THE VERDICT

**THE THREE MASTERS ARE GREEN, AND THE PRODUCTION SHAPE IS ABOUT FIVE
TIMES CHEAPER THAN THE PROBE PRICE.** The two six-row partials and the
composer all check green at the C-12 cap, one process each. The composer
produces the twelve-row agreement in both directions by applying the
partials' `out`/`back`; it does not re-apply the rows. The vacuous
`TwelveAgree` submodule is removed from `src/L/Condensation.lagda.md`,
backed up outside the repository. The three new masters total
**53.20 s** across three invocations, against the brief's measured target
of about 274 s. The gap is MEASURED and it is a DD4 win: the probes
re-copied about 6,000 lines of row machinery per file; the masters import
the row agreements from the already-green master.

Per the pre-fixed abort criterion (D-1): all three masters green, so this
dispatch STOPS at the measurement. Nothing is wired: `SatGraphAgree`,
`LeafAgree`, `levelIn` and `cover` are untouched.

## 1. THE THREE MASTERS AND THEIR COLD SECONDS

Caliber: `GHCRTS="-A64m -I0 -M8g"`, one process, warm dependencies, cold
target file (no stale `.agdai`; the edited master's stale interface was
moved aside first, per P-p). Load from `uptime` before and after each run.

| master | rows | facts | result | seconds | load (start / end) |
|---|---:|---:|---|---:|---:|
| `src/L/Condensation/LowerAgree.lagda.md` | 0-5 | 43 | green, exit 0 | 20.64 | 6.69 / 6.08 |
| `src/L/Condensation/UpperAgree.lagda.md` | 6-11 | 43 | green, exit 0 | 11.23 | 8.38 / 7.98 |
| `src/L/Condensation/TwelveAgree.lagda.md` | all | 69 | green, exit 0 | 21.33 | 7.98 / 6.73 |

Edited master and its consumer, same caliber:

| file | result | seconds | load (start / end) |
|---|---:|---:|---:|
| `src/L/Condensation.lagda.md` (after removal) | green, exit 0 | 102.38 | 11.20 / 8.69 |
| `src/L/BoundedSubset.lagda.md` (consumer) | green, exit 0 | 15.12 | 6.73 / 6.42 |

The three new masters total **20.64 + 11.23 + 21.33 = 53.20 s**. The
brief's about-274 s target was built from the `[LJ-1.75]` probe figure of
122.45 s per partial, and that figure carried the probe's re-copied row
machinery. The masters import `MemAgree` through `ExInAgree` from
`L.Condensation`, so each partial pays only its telescope and its six row
applications. Every per-process peak stays far below the measured
nine-row wall, so the split's wall-avoidance property holds by
construction.

## 2. THE COMPOSER'S TWELVE-ROW AGREEMENT

The composer is `src/L/Condensation/TwelveAgree.lagda.md`, module
`L.Condensation.TwelveAgree.AbstractFrame`. It takes the full sixty-nine
facts at the abstract environment `γ'`, applies the two partials, and
states:

- `p0b` at `:245` is `LowerAgree.sixB` (rows 0-5) and `p1b` at `:256` is
  `UpperAgree.sixB` (rows 6-11), so `twelveB` at `:267` is the twelve-row
  conjunction `p0b ∧̇ p1b`.
- `out : ⟨ γ' ⊨ twelveAt (suc (suc zero)) (suc zero) zero ⟩ → ⟨ γ' ⊨ twelveB ⟩`
  at `:270`, whose body applies `LowerAgree.out` and `UpperAgree.out` to
  the full target satisfaction.
- `back : ⟨ γ' ⊨ twelveB ⟩ → ⟨ γ' ⊨ twelveAt (suc (suc zero)) (suc zero) zero ⟩`
  at `:291`, whose body applies `LowerAgree.back` and `UpperAgree.back`
  and reassembles the twelve component satisfactions.

Both directions are produced from the partials' already-proved `out`/
`back`. The composer never re-applies a row module, so P-w's interposition
finding does not bite: the composer narrows each partial to the three
exports it reaches (`sixB`, `out`, `back`), which is P-w class (b).

**Does anything consume it? No.** No file in `src/` imports
`L.Condensation.TwelveAgree`. The composer is delivered-and-unconsumed,
and C-35 applies to it: it is staged, not discharged, until the
orchestrator wires the catalog and a consumer instantiates it. That is
said plainly rather than reported as a discharge.

## 3. THE REMOVAL FROM `src/L/Condensation.lagda.md`

The vacuous `TwelveAgree` submodule (comment plus module, lines 6401-6749
of the pre-edit file) is removed. `[LJ-1.71]` proved its `tagEq`
statement uninhabited at every frame (`src/ProbeLJ171A.agda:142-146`),
so it could never be instantiated and proved nothing; it has zero
consumers. Removing it is removing a statement that was never true, not
deleting content. The composer master now carries the same qualified name
`L.Condensation.TwelveAgree` as a real module.

The backup is outside the repository:
`/private/tmp/bedrock-lj1.76-TwelveAgree-vacuous-backup-2026-08-12.txt`
(349 lines, sha256 `94e542e17d8b35756733af5007b38dba326079ea2bc51e3b19e9db722e6785e0`).
The pre-edit text is also recoverable from `git show dd3aa13:src/L/Condensation.lagda.md`.

## 4. THE GATE'S AGGREGATE

`python3 scripts/check-ratio.py --check` cannot run on this machine. The
tool's own guard fails closed: `pgrep -x agda` exits 3 with "Cannot get
process list" (this environment lacks the `sysmond` service pgrep needs),
so the tool refuses before measuring:

```text
check-ratio: refusing to measure, pgrep cannot verify the process list; the guard fails closed (C-12).
```

exit 1. No aggregate exists to quote, and that is the honest report. The
ceiling it would have judged against, quoted from `dev/ledger.toml`: the
module caliber `ac_baseline_module_rate = 0.011057` over
`ac_baseline_module_lines = 17081` (`:2590-2591`), and the whole-cone rate
`ac_baseline_seconds_per_line = 0.007847` over the 133.45 s measured AC
build (`:2526`). The GCH wing is declared (`:2855-2861`), and it includes
`src/L/Condensation.lagda.md`, whose post-removal cold check is 102.38 s
at the C-12 cap. The refusal is MEASURED machine behavior; no verdict on
the ratio is drawn.

## 5. NEGATIVES AND THEIR STATUS

1. A six-row partial as a master carrying only its own 43 facts walls or
   matches the probe's 122.45 s: **MEASURED FALSE**. Both partials are
   green at 20.64 s and 11.23 s. The probe's price included the re-copied
   row machinery; the masters import it.
2. The composer must re-apply the rows to typecheck: **MEASURED FALSE**.
   It is green at 21.33 s and its body applies only the partials'
   `out`/`back`. The mechanism (an imported function application does not
   re-elaborate the body) is INFERRED from Agda semantics; the green
   result is MEASURED.
3. Removing the vacuous `TwelveAgree` breaks the master or a consumer:
   **MEASURED FALSE**. The edited master is green at 102.38 s and the
   one consumer (`L.BoundedSubset`) at 15.12 s.
4. The removal is a deletion of content: **MEASURED FALSE by
   construction**. `tagEq` is uninhabited at every frame
   (`src/ProbeLJ171A.agda:142-146`), and zero consumers exist. The
   composer replaces the statement with a provable one.
5. The 274 s target transfers to the production masters: **MEASURED
   FALSE**. The three invocations total 53.20 s. The target's
   per-process-peak reasoning still holds: each master is its own
   process, and every peak is far below the nine-row wall.
6. The J tower inherits the split shape's seconds free: **INFERRED, NOT
   MEASURED**. No J-site measurement exists. The shape transfers by
   construction (slot-generic partials and composer); the seconds do not.

The deciding claims are items 1 and 2, both MEASURED.

## 6. THE DD4 ANSWER

The split maximizes shared code at the module boundary: the partials
import the twelve row agreements from `L.Condensation` and never restate
them. That is the measured sixfold saving (20.64 s and 11.23 s against
the probe's 122.45 s) and it is the same generic-frame move P-w's
amendment priced: one frame stated once, used by the twelve rows.

The partials are generic in the slots, MEASURED by construction: both
take the same fifteen slots (`N0` to `N11`, `t0`, `t1`, `K : Fin (5 + n)`)
and the same abstract `γ : S ^ (11 + n)`, with the 43 facts as telescope
hypotheses. No slot was dropped and no row was weakened.

The DD4 trade named by `[LJ-1.75]` stands: the two partials state 86 fact
parameters (the 52 half-specific facts once each, the 17 shared facts
twice), against one union statement of 69. The composer is generic in the
69 facts and slots, so a J tower that states the same telescope at its
own frame could instantiate the same composer verbatim: INFERRED, no
J-site measurement exists, and per `[LJ-1.71]` the J tower still states
its facts at its own frame rather than reusing the L frame's.

## 7. THE CONVERGENCE ANSWER

CLOSING for this dispatch's content, per the pre-fixed abort criterion.
The three masters are green at 20.64 / 11.23 / 21.33 s, the composer
produces the twelve-row agreement in both directions from the partials,
and the vacuous `TwelveAgree` is gone. The composer is
delivered-and-unconsumed: C-35 applies until the orchestrator wires the
catalog. `SatGraphAgree`, `LeafAgree`, `levelIn` and `cover` are
untouched, and the DD24 threshold question is not traded away; the
owner's ruling commits the content now and settles the threshold when the
phase's content is complete.

## 8. ARCHIVE USED

- `_build/lj-1.75-report.md`, read WHOLE. TOOK section 1's fact table
  (the 43/43 split and the 17 shared facts) and section 2's measured
  122.45 s partial. The masters were built from that table.
- `_build/lj-1.74-report.md`, read WHOLE. TOOK the ladder, the
  separate-invocation split shape, the composer probe F (28.98 s), the
  per-process peak verdict and the abort discipline.
- `src/ProbeLJ175A.agda`, read. TOOK the reduced lower partial
  (`TwelveAgree6` `:6386-6510`, `AbstractFrame6` `:6604-6727`,
  application `:6730-6772`), the model for `LowerAgree`.
- `src/ProbeLJ174F.agda`, read WHOLE. TOOK `AbstractFrameSplit`'s
  sixty-nine-fact telescope and the two-direction composition, the model
  for the composer.
- `src/ProbeLJ174C.agda` `:6624-6641` and `src/ProbeLJ174D.agda`
  `:6643-6663`, read. TOOK the rows 6-11 applications, the model for
  `UpperAgree`.
- `_build/lj-1.72-report.md`, read WHOLE. TOOK sections 1a and 1b (the
  per-row telescope repair) and the `someEnvDef` naming cure.
- `_build/lj-1.71-report.md`, read WHOLE, and `src/ProbeLJ171A.agda`,
  read. TOOK the `tagEq` refutation (`:142-146`) that licenses the
  removal.
- `dev/LESSONS.md`, read WHOLE. TOOK C-38 (the acceptance test is the
  instantiation), C-35 (the composer is unconsumed), P-w as amended (the
  composer is class (b), narrowing to the exports it reaches), P-t (the
  facts are telescope hypotheses, not built trees), P-m/P-n (the
  instantiation class is the payable floor), C-12 (the cap), C-22
  (incremental writing), P-p (stale interface moved aside before the
  price), and the remaining briefed rules: P-h, P-k, P-l, P-o, P-q, P-u,
  P-v, P-c, R-35, R-36, R-38, R-40, I-5, C-31, C-32, C-33, C-34, C-36,
  C-37, D-1, D-8, D-10, D-13, D-26, D-29, D-30.
- `dev/STYLE-i18n.md` and `dev/STYLE-agda.md`, read WHOLE. TOOK the
  marker grammar and the master template (OPTIONS header, minimal prose
  under DD23, import discipline).
- `archive/rud-route/`, SHAPE only. Took nothing.

## 9. LITERATURE USED

Nothing in the literature prices a spelling. One line, nothing spent.

## 10. GATES

`scripts/check-fences.py --check` clean (87 masters).
`scripts/lint-prose.py --check` exit 0 on every touched file.
`scripts/lint-agda.py --check` exit 0 on the three new masters and the
edited master.
`scripts/ledger.py --brief`: standing 27,673 lines over 82 masters,
measured from HEAD. The three new masters are untracked (as the probes
are), so they do not move the standing until the orchestrator commits;
their fenced non-blank lines are 246 (LowerAgree), 237 (UpperAgree) and
292 (TwelveAgree), 775 total.
`scripts/check-ratio.py --check` refuses on this machine: its pgrep
guard cannot verify the process list (section 4).
No `make check`, per the brief. No commit, no push.

The working tree carries: the edited `src/L/Condensation.lagda.md`
(minus the vacuous `TwelveAgree`), the new directory
`src/L/Condensation/` (README plus the three masters), and this report.
`src/Everything.lagda.md` and `src/L/Coding/` are untouched.
