# Adversarial review of LJ-1.710#2

## HEAD

head_slot: coder
machine: shared
task: LJ-1.710, review of instance 2
verdict: **upheld**

## WHAT THIS REVIEW ATTACKED, AND WHERE ITS FACTS COME FROM

Instance #2's return, as this checkout holds it. This worktree carries no
transition line for the task: `grep -c '"task": "LJ-1.710"'` over
`dev/pod/transitions/2026-08.jsonl` returns 0, and that tracked file ends at
line 4618 with dispatch seq 4617 of task LJ-1.692. As the brief allows, every
fact below comes from the acceptance arms or not at all.

The three arms say what each round left in the tree:

- `runs/accept-1.out`: instance #1 changed 21 of its 21 own scope files;
  `:15` conjunct 6 FAILED; `:18`; `:22` error class lint.
- `runs/accept-2.out`:9 started 17:10:24; `:15` conjunct 6 FAILED; `:18`
  changed files own 1 of 22, and the JSON names the one file:
  `agents/tasks/LJ-1-710/review-of-LJ-1-710-1.md`.
- `runs/accept-3.out`:9 started 17:26:34; the same four lines (`:15`, `:18`,
  `:22`) carry identical values, and both `lint_detail` strings are the same
  single defect.

So the attackable body of instance #2, in writing, is exactly
`agents/tasks/LJ-1-710/review-of-LJ-1-710-1.md`, together with the frozen
instance #1 return it adjudicates (`lj-1.710-report.md`,
`Probe710.agda`, `review-of-bound2-in-limit.md`). Nothing else appeared or
changed under the task home between arm 1 and arm 3. This review answers
section 6.6's three questions against that pair. The lens is this slot's
clauses; this brief's pointer to design memo lines 2853 to 2858 still names a
sample brief, so the live list at `dev/memos/LJ-4-pod-program-design.md:3064`
to `:3068` is what gets answered here.

## QUESTION 1. Does the verdict LINE match its own BODY?

**Yes, on both layers instance #2 delivered.**

Layer A, instance #2's own judgement: its HEAD states `verdict: upheld`
(`review-of-LJ-1-710-1.md`, first section) and the body delivers exactly an
uphold with named defects: question 1 answered yes with one label drift, the
stale final.out decimal pair, a split answer on completeness, a stop section
on the survey lock, and a VERDICT section that upholds while naming the defects
it found. Line and body agree.

Layer B, the NO-GO that instance #2 let stand: `lj-1.710-report.md:10-13`
states NO-GO on the obligation plus a green frame and merge beside it, and the
body still matches that split when every measurement is re-read today:

- `runs/t-e1.out:5-9`: `[UnequalTerms]`, `L.Ordinal.f σ₁ σ₂ o₁ o₂ x != mf x`,
  against the goal `< fst (bound2 σ₁ σ₂ o₁ o₂) ∈ₛ α ⟩` (`:10`). EXIT=42 at
  `:29`. Re-read today, unchanged.
- `runs/t-paths2.out:5-8`: `[NotInScope]` for `L.Ordinal.bound2.f`. Unchanged.
- `runs/t-selflambda.out:5-6`: the same inequality against a locally written
  clause function. Unchanged.
- `runs/t-small.out:5-6`: 1.37 real, 278364160 bytes; EXIT=0 at `:23`.
  Matches the report's price line.
- The obligation stays open: `accept-2.out` records `obligations_open: 1`,
  delta 0, and the probe was re-run rc 0 in both later arms (`:16`).

One label drift stands where instance #1 left it: `lj-1.710-report.md:9` names
the term `Probe710.agda::the-obligation`, while the work brief's canonical
name is `bound2-in-limit` (`agents/tasks/LJ-1-710/LJ-1.710.md:20`), and
`Probe710.agda:93` defines `the-obligation` as the statement typed verbatim.
Disclosed on every side already; no contradiction between any verdict line and
its body.

## QUESTION 2. Is every load-bearing claim backed by a `file:line` that resolves today?

**Yes. Every citation instance #2 loads on was re-opened today and resolves.**
Against its stops and mines:

| claim | cited | reads today |
|---|---|---|
| refl wall, predecessor form | `agents/tasks/LJ-1-705/runs/p-26.out:5-8` | `f x != L.Ordinal.f σ₁ σ₂ o₁ o₂ x` at `:6`, against `refl` of type `bound2 ... .fst ≡ β` at `:8` |
| source premise | `src/L/Ordinal.lagda.md:185` | `bound2 :` Σ-type; the where-bound family sits at `:190-191` |
| trimmed floor | `runs/t-small.out:5-6` | 1.37 real / 278364160 B |
| the three questions live | `dev/memos/LJ-4-pod-program-design.md:3064-3068` | present verbatim |
| conjunct 6 passes the bare code | `scripts/pod/accept.py:235`, `:273` | `_run(SURVEY_QUOTES + [code], ...)`, constant at `:99` |
| checker picks its own pair | `scripts/pod/check-survey-quotes.py:421-441` | `brief_of` at `:421`, `report_of` at `:427`, whose docstring says a review companion "is another dispatch's return and is not judged here" |
| suffix pinning | `scripts/agents_tree.py:72` | `REPORT_SUFFIXES = ("-report", "-review")` |
| task-scoped rows outrank system rows | `scripts/pod/table.py:607-612` | `sort_key` step two at `:611` |
| R4 gate for a NO-GO close | `scripts/pod/accept.py:364-382` | need `(5, 6)` for outcome `no-go` at `:371-372` |
| the frozen-record rule | `agents/README.md:107-109` | "Nobody edits a file in this tree." |
| the lint row | `dev/pod/table.toml:35411-35423` | id at `:35411`, `exit_code = 1` + lint at `:35421-35423` |

Stale content survives only where instance #2 already filed it: the
final.out decimals. Today `runs/final.out:5-6` reads `1.50 real` and
280887296 bytes, against `lj-1.710-report.md:13,41,95` claiming 1.43 s and
280788992 bytes. Green status itself triple-witnesses: `runs/final.out:23`
EXIT=0, rc 0 rerun recorded in both later arms. A stale-decimal citation,
already on the record; not grounds to overturn anything.

No claim of instance #2 rests on a `file:line` that fails to resolve today.

## QUESTION 3. Is the enumeration complete?

**Complete where instance #2 could reach. One instrument fact added below,
and it does not change its conclusion.**

Its mathematical enumeration was already complete and needs no addition from
me: five routes off the ridge, each dead on a named wall (refl
`p-26.out:5-8`; elaboration unification `t-e1.out:5-9`; qualified reference
`t-paths2.out:5-8`; local twin `t-selflambda.out:5-6`; index-splitting, which
works and closes everything but parity). No sixth strategy exists for a
statement whose right side has no referable symbol.

Its lock diagnosis also re-measures clean today, and sharper than before:
importing the checker directly now shows `brief_of` returning
`agents/tasks/LJ-1-710/LJ-1.710.md` and `report_of` returning
`agents/tasks/LJ-1-710/lj-1.710-report.md`, with findings exactly
`['unanswered: the return never names dev/literature/primary-sources.md']`.
Two mechanical details sit behind that choice:

1. `report_of` first tries a stem match `task.name.lower() + "-report"`
   (`check-survey-quotes.py:430-433`), which for directory `LJ-1-710` spells
   `lj-1-710-report`, missing the dotted `lj-1.710-report`; the fallback then
   returns the same file as the first sorted report-suffix document. Same
   winner either way: the frozen instance #1 return.
2. Because the judged text is fixed, `findings()` can emit only that one
   defect, forever, for every future writer. `review-of-LJ-*-*.md` is
   excluded from the judged pair BY DESIGN (its own docstring), which is why
   instance #2's compliant writing moved nothing and why this review cannot
   move it either.

Row arithmetic, re-measured: `sys-critic-upheld-no-go` requires
`exit_code = 0` (`dev/pod/table.toml:4318`); conjunct 6 red forces exit 1 and
class lint into the priority 13 task row (`table.toml:35411-35423`), and R4
demands conjuncts 5 AND 6 before any NO-GO close (`accept.py:371-372`). So no
return can close this task while the judged pair stays frozen. Arms 2 and 3
are the measured recurrence, twice.

Instance #2 listed two owner cures; both stand. For completeness I add a third
family it did not reach: an instrument-side cure, changing the CALLER rather
than any record, namely having the runner pass the DISPATCH'S OWN brief/report
pair explicitly (`--brief/--report` already exist at
`check-survey-quotes.py:463-477`) instead of letting the checker re-derive a
pair by sort order. That is a maintainer call on program code and outside
every slot's write scope; it is filed here as evidence, not built by me.

Pre-commit re-run from this worktree, after this file's final save, with the
repository venv: the six pinned members pass (`lint-agda`, `lint-prose`,
`glossary`, `fences`, `probes`, `markers`, each rc 0), and the bare-code form
of the survey gate still exits 1 with the single defect above. The hygiene red
is exactly and only the pair-choice question.

## VERDICT

Upheld. Instance #2's uphold of instance #1's NO-GO on `bound2-in-limit`
stands: the obligation reduces to name parity with a where-bound family no
probe can reference or convert, five walls measured green-today, a src-side
cure stated in `review-of-bound2-in-limit.md`. No new defect exists in
instance #2 beyond what it already filed. The residual survey defect cannot be
closed by any dispatched writer; its mechanics, the recurrence, and three cure
options (owner edit, ruling amendment, explicit-pair caller change) stand
recorded above with `file:line`.

## ARCHIVE USED

Union coverage: this block answers every candidate injected into BOTH briefs
this chain could be judged against, the work brief and this reviewer brief.

- `archive/dev/ORCHESTRATION.md` not used, declined: archived orchestrator rules bear nothing on elaborator conversion walls or checker mechanics.
- `archive/dev/DD-archived.md` not used, declined: governing clauses live in AGENTS.md and the slot file.
- `archive/dev/PLAN-archived.md` not used, declined: retired planning holds nothing this review needs.
- `archive/dev/STATUS-archived.md` not used, declined: a retired goal table, not this route.
- `archive/dev/TASKS-archived.md` not used, declined: a retired task index, not this route.
- `archive/dev/measurements/README.md` not used, declined: every price cited here resolves under live `runs/` directories.
- `archive/dev/README.md` not used, declined: the retired route is not this route.

## LITERATURE USED

- `dev/literature/primary-sources.md:23-24` "Extraction note: the Dev chapters are OCR scans (ABBYY), so math glyphs are degraded". Read. This is the skipped path that escalated the whole chain: it confirms the classical truth side of D-10 rests partly on rescans held outside the tree, so instance #1's D-10 note correctly kept the obstruction a naming fact, not a truth fact.
- `dev/literature/level-formula-slot-roles.md:35` "The free pair is the VALUE and the ORDINAL, in every source". Read. Bears on the reopen-cure: the consuming staging formula leaves exactly value and ordinal free per merge slot, the shape `bound2OwnLimit` supplies once the src-side family symbol exists.
- `dev/literature/BIBLIOGRAPHY.md` declined, not used: no external citation enters this review beyond the two digests above.
- `dev/literature/devlin-errata.md` declined, not used: no classical text claim is restated here beyond the D-10 note already sourced.
- `dev/literature/glossary-review-2026-08.md` declined, not used: terms come from the live glossary files, not the archived review round.

Standing paths, declined together, none read: `archive/dev/JOURNAL-archived.md`,
`archive/dev/JOURNAL.md`, `archive/dev/LJ-dispatch-index.md`,
`archive/dev/DECISIONS-archived.md`, `dev/ARCHIVE.md`,
`dev/literature/truncation-and-selection.md`, `dev/literature/devlin-II5.md`,
`dev/literature/digest.md`, `dev/literature/terms-2026-08.md`,
`dev/literature/geology.md`. None bears on an elaborator conversion wall, on
checker pair selection, or on the three questions this file answers.
