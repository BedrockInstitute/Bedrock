# LJ-1.133: give the probes a lifecycle, and settle where evidence lives

tier: opus (version `override`, set 2026-08-13; the head for every case is in
`scripts/dispatch_policy.py`, which is the only place the tables live)

## GOAL

**283 probe files sit in `src/`, none of them tracked.** The owner's ruling:
a probe should be deleted or archived once its mission is done. **But 244 of
them are cited by a report, so they are evidence, and evidence must stay
checkable.**

## CWD

`/Users/alsg/Agentic/Bedrock`, branch `two-tower-bridge`. Reports are in
`agents/reports/`, briefs in `agents/briefs/`.

## WHAT IS MEASURED, by the orchestrator before you started

| | |
|---|---|
| Probes on disk, `src/*.agda` | **283**, 9.1 MB |
| Tracked by git | **0**, and `.gitignore:27` covers `src/**/*.agda` |
| **Cited by a report** | **244** |
| **Cited by nothing** | **39** |

The citation count came from `grep -rF <basename> agents/reports/`, the same
test `scripts/check-probes.py`'s `stale_probes()` uses.

## THE TENSION, AND IT IS THE WHOLE TASK

**`scripts/check-probes.py` exists to stop a probe entering git.** Read its
docstring: on 2026-08-04 one `git add -A src/` committed 13 probe files,
3,274 lines, which had to be untracked afterwards. **An ignore rule is a
default, not a gate; `git add -f` walks past it.** So the checker is the
gate, and it runs on tracked files AND on staged files.

**But a probe that a report cites has stopped being a probe.** It is the
evidence for a `file:line` claim, and this project's entire discipline is
that a claim is checkable. **Today those 244 files live in an untracked
directory that `make clean` or a stray command can take away.**

**So the tree currently does neither thing well: it does not throw probes
away, and it does not keep the evidence safe.**

**Your job is to resolve that, not to pick a side.**

## WHAT TO DECIDE, and I want your reasoning not just your answer

1. **Is a cited probe evidence, or is the REPORT the evidence?** A report
   quotes the term and gives its `file:line`. **If the report is
   self-sufficient, the probe can go and the citation becomes historical.
   If it is not, the probe must be kept and tracked.** Read several reports
   and their cited probes and answer from what you find. **This is the
   question everything else turns on.**
2. **If probes must be kept: where, and how does `check-probes.py` learn the
   difference** between a probe in flight and a probe that has become
   evidence? The orchestrator's guess, which you may overrule: cited probes
   move to `agents/reports/probes/` and the checker's rule becomes "no probe
   under `src/`", which is the rule that actually protects the tree.
3. **What about the 39 uncited ones?** `stale_probes()` already has a
   freshness rule: six hours, so a probe a live agent is using is not
   deleted. **Apply it. Say how many were fresh and therefore kept.**
4. **Citations.** If any probe moves, every `file:line` citing it must
   follow. `[LJ-1.130]` rewrote 283 citations for the reports move; this is
   the same problem in miniature. **Count them before you move anything.**

## COORDINATE WITH THE LIFECYCLE REGIME

`[LJ-1.132]` is defining a lifecycle regime for `_build/`: every temporary
file declares, at creation, when it may be deleted and when it moves
somewhere permanent. **Read `agents/reports/lj-1.132-report.md` before you
design anything.**

**A probe is the same species of object.** Use its classes if they fit, and
say so. **If they do not fit, say why, because two regimes for one problem
is worse than one imperfect regime.**

## THE ABORT CRITERION

- **The question in point 1 resolves cleanly**: act on it, report the counts,
  STOP.
- **It does not resolve**: **do not move or delete anything.** Report what
  you found and what would decide it. **An honest undecided beats a wrong
  deletion, and a deleted probe is unrecoverable.**
- **`check-probes.py` cannot be taught the difference safely**: say so, and
  say what the cost of keeping the current arrangement is.
- **Anything walls**: STOP, report it.

## WHAT YOU MUST NOT DO

- **Do not delete a probe that any report cites**, unless point 1 resolves
  that the report is self-sufficient AND you say so explicitly.
- **Do not weaken `check-probes.py`'s protection of `src/`.** That rule was
  bought with a real incident.
- **Do not touch `src/*.lagda.md`.** Those are masters, not probes.
- **Do not touch `_build/2.8.0/`.**
- Do not edit `AGENTS.md`. DD19: propose the line, the owner rules. **The
  Never list names probes explicitly, so this task probably needs a word
  there.**
- Never commit, never push, never `git checkout .`, `git stash`,
  `git reset --hard` or `git clean`.
- Do not run `make check`; the orchestrator runs it. **Do not run Agda:**
  283 probes are not worth a rebuild, and C-12 caps you anyway.

## THE CLASSIFICATION I WANT ON EVERY NEGATIVE

**MEASURED or INFERRED, in those words.** "Nothing cites this probe" is
MEASURED only if you ran the search and say which search.

## ARCHIVE (DD18)

- **`scripts/check-probes.py`**, read WHOLE, especially the docstring and
  `stale_probes()`.
- **`agents/reports/lj-1.132-report.md`**, the lifecycle regime.
- `agents/reports/lj-1.130-report.md`, the reports move and its citation
  rewrite.
- `dev/LESSONS.md` **D-1**, the probe doctrine, read WHOLE.
- `dev/ARCHIVE.md` and `archive/README.md`, for what an archival record must
  carry.

Return an **ARCHIVE USED** section at `file:line`.

## LITERATURE (DD18)

**Nothing in the literature governs a probe directory. Say so in one line.**

## SCOPE (read)

`scripts/check-probes.py` FIRST, then several report and cited-probe pairs,
then `agents/reports/lj-1.132-report.md`.

## SCOPE (write)

`src/Probe*.agda` and `src/*.agda` for deletion or moving only,
`scripts/check-probes.py`, `.gitignore`, and wherever you rehome. Your report
is `agents/reports/lj-1.133-report.md`.

## MANDATORY RULES

Run `python3 scripts/rules.py --for rewrite` and read every statement.

- **D-1.** The probe doctrine: the smallest decisive miniature, then throw it
  away. **Read it whole, because this task tests exactly where "throw it
  away" stops.**
- **C-22, C-36, C-39, C-40, D-10, D-26, D-29, D-30.**
- **C-31, C-32, C-33, C-34, C-37.**

## CONSTRAINTS

- Run `scripts/lint-prose.py --check` on anything you write.
- Evidence is `file:line`. Write ASD-STE100.
- **Report sizes and counts before and after.**

## RETURN

**Lead with the answer to point 1**, with the reasoning and the reports you
read to get it. Then the counts: deleted, moved, kept fresh, citations
rewritten. Then how `check-probes.py` changed and what it now protects. Then
whether the `[LJ-1.132]` classes fitted. Then the `AGENTS.md` line you
propose. **Mark every negative MEASURED or INFERRED.**
