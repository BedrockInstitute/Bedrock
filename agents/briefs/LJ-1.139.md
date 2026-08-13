# LJ-1.139: the memo STATUS headers point at a retired era

tier: opus (version `override`, set 2026-08-13; the head for every case is in
`scripts/dispatch_policy.py`, which is the only place the tables live)

## GOAL

**`dev/memos/` carries 21 memos. Each opens with a STATUS header that tells the
reader what is live and where to go instead. Some of those headers now send the
reader to a rule that was revoked.**

Repair the headers. **Do not rewrite the memos themselves.**

## THE DEFECT, measured, and it is the one that started this

**`dev/memos/source-material-survey.md:3` is marked `STATUS: STANDING`** and
says its measurements 「remain the calibration anchor for the **two-caliber
discipline** (`dev/PLAN.md` section 6.2)」.

**`dev/PLAN.md:164` REVOKED the two-caliber rule.** DD7 is revoked outright, a
projection is now ONE best-effort figure naming its basis, and that lives in
DD8. **`dev/PLAN.md:261` is still section 6.2, but it is now titled 「Caliber,
and the single best-effort projection」.**

**So a memo that calls itself STANDING points a reader at a section that says
the opposite of what the memo says it says.**

`dev/memos/route-tree.md:3` has the same sentence. Both were caught when
`[LJ-1.137]` cut the revocation notice out of `AGENTS.md`, whose canonical home
is `dev/PLAN.md:164`. **The cut was correct. It removed the sentence that was
masking these two.**

## WHAT TO DO

1. **Read all 21 STATUS headers.** They are line 3 of each file, in a blockquote.
2. **For each, check every pointer it makes.** A pointer is a `dev/PLAN.md`
   section number, a `D` or `DD` code, a script, or another document. **Check
   that the target exists AND that it still says what the header claims.**
   **The second half is the whole task. A resolving pointer to a reversed rule
   is worse than a dangling one**, because nothing looks wrong.
3. **Fix the header.** Keep the form that is there: what the memo is, why it
   was retired or why it stands, and when to read it.
4. **Re-judge STANDING against SUPERSEDED where the evidence demands it.**
   `source-material-survey.md` may still be STANDING as *evidence* while its
   stated *purpose* is dead. **Say which, and say it in the header.**

## WHAT IS NOT BROKEN, so do not "fix" it

- **A `D` code resolves against `archive/dev/DECISIONS-archived.md`.** The
  whole `D` series was archived on 2026-08-09 and the live series is `DD`, but
  **a `D` citation is not dangling.** `scripts/check-rule-ids.py` is green
  today, MEASURED. **Do not renumber a `D` code to a `DD` code**, and do not
  assume a mapping: several `D` rows merged and some were revoked outright.
- **A memo's BODY is a dated record.** `AGENTS.md`: nobody rewrites an existing
  document. **You touch the header only**, unless a body sentence is a live
  instruction rather than a record, in which case **report it and do not
  change it**.

## THE TEST FOR A HEADER

**A STATUS header exists so a reader can decide, without opening the memo,
whether to read it.** So each must answer three things and nothing more:

1. Is this live, superseded, or wrong?
2. Where does the live rule live NOW?
3. When would I still open this?

**A header that fails 2 is the defect you are here to fix.**

## THE ABORT CRITERION

- **Every header checks out or is repaired**: report the table and STOP.
- **A header's claim cannot be settled** without a ruling on what is live:
  **leave it, list it, and say what would decide it.**
- **A memo turns out to hold a LIVE rule that has no other home**: **STOP AND
  SAY SO.** That is a rule with a broken home, which DD19 forbids, and it is a
  bigger finding than the headers.

## WHAT YOU MUST NOT DO

- **Do not rewrite a memo body.**
- **Do not archive or delete a memo.** Retirement is priced from the rewrite
  side and is the owner's call.
- Do not edit `AGENTS.md`, `dev/PLAN.md`, `dev/LESSONS.md` or
  `dev/ORCHESTRATION.md`. **If one of them is what is wrong, report it.**
- Do not touch `src/`, do not run Agda. **A sibling is measuring build times.**
- Never commit, never push, never `git checkout .`, `git stash`,
  `git reset --hard` or `git clean`. **Two siblings hold uncommitted work.**
- Do not run `make check`; I run it.

## THE CLASSIFICATION I WANT ON EVERY NEGATIVE

**MEASURED or INFERRED, in those words.** 「This pointer resolves」 is MEASURED
only if you opened the target and read it.

## ARCHIVE (DD18)

- **`dev/PLAN.md:157-320`**, the pointer sections. Every memo was moved out of
  PLAN by `[L3.32-T113]` and the pointer sections are its other half.
- **`dev/PLAN.md:164`** and **`:261`**, the revocation and section 6.2 as it
  reads now.
- `archive/dev/DECISIONS-archived.md`, for what each `D` code says.
- `agents/reports/archive/lj-0.1-consistency.md` and `lj-0.2-sufficiency.md`.
  **Both audited this class of defect before and both name the two-caliber
  passages. Read what they found and say what they missed, because the defect
  survived them.**

Return an **ARCHIVE USED** section at `file:line`.

## LITERATURE (DD18)

**Nothing in the literature governs a memo header. Say so in one line.**

## SCOPE (read)

`dev/memos/*.md` line 3 of each, FIRST. Then `dev/PLAN.md` sections 2 to 10.

## SCOPE (write)

**`dev/memos/*.md`, the STATUS header only.** Your report is
`agents/reports/lj-1.139-report.md`.

## MANDATORY RULES

Run `.venv/bin/python scripts/rules.py --for rewrite` and read every
statement.

- **C-22.** Write the deliverable incrementally.
- **C-36.** Write the term you could not write.
- **C-40.** Verify the CONSUMERS: `check-rule-ids.py` reads these files.
- **C-31, C-32, C-33, C-34, C-37, C-39, D-10, D-26, D-29.**

## CONSTRAINTS

- Run `.venv/bin/python scripts/lint-prose.py --check dev/memos/` and
  `.venv/bin/python scripts/check-rule-ids.py`. **Both must be green.**
- **No em dash, in any language.** These files are English.
- Evidence is `file:line`. Write ASD-STE100.

## RETURN

**Lead with the count: headers checked, headers repaired, pointers that
resolved to a reversed rule.** Then the table: memo, what was wrong, what it
says now. Then any memo whose STANDING or SUPERSEDED verdict you changed, with
the reason. Then anything you could not settle. **Mark every negative MEASURED
or INFERRED.**
