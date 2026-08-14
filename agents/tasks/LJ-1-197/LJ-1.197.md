# LJ-1.197: do `build-manifest.toml` and `rules.toml` actually FIRE when they should

tier: pi (deepseek-subagent-mode), **model `deepseek-v4-flash`**, by the owner's
rule of 2026-08-14: work that touches no Agda code takes flash.

## GOAL

**Two configuration files carry rules. The owner asks whether those rules are
LANDED, and defines landed as: it TRIGGERS at the moment it should.**

- `dev/build-manifest.toml`, read by `scripts/check-build-manifest.py`
- `dev/rules.toml`, read by `scripts/rules.py` and validated by
  `scripts/check-rule-ids.py`

**Present in the tree is not landed. Green is not landed. FIRING when it should
is landed.**

## THE METHOD: PROVOKE EACH RULE, do not read it

**For every rule either file carries, construct the violation it exists to
catch, run the checker, and record whether it FIRED.** Then undo the violation.

**A rule you only READ is a rule you did not test.** This project has now
measured four checkers that were green while the thing they guard was broken:
a dispatch path that refused every brief for days, a series check that verifies
resolution and never uniqueness, a `--staged` filter that missed 257 renames,
and an archive section obeyed in FORM while its content decayed.

**Clean up after every provocation.** Leave the working tree exactly as you
found it, and say so in your report. **`scripts/check-live-territory.py` is now
a gate; do not stage anything.**

## WHAT `dev/build-manifest.toml` CLAIMS

It declares a CLASS for every file under `_build/`, and `AGENTS.md` states the
rule it serves: **never leave an undeclared file in `_build/`; declare its class
when you create it, or move it to a permanent home.**

**Questions to answer by provocation:**

1. **Does an undeclared file in `_build/` make the checker fire?** Create one,
   run it, delete it.
2. **Is the checker a GATE or a REPORT?** Its own last line said 「Advisory only.
   This is not a gate.」 **Then it fires and nothing stops.** Say whether that
   matches what `AGENTS.md` promises, and whether `make check` runs it at all.
3. **MEASURED 2026-08-14: it caught a real violation.** The orchestrator created
   `_build/briefs/` and the checker listed those files as undeclared. **Nothing
   failed and nothing blocked; the owner caught the mistake, not the tool.**
   Confirm that account and say what it means for the rule's enforcement.
4. **Are any classes DEAD?** A class no file has used since it was declared is a
   rule with no subject.

## WHAT `dev/rules.toml` CLAIMS

It routes mandatory rules to task kinds, capped at `max_ids = 12` per bundle,
plus a trigger tail resolved by `rules.py --grep`.

**Questions to answer by provocation:**

1. **Does the CAP fire?** Add a thirteenth ID to a bundle in a scratch copy and
   run `rules.py --check`. **The cap is called 「THE DESIGN」 in the file's own
   header: a bundle that cannot fit a new law must EVICT one.**
2. **Does a dangling ID fire?** Put a fake ID in a bundle and in a trigger.
3. **Does the kind DERIVATION work?** The file says the kind is derived from the
   brief's write scope and never self-declared, because an author who picks the
   kind picks the bundle. **`dispatch.py` refuses a brief missing its kind's
   bundle, and it refused `[LJ-1.188]`'s brief for three missing rules on
   2026-08-14.** Confirm the derivation on at least three briefs of different
   kinds and say whether the kind it derives is the one a reader would.
4. **DO THE TRIGGERS RESOLVE?** `rules.py --grep <term>` for every term in
   `[triggers]`. **A trigger that returns nothing is a rule that cannot be
   reached.**
5. **IS ANY ROUTED RULE UNREACHABLE IN PRACTICE?** A rule in no bundle and under
   no trigger is present and unreachable. **Count them.**

## THE HARDEST QUESTION, and it is the owner's real one

**Both files encode rules whose enforcement point is 「the orchestrator, at
brief-writing time」 or 「review」.** `dev/rules.toml`'s own header says that is
exactly why it was built: **「the orchestrator is exactly the component that
drifted for five days.」**

**So: for each rule in each file, name the MOMENT it must fire, and say whether
anything fires at that moment.** A rule that fires only when somebody runs a
command by hand fires when that person already suspected something.

## THE ABORT CRITERION, fixed BEFORE the run (D-1)

- **ALL FIRE.** Report the provocation table: rule, violation constructed,
  checker run, fired or silent. STOP.
- **SOME DO NOT FIRE.** **That is the finding.** Rank by what the silent rule
  guards.
- **A RULE CANNOT BE PROVOKED.** Say why. **A rule whose violation cannot be
  constructed may be unfalsifiable rather than safe**, and naming one is worth
  more than a green table.

## WHAT YOU MUST NOT DO

- **Do not edit `dev/build-manifest.toml`, `dev/rules.toml`, any checker, any
  `dev/` document, `src/`, or any brief or report but your own.** **This is an
  audit.** Report every fix you would make; make none.
- **Do not stage anything and do not commit.** A gate now watches for staged
  files in a live agent's territory.
- **Do not run Agda and do not dispatch an agent.** Two siblings are live and
  one holds an Agda slot.
- Never `git checkout .`, `git stash`, `git reset --hard` or `git clean`.
- Do not run `make check`; the orchestrator runs it.

## THE TRAP THIS PROJECT PAID FOR FIVE TIMES ON 2026-08-14

**A search that excludes what it looks for**, and its newest instance is one
hour old and inside the dispatch skill itself: a claim was written MEASURED on
the strength of a `--help` listing, when the claim was about BEHAVIOUR. **The
flag was accepted and silently ignored.**

**So: test behaviour, never documentation. Say which command you ran for every
「it fires」 and every「it does not」.**

## THE CLASSIFICATION I WANT ON EVERY ANSWER

**FIRES, SILENT or UNPROVOKABLE, in those words**, and **MEASURED or INFERRED**
on each.

## DD4

**Maximize the code the two proofs share, and write it generic.** One rule, two
ends, no metric and no checker.

**Here DD4 is one of the subjects: it is routed by `rules.toml` into the build
bundle and it is the one rule with NO metric by ruling.**
`scripts/check-dd4-stated.py` now gates that a brief SAYS it. **Provoke that
gate too, and say whether the bundle routing and the gate agree about which
briefs must carry DD4.**

## ARCHIVE (DD18)

- **`dev/rules.toml` WHOLE**, header included. **Its header is the argument for
  its own existence and it names the drift it was built against.**
- **`dev/build-manifest.toml` WHOLE**, header included.
- **`scripts/rules.py`, `scripts/check-build-manifest.py`,
  `scripts/check-rule-ids.py`, `scripts/check-dd4-stated.py`**, read WHOLE.
- `scripts/README.md`, for what each checker claims to enforce.
- `AGENTS.md`'s 「Where the rules live」 table: **several rows are marked
  PARTIAL, and that column is the project's own admission of this exact
  question.** **Check whether the PARTIAL marks are still accurate.**

Return an **ARCHIVE USED** section at `file:line`.

## LITERATURE (DD18)

**Not this task's subject. Say so in one line.**

## SCOPE (read)

`dev/rules.toml` and `dev/build-manifest.toml` FIRST, headers included.

## SCOPE (write)

`agents/tasks/LJ-1-197/lj-1.197-report.md` ONLY. **A scratch copy for a
provocation goes in `agents/tasks/LJ-1-197/` and is deleted before you finish.**

## MANDATORY RULES

Run `python3 scripts/rules.py --for review` and read every statement.

- **C-22.** Write your deliverable incrementally, never at the end.
- **C-42.** A refutation measures the site it names, never its extent.
- **C-43.** An escape hatch is the shape a wrong choice hides in.
- **P-l, D-10, D-26, D-29, D-30. C-31, C-32, C-33, C-34, C-36, C-37, C-39,
  C-40. I-5. DD0.**

## CONSTRAINTS

- Run `python3 scripts/lint-prose.py --check` on your report.
- **No em dash in any language.**
- Evidence is a COMMAND and its output, plus `file:line`. Write ASD-STE100.

## RETURN

**Lead with the count: how many rules FIRE, how many are SILENT, how many are
UNPROVOKABLE.** Then the provocation table, one row per rule, with the exact
command and its output. Then the silent ones ranked by what they guard. Then
whether `AGENTS.md`'s PARTIAL marks are still accurate. **Mark every answer
MEASURED or INFERRED, and confirm the working tree is exactly as you found it.**
