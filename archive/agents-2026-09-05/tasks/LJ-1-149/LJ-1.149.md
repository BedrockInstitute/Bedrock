# LJ-1.149: the six standing OWED markers, and what each still owes

tier: opus (version `override`, set 2026-08-13; the head for every case is in
`scripts/dispatch_policy.py`, which is the only place the tables live)

## GOAL

**Six `OWED` markers stand in the live plan and the live ledger. Nobody has
audited them as a set.** Say what each still owes, to whom, and whether it is
live, dead or already paid.

**This is a READING task. Do not run Agda. Two siblings are measuring seconds
and one of them says so in its own return.**

## WHY IT MATTERS, and I got this wrong once today

**I told the owner these 「look like retired rud-route residue」.** Then I read
five of them and **four were current-route items**, two of which had predicted
today's DD24 result before anybody measured it.

**So the prior is: an OWED marker in a LIVE document is live until you prove
otherwise.** `dev/LESSONS.md` C-41, admitted today, is the family this belongs
to: **a rule keeps reading true after the world it described has changed, and
nothing notices.**

## THE SIX, and what I already know about each

| site | text | what I found |
|---|---|---|
| `dev/PLAN.md:187` | 「## 4. Target skeleton (**OWED a re-derivation for DD2**)」 | **DD2 is the live endpoint ruling.** The section says the archived D5 skeleton moved to a memo and names what stays binding. **The re-derivation for the two-tower route has never been done.** Live |
| `dev/PLAN.md:386` | 「TWO PIECES OF EVIDENCE THE RULING IS OWED」 | `[L3.32-T261]`'s S-tower probe was **QUEUED for an Agda slot and never ran**; `[L3.32-T257]`'s line comparison carries a declared weak point worth 4,238 to 5,218. **Both feed `[LJ-2.5]`, the architecture ruling.** `[LJ-2.3]` is supposed to survey them |
| `dev/PLAN.md:513` | `[LJ-1.57-A]`, 「GATE OWED, priced」 | 「884 lines at the measured 0.0755 puts Condensation at 0.0220, **1.73x over DD24's bar**」. **Today Condensation measured 0.0187, 1.58x.** The prediction preceded the measurement |
| `dev/PLAN.md:548` | `[LJ-1.76-A]`, 「BRIDGE OWED」 | **SETTLED TODAY.** `[LJ-1.144]` built the bridge in a probe at the consumer's exact types. **Check whether the row should now change, and say what it should say** |
| `dev/PLAN.md:561` | `[LJ-1.83-A]`, 「OWED, RECORDED」 | 「`C = K` is a probe convenience. The real `C` is `AllCodes`, needing `AllCodes ∈ K`, **unproved**」 |
| `dev/ledger.toml:732` | 「**THE OWNER'S RULING IS OWED between two routes**」 | The row is `[[remaining]]`, id `blockpowlim-instance`, trophy **BOTH**, `naive_low` 1,619, **so it is a LIVE cost row**. But its gate narrative argues REVIVAL against RE-FORMULATION, **which is the retired rud route's fork.** Live row, stale narrative |

**Check every one of these readings. They are mine and I have been wrong today.**

## WHAT TO DO, for each of the six

1. **State what is owed, to whom, and what would discharge it.** One sentence
   each.
2. **Say whether it is LIVE, DEAD or ALREADY PAID**, with the evidence at
   `file:line`. **A marker whose debt was paid by a later task and never struck
   is the most likely finding and the cheapest fix.**
3. **Where the debt is live, say what it costs to discharge** and who should.
   **Where it is dead or paid, propose the exact replacement text.**

**Do NOT edit `dev/PLAN.md` section 11 verdict cells or `dev/ledger.toml` rows
yourself. Propose; I apply.** A section 11 row records what a dispatch found on
its day, and the `[[remaining]]` table is the size ledger's own accounting.

**You MAY edit `dev/PLAN.md:187`'s section heading and prose**, which is not a
verdict row, if the audit says it should change.

## THE ONE THAT IS MOST LIKELY TO BE INTERESTING

**`dev/PLAN.md:386`'s two pieces of evidence.** One is a probe that **never
ran** because it was queued for an Agda slot and the queue outlived the route.
The other is a line comparison with a declared weak point worth about a fifth
of its band.

**`[LJ-2.5]` is the ruling that decides the architecture, and DD2 says it is
ruled 「on measured evidence and not before」.** So: **is that evidence still
needed, is it still gettable, and what would it cost to get?** If a probe
queued for the retired route is now meaningless, say so and say what replaces
it.

## THE ABORT CRITERION

- **Six verdicts with evidence**: report and STOP.
- **A marker's status cannot be settled** without a ruling: leave it, name it,
  say what would decide it.
- **A marker turns out to hide a real unpaid debt on the current route**:
  **that is the finding. Report it first**, ahead of the table.

## WHAT YOU MUST NOT DO

- **Do not run Agda.** Two siblings are measuring seconds. **`[LJ-1.146]`
  refused to run a probe for exactly this reason today and it was right.**
- **Do not touch anything under `src/`.**
- **Do not edit a section 11 verdict cell or a `[[remaining]]` row.** Propose.
- Do not edit `AGENTS.md`. DD19. **It changed three times today; read it
  fresh.**
- Never commit, never push, never `git checkout .`, `git stash`,
  `git reset --hard` or `git clean`. **Siblings hold uncommitted work.**
- Do not run `make check`; I run it.

## THE CLASSIFICATION I WANT ON EVERY NEGATIVE

**MEASURED or INFERRED, in those words.** 「Nothing still needs this」 is
MEASURED only if you ran the search and say which search.

## ARCHIVE (DD18)

- **`archive/dev/DECISIONS-archived.md`**, for the `D` codes these rows cite.
  **A `D` code resolves against the archive and is NOT dangling; do not
  renumber one to a `DD` code.** See `dev/LESSONS.md` C-41, admitted today.
- **`agents/tasks/archive/L3-32-T261/`** and **`L3-32-T257/`**, the two pieces
  of evidence.
- `agents/tasks/archive/LJ-1-57/`, `LJ-1-76/`, `LJ-1-83/`.
- **`agents/tasks/LJ-1-144/lj-1.144-report.md`**, which settled the bridge row
  today.
- `dev/PLAN.md` DD2 and DD5, read WHOLE, for what `[LJ-2.5]` rules and when.

Return an **ARCHIVE USED** section at `file:line`.

## LITERATURE (DD18)

**Nothing in the literature governs a plan marker. Say so in one line.**

## SCOPE (read)

The six sites FIRST, in the order above. Then their tasks.

## SCOPE (write)

`agents/tasks/LJ-1-149/` for your report, and `dev/PLAN.md:187`'s section
heading and prose only.

## MANDATORY RULES

Run `.venv/bin/python scripts/rules.py --for recon` and read every statement.

- **C-41**, admitted today: a rule that keeps reading true after its world
  changed. **This task is that law applied to plan markers.**
- **C-32**, a threshold outliving its tree.
- **C-35**, a delivered block with no consumer is untested.
- **C-22, C-36, C-39, C-40, D-10, D-26, D-29, D-30.**
- **C-31, C-33, C-34, C-37.**

## CONSTRAINTS

- Run `.venv/bin/python scripts/lint-prose.py --check` and
  `.venv/bin/python scripts/check-rule-ids.py` on anything you write.
- Evidence is `file:line`. Write ASD-STE100.

## RETURN

**Lead with any real unpaid debt you found on the current route.** Then the
table: site, what is owed, to whom, LIVE or DEAD or PAID, and the evidence.
Then the proposed replacement text for each dead or paid one. Then what
`[LJ-2.5]` still needs. **Mark every negative MEASURED or INFERRED.**
