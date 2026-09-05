# LJ-1.186 report: compress the `DD` series to the rule itself

tier: pi (deepseek-subagent-mode).

## Result

- **Before: 41,981 characters** in the 19 ruling cells of `dev/PLAN.md` section 3.
- **After: 28,662 characters.** Compressed by **13,319**.
- **Rows left untouched: 9.** DD1, DD8, DD9, DD11, DD13, DD15, DD19, DD22, DD23.
- **Rows compressed: 10.** DD0, DD2, DD4, DD5, DD17, DD18, DD24, DD25, DD26, DD27.
- **Rows stopped on: 0.** No row failed the RULE/READING test. Every row either
  compressed or was already pure rule.
- **Nothing lost.** Every sentence removed from a row appears in
  `dev/JOURNAL.md` under the 2026-08-14 entry. Each compressed row keeps a
  pointer to that entry.

The count is the ruling cell only (the text between the second and third `|`),
leading and trailing spaces stripped. This is the caliber the brief's
"41,981" was measured with; it reproduces exactly.

## Per-row table

| code | before | after | journal heading |
|---|---|---|---|
| DD0 | 1866 | 1317 | `#### DD0` |
| DD2 | 3515 | 1220 | `#### DD2` |
| DD4 | 4180 | 2808 | `#### DD4` |
| DD5 | 7904 | 3051 | `#### DD5` |
| DD17 | 5269 | 5107 | `#### DD17` |
| DD18 | 4077 | 2971 | `#### DD18` |
| DD24 | 2343 | 1269 | `#### DD24` |
| DD25 | 3181 | 2508 | `#### DD25` |
| DD26 | 1491 | 1179 | `#### DD26` |
| DD27 | 2003 | 1080 | `#### DD27` |
| DD1 | 283 | 283 | left alone |
| DD8 | 797 | 797 | left alone |
| DD9 | 548 | 548 | left alone |
| DD11 | 547 | 547 | left alone |
| DD13 | 972 | 972 | left alone |
| DD15 | 524 | 524 | left alone |
| DD19 | 1418 | 1418 | left alone |
| DD22 | 218 | 218 | left alone |
| DD23 | 845 | 845 | left alone |

## What moved, per row

- **DD0**: the `fable 5` episode, the checker finding, and the C-43 pointer.
- **DD2**: the amendment's warrant and the whole `[LJ-2.5]` measurement block.
- **DD4**: the `ledger.py --reuse` report, the P-h measurements, and the two
  paid-for episodes.
- **DD5**: the benchmark status, the wing-above-ceiling episode, the whole
  compression-prerequisite history, and the self-set-hole analysis.
- **DD17**: the mode-rename history, the flip's cost, the five-briefs gate fix,
  the second "52" count, and the `dispatch.py` refusal evidence.
- **DD18**: the three WHY blocks and the `[LJ-1.11]` gap clause.
- **DD24**: the ratio reasoning, the first bar measurement, the
  wing-exists-to-measure reasoning, and the P-m/P-q/P-t measurements.
- **DD25**: the sign-error episode, the fixed-tier history, and the `[LJ-1.11]`
  hand-applied gap.
- **DD26**: the two-numbers discrepancy the ruling collapsed.
- **DD27**: the prices, the counting objection, and the DD4 reason.

## Rows left alone

DD1, DD8, DD9, DD11, DD13, DD15, DD19, DD22, DD23 are pure rule. They state an
obligation, a prohibition, a threshold, an enforcement point, or a named
exception, and little else. DD15's only reasoning clauses are two short ones
("it costs minutes to tens of minutes", "DD5's time constraint makes the
measurement more load-bearing"), and moving them would not repay the risk.
This is the "already right" finding the brief names.

## Judgements (RULE or READING)

These are the borderline calls. A borderline passage I kept is marked RULE. A
passage I moved is marked READING.

- **DD0 "governs how EVERY other row is read"**: RULE. It is the rule's scope.
- **DD0 "THREE PARTS, and the third is the one that was missed"**: RULE. It
  names part (3) as the part a reader most needs.
- **DD4 "(ruled 2026-08-09, when a sufficiency audit proposed a reuse
  checker)"**: RULE. It is provenance of the no-metric decision.
- **DD4 "Sharing between the two proofs is what generic writing BUYS; they are
  one discipline seen from two ends"**: RULE. It is the rule's identity.
- **DD4 "Content written structure-generic at full strength makes every
  re-instantiation nearly free"**: READING. It states the payoff, not the
  obligation. Moved.
- **DD5 "by the owner's own instruction"**: RULE. It marks the sub-rule's
  authority.
- **DD17 "because 52 frozen briefs carry one of them"**: RULE. It is the
  reason the alias map must exist.
- **DD24 "The bar is a number rather than a judgment"**: RULE. It fixes the
  threshold's nature. The measured number it followed is READING and moved.
- **DD26 "The reason is DRIFT, and it is the owner's"**: RULE. It is the
  owner's stated reason for the exclusion and defines what an index is.
- **DD27 the blocking explanation (`[LJ-1.3]` built the hull ... index demands
  an X-formula)**: RULE. It is the technical content of the ruling. The
  prices, the counting objection and the DD4 reason are READING and moved.

## Rows stopped on

None. No row forced me to decide something the row left open. The two rows that
could have forced a stop did not:

- **DD24's stale baseline** (0.007614 over 17,492). DD26's retrospective in the
  same table re-bases it to 0.007913 over 16,897, so the live number is not
  lost when the stale one moves.
- **DD18's two enforcement sentences** ("ENFORCEMENT IS REVIEW ONLY" and
  "dispatch.py REFUSES"). They do not contradict: the first governs the
  return's USED section, the second governs the brief's sections. Both stayed,
  verbatim.

## Searches run

I swept for the SHAPE of each moved passage, not one spelling. For each, I
checked both files and confirmed the passage is gone from section 3 and present
in the journal.

- `passed all four` (DD0)
- `cannot be too weak to set a threshold` (DD2)
- `ledger.py --reuse` (DD4): the row keeps only the pointer; the two other
  PLAN hits are in section 11 task rows, which are not section 3.
- `THE COMPRESSION PREREQUISITE` (DD5)
- `THE BENCHMARK IS SELF-SET` (DD5)
- `when five briefs went red` (DD17)
- `WHY THIS WAS ADDED` (DD18)
- `WHY BOTH, when the archive half` (DD18)
- `twentyfold spread` (DD24): the one PLAN hit is in section 0, not section 3.
- `propagated sign error` (DD25)
- `collapsed a real discrepancy` (DD26)
- `THE COUNTING OBJECTION DIED` (DD27)

I also verified the full moved blocks by diffing `dev/PLAN.md` section 3 against
`/tmp/PLAN.md.bak`.

## ARCHIVE USED

- `dev/PLAN.md` section 3, whole, and DD0 first (`dev/PLAN.md:234-260`).
- `dev/JOURNAL.md`, whole, for the voice and structure (`dev/JOURNAL.md:1-352`
  before this edit).
- `archive/dev/DECISIONS-archived.md:36-43`: read the archived `D` rows
  (D11, D21) to confirm the retired series keeps its rows verbatim; no
  compression pattern came from it.
- `AGENTS.md:93`: the "Where the rules live" row on project rulings, read to
  confirm the division of ruling/episode/law.

## LITERATURE (DD18)

Not this task's subject.

## Checks

- `lint-prose.py --check dev/PLAN.md dev/JOURNAL.md agents/tasks/LJ-1-186/lj-1.186-report.md`: exit 0.
- `check-rule-ids.py`: clean (45 files, 145 lessons, 67 decisions).
- No em dash in any written file.
