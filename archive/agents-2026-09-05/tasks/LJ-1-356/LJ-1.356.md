# LJ-1.356: design a mechanism that SHOUTS when DD18 is not followed

tier: pi (pi-subagent-mode), model `glm-5.3`. **I ran
`scripts/dispatch/dispatch_policy.py` before writing this line and took the
head it gave.** No Agda.

## THE OWNER'S INSTRUCTION, in their own words

> **Design a mechanism that makes sure DD18 is never forgotten and never
> SILENTLY downgraded. The moment DD18 is not properly followed, it must SHOUT.**

**Your deliverable is a DESIGN with evidence, not a rewrite of the rulebook.**

## WHAT DD18 SAYS AND WHERE IT LIVES

**A brief carries an ARCHIVE section naming what in the four archives may bear
on the task, and a LITERATURE section naming what in `dev/literature/` may. A
return carries ARCHIVE USED and LITERATURE USED, at `file:line`, including WHY
NOT for anything not used.** Text at
`.claude/skills/codex-dispatch/dispatch.py:2281-2330`; `AGENTS.md` states it in
「Probes, gates and estimates」.

**WHY it exists, from the checker's own docstring:** `[LJ-1.107]` **rebuilt 82
delivered lines of Cantor-Bernstein** that were sitting green in the archive,
and three tasks priced `levelIn` without the 845-line comparable the route's
own recon had already marked ADAPTABLE.

## THE THREE ENFORCEMENT POINTS, AND WHAT I MEASURED ABOUT EACH TODAY

**1. `dispatch.py:2313`, the only hard refusal.** MEASURED: it passes if the
text matches `^#*\s*ARCHIVE\b` **OR contains the literal substring
`archive/`**. **It reads the HEADING and never the content.** A brief with the
word and no survey passes.

**2. `scripts/gate/check-archive-cited.py`, advisory.** Its own last lines say
so: **「THIS IS A REPORT AND NEVER A GATE. It cannot tell whether an archive
bears on a task, and a red gate would buy a pasted citation rather than a
survey.」** Current figure: **204 of 305 live briefs cite an archive, and 83
cite archived CODE rather than only the retired route's RECORDS.**

**3. The return side. MEASURED: NOTHING checks it at all.** No gate reads a
report for ARCHIVE USED.

## THE MEASUREMENT THAT MADE THE OWNER ASK

**My own last twelve briefs, counted an hour ago:**

| brief | distinct `archive/` paths | mentions of `archive/src/` |
|---|---|---|
| LJ-1.344 to LJ-1.354, **eleven briefs** | **1 each** | **0 each** |
| LJ-1.355, written AFTER the owner's question | 4 | 5 |

**Every one of the eleven passed the refusal.** **Every one cited the SAME
boilerplate line**, `archive/dev/TASKS-archived.md`,「taking SHAPE and never a
claim」. **ZERO of eleven cited archived CODE.** **And `[LJ-1.353]` then had to
be told by the OWNER, in the chat, that `archive/` holds a green
Cantor-Bernstein.** **This is exactly the failure `[LJ-1.107]` cost 82 lines
for, at the same file, one year of rulings later.**

**So the form survived and the substance decayed, invisibly, for eleven
consecutive dispatches, with every gate GREEN.** **That is what「silently
downgraded」means and it is the thing you must make impossible.**

## THE ARGUMENT YOU MUST DEFEAT, NOT IGNORE

**The checker's authors were RIGHT that a red gate buys a pasted citation.**
**A rule you cannot check, gated hard, converts into a lie that passes.** **Any
design that answers「make it a gate」without answering this is REFUSED.**

**So the real question is: WHAT IS MECHANICALLY CHECKABLE THAT CORRELATES WITH
A REAL SURVEY?** Some directions, and you are not limited to them:

- **the boilerplate detector**: a citation repeated verbatim across N
  consecutive briefs is evidence of a template, not a survey, and it is
  cheap to measure;
- **the records-against-code split**, which I added today and which already
  separates 83 from 204;
- **a TREND alarm rather than a threshold**: shout when the rate falls below
  its own trailing figure, so decay is caught even while the absolute number
  looks healthy;
- **the RETURN side**, wholly unchecked today: a brief's demand is worth
  little if no report is ever read for its answer;
- **making the price VISIBLE**: `[LJ-1.107]`'s 82 lines and `[LJ-1.353]`'s
  finding are the only two arguments that have ever changed behaviour here.

**Judge each candidate by: can it be gamed by pasting? What does it cost per
dispatch? What does it FAIL to catch?** **Name the false negatives of your own
design. A design that claims full coverage is wrong.**

## THE COVERAGE INVERSION, and it is the fourth instance

**An in-harness dispatch passes through NO tool, so `dispatch.py:2313` does not
fire at all.** **Under `in-harness-subagent-mode` the ONLY hard DD18 refusal in
the project is dead**, and it was dead all week. **Whatever you design must say
which of the two modes it is live under.** **A mechanism live in only one mode
reproduces the defect it fixes.**

## THE ABORT CRITERION (D-1)

- **A DESIGN THAT SHOUTS AND CANNOT BE PASTED PAST.** Give the mechanism, where
  it is wired, what it costs, and its false negatives. **Best outcome.**
- **THE HONEST NEGATIVE: no mechanical signal correlates.** **Then say so with
  the evidence, and design the review step instead**, because `AGENTS.md`'s own
  rule is that **a rule no machine enforces MUST NAME its enforcement point**.
  **A named review step is a legitimate answer; a wish is not.**
- **THE RULE ITSELF IS WRONG.** If the measurement says DD18 as written cannot
  be followed on most tasks, **say that with the evidence and stop.** That is a
  more valuable return than a mechanism.

## CONSTRAINTS

- **PROPOSE, DO NOT LAND.** Write only in `agents/tasks/LJ-1-356/`. **You may
  write a PROTOTYPE checker there and RUN it over the corpus to get real
  numbers; do not wire it into `Makefile` or `scripts/`.** `src/` is
  forbidden (I-5).
- **DO NOT EDIT `AGENTS.md`.** DD19 gates it: owner's diff, owner's ruling, a
  dated trailer. **If your design needs an `AGENTS.md` change, write the exact
  diff into your report and say so.** Same for `dev/PLAN.md` section 3.
- **Never commit, never push**, never `git checkout .`, `git stash`,
  `git reset --hard` or `git clean`. Do not run `make check`.
- **Create `agents/tasks/LJ-1-356/lj-1.356-report.md` in your FIRST five
  minutes** (C-22).
- Run `.venv/bin/python scripts/gate/lint-prose.py --check`. **No em dash.**
- **Evidence is `file:line`, and for a rate, the command that produced it.**
  ASD-STE100. Mark every negative **MEASURED** or **INFERRED**.

## THE PREMISE OF MINE MOST LIKELY TO BE WRONG

**Eleven of my last twenty-six briefs carried a claim an agent measured FALSE.**
**The one at risk:「the form survived and the substance decayed」.** **I counted
distinct `archive/` paths with one grep over my own twelve briefs. That is a
crude proxy: a brief citing ONE archived file WELL beats one citing four
badly.** **Re-derive the decay claim your own way, and if my proxy is bad, say
so: my whole framing rests on it.**

## THE RULES

**C-48: a policy that only a document states is not enforced.** **C-45: `exit
0` is not a supply, and its analogue here is that a green gate is not a
survey.** **D-10, C-42, C-44, C-53, P-l, P-k.** **C-22, C-32, C-36, C-39,
C-40.** I-5. **D-1, D-26.** **DD0, DD4, DD8, DD17, DD18, DD19, DD23, DD25.**

Run `.venv/bin/python scripts/dispatch/rules.py --for recon` and
`--grep archive`, and read every statement.

## DD4

**Maximize the code the two proofs share, and write it generic.** One rule, two
ends, no metric and no checker. **NAME YOUR AXIS** (C-46).

**DD4 is the precedent that decides this task, and you must study it.** **DD4
has NO METRIC by the owner's decision, because a shared-line count would be
gamed the moment it gated anything.** **Its answer was to make the STATEMENT
mandatory and the substance a review matter, and `check-dd4-stated.py` reads
the heading and never the content.** **That is EXACTLY today's DD18 design.**
**So: has DD4's own mechanism worked? Measure it, do not assume.** **If
「state it and review it」has held for DD4 and failed for DD18, the difference
between them is your answer.**

## ARCHIVE (DD18)

**This section is itself under test. Do not let it be boilerplate.**

- **`archive/dev/DECISIONS-archived.md`**: find whether the RETIRED route had
  any archive-survey rule, and what became of it. **A rule that already died
  once is the strongest evidence you can bring.**
- **`archive/dev/JOURNAL-archived.md`**: the entry for `[LJ-1.107]`, the
  82 rebuilt lines. **It is DD18's founding cost. Quote it at `file:line`.**
- **`archive/src/2026-08-09-rud-route/L/Cardinal.lagda.md:89`**, the code
  nobody found. **Open it, so your report is written by someone who has seen
  what a missed survey costs.**

**Return an ARCHIVE USED section naming ONE line read per archived file.**

## LITERATURE (DD18)

**`dev/literature/`: run `ls` and say in one line whether anything there bears
on rule design.** **If nothing does, say「nothing bears on it」and name what you
checked.** **That honest line is what DD18 asks for and my eleven briefs did
not give.** Return a **LITERATURE USED** section.

## THE WORKING PRECEDENT IN THE SAME FILE, and I hit it dispatching YOU

**`dispatch.py` REFUSED the first launch of this brief**, because a `recon`
brief must cite every rule in its kind's bundle and mine had dropped `D-26`.
**That refusal reads the CONTENT: it enumerates the required rule codes and
checks each one is present.**

**So the same file holds a heading gate that decayed for eleven briefs and a
content gate that caught the orchestrator within one minute.** **Say why the
rule-bundle check can read content and DD18's check cannot, and whether any
part of that difference is recoverable.** **If DD18's demand can be made
enumerable the way a rule bundle is, that is probably your answer.**

## SCOPE (read)

`scripts/gate/check-archive-cited.py` WHOLE, FIRST. **It is the previous
attempt at your task; its docstring holds the argument you must defeat and the
date the owner caught this same failure at this same file.**

## SCOPE (write)

`agents/tasks/LJ-1-356/` only.

## RETURN

**Lead with ONE line: the mechanism, in one sentence.** Then where it is wired
and under WHICH mode. Then what it costs per dispatch. Then **its false
negatives, named by you.** Then whether it can be passed by pasting. Then
DD4's precedent, measured. Then whether my decay proxy holds. **Mark every
negative MEASURED or INFERRED.**
