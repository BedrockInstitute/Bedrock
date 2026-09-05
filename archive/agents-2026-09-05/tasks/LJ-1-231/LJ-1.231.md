# LJ-1.231: DD25 review of `[LJ-1.226]`, where 160 became about 700

tier: opus (deepseek-subagent-mode). **The switch's ADVERSARIAL row, taken as
the table gives it.** The target was written by pi, so DD17's invariant holds:
the critic is never the same head as the author.

## GOAL

**`[LJ-1.226]` returned a negative and it re-prices Route A-prime by about
+540 lines. DD25 says review it immediately, because a negative CLOSES a line of
work and a wrong one is the most expensive kind there is.**

**The verdict: `pairω` is MATERIALLY OVER its inferred 160, and the total is
INFERRED at about 700.**

**83 of the 700 are MEASURED. 617 are INFERRED from that one anchor.**

| component | lines | class |
|---|---:|---|
| addition description (`addFo` + clauses) | 36 | **MEASURED** |
| addition witness construction (finite graph) | 47 | **MEASURED** |
| addition adequacy (read-back, intro, elim) | about 130 | INFERRED |
| multiplication, formula plus full adequacy | about 220 | INFERRED |
| pairing formula plus adequacy | about 80 | INFERRED |
| the product set `ω×ω` in L | about 50 | INFERRED |
| the carve plus readback | about 120 | INFERRED |
| L instantiation plus C-38 guard | about 60 | INFERRED |

**Attack the 617.**

## THE FOUR QUESTIONS

**1. IS THE ANCHOR REAL?** `agents/tasks/LJ-1-226/ProbeLJ1226A.agda`, 203
non-comment lines whole, `--safe`, exit 0, cold mean 1.69 s over three kept
runs at load 5.96. **Its `.agdai` is at
`_build/2.8.0/agda/agents/tasks/LJ-1-226/ProbeLJ1226A.agdai` and Agda writes an
interface only on success; I checked that myself.** **Check the 36 and the 47:
are those line counts the ledger caliber, and is Part 0's 76 lines correctly
excluded as「the base, not the charge」?**

**2. ARE THE FIVE INFERENCES SOUND?** **This is where your budget goes.**
**P-l: an expected figure anchored on a comparable is a HYPOTHESIS, not a
price** (`dev/LESSONS.md:2370`). **The report anchors five rows on one 83-line
measurement, and the two largest, 130 and 220, are the ones a wrong analogy
would inflate most.** **Ask specifically: is multiplication really「addition
with one more existential layer」, or does it need an induction the addition
did not?**

**3. DID THE BRIEF CAUSE THE OUTCOME?** **My brief quoted `[LJ-1.176]`'s own
warning that「row 5 may be far too LOW」and put it near the top.** **An agent
told a figure is probably low will find it low.** **Say whether the report's
numbers stand independently of that framing.** `[LJ-1.211]` measured that briefs
caused 8 of 10 overturns on record.

**4. IS THERE A CHEAPER SHAPE THE REPORT MISSED?** **`[LJ-1.156]` and
`[LJ-1.176]` each DISSOLVED an A5 item rather than pricing it.** **`[LJ-1.152]`
measured that separation carries at 2,500 to 1 where replacement was assumed
necessary.** **Does `pairω` need an object-language ADDITION at all, or can the
pairing be carved directly?**

## A FALSE PREMISE IN THE TARGET, AND I CAUSED IT

**`[LJ-1.226]` section 6 reports「MEASURED: the readback device is GONE from the
tree」, because `src/ProbeLJ1134A.agda` no longer exists.**

**IT IS NOT GONE. I MOVED IT WHILE THAT AGENT WAS RUNNING.** It is at
`agents/tasks/LJ-1-134/ProbeLJ1134A.agda`, now TRACKED, where D-1 says a probe
lives. It was untracked and git-ignored inside `src/`, invisible to
`check-probes.py` and to `git status`, and one `git clean` from gone.

**`dev/JOURNAL.md` records this exact orchestrator habit under `[LJ-1.187]`: do
not change anything under a running agent. I did it again today.**

**So: the file is safe, and「no longer exists」is FALSE.** **But the report's
other half may still be true:** `injAt` and `module Small` are in no master
under `src/L/`, which `[LJ-1.227]` measured independently as zero hits across
`src/**/*.lagda.md`. **Separate the two claims. Say which parts of section 6
survive, and whether anything else in the report leans on the false half.**

## C-42 BOTH DIRECTIONS

**A refutation measures the site it NAMES and never how far that site
EXTENDS.** **Does the 700 reach FURTHER than `pairω`, and does it reach LESS
far?** **`[LJ-1.227]` measured the column square at 99 INFERRED and warned it
「may be too low as well」. If `pairω`'s inflation is structural, row 4 inflates
too, and the report did not measure row 4.**

## THE ABORT CRITERION, fixed BEFORE the run (D-1)

- **UPHELD.** The 700 is sound on its own basis. Say what you re-derived.
- **OVERTURNED.** Give the evidence at `file:line`. **A cheaper shape or a bad
  analogy in the five inferences are the two live ways this falls.**
- **UPHELD BUT MISATTRIBUTED.** The overrun is real and the CAUSE is wrong, most
  often the brief. **Four reviews today came back this way.**
- **UPHELD BUT UNQUANTIFIED.** **If「over 160」is right and「about 700」is not
  supportable, say so and give the band the evidence actually carries.** **This
  is a real outcome and I would rather have a band I can trust than a number I
  cannot.**
- **UNDECIDABLE ON THE RECORD.** Say what is missing. Do not guess.

## WHAT YOU MUST NOT DO

- **Do not edit any master, brief or report.** **Write your own report and
  nothing else.**
- **DO NOT RUN AGDA.** Two siblings hold both Agda slots (C-12): `[LJ-1.229]` is
  building A2 and `[LJ-1.230]` is running the stage decode.
- **Do not re-price A6 or A5's other rows.** `[LJ-1.217]` measured A6 at 446 and
  `[LJ-1.176]` measured A5 at 547.
- **Do not quote a total for A-prime.** Four reports now refuse one.
- **Do not touch `agents/tasks/LJ-1-229/` or `LJ-1-230/`.**
- Never commit, never push, never `git checkout .`, `git stash`,
  `git reset --hard` or `git clean`.
- Do not run `make check`.
- **Create your report file in your FIRST five minutes (C-22).**

## THE CLASSIFICATION I WANT ON EVERY NEGATIVE

**MEASURED or INFERRED, in those words.**

## DD4

**Maximize the code the two proofs share, and write it generic.** One rule, two
ends, no metric and no checker.

**`[LJ-1.227]` measured that A5's siblings split by tower: A1 is the level-hood
certificate, A3 and A4 are the definable well-order, A2 and A7 are
tower-neutral.** **Where does `pairω` fall?** **A pairing on `ω` names no tower
in its statement**, so if the 700 lines are per-tower content the report should
say why. **And if they are tower-neutral, the J tower pays them once rather than
twice, which halves their weight in any route decision.**

## ARCHIVE (DD18)

- **`agents/tasks/LJ-1-226/lj-1.226-report.md` and `ProbeLJ1226A.agda`**, both
  read WHOLE. **Read the probe, not the report's account of it.**
- **`agents/tasks/LJ-1-176/lj-1.176-report.md`**: the 547, the two inferred
  rows, and the warnings at `:252` and `:265` that my brief quoted.
- `agents/tasks/LJ-1-217/lj-1.217-report.md`: the 296-line shift charge and the
  carve shape the report borrows for its 120-line row.
- `agents/tasks/LJ-1-227/lj-1.227-report.md`: the column square at 99 INFERRED,
  and the tower split.
- **`agents/tasks/LJ-1-156/`** and **`agents/tasks/LJ-1-152/`**: the two
  dissolutions and the 2,500-to-1 separation finding. **These are question 4.**
- **`agents/tasks/LJ-1-134/ProbeLJ1134A.agda`**: the readback device the target
  says is gone. **It is here.**
- **`archive/dev/TASKS-archived.md` and `archive/src/2026-08-09-rud-route/`.**
  **A pairing on `ω` is standard content and the retired route may hold one.
  Take SHAPE from the archive, never a claim.**

Return an **ARCHIVE USED** section at `file:line`.

## LITERATURE (DD18)

**`dev/literature/rudimentary-functions.md:68` is the basis `[LJ-1.176]`
inferred from.** **Say whether it settles `pairω`'s size or only its
existence**, and whether any source prices an object-language arithmetic. Return
a **LITERATURE USED** section.

## SCOPE (read)

`agents/tasks/LJ-1-226/lj-1.226-report.md` FIRST, whole.

## SCOPE (write)

`agents/tasks/LJ-1-231/lj-1.231-report.md` ONLY.

## MANDATORY RULES

Run `.venv/bin/python scripts/rules.py --for review` and read every statement.

- **P-l.** **The load-bearing rule here.** An expected figure anchored on a
  comparable is a hypothesis, not a price.
- **D-10.** Price the truth of a recorded residue before pricing its proof.
- **C-22.** Write your deliverable incrementally.
- **C-42.** A refutation measures the site it names, never its extent.
- **C-38 as extended.** A hypothesis is discharged when something SUPPLIES it.
- **C-31, C-32, C-33, C-34, C-36, C-37, C-39, C-40. D-26, D-29, D-30. I-5.
  DD0, DD8, DD24, DD25.**

## CONSTRAINTS

- Run `.venv/bin/python scripts/lint-prose.py --check` on your report.
- **No em dash in any language.**
- Evidence is `file:line` on BOTH sides. Write ASD-STE100.

## RETURN

**Lead with ONE verdict word and ONE number: what `pairω` costs on the evidence
that exists.** Then the four questions, answered. Then which parts of section 6
survive my file move. Then C-42 in both directions, including whether the column
square inflates for the same reason. **Mark every negative MEASURED or
INFERRED.**
