# LJ-1.365: does a `PT.rec` at the use site dissolve the last untruncation?

tier: pi (pi-subagent-mode), model `glm-5.3`. **I ran
`scripts/dispatch/dispatch_policy.py` before writing this line and took the
head it gave.** Agda. **PROBE. Land nothing.**

## THE SENTENCE NOBODY HAS CHECKED

**`[LJ-1.301]` wrote this on 2026-08-15 and it has sat unverified since**
(`agents/tasks/LJ-1-301/lj-1.301-report.md:157-163`):

> **What the truncated form already buys at the use site.** The GCH conclusion
> is itself truncated, **so a proof of `[LJ-1.8]` whose body consumes the law
> under a propositional motive can be wrapped in ONE `PT.rec` over
> `∥ sq κ ∥₁` per use.**

**MEASURED by me before writing this brief: the conclusion IS truncated**,
`src/L/GCH.lagda.md:68`, `∥ Σ[ δ ∈ S ] ( … ) ∥₁`. **`[LJ-1.301]`'s own
citation `:85-87` is STALE; the restatement moved it. Re-derive it.**

## WHY THIS MATTERS MORE THAN ITS SIZE

**`[LJ-1.332]` ruled: 「ONE-TRUNCATION. THE MATHEMATICS IS FINISHED. The
blocker is no longer a construction, it is one untruncation.」**

**`[LJ-1.333]` then measured that the untruncation is HARD: 「the band is the
exact complement of the only canonicalizer. Five attempts were not
unlucky.」**

**So the last structural debt on the GCH descent is an untruncation that five
attempts failed to discharge.** **If `[LJ-1.301]` is right, THAT DEBT DOES NOT
NEED TO BE PAID AT ALL, because the consumer's goal is already a proposition
and `PT.rec` applies.** **Nobody has put the two findings in the same room.**

**This probe is cheap and it may retire the single hardest remaining item on
the critical path. That asymmetry is the whole reason it is funded.**

## THE CRUX, and it is C-54

**`PT.rec` needs a PROPOSITIONAL motive.** The trophy's conclusion is a
truncation, hence a proposition, **so at the OUTERMOST goal the wrap is
free.** **The question is whether every INTERMEDIATE goal between the trophy's
conclusion and the point where `sq` is consumed is also a proposition.**

**C-54 is the law and it was written for exactly this shape:** *a truncation
stall at a SET motive is a `2-Constant` obligation before it is a principle.*
**If a SET motive appears anywhere on that path, the wrap does not go through
as stated and the debt survives in a different form.** **Find out which.**

**`[LJ-1.301]` said「under a propositional motive」. It did NOT verify that the
descent's intermediate motives are propositional. That is the gap and it is
your target.**

## WHAT IS DELIVERED AND GREEN, so you assemble rather than build

- **`agents/tasks/LJ-1-332/ProbeLJ1332A.agda:196-204`**: `limit-truncated`,
  **the truncated limit band, green at 32 lines.**
- **`agents/tasks/LJ-1-337/ProbeLJ1337B.agda:203-204`**: **`sq-below`, 90
  lines, and `[LJ-1.337]` measured its CONSUMER DIFF EMPTY.** «one band in,
  delivered conclusion out».
- **`agents/tasks/LJ-1-337/ProbeLJ1337D.agda`**: the caller's side of
  `sq-below`.
- **`src/L/GCH.lagda.md`**: the trophy, and `sq` is NOT in it any more.
  `[LJ-1.323]`'s restatement dropped it, so **`sq` is now a debt of the PROOF
  and not a hypothesis of the STATEMENT.** **That is a change since
  `[LJ-1.301]` wrote its sentence, and it may make the question EASIER.
  Check.**

**Read all four before you write a line.** **RE-RUN the two probes: they are a
day old and the chapters have drifted** (C-44).

## THE MINIATURE THAT SETTLES IT

**Build the smallest term of this shape:**

```
given  ∥ sq κ ∥₁   produce  the trophy's conclusion at κ
```

**using `PT.rec` and the delivered `sq-below` path, at the real goal type from
`src/L/GCH.lagda.md`.** **You do not need the GCH proof. You need to know
whether the wrap TYPES.**

**If it types: the untruncation is not needed and you have retired the
blocker.** **If it does not: report the exact intermediate goal whose motive
is not a proposition, at `file:line`, with the type Agda refused.** **That
goal is then the real blocker and it has a name for the first time.**

## THE ABORT CRITERION, fixed BEFORE the run (D-1)

- **THE WRAP TYPES.** **Then `[LJ-1.332]`'s「one untruncation」is dissolved and
  the GCH descent's last structural debt is gone. Report the term and STOP.
  Best possible outcome on this chain.**
- **THE WRAP FAILS AT A SET MOTIVE.** **Name the goal. Then C-54 applies and
  the question becomes a `2-Constant` obligation, which is a DIFFERENT and
  possibly cheaper debt than the untruncation.** **Price it.**
- **THE WRAP FAILS FOR ANOTHER REASON.** **Say which. `[LJ-1.333]` measured
  that the band is the exact complement of the only canonicalizer; if that is
  what bites here too, say so, because then one obstruction explains both
  failures and that is a route-level finding.**
- **`[LJ-1.301]`'s SENTENCE IS SIMPLY WRONG.** **Say so plainly.** It was
  written as an aside, marked INFERRED by its own author, and never checked.
  **A clean refutation closes a hope that is currently costing planning
  attention.**

## CONSTRAINTS

- **LAND NOTHING. `src/` is forbidden** (I-5). Write only in
  `agents/tasks/LJ-1-365/`.
- **Do not edit another task's directory.** **You may READ and COPY from
  `LJ-1-301/`, `LJ-1-332/`, `LJ-1-333/` and `LJ-1-337/`.**
- **`agents/tasks/LJ-1-344/Supply344.agda`, `LJ-1-350/MustFail350.agda` and
  `LJ-1-348/MustFail348.agda` are EXPECTED RED. Repair none.**
- **`[LJ-1.362]` and `[LJ-1.364]` may be live.** **COUNT THE AGDA SLOTS**
  before every invocation, exactly:
  `ps aux | awk '/libexec.*bin\/agda/ && !/awk/' | wc -l`. **Both obvious
  alternatives OVER-COUNT, MEASURED.** **The cap is TWO. If it reads 2, WAIT.**
- **ONE agda process, `GHCRTS="-A64m -I0 -M8g"`, cap NEVER raised.** **Report
  the empty-file floor beside any seconds figure** (C-53 as extended).
- **RUN A NEGATIVE CONTROL that MEASURES.** **If your wrap types, show a
  variant that does NOT**, so the green is not vacuous.
- **Never commit, never push**, never `git checkout .`, `git stash`,
  `git reset --hard` or `git clean`. Do not run `make check`.
- **Create `agents/tasks/LJ-1-365/lj-1.365-report.md` in your FIRST five
  minutes** (C-22).
- Run `.venv/bin/python scripts/gate/lint-prose.py --check` and
  `lint-agda.py --check`. **No em dash.** ASD-STE100. Evidence is `file:line`.
  Mark every negative **MEASURED** or **INFERRED**.

## PREMISES

> **ADDED 2026-08-16 AFTER THE RETURN, AND THE AGENT NEVER SAW THIS SECTION.**
> `check-premises-stated.py` refused this brief, correctly: it carries a
> trigger and no `## PREMISES` heading. **The substance WAS in the brief**, in
> 「THE PREMISE OF MINE MOST LIKELY TO BE WRONG」above, and the return answered
> it. **The form was not, and the gate reads the form.** This section records
> the premise and its verdict so the record is complete; it does not pretend
> the agent read it. **The orchestrator wrote this brief and broke the gate
> the same day it wrote law C-59 about gates going unread.**

- **The intermediate motives between the trophy's conclusion and the band might all be propositions**, so one `PT.rec` would discharge the law, at `agents/tasks/LJ-1-301/lj-1.301-report.md:157-163`.
  **REFUTED**, `agents/tasks/LJ-1-365/SoloC2.agda:24-27`, exit 42: the first data goal is `isSet (⟪ Lset α ⟫ ↪ ⟪ α ⟫)`, re-derived green at `agents/tasks/LJ-1-365/ProbeLJ1365A.agda:160-163`.
- **The trophy's conclusion is truncated, so the OUTER wrap is free**, at `src/L/GCH.lagda.md:65-68`.
  **VERIFIED**, `agents/tasks/LJ-1-365/ProbeLJ1365A.agda:116-121`, exit 0, with the spelling machine-checked against the delivered `GCHStatement` at `:95-99`.

## THE PREMISE OF MINE MOST LIKELY TO BE WRONG

**Eleven of my last thirty-three briefs carried a claim an agent measured
FALSE.** **The one at risk: 「the intermediate motives might all be
propositions」.** **I am hoping, not measuring. `[LJ-1.333]` measured that five
attempts at the untruncation failed and called them「not unlucky」, which is
evidence that something structural sits in the way, and that something may
well be a SET motive that kills this wrap too.** **Treat my optimism as
evidence of nothing, and expect to refute me.**

## THE RULES

**C-54 is the law of this task: a truncation stall at a SET motive is a
`2-Constant` obligation before it is a principle.** **Read its FULL entry
first, not its headline.** **C-56: when a truncated proof walls, the cost is
in the ASSEMBLY and not in the mathematics; bisect the eliminator nesting
first.** **C-44, C-45, C-57, D-10, C-42, C-53, C-58, P-l, P-k.**
**C-12, C-22, C-32, C-36, C-39, C-40.** I-5. **D-1, D-26.**
**DD0, DD4, DD8, DD18, DD23, DD24, DD25.**

Run `.venv/bin/python scripts/dispatch/rules.py --for probe` and read every
statement, opening the full entry for any law you act on.

## DD4

**Maximize the code the two proofs share, and write it generic.** One rule,
two ends, no metric and no checker. **NAME YOUR AXIS** (C-46), fixed at
`scripts/measure/ledger.py:50`.

**Say whether your wrap is class-free.** **Every term on the `sq` chain has
been, and `[LJ-1.337]`'s `sq-below` has an EMPTY consumer diff, which is the
strongest DD4 shape this chain has produced.** **If the wrap preserves that,
say so; if it forces a consumer edit, that is a cost and it belongs in your
lead.**

## ARCHIVE (DD18)

**A live `agents/tasks/` path is NOT an archive citation, MEASURED
2026-08-16** (`scripts/gate/check-archive-cited.py:26-27`). **DD18's row was
AMENDED by the owner TODAY: name each of the four corpora, cited or declined
in ONE line, and QUOTE one line per archived file you read, at its real line
number.** **`scripts/gate/check-dd18-survey.py` now GATES the return side and
it verifies the quote against the cited line. Your task is gated.**

- **`archive/src/2026-08-09-rud-route/`**: **did the retired route face a
  truncated square law, and how did it consume one?** **Grep it for the square
  law and for `PT.rec` at a similar site.** **A delivered answer there would
  settle this in an hour.**
- **`archive/dev/JOURNAL-archived.md`**: the retired route's truncation
  episodes. **WHY NOT in one line if nothing bears.**
- **`archive/dev/DECISIONS-archived.md`**: any ruling on truncation policy.
  **WHY NOT in one line if none.**
- **`archive/dev/TASKS-archived.md`**: **grep for the retired route's square
  law work**, taking SHAPE and never a claim.

**Return an ARCHIVE USED section with a real quote per file.**

## LITERATURE (DD18)

**`dev/literature/truncation-and-selection.md`.** **It is the digest written
for exactly this class of question. Say in ONE line whether the HoTT Book's
treatment gives a reason to expect the intermediate motives to be
propositions, or a reason to expect they are not.** Return a **LITERATURE
USED** section.

## SCOPE (read)

`dev/LESSONS.md`, **C-54's FULL entry**, FIRST. Then
`agents/tasks/LJ-1-337/ProbeLJ1337B.agda:203-204` and
`agents/tasks/LJ-1-332/ProbeLJ1332A.agda:196-204`, and RE-RUN both.

## SCOPE (write)

`agents/tasks/LJ-1-365/` only.

## RETURN

**Lead with ONE word: DISSOLVED, SET-MOTIVE, BLOCKED, or REFUTED.** Then the
wrap as a term, or the exact goal that refused it with Agda's own type. Then
whether `[LJ-1.323]`'s dropping of `sq` from the statement changed the
question. Then what `[LJ-1.332]`'s untruncation becomes. Then your negative
control. **Mark every negative MEASURED or INFERRED.**
