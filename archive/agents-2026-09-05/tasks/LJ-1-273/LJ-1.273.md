# LJ-1.273: what must land before `gch_root` can be declared, and what does it cost

tier: pi (deepseek-subagent-mode), **model `deepseek-v4-pro`**. **This task
runs NO Agda and holds no slot, so the model rule would give flash. I override
it and record why: the task READS Agda probes and judges what each still owes
before a module can be called an endpoint, which the `--agda` flag cannot
see.** The clock selected the mode.

## GOAL

**`[LJ-1.272]` measured today that DD4's own report has NEVER been able to
run.** I re-derived it myself:

- `scripts/ledger.py:404-407` is DD4's report and `scripts/ledger.py:50` fixes
  its axis in code: **the AC closure against the GCH closure.**
- `.venv/bin/python scripts/ledger.py --reuse` on 2026-08-15 prints that there
  is **no GCH endpoint in `src/` yet, so there is nothing to share WITH.**
- `dev/ledger.toml` `[reuse]` declares `gch_root = ""` and says
  **`[LJ-1.8]` lands the first.**

**So the project's CORE constraint becomes measurable on exactly one day: the
day a GCH endpoint exists in `src/`. Nobody has priced that day.**

**This task prices it.** **What must land, in what order, before
`reuse.gch_root` can name a real module?**

## THE QUESTION UNDER THE QUESTION, and it is the one that decides the price

**`[LJ-1.8]`'s row reads「Build: assemble L models GCH... Needs `[LJ-1.7]`」
(`dev/PLAN.md:895`).** **Route A-prime's block A7 is `GCHStatement` at 33
lines (`agents/tasks/LJ-1-236/ProbeLJ1236A7.agda`).**

**ARE THOSE THE SAME THING, OR TWO THINGS?**

- **If A7 IS the endpoint**, then A-prime's landing declares `gch_root`, and
  `[LJ-1.268]`'s wave order is already the schedule. **The wait is short.**
- **If `[LJ-1.8]` is the endpoint and A7 is only its STATEMENT**, then a
  statement is not a proof, `gch_root` waits on `[LJ-1.7]`, and **the wait is
  the whole remaining phase.**

**Nobody has written down which. That single answer is this task's centre.**

**Do not decide it by the names.** `[LJ-1.236]` measured that A7's statement
audits the rest: A5's `sq` and A6's `absorbs` have conclusion types that are
A7's hypotheses **on the nose**. **So read what A7's probe actually PROVES
against what its hypotheses still ASSUME.** C-45 is the law: audit the
INSTANTIATION, never the telescope. **`exit 0` is not a supply.**

## THE THREE THINGS TO BRING BACK

**1. WHAT `gch_root` MUST NAME.** **A module path, and the theorem in it that
makes it an endpoint.** **Say what `ac_root` names and why**, because
`dev/ledger.toml` already declares it (`ac_root = "src/L/Model.lagda.md"`, the
delivered AC endpoint at `Model.lagda.md:99`) and **the GCH side must be the
same KIND of object**. **Read `Model.lagda.md:99` and say what shape an
endpoint is.**

**2. THE CHAIN, with every link named.** **From today's tree to a declarable
`gch_root`.** For each link: **is it BUILT, is it SUPPLIED, or is it OPEN**
(C-38 as extended), and **what does it still owe at `file:line`**. **`[LJ-1.267]`
measured `[LJ-1.7]`'s seven parameters at 3 SUPPLIED, 3 BUILT-not-supplied and
1 OPEN. Start from that and check it** (C-44).

**3. THE PRICE, and its basis named** (DD8). **One best-effort number for the
gap between today and a declarable `gch_root`.** **Say whether the basis is a
probe, a delivered comparable or a survey.** **A band is acceptable if you say
what makes it a band.**

## THE ABORT CRITERION, fixed BEFORE the run (D-1)

- **A7 IS THE ENDPOINT.** **Then say so with the evidence, and `gch_root` is
  declarable on the day `[LJ-1.268]`'s wave lands A7.** **That is the best
  outcome and it would mean DD4 becomes measurable within this phase.** STOP.
- **A7 IS ONLY THE STATEMENT.** **Then name every hypothesis it still assumes,
  at `file:line`, and price the chain.** **A statement whose hypotheses are
  unsupplied is not an endpoint, and saying so plainly is the right answer.**
- **THE ENDPOINT NEEDS SOMETHING NOBODY HAS NAMED.** **That is the most
  valuable outcome here. Name it and price it, or name the probe that would.**
- **`ac_root` IS NOT WHAT ITS COMMENT SAYS.** **Check it** (C-44). **If the AC
  side's own declared endpoint does not hold up, the GCH side has no template
  and the ledger has a defect. Report it loudly.**

## WHAT YOU MUST NOT DO

- **DO NOT RUN AGDA.** **A sibling is measuring SECONDS right now and needs a
  quiet machine.** **This is the hardest constraint in this brief.**
- **Do not re-price Route A-prime.** `[LJ-1.253]` summed it to 1,089 and
  `[LJ-1.268]` wrote the landing order. **You price the gap to `gch_root`,
  which may be larger or smaller than either.**
- **Do not edit `dev/ledger.toml`.** **You say what `gch_root` should name.
  The orchestrator declares it on the day it is true.**
- **Do not edit any master, brief or report.** **Write your own report and
  nothing else.** **I write the status screen.**
- **Do not touch `agents/tasks/LJ-1-266/`.** A sibling is live there.
- **Create your report file in your FIRST five minutes (C-22).**
- Never `src/Everything.lagda.md`. Never commit, never push, never
  `git checkout .`, `git stash`, `git reset --hard` or `git clean`.
- Do not run `make check`; the orchestrator runs it.

## SEVEN RULES THIS CHAIN EARNED

**`exit 0` IS NOT A SUPPLY** (C-45). **A green probe is not a delivered master,
and a delivered master is not an ENDPOINT. This task is that distinction
applied twice.**

**A CONDITIONAL SUPPLY RECORDED AS A SUPPLY is the failure that cost this phase
the most.** **`amb` read SUPPLIED in the status screen for a day.**

**DERIVE A FIGURE OR DO NOT WRITE IT** (C-44). **Every figure in this brief is
another report's except the `--reuse` run, which I made myself today.**

**C-46, WRITTEN TODAY FROM THIS EXACT FINDING.** **A rule with no metric still
has an axis. Read the rule's own text for the axis it names, and run its report
if it has one.**

**SEARCH THE OPEN-WORK LIST BY CONTENT, NOT BY NAME.** **Ten dispatches once
re-derived a price the plan already carried. `dev/PLAN.md` section 0.0 may
already answer part of this.**

**THE ARCHIVE BEARS UNTIL YOU OPEN IT.**

**AN ESCAPE HATCH IS THE SHAPE A WRONG CHOICE HIDES IN** (C-43).

## THE CLASSIFICATION I WANT ON EVERY NEGATIVE

**MEASURED or INFERRED, in those words.**

## DD4

**Maximize the code the two proofs share, and write it generic.** One rule, two
ends, no metric and no checker.

**THIS TASK IS ABOUT DD4'S OWN MEASURABILITY, so answer DD4 on its OWN axis for
once.** **`[LJ-1.272]` measured that DD4's axis is AC-against-GCH, fixed in
`scripts/ledger.py:50`.**

**So: of the chain you price, how much lands INSIDE the AC closure, and how much
is GCH-only?** **A link that lands inside the shared part raises DD4's figure on
the day it lands; a GCH-only link does not.** **You cannot compute the closure
without running the tool, and you may not run Agda, so give the JUDGEMENT with
its evidence and mark it INFERRED.**

**And NAME YOUR AXIS on anything else you say about towers**, because the phase
mixed two and C-46 is why.

## ARCHIVE (DD18)

- **`agents/tasks/LJ-1-272/lj-1.272-report.md`, sections 3 and 4, read WHOLE.**
  **The finding this task follows.**
- **`agents/tasks/LJ-1-236/ProbeLJ1236A7.agda`, read WHOLE.** **A7 is the
  object.** **Read the SOURCE, not a report about it.**
- **`src/L/Model.lagda.md:99`**: the delivered AC endpoint, the template.
- `agents/tasks/LJ-1-267/lj-1.267-report.md`: `[LJ-1.7]`'s seven parameters.
- `agents/tasks/LJ-1-268/lj-1.268-report.md`: the landing order and which
  blocks cannot land yet.
- `agents/tasks/LJ-1-253/lj-1.253-report.md`: the 1,089 and every block's
  basis.
- **`archive/dev/TASKS-archived.md` and `archive/dev/STATUS-archived.md`.**
  **The retired RUD route also planned a GCH endpoint, and `[LJ-1.1]`'s recon
  called `CardinalPredicates` PORTABLE at 399 lines** (`dev/PLAN.md:895`).
  **Is that 399 still portable, and is it inside this chain or beside it?**
  **Take SHAPE from the archive, never a claim.**

**Return an ARCHIVE USED section naming ONE line read per archived file.**

## LITERATURE (DD18)

**`dev/literature/devlin-II5.md` splits II.5 into twelve rows.** **Say which
rows the endpoint chain still needs**, and whether any row in it has no
delivered counterpart at all. Return a **LITERATURE USED** section.

## SCOPE (read)

`agents/tasks/LJ-1-272/lj-1.272-report.md` FIRST, sections 3 and 4.

## SCOPE (write)

`agents/tasks/LJ-1-273/` only. **No master, no ledger, no plan, no other
report.**

## MANDATORY RULES

Run `.venv/bin/python scripts/rules.py --for recon` and read every statement.
**The tool prints `Full entry: dev/LESSONS.md:<line>` for every rule and says
THIS IS AN EXCERPT when it truncated. OPEN the full entry for any law you act
on.**

- **C-38 as extended.** **A hypothesis is discharged when something SUPPLIES
  it. The centre of the chain question.**
- **C-45.** Audit the instantiation, never the telescope.
- **D-10.** **Price the truth of a recorded residue before pricing its proof.**
  **`[LJ-1.8]`'s row is exactly such a record and it is dated.**
- **C-44.** A brief's claim is unchecked until you check it.
- **C-46.** A rule with no metric still has an axis.
- **P-l.** A judgement at one site is a hypothesis at another.
- **D-26.** A well-founded key on a tower needs generation data, or it needs
  syntax. **It bears here: the GCH endpoint's chain runs through the definable
  well-order, and D-26 is what decides whether that costs syntax.**
- **C-22, C-32, C-36, C-39, C-40, C-42, C-43. I-5. DD0, DD2, DD4, DD5, DD8,
  DD18, DD24.**

## CONSTRAINTS

- Count with `.venv/bin/python scripts/ledger.py`. **`--brief` is the only
  admissible source for a standing size figure.**
- Run `.venv/bin/python scripts/lint-prose.py --check` on your report.
- **No em dash in any language.**
- Evidence is `file:line`. Write ASD-STE100.

## RETURN

**Lead with ONE sentence: is A7 the GCH endpoint, or only its statement?** Then
what `gch_root` must name and the theorem that makes it an endpoint. Then the
chain, one link per row, each BUILT, SUPPLIED or OPEN with its `file:line`.
Then the price with its basis named. Then the DD4 answer on the AC-against-GCH
axis. **Mark every negative MEASURED or INFERRED.**
