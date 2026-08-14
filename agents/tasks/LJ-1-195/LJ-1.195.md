# LJ-1.195: a consistency audit of `AGENTS.md` against `dev/`, by document rank

tier: pi (deepseek-subagent-mode), **model `deepseek-v4-flash`**, by the owner's
rule of 2026-08-14: work that touches no Agda code takes flash. **The model is a
command-line flag and this line only records the choice.**

## GOAL

**Find the contradictions between `AGENTS.md` and the documents under `dev/`,
and judge each one by RANK.**

**THE RANK, ruled by the owner 2026-08-14, highest first:**

1. **`AGENTS.md`**
2. **The `DD` series**, `dev/PLAN.md` section 3
3. **Everything else**

**Report the FIVE most severe and no more.**

**Give concrete examples of BOTH directions**: something in「everything else」
that violates a `DD`, and a `DD` that violates `AGENTS.md`.

## THIS IS READ ONLY

**Find contradictions. Fix nothing.**

**Do not edit `AGENTS.md`, any `dev/` file, any `DD` row, any script, `src/`, or
any brief or report but your own.** DD19 requires the owner's ruling and a dated
trailer for `AGENTS.md`; DD0 makes a `DD` row the owner's.

**Your report is the whole product.**

## THE TRAP, and it is the reason rank alone does not settle every tie

**`AGENTS.md` IS ITSELF STALE IN PLACES.** MEASURED 2026-08-14: its rules table
at `AGENTS.md:105` says live reports live in `agents/reports/`, older ones in
`agents/reports/archive/`, and every brief in `agents/briefs/`. `AGENTS.md:137`
says a probe goes in `agents/reports/<TASK>/`.

**None of those directories exists.** The owner merged briefs and reports into
`agents/tasks/<CODE>/`, and `bedrock.agda-lib` reads `include: src agents/tasks`.

**So a lower document that says `agents/tasks/` is RIGHT about the world and
「violates」 the highest document.** That is not a defect in the lower document.

**THE RULE FOR YOUR VERDICTS:** when a contradiction is between a document and
the WORLD, say which side matches the world, at `file:line` or with a directory
listing. **Rank decides which document must change; it does not decide which one
is true.** Say both.

**That distinction is the audit's whole value.** A report that ranks without
checking the world would order the tree rewritten to match a stale line.

## WHAT COUNTS AS A CONTRADICTION

- **A rule stated in two places with different content.** DD19 forbids a rule
  canonical twice, and `[LJ-1.187]` found four such defects this week.
- **A pointer that resolves to the wrong thing.** C-41: a citation resolving to
  the wrong thing is worse than one that dangles. The `D` against `DD` collision
  left 87 defective lines in 15 files, every one of them resolving.
- **An enforcement claim a checker does not deliver.** `AGENTS.md` says a row
  claiming more than its checker delivers turns a rule into false safety, and it
  marks several rows **PARTIAL** for that reason. **A row claiming a gate it
  does not have is a severe contradiction.**
- **A prohibition contradicted by a permission**, or a threshold stated twice
  with two numbers.

**NOT a contradiction:** a lower document giving the OPERATIONAL FORM of a rule
whose principle lives higher, when it says so and points. DD17, DD18 and DD25
all do this deliberately.

## SEVERITY, and rank it by CONSEQUENCE rather than by rank alone

**Rank the five by what the contradiction would cost an agent that obeyed the
wrong side.**

- **A defect that would make an agent write to a directory that does not exist,
  or skip a gate, is severe.**
- **A defect that a reader resolves in one step, because both sides point at
  each other, is not.**

**Say the cost in each case: a dead dispatch, a lost record, a skipped gate, a
wrong figure, or a wasted dispatch.**

## THE ABORT CRITERION, fixed BEFORE the run (D-1)

- **FIVE FOUND.** Report them ranked, each with both sides at `file:line`, the
  rank verdict, the world verdict, and the cost. STOP.
- **FEWER THAN FIVE EXIST.** **Report what you found and say the corpus is
  cleaner than the brief assumed.** **Do not manufacture findings to reach
  five.** `[LJ-1.186]` found nine of nineteen rows already pure rule and that
  was a real result.
- **A CONTRADICTION HAS NO RESOLUTION.** If neither side is wrong, because the
  rule genuinely has two legitimate readings, **that is a finding for the owner
  and the most valuable kind.** Name it and stop on it.

## THE TRAP THIS PROJECT PAID FOR FIVE TIMES ON 2026-08-14

**A search that excludes what it looks for.** The orchestrator grepped
`(override)` in parentheses when the real form was `` (version `override`, ...)
``, got 5 hits against a true 52, and acted on the 5. It grepped a struck ruling
by its NUMBER when two more sites wrote its NAME.

**Sweep by SHAPE, never by one spelling, and say which searches you ran.**

## THE CLASSIFICATION I WANT ON EVERY FINDING

**MEASURED or INFERRED, in those words.** 「These two disagree」 is MEASURED only
if you quote both sides at `file:line`.

## DD4

**Maximize the code the two proofs share, and write it generic.** One rule, two
ends, no metric and no checker.

**Here DD4 is one of the things to audit.** Its row says its enforcement is
repetition in every brief, and `scripts/check-dd4-stated.py` now gates that a
brief SAYS it. **Check whether `AGENTS.md`'s account of DD4 still matches the
row and the checker**, because that checker was written yesterday and
`AGENTS.md` has not been touched since.

## ARCHIVE (DD18)

- **`AGENTS.md` WHOLE**, and its 「Where the rules live」 table row by row. **That
  table is the specification and it names its own enforcement per row.**
- **`dev/PLAN.md` section 3 WHOLE**, all 19 `DD` rows.
- **`dev/ORCHESTRATION.md`, `dev/LESSONS.md`, `dev/STYLE-agda.md`,
  `dev/STYLE-i18n.md`, `dev/ARCHIVE.md`, `dev/GLOSSARY.md`, `dev/README.md`.**
- **`agents/tasks/LJ-1-187/lj-1.187-report.md`**, read WHOLE. **It classified
  every `dev/` document by kind last night and found four canonical-twice
  defects. Do not re-report what it already found and the orchestrator already
  fixed; check whether the fixes hold.**
- `agents/tasks/LJ-1-183/lj-1.183-report.md`: the audit of the orchestrator
  against every `DD`, and its six findings.

Return an **ARCHIVE USED** section at `file:line`.

## LITERATURE (DD18)

**Not this task's subject. Say so in one line.**

## SCOPE (read)

`AGENTS.md` FIRST, whole, then `dev/PLAN.md` section 3.

## SCOPE (write)

`agents/tasks/LJ-1-195/lj-1.195-report.md` ONLY.

## MANDATORY RULES

Run `python3 scripts/rules.py --for review` and read every statement.

- **C-22.** Write your deliverable incrementally, never at the end.
- **C-41.** A retired name must keep resolving at every citation.
- **C-42.** A refutation measures the site it names, never its extent. **So when
  you find one contradiction, sweep for the rest of its shape before ranking.**
- **P-l, D-10, D-26, D-29, D-30. C-31, C-32, C-33, C-34, C-36, C-37, C-39,
  C-40. I-5. DD0.**

## CONSTRAINTS

- Run `python3 scripts/lint-prose.py --check` on your report.
- **No em dash in any language.**
- Evidence is `file:line` on BOTH sides of every contradiction. Write
  ASD-STE100.

## RETURN

**Lead with the count and the single most severe contradiction in one
sentence.** Then the five, ranked by cost, each with: both sides quoted at
`file:line`, which document RANK says must change, which side matches the
WORLD, and what obeying the wrong side would cost. Then at least one example in
each direction, a lower document violating a `DD` and a `DD` violating
`AGENTS.md`. Then the searches you ran. **Mark every finding MEASURED or
INFERRED.**
