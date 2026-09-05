# LJ-1.317: literature for the typecheck-cost question

tier: opus (in-harness-subagent-mode), the switch's DEFAULT row. I ran
`scripts/dispatch/dispatch_policy.py` before writing this line.

## WHY THIS EXISTS

**The owner asked for literature beside the probe, so a ruling rests on both.**

**This project has a measured seconds problem and it is close to a gate.**
DD24's bar is 0.010514 s per line and the standing gap is **60.0 s**
(`dev/ledger.toml:303-304`). **One master, `src/L/Condensation.lagda.md`, is
132.28 s, which is 71.4 percent of the GCH wing's whole cost, and its overage
alone is about the size of the gap.** **VERIFY both figures** (C-44); an earlier
brief of mine said 62 percent and `[LJ-1.311]` measured that wrong.

**Two cures have landed and both were enormous:**

| site | before | after | delta |
|---|---:|---:|---:|
| `src/L/Cardinal.lagda.md`, an `opaque` seal | 99.78 s | 9.31 s | **-90.5** |
| `src/L/Coding/EnvSupply.lagda.md`, a respelling | 495.23 s | 6.65 s | **-488.6** |

**And `[LJ-1.309]` then swept the tree for more of the second shape and found
NOTHING deeper than depth 2.** So the known cures are spent.

**THE QUESTION THIS TASK ANSWERS: what OTHER cost mechanisms are known to
exist, so the project can look for shapes it has not met yet.** **This project
has been finding them one crisis at a time. The literature has a list.**

## THE THREE LAWS THIS PROJECT MEASURED, and they are your starting point

**Read these three entries WHOLE in `dev/LESSONS.md` before anything else.**
They are what Bedrock knows, and your job is to find what it does not.

- **R-41** (`:4247`). **Depth is free and MIXED SPELLING is what costs.** An
  index stated in a spelling its proof does not produce charges super-linearly
  in depth. **MEASURED ladder: 219 ms at depth 2, 9,286 ms at depth 3, 419,218
  ms at depth 4, about 43 times per step.**
- **P-y** (`:3803`). **A seal's price is set by how many definitions look
  INSIDE a formula**, not by how many name it.
- **C-51**, written 2026-08-15 from `[LJ-1.305]`'s walls. **A seal stops the
  conversion checker walking a formula; it does NOT stop a `with`-abstraction.**
  A `with` on a record-returning function exhausted 8 GB six times at about 310
  s each and the seal was inert; **projections cured it in 3 s.**

## THE FOUR THINGS TO COLLECT

**1. THE DOCUMENTED AGDA COST PATHOLOGIES.** **Agda's own issue tracker,
documentation and changelog record performance pathologies with names and
causes.** Collect the ones that could plausibly appear in a large dependently
typed development:

- **`with`-abstraction and its type reconstruction.** C-51 measured one case;
  **what does the literature say about why, and what other shapes trigger it?**
- **Instance resolution, unification and metavariable solving.** `[LJ-1.305]`
  hit「a left metavariable under `#` made the unifier unfold the numeral
  structure without limit」, cured by explicit indices.
- **Large records, copatterns, `abstract` against `opaque`.**
- **Level arithmetic and universe polymorphism.**
- **`REWRITE` rules and `--erasure`**, if they bear.

**For each: the mechanism, the symptom, and the documented cure.** **The symptom
column is the one that matters, because that is what an agent sees first.**

**2. THE NORMALIZATION LITERATURE, only as deep as it pays.** Conversion
checking is where the seconds go. **Report at a useful level: what strategy
Agda uses, and which term shapes are known to defeat it.** **Do not write a
tutorial.** **One page that lets a reader recognise a bad shape beats ten pages
of theory.**

**3. WHAT OTHER LARGE DEVELOPMENTS DID.** **Large Agda and Coq developments
have published their performance work.** `dev/literature/formalizations-landscape.md`
surveys the formalization landscape; **read it first**. Then look for: the
cubical library's own performance notes, any published account of scaling a
dependently typed development, and any tooling for attributing cost.

**AND ONE SPECIFIC QUESTION:** **is there a better attribution tool than
`agda --profile=definitions`?** **`[LJ-1.309]` hit a real limit: a definition
that costs 261 ms in isolation did not appear in the profile at all, and it
could not reconcile that.** **If a profile can hide a charged definition by
grouping, every「not charged」verdict this project has recorded is weaker than
it reads.** **Find out whether that is a known limitation and whether another
mode or tool avoids it.**

**4. THE SHAPE IN `Condensation`, AND ITS COST IS ALREADY ATTRIBUTED.**
**READ THIS PARAGRAPH BEFORE YOU PLAN ITEM 4; it changed at 22:20 on
2026-08-15 and an earlier draft of this brief said the opposite.**

`[LJ-1.309]` cleared `src/L/Condensation.lagda.md` of R-41's shape because it
holds **12 `sucV` and ZERO `sucIter`**. **`[LJ-1.311]` then confirmed the file
is genuinely clear AND reported that its 132.28 s is ALREADY ATTRIBUTED on the
record: the rebuilt saturation-graph machinery**, `SatGraphB` at
`src/L/Condensation.lagda.md:2236` and `:2294`, and `closedBS` at `:1586`, from
`[LJ-1.283]`. **The file is 71.4 percent of the GCH wing's seconds, not the 62
percent an earlier brief of mine said.**

**SO ITEM 4 IS NOT「find the hidden cause」. It is this:** **the cause is named
and nobody has priced a CURE for it.** **From your list of mechanisms, say which
ones could plausibly drive a saturation-graph rebuild across thirty
near-identical agreement modules with deep telescopes**, and for each, **the
symptom, the one command that tests it, and whether any documented cure
exists.** **Rank them.** **Do not run the commands: siblings hold the Agda
slots.** **A ranked, testable list is the deliverable and the next probe is
built from it.**

**AND ONE MORE, because `[LJ-1.307]` measured it:** the thirty modules spell
about 990 lines of repeated telescope, and a `KFacts`-style record states
thirty-one ties in 35 lines where a telescope spells sixty. **Is「a deep
telescope repeated thirty times」a DOCUMENTED cost shape, and does recording it
in a record cut the seconds as well as the lines?** **That would join a lines
question to a seconds question and both are open.**

## THE HARD RULE ON CITATIONS

**NEVER write a citation you did not read.** **Mark every source READ, SKIMMED
or POINTER-ONLY, in those words.** **An invented issue number is worse than
nothing** and this project cannot detect it mechanically.

**Give a locator for everything**: `file:line` in repo, or a URL plus section,
issue number or version.

## THE ABORT CRITERION, fixed BEFORE the run (D-1)

- **A RANKED LIST OF MECHANISMS EXISTS AND YOU DELIVER IT.** Report it with
  symptoms and one test command each. STOP. **That is the deliverable.**
- **THE PROFILE'S GROUPING LIMIT IS DOCUMENTED.** **Say so and name the
  alternative.** That would repair a measurement method this project relies on.
- **NOTHING IS DOCUMENTED BEYOND WHAT BEDROCK ALREADY MEASURED.** **A real
  answer.** It would mean R-41, P-y and C-51 are the state of the art here and
  the project should keep writing its own laws. **Say it plainly rather than
  padding.**
- **THE LITERATURE IS ABOUT A DIFFERENT AGDA.** Version matters. **This project
  runs Agda 2.8.0 with cubical 0.9.** **Mark anything version-specific.**

## WHAT YOU MUST NOT DO

- **RUN NO AGDA.** **C-12 caps this machine at TWO concurrent processes and
  siblings hold them.** **This task is reading and fetching only, and its whole
  value is a list somebody else measures.**
- **LAND NOTHING in `dev/literature/` or `dev/LESSONS.md`.** **Write your
  dossier in `agents/tasks/LJ-1-317/` and PROPOSE any digest or law; the
  orchestrator assigns LESSON IDs** (owner's delegation, 2026-08-06) **and
  lands digests** (DD19: nothing is canonical twice).
- **A LAW IS NOT ADMITTED WITHOUT ITS MEASUREMENT.** **You are collecting
  literature, so anything you propose is a HYPOTHESIS and must say so.**
- **Do not edit `src/`, `dev/`, `AGENTS.md`, or another task directory.**
- **Never commit, never push**, never `git checkout .`, `git stash`,
  `git reset --hard` or `git clean`. Do not run `make check`.
- **Create `agents/tasks/LJ-1-317/lj-1.317-report.md` in your FIRST five
  minutes** and fill it incrementally (C-22).
- Run `.venv/bin/python scripts/gate/lint-prose.py --check` on what you write.
  **No em dash in any language.**
- Evidence is `file:line` or a URL. Write ASD-STE100. **Mark every negative
  MEASURED or INFERRED**, and every source READ, SKIMMED or POINTER-ONLY.

## THE RULES THIS CHAIN EARNED

**C-50. Profile before you cure.** **A mechanism you cannot test is not a
cure, so every row of your list carries its test command.**

**C-42. A refutation measures the site it names.** **`[LJ-1.309]` cleared
`Condensation` of ONE shape. Your item 4 exists because that is all it did.**

**P-l. A judgement at one site is a hypothesis at another.** **A cost mechanism
documented against another codebase is a hypothesis here until measured, and
`dev/LESSONS.md` P-l says an expected figure anchored on a comparable elsewhere
is a hypothesis, not a price.**

**C-44.** Every number in this brief is from this project's records and you
re-derive each one.

## DD4

**Maximize the code the two proofs share, and write it generic.** One rule, two
ends, no metric and no checker. **This task writes no code.**

**NAME THE AXIS** (C-46). DD4's own axis is AC-against-GCH, fixed in code at
`scripts/measure/ledger.py:50`. **Seconds are paid once per master, so a cure in
a SHARED master pays on both ends and a cure in a wing master pays on one.**
**Say in one line which end a `Condensation` cure would serve**, noting
`dev/ledger.toml:204`: the GCH closure is read from a STATEMENT whose proof is
not wired, so it UNDERSTATES.

## ARCHIVE (DD18)

- **`agents/tasks/LJ-1-309/lj-1.309-report.md`, read WHOLE.** The sweep that
  spent the known cure and found the profile's limit.
- **`agents/tasks/LJ-1-292/lj-1.292-report.md`**, the ladder's origin.
- **`agents/tasks/LJ-1-283/lj-1.283-report.md`**, the seal survey where a seal
  was measured VOID at minus 0.19 percent.
- **`agents/tasks/LJ-1-305/lj-1.305-report.md` section 5.4**, the four walls and
  their cures, which is where C-51 came from.
- **`archive/dev/TASKS-archived.md`**, taking SHAPE and never a claim: the
  retired route had its own seconds crisis. **Say what would not transfer.**

**Return an ARCHIVE USED section naming ONE line read per archived file.**

## LITERATURE (DD18)

**This task IS the literature section, and its corpus is a proof assistant's
rather than a mathematician's.** **Say so in one line**, and return a
**LITERATURE USED** section naming every source, its status, its locator, its
Agda version where that matters, and **WHY NOT for anything you chose not to
read.**

## SCOPE (read)

`dev/LESSONS.md` entries **R-41, P-y and C-51** FIRST, all three whole, so you
know what this project has already measured.

## SCOPE (write)

`agents/tasks/LJ-1-317/` only.

## MANDATORY RULES

Run `.venv/bin/python scripts/dispatch/rules.py --for recon` and read every
statement. **The tool prints `Full entry: dev/LESSONS.md:<line>` and says THIS
IS AN EXCERPT when it truncated. OPEN the full entry for any law you act on.**

- **C-50, C-42, P-l, C-44.** Named above with what each governs.
- **R-41, P-y, C-51, P-i, R-40, C-49.** The measured cost laws.
- **C-12.** No Agda in this task, and the reason is above.
- **C-22, C-32, C-39.** I-5. **D-1, D-8.**
- **DD0, DD4, DD8, DD18, DD19, DD24.**

## RETURN

**Lead with ONE list: the three most likely causes of `Condensation`'s 132
seconds, ranked, each with its symptom and the one command that tests it.**
Then the full table of documented Agda cost mechanisms, with mechanism, symptom,
cure and locator. Then whether `--profile=definitions`'s grouping limit is
documented and what avoids it. Then what other large developments published.
Then anything you propose as a law, marked HYPOTHESIS with the measurement it
would need. **Mark every source READ, SKIMMED or POINTER-ONLY, and every
negative MEASURED or INFERRED.**
