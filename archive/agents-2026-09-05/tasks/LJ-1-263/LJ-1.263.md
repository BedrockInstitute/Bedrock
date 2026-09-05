# LJ-1.263: land the three L-rows into `src/L/Coding/Key.lagda.md`

tier: pi (deepseek-subagent-mode), **model `deepseek-v4-pro`**: this task runs
Agda and holds a slot. **The clock selected the mode.** **THIS TASK EDITS A
MASTER. It is a BUILD, not a probe.**

## GOAL

**Three L-rows that the nine-lemma table never priced are now built and green
in probes. Land them.**

| lemma | at | what it is |
|---|---|---|
| `union∈Lset-suc` | `agents/tasks/LJ-1-254/ProbeLJ1254.agda:117-118` | the union closure beneath `sucK` |
| `envConsK` | `agents/tasks/LJ-1-259/ProbeLJ1259.agda:114-117` | the env closure, three `consK-*` sit on it |
| the finite-supremum merge | `agents/tasks/LJ-1-261/ProbeLJ1261Merge.agda` | `union2∈λ`, `merge2`, `finSup`, and `finSetK` |

**`src/L/Coding/Key.lagda.md` is the home**: it already delivers `Lset-fin`
(`:130-135`) and `paramEnv∈` (`:104-111`), which are the two neighbours
`[LJ-1.259]` found for exactly this content. **481 lines today.**

**If a lemma does not belong there, say where it belongs and why, and land it
there instead.** **The home is my reading and C-44 says it is unchecked.**

## WHY LAND THESE THREE FIRST

**Everything else in step 6 depends on them and nothing depends on the rest.**
**They are self-contained lemmas with a clear home, so this is the smallest
landing that moves real content out of probes.**

**`[LJ-1.260]` landed the numeral premise at net +42 and every touched master
stayed green.** **That is the comparable, and P-l says it is not a price.**

## THE ABORT CRITERION, fixed BEFORE the run (D-1)

- **ALL THREE LAND AND THE MASTER IS GREEN.** Report the lines added and the
  seconds, and **re-run `ProbeLJ1254.agda`, `ProbeLJ1259.agda` and
  `ProbeLJ1261Closure.agda` IMPORTING the master's versions rather than their
  own copies.** **That is the difference between landing and copying** (C-45).
  STOP.
- **A LEMMA DOES NOT BELONG IN `Key.lagda.md`.** **Say where it belongs**, land
  it there, and say what its real dependency is.
- **THE MASTER GOES RED AND STAYS RED.** **Revert your own edits, report the
  term, and leave the tree GREEN.** **A red master is worse than an unlanded
  lemma.**
- **A CONSUMER BREAKS.** `Key.lagda.md` has consumers. **Name each at
  `file:line` and price the fix** (C-40). **Do not change a consumer to make
  the landing work without saying so.**
- **A WALL.** **A single `agda` invocation past 20 MINUTES is a wall**:
  interrupt, report the ELAPSED SECONDS, bisect. **`[LJ-1.261]`'s first attempt
  walled and its cure is in that report; read it before you start.**

## WHAT YOU MAY AND MAY NOT TOUCH

**YOU MAY EDIT:** `src/L/Coding/Key.lagda.md`, and any master you name and
justify under the second abort branch.

**YOU MAY NOT:**

- **Never `src/Everything.lagda.md`.** **The orchestrator wires it.**
- **Do not touch `src/L/Choice/Name.lagda.md`.** DD23 blocks a pending change.
- **Do not change mathematical prose** (DD23). **The `<!--en--> <!--zh-->
  <!--ja-->` marker grammar binds the master: if your change makes a prose
  sentence false, STOP and report it rather than rewriting it.**
- **Do not touch `agents/tasks/LJ-1-264/`.** A sibling is live there.
- Never commit, never push, never `git checkout .`, `git stash`,
  `git reset --hard` or `git clean`. **Leave the working tree as your report
  describes it.**
- **Do not run `make check`**; the orchestrator runs it.
- **ONE agda process, `GHCRTS="-A64m -I0 -M8g"`, cap NEVER raised.**
- **Create your report file in your FIRST five minutes (C-22).**

## EIGHT RULES THIS CHAIN EARNED

**`exit 0` IS NOT A SUPPLY** (C-45). **Here it is sharper: a probe that
typechecks its OWN copy has not landed anything. Re-run the three probes
against the MASTER.**

**C-40 IS THE OTHER CENTRE: verify the CONSUMERS of a changed master.**

**CHECK THE TREE BEFORE YOU CALL SOMETHING ABSENT.** **`[LJ-1.259]` found two
of three pieces delivered by sweeping first.**

**DERIVE A FIGURE OR DO NOT WRITE IT** (C-44). **Three of my briefs have
carried a number I did not derive.**

**AN ESCAPE HATCH IS THE SHAPE A WRONG CHOICE HIDES IN** (C-43).

**A PROHIBITION IN A BRIEF CAN BE THE WHOLE BLOCKER** (C-39).

**A FAILED SUBSTITUTION IS NOT A PROOF OF IMPOSSIBILITY** (C-36).

**SEARCH THE OPEN-WORK LIST BY CONTENT, NOT BY NAME.**

## THE CLASSIFICATION I WANT ON EVERY NEGATIVE

**MEASURED or INFERRED, in those words.**

## DD4

**Maximize the code the two proofs share, and write it generic.** One rule, two
ends, no metric and no checker.

**`[LJ-1.259]` measured `envConsK` tower-neutral over `(K, Ktr)` and
`[LJ-1.261]` measured the merge the same way.** **So all three should land
tower-neutral and the J tower pays them once.**

**AND SAY WHICH AXIS YOUR DD4 ANSWER IS ON.** `[LJ-1.262]` measured that this
phase has been mixing two: **Def against J**, which is Devlin's, and **L
against ambient**, which is the port's. **Every DD4 figure here names one and
none of them says which. Yours must.**

## ARCHIVE (DD18)

- **`agents/tasks/LJ-1-254/`, `LJ-1-259/` and `LJ-1-261/`**, read WHOLE with
  their probes. **The three lemmas and `[LJ-1.261]`'s wall cure.**
- `agents/tasks/LJ-1-260/lj-1.260-report.md`: the last master change, its
  method and its +42.
- **`src/L/Coding/Key.lagda.md:104-111`, `:130-135`: read the two neighbours
  at the source.**
- **`archive/dev/TASKS-archived.md`.** **Take SHAPE from the archive, never a
  claim.**

**Return an ARCHIVE USED section naming ONE line read per archived file.**

## LITERATURE (DD18)

**Say in one line whether the literature names any of these three closures or
takes them for granted.** Return a **LITERATURE USED** section.

## SCOPE (read)

`agents/tasks/LJ-1-261/lj-1.261-report.md` FIRST, whole.

## SCOPE (write)

`src/L/Coding/Key.lagda.md` and `agents/tasks/LJ-1-263/` for your report.

## MANDATORY RULES

Run `.venv/bin/python scripts/rules.py --for build` and read every statement.
**The tool prints `Full entry: dev/LESSONS.md:<line>` for every rule and says
THIS IS AN EXCERPT when it truncated. OPEN the full entry for any law you act
on.**

- **P-h.** Definability walks are module-parameterized, never
  function-parameterized.
- **P-k.** A read lemma is stated where its consumers use it. **That is the
  home question, and it is abort branch two.**
- **P-l.** `[LJ-1.260]`'s +42 is a comparable and NOT your price.
- **P-m.** The check-cost rate is a content-class certificate.
- **P-n.** Satisfaction content at a concrete carrier is a payable floor.
- **R-35.** Union representations are meta-poisoned; state memberships at small
  indices. **Two of your three lemmas are about unions.**
- **R-38.** A consumer's alias of a transparent imported operation is a birth
  site.
- **R-40.** A deep successor-chain membership witness normalizes
  super-linearly; climb by small closures.
- **I-5.** Inner-world truncation branches carry written types.
- **C-12.** One agda process, the cap never raised.
- **D-10.** Price the truth of a recorded residue before pricing its proof.
- **C-22.** Write your deliverable incrementally.
- **C-36, C-38, C-39, C-40, C-42, C-43, C-44, C-45. R-34. P-t, P-y. DD0, DD8,
  DD18, DD23, DD24, D-26, D-29, D-30.**

## CONSTRAINTS

- Count with `.venv/bin/python scripts/ledger.py`.
- Run `scripts/lint-prose.py --check` and `scripts/lint-agda.py --check` on
  every file you touch.
- DD23 freezes mathematical prose.
- Evidence is `file:line`. Write ASD-STE100.

## RETURN

**Lead with whether all three landed and whether `src/L/Coding/Key.lagda.md` is
GREEN.** Then the lines added and the master's seconds. Then the three probes
re-run against the MASTER, with their exit codes. Then every consumer checked.
Then the DD4 answer WITH ITS AXIS NAMED. **Mark every negative MEASURED or
INFERRED.**
