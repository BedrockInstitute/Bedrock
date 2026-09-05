# LJ-1.385: DD25 review of `[LJ-1.383]`'s「all six residues are FALSE」

tier: opus (pi-subagent-mode), **the switch's ADVERSARIAL row.** `[LJ-1.383]`
was authored by `pi` / `glm-5.3`, this mode's DEFAULT row, so the adversarial
row is in-harness opus. **I ran `scripts/dispatch/dispatch_policy.py`.**
**DD17's invariant holds: the critic is not the author.** Agda.

> **CORRECTED IN PLACE 2026-08-16, and only the tier token.** As dispatched
> this line read `tier: pi`, while the same sentence said the adversarial row
> is in-harness opus and the dispatch WAS in-harness opus. **The HEAD was
> right and the TOKEN was wrong**, so `check-dispatch-policy.py` refused it,
> correctly: under `pi-subagent-mode` the critic's head is `opus`. **Nothing
> about the dispatch changed.** Same defect and same remedy as `[LJ-1.354]`
> earlier today, which is the second time in one day that this orchestrator
> wrote a tier token contradicting its own next sentence.

**NOTE: the project pauses for infrastructure work after this dispatch
returns. Finish cleanly and do not start anything you cannot finish.**

## WHY DD25 FIRES

**`[LJ-1.383]` returned a refutation of six parameters at once.** If it holds,
**the composite's ambient leaf-stem rests on six FALSE parameters**, so
`[LJ-1.378]`'s「TERMS modulo residue」reads「terms modulo something false」and
that row of the composite's price is not a price at all.

## THE CLAIM, in two separable halves

**1. FIVE WERE ALREADY FALSE IN THE RECORD.** `envK` and `defPairK` at
`agents/tasks/LJ-1-341/ProbeTies341.agda:185-190` and `:231-238`; `witK` at
`agents/tasks/LJ-1-348/Refute348.agda:247-252`; `graphWitK` at
`agents/tasks/LJ-1-351/Refute351.agda:408-412`; the BINARY arity conjunct at
`agents/tasks/LJ-1-347/Residue347.agda`. **It re-ran all four green TODAY.**

**2. THE SIXTH, the UNARY arity residue, it refuted with a NEW term**,
`agents/tasks/LJ-1-383/Probe383.agda`, exit 0. **I re-ran that myself: exit 0.**

## WHAT TO ATTACK

**1. NON-VACUITY, which is this chain's pivot every time.** **A refutation
whose premise is empty refutes nothing.** `[LJ-1.349]` set the standard by
exhibiting a term showing the countermodel lives INSIDE the chapter's intended
premise class. **Apply that standard to the SIXTH refutation, the only new
one.**

**2. IS THE COUNT SIX?** `[LJ-1.378]` says six residue parameters at
`agents/tasks/LJ-1-338/ProbeLeaf338.agda:353-356`. **This chain's counts have
been wrong before: 6 to 24 to 32 producers on a sibling.** **Re-derive it.**

**3. ARE THE FIVE PRIOR REFUTATIONS ABOUT THE SAME OBJECTS?** **The five were
refuted as CONSTRUCTION TIES in their own tasks. `[LJ-1.383]` identifies them
with the leaf-stem's RESIDUE PARAMETERS.** **That identification is the load-
bearing step and it is the one nobody has checked.** **If a residue parameter
is merely NAMED like a refuted tie, the identification fails and five of the
six are unrefuted.**

**4. DOES「ALL SIX FALSE」FOLLOW?** **Six separate refutations are not one
theorem.** **Say whether the leaf-stem could still be supplied by a DIFFERENT
set of parameters, which would make the finding a defect in `[LJ-1.338]`'s
packaging rather than in the mathematics.**

## THE ABORT CRITERION (D-1)

- **UPHOLD.** Then `[LJ-1.378]`'s composite price loses a row and the ambient
  leaf-stem needs re-design, not re-pricing. Say so plainly.
- **OVERTURN.** **Most likely at attack 3: the identification.** That is the
  valuable outcome.
- **SPLIT.** **Likeliest: the sixth is genuinely refuted and the identification
  of the other five is looser than stated.**
- **A WALL.** **C-58**, then **C-56**.

## CONSTRAINTS

- **LAND NOTHING, REPAIR NOTHING.** Write only in `agents/tasks/LJ-1-385/`.
  **`src/` is forbidden** (I-5).
- **You may READ and COPY from `LJ-1-338/`, `LJ-1-341/`, `LJ-1-347/`,
  `LJ-1-348/`, `LJ-1-351/`, `LJ-1-378/` and `LJ-1-383/`. Edit none.**
  **Several are EXPECTED RED and are evidence; repair none.**
- **`[LJ-1.381]` and `[LJ-1.386]` may be live.** **COUNT THE AGDA SLOTS**
  before every invocation, exactly:
  `ps aux | awk '/libexec.*bin\/agda/ && !/awk/' | wc -l`. **Both obvious
  alternatives OVER-COUNT, MEASURED.** Cap TWO. **If it reads 2, WAIT.**
- **ONE agda process, `GHCRTS="-A64m -I0 -M8g"`, cap NEVER raised.** **Report
  the empty-file floor beside any seconds figure** (C-53).
- **Never commit, never push**, never `git checkout .`, `git stash`,
  `git reset --hard` or `git clean`. Do not run `make check`.
- **Create `agents/tasks/LJ-1-385/lj-1.385-report.md` in your FIRST five
  minutes** (C-22).
- Run `.venv/bin/python scripts/gate/lint-prose.py --check` and
  `lint-agda.py --check`. **No em dash.** ASD-STE100. Evidence is `file:line`.
  Mark every negative **MEASURED** or **INFERRED**.

## THE VERDICT WORD

**UPHOLD, OVERTURN or SPLIT**, the first word of your return. **13 of 34
decided DD25 reviews here have overturned, 38 percent. You are not rewarded
for agreeing.**

## PREMISES

- **There are six residue parameters**, at
  `agents/tasks/LJ-1-338/ProbeLeaf338.agda:353-356`.
- **Five were refuted before this task**, at the five files named above.
- **The sixth is refuted by a new term**, at
  `agents/tasks/LJ-1-383/Probe383.agda`, exit 0, re-run by the orchestrator.
- **`[LJ-1.378]` called the leaf-stem「TERMS modulo residue」**, at
  `agents/tasks/LJ-1-378/lj-1.378-report.md:61`.

**Mark each VERIFIED or REFUTED at `file:line`.**

## LIVE RECORD

- **blocked:LJ-1.7** (`dev/PLAN.md:47`): BLOCKED at about 400 lines. BEARS: the leaf-stem is inside that figure.
- **open work item 0** (`:53`): BEARS as context, the terminus's two halves.
- **open work item 1** (`:179`): DOES NOT BEAR, `EnvSupply`'s seconds.
- **open work item 2** (`:244`): DOES NOT BEAR.
- **open work item 3** (`:265`): DOES NOT BEAR.
- **open work item 4** (`:296`): DOES NOT BEAR.
- **open work item 5** (`:311`): DOES NOT BEAR.
- **open work item 6** (`:347`): DOES NOT BEAR.
- **open work item 7** (`:410`): DOES NOT BEAR on the residue; it is `[LJ-1.8]`'s blocker and it is STALE, naming `SqShape` which occurs in zero files under `src/`.

## THE PREMISE OF MINE MOST LIKELY TO BE WRONG

**The identification in attack 3.** **I wrote 「the five were already false」
into this brief by copying `[LJ-1.383]`'s lead, and I did NOT check that a
construction tie and a residue parameter are the same object.** **Today
`[LJ-1.375]` measured a verdict line overstating its own body, and
`[LJ-1.383]` measured `[LJ-1.378]`'s claim stale against its own record. Two
relays, two failures, both mine to carry.**

## THE RULES

**C-45: `exit 0` is not a supply, and its mirror, exit 42 is not an
impossibility.** **D-10, C-42, C-44, C-53, C-55, C-57, C-58, P-l, P-k.**
**C-12, C-22, C-32, C-36, C-39, C-40.** I-5. **D-1, D-26.**
**DD0, DD4, DD17, DD18, DD23, DD24, DD25, DD28.**

Run `.venv/bin/python scripts/dispatch/rules.py --for review` and read every
statement.

## DD4

**Maximize the code the two proofs share, and write it generic.** **NAME YOUR
AXIS** (C-46), fixed at `scripts/measure/ledger.py:50`. **`[LJ-1.338]`
measured the ambient ties at three sites and found the third CONTAINS the
other four. Say whether the residues inherit that containment, because if they
do then one repair serves all of them and the finding is cheaper than it
looks.**

## ARCHIVE (DD18)

**`scripts/gate/check-dd18-survey.py` GATES your return: name each of the four
corpora, cited or declined in ONE line, and QUOTE one line per archived file
you read, at its real line number.**

- **`archive/src/2026-08-09-rud-route/`**: did the retired route carry an
  ambient leaf residue? Its coding differed, so a MEASURED「nothing transfers」
  is a fine answer.
- **`archive/dev/TASKS-archived.md`**: the retired leaf dispatches, SHAPE only.
- **`archive/dev/JOURNAL-archived.md`**: why the retired leaf bridge was shaped
  as it was. WHY NOT in one line if nothing bears.
- **`archive/dev/DECISIONS-archived.md`**: any ruling on residue parameters.
  WHY NOT in one line if none.

## LITERATURE (DD18)

**`dev/literature/devlin-II5.md`.** Say in ONE line whether a leaf-level
ambient residue has any counterpart in the text. Return a **LITERATURE USED**
section.

## SCOPE (read)

`agents/tasks/LJ-1-383/lj-1.383-report.md` WHOLE, FIRST, then
`agents/tasks/LJ-1-338/ProbeLeaf338.agda:340-360`, which holds the six.

## SCOPE (write)

`agents/tasks/LJ-1-385/` only.

## RETURN

**Lead with ONE word: UPHOLD, OVERTURN or SPLIT.** Then non-vacuity on the
sixth. Then the count, re-derived. Then the identification, checked. Then
whether「all six false」follows. **Mark every negative MEASURED or INFERRED.**
