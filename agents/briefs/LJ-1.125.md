# LJ-1.125: give envSetK a home in the frame

tier: codex (default)

## GOAL

**Close the last gap in the closure family.** The generic environment-set is
in the coding machinery. **One membership fact is still a bare hypothesis,
and P-x says where it may not go.**

## CWD

`/Users/alsg/Agentic/Bedrock`, on branch `two-tower-bridge`, **clean at
`3619ad4`. `make check` passes.** A sibling agent runs in the
`bedrock-agents` workspace.

## WHAT IS MEASURED

`[LJ-1.122]` landed the generic construction: **`Generic.envSetGen`
(`src/L/Coding/EnvSet.lagda.md:456`) and `AmbientHoldsGen.holds`
(`src/L/Coding/Sound.lagda.md:287`)**, added beside the numeral versions, with
the numeral one DERIVED from the generic (`NumeralFromGeneric.derived`,
`Sound:300`) and its type byte-identical. **Both masters green, `make check`
passes, all seven other consumers checked.**

`[LJ-1.120]`: **`someEnv`'s obligation closes once `envSetK` is supplied**
(`wired`, `src/ProbeLJ1120B.agda:71`).

**`envSetK` is the one fact left:** `K` closed under the environment-set built
over an arbitrary arity in `K`, values in the ambient slot, satisfying the
machine's `envSetAt`. `[LJ-1.115]` measured the other three properties
supplied.

**P-x forbids the obvious home.** A `KFacts` record field carrying a
transparent built set **walls the master at the C-12 cap in three
configurations**, and removing two lines returns it to green at 154 to 155 s
(`_build/lj-1.109-report.md` section 2). **Its home is the frame telescope,
the shape `transK` and `sucK` already take.**

## WHAT TO DO

1. **State `envSetK` at the frame**, in
   `src/L/Condensation/TwelveAgree.lagda.md` and whichever partials need it.
   **Read the current telescopes; they were restated at `[LJ-1.110]`.**
2. **Say what would supply it**, at `file:line`, and **TRY TO REFUTE IT**.
   `src/ProbeLJ197A.agda` is the shape. **Eleven hypotheses of this frame were
   empty types, and every one was found only when somebody attacked it.**
3. **Then re-run the instantiation.** `src/ProbeLJ1112A.agda` measured ZERO
   unsolved metas against the frame as it stood. **Adding a hypothesis to the
   frame adds an obligation to the consumer, so the count must be re-measured
   and the consumer's extended frame must gain it.** Report the new count with
   0 beside it.
4. **All masters GREEN when you finish, or you revert them and say so.**

## C-40

**After you change a frame, check every master that imports it and name them
at `file:line` with their results.** `git grep -l "Condensation.TwelveAgree\|
Condensation.LowerAgree\|Condensation.UpperAgree" src/` is the list. **Verify
it is complete rather than assuming it.** Do NOT run `make check`; I run it.

## THE RULE ON HYPOTHESES, stated as a test and not as a shape

**Adding a hypothesis to a frame is a new obligation, not a discharge.**
C-38. **Say so in those words**, and name what would supply it.

**Run `scripts/check-unbound-hyp.py`** on every master you touch and on your
probe. **It flagged all eleven refuted hypotheses on the unrepaired frames.
If it flags your new one, attack it before you keep it.**

## THE ABORT CRITERION

- **`envSetK` lands, the frame is green, and the instantiation re-measures**:
  report the count, the diff and the consumers, then STOP.
- **`envSetK` is refutable as you state it**: STOP and report it. **Best
  outcome.**
- **Stating it at the frame walls a master**: STOP, report the wall with its
  seconds, and say whether it is the P-x shape again.
- **Anything walls**: STOP, report the wall with its seconds.

**Do not stop at the first negative.**

**Probes are `src/ProbeLJ1125*.agda`, never `.lagda.md`.**

## C-12, AND THIS IS NOT BOILERPLATE

`[LJ-1.80]` left **SIX agda processes alive at once**, all children of one
wrapper, all on the same probe, none killed. Each carried `-M8g`: 48 GB of
worst case on a 64 GB machine at load 19. **The owner caught it; no tool
did.**

**ONE agda process at a time, and a sibling agent holds the other slot.
`GHCRTS` is set for you by the dispatcher; if `env | grep GHCRTS` shows
nothing, pass `GHCRTS="-A64m -I0 -M8g"` yourself and SAY SO. Never raise
it.**

## WHAT YOU MUST NOT DO

- **Do not add a `KFacts` field.** P-x, measured three ways.
- **Do not weaken any row's or frame's conclusion.**
- **Do not touch `src/L/Coding/`, `src/V/` or
  `src/L/BoundedSubset.lagda.md`.**
- **Never `src/Everything.lagda.md`.**
- **Do not raise the heap cap.** C-12.
- **Read line numbers from the source, never from a report.**

## THE CLASSIFICATION I WANT ON EVERY NEGATIVE

State for every negative whether its deciding claim is **MEASURED** or
**INFERRED**, in those words. **A negative that rests on an inference sets no
verdict.**

## DD4

**Maximize the code the two proofs share, and write it generic.** One rule,
two ends, no metric and no checker, so it is stated in every brief and
answered in every return.

**`[LJ-1.120]` measured the generic environment-set TOWER-FREE**, so the J
tower inherits the whole closure family. **Say whether `envSetK` at the frame
keeps that.**

## ARCHIVE (DD18)

- **`_build/lj-1.122-report.md`**, read WHOLE. The landed construction.
- **`_build/lj-1.120-report.md`** and `src/ProbeLJ1120B.agda`. **`wired` is
  your acceptance test.**
- **`_build/lj-1.115-report.md`**, the four properties and which are
  supplied.
- **`_build/lj-1.109-report.md` section 2**, P-x measured.
- `_build/lj-1.112-report.md` and `src/ProbeLJ1112A.agda`, the zero-meta
  instantiation you must re-measure.
- `src/L/Condensation/TwelveAgree.lagda.md`, the current frame.
- `dev/LESSONS.md` **P-x, C-38 as extended, C-39, C-40**, C-35, C-36, D-29,
  D-30, read WHOLE.

Return an **ARCHIVE USED** section at `file:line`.

## LITERATURE (DD18)

**Banked. Spend nothing.** Say so in one line.

## SCOPE (read)

`_build/lj-1.120-report.md` FIRST, then `src/ProbeLJ1120B.agda`, then
`src/L/Condensation/TwelveAgree.lagda.md`'s telescope.

## SCOPE (write)

`src/L/Condensation/*.lagda.md` (**all green at the end, or all reverted**)
and `src/ProbeLJ1125*.agda`. Your report is `_build/lj-1.125-report.md`.
**Never `src/Everything.lagda.md`.**

## MANDATORY RULES FOR A BUILD

Run `python3 scripts/rules.py --for build` and `--for rewrite`, and read
every statement.

- **P-x.** A transparent construction in a record field type is paid by every
  elaboration of the record.
- **C-38 as extended.** A hypothesis is discharged when something SUPPLIES
  it.
- **C-40.** Verify the CONSUMERS of a changed master, never the master alone.
- **C-39.** A brief's prohibition binds harder than its goal. **If a line of
  this brief blocks a route you can see, say so and name the route. Required
  section.**
- **C-35, C-36, D-10, D-29, D-30.**
- **P-l, P-m, P-i, P-w, P-h, P-k, P-n, P-o, P-q, P-t, P-u, P-v** as the
  bundle gives them.
- **P-c, R-36, R-38, R-35, R-40.**
- **I-5.** The inference trap this tree has paid for.
- **C-12.** ONE agda process, cap never raised.
- **C-22.** Write the deliverable incrementally.
- **C-31, C-32, C-33, C-34, C-37.**
- **D-1, D-8, D-26.**

## CONSTRAINTS

- Never commit, never push, never `git checkout .`, `git stash`,
  `git reset --hard` or `git clean`.
- Do NOT run `make check`. **I run it on your result.**
- **Run `scripts/check-fences.py --check`** and say the master count. **It
  should be 87.**
- Count with `scripts/ledger.py`. Run `scripts/lint-prose.py --check` and
  `scripts/lint-agda.py --check` on anything you touch.
- DD23 freezes mathematical prose.
- **Report the load average beside every absolute figure.**
- Evidence is `file:line`. Write ASD-STE100.

## RETURN

Write `_build/lj-1.125-report.md` incrementally, skeleton first.

**Lead with whether `envSetK` is refutable as you stated it**, then whether
the frame is green and what the re-measured meta count is, with 0 beside it.
Then what would supply it, at `file:line`. **Then the C-40 section: every
consumer checked and a statement that the list is complete.** Then what
`check-unbound-hyp.py` says. Then the C-39 section. **Mark every negative
MEASURED or INFERRED.** Then the DD4 answer.
