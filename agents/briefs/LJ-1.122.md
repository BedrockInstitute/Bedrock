# LJ-1.122: land the generic environment-set, by ADDING not replacing

tier: codex (default)

## GOAL

**Put the built construction into the coding machinery.** It is green in a
probe and audited. **Land it beside the numeral one, not in place of it.**

## CWD

`/Users/alsg/Agentic/Bedrock`, on branch `two-tower-bridge`, **clean at
`cc0ea60`. `make check` passes.** A sibling agent works on
`src/L/BoundedSubset.lagda.md` and its probes. **Do not touch that file.**

## WHAT IS MEASURED

`[LJ-1.120]` built it and I re-ran both probes: **exit 0.**

- **`Generic.envSetGen`** (`src/ProbeLJ1120A.agda:123`), 2.29 s cold. The
  generic index is `⟪ fst ar ⟫ × ⟪ fst B ⟫` and the numeral `nn n` becomes
  the arbitrary arity set `ar`.
- **`wired`** (`src/ProbeLJ1120B.agda:71`), 1.94 s: `someEnv`'s full
  obligation closes from the delivered companions **once `envSetK` is
  supplied**.
- **The numeral assumption was GENERALIZED, not rebuilt.** The delivered
  `envSet : (n : ℕ) → S` (`src/L/Coding/EnvSet.lagda.md:183`) indexes by
  `Fin n → ⟪ fst B ⟫` (`:122`) and names `nn n` (`:171`); the reader demands
  the arity slot be `# m` (`src/L/Coding/Sound.lagda.md:262-264`).
- **It is TOWER-FREE**, so the J tower inherits it unchanged. That is the
  largest DD4 win in this phase.

## WHAT TO BUILD, and the shape is deliberate

**ADD the generic constructor and its adequacy. Do NOT replace the numeral
ones.**

`[LJ-1.120]` says the generic constructor "replaces" the numeral one. **I am
overruling that for this dispatch, and the reason is C-40:**
`src/L/Coding/EnvSet.lagda.md` and `src/L/Coding/Sound.lagda.md` are
imported widely, and this session already lost three commits to a change
that was green in its own master and red in its consumers. **An addition
cannot break a consumer. A replacement can.**

1. **Add the generic environment-set** and its `envSetAt` adequacy beside
   the delivered numeral versions, in the same masters.
2. **If the numeral version can then be DERIVED from the generic one, do it
   and say so**, but keep its name and type byte-identical so no consumer
   moves. **If it cannot be derived, say why, and leave both.**
3. **The masters are GREEN when you finish, or you revert them and say so.**
4. **Then re-point `src/ProbeLJ1120B.agda`'s `wired` at the master's version
   rather than the probe's**, and report that it still closes. **That is the
   acceptance test: a construction with no consumer is untested (C-35).**

## C-40, AND IT IS THE RULE THIS SESSION BROKE

**After you change either master, check every master that imports it and
name them at `file:line` with their results.**
`git grep -l "Coding.EnvSet\|Coding.Sound" src/` is the list. **Verify the
list is complete rather than assuming it**, the way `[LJ-1.117]` and
`[LJ-1.119]` both did. **Do NOT run `make check`; I run it.**

## THE RULE ON HYPOTHESES, stated as a test and not as a shape

**`envSetK` stays a hypothesis in this dispatch.** `[LJ-1.120]` measured
that `KFacts` has no field for it, and **P-x forbids adding one: a record
field carrying a transparent built set walls the master in three
configurations.** **Its home is the frame, and that is a later dispatch.**

**Try to refute anything you state**, and **run
`scripts/check-unbound-hyp.py`** on both masters and on your probe.

## THE ABORT CRITERION

- **Both masters land green and `wired` still closes against the master's
  version**: report the diff, the cold seconds before and after with your
  run-to-run spread, and the consumers checked. Then STOP.
- **A consumer breaks**: STOP, revert, and say **how many broke and which**,
  not just the first.
- **The generic version cannot be stated in the master because of a
  parameter the probe had and the master does not**: report it exactly.
- **Anything walls**: STOP, report the wall with its seconds.

**Do not stop at the first negative.**

**Probes are `src/ProbeLJ1122*.agda`, never `.lagda.md`.**

## C-12, AND THIS IS NOT BOILERPLATE

`[LJ-1.80]` left **SIX agda processes alive at once**, all children of one
wrapper, all on the same probe, none killed. Each carried `-M8g`: 48 GB of
worst case on a 64 GB machine at load 19. **The owner caught it; no tool
did.**

**ONE agda process at a time, and a sibling agent holds the other slot. If a
check does not return, KILL IT before you start another, and report the wall
with its seconds.**

## WHAT YOU MUST NOT DO

- **Do not change the numeral constructor's name or type.** A consumer that
  compiles today must compile after.
- **Do not add a `KFacts` field.** P-x, measured.
- **Do not touch `src/L/BoundedSubset.lagda.md`**, where a sibling works.
- **Do not touch `src/L/Condensation*` or `src/V/`.**
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

**`[LJ-1.120]` measured this content tower-free.** **Confirm that survives
the landing**: say whether any tower object enters a type once the
construction sits in the master.

## THE COST QUESTION

The wing is over DD24 and the owner ruled the threshold question is settled
when the phase's content is complete. **So measure, do not gate.** Report
each touched master's cold seconds before and after and the non-blank
in-fence lines, **with your run-to-run spread before you claim a delta**.

## ARCHIVE (DD18)

- **`_build/lj-1.120-report.md`**, read WHOLE, and **`src/ProbeLJ1120A.agda`**
  and **`src/ProbeLJ1120B.agda`**, read WHOLE. **The construction and the
  wiring. This is what you are landing.**
- `_build/lj-1.115-report.md`, the four properties and which are supplied.
- `_build/lj-1.113-report.md`, the twenty nine and the C-39 section on the
  canonical home.
- **`src/L/Coding/EnvSet.lagda.md`** and **`src/L/Coding/Sound.lagda.md`**,
  read whole.
- `dev/LESSONS.md` **C-40, P-x, C-38 as extended, C-39**, C-35, C-36, D-30,
  P-l, P-w, read WHOLE.

Return an **ARCHIVE USED** section at `file:line`.

## LITERATURE (DD18)

**Banked. Spend nothing.** Say so in one line.

## SCOPE (read)

`src/ProbeLJ1120A.agda` FIRST, then `src/L/Coding/EnvSet.lagda.md`, then
`src/L/Coding/Sound.lagda.md:250-300`.

## SCOPE (write)

`src/L/Coding/EnvSet.lagda.md`, `src/L/Coding/Sound.lagda.md` and any master
their change forces (**all green at the end, or all reverted**), plus
`src/ProbeLJ1122*.agda`. Your report is `_build/lj-1.122-report.md`.
**Never `src/Everything.lagda.md`.**

## MANDATORY RULES FOR A BUILD

Run `python3 scripts/rules.py --for build` and `--for rewrite`, and read
every statement.

- **C-40.** Verify the CONSUMERS of a changed master, never the master
  alone. **Three commits this session were red because of this.**
- **P-x.** A transparent construction in a record field type is paid by
  every elaboration of the record.
- **C-38 as extended, C-35, C-36, D-29, D-30, D-10.**
- **C-39.** A brief's prohibition binds harder than its goal. **If a line of
  this brief blocks a route you can see, say so in the report and name the
  route. That is a required section, not a courtesy.** **In particular: if
  ADDING rather than replacing costs something real, say what.**
- **P-l.** A price from a comparable elsewhere is a hypothesis.
- **P-w.** A module application COPIES, and the copy is paid at USE.
- **P-i, P-h, P-k, P-m, P-n, P-o, P-q, P-t, P-u, P-v** as the bundle gives
  them.
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
- DD23 freezes mathematical prose. **Change the code, not the prose, unless
  a sentence becomes false. If one does, say which and leave it.**
- **Report the load average beside every absolute figure.**
- Evidence is `file:line`. Write ASD-STE100.

## RETURN

Write `_build/lj-1.122-report.md` incrementally, skeleton first.

**Lead with whether both masters are green and whether `wired` still closes
against the master's version.** Then the diff and the seconds with your
spread. **Then the C-40 section: every consumer checked, at `file:line`,
with its result, and a statement that the list is complete.** Then whether
the numeral version was derived or left standing. Then the C-39 section,
including what ADDING cost. **Mark every negative MEASURED or INFERRED.**
Then the DD4 answer: is it still tower-free?
