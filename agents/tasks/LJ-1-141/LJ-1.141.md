# LJ-1.141: a probe lives beside its report, tracked, and is never deleted

tier: opus (version `override`, set 2026-08-13; the head for every case is in
`scripts/dispatch_policy.py`, which is the only place the tables live)

## THE OWNER'S RULING, 2026-08-13

> 「如果 Agda 可以读 src 之外的代码，我倾向于把探针代码跟 reports 一一对应放在
> 同一个地方，也不用再删除了，进 Git 管理也可以。」

**The direction is RULED. Do not re-litigate it.** A probe pairs one-to-one
with its report, lives with it, is tracked, and is never deleted.

**Your job is to make it work and to price what it costs.** Where the
implementation has a genuine fork, surface it with a recommendation.

## THE PRECONDITION IS ALREADY MEASURED

`[LJ-1.138]` measured all three in Agda 2.8.0, and its report is
`agents/reports/lj-1.138-report.md`:

- **Agda accepts several paths in `include:`.** MEASURED.
- **A missing include root is not an error.** MEASURED.
- **The same module name under two roots gives
  `[AmbiguousTopLevelModuleName]`.** MEASURED.
- `_build/2.8.0/agda/` gains one subtree per root. MEASURED.

**`bedrock.agda-lib` reads `include: src` today, one entry. THAT is the only
reason a probe was ever written into `src/`.**

**Re-verify these yourself before you build on them.** P-l: a measurement
elsewhere is a hypothesis at your site, and `[LJ-1.138]` measured in `/tmp`
with two four-line modules, not in this tree.

## WHAT `[LJ-1.138]` RECOMMENDED AGAINST, and why the owner's ruling is different

`[LJ-1.138]` priced a top-level `probes/` root and said 「cheap, works, worth
little」. **Its decider: 216 of 412 briefs write `src/Probe` and briefs are
frozen, so the tool must sweep both roots anyway and the rule never becomes
structural.**

**That argument does not touch the owner's design, and you should understand
why before you start.** `[LJ-1.138]` was pricing a way to keep `src/` clean.
**The owner is buying something else: a probe stops being throwaway and becomes
the report's other half.** The evidence stays with the claim, git keeps it, and
the sweep problem disappears because there is nothing to sweep.

**The 216 frozen briefs are still real.** New briefs name the new place; old
ones are records. **Say what that costs a reader.**

## THE QUESTION THAT DECIDES THE DESIGN, and nobody has answered it

**A tracked probe that nothing typechecks will ROT.** The tree moves under it,
a master changes, and the probe stops compiling. Nobody notices, because
nothing runs it.

**So: does anything check them, and what does that cost?**

Price all three, in seconds, MEASURED on a sample rather than projected:

1. **Nothing checks them.** Cheapest. A probe becomes a text record of what
   compiled once, on a tree that no longer exists. **Say plainly whether that
   is still evidence.**
2. **`make check` typechecks them all.** 257 probes are in `archive/probes/`
   today. **Measure a sample and extrapolate, saying it is an extrapolation.**
   If this is hours, it is dead and say so.
3. **A separate target**, `make probes-check`, run on demand or in CI.

**Recommend one with its price. This is the DD8 gate of this task and it is
the widest unmeasured term.**

## THE OTHER FORKS, each with a recommendation from you

1. **Where exactly?** `agents/reports/ProbeLJ1134A.agda` beside
   `agents/reports/lj-1.134-report.md`, or `agents/probes/`, or a
   per-task directory. **The owner said 「同一个地方」, one-to-one with the
   report. Take that literally unless it breaks something, and say what.**
2. **Do the 257 in `archive/probes/` migrate?** They are already tracked, and
   `[LJ-1.133]` moved them there today. **Moving them again costs another
   citation rewrite. Price it and recommend.** Leaving them is defensible: they
   belong to closed tasks and `archive/` means frozen.
3. **What happens to `src/`'s gate?** **It must NOT weaken.** The 2026-08-04
   incident stands: one `git add -A src/` committed 13 probe files. **`src/`
   stays forbidden. That is not open.**
4. **What happens to the sweep `[LJ-1.138]` built today?** If probes are never
   deleted, `--gate` and `make probes-sweep` may have nothing left to do for
   NEW probes. **Say what survives, what retires, and do not silently leave a
   dead code path.** Archive what retires; never delete it.
5. **`.gitignore`, `REUSE.toml`, `scripts/ledger.py`'s counting,
   `check-probes.py`, `dev/build-manifest.toml`.** Name every one that must
   follow and change the ones in your write scope.

## SIZE, and the owner should see the number

`archive/probes/` is about **8.5 MB over 257 files** today. **Measure it, and
project what a year of this costs at the current dispatch rate.** The owner has
already accepted tracking them, so this is information, not an objection.

## THE ABORT CRITERION

- **The rehome works and the rot question has a priced answer**: report and
  STOP.
- **A second include root breaks something in THIS tree** that `/tmp` could not
  show: **STOP AND SAY SO.** That is the finding.
- **Typechecking the probes is unaffordable at every option**: say so, and say
  what option 1 really buys.
- **Anything walls**: STOP, report it with its seconds.

## WHAT YOU MUST NOT DO

- **Do not weaken the `src/` gate.**
- **Do not delete a probe.** The ruling is that nothing is deleted.
- **Do not touch `src/ProbeLJ1136*.agda` or `src/ProbeLJ1134A.agda`.** A
  sibling is running probes RIGHT NOW and those files are live.
- **Do not run Agda on the tree beyond the minimum your measurement needs, and
  ONE process.** A sibling holds the Agda slot. **Coordinate by keeping your
  runs small, and report the load beside every figure.**
- Do not edit `AGENTS.md`. DD19: propose the line, the owner rules. **It
  changed twice today; read it fresh.**
- Never commit, never push, never `git checkout .`, `git stash`,
  `git reset --hard` or `git clean`. **Siblings hold uncommitted work.**
- Do not run `make check`; I run it.

## THE CLASSIFICATION I WANT ON EVERY NEGATIVE

**MEASURED or INFERRED, in those words.**

## ARCHIVE (DD18)

- **`agents/reports/lj-1.138-report.md`**, read WHOLE. Part C is your
  starting point and its decider is the part to think past.
- **`agents/reports/lj-1.133-report.md`**, read WHOLE. The three verdicts, the
  citation rewriter and its brace-form recall bug, which **you will need if
  anything moves**.
- `scripts/check-probes.py`, read WHOLE. It changed twice today.
- `dev/LESSONS.md` **D-1**, the probe doctrine, read WHOLE. **The owner's
  ruling amends it: a probe is no longer thrown away. Say what D-1 must now
  read, and propose the text.**
- `archive/probes/README.md`, `archive/README.md`, `dev/ARCHIVE.md`.
- `REUSE.toml`, read whole.

Return an **ARCHIVE USED** section at `file:line`.

## LITERATURE (DD18)

**Nothing in the literature governs a probe directory. Say so in one line.**

## SCOPE (read)

`bedrock.agda-lib` FIRST, then `agents/reports/lj-1.138-report.md` Part C,
then `scripts/check-probes.py`.

## SCOPE (write)

`bedrock.agda-lib`, `.gitignore`, `REUSE.toml`, `Makefile`,
`scripts/check-probes.py`, `scripts/tests/`, `dev/build-manifest.toml`,
`archive/probes/README.md`, and wherever you rehome. Your report is
`agents/reports/lj-1.141-report.md`.

## MANDATORY RULES

Run `.venv/bin/python scripts/rules.py --for rewrite` and `--for probe`, and
read every statement.

- **D-1.** The probe doctrine, read WHOLE, **and it is what this task amends.**
- **DD8.** Name the widest unmeasured term. **Here it is the rot question.**
- **P-l.** A price from a comparable elsewhere is a hypothesis. **`[LJ-1.138]`
  measured in `/tmp`; you are in this tree.**
- **C-22, C-36, C-39, C-40, C-12.**
- **C-31, C-32, C-33, C-34, C-37, D-10, D-26, D-29, D-30.**

## CONSTRAINTS

- **Add a test for every rule you change.**
- `.venv/bin/python scripts/lint-prose.py --check` on everything you write.
- **Run the full `scripts/tests/` suite**, and `reuse lint`.
- Evidence is `file:line`. Write ASD-STE100.

## RETURN

**Lead with whether it works in THIS tree, MEASURED, and the answer to the rot
question with its price.** Then the layout you chose and why. Then what must
follow, file by file. Then the size figure and the year projection. Then what
survives of `[LJ-1.138]`'s sweep and what retires. Then the D-1 text you
propose and the `AGENTS.md` line, both for the owner. **Mark every negative
MEASURED or INFERRED.**
