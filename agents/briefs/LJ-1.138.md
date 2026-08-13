# LJ-1.138: give the probe lifecycle a correct trigger and a real execution point

tier: opus (version `override`, set 2026-08-13; the head for every case is in
`scripts/dispatch_policy.py`, which is the only place the tables live)

## GOAL

**The probe lifecycle has a wrong clock and NO execution point.** `[LJ-1.133]`
built the classifier and it is good. **Nothing ever runs it, and the one rule
that decides WHEN is measuring the wrong thing.**

Fix both. **Then answer the structural question: must a probe be written into
`src/` at all?**

## THE OWNER'S INSTRUCTION, 2026-08-13

> 「src 里现在还有探针，要明确什么时候能删，并且确保到时候确实会执行删除。今后
> 探针还是往 src 里写吗？有明确定义什么时候删除吗？」

**Three demands: a definition, a guarantee that it EXECUTES, and an answer on
where probes are written.**

`AGENTS.md` states the standard you are held to: **a rule that no machine
enforces must name its enforcement point, and a rule with no enforcement point
is a wish.** Today the probe lifecycle is a wish.

## WHAT I MEASURED BEFORE DISPATCHING YOU, and you should check each

### 1. The clock is wrong, and all 14 files proved it at once

`scripts/check-probes.py:122` sets `FRESH_HOURS = 6.0` and `:207` compares the
file's mtime. At 14:04 today the tool said of all 14 probes in `src/`:

> modified 5.8h ago, inside the 6h freshness window: **an agent may still be
> writing it**

**MEASURED: every one of those 14 tasks was CLOSED, with its report written.**
I mapped each probe name to its task code and found
`agents/reports/lj-1.115-report.md` and its 13 siblings all present. **No agent
was writing any of them.**

**mtime is a PROXY for「a task is live」and it fails in both directions:**

- A probe written once at the start of a three hour task **ages out while the
  agent still needs it.** That is the 2026-08-05 incident that killed two
  agents, and the current rule does not actually prevent it.
- A finished task's probe **stays protected for six hours after it is dead.**

### 2. But the naive fix is ALSO wrong, and one file proves it

**「The report exists, so the probe is done」 is not sufficient.**

`src/ProbeLJ1134A.agda` belongs to `[LJ-1.134]`, whose report is written and
whose task is closed. **I held it back from archiving anyway**, because
`[LJ-1.136]` is running RIGHT NOW and its brief sends it into
`agents/reports/lj-1.134-report.md`, which carries **17 citations that point
INTO that probe**.

**So the trigger has two parts, and you must get both:**

> A probe may be swept when its own task is closed **AND** no LIVE task needs
> it.

**Design the second half.** How does a tool know a task is live? Candidates
you may take, replace or reject with a reason: the PLAN section 11 row's
status column; a brief with no matching report; an explicit hold file. **Say
what you chose and what it costs when it is wrong in each direction.**

### 3. There is no execution point at all

**MEASURED.** `Makefile:82` runs `scripts/check-probes.py --check`, the GATE
that refuses a tracked probe. **`grep -rn "check-probes" Makefile scripts/
.pre-commit-config.yaml` finds no other caller.** `--stale`, `--archive` and
`--delete` have never been run by anything except a human typing them.

**That is why 284 probes accumulated.**

### 4. A trap I hit myself, an hour ago

**`--archive` alone silently does nothing and prints the `--check` success
line.** `main()` at `:337-351` treats `--stale` as the mode and `--archive` as
a flag, so `--archive` falls through to the default check. I ran it, read
「check-probes: clean」, and believed the archive had happened.

**A command that no-ops while printing a success line is worse than one that
errors.** Fix it: an unknown or ineffective combination must fail loudly.

## WHAT TO BUILD

### A. The correct trigger

Replace the mtime rule with the two-part rule above. **Keep a safety net:**
`[LJ-1.133]` was right that a rule which accepts 「it is done」 from a human
puts a human in its critical path. **Your rule must be derivable from files on
disk, not from anyone's say-so.**

### B. The execution point, and it must actually run

**`make check` is the obvious host: it is the gate before every commit and it
already calls the script.** Options, and you choose with a reason:

1. **Sweep automatically** in `make check`. Strongest guarantee, and the
   riskiest: a gate that moves files surprises everyone.
2. **Report loudly** in `make check`, and fail when the backlog passes a
   threshold. Safer; it still needs somebody to act.
3. **A separate `make probes-sweep`** that `make check` reminds you about.
   Weakest, and it is what we have.

**I lean toward 2 with a threshold, because a gate that moves files while an
agent runs is exactly the 2026-08-05 failure. Overrule me if the evidence
says otherwise.** State the honest limit of whatever you choose.

### C. The structural question, and it is the owner's real question

**`bedrock.agda-lib` reads `include: src`, one entry. THAT is why a probe must
be written into `src/`:** a probe importing `L.Choice.Step` must sit under an
include root.

**Price a second include root**, so that `src/` holds masters and nothing
else, and the probe rule becomes structural rather than a convention.

**Answer these, MEASURED:**

1. **Does Agda 2.8.0 accept several paths in `include:`?** Verify by doing it,
   not by reading documentation.
2. **What does it cost?** Does `_build/2.8.0/` change shape? Does
   `make check`'s time move? Does `src/Everything.lagda.md` see anything new?
3. **What must follow?** `.gitignore`, `REUSE.toml`, `check-probes.py`'s
   paths, `dev/build-manifest.toml`, `scripts/ledger.py`'s counting.
4. **What breaks for an agent?** Every brief says 「probes are
   `src/ProbeLJ11xxA.agda`」. **That instruction would have to change
   everywhere, and old briefs are frozen.**

**A new top-level directory needs the OWNER'S WORD** (`AGENTS.md`, Ask first).
**So PREPARE it and PRICE it. Do NOT create it.** Say what its `README.md`
would say.

## THE ABORT CRITERION

- **The trigger and the execution point both land**: report and STOP. **Part C
  may stay a priced proposal.**
- **The two-part trigger cannot be made reliable from files on disk**: say so
  and say what the least-bad rule is. **An honest limit beats a rule that
  quietly deletes an agent's working file.**
- **A second include root does not work in Agda 2.8.0**: that settles part C.
  Report it and stop that half.
- **Anything walls**: STOP, report it.

## WHAT YOU MUST NOT DO

- **Do not touch `src/ProbeLJ1134A.agda`.** `[LJ-1.136]` needs it. It is the
  live counterexample your trigger must handle, and taking it would prove the
  point the hard way.
- **Do not weaken the `src/` gate.** It was bought with a real incident on
  2026-08-04: one `git add -A src/` committed 13 probes.
- **Do not create a top-level directory.** Price it, and the owner rules.
- **Do not delete anything.** Archiving is reversible; deletion is not. **This
  session already found one rule that was backwards and would have deleted 234
  files while printing 「safe to delete」.**
- **Do not touch any `.lagda.md` master. Do not run Agda on the tree**, except
  the one minimal experiment part C needs. **A sibling is measuring build
  times, so keep your Agda to one small module and report the load.**
- Never commit, never push, never `git checkout .`, `git stash`,
  `git reset --hard` or `git clean`. **The tree carries three agents'
  uncommitted work.**
- Do not edit `AGENTS.md`. DD19, and a sibling is editing it right now.
- Do not run `make check`; I run it.

## THE CLASSIFICATION I WANT ON EVERY NEGATIVE

**MEASURED or INFERRED, in those words.**

## ARCHIVE (DD18)

- **`scripts/check-probes.py`**, read WHOLE, with `git log -p` on it. It
  changed twice today.
- **`agents/reports/lj-1.133-report.md`**, read WHOLE. The classifier, the
  three verdicts, the brace-form recall bug, and the 2026-08-05 reason the
  freshness rule exists at all.
- `dev/LESSONS.md` **D-1**, the probe doctrine, read WHOLE.
- `dev/build-manifest.toml` and `agents/reports/lj-1.132-report.md`: the
  lifecycle classes for `_build`. **A probe is the same species. Reuse the
  vocabulary or say why it does not fit.**
- `archive/probes/README.md`, which `[LJ-1.133]` wrote.
- `dev/ARCHIVE.md`, for what an archival record carries.

Return an **ARCHIVE USED** section at `file:line`.

## LITERATURE (DD18)

**Nothing in the literature governs a probe directory. Say so in one line.**

## SCOPE (read)

`scripts/check-probes.py` FIRST, then `bedrock.agda-lib`, then `Makefile:75-95`,
then `agents/reports/lj-1.133-report.md`.

## SCOPE (write)

`scripts/check-probes.py`, `Makefile`, `scripts/tests/`, `archive/probes/README.md`,
`dev/build-manifest.toml`. Your report is `agents/reports/lj-1.138-report.md`.

## MANDATORY RULES

Run `.venv/bin/python scripts/rules.py --for rewrite` and read every
statement.

- **D-1.** The probe doctrine, read WHOLE.
- **C-22.** Write the deliverable incrementally.
- **C-36.** Write the term you could not write.
- **C-39.** A brief's prohibition binds harder than its goal.
- **C-40.** Verify the CONSUMERS of what you change: `Makefile`,
  `scripts/tests/`, `check-build-manifest.py:85` cites `check-probes.py:60`
  by line and your edit may move it.
- **C-31, C-32, C-33, C-34, C-37, D-10, D-26, D-29, D-30.**

## CONSTRAINTS

- **Add a test for every rule you change.** `scripts/tests/` exists. A
  lifecycle rule with no test is the thing that was backwards this morning.
- Run `scripts/lint-prose.py --check` on anything you write.
- Evidence is `file:line`. Write ASD-STE100.

## RETURN

**Lead with the trigger, stated as one sentence an agent can act on, and where
it EXECUTES.** Then how it handles the two failure directions, with the
`ProbeLJ1134A` case worked through. Then the execution point you chose and its
honest limit. Then part C: does a second include root work, what it costs,
what must follow, and what the `README.md` would say. Then the tests you
added. **Mark every negative MEASURED or INFERRED.**
