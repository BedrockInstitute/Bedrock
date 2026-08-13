# LJ-1.105: land the tie repair in EnvSet and the Mem row

tier: codex (default)

## GOAL

**Put the measured repair into the master.** One row is proved in tied form.
**Land the shared half and the one row, green, and price the other eleven
from what it costs.**

## CWD

`/Users/alsg/Agentic/Bedrock`, on branch `two-tower-bridge`, **clean at
`5cc68f7`**. HEAD is green. **A sibling agent holds the other Agda slot and
works on the cardinal side. It will not touch `src/L/Condensation.lagda.md`.**

## WHAT IS MEASURED, and I re-ran both checks myself

`[LJ-1.104]`: **the Mem row proves BOTH directions in tied form**, against
the same statements the master proves today. `src/ProbeLJ1104A.agda`, GREEN,
9.67 s. **I re-ran it: exit 0.**

- **One hypothesis added: `arityK`**, a `KFacts` field in its exact shape
  (`src/L/Condensation.lagda.md:5769-5770`).
- **`entryK` and `arSubK` become tied forms**, both then SUPPLIED by
  `arityK` and machine-checked as supplied.
- **`tmKeyK` becomes a DERIVATION at zero telescope cost.** Its tied form
  `keyValK` was itself refuted (`src/ProbeLJ1104A.agda:118-120`).
- **Telescope 44 to 51 non-blank lines.**

**Its DD4 answer names the cheaper shape and that is what you build:
`EnvSet` carries `arityK`, `E ∈ K` and `ar ∈ K`, and derives the ties ONCE.
Nine rows use `EnvSet`; stating the ties per row duplicates the same
derivation nine times.**

## WHAT TO BUILD, in `src/L/Condensation.lagda.md`

1. **`EnvSet` (`:2764-2874`) gains `arityK`, `E ∈ K` and `ar ∈ K`**, and
   derives the ChainZ `entryK` tie and the `arSubK` tie inside itself.
   **`src/ProbeLJ1104A.agda`'s `EnvSetTied` (`:132-251`) already has this
   shape. Read it and follow it.**
2. **The Mem row (`:4141-4240`) uses the new `EnvSet`**, with `arityK` in
   its telescope, `tmKeyK` removed and derived.
3. **The master is GREEN when you finish, or you revert it and say so.**
4. **The other eleven rows keep their current shape** unless the `EnvSet`
   change forces a signature update. **If it does, do the minimum that
   keeps them green and say what you changed.**

**Do not touch the three masters under `src/L/Condensation/`. Their frames
come after this.**

## THE RULE ON HYPOTHESES, stated as a test and not as a shape

**Every hypothesis you add must be one the CONSUMER can supply. Name what
supplies each one, at `file:line`, before you add it.** If nothing supplies
it, do not add it, and report the term you could not write.

**Try to refute every tied form you write**, the way
`src/ProbeLJ1104A.agda:118-120` refuted `keyValK`. **A tie that is itself an
empty type closes the row for the wrong reason. That happened one dispatch
ago, inside the material this repair is built on.**

## THE ABORT CRITERION

- **`EnvSet` and the Mem row land green**: report the diff, the master's
  cold seconds before and after, and **the projected price of the other
  eleven rows with its basis named**. Then STOP.
- **A row outside Mem breaks and cannot be kept green cheaply**: STOP,
  revert, and report which row and why. **Say how many rows broke, not just
  the first.**
- **Anything walls**: STOP, report the wall with its seconds. **The master
  is 6,529 in-fence lines and its cold check has measured near 102 to 108 s.
  A wall here is a real measurement.**

**Do not stop at the first negative. Count the failures and report the
count.**

## C-12, AND THIS IS NOT BOILERPLATE

`[LJ-1.80]` left **SIX agda processes alive at once**, all children of one
wrapper, all on the same probe, none killed. Each carried `-M8g`: 48 GB of
worst case on a 64 GB machine at load 19. **The owner caught it; no tool
did.**

**ONE agda process at a time, and a sibling agent holds the other slot. If a
check does not return, KILL IT before you start another, and report the wall
with its seconds.**

## WHAT YOU MUST NOT DO

- **Do not weaken any row's conclusion.** Every row proves the SAME
  statement it proves today.
- **Do not touch `src/L/Condensation/`, `src/L/Coding/`, `src/V/` or
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

**This dispatch IS a DD4 move: one derivation inside `EnvSet` instead of
nine copies.** Say what it saved, in lines, and whether the J tower gets the
new `EnvSet` unchanged.

## THE COST QUESTION

The wing is over DD24 and the owner ruled the threshold question is settled
when the phase's content is complete. **So measure, do not gate.** Report
the master's cold seconds before and after, and the non-blank in-fence lines
added, with the load average.

## ARCHIVE (DD18)

- **`src/ProbeLJ1104A.agda`**, read WHOLE, and `_build/lj-1.104-report.md`.
  **This is the shape you are landing. Do not redesign it.**
- `src/ProbeLJ1102A.agda` and `_build/lj-1.102-report.md`, the two tie forms
  and the failure that `arityK` fixes.
- `src/ProbeLJ199A.agda` and `_build/lj-1.99-report.md`, the chain.
- `src/ProbeLJ197A.agda`, the refutation shape.
- `src/L/Condensation.lagda.md:2764-2874`, `:4141-4240`, `:5734-5770`.
- `dev/LESSONS.md` **C-38 as extended, C-39**, C-35, C-36, D-29, D-30, P-i,
  P-w, read WHOLE.

Return an **ARCHIVE USED** section at `file:line`.

## LITERATURE (DD18)

**Banked. Spend nothing.** Say so in one line.

## SCOPE (read)

`src/ProbeLJ1104A.agda:132-251` FIRST, then
`src/L/Condensation.lagda.md:2764-2874`, then `:4141-4240`.

## SCOPE (write)

`src/L/Condensation.lagda.md` (**green at the end or reverted**) and
`src/ProbeLJ1105*.agda`. Your report is `_build/lj-1.105-report.md`.
**Never `src/Everything.lagda.md`.**

## MANDATORY RULES FOR A BUILD

Run `python3 scripts/rules.py --for build` and `--for rewrite`, and read
every statement.

- **C-38 as extended.** A hypothesis is discharged when something SUPPLIES
  it.
- **C-39.** A brief's prohibition binds harder than its goal. **If a line of
  this brief blocks a route you can see, say so in the report and name the
  route. That is a required section, not a courtesy.**
- **C-35, C-36, D-29, D-30, D-10.**
- **P-i.** The conversion-explosion playbook. **Read it whole.**
- **P-w.** A module application COPIES, and the copy is paid at USE.
  **`EnvSet` is applied nine times: three added parameters are paid nine
  times. Say what that costs in seconds.**
- **P-h, P-k, P-l, P-m, P-n, P-o, P-q, P-t, P-u, P-v** as the bundle gives
  them.
- **P-c, R-36, R-38.** Seal at the birth site; expose with a read lemma.
- **R-35, R-40.** State the membership SHALLOW and climb.
- **I-5.** The inference trap this tree has paid for.
- **C-12.** ONE agda process, cap never raised.
- **C-22.** Write the deliverable incrementally.
- **C-31, C-32, C-33, C-34, C-37.**
- **D-1, D-8, D-26.**

## CONSTRAINTS

- Never commit, never push, never `git checkout .`, `git stash`,
  `git reset --hard` or `git clean`.
- Do NOT run `make check`.
- **Run `scripts/check-fences.py --check`** and say the master count.
- Count with `scripts/ledger.py`. Run `scripts/lint-prose.py --check` and
  `scripts/lint-agda.py --check` on anything you touch.
- DD23 freezes mathematical prose. **Change the code, not the prose, unless
  a sentence becomes false. If one does, say which and leave it.**
- **Report the load average beside every absolute figure.**
- Evidence is `file:line`. Write ASD-STE100.

## RETURN

Write `_build/lj-1.105-report.md` incrementally, skeleton first.

**Lead with whether the master is green**, with its cold seconds before and
after. Then the diff: lines added, what `EnvSet` now carries, what the Mem
row now derives. Then **the projected price of the other eleven rows, with
its basis named**. Then every hypothesis added and what supplies it. Then
whether each tie survived your refutation attempt. Then the C-39 section:
any line of this brief that blocked a route. **Mark every negative MEASURED
or INFERRED.** Then the DD4 answer with the lines saved.
