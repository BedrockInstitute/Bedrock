# LJ-1.335: where do the `sq` band terms LAND, and what re-plumbing does it cost?

tier: opus (in-harness-subagent-mode), the switch's DEFAULT row. I ran
`scripts/dispatch/dispatch_policy.py` before writing this line.

## THE SITUATION

**Three bands of `sq` now have built terms and NONE of them is landed.**

| band | term | where |
|---|---|---|
| successors | `sq-suc`, 25 code lines, green | `agents/tasks/LJ-1-330/ProbeLJ1330A.agda:120-152` |
| non-initial limits | `limit-truncated`, 32 code lines, green | `agents/tasks/LJ-1-332/ProbeLJ1332A.agda:196-204` |
| `Init` and ω | delivered in `src/` already | `SquareLaw.lagda.md:960`, `InjChain.lagda.md:184` |

**`[LJ-1.330]` refused to land its own term and named why:**

> **`BoundedSubsetAt` at `src/L/BoundedSubset.lagda.md:1385` has NO consumer in
> `src/`, and that chapter imports neither `L.Absorption` nor `L.InjChain`.
> MEASURED.** **So the landing site is a real open question.**

**A probe that stays in `agents/tasks/` forever is a probe that was never
funded.** **This task settles where the work goes.**

## THE QUESTION

**Where should each term land, what does the landing cost, and what does the
consumer need re-plumbed?**

## THE FOUR THINGS TO SETTLE

**1. THE HOME.** For each term: which master, and why that one. **`P-k` is the
law: a read lemma is stated where its consumers use it.** **So find the
consumers first and let them decide the home.**

**2. THE IMPORT COST.** `[LJ-1.330]` INFERRED that landing `sq-suc` pulls
`L.Absorption` and `L.InjChain` back into the GCH closure. **`[LJ-1.326]`
BOUNDED that at 51 masters, 9,953 lines and 39.1 percent, by construction**
(`dev/ledger.toml:206-211`). **CONFIRM or refute it by re-running the closure
with each term's imports.** `ledger.py --reuse` runs no Agda.

**3. THE CONSUMER.** **`BoundedSubsetAt` takes `sq` as a Π-indexed AMBIENT
family** at `src/L/BoundedSubset.lagda.md:1388-1391`. **`[LJ-1.333]` measured
that this is exactly what blocks the truncated band**: a propositional
conclusion untruncates a fixed number of data points, not a family indexed by
the site.

**So say plainly: can the three untruncated bands be supplied to that parameter
TODAY, leaving only the limit band open?** **If yes, the chapter goes from「one
unsupplied family」to「one unsupplied BAND」, which is a real narrowing and it
can land now.**

**4. THE SHAPE OF A PARTIAL SUPPLY.** **If a band-split parameter is the right
form, say what it looks like.** **If splitting the parameter would touch the
delivered chapter's own signature, say what that costs and STOP: a signature
change to a delivered chapter is the orchestrator's, not yours.**

## THE ABORT CRITERION, fixed BEFORE the run (D-1)

- **A HOME EXISTS FOR EACH TERM AND YOU NAME IT.** Report the homes, the import
  deltas and the re-plumbing. STOP. **Landing is mine.**
- **THE CONSUMER CANNOT TAKE A PARTIAL SUPPLY.** **Say why, at `file:line`.**
  Then the terms wait for the limit band and the project should know that.
- **THERE IS NO CONSUMER AT ALL.** `[LJ-1.330]` measured `BoundedSubsetAt` has
  none in `src/`. **If the whole chapter is unreached, say so: that is a DD13
  question and it changes what「landing」even means.**
- **THE RESTATEMENT MOVED THE TARGET.** `src/L/GCH.lagda.md` was restated
  yesterday and `sq` LEFT the trophy statement. **Check that the consumers still
  want what these terms give.**

## WHAT YOU MUST NOT DO

- **LAND NOTHING YOURSELF.** Write only in `agents/tasks/LJ-1-335/`. **`src/` is
  forbidden** (I-5). **Propose the diff; the orchestrator applies it.**
- **RUN NO AGDA unless a slot is free**, and prefer not to: **this task is
  placement and import analysis, and `ledger.py --reuse` needs no typechecker.**
  If you do run it, count the slots first:
  ```sh
  ps aux | awk '/libexec.*bin\/agda/ && !/awk/' | wc -l
  ```
  **`ps aux | grep -c '[a]gda '` and `grep -c 'libexec.*bin/agda'` BOTH
  over-count. MEASURED 2026-08-15.** `GHCRTS="-A64m -I0 -M8g"`, cap never
  raised.
- **Do not edit another task directory.** You may READ and RE-RUN the probes in
  `agents/tasks/LJ-1-330/` and `LJ-1-332/`.
- **Never commit, never push**, never `git checkout .`, `git stash`,
  `git reset --hard` or `git clean`. Do not run `make check`.
- **Create `agents/tasks/LJ-1-335/lj-1.335-report.md` in your FIRST five
  minutes** (C-22).
- Run `.venv/bin/python scripts/gate/lint-prose.py --check` on what you write.
  **No em dash in any language.**
- Evidence is `file:line`. Write ASD-STE100. Mark every negative **MEASURED**
  or **INFERRED**, in those words.

## THE PREMISE OF MINE MOST LIKELY TO BE WRONG

**Six of my last eight briefs carried a claim an agent measured FALSE.**
**The one at risk here: 「the three untruncated bands can be supplied to that
parameter today」.** **That is my inference from `[LJ-1.333]`'s wording, not a
measurement, and the parameter's exact shape may forbid a partial supply.**

## THE RULES

**P-k.** A read lemma is stated where its consumers use it.
**C-40.** Verify the CONSUMERS of a changed file, never the file alone.
**C-44, C-42, D-10, P-l, C-45, C-22, C-32, C-39.** I-5. **D-26.**
**DD0, DD4, DD8, DD13, DD18, DD23, DD24.**

Run `.venv/bin/python scripts/dispatch/rules.py --for recon` and read every
statement, opening the full entry for any law you act on.

## DD4

**Maximize the code the two proofs share, and write it generic.** One rule, two
ends, no metric and no checker. **NAME YOUR AXIS** (C-46), which is
AC-against-GCH, fixed at `scripts/measure/ledger.py:50`.

**Every term on this leg is tower-blind, MEASURED by its author.** **Say
whether landing preserves that, and report the closure delta for each home you
propose**, noting `dev/ledger.toml:204`: the GCH closure is read from a
STATEMENT whose proof is not wired, so it UNDERSTATES.

## ARCHIVE (DD18)

- **`agents/tasks/LJ-1-330/lj-1.330-report.md`** and
  **`agents/tasks/LJ-1-332/lj-1.332-report.md`**, the two terms and their own
  landing notes.
- **`agents/tasks/LJ-1-333/lj-1.333-report.md` section 2**, which measured why
  the consumer's motive does not help.
- **`archive/dev/TASKS-archived.md`**, taking SHAPE and never a claim.

**Return an ARCHIVE USED section naming ONE line read per archived file.**

## LITERATURE (DD18)

**No mathematical literature bears on where a delivered lemma is placed.** Say
so in one line and return a **LITERATURE USED** section.

## SCOPE (read)

`src/L/BoundedSubset.lagda.md:1380-1420` FIRST, the consumer's own parameter.

## SCOPE (write)

`agents/tasks/LJ-1-335/` only.

## RETURN

**Lead with ONE line: can the three untruncated bands land today, yes or no.**
Then each term's home with its reason. Then the closure delta per home. Then
what the consumer needs re-plumbed, as a diff you did NOT apply. Then whether a
band-split parameter touches a delivered signature. **Mark every negative
MEASURED or INFERRED.**
