# LJ-1.325: re-price PLAN 0.0 against the restated trophy, and gate both new debts

tier: opus (in-harness-subagent-mode), the switch's DEFAULT row. I ran
`scripts/dispatch/dispatch_policy.py` before writing this line.

## WHY THIS EXISTS

**The GCH trophy's STATEMENT changed last night**, by the owner's delegation and
the `[LJ-1.323]` ruling. It landed at `src/L/GCH.lagda.md`, `agda` exit 0 in
3 s. **`dev/PLAN.md` section 0.0 still prices the route that the OLD statement
demanded.**

**A price built on a superseded statement is not a stale number. It is a number
about a different theorem.**

## WHAT CHANGED, and read the file rather than this summary

**Read `src/L/GCH.lagda.md` WHOLE first.** Then
`agents/tasks/LJ-1-323/lj-1.323-ruling.md` sections 1, 3 and 4.

Three changes, and each moves the price differently:

1. **`sq : SqShape` LEFT the statement.** It is now an owed LEMMA rather than a
   hypothesis. **The work does not vanish; it moves from the statement to the
   proof.**
2. **Every ambient injection left.** The conclusion is now `InjL`, a coded
   injection inside the model.
3. **The conclusion became an EQUALITY**: `InjL (𝒫 κ) δ × InjL δ (𝒫 κ)`. **The
   second component is NEW.**

## THE TWO NEW DEBTS, and DD8 says a build brief that cannot name its widest
## unmeasured term is not ready to send

**`[LJ-1.323]` priced both by SURVEY and gated both. Your job is to make those
gates real.**

| debt | the ruling's survey price | what it rests on |
|---|---:|---|
| the final injection, delivered CODED | about 800 naive lines | the delivered coding-readback half of `src/L/Coding/Injection.lagda.md` |
| **the reverse bound `InjL δ (𝒫 κ)`** | about 600 naive lines | **NOT free: MEASURED, the tree has no Cantor lemma, grep zero hits** |

**FOR EACH DEBT, NAME:**

- **The WIDEST UNMEASURED TERM.** The one thing whose cost nobody has measured
  and which dominates the estimate.
- **THE SMALLEST DECISIVE MINIATURE that measures it**, as a probe somebody
  could build next, with what it would run and what its GO and NO-GO look like.
- **What the estimate becomes if the miniature says NO-GO.**

**The ruling already names one:** for the coded injection, **「the decisive
miniature is interning `absorbs` at its smallest site」**. **Check that reading
and either take it or replace it with a better one.**

**The reverse bound has NO named miniature and it is the one with no lemma
behind it. That is the most valuable half of this task.**

## THE RE-PRICING

**`dev/PLAN.md` section 0.0 carries a block of figures.** Re-derive it against
the new statement. **At minimum:**

- **The 470-line ingredient total.** `[LJ-1.310]` measured the composite's chain
  at 23 steps with 10 unbuilt and **about 175 hand-written lines OUTSIDE that
  470**. **Does the restatement change which steps are needed at all?** **A step
  that existed only to produce an ambient injection may now be dead.**
- **The endpoint figure, about 33,200.** **Say what it becomes, as ONE number
  with its basis named** (DD8: a probe, a delivered comparable, or a survey).
- **What the restatement DELETED from the price**, and say it plainly. The old
  statement's `sq` hypothesis, `AbsorbsShape` and `absorbsL` moved or left.
- **What it ADDED.** The two debts above.

**Give a NET.** **If the honest answer is that the restated trophy costs MORE,
say so in the first line of your report.** **The owner asked for the right
statement and was told the price would move; nobody has said which way.**

## WHAT ELSE THE RESTATEMENT MAY HAVE MOVED, and check each

- **The DD4 closure.** `ledger.py --reuse` reads `gch_root`, which is
  `src/L/GCH.lagda.md`. **Its imports changed: `_↪_` and `L.Absorption` left,
  `InjCode` and `_⊆ˢ_` arrived.** **Re-run it and report the new AC, GCH,
  SHARED and share figures against the old 73 / 51 / 44 and 39.1 percent.**
- **`dev/ledger.toml`'s `gch_root_why`** names `absorbs` as SUPPLIED and `sq`
  as the one remaining Pi-parameter. **Both sentences may now be false. Say
  exactly which words are wrong; the orchestrator edits the file.**
- **The standing line count.** `ledger.py --brief`. The file lost about 18
  lines.
- **Any dated record in `dev/` that quotes the OLD statement.** **List them at
  `file:line`; do not edit them.** A record is never rewritten, but the
  orchestrator must know which ones now describe a superseded theorem.

## THE ABORT CRITERION, fixed BEFORE the run (D-1)

- **BOTH DEBTS GET A NAMED TERM AND A MINIATURE.** Report them with the
  re-priced block. STOP. **That is the deliverable.**
- **A DEBT'S WIDEST TERM CANNOT BE NAMED WITHOUT A BUILD.** **Say so and say
  what the build costs.** An honest「this needs a probe to price」beats a survey
  number dressed as a price.
- **THE RESTATEMENT MAKES A DELIVERED CHAPTER DEAD.** **That is a large finding
  and it goes in your first line.** DD13 governs the retirement and
  `dev/ARCHIVE.md` would owe a record.
- **THE PRICE FALLS.** Equally possible and equally worth saying: the ambient
  injections leaving may delete more than the reverse bound adds.

## WHAT YOU MUST NOT DO

- **RUN NO AGDA.** **A sibling (`[LJ-1.322]`) is measuring CHECK TIMES and needs
  a quiet machine.** **Anything you start corrupts its figures.** **`ledger.py`,
  `--brief` and `--reuse`, does NOT run Agda; `check-ratio.py` DOES, so do not
  run it.** **If you believe a number needs a typecheck, name it and stop.**
- **Write only in `agents/tasks/LJ-1-325/`.** **Do not edit `dev/PLAN.md`,
  `dev/ledger.toml` or `src/`.** **The orchestrator lands every figure.**
- **Do not touch another task directory.**
- **Never commit, never push**, never `git checkout .`, `git stash`,
  `git reset --hard` or `git clean`. Do not run `make check`.
- **Create `agents/tasks/LJ-1-325/lj-1.325-report.md` in your FIRST five
  minutes** and fill it incrementally (C-22).
- Run `.venv/bin/python scripts/gate/lint-prose.py --check` on what you write.
  **No em dash in any language.**
- Evidence is `file:line`. Write ASD-STE100. Mark every negative **MEASURED**
  or **INFERRED**, in those words.

## THE RULES THIS CHAIN EARNED

**DD8. An estimate is ONE best-effort number and it names its basis.** **And a
build brief that cannot name its widest unmeasured term, and the probe that
measures it, is not ready to send.** **This task exists to make two such briefs
sendable.**

**C-44. A brief's claim is a measurement until you check it.** **Every figure in
`dev/PLAN.md` section 0.0 is some earlier agent's, and the statement under them
just changed.**

**P-l. A judgement at one site is a hypothesis at another**, and an expected
figure anchored on a comparable elsewhere is a hypothesis rather than a price.
**Both of the ruling's new prices are surveys against comparables. Treat them
as hypotheses.**

**D-10. Price the TRUTH of a recorded residue before pricing its proof.**
**Several residues in section 0.0 were recorded against the OLD statement.
Check each is still a residue at all.**

**C-42. A refutation measures the site it names.** **The restatement's effects
extend exactly as far as you measure them.**

## THE CLASSIFICATION I WANT ON EVERY NEGATIVE

**MEASURED or INFERRED, in those words.**

## DD4

**Maximize the code the two proofs share, and write it generic.** One rule, two
ends, no metric and no checker. **This task writes no code.**

**NAME THE AXIS** (C-46). DD4's own axis is AC-against-GCH, fixed in code at
`scripts/measure/ledger.py:50`. **The restatement changed `gch_root`'s imports,
so this task is the first chance to measure DD4's own figure against the new
statement.** **Report the four numbers and say which way the share moved and
why.** **And note `dev/ledger.toml:204`: the closure is read from a STATEMENT
whose proof is not wired, so it UNDERSTATES; the restatement may have changed
BY HOW MUCH.**

## ARCHIVE (DD18)

- **`agents/tasks/LJ-1-323/lj-1.323-ruling.md` sections 1, 3 and 4, read
  WHOLE.** The statement, the diff and the damage.
- **`agents/tasks/LJ-1-310/lj-1.310-report.md`**, the composite's 23-step chain
  and its 175 lines outside the 470. **The step table is what you re-check
  against the new statement.**
- **`agents/tasks/LJ-1-321/lj-1.321-report.md`**, which shrank the descent's
  debt to one canonical injection, and `[LJ-1.324]`, which refuted the most
  promising source for it.
- **`archive/dev/STATUS-archived.md` and `archive/dev/TASKS-archived.md`**,
  taking SHAPE and never a claim: the retired route was priced and re-priced
  too, and its endpoint band was overtaken. **Say what would not transfer.**

**Return an ARCHIVE USED section naming ONE line read per archived file.**

## LITERATURE (DD18)

**`dev/literature/truncation-and-selection.md` and
`dev/literature/level-formula-slot-roles.md`, both landed 2026-08-15.** **Say in
one line whether the literature bears on the reverse bound**, which is the debt
with no lemma behind it: **a set theorist gets `κ⁺ ≤ 2^κ` from Cantor and the
definition of the successor cardinal, and the question is what that costs
here.** Return a **LITERATURE USED** section.

## SCOPE (read)

`src/L/GCH.lagda.md` WHOLE first, then `dev/PLAN.md` section 0.0.

## SCOPE (write)

`agents/tasks/LJ-1-325/` only.

## MANDATORY RULES

Run `.venv/bin/python scripts/dispatch/rules.py --for recon` and read every
statement. **The tool prints `Full entry: dev/LESSONS.md:<line>` and says THIS
IS AN EXCERPT when it truncated. OPEN the full entry for any law you act on.**

- **DD8, C-44, P-l, D-10, C-42.** Named above with what each governs.
- **C-12.** No Agda in this task, and the reason is a sibling's timing runs.
- **C-52, C-53.** The two measurement laws written last night.
- **C-22, C-32, C-39, C-40, C-45.** I-5. **D-26.**
- **DD0, DD4, DD13, DD18, DD24.**

## RETURN

**Lead with ONE line: does the restated trophy cost MORE or LESS, and by how
much, with the basis named.** Then the two debts, each with its widest
unmeasured term and the smallest decisive miniature that measures it. Then the
re-priced section 0.0 block. Then the four DD4 closure numbers against the old
ones. Then the exact words in `dev/ledger.toml` that are now false. Then every
dated record that quotes the old statement, at `file:line`, unedited. **Mark
every negative MEASURED or INFERRED.**
