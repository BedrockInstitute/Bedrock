# LJ-1.103: restate absorbs-subset, and re-check Devlin55

tier: codex (default)

## GOAL

**Repair a false hypothesis in a delivered master.** `absorbs-subset` is
refuted. It is a parameter of `Devlin55`, and `BoundedSubsetAt` is inside
`Devlin55`. **So the phase's main theorem module is vacuous as it stands.**

## CWD

`/Users/alsg/Agentic/Bedrock`, on branch `two-tower-bridge`, clean at
`03fa4d2` except `dev/PLAN.md`. HEAD is green. **A sibling agent holds the
other Agda slot.**

## WHAT IS MEASURED, and I verified all of it myself

`[LJ-1.101]` refuted `absorbs-subset` (`src/L/BoundedSubset.lagda.md:1364-1368`):

```agda
(absorbs-subset : (α x : S) → ((z : S) → ⟨ z ∈ˢ x ⟩ → ⟨ z ∈ˢ Lset α ⟩)
                → ⟪ Lset α ∪ ⁅ x ⁆s ⟫ ↪ ⟪ Lset α ⟫)
```

**It quantifies over ALL ordinals.** At `α = ∅` and `x = ∅`, `Lset ∅` is
empty, and the union carries the witness `∅`, so the injection maps a
witness into an empty type. `AbsorbsRefute.refute`
(`src/ProbeLJ1101A.agda:153-156`) closes it. **I re-ran the probe: exit 0.**

**I checked the blast radius in the source.** `Devlin55` runs from
`src/L/BoundedSubset.lagda.md:1361` to the end of the file at `:1627`, and
`module BoundedSubsetAt` is at `:1396`, inside it. **About 266 lines of the
wing's main theorem sit under an empty telescope.**

`[LJ-1.101]` also closed the good news, and I verified that too:
**`cardκ` typechecks at the MASTER's `IsCardinal`**, no transport
(`src/ProbeLJ1101A.agda:56-57`, `open BS using ( IsCardinal; _↪_ )` at
`:23`). Exit 0, 3.46 s. **The cardinal blocker is genuinely closed.**

## WHAT TO DO

1. **Find the true statement.** `[LJ-1.101]` names two candidates:
   - **the site instance**, `α = ω`, `x = ∅`, priced 20 to 30 lines;
   - **the general infinite form**, priced 150 lines (band 80 to 200),
     with the union PRESENTATION as its widest unmeasured term.
   **Do not take either from the report. Read the uses in `Devlin55` and
   say what the body actually needs**, at `file:line`.
   **The narrowest true statement that the body still uses is the answer.**
   The obvious candidate is the same statement with `⟨ ω ∈ˢ α ⟩` added as a
   premise. **Check whether the body ever applies it at a finite `α`.**

2. **Restate it in the master** and **re-check `Devlin55` end to end.**
   You may edit `src/L/BoundedSubset.lagda.md`. **It is GREEN when you
   finish, or you revert it and say so.**

3. **Report the diff**: lines changed, and the master's cold seconds before
   and after, with the load average.

4. **Try to refute your own new statement**, the same way `[LJ-1.101]`
   refuted the old one. **Say REFUTED or NOT REFUTED. A statement that
   survives your own attack is worth more than one nobody attacked.**

## THE ABORT CRITERION, fixed in advance per D-1

- **The restated hypothesis holds and `Devlin55` re-checks green**: report
  the diff and the seconds, and STOP. **Do not go on to supply it.**
- **The body genuinely needs the finite case**: STOP and say where, at
  `file:line`. **That would mean the theorem's own proof used the false
  generality, and it is a much larger finding.**
- **Your restatement is refutable**: STOP and report it.
- **Anything walls**: STOP, report the wall with its seconds. **The master
  is heavy. A wall on its check is a real measurement.**

## C-12, AND THIS IS NOT BOILERPLATE

`[LJ-1.80]` left **SIX agda processes alive at once**, all children of one
wrapper, all on the same probe, none killed. Each carried `-M8g`: 48 GB of
worst case on a 64 GB machine at load 19. **The owner caught it; no tool
did.**

**ONE agda process at a time, and a sibling agent holds the other slot. The
load has been near 6. If a check does not return, KILL IT before you start
another, and report the wall with its seconds.**

## WHAT YOU MUST NOT DO

- **Do not weaken the theorem's conclusion.** Only the hypothesis moves.
- **Do not delete the hypothesis.** `Devlin55`'s body uses it.
- **Do not pin the hypothesis to one site** unless the body permits nothing
  wider. **A theorem that holds only where it is applied is not a theorem;
  say so if that is what you find.**
- **Do not touch anything under `src/L/Coding/`, `src/V/` or
  `src/L/Condensation/`.**
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

**`absorbs-subset` is about stages and injections, not about definability**,
so a corrected form should be shared content. **Say whether the J tower gets
the corrected statement unchanged.**

## THE COST QUESTION

The wing is over DD24 and the owner ruled the threshold question is settled
when the phase's content is complete. **So measure, do not gate.** Report
the master's cold seconds before and after the edit, and the non-blank
in-fence lines changed, with the load average.

## ARCHIVE (DD18)

- **`_build/lj-1.101-report.md`**, read WHOLE, and **`src/ProbeLJ1101A.agda`**,
  read WHOLE. The refutation and the two candidate forms.
- **`src/L/BoundedSubset.lagda.md:1361-1627`**, read WHOLE. **The whole of
  `Devlin55`, which is what you are repairing.**
- `src/L/StageCardinal.lagda.md:205-215` and `:555-565`,
  `stage-card-lower` and `stage-card-upper`, which the general form would
  ride.
- `src/L/Axioms/Basic.lagda.md:485-495`, the empty set in a stage.
- `_build/lj-1.94-report.md` and `src/ProbeLJ194A.agda`, the site that
  applies it.
- `dev/LESSONS.md` **C-38 as extended**, C-36, D-10, D-29, D-30, read
  WHOLE. **D-10 is the rule this defect breaks.**

Return an **ARCHIVE USED** section at `file:line`.

## LITERATURE (DD18)

**Devlin's 5.5 uses this absorption.** Say in two lines what he assumes
about the stage, from `dev/literature/devlin-II5.md`. Spend little.

## SCOPE (read)

`src/L/BoundedSubset.lagda.md:1361-1400` FIRST, then the uses of
`absorbs-subset` in the rest of `Devlin55`, then
`src/ProbeLJ1101A.agda:140-160`.

## SCOPE (write)

`src/L/BoundedSubset.lagda.md` (**green at the end or reverted**) and
`src/ProbeLJ1103*.agda`. Your report is `_build/lj-1.103-report.md`.
**Never `src/Everything.lagda.md`.**

## MANDATORY RULES FOR A BUILD

Run `python3 scripts/rules.py --for build` and `--for rewrite`, and read
every statement.

- **D-10.** The rule this defect breaks: a recorded hypothesis must be
  dischargeable.
- **C-38 as extended.** A closure or absorption hypothesis must be
  conditional, and the condition must be one the site can supply.
- **C-36.** Write the term you could not write.
- **C-35.** A block with no consumer is UNTESTED.
- **D-30.** Price what the CONSUMER needs.
- **P-l.** A price from a comparable elsewhere is a hypothesis.
- **P-i, P-w, P-h, P-k, P-m, P-n, P-o, P-q, P-t, P-u, P-v** as the bundle
  gives them.
- **P-c, R-36, R-38.** Seal at the birth site; expose with a read lemma.
- **R-35, R-40.** State the membership SHALLOW and climb. **R-35 is the
  union-presentation class, which is this repair's hard part.**
- **I-5.** The inference trap this tree has paid for.
- **C-12.** ONE agda process, cap never raised.
- **C-22.** Write the deliverable incrementally.
- **C-31, C-32, C-33, C-34, C-37.**
- **D-1, D-8, D-26, D-29.**

## CONSTRAINTS

- Never commit, never push, never `git checkout .`, `git stash`,
  `git reset --hard` or `git clean`.
- Do NOT run `make check`.
- **Run `scripts/check-fences.py --check`** and say the master count.
- Count with `scripts/ledger.py`. Run `scripts/lint-prose.py --check` and
  `scripts/lint-agda.py --check` on anything you touch.
- DD23 freezes mathematical prose. **The master carries mathematical prose:
  change the code, not the prose, unless a sentence becomes false. If one
  does, say which and leave it.**
- **Report the load average beside every absolute figure.**
- Evidence is `file:line`. Write ASD-STE100.

## RETURN

Write `_build/lj-1.103-report.md` incrementally, skeleton first.

**Lead with the restated hypothesis, quoted**, and whether `Devlin55`
re-checks green, with the seconds before and after. Then whether your own
refutation attempt succeeded. Then the diff size. Then, if the body needs
the finite case, where. **Mark every negative MEASURED or INFERRED.** Then
the DD4 answer. Confirm the master is green or reverted.
