# LJ-1.153: a delivered frame states a hypothesis that is FALSE

tier: opus (version `override`, set 2026-08-13; the head for every case is in
`scripts/dispatch_policy.py`, which is the only place the tables live)

## GOAL

**`[LJ-1.151]` REFUTED `valK` as stated, with a probe that exits 0.** Repair it
and every sibling of the same shape, so that the theorems conditional on them
stop being vacuous.

## THE REFUTATION, and I verified every part myself

**`src/L/Condensation/TwelveAgree.lagda.md:155-157`:**

```agda
(valK : (k : ℕ) (c ar a b yc : S) → ⟨ fst c ∈ fst (lookup ... γ') ⟩
        → fst c ≡ pr (fst ar) (pr (# k) (pr (fst a) (fst b)))
        → ⟨ fst yc ∈ fst (lookup ... γ') ⟩)
```

**`yc` occurs in NO premise.** So instantiate `yc := K` and the hypothesis
yields `K ∈ K`, which `∈-irrefl` closes.

**`agents/tasks/LJ-1-151/ProbeLJ1151B.agda:58` does exactly that**, exit 0:

```agda
absurd = ∈-irrefl (fst K) (valK k c₀ ar a b K c∈ shape)
```

**The refutation needs no property of `K` beyond `K : S`.**

**So this is not a debt. It is a DEFECT.** `[LJ-1.113]` measured only that
`valK` is not DERIVABLE; that it is FALSE is new, and a theorem conditional on
a false hypothesis proves nothing.

## THE BLAST RADIUS, MEASURED by me before dispatch

`.venv/bin/python scripts/check-unbound-hyp.py` reports **38 hypotheses worth a
refutation attempt**, of which **20 lines carry 「conclusion subject
unconstrained」**:

| name | flags |
|---|---:|
| `valK` | **17** |
| `valK-un` | 3 |
| `unCodesK`, `domK`, `domEntryK`, `codesK` | 2 each |
| `wUnCodesK`, `wEntryK`, `wCodesK`, `gUnCodesK`, `gEntryK` | 1 each |
| `ih` (`src/L/StageCardinal.lagda.md:281`) | 1, and it is 「no premise at all」 |

**Most sites are in `src/L/Condensation.lagda.md`**, at `:2740`, `:3249`,
`:3499`, `:3552` and more. **Count them yourself; that list is from a glance.**

## THE PRECEDENT, and it is the closest thing this project has to a playbook

**`[LJ-1.95]` through `[LJ-1.112]` did this once already**: eleven telescope
hypotheses machine-refuted as empty types, then repaired by **tying each to a
membership the row sites already hold**. `[LJ-1.112]` closed it at ZERO unsolved
metas.

**Read that arc before you write anything.** The cure shape is known: the
conclusion's subject must be constrained by a premise, and the premise must be
one the call sites can supply.

**`[LJ-1.151]` has already done the work for `valK`**: its 21-line supply
carries the graph membership `hc`, **which the row's `back` already binds.**
That is the repaired statement, and it is measured.

## WHAT TO DO

1. **Census every flagged hypothesis.** Name, site, and whether the same
   refutation applies. **A flag is a suspicion; a refutation is a fact.**
   `[LJ-1.97]`'s `ProbeLJ197A.agda` is the probe shape and the checker's own
   message points at it.
2. **For each one that IS refutable, repair the statement**, tying the free
   subject to a premise the call sites hold.
3. **Verify the call sites can still supply it.** **This is the half that
   decides the repair**: a statement nobody can instantiate is C-38's
   restatement, not a supply.
4. **Typecheck every consumer.** C-40.

## THE ONE-LINE FIX ALREADY NAMED

`[LJ-1.151]` names the master fix for `valK` in its report's C-39 section and
**deliberately did not apply it**, because `[LJ-1.150]` held that file at the
time. **That file is now free.** Start there, verify it, and say whether it
generalizes to the other 19.

## THE ABORT CRITERION

- **Every refutable hypothesis repaired and every consumer green**: report and
  STOP.
- **A repair cannot be supplied at the call sites**: **STOP AND SAY SO for that
  one.** That is C-38 firing and it means the row needs content, not a
  rewording.
- **A flag turns out NOT to be refutable**: say so, MEASURED, and leave it. The
  checker flags suspicion.
- **The repair changes what a theorem SAYS**: stop. **That is a mathematical
  change and it is the owner's, not yours.**
- **Anything walls**: STOP, report it with its seconds.

## WHAT YOU MUST NOT DO

- **Do not weaken a statement to make it true.** A hypothesis that is true
  because it says nothing is worse than one that is false, because the checker
  goes quiet.
- **Do not touch `src/L/Coding/Graph.lagda.md`**: 21 consumers are green on
  `[LJ-1.147]`'s seal.
- **Do not touch `src/ProbeLJ1134A.agda` or `src/ProbeLJ1136*.agda`.**
- **A probe goes in `agents/tasks/LJ-1-153/`**, never in `src/`, tracked, never
  deleted. **Read `AGENTS.md` and `dev/LESSONS.md` D-1 fresh; both changed
  today.**
- **ONE agda process, `GHCRTS="-A64m -I0 -M8g"`, cap NEVER raised.** A sibling
  is running Agda and measuring SECONDS. **Report the load; your figures are
  correctness, not timing, so a busy machine costs you only time.**
- Never `src/Everything.lagda.md`. Never commit, never push, never
  `git checkout .`, `git stash`, `git reset --hard` or `git clean`.
- Do not run `make check`; I run it. **Run `agda` on each changed master and
  each consumer.**

## THE CLASSIFICATION I WANT ON EVERY NEGATIVE

**MEASURED or INFERRED, in those words.** 「This one is not refutable」 is
MEASURED only if you tried and say how.

## DD4

**Maximize the code the two proofs share, and write it generic.** One rule, two
ends, no metric and no checker.

**`[LJ-1.151]` measured that 19 of its 21 lines name NO tower**, so the repaired
fact is template content and the per-tower part is 2 lines. **That corrects
`[LJ-1.146]` section 6, which put the instantiation on the per-tower side.**
**If your repairs are template content too, say so: it moves the whole
instantiation half of the bill.**

## ARCHIVE (DD18)

- **`agents/tasks/LJ-1-151/lj-1.151-report.md`** and **`ProbeLJ1151B.agda`**,
  read WHOLE. The refutation and the repaired statement.
- **`agents/tasks/archive/LJ-1-95/` through `LJ-1-112/`**: the eleven-name
  repair arc. **This is the playbook.**
- `agents/tasks/archive/LJ-1-97/ProbeLJ197A.agda`: the probe shape the checker
  names.
- `agents/tasks/LJ-1-113/lj-1.113-report.md`: the 28 pieces and what each was
  measured to be.
- **`dev/LESSONS.md` C-38 as extended, C-36, C-40, C-35**, read WHOLE.
- `scripts/check-unbound-hyp.py`, read WHOLE, for what it does and does not
  claim.

Return an **ARCHIVE USED** section at `file:line`.

## LITERATURE (DD18)

`dev/literature/devlin-II5.md`. **Say whether Devlin's own argument needs the
free subject at all, or whether it is an artifact of our frame.** Return a
**LITERATURE USED** section.

## SCOPE (read)

`src/L/Condensation/TwelveAgree.lagda.md:150-165` FIRST, then
`agents/tasks/LJ-1-151/ProbeLJ1151B.agda`, then the flagged sites in
`src/L/Condensation.lagda.md`.

## SCOPE (write)

`src/L/Condensation.lagda.md`, `src/L/Condensation/TwelveAgree.lagda.md`,
`src/L/StageCardinal.lagda.md`. Your report and probes are
`agents/tasks/LJ-1-153/`.

## MANDATORY RULES

Run `.venv/bin/python scripts/rules.py --for rewrite` and read every
statement.

- **C-38 as extended.** A hypothesis is discharged when something SUPPLIES it.
  **This task is C-38 at its sharpest: the hypothesis is not merely
  unsupplied, it is false.**
- **C-40.** Verify the CONSUMERS.
- **C-36.** Write the term you could not write.
- **C-39.** A brief's prohibition binds harder than its goal.
- **C-12, C-22, C-35, P-l, P-y, D-1, D-10, D-26, D-29, D-30.**
- **C-31, C-32, C-33, C-34, C-37. I-5.**

## CONSTRAINTS

- Count with `.venv/bin/python scripts/ledger.py`.
- **`.venv/bin/python scripts/check-unbound-hyp.py` must be reported before and
  after**, with the count.
- Run `scripts/lint-prose.py --check` and `scripts/lint-agda.py --check`.
- DD23 freezes mathematical prose. **Code comments are not prose; write them.**
- Evidence is `file:line`. Write ASD-STE100.

## RETURN

**Lead with how many were refutable, how many repaired, and the checker's count
before and after.** Then each repair: the statement before, after, and the
premise that now constrains the subject. Then which call sites supply it, at
`file:line`. Then every consumer's verdict. Then anything you could not repair
and why. **Mark every negative MEASURED or INFERRED.**
