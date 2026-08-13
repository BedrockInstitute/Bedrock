# LJ-1.94: build the ambient Hartogs cardinal, and end at the consumer

tier: codex (default)

## GOAL

**Supply `cardκ` at the `[LJ-1.90]` site.** The gate is passed and the hard
half is measured. Build the five steps as a probe chain and end at the
consumer, not at a module boundary.

## CWD

`/Users/alsg/Agentic/Bedrock`, on branch `two-tower-bridge`, **clean at
`a1f0e95`**. HEAD is green. **A sibling agent holds the other Agda slot.**

## WHAT IS SETTLED, and what it cost to settle

`[LJ-1.90]` instantiated `BoundedSubsetAt` for the first time. **The one
hypothesis nothing supplies is `cardκ : IsCardinal κ`**
(`src/L/BoundedSubset.lagda.md:1397`), and `IsCardinal` appears **exactly
twice** in `src/`: its definition at `:1045-1046` and that hypothesis.

`[LJ-1.91]` found that **`IsCardinal` is AMBIENT**, which I verified myself:
`src/L/BoundedSubset.lagda.md:56` opens the V-structure and `:58` keeps the
L-structure qualified as `CS`. **So the internal `ω₁ᴸ` is not the route.**

`[LJ-1.92]` measured the widest term. **The order-type block re-instantiates
at a generic `SWO` carrier and checks GREEN**: `src/ProbeLJ192A.agda`, 365
non-blank lines, 18.4 s cold at load 3.3, one process at the C-12 cap.
**That probe is your starting material. Read it first and reuse it.**

**Two of `[LJ-1.92]`'s findings change what you should expect:**

- **`src/V/Collapse.lagda.md` does NOT carry this.** It collapses the
  hierarchy's own membership (`:40-58`, the recursion is `∈-induction`), not
  an arbitrary well-order. I read it and confirm this.
- **The image block is the expense: about 17 s of the 18.4 s.** `col-img`
  and `col-surj`, `src/ProbeLJ192A.agda:136-252`. The recursion shape is
  1.6 s. **Expect the same shape in your own build and do not be surprised
  by it.**

**The inferred seconds were wrong by 4.7x** (0.0107 s per line inferred from
the AC side, 0.050 s per line measured). **P-l again: a price anchored on a
comparable elsewhere is a hypothesis. Do not repeat it inside this
dispatch.**

## THE ROUTE, five steps

| step | content | lines | status |
|---|---|---:|---|
| 1 | the set `W` of well-orders on subsets of `ω` | 60 to 120 | unmeasured |
| 2 | the order type of a well-order | 365 | **MEASURED, green** |
| 3 | the Hartogs set itself | a few | unmeasured |
| 4 | ordinality and the countability facts | 70 to 150 | unmeasured |
| 5 | initiality, and the supply at the `[LJ-1.90]` site | 60 to 120 | unmeasured |

Steps 1, 3 and 4 ride delivered machinery: the V power set
(`src/V/Model.lagda.md:280-329`), separation (`:361-371`), and replacement
for the image of a small family.

## WHAT TO BUILD

**A probe chain that ends at the consumer.** Not a master. The phase has
delivered four blocks with no consumer and every one of them held a
statement-level defect that only a consumer found.

1. **Reuse `src/ProbeLJ192A.agda` for step 2.** Do not rewrite it.
2. Build steps 1, 3, 4 and 5.
3. **Finish by feeding the result into `src/ProbeLJ190A.agda`'s site**, so
   `cardκ` receives a VALUE. **That is the acceptance test.**

**C-38: a hypothesis is discharged when something SUPPLIES it, never when it
is restated.** Do not report a discharge from a parameter count. **That error
has been made four times this phase, twice by me.**

## THE ABORT CRITERION, fixed in advance per D-1

- **`cardκ` receives a value at the `[LJ-1.90]` site**: report the term at
  `file:line` with its seconds, and STOP. **Do not promote anything to a
  master.** That is a separate dispatch and it needs this one audited first.
- **A step cannot be built**: STOP at that step, write the term you could not
  write, and say what the tree would have to provide. **Report the steps that
  DID close, with their lines and seconds.** A partial chain with an honest
  boundary is a good return.
- **Anything walls**: STOP, report the wall with its seconds. **Do not raise
  the cap and do not split the file to get under it without saying so.**

**Work in `src/ProbeLJ194*.agda`.** If you touch a master it is GREEN when
you finish or you revert it. `[LJ-1.72]` and `[LJ-1.80]` each left one broken
and each cost a revert.

## C-12, AND THIS IS NOT BOILERPLATE

`[LJ-1.80]` left **SIX agda processes alive at once**, all children of one
wrapper, all on the same probe, none killed. Each carried `-M8g`: 48 GB of
worst case on a 64 GB machine at load 19. **The owner caught it; no tool
did.**

**ONE agda process at a time, and a sibling agent holds the other slot. If a
check does not return, KILL IT before you start another, and report the wall
with its seconds.**

## WHAT YOU MUST NOT DO

- **Do not assume the axiom of choice.** `[LJ-1.92]` measured the order-type
  core choice-free and LEM-free. **Keep it that way, and say at once if a
  step needs either.**
- **Do not weaken `IsCardinal`.** The consumer's statement is fixed.
- **Do not build a cardinal by assuming one.** A set that is a cardinal
  because a hypothesis says so is the defect this phase keeps finding.
- **Do not touch anything under `src/L/Coding/`.**
- **Never `src/Everything.lagda.md`.**
- **Do not raise the heap cap.** C-12.
- **Read line numbers and counts from the source, never from a report**, and
  say where a module ends if you report a count.

## THE CLASSIFICATION I WANT ON EVERY NEGATIVE

State for every negative whether its deciding claim is **MEASURED** or
**INFERRED**, in those words. **A negative that rests on an inference sets no
verdict.**

## DD4

**Maximize the code the two proofs share, and write it generic.** One rule,
two ends, no metric and no checker, so it is stated in every brief and
answered in every return.

**`[LJ-1.92]` measured the order-type block generic in the `SWO` carrier and
free of any tower object.** Keep the whole chain that way: **it is about
well-orders and injections, not about definability, so it should be the most
shared block of the phase.** Say whether any step you write breaks that, and
name the step.

## THE COST QUESTION

The wing is over DD24 and the owner ruled the threshold question is settled
when the phase's content is complete. **So measure, do not gate.** Report the
non-blank in-fence lines and the cold seconds **per step**, with the load
average beside every figure. **A per-step table is what the next decision
needs; a single total is not.**

## ARCHIVE (DD18)

- **`_build/lj-1.92-report.md`**, read WHOLE, and **`src/ProbeLJ192A.agda`**,
  read WHOLE. Your step 2, already green.
- **`_build/lj-1.91-report.md`**, read WHOLE. The five steps and why the
  internal Hartogs fails.
- `_build/lj-1.90-report.md` and **`src/ProbeLJ190A.agda`**. **The site you
  must reach.**
- `src/L/Ordinal/SquareLaw.lagda.md:146-496`, the delivered `col` machinery,
  and `:692-700` for `Init`.
- `src/L/WellOrder/Base.lagda.md:101-107`, the `SWO` record.
- `src/L/StageCardinal.lagda.md:205`, `:226-258`, the delivered ordinal
  well-order shape.
- `src/L/Ordinal.lagda.md:77-258`, the ordinal supply.
- `archive/rud-route/src/L/Ordinal/Pairing.lagda.md:436-575`, the archived
  order-type assembly, SHAPE only.
- `dev/LESSONS.md` **P-l, P-m, P-i, D-1, D-8, D-30, C-35, C-36, C-38**, read
  WHOLE.

Return an **ARCHIVE USED** section at `file:line`.

## LITERATURE (DD18)

**Banked. Spend nothing.** `[LJ-1.92]` settled it: Devlin assumes order
types and proves no order-type content in II.5
(`dev/literature/devlin-II5.md:145-166`). Say so in one line.

## SCOPE (read)

`src/ProbeLJ192A.agda` FIRST, then `src/ProbeLJ190A.agda`, then
`src/L/BoundedSubset.lagda.md:1040-1050` and `:1390-1402`, then
`src/V/Model.lagda.md:280-371`.

## SCOPE (write)

`src/ProbeLJ194*.agda`, and any master **only if you revert it before
finishing**. Your report is `_build/lj-1.94-report.md`. **Never
`src/Everything.lagda.md`.**

## MANDATORY RULES FOR A BUILD

Run `python3 scripts/rules.py --for build` and `--for probe`, and read every
statement.

- **C-38 as extended.** A hypothesis is discharged when something SUPPLIES
  it. **This dispatch is the supply site for `cardκ`.**
- **C-35.** A block with no consumer is UNTESTED. **End at the consumer.**
- **C-36.** Write the term you could not write.
- **D-30.** Price what the CONSUMER needs. **The consumer needs ONE cardinal,
  not a chapter.**
- **P-l.** A measured cure does not transfer by analogy, and neither does a
  price.
- **P-m.** The instantiation class, which is where `[LJ-1.92]`'s 17 s went.
- **P-i.** The conversion-explosion playbook. **Read it whole; heavy
  hypothesis packs go as module Pi-parameters, never as records.**
- **P-h.** Module-parameterized, never function-parameterized.
- **P-c, R-36, R-38.** Seal at the birth site; expose with a read lemma.
  **`src/ProbeLJ192A.agda` already does this for `col`; keep it.**
- **P-k, P-n, P-o, P-q, P-t, P-u, P-v, P-w** as the bundle gives them.
- **R-35, R-40.** State the membership SHALLOW and climb.
- **I-5.** The inference trap this tree has paid for.
- **C-12.** ONE agda process, cap never raised, **kill a hung check before
  starting another.**
- **C-22.** Write the deliverable incrementally.
- **C-31, C-32, C-33, C-34, C-37.**
- **D-1, D-8, D-10, D-26, D-29.**

## CONSTRAINTS

- Never commit, never push, never `git checkout .`, `git stash`,
  `git reset --hard` or `git clean`.
- Typecheck what you touch. Do NOT run `make check`.
- **Run `scripts/check-fences.py --check` before you report anything closed**
  and say the master count.
- Count with `scripts/ledger.py`. Run `scripts/lint-prose.py --check` and
  `scripts/lint-agda.py --check`.
- DD23 freezes mathematical prose.
- **Report the load average beside every absolute figure.**
- Evidence is `file:line`. Write ASD-STE100.

## RETURN

Write `_build/lj-1.94-report.md` incrementally, skeleton first.

**Lead with whether `cardκ` received a value at the `[LJ-1.90]` site**, with
the term at `file:line` and its seconds. Then the per-step table: lines,
cold seconds, load. Then, if a step did not close, the term you could not
write. **Mark every negative MEASURED or INFERRED.** Then whether any step
needs choice or LEM. Then the DD4 answer. Confirm every master is green or
untouched.
