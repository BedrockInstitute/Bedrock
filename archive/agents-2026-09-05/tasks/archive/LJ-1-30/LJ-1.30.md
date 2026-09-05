# LJ-1.30: price the upstream cure, making `consAtL` constant-free

tier: codex (default)

## GOAL

`[LJ-1.27]`'s gate went RED and `[LJ-1.27-R]` closed three of the four ways
out by measurement. **Price the fourth.** Make `consAtL` constant-free, so the
clause reaches the parameter-free axis through the DELIVERED `erase` with no
placement anywhere.

## CWD

`/Users/alsg/Agentic/Bedrock`, on branch `two-tower-bridge`.

## THE MECHANISM, and `[LJ-1.27-R]` marked it a HYPOTHESIS rather than a price

From `_build/lj-1.27-review.md:217-239`. The clause carries **17 constants**:
16 from `consAtL` and 1 from the numeral. If `consAtL` were constant-free and
the numeral moved to a slot, `countFo` of the clause would be **0**. A formula
with no constants reaches the parameter-free axis by the delivered `erase`:

- `erase : (φ : Formula K n) → countFo φ ≡ 0 → Formula (⊥* {ℓ}) n`
  (`src/FOL/Count.lagda.md:598-611`)
- `erase-inv : mapFo Empty.rec* (erase φ p) ≡ φ` (`src/FOL/Count.lagda.md:617-637`)

Then `σL = embed (erase φ refl)`, and `erase-inv` says `σL ≡ φ` as syntax. The
transfer becomes two syntactic `cong`s plus one `abs₀` at the original clause.
**`[LJ-1.27]` measured that `abs₀` at about 1.6 s**
(`_build/lj-1.27-report.md:95`).

`[LJ-1.27-R]` wrote the variant as `src/ProbeDD25E.agda`. **It fails at ONE
line only**, the `refl` asserting the count is zero. Read that probe and its
error first: the error message is the measurement.

**It did NOT measure the cure, because it needs a rewrite of `L.Coding.Model`
and `L.Coding.Environment`, outside a probe's scope. P-l forbids pricing it by
analogy.**

## THE RISK THAT IS ALREADY NAMED, and it may kill this

The 16 constants sit in `tagAt` and `shiftPairAt` inside `consAt`
(`src/L/Coding/Environment.lagda.md:338-343`). **Those readers name concrete
coded objects. Moving 16 constants into environment slots widens every
consumer's arity**, and nobody has measured what that costs.

`dev/LESSONS.md:2330-2348` records that **four of five transplants in this tree
FAILED**, and one made its module WORSE. **A widened arity across a delivered
coding layer is exactly the shape that has failed before.**

**So a NO-GO here is a likely and fully acceptable outcome.** Price it
honestly.

## THE FIVE QUESTIONS

1. **How many consumers does `consAtL` have, and what is each?** Name them at
   `file:line`. **Count them before you form an opinion**; a grep of use sites
   beats an impression.
2. **What does the arity widening actually cost** at each consumer, in lines?
   One best-effort number with its basis (DD8).
3. **Does the count really reach 0?** `[LJ-1.27-R]` says 16 of 17 constants
   come from `consAtL`. **Re-verify that with Agda's own count**, not by
   reading. `src/FOL/Count.lagda.md`'s `countFo` is the arbiter.
4. **What does the cured clause measure?** If you can build it, build it and
   measure. **The gate numbers are unchanged: GO at or below 0.013 s per line,
   NO-GO at or above 0.10.**
5. **Is the rewrite reversible?** The coding layer is delivered and green.
   **Say what would have to be re-verified if it lands**, and how many masters
   its import cone touches.

## WHAT YOU MAY WRITE

**Probes only: `src/ProbeLJ130*.agda`.** You may NOT edit
`src/L/Coding/Environment.lagda.md`, `src/L/Coding/Model.lagda.md` or any other
master. **This is a PRICING task, not the rewrite.**

If the rewrite cannot be priced without doing it, **say so with what you
learned and stop.** That is a full deliverable and it tells the owner the true
shape of the decision.

## DD4, WHICH GOES IN EVERY BRIEF

**Maximize the code the two proofs share, and write it generic.** One rule,
two ends. It has NO metric and no checker by the owner's ruling, so it is
stated in every brief and answered in every return; the repetition is its only
enforcement.

**The coding layer is TEMPLATE content and that raises the stakes both ways.**
If a constant-free `consAtL` is cleaner, both towers get it. If the widened
arity is a tax, both towers pay it. **Say which, and say whether the J tower's
structural certificate even uses `consAtL`.** `[LJ-1.27-R]` found the J
certificate avoids the syntax entirely (D-26), so it may not care at all.

## LITERATURE (DD18)

**None bears, and I have checked.** This is a coding-layer engineering
question about this tree's own representation choices. **Say so in one line
naming `dev/literature/` and spend nothing.**

## ARCHIVE (DD18)

- **`_build/lj-1.27-review.md` sections 4, 5 and 6**, and `src/ProbeDD25E.agda`
  with its error. **That probe is your starting point.**
- `_build/lj-1.27-report.md` section 4, the profile and the 1.6 s `abs₀`.
- `src/FOL/Count.lagda.md:598-611` and `:617-637`, `erase` and `erase-inv`.
- `src/L/Coding/Environment.lagda.md:338-343`, where the 16 constants live.
- `dev/LESSONS.md` is NOT archived and still binds. **P-l, P-m, P-t, P-u (new
  today), D-10 and D-26 decide this block.** P-u is the measured law: a Levy
  witness travels along a relabelling for free and does not travel along a
  placement at all.

Return an **ARCHIVE USED** section at `file:line`.

## MANDATORY RULES

**Run BOTH `python3 scripts/rules.py --for probe` and
`python3 scripts/rules.py --for recon`, and read each statement.**

- **D-1.** The smallest decisive miniature, GO or NO-GO with a price.
- **D-10.** Every figure in this brief is a residue one hour old. **Re-verify
  the 16-constant count before you build on it.**
- **P-l.** A measured cure does not transfer by analogy. Re-measure at its own
  site.
- **P-m.** The check-cost rate is a content-class certificate.
- **P-u.** Certify BEFORE you place. That law is why this route exists.
- **C-12.** `GHCRTS="-A64m -I0 -M8g" agda <file>`, ONE process. **Report a heap
  exhaustion as a wall and NEVER raise the cap**; `[LJ-1.27-R]` hit an 8 GB
  wall on the neighbouring route and reported it correctly.
- **C-22.** Write the deliverable incrementally.

## SCOPE (read)

`src/ProbeDD25E.agda` and its error FIRST. Then
`_build/lj-1.27-review.md:217-246`. Then `src/L/Coding/Environment.lagda.md`.
Then `src/FOL/Count.lagda.md` at the named lines.

## SCOPE (write)

`src/ProbeLJ130*.agda` and your report `_build/lj-1.30-report.md`. **No master.
No file under `dev/`. Never `src/Everything.lagda.md`.**

## CONSTRAINTS

- **Never commit and never push.** `scripts/check-probes.py` refuses a
  committed probe.
- **Never run `git checkout .`, `git stash`, `git reset --hard` or `git
  clean`.** `dev/` has uncommitted changes and a sibling recon is running.
- **Do NOT run `make check`.**
- **A sibling, `[LJ-1.29]`, is running and writes NO Agda**, so the machine is
  yours. Say if that changes.
- **Report cold seconds and the RATE**, noise rule: under 0.5 s or 5 percent,
  whichever is larger, is flat.
- **Evidence is `file:line`.**
- **A measured NO-GO is a SUCCESS**, and given the transplant record it is the
  likelier outcome.
- Write ASD-STE100 in the report.

## RETURN

Write `_build/lj-1.30-report.md` INCREMENTALLY, skeleton first.

1. **THE VERDICT**, first line: the price, or a measured NO-GO.
2. **THE CONSUMER COUNT** for `consAtL`, each at `file:line`.
3. **DOES THE COUNT REACH 0?** Re-verified with Agda's own `countFo`.
4. **THE ARITY WIDENING'S COST**, in lines, with its basis.
5. **WHAT THE CURED CLAUSE MEASURES**, if you could build it; what stopped you
   if not.
6. **IS THE REWRITE REVERSIBLE**, and how many masters its cone touches.
7. **DD4**: does the J tower use `consAtL` at all?
8. **ARCHIVE USED.** 9. **WHAT I AM NOT SURE OF.**
