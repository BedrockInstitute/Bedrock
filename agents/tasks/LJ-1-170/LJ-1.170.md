# LJ-1.170: price BOTH arms of the fork, so the owner rules on numbers

tier: opus (version `override`, set 2026-08-13; the head for every case is in
`scripts/dispatch_policy.py`, which is the only place the tables live)

## GOAL

**`[LJ-1.169]` found a genuine architecture fork and correctly refused to
publish a total.** `AGENTS.md` says an architecture fork is surfaced with a
recommendation and never charged ahead on one reading.

**Price BOTH arms. Recommend one. Do NOT take either.**

## THE FORK, and why it is real

`[LJ-1.169]` MEASURED that the rank-accounting argument holds by **Devlin's**
coding and not by **this tree's**:

- **Devlin's `K(u)` is finite SEQUENCES over a FIXED formula set**
  (`_build/literature/dev2.txt:600-608`, which I read: sequences of members of
  the formula set, the variables and the members of `u`). **His parameters cost
  one uniform finite bump.**
- **This tree BAKES the parameters into the code tree**: codes are nested
  Kuratowski pairs with the carrier's members at the leaves, and pairing shifts
  a stage by **TWO per pair** (`src/L/Axioms/Basic.lagda.md:596-599`).
  `[LJ-1.169]` proved the growth law and proved the omega-limit absorbs it.
- **And the coding layer is LEVEL-BLIND**, MEASURED: `src/L/Coding/Sat.lagda.md`
  and `Bridge.lagda.md` mention neither `Lset` nor `IsOrd`, not once. **So
  discharging `DefOK` or `PowOK` does NOT give `powIter`.**

## THE TWO ARMS

### ARM A: move the carrier to the omega-limit

**`[LJ-1.169]` recommends this.** Its evidence:

- **`src/L/Ordinal/StageArith.lagda.md` was written for it**, by its own comment
  at `:84-85`, and it is live, green, and had ZERO consumers until `[LJ-1.169]`.
- **The retired route REACHED exactly that bound at a general carrier**:
  `archive/src/2026-08-09-rud-route/L/Rud/SatTable.lagda.md:214-220` concludes
  `𝒟ₒ C ∈ˢ Sset (+ω δ)`. **That master is 109 in-fence lines**, which I
  measured.
- `powAtBlock` is 3 lines, and moving the CONCLUSION to `+ω` buys nothing while
  moving the CARRIER does.

**Its cost, per `[LJ-1.169]`: `closedω` plus successor closure at the
consumer.** **Price that.** How many consumers, and what does each pay?

### ARM B: re-code along Devlin's split

Codes become finite sequences over a fixed formula set, so parameters cost one
uniform bump instead of two stages per pair.

**Price the blast radius.** `src/L/Coding/` is the whole coding layer, and
`[LJ-1.168]` MEASURED that the coding cone is monomorphic in the L structure
(`src/L/Coding/Sequence.lagda.md:59-62`) and that `[LJ-1.10]` priced abstracting
it at 2.45k to 5.1k.

## WHAT TO DO

1. **Search first, and report what is delivered before any number.** This
   wing's measured blind spots are `src/L/Choice/`, `src/L/Axioms/Separation.lagda.md`
   and `src/L/Ordinal/StageArith.lagda.md`. **Five delivered zero-consumer files
   have held part of an answer this phase.**
2. **Price ARM A**: what changes, at how many sites, and what each consumer
   pays for the extra closure.
3. **Price ARM B**: what re-codes, and whether `[LJ-1.10]`'s 2.45k-to-5.1k
   figure is the right comparable or a false anchor like the 5,047 was.
   **`[LJ-1.168]` found that one quoted figure had never been measured. Check
   this one.**
4. **One best-effort figure per arm, each naming its basis** (DD8), **and the
   widest unmeasured term of each with the probe that would measure it.**
5. **Recommend one, in mathematics and in lines. Then STOP.**

## THE ABORT CRITERION

- **Both arms price**: report both, recommend one, STOP.
- **One arm is impossible for a reason you can state**: **that settles the fork
  and it is the best outcome here.** Say it first.
- **A third arm exists**: **say so.** `[LJ-1.169]` named two; it did not claim
  they were exhaustive.
- **Anything walls**: STOP with its wall-clock. **Never raise the cap.**

## WHAT YOU MUST NOT DO

- **DO NOT TAKE EITHER ARM.** This is a price. The fork is the owner's.
- **Do not edit any master.**
- **Do not price by analogy.** P-l is the reason this fork exists at all:
  `[LJ-1.167]` inferred the rank accounting from Devlin and `[LJ-1.169]`
  measured that it does not transfer.
- **A probe goes in `agents/tasks/LJ-1-170/`**, never in `src/`, tracked. **One
  probe per arm is allowed if a step cannot be priced by reading.**
- **ONE agda process, `GHCRTS="-A64m -I0 -M8g"`, cap NEVER raised. Fix a
  wall-clock criterion in writing before each run.**
- Never `src/Everything.lagda.md`. Never commit, never push, never
  `git checkout .`, `git stash`, `git reset --hard` or `git clean`.
- Do not run `make check`; I run it.

## THE CLASSIFICATION I WANT ON EVERY NEGATIVE

**MEASURED or INFERRED, in those words.**

## DD4

**Maximize the code the two proofs share, and write it generic.** One rule, two
ends, no metric and no checker.

**This fork is a DD4 question and that may decide it.** ARM B re-codes a layer
BOTH towers use; ARM A adds a closure obligation that may be per-tower.
**Say which arm leaves more shared, and by how much.**

## ARCHIVE (DD18)

**Five delivered zero-consumer files have held part of an answer this phase, and
three archive lookups changed a verdict.**

- **`archive/src/2026-08-09-rud-route/L/Rud/SatTable.lagda.md`**, 109 in-fence,
  read WHOLE. **It REACHED ARM A's bound at a general carrier. What did it pay,
  and what did it assume?** `[LJ-1.169]` found this after my brief pointed at
  the wrong file.
- **`archive/src/2026-08-09-rud-route/L/Coding/`** and `L/Definability.lagda.md`:
  did the retired route's coding bake parameters into the code tree, or not?
  **That answers whether ARM B has a delivered comparable at all.**
- **Take SHAPE, never a claim.** `[LJ-1.11]` ruled that route's condensation
  target classically FALSE.
- `agents/tasks/LJ-1-169/lj-1.169-report.md` and `LJ-1-168/`, read WHOLE.
- **`dev/LESSONS.md` P-l, DD8, C-38 as extended, C-36**, read WHOLE.

Return an **ARCHIVE USED** section at `file:line`.

## LITERATURE (DD18)

`_build/literature/dev2.txt:593-640` and `dev/literature/devlin-II5.md:240-260`.
**Say exactly what Devlin's `K(u)` contains, why his bound is uniform, and
whether ARM B would reproduce that or merely approximate it.** Return a
**LITERATURE USED** section.

## SCOPE (read)

`agents/tasks/LJ-1-169/lj-1.169-report.md` FIRST, then
`archive/src/2026-08-09-rud-route/L/Rud/SatTable.lagda.md`, then
`src/L/Ordinal/StageArith.lagda.md`.

## SCOPE (write)

`agents/tasks/LJ-1-170/` only. **No master.**

## MANDATORY RULES

Run `.venv/bin/python scripts/rules.py --for recon` and `--for probe`.

- **DD8.** One figure per arm, each naming its basis.
- **DD13.** Price a rewrite from the REWRITE side: the ideal form first, then
  compare. **「We already paid for it」 decides nothing.**
- **P-l, C-38 as extended, C-35, D-1, C-12, C-22, C-36, C-39, C-40.**
- **D-10, D-26, D-29, D-30. C-31, C-32, C-33, C-34, C-37. I-5.**

## CONSTRAINTS

- Count with `.venv/bin/python scripts/ledger.py`.
- Run `scripts/lint-prose.py --check` and `scripts/lint-agda.py --check`.
- DD23 freezes mathematical prose.
- Evidence is `file:line`. Write ASD-STE100.

## RETURN

**Lead with your recommendation in ONE sentence, then the two figures side by
side with their bases.** Then what is already delivered for each. Then the
widest unmeasured term of each and its probe. Then whether a third arm exists.
Then the DD4 answer. **Mark every negative MEASURED or INFERRED.**
