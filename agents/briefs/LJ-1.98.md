# LJ-1.98: can the eleven refuted facts be TIED, and does the tie hold at the use site?

tier: codex (default)

## GOAL

**Decide repair against retirement with a measurement instead of an
inference.** Eleven facts of the shared frame are refuted. **Every one of
them is refuted for the same reason: a variable that should be tied to the
bounding set is free.** Find the tie each one was meant to have, and measure
whether the use site supplies it.

## CWD

`/Users/alsg/Agentic/Bedrock`, on branch `two-tower-bridge`, clean at
`4999160` except `dev/PLAN.md`. HEAD is green. **A sibling agent holds the
other Agda slot.**

## WHAT IS MEASURED, and I checked the shapes myself

`[LJ-1.95]` refuted `tmKeyK`. `[LJ-1.97]` refuted **ten more**, machine
checked in `src/ProbeLJ197A.agda`, which I re-ran: exit 0, 1.86 s, load 7.39.

**I read all ten types in the source and the diagnosis is one sentence: the
statement quantifies over a set that nothing binds.**

| fact | source | the free variable |
|---|---|---|
| `succK` `keyK-un` | `TwelveAgree.lagda.md:205-208` | `ar`, through `succU` and `keyU` (`Condensation.lagda.md:3635-3644`), **whose bodies ignore `C`, `T`, `B` and `N` entirely** |
| `keyK-neg` | `:201-204` | `ar` and `a` |
| `succK-allin` `keyK-allin` | `:224-235` | `ar`, and `b` |
| `entryK` | `:118-120` | **`z`**, which nothing constrains |
| `arSubK-mem/neg/top/imp` | `:121-132` | **`ar`**, the premise is `x ∈ ar` for a free `ar` |
| `tmKeyK` | `:96` | `k`, no premise at all |

## THE QUESTION, and it decides retire against repair

**For each of the eleven, what was the tie meant to be, and does the USE
SITE supply it?**

`[LJ-1.96]` already answered this shape once, positively: `valK`'s row use is
closed by `domEntryK`'s second projection, green at
`src/ProbeLJ196A.agda:50-52`. **That is the pattern. Repeat it here.**

1. **Read each fact's USE SITE in the rows**, inside
   `src/L/Condensation.lagda.md`. `[LJ-1.96]` section 2 lists many of them;
   **verify them in the source, do not take them from the report.**
2. **Write the tied form each use site actually needs.** Not an invented
   weakening: the form that the site's own binders make available. For
   `entryK` the candidate is the T-slot tie that `domEntryK`
   (`src/L/Condensation.lagda.md:6504-6506`) already states. For the
   `arSubK-*` family it is a tie of `ar` to the arity slot or to `K`.
3. **MEASURE the tie at the use site**, for **at least four** of the eleven,
   and **`entryK` must be one of them**. Machine-check that the site's
   binders supply the tie. **Copy `src/ProbeLJ196A.agda`, which is short.**
4. **Say for each of the eleven: TIED AND SUPPLIED, TIED BUT NOT SUPPLIED,
   or NOT ATTEMPTED.**

**Do not repair any master. This dispatch measures.**

## WHY THE ANSWER DECIDES THE PHASE

- **If the ties are supplied at the sites**, the eleven statements are a
  writing defect. The layer's content stands and the repair is bounded.
- **If several ties are NOT supplied**, the rows genuinely used the
  over-generality, the content is wrong and not only the statements, and
  **retirement becomes the honest answer.** That goes to the owner with a
  price.

**Say which of the two your measurement supports, and do not soften it.**

## THE ABORT CRITERION, fixed in advance per D-1

- **Four or more ties measured supplied**: report them and STOP. That
  supports repair.
- **A tie is measured NOT supplied**: STOP at that one, write the term you
  could not write, and say what the row would have to bind. **A single clean
  negative here is worth more than four positives.**
- **Anything walls**: STOP, report the wall with its seconds.

**Work in `src/ProbeLJ198*.agda`. Do not touch any master.**

## C-12, AND THIS IS NOT BOILERPLATE

`[LJ-1.80]` left **SIX agda processes alive at once**, all children of one
wrapper, all on the same probe, none killed. Each carried `-M8g`: 48 GB of
worst case on a 64 GB machine at load 19. **The owner caught it; no tool
did.**

**ONE agda process at a time, and a sibling agent holds the other slot. The
load is above 7 right now. If a check does not return, KILL IT before you
start another, and report the wall with its seconds.**

## WHAT YOU MUST NOT DO

- **Do not invent a tie that makes the fact true but useless.** The tie must
  be what the USE SITE needs. A hypothesis nobody can use is the same defect
  in a new place.
- **Do not weaken the row's conclusion.**
- **Do not repair, delete or archive any master.**
- **Do not touch anything under `src/L/Coding/` or `src/V/`.**
- **Never `src/Everything.lagda.md`.**
- **Do not raise the heap cap.** C-12.
- **Read line numbers from the source, never from a report.**

## THE CLASSIFICATION I WANT ON EVERY NEGATIVE

State for every negative whether its deciding claim is **MEASURED** or
**INFERRED**, in those words. **A negative that rests on an inference sets no
verdict.** `[LJ-1.96]` set one on inferences and `[LJ-1.97]` overturned half
of its table. **Do not repeat that.**

## DD4

**Maximize the code the two proofs share, and write it generic.** One rule,
two ends, no metric and no checker, so it is stated in every brief and
answered in every return.

**The sharpest reading of DD4 this phase came from `[LJ-1.93]`: sharing is
only free when the shared frame is the frame the consumer actually holds.**
Say whether the tied frame is a frame the consumer can hold.

## ARCHIVE (DD18)

- **`_build/lj-1.97-report.md`**, read WHOLE, and **`src/ProbeLJ197A.agda`**,
  read WHOLE. The ten refutations and the cycle lemmas.
- **`_build/lj-1.96-report.md`**, read WHOLE, and **`src/ProbeLJ196A.agda`**.
  **Its per-use table is your starting point and its `domEntryK` result is
  the pattern to copy. Verify its use sites in the source.**
- `_build/lj-1.95-report.md` and `src/ProbeLJ195A.agda`.
- `_build/lj-1.93-report.md` and its three probes.
- `src/L/Condensation.lagda.md:3635-3644`, `succU` and `keyU`.
- `src/L/Condensation.lagda.md:5734-5770`, the 29-field `KFacts`, and
  `:6476-6513`, the consumer's telescope and six site facts.
- `dev/LESSONS.md` **C-38 as extended**, C-35, C-36, D-29, D-30, read WHOLE.

Return an **ARCHIVE USED** section at `file:line`.

## LITERATURE (DD18)

**Banked. Spend nothing.** Say so in one line.

## SCOPE (read)

`src/ProbeLJ196A.agda` FIRST, then `_build/lj-1.96-report.md` section 2,
then the row use sites in `src/L/Condensation.lagda.md`.

## SCOPE (write)

`src/ProbeLJ198*.agda` only. Your report is `_build/lj-1.98-report.md`.
**No master. Never `src/Everything.lagda.md`.**

## MANDATORY RULES FOR A BUILD

Run `python3 scripts/rules.py --for build` and `--for probe`, and read every
statement.

- **C-38 as extended.** A closure hypothesis about a bounding set must be
  conditional, and the condition must be one the site can supply.
- **C-36.** Write the term you could not write.
- **C-35.** A block with no consumer is UNTESTED.
- **D-30.** Price what the CONSUMER needs.
- **D-1, D-8, D-10, D-26, D-29.**
- **P-h, P-i, P-k, P-l, P-m, P-n, P-o, P-q, P-t, P-u, P-v, P-w** as the
  bundle gives them.
- **P-c, R-36, R-38.** Seal at the birth site; expose with a read lemma.
- **R-35, R-40.** State the membership SHALLOW and climb.
- **I-5.** The inference trap this tree has paid for.
- **C-12.** ONE agda process, cap never raised.
- **C-22.** Write the deliverable incrementally.
- **C-31, C-32, C-33, C-34, C-37.**

## CONSTRAINTS

- Never commit, never push, never `git checkout .`, `git stash`,
  `git reset --hard` or `git clean`.
- Do NOT run `make check`.
- Run `scripts/lint-prose.py --check` and `scripts/lint-agda.py --check`.
- DD23 freezes mathematical prose.
- **Report the load average beside every absolute figure.**
- Evidence is `file:line`. Write ASD-STE100.

## RETURN

Write `_build/lj-1.98-report.md` incrementally, skeleton first.

**Lead with the count: how many ties are measured supplied, and how many
measured not.** Then the table, one row per fact: the use site, the tied
form, and the status in the three words above. Then, for any tie not
supplied, the term you could not write. **Mark every negative MEASURED or
INFERRED.** Then say plainly whether the measurement supports repair or
retirement. Then the DD4 answer. Confirm no master was touched.
