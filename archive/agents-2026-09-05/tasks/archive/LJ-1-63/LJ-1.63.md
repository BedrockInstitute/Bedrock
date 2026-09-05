# LJ-1.63: find 11.83 seconds anywhere in the wing

tier: codex (default)

## GOAL

The whole leaf chain is placed and green. **The wing is 11.83 seconds over
DD24.** Find those seconds. **They may come off ANY module in the wing.**

## CWD

`/Users/alsg/Agentic/Bedrock`, on branch `two-tower-bridge`, at `f2c8643`.
**The working tree carries `[LJ-1.62]`'s uncommitted placement**: the
`KFacts` bundle and the whole leaf chain, `src/L/Condensation.lagda.md` at
6,390 in-fence lines against HEAD's 5,562. **It is green and it is over the
bar, which is why it is not committed. Do not discard it.** A backup patch
exists outside the repository.

## THE FRAMING THAT MATTERS, and it is not the one you will inherit

`[LJ-1.62]` concluded that about 12 s must come off **the chain**. **That is
the wrong target.** DD24 judges the **WING AGGREGATE**, which is a SUM, so a
second removed anywhere counts the same. I re-ran the gate myself and did the
arithmetic:

```text
wing now: 118.12 s over 8,358 lines = 0.0141   (1.28x the bar 0.012716)
ceiling at this line count: 106.28 s
SECONDS THAT MUST COME OFF: 11.83
```

| module | lines | seconds | rate | against its own share |
|---|---:|---:|---:|---:|
| `src/V/Collapse.lagda.md` | 335 | 1.89 | 0.0056 | 2.37 under |
| `src/L/Hull.lagda.md` | 431 | 2.71 | 0.0063 | 2.77 under |
| **`src/V/Presentation.lagda.md`** | 18 | 0.65 | 0.0361 | **0.42 OVER** |
| `src/FOL/Count.lagda.md` | 620 | 1.62 | 0.0026 | 6.26 under |
| **`src/L/StageCardinal.lagda.md`** | 564 | 11.51 | 0.0204 | **4.34 OVER** |
| `src/L/Condensation.lagda.md` | 6,390 | 99.73 | 0.0156 | 18.47 OVER |

**`StageCardinal` and `Presentation` hold 4.76 s between them, and nobody has
looked at either module this phase.** That leaves 7.07 s to find in the
chain, not 12.

**Take the cheap seconds first.** A second from `StageCardinal` is worth
exactly as much as a second from `LeafAgree`.

## WHERE TO LOOK, in order

### 1. `src/L/StageCardinal.lagda.md`, 564 lines at 0.0204, 4.34 s over

This is where `[LJ-1.47]`'s square-law cure landed, and it still sits at
1.6x the bar. **Profile it first and say where its seconds are.**
`[LJ-1.47]` measured 5.45x on this file's neighbourhood by asking what the
CONSUMER needs (D-30), and four of five general-law sections turned out to
have no consumer at all. **Ask that question again here.**

`sq` still carries a module parameter whose discharge is `[LJ-1.17]` route 1.
**That reshaping is still not your task; the seconds are.**

### 2. `src/V/Presentation.lagda.md`, 18 lines at 0.0361, 0.42 s over

**Eighteen lines costing 0.65 s.** Say what it is and whether it needs to be
in the wing at all. **If it is a definition with no consumer, that is D-13's
question and the answer belongs in your report, not in a deletion.**

### 3. The chain's hot definitions, 7.07 s

`[LJ-1.62]`'s profile names them: `LeafAgree.out` 4,113 ms,
`LeafAgree.back` 4,095 ms, `SatGraphAgree.back` 3,289 ms,
`SatGraphAgree.out` 1,950 ms, `SatGraphAgree.body-back` 951 ms,
`body-out` 929 ms, `TwelveAgree.back` 749 ms, `.twelveB` 720 ms, `.out` 708 ms.

`[LJ-1.62]` classed these as **P-n content, a payable floor**, and classed
the claim that a statement-level re-spelling would help as **INFERRED, not
measured at this site.**

**Measure it.** P-n's admissible moves are less instantiation or accepting
the floor. P-c, R-36 and R-38 say seal at the birth site and expose with a
read lemma in its own `opaque unfolding` block.

## WHY I THINK THE FLOOR IS WORTH TESTING, and this is my reasoning, not a fact

**Every INFERRED wall this phase has fallen when somebody measured it:**

| the inferred wall | what measurement found |
|---|---|
| `[LJ-1.50]`'s 150 s obstruction | one unnamed proof; **681x** |
| `[LJ-1.55]`'s "only K is hard-coded" | every slot; the fix was mechanical |
| `[LJ-1.59]`'s hand-written forward walk | `Lift12Out`; **2.6x fewer seconds** |
| `[LJ-1.61]`'s module-header cost | the `KFacts` bundle; **30 s** |

Four for four. And `scripts/dd25-record.py` reports **13 reviews, 9 overturn,
69 percent**, with the tool's own note that a rate at or above 60 percent
indicts the upstream process rather than the reviews.

**That is a reason to measure, not a promise that it will fall.** If it is a
floor, say so with the number and stop.

## THE ABORT CRITERION, fixed in advance per D-1

`python3 scripts/check-ratio.py --check` is the gate and its **AGGREGATE** is
the verdict.

- **Under the bar**: **STOP and report.** Do not go on to the post-leaf five;
  a green wing with the whole leaf chain placed is the deliverable, and I
  will commit it.
- **Still over after your best attempts**: **STOP and report the price**, with
  each attempt's measured before and after, and the residual in seconds.

**Either way this dispatch ends at the gate.** Do not attempt `levelIn` or
`cover`.

**The gate's guard may refuse in your sandbox** (`pgrep` cannot read the
process list). Say so, bypass it as `[LJ-1.61]` and `[LJ-1.62]` did, and keep
every Agda invocation sequential so C-12's intent holds. **I re-run the gate
myself with a working guard, and my runs have agreed with yours twice.**

## WHAT YOU MUST NOT DO

- **You may not weaken a statement to make it cheap, and you may not narrow a
  direction.** Both directions are needed; that is settled.
- **Do not delete content to buy the ratio.** P-q measured that removing
  duplicated content removes lines and almost no seconds, so a deletion makes
  the ratio WORSE by shrinking the denominator faster than the numerator. I
  measured this for the prepared compression patch: it raises the ratio.
- **Archive, never delete**, if a module turns out to be unneeded, and that is
  a report finding rather than an edit (DD13, D-13).
- **Do not touch anything under `src/L/Coding/`.**
- All masters carry ZERO placement of `absFo` or a placed `Δ₀`.

## THE CLASSIFICATION I WANT ON EVERY NEGATIVE

State for every negative whether its deciding claim is **MEASURED** or
**INFERRED**, in those words. **A negative that rests on an inference sets no
verdict.**

## DD4

**Maximize the code the two proofs share, and write it generic.** One rule,
two ends, no metric and no checker, so it is stated in every brief and
answered in every return.

`[LJ-1.62]` found the bundle packages the sharing rather than reducing it,
and no placed type mentions a concrete carrier. **Keep that.** If a cure of
yours reduces what the J tower inherits, name the trade before you take it.

## ARCHIVE (DD18)

- **`_build/lj-1.62-report.md`**, read WHOLE. Sections 2, 3 and 4 are the
  spellings, the profile split and what was tried.
- **`_build/lj-1.47-report.md`**, read WHOLE. **The square-law cure, 5.45x
  from the D-30 question, and it is the closest measured analogue to
  `StageCardinal`.**
- `_build/lj-1.61-report.md` section 4, the wall before the bundle.
- `_build/lj-1.17-report.md` for `sq`'s surviving parameter, which is context
  and not your task.
- `_build/gch-compression-audit.md`, for what is known removable and why it
  does not help the ratio.
- **`src/ProbeLJ161A.agda`** and the four earlier probes. They must survive.
- `dev/LESSONS.md` P-m, P-n, P-q, P-t, P-c, R-36, R-38, D-30, read WHOLE.
- `archive/rud-route/` for SHAPE only.

Return an **ARCHIVE USED** section at `file:line`.

## LITERATURE (DD18)

**Nothing in the literature prices a spelling.** Say so in one line and spend
nothing.

## SCOPE (read)

The gate table above FIRST, then `src/L/StageCardinal.lagda.md` WHOLE, then
`src/V/Presentation.lagda.md` WHOLE, then `_build/lj-1.62-report.md`
section 3.

## SCOPE (write)

`src/L/Condensation.lagda.md`, `src/L/StageCardinal.lagda.md`,
`src/V/Presentation.lagda.md`, `src/L/BoundedSubset.lagda.md`, and
`src/ProbeLJ163*.agda`. Your report is `_build/lj-1.63-report.md`. **No other
master. Never `src/Everything.lagda.md`.**

## MANDATORY RULES FOR A BUILD

Run `python3 scripts/rules.py --for build` and `--for probe`, and read every
statement.

- **D-1.** The probe doctrine; the abort criterion is fixed above.
- **P-i.** The conversion-explosion playbook: select the cure by its decision
  tree, not by trial.
- **P-h.** Module-parameterized, never function-parameterized.
- **P-k.** A read lemma is stated where its consumers use it.
- **P-l, P-m, P-n, P-q, P-t, P-u, P-v** as above, each with its action.
- **P-c, R-36, R-38.** Seal at the birth site; expose with a read lemma.
- **R-35, R-40.** State the membership SHALLOW and climb.
- **I-5.** The inference trap this tree has paid for.
- **C-12.** `GHCRTS="-A64m -I0 -M8g" agda <file>`, ONE process, cap never
  raised. **A heap exhaustion is a WALL with its seconds.**
- **C-22.** Write the deliverable incrementally.
- **C-31, C-32, C-33, C-34, C-35, C-36, C-37.**
- **D-8, D-10, D-13, D-26, D-29, D-30.**

## CONSTRAINTS

- Never commit, never push, never `git checkout .`, `git stash`,
  `git reset --hard` or `git clean`. **The tree carries uncommitted work that
  is not in HEAD; do not discard it.**
- Typecheck what you touch and every consumer. Do NOT run `make check`.
- **Run `scripts/check-fences.py --check` before you report anything closed.**
- Count with `scripts/ledger.py`. Run `scripts/lint-prose.py --check` and
  `scripts/lint-agda.py --check`.
- DD23 freezes mathematical prose. Code and its own comments only.
- **The machine is quiet and both Agda slots are yours. Report the load
  average beside every absolute figure.**
- Evidence is `file:line`. Write ASD-STE100.

## RETURN

Write `_build/lj-1.63-report.md` incrementally, skeleton first.

**Lead with the gate's aggregate verdict, quoted, and the seconds you
removed and from where.** Then each attempt with its measured before and
after in one caliber. Then, for anything that did not move, **the term you
could not write** and whether the floor claim is now MEASURED. **Mark every
negative MEASURED or INFERRED.** Then the DD4 answer and **the convergence
answer.**
