# LJ-1.109: tie the key-fact family, the last five of the eleven

tier: codex (default)

## GOAL

**Finish the eleven.** Six of the refuted names are out of the master. **Five
remain, and they are still stated and still USED.** Tie them, and the rows
stop being vacuous.

## CWD

`/Users/alsg/Agentic/Bedrock`, on branch `two-tower-bridge`.
**`src/L/Condensation.lagda.md` carries `[LJ-1.108]`'s deletions,
uncommitted and GREEN. A sibling agent works on the cardinal side and will
not touch this file.**

## WHAT IS LANDED

`[LJ-1.105]` put the shared half in `EnvSet`. `[LJ-1.108]` deleted the
unused refuted hypotheses from all nine rows: **`entryK` and `arSubK` gone
from every telescope, `tmKeyK` gone from `EqAgree`, `AllInAgree` and
`ExInAgree`. Master green, 6,433 non-blank in-fence lines, 147.9 to 148.4 s
cold.**

**Its remaining-occurrence grep is your work list.** `tmKeyK` survives only
in two prose comments. `entryK` survives as the DERIVED tied form inside
`EnvSet`, which is supplied. **What survives as a real row hypothesis is the
key-fact family.**

## THE FIVE, and all five are REFUTED

At the frame (`src/L/Condensation/TwelveAgree.lagda.md`), machine-checked in
`src/ProbeLJ197A.agda`:

| name | frame line | probe | why it is empty |
|---|---|---|---|
| `succK` | `:205-206` | `:136-139` | no premise; `sucV ar ∈ K` for free `ar`; 2-cycle |
| `keyK-un` | `:207-208` | `:151-155` | no premise; 4-cycle |
| `keyK-neg` | `:201-204` | `:171-174` | no premise; 3-cycle |
| `succK-allin` | `:224-228` | `:186-189` | no premise; 2-cycle |
| `keyK-allin` | `:229-235` | `:204-208` | no premise; 4-cycle |

**`succK` and `keyK-un` go through `succU` and `keyU`
(`src/L/Condensation.lagda.md` near `:3830`, VERIFY the line), whose bodies
ignore `C`, `T`, `B` and `N` entirely.**

**Their uses in the master, from `[LJ-1.108]`'s grep**: `SubValSuccB2T`'s
hypotheses, then `ForallAgree`, `ExistAgree`, `ClauseAgree`, `AllInAgree`,
`ExInAgree`. **VERIFY every line in the source; the master moved twice this
morning and every earlier line number is stale.**

## THE TIE, already measured supplyable

`[LJ-1.99]` measured it: **every one of these sites binds `ar ∈ K`, and
some also `a ∈ K` or `b ∈ K`.** So the tied forms are

- `succK`: `ar ∈ K → sucV ar ∈ K`;
- `keyK-un`, `keyK-neg`, `keyK-allin`: `ar ∈ K → a ∈ K → pr … ∈ K`;
- `succK-allin`: `ar ∈ K → sucV ar ∈ K`.

**Read `[LJ-1.99]`'s per-site table, then verify each binder in the source.**

**`KFacts` may not close these.** It has `pairK` (pairing INTO K) and
`arityK` (transitivity into K), but **`sucV a ∈ K` from `a ∈ K` is a
successor closure and `KFacts` has no such field.** **If the tie needs a new
`KFacts` field, say so, name it, and say why the consumer can hold it. Then
try to refute it.**

## THE RULE ON HYPOTHESES, stated as a test and not as a shape

**Every hypothesis you add must be one the CONSUMER can supply. Name what
supplies each, at `file:line`, before you add it.** A new `KFacts` field is
allowed if you say what would inhabit it; a hypothesis nothing can inhabit
is the defect this whole repair is about.

**Try to refute every tied form you write.** `src/ProbeLJ1104A.agda:118-120`
caught an empty tie one dispatch after that rule was written.

## THE ABORT CRITERION

- **All five are tied and the master is green**: report the diff, the cold
  seconds before and after, and STOP.
- **A tie needs something nothing supplies**: report it with the term you
  could not write, **and CONTINUE to the next name. Report the count.**
- **Anything walls**: STOP, report the wall with its seconds. **The master's
  cold check is about 148 s. My own re-check hit a two minute limit and I
  killed the process; there are no strays. Budget for the full check.**

**Do not stop at the first negative.**

## C-12, AND THIS IS NOT BOILERPLATE

`[LJ-1.80]` left **SIX agda processes alive at once**, all children of one
wrapper, all on the same probe, none killed. Each carried `-M8g`: 48 GB of
worst case on a 64 GB machine at load 19. **The owner caught it; no tool
did.**

**ONE agda process at a time, and a sibling agent holds the other slot. If a
check does not return, KILL IT before you start another, and report the wall
with its seconds.**

## WHAT YOU MUST NOT DO

- **Do not weaken any row's conclusion.**
- **Do not delete a used hypothesis without replacing it.** These five are
  USED, unlike `[LJ-1.108]`'s.
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

**`[LJ-1.105]` put the `entryK` and `arSubK` derivations inside `EnvSet`,
once, for nine rows.** Ask the same question here: **is there one place that
should hold the key-fact derivations, rather than five names at six sites?
`SubValSuccB2T` is the candidate. Say so or say why not.**

## THE COST QUESTION

The wing is over DD24 and the owner ruled the threshold question is settled
when the phase's content is complete. **So measure, do not gate.** Report
cold seconds before and after and the net non-blank in-fence lines, with the
load average. **`[LJ-1.108]` measured +8.1 to +8.6 s against a projection of
+2 to +4 s, and noted the run-to-run spread is itself 8.2 s. Say what your
spread is before you claim a delta.**

## ARCHIVE (DD18)

- **`_build/lj-1.108-report.md`**, read WHOLE. **Its section 2 grep is your
  work list.**
- **`_build/lj-1.99-report.md`**, read WHOLE. **The per-site table saying
  every site binds `ar ∈ K` and `a ∈ K`. That is the claim this dispatch
  cashes.**
- `_build/lj-1.105-report.md`, the shared-half landing and the DD4 shape.
- `src/ProbeLJ197A.agda`, the five refutations, read WHOLE.
- `src/ProbeLJ1104A.agda`, the proved row and its refutation of its own tie.
- `src/L/Condensation.lagda.md`: `SubValSuccB2T`, `succU`, `keyU`, the
  `KFacts` record. **Find them by name, not by line.**
- `dev/LESSONS.md` **C-38 as extended, C-39**, C-35, C-36, D-29, D-30, P-i,
  P-w, read WHOLE.

Return an **ARCHIVE USED** section at `file:line`.

## LITERATURE (DD18)

**Banked. Spend nothing.** Say so in one line.

## SCOPE (read)

`_build/lj-1.108-report.md` section 2 FIRST, then `_build/lj-1.99-report.md`
section 2, then `SubValSuccB2T` and the five names' uses in the master.

## SCOPE (write)

`src/L/Condensation.lagda.md` (**green at the end or reverted**) and
`src/ProbeLJ1109*.agda`. Your report is `_build/lj-1.109-report.md`.
**Never `src/Everything.lagda.md`.**

## MANDATORY RULES FOR A BUILD

Run `python3 scripts/rules.py --for build` and `--for rewrite`, and read
every statement.

- **C-38 as extended.** A closure hypothesis about a bounding set must be
  conditional, and the condition must be one the site can supply.
- **C-39.** A brief's prohibition binds harder than its goal. **If a line of
  this brief blocks a route you can see, say so in the report and name the
  route. That is a required section, not a courtesy.**
- **C-35, C-36, D-29, D-30, D-10.**
- **P-i.** The conversion-explosion playbook. **Read it whole.**
- **P-w.** A module application COPIES, and the copy is paid at USE.
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
  `git reset --hard` or `git clean`. **The working tree carries
  `[LJ-1.108]`'s uncommitted deletions. Losing them would cost a dispatch.**
- Do NOT run `make check`.
- **Run `scripts/check-fences.py --check`** and say the master count.
- Count with `scripts/ledger.py`. Run `scripts/lint-prose.py --check` and
  `scripts/lint-agda.py --check` on anything you touch.
- DD23 freezes mathematical prose. **Change the code, not the prose, unless
  a sentence becomes false. If one does, say which and leave it.**
- **Report the load average beside every absolute figure.**
- Evidence is `file:line`. Write ASD-STE100.

## RETURN

Write `_build/lj-1.109-report.md` incrementally, skeleton first.

**Lead with how many of the five are tied**, and whether the master is
green, with cold seconds before and after and your run-to-run spread. Then
the per-name table: tied form, site binder, supplier, refutation attempt.
Then any new `KFacts` field, with what would inhabit it. Then the C-39
section. **Mark every negative MEASURED or INFERRED.** Then the DD4 answer:
one place or five names.
