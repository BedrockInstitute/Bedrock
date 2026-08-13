# LJ-1.82: supply KFacts to the chain, at the stage

tier: codex (default)

## GOAL

**Feed the layer.** `KFacts` has a value at a limit stage and the stage is
the site the proof needs. **Instantiate the chain with it**, as far as it
goes, and report the first thing that blocks.

## CWD

`/Users/alsg/Agentic/Bedrock`, on branch `two-tower-bridge`, **clean at
`eae5033`**. HEAD is green.

## WHAT IS SETTLED, so you build rather than re-derive

**`KFacts` is inhabitable, machine-checked.** `src/ProbeLJ180A.agda:186-226`
builds `kfacts : KFactsNS.KFacts {14} A₀ K₀ ...` at `K = LsetS lam ordλ`, a
limit stage, with all twenty-seven fields supplied. **I re-ran it myself:
green, 1.59 s user.** Read that probe; it is your starting value.

**The stage is the site.** `[LJ-1.81]` read the consumer chain and I checked
its load-bearing step: in

```agda
Adeq m = ∥ Σ[ K' ∈ S ] Σ[ v' ∈ S ] Σ[ w' ∈ S ]
           (⟨ w' ∈ˢ K' ⟩ × ⟨ (w' ∷ v' ∷ m ∷ K' ∷ []) ⊨ LH0.matrix ⟩) ∥₁
```

**`K'` is EXISTENTIALLY quantified**, so the proof chooses the bound. It is
never the hull. **No `isL` certificate for `M` or `πX` is needed and none is
missing.**

**The closure facts are repaired** (`[LJ-1.79]`) and the old refutation no
longer typechecks against them.

## WHAT TO DO

**Instantiate the agreement chain with the stage's `KFacts`, and go as far as
it goes.** The chain, in order:

1. `ShapesAgree`, `ClosedAgree`, `ShapedAgree`, `WitnessAgree`
   (`src/L/Condensation.lagda.md:5753`, `:6033`, `:6133`, `:6159`), each
   taking `KFacts` as one parameter.
2. `SatGraphAgree` (`:6411`) and `LeafAgree` (`:6640`).
3. The twelve-row composition: `L.Condensation.TwelveAgree`, the composer
   master.

**Report the FIRST thing that blocks, at `file:line`, and stop there.**

## WHAT I EXPECT TO BLOCK, and I want it confirmed or refuted

**The association mismatch.** The composer proves

```text
twelveB = sixB ∧̇ sixB
```

where each `sixB` is a right-nested chain of six, while `SatGraphB.twelveB`
(`src/L/Condensation.lagda.md:2233`) is ONE right-nested chain of twelve.
`∧̇` is a Formula constructor, so those are different terms.

**I found that by reading and the fable review found it independently.
Nobody has measured what it costs to bridge.** If you reach it, say what the
bridge would be and whether the tree delivers a satisfaction-level
associativity for `∧̇`.

**But do not assume it is the first blocker.** Something earlier may go
first, and that would be the more useful finding.

## THE ACCEPTANCE TEST

**C-38: a hypothesis is discharged when something SUPPLIES it.** So:

- **Every module you instantiate must actually receive a VALUE**, not another
  parameter. Report each at `file:line`.
- **Say plainly how far the supply reaches** and what the first unsupplied
  hypothesis is.

**Do not report a discharge on a parameter count.**

## THE ABORT CRITERION, fixed in advance per D-1

- **You reach `LeafAgree` with everything supplied**: report it and STOP. Do
  not go on to `Adeq`, `levelIn` or `cover`.
- **Something blocks**: STOP there, write the term you could not write, and
  say whether it is the association bridge or something else.
- **Anything walls**: STOP, report the wall with its seconds.

**Work in `src/ProbeLJ182*.agda`.** If you touch a master it is GREEN when
you finish or you revert it; `[LJ-1.72]` and `[LJ-1.80]` both left one broken
and both cost a revert.

## C-12, AND THIS IS NOT BOILERPLATE

`[LJ-1.80]` left **SIX agda processes alive at once**, all children of one
wrapper, all checking the same probe, none of the earlier ones killed. Each
carried `-M8g`, so the worst case was 48 GB on a 64 GB machine at load 19.
**The owner caught it; no tool did.**

**ONE agda process at a time. If a check does not return, KILL IT before you
start another, and report the wall with its seconds.**

## WHAT YOU MUST NOT DO

- **You may not weaken a statement and you may not narrow a direction.**
- **Do not add a hypothesis to make a supply go through.** A value built from
  new assumptions supplies nothing. **If you need an assumption, that IS the
  term you could not write.**
- **Do not touch anything under `src/L/Coding/` or `src/V/`.**
- **Never `src/Everything.lagda.md`.**
- **Do not raise the heap cap.** C-12.
- Name probes `src/Probe*.agda`, never `.lagda.md`.

## THE CLASSIFICATION I WANT ON EVERY NEGATIVE

State for every negative whether its deciding claim is **MEASURED** or
**INFERRED**, in those words. **A negative that rests on an inference sets no
verdict.**

## DD4

**Maximize the code the two proofs share, and write it generic.** One rule,
two ends, no metric and no checker, so it is stated in every brief and
answered in every return.

**Say whether the supply is generic in the stage**, so the J tower supplies
its own `KFacts` the same way.

## ARCHIVE (DD18)

- **`src/ProbeLJ180A.agda`**, read WHOLE. **Your starting value.**
- **`_build/lj-1.81-report.md`**, read WHOLE. The consumer chain and why the
  stage is the site.
- `_build/lj-1.79-report.md`, the repaired fields and their suppliers.
- `_build/lj-1.76-report.md`, the three composer masters and what they prove.
- `_build/diag-twelve-row-math.md` section 1, the association finding.
- `dev/LESSONS.md` C-38 as extended, C-35, C-36, P-w, D-29, D-30, read WHOLE.
- `archive/rud-route/` for SHAPE only.

Return an **ARCHIVE USED** section at `file:line`.

## LITERATURE (DD18)

**Banked.** `[LJ-1.81]` answered what Devlin's bounding set is. Say so in one
line and spend nothing.

## SCOPE (read)

`src/ProbeLJ180A.agda` FIRST, then `_build/lj-1.81-report.md` section 1, then
`src/L/Condensation.lagda.md:6411` and `:6640`, then
`src/L/Condensation/TwelveAgree.lagda.md`.

## SCOPE (write)

`src/ProbeLJ182*.agda`, and any master **only if you revert it before
finishing**. Your report is `_build/lj-1.82-report.md`. **Never
`src/Everything.lagda.md`.**

## MANDATORY RULES FOR A BUILD

Run `python3 scripts/rules.py --for build` and read every statement.

- **C-38 as extended.** A hypothesis is discharged when something SUPPLIES
  it. **This dispatch is that supply.**
- **C-35.** A block with no consumer is UNTESTED.
- **C-36.** Write the term you could not write.
- **P-w as amended.** A module application copies; no interposition.
- **P-h.** Module-parameterized, never function-parameterized.
- **P-k, P-l, P-m, P-n, P-o, P-q, P-t, P-u, P-v** as the bundle gives them.
- **P-c, R-36, R-38.** Seal at the birth site; expose with a read lemma.
- **R-35, R-40.** State the membership SHALLOW and climb.
- **I-5.** The inference trap this tree has paid for.
- **C-12.** ONE agda process, cap never raised, **kill a hung check before
  starting another.**
- **C-22.** Write the deliverable incrementally.
- **C-31, C-32, C-33, C-34, C-37.**
- **D-1, D-8, D-10, D-26, D-29, D-30.**

## CONSTRAINTS

- Never commit, never push, never `git checkout .`, `git stash`,
  `git reset --hard` or `git clean`.
- Typecheck what you touch. Do NOT run `make check`.
- **Run `scripts/check-fences.py --check` before you report anything closed**
  and say the master count.
- Run `scripts/lint-prose.py --check` and `scripts/lint-agda.py --check`.
- DD23 freezes mathematical prose.
- **Report the load average beside every absolute figure.**
- Evidence is `file:line`. Write ASD-STE100.

## RETURN

Write `_build/lj-1.82-report.md` incrementally, skeleton first.

**Lead with how far the supply reached**, module by module at `file:line`,
and what the first unsupplied hypothesis is. Then, if you hit the
association mismatch, what the bridge would be and whether the tree delivers
it. **Mark every negative MEASURED or INFERRED.** Then the DD4 answer.
Confirm every master is green or untouched.
