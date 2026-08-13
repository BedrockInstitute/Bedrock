# LJ-1.61: place the rest of the leaf chain, then take levelIn and cover

tier: codex (default)

## GOAL

The forward walk is placed and **the wing gate passes**. Place the rest of
the leaf chain, then take `levelIn` and `cover`.

## CWD

`/Users/alsg/Agentic/Bedrock`, on branch `two-tower-bridge`, **clean at
`24ada39`**. There are no working-tree edits.

## THE CRITERION CHANGED, AND THE OLD ONE WAS MINE AND WRONG

`[LJ-1.60]` returned NO-GO against a whole-FILE rate. **That criterion was
wrong and I wrote it.** DD24 judges the **WING AGGREGATE**, not a file.

`scripts/check-ratio.py`'s own header, lines 40 to 44:

> **THE PER-MODULE FLAG IS ADVICE; THE AGGREGATE IS THE JUDGMENT.** A single
> module may sit above the bar for a reason the wing as a whole pays back,
> which is exactly what a shared parameterized core does for its
> instantiations. **Only the aggregate fails the run.**

I ran the real gate on the placed tree:

```
  OVER 0.0136   5,355 lines   73.07 s   src/L/Condensation.lagda.md
  wing aggregate 0.0125 s/line over 7,323 lines and 91.40 s, WITHIN the bar
```

**`L.Condensation` sits above the bar and the wing passes anyway.** That is
the case the tool's header describes. **Do not stop on a per-file rate.**

## THE ABORT CRITERION, fixed in advance per D-1

**`python3 scripts/check-ratio.py --check` is the gate. Run it, and use its
aggregate verdict.**

- **Under the bar**: keep placing.
- **Over the bar**: **STOP and report the aggregate with the per-module
  table.** Do not push on. A measured stop with the gate's own numbers is a
  full deliverable.

**Run the gate after each placement step, not only at the end**, so a
crossing is caught where it happened. The gate refuses to run beside a live
Agda process, so give it a quiet slot.

**It costs about six minutes.** Budget for at least three runs.

## A FIX YOU INHERIT

`check-ratio` used to pair HEAD line counts with working-tree seconds. **I
fixed it at `24ada39`**; `measure()` now counts the working tree. **Its
numbers are now same-caliber. Trust the tool, not the old readings**, and if
a figure in an older report disagrees with the tool, the tool is right.

## WHAT TO PLACE, all green probe content, both directions

- `ShapedAgree`, `WitnessAgree` (`src/ProbeLJ157A.agda` sections 4 to 5)
- `KeyAgree`, `DefinesAgree` (`src/ProbeLJ154A.agda:111-246`)
- the `TwelveAgree` composition (`src/ProbeLJ155B.agda:788`, `:951`, `:966`)
- `SatGraphAgree` (`src/ProbeLJ156A.agda` section 7, `:689-835`)
- `LeafAgree` (`src/ProbeLJ157A.agda` section 5, `:822-985`)

**These are PORTS, not re-proofs.** If you find yourself re-proving one,
stop and say which.

## THEN THE ACTUAL GOAL

`levelIn` and `cover` have now survived **nine dispatches**. `[LJ-1.60]`
records that the brief's old `:598-599` line references are stale and the
live statements sit in `HullStage.Condense`, `src/L/BoundedSubset.lagda.md:916-917`.
**Use the live ones.**

The post-leaf chain is `[LJ-1.57]` section 8's five terms:

1. `StepAgree` and `ApproxAgree` from `LeafAgree`.
2. `GraphAgree` and the `Adeq` form.
3. **The stage truth of `Adeq m` at ordinal hull members.** This is the one
   that needs the machine to story direction, which is why the forward walk
   had to be placed.
4. The ElemDown wiring (`[LJ-1.53]` wall 2, probe green).
5. The collapse of the level, `π (Lset m) = Lset (π m)`.

**Say in the ledger exactly where you stopped.**

## SOMETHING YOU MUST NOT DELETE

**`src/ProbeLJ157A.agda`, `ProbeLJ156A.agda`, `ProbeLJ155B.agda` and
`ProbeLJ154A.agda` hold the proofs you are porting.** A probe is never
committed, so they are the only copies. **Do not delete, do not overwrite,
do not let a cleanup take them.** Copy content forward; never move it.

## THE LAWS, each with the ACTION it prescribes (C-37)

- **P-t.** State an assembly as a telescope at abstract propositions.
  `Lift12Back` and `Lift12Out` are both placed and are your model.
- **P-l.** A measured cure does not transfer by analogy. **Re-measure at each
  site.** `[LJ-1.59]` inferred the mirror would land in the back rate class
  and `[LJ-1.60]` measured it 3.05x higher.
- **P-m.** Instantiation is the expensive class. **Say which class each block
  you place is in**, and expect the `out` content to be the heavier one: it
  carries the code-set membership and the component-in-K facts the `back`
  content never carried.
- **P-v.** Give a proof a NAME and pass the name.
- **C-34. Build the cure or report the wall.**
- **C-36.** A failed substitution is not a proof of impossibility. **Write
  the term you could not write.** You may strengthen; you may not weaken.

## WHAT YOU MUST NOT DO

- **You may not weaken a statement to make it cheap, and you may not narrow
  a direction.** `[LJ-1.58]` narrowed and `[LJ-1.59]` found the other
  direction was owed. **Both directions are needed. This is settled.**
- **Do not touch anything under `src/L/Coding/`.** If the machine looks
  wrong, STOP and report it.
- All masters carry ZERO placement of `absFo` or a placed `Δ₀`. **If you
  need one, STOP and report it.**

## WHAT IS SETTLED

- `fin-inj` and `Mext` are DISCHARGED. `sq` has a master whose parameter
  survives on a reshaping that is NOT your task.
- **The whole leaf chain is PROVED in both directions in the probes.** This
  is placement, not proof.
- The direction question is SETTLED: both directions are needed
  (`[LJ-1.59]` section 0). **Do not re-open it.**
- **Δ₀ IS the target.** Delivered `Σ₁`'s only base is `σ-Δ₀`.

## SOMETHING YOU WILL SEE AND MUST NOT TOUCH

The superseded **Row layer** (`RowTransfer`, `RowDecode`, eleven `*Row`
modules, five `*Decode` kits), about 613 lines. **The compression patch is
NOT your task, and I measured that it would RAISE the ratio, not lower it.**

## THE CLASSIFICATION I WANT ON EVERY NEGATIVE

State for every negative whether its deciding claim is **MEASURED** or
**INFERRED**, in those words. **A negative that rests on an inference sets no
verdict.** This has produced something on each of the last five dispatches.

## DD4

**Maximize the code the two proofs share, and write it generic.** One rule,
two ends, no metric and no checker, so it is stated in every brief and
answered in every return.

Every placement so far kept the template shape: no placed type mentions a
concrete carrier, and `Lift12Out` is one instantiation of `Lift12Back`
rather than a copy. **Keep that and say so.**

## ARCHIVE (DD18)

- **`_build/lj-1.60-report.md`**, read WHOLE. Its section 1 is the placed
  forward walk and its section 5 the DD4 answer. **Its section 0 verdict is
  superseded by the wing gate; the measurements in it are sound.**
- **`_build/lj-1.59-report.md`** sections 0 and 2, the direction answer and
  the remaining chain.
- `_build/lj-1.58-report.md` section 2, the `Lift12Back` spelling.
- **`src/ProbeLJ157A.agda`**, `ProbeLJ156A.agda`, `ProbeLJ155B.agda`,
  `ProbeLJ154A.agda`, read WHOLE. Your sources, and they must survive.
- `src/ProbeLJ152A.agda`, `ProbeLJ152B.agda`, the pinned consumers and the
  post-leaf assembly shape.
- `_build/lj-1.52-report.md` and `_build/lj-1.51-report.md` for what
  `levelIn` and `cover` each still need, written as terms.
- `archive/rud-route/` for SHAPE only; `[LJ-1.11]` showed its condensation
  target is classically FALSE.
- `dev/LESSONS.md` is NOT archived and still binds.

Return an **ARCHIVE USED** section at `file:line`.

## LITERATURE (DD18)

**Banked. Spend nothing.** `[LJ-1.59]` read Devlin Step C and recorded that
the elementarity step transfers the bounded statement, and that the
production side is a tree fact rather than a literature fact. Return a
**LITERATURE USED** section saying that.

## SCOPE (read)

`_build/lj-1.60-report.md` section 1 FIRST, then the placed `Lift12Back` and
`Lift12Out` in `src/L/Condensation.lagda.md`, then `src/ProbeLJ157A.agda`
sections 4 to 5, then `src/ProbeLJ152A.agda`.

## SCOPE (write)

`src/L/Condensation.lagda.md`, `src/L/BoundedSubset.lagda.md`, and
`src/ProbeLJ161*.agda`. Your report is `_build/lj-1.61-report.md`. **No other
master. Never `src/Everything.lagda.md`.**

## MANDATORY RULES FOR A BUILD

Run `python3 scripts/rules.py --for build` and read every statement.

- **P-h.** Module-parameterized, never function-parameterized.
- **P-k.** A read lemma is stated where its consumers use it.
- **P-l, P-m, P-n, P-t, P-u, P-v** as above, each with its action.
- **P-c, R-36, R-38.** Seal at the birth site; expose with a read lemma.
- **R-35, R-40.** State the membership SHALLOW and climb.
- **I-5.** The inference trap this tree has paid for.
- **C-12.** `GHCRTS="-A64m -I0 -M8g" agda <file>`, ONE process, cap never
  raised. **A heap exhaustion is a WALL with its seconds.**
- **C-22.** Write the deliverable incrementally, and delete each placeholder
  as you fill it.
- **C-31, C-32, C-33, C-34, C-35, C-36, C-37.**
- **D-1, D-8, D-10, D-26, D-29, D-30.**

## CONSTRAINTS

- Never commit, never push, never `git checkout .`, `git stash`,
  `git reset --hard` or `git clean`. **The tree is clean; keep your work
  visible in it.**
- Typecheck what you touch and every consumer. Do NOT run `make check`.
- **Run `scripts/check-fences.py --check` before you report anything closed.**
- Count with `scripts/ledger.py`. Run `scripts/lint-prose.py --check` and
  `scripts/lint-agda.py --check`.
- DD23 freezes mathematical prose. Code and its own comments only.
- **The machine is quiet and both Agda slots are yours. Report the load
  average beside every absolute figure.**
- Evidence is `file:line`. Write ASD-STE100.

## RETURN

Write `_build/lj-1.61-report.md` incrementally, skeleton first.

**Lead with the ledger: what is placed, and are `levelIn` and `cover`
discharged.** Then `check-ratio --check`'s aggregate verdict, quoted. Then
for anything unbuilt, **the term you could not write**. **Mark every negative
MEASURED or INFERRED.** Then the rates with spreads in one caliber and the
load average, the DD4 answer, and **the convergence answer.**
