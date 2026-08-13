# LJ-1.57: the shapedness walk, then WitnessAgree, LeafAgree, and the two hypotheses

tier: codex (default)

## GOAL

`[LJ-1.56]` left **one unbuilt term**: the `shapesBS` against `shapes`
twelve-row frame walk. Build it, then `WitnessAgree`, then `LeafAgree`, then
**go back to `levelIn` and `cover`, which are the point of all of this.**

## CWD

`/Users/alsg/Agentic/Bedrock`, on branch `two-tower-bridge`, **clean at
`1e1c388`**. There are no working-tree edits.

## WHAT LANDED UNDER YOU, audited and committed

I audited `[LJ-1.56]`'s three cures myself and **upheld all three**. They are
in HEAD. `L.Condensation` and `L.BoundedSubset` are green.

**What is green and yours to build on, not to rebuild:**

- **`src/ProbeLJ156A.agda`**: `ClosedAgree` (all eight frames, both
  directions), `DomainAgree` (both directions), `TmBranch`/`TmAgree` (the
  term-shape atoms), `ConstVarDisjoint`, and **`SatGraphAgree` at the graph
  frame, both directions**.
- `src/ProbeLJ156Shape.agda`: `arTagBS` against `arityTagAtL`, both ways.
- `src/ProbeLJ155B.agda`: `TwelveAgree` at the `twelveB` frame.
- `src/ProbeLJ155C.agda`: the closedness bodies, and `oneSameB ≡ oneSameAt`.
- `src/ProbeLJ154A.agda`: `TagAgree`, `KeyAgree`, `EnvOneAgree`,
  `DefinesAgree`.

**Each of those states its agreement against the machine's own IMPORTED
definition**, not a restated copy. Keep that. It is what makes a cure
checkable instead of believable.

## THE ONE UNBUILT TERM

`shapesBS A K N0..N11` against `shapes`, the twelve-row frame walk: the
`binFormBS` and `unFormBS` frames and the disjunction
(`src/L/Condensation.lagda.md:1645-1690`).

**The atoms are done.** `TmAgree` proves the term shape both directions.
`arTagBS` transfers. The rows with `⊤̇` relations are trivial. **So this is a
walk over twelve disjuncts, not twelve new ideas.** If you find yourself
proving a new atom, stop and say which.

Then `WitnessAgree` = the membership atom, `ClosedAgree`, the bounded
existential frame, and `ShapedAgree`. Then `LeafAgree` = `KeyAgree` x
`WitnessAgree` x `SatGraphAgree` x `DefinesAgree`, one conjunction deep.

## THEN THE ACTUAL GOAL

`levelIn` and `cover` (`src/L/BoundedSubset.lagda.md:598-599`) have survived
six dispatches. **With `LeafAgree` built, take them.** `[LJ-1.52]` wrote what
`levelIn` needs as an explicit term; `[LJ-1.51]` recorded that `cover` needs
the same adequacy plus the least-delta selection.

**If your budget will not reach them, say so in the ledger rather than
leaving them unmentioned.**

## THE STANDING RULE FOR A CONVICTED DEFINITION, and it changed this round

**Four delivered definitions have now been convicted by their first
consumer**: `oneSameB`, `arTagBS`, `isTmBS`, `satGraphB`. Expect more. The
layer was written before any consumer existed and every gate passed over it.

**You are authorized to cure a delivered bounded restatement when a two-way
transfer against the machine's imported definition proves the correction.**
Three conditions, all of them:

1. **The cure carries its consumer test**, the two-way transfer, in a probe.
2. **You may strengthen; you may NEVER weaken.** A cure that makes a
   statement easier to prove is a defect, not a cure.
3. **You report every cure**, with the delivered reading, the corrected
   reading and the machine's reading, at `file:line`.

`[LJ-1.55]` stopped and waited for my ruling on `oneSameB`, which cost a
round trip. `[LJ-1.56]` cured three and consumer-tested each. **The second is
right.** This does NOT extend to changing a machine-side definition under
`src/L/Coding/`: if the machine looks wrong, STOP and report it.

## THE CLASSIFICATION I WANT ON EVERY NEGATIVE

State for every negative whether its deciding claim is **MEASURED** or
**INFERRED**, in those words. `[LJ-1.56]` did this and it turned an inherited
inference into a countermodel. **A negative that rests on an inference sets
no verdict.**

## THE SPELLING RULE THAT DECIDES YOUR SECONDS

**P-v: GIVE A PROOF A NAME AND PASS THE NAME.** The same proof inline as
`refl` in both a type and a body makes the elaborator decide a conversion
between two elaborations of it: **150,133 ms against 220 ms**. One named side
is not enough (151,402 ms). **If a measurement of yours lands in the
hundred-second range, look here before anywhere else.**

## THE LAWS, each with the ACTION it prescribes (C-37)

- **P-u. CERTIFY BEFORE YOU PLACE**, and the action is to compose absoluteness
  through the UNPLACED form, which IS `EraseTransfer`.
- **P-t.** The class follows the FORMULA, not the carrier.
- **P-m.** Instantiation content is the expensive class. `[LJ-1.56]` measured
  its probe at 0.0363 s per line against the atoms' 0.0034. **Say which class
  each block you write is in.**
- **D-30. Price what the CONSUMER needs.**
- **C-34. Build the cure or report the wall.**
- **C-35. A delivered block with no consumer is UNTESTED.** This is the law
  this whole sub-phase is paying out.
- **C-36.** A failed substitution is not a proof of impossibility. **Write the
  term you could not write.**

## WHAT IS SETTLED

- `fin-inj` and `Mext` are DISCHARGED. `sq` has a master whose parameter
  survives on a reshaping that is NOT your task.
- The twelve row agreements are PROVED and frame-generic. **Not a re-proof
  question.**
- **Δ₀ IS the target.** Delivered `Σ₁`'s only base is `σ-Δ₀`.
- All masters carry ZERO placement. **If you need `absFo` or a placed `Δ₀`,
  STOP and report it.**

## SOMETHING YOU WILL SEE AND MUST NOT TOUCH

`src/L/Condensation.lagda.md` carries a superseded **Row layer**
(`RowTransfer`, `RowDecode`, eleven `*Row` modules, five `*Decode` kits),
about 613 lines, dead in both directions. **A compression patch is prepared
and it is NOT your task.**

## THE THRESHOLD

DD24's live bar is **0.012716**. **Do not use 0.013193.** `[LJ-1.56]`
measured `L.Condensation` at 54.77 s over three cold runs, 4,640 in-fence
lines, rate **0.01181**, under the bar.

Report the marginal rate, the whole-file rate and the cone separately, each
from three cold runs in ONE caliber with the spread.

## DD4

**Maximize the code the two proofs share, and write it generic.** One rule,
two ends, no metric and no checker, so it is stated in every brief and
answered in every return.

`[LJ-1.56]` found the transfers are TEMPLATE content: every one states slots,
environments and site facts as module parameters with no concrete carrier in
any type. **Say whether the shapedness walk and `LeafAgree` keep that**, and
what the J tower inherits.

## ARCHIVE (DD18)

- **`_build/lj-1.56-report.md`**, read WHOLE, and its three probes
  `src/ProbeLJ156A.agda`, `Shape`, `Cone`, read WHOLE.
- **`_build/lj-1.55-report.md`** and `src/ProbeLJ155B.agda`,
  `src/ProbeLJ155C.agda`.
- `_build/lj-1.54-report.md` section 1 and `src/ProbeLJ154A.agda`, for the
  `WitnessAgree` decomposition.
- `_build/lj-1.52-report.md` and `_build/lj-1.51-report.md`, for what
  `levelIn` and `cover` each still need, written as terms.
- `_build/gch-design-audit.md`, the two-spelling section.
- `archive/rud-route/` for SHAPE only; `[LJ-1.11]` showed its condensation
  target is classically FALSE.
- `dev/LESSONS.md` is NOT archived and still binds.

Return an **ARCHIVE USED** section at `file:line`.

## LITERATURE (DD18)

`_build/literature/dev2.txt:1372-1385` and `dev/literature/devlin-II5.md`
Step C. `[LJ-1.56]` recorded that Devlin assumes the Σ₀ matrix is absolute
for transitive carriers where this tree proves a bounded transfer under
explicit membership facts. **Spend little; that answer is already banked.**
The errata do NOT cover Chapter II section 5; `[LJ-1.14]` verified it.

Return a **LITERATURE USED** section, with WHY NOT for anything skipped.

## SCOPE (read)

`_build/lj-1.56-report.md` sections 4 and 6 FIRST, then `src/ProbeLJ156A.agda`
sections 5 and 6, then `src/L/Condensation.lagda.md:1600-1700`, then
`src/L/Coding/Shape.lagda.md:109-250`.

## SCOPE (write)

`src/L/Condensation.lagda.md`, `src/L/BoundedSubset.lagda.md`, and
`src/ProbeLJ157*.agda`. Your report is `_build/lj-1.57-report.md`. **No other
master. Never `src/Everything.lagda.md`.**

## MANDATORY RULES FOR A BUILD

Run `python3 scripts/rules.py --for build` and read every statement.

- **P-h.** Module-parameterized, never function-parameterized.
- **P-k.** A read lemma is stated where its consumers use it.
- **P-l, P-m, P-n, P-t, P-u, P-v** as above, each with its action.
- **R-35.** State the membership at the SMALL index and climb.
- **R-38.** Seal at the birth site, and do NOT unseal.
- **R-40.** State a membership witness SHALLOW and climb.
- **I-5.** The inference trap this tree has paid for.
- **C-12.** `GHCRTS="-A64m -I0 -M8g" agda <file>`, ONE process, cap never
  raised. **A heap exhaustion is a WALL with its seconds; an interruption is
  NOT.**
- **C-22.** Write the deliverable incrementally. **`[LJ-1.56]`'s report sat
  at a skeleton for 47 minutes. Fill it as each answer lands.**
- **C-31, C-32, C-33, C-34, C-35, C-36, C-37.**
- **D-10, D-26, D-29, D-30.**

## CONSTRAINTS

- Never commit, never push, never `git checkout .`, `git stash`,
  `git reset --hard` or `git clean`. **The tree is clean; keep your work
  visible in it.**
- Typecheck what you touch and every consumer. Do NOT run `make check`.
- **Run `scripts/check-fences.py --check` before you report anything closed.**
- Count with `scripts/ledger.py`. Run `scripts/lint-prose.py --check` and
  `scripts/lint-agda.py --check`.
- DD23 freezes mathematical prose. Code and its own comments only.
- **The machine is quiet and both Agda slots are yours.**
- Evidence is `file:line`. Write ASD-STE100.

## RETURN

Write `_build/lj-1.57-report.md` incrementally, skeleton first.

Lead with the ledger: is `LeafAgree` built, and are `levelIn` and `cover`
discharged. For anything unbuilt, **the term you could not write**. Then every
cure, with the three readings. **Mark every negative MEASURED or INFERRED.**
Then the rates with spreads in one caliber, the DD4 answer, and **the
convergence answer: is this closing, or is each dispatch renaming the same
obligation?**
