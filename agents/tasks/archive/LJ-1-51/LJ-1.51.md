# LJ-1.51: discharge the five hypotheses

tier: codex (default)

## GOAL

Devlin 5.5 closes from **five unproved module parameters**. Discharge them, or
return a measured wall for each one that stands. **The route is now known to
fit**, so this is the last obstruction before the trophy.

## CWD

`/Users/alsg/Agentic/Bedrock`, on branch `two-tower-bridge`, clean at
`c88cb22`.

## THE FIVE, with their homes

| hypothesis | home | what discharges it |
|---|---|---|
| `levelIn` | `src/L/BoundedSubset.lagda.md:597`, `:953` | the level-hood adequacy at the hull's carrier; its deepest step, the collapse-of-the-level, has NO price and nothing measures it |
| `cover` | `:598`, `:954` | the rank/cofinality chain for hull members |
| `Mext` | `BoundedSubsetAt.Co` | provable from `hull-closed` plus LEM plus least-code selection; priced 120 to 250 lines by `[LJ-1.49]` |
| `sq` | `src/L/StageCardinal.lagda.md:15`, `BoundedSubset:907` | `[LJ-1.47]` measured the consumer's form at 744 lines and 7.94 s but did NOT build it as a master |
| `fin-inj` | `BoundedSubset:909` | the finite-stage injections into ω, 50 to 100 lines by `[LJ-1.21]`, unbuilt |

**C-35: a theorem whose hard part is a hypothesis is not the theorem.** Report
exactly which survive and why.

## THE ROUTE FITS, and here is the number that settles it

`[LJ-1.50-R]` overturned the apparent 150-second obstruction. **It was one
unnamed proof.** Naming the count proof instead of writing `refl` inline in
both a type and a body takes the identical `erase-Δ₀` call from **150,133 ms to
220 ms, a factor of 681.** I re-ran both ends myself: 154.92 s against 2.20 s.

**And the exit is delivered and green.** `src/ProbeDD25H2.agda` instantiates
`EraseTransfer` at the same leaf at 1.56 s, and **it never calls `erase-Δ₀` at
all**: `abs₀` recurses on the Δ₀ WITNESS, not the formula, so the certificate
never crosses `erase`. The matrix piece costs 811 ms. `src/ProbeDD25H8.agda`
holds the Σ₁ counterpart as 16 lines of template content with no `L` syntax.

**Use those probes.** They are the shape, and I verified all three.

## THE SPELLING RULE THAT DECIDES YOUR SECONDS

**P-v, extended today: give a proof a NAME and pass the name.** Writing the same
proof inline as `refl` in both a type and a body forces the elaborator to decide
a conversion between two elaborations of it, and deciding that unfolds the built
tree. **One named side is not enough**: the measured middle case is 151,402 ms.

**This is the single highest-leverage habit in this file. If a measurement of
yours comes out in the hundred-second range, look here first.**

## THE LAWS, each with the ACTION it prescribes (C-37)

- **P-u. CERTIFY BEFORE YOU PLACE**, and the action is to compose the
  absoluteness through the UNPLACED form. **That is `EraseTransfer`.** Do NOT
  build the certificate at variable slots: `[LJ-1.50]` measured that as slower,
  327 ms against 220.
- **P-t.** The class follows the FORMULA. The concrete-versus-variable carrier
  axis does NOT decide the cost, which is why the slot move failed.
- **D-30. Price what the CONSUMER needs.** 5.5 uses each of these at ONE shape.
  `[LJ-1.47]` measured 5.45x from exactly this question.
- **C-34.** Build the cure or report the wall that stopped you. **"It is a
  design decision" is not a third option.** This rule has been broken three
  times this phase, and each time a review built the deferred cure: 0.334 to
  0.0108, 0.436 to 0.0072, and 150 s to 1.56 s.
- **C-36.** A failed substitution is not a proof of impossibility. **Write the
  term you could not write.** You may strengthen a statement; you may not weaken
  one.

## ORDER OF ATTACK

**Cheapest and most certain first**, so a budget exhaustion still leaves the
theorem better off:

1. **`fin-inj`**, 50 to 100 lines, mechanical.
2. **`sq`**, whose consumer form is already measured at 744 lines and 7.94 s.
   **Build it as a master.** `[LJ-1.47]`'s two levers were deletions: four of
   five general-law sections had no consumer, and the order-type route is
   replaceable by the direct collapse injection.
3. **`Mext`**, priced 120 to 250 lines from `hull-closed`.
4. **`cover`**, the rank chain.
5. **`levelIn`**, whose deepest step has no price. **Price it before building
   it**, and if it walls, report the term you could not write.

**If you discharge only some, say exactly which and what each survivor still
needs.** A partial with an honest ledger is a full deliverable.

## THE THRESHOLD

DD24's live bar is **0.012716**, from the AC baseline 0.011057 times the 1.15
tolerance. **Do not use 0.013193.** The GCH aggregate sits inside the
run-to-run band around the bar, so **there is no margin**. Report the marginal
rate for what you add, the whole-file rate and the module-load cone separately,
each from three cold runs in ONE caliber with the spread.

## DD4

**Maximize the code the two proofs share, and write it generic.** One rule, two
ends, no metric and no checker, so it is stated in every brief and answered in
every return.

`sq` is cardinal arithmetic and `fin-inj` is a counting fact: **both are
template content that the J tower inherits.** `levelIn` and `cover` key on the
Def syntax, so D-26 predicts per-tower. **Say which side each discharge falls
on.**

## ARCHIVE (DD18)

- **`_build/lj-1.50-review.md`** and the probes `src/ProbeDD25H2.agda`,
  `H3`, `H8`, read WHOLE. C-32 exists because a brief of mine named a section
  and hid the decisive probe.
- **`_build/lj-1.47-report.md`** for `sq`'s consumer form and its two deletion
  levers.
- `_build/lj-1.49-report.md` for the hypothesis ledger and `Mext`'s price.
- `_build/lj-1.21-report.md` for `fin-inj`.
- `archive/rud-route/src/L/Ordinal/SquareLaw.lagda.md` for `sq`'s SHAPE. **Its
  target is sound here**, unlike the archived condensation.
- `dev/LESSONS.md` is NOT archived and still binds.

Return an **ARCHIVE USED** section at `file:line`.

## LITERATURE (DD18)

- `_build/literature/dev2.txt:1372-1385` for 5.5, and
  `dev/literature/devlin-II5.md` for what Devlin assumes about cardinal
  arithmetic. **He assumes it; the formal proof supplies it.** Say in one line
  what you had to supply.
- The errata do NOT cover Chapter II section 5. `[LJ-1.14]` verified it. **Do
  not re-check it.**

Return a **LITERATURE USED** section, with WHY NOT for anything skipped.

## SCOPE (read)

`_build/lj-1.50-review.md` and its three probes FIRST, then
`src/L/BoundedSubset.lagda.md`'s parameter lists, then
`_build/lj-1.47-report.md`.

## SCOPE (write)

`src/L/BoundedSubset.lagda.md`, `src/L/StageCardinal.lagda.md`, **at most ONE
new master under `src/L/`** for `sq`, and `src/ProbeLJ151*.agda`. Your report is
`_build/lj-1.51-report.md`. **No other master. Never
`src/Everything.lagda.md`.**

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
  NOT**, and must be labelled a stop with its bound.
- **C-22.** Write the deliverable incrementally.
- **C-31, C-32, C-33, C-34, C-35, C-36, C-37.**
- **D-10, D-26, D-29, D-30.**

## CONSTRAINTS

- Never commit, never push, never `git checkout .`, `git stash`,
  `git reset --hard` or `git clean`.
- Typecheck what you touch and every consumer. Do NOT run `make check`.
- **Run `scripts/check-fences.py --check` before you report anything closed.**
- Count with `scripts/ledger.py`. Run `scripts/lint-prose.py --check` and
  `scripts/lint-agda.py --check`.
- DD23 freezes mathematical prose. Code and its own comments only.
- **The machine is quiet and both Agda slots are yours.**
- Evidence is `file:line`. Write ASD-STE100.

## RETURN

Write `_build/lj-1.51-report.md` incrementally, skeleton first.

Lead with the ledger: which of the five are discharged and which survive, and
for each survivor what it still needs. Then the rates with spreads in one
caliber. Then, for anything that walled, the term you could not write. Then the
DD4 split and what you are not sure of.
