# LJ-1.17: is the square law affordable at DD24 at all?

tier: codex (default)

## GOAL

Decide whether the level-size chain can afford a square law under DD24, and at
what shape. **Price the IDEAL form written fresh today, do NOT port.** A
refusal that no shape fits the budget is a full deliverable and re-prices the
wing.

## CWD

`/Users/alsg/Agentic/Bedrock`, on branch `two-tower-bridge`.

## THE FINDING THAT COMMISSIONED YOU

`[LJ-1.6-R]`, an adversarial review, computed something nobody had: **the
wing's whole seconds budget.** DD24's bar of 0.013193 s per line over the
a-priori wing of 7,553 to 11,197 lines gives **99.6 to 147.7 seconds for the
entire GCH wing.**

**The archived square law does not fit in it.**

| scenario | lines | seconds | s/line | vs 0.013193 |
|---|---:|---:|---:|---|
| wing plus the delivered counting half | 1,394 | 5.46 | 0.0039 | 0.30x PASS |
| plus the square law at ledger figures | 2,677 | 47.36 | **0.0177** | **1.34x FAIL** |
| plus the square law at LJ-1.6's figures | 2,677 | 85.96 | **0.0321** | **2.43x FAIL** |

**In budget terms it consumes 28 to 42 percent of the wing's whole seconds
allowance for 11 to 17 percent of its lines.**

**THE FAIL DOES NOT DEPEND ON TODAY'S WING RATE.** Credit the delivered wing
with ZERO seconds and 47.36 over 2,677 is still over the bar. **It cannot be
absorbed by building everything else cheaply.** That is why this is a gate and
not a preference.

## THE NUMBERS ARE CORRECTED, so start from these

Two figures in the route's own record were wrong and `[LJ-1.6-R]` found both.
I verified both myself.

- **Lines: 1,283, not 1,540.** `archive/rud-route/src/L/Ordinal/SquareLaw.lagda.md`
  is 907 in-fence and `.../Pairing.lagda.md` is 376 in-fence. The 1,540 figure
  in `_build/lj-1.1-recon.md:251` added SquareLaw's in-fence to Pairing's FILE
  count of 633. A caliber error, 20 percent high.
- **Seconds: `dev/ledger.toml:1765` records SquareLaw 64.4 to 23.3, and
  `:1769` records Pairing 18.6.** The 61.9 s figure quoted elsewhere is stale
  by two supersessions.

**Re-verify both before you use them.** D-10, and this row has already carried
two wrong numbers.

## THE QUESTIONS, in order

**1. IS THE FULL SQUARE LAW NEEDED AT ALL?** The chain consumes `|L_α| = |α|`
for infinite α. Read `dev/literature/devlin-II5.md` sections 1.4, 1.5 and 5.2,
and Devlin 5.4 to 5.6. **Does that need `|α × α| = |α|` in full, or a weaker
bound the tree already has?** A negative answer here ends the task cheaply and
is the best outcome available.

**2. THERE IS A GAP NEITHER EARLIER DOCUMENT NAMED.** The archived square law
holds at **INITIAL ordinals only**, by its own prose at
`archive/rud-route/src/L/Ordinal/SquareLaw.lagda.md:956-963`, and `Init ω` is
uninhabited. The chain needs the level size at **arbitrary infinite ordinals**.
**The non-initial transfer is unpriced.** Price it, because a port that does
not reach the consumer is worth nothing however cheap it is.

**3. PRICE THE IDEAL FORM, NOT THE PORT.** `dev/PLAN.md` D17 and AGENTS.md say
plan from the REWRITE side: price the ideal form of the content written fresh
today, THEN compare. "We already paid for it" decides nothing in either
direction. `[T98]` found the archived module **presentation-bound**, which is
exactly the property that makes a port expensive and a rewrite cheap. **So the
central question is whether a presentation-free square law is affordable, and
that question has never been asked.**

**4. WHAT WOULD IT COST IN SECONDS, not lines?** This is a seconds gate. Give
one best-effort seconds figure for your recommended shape, with its basis, and
say what fraction of the 99.6 to 147.7 budget it takes.

## A CHEAP MEASUREMENT FIRST, BEFORE ANY PRICING

**Run a seconds gate on `Pairing` at DD24's declared caliber.** The ledger's
18.6 s was measured under a different protocol on a different tree. The
declared caliber is in `dev/ledger.toml`: `ac_baseline_ghcrts` is
`-A64m -I0 -M16g`, and the module rate is measured COLD with dependencies
WARM.

**You cannot run it in `src/`** because the module is archived and does not
typecheck against today's tree. So either measure it in a scratch copy, or
report that it cannot be measured without a port and say what that costs.
**Either answer is useful; guessing is not.**

## THE CONTENT CLASS IS THE REAL QUESTION

`dev/LESSONS.md` **P-m**: parameterized work runs 0.010 to 0.013 s per line,
instantiation 0.22 to 0.297. **P-n**: satisfaction content at a concrete
carrier is a payable floor at that instantiation rate.

**A square law that lands in the instantiation class cannot fit any budget**,
so the shape question is really a class question. Say which class each shape
you price lands in, and why.

## DD4, WHICH GOES IN EVERY BRIEF

**Maximize the code the two proofs share, and write it generic.** One rule,
two ends. It has NO metric and no checker by the owner's ruling, so it is
stated in every brief and answered in every return; the repetition is its only
enforcement.

**A square law is ordinal arithmetic and it is tower-agnostic.** `[LJ-0.7]`
found the per-tower content is exactly two objects, the level-hood certificate
and the definable well-order; **a square law is neither**, so it SHOULD be
template content that both proofs share and the AC side may want too.

**So price it as SHARED, and say what each tower would reuse.** If your
cheapest shape is Def-tower-specific, say so plainly with both numbers,
because that would be an argument against the shape rather than for it.

## LITERATURE (DD18)

- **`dev/literature/devlin-II5.md` sections 1.4, 1.5, 2.5 and 5.2.** 5.4 is
  the counting and 5.5 to 5.6 the chain that consumes the level size.
- `_build/literature/dev2.txt:1357-1360` for 5.4.
- **Devlin may not need a square law at all**, and question 1 is exactly that.
  Say what the source actually assumes about ordinal arithmetic.
- The digest marks two OCR items UNRESOLVED; check whether either touches
  this.

Return a **LITERATURE USED** section, with WHY NOT for anything skipped.

## ARCHIVE (DD18)

- **`archive/rud-route/src/L/Ordinal/SquareLaw.lagda.md` and `Pairing.lagda.md`.**
  Read them, including SquareLaw's prose at `:956-963` where the initial-ordinal
  restriction is stated.
- `_build/lj-1.6-review.md`, your commissioning document, and
  `_build/lj-1.6-report.md`.
- `archive/dev/TASKS-archived.md` for `[T98]`'s presentation-bound finding and
  for what the retired route paid here.
- `dev/ledger.toml:1765` and `:1769` for the seconds.
- `dev/LESSONS.md` is NOT archived and still binds. **P-m, P-n, P-s, D-10 and
  D17's rewrite-side rule decide this block.**

Return an **ARCHIVE USED** section at `file:line`.

## MANDATORY RULES FOR A RECON

From `python3 scripts/rules.py --for recon`. Run it and read each statement.

- **D-10. Price the truth of a recorded residue before pricing its proof.**
  **This row has already carried two wrong numbers.** Verify before you build
  on anything.
- **C-22. Write the deliverable incrementally.**
- **P-l. A statement may be ABOUT a concrete stage without dragging that
  stage's PRESENTATION into its type.** This is the law behind
  presentation-bound.
- **D-26. A well-founded key on a tower needs generation data, or it needs
  syntax.** Say whether it bears here; a square law may be below that line.

## SCOPE (read)

`_build/lj-1.6-review.md` first. Then the two archived modules. Then the
digest. Then `dev/ledger.toml`'s `[ratio]` block and the seconds rows.

## SCOPE (write)

`_build/lj-1.17-report.md` only, plus scratch probe files named
`src/Probe*.agda` if you measure. **No master under `src/` and no file under
`dev/`.**

## CONSTRAINTS

- **Never commit and never push.** Probe files are untracked by standing rule.
- **A sibling may hold an Agda slot.** Check
  `python3 .claude/skills/codex-dispatch/dispatch.py status` before measuring,
  and if one is live, report that you could not measure rather than measuring
  anyway. A contended measurement is void; a contended gate read 150.09 s
  against 133.69 s quiet.
- **ONE best-effort number per shape, naming its basis** (DD8).
- **Separate MEASURED from ESTIMATED everywhere.**
- **Evidence is `file:line`.**
- **A refusal that no shape fits the budget is a SUCCESS.**
- Write ASD-STE100 in the report.

## RETURN

Write `_build/lj-1.17-report.md` INCREMENTALLY, skeleton first.

1. **THE VERDICT**, first line: which shape at what seconds, or no shape fits.
2. **IS THE FULL SQUARE LAW NEEDED?** answered from the source.
3. **THE NON-INITIAL TRANSFER**, priced, because the archived law does not
   reach the consumer without it.
4. **THE IDEAL FORM**, priced against the port, per D17.
5. **SECONDS**, and the fraction of the 99.6 to 147.7 budget.
6. **THE CONTENT CLASS** per shape, against P-m and P-n.
7. **THE PAIRING MEASUREMENT**, or why it could not be made.
8. **DD4**: what each tower reuses.
9. **LITERATURE USED.**
10. **ARCHIVE USED.**
11. **WHAT I AM NOT SURE OF.**
