# LJ-1.24: is the limit half's 31 seconds curable? Root cause first

tier: codex (default)

## GOAL

`[LJ-1.21]` delivered the level size and it costs **31.0 seconds in one
block**. Measure whether that block is curable. **This is a PROBE. Write no
master. Throw the code away.**

## CWD

`/Users/alsg/Agentic/Bedrock`, on branch `two-tower-bridge`.

## WHY THIS IS THE MOST VALUABLE MEASUREMENT AVAILABLE

The wing's WHOLE seconds budget is **99.6 to 147.7 s**
(`dev/ledger.toml:305`). The delivered wing masters now measure about **47 s**,
and **42.03 of those are `src/L/StageCardinal.lagda.md` alone**, of which
**31.0 s is the limit half over 115 lines, a rate of 0.270**.

So ONE block holds about two thirds of everything the wing has spent. If it is
curable, the wing's arithmetic is comfortable. If it is not, the residue must
run at 0.0092 to 0.0107 s per line for the rest of the wing, and that is the
number the phase turns on.

**Do not re-derive that arithmetic and do not audit it.** It is mine. Your job
is the measurement.

## THE ROOT CAUSE, and it is more precise than the report said

`[LJ-1.21]` reported "a transparent imported operation in statement position,
the R-38 class". **The profile says something narrower.** The two hottest
definitions are TRANSPORTS:

- **`defset-stable` at `src/L/StageCardinal.lagda.md:393`**, 6.2 s. It
  transports `defSet` along a path `m₂ ≡ m₁` between carrier members.
- **`defset-stable-δ` at `:401`**, 5.5 s. It transports along a path
  `δ₁ ≡ δ₂` between stages.
- `LimitStep`'s `mk` 5.3 s, `eq-defset` at `:484` 5.3 s, `Successor`'s `go₂`
  at `:314` 4.5 s.

`DefOf.defSet` is born at **`src/L/Definability.lagda.md:111-112`** as
`sett (Σ[ m ∈ ⟪ A ⟫ ] ⟨ smallSat φ m ⟩) ...`, delivered TRANSPARENT. **A
transport across that index unfolds the satisfaction tower.**

**So the suspect is the transport over a transparent `sett` index, not merely
the naming of a transparent operation.** Test that.

## THE CONTROL IS IN THE SAME FILE, AND THIS IS YOUR BEST CLUE

`[LJ-1.21]` measured, in ONE file, one cold run:

| block | seconds | lines | rate |
|---|---:|---:|---:|
| descent (`Successor`, `op-step`, `successor-step`) | 7.95 | 130 | **0.061** |
| limit half (`LimitStep`, `limit-step`) | 31.0 | 115 | **0.270** |

Its own explanation of the descent: **"At a variable carrier, nothing
unfolds."** The descent is parameterized; the limit half names
`DefOf.defSet (Lset ...)` concretely and transports along it.

**A 4.4x rate gap between two blocks of one file, one abstract and one
concrete, is a hypothesis you can test directly.**

## THE THREE ARMS, and the tree has already measured two of them elsewhere

Run them in this order. **Stop early and report if arm 1 wins.**

1. **ABSTRACT THE SOURCE.** Re-state the limit half generic in an abstract
   `D : ⟪ α ⟫ → S` with only the spec the argument uses, and instantiate at
   `DefOf.defSet (Lset ...)` at the very end.
   **This is the ONLY transplant in this tree's history that ever worked**:
   `dev/LESSONS.md:2338`, "the abstract restatement, redirected by root cause,
   abstracting the SOURCE rather than the target, **1.28 s where the
   analogy-guided form had exhausted 8 GB after 26 minutes**".
2. **KILL THE TRANSPORT.** State the membership at the SMALL INDEX and climb,
   rather than transporting `defSet` along a path. **R-35** and **R-40** are
   this shape, and R-35 cured an OOM runaway that crashed the machine.
3. **SEAL `defSet`.** Last, and **expect nothing.** `dev/LESSONS.md:2336`
   records this exact cure transplanting at **ZERO**: 52.9 to 53.2 s. R-38's
   own text says "sealing only moves the cost" (`dev/LESSONS.md:835`).
   **Measure it anyway so the answer is closed, not assumed.**

**Four of this tree's five recorded transplants FAILED**
(`dev/LESSONS.md:2340`). **You are not expected to find a cure. A measured
"none of the three works" is a full deliverable** and it lets the owner price
the wing honestly instead of hoping.

## MEASURE RELATIVE, NOT ABSOLUTE

A sibling holds the other Agda slot, so absolute seconds carry machine noise.
**Measure control and cure back to back in the same conditions and report the
DELTA**, with both raw numbers. Re-run the control last to show the drift.

Noise rule: under 0.5 s or 5 percent, whichever is larger, is flat.

## WHAT YOU MAY NOT TOUCH

- **`src/L/StageCardinal.lagda.md`.** It is `[LJ-1.21]`'s delivery, uncommitted
  and unaudited. **COPY the block into your probe. Do not edit the master.**
- **`src/L/Hull.lagda.md`.** `[LJ-1.23]` is editing it right now (C-25).
- **`src/L/Definability.lagda.md`.** Sealing it would change what every sibling
  sees mid-flight. **Do arm 3 with a LOCAL opaque alias in your probe.**
- **`src/Everything.lagda.md`.** I wire the catalog after auditing.

## DD4, WHICH GOES IN EVERY BRIEF

**Maximize the code the two proofs share, and write it generic.** One rule,
two ends. It has NO metric and no checker by the owner's ruling, so it is
stated in every brief and answered in every return; the repetition is its only
enforcement.

**Arm 1 IS a DD4 move, and that is why it is first.** A limit half generic in
`D` is template content the J tower instantiates at its own step operator,
while the concrete form buys the argument once per tower. `[LJ-1.21]` reported
the L-specific ingredients as `Lset`, `𝒟ₒ`, `𝒟ₒ-inv`, `Lset-suc` and
`Lset-out`. **Say whether arm 1 shrinks that list.** If the cure is also the
shared form, the phase gets both for one price.

## LITERATURE (DD18)

**None bears, and I have checked.** This is a check-cost measurement on
delivered code. Devlin proves the level size in one line and says nothing
about transport cost. **Say so in one line naming `dev/literature/` and move
on.** Do not spend budget looking.

## ARCHIVE (DD18)

- **`dev/LESSONS.md:2330-2348`, the transplant table and the paragraph under
  it.** Read all six rows. **They tell you which arm to expect to win.**
- **`dev/LESSONS.md:835`**, R-38's own "sealing only moves the cost".
- `_build/lj-1.21-report.md` sections 5 and 9, the profile and the two
  uncertainties.
- `archive/rud-route/src/L/Ordinal/SquareLaw.lagda.md`, where the abstract
  restatement won at `[T98]`'s direction. **Find the shape it used and cite it
  at `file:line`.**
- `dev/LESSONS.md` is NOT archived and still binds. **R-35, R-38, R-40, P-l,
  P-m, P-n and D-10 decide this block.**

Return an **ARCHIVE USED** section at `file:line`.

## MANDATORY RULES

**Run BOTH `python3 scripts/rules.py --for probe` and
`python3 scripts/rules.py --for recon`, and read each statement.** This task
writes throwaway Agda, so it is a probe by method; its write scope is a report
and a `Probe` file, so the gate reads it as a recon. Both bundles bind.

- **D-1.** Build the smallest decisive miniature, report GO or NO-GO with a
  price, throw it away.
- **D-10.** Every figure in this brief is a residue from a report one hour
  old. Re-verify the control before you cure anything.
- **P-l, AND IT IS THE HYPOTHESIS ARM 1 TESTS.** The law's own words: "Being
  about a concrete position is not what costs. **Naming a transparent
  construction in a statement's TYPE is.**" `defSet` is transparent and the
  limit half names it. **P-l also forbids transferring a measured cure by
  analogy**, which is why all three arms are measured here and none is
  assumed.
- **D-26. Does it bear? Answer in one line.** A well-founded key on a tower
  needs generation data or syntax. `Lset` is a definable power, so its members
  carry nothing, and `[LJ-1.21]`'s descent took the least VALUE over the
  ordinal's own well-order rather than a key on the stage. **If D-26 explains
  why the limit half must touch `defSet` at all, that is a finding and it
  makes arms 1 and 2 harder.** If it sits below this question, say so and move
  on.
- **P-m.** The check-cost rate is a content-class certificate.
- **P-n.** 0.22 to 0.297 s per line is a payable FLOOR for satisfaction
  content at a concrete carrier. **The limit half measures 0.270, inside that
  band.** `[LJ-1.21]` argued it is R-38 class rather than P-n's floor.
  **If P-n's floor is the true class, no arm will work and that is the
  finding.** Answer this question explicitly.
- **C-12.** `GHCRTS="-A64m -I0 -M8g" agda <file>`, ONE process. A sibling
  holds the other slot.
- **C-22.** Write the deliverable incrementally.

## SCOPE (read)

`src/L/StageCardinal.lagda.md:373-500` FIRST, the limit half. Then
`src/L/Definability.lagda.md:98-160`, `defSet`'s birth. Then the transplant
table.

## SCOPE (write)

`src/ProbeLJ124*.agda` only, and your report `_build/lj-1.24-report.md`.
**No file under `src/` except a `Probe` file. No master. No file under
`dev/`.**

## CONSTRAINTS

- **Never commit and never push.** `scripts/check-probes.py` refuses a
  committed probe, and `git add -f` walks past the ignore rule.
- **Never run `git checkout .`, `git stash`, `git reset --hard` or `git
  clean`.** Revert by exact path only. Two siblings have uncommitted work.
- **Do NOT run `make check`.**
- **Evidence is `file:line`.**
- **A measured NO-GO on all three arms is a SUCCESS.**
- Write ASD-STE100 in the report.

## RETURN

Write `_build/lj-1.24-report.md` INCREMENTALLY, skeleton first.

1. **THE VERDICT**, first line: the best delta measured, or NO-GO on all three.
2. **THE CONTROL**, re-verified, with its raw seconds.
3. **ARM 1**, abstract the source: delta, and the cured rate.
4. **ARM 2**, kill the transport: delta.
5. **ARM 3**, the local seal: delta, and whether it reproduced the archive's
   zero.
6. **IS IT P-n's FLOOR OR R-38's CLASS?** Answer explicitly, with the
   evidence that decides it.
7. **WHAT THE CURE WOULD COST** as a real edit to the master, in lines.
8. **DD4**: does arm 1 shrink the L-specific ingredient list?
9. **ARCHIVE USED.** 10. **WHAT I AM NOT SURE OF.**
