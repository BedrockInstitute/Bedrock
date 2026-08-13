# LJ-1.26: gate LJ-1.5 by pricing condensation in SECONDS

tier: codex (default)

## GOAL

`[LJ-1.5]`, the condensation lemma, is priced in LINES and has never been
priced in SECONDS. Seconds are what DD24 gates. **Price it, and name the ONE
probe that would decide it.** **Write no Agda and hold no Agda slot.**

## CWD

`/Users/alsg/Agentic/Bedrock`, on branch `two-tower-bridge`.

## WHY THIS BLOCKS THE PHASE

`dev/PLAN.md:452` prices `[LJ-1.5]` at **route A, 3.3k lines, band 2.0 to
4.5k**. That is a line figure. **DD24 gates cold seconds over in-fence lines,
and the wing's WHOLE seconds budget is 99.6 to 147.7 s** (`dev/ledger.toml:305`).

**The spread on the seconds is about 100x and that is the whole problem:**

| basis | rate | 3.3k lines would cost |
|---|---:|---:|
| the ARCHIVED condensation, 514 in-fence lines at **203.3 s** (`dev/LESSONS.md:2334`) | **0.395** | about **1,300 s** |
| `[LJ-1.23]`'s delivered hull, today | 0.0039 | about **13 s** |

**1,300 s is 9 to 13 times the wing's entire budget. 13 s is comfortable.**
Nobody knows which end this lands at, and DD8 forbids funding 3.3k lines on a
survey. **That is the gate you are building.**

## WHAT CHANGED TODAY, and it is why the old price is stale

Four things landed after `[LJ-1.5]`'s row was written. **Each could move the
seconds, and you must say which do:**

1. **DD27, the hull re-index.** `[LJ-1.23]` delivered
   `src/L/Hull.lagda.md` at 431 lines and **0.0039 s per line**, and
   `hull-closed` now gives the Tarski-Vaught criterion **at HULL parameters**
   (report section 2). **That was condensation's stated blocker.**
2. **The level size.** `[LJ-1.21]` delivered `|Lset α| = |α|`'s upper half at
   every infinite ordinal. It owes `fin-inj`, priced at 50 to 100 lines.
3. **The stage arithmetic.** `[LJ-1.20]` delivered `+ω` and its bounds.
4. **A 12.8x SECONDS CURE, measured today.** `[LJ-1.24]` cut a transport-heavy
   block from 29.1 s to 2.3 s by abstracting the SOURCE. **If condensation's
   cost is the same class, its price is not the archive's.**

## THE ROOT-CAUSE EVIDENCE ALREADY IN THE TREE, and it is unusually rich

**Do not re-measure the archive. Read what was already measured on it.**

- **`dev/LESSONS.md:2364`** classifies the archived module's defect as
  **body-bound**: "a body elaborates delivered machinery at a concrete
  argument", with `ambientOnly-from` at **128.5 s falling to 0 ms while
  131.1 s appeared in the lemma it now calls". **The cost MOVED and the total
  did not change.** The row names the only real cure: "restate the obligation
  so the concrete application is not built".
- **`dev/LESSONS.md:2334`** the abstract-carrier discipline gave **no movement
  at all** on `Condensation`'s clauses, 203.3 s against 203.5.
- **`dev/LESSONS.md:2337`** `[T104]` argued a lift would carry by resemblance
  and ran nothing; `[T106]` measured it and **piece 1 got WORSE, 204.7 s to
  308.8**.
- **`dev/LESSONS.md:2703`** three defects in the structural story.

**So condensation has DEFEATED two cures already and one made it worse.**
`[LJ-1.24]`'s cure is a third, and it is the one that has never been tried
there. **Say whether the body-bound class and the transport class are the same
disease or different ones.** That is the most valuable sentence you can write.

## THE FOUR QUESTIONS

1. **What is condensation's seconds price**, as ONE best-effort number with
   its basis named (DD8)? Not a range with no basis, and not two calibers.
2. **Is the archived 0.395 rate evidence about the NEW route at all?** The
   archived module served the retired rud route. `[LJ-1.11]` already refuted
   one archived story as classically FALSE. **If the archive does not transfer,
   say so and say what does.**
3. **Which of the four landings above actually reduce the work?** Name each at
   `file:line`, and say what is left.
4. **THE PROBE**: name the ONE smallest miniature that would decide the price,
   with its own expected cost in minutes. **A gate that cannot name its probe
   is not a gate.**

## THE SECOND-ORDER QUESTION, and it may be the real answer

**Is route A still the route?** It was recommended before the hull was
re-indexed. `[LJ-1.23]` made the criterion available at hull parameters, and
`[LJ-1.16-R]` found the definable well-order appears on the whole GCH chain at
exactly ONE place. **If the DD27 hull shortens the chain, the 3.3k figure is
stale in LINES as well as in seconds. Say so with the evidence.**

## DD4, WHICH GOES IN EVERY BRIEF

**Maximize the code the two proofs share, and write it generic.** One rule,
two ends. It has NO metric and no checker by the owner's ruling, so it is
stated in every brief and answered in every return; the repetition is its only
enforcement.

**Condensation is where DD4 pays or fails.** `[LJ-0.7]` found exactly TWO
per-tower objects on the whole GCH chain: the level-hood certificate and the
definable well-order. **Say which parts of condensation are template and which
are per-tower**, and price them separately. A price that does not split them
tells the owner nothing about whether the J tower pays twice.

## LITERATURE (DD18)

- **`dev/literature/devlin-II5.md` sections 1.5 and 2.x**, Devlin 5.5 and 5.6,
  and `_build/literature/dev2.txt:1369-1388` for the statements themselves.
- **Devlin proves condensation in about a page.** `[LJ-0.7]` digested the
  chain. **Say what the formal cost is buying that the book gets for free**;
  that difference IS the price you are estimating.
- `dev/literature/devlin-errata.md` does NOT cover Chapter II section 5.
  `[LJ-1.14]` verified it. **Do not re-check it.**

Return a **LITERATURE USED** section, with WHY NOT for anything skipped.

## ARCHIVE (DD18)

- **`archive/rud-route/src/L/Condensation.lagda.md`, 514 in-fence lines.**
  The measured comparable. **Read it and say what it actually spends its
  lines on.**
- **`dev/LESSONS.md:2330-2370` and `:2700-2720`.** Every measurement ever
  taken on that module. **These are your primary source, not the code.**
- `_build/lj-1.23-report.md` sections 2, 4 and 10: the criterion at hull
  parameters, what lost its consumer, and what the J tower supplies.
- `_build/lj-1.24-report.md` sections 3, 6 and 7: the cure, its class and its
  price.
- `_build/lj-1.15-review.md` and `_build/lj-1.16-review.md`, which separated
  the two obstructions and found the fourth shape.
- `_build/lj-1.1-recon.md` section 6, where the 3.3k figure and its band come
  from. **Check whether its basis was a survey or a comparable.**
- `dev/LESSONS.md` is NOT archived and still binds. **P-m, P-l, P-n, D-10 and
  C-31 decide this block.**

Return an **ARCHIVE USED** section at `file:line`.

## MANDATORY RULES FOR A RECON

From `python3 scripts/rules.py --for recon`. Run it and read each statement.

- **D-10. Price the truth of a recorded residue before pricing its proof.**
  Every figure in this brief is a residue. The 3.3k especially: **check its
  basis before you build on it.**
- **C-22. Write the deliverable incrementally.**
- **P-l.** Naming a transparent construction in a statement's TYPE is what
  costs. **This is the lens for reading the archived module.**
- **D-26. A well-founded key on a tower needs generation data, or it needs
  syntax.** **Say whether it bears.** Condensation collapses a hull, and the
  collapse needs an extensional carrier, so the key question may be live here
  in a way it was not for the level size.

## SCOPE (read)

`dev/LESSONS.md:2330-2370` FIRST, then `_build/lj-1.23-report.md`, then
`archive/rud-route/src/L/Condensation.lagda.md`, then
`src/V/Collapse.lagda.md`, which is DELIVERED at 335 lines and may already
carry the collapse half.

## SCOPE (write)

`_build/lj-1.26-report.md` only. **No file under `src/` and no file under
`dev/`.**

## CONSTRAINTS

- **Run NO `agda` and NO `make check`.** A sibling holds an Agda slot and is
  taking timing measurements. **Your figures come from the record, not from
  the machine.**
- **Never commit and never push.**
- **ONE best-effort number, naming its basis** (DD8). The two-caliber rule is
  REVOKED.
- **Separate MEASURED from ESTIMATED everywhere.**
- **A finding that the price is UNKNOWABLE without the probe is a SUCCESS**,
  provided you name the probe and its cost.
- **Evidence is `file:line`.**
- Write ASD-STE100 in the report.

## RETURN

Write `_build/lj-1.26-report.md` INCREMENTALLY, skeleton first.

1. **THE VERDICT**, first line: condensation's seconds price and its basis.
2. **DOES THE ARCHIVED 0.395 RATE TRANSFER?** Answered first, with evidence.
3. **BODY-BOUND OR TRANSPORT: same disease or different?**
4. **WHAT THE FOUR LANDINGS REMOVED**, each at `file:line`.
5. **IS ROUTE A STILL THE ROUTE**, and is 3.3k still the line figure?
6. **TEMPLATE VERSUS PER-TOWER**, priced separately (DD4).
7. **THE PROBE**: the one miniature that decides it, and its cost.
8. **LITERATURE USED.** 9. **ARCHIVE USED.** 10. **WHAT I AM NOT SURE OF.**
