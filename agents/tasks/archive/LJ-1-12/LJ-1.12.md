# LJ-1.12: re-target the crossing, and price what survives

tier: codex (default)

## GOAL

Price the crossing candidates that survive, now that the source has been
digested, and **recommend one with a number**. `[LJ-1.5]` cannot be funded
until this returns. **Write no Agda and hold no Agda slot.**

## CWD

`/Users/alsg/Agentic/Bedrock`, on branch `two-tower-bridge`.

## WHAT CHANGED SINCE THIS TASK WAS REGISTERED

**`[LJ-0.7]` digested Devlin II.5 hours ago and it moved the target.** Read
`dev/literature/devlin-II5.md` section 2.3 FIRST. Its finding:

> a Δ₀ witness for the satisfaction leaves is NOT what Devlin's argument
> needs. Level-hood is used at Σ₁ strength, `∃z` with a Σ₀ matrix.

`[LJ-1.2]` returned NO-GO because the step clause of `LsetGraphAt` has no Δ₀
witness at any carrier. **That measurement stands and it tested a strength the
literature never asks for.** I verified the two load-bearing citations at
source myself: `dev2.txt:679-686` for the Σ₁ level formula, and
`dev2.txt:593-630` for the bound.

**So the question is no longer "where is the Δ₀ witness".** It is:

> **What bounded description of the Def step exists, with a concrete bound
> that lives inside the carrier?**

Devlin's answer is `K(u)`, the finite sequences over the formula set, the
variables and the members of `u` (`dev2.txt:593-630`). `[LJ-1.2]`'s own
missing facts, a bounded object-level description of the code set and of the
satisfaction table (`_build/lj-1.2-gate.md` section 5), are the project-side
analogues. **The argument does not require them to have any particular shape,
only that some bounded description with a bound inside the carrier exists.**

## THE CANDIDATES TO PRICE

1. **Route A**, whose substrate `[LJ-1.10]` priced at 1.7k to 3.8k. **Re-price
   it against the Σ₁ target rather than the Δ₀ one.** The old figure was set
   when the bar was thought to be Δ₀; if that bar was wrong, the price may be
   too.
2. **The π-commutation route**, never priced.
3. **The K(u) analogue**, which is new and comes from the digest: build the
   project's own bounded description with its bound inside the carrier, in
   the shape section 2.3 item 1 describes. **Nobody has priced this because
   nobody had read the source.**

**Price all three. Recommend one. A refusal that all three are unaffordable is
a full deliverable** and it re-prices the wing rather than stalling it.

## WHAT `[LJ-1.11]` KILLED, so you do not re-propose it

Route C, the archived structural story. Its Def-step collapses to `⊤̇`, so it
recognizes no level at all (`_build/lj-1.11-review.md` F1). `[LJ-1.10]` read
that `⊤̇` step as a saving; it is the missing content. **Do not revive it.**

## WHAT IS ALREADY DELIVERED, so you price the REMAINDER

Two of `[LJ-1.5]`'s three gates closed today and the third is you.

- **`[LJ-1.13]`**: the collapse now holds at an EXTENSIONAL carrier,
  `src/V/Collapse.lagda.md:220`, `module InjExt (Xext : isExt X)`. The J tower
  instantiates it by supplying one certificate.
- **`[LJ-1.14]`**: Tarski-Vaught now holds at ANY carrier inside a stage,
  `src/L/Hull.lagda.md:73`. `Mtr` is gone from the file entirely.
- **STILL OWED, and `[LJ-1.14]` named it unprompted:** the criterion AT HULL
  PARAMETERS. `hull-closed` gives it at X-parameters; the substitution bridge
  is the missing piece and `[LJ-1.14]` priced that content at 210 to 430
  lines. **Say whether your recommended route still needs it.**

## THE THRESHOLD YOUR ANSWER LIVES UNDER

DD24 is the wing's ONLY threshold and it now GATES rather than reports. The bar
is **0.011472 s per line at the module caliber**, times a 1.15 tolerance, so
**0.013193**. The wing today measures 0.0065 aggregate, 0.57x the AC side.

**There is no line cap on the wing, by DD24's deliberate omission**, because
this wing exists to MEASURE what GCH costs. So price in lines AND say what
content class each route lands in: `dev/LESSONS.md` P-m measures parameterized
work at 0.010 to 0.013 s per line and instantiation at 0.22 to 0.297, a
twentyfold spread. **A route that lands in the instantiation class is the real
risk, not a route that is long.**

## DD4, WHICH GOES IN EVERY BRIEF

**Maximize the code the two proofs share, and write it generic.** One rule,
two ends. It has NO metric and no checker by the owner's ruling, so it is
stated in every brief and answered in every return; the repetition is its only
enforcement.

**`[LJ-0.7]` has already done the hard half for you, and your pricing must use
it.** Its section 4 found that the condensation template 5.1 to 5.6 is SHARED
between the two towers, and that the per-tower content is EXACTLY TWO OBJECTS:
the level-hood certificate and the definable well-order.

**So price each route by how much of it is the shared template and how much is
the Def tower's own two objects.** A route that puts more into the template is
worth more than its line count says, because the J tower gets it free. Say
this per route, with a split.

## LITERATURE (DD18)

- **`dev/literature/devlin-II5.md`, sections 2.3 and 3 and 4. This is your
  commissioning document** and it did not exist when this task was
  registered.
- `_build/literature/dev2.txt` at the lines the digest cites. **Check at least
  the two load-bearing ones yourself**; the digest marks two OCR items
  UNRESOLVED and you should know which they are.
- `dev/literature/j-hierarchy.md` for what the J tower supplies.
- `dev/literature/digest.md` for the orthodox route.

Return a **LITERATURE USED** section, with WHY NOT for anything skipped.

## ARCHIVE (DD18)

- `_build/lj-1.2-gate.md` sections 3 and 5, the NO-GO and its missing facts.
- `_build/lj-1.10-reprice.md`, refuted on route C but its route decomposition
  survives per `[LJ-0.7]`.
- `_build/lj-1.11-review.md` F1 and F4.
- `_build/lj-1.1-recon.md`, the wing plan and its 8.0k to 10.8k band.
- `archive/rud-route/` and `archive/dev/TASKS-archived.md`: the retired route
  crossed this same gap. **Say what it paid and whether that price transfers.**
- `dev/LESSONS.md` is NOT archived and still binds. **D-26 is the law your
  answer tests, P-m sets the content classes, and D-10 is why every recorded
  price here is a residue.**

Return an **ARCHIVE USED** section at `file:line`.

## MANDATORY RULES FOR A RECON

From `python3 scripts/rules.py --for recon`. Run it and read each statement.

- **D-10. Price the truth of a recorded residue before pricing its proof.**
  **This is the spine.** Route C was a recorded residue and it was false.
  `[LJ-1.10]`'s 1.7k-to-3.8k is a residue set against the wrong bar.
- **C-22. Write the deliverable incrementally.**
- **P-l. A statement may be ABOUT a concrete stage without dragging that
  stage's PRESENTATION into its type.**
- **D-26. A well-founded key on a tower needs generation data, or it needs
  syntax.** `[LJ-0.7]` located this precisely; your pricing tests it.

## SCOPE (read)

`dev/literature/devlin-II5.md` sections 2.3, 3, 4 first. Then
`_build/lj-1.2-gate.md`. Then the reports above. Then `src/L/Coding/` where a
candidate points.

## SCOPE (write)

`_build/lj-1.12-report.md` only. **No file under `src/` and no file under
`dev/`.**

## CONSTRAINTS

- **Run NO `agda` and NO `make check`.** A sibling holds an Agda slot.
- **Never commit and never push.**
- **Evidence is `file:line`.**
- **Separate MEASURED from ESTIMATED in every price.** Conflating them is the
  defect that produced four refused blocks this week.
- **ONE best-effort number per route, naming its basis** (DD8). Not a range
  dressed as a measurement.
- **If you propose a probe, name the smallest decisive one** and what GO and
  NO-GO would look like.
- Write ASD-STE100 in the report.

## RETURN

Write `_build/lj-1.12-report.md` INCREMENTALLY, skeleton first.

1. **THE RECOMMENDATION**, first line: which route, at what price.
2. **THE THREE PRICES**, each with its basis and its MEASURED/ESTIMATED split.
3. **THE SHARED-TEMPLATE SPLIT** per route (DD4): how much is 5.1 to 5.6 and
   how much is the Def tower's own two objects.
4. **THE CONTENT CLASS** per route, against P-m's bands, and the DD24 risk.
5. **DOES YOUR ROUTE STILL NEED THE SUBSTITUTION BRIDGE** that `[LJ-1.14]`
   priced at 210 to 430?
6. **THE PROBE**, if one is needed, with its GO and NO-GO.
7. **WHAT THE RETIRED ROUTE PAID** for the same crossing, and whether it
   transfers.
8. **LITERATURE USED.**
9. **ARCHIVE USED.**
10. **WHAT I AM NOT SURE OF.**
