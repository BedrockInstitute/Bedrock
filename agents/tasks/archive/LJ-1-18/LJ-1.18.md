# LJ-1.18: probe the meta term algebra, the fourth shape

tier: codex (default). **THROWAWAY PROBE under D-1: nothing lands, nothing is
committed, the deliverable is a report with numbers.**

## GOAL

Close the arity-one case of a **meta-level term algebra** for the hull, in
about 120 probe lines. **GO or NO-GO with numbers**, then throw it away.

## CWD

`/Users/alsg/Agentic/Bedrock`, on branch `two-tower-bridge`.

## WHY, AND THE STAKES ARE A FACTOR OF HUNDREDS

`[LJ-1.16]` refused the criterion at hull parameters and priced its best
surviving shape at 1.0 to 3.0k lines in P-n's class, so 220 to 890 seconds and
17 to 23 times DD24's bar. `[LJ-1.16-R]`, an adversarial review, then found a
**fourth shape it estimates at 150 to 300 in-fence lines at 0.005 to 0.013 s
per line, so 0.8 to 3.9 seconds.** That is under 4 percent of the wing's
99.6-to-147.7-second budget.

**The gap between the two is 3 to 20x in lines and 56 to 1100x in seconds.**
That is far too large to accept on a reading, which is why you are a probe and
not a build. **The 150-300 is READ, not measured**, and the review says so.

## THE SHAPE TO PROBE

Put the term algebra in the **META language**, not in the object syntax:

```
data Code : Type where
  base : ⟪ X ⟫ → Code
  wit  : (k : ℕ) → Formula (⊥* ) (suc k) → Vec Code k → Code
```

valued by the `wL`-least witness when one exists, and by a **junk value**
otherwise. The junk value is the point: it keeps the witness out of the index,
so `Code` stays a plain inductive type rather than an indexed one.

**Close the arity-one case only.** Define `Code`, define `val : Code → ⟪ X ⟫`
or the appropriate target, and show the hull built over `Code` is closed at
hull parameters for arity one. That is the decisive miniature.

## WHAT THE REVIEW SAYS IS ALREADY GREEN, so do not rebuild it

`[LJ-1.16]` priced the **inverse** of `FOL.Manipulation.Parameters`. The
**forward** face is what this shape needs and it is delivered:

- `absFo` at `src/FOL/Manipulation/Parameters.lagda.md:260-261`
- `⊨-abs` at `:421-429`
- `⊨-map`, and the untruncated `fiber`

**Read those before you write anything.** If the review is wrong that they
suffice, that is your first finding and it is worth the dispatch on its own.

## THE GATE, FIXED BEFORE YOU START

- **GO**: the arity-one case closes at or below **120 probe lines**, `Code`
  typechecks as a plain inductive type with termination and positivity
  accepted, and the rate stays under **0.013193 s per line**.
- **NO-GO**: any of those fails. Report which, with the number.

**A NO-GO is a full deliverable.** The fallback is already named: iterate the
delivered `module Hull` at 250 to 450 lines. So a NO-GO costs the campaign one
dispatch, not a route.

## THREE THINGS THE REVIEW IS LEAST SURE OF, and they are your job

1. **The 150-300 is read, not measured.** Your line count replaces it.
2. **`Code`'s termination and positivity are argued on TYPES ONLY.** Agda has
   the last word. **Check them first**, because a failure there kills the
   shape before any line count matters.
3. **Both variants add one countable union at the counting site** that the
   delivered one-step hull escapes. **Say what that costs**, because the
   counting site is `[LJ-1.6]`'s delivered work and this must not break it.

## THE SIBLING ALIGNMENT, and it may save you work

`src/FOL/Count.lagda.md` is `[LJ-1.6]`'s delivered counting kit, untracked in
the working tree. Its `encode` at `:654` has type
`Formula K 1 → Σ[ k ∈ ℕ ] (Formula (⊥*) k × Vec K k)`, which returns **exactly
`wit`'s payload**. The review flags this as alignment rather than coincidence.
**Read it and say whether the counting kit gives you `wit` for free.**

## DD4, WHICH GOES IN EVERY BRIEF

**Maximize the code the two proofs share, and write it generic.** One rule,
two ends. It has NO metric and no checker by the owner's ruling, so it is
stated in every brief and answered in every return; the repetition is its only
enforcement.

**This shape's DD4 case is why it matters beyond its price.** `[LJ-1.16-R]`
found the obstruction hits BOTH towers, because the digest books the definable
well-order as per-tower content each tower carries, so the blocked shape buys
it twice. **The term algebra needs only a META well-order, which both towers
have**, so it is template content bought once.

**So keep it generic in the carrier and the well-order.** No `Lset`, no stage
presentation, no Def-tower content in any type (P-l), and parameterize the
MODULE (P-h). Say in the return what the J tower would supply.

## LITERATURE (DD18)

- **`dev/literature/devlin-II5.md` sections 1.3 and 2.4**, Devlin 5.3, the
  hull with least witnesses. `[LJ-1.16-R]` found the definable well-order
  appears on the GCH chain at exactly ONE place, Devlin's own proof of the
  hull, and that a META well-order answers instead.
- `_build/literature/dev2.txt:1329-1356`, where Devlin's internal order makes
  the least witness the UNIQUE witness. **That is the role your junk value
  replaces.**
- `dev/literature/devlin-II5.md:278-285`, Step F: 5.5 consumes condensation
  parts (i) and (ii) only.

Return a **LITERATURE USED** section, with WHY NOT for anything skipped.

## ARCHIVE (DD18)

- **`_build/lj-1.16-review.md`. Your commissioning document**, especially its
  sections 3 and 8.
- `_build/lj-1.16-report.md`, the refusal it overturned, for the three shapes
  that did not pay.
- `_build/lj-1.3-report.md`, which chose the hull's index type. **That choice
  is the obstruction and the owner is being asked to rule on it.**
- `_build/l3.32-t49-report.md:53`, which records this piece as never priced,
  and `[L3.32-T5]`, which refused an iterated REFLECTION hull for a reason the
  review says does not apply here. **Check that yourself.**
- `dev/LESSONS.md` is NOT archived and still binds. **D-1 makes you
  throwaway, P-l keeps the carrier abstract, P-n is the class you must stay
  out of, D-10 is why the 150-300 is a residue.**

Return an **ARCHIVE USED** section at `file:line`.

## MANDATORY RULES FOR A PROBE

From `python3 scripts/rules.py --for probe`. Run it and read each statement.

- **D-1. A probe prices THIS setting.** Smallest decisive miniature, then
  throw it away.
- **P-l. A statement may be ABOUT a concrete stage without dragging that
  stage's PRESENTATION into its type.**
- **P-i.** normalisation and heap.
- **C-12.** `GHCRTS="-A64m -I0 -M8g" agda <file>`, ONE process. A sibling may
  hold the other slot. Heap exhaustion is a wall to report, never a cap to
  raise.
- **D-10. Price the truth of a recorded residue before pricing its proof.**
  The 150-300 estimate and the "already green" claim are both residues.
- **C-22. Write the deliverable incrementally.** The last probe missed C-22's
  letter; fill each number as it lands.
- **R-40**: state a membership witness SHALLOW and climb.

## SCOPE (read)

`_build/lj-1.16-review.md` section 3 first. Then
`src/FOL/Manipulation/Parameters.lagda.md` at the named lines. Then
`src/L/Hull.lagda.md` around `:296` and `:360`, which is the index type at
issue. Then `src/FOL/Count.lagda.md:654`.

## SCOPE (write)

**Probe files only, named `src/Probe*.agda`.** They are untracked by standing
rule and `scripts/check-probes.py` refuses a commit containing one. Your
report is `_build/lj-1.18-report.md`. **No `.lagda.md` master may be edited,
for any reason.**

## CONSTRAINTS

- **Never commit and never push.**
- **Do NOT edit any master.** If the probe needs an export the tree lacks,
  that is a FINDING: report it, do not add it.
- **Do NOT run `make check` or a whole-tree check.**
- **Report SECONDS and the RATE**, against the 0.013193 bar and P-n's 0.22 to
  0.297 floor.
- **Count probe lines the same way**: non-blank lines inside the code.
- **Evidence is `file:line`.**
- **A NO-GO with numbers is a SUCCESS.**
- Write ASD-STE100 in the report.

## RETURN

Write `_build/lj-1.18-report.md` INCREMENTALLY, skeleton first.

1. **THE VERDICT**, first line: GO or NO-GO, with the line count.
2. **TERMINATION AND POSITIVITY**: what Agda said, first, because it gates
   everything else.
3. **THE LINE COUNT**, against 120, and against the review's read 150-300.
4. **SECONDS AND RATE**, against 0.013193 and P-n.
5. **DID THE DELIVERED FORWARD FACE SUFFICE?** naming what you used.
6. **THE COUNTABLE UNION** at the counting site, and what it costs.
7. **DOES `FOL.Count`'s `encode` GIVE `wit` FOR FREE?**
8. **DD4**: what the J tower supplies.
9. **LITERATURE USED.**
10. **ARCHIVE USED.**
11. **WHAT I AM NOT SURE OF.**
