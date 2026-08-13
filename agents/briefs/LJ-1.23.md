# LJ-1.23: the hull on the meta term algebra (DD27)

tier: codex (default)

## GOAL

Re-index the hull by the meta term algebra `Code`, and deliver the
Tarski-Vaught criterion **at hull parameters**. **This is a ruled build, not a
probe.** Land it or refuse with a measurement.

## CWD

`/Users/alsg/Agentic/Bedrock`, on branch `two-tower-bridge`.

## THE RULING YOU ARE EXECUTING

**DD27, ruled by the owner 2026-08-10** (`dev/PLAN.md` section 3). Read it.

`[LJ-1.3]` built the hull as `sett (Σ[ φ ∈ Formula ⟪X⟫ 1 ] Witnessed-small φ)`
at `src/L/Hull.lagda.md:296`, so every membership certificate is an X-formula
(`:360`). **That choice blocked condensation**: the criterion at HULL
parameters needs the order named inside the model, `relL α` sits at rank at
least α while `Lset α` holds only rank below α, and the index leaves no room
to widen, because a hull-expressible order yields a hull-formula.

**Keeping it: 1.0 to 3.0k lines, 220 to 890 s, 17 to 23x DD24's bar.**
**Moving: about 270 lines under 6 s.** The owner ruled the move.

## THE SHAPE, MEASURED GREEN by `[LJ-1.18]`

`src/ProbeLJ118.agda` is the throwaway probe and it typechecked clean at 116
non-blank lines. **Re-derive from it; do not copy a probe into a master.**

```
data Code : Type where
  base : ⟪ X ⟫ → Code
  wit  : (k : ℕ) → Formula (⊥*) (suc k) → Vec Code k → Code
```

valued by the `wL`-least witness when one exists and by a **junk value**
otherwise. The junk keeps the witness out of the index, so `Code` is a PLAIN
inductive type: Agda 2.8.0 accepted strict positivity and `val`'s recursion.

Then `Hull = sett Code (fst ∘ val)`, and the arity-one closure theorem,
**generic in carrier, order and junk** (P-l and P-h clean), instantiated at
`orderAt α ordα` with `⊨-abs` and `⊨-map` doing the environment move. The
FORWARD face of `FOL.Manipulation.Parameters` suffices: `absFo` at `:260-261`,
`⊨-abs` at `:421-429`.

## THE THREE FOLLOW-ONS `[LJ-1.18]` FOUND, about 30 lines, all named

The probe corrected the review that commissioned it on these. **Do not
re-discover them.**

1. **`∅ ∈ˢ Lset α` at limit α** is true and NOT in the tree. About 10 to 15
   lines of foundation argument. The probe's hull layer took junk as a
   parameter to avoid it; a master should not.
2. **Termination through the library `Vec.map` is REJECTED here.** The
   hand-rolled mutual `vals`/`val`, 4 lines, is required. A review called this
   standard and was wrong.
3. **The junk split makes `val (wit ...)` opaque**, so the closure needs a
   4-line lemma identifying it with the least search when a witness exists.

## WHAT MUST BE RE-STATED OVER `Code`, and this is the real work

`src/L/Hull.lagda.md:248-297` states these over `Formula ⟪X⟫ 1`. Each is
re-stated over `Code`:

`Witnessed-small`, `small→big`, `big→small`, `leastSearch`,
`leastSearch-spec`, `leastWit`, `leastWit-spec`, and `hullVal`.

**`hull-closed` is the point of the exercise**: today it gives the criterion at
X-parameters, and over `Code` it must give it at HULL parameters. Say plainly
in the return whether it does.

**DD27 also RETIRES `[LJ-1.3]`'s booked residue piece one, 30 to 80 lines.**
Say what actually went.

## THE THRESHOLD, and read C-31 before you compute anything

DD24 GATES at **0.013193 s per line**, module caliber.

**The wing's seconds budget is 99.6 to 147.7 s over the PROJECTED wing of
7,553 to 11,197 lines, and it is divided by the PROJECTED count, never by
today's.** `dev/LESSONS.md` **C-31** exists because the orchestrator got this
wrong today, read a passing chapter as a 1.34x FAIL, and wrote it into three
places at once.

**And the per-module flag is ADVICE; the AGGREGATE is the judgment**, which
`scripts/check-ratio.py`'s own header has said from the start. So report your
rate, and do NOT declare a failure from one module's number.

The wing's measured rates today: `FOL.Count` 0.0011, `StageCardinal` 0.0052,
`Collapse` 0.0053, `Hull` 0.0064, the probe 0.0103.

## DD4, WHICH IS WHY THE OWNER RULED THIS WAY

**Maximize the code the two proofs share, and write it generic.** One rule,
two ends. It has NO metric and no checker by the owner's ruling, so it is
stated in every brief and answered in every return; the repetition is its only
enforcement.

**The obstruction hits BOTH towers**, so the blocked shape would have bought
the definable well-order twice. **The term algebra needs only a META
well-order, which both towers already have**, so this is template content
bought once. `[LJ-0.7]` found the definable well-order appears on the whole
GCH chain at exactly ONE place, Devlin's own proof of the hull.

**So keep `Code`, `val` and the closure generic in the carrier, the order and
the junk**, exactly as the probe did, and instantiate only at the end.
Parameterize the MODULE (P-h). No `Lset` presentation in a type that does not
need one (P-l). **Say what the J tower supplies to instantiate it.**

## WHAT YOU MAY NOT TOUCH

- **`src/L/StageCardinal.lagda.md` and `src/L/Ordinal/`.** `[LJ-1.21]` is
  editing StageCardinal right now (C-25), and `[LJ-1.20]` just delivered
  `src/L/Ordinal/StageArith.lagda.md`.
- **The counting extension is NOT yours.** `[LJ-1.22]` priced it at about 120
  lines and about 2 s, and found `Code` needs the SAME cardinal law as
  `Formula K 1`. It lands after `[LJ-1.21]` frees StageCardinal. **If your
  work makes the counting harder than that pricing assumed, SAY SO**; that is
  a finding.
- **`src/Everything.lagda.md`.** I wire the catalog after auditing, and the
  gate refused a commit today for exactly that.

## LITERATURE (DD18)

- **`dev/literature/devlin-II5.md` sections 1.3 and 2.4**, Devlin 5.3, the
  hull with least witnesses. `[LJ-1.16-R]` found the definable well-order
  appears on the chain at exactly one place, and a META well-order answers.
- **`_build/literature/dev2.txt:1329-1356`**, where Devlin's internal order
  makes the least witness the UNIQUE witness. **That is the role your junk
  value replaces.** Say whether the replacement is faithful.
- The errata do NOT cover Chapter II section 5; `[LJ-1.14]` verified that, so
  do not re-check it.

Return a **LITERATURE USED** section, with WHY NOT for anything skipped.

## ARCHIVE (DD18)

- **`_build/lj-1.18-report.md`. Your shape and its three follow-ons.**
- **`_build/lj-1.16-review.md` section 3**, which found the fourth shape, and
  `_build/lj-1.16-report.md`, the refusal it overturned, for the three shapes
  that do not pay.
- `_build/lj-1.22-report.md` for the counting pricing you must not invalidate.
- `_build/lj-1.3-report.md`, which chose the index type, and whose piece one
  this retires. **Read section 6.**
- `dev/LESSONS.md` is NOT archived and still binds. **P-h, P-l, P-n, R-35,
  R-38, C-31 and D-10 decide this block.**

Return an **ARCHIVE USED** section at `file:line`.

## MANDATORY RULES FOR A BUILD

From `python3 scripts/rules.py --for build`. Run it and read each statement.

- **P-h.** Module-parameterized, never function-parameterized.
- **P-l.** No stage presentation in a type that does not need one.
- **P-k.** A read lemma is stated where its consumers use it.
- **P-m.** The check-cost rate is a content-class certificate.
- **P-n.** Satisfaction content at a concrete carrier is a payable floor.
- **R-35, R-38**: sealing and opacity. **Do not unseal**: R-38 measures an
  unseal at 25.7 s per invocation, 17 to 26 percent of the wing's budget.
- **R-40**: state a membership witness SHALLOW and climb.
- **I-5**: the inference trap this tree has paid for.
- **C-12.** `GHCRTS="-A64m -I0 -M8g" agda <file>`, ONE process. A sibling
  holds the other slot.
- **C-22.** Write the deliverable incrementally.
- **C-31.** A budget from a projected size is divided by the projected size.
- **D-10.** The probe's 116 lines are a residue; re-verify before building.

## SCOPE (read)

`dev/PLAN.md`'s DD27 row first. Then `src/ProbeLJ118.agda`. Then
`src/L/Hull.lagda.md` in full. Then
`src/FOL/Manipulation/Parameters.lagda.md` at the named lines.

## SCOPE (write)

`src/L/Hull.lagda.md`, and **at most ONE new master under `src/L/`** if the
term algebra deserves its own home. Your report is
`_build/lj-1.23-report.md`. **Never `src/L/StageCardinal.lagda.md`, never
`src/L/Ordinal/`, never `src/Everything.lagda.md`.**

## CONSTRAINTS

- **Never commit and never push.**
- **Do not weaken or delete a theorem that stands.** If a statement over
  `Formula ⟪X⟫ 1` has no consumer after the re-index, say so; D-27 governs
  whether it goes, and a chapter's stated result is not deleted to make room.
- **Typecheck every file you edit AND every consumer**, one process at a time.
  Do NOT run `make check`.
- **Count with `python3 scripts/ledger.py`'s caliber.** DD26 excludes the two
  catalogs.
- **Report cold seconds and the RATE per file**, noise rule: under 0.5 s or 5
  percent, whichever is larger, is flat.
- **Run `python3 scripts/lint-prose.py --check` and `python3
  scripts/lint-agda.py --check`.**
- **DD23 freezes mathematical prose.** Code and its own comments only. **You
  may TRIM a prose clause that names something you removed; you may not write
  new exposition describing the new index.**
- **Evidence is `file:line`.**
- **A refusal with a measurement is a SUCCESS.**
- Write ASD-STE100 in the report.

## RETURN

Write `_build/lj-1.23-report.md` INCREMENTALLY, skeleton first.

1. **THE VERDICT**, first line: delivered with lines and rate, or refused with
   a measurement.
2. **DOES `hull-closed` NOW GIVE THE CRITERION AT HULL PARAMETERS?**
3. **THE THREE FOLLOW-ONS**: what each actually cost.
4. **WHAT WAS RE-STATED OVER `Code`**, and what had no consumer afterwards.
5. **WHAT `[LJ-1.3]`'s PIECE ONE RETIREMENT ACTUALLY REMOVED.**
6. **THE NUMBER**: in-fence lines per file, and the net against the ~270
   estimate.
7. **SECONDS AND RATE**, against 0.013193, with the aggregate framing of C-31.
8. **IS THE JUNK VALUE FAITHFUL** to Devlin's uniqueness role?
9. **DID YOU MAKE THE COUNTING HARDER** than `[LJ-1.22]` priced?
10. **DD4**: what the J tower supplies.
11. **LITERATURE USED.** 12. **ARCHIVE USED.** 13. **WHAT I AM NOT SURE OF.**
