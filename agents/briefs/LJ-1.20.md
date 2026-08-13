# LJ-1.20: the stage-arithmetic kit, shared by both towers

tier: codex (default)

## GOAL

Deliver the ordinal stage-arithmetic the tree lacks: `+ω`, closure under it,
and the bound lemmas `[LJ-1.19]` proved at probe scale. **Write it generic and
land it where both towers reach it.**

## CWD

`/Users/alsg/Agentic/Bedrock`, on branch `two-tower-bridge`.

## WHY IT IS UNBLOCKED WHEN MOST OF THE PHASE IS NOT

Two independent reviews asked for this same kit, and it depends on no open
ruling.

- `[LJ-1.15-R]`: "neither site has a stage-arithmetic API, and that kit is
  DD4-shared code."
- `[LJ-1.19]` measured the concrete gap: **the tree has no `+ω` in any
  master.** It proved the pieces at probe scale, GREEN, 30 body lines.

The hull's index-type fork is with the owner and blocks `[LJ-1.5]`. **This kit
is behind neither.**

## WHAT TO DELIVER, and `[LJ-1.19]` already proved it green

Read `_build/lj-1.19-report.md` and `src/ProbeLJ119.agda` first. **The probe is
throwaway, so re-derive rather than copy**, but its statements are the spec:

1. **`+ω` on ordinals**, and the predicate "α is closed under `+ω`".
2. **`boundCloses`**: the code set at `δ+ω` lands in `Lset α` for α closed
   under `+ω` and δ below α.
3. **`envCloses`**: the environment component at `δ+3` lands in `Lset α`, via
   the finite-iterate law.

Both go through `Lset-mono`. **No unsealing**: R-38 prices an unseal at 25.7 s
per invocation, which is 17 to 26 percent of the wing's whole budget.

## DD4, AND IT DECIDES WHERE THIS FILE LIVES

**Maximize the code the two proofs share, and write it generic.** One rule,
two ends. It has NO metric and no checker by the owner's ruling, so it is
stated in every brief and answered in every return; the repetition is its only
enforcement.

**This is ordinal arithmetic. It is neither of the two per-tower objects**
`[LJ-0.7]` identified, the level-hood certificate and the definable
well-order, **so it is template content and both towers want it.** The J side
already used the same restriction, at
`archive/rud-route/src/L/Rud/LevelSigma.lagda.md:203,209-213`.

- **Land it under `src/L/Ordinal/`**, beside the existing ordinal material,
  not inside a GCH chapter. A GCH-only home would mis-attribute shared lines,
  which is exactly the mistake `L.Count` made before it became `FOL.Count`.
- **Parameterize the MODULE** (P-h). **No `Lset` presentation in a statement
  that does not need one** (P-l).
- Say in the return what the J tower reuses unchanged.

## THE THRESHOLD

DD24 GATES the wing at **0.013193 s per line**, module caliber. The wing's
whole seconds budget is **99.6 to 147.7 s** and it currently spends about 5.

**But if this lands under `src/L/Ordinal/` it is AC-side or shared, not wing**,
so it is judged against the AC baseline rather than the wing's. **Report your
rate and say which bucket you believe it lands in**; the split is by import
closure and I wire the catalog.

`[LJ-1.19]` measured the probe at 0.0119 s/line, and noted the 30-line body
alone reads 0.019 because it pays the module-load floor. **Expect your rate to
improve as the file grows.**

## LITERATURE (DD18)

- `dev/literature/devlin-II5.md` section 2.3 item 2, the witness inside the
  carrier, which is what these bounds serve.
- `_build/literature/dev2.txt:676-678`, where Devlin's bound sits at `δ+4`
  because he codes formulas as finite sequences. **This tree reaches `δ+ω`
  because it codes them as trees over the carrier's own members.** That
  difference is why the kit is needed here and not in the book.

**If nothing else bears, say so in one line naming `dev/literature/`.**

Return a **LITERATURE USED** section, with WHY NOT for anything skipped.

## ARCHIVE (DD18)

- **`archive/rud-route/src/L/Rud/LevelSigma.lagda.md:203` and `:209-213`.**
  The J side bounded a carrier member only above the first limit and recorded
  it as a clause parameter. **Read those exact lines** and say whether the
  shape transfers or only the idea.
- `_build/lj-1.19-report.md`, the GO and its two gate answers.
- `_build/lj-1.15-review.md`, which named the kit.
- `dev/LESSONS.md` is NOT archived and still binds. **P-h, P-l, R-38 and D-10
  decide this block.**

Return an **ARCHIVE USED** section at `file:line`.

## MANDATORY RULES FOR A BUILD

From `python3 scripts/rules.py --for build`. Run it and read each statement.

- **P-h.** Module-parameterized, never function-parameterized.
- **P-l.** No stage presentation in a type that does not need one.
- **P-k.** A read lemma is stated where its consumers use it.
- **P-m.** The check-cost rate is a content-class certificate.
- **P-n.** Satisfaction content at a concrete carrier is a payable floor.
- **R-35, R-38**: sealing and opacity. **Do not unseal anything.**
- **R-40**: state a membership witness SHALLOW and climb.
- **I-5**: the inference trap this tree has paid for.
- **C-12.** `GHCRTS="-A64m -I0 -M8g" agda <file>`, ONE process. A sibling may
  hold the other slot.
- **C-22.** Write the deliverable incrementally.
- **D-10.** The probe's 30 lines are a residue; re-verify before building on
  them.

## THE SIBLING

`[LJ-1.21]` may be running in `src/L/StageCardinal.lagda.md` and the archive.
Check `python3 .claude/skills/codex-dispatch/dispatch.py status`.

- **Never run `git checkout .`, `git stash`, `git reset --hard` or `git
  clean`.** Revert by exact path only.
- **Never commit and never push.**

## SCOPE (read)

`_build/lj-1.19-report.md` and `src/ProbeLJ119.agda` first. Then
`src/L/Ordinal/` in full, and `src/L/Ordinal/Stages.lagda.md`. Then the
archived J-side lines.

## SCOPE (write)

**At most ONE new master under `src/L/Ordinal/`**, and
`src/L/Ordinal/Stages.lagda.md` if the material belongs beside what is there.
Your report is `_build/lj-1.20-report.md`. Never `src/Everything.lagda.md`: I
wire the catalog after auditing, and the gate refused a commit today for
exactly that reason.

## CONSTRAINTS

- **Never commit and never push. Do NOT unseal anything.**
- **Typecheck every file you write AND every consumer you touch**, one process
  at a time. Do NOT run `make check`.
- **Count with `python3 scripts/ledger.py`'s caliber.** DD26 excludes the two
  catalogs from every size figure.
- **Report cold seconds and the RATE**, noise rule: under 0.5 s or 5 percent,
  whichever is larger, is flat.
- **Run `python3 scripts/lint-prose.py --check` and `python3
  scripts/lint-agda.py --check`.**
- **DD23 freezes mathematical prose.** Code and its own comments only.
- **Evidence is `file:line`.**
- Write ASD-STE100 in the report.

## RETURN

Write `_build/lj-1.20-report.md` INCREMENTALLY, skeleton first.

1. **THE VERDICT**, first line: delivered with lines and rate, or refused with
   a price.
2. **THE THREE STATEMENTS**, as delivered.
3. **THE NUMBER**: in-fence lines, ledger caliber.
4. **SECONDS AND RATE**, and **WHICH BUCKET** you believe it lands in.
5. **WHAT THE J TOWER REUSES UNCHANGED** (DD4).
6. **DID THE J-SIDE SHAPE TRANSFER**, or only the idea?
7. **LITERATURE USED.**
8. **ARCHIVE USED.**
9. **WHAT I AM NOT SURE OF.**
