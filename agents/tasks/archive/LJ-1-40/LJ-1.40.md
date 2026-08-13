# LJ-1.40: re-index the condensation rows so they are TRUE, and close the agreement

tier: codex (default)

## GOAL

Committed content is defective. **Repair it, and then CONSUME it**: the same
dispatch must close the story-to-machine agreement that exposed the defect.
**A repair nothing consumes is not a repair.**

## CWD

`/Users/alsg/Agentic/Bedrock`, on branch `two-tower-bridge`.

## THE DEFECT, machine-checked three ways

`[LJ-1.38]` refused to close leg D. `[LJ-1.38-R]` upheld it at maximum effort
and found it WORSE than reported. **The orchestrator re-ran all three probes.**

1. **The rows are vacuous at an empty value.** Every story frame ends in
   `∀̇∈ (var yc) body`, which is vacuously true when `yc` is empty. The
   machine's `extAt yc body` has a second direction `∀̇ (body ⇒̇ z ∈ yc)` that
   CONSTRAINS an empty value. **`src/ProbeDD25E1.agda` proves the countermodel
   and is GREEN.**
2. **Worse, at a NONEMPTY value the rows are FALSE of the true satisfaction
   table.** One index (`src/L/Condensation.lagda.md:946,952`) reads the terms
   at the frame's member rather than the extension candidate, **so the defining
   condition never mentions the element it defines**. One member of `yc` forces
   all of `E ∩ K` into `yc`.
3. **The control proves the probe measured the defect, not a triviality.**
   `src/ProbeDD25E3.agda` is the same proof term against a body with that one
   index corrected, and Agda rejects it: `fst e != fst z`. **I re-ran it and saw
   that exact message.**

**`src/ProbeDD25E2.agda` is GREEN and it is your route**: it proves the
CORRECTED frame reaches the machine's frame under ONE site fact, which the
row's own leaf supplies.

## THE CURE THAT IS ALREADY DEAD, so you do not spend a day on it

**Adding "the value is nonempty" does NOT work.** It makes four rows worse,
because the incompatibility NEEDS nonemptiness. And for the six rows it would
save, the hypothesis is false at the site: **the story's own `Bot` row asserts
an empty value.** `[LJ-1.38-R]` measured this. Do not retry it.

## THE SCOPE, measured by `[LJ-1.38-R]` at the ledger's caliber

**Re-opened, about 968 of 2,141 in-fence lines:**

| region | lines | why |
|---|---:|---|
| block 1: `Clause`, `ClauseDecode`, the certificate, `:54-366` | 269 | `existBndAt` at `:133-141` has the same `∀e∈yc` binder, and `bodyBnd` at `:100-106` has NO `extAtB` at all. **Both defects.** |
| the five frames and their Δ₀ witnesses, `:629-732` | 94 | four of five carry the extra binder |
| the frame decodes, `:733-916` | 174 | four of five lose one argument. **`UnBareDecode` survives** |
| the eleven row bodies and rows, `:917-1400` | 431 | every body re-indexes |

**Surviving, about 1,021 lines. Do NOT re-lay these:**

| region | lines |
|---|---:|
| the bounded atoms, `:368-628` | 223 |
| the description region, `:1401-2251` | 798 |
| block 3, the bounded matrices, `:2252-end` | 111 |

**The reason is a type.** A frame's OUTER type is `Formula S m` and the repair
does not change it; only the body argument's arity changes. So `twelveB`,
`satGraphB`, `DefBodyB` and `Δ₀-DefBodyB` need **RE-CHECKING, not re-laying**.
**The 227-line bounded code-set description stands.**

**So this is a RE-INDEX, not a rebuild.** `extAtB` is already the correct frame
and eleven of twelve rows already use it.

**The three that need more than a re-index:**

- **`Exist` and block 1** need an `extAtB` wrap.
- **`Forall`** has a genuinely wrong slot.

## WHAT YOU MUST DELIVER, and the second half is the point

1. **The re-indexed rows**, true of the satisfaction table.
2. **The story-to-machine agreement (leg D) CLOSED at the master.** This is what
   makes the rows tested. `[LJ-1.34-R]` measured this shape at **0.0079 s per
   line** and `[LJ-1.36]` measured the row readings at **under 0.12 s total**,
   so it is cheap when stated right.

**`dev/LESSONS.md` C-35 was admitted today because of this exact block: a
delivered block with no consumer is UNTESTED, and its first consumer is its
first real audit.** The repair is not complete until the agreement closes on
it. **If you can only do the repair, say so and report what the agreement still
owes; do not report the repair as delivered.**

## THE ORCHESTRATOR'S OWN ERROR, corrected here so you do not inherit it

My `[LJ-1.38]` brief asserted that the machine's `atomBody` reads the second
term from the VALUE slot. **That is FALSE. The machine is correct**: `b9″` is
slot 5, the term slot (`src/L/Coding/Model.lagda.md:1746-1751`), and the lines
I cited at `:1765-1770` are inside `AtomWit` and hold no slot definition.

**No delivered master outside `src/L/Condensation.lagda.md` needs an edit.** I
carried a false premise from a return into a brief while listing D-10 in the
same document. **Check my claims against the files.**

## THE LAWS THAT DECIDE THE SHAPE, all measured on THIS chain

- **P-u.** Certify BEFORE you place. The master has ZERO placement and that is
  load-bearing. **If you find yourself needing `absFo` or a placed `Δ₀`, STOP
  and report it**: that wall is flat at 8 GB across constant counts 0, 1, 2
  and 5.
- **P-v.** Never force a satisfaction-level conversion between two spellings of
  one formula. **Where the story is yours to write, write it in the machine's
  spelling from the start.** 59 ms against 29,415 ms. **This defect is that law
  ignored**: the story chose its own spelling and it was the wrong one.
- **P-l.** Naming a built construction in a statement's TYPE is what costs.
- **P-t.** The class follows the FORMULA, not the carrier.

## DD4, WHICH GOES IN EVERY BRIEF

**Maximize the code the two proofs share, and write it generic.** One rule,
two ends. It has NO metric and no checker by the owner's ruling, so it is
stated in every brief and answered in every return; the repetition is its only
enforcement.

`[LJ-1.5]` made `EraseTransfer` TEMPLATE. `[LJ-1.33-R]` measured the bound-drop
layer as template and AMORTIZING. **The frames are the shared object here: four
of five carry the defect, so ONE frame repair should propagate to eleven rows.
Report how many rows needed an individual fix beyond the frame change.** That
number is this block's DD4 evidence, and it is also the honest measure of
whether the original design was really shared or only looked shared.

## THE THRESHOLD

DD24 gates at **0.013193 s per line**, module caliber. The committed master
runs at **0.0046**, but that figure is on defective content and does not
transfer. **Re-measure.** `[LJ-1.39]` separately measured a 318-line
compression of the index spelling that made the file FASTER; **do not apply it,
it is held pending this repair.**

**C-31: a budget from a projected size is divided by the PROJECTED size. The
per-module flag is ADVICE; the aggregate is the judgment.** Report the
module-load cone separately.

## LITERATURE (DD18)

- `dev/literature/devlin-II5.md`, Step C. Devlin binds every Def-step
  quantifier by `K(u)` INSIDE the matrix. **Say whether his shape has the
  extension-candidate structure the machine has**, because that is the point
  the story got wrong.
- The errata do NOT cover Chapter II section 5. `[LJ-1.14]` verified it. **Do
  not re-check it.**

Return a **LITERATURE USED** section, with WHY NOT for anything skipped.

## ARCHIVE (DD18)

**Read these WHOLE. C-32 exists because a brief of mine named a SECTION and hid
the decisive probe.**

- **`_build/lj-1.38-review.md`**, the defect, the scope table and the dead cure.
- **`src/ProbeDD25E1.agda`, `E2` and `E3`.** E2 is your route; E3 is the
  control and is RED by design.
- **`_build/lj-1.38-report.md`**, the refusal and its per-row deviation table.
- `src/L/Condensation.lagda.md` as it stands, with `[LJ-1.38]`'s uncommitted
  block 3.
- `src/L/Coding/Model.lagda.md`, the machine, which is CORRECT.
- `_build/lj-1.37-report.md`, which built the defective rows, **and whose
  premise about the machine was wrong.**
- `dev/LESSONS.md` is NOT archived and still binds. **C-35 is new today and it
  is about this block.**

Return an **ARCHIVE USED** section at `file:line`.

## MANDATORY RULES FOR A BUILD

From `python3 scripts/rules.py --for build`. Run it and read each statement.

- **P-h.** Module-parameterized, never function-parameterized.
- **P-k.** A read lemma is stated where its consumers use it.
- **P-l, P-m, P-n, P-t, P-u, P-v** as above.
- **R-35, R-38**: sealing and opacity. **Do not unseal.**
- **R-40**: state a membership witness SHALLOW and climb.
- **I-5**: the inference trap this tree has paid for.
- **C-12.** `GHCRTS="-A64m -I0 -M8g" agda <file>`, ONE process. A heap
  exhaustion is a WALL with its seconds; never raise the cap.
- **C-22.** Write the deliverable incrementally.
- **C-31.** A budget from a projected size is divided by the projected size.
- **C-32.** A cure invalidates downstream measurements. **Interfaces live in
  `_build/2.8.0/agda/src/`, NOT beside the source.**
- **C-33.** I have tried to name the OBLIGATION and not an entry point. **If I
  named an API where I should have named a job, say so and use the better
  one.**
- **C-34.** Build the cure or report the wall. **A named unpriced cure is not a
  caveat.**
- **C-35.** No consumer, no DELIVERED.
- **D-10.** Every figure here is a residue, **including mine, and one of my
  claims was already proved false.** Re-verify.

## SCOPE (read)

`_build/lj-1.38-review.md` FIRST, then `src/ProbeDD25E2.agda`, then
`src/L/Condensation.lagda.md`, then `src/L/Coding/Model.lagda.md`.

## SCOPE (write)

`src/L/Condensation.lagda.md`, plus `src/ProbeLJ140*.agda` if you need them.
Your report is `_build/lj-1.40-report.md`. **No other master. Never
`src/Everything.lagda.md`.**

## CONSTRAINTS

- **Never commit and never push.**
- **Never `git checkout .`, `git stash`, `git reset --hard` or `git clean`.**
  **`[LJ-1.38]`'s block 3 is uncommitted in the file you are editing and it
  SURVIVES the repair. Do not lose it.**
- **Typecheck the master AND every consumer.** Do NOT run `make check`.
- **Do not weaken a statement to make it close.** That is what produced this
  defect. **If a row cannot be made true, say which and why.**
- **Count with `python3 scripts/ledger.py`'s caliber.** DD26 excludes the two
  catalogs.
- **Report cold seconds and the RATE, with the cone separately.**
- **Run `python3 scripts/lint-prose.py --check` and `python3
  scripts/lint-agda.py --check`.**
- **DD23 freezes mathematical prose.** Code and its own comments only.
- **The machine is quiet and both Agda slots are yours.**
- **Evidence is `file:line`.**
- **A refusal with a measurement is a SUCCESS.**
- Write ASD-STE100 in the report.

## RETURN

Write `_build/lj-1.40-report.md` INCREMENTALLY, skeleton first.

1. **THE VERDICT**, first line: repaired and consumed, repaired only, or
   refused with a measurement.
2. **DID THE AGREEMENT CLOSE?** Answer first after the verdict. This is what
   tests the repair.
3. **ARE THE ROWS TRUE NOW?** State the evidence, and say what would be false
   if a row were still wrong.
4. **HOW MANY ROWS NEEDED AN INDIVIDUAL FIX** beyond the frame change? (DD4.)
5. **DID THE SURVIVING 1,021 LINES REALLY SURVIVE**, or did any need re-laying?
6. **THE NUMBER**: in-fence lines, before and after.
7. **SECONDS AND RATE**, cone separately, against 0.013193.
8. **DID YOU NEED A PLACEMENT ANYWHERE?**
9. **LITERATURE USED.** 10. **ARCHIVE USED.** 11. **WHAT I AM NOT SURE OF.**
