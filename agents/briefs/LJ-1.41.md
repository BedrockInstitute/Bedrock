# LJ-1.41: close the eleven remaining row agreements

tier: codex (default)

## GOAL

`[LJ-1.40]` repaired the rows and closed ONE row's agreement plus all the
shared machinery. **Close the other eleven.** The pattern is worked and the
machinery is delivered.

## CWD

`/Users/alsg/Agentic/Bedrock`, on branch `two-tower-bridge`.

## WHAT IS DELIVERED AND GREEN, committed at `6656922`

`src/L/Condensation.lagda.md` is **2,498 in-fence lines at 0.00512 s per line**,
0.39 of DD24's bar, **zero placement constructs, zero escape hatches**. The
orchestrator re-measured it cold at 12.79 s.

**Closed and machine-checked, so do NOT rebuild any of it:**

- the **Bot row**, both directions: `BotAgree.bot-out` and `BotAgree.bot-in`
  (`:2610-2638`). **This is your worked pattern.**
- the extension-frame transfer both ways, `extAtB→extAt` and `extAt→extAtB`
  (`:2398-2416`);
- the unary and binary shape transfers, `UnaryShape` and `BinaryShape`
  (`:2418-2608`);
- the empty operation transfer (`:2597-2606`);
- the environment-condition transfer at the ATOM layout, `EnvB2T`
  (`:2645-2682`);
- the term-value transfer, `TmVal` (`:2684-2776`).

## WHAT EACH REMAINING ROW OWES, named by `[LJ-1.40]`

Each of the eleven needs the same assembly:

1. **its leaf transfers**: the operations `sameAt`, `diffAt`, `interAt`,
   `unionAt` and `implAt` against the bounded operations; the atom body; the
   quantifier bodies; the bounded-quantifier bodies; and the proposition body;
2. **its frame assembly at the class carrier.**

**The environment transfer exists for the ATOM layout only. The other three
frame layouts need their own instances of the same transfer.** That is the one
piece of genuinely new machinery, and it is three instances of a delivered
shape.

## D-29 IS THE LAW THIS BLOCK TESTS, and it was admitted from this same file

**A shared layer propagates a FIX and a DEFECT at the same rate.** After
`[LJ-1.40]`'s frame repair, **nine of eleven rows were pure mechanical
re-indexing**. So the sharing is real.

**Therefore: if you find yourself writing eleven similar agreements, stop and
ask whether one parameterized agreement serves.** Report how many rows needed
anything beyond the shared assembly. **That number is this block's DD4
evidence**, and `[LJ-1.40]` measured the comparable at two of twelve.

**And D-29's other face binds you too: audit the shared assembly against the
machine BEFORE instantiating it eleven times.** Instantiating first buys eleven
copies of any defect for the price of one. **That is exactly how the defect you
are repairing got in.**

## THE STANDARD THE LAST BLOCK SET, and you are held to it

`[LJ-1.40]` did NOT call a partial result delivered. It closed one row, said
precisely what the other eleven owed, and stopped. **That was the right call
and it is the standard here.**

**C-35: a delivered block with no consumer is UNTESTED.** The agreement IS the
consumer. **A row whose agreement does not close is not a repaired row; it is
an untested one.** If a row cannot close, **say which and why, and do not
weaken the statement to make it close** — weakening is what produced the
original defect.

## THE DEFECT'S SHAPE, so you recognize it if it recurs

The old rows ended in `∀̇∈ (var yc) body`, vacuous at an empty value, where the
machine's `extAt yc body` constrains it. Worse, one index read the terms at the
frame's member rather than the extension candidate, **so the defining condition
never mentioned the element it defines**. `src/ProbeDD25E1.agda` is the green
countermodel and `src/ProbeDD25E3.agda` is the RED control.

**If a row's agreement closes suspiciously easily, check it against those two
probes before believing it.**

## THE LAWS THAT DECIDE THE SHAPE

- **P-u.** Certify BEFORE you place. **The master has ZERO placement and that
  is load-bearing. If you need `absFo` or a placed `Δ₀`, STOP and report it**:
  that wall is flat at 8 GB across constant counts 0, 1, 2 and 5.
- **P-v.** Never force a satisfaction-level conversion between two spellings of
  one formula. **Write in the machine's spelling from the start.** 59 ms
  against 29,415 ms. **The original defect is this law ignored.**
- **P-l.** Naming a built construction in a statement's TYPE is what costs.
- **P-t.** The class follows the FORMULA, not the carrier.

## DD4, WHICH GOES IN EVERY BRIEF

**Maximize the code the two proofs share, and write it generic.** One rule,
two ends. It has NO metric and no checker by the owner's ruling, so it is
stated in every brief and answered in every return; the repetition is its only
enforcement.

**Say which side each agreement piece falls on.** The transfers are template if
they are generic in the row's body; the row-specific leaf content is per-tower
Def content. D-26 predicts per-tower for anything keyed on the Def syntax,
because `Lset` is a definable power while the J tower's stage carries
generation data.

## THE THRESHOLD

DD24 gates at **0.013193 s per line**, module caliber. The master runs at
**0.00512** and the agreement content measured **0.0079** at
`[LJ-1.34-R]`'s site, with row readings **under 0.12 s total** at `[LJ-1.36]`.
**So expect the rate to rise slightly and stay far under. Report it, and
report the module-load cone separately.**

**C-31: a budget from a projected size is divided by the PROJECTED size. The
per-module flag is ADVICE; the aggregate is the judgment.**

## LITERATURE (DD18)

- `dev/literature/devlin-II5.md`, Step C. **Devlin asserts absoluteness where
  this block proves a decode**, so the book cannot price these rows. Say so in
  one line and spend nothing more.
- The errata do NOT cover Chapter II section 5. `[LJ-1.14]` verified it. **Do
  not re-check it.**

Return a **LITERATURE USED** section, with WHY NOT for anything skipped.

## ARCHIVE (DD18)

**Read these WHOLE. C-32 exists because a brief of mine named a SECTION and hid
the decisive probe.**

- **`_build/lj-1.40-report.md`**, what closed and what each row owes.
- **`src/L/Condensation.lagda.md`** as committed, especially `BotAgree` at
  `:2610-2638`, which is your pattern.
- **`_build/lj-1.38-review.md`**, the defect and why the nonemptiness cure is
  dead.
- `src/ProbeDD25E1.agda`, `E2` and `E3`.
- `src/L/Coding/Model.lagda.md`, the machine, which is CORRECT.
- `dev/LESSONS.md` is NOT archived and still binds. **C-35 and D-29 are new and
  both were admitted from this file.**

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
- **C-22.** Write the deliverable incrementally. **`[LJ-1.40]` did this and its
  in-progress report is why its health was checkable mid-run.**
- **C-31.** A budget from a projected size is divided by the projected size.
- **C-32.** A cure invalidates downstream measurements. **Interfaces live in
  `_build/2.8.0/agda/src/`, NOT beside the source.**
- **C-33.** I have tried to name the OBLIGATION and not an entry point.
- **C-34.** Build the cure or report the wall.
- **C-35.** No consumer, no DELIVERED.
- **D-29.** Audit the shared assembly before instantiating it eleven times.
- **D-10.** Every figure here is a residue. Re-verify.

## SCOPE (read)

`_build/lj-1.40-report.md` FIRST, then `src/L/Condensation.lagda.md`'s
`BotAgree` and the shared transfers, then `src/L/Coding/Model.lagda.md`.

## SCOPE (write)

`src/L/Condensation.lagda.md`, plus `src/ProbeLJ141*.agda` if you need them.
Your report is `_build/lj-1.41-report.md`. **No other master. Never
`src/Everything.lagda.md`.**

## CONSTRAINTS

- **Never commit and never push.**
- **Never `git checkout .`, `git stash`, `git reset --hard` or `git clean`.**
- **Typecheck the master AND every consumer.** Do NOT run `make check`.
- **Do not weaken a statement to make it close.**
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

Write `_build/lj-1.41-report.md` INCREMENTALLY, skeleton first.

1. **THE VERDICT**, first line: how many of the eleven closed, and the rate.
2. **WHICH ROWS CLOSED AND WHICH DID NOT**, with what each unclosed one owes.
3. **HOW MANY ROWS NEEDED ANYTHING BEYOND THE SHARED ASSEMBLY?** (DD4, D-29.)
4. **DID YOU AUDIT THE SHARED ASSEMBLY BEFORE INSTANTIATING IT?** Say how.
5. **THE NUMBER**: in-fence lines, before and after.
6. **SECONDS AND RATE**, cone separately, against 0.013193.
7. **DID YOU NEED A PLACEMENT ANYWHERE?**
8. **WHAT CONDENSATION STILL OWES** after this block. `[LJ-1.7]` is next.
9. **LITERATURE USED.** 10. **ARCHIVE USED.** 11. **WHAT I AM NOT SURE OF.**
