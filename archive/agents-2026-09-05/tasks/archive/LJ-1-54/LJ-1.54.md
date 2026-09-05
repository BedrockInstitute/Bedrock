# LJ-1.54: the last unbuilt term, then discharge `levelIn` and `cover`

tier: codex (default)

## GOAL

`[LJ-1.53]` reduced the obligation to **one unbuilt term plus two mechanical
placements**. Build the term, place the two, and discharge both hypotheses.

## CWD

`/Users/alsg/Agentic/Bedrock`, on branch `two-tower-bridge`, clean at
`f7314af`.

## WHAT IS LEFT, from `[LJ-1.53]`'s own ledger

| wall | status |
|---|---|
| 1. `DefBodyB`/`DefBody` leaf adequacy inside `StepAgree` | **half green.** `EraseTransfer` at the leaf is measured at 1.617 s. The residual is a concrete two-way term whose pieces have the delivered row agreements' shape |
| 2. parameter-to-code relabelling inside TV/ElemDown | **FELL.** Built and machine-checked in `src/ProbeLJ153A.agda`. **It needs placing, not proving.** |
| 3. collapse/transitivity | **NOT A WALL.** No `M`-transitivity is needed; the collapse route uses delivered pieces plus walls 1 and 2 |

**So the work is: one unbuilt term, then two placements.**

**The unbuilt term is the machine-side leaf reduction under the site facts.**
`[LJ-1.53]` says its pieces have the shape of the delivered row agreements in
`src/L/Condensation.lagda.md`. **Read those first and reuse their shape.**

## THE ROUTE THAT WORKS

**`EraseTransfer` never runs `erase-Δ₀` at all**: `abs₀` recurses on the Δ₀
WITNESS, not the formula, so the certificate never crosses `erase`.
`src/ProbeDD25H2.agda` instantiates it at 1.56 s and `[LJ-1.53]` measured it at
the leaf at 1.617 s. **Use it.**

**Do NOT build the certificate at variable slots.** `[LJ-1.50]` measured that
as SLOWER, 327 ms against 220.

## THE SPELLING RULE THAT DECIDES YOUR SECONDS

**P-v: GIVE A PROOF A NAME AND PASS THE NAME.** The same proof written inline as
`refl` in both a type and a body makes the elaborator decide a conversion
between two elaborations of it, and deciding that unfolds the built tree.

| spelling | ms |
|---|---:|
| `refl` inline in the type AND the body | **150,133** |
| the proof NAMED and passed | **220** |
| named in the type, `refl` in the body | 151,402 |

**One named side is not enough. If any measurement of yours lands in the
hundred-second range, look here before anywhere else.**

## THE LAWS, each with the ACTION it prescribes (C-37)

- **P-u. CERTIFY BEFORE YOU PLACE**, and the action is to compose the
  absoluteness through the UNPLACED form, which IS `EraseTransfer`.
- **P-t.** The class follows the FORMULA, not the carrier.
- **D-30. Price what the CONSUMER needs.** 5.5 uses each piece at ONE shape.
- **C-34. Build the cure or report the wall that stopped you.** "It is a design
  decision" is not a third option. **Broken three times this phase; a review
  built the deferred cure every time: 0.334 to 0.0108, 0.436 to 0.0072, and
  150 s to 1.56 s.**
- **C-36.** A failed substitution is not a proof of impossibility. **Write the
  term you could not write.** You may strengthen a statement; you may not weaken
  one.

## A NAME I WANT FIXED WHILE YOU ARE IN THE FILE

`src/L/BoundedSubset.lagda.md:1047` has a module parameter called **`hotel`**.
That is a placeholder, and it sits on the proof chain to the trophy
(`:1212` builds `code-inj` from it). **Rename it to what it means.** Its
statement is: every subset of `Lset α` injects into `⟪ α ⟫`. **Say what you
called it.**

**This is presentational and it is not an excuse to touch a theorem.**

## WHAT IS SETTLED, so you do not re-open it

- `fin-inj` and `Mext` are DISCHARGED. `sq` has a master; its parameter
  survives on a consumer reshaping that is NOT your task.
- The twelve-row table, block 1 and the row agreements are CLOSED.
- **Δ₀ IS the target.** Delivered `Σ₁`'s only base is `σ-Δ₀`.
- All masters carry ZERO placement. **If you need `absFo` or a placed `Δ₀`,
  STOP and report it.**

## SOMETHING YOU WILL SEE AND MUST NOT TOUCH

An audit found that `src/L/Condensation.lagda.md` carries a **superseded Row
layer** (`RowTransfer`, `RowDecode`, eleven `*Row` modules, five `*Decode`
kits) that is dead in both directions, about 613 lines. **A compression patch
for it is prepared and it is NOT your task.** Leave it alone: touching it would
force the patch's line numbers to be re-derived twice.

## THE THRESHOLD

DD24's live bar is **0.012716**; the GCH aggregate is 0.0118, within. **Do not
use 0.013193.** Report the marginal rate, the whole-file rate and the cone
separately, each from three cold runs in ONE caliber with the spread.

## DD4

**Maximize the code the two proofs share, and write it generic.** One rule, two
ends, no metric and no checker, so it is stated in every brief and answered in
every return.

`[LJ-1.52]` found the matrix semantics and the graph agreement are Def-side.
**Say which side the leaf reduction falls on**, and whether the collapse route
is template, since it is about a collapse and a tower rather than about
definability.

## ARCHIVE (DD18)

- **`_build/lj-1.53-report.md`** and its probes `src/ProbeLJ153A.agda`,
  `ProbeLJ153Cone.agda`, read WHOLE. C-32 exists because a brief of mine named
  a section and hid the decisive probe.
- **`_build/lj-1.52-report.md`** and its two green probes, for the assembled
  chain.
- `_build/lj-1.50-review.md` with `src/ProbeDD25H2.agda` for the
  `EraseTransfer` route.
- `archive/rud-route/` for SHAPE only; `[LJ-1.11]` showed its condensation
  target is classically FALSE.
- `dev/LESSONS.md` is NOT archived and still binds.

Return an **ARCHIVE USED** section at `file:line`.

## LITERATURE (DD18)

- `_build/literature/dev2.txt:1372-1385` for 5.5, and
  `dev/literature/devlin-II5.md` Step C. **Devlin asserts absoluteness where
  this proves a transfer.** Say in one line what he assumes.
- The errata do NOT cover Chapter II section 5. `[LJ-1.14]` verified it. **Do
  not re-check it.**

Return a **LITERATURE USED** section, with WHY NOT for anything skipped.

## SCOPE (read)

`_build/lj-1.53-report.md` sections 2 to 4 FIRST, then `src/ProbeLJ153A.agda`,
then the delivered row agreements in `src/L/Condensation.lagda.md`, then
`src/ProbeDD25H2.agda`.

## SCOPE (write)

`src/L/BoundedSubset.lagda.md`, `src/L/Condensation.lagda.md`, and
`src/ProbeLJ154*.agda`. Your report is `_build/lj-1.54-report.md`. **No other
master. Never `src/Everything.lagda.md`.**

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
  NOT.**
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

Write `_build/lj-1.54-report.md` incrementally, skeleton first.

Lead with the ledger: are `levelIn` and `cover` DISCHARGED, and if not what each
still needs. Then the leaf reduction: built, or the term you could not write.
Then what you renamed `hotel` to. Then the rates with spreads in one caliber,
the DD4 split, and what you are not sure of.
