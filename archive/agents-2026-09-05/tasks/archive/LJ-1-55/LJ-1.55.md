# LJ-1.55: the agreements' slot convention, and the last two atoms

tier: codex (default)

## GOAL

`[LJ-1.54]` found that the twelve row agreements **cannot be instantiated at the
frame that needs them**. Fix that, then finish the leaf reduction.

## CWD

`/Users/alsg/Agentic/Bedrock`, on branch `two-tower-bridge`, clean at
`f7314af` plus two working-tree edits.

## THE FINDING, and I verified it myself

`BotAgree` takes `(C T B N : Fin n)` and `(γ : S ^ suc n)` with **K hard-coded
at `lookup zero γ`** (`src/L/Condensation.lagda.md:2704-2712`).

`SatGraphB.twelveB` puts **B at slot 0**, T at 1, C at 2, and K at `suc⁶ K`
(`:2211-2222`).

**So the instantiation needs `suc B = zero`, which has no solution in `Fin`.**
The twelve agreements do not compose at their consumer's frame.

This also explains, mechanically, a separate audit's finding that the ~2,500
line agreement layer has **zero consumers**: `src/L/BoundedSubset.lagda.md` takes
only `DefBodyB`, `Δ₀-DefBodyB` and `module GraphB` from `L.Condensation`.

## THE QUESTION I WANT ANSWERED FIRST, and it is a question

The agreements are already generic in `C`, `T`, `B` and `N`: they take them as
`Fin n` parameters. **Only K is hard-coded, as `lookup zero γ`.**

**So: can K become a parameter too?** If the agreements took `(K : Fin n)`
beside the other four and read `lookup K γ`, they would instantiate at any
frame, including `twelveB`'s.

**If that is right, this is a signature change across twelve modules and their
shared frames, mechanical, with the proofs untouched.** If it is wrong, say why
and what the real shape is.

**I am asking, not instructing.** `dev/LESSONS.md` C-33 and C-37 exist because
my briefs foreclosed answers, and I have been wrong about this file's
mathematics before. **Test it before you build it.**

**D-30 is the frame: price what the CONSUMER needs.** The slot convention was
chosen when the agreements were written, before their consumer existed. That is
exactly the shape D-30 was admitted for, and there it was worth 5.45x.

## THEN THE TWO REMAINING ATOMS

`[LJ-1.54]` built four atoms of the leaf reduction and left two, both with their
shape named:

1. **`WitnessAgree`**: `hasWitnessBS ↔ hasWitnessAt`. Its pieces are eight shape
   frames, the shapedness transfer and the `domB ↔ domAt` transfer. **None is a
   new idea; all have the delivered shape agreements' shape**
   (`src/L/Condensation.lagda.md:2512-2702`).
2. **`SatGraphAgree`**: composing `TwelveAgree` with closedness, domain,
   pin-equality and three existential-frame transfers.

Then `LeafAgree` is their conjunction with the two built atoms, **one
conjunction deep**.

## WHAT IS ALREADY GREEN, so you build on it

`src/ProbeLJ154A.agda` typechecks at 1.92 / 1.99 / 2.03 s and holds `TagAgree`,
`KeyAgree`, `EnvOneAgree` and `DefinesAgree`. **`DefinesAgree` is the third
conjunct of the leaf adequacy, already done.**

Wall 2 is PLACED and green in the master. The `hotel` rename is done.

## THE SPELLING RULE THAT DECIDES YOUR SECONDS

**P-v: GIVE A PROOF A NAME AND PASS THE NAME.** The same proof inline as `refl`
in both a type and a body makes the elaborator decide a conversion between two
elaborations of it, and deciding that unfolds the built tree: **150,133 ms
against 220 ms**, and one named side is not enough (151,402 ms).

## THE LAWS, each with the ACTION it prescribes (C-37)

- **P-u. CERTIFY BEFORE YOU PLACE**, and the action is to compose absoluteness
  through the UNPLACED form, which IS `EraseTransfer`.
- **P-t.** The class follows the FORMULA, not the carrier.
- **D-30. Price what the CONSUMER needs**, which is this brief's whole first
  half.
- **C-34. Build the cure or report the wall.** "It is a design decision" is not
  a third option; that has been broken three times this phase and a review built
  the deferred cure every time.
- **C-36.** A failed substitution is not a proof of impossibility. **Write the
  term you could not write.** You may strengthen; you may not weaken.

## WHAT IS SETTLED

- `fin-inj` and `Mext` are DISCHARGED; `sq` has a master whose parameter
  survives on a reshaping that is NOT your task.
- The twelve row agreements are PROVED. **This is a re-indexing question, not a
  re-proof.** If you find yourself re-proving a row, stop and say so.
- **Δ₀ IS the target.** Delivered `Σ₁`'s only base is `σ-Δ₀`.
- All masters carry ZERO placement. **If you need `absFo` or a placed `Δ₀`,
  STOP and report it.**

## SOMETHING YOU WILL SEE AND MUST NOT TOUCH

`src/L/Condensation.lagda.md` carries a superseded **Row layer**
(`RowTransfer`, `RowDecode`, eleven `*Row` modules, five `*Decode` kits), about
613 lines, dead in both directions. **A compression patch is prepared and it is
NOT your task.** Leave it: touching it forces the patch's line numbers to be
re-derived twice.

## THE THRESHOLD

DD24's live bar is **0.012716**; the GCH aggregate is 0.0118, within. **Do not
use 0.013193.** Report the marginal rate, the whole-file rate and the cone
separately, each from three cold runs in ONE caliber with the spread.

## DD4

**Maximize the code the two proofs share, and write it generic.** One rule, two
ends, no metric and no checker, so it is stated in every brief and answered in
every return.

**A K-parameterized agreement is strictly more shared than a K-at-slot-zero
one**, so if the answer to the first question is yes, the fix is also the DD4
move. Say what the J tower inherits.

## ARCHIVE (DD18)

- **`_build/lj-1.54-report.md`** sections 1.1 and 1.2, and its probe
  `src/ProbeLJ154A.agda`, read WHOLE. C-32 exists because a brief of mine named
  a section and hid the decisive probe.
- `_build/lj-1.53-report.md` and `_build/lj-1.52-report.md` for the assembled
  chain and the placed wall 2.
- `_build/gch-design-audit.md`, which found the agreement layer has no
  consumers. **Read its section on the two-spelling table.**
- `archive/rud-route/` for SHAPE only; `[LJ-1.11]` showed its condensation
  target is classically FALSE.
- `dev/LESSONS.md` is NOT archived and still binds.

Return an **ARCHIVE USED** section at `file:line`.

## LITERATURE (DD18)

**Nothing bears on the slot convention**; it is this tree's own indexing choice.
`_build/literature/dev2.txt:1372-1385` and `dev/literature/devlin-II5.md`
Step C bear on the leaf's mathematics. **Say so in one line and spend little.**

Return a **LITERATURE USED** section, with WHY NOT for anything skipped.

## SCOPE (read)

`_build/lj-1.54-report.md` section 1 FIRST, then
`src/L/Condensation.lagda.md:2211-2310` and `:2704-2743`, then
`src/ProbeLJ154A.agda`.

## SCOPE (write)

`src/L/Condensation.lagda.md`, `src/L/BoundedSubset.lagda.md`, and
`src/ProbeLJ155*.agda`. Your report is `_build/lj-1.55-report.md`. **No other
master. Never `src/Everything.lagda.md`.**

## MANDATORY RULES FOR A BUILD

Run `python3 scripts/rules.py --for build` and read every statement.

- **P-h.** Module-parameterized, never function-parameterized. **This brief's
  first question is P-h applied to K.**
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
  `git reset --hard` or `git clean`. **Two masters carry uncommitted work.**
- Typecheck what you touch and every consumer. Do NOT run `make check`.
- **Run `scripts/check-fences.py --check` before you report anything closed.**
- Count with `scripts/ledger.py`. Run `scripts/lint-prose.py --check` and
  `scripts/lint-agda.py --check`.
- DD23 freezes mathematical prose. Code and its own comments only.
- **The machine is quiet and both Agda slots are yours.**
- Evidence is `file:line`. Write ASD-STE100.

## RETURN

Write `_build/lj-1.55-report.md` incrementally, skeleton first.

Lead with the slot answer: can K be a parameter, and what did the change cost?
Then the two atoms: built, or the terms you could not write. Then whether
`levelIn` and `cover` are discharged. Then the rates with spreads in one
caliber, the DD4 answer, and **the convergence answer: is this closing, or is
each dispatch renaming the same obligation?**
