# LJ-1.56: the closedness transfer, then SatGraphAgree and LeafAgree

tier: codex (default)

## GOAL

`[LJ-1.55]` made the twelve agreements frame-generic and they now compose at
their consumer's frame. **The blocker it reported is CURED and committed.**
Build the closedness transfer, the shapedness transfer, `SatGraphAgree` and
`LeafAgree`.

## CWD

`/Users/alsg/Agentic/Bedrock`, on branch `two-tower-bridge`, **clean at
`4afffa5`**. There are no working-tree edits. Earlier briefs said otherwise;
that is no longer true.

## WHAT CHANGED UNDER YOU, and it removes your predecessor's stop

`[LJ-1.55]` found that `oneSameB` read the pair (code, arity) where the
machine's `oneSameAt` reads the pair (arity, argument). **I verified that
myself and cured it** (`src/L/Condensation.lagda.md:1549`, `:1552`).

**So the premise "the same formula on both sides" is now TRUE for the
oneSame frame**, and it was the only frame where it was false.

The cure carries its own consumer test:

```agda
oneSame-eq : ∀ {m} (C : Fin m) → oneSameB C ≡ oneSameAt C
oneSame-eq C = refl
```

That is machine-checked in `src/ProbeLJ155C.agda` at 1.52 s. `bothSameB`
matches `bothSameAt` the same way. `oneSuccB` and `succSndB` match their
machine forms and differ only by the bounded quantifier, which is expected.

**All four closedness relation bodies now agree with the machine.**

## WHAT IS GREEN, so you build on it and do not rebuild it

- `src/ProbeLJ155A.agda`, the slot generalization test.
- **`src/ProbeLJ155B.agda`, 903 in-fence lines: all twelve generalized
  agreements instantiated at the `twelveB` frame, and `TwelveAgree` threading
  the conjunction both directions.** Cold at 13.72 s, spread 1.5 percent.
  **There is no re-indexing layer and you must not add one.**
- `src/ProbeLJ155C.agda`, the closedness diagnostics and the cure's test.
- `src/ProbeLJ154A.agda`: `TagAgree`, `KeyAgree`, `EnvOneAgree`,
  `DefinesAgree`. **`DefinesAgree` is the third conjunct of the leaf
  adequacy, already done.**

## THE CLAIM I WANT TESTED, and it is INFERRED, not measured

`[LJ-1.55]` reported that `domB → domAt` **"is false at the generic frame"**
and that the graph frame's own bounded quantifiers must supply the missing
memberships (`_build/lj-1.55-report.md:114-122`).

**The `domAt → domB` direction is PROVED** under a site fact giving the
witness in K (`ProbeLJ155C:66-86`). That half is measured.

**The other half is an inference and nothing checked it.** Do not accept it
and do not accept my restatement of it. **Test it, then build the wiring that
the graph frame supplies.** If the memberships are there, the transfer is
work rather than a wall. If they are not, write the term you could not write.

**A negative that rests on an inference sets no verdict.** State for every
negative in your return whether its deciding claim is **MEASURED** or
**INFERRED**, in those words.

## THE ORDER OF ATTACK

1. **The eight-frame closedness transfer.** All four bodies now agree, so the
   eight frames are the delivered `UnaryShape` and `BinaryShape` pattern plus
   the bounded-existential rel transfers for the oneSucc and succSnd cases.
2. **The domain transfer**, per the section above.
3. **The shapedness transfer.**
4. **`SatGraphAgree`**: `TwelveAgree` plus closedness, domain, pin-equality
   and the three existential-frame transfers.
5. **`LeafAgree`**, the conjunction of the four atoms, one conjunction deep.

**A partial with an honest ledger is a full deliverable.**

## THE SPELLING RULE THAT DECIDES YOUR SECONDS

**P-v: GIVE A PROOF A NAME AND PASS THE NAME.** The same proof inline as
`refl` in both a type and a body makes the elaborator decide a conversion
between two elaborations of it, and deciding that unfolds the built tree:
**150,133 ms against 220 ms**. One named side is not enough (151,402 ms).

**If any measurement of yours lands in the hundred-second range, look here
before anywhere else.**

## THE LAWS, each with the ACTION it prescribes (C-37)

- **P-u. CERTIFY BEFORE YOU PLACE**, and the action is to compose absoluteness
  through the UNPLACED form, which IS `EraseTransfer`.
- **P-t.** The class follows the FORMULA, not the carrier.
- **D-30. Price what the CONSUMER needs.** That question was worth 5.45x at
  the square law and it produced `[LJ-1.55]`'s slot fix.
- **C-34. Build the cure or report the wall.** "It is a design decision" is
  not a third option.
- **C-35. A delivered block with no consumer is UNTESTED.** `oneSameB` sat
  wrong in HEAD for as long as nothing consumed it, and every gate passed over
  it. **Give what you build a consumer test, not a claim.**
- **C-36.** A failed substitution is not a proof of impossibility. **Write the
  term you could not write.** You may strengthen; you may not weaken.

## WHAT IS SETTLED

- `fin-inj` and `Mext` are DISCHARGED. `sq` has a master whose parameter
  survives on a reshaping that is NOT your task.
- The twelve row agreements are PROVED and now frame-generic. **This is not a
  re-proof question.** If you find yourself re-proving a row, stop and say so.
- **Δ₀ IS the target.** Delivered `Σ₁`'s only base is `σ-Δ₀`.
- All masters carry ZERO placement. **If you need `absFo` or a placed `Δ₀`,
  STOP and report it.**

## SOMETHING YOU WILL SEE AND MUST NOT TOUCH

`src/L/Condensation.lagda.md` carries a superseded **Row layer**
(`RowTransfer`, `RowDecode`, eleven `*Row` modules, five `*Decode` kits),
about 613 lines, dead in both directions. **A compression patch is prepared
and it is NOT your task.** Its line numbers already need re-deriving once.

## THE THRESHOLD

DD24's live bar is **0.012716**. **Do not use 0.013193.** `L.Condensation` is
4,632 in-fence lines; `[LJ-1.55]` measured it at 58.08 s over three cold runs
(rate 0.01254) and I measured 55.00 user s after the cure, one run, which I
do not offer as a cold caliber figure.

Report the marginal rate, the whole-file rate and the cone separately, each
from three cold runs in ONE caliber with the spread.

## DD4

**Maximize the code the two proofs share, and write it generic.** One rule,
two ends, no metric and no checker, so it is stated in every brief and
answered in every return.

`[LJ-1.55]` made the agreement layer frame-generic, which is the DD4 move at
its largest this phase. **Say what the closedness and domain transfers give
the J tower**, and whether they are template or per-tower content.

## ARCHIVE (DD18)

- **`_build/lj-1.55-report.md`**, read WHOLE, and its three probes
  `src/ProbeLJ155A.agda`, `B`, `C`, read WHOLE. C-32 exists because a brief of
  mine named a section and hid the decisive probe.
- **`_build/lj-1.54-report.md`** section 1, for the two atoms' precise
  statements, and `src/ProbeLJ154A.agda`.
- `_build/lj-1.53-report.md` and `_build/lj-1.52-report.md` for the assembled
  chain and the placed wall 2.
- `_build/gch-design-audit.md`, the two-spelling section. **Its zero-consumer
  finding is what C-35 was admitted for and what this dispatch answers.**
- `archive/rud-route/` for SHAPE only; `[LJ-1.11]` showed its condensation
  target is classically FALSE.
- `dev/LESSONS.md` is NOT archived and still binds.

Return an **ARCHIVE USED** section at `file:line`.

## LITERATURE (DD18)

`_build/literature/dev2.txt:1372-1385` and `dev/literature/devlin-II5.md`
Step C bear on the leaf's mathematics. **Devlin asserts absoluteness where
this proves a transfer.** Say in one line what he assumes. The errata do NOT
cover Chapter II section 5; `[LJ-1.14]` verified it, so do not re-check it.

Return a **LITERATURE USED** section, with WHY NOT for anything skipped.

## SCOPE (read)

`_build/lj-1.55-report.md` sections 1c and 2b FIRST, then
`src/ProbeLJ155B.agda` and `src/ProbeLJ155C.agda`, then
`src/L/Condensation.lagda.md:1500-1600` for the cured closedness block, then
`src/L/Coding/Model.lagda.md:2026-2095`.

## SCOPE (write)

`src/L/Condensation.lagda.md`, `src/L/BoundedSubset.lagda.md`, and
`src/ProbeLJ156*.agda`. Your report is `_build/lj-1.56-report.md`. **No other
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
  `git reset --hard` or `git clean`. **The tree is clean; keep your work
  visible in it.**
- Typecheck what you touch and every consumer. Do NOT run `make check`.
- **Run `scripts/check-fences.py --check` before you report anything closed.**
- Count with `scripts/ledger.py`. Run `scripts/lint-prose.py --check` and
  `scripts/lint-agda.py --check`.
- DD23 freezes mathematical prose. Code and its own comments only.
- **The machine is quiet and both Agda slots are yours.**
- Evidence is `file:line`. Write ASD-STE100.

## RETURN

Write `_build/lj-1.56-report.md` incrementally, skeleton first.

Lead with the ledger: which of the five steps landed, and for each that did
not, the term you could not write. **Mark every negative MEASURED or
INFERRED.** Then whether `levelIn` and `cover` are discharged. Then the rates
with spreads in one caliber, the DD4 answer, and **the convergence answer: is
this closing, or is each dispatch renaming the same obligation?**
