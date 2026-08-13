# LJ-1.21: the carrier-level descent, using the cure that already exists

tier: codex (default)

## GOAL

Deliver `|Lset α| = |α|`'s upper half: the descent from the carrier to a
canonical index. **`[L3.32-T85]` already cured this and the cure is GREEN in
the working tree.** Re-derive it as a master. **52 measured lines is the
anchor, not 250 to 450.**

## CWD

`/Users/alsg/Agentic/Bedrock`, on branch `two-tower-bridge`.

## THE SITUATION, and it is a correction

`[LJ-1.6]` delivered the counting half, now at `src/FOL/Count.lagda.md` (620
lines) and `src/L/StageCardinal.lagda.md` (174), and REFUSED the carrier-level
assembly. Its reason: a `sett`'s carrier is the quotient of its index by the
kernel of the embedding, so `⟪ Lset α ⟫` is a quotient of
`Σ β∈α Formula ⟪ Lset β ⟫ 1`, and two formulas can name one definable set, so
the count-bound does not factor through it.

**That objection is TRUE. `[LJ-1.6-R]` verified it and then found it spent:**

> `[L3.32-T85]` found the same quotient on 2026-08-05, verified it under D-10,
> and CURED it. The cure is GREEN in this working tree at
> `src/ProbeTowerInd2.agda:99-159`. The row is at
> `archive/dev/TASKS-archived.md:120`.

**The descent is 52 MEASURED lines** (`_build/l3.32-t85-report.md:108`, GREEN,
12.8 s cold), and the limit half is priced at 150 to 220 (`:245`). So descent
plus assembly is about **220 to 290**, not the 450 to 800 the refusal implied.

**`[LJ-1.6]` asked for the wrong object.** It wanted a canonical NAME. The
delivered route takes the least VALUE in the class via `leastOf` over the
ordinal's own well-order. **No naming theory is needed.** `[LJ-1.6]` never
read `src/L/Choice/` or `src/L/WellOrder/`, which hold `leastOf`,
`stageOrder`, `pullOrder`, `birth` and `leastName`.

## WHAT TO DELIVER

1. **The descent**, re-derived from `src/ProbeTowerInd2.agda:99-159`. **The
   probe is throwaway, so re-derive rather than copy**, and its signature
   tells you the shape: `module Successor (α : S) (iα : Init α) (g : ⟪ Lset α ⟫ ↪ ⟪ α ⟫)`.
2. **The limit half**, priced at 150 to 220.
3. **The assembly**: `|Lset α| = |α|` for the α the chain uses, on top of
   `src/L/StageCardinal.lagda.md`'s delivered counting bound and lower half
   `⟪ α ⟫ ↪ ⟪ Lset α ⟫`.

**READ `StageCardinal` FIRST.** It already holds the counting bound and the
lower half, so the remaining obligation may be smaller than the archive's
figure suggests. Say what it actually leaves.

## THE RESTRICTION YOU INHERIT, and it is not free

`ProbeTowerInd2`'s cure takes `Init α`, **INITIAL ordinals only**, and
`Init ω` is uninhabited. The chain needs the level size at **arbitrary
infinite** ordinals.

**So say plainly which α your delivery covers**, and if it does not reach the
chain's α, price the transfer. `[LJ-1.17]` priced a non-initial transfer at
150 to 400 lines and about 8 seconds, in the same content class, and found it
cannot be extracted from truncated equinumerosity by least-of.

**A delivery that does not reach the consumer is worth nothing however cheap
it is.** If the honest answer is that the restriction blocks it, stop and say
so with the price. That is a full deliverable.

## THE THRESHOLD

DD24 GATES the wing at **0.013193 s per line**, module caliber. The wing's
whole seconds budget is **99.6 to 147.7 s**; it spends about 5 today, and
`[LJ-1.17]` found the square law alone would take 28 to 42 percent of it.

**So seconds are the scarce resource here, not lines.** The wing has NO line
cap by DD24's deliberate omission. **Report your rate, and if a piece lands in
P-n's instantiation class at 0.22 to 0.297 s per line, say so with the number:
that is a finding, not a failure.**

The archive measured the descent at 12.8 s cold for 52 lines, which is 0.246,
squarely in P-n's band. **Ask why, and whether a re-derivation avoids it.**
That question is the most valuable thing you can answer.

## DD4, WHICH GOES IN EVERY BRIEF

**Maximize the code the two proofs share, and write it generic.** One rule,
two ends. It has NO metric and no checker by the owner's ruling, so it is
stated in every brief and answered in every return; the repetition is its only
enforcement.

**`[LJ-1.6]` set the standard here and you should match it:**
`src/FOL/Count.lagda.md` has ZERO `L.` imports and no stage in any type, so
the J tower instantiates it unchanged. **Counting is neither of the two
per-tower objects** `[LJ-0.7]` identified.

**A descent over an ordinal's own well-order is also tower-agnostic**, so keep
it that way: parameterize the MODULE (P-h), keep the stage presentation out of
the types (P-l), and say what the J tower supplies.

## LITERATURE (DD18)

- `dev/literature/devlin-II5.md` sections 1.4 and 1.5, Devlin 5.4 and the
  5.5-5.6 chain that consumes the level size.
- `_build/literature/dev2.txt:1357-1360` for 5.4.
- **Devlin does not prove ordinal arithmetic; he assumes it.** Say what he
  assumes about `|α|` at limits, because it bears on whether the restriction
  above is a real gap or a formalization artefact.

Return a **LITERATURE USED** section, with WHY NOT for anything skipped.

## ARCHIVE (DD18)

- **`_build/l3.32-t85-report.md:108` for the 52 measured lines and `:245` for
  the limit half's 150-to-220 price.** These are your anchors.
- **`archive/dev/TASKS-archived.md:120`, the T85 row.** Read that exact line.
  A previous task grepped this file by topic and missed the row it needed,
  which is why this brief names the line.
- `_build/lj-1.6-review.md`, your commissioning document, and
  `_build/lj-1.6-report.md`, the refusal it corrected.
- `src/ProbeTowerInd2.agda:99-159`, the green cure. Untracked, and it survives
  from 2026-08-05.
- `dev/LESSONS.md` is NOT archived and still binds. **P-h, P-l, P-n, P-m and
  D-10 decide this block.**

Return an **ARCHIVE USED** section at `file:line`.

## MANDATORY RULES FOR A BUILD

From `python3 scripts/rules.py --for build`. Run it and read each statement.

- **P-h.** Module-parameterized, never function-parameterized.
- **P-l.** No stage presentation in a type that does not need one.
- **P-k.** A read lemma is stated where its consumers use it.
- **P-m.** The check-cost rate is a content-class certificate.
- **P-n.** Satisfaction content at a concrete carrier is a payable floor,
  0.22 to 0.297 s per line. **The archived descent measured 0.246. Ask why.**
- **R-35, R-38**: sealing and opacity. Do not unseal.
- **R-40**: state a membership witness SHALLOW and climb.
- **I-5**: the inference trap this tree has paid for.
- **C-12.** `GHCRTS="-A64m -I0 -M8g" agda <file>`, ONE process. A sibling
  holds the other slot.
- **C-22.** Write the deliverable incrementally.
- **D-10.** Every figure above is a residue from a report that is five days
  old. Re-verify.

## THE SIBLING

`[LJ-1.20]` is building the stage-arithmetic kit under `src/L/Ordinal/`.
**Do not write there.** Check
`python3 .claude/skills/codex-dispatch/dispatch.py status`.

- **Never run `git checkout .`, `git stash`, `git reset --hard` or `git
  clean`.** Revert by exact path only.
- **Never commit and never push.**

## SCOPE (read)

`src/L/StageCardinal.lagda.md` FIRST, then `src/ProbeTowerInd2.agda:99-159`,
then `_build/l3.32-t85-report.md`, then `src/L/WellOrder/` and
`src/L/Choice/Stage.lagda.md` for `leastOf` and the stage order.

## SCOPE (write)

`src/L/StageCardinal.lagda.md`, and **at most ONE new master under `src/L/`**.
Your report is `_build/lj-1.21-report.md`. **Not `src/L/Ordinal/`**, which the
sibling owns, and never `src/Everything.lagda.md`.

## CONSTRAINTS

- **Never commit and never push.**
- **Typecheck every file you write AND every consumer**, one process at a
  time. Do NOT run `make check`.
- **Count with `python3 scripts/ledger.py`'s caliber.**
- **Report cold seconds and the RATE per file.**
- **Run `python3 scripts/lint-prose.py --check` and `python3
  scripts/lint-agda.py --check`.**
- **DD23 freezes mathematical prose.** Code and its own comments only.
- **Evidence is `file:line`.**
- **A stop with a price is a SUCCESS.**
- Write ASD-STE100 in the report.

## RETURN

Write `_build/lj-1.21-report.md` INCREMENTALLY, skeleton first.

1. **THE VERDICT**, first line: delivered with lines and rate, or stopped with
   a price.
2. **WHICH α YOUR DELIVERY COVERS**, and whether it reaches the chain's.
3. **WHAT `StageCardinal` ALREADY LEFT**, so the remaining obligation is
   stated rather than assumed.
4. **THE NUMBER**: in-fence lines per file.
5. **SECONDS AND RATE**, and **WHY THE ARCHIVED DESCENT RAN AT 0.246**, and
   whether your re-derivation avoids it.
6. **WHAT THE J TOWER SUPPLIES** (DD4).
7. **LITERATURE USED.**
8. **ARCHIVE USED.**
9. **WHAT I AM NOT SURE OF.**
