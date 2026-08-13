# LJ-1.25: apply the measured cure to the limit half

tier: codex (default)

## GOAL

`[LJ-1.24]` measured a 12.8x cure and did not apply it. Apply it to
`src/L/StageCardinal.lagda.md`. **The measurement is done. Your job is to land
it and re-measure the whole master.**

## CWD

`/Users/alsg/Agentic/Bedrock`, on branch `two-tower-bridge`.

## WHAT WAS MEASURED, and it is not a hypothesis

`[LJ-1.21]` delivered the level size. Its limit half costs **31.0 s over 115
lines, a rate of 0.270**. That single block held about two thirds of every
second the GCH wing has spent.

`[LJ-1.24]` abstracted the SOURCE and measured, back to back on one machine:

| form | cold seconds | rate |
|---|---:|---:|
| control, a verbatim copy of the master's limit half | 29.122, then 31.767 | 0.247 to 0.269 |
| **arm 1, the abstract source** | **2.281, then 2.325** | **0.019** |

**A 12.8x reduction, about 26.8 s, for about 6 lines.** The cured form is
GREEN at `src/ProbeLJ124Arm1.agda`.

## THE CURE, exactly as measured

The module takes two new parameters:

```
D   : (δ : S) → Formula ⟪ Lset δ ⟫ 1 → S
inv : the D-shaped δ-witness
```

Every `DefOf.defSet (Lset ...)` mention **in the limit half's STATEMENTS**
becomes a `D` application. `inv` is instantiated with `𝒟ₒ-inv` at the end of
`limit-step`. **The proof bodies do not change**: `[LJ-1.24]` reports the two
stability proofs were already generic in the source.

`[LJ-1.24]` priced the edit at about 6 lines: 3 for the module header, 3 for
the two instantiations in `limit-step`, and seven one-line replacements that
add nothing.

**`Upper` calls `limit-step` with the same signature, so no consumer changes.**
Verify that rather than trust it.

## THE ROOT CAUSE, so you do not over-apply the cure

The cost is **the transport over a TRANSPARENT `sett` index**. `DefOf.defSet`
is born at `src/L/Definability.lagda.md:111-112` as
`sett (Σ[ m ∈ ⟪ A ⟫ ] ⟨ smallSat φ m ⟩) ...`, delivered transparent. A
transport across that index unfolds the satisfaction tower. The same transport
across an abstract index unfolds nothing.

**So abstract the statement positions the transports cross. Do not abstract
the whole module for tidiness**, and do not touch the descent: it already runs
at 0.061 because it is parameterized.

**One open thread from `[LJ-1.24]` section 10.** `Successor.go₂` costs 4.5 s
and names `defSet` WITHOUT a transport, so naming alone costs something
somewhere. **If the same abstraction cheaply covers `go₂`, measure it and say
what it bought. If it does not, leave it and say so.** Do not spend the block
on it.

## WHAT YOU MUST RE-MEASURE

`[LJ-1.24]` measured the block in ISOLATION. You must report the WHOLE master
cold, because that is the number the ledger takes.

`[LJ-1.21]` measured the whole master at **42.03 s over 484 in-fence lines,
a rate of 0.087**. **Report the new whole-master cold seconds and rate against
that.** DD24's bar is 0.013193, module caliber.

**Machine state: the tree is quiet and no sibling holds an Agda slot.** Say so
if that changes. `[LJ-1.21]`'s and `[LJ-1.24]`'s figures were taken under
contention, so a quiet re-measure is worth stating plainly.

## DD4, WHICH GOES IN EVERY BRIEF

**Maximize the code the two proofs share, and write it generic.** One rule,
two ends. It has NO metric and no checker by the owner's ruling, so it is
stated in every brief and answered in every return; the repetition is its only
enforcement.

**This cure IS a DD4 move and that is the second reason to take it.**
`[LJ-1.24]` found it shrinks the L-specific list: the limit half stops naming
`DefOf.defSet` and stops applying `𝒟ₒ-inv`, and the J tower supplies the pair
`(D, inv)` instead. It also found the shrink is PARTIAL: `Lset`, `Formula` and
`𝒟ₒ` remain in the parameter types.

**Say in the return what the J tower now supplies, and whether a second layer
would remove the remaining three.** Do not build that second layer here.

## WHAT YOU MAY NOT TOUCH

- **`src/L/Hull.lagda.md`.** `[LJ-1.23]` just delivered it, uncommitted and
  under audit.
- **`src/L/Ordinal/`.** `[LJ-1.20]` just delivered `StageArith.lagda.md`,
  uncommitted.
- **`src/L/Definability.lagda.md`.** Sealing or changing `defSet` at its birth
  site is a different task with a different price. `[LJ-1.24]` did not measure
  it, and the archive records that seal transplanting at ZERO.
- **`src/Everything.lagda.md`.** I wire the catalog after auditing.

## LITERATURE (DD18)

**None bears, and `[LJ-1.24]` already established that.** This is a check-cost
edit on delivered code. **Say so in one line naming `dev/literature/` and
spend nothing.**

## ARCHIVE (DD18)

- **`_build/lj-1.24-report.md` sections 3, 6 and 7.** The cure, its class and
  its line price. **Section 10 names what it did not measure.**
- **`src/ProbeLJ124Arm1.agda`, the GREEN cured form**, with
  `src/ProbeLJ124Control.agda` and `src/ProbeLJ124Base.agda` beside it.
  **The probes are throwaway. Re-derive into the master; do not copy a probe
  in.**
- `_build/lj-1.21-report.md` sections 4 and 5, the delivered block and its
  profile.
- **`archive/rud-route/src/L/Ordinal/SquareLaw.lagda.md:213-242`**, where this
  same abstract-restatement shape won before.
- `dev/LESSONS.md` is NOT archived and still binds. **P-l, P-h, P-m, P-n,
  R-38, C-31 and D-10 decide this block.**

Return an **ARCHIVE USED** section at `file:line`.

## MANDATORY RULES FOR A BUILD

From `python3 scripts/rules.py --for build`. Run it and read each statement.

- **P-h.** Module-parameterized, never function-parameterized.
- **P-l, AND IT IS THE LAW THIS CURE OBEYS.** "Being about a concrete position
  is not what costs. **Naming a transparent construction in a statement's TYPE
  is.**"
- **P-k.** A read lemma is stated where its consumers use it.
- **P-m.** The check-cost rate is a content-class certificate.
- **P-n.** `[LJ-1.24]` ruled this block R-38's class, NOT P-n's floor, and
  measured the proof. Do not re-litigate it.
- **R-38.** Do not unseal. Do not seal `defSet`.
- **R-35, AND IT IS ARM 2 THAT NOBODY RAN.** Union representations are
  meta-poisoned; state the membership at the SMALL INDEX and climb. The limit
  half argues over a union of member stages, so R-35 genuinely bears here.
  `[LJ-1.24]` stopped at arm 1 by my stop rule and never measured it.
  **Arm 1 is the ruled cure and you land it first.** If R-35's shape then
  removes a transport that arm 1 only made cheap, measure it and report the
  delta. **Do not restructure the block for R-35 if arm 1 already lands it
  under the bar.**
- **R-40.** State a membership witness SHALLOW and climb. The limit half's
  witnesses come from `Lset-out`. **Say whether any witness is stated deeper
  than it needs to be**; that is the same family as R-35 and it is cheap to
  check while you are in the file.
- **I-5**: the inference trap this tree has paid for.
- **C-12.** `GHCRTS="-A64m -I0 -M8g" agda <file>`, ONE process.
- **C-22.** Write the deliverable incrementally.
- **D-10.** The 6-line price is a residue from a report one hour old.
  Re-verify the control before you trust the delta.

## SCOPE (read)

`src/ProbeLJ124Arm1.agda` FIRST, then `src/L/StageCardinal.lagda.md:363-580`,
then `_build/lj-1.24-report.md`.

## SCOPE (write)

`src/L/StageCardinal.lagda.md` ONLY. Your report is
`_build/lj-1.25-report.md`. **No new master. No other file under `src/`
except a `Probe` file if you need one.**

## CONSTRAINTS

- **Never commit and never push.**
- **Never run `git checkout .`, `git stash`, `git reset --hard` or `git
  clean`.** Revert by exact path only. Two builds are uncommitted.
- **Typecheck the master AND its consumers.** Do NOT run `make check`.
- **Do not weaken or delete a theorem that stands.** The cure changes
  statement positions, not results. **If any exported type changes, say so
  loudly**: `stage-card-upper`'s statement must survive unchanged.
- **Count with `python3 scripts/ledger.py`'s caliber.** DD26 excludes the two
  catalogs.
- **Run `python3 scripts/lint-prose.py --check` and `python3
  scripts/lint-agda.py --check`.**
- **DD23 freezes mathematical prose.** Code and its own comments only.
- **Evidence is `file:line`.**
- **If the cure does NOT reproduce on the master, say so with the number.**
  That is a full deliverable and it is more valuable than a forced landing.
- Write ASD-STE100 in the report.

## RETURN

Write `_build/lj-1.25-report.md` INCREMENTALLY, skeleton first.

1. **THE VERDICT**, first line: the new whole-master cold seconds and rate,
   against 42.03 s and 0.087.
2. **DID THE CURE REPRODUCE** at the master, and what did it actually cost in
   lines?
3. **DID ANY EXPORTED TYPE CHANGE?** `stage-card-upper` above all.
4. **`Successor.go₂`**: measured, or left with a reason?
5. **THE NUMBER**: in-fence lines, before and after.
6. **DD4**: what the J tower supplies now, and whether a second layer would
   remove `Lset`, `Formula` and `𝒟ₒ`.
7. **ARCHIVE USED.** 8. **WHAT I AM NOT SURE OF.**
