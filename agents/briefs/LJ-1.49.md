# LJ-1.49: discharge the two hypotheses, then price what is left

tier: codex (default)

## GOAL

`[LJ-1.7-R]` overturned both of `[LJ-1.7]`'s blockers and built the cures.
**Land them, delete the hypotheses, and then attack the one genuine residue it
names.**

## CWD

`/Users/alsg/Agentic/Bedrock`, on branch `two-tower-bridge`. HEAD `69059c0`,
plus the untracked master `src/L/BoundedSubset.lagda.md`.

## THE TWO CURES, built and green, and I re-ran all three probes myself

**Cure 1, the slot spelling.** `countFo matrix = 328` is TRUE and
machine-checked, but "therefore the level-hood instantiation is blocked" is an
inference and it is wrong. The 328 decomposes as **eight copies of one
41-constant leaf**, and every constant is `con (numeralL k)`, an arity tag.

**The file already documents the cure as its own house style**
(`src/L/Condensation.lagda.md:1111-1114`: the tag numerals are slots, so every
formula is constant-free) **and its twelve delivered rows already run it** via
`arTagB` and `arTagPairB`. **The `*Bnum` family is a second spelling**, which is
P-v's defect.

The slot spelling of the whole chain gives `countFo ≡ 0` by `refl`, `erase`
then applies, Δ₀ survives. **256 lines at 0.0113 s per line marginal, ZERO
consumer edits**, because `DefBodyB`'s signature already carries `N0` to `N11`.
`src/ProbeDD25G1.agda` is green; I measured it at 2.61 s.

**Cure 2, delete `collapseCode` outright.** `[LJ-1.7]` said the witness of a
collapse value "is merely a code". **That conflates two fibres.** The witness is
a member of `M`, and THAT fibre is a proposition because π is injective on `M`.
Only `⟪M⟫ → Code` has a non-prop fibre, and `L.StageCardinal.Successor.h`
already solves that exact shape with `leastOf` over `OrdSWO.ordSWO`. The order
on the codes is `CC.count`, which the master proves itself.

`src/ProbeDD25G3.agda` builds the composite `⟪πX⟫ ↪ ⟪α⟫` with **no
`collapseCode` hypothesis**, 104 lines, and I measured it at 0.87 s. **The
hypothesis is deleted, not discharged.**

## WHAT TO DELIVER

1. **Land cure 1** so `levelIn` can be discharged.
2. **Land cure 2** so `collapseCode` disappears from the module parameters.
3. **Attack the residue** in section 3.

**`levelIn` and `cover` are module parameters at
`src/L/BoundedSubset.lagda.md:597-598`.** The theorem is proved FROM them.
**C-35: a theorem whose hard part is a hypothesis is not the theorem.** Report
exactly which parameters survive and why.

## THE RESIDUE THE REVIEW DID NOT SETTLE, and it is now the widest term

`[LJ-1.7-R]` says plainly that it did not build or price two things:

- **the adequacy of the level-hood formula at the hull's carrier**, and
- **`ElemDown`.**

It argues their machines exist and says it did not verify that. **If that chain
is the real obstruction, `[LJ-1.7]`'s stop was right for a reason it never
gave.**

**So price them, and build them if they are small.** C-34: if you name a cure,
build it and measure it, or report the wall that stopped you. **"P-l forbids
it" is not a third option**: P-l forbids pricing by analogy, never measuring.

## HOW THE LAWS HERE CUT, and I got this wrong last time

**`dev/LESSONS.md` C-37 was admitted today because my last brief stated P-u as a
prohibition and hid its cure.** Both halves, action first:

- **P-u. CERTIFY BEFORE YOU PLACE.** The action is to make the formula
  constant-free so no placement is needed. **That is what cure 1 does.** The
  prohibition is the second half: if you find yourself needing `absFo` or a
  placed `Δ₀`, that is the sign you skipped the action, and the wall behind it
  is flat at 8 GB across constant counts 0, 1, 2 and 5.
- **P-v. WRITE ONE SPELLING, decided at the formula level.** It is a CURE, not
  only a cost. The `*Bnum` family being a second spelling of the slot family is
  exactly the defect it names.
- **D-30. Price what the CONSUMER needs.** 5.5 uses condensation at ONE shape.
- **C-36.** A failed substitution is not a proof of impossibility. **You may
  strengthen a statement; you may not weaken one.**

## DD4

**Maximize the code the two proofs share, and write it generic.** One rule, two
ends, no metric and no checker, so it is stated in every brief and answered in
every return.

Cure 1 costs zero consumer edits because the signature already carries the
slots, which is the same property `[LJ-1.31]` measured. **Say what the J tower
inherits from each cure.**

## THE THRESHOLD

DD24's live bar is **0.012716**. `src/L/BoundedSubset.lagda.md` measures
**0.0111** on my own cold run, under it. The GCH aggregate sits at **0.0129 to
0.0132**, inside the run-to-run band around the bar, **so there is no margin**.
Report the marginal rate for what you add, the whole-file rate and the cone,
each from three cold runs with the spread.

## ARCHIVE (DD18)

- **`_build/lj-1.7-review.md`**, the overturn and both cures, read WHOLE.
- **`src/ProbeDD25G1.agda`, `G2` and `G3`**, all green and re-run by me.
- `_build/lj-1.7-report.md`, the structure that is already proved.
- `_build/lj-1.48-report.md` with `src/ProbeLJ148.agda`, the measured transfer
  skeleton.
- `archive/rud-route/` bears only for SHAPE; `[LJ-1.11]` showed its
  condensation target is classically FALSE, so take no price from it.
- `dev/LESSONS.md` is NOT archived and still binds.

Return an **ARCHIVE USED** section at `file:line`.

## LITERATURE (DD18)

- `_build/literature/dev2.txt:1372-1385` for 5.5, and
  `dev/literature/devlin-II5.md` Step C for what absoluteness Devlin asserts
  where this proves a transfer.
- The errata do NOT cover Chapter II section 5. `[LJ-1.14]` verified it. **Do
  not re-check it.**

Return a **LITERATURE USED** section, with WHY NOT for anything skipped.

## SCOPE (read)

`_build/lj-1.7-review.md` FIRST, then the three `ProbeDD25G*` probes, then
`src/L/BoundedSubset.lagda.md`, then `src/L/Condensation.lagda.md:1111-1114`
and the `*Bnum` family.

## SCOPE (write)

`src/L/BoundedSubset.lagda.md` and `src/L/Condensation.lagda.md`, plus
`src/ProbeLJ149*.agda` if you need them. Your report is
`_build/lj-1.49-report.md`. **No other master. Never
`src/Everything.lagda.md`.**

## MANDATORY RULES FOR A BUILD

Run `python3 scripts/rules.py --for build` and read every statement.

- **P-h.** Module-parameterized, never function-parameterized.
- **P-k.** A read lemma is stated where its consumers use it.
- **P-l, P-m, P-n, P-t, P-u, P-v** as above.
- **R-35.** Union representations are meta-poisoned: state the membership at
  the SMALL index and climb.
- **R-38.** Seal at the birth site, and do NOT unseal.
- **R-40.** State a membership witness SHALLOW and climb.
- **I-5.** The inference trap this tree has paid for.
- **C-12.** `GHCRTS="-A64m -I0 -M8g" agda <file>`, ONE process, cap never
  raised. **Report a heap exhaustion as a WALL with its seconds.**
- **C-22.** Write the deliverable incrementally.
- **C-31, C-32, C-33, C-34, C-35, C-36, C-37.**
- **D-10, D-26, D-29, D-30.**

## CONSTRAINTS

- Never commit, never push, never `git checkout .`, `git stash`,
  `git reset --hard` or `git clean`.
- Typecheck both masters and every consumer. Do NOT run `make check`.
- **Run `scripts/check-fences.py --check` before you report anything closed.**
- Count with `scripts/ledger.py`. Run `scripts/lint-prose.py --check` and
  `scripts/lint-agda.py --check`.
- DD23 freezes mathematical prose. Code and its own comments only.
- **The machine is quiet and both Agda slots are yours.**
- Evidence is `file:line`. Write ASD-STE100.

## RETURN

Write `_build/lj-1.49-report.md` incrementally, skeleton first.

Lead with the verdict: which module parameters survive, and the rates with
their spreads. Then what each cure cost to land. Then the level-hood adequacy
and `ElemDown`: built, priced, or walled with the term you could not write.
Then the DD4 answer and what you are not sure of.
