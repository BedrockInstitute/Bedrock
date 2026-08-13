# LJ-1.42: add the missing conjunct, close the nine rows, and price `PropAgree`

tier: codex (default)

## GOAL

`[LJ-1.41-R]` refuted a stated impossibility with four probes and located the
real defect: **one missing conjunct**. Land the cure, close the nine rows, and
measure the one thing that is now the widest unmeasured term.

## CWD

`/Users/alsg/Agentic/Bedrock`, on branch `two-tower-bridge`.

## THE INSTRUCTION THAT WAS MISSING FROM MY LAST BRIEF, and it cost a dispatch

**Do NOT weaken a statement to make it close. You MAY and often MUST
STRENGTHEN one**, provided the stronger form is still true and still
Δ₀-compatible. **`dev/LESSONS.md` C-36 was admitted today because my last brief
gave only the first half**, and the cure here is a strengthening.

**And C-36's other half: a failed substitution is NOT a proof of
impossibility.** An Agda type error says two types differ; it never says no
term connects them. `[LJ-1.41]` declared a Δ₀ impossibility from a bare
identity coercion whose error already showed the missing conjunct's shape.
**If you find yourself reporting that something cannot exist, write the term
you think cannot exist, or name the constructor that is missing and show
nothing supplies it.**

## THE DEFECT AND ITS CURE, machine-checked and re-run by me

**The machine's `extAt` is a PAIR of implications. The story wrote the first
and stopped.** That single missing conjunct blocks nine rows.

Four probes settle it, and I re-ran all four:

- **`src/ProbeDD25F41A.agda`, GREEN, 1.45 s.** The "impossible" Δ₀ witness in
  ONE line from the delivered `Δ₀-extAtB` and `Δ₀-envBndGen`. **The unbounded
  `envSetAt` witness is never needed**: every leaf is a K-bounded Δ₀
  restatement transferred under site facts.
- **`src/ProbeDD25F41B.agda`, GREEN, 1.67 s, 98 lines, marginal 0.22 s.**
  BOTH directions between the bounded condition and `envSetAt`, from delivered
  machinery plus three site facts. **This is your route.**
- **`src/ProbeDD25F41C.agda`, GREEN.** `envHypT` is definitionally conjunct one
  of the cure, **so the delivered environment layer does NOT need re-laying.**
- **`src/ProbeDD25F41D.agda`, RED by design.** The delivered condition plus ALL
  three site facts, still refused. **The conjunct is what is missing, not the
  facts.**

## WHAT TO DELIVER

1. **The missing conjunct**, as `[LJ-1.41-R]` built it: about 100 lines,
   about 0.22 s marginal.
2. **The nine row agreements**: Top, Neg, Forall, Exist, Mem, Eq, Imp, AllIn,
   ExIn. And and Or are already closed (`AndAgree`, `OrAgree`).
3. **BLOCK 1'S IDENTICAL DEFECT.** `Clause.envHyp` is ONE conjunct where
   `existClauseAt` wants TWO. **It has been there since `[LJ-1.5]`**, whose own
   report recorded the symptom as "the matrix-to-clause link is unproven" and
   nobody read it as this. **Fix it and close block 1's agreement too.**

## THE MEASUREMENT THAT DECIDES THE NEXT BLOCK, and it is not optional

`[LJ-1.41-R]` found a warning the return under-priced:

| what | rate |
|---|---:|
| `[LJ-1.41]`'s block, 11.30 s over 307 lines | **0.0368 s/line** |
| the review's env machinery | **0.0025 s/line** |
| DD24's bar | 0.013193 |

**Nine more rows at 0.0368 project about 0.0175 s/line, a DD24 breach by about
a third.** The env machinery is **15x cheaper**, so the cost is inside
`PropAgree`, not in the environment layer.

**So measure what inside `PropAgree` costs 0.037 s per line, and report it.**
**P-v names the suspect**: a satisfaction-level conversion between two
spellings of one formula costs seconds where the formula-level identity is
free, measured at 59 ms against 29,415 ms. **If `PropAgree` carries such a
conversion, fix it and report the delta.** C-34: build the cure or report the
wall.

## THE OPEN RISK `[LJ-1.41-R]` NAMED, so you check it rather than inherit it

**`envInK`**, that every environment over `ar` with values in `B` lies in K, is
needed **only for the machine-to-story leg**. It holds when the arity is a
numeral and K is a limit level. **The review did NOT verify that the row forces
the arity to be a numeral. Check that, and if it does not, say so plainly**:
that would make the cure conditional and the condition would need its own
price.

## WHAT IS SETTLED, so you do not re-open it

- **Δ₀ IS the target.** Delivered `Σ₁`'s only base is `σ-Δ₀`
  (`src/FOL/LevyHierarchy.lagda.md:73-75`). The Σ₁ certificate buys exactly one
  outer `∃` over K.
- **The environment condition IS an object-language antecedent inside all four
  row frames**, so the Δ₀ certificate must cover it. **And it can.** The
  orchestrator's own proposed escape, that the condition could be an
  Agda-level hypothesis, was tested and FAILS. Do not retry it.
- **The delivered environment layer stands.** `envHypT`, `envHypU`, `envHypB2`
  and `envHypB2T` are conjunct one, not wrong.
- **The nonemptiness cure is dead** (`[LJ-1.38-R]`).
- **P-u**: certify BEFORE you place. The master has ZERO placement and that is
  load-bearing; the wall is flat at 8 GB.
- `[LJ-1.41]`'s two repaired shared leaves, `subValSuccB` and `bndBodyAll`, are
  GREEN and correct. **Do not revisit them.**

## DD4, WHICH GOES IN EVERY BRIEF

**Maximize the code the two proofs share, and write it generic.** One rule,
two ends. It has NO metric and no checker by the owner's ruling, so it is
stated in every brief and answered in every return; the repetition is its only
enforcement.

**D-29, admitted from this same file: a shared layer propagates a FIX and a
DEFECT at the same rate.** The missing conjunct is in the shared layer, so
**one cure should close nine rows**. `[LJ-1.41]` showed the saving side works:
And and Or are one module instantiated twice with nothing row-specific.

**Report how many rows needed anything beyond the shared cure.** That is this
block's DD4 evidence.

**And D-29's other face still binds: audit the shared cure against the machine
BEFORE instantiating it nine times.** `[LJ-1.41]` did this and caught two real
defects; do the same.

## THE THRESHOLD

DD24 gates at **0.013193 s per line**, module caliber. The master is at
**0.00512** overall but this block's marginal content ran **0.0368**. **Report
the marginal rate for what YOU add, not only the whole-file rate**, and report
the module-load cone separately. **C-31: the per-module flag is ADVICE; the
aggregate is the judgment.**

## LITERATURE (DD18)

- `dev/literature/devlin-II5.md`, Step C. **Devlin asserts absoluteness where
  this block proves a decode.** Say so in one line and spend nothing more.
- The errata do NOT cover Chapter II section 5. `[LJ-1.14]` verified it. **Do
  not re-check it.**

Return a **LITERATURE USED** section, with WHY NOT for anything skipped.

## ARCHIVE (DD18)

**Read these WHOLE. C-32 exists because a brief of mine named a SECTION and hid
the decisive probe.**

- **`_build/lj-1.41-review.md`**, the refutation, the cure and the rate warning.
- **`src/ProbeDD25F41A.agda`, `B`, `C` and `D`.** B is your route; D is the RED
  control.
- **`_build/lj-1.41-report.md`**, the two closed rows and the audit that caught
  two shared-leaf defects.
- `src/L/Condensation.lagda.md`, especially `AndAgree` and `OrAgree` and the
  shared `PropAgree`.
- `_build/lj-1.5-report.md`, **whose "matrix-to-clause link is unproven" was
  this same defect and went unread.**
- `dev/LESSONS.md` is NOT archived and still binds. **C-35, C-36 and D-29 were
  all admitted from this one file.**

Return an **ARCHIVE USED** section at `file:line`.

## MANDATORY RULES FOR A BUILD

From `python3 scripts/rules.py --for build`. Run it and read each statement.

- **P-h.** Module-parameterized, never function-parameterized.
- **P-k.** A read lemma is stated where its consumers use it.
- **P-l, P-m, P-n, P-t, P-u, P-v** as above. **P-v is the named suspect for the
  0.037 rate.**
- **R-35, R-38**: sealing and opacity. **Do not unseal.**
- **R-40**: state a membership witness SHALLOW and climb.
- **I-5**: the inference trap this tree has paid for.
- **C-12.** `GHCRTS="-A64m -I0 -M8g" agda <file>`, ONE process. A heap
  exhaustion is a WALL with its seconds; never raise the cap.
- **C-22.** Write the deliverable incrementally.
- **C-31, C-32, C-33.**
- **C-34.** Build the cure or report the wall.
- **C-35.** No consumer, no DELIVERED.
- **C-36.** A failed substitution is not a proof of impossibility. **You may
  strengthen.**
- **D-29.** Audit the shared cure before instantiating it nine times.
- **D-10.** Every figure here is a residue. Re-verify.

## SCOPE (read)

`_build/lj-1.41-review.md` FIRST, then `src/ProbeDD25F41B.agda`, then
`src/L/Condensation.lagda.md`'s `PropAgree`, `AndAgree` and `Clause.envHyp`.

## SCOPE (write)

`src/L/Condensation.lagda.md`, plus `src/ProbeLJ142*.agda` if you need them.
Your report is `_build/lj-1.42-report.md`. **No other master. Never
`src/Everything.lagda.md`.**

## CONSTRAINTS

- **Never commit and never push.**
- **Never `git checkout .`, `git stash`, `git reset --hard` or `git clean`.**
  **`[LJ-1.41]`'s work is uncommitted in the file you are editing.**
- **Typecheck the master AND every consumer.** Do NOT run `make check`.
- **Count with `python3 scripts/ledger.py`'s caliber.** DD26 excludes the two
  catalogs.
- **Report cold seconds and BOTH rates**, whole-file and marginal, with the
  cone separately.
- **Run `python3 scripts/lint-prose.py --check` and `python3
  scripts/lint-agda.py --check`.**
- **DD23 freezes mathematical prose.** Code and its own comments only.
- **The machine is quiet and both Agda slots are yours.**
- **Evidence is `file:line`.**
- **A refusal with a measurement is a SUCCESS**, but **an impossibility claim
  needs the term you could not write** (C-36).
- Write ASD-STE100 in the report.

## RETURN

Write `_build/lj-1.42-report.md` INCREMENTALLY, skeleton first.

1. **THE VERDICT**, first line: how many of the nine closed, block 1's state,
   and both rates.
2. **DID THE MISSING CONJUNCT CLOSE THEM?**
3. **BLOCK 1**: fixed and closed, or what it owes.
4. **WHAT INSIDE `PropAgree` COSTS 0.037 s/line?** Measured, with the cure if
   you found one.
5. **DOES THE ROW FORCE THE ARITY TO BE A NUMERAL?** (`envInK`'s condition.)
6. **HOW MANY ROWS NEEDED ANYTHING BEYOND THE SHARED CURE?** (DD4, D-29.)
7. **THE NUMBER**: in-fence lines, before and after.
8. **SECONDS AND RATES**, whole-file and marginal, cone separately.
9. **DID YOU NEED A PLACEMENT ANYWHERE?**
10. **LITERATURE USED.** 11. **ARCHIVE USED.** 12. **WHAT I AM NOT SURE OF.**
