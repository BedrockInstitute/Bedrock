# LJ-1.368: DD25 review of `[LJ-1.365]`'s SET-MOTIVE refutation

tier: opus (pi-subagent-mode), **the switch's ADVERSARIAL row.**
`[LJ-1.365]` was authored by `pi` / `glm-5.3`, this mode's DEFAULT row, so the
adversarial row is in-harness opus. **DD17's invariant holds: the critic is
not the author.** I ran `scripts/dispatch/dispatch_policy.py` before writing
this line.

## WHY DD25 FIRES, and why this one is worth a maximum-effort read

**`[LJ-1.365]` returned a refutation and it CLOSES A HOPE ON THE GCH CRITICAL
PATH.** **If the refutation is wrong, we have just frozen work that could have
moved, and the freeze is invisible: nobody re-opens a question that has a
green-looking answer.**

**The stakes, stated exactly.** `[LJ-1.332]` ruled that the GCH descent's
mathematics is FINISHED and the sole remaining blocker is ONE untruncation.
`[LJ-1.333]` then measured that untruncation HARD: 「the band is the exact
complement of the only canonicalizer, and five attempts were not unlucky」.
**`[LJ-1.301]` had written an aside claiming the untruncation may be
unnecessary, because the trophy's conclusion is itself truncated and one
`PT.rec` per use would do.** **`[LJ-1.365]` says that aside is refuted in its
premise.** **So the hardest open item on the critical path stays open, on the
strength of one probe that nobody has checked.**

## THE CLAIM, in three separable parts

**1. THE TOP WRAP TYPES.** `wrap-top`,
`agents/tasks/LJ-1-365/ProbeLJ1365A.agda:116-121`, exit 0. **And it claims the
conclusion type is machine-checked rather than transcribed**: `statement-fits`
at `:95-99` applies the delivered `GCHStatement` to the hand-spelled `Concl`.
**Verify that application actually pins the spelling. A hand-spelled type that
merely LOOKS right is the classic way a probe proves the wrong thing.**

**2. THE FIRST DATA GOAL IS A SET, NOT A PROPOSITION.** `SoloC2.agda:24-27`,
**exit 42**, with Agda's own message:

```text
(Σ (⟪ Lset α ⟫ → ⟪ α ⟫) (λ f → (x y : ⟪ Lset α ⟫) → f x ≡ f y → x ≡ y))
  !=< ∥ _A_21 ∥₁
when checking that squash₁ has type isProp (⟪ Lset α ⟫ ↪ ⟪ α ⟫)
```

**and `inj-set` at `ProbeLJ1365A.agda:160-163` re-derives
`isSet (⟪ Lset α ⟫ ↪ ⟪ α ⟫)` green.** **Re-run both.**

**3. THE GOAL IS REALLY ON THE PATH.** It names the supplier as
`stage-card-upper`, `src/L/StageCardinal.lagda.md:564-566`, consumed at
`src/L/BoundedSubset.lagda.md:1513`. **THIS IS THE PART MOST LIKELY TO BE
WRONG AND IT IS THE PART THAT DECIDES THE VERDICT.** **A goal that is a SET
refutes nothing unless the proof MUST pass through it.**

## WHAT TO ATTACK, in priority order

**1. IS THERE ANOTHER ROUTE TO THE CONCLUSION?** **`[LJ-1.365]` showed that
ONE path from the conclusion to the band crosses a SET. It did NOT show that
EVERY path does.** **That gap is the whole review.** **The conclusion is
`∥ Σ[ δ ] ( SuccCardL δ κ × InjL (𝒫 κ) δ × InjL δ (𝒫 κ) ) ∥₁`, and both `InjL`
components are THEMSELVES truncations** (`src/L/GCH.lagda.md:37-38`). **So a
proof that builds the witness `δ` and both codes UNDER the truncation may
never need the ambient injection as data at all.** **Ask whether the SET goal
is forced by the mathematics or by the probe's chosen assembly.** **C-56 is
the law: when a truncated proof walls, the cost is in the ASSEMBLY and not in
the mathematics.**

**2. IS `stage-card-upper` THE ONLY SUPPLIER?** **Re-derive its consumer at
`BoundedSubset.lagda.md:1513` and ask whether a coded supplier exists that
never leaves the truncation.** **`[LJ-1.337]` measured `sq-below` with an
EMPTY consumer diff, which means the delivered path is more flexible than it
looks.**

**3. C-54, WHICH THE PROBE INVOKED BUT MAY NOT HAVE APPLIED.** The law says a
SET-motive stall is a **`2-Constant` obligation** before it is a principle.
**`PT.rec` is not the only eliminator: `PT.rec2`, `PT.elim` at a family, and
the `2-Constant` route through `Cubical.HITs.PropositionalTruncation` all
exist.** **Did `[LJ-1.365]` try any of them, or only `PT.rec` with
`squash₁`?** **If it tried only the one, its「the body cannot exist」is
`PT.rec` failing, not the body failing, and the verdict is too strong.**

**4. THE STALE CITATION IT CORRECTED.** It reports the conclusion at
`src/L/GCH.lagda.md:65-68` against `[LJ-1.301]`'s `:85-87`. **Verify the
correction; a probe that re-spelled a type from the wrong lines proves nothing
about the right ones.**

## THE ABORT CRITERION (D-1)

- **UPHOLD.** **Then the untruncation is genuinely required and `[LJ-1.333]`'s
  five failures are the real cost of the critical path.** Say so, and the
  question closes for good.
- **OVERTURN.** **Most likely at attack 1 or 3: another eliminator, or a route
  that never leaves the truncation.** **That would re-open the cheapest
  possible cure for the GCH descent and it is the valuable outcome.**
- **SPLIT.** **Likeliest shape: the SET goal is real on the probe's assembly
  and NOT forced by the mathematics.** **Then the verdict word is wrong even
  though every measurement in the report is right.** **Say exactly that.**
- **A WALL.** **C-58: replace a numeral pattern-match split with the library
  eliminator before bisecting the mathematics.**

## CONSTRAINTS

- **LAND NOTHING, REPAIR NOTHING.** Write only in `agents/tasks/LJ-1-368/`.
  **`src/` is forbidden** (I-5).
- **You MAY copy and modify `[LJ-1.365]`'s probes into your own directory.**
  **Do not edit `agents/tasks/LJ-1-365/`.**
- **`agents/tasks/LJ-1-344/Supply344.agda`,
  `agents/tasks/LJ-1-350/MustFail350.agda` and
  `agents/tasks/LJ-1-348/MustFail348.agda` are EXPECTED RED. Repair none.**
  **`[LJ-1.365]`'s `SoloC2.agda` is EXPECTED RED at exit 42 and is its
  evidence; do not repair it either.**
- **A full-tree `make check` may be running.** **Do not run `make check`.**
- **COUNT THE AGDA SLOTS** before every invocation, exactly:
  `ps aux | awk '/libexec.*bin\/agda/ && !/awk/' | wc -l`. **Both obvious
  alternatives OVER-COUNT, MEASURED.** **The cap is TWO.**
- **ONE agda process, `GHCRTS="-A64m -I0 -M8g"`, cap NEVER raised.** **Report
  the empty-file floor beside any seconds figure** (C-53 as extended).
- **Never commit, never push**, never `git checkout .`, `git stash`,
  `git reset --hard` or `git clean`.
- **Create `agents/tasks/LJ-1-368/lj-1.368-report.md` in your FIRST five
  minutes** (C-22).
- Run `.venv/bin/python scripts/gate/lint-prose.py --check` and
  `lint-agda.py --check`. **No em dash.** ASD-STE100. Evidence is `file:line`.
  Mark every negative **MEASURED** or **INFERRED**.

## THE VERDICT WORD

**UPHOLD, OVERTURN or SPLIT**, the first word of your return. **13 of 33
decided DD25 reviews here have overturned, 39 percent. An overturn is the
valuable outcome and you are not rewarded for agreeing.**

## THE PREMISE OF MINE MOST LIKELY TO BE WRONG

**I WROTE `[LJ-1.365]`'s BRIEF AND I TOLD IT TO EXPECT TO REFUTE ME.** **It
did, and I accepted the refutation within minutes because it came with an exit
42 and Agda's own message.** **An exit 42 proves that ONE term does not type.
It does not prove that no term does.** **C-45's shape exactly: `exit 0` is not
a supply, and the mirror holds, exit 42 is not an impossibility.** **Treat my
acceptance as evidence of nothing.**

## THE RULES

**C-54 is the law the target invoked; read its FULL entry and check whether
the target APPLIED it or only cited it.** **C-56: a truncated proof's wall is
in the assembly.** **C-45 and its mirror.** **C-44, C-57, D-10, C-42, C-53,
C-58, P-l, P-k.** **C-12, C-22, C-32, C-36, C-39, C-40.** I-5. **D-1, D-26.**
**DD0, DD4, DD17, DD18, DD23, DD24, DD25.**

Run `.venv/bin/python scripts/dispatch/rules.py --for review` and read every
statement, opening the full entry for any law you act on.

## DD4

**Maximize the code the two proofs share, and write it generic.** One rule,
two ends, no metric and no checker. **NAME YOUR AXIS** (C-46), fixed at
`scripts/measure/ledger.py:50`.

**The `sq` chain has been class-free throughout and `[LJ-1.337]`'s `sq-below`
has an EMPTY consumer diff, the strongest DD4 shape this chain has
produced.** **If a route exists that keeps everything under the truncation, it
is also the route that preserves that shape. Say whether the target's
assembly gave that up unnecessarily.**

## ARCHIVE (DD18)

**A live `agents/tasks/` path is NOT an archive citation, and
`scripts/gate/check-dd18-survey.py` now GATES your return: name each of the
four corpora, cited or declined in ONE line, and QUOTE one line per archived
file you read, at its real line number.**

- **`archive/src/2026-08-09-rud-route/`**: **did the retired route ever
  consume a truncated square law, and with which eliminator?** **A delivered
  answer settles attack 3 in an hour. Grep for `PT.rec`, `rec2` and `elim`
  near its square-law work.**
- **`archive/dev/JOURNAL-archived.md`**: the retired route's truncation
  episodes. **WHY NOT in one line if nothing bears.**
- **`archive/dev/DECISIONS-archived.md`**: any ruling on truncation policy.
  **WHY NOT in one line if none.**
- **`archive/dev/TASKS-archived.md`**: the retired square-law dispatches,
  taking SHAPE and never a claim.

## LITERATURE (DD18)

**`dev/literature/truncation-and-selection.md`**, written for this exact
class. **Say in ONE line whether it names an eliminator the target did not
try.** Return a **LITERATURE USED** section.

## SCOPE (read)

`agents/tasks/LJ-1-365/ProbeLJ1365A.agda` WHOLE and `SoloC2.agda` WHOLE,
FIRST, and RE-RUN both. Then `dev/LESSONS.md`'s C-54 entry in full.

## SCOPE (write)

`agents/tasks/LJ-1-368/` only.

## RETURN

**Lead with ONE word: UPHOLD, OVERTURN or SPLIT.** Then whether EVERY path to
the conclusion crosses a SET, or only the probe's. Then which eliminators were
tried and which were not. Then whether `stage-card-upper` is the only
supplier. Then the three measurements re-run, with your own exit codes. Then
what `[LJ-1.332]`'s untruncation is worth after your verdict. **Mark every
negative MEASURED or INFERRED.**
