# LJ-1.93: be the first consumer of the three split masters

tier: codex (default)

## GOAL

**Discharge `twelve-out` and `twelve-back` from `TwelveAgree`.** They are
hypotheses of the consumer today. The composer exists to supply them. Nothing
has ever joined the two.

## CWD

`/Users/alsg/Agentic/Bedrock`, on branch `two-tower-bridge`, **clean at
`a1f0e95`**. HEAD is green. **A sibling agent holds the other Agda slot.**

## WHAT I VERIFIED MYSELF, in the source, just now

**The three split masters have NO consumer.** `L.Condensation.LowerAgree`,
`UpperAgree` and `TwelveAgree` appear in `src/` only in
`src/Everything.lagda.md:371-373` and inside each other
(`src/L/Condensation/TwelveAgree.lagda.md:31,33`). **C-35 says a delivered
block with no consumer is UNTESTED. These three are that.**

**The consumer states the join as two hypotheses**, at
`src/L/Condensation.lagda.md:6486-6491`, and again at `:6729-6734`:

```agda
(twelve-out : (d e f : S) → ⟨ (f ∷ e ∷ d ∷ γ) ⊨ twelveAt (suc (suc zero)) (suc zero) zero ⟩
            → ⟨ (f ∷ e ∷ d ∷ γ) ⊨ SatGraphB.twelveB {n} w K N0 N1 N2 N3 N4 N5
                                        N6 N7 N8 N9 N10 N11 t0 t1 ⟩)
(twelve-back : ... the other direction ...)
```

**The composer proves the same two directions against a DIFFERENT formula.**
`src/L/Condensation/TwelveAgree.lagda.md:270-271`:

```agda
twelveB = p0b ∧̇ p1b
```

with `p0b = LowerAgree.sixB ...` (`:248-257`) and `p1b = UpperAgree.sixB ...`
(`:259-268`), and `out` at `:273` and `back` at `:294`.

**The two formulas are associated differently, and I checked both shapes.**
`LowerAgree.sixB` (`src/L/Condensation/LowerAgree.lagda.md:226-260`) is a
self-contained right-nested chain of six, so `p0b ∧̇ p1b` puts a conjunction
on the LEFT of the outer `∧̇`. The consumer's `SatGraphB.twelveB`
(`src/L/Condensation.lagda.md:2233-2254`) is **one right-nested chain of
twelve**, so its outer `∧̇` has `memBndAt ...` on the left.

## WHAT TO DO

**Supply the two hypotheses.** Two obligations, and the second is probably the
larger one:

1. **The association bridge.** `p0b ∧̇ p1b` and `SatGraphB.twelveB` must be
   shown to have equivalent satisfaction, in both directions, at the
   consumer's environment. **First check whether the twelve conjuncts are
   literally the same formulas on both sides**, index for index, and say so
   at `file:line`. If one conjunct differs, that is the finding and it is
   more important than the association.
2. **The hypothesis pack.** `TwelveAgree` carries a long telescope
   (`tagEq0` to `tagEq11`, `numK0` to `numK11`, the closure family, and the
   `consK` group). The consumer holds a **`KFacts` record**
   (`src/L/Condensation.lagda.md:6479-6485`, defined at `:5675-5708`).
   **Say for EACH of the composer's hypotheses whether `KFacts` supplies it,
   the consumer's other parameters supply it, or nothing supplies it.**

**C-38: a hypothesis is discharged when something SUPPLIES it, never when it
is restated.** Do not report a discharge from a count of parameters. **That
error has been made four times this phase, twice by me.**

## THE ABORT CRITERION, fixed in advance per D-1

- **Both hypotheses are supplied**: report the terms at `file:line` with
  their seconds, and STOP. Do not go on to `levelIn` or `cover`.
- **Something cannot be supplied**: STOP, write the term you could not write,
  and name what must provide it.
- **A conjunct differs between the two formulas**: STOP and report which one.
  **That would mean the split masters prove a statement about a formula no
  consumer uses, and it is a route-level finding.**
- **Anything walls**: STOP, report the wall with its seconds.

**Work in `src/ProbeLJ193*.agda` first.** Only after a probe is green may you
write into a master, and then a master is GREEN when you finish or you revert
it. `[LJ-1.72]` and `[LJ-1.80]` each left one broken and each cost a revert.

## C-12, AND THIS IS NOT BOILERPLATE

`[LJ-1.80]` left **SIX agda processes alive at once**, all children of one
wrapper, all on the same probe, none killed. Each carried `-M8g`: 48 GB of
worst case on a 64 GB machine at load 19. **The owner caught it; no tool
did.**

**ONE agda process at a time, and a sibling agent holds the other slot. If a
check does not return, KILL IT before you start another, and report the wall
with its seconds.**

## WHAT YOU MUST NOT DO

- **Do not change `SatGraphB.twelveB`.** The consumer's formula is fixed by
  the machine side.
- **Do not add a hypothesis to the consumer to make the join go through.** A
  site that assumes what it should supply has moved the obligation.
- **Do not touch anything under `src/L/Coding/` or `src/V/`.**
- **Never `src/Everything.lagda.md`.**
- **Do not raise the heap cap.** C-12.
- **Read line numbers and counts from the source, never from a report**, and
  say where a module ends if you report a count.

## THE CLASSIFICATION I WANT ON EVERY NEGATIVE

State for every negative whether its deciding claim is **MEASURED** or
**INFERRED**, in those words. **A negative that rests on an inference sets no
verdict.**

## DD4

**Maximize the code the two proofs share, and write it generic.** One rule,
two ends, no metric and no checker, so it is stated in every brief and
answered in every return.

**An association bridge is pure logic and should be generic in the
conjuncts.** Say whether you wrote it that way, and whether the J tower gets
it unchanged.

## THE COST QUESTION

The wing is over DD24 and the owner ruled the threshold question is settled
when the phase's content is complete. **So measure, do not gate.** Report the
in-fence lines you added and the cold seconds of every master you touched,
with the load average.

## ARCHIVE (DD18)

- **`_build/lj-1.76-report.md`**, read WHOLE. It built the three masters and
  it is the record of why the composer chose `p0b ∧̇ p1b`.
- `_build/lj-1.79-report.md`, the `KFacts` repair, and `_build/lj-1.77-report.md`,
  which machine-checked the old `KFacts` uninhabitable.
- `src/L/Condensation.lagda.md:2227-2385`, the whole `SatGraphB` module.
- `src/L/Condensation.lagda.md:5675-5708`, the `KFacts` record. **29 fields;
  count them yourself and say where the record ends.**
- `dev/LESSONS.md` **C-38 as extended**, C-35, C-36, D-30, P-w, read WHOLE.
- `archive/rud-route/` for SHAPE only.

Return an **ARCHIVE USED** section at `file:line`.

## LITERATURE (DD18)

**Banked. Spend nothing.** This is a wiring task inside our own encoding and
no source speaks to it. Say so in one line.

## SCOPE (read)

`src/L/Condensation.lagda.md:6470-6500` FIRST, then
`src/L/Condensation.lagda.md:2227-2260`, then
`src/L/Condensation/TwelveAgree.lagda.md:240-318`.

## SCOPE (write)

`src/ProbeLJ193*.agda`; `src/L/Condensation/TwelveAgree.lagda.md` and
`src/L/Condensation.lagda.md` **only if they are green when you finish, or
reverted**. Your report is `_build/lj-1.93-report.md`. **Never
`src/Everything.lagda.md`.**

## MANDATORY RULES FOR A BUILD

Run `python3 scripts/rules.py --for build` and read every statement.

- **C-38 as extended.** A hypothesis is discharged when something SUPPLIES
  it. **This dispatch is the supply site.**
- **C-35.** A block with no consumer is UNTESTED. **You are its first
  consumer.**
- **C-36.** Write the term you could not write.
- **D-30.** Price what the CONSUMER needs.
- **P-w.** A module application COPIES, and the copy is paid at USE.
- **P-h.** Module-parameterized, never function-parameterized.
- **P-i.** The conversion-explosion playbook. **Read it whole; heavy
  hypothesis packs go as module Pi-parameters, never as records.**
- **P-k, P-l, P-m, P-n, P-o, P-q, P-t, P-u, P-v** as the bundle gives them.
- **P-c, R-36, R-38.** Seal at the birth site; expose with a read lemma.
- **R-35, R-40.** State the membership SHALLOW and climb.
- **I-5.** The inference trap this tree has paid for.
- **C-12.** ONE agda process, cap never raised, **kill a hung check before
  starting another.**
- **C-22.** Write the deliverable incrementally.
- **C-31, C-32, C-33, C-34, C-37.**
- **D-1, D-8, D-10, D-26, D-29.**

## CONSTRAINTS

- Never commit, never push, never `git checkout .`, `git stash`,
  `git reset --hard` or `git clean`.
- Typecheck what you touch. Do NOT run `make check`.
- **Run `scripts/check-fences.py --check` before you report anything closed**
  and say the master count.
- Count with `scripts/ledger.py`. Run `scripts/lint-prose.py --check` and
  `scripts/lint-agda.py --check`.
- DD23 freezes mathematical prose.
- **Report the load average beside every absolute figure.**
- Evidence is `file:line`. Write ASD-STE100.

## RETURN

Write `_build/lj-1.93-report.md` incrementally, skeleton first.

**Lead with whether the twelve conjuncts are the same formulas on both
sides**, at `file:line`. Then whether `twelve-out` and `twelve-back` are
supplied, with the terms and their seconds. Then the per-hypothesis table:
what supplies each of the composer's hypotheses. **Mark every negative
MEASURED or INFERRED.** Then the lines added and the cold seconds. Then the
DD4 answer. Confirm every master is green or untouched.
