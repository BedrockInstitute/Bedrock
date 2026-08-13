# LJ-1.114: thread the truncation from StageCardinal to Devlin55

tier: codex (default)

## GOAL

**Cash the truncated square law.** `∥ sq α ∥₁` is proved at every infinite
ordinal. `Devlin55` takes the untruncated `sq`. **Thread the truncation
down so the theorem can use what is proved.**

## CWD

`/Users/alsg/Agentic/Bedrock`, on branch `two-tower-bridge`, **clean at
`126773f`. `make check` passes.** A sibling agent works inside
`src/L/Condensation*` and its probes. **Do not touch `src/L/Condensation*`.**

## WHAT IS MEASURED, and I re-ran the decisive check myself

`[LJ-1.111]` answered all three questions.

**The cheapest cure is NO, measured.** The least witness's uniqueness does
not make the fiber a proposition: extracting `⟪ α ⟫ ↪ ⟪ κ ⟫` from the
truncated `κ-eqα` is refused with `Type _ !=< x ≡ y`, **with the leastness in
scope** (`src/ProbeLJ1111B.agda:46`). The leastness constrains the ordinal,
never the bijection type.

**The truncation-at-top route CLOSES.**

```agda
TruncatedChain.theorem : (α : S) → IsOrd α → (⟨ α ∈ˢ ω ⟩ → Empty.⊥)
                       → ∥ SQ.sq α ∥₁
```

`src/ProbeLJ1111A.agda:236-237` and `:271-272`, by `∈-induction`, where `SQ`
is the master `L.Ordinal.SquareLaw`. **GREEN: I re-ran it, exit 0**, 250
non-blank lines, about 20.9 s cold. **No choice.**

**The threading is priced at about 350 non-blank in-fence lines**, module
extents MEASURED and the lift pattern INFERRED at 5 to 8 lines per module.
**Every type between `Bound`'s pairing and the conclusion is data; the
truncation eliminates only at the proposition points `β∈κ` and `x∈Lκ`.**

## WHAT TO BUILD

**Change `sq` to `∥ sq α ∥₁` at `L.StageCardinal`'s parameter
(`src/L/StageCardinal.lagda.md:15`) and at `Devlin55`'s
(`src/L/BoundedSubset.lagda.md:1362-1363`), and carry the truncation to the
proposition points.**

1. **Follow `[LJ-1.111]` sections 2 and 4**, which name the modules and the
   two elimination points. **Verify each in the source.**
2. **`Devlin55` already eliminates a truncation against its conclusion**:
   `src/L/BoundedSubset.lagda.md:1606` reads
   `x∈Lκ = PT.rec (snd (x ∈ˢ Lset κ)) go (cover x x∈M)`. **That is the
   pattern.**
3. **Then supply it.** With the parameter truncated,
   `src/ProbeLJ1111A.agda`'s theorem is the value. **Say whether `Devlin55`
   can now be entered, and if not, what else it still wants.**

## C-40, AND IT IS THE RULE I BROKE THIS MORNING

**A master's own check answers "does this file still elaborate", never "does
anything that uses it still elaborate".** I changed every row telescope in
`Condensation`, checked that master three times, committed three times, and
left the tree RED all three times.

**So: after you change `StageCardinal`'s or `BoundedSubset`'s parameter,
check every master that imports them, and say which ones you checked, at
`file:line`.** `git grep -l "StageCardinal\|BoundedSubset" src/` is the list.
**Do NOT run `make check`; I run it. But name the consumers you checked.**

## THE RULE ON HYPOTHESES, stated as a test and not as a shape

**Do not weaken a conclusion to make the truncation fit.** If a conclusion
must become truncated, **say which one and why, and say whether the
theorem's final statement changes.** **The theorem's final statement must
not change.**

**Run `scripts/check-unbound-hyp.py` on anything you write** and report what
it says.

## THE ABORT CRITERION

- **The threading lands and every consumer is green**: report the diff, the
  cold seconds of each master you touched, the consumers you checked, and
  STOP.
- **A module cannot carry the truncation because its output is data all the
  way to the top**: STOP, name the module and the type, and say what the
  theorem would have to state instead. **That would be a route-level
  finding.**
- **Anything walls**: STOP, report the wall with its seconds. **`BoundedSubset`
  measured about 15 s and `Condensation` about 150 s; `StageCardinal` is
  unmeasured by me. Report what you find.**

**Do not stop at the first negative. If one consumer breaks, say how many.**

**Every master you touch is GREEN when you finish, or you revert all of them
and say so.**

## C-12, AND THIS IS NOT BOILERPLATE

`[LJ-1.80]` left **SIX agda processes alive at once**, all children of one
wrapper, all on the same probe, none killed. Each carried `-M8g`: 48 GB of
worst case on a 64 GB machine at load 19. **The owner caught it; no tool
did.**

**ONE agda process at a time, and a sibling agent holds the other slot. If a
check does not return, KILL IT before you start another, and report the wall
with its seconds.**

## WHAT YOU MUST NOT DO

- **Do not assume the axiom of choice.** Six dispatches have measured this
  chain choice-free, and choice would make the whole truncation question
  vanish for the wrong reason.
- **Do not change any theorem's final statement.**
- **Do not touch `src/L/Condensation*`**, where a sibling works.
- **Do not touch `src/L/Coding/` or `src/V/`.**
- **Never `src/Everything.lagda.md`.**
- **Do not raise the heap cap.** C-12.
- **Read line numbers from the source, never from a report.**

## THE CLASSIFICATION I WANT ON EVERY NEGATIVE

State for every negative whether its deciding claim is **MEASURED** or
**INFERRED**, in those words. **A negative that rests on an inference sets no
verdict.**

## DD4

**Maximize the code the two proofs share, and write it generic.** One rule,
two ends, no metric and no checker, so it is stated in every brief and
answered in every return.

**The square law is about ordinals and injections, never about
definability**, so this is shared content. **Say whether the truncated
parameter changes that, and whether the J tower gets the threaded modules
unchanged.**

## THE COST QUESTION

The wing is over DD24 and the owner ruled the threshold question is settled
when the phase's content is complete. **So measure, do not gate.** Report
each touched master's cold seconds before and after, and the non-blank
in-fence lines, with the load average. **Report your run-to-run spread
before you claim a delta: two returns this session claimed deltas smaller
than the noise, and both said so honestly.**

## ARCHIVE (DD18)

- **`_build/lj-1.111-report.md`**, read WHOLE, and **`src/ProbeLJ1111A.agda`**
  and `src/ProbeLJ1111B.agda`, read WHOLE. **The proved truncated chain, the
  refused extraction, and the threading plan with its two elimination
  points.**
- `_build/lj-1.107-report.md`, the wall this route goes around.
- `_build/lj-1.106-report.md` and `src/ProbeLJ1106A.agda`, `Init` and `sq`
  at the Hartogs cardinal.
- **`src/L/StageCardinal.lagda.md`**, the whole file: it takes `sq` at
  `:15` and consumes it at `:281`.
- **`src/L/BoundedSubset.lagda.md:1361-1627`**, `Devlin55` whole, and
  `:1606` for the elimination pattern it already uses.
- `src/L/Ordinal/SquareLaw.lagda.md:938-964`, `via-col-square` and
  `via-col-truncated`.
- `dev/LESSONS.md` **C-40, C-39, C-38 as extended, P-x**, C-35, C-36, D-8,
  D-30, P-l, read WHOLE.

Return an **ARCHIVE USED** section at `file:line`.

## LITERATURE (DD18)

**Banked. Spend nothing.** `[LJ-1.111]` settled how Devlin uses the square
law. Say so in one line.

## SCOPE (read)

`src/ProbeLJ1111A.agda` FIRST, then `src/L/StageCardinal.lagda.md:1-30` and
`:270-300`, then `src/L/BoundedSubset.lagda.md:1361-1370` and `:1595-1615`.

## SCOPE (write)

`src/L/StageCardinal.lagda.md`, `src/L/BoundedSubset.lagda.md` and any
master their change forces (**all green at the end, or all reverted**), plus
`src/ProbeLJ1114*.agda`. Your report is `_build/lj-1.114-report.md`.
**Never `src/Everything.lagda.md`. Never `src/L/Condensation*`.**

## MANDATORY RULES FOR A BUILD

Run `python3 scripts/rules.py --for build` and `--for rewrite`, and read
every statement.

- **C-40.** Verify the CONSUMERS of a changed master, never the master
  alone. **This is the rule the orchestrator broke this morning and it cost
  three red commits.**
- **C-39.** A brief's prohibition binds harder than its goal. **If a line of
  this brief blocks a route you can see, say so in the report and name the
  route. That is a required section, not a courtesy.**
- **C-38 as extended, C-35, C-36, D-29, D-30, D-10.**
- **P-x.** A transparent construction in a record field type is paid by
  every elaboration of the record.
- **P-l.** A price from a comparable elsewhere is a hypothesis. **The 350
  line figure is part MEASURED, part INFERRED; say which half you hit.**
- **P-i, P-w, P-h, P-k, P-m, P-n, P-o, P-q, P-t, P-u, P-v** as the bundle
  gives them.
- **P-c, R-36, R-38, R-35, R-40.**
- **I-5.** The inference trap this tree has paid for.
- **C-12.** ONE agda process, cap never raised.
- **C-22.** Write the deliverable incrementally.
- **C-31, C-32, C-33, C-34, C-37.**
- **D-1, D-8, D-26.**

## CONSTRAINTS

- Never commit, never push, never `git checkout .`, `git stash`,
  `git reset --hard` or `git clean`.
- Do NOT run `make check`. **I run it, and I will run it on your result.**
- **Run `scripts/check-fences.py --check`** and say the master count.
- Count with `scripts/ledger.py`. Run `scripts/lint-prose.py --check` and
  `scripts/lint-agda.py --check` on anything you touch.
- DD23 freezes mathematical prose. **Change the code, not the prose, unless
  a sentence becomes false. If one does, say which and leave it.**
- **Report the load average beside every absolute figure.**
- Evidence is `file:line`. Write ASD-STE100.

## RETURN

Write `_build/lj-1.114-report.md` incrementally, skeleton first.

**Lead with whether the threading landed and whether `Devlin55` can now be
entered.** Then the diff and each touched master's cold seconds before and
after, with your run-to-run spread. **Then the C-40 section: every consumer
you checked, at `file:line`, and its result.** Then whether any theorem's
final statement changed. Then the C-39 section. **Mark every negative
MEASURED or INFERRED.** Then the DD4 answer.
