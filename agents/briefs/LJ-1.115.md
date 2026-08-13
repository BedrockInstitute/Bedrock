# LJ-1.115: probe someEnv, the K-closure family's widest term

tier: codex (default)

## GOAL

**Gate the K-closure family before funding it.** Twenty eight of the
consumer's twenty nine facts need new content, and twenty five of them are
one pattern. **One of them is not, and it is the one that must be measured
first.**

## CWD

`/Users/alsg/Agentic/Bedrock`, on branch `two-tower-bridge`, **clean at
`b15ff83`. `make check` passes.** A sibling agent works in
`src/L/StageCardinal.lagda.md` and `src/L/BoundedSubset.lagda.md`. **Do not
touch either.**

## WHAT IS MEASURED

`[LJ-1.113]` classified all twenty nine: **PROVABLE 1, NEEDS NEW CONTENT
28, UNKNOWN 0, and none REFUTABLE.**

**The one that is provable is `t0K`**: the frame's own `t0eq` transported
into the delivered `numK0`, machine-checked.

**Twenty five of the twenty eight are ONE pattern**: `K` is closed under a
machine construction. `envK-*` at the environment set, `envInK-*` at the
environment, `valV`, `valW`, `wKfact` at term values, `subK-*` at
substitution values, `consK-*` at the cons. **Each is conditional on a
satisfaction premise, so none is refutable, and each reduces to a closure
statement the delivered adequacy theorems already reach.**

**`t0eq` and `t1eq` cost the consumer no machinery**: they are slot
equalities at concrete indices the rows already state.

**`someEnv` is the odd one, and `[LJ-1.113]` names it the widest unmeasured
term.** It is the only fact whose supplier is a CONSTRUCTION rather than a
closure: an environment `E ∈ K` satisfying `envHypB2`, built from three
memberships (`src/L/Condensation/LowerAgree.lagda.md:51-58`). **The machine's
environment machinery DESCRIBES environments; it does not BUILD one from K
memberships.**

## WHAT TO PROBE

**Build the smallest decisive miniature of `someEnv` and price it.** State
it generically at the K slot:

```
(ya yc ar : S) → ya ∈ K → yc ∈ K → ar ∈ K
              → Σ[ E ∈ S ] (E ∈ K × <the envHypB2 satisfaction>)
```

**Read the real statement in the source** at
`src/L/Condensation/LowerAgree.lagda.md:51-58` and at the `someEnv`
parameter of the current frame; do not work from this sketch.

Build it from the model's `env` and `cons` constructors
(`src/L/Coding/Model.lagda.md`, READ ONLY) plus whatever closure `K` must
have. **Say exactly which closure properties of `K` the construction needs,
because that is what decides whether the closure family is 5 lemma shapes
or 15.**

**Then price the other 25 at the rate you measure**, not at the rate
`[LJ-1.113]` inferred. Its figure, about 250 lines and 3 to 5 s, is a
hypothesis by its own admission (P-l, P-m). **Replace it with a
measurement.**

## THE RULE ON HYPOTHESES, stated as a test and not as a shape

**If the construction needs a property of `K` that nothing supplies, that is
the finding.** Name it, say what would supply it, and **try to refute it**.
`src/ProbeLJ197A.agda` is the shape.

**Run `scripts/check-unbound-hyp.py` on your probe** and report what it
says.

## THE ABORT CRITERION

- **`someEnv` builds**: report the term, its seconds, the closure properties
  of `K` it needed, and the re-priced family. Then STOP. **Do not build the
  other 25.**
- **It cannot be built**: STOP, write the term you could not write, and say
  what the machine would have to provide. **That would be the finding that
  matters most, because `someEnv` is the only one of the twenty eight that
  is not a closure.**
- **Anything walls**: STOP, report the wall with its seconds.

**Do not stop at the first negative.**

**Work in `src/ProbeLJ1115*.agda`. Do not touch any master.**

## C-12, AND THIS IS NOT BOILERPLATE

`[LJ-1.80]` left **SIX agda processes alive at once**, all children of one
wrapper, all on the same probe, none killed. Each carried `-M8g`: 48 GB of
worst case on a 64 GB machine at load 19. **The owner caught it; no tool
did.**

**ONE agda process at a time, and a sibling agent holds the other slot. If a
check does not return, KILL IT before you start another, and report the wall
with its seconds.**

## WHAT YOU MUST NOT DO

- **Do not edit `src/L/Coding/` or `src/V/`.** Read only. **`[LJ-1.113]`'s
  C-39 section is right that the closure family's canonical home is
  `Model.lagda.md`; that is the BUILD this probe gates, not this probe.**
- **Do not touch `src/L/StageCardinal.lagda.md` or
  `src/L/BoundedSubset.lagda.md`**, where a sibling works.
- **Do not touch any master.**
- **Never `src/Everything.lagda.md`.**
- **Do not raise the heap cap.** C-12.
- **Read line numbers and types from the source, never from a report.**

## THE CLASSIFICATION I WANT ON EVERY NEGATIVE

State for every negative whether its deciding claim is **MEASURED** or
**INFERRED**, in those words. **A negative that rests on an inference sets no
verdict.**

## DD4

**Maximize the code the two proofs share, and write it generic.** One rule,
two ends, no metric and no checker, so it is stated in every brief and
answered in every return.

**`[LJ-1.113]`'s DD4 split is the question this probe sharpens: the coding
half is shared by construction, the tower half is not.** **Say which side
`someEnv` falls on**, and whether the closure family it prices is coding or
tower.

## ARCHIVE (DD18)

- **`_build/lj-1.113-report.md`**, read WHOLE. **The twenty nine, their
  verdicts, the price and the widest term. This is your work list.**
- `_build/lj-1.112-report.md` and `src/ProbeLJ1112A.agda`, the frame the
  facts serve.
- `src/L/Coding/Model.lagda.md`, the environment machinery. **READ ONLY:**
  `envSetAt`, `envOverAt`, `extAt`, `consAtL` and the adequacy theorems.
- `src/L/Condensation/LowerAgree.lagda.md:51-58`, `someEnv`'s real
  statement.
- `src/ProbeLJ197A.agda`, the refutation shape.
- `dev/LESSONS.md` **C-38 as extended, C-39, C-40, P-x**, D-1, D-8, D-30,
  P-l, P-m, read WHOLE.

Return an **ARCHIVE USED** section at `file:line`.

## LITERATURE (DD18)

**Banked. Spend nothing.** Say so in one line.

## SCOPE (read)

`_build/lj-1.113-report.md` section 3 FIRST, then
`src/L/Condensation/LowerAgree.lagda.md:40-70`, then
`src/L/Coding/Model.lagda.md`'s environment constructors.

## SCOPE (write)

`src/ProbeLJ1115*.agda` only. Your report is `_build/lj-1.115-report.md`.
**No master. Never `src/Everything.lagda.md`.**

## MANDATORY RULES FOR A BUILD

Run `python3 scripts/rules.py --for build` and `--for probe`, and read every
statement.

- **D-1.** The probe doctrine: the smallest decisive miniature, then throw
  it away.
- **D-8.** Gate a block before funding it. One best-effort figure with its
  basis named, and the widest unmeasured term. **This brief IS the gate.**
- **P-l.** A price from a comparable elsewhere is a hypothesis. **The 250
  line figure is one; replace it.**
- **P-m.** The instantiation class, where the seconds have gone four times
  running.
- **C-38 as extended, C-35, C-36, D-29, D-30, D-10.**
- **C-39.** A brief's prohibition binds harder than its goal. **If a line of
  this brief blocks a route you can see, say so in the report and name the
  route. That is a required section, not a courtesy.**
- **C-40.** Verify the CONSUMERS of a changed master, never the master
  alone.
- **P-x, P-i, P-w, P-h, P-k, P-n, P-o, P-q, P-t, P-u, P-v** as the bundle
  gives them.
- **P-c, R-36, R-38, R-35, R-40.**
- **I-5.** The inference trap this tree has paid for.
- **C-12.** ONE agda process, cap never raised.
- **C-22.** Write the deliverable incrementally.
- **C-31, C-32, C-33, C-34, C-37.**
- **D-26.**

## CONSTRAINTS

- Never commit, never push, never `git checkout .`, `git stash`,
  `git reset --hard` or `git clean`.
- Do NOT run `make check`.
- Count with `scripts/ledger.py`. Run `scripts/lint-prose.py --check` and
  `scripts/lint-agda.py --check`.
- **Run `scripts/check-unbound-hyp.py` on your probe** and report what it
  says.
- DD23 freezes mathematical prose.
- **Report the load average beside every absolute figure.**
- Evidence is `file:line`. Write ASD-STE100.

## RETURN

Write `_build/lj-1.115-report.md` incrementally, skeleton first.

**Lead with whether `someEnv` builds**, YES or NO, with the term at
`file:line` and its seconds. Then the closure properties of `K` it needed,
each named, and whether anything supplies them. Then the re-priced family,
MEASURED this time, with the per-lemma rate. Then the C-39 section. **Mark
every negative MEASURED or INFERRED.** Then the DD4 answer: coding or tower.
