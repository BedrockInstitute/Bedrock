# LJ-1.120: build the generic environment-set over an arbitrary arity

tier: codex (default)

## GOAL

**Build the one piece the closure family is missing.** Twenty five of the
twenty eight facts are closures of a GIVEN satisfier. **One is a
construction, and nothing constructs it.**

## CWD

`/Users/alsg/Agentic/Bedrock`, on branch `two-tower-bridge`, **clean at
`963cc11`. `make check` passes.** A sibling agent works in
`src/L/BoundedSubset.lagda.md`. **Do not touch that file.**

## WHAT IS MEASURED

`[LJ-1.115]` paid the gate and bounded the family.

**`someEnv` does not build. The rest of its obligation does**: `build` at
`src/ProbeLJ1115A.agda:123-134` is GREEN and wires the delivered
`EnvSet.back` transfer at the And-row layout. The two walls are at
`src/ProbeLJ1115B.agda:64` and `:72`.

**The construction needs four closure properties of `K`, and exactly one is
missing:**

| property | status, with the return's citation |
|---|---|
| **`envSetK`**: `K` closed under an environment-set built over an **arbitrary arity in `K`**, values in the ambient slot, satisfying the machine's `envSetAt` | **NOT SUPPLIED.** The machine builds over **numerals only** (`src/L/Coding/EnvSet.lagda.md:183`); `AmbientHolds` demands the arity equality (`src/L/Coding/Sound.lagda.md:262-284`); `KFacts` has no such field; the frame's `envK-*` close a GIVEN satisfier and construct none |
| `arityK` | SUPPLIED, a delivered `KFacts` field |
| `envInK` at the And-row layout | SUPPLIED, the frame's `envInK-imp` |
| the bounded transfer `envSetAt → envHypB2` | DELIVERED as `EnvSet.back` |

**So the family is the twenty five's five to seven lemma shapes PLUS ONE
construction closure. It is not fifteen.** Measured rate at the site: 0.019
s per line, 134 in-fence lines at 2.57 s cold.

## WHAT TO BUILD

**The generic environment-set over an arbitrary arity, and its
`envSetAt` adequacy.**

1. **Read what the machine already builds.** `src/L/Coding/EnvSet.lagda.md`
   builds over numerals (`:183`, VERIFY). **Say exactly where the numeral
   assumption enters, and whether the construction generalizes or must be
   rebuilt.**
2. **Build the generic version in a probe**: for an arity set `ar` and a
   value assignment, the environment-set exists and satisfies `envSetAt` at
   the And-row layout.
3. **Then state its K-closure**: with `ar ∈ K` and the values in `K`, the
   constructed set is in `K`. **Say what closure of `K` that needs, and
   whether `KFacts` supplies it.**
4. **Then feed it to `src/ProbeLJ1115A.agda`'s `build`** and report whether
   `someEnv` now closes. **That is the acceptance test.**

**Work in `src/ProbeLJ1120*.agda`. Do NOT edit any master.** The canonical
home for this content is the coding machinery, and `[LJ-1.113]`'s C-39
section is right about that, **but the master edit is the NEXT dispatch and
it needs this one audited first.** Say in your report where you would put
it and why.

## THE RULE ON HYPOTHESES, stated as a test and not as a shape

**If you leave a hypothesis standing, name what would supply it at
`file:line`, and TRY TO REFUTE IT.** `src/ProbeLJ197A.agda` is the shape.
**Eleven hypotheses of this layer were refutable and every one was found
only when somebody attacked it.**

**Run `scripts/check-unbound-hyp.py` on your probe** and report what it
says.

## THE ABORT CRITERION

- **The construction builds and `someEnv` closes**: report both terms with
  their seconds, and **re-price the twenty five at the rate you measure**.
  Then STOP.
- **The construction builds but `someEnv` does not**: report how far, and
  the term you could not write.
- **The machine's numeral assumption is load-bearing and the construction
  must be rebuilt**: report what that costs, with a basis. **That is a
  price, not a failure.**
- **Anything walls**: STOP, report the wall with its seconds.

**Do not stop at the first negative. Report how far you reached.**

## C-12, AND THIS IS NOT BOILERPLATE

`[LJ-1.80]` left **SIX agda processes alive at once**, all children of one
wrapper, all on the same probe, none killed. Each carried `-M8g`: 48 GB of
worst case on a 64 GB machine at load 19. **The owner caught it; no tool
did.**

**ONE agda process at a time, and a sibling agent holds the other slot. If a
check does not return, KILL IT before you start another, and report the wall
with its seconds.**

## WHAT YOU MUST NOT DO

- **Do not edit any master**, and in particular not `src/L/Coding/`,
  `src/V/`, `src/L/Condensation*` or `src/L/BoundedSubset.lagda.md`. **Read
  `src/L/Coding/` freely.**
- **Do not weaken `envSetAt` or the And-row layout to make the construction
  fit.** If the layout must change, that is the finding.
- **Do not write a probe as `.lagda.md`.** `[LJ-1.113]` did, and
  `check-fences` counted five probes as masters. **Probes are
  `src/ProbeLJ1120*.agda`.**
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

**This is CODING machinery, which `[LJ-1.113]` called shared by
construction.** **Say whether the generic environment-set is tower-free**,
because if it is, the J tower gets the whole closure family unchanged and
that is the largest DD4 win available in this phase.

## ARCHIVE (DD18)

- **`_build/lj-1.115-report.md`**, read WHOLE, and **`src/ProbeLJ1115A.agda`**
  and `src/ProbeLJ1115B.agda`. **The four properties, the two walls, and
  `build`, which is your acceptance test.**
- **`_build/lj-1.113-report.md`**, read WHOLE. **The twenty nine, their
  verdicts, and the C-39 section naming the canonical home.**
- `_build/lj-1.112-report.md` and `src/ProbeLJ1112A.agda`, the frame the
  facts serve.
- **`src/L/Coding/EnvSet.lagda.md`** and **`src/L/Coding/Sound.lagda.md`**,
  READ ONLY. The numeral construction and the adequacy.
- `src/L/Coding/Model.lagda.md`, the environment machinery. READ ONLY.
- `src/ProbeLJ197A.agda`, the refutation shape.
- `dev/LESSONS.md` **C-38 as extended, C-39, C-40, P-x**, C-35, C-36, D-8,
  D-30, P-l, P-m, read WHOLE.

Return an **ARCHIVE USED** section at `file:line`.

## LITERATURE (DD18)

**Say in two lines whether Devlin's coding builds environments over
arbitrary sets or over numerals**, from `dev/literature/devlin-II5.md`.
Spend little.

## SCOPE (read)

`src/ProbeLJ1115A.agda` FIRST, then `src/L/Coding/EnvSet.lagda.md`, then
`src/L/Coding/Sound.lagda.md:250-300`.

## SCOPE (write)

`src/ProbeLJ1120*.agda` only. Your report is `_build/lj-1.120-report.md`.
**No master. Never `src/Everything.lagda.md`.**

## MANDATORY RULES FOR A BUILD

Run `python3 scripts/rules.py --for build` and read every statement.

- **C-38 as extended.** A hypothesis is discharged when something SUPPLIES
  it.
- **C-35.** A block with no consumer is UNTESTED. **`build` is your
  consumer.**
- **C-36.** Write the term you could not write.
- **C-39.** A brief's prohibition binds harder than its goal. **If a line of
  this brief blocks a route you can see, say so in the report and name the
  route. That is a required section, not a courtesy.**
- **C-40, D-8, D-30, D-10, D-29.**
- **P-l.** A price from a comparable elsewhere is a hypothesis. **The site
  rate 0.019 s per line is measured; the twenty five's line count is not.**
- **P-m.** The instantiation class.
- **P-x, P-i, P-w, P-h, P-k, P-n, P-o, P-q, P-t, P-u, P-v** as the bundle
  gives them.
- **P-c, R-36, R-38, R-35, R-40.**
- **I-5.** The inference trap this tree has paid for.
- **C-12.** ONE agda process, cap never raised.
- **C-22.** Write the deliverable incrementally.
- **C-31, C-32, C-33, C-34, C-37.**
- **D-1, D-26.**

## CONSTRAINTS

- Never commit, never push, never `git checkout .`, `git stash`,
  `git reset --hard` or `git clean`.
- Do NOT run `make check`.
- **Run `scripts/check-fences.py --check`** and say the master count. **It
  should be 87.**
- Count with `scripts/ledger.py`. Run `scripts/lint-prose.py --check` and
  `scripts/lint-agda.py --check`.
- **Run `scripts/check-unbound-hyp.py` on your probe.**
- DD23 freezes mathematical prose.
- **Report the load average beside every absolute figure.**
- Evidence is `file:line`. Write ASD-STE100.

## RETURN

Write `_build/lj-1.120-report.md` incrementally, skeleton first.

**Lead with whether the generic environment-set builds and whether
`someEnv` closes**, YES or NO for each, with terms at `file:line` and their
seconds. Then where the numeral assumption enters and whether it was
generalized or rebuilt. Then the K-closure the construction needs and what
supplies it. Then the twenty five re-priced at your measured rate. Then
where you would put this content in the tree and why. Then the C-39
section. **Mark every negative MEASURED or INFERRED.** Then the DD4 answer:
is it tower-free?
