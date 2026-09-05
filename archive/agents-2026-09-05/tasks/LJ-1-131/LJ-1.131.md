# LJ-1.131: price the V = L route against the ambient one

tier: opus (version `override`, set 2026-08-13; the head for every case is in
`scripts/dispatch_policy.py`, which is the only place the tables live)

## GOAL

**Price a route change the owner is leaning toward, before anyone funds it.**
`[LJ-1.129]` found that this wing's theorem carries ambient hypotheses that
the ambient universe cannot pay. **Devlin pays them from `V = L`. Price that
switch. Do NOT make it.**

## CWD

`/Users/alsg/Agentic/Bedrock`, branch `two-tower-bridge`. **Reports now live
in `agents/reports/`, briefs in `agents/briefs/`, and older reports in
`agents/reports/archive/`.** `_build/` no longer holds them.

## WHAT IS MEASURED, and I verified each of these in the source myself

`[LJ-1.129]`, an adversarial review at maximum effort, found four facts:

1. **Devlin 5.5's first line is "Assume V = L"**
   (`agents/reports/devlin-II5.md` is NOT it; the digest is
   `dev/literature/devlin-II5.md:147`, verbatim). **Our `Devlin55` dropped
   that premise** and pays instead with two ambient injection hypotheses,
   `sq` and `absorbs`.
2. **The ambient V cannot pay them.** `[LJ-1.107]` delivered `sq` at initial
   ordinals only. `[LJ-1.114]` PROVED the truncation cannot pass `Upper`'s
   induction: two independent truncation eliminations give injections whose
   codes collide.
3. **The only site is `α = ω`, `x = ∅`**, and at `x = ∅` the conclusion is
   already provable without `Devlin55`: `∅∈Lλ` at
   `src/L/BoundedSubset.lagda.md:1215-1217` uses two `Lset-mono` steps.
4. **`IsCardinal` is ambient**, while DD1 rules the endpoint "stated
   internally" (`dev/PLAN.md:167`).

**No delivered proof in the window is false.** The drift is at statement
level.

## THE ORCHESTRATOR'S OWN READING, and it is INFERRED

**I think `V = L` is the more natural and more elegant route, and the reason
is that the theorem's subject and its proof would then live in one
universe.** In L the definable well-order `<_L` gives the Skolem functions
5.4 needs and the cardinal arithmetic `1.1(vii)` needs, so `sq` and
`absorbs` stop being hypotheses and become theorems.

**That is a judgement, not a measurement, and it is what you are here to
price.** **If the mathematics says I am wrong, say so.**

## WHAT TO PRICE

**Both routes, in in-fence lines, each with its basis named.** DD8.

### Route A: assume V = L

1. **What does `V = L` cost to STATE in this tree?** Is it a module
   parameter, and over what? Read how `src/L/Constructible.lagda.md` and
   `src/L/Coding/` set the tower up. **Say whether the tree can express
   "every set is constructible" at all today.**
2. **Does the tree have, or can it cheaply get, the definable well-order
   `<_L`?** This is the load-bearing question. Search for any existing
   well-order of L, any Gödel pairing on the tower, any canonical code
   ordering. `src/L/Coding/` builds codes, and a code ordering may already
   be most of it.
3. **Given `<_L`, what do `sq` and `absorbs` cost as THEOREMS?** They are
   currently unpayable hypotheses. Price them as derivations.
4. **What breaks?** `Devlin55` and `BoundedSubsetAt` would change shape.
   `L.StageCardinal` takes `sq` as a parameter. Name every master that
   moves and say whether its content survives.

### Route B: keep the ambient route

1. **What does the gap from `α = ω` to every infinite cardinal cost?**
   Devlin 5.6 applies 5.5 at `κ⁺` with `α = κ` for every infinite `κ`
   (`dev/literature/devlin-II5.md:160-166`). **The current site reaches CH
   at most; price the rest.**
2. **What does the ambient-to-internal conversion cost?** DD1 wants the
   endpoint stated in L. No PLAN row prices this. **Price it, or say it
   cannot be priced without a probe and name the probe.**
3. **`[LJ-1.114]`'s wall.** Does Route B have to go through it, or around
   it, and at what cost?

### Then compare

**One best-effort figure each, with its basis, plus the widest unmeasured
term of each and the probe that would measure it.** **Say which you would
take and why, in mathematics, not in line counts.** The owner asked which is
more natural and elegant; the price is what tells them whether elegance is
affordable.

## THE ABORT CRITERION

- **Both routes price**: report both, recommend one, name the widest term of
  each. STOP.
- **Route A is impossible in this tree** for a reason you can state: STOP and
  say exactly what is missing. **That would settle the question.**
- **Anything walls**: STOP, report the wall with its seconds.

**This is a recon and pricing task. Do NOT change the route. Do NOT edit any
master.** You may write ONE small probe to price a step.

## WHAT YOU MUST NOT DO

- **Do not assume the axiom of choice in the ambient universe** when pricing
  Route A. The point of `V = L` is that you do not need it.
- **Do not price by analogy.** P-l: a price from a comparable elsewhere is a
  hypothesis. Three inherited figures came in low this session and one came
  in high.
- **Do not edit any master.** Probes are `src/ProbeLJ1131*.agda`, never
  `.lagda.md`.
- Never `src/Everything.lagda.md`. Never commit, never push.
- **Do not raise the heap cap.** C-12, `GHCRTS="-A64m -I0 -M8g"`, ONE agda
  process.

## THE CLASSIFICATION I WANT ON EVERY NEGATIVE

**MEASURED or INFERRED, in those words.** A negative that rests on an
inference sets no verdict. **My own reading above is INFERRED and you may
overturn it.**

## DD4

**Maximize the code the two proofs share, and write it generic.** One rule,
two ends, no metric and no checker, so it is stated in every brief and
answered in every return.

**Which route shares more with the AC side?** The AC side is delivered. **If
`V = L` lets the two proofs share the well-order, that is a DD4 argument for
Route A and it belongs in your answer.**

## ARCHIVE (DD18)

- **`agents/reports/lj-1.129-report.md`**, read WHOLE. The four facts and the
  five questions.
- `agents/reports/lj-1.107-report.md`, `lj-1.111-report.md`,
  `lj-1.114-report.md`: the square-law wall and its proof.
- `agents/reports/lj-1.91-report.md`: why the internal `ω₁ᴸ` was rejected.
- `agents/reports/archive/`: the retired route's records. **`[LJ-1.11]` ruled
  the rud route's condensation target classically FALSE, so take no claim
  from it, only shape.**
- `src/L/BoundedSubset.lagda.md`, `src/L/Constructible.lagda.md`,
  `src/L/Coding/`, `src/L/Ordinal/SquareLaw.lagda.md`,
  `src/L/StageCardinal.lagda.md`.
- `dev/LESSONS.md` D-8, D-30, P-l, C-36, C-38 as extended, C-39, read WHOLE.

Return an **ARCHIVE USED** section at `file:line`.

## LITERATURE (DD18)

**This is the one place the literature decides.** `dev/literature/devlin-II5.md`
and its surroundings, `devlin-errata.md` for known errors in the primary
text. **Say exactly where Devlin uses `V = L` in the 5.5 proof and in
1.1(vii), and whether he could avoid it.** Return a **LITERATURE USED**
section.

## SCOPE (read)

`dev/literature/devlin-II5.md:140-170` FIRST, then
`agents/reports/lj-1.129-report.md`, then `src/L/Constructible.lagda.md`.

## SCOPE (write)

`src/ProbeLJ1131*.agda` only. Your report is
`agents/reports/lj-1.131-report.md`. **No master.**

## MANDATORY RULES

Run `python3 scripts/rules.py --for recon` and `--for probe`, and read every
statement.

- **D-8.** Gate a block before funding it. **This brief IS the gate.**
- **D-30.** Price what the CONSUMER needs. **The consumer is `L ⊨ GCH`
  stated in L, not the current site.**
- **P-l.** A price from a comparable elsewhere is a hypothesis.
- **C-36.** Write the term you could not write.
- **C-38 as extended, C-35, C-39, C-40, D-10, D-29.**
- **P-m, P-x, P-i, P-w, P-h, P-k, P-n, P-o, P-q, P-t, P-u, P-v** as the
  bundle gives them.
- **P-c, R-36, R-38, R-35, R-40.**
- **I-5.** The inference trap this tree has paid for.
- **C-12.** ONE agda process, cap never raised.
- **C-22.** Write the deliverable incrementally.
- **C-31, C-32, C-33, C-34, C-37.**
- **D-1, D-26.**

## CONSTRAINTS

- Do NOT run `make check`.
- Count with `scripts/ledger.py`. Run `scripts/lint-prose.py --check` and
  `scripts/lint-agda.py --check`.
- DD23 freezes mathematical prose.
- **Report the load average beside every absolute figure.**
- Evidence is `file:line`. Write ASD-STE100.

## RETURN

**Lead with which route you would take and why, in mathematics.** Then the
two prices with their bases. Then the widest unmeasured term of each and its
probe. Then what breaks under Route A, master by master. Then where Devlin
uses `V = L` and whether he could avoid it. **Mark every negative MEASURED or
INFERRED.** Then the DD4 answer.
