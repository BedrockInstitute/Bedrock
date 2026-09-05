# LJ-1.166: gate `K(u)`, the SUPPLY that six gates never priced

tier: opus (version `override`, set 2026-08-13; the head for every case is in
`scripts/dispatch_policy.py`, which is the only place the tables live)

## GOAL

**Six gates priced the DERIVATIONS. Not one priced a SUPPLY.**
`[LJ-1.165]` measured that and stopped. **You price the supply.**

## THE FINDING THAT SENT YOU, MEASURED by `[LJ-1.165]`

**`levelIn` and `cover` are not discharged and `theorem` does not derive**, and
the reason is not the derivation:

- **The assembly WORKS**: 17 in-fence lines against a gated 16, master exit 0.
  `[LJ-1.165]` built it, then REMOVED it, because nothing supplies the face.
- **`powK` is not one missing fact. It is SEVEN and they are one thing**:
  `envK`, `codeK`, `memK`, `valK`, `powK`, `stepK`, `entryK` are all adequacy
  conditions on the bound `K`, and none has a supplier.
- **`KFacts` is NEVER CONSTRUCTED anywhere in `src/`.** I verified it: the only
  thing shaped like a constructor builds a `KFacts` FROM another `KFacts`, so
  there is no base case and no value is ever made.
- **The same absence blocks `HasLevels` and `Covered`**, which no gate looked
  at. The bounded graph has exactly ONE consumer and that consumer only STATES
  it; nothing anywhere concludes a satisfaction of it.
- **C-35 fires a fifth time**: `LevelHood0` (`src/L/BoundedSubset.lagda.md:840-869`)
  has no consumer, and one of its four definitions is exactly what `HasLevels`
  needs.

## WHAT DEVLIN SUPPLIES, and it is one construction

`dev/literature/devlin-II5.md:245-256`:

> What IS required is a bounded description of the Def step inside the Σ₀
> matrix: 2.2-2.4 write `D(v, u) = "v = Def(u)"` as Σ₁, **then bind every
> unbounded quantifier by the concrete set `K(u)`, the finite sequences over
> the formula set, the variables and the members of `u`.** The Σ₀ matrix
> `C(w, v, u)` with `w = K(u)` **is the bounded satisfaction substrate of
> Devlin's engine.**

**And the digest already says what it must be here:**

> the `[LJ-1.2]` probe's missing facts, a bounded object-level description of
> the code set and of the satisfaction table, **are exactly the analogues of
> this substrate on the project's coding; the argument does not require them to
> have any particular shape, only that some bounded description with a bound
> inside the carrier exists.**

**That last clause is your freedom and your criterion: ANY bounded description
with its bound inside the carrier.**

## WHAT TO DO

1. **Say what `K(u)` is on THIS coding.** Devlin's is the finite sequences over
   the formula set, the variables and the members of `u`. **Name the analogue
   at this tree's coding layer, at `file:line`.**
2. **Say what already exists.** `src/L/Coding/` builds codes; `src/L/Coding/CodeSet.lagda.md`
   and `Sequence.lagda.md` are the obvious places. **A bounded code set may be
   most of it.**
3. **Then PRICE the construction of one `KFacts` value**, in in-fence lines and
   in cold seconds, one best-effort figure each with its basis named (DD8).
4. **And name the widest unmeasured term of that price, with the probe that
   would measure it.**

## THE ABORT CRITERION, fixed BEFORE you start (D-1)

- **You can price it**: report the figure, its basis and its widest unmeasured
  term. STOP.
- **The bound cannot sit inside the carrier on this coding**: **STOP AND SAY
  SO.** That is the deepest possible finding here: it would mean Devlin's
  engine does not transfer to this coding, and the route needs re-planning
  rather than funding.
- **`K(u)` turns out to be already built under another name**: **say so
  first.** `[LJ-1.163]` found exactly that for `ElemDown` and the phase had
  spent three dispatches pricing a term the tree already held. **Search before
  you price.**
- **Anything walls**: STOP with its wall-clock. **Never raise the cap.**

## THE TWO WALLS ALREADY MEASURED HERE

- **`[LJ-1.165]` cured one**: a `mapΣ₁` at 171 s and heap exhaustion becomes
  exit 0 in 4 s when one implicit index is given explicitly. **It also REFUTED
  `[LJ-1.161]`'s diagnosis by bisection: the `refl` blamed for it is four
  seconds.**
- **One is NOT cured**: `σ₁-up` at the level-hood certificate, **20 min 1 s,
  9.40 GB, SIGTERM, no heap exhaustion**, with and without the index.

**Fix your own wall-clock criterion in writing before each run.**

## THE RULE THIS PHASE HAS PAID FOR FIVE TIMES

**C-38 as extended: a hypothesis is discharged when something SUPPLIES it.**

**`[LJ-1.151]` found a delivered hypothesis that was outright FALSE.
`[LJ-1.153]` repaired 36 of that class. `[LJ-1.161]` found three delivered
definitions with no consumer, `[LJ-1.163]` a fourth, `[LJ-1.165]` a fifth.**

**You are pricing the cure for that whole class. Do not price a restatement:
if your figure covers an interface rather than a value, say so and price the
value separately.** `[LJ-1.146]` made exactly that mistake and caught itself.

## WHAT YOU MUST NOT DO

- **Do not build `K(u)`.** You gate it.
- **Do not edit any master.**
- **Do not touch the three `*Agree` masters**, `src/L/Coding/Graph.lagda.md`, or
  `[LJ-1.164]`'s move.
- **A probe goes in `agents/tasks/LJ-1-166/`**, never in `src/`, tracked.
- **ONE agda process, `GHCRTS="-A64m -I0 -M8g"`, cap NEVER raised.**
- Never `src/Everything.lagda.md`. Never commit, never push, never
  `git checkout .`, `git stash`, `git reset --hard` or `git clean`.
- Do not run `make check`; I run it.

## THE CLASSIFICATION I WANT ON EVERY NEGATIVE

**MEASURED or INFERRED, in those words.**

## DD4

**Maximize the code the two proofs share, and write it generic.** One rule, two
ends, no metric and no checker.

**A bounded description of a coding layer is template content if anything is.**
**Say what fraction of your priced construction names the Def tower**, and
whether the J tower would re-instantiate or rewrite.

## ARCHIVE (DD18)

**`[LJ-1.157]` measured 37 of 61 live briefs citing no archive. This section is
not a form: `[LJ-1.160]` found the phase's bypass inside one.**

- **`agents/tasks/archive/LJ-1-2/lj-1.2-gate.md` section 5**, which the
  literature digest names as holding the missing facts. **That is a gate this
  route already ran and its section 5 is cited by the digest. Read it.**
- **`archive/src/2026-08-09-rud-route/L/Coding/`** and **`L/Definability.lagda.md`**:
  the retired route's own coding layer. **Did it build a bounded code set? At
  what size?**
- `archive/src/2026-08-09-rud-route/L/LevelFormula.lagda.md`, 258 in-fence.
- **Take SHAPE, never a claim.** `[LJ-1.11]` ruled that route's condensation
  target classically FALSE.
- `agents/tasks/LJ-1-165/lj-1.165-report.md`, read WHOLE.
- **`dev/LESSONS.md` C-38 as extended, C-35, D-1, DD8, P-l, C-36**, read WHOLE.

Return an **ARCHIVE USED** section at `file:line`.

## LITERATURE (DD18)

`dev/literature/devlin-II5.md:240-260` and `_build/literature/dev2.txt:593-630`,
which the digest cites for `K(u)` itself. **Say exactly what Devlin's `K(u)`
contains and what makes its bound work.** Return a **LITERATURE USED** section.

## SCOPE (read)

`dev/literature/devlin-II5.md:240-260` FIRST, then
`agents/tasks/archive/LJ-1-2/lj-1.2-gate.md` section 5, then
`src/L/Coding/CodeSet.lagda.md`.

## SCOPE (write)

`agents/tasks/LJ-1-166/` only. **No master.**

## MANDATORY RULES

Run `.venv/bin/python scripts/rules.py --for recon` and `--for probe`.

- **DD8.** Name the widest unmeasured term and the probe that measures it.
- **C-38 as extended.** Price a VALUE, not an interface.
- **C-35, D-1, P-l, P-i, C-12, C-22, C-36, C-39, C-40.**
- **D-10, D-26, D-29, D-30. C-31, C-32, C-33, C-34, C-37. I-5.**

## CONSTRAINTS

- Count with `.venv/bin/python scripts/ledger.py`.
- Run `scripts/lint-prose.py --check` and `scripts/lint-agda.py --check`.
- DD23 freezes mathematical prose.
- Evidence is `file:line`. Write ASD-STE100.

## RETURN

**Lead with whether `K(u)` can be built on this coding, and its price with its
basis.** Then what already exists. Then the widest unmeasured term and its
probe. Then whether the bound sits inside the carrier, MEASURED. Then the DD4
answer. **Mark every negative MEASURED or INFERRED.**
