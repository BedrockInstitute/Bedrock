# LJ-1.52: the level-hood adequacy at the hull

tier: codex (default)

## GOAL

One obligation blocks two hypotheses. Build it, or return the term you could
not write.

## CWD

`/Users/alsg/Agentic/Bedrock`, on branch `two-tower-bridge`, clean at
`f7314af`.

## THE OBLIGATION

`levelIn` and `cover` both survive on **the level-hood adequacy at the hull's
carrier**. `[LJ-1.51]` wrote the missing term for `levelIn` explicitly:

```text
levelIn δ oδ δ∈πX =
  -- δ = π m for a hull member m; eliminate the truncation into the
  --   proposition Lset δ ∈ πX
  -- the Σ₂ level-hood statement at the hull gives, by elementarity of the
  --   hull (an unbuilt TV/ElemDown instance), witnesses K' v' w' ∈ M of the
  --   level graph at m, with v' the level value
  -- collapse-of-the-level:  π v' ≡ Lset (π m) = Lset δ
  --     needs (i) the twelve-row agreement re-based at the hull's carrier,
  --               so v' = Lset m' for the code witness m'
  --      and (ii) π (Lset m') = Lset (π m'), the collapse commuting with
  --               the level construction
  -- then πX-intro v' gives Lset δ ∈ πX
```

`cover` needs the same adequacy plus the least-δ and level-preservation steps.

**Three unbuilt pieces, all named:** the TV/ElemDown instance, the twelve-row
re-basing, and the collapse commuting with `Lset`.

## THE SPELLING RULE THAT DECIDES YOUR SECONDS

**P-v, extended yesterday: GIVE A PROOF A NAME AND PASS THE NAME.** Writing the
same proof inline as `refl` in both a type and a body forces the elaborator to
decide a conversion between two elaborations of it, and deciding that unfolds
the built tree.

| spelling | ms |
|---|---:|
| `refl` inline in the type AND the body | **150,133** |
| the proof NAMED and passed | **220** |
| named in the type, `refl` in the body | 151,402 |

**One named side is not enough.** I re-ran the ends myself at 154.92 s against
2.20 s. **If any measurement of yours lands in the hundred-second range, look
here before you look anywhere else.**

## THE ROUTE THAT WORKS, delivered and green

**`EraseTransfer` never runs `erase-Δ₀` at all.** `abs₀` recurses on the Δ₀
WITNESS, not the formula, so the certificate never crosses `erase`.
`src/ProbeDD25H2.agda` instantiates it at 1.56 s with the transfer below the
profiler's threshold, and I measured it at 1.59 s. `src/ProbeDD25H8.agda` holds
the Σ₁ counterpart as 16 lines of template content with no `L` syntax.

**Use that route.** Do NOT build the certificate at variable slots: `[LJ-1.50]`
measured that as SLOWER, 327 ms against 220.

## THE LAWS, each with the ACTION it prescribes (C-37)

- **P-u. CERTIFY BEFORE YOU PLACE**, and the action is to compose the
  absoluteness through the UNPLACED form, which IS `EraseTransfer`.
- **P-t.** The class follows the FORMULA. The concrete-versus-variable carrier
  axis does not decide the cost.
- **D-30. Price what the CONSUMER needs.** 5.5 uses each piece at ONE shape.
  That question was worth 5.45x at the square law.
- **C-34. Build the cure or report the wall that stopped you.** "It is a design
  decision" is not a third option. **This has been broken three times this
  phase and a review built the deferred cure every time**: 0.334 to 0.0108,
  0.436 to 0.0072, and 150 s to 1.56 s.
- **C-36.** A failed substitution is not a proof of impossibility. **Write the
  term you could not write**, as `[LJ-1.51]` did. You may strengthen a
  statement; you may not weaken one.

## ORDER OF ATTACK

1. **The collapse commuting with `Lset`**, `π (Lset m') = Lset (π m')`. It is
   the most self-contained of the three and the collapse's transitive-fixing
   clause is delivered at `src/V/Collapse.lagda.md`.
2. **The twelve-row re-basing at the hull's carrier.** The rows are CLOSED and
   machine-checked at `src/L/Condensation.lagda.md`; this is a re-basing, not a
   re-proof. **Check whether the rows are already generic enough in the
   carrier**, because if they are, this piece is a instantiation rather than
   work.
3. **The TV/ElemDown instance.** `hull-closed` gives Tarski-Vaught at HULL
   parameters, which is the hard half.

**If you discharge only some, say exactly which and what each survivor still
needs.** A partial with an honest ledger is a full deliverable, and
`[LJ-1.51]`'s ledger is the model.

## WHAT IS SETTLED, so you do not re-open it

- `fin-inj` and `Mext` are DISCHARGED and their parameters removed.
- `sq` has a master at `src/L/Ordinal/SquareLaw.lagda.md`, 775 lines. **Its
  parameter still survives** because the consumer wants the law at every
  infinite ordinal; that reshaping is `[LJ-1.17]` route 1 at 200 to 280 lines
  and **it is NOT your task.**
- The twelve-row table, block 1 and both `[LJ-1.49]` cures are CLOSED.
- **Δ₀ IS the target.** Delivered `Σ₁`'s only base is `σ-Δ₀`
  (`src/FOL/LevyHierarchy.lagda.md:73-75`).
- All masters carry ZERO placement. **If you need `absFo` or a placed `Δ₀`,
  STOP and report it.**

## THE THRESHOLD

DD24's live bar is **0.012716**. The GCH aggregate is **0.0118 over 6,600 lines
and 77.94 s, within**. **Do not use 0.013193.** Report the marginal rate for
what you add, the whole-file rate and the module-load cone separately, each from
three cold runs in ONE caliber with the spread. `[LJ-1.49]` mixed wall and user
seconds and flagged it; do not repeat that.

## DD4

**Maximize the code the two proofs share, and write it generic.** One rule, two
ends, no metric and no checker, so it is stated in every brief and answered in
every return.

`levelIn` and `cover` key on the Def syntax, so D-26 predicts per-tower. **But
the collapse commuting with the level construction may be template**, since it
is about a collapse and a tower rather than about definability. **Say which side
each piece falls on.**

## ARCHIVE (DD18)

- **`_build/lj-1.51-report.md`** sections 4.1 and 4.2, and
  **`_build/lj-1.50-review.md`** with probes `src/ProbeDD25H2.agda`, `H3`,
  `H8`. **Read both WHOLE.** C-32 exists because a brief of mine named a
  section and hid the decisive probe.
- `_build/lj-1.49-report.md` for the hypothesis ledger.
- `archive/rud-route/src/L/Condensation.lagda.md` for SHAPE only; `[LJ-1.11]`
  showed its target is classically FALSE.
- `dev/LESSONS.md` is NOT archived and still binds.

Return an **ARCHIVE USED** section at `file:line`.

## LITERATURE (DD18)

- `_build/literature/dev2.txt:1372-1385` for 5.5, and
  `dev/literature/devlin-II5.md` Step C. **Devlin asserts absoluteness where
  this proves a transfer.** Say in one line what he assumes.
- The errata do NOT cover Chapter II section 5. `[LJ-1.14]` verified it. **Do
  not re-check it.**

Return a **LITERATURE USED** section, with WHY NOT for anything skipped.

## SCOPE (read)

`_build/lj-1.51-report.md` section 4 FIRST, then `src/ProbeDD25H2.agda`, then
`src/L/BoundedSubset.lagda.md`'s `HullStage.Condense`, then
`src/V/Collapse.lagda.md`.

## SCOPE (write)

`src/L/BoundedSubset.lagda.md`, `src/L/Condensation.lagda.md`, and
`src/ProbeLJ152*.agda`. Your report is `_build/lj-1.52-report.md`. **No other
master. Never `src/Everything.lagda.md`.**

## MANDATORY RULES FOR A BUILD

Run `python3 scripts/rules.py --for build` and read every statement.

- **P-h.** Module-parameterized, never function-parameterized.
- **P-k.** A read lemma is stated where its consumers use it.
- **P-l, P-m, P-n, P-t, P-u, P-v** as above, each with its action.
- **R-35.** State the membership at the SMALL index and climb.
- **R-38.** Seal at the birth site, and do NOT unseal.
- **R-40.** State a membership witness SHALLOW and climb.
- **I-5.** The inference trap this tree has paid for.
- **C-12.** `GHCRTS="-A64m -I0 -M8g" agda <file>`, ONE process, cap never
  raised. **A heap exhaustion is a WALL with its seconds; an interruption is
  NOT**, and must be labelled a stop with its bound.
- **C-22.** Write the deliverable incrementally.
- **C-31, C-32, C-33, C-34, C-35, C-36, C-37.**
- **D-10, D-26, D-29, D-30.**

## CONSTRAINTS

- Never commit, never push, never `git checkout .`, `git stash`,
  `git reset --hard` or `git clean`.
- Typecheck what you touch and every consumer. Do NOT run `make check`.
- **Run `scripts/check-fences.py --check` before you report anything closed.**
- Count with `scripts/ledger.py`. Run `scripts/lint-prose.py --check` and
  `scripts/lint-agda.py --check`.
- DD23 freezes mathematical prose. Code and its own comments only.
- **The machine is quiet and both Agda slots are yours.**
- Evidence is `file:line`. Write ASD-STE100.

## RETURN

Write `_build/lj-1.52-report.md` incrementally, skeleton first.

Lead with the ledger: are `levelIn` and `cover` discharged, and if not what each
still needs. Then which of the three pieces landed and what each cost. Then the
rates with spreads in one caliber. Then, for anything that walled, the term you
could not write. Then the DD4 split and what you are not sure of.
