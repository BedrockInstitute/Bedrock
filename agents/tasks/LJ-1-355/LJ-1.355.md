# LJ-1.355: port the archived ambient `csb` into `src/V/`, plus the corollary

tier: pi (pi-subagent-mode), model `glm-5.3`. **I ran
`scripts/dispatch/dispatch_policy.py` before writing this line and took the head
it gave.**

## WHY, and the owner found this line himself

The owner asked why the restated GCH trophy gives two coded injections rather
than `|𝒫(κ)| = κ⁺`. **I answered「the tree has no Cantor-Bernstein」after
grepping `src/` ONLY.** **The owner said the archive surely has it. It does, 37
hits**, and `[LJ-1.353]`'s recon then priced the whole question.

## WHAT `[LJ-1.353]` RETURNED

**Internal `L ⊨ CSB` is EXPENSIVE, about 650 lines**, survey anchored on four
measured points, and it wants **Tarski's fixed-point form, not the chain form**:
one separation over a `𝒫 a`-bounded quantifier. **Its widest unmeasured term is
the three closure facts as satisfaction inferences, and its miniature is one
formula plus one adequacy proof.** **That build is NOT this task.**

**What IS this task is the cheap half it recommends:**

> **Port the ambient `csb` into `src/V/` at about 100 lines, and add the
> corollary.** **Both pieces are tower-free, so both trophies inherit them
> (DD4).**

**The corollary it names:** the trophy's two injections give an **ambient
bijection between the small types**, **discharging the step the set-theorist
reading currently leaves to the reader.** **It does NOT touch the 600-line
reverse bound, whose missing object is a code in `L`.**

## THE SOURCE, and it is delivered and green in the archive

`archive/src/2026-08-09-rud-route/L/Cardinal.lagda.md`:

- **`module CSB` at `:89`**, the construction;
- **`csb` at `:183-190`**: two injections give
  `Σ[ h ] (h injective × (∀ y → ∥ Σ[ x ] h x ≡ y ∥₁))`;
- **the block is about 105 lines**, and its own header at `:7` records that the
  installed library does NOT provide it, so it was proved **once for all
  carriers rather than once per consumer.**

**Take it for SHAPE and re-derive every line** (DD18, C-44). **That route
retired: its carrier and its predicates differ, and C-41 governs its retired
names.** **Say explicitly what does NOT transfer.**

## THE RULING YOU MUST NOT RE-OPEN

**The two routes ruled OPPOSITE ways on the same fork and `[LJ-1.353]` measured
why both are sound:**

- **the retired scope gate** ruled equinumerosity as「there exists a bijection」,
  **to avoid a per-consumer CSB obligation**
  (`archive/src/2026-08-09-rud-route/L/CardinalPredicates.lagda.md:10`);
- **`[LJ-1.323]`** ruled mutual injections, **to avoid an internal CSB**.

> **The rulings disagree because the PACKAGINGS differ, and each is sound at its
> own.** **Recommendation: KEEP the ruling.**

**So do not change `src/L/GCH.lagda.md`.** **You are adding an ambient theorem
and a corollary, not restating a trophy.**

## THE ABORT CRITERION (D-1)

- **BOTH LAND GREEN.** Report the port's lines, the corollary, the check time
  past any cache, and every consumer. STOP.
- **THE PORT DOES NOT TRANSFER.** **Name what differs at `file:line` and price
  it.** The archived carrier is not this one.
- **THE COROLLARY NEEDS SOMETHING UNDELIVERED.** **Say what.** It should need
  only `csb` and the trophy's own two injections.
- **A WALL.** **C-58: replace a numeral pattern-match split with the library
  eliminator before bisecting the mathematics.** **C-55: do not fold telescopes
  into records.**

## CONSTRAINTS

- **You MAY create a new master under `src/V/` and edit nothing else in `src/`.**
  **Do NOT touch `src/L/GCH.lagda.md`.** If a consumer forces another edit, say
  so BEFORE making it.
- **A new master is trilingual-lite: `src/` is `en` + `zh`, MEASURED** (96
  masters, zero carry `ja`; `Makefile:29` reads `LANGS := en,zh`). **Write both.**
  **If you need a term rendering `dev/glossary.toml` lacks, STOP and name it:
  DD19's pipeline is two agents and it is not yours.**
- **Never commit, never push**, never `git checkout .`, `git stash`,
  `git reset --hard` or `git clean`. **Do not run `make check`; I run it.**
- **COUNT THE AGDA SLOTS** before every invocation, exactly:
  `ps aux | awk '/libexec.*bin\/agda/ && !/awk/' | wc -l`. **Both obvious
  alternatives OVER-COUNT, MEASURED.**
- **ONE agda process, `GHCRTS="-A64m -I0 -M8g"`, cap NEVER raised.** **Report
  the empty-file floor beside any seconds figure** (C-53 as extended).
- **RUN A NEGATIVE CONTROL that MEASURES.**
- **Create `agents/tasks/LJ-1-355/lj-1.355-report.md` in your FIRST five
  minutes** (C-22).
- Run `.venv/bin/python scripts/gate/lint-prose.py --check`,
  `lint-agda.py --check` and `scripts/site/weave-i18n.py --check`. **No em
  dash.**
- Evidence is `file:line`. **Your REPORT is ASD-STE100; the MASTER's prose is
  not.** Mark every negative **MEASURED** or **INFERRED**.

## THE PREMISE OF MINE MOST LIKELY TO BE WRONG

**Eleven of my last twenty-five briefs carried a claim an agent measured FALSE,
and this task exists because the owner caught one an hour ago.** **The one at
risk: 「about 100 lines」.** **That is `[LJ-1.353]`'s figure against an archived
block of about 105, and P-l says a judgement at one site is a hypothesis at
another: the archived carrier is not `src/V/`'s.**

## THE RULES

**DD18** is why this task exists: **survey the archive BEFORE pricing, not
after.** **C-41**: a retired name must still resolve. **C-44, C-42, C-45, C-53,
C-55, C-58, D-10, P-l, P-k.** **C-12, C-22, C-32, C-36, C-39, C-40.** I-5.
**D-1, D-26. DD0, DD4, DD8, DD9, DD19, DD23, DD24.**

Run `.venv/bin/python scripts/dispatch/rules.py --for build` and read every
statement, opening the full entry for any law you act on.

## DD4

**Maximize the code the two proofs share, and write it generic.** One rule, two
ends, no metric and no checker. **NAME YOUR AXIS** (C-46), fixed at
`scripts/measure/ledger.py:50`.

**`[LJ-1.353]` measured that BOTH pieces are tower-free, so both trophies
inherit them.** **That is a rare unambiguous DD4 win: confirm it, and report
the closure for both ends**, noting `dev/ledger.toml:204`: the GCH closure is
read from a STATEMENT whose proof is not wired, so it UNDERSTATES.

## ARCHIVE (DD18)

- **`archive/src/2026-08-09-rud-route/L/Cardinal.lagda.md:7`, `:89`, `:183-190`,
  read the CSB block WHOLE.** It is your source.
- **`archive/src/2026-08-09-rud-route/L/CardinalPredicates.lagda.md:10` and
  `:23`**, the scope gate's ruling on bijection against mutual injections.
- **`archive/dev/JOURNAL-archived.md:1370` and `:1377`**, the trap that ruling
  avoided.
- **`archive/dev/TASKS-archived.md`**, taking SHAPE and never a claim.

**Return an ARCHIVE USED section naming ONE line read per archived file.**
**Cite archived CODE and not only the retired route's records: a checker now
reports that split and my last ten briefs failed it.**

## LITERATURE (DD18)

**`dev/literature/truncation-and-selection.md`**, for the HoTT Book's cardinal
inequality as a truncated injection. **Say in one line whether the corollary's
surjectivity being truncated matters to the set-theorist reading.** Return a
**LITERATURE USED** section.

## SCOPE (read)

`archive/src/2026-08-09-rud-route/L/Cardinal.lagda.md:89-190` FIRST, whole.

## SCOPE (write)

A new master under `src/V/`, and `agents/tasks/LJ-1-355/`.

## RETURN

**Lead with ONE line: does the port land green, and at how many lines against
the archived 105.** Then the corollary. Then what did NOT transfer. Then every
consumer. Then the closure for both ends. Then your negative control. **Mark
every negative MEASURED or INFERRED.**
