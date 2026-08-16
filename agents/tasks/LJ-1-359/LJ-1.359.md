# LJ-1.359: land the CSB corollary at the trophy's own `InjL`

tier: pi (pi-subagent-mode), model `glm-5.3`. **I ran
`scripts/dispatch/dispatch_policy.py` before writing this line and took the
head it gave.** Agda.

## WHAT THIS IS

**`[LJ-1.355]` landed `src/V/CantorBernstein.lagda.md` today**, 118 lines,
exit 0 in 1.39 s, wired into the catalog and committed at `c370161`. **It
proved the L-side instantiation green in a probe and was forbidden from
landing it.** **You land it.**

**The mathematics is done and MEASURED. This is an assembly task.** **If it
turns into mathematics, that is a finding and you should say so.**

## THE RECIPE, verbatim from `[LJ-1.355]`'s report section 4

**About 15 code lines, MEASURED green at
`agents/tasks/LJ-1-355/InstProbe.agda`, 1.45 s against a 0.62 s floor:**

- **`setPL`, 2 lines**, through the exported `small-set`;
- **`readL`, 6 lines**, the delivered `Small` readback applied to the four
  `InjCode` conjuncts, `src/L/Coding/Injection.lagda.md:103`;
- **one `module MI = MutualInj ...` application, 2 lines**;
- **`csb-corollary = MI.∃bijection`, 5 lines of statement.**

**It consumes `InjL` from `src/L/GCH.lagda.md:38` WITHOUT editing that file.**
**Read `InstProbe.agda` FIRST and re-derive every line** (C-44); a probe is
evidence, never proof, and its line numbers have not been re-checked since it
was written.

## MY RULING ON THE SITE, which `[LJ-1.355]` left to me

**A NEW MASTER under `src/L/`.** **NOT the tail of `src/L/GCH.lagda.md` and
NOT `src/L/Cardinal.lagda.md`.** Two reasons, both structural:

- **`Cardinal.lagda.md` cannot host it: the corollary needs `InjL`, which
  lives in `GCH.lagda.md`, and `GCH.lagda.md` imports `Cardinal`.** That is a
  cycle. **Verify this yourself before you accept it.**
- **`GCH.lagda.md` stays a PURE STATEMENT.** `[LJ-1.323]` restated the trophy
  so that it carries no unsupplied hypothesis and no proof obligation. **A
  corollary in the same file erodes that.**

**Name the new master yourself and say why in your report.** **If you find a
third site that is better, take it and give the evidence; my ruling is a
ruling on structure, not on the name.**

## THE ABORT CRITERION (D-1)

- **IT LANDS GREEN.** Report lines, seconds past the floor, every consumer,
  and the closure for both ends. STOP.
- **THE PROBE DOES NOT TRANSFER.** **P-l: a judgement at one site is a
  hypothesis at another, and a probe file is a different site from a master.**
  **Name what differs at `file:line` and price it.**
- **IT NEEDS SOMETHING UNDELIVERED.** **Say what.** It should need only
  `V.CantorBernstein`, `InjL`, and the `Small` readback.
- **A WALL.** **C-58: replace a numeral pattern-match split with the library
  eliminator before bisecting the mathematics.** **C-55: do not fold
  telescopes into records.**

## CONSTRAINTS

- **You MAY create ONE new master under `src/L/`.** **Do NOT edit
  `src/L/GCH.lagda.md`, `src/L/Cardinal.lagda.md`, or
  `src/V/CantorBernstein.lagda.md`.** **NEVER touch `src/Everything.lagda.md`;
  I wire it after auditing your work.** If a consumer forces another edit, say
  so BEFORE making it.
- **`src/` is bilingual, `en` + `zh`, MEASURED** (`Makefile:29` reads
  `LANGS := en,zh`; 97 masters carry no `<!--ja-->`). **Write both, and no
  Japanese.** **If you need a term rendering `dev/glossary.toml` lacks, STOP
  and name it: DD19's pipeline is two agents and it is not yours.**
- **`[LJ-1.358]` is LIVE and writes only in `agents/tasks/LJ-1-358/`.** No
  collision, and it holds no Agda slot.
- **COUNT THE AGDA SLOTS** before every invocation, exactly:
  `ps aux | awk '/libexec.*bin\/agda/ && !/awk/' | wc -l`. **Both obvious
  alternatives OVER-COUNT, MEASURED.**
- **ONE agda process, `GHCRTS="-A64m -I0 -M8g"`, cap NEVER raised.** **Report
  the empty-file floor beside any seconds figure** (C-53 as extended).
- **RUN A NEGATIVE CONTROL that MEASURES.** `[LJ-1.355]`'s standard: swap two
  components of one tuple and show Agda refuses with exit 42 naming the
  expected type. **A green run on a new file proves nothing until you have
  seen the file go red.**
- **Never commit, never push**, never `git checkout .`, `git stash`,
  `git reset --hard` or `git clean`. **Do not run `make check`; I run it.**
- **Create `agents/tasks/LJ-1-359/lj-1.359-report.md` in your FIRST five
  minutes** (C-22).
- Run `.venv/bin/python scripts/gate/lint-prose.py --check`,
  `lint-agda.py --check` and `scripts/site/weave-i18n.py --check`. **No em
  dash.** Evidence is `file:line`. **Your REPORT is ASD-STE100; the MASTER's
  prose is not.** Mark every negative **MEASURED** or **INFERRED**.

## THE PREMISE OF MINE MOST LIKELY TO BE WRONG

**Eleven of my last twenty-eight briefs carried a claim an agent measured
FALSE.** **The one at risk: 「about 15 code lines」.** **That is a probe
figure, and `[LJ-1.355]` itself measured that abstracting its construction to
a master cost +2 lines over the archived original.** **A probe imports
freely; a master pays for its own header, its OPTIONS line and its bilingual
prose.** **Report the real number without apology; the estimate is mine and it
is cheap.**

## THE RULES

**C-44: re-derive every cited line.** **C-45: `exit 0` is not a supply.**
**P-l, D-10, C-42, C-53, C-55, C-58, P-k.** **C-12, C-22, C-32, C-36, C-39,
C-40.** I-5. **D-1, D-26.** **DD0, DD4, DD8, DD9, DD19, DD23, DD24.**

Run `.venv/bin/python scripts/dispatch/rules.py --for build` and read every
statement, opening the full entry for any law you act on.

## DD4

**Maximize the code the two proofs share, and write it generic.** One rule,
two ends, no metric and no checker. **NAME YOUR AXIS** (C-46), fixed at
`scripts/measure/ledger.py:50`.

**This task is where a rare DD4 win gets SPENT, and it is worth understanding
before you write.** **`[LJ-1.355]` MEASURED that `V.CantorBernstein` imports
`Base.Prelude`, `Base.Classical` and cubical only: no `FOL`, no `V.*` chapter,
no `L.*`.** **It is pure substrate and BOTH towers can import it.** **Your
master is the opposite: it is L-side by necessity, because `InjL` is.** **So
say honestly which half of what you write is generic and which is not, and
whether the L-side half could be written at a shape the AC end could also
read.** **`Small` gets its first consumer outside its own master here**
(`[LJ-1.353]` section 1 recorded it delivered but unconsumed).

**Report the closure for BOTH ends after your landing**, noting
`dev/ledger.toml:200-206`: the GCH closure is read from a STATEMENT whose
proof is not wired, so it UNDERSTATES by about 1,027 lines. **Your master is
the first thing to pull `V.CantorBernstein` into the GCH closure.**

## ARCHIVE (DD18)

**A live `agents/tasks/` path is NOT an archive citation, MEASURED by
`[LJ-1.357]` today** (`scripts/gate/check-archive-cited.py:26-27`:「A section
that names only live `agents/tasks/` directories is THE DRIFT」). **The four
corpora below are the archives. Cite archived CODE, not only records.**

- **`archive/src/2026-08-09-rud-route/L/Cardinal.lagda.md:89-190`**, the CSB
  the port came from. **Read the CONSUMER end: how did the retired route
  actually use it at the cardinal level?** That is your closest comparable.
- **`archive/src/2026-08-09-rud-route/L/CardinalPredicates.lagda.md:10`**, the
  retired route's OPPOSITE ruling: equinumerosity as a bijection, precisely to
  avoid a per-consumer CSB obligation. **Your corollary is the bridge between
  the two packagings. Say in one line whether the retired ruling's worry
  materialises here.**
- **`archive/dev/TASKS-archived.md:116`**, the T81 row. **Note: the story that
  `[LJ-1.107]` failed to survey is FALSE, measured by `[LJ-1.357]`, and I
  repaired the checker that told it. Do not repeat it.**
- **`archive/dev/JOURNAL-archived.md:1368-1380`**, the trap the bijection
  ruling avoided.

**Return an ARCHIVE USED section naming ONE line read per archived file, with
WHY NOT for anything you decline.**

## LITERATURE (DD18)

**`dev/literature/truncation-and-selection.md`**, for the HoTT Book's cardinal
inequality as a truncated injection. **Say in ONE line whether the corollary's
surjectivity being truncated changes what a set-theorist may conclude.** That
is the whole reason this corollary exists. Return a **LITERATURE USED**
section.

## SCOPE (read)

`agents/tasks/LJ-1-355/InstProbe.agda` FIRST, WHOLE. It is the recipe and it
is already green.

## SCOPE (write)

ONE new master under `src/L/`, and `agents/tasks/LJ-1-359/`.

## RETURN

**Lead with ONE line: does it land green, at how many lines against the
probe's 15.** Then the site you chose and why. Then what did NOT transfer from
the probe. Then your negative control, with the exit code and the type Agda
named. Then every consumer. Then the closure for both ends. **Mark every
negative MEASURED or INFERRED.**
