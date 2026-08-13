# LJ-1.160: read the 845-line level substrate against `levelIn` and `cover`

tier: opus (version `override`, set 2026-08-13; the head for every case is in
`scripts/dispatch_policy.py`, which is the only place the tables live)

## GOAL

**`[LJ-1.157]` measured that three tasks priced `levelIn` and `cover` without
ever naming an 845-line archived substrate that the route's OWN recon had
marked ADAPTABLE.** Read it, and say what it changes.

**This is the LJ-1 phase's blocker.** `[LJ-1.7]` is STRUCTURE ONLY because
those two are hypotheses; `[LJ-1.8]`, the trophy, needs `[LJ-1.7]` whole.

## THE MISS, MEASURED

`agents/tasks/LJ-1-157/lj-1.157-report.md:30`, finding M3:

> the level-story substrate, **845 in-fence**:
> `L/LevelFormula.lagda.md`, `L/LevelKit.lagda.md`,
> `L/Condensation.lagda.md:142,:260,:297,:791`,
> `L/InitialSegment.lagda.md:155,:234`
>
> not named by `LJ-1.121.md:127-143`, `LJ-1.123.md:119-133`,
> `LJ-1.146.md:93-104`
>
> **a price anchor today; a whole chapter when the wall is funded**

**I sized the three files myself**, under
`archive/src/2026-08-09-rud-route/L/`:

| | in-fence |
|---|---:|
| `LevelKit.lagda.md` | **587** |
| `LevelFormula.lagda.md` | 258 |
| `InitialSegment.lagda.md` | 114 |

**`LevelKit` at `:98` is `module LevelKit (u : V ℓ) (utr : isTransV u)`, and
at `:562` it carries a successor atom's COVERAGE body.** That is the same word
as `cover`.

## WHAT IS OWED HERE, and it is a price and a route

`[LJ-1.146]` priced `levelIn` and `cover` at **about 1.0k lines, band 0.6k to
1.5k**, from a certificate remainder plus an instantiation term, **with NO
delivered comparable.** `[LJ-1.157]` calls the loss today 「price confidence」
and warns it converts to a full rebuild when the wall is funded.

**`[LJ-1.151]` then MEASURED the instantiation half at 21 lines for one fact,
GO**, and MEASURED that the wall is SEPARABLE from it: neither of its probes
names the projection, the collapse or the hull.

**So the open half is the certificate side, and that is exactly what these 845
lines might anchor.**

## THE WALL, which you are NOT funded to break

`levelIn`'s deepest step is `π (Lset m') ≡ Lset (π m')`.
`agents/tasks/archive/LJ-1-51/lj-1.51-report.md:135` titles its section 「the
wall, and the term I cannot write」, and `[LJ-1.121]` reached the same term by
a different method and stopped. **Four dispatches went around it. Nobody has
ever been funded to build that chapter.**

**Your job is to say whether the archive changes that**, not to break it.

## WHAT TO DO

1. **Read `LevelKit.lagda.md` WHOLE**, then `LevelFormula.lagda.md`, then the
   named lines of `InitialSegment.lagda.md` and the archived
   `Condensation.lagda.md`.
2. **Say what it actually PROVES**, in the retired route's own terms, and what
   it assumes.
3. **Then the two questions that decide the phase:**
   - **Does it hold anything that would DISCHARGE `levelIn` or `cover`, or an
     analogue of them?** If yes, name it at `file:line` and say what would have
     to change to port it.
   - **Does it hold the term `[LJ-1.51]` could not write, or something that
     routes around it?** **That is the finding that would unblock the phase.**
4. **Re-price** `[LJ-1.146]`'s 1.0k band against this comparable, one
   best-effort figure with its basis (DD8), and say whether the band tightens,
   holds or widens.

## THE STANDING RULE, and it is the one that makes this hard

**Take SHAPE from the archive, NEVER a claim.** `[LJ-1.11]` ruled the retired
route's condensation target classically FALSE, so **a theorem there is not a
theorem here.** And the tower is different: that route ran on rud, this one on
the Def tower.

**So say, for everything you take: what transfers, what does not, and why.** A
finding that only says 「this exists over there」 is half a finding, and
`[LJ-1.157]` was held to the same standard.

## THE ABORT CRITERION

- **You can re-price with a delivered comparable**: report it and STOP.
- **The substrate discharges one of the two, or routes around the wall**:
  **STOP AND SAY SO FIRST.** That unblocks `[LJ-1.7]` and it is the most
  valuable thing available in this phase.
- **The substrate is rud-specific and transfers nothing**: **say so plainly,
  MEASURED.** Then `[LJ-1.146]`'s band stands unanchored and the owner knows
  the wall must be funded blind. **That is a complete answer.**
- **Anything walls**: STOP, report it.

## WHAT YOU MUST NOT DO

- **Do not edit any master.** This is a recon.
- **Do not try to break the wall.** If you see how, say so and stop; that is a
  build and it needs the owner's funding.
- **Do not touch the three `*Agree` masters**: `[LJ-1.158]` landed there an
  hour ago and they are green.
- **A probe goes in `agents/tasks/LJ-1-160/`**, never in `src/`, tracked.
- **ONE agda process, `GHCRTS="-A64m -I0 -M8g"`, cap NEVER raised.** A sibling
  may run Agda. **Your figures are lines and shape, not seconds, so a busy
  machine costs you only time. Say so.**
- Never `src/Everything.lagda.md`. Never commit, never push, never
  `git checkout .`, `git stash`, `git reset --hard` or `git clean`.
- Do not run `make check`; I run it.

## THE CLASSIFICATION I WANT ON EVERY NEGATIVE

**MEASURED or INFERRED, in those words.** 「This transfers」 is INFERRED until
something elaborates.

## DD4

**Maximize the code the two proofs share, and write it generic.** One rule, two
ends, no metric and no checker.

**`[LJ-1.146]` settled that `levelIn` and `cover` are both towers in SHAPE and
one tower in INSTANCE, with the per-tower half the LARGER half of the bill.
`[LJ-1.151]` and `[LJ-1.153]` then corrected that from the other end: the
repaired statements are 100 percent template.** **This archive is rud-tower
code. Say which correction it supports.**

## ARCHIVE (DD18)

**This task IS the archive section, and it exists because that section decayed.**

- **`archive/src/2026-08-09-rud-route/L/LevelKit.lagda.md`**, 587 in-fence,
  read WHOLE. **`:98` and `:562` are the entry points I found.**
- **`archive/src/2026-08-09-rud-route/L/LevelFormula.lagda.md`**, 258 in-fence.
- `archive/src/2026-08-09-rud-route/L/InitialSegment.lagda.md:155,:234` and
  `L/Condensation.lagda.md:142,:260,:297,:791`.
- **`agents/tasks/archive/LJ-1-1/lj-1.1-recon.md`**, which marked this
  substrate ADAPTABLE. **Find that line and quote it.**
- `agents/tasks/LJ-1-146/lj-1.146-report.md` and
  `agents/tasks/LJ-1-151/lj-1.151-report.md`, read WHOLE.
- `agents/tasks/archive/LJ-1-51/lj-1.51-report.md:135`, the wall.
- **`dev/LESSONS.md` P-l, C-35, C-38 as extended, C-36**, read WHOLE.

Return an **ARCHIVE USED** section at `file:line`.

## LITERATURE (DD18)

`dev/literature/devlin-II5.md`. **`[LJ-1.146]` found `levelIn` and `cover` are
Devlin's content rather than our encoding's. Confirm or refute, and say whether
the archived substrate follows Devlin or departs from him.** Return a
**LITERATURE USED** section.

## SCOPE (read)

`archive/src/2026-08-09-rud-route/L/LevelKit.lagda.md` FIRST, whole.

## SCOPE (write)

`agents/tasks/LJ-1-160/` only. **No master.**

## MANDATORY RULES

Run `.venv/bin/python scripts/rules.py --for recon` and read every statement.

- **DD18.** The archive survey. **This task is its repair.**
- **P-l.** A price from a comparable elsewhere is a hypothesis, **and a
  comparable on a DIFFERENT TOWER is a weaker one still.**
- **C-35, C-36, C-38 as extended, C-12, C-22, C-39, C-40.**
- **DD8, DD13, D-1, D-10, D-26, D-29, D-30. C-31, C-32, C-33, C-34, C-37. I-5.**

## CONSTRAINTS

- Count with `.venv/bin/python scripts/ledger.py`.
- Run `scripts/lint-prose.py --check` on anything you write.
- DD23 freezes mathematical prose.
- Evidence is `file:line`. Write ASD-STE100.

## RETURN

**Lead with whether the substrate unblocks `[LJ-1.7]`, in one sentence.** Then
what it proves and assumes. Then the two questions. Then the re-priced band
with its basis. Then what transfers and what does not, item by item. Then the
DD4 answer. **Mark every negative MEASURED or INFERRED.**
