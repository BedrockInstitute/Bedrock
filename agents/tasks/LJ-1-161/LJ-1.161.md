# LJ-1.161: gate the transfer half of `CrossOut`

tier: opus (version `override`, set 2026-08-13; the head for every case is in
`scripts/dispatch_policy.py`, which is the only place the tables live)

## GOAL

**`[LJ-1.160]` bypassed the wall that blocked `[LJ-1.7]` all phase.** It named
the next probe with its criterion fixed in advance and did not run it, because
running the BUILD needs the owner.

**This is the PROBE, not the build. DD8: gate a block before you fund it.**

## THE OBLIGATION, in `[LJ-1.160]`'s own words, unchanged

> **Instantiate `FOL.Absoluteness.Single` at `C.πX` and supply `TransferM` for
> ONE delivered `Σ₁` certificate, namely `Σ₁-cert`
> (`src/L/Condensation.lagda.md:269-270`). Report the in-fence line count for
> that ONE transfer.**
>
> - **GO** at or below 60 lines. Then `CrossOut`'s transfer half is cheap, and
>   the open term narrows to the ambient identification alone.
> - **NO-GO** if the certificate's formula does not sit at the image's carrier
>   without re-labelling. Then the relabelling kit
>   (`src/FOL/Manipulation/Bounding.lagda.md:146`) enters the price, and the
>   archive's `Transport` at `:260-297` is the delivered comparable.

**Do not move that criterion after you see a number.** `[LJ-1.60]`'s own PLAN
row reads 「NO-GO on a criterion I wrote wrong」.

## WHY IT MATTERS, in the phase's terms

`[LJ-1.7]` is STRUCTURE ONLY because `levelIn` and `cover` are hypotheses.
`[LJ-1.8]`, the trophy, needs `[LJ-1.7]` whole.

**`[LJ-1.160]` MEASURED that both hypotheses close in 16 in-fence lines from a
crossing face at the collapse image, and that
`π (Lset m') ≡ Lset (π m')` appears nowhere in that route.** I re-ran its probe
myself: exit 0, 1.52 s.

**The debt did not vanish. It moved to three open facts: `CrossOut`,
`HasLevels`, `Covered`.** You measure the transfer half of the first.

## WHAT IS ALREADY DELIVERED, so you do not rebuild it

- **`C.πX-trans : isTrans πX`**, `src/V/Collapse.lagda.md:89`. I verified it. It
  is definitionally what `Single`'s third parameter wants.
- **The collapse isomorphism, BOTH directions**, `src/V/Collapse.lagda.md:203-206`,
  which `[LJ-1.160]` names as what `HasLevels` and `Covered` transport along.
- **`Σ₁-cert`**, `src/L/Condensation.lagda.md:269-270`. **This is the thing the
  archive lacked**, and its presence is why `[LJ-1.160]` calls the bypass real
  rather than a fantasy.

## THE ONE THING THAT WOULD MAKE THE RETURN WORTHLESS

**Report the line count for the ONE TRANSFER, not for the file.**
`[LJ-1.124]` was marked MEASURED FALSE on exactly that distinction, and
`[LJ-1.151]` was held to it. Exclude the OPTIONS header, the imports, the module
header and every comment, and give the file total separately.

## THE C-38 GUARD

**An interface nothing satisfies is a restatement, not a supply.** Instantiate
at the REAL `Σ₁-cert`, not at an abstract certificate. `[LJ-1.136]` nearly
shipped a vacuous probe and its own guard caught it.

## THE ABORT CRITERION, second half

- **GO or NO-GO on 60 lines**: report and STOP.
- **The relabelling kit is needed**: that is the NO-GO, and it is a complete
  answer. **Price it against the archive's `Transport` comparable and stop.**
- **The certificate cannot reach the image's carrier at all**: **STOP AND SAY
  SO.** That would put the wall back and it is the most valuable negative
  available here.
- **Anything walls**: STOP, report it. **Never raise the cap.**

## WHAT YOU MUST NOT DO

- **Do not build `CrossOut`.** That is the chapter and it needs the owner's
  funding. **You gate its transfer half.**
- **Do not edit any master.**
- **Do not touch the three `*Agree` masters**: `[LJ-1.158]` landed there and
  `make check` is green on them.
- **A probe goes in `agents/tasks/LJ-1-161/`**, never in `src/`, tracked.
- **ONE agda process, `GHCRTS="-A64m -I0 -M8g"`, cap NEVER raised.**
- Never `src/Everything.lagda.md`. Never commit, never push, never
  `git checkout .`, `git stash`, `git reset --hard` or `git clean`.
- Do not run `make check`; I run it.

## THE CLASSIFICATION I WANT ON EVERY NEGATIVE

**MEASURED or INFERRED, in those words.**

## DD4

**Maximize the code the two proofs share, and write it generic.** One rule, two
ends, no metric and no checker.

**`[LJ-1.160]` MEASURED that the archived substrate is 73 percent shared and
that Devlin's own step is EITHER TOWER.** **Say whether your transfer is
template content or names the Def tower.**

## ARCHIVE (DD18)

**`[LJ-1.157]` measured that 37 of 61 live briefs cited no archive at all, and
`[LJ-1.160]` then found the phase's bypass inside one. This section is real.**

- **`archive/src/2026-08-09-rud-route/L/Condensation.lagda.md:160-257`**, the
  crossing face and `module Assembly`, and **`:260-297`, `Transport`, which is
  the NO-GO branch's delivered comparable.** Read both.
- **`agents/tasks/archive/LJ-1-1/lj-1.1-recon.md:241`**, which marked that
  master ADAPTABLE IN SHAPE ONLY and listed `CrossOut`, `HasLevels` and
  `Covered` by name, three phases before anybody used it.
- **Take SHAPE, never a claim.** `[LJ-1.11]` ruled that route's condensation
  target classically FALSE, and `[LJ-1.160]` explains why that kills the
  instance and not the derivation.
- `agents/tasks/LJ-1-160/lj-1.160-report.md` and `ProbeLJ1160A.agda`, read
  WHOLE.
- **`dev/LESSONS.md` C-38 as extended, D-1, P-l, C-36**, read WHOLE.

Return an **ARCHIVE USED** section at `file:line`.

## LITERATURE (DD18)

`dev/literature/devlin-II5.md:102-106`, which `[LJ-1.160]` cites for Devlin
working at the transitive collapse. **Say what he transports and how.** Return
a **LITERATURE USED** section.

## SCOPE (read)

`agents/tasks/LJ-1-160/ProbeLJ1160A.agda` FIRST, then
`src/L/Condensation.lagda.md:260-300`, then `src/FOL/Absoluteness.lagda.md`.

## SCOPE (write)

`agents/tasks/LJ-1-161/` only. **No master.**

## MANDATORY RULES

Run `.venv/bin/python scripts/rules.py --for probe` and read every statement.

- **D-1.** The abort criterion fixed BEFORE the run.
- **C-38 as extended.** Instantiate at the real certificate.
- **DD8, P-l, P-y, C-12, C-22, C-36, C-39, C-40.**
- **D-10, D-26, D-29, D-30. C-31, C-32, C-33, C-34, C-37. I-5.**

## CONSTRAINTS

- Count with `.venv/bin/python scripts/ledger.py`.
- Run `scripts/lint-prose.py --check` and `scripts/lint-agda.py --check`.
- DD23 freezes mathematical prose.
- Evidence is `file:line`. Write ASD-STE100.

## RETURN

**Lead with GO or NO-GO against 60 lines, and the count for the ONE TRANSFER
with what you excluded.** Then what remains open in `CrossOut` after it. Then
whether `HasLevels` and `Covered` look the same or different. Then the DD4
answer. **Mark every negative MEASURED or INFERRED.**
