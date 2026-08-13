# LJ-1.164: move `elem-down` out of `Co`, which is a pure move

tier: opus (version `override`, set 2026-08-13; the head for every case is in
`scripts/dispatch_policy.py`, which is the only place the tables live)

## GOAL

**`[LJ-1.163]` MEASURED that `ElemDown` is already supplied and sits in a place
nobody who needs it can reach.** Move it. **Change no proof and write no line.**

## THE FINDING, and I verified every part

**The supply exists**, `src/L/BoundedSubset.lagda.md:1568-1569`:

```agda
elem-down : DR54.ElemDown
elem-down = HEDC.elem-down
```

**It sits inside `module Co`, `:1409-1412`, which itself takes `levelIn` and
`cover` as parameters:**

```agda
module Co
  (levelIn : (δ : S) → IsOrd δ → ⟨ δ ∈ˢ HS.C.πX ⟩ → ⟨ Lset δ ∈ˢ HS.C.πX ⟩)
  (cover : (y : S) → ⟨ y ∈ˢ HS.M ⟩ → ∥ ... ∥₁)
  where
```

**So anybody trying to PROVE `levelIn` and `cover` cannot reach `elem-down`.
That is the phase blocker, and it is a placement rather than mathematics.**

**Independence is MEASURED two ways by `[LJ-1.163]`:** a name sweep of
`:1426-1570` matches none of `levelIn`, `cover`, `Cn.` or `β`; and its BLOCK 1
rebuilds the same supply in a module where those names are not in scope at all.
Its probe is green in 2.9 s and I re-ran it: exit 0.

## WHY THIS IS ORDINARY WORK AND NOT AN ARCHITECTURE FORK

**It changes no proof, adds no line and removes no line.** The four definitions
it depends on are all bound ABOVE `Co`: `HED`, `HEDC` and `DR54` at
`:1560-1566`, and those in turn take only `lam`, `ordλ` and the three `UK`
fields.

**The tree decides whether that is true. If the move is not pure, Agda says so
and you STOP.**

## WHAT TO DO

1. **Move `elem-down`, and the three module aliases it needs, from inside `Co`
   to the scope directly above it**, so that a proof of `levelIn` or `cover` can
   use it.
2. **Leave a re-export inside `Co` if anything there used it**, so no consumer
   breaks. **`[LJ-1.163]` MEASURED that nothing uses it anywhere, which is C-35
   firing for the fourth time in this wing, so the re-export may be
   unnecessary. Check rather than assume.**
3. **Typecheck `src/L/BoundedSubset.lagda.md` and EVERY consumer.** C-40.
4. **Report the diff shape**: lines added, lines removed, and whether any line
   of PROOF changed.

## THE ABORT CRITERION, fixed BEFORE you start

- **The move is pure and the tree is green**: report the diff shape and STOP.
- **The move requires changing a proof line**: **STOP. Report exactly which
  line and why.** That would mean the dependence is real and `[LJ-1.163]`'s two
  measurements missed it, which is a finding worth more than the move.
- **A consumer goes RED**: STOP, report it. Do not repair it in the same pass.
- **Anything walls**: STOP with its wall-clock. **Never raise the cap.**

## THE WALL ALREADY MEASURED AT THIS EXACT SPOT

**`[LJ-1.163]` walled on `refl` identifying two module applications: 20:42.15,
RSS 2.07 GB against an 8 GB cap, so NO heap exhaustion.** It commented the
block per its own pre-fixed criterion and did not repair it (P-i).

**Do not try to prove the moved definition equals the old one by `refl`.** That
is the wall, it is measured, and the move does not need it.

## WHAT YOU MUST NOT DO

- **Do not change a proof.** This is a move.
- **Do not delete anything.** If a definition must stay for compatibility,
  leave it and say so.
- **Do not touch the three `*Agree` masters.**
- **Do not touch `src/L/Coding/Graph.lagda.md`**: 21 consumers are green on
  `[LJ-1.147]`'s seal.
- **A probe goes in `agents/tasks/LJ-1-164/`**, never in `src/`, tracked.
- **ONE agda process, `GHCRTS="-A64m -I0 -M8g"`, cap NEVER raised.**
- Never `src/Everything.lagda.md`. Never commit, never push, never
  `git checkout .`, `git stash`, `git reset --hard` or `git clean`.
- Do not run `make check`; I run it. **Run `agda` on the master and on each
  consumer.**

## THE CLASSIFICATION I WANT ON EVERY NEGATIVE

**MEASURED or INFERRED, in those words.**

## AFTER THE MOVE, and this is why it matters

**`[LJ-1.7]` is STRUCTURE ONLY because `levelIn` and `cover` are hypotheses.**
Once `elem-down` is reachable, the route `[LJ-1.160]` measured becomes
buildable: both hypotheses close in 16 in-fence lines from a crossing face at
the collapse image, and `CrossOut` is priced at 163.

**Say in your return what is now reachable that was not.** That sentence is the
deliverable as much as the diff is.

## DD4

**`[LJ-1.163]` MEASURED that 158 of the 242 delivered lines name no tower and
that the fork point is ONE line, `:670`.** **A move does not change that. Say
whether the moved definition lands above or below that fork.**

## ARCHIVE (DD18)

- **`archive/src/2026-08-09-rud-route/L/Hull.lagda.md:248-249` and `:396-398`**,
  which `[LJ-1.163]` found hold a BUILT Tarski-Vaught theorem and
  `hull-closed`, not hypotheses. **Say whether the archive placed its
  elementarity above or below its own condensation parameters.** That is the
  same question you are answering, already answered once.
- **Take SHAPE, never a claim.** `[LJ-1.11]` ruled that route's condensation
  target classically FALSE.
- `agents/tasks/LJ-1-163/lj-1.163-report.md`, read WHOLE.
- **`dev/LESSONS.md` C-35, C-40, P-i, C-36**, read WHOLE.

Return an **ARCHIVE USED** section at `file:line`.

## LITERATURE (DD18)

**Nothing in the literature governs module placement. Say so in one line.**

## SCOPE (read)

`src/L/BoundedSubset.lagda.md:1400-1600` FIRST, then
`agents/tasks/LJ-1-163/lj-1.163-report.md`.

## SCOPE (write)

`src/L/BoundedSubset.lagda.md` ONLY. Your report and probes are
`agents/tasks/LJ-1-164/`.

## MANDATORY RULES

Run `.venv/bin/python scripts/rules.py --for rewrite` and read every statement.

- **C-40.** Verify the CONSUMERS. **I committed three RED trees in one day for
  omitting this.**
- **C-35.** A delivered block with no consumer is untested. **`elem-down` is
  the fourth in this wing.**
- **P-i.** No surgery on a walling term.
- **C-12, C-22, C-36, C-39, D-10, D-26, D-29, D-30.**
- **C-31, C-32, C-33, C-34, C-37. I-5.**

## CONSTRAINTS

- Count with `.venv/bin/python scripts/ledger.py`.
- Run `scripts/lint-prose.py --check` and `scripts/lint-agda.py --check`.
- DD23 freezes mathematical prose. **Code comments are not prose; write them.**
- Evidence is `file:line`. Write ASD-STE100.

## RETURN

**Lead with whether the move was pure, and the diff shape.** Then every
consumer's verdict. Then what is now reachable that was not. Then whether the
re-export was needed. Then the DD4 answer. **Mark every negative MEASURED or
INFERRED.**
