# LJ-1.146: `levelIn` and `cover`, the root of the unconsumed chain

tier: opus (version `override`, set 2026-08-13; the head for every case is in
`scripts/dispatch_policy.py`, which is the only place the tables live)

## GOAL

**`levelIn` and `cover` have been unsupplied all phase, and `[LJ-1.144]` has
just shown they are the ROOT of the C-35 chain.** Price supplying them, or
prove they cannot be supplied on this route.

## WHY NOW, and the evidence arrived today

**`[LJ-1.144]`, 2026-08-13, MEASURED:** `LeafAgree` is imported by nothing and
`LevelHood` in `BoundedSubset` is consumed by nothing, so

> **C-35 is not local to the three masters. It runs from `levelIn`/`cover`
> down.**

**`[LJ-1.131]` excluded them from BOTH routes and left them owed in full**
(`agents/tasks/LJ-1-131/lj-1.131-report.md:402-406` and `:451`). So the A-prime
price of 705 lines does NOT contain them, and neither did Route B's.

**They are therefore the oldest open term in the wing and nobody has priced
them.** Every consumer-side chain in `Condensation.lagda.md` terminates in
something these two would supply.

## WHAT TO DO

1. **Find them and state what they ARE.** Their types, their sites, and what a
   supplier would have to produce. `file:line` for each.
2. **Say why they were never supplied.** Read the history: which task met them,
   what it said, and whether it was a wall or a deferral. **A deferral and a
   wall have different cures and the reports will say which.**
3. **Price the supply.** In in-fence lines and in cold seconds, one best-effort
   figure each with its basis named (DD8). **Name the widest unmeasured term
   and the probe that would measure it.**
4. **Then answer the question that decides funding: does the GCH trophy need
   them?** `[LJ-1.144]` found the chain above them is unconsumed. **If nothing
   above them is on the route to `L ⊨ GCH` stated in L, then supplying them
   buys a chain nobody uses, and the honest recommendation is to say so.**

## THE TRAP THIS WING HAS PAID FOR TWICE

**C-38 as extended:** a hypothesis is discharged when something SUPPLIES it. A
closure hypothesis about a bounding set must be CONDITIONAL. **An interface
that nothing instantiates is not a supply, it is a restatement**, and
`[LJ-1.136]` nearly shipped exactly that this afternoon before its own C-38
guard caught it.

**So if you price a supply, price the INSTANTIATION too, at a real site.**

## THE ABORT CRITERION

- **A price with a basis, and an answer on whether the trophy needs them**:
  report and STOP.
- **They cannot be supplied on this route**: **STOP AND SAY SO with the
  evidence.** That is the most valuable return available here, and it would
  decide the fate of the whole chain above them.
- **Nothing above them is on the trophy's route**: report that, because it
  changes the question from 「how much」 to 「why at all」.
- **Anything walls**: STOP, report it with its seconds.

## WHAT YOU MUST NOT DO

- **Do not edit any master.** This is a recon and a price.
- **Do not touch `src/L/Condensation.lagda.md`**: `[LJ-1.145]` owns it and is
  measuring it RIGHT NOW.
- **Do not touch the three `*Agree` masters.**
- **Do not touch `src/ProbeLJ1134A.agda` or `src/ProbeLJ1136*.agda`.**
- **A probe goes in `agents/tasks/LJ-1-146/`, beside this brief**, never in
  `src/`, tracked, never deleted. **That rule changed today: read `AGENTS.md`
  and `dev/LESSONS.md` D-1 fresh, not from any report.**
- **ONE agda process, `GHCRTS="-A64m -I0 -M8g"`, cap never raised.**
  **`[LJ-1.145]` is running Agda and is MEASURING SECONDS.** Keep your runs
  small, report the load beside every figure, and **say plainly that your
  seconds are upper bounds taken on a busy machine.**
- Never `src/Everything.lagda.md`. Never commit, never push, never
  `git checkout .`, `git stash`, `git reset --hard` or `git clean`.
- Do not run `make check`; I run it.

## THE CLASSIFICATION I WANT ON EVERY NEGATIVE

**MEASURED or INFERRED, in those words.**

## DD4

**Maximize the code the two proofs share, and write it generic.** One rule, two
ends, no metric and no checker, so it is stated in every brief and answered in
every return. **Do `levelIn` and `cover` serve both towers or one? Say which,
because it doubles or halves what a supply is worth.**

## ARCHIVE (DD18)

- **`agents/tasks/LJ-1-144/lj-1.144-report.md`**, read WHOLE. The finding that
  sent you.
- **`agents/tasks/LJ-1-131/lj-1.131-report.md:402-406` and `:451`**, where they
  were excluded from both routes.
- `agents/tasks/archive/LJ-1-57/`, `LJ-1-112/`, `LJ-1-113/`: the eleven-name
  repair arc and the 28 pieces of consumer-side supply.
- **`dev/LESSONS.md` C-35, C-38 as extended, D-30, P-l, C-36**, read WHOLE.

Return an **ARCHIVE USED** section at `file:line`.

## LITERATURE (DD18)

`dev/literature/devlin-II5.md`. **Say what Devlin's own proof needs at this
point, and whether `levelIn` and `cover` are his content or our encoding's.**
Return a **LITERATURE USED** section.

## SCOPE (read)

Search the tree for both names FIRST, then
`agents/tasks/LJ-1-144/lj-1.144-report.md`.

## SCOPE (write)

`agents/tasks/LJ-1-146/` only. **No master.**

## MANDATORY RULES

Run `.venv/bin/python scripts/rules.py --for recon` and `--for probe`.

- **C-35, C-38 as extended, D-30, DD8, D-1, P-l, P-x, C-12, C-22, C-36, C-39,
  C-40.**
- **C-31, C-32, C-33, C-34, C-37, D-10, D-26, D-29. I-5.**

## CONSTRAINTS

- Count with `.venv/bin/python scripts/ledger.py`.
- Run `scripts/lint-prose.py --check` and `scripts/lint-agda.py --check`.
- DD23 freezes mathematical prose.
- Evidence is `file:line`. Write ASD-STE100.

## RETURN

**Lead with what they are and whether the trophy needs them.** Then why they
were never supplied, wall or deferral, with the evidence. Then the price and
its basis. Then the widest unmeasured term and its probe. Then the DD4 answer.
**Mark every negative MEASURED or INFERRED.**
