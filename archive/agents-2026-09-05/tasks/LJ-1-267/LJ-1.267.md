# LJ-1.267: re-derive `[LJ-1.7]`'s residue, because the tree moved under it today

tier: pi (deepseek-subagent-mode), **model `deepseek-v4-pro`**. **This task runs
NO Agda and holds no slot, so the model rule would give flash. I override it
and record why: the task READS Agda telescopes and judges which parameters are
now supplied, which the `--agda` flag cannot see.** The clock selected the
mode.

## GOAL

**`[LJ-1.7]` is phase 1's blocking row and its residue has not been re-derived
since `[LJ-1.251]`, which was fourteen dispatches ago. The tree moved a great
deal under it today.**

**What moved, all MEASURED and all green:**

| what | where |
|---|---|
| the join `envSetK`, and `sucK` does not wall | `agents/tasks/LJ-1-254/` |
| five `envK-*`, collapsed to 67 lines from 85 | `agents/tasks/LJ-1-255/`, `LJ-1-257/` |
| four `envInK-*` and `someEnv` | `agents/tasks/LJ-1-257/` |
| twelve of fifteen val and sub fields | `agents/tasks/LJ-1-258/` |
| `envConsK` and the three `consK-*` | `agents/tasks/LJ-1-259/` |
| the finite-supremum merge, `finSetK` SUPPLIED | `agents/tasks/LJ-1-261/` |
| **the numeral premise, LANDED in three delivered records** | `[LJ-1.260]`, net +42, all masters green |
| **the three L-rows, LANDED in `src/L/Coding/Key.lagda.md`** | `[LJ-1.263]`, master green, re-runs import the master |

**So step 6's 28 fields are all reachable and two landings are in `src/`.**

**The question nobody has asked since: what does `[LJ-1.7]` still owe?**

## THE OBJECT TO RE-DERIVE

**`module Whole` at `agents/tasks/LJ-1-178/ProbeLJ1178A.agda:489-493` takes
SEVEN parameters:**

```agda
(el : A.Elementary) (fwd : IsoFwd) (bwd : IsoBwd)
(sl : StageLevels) (sc : StageCovered)
(s₁ : Σ₁ Cr.φP)
(amb : AmbientCross.AmbientRead P Ptr φ₀)
```

**For each of the seven, say: SUPPLIED, BUILT-not-supplied, or OPEN, with the
evidence at `file:line`.** **C-38 as extended: a hypothesis is discharged when
something SUPPLIES it, and BUILT is not SUPPLIED.**

**`el`, `fwd` and `bwd` have never been discussed in this phase's record. Start
with them: they may be the residue nobody has looked at.**

## WHAT THE RECORD SAYS TODAY, and every line of it is a claim to check

- **`amb`**: `[LJ-1.184]` supplied it, and `[LJ-1.242]` and `[LJ-1.243]`
  measured that supply CONDITIONAL on `q`, a telescope parameter nothing
  instantiates. **So `amb` is NOT supplied outright.**
- **`s₁`**: BUILT in shape, with a 2-line gap (`[LJ-1.225]`).
- **`sl` and `sc`**: `[LJ-1.237]` built them at 14 and 38 lines over `lh`, a
  parameter. **`[LJ-1.251]` measured `lh`'s supply IS step 6.**
- **`el`, `fwd`, `bwd`**: **nothing in this phase's record. That is the
  finding to look for.**

**C-44: every one of those bullets is a claim and I have re-derived only the
`amb` one.**

## THE ABORT CRITERION, fixed BEFORE the run (D-1)

- **THE RESIDUE IS SMALLER THAN THE RECORD SAYS.** Name what is now supplied
  and at `file:line`. **Then phase 1's blocking row moves and I say so.** STOP.
- **THE RESIDUE IS THE SAME SIZE.** Say so plainly. **Today's work then bought
  reachability and not discharge, and that is worth knowing before more is
  funded.**
- **THE RESIDUE IS LARGER.** **If `el`, `fwd` or `bwd` is an unpriced
  obligation, that is the most valuable outcome here.** **Name it and price it,
  or name the probe that would.**
- **A PARAMETER IS NOT WHAT ITS NAME SUGGESTS.** **`[LJ-1.243]` found a supply
  that relayed rather than discharged. Look for that shape in all seven.**

## WHAT YOU MUST NOT DO

- **DO NOT RUN AGDA.** A sibling holds an Agda slot and is measuring seconds.
- **Do not re-price step 6.** `[LJ-1.256]` settled it at about 255 plus about
  50, and `[LJ-1.258]` measured the marginal rate at 1 to 2 body lines per
  field.
- **Do not edit any master, brief or report.** **Write your own report and
  nothing else.** **I write the status screen.**
- **Do not touch `agents/tasks/LJ-1-266/` or `LJ-1-268/`.** Siblings are live.
- **Create your report file in your FIRST five minutes (C-22).**
- Never commit, never push, never `git checkout .`, `git stash`,
  `git reset --hard` or `git clean`.
- Do not run `make check`; the orchestrator runs it.

## EIGHT RULES THIS CHAIN EARNED

**`exit 0` IS NOT A SUPPLY** (C-45). **Audit the INSTANTIATION, never the
telescope. This task IS that law applied to seven parameters.**

**A CONDITIONAL SUPPLY RECORDED AS A SUPPLY is the failure that cost this
phase the most.** **`amb` read SUPPLIED in the status screen for a day.**

**DERIVE A FIGURE OR DO NOT WRITE IT** (C-44).

**SEARCH THE OPEN-WORK LIST BY CONTENT, NOT BY NAME.** **Ten dispatches
re-derived a price the plan already carried.**

**THE ARCHIVE BEARS UNTIL YOU OPEN IT.** **Three times this week.**

**A FAILED SUBSTITUTION IS NOT A PROOF OF IMPOSSIBILITY** (C-36).

**AN ESCAPE HATCH IS THE SHAPE A WRONG CHOICE HIDES IN** (C-43).

**CARRY A CLAIM'S QUALIFIER OR CARRY NEITHER.**

## THE CLASSIFICATION I WANT ON EVERY NEGATIVE

**MEASURED or INFERRED, in those words.**

## DD4

**Maximize the code the two proofs share, and write it generic.** One rule, two
ends, no metric and no checker.

**`[LJ-1.262]` measured that this phase mixes TWO AXES and no figure says
which: Devlin's Def-against-J, and the port's L-against-ambient.**

**So for each of the seven parameters, say which axis its tower status is on**,
or say the question does not apply. **That single labelling makes the phase's
DD4 accounting usable for the first time.**

## ARCHIVE (DD18)

- **`agents/tasks/LJ-1-178/ProbeLJ1178A.agda:486-505` and its report**, read
  WHOLE. **`module Whole` is the object.**
- **`agents/tasks/LJ-1-251/lj-1.251-report.md`**: the last re-derivation, and
  what it settled.
- `agents/tasks/LJ-1-243/`: the conditional supply and how it was found.
- `agents/tasks/LJ-1-254/` through `LJ-1-261/`: today's green work.
- `agents/tasks/LJ-1-260/` and `LJ-1-263/`: the two landings.
- **`src/L/BoundedSubset.lagda.md:1555-1621` and `src/L/Coding/Key.lagda.md`:
  read the source, never a report about it.**
- **`archive/dev/TASKS-archived.md` and `archive/src/2026-08-09-rud-route/`.**
  **The retired route had an elementarity obligation too. `el`, `fwd` and
  `bwd` may be named there. Take SHAPE from the archive, never a claim.**

**Return an ARCHIVE USED section naming ONE line read per archived file.**

## LITERATURE (DD18)

**`dev/literature/devlin-II5.md` splits II.5 into twelve rows, eight EITHER and
four PER-TOWER.** **Say which row each of the seven parameters sits on**, and
whether any has no row at all. Return a **LITERATURE USED** section.

## SCOPE (read)

`agents/tasks/LJ-1-178/ProbeLJ1178A.agda` FIRST, whole.

## SCOPE (write)

`agents/tasks/LJ-1-267/` only. **No master.**

## MANDATORY RULES

Run `.venv/bin/python scripts/rules.py --for recon` and read every statement.
**The tool prints `Full entry: dev/LESSONS.md:<line>` for every rule and says
THIS IS AN EXCERPT when it truncated. OPEN the full entry for any law you act
on.**

- **C-38 as extended.** **A hypothesis is discharged when something SUPPLIES
  it. The centre.**
- **C-45.** Audit the instantiation, never the telescope.
- **C-44.** A brief's claim is unchecked until you check it.
- **D-10.** Price the truth of a recorded residue before pricing its proof.
- **P-l.** A judgement at one parameter is not a judgement at another.
- **D-26.** A well-founded key on a tower needs generation data, or syntax.
- **C-22, C-32, C-36, C-39, C-40, C-42, C-43. I-5. DD0, DD8, DD18, DD24.**

## CONSTRAINTS

- Count with `.venv/bin/python scripts/ledger.py`.
- Run `.venv/bin/python scripts/lint-prose.py --check` on your report.
- **No em dash in any language.**
- Evidence is `file:line`. Write ASD-STE100.

## RETURN

**Lead with the seven parameters and one word each: SUPPLIED, BUILT or OPEN.**
Then the evidence for each at `file:line`. Then whether the residue shrank,
held or grew today. Then anything `el`, `fwd` or `bwd` owes that nobody has
priced. Then the axis for each. **Mark every negative MEASURED or INFERRED.**
