# LJ-1.315: literature for the `φ₀` slot-role ruling

tier: opus (in-harness-subagent-mode), the switch's DEFAULT row. I ran
`scripts/dispatch/dispatch_policy.py` before writing this line.

## WHY THIS EXISTS

**The owner asked for literature beside the probe, so a ruling rests on both.**

`[LJ-1.312]` REFUTED the composite's type by machine: `φ₀`'s two free slots are
the graph's ORDINAL and its machinery BOUND, while `q'` needs the VALUE and the
ORDINAL. **Two cures are on the table and the owner must choose one.** **The
probe evidence exists. The literature beside it does not.**

**YOU ARE NOT REVIEWING THE PROBE.** `[LJ-1.313]` is doing that, in parallel,
at the emergency tier. **Your job is the outside view: what do the sources say
the formula should look like, and does either cure match them.**

## THE QUESTION, in one sentence

**How does each source state「`v` is the `γ`-th level of `L`」as a formula, how
many slots does it use, which does it bind, and which stay free in the roles the
conclusion needs?**

## WHAT `[LJ-1.312]` ALREADY CLAIMS FROM DEVLIN, and you must check it

**It reads `dev/literature/devlin-II5.md:95-96` as:**

> Φ(z, v, γ) with `(a) ∀v∀γ [v = L_γ ↔ ∃z Φ(z, v, γ)]`. Three slots; (a) closes
> ONE, `z`, at position 0; the free pair is `v` at 1 and `γ` at 2, used as VALUE
> and ORDINAL. **Bedrock copies (a) exactly at
> `src/L/BoundedSubset.lagda.md:142-143`.**

**VERIFY that reading against the digest AND say whether the digest is faithful
enough to carry a ruling.** The digest cites `_build/literature/dev2.txt` by
line. **If the primary text is needed, say so and fetch what you can.**

## THE FOUR THINGS TO COLLECT

**1. THE ORTHODOX STATEMENT, from more than one author.** Devlin is one source.
**Get at least two more.** Jech and Kunen both state the constructible
hierarchy's definability formula. **Report each one's arity, what it binds, and
what stays free**, in a single comparison table. **A single author's convention
is not a specification; agreement across three is.**

**2. THE FORMALIZATIONS, and this is the strongest evidence available.**
`dev/literature/formalizations-landscape.md` and
`dev/literature/formalizations.md` already survey Lean, Isabelle/ZF, Mizar and
Metamath. **READ THEM FIRST; do not re-derive what they hold.** Then answer:

- **Isabelle/ZF's `L` (Paulson) is the most complete formalization of this
  material.** **How does it state level-hood, and does it face a slot-role
  question at all?**
- **Lean's mathlib and Flypitch.** Same question.
- **Does ANY formalization close the value slot the way Bedrock does?** **If
  none does, that is the finding**, because it would mean Bedrock's `closeN 14`
  is a local design choice with no precedent, and the owner should know that
  before choosing a cure.

**3. WHY BEDROCK CLOSES FOURTEEN.** `[LJ-1.310]` reports that Devlin's clause
closes ONE slot and Bedrock's `φ₀ = closeN 14 (pins ∧̇ renamed)` closes
fourteen, and calls the divergence **the SHAPE OF THE CLOSURE**, a choice of
the port and not of the mathematics. **Trace that choice to its origin in this
repository's own record.** `[LJ-1.240]` is named as the design that made `φ₀`
constant-free. **Read what it decided and why, and say whether the fourteen
closures follow from the constant-free requirement or were an independent
choice.** **That is a repository-history question and the answer is in
`agents/tasks/` and `dev/JOURNAL.md`.**

**4. WHICH CURE THE LITERATURE FAVOURS.** The two cures, from
`agents/tasks/LJ-1-312/lj-1.312-report.md`:

| form | what it changes | status |
|---|---|---|
| Form 1 | two lines in `src/L/BoundedSubset.lagda.md`, `:105` and `:111` | PROVED in a copy |
| Form 2 | one line, a different renaming `ρ'`, never touches `src/` | INFERRED, not built |

**`[LJ-1.312]` says the two DIFFER IN MEANING: one closed bound against two.**
**Say which meaning the literature's formula has.** **If the sources leave one
bound free and Bedrock's Form 2 leaves two, Form 2 does not match the sources
and the owner should hear that.**

## THE HARD RULE ON CITATIONS

**NEVER write a citation you did not read.** **Mark every source READ, SKIMMED
or POINTER-ONLY, in those words.** A pointer you could not open is useful and
honest; an invented page number is worse than nothing and this project cannot
detect it mechanically.

**Give a locator for everything**: `file:line` for in-repo material, a URL plus
section or page for anything fetched.

**If a source is paywalled or unfetchable, say so and say what it would settle.**

## THE ABORT CRITERION, fixed BEFORE the run (D-1)

- **THE SOURCES AGREE AND ONE CURE MATCHES THEM.** Report the comparison table,
  name the cure, and STOP. **That is the deliverable.**
- **THE SOURCES DISAGREE WITH EACH OTHER.** **Then「the orthodox shape」is not a
  single thing and the owner is choosing between conventions, not between right
  and wrong.** **Say that plainly; it changes the character of the ruling.**
- **NO FORMALIZATION FACES THIS QUESTION.** **A real and useful answer.** It
  would mean the slot-role problem is created by Bedrock's own closure choice.
- **THE DIGEST CANNOT CARRY THE WEIGHT.** Say what the primary text would settle
  and what it costs to get it.

## WHAT YOU MUST NOT DO

- **RUN NO AGDA.** This is a reading and fetching task. **C-12's two slots are
  spoken for by siblings.**
- **LAND NOTHING in `dev/literature/`.** **Write your dossier in
  `agents/tasks/LJ-1-315/` and PROPOSE the digest; the orchestrator lands it.**
  A digest is canonical once it is in `dev/literature/` and nothing is canonical
  twice (DD19).
- **Do not edit `src/`, `dev/`, `AGENTS.md`, or another task directory.**
- **Never commit, never push**, never `git checkout .`, `git stash`,
  `git reset --hard` or `git clean`. Do not run `make check`.
- **Create `agents/tasks/LJ-1-315/lj-1.315-report.md` in your FIRST five
  minutes** and fill it incrementally (C-22). **A survey held in your head dies
  with your budget, and this one is mostly reading.**
- Run `.venv/bin/python scripts/gate/lint-prose.py --check` on what you write.
  **No em dash in any language.**
- Evidence is `file:line` or a URL with a section. Write ASD-STE100. **Mark
  every negative MEASURED or INFERRED, in those words**, and every source READ,
  SKIMMED or POINTER-ONLY.

## THE RULES THIS CHAIN EARNED

**DD18. A brief that dispatches mathematics carries a LITERATURE section and its
return carries LITERATURE USED, including WHY NOT for anything it did not use.**
**This whole task is that section made into a task, so WHY NOT matters more than
usual: a source you decided not to read is a decision the owner should see.**

**C-44. A brief's claim is a measurement until you check it.** Every reading
attributed to `[LJ-1.312]` and `[LJ-1.310]` above is theirs, not mine, and you
check both.

**C-41. A retired name must still resolve.** Most of `dev/literature/` was
written for the RETIRED rud route. **It is still true about the mathematics and
often false about this route's plan.** **Take the mathematics and mark the
route-specific parts as not transferring.**

**P-l. A judgement at one site is a hypothesis at another.** A convention in one
author's book is a hypothesis about another's.

## DD4

**Maximize the code the two proofs share, and write it generic.** One rule, two
ends, no metric and no checker. **This task writes no code.**

**Say in one line whether the literature suggests a formula shape that would
serve BOTH trophies**, because `φ₀` sits in the FOL and bounded-set layer, which
is carrier-free and tower-free, and a shape chosen there is inherited by
everything above it.

## ARCHIVE (DD18)

- **`dev/literature/devlin-II5.md`, the II.5 digest, read the level-hood part
  WHOLE.**
- **`dev/literature/formalizations-landscape.md` and
  `dev/literature/formalizations.md`**, both, before any web search.
- **`dev/literature/BIBLIOGRAPHY.md`**, for what has already been fetched and
  what is known unfetchable. **This will save you hours.**
- **`agents/tasks/LJ-1-312/lj-1.312-report.md`** and
  **`agents/tasks/LJ-1-310/lj-1.310-report.md` section 7**, the probe evidence
  your dossier sits beside.
- **`archive/dev/TASKS-archived.md`**, taking SHAPE and never a claim.

**Return an ARCHIVE USED section naming ONE line read per archived file.**

## LITERATURE (DD18)

**This task IS the literature section.** Return a **LITERATURE USED** section
that names every source, its status, its locator, and **WHY NOT for anything
you chose not to read.**

## SCOPE (read)

`dev/literature/BIBLIOGRAPHY.md` FIRST, so you do not re-fetch what the project
already has.

## SCOPE (write)

`agents/tasks/LJ-1-315/` only.

## MANDATORY RULES

Run `.venv/bin/python scripts/dispatch/rules.py --for recon` and read every
statement. **The tool prints `Full entry: dev/LESSONS.md:<line>` and says THIS
IS AN EXCERPT when it truncated. OPEN the full entry for any law you act on.**

- **DD18, C-44, C-41, P-l.** Named above with what each governs.
- **C-22, C-32, C-39, C-42.** I-5. **D-1, D-10.**
- **DD0, DD4, DD8, DD19, DD23.**

## RETURN

**Lead with ONE sentence: which cure the literature favours, or that it favours
neither and why.** Then the comparison table: each source, its arity, what it
binds, what stays free, with a locator. Then what the formalizations do, with
Isabelle/ZF first. Then why Bedrock closes fourteen, traced to its origin in
this repository. Then whether Form 2's two-closed-bounds meaning has any
precedent. Then your proposed digest, as a file in your own directory, ready for
the orchestrator to land. **Mark every source READ, SKIMMED or POINTER-ONLY, and
every negative MEASURED or INFERRED.**
