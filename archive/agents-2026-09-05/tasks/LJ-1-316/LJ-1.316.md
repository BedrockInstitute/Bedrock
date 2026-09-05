# LJ-1.316: literature for the `InjData` ruling

tier: opus (in-harness-subagent-mode), the switch's DEFAULT row. I ran
`scripts/dispatch/dispatch_policy.py` before writing this line.

## WHY THIS EXISTS

**The owner asked for literature beside the probe, so a ruling rests on both.**

`[LJ-1.305]` asks the project to admit a new principle into a trophy:

```agda
Wat α    = Σ[ δ ∈ V ℓ ] (⟨ δ ∈ˢ α ⟩ × (⟪ α ⟫ ↪ ⟪ δ ⟫))
InjData  = (α : V ℓ) → IsOrd α → ⟨ ω ∈ˢ α ⟩ → ∥ Wat α ∥₁ → Wat α
```

**Sufficiency is MEASURED: the untruncated descent is green under it, 322
lines, 4 s. Necessity is INFERRED at the theory level, by the report's own
words, with no independence model built.**

**YOU ARE NOT REVIEWING THE PROBE.** `[LJ-1.314]` is doing that in parallel and
attacking necessity from inside the tree. **Your job is the outside view: what
do the sources do at this exact step, and do any of them need something of this
shape.**

## THE QUESTION, in one sentence

**At the step where the square-law descent needs a `δ ∈ α` with an injection
`⟪ α ⟫ ↪ ⟪ δ ⟫`, how does each source PRODUCE that `δ`, and does the production
use choice, a definable well-order, or something else?**

## THE REASON THIS SHOULD HAVE AN ANSWER IN THE SOURCES

**`L`'s whole point is that it is well-ordered by a definable relation.** That
is why `L ⊨ AC` is a THEOREM and not an assumption, and it is this project's
first trophy. **A classical proof at this step does not choose: it takes the
LEAST such `δ` under `<_L`.** **So the orthodox argument should need no choice
at all, and the question is what happens to「take the least」when the ambient
logic is cubical type theory and the existence arrives propositionally
truncated.**

**That is a type-theory question, not a set-theory one, and BOTH literatures
bear on it.** **Collect both.**

## THE FOUR THINGS TO COLLECT

**1. THE SET-THEORY SIDE: how the classical proof selects.** Devlin's II.5 is
digested at `dev/literature/devlin-II5.md`. **Find the corresponding step and
report, at a locator, exactly how the witness is produced.** Then get at least
one more author, Jech or Kunen, on the same step. **Report whether any of them
invokes choice, and if none does, say what supplies the selection instead.**

**2. THE TYPE-THEORY SIDE, and this is where the real answer probably is.**
**In HoTT and cubical type theory, `∥ A ∥₁ → A` is not generally available**,
and the conditions under which it IS available are a studied question. Collect:

- **The HoTT Book's treatment of propositional truncation and its
  eliminator**, and specifically **when a truncation can be untruncated**: an
  hProp target, a decidable predicate over a set with a well-order, unique
  choice, or a constructive choice operator.
- **「Unique choice」and「the axiom of choice in HoTT」**: what exactly fails
  and what does not. **`∥ Σ ∥₁ → Σ` for a Σ whose first component is UNIQUE is
  free. Our `Wat α` is not unique, but the LEAST such `δ` might be.**
- **Search for the standard trick: turning a truncated existence into an
  untruncated one by minimality over a well-order.** **If that trick is
  documented, `InjData` may be derivable and the whole principle disappears.**
  **That is the most valuable thing you can find and you should look for it
  first.**

**3. WHAT OTHER FORMALIZATIONS DID.** `dev/literature/formalizations-landscape.md`
and `dev/literature/formalizations.md` survey Isabelle/ZF, Lean, Mizar and
Metamath. **READ THEM BEFORE ANY WEB SEARCH.** Then:

- **Isabelle/ZF (Paulson) formalized `L` and AC-in-L in a CLASSICAL logic with
  choice available.** **So it may simply not face this.** **Say so if true; a
  formalization that cannot face the question is not evidence that the question
  is easy.**
- **Is there ANY constructive or type-theoretic formalization of `L`?** **If
  none exists, say so.** **That would mean Bedrock is first here and no
  precedent can settle the ruling**, which the owner should know.

**4. WHAT `InjData` IS, in strength terms.** **Name it if the literature names
it.** Is it an instance of a known principle: countable choice, dependent
choice, `AC_{set,set}`, the axiom of unique choice, or none? **If it is a known
principle, say what is known about its status in cubical type theory and whether
`--safe` Agda already proves or refutes it.**

**AND THE QUESTION THAT MATTERS MOST TO THIS PROJECT:** **this project's first
trophy PROVES choice inside `L`.** **If `InjData` is a choice principle assumed
in the ambient theory, say plainly whether that undermines the AC trophy or is
orthogonal to it.** **I do not assert that it does. I cannot answer it and it
must be answered.**

## THE HARD RULE ON CITATIONS

**NEVER write a citation you did not read.** **Mark every source READ, SKIMMED
or POINTER-ONLY, in those words.** A pointer you could not open is useful and
honest; an invented theorem number is worse than nothing and this project cannot
detect it mechanically.

**Give a locator for everything**: `file:line` for in-repo material, a URL plus
section, page or theorem number for anything fetched.

## THE ABORT CRITERION, fixed BEFORE the run (D-1)

- **THE LITERATURE GIVES A DERIVATION.** **The best outcome.** Report it with
  its locator and say what it would take to build here. **No new principle
  enters the trophy.**
- **THE LITERATURE SAYS IT CANNOT BE DERIVED IN THIS SETTING.** **Also
  valuable.** Then the owner rules on a measured necessity, not an inferred one.
- **NO CONSTRUCTIVE FORMALIZATION OF `L` EXISTS.** **Say so plainly.** Then
  there is no precedent and the ruling is genuinely new.
- **THE CLASSICAL PROOF SELECTS BY LEAST ELEMENT AND THAT IS ALL.** **Then say
  exactly what blocks the same move here**, and hand that sentence to
  `[LJ-1.314]`'s attack 1 through your report. **The two tasks meet at that
  sentence.**

## WHAT YOU MUST NOT DO

- **RUN NO AGDA.** This is a reading and fetching task. **C-12's two slots are
  spoken for by siblings.**
- **LAND NOTHING in `dev/literature/`.** **Write your dossier in
  `agents/tasks/LJ-1-316/` and PROPOSE the digest; the orchestrator lands it**
  (DD19: nothing is canonical twice).
- **Do not edit `src/`, `dev/`, `AGENTS.md`, or another task directory.**
- **Never commit, never push**, never `git checkout .`, `git stash`,
  `git reset --hard` or `git clean`. Do not run `make check`.
- **Create `agents/tasks/LJ-1-316/lj-1.316-report.md` in your FIRST five
  minutes** and fill it incrementally (C-22).
- Run `.venv/bin/python scripts/gate/lint-prose.py --check` on what you write.
  **No em dash in any language.**
- Evidence is `file:line` or a URL with a section. Write ASD-STE100. **Mark
  every negative MEASURED or INFERRED, in those words**, and every source READ,
  SKIMMED or POINTER-ONLY.

## THE RULES THIS CHAIN EARNED

**D-10. Price the TRUTH of a recorded residue before pricing its proof.** **The
residue is「the truncation cannot be lifted」and this task prices its truth from
outside the tree.**

**DD18.** This task is that rule made into a task. **WHY NOT matters more than
usual here: a source you decided not to read is a decision the owner should
see.**

**C-44.** Every claim attributed to `[LJ-1.305]` above is its own, not mine.

**C-41. A retired name must still resolve.** Most of `dev/literature/` was
written for the RETIRED rud route. **It is still true about the mathematics and
often false about this route's plan.**

**C-36. A failed substitution is not a proof of impossibility.** **`[LJ-1.305]`
could not lift the truncation. The literature may know how.**

## DD4

**Maximize the code the two proofs share, and write it generic.** One rule, two
ends, no metric and no checker. **This task writes no code.**

**NAME THE AXIS** (C-46). DD4's own axis is AC-against-GCH. **Say in one line
whether a principle of this shape, if admitted, would sit in the shared part or
in the GCH-only part**, because a principle in the shared part is one both
trophies then rest on, and that is a much larger commitment than a GCH-only one.

## ARCHIVE (DD18)

- **`dev/literature/devlin-II5.md`**, the descent step, read it whole.
- **`dev/literature/formalizations-landscape.md` and
  `dev/literature/formalizations.md`**, both, before any web search.
- **`dev/literature/BIBLIOGRAPHY.md`**, for what is already fetched and what is
  known unfetchable. **This will save you hours.**
- **`agents/tasks/LJ-1-305/lj-1.305-report.md`**, the probe evidence your
  dossier sits beside. **Read its route analysis, sections on routes 1 to 3.**
- **`archive/dev/TASKS-archived.md`**, taking SHAPE and never a claim: the
  retired route met choice-shaped obligations too.

**Return an ARCHIVE USED section naming ONE line read per archived file.**

## LITERATURE (DD18)

**This task IS the literature section.** Return a **LITERATURE USED** section
naming every source, its status, its locator, and **WHY NOT for anything you
chose not to read.**

## SCOPE (read)

`dev/literature/BIBLIOGRAPHY.md` FIRST, so you do not re-fetch what the project
already has.

## SCOPE (write)

`agents/tasks/LJ-1-316/` only.

## MANDATORY RULES

Run `.venv/bin/python scripts/dispatch/rules.py --for recon` and read every
statement. **The tool prints `Full entry: dev/LESSONS.md:<line>` and says THIS
IS AN EXCERPT when it truncated. OPEN the full entry for any law you act on.**

- **D-10, DD18, C-44, C-41, C-36.** Named above with what each governs.
- **C-22, C-32, C-39, C-42.** I-5. **D-1, D-26, P-l.**
- **DD0, DD4, DD8, DD9, DD19, DD23.**

## RETURN

**Lead with ONE sentence: whether the literature derives `InjData`, refutes its
derivability, or is silent.** Then how the classical proof produces the witness,
with a locator, from at least two authors. Then the type-theory side: when a
truncation can be untruncated, and specifically whether minimality over a
well-order is a documented route. Then what other formalizations did and whether
any faced this. Then what `InjData` is in strength terms and whether it bears on
the AC trophy. Then your proposed digest, as a file in your own directory, ready
for the orchestrator to land. **Mark every source READ, SKIMMED or
POINTER-ONLY, and every negative MEASURED or INFERRED.**
