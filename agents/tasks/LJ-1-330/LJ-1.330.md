# LJ-1.330: a CANONICAL element of `sq α` at non-initial α

tier: opus (in-harness-subagent-mode), the switch's DEFAULT row. I ran
`scripts/dispatch/dispatch_policy.py` before writing this line.

## WHY THIS, AND WHY NOT THE FOUR THINGS BEFORE IT

**Four tasks in a row returned「do not fund this」, and each one measured the
reason.** `[LJ-1.329]` closed the last of them:

> **There is no single function to choose.** `pullOrder`'s third parameter has
> type `sq α → C`: **a TOTAL MAP OUT of the ambient type, not a point of it.**
> One coded function is a point of the carrier. **The three-task convergence was
> on a NAME, not an object.**

**And it measured what the total map would BUY:** an **ambient choice principle
over a power set**, at every infinite ordinal. Bedrock's ambient theory takes
`LEM` only, `src/Base/Classical.lagda.md:41-42`. **Not false, but not
buildable: the same fence as `AmbientToCode`.**

**Its alternative 1 is this task, and it is the one that needs NO well-order and
NO choice at all.**

## THE QUESTION

**Is there a CANONICAL element of `sq α` at a non-initial ordinal α?**

**Not「is one merely there」. A canonical one: a term, built from α's own
structure, with no selection step.**

## WHY IT SHOULD BE POSSIBLE, and the tree does it twice already

| site | delivers | at |
|---|---|---|
| `via-col-square`, `src/L/Ordinal/SquareLaw.lagda.md:960-961` | untruncated, canonical | **initial** α |
| `squareω`, `src/L/InjChain.lagda.md:184-185` | untruncated, canonical | **ω** |

**MEASURED by `[LJ-1.329]`, and the gap is exactly the NON-INITIAL ordinals**
(`agents/tasks/LJ-1-300/lj-1.300-report.md:162-165`).

**A canonical element dissolves the whole line**, because:

- the truncation never arises: there is nothing to select from;
- `[LJ-1.321]`'s `2-Constant` obligation is discharged trivially by a constant
  map;
- **no coded order, no coded function, no new principle.**

**That is why it is worth a task after four refusals.**

## WHAT `[LJ-1.329]` DID NOT SETTLE, and you settle it

> **Whether a canonical `sq α` exists at non-initial α.** It named this first
> among the things it did not settle, and it did not price it.

## THE SHAPE TO AIM AT

`sq α` is `Σ[ f ∈ (⟪α⟫ × ⟪α⟫ → ⟪α⟫) ] injectivity`,
`src/L/Ordinal/SquareLaw.lagda.md:685-688`. **So you owe a pairing function on
the carrier of a non-initial ordinal, plus its injectivity, both built and not
chosen.**

**The obvious route, and check whether it is the right one:** a non-initial α
has an INITIAL ordinal below it of the same cardinality, and `via-col-square`
serves that one. **If a bijection `⟪α⟫ ≃ ⟪init α⟫` is delivered and canonical,
the pairing transports along it and the task is a transport rather than a
construction.**

**MEASURE whether that bijection is delivered, canonical, and at the right
pair.** **If it is merely truncated, say so: that would be the same wall one
step further out, and naming it is the deliverable.**

## THE ABORT CRITERION, fixed BEFORE the run (D-1)

- **A CANONICAL ELEMENT EXISTS AND YOU BUILD IT.** **Then the descent's whole
  truncation line dissolves and this is the largest result of the chain.**
  Report the term, its lines, its seconds, **and its negative control.** STOP.
- **THE TRANSPORT IS THE ROUTE AND THE BIJECTION IS TRUNCATED.** **Then the wall
  moved one step and you have located it exactly.** Name it at `file:line`.
- **NO CANONICAL ELEMENT IS POSSIBLE.** **Say why, with the term you could not
  write** (C-36). **Then alternative 2 is the only route left and the project
  should hear that plainly.**
- **THE OBVIOUS ROUTE IS WRONG.** Say what the right one is, or that none is
  visible.
- **A WALL.** A single `agda` invocation past 30 MINUTES is a wall: interrupt,
  report ELAPSED SECONDS, bisect. **NEVER raise the cap.**

## ALTERNATIVE 2, and it is NOT yours

`[LJ-1.329]` offered a second exit: **move the descent's `sq` hypothesis inside
L.** **Do not attempt it.** It touches how a delivered chapter takes its
parameters and it interacts with the restated trophy, so it needs its own task
and possibly the owner. **If your work shows alternative 2 is forced, say so and
stop.**

## THE PREMISE OF MINE MOST LIKELY TO BE WRONG

**Three of my last four briefs carried a claim an agent measured FALSE.** **The
one above most at risk is「a non-initial α has an initial ordinal below it of
the same cardinality, and a canonical bijection to it」.** **I have not checked
it. Check it first, and if it is false, that is your headline.**

## WHAT YOU MUST NOT DO

- **LAND NOTHING. This is a probe.** Write and run only in
  `agents/tasks/LJ-1-330/`. **`src/` is forbidden** (I-5).
- **Do not edit another task directory.** You may READ and RE-RUN the sibling
  probes in `agents/tasks/LJ-1-321/`, `LJ-1-326/` through `LJ-1-329/`; you may
  not change them.
- **`src/L/GCH.lagda.md` was RESTATED and `src/L/BoundedSubset.lagda.md` had a
  cure landed, both yesterday.** **Read the CURRENT files.**
- **COUNT THE AGDA SLOTS BEFORE EVERY INVOCATION.** C-12 caps this machine at
  TWO. **`ps aux | grep -c '[a]gda '` OVER-COUNTS (the bash wrapper) and
  `grep -c 'libexec.*bin/agda'` over-counts too (the grep). MEASURED
  2026-08-15.** Use:
  ```sh
  ps aux | awk '/libexec.*bin\/agda/ && !/awk/' | wc -l
  ```
  Take ONE slot and report the load beside every figure.
- **ONE agda process, `GHCRTS="-A64m -I0 -M8g"`, cap NEVER raised.**
- **RUN A NEGATIVE CONTROL on anything you build**, and **prefer the kind that
  MEASURES**: write the type you expect to fail and let Agda name the blocker.
  **`[LJ-1.328]` and `[LJ-1.329]` both did that and in both cases the error
  message WAS the finding.**
- **Never commit, never push**, never `git checkout .`, `git stash`,
  `git reset --hard` or `git clean`. Do not run `make check`.
- **Create `agents/tasks/LJ-1-330/lj-1.330-report.md` in your FIRST five
  minutes** and fill it incrementally (C-22).
- Run `.venv/bin/python scripts/gate/lint-prose.py --check` and
  `.venv/bin/python scripts/gate/lint-agda.py --check` on what you write. **No
  em dash in any language.** DD23 freezes mathematical prose in `src/`.
- Evidence is `file:line`. Write ASD-STE100. Mark every negative **MEASURED**
  or **INFERRED**, in those words.

## THE RULES THIS CHAIN EARNED

**D-10. Price the TRUTH of a recorded residue before pricing its proof.**
**Four tasks priced proofs of a residue that was not what anyone thought it
was.**

**C-44.** See the premise warning above.

**C-36. A failed substitution is not a proof of impossibility.** **`[LJ-1.329]`
said so about its own refutation: it measured only the `pullOrder` route, and
`[LJ-1.321]`'s other candidates are untouched.**

**C-45. `exit 0` is not a supply.**

**P-l, C-42.** One construction measures one site.

**A STOP IS A DELIVERABLE, and it has been the most valuable return FOUR times
running on this leg. If it is right a fifth time, say it plainly.**

## DD4

**Maximize the code the two proofs share, and write it generic.** One rule, two
ends, no metric and no checker.

**NAME YOUR AXIS** (C-46). DD4's own axis is AC-against-GCH, fixed in code at
`scripts/measure/ledger.py:50`.

**AND `[LJ-1.329]` MEASURED A DD4 INVERSION YOU SHOULD KEEP IN MIND.** It found
`pullOrder` cannot help **because** it is shared and generic: generic in the
carrier means it demands a total map OUT of that carrier. **DD4 measures what
two proofs share; it never certifies that a shared device reaches a given
site.** **A canonical construction has no such problem, so say whether yours is
tower-blind and which closure it lands in.**

## ARCHIVE (DD18)

- **`agents/tasks/LJ-1-329/lj-1.329-report.md`, read WHOLE.** It funds you and
  its「what I did not settle」section names your question first.
- **`agents/tasks/LJ-1-321/lj-1.321-report.md` section 8**, the candidate maps
  it wrote and could not refute. **They are still live.**
- **`agents/tasks/LJ-1-300/lj-1.300-report.md:162-165`**, which located the gap
  at the non-initial ordinals.
- **`archive/dev/TASKS-archived.md`**, taking SHAPE and never a claim.

**Return an ARCHIVE USED section naming ONE line read per archived file.**

## LITERATURE (DD18)

**`dev/literature/devlin-II5.md`.** **Devlin proves the square law for every
infinite ordinal, and `[LJ-1.327]` measured that his 5.6 takes the pairing from
generic cardinal arithmetic.** **Say in one line whether his construction is
canonical at non-initial ordinals or whether he reduces to the initial one**,
because that is exactly the question this task asks. Return a **LITERATURE
USED** section.

## SCOPE (read)

`src/L/Ordinal/SquareLaw.lagda.md:940-970`, `via-col-square` and what it demands,
FIRST.

## SCOPE (write)

`agents/tasks/LJ-1-330/` only.

## MANDATORY RULES

Run `.venv/bin/python scripts/dispatch/rules.py --for probe` and read every
statement. **The tool prints `Full entry: dev/LESSONS.md:<line>` and says THIS
IS AN EXCERPT when it truncated. OPEN the full entry for any law you act on.**

- **D-1, D-10, C-44, C-36, C-45, C-42, P-l.** Named above with what each
  governs.
- **C-12.** Two Agda processes, counted with the command above.
- **C-51, C-52, C-53, C-49, C-50, P-i, P-k, P-m, P-y, R-40, R-41.**
- **C-22, C-32, C-38, C-39, C-40.** I-5. **D-26.**
- **DD0, DD4, DD8, DD18, DD23, DD24.**

## RETURN

**Lead with ONE word: CANONICAL, TRANSPORTED, WALLED or IMPOSSIBLE.** Then
whether my premise about the initial ordinal below α holds. Then the term or the
wall at `file:line`. Then lines, seconds and load. Then your negative control
and what it named. Then what the descent re-prices to. Then the DD4 axis.
**Mark every negative MEASURED or INFERRED.**
