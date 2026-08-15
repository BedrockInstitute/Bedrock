# LJ-1.333: item 2, the weakly constant endomap, at the CHEAPER truncation

tier: opus (in-harness-subagent-mode), the switch's DEFAULT row. I ran
`scripts/dispatch/dispatch_policy.py` before writing this line.

## WHERE THE LEG STANDS, and it is one step from done

**`[LJ-1.332]` finished the mathematics of the last band.**

| band | supplier |
|---|---|
| `Init α` | **DELIVERED**, untruncated |
| ω | **DELIVERED**, untruncated |
| successors | **BUILT**, untruncated, 25 code lines (`[LJ-1.330]`) |
| non-initial limits | **BUILT, but TRUNCATED**: `limit-truncated`, green, 32 code lines |

> **The blocker is no longer a missing construction. It is a missing
> untruncation, at ONE band.**

## AND THE TRUNCATION IS CHEAPER THAN ANYONE THOUGHT

**My brief told `[LJ-1.332]` the wall would be `src/L/Cardinal.lagda.md:133-134`.
It MEASURED that the band never reaches there.**

> **The band's truncation is `Init`'s own FOURTH ROW, and it is weaker and
> cheaper: it asks for SOME member, not the LEAST one.**

**That is why this task exists rather than a repeat of an earlier one.** **Every
previous attempt on this leg fought the LEAST-member truncation, which needs a
well-order on a function type that this tree does not have** (`[LJ-1.329]`: 35
`SWO` instances in `src/`, not one carrier is a function type).

**A SOME-member truncation does not need a well-order at all.**

## THE QUESTION

**Is there a weakly constant map that untruncates the limit band's `sq`?**

**`[LJ-1.321]` section 8 item 2 is the candidate and it has never been tried.**
**Items 3 and 4 are now RETIRED**, by `[LJ-1.330]` and `[LJ-1.332]`
respectively. **Item 1 and item 2 remain, and item 2 is the one the cheaper
truncation opens.**

**The criterion is exact and delivered** (`dev/literature/truncation-and-selection.md`,
Kraus, Escardó, Coquand and Altenkirch, LMCS 13(1) 2017, Theorem 16): **a type
admits `∥X∥ → X` if and only if it has a weakly constant endomap.** And the
library's `rec→Set` needs only a `2-Constant` map into a SET, with `sq α`
measured to BE a set (`agents/tasks/LJ-1-319/SqIsSet.agda`, green).

## WHAT THE MACHINE HAS ALREADY SAID ABOUT THIS

**`[LJ-1.332]`'s negative control 2 stated the obligation for you:** it wrote
`PT.rec` with `refl` and **Agda named the two arbitrary pairing functions.**
**That IS the `2-Constant` obligation, written by the typechecker rather than by
a person.** Read that control before you write anything,
`agents/tasks/LJ-1-332/ProbeLJ1332A.agda`.

**And `[LJ-1.329]` REFUTED the naive map by a term**: two witnesses differing by
one transposition break `2-Constant`. **That refutation stands and you must not
re-derive it.** **The question is whether a DIFFERENT map works, and the cheaper
truncation is the new information.**

## THE ABORT CRITERION, fixed BEFORE the run (D-1)

- **THE MAP EXISTS AND YOU BUILD IT.** **Then `sq` is total, `[LJ-1.8]`'s
  blocker is gone, and the leg is finished.** Report the term, its lines, its
  seconds and its negative control. STOP.
- **THE SOME-MEMBER TRUNCATION STILL NEEDS A CHOICE.** **Then the leg's answer
  is that no untruncation exists in this theory**, and the question goes to the
  owner as a statement-level one: the consumers demand DATA where Devlin works
  truncated throughout. **Say so plainly; that is a route-level finding.**
- **THE CONSUMERS DO NOT NEED DATA.** **CHECK THIS EARLY AND CHEAPLY.** **If
  `∥ sq α ∥₁` serves `src/L/StageCardinal.lagda.md:17-19` and
  `src/L/BoundedSubset.lagda.md:1388-1391` after their final motives are made
  propositional, the untruncation is not needed at all and the leg closes
  today.** **`[LJ-1.332]` measured that Devlin's own argument is complete at the
  truncated level.** **This is the cheapest possible answer and it may be the
  right one.**
- **A WALL.** **C-56, written from `[LJ-1.332]`'s own bisection:** a truncated
  proof that walls is paying for its ASSEMBLY, not its mathematics. **Write the
  untruncated control FIRST and keep it.** One definition there cost 400 s
  interrupted against 2 s for identical mathematics, from nesting `PT.map`
  inside `PT.rec`.

## WHAT YOU MUST NOT DO

- **LAND NOTHING. This is a probe.** Write and run only in
  `agents/tasks/LJ-1-333/`. **`src/` is forbidden** (I-5).
- **Do not re-derive `[LJ-1.329]`'s refutation of the naive map.** It stands.
- **Do not land `[LJ-1.330]`'s or `[LJ-1.332]`'s terms.** Their landing site is
  an open question the orchestrator settles.
- **Do not edit another task directory.** You may READ and RE-RUN the probes in
  `agents/tasks/LJ-1-319/`, `LJ-1-321/`, `LJ-1-329/`, `LJ-1-330/` and
  `LJ-1-332/`; you may not change them.
- **COUNT THE AGDA SLOTS BEFORE EVERY INVOCATION.** C-12 caps this machine at
  TWO. **`ps aux | grep -c '[a]gda '` OVER-COUNTS (the bash wrapper) and
  `grep -c 'libexec.*bin/agda'` over-counts too (the grep). MEASURED
  2026-08-15.** Use:
  ```sh
  ps aux | awk '/libexec.*bin\/agda/ && !/awk/' | wc -l
  ```
- **ONE agda process, `GHCRTS="-A64m -I0 -M8g"`, cap NEVER raised.** Report the
  load beside every figure.
- **RUN NEGATIVE CONTROLS, and prefer the kind that MEASURES.**
  **`[LJ-1.332]` ran four and all four measured; one of them put its whole
  verdict into a single error message, `∥ _ ∥₁ !=< sq α`.** **That is the
  standard here.**
- **Never commit, never push**, never `git checkout .`, `git stash`,
  `git reset --hard` or `git clean`. Do not run `make check`.
- **Create `agents/tasks/LJ-1-333/lj-1.333-report.md` in your FIRST five
  minutes** and fill it incrementally (C-22).
- Run `.venv/bin/python scripts/gate/lint-prose.py --check` and
  `.venv/bin/python scripts/gate/lint-agda.py --check` on what you write. **No
  em dash in any language.** DD23 freezes mathematical prose in `src/`.
- Evidence is `file:line`. Write ASD-STE100. Mark every negative **MEASURED**
  or **INFERRED**, in those words.

## THE PREMISE OF MINE MOST LIKELY TO BE WRONG

**Five of my last six briefs carried a claim an agent measured FALSE, and
`[LJ-1.332]`'s catch was that I named the wrong supplier for the wall.**

**The one most at risk here: 「the SOME-member truncation does not need a
well-order at all」.** **That is my inference from `[LJ-1.332]`'s wording, not
its measurement.** **Check it first, and if it is wrong, that is your
headline.**

## THE RULES THIS CHAIN EARNED

**C-56**, written today from `[LJ-1.332]`'s bisection. **It is the fourth law in
this family, with C-51, C-55 and R-41: the price is in the FORM, and the
mathematics is not what you are paying for.**

**C-54.** A truncation stall at a SET motive is a `2-Constant` obligation before
it is a principle. **This task is that law's own follow-through.**

**C-36. A failed substitution is not a proof of impossibility.** **`[LJ-1.329]`
refuted ONE map. `[LJ-1.332]` refuted ONE supplier. Neither refuted the goal,
and both said so.**

**C-44, C-42, D-10, P-l, C-45.**

**A STOP IS A DELIVERABLE.**

## DD4

**Maximize the code the two proofs share, and write it generic.** One rule, two
ends, no metric and no checker.

**NAME YOUR AXIS** (C-46). DD4's own axis is AC-against-GCH, fixed in code at
`scripts/measure/ledger.py:50`.

**Both terms on this leg kept one property and you should too:** they take a
POINT of a delivered injection type, never a total map out of `sq α`, **which is
exactly why `[LJ-1.329]`'s object could not exist.** **`[LJ-1.332]`'s term is
tower-blind and imports neither `L.Absorption` nor `L.InjChain`**, so it does
not charge the closure rise `[LJ-1.330]` inferred. **Say what yours does.**

## ARCHIVE (DD18)

- **`agents/tasks/LJ-1-332/lj-1.332-report.md`, read WHOLE.** It funds you, it
  measured the cheaper truncation, and its control 2 states your obligation.
- **`agents/tasks/LJ-1-321/lj-1.321-report.md` section 8**, the four candidate
  maps. **Items 3 and 4 are RETIRED; item 2 is yours.**
- **`agents/tasks/LJ-1-329/lj-1.329-report.md`**, the naive map's refutation,
  which stands.
- **`archive/dev/TASKS-archived.md`**, taking SHAPE and never a claim.

**Return an ARCHIVE USED section naming ONE line read per archived file.**

## LITERATURE (DD18)

**`dev/literature/truncation-and-selection.md`**, for Theorem 16's criterion and
the library's set-motive eliminators. **And `[LJ-1.332]` measured a finding you
should weigh: Devlin has NO separate limit case, he reduces by cardinal
arithmetic, and a cardinality equation asserts a bijection EXISTS, which is
already truncated.** **So his argument is complete at the truncated level and
the untruncation is a debt this formalization owes that his proof never does.**
**Say in one line whether that makes the untruncation optional or merely
unusual.** Return a **LITERATURE USED** section.

## SCOPE (read)

`agents/tasks/LJ-1-332/lj-1.332-report.md` FIRST, whole.

## SCOPE (write)

`agents/tasks/LJ-1-333/` only.

## MANDATORY RULES

Run `.venv/bin/python scripts/dispatch/rules.py --for probe` and read every
statement. **The tool prints `Full entry: dev/LESSONS.md:<line>` and says THIS
IS AN EXCERPT when it truncated. OPEN the full entry for any law you act on.**

- **D-1, C-54, C-56, C-36, C-44, C-42, D-10, P-l, C-45.** Named above.
- **C-12.** Two Agda processes, counted with the command above.
- **C-51, C-55, C-53, C-49, C-50, P-i, P-k, P-m, P-y, R-40, R-41.**
- **C-22, C-32, C-38, C-39, C-40.** I-5. **D-26.**
- **DD0, DD4, DD8, DD18, DD23, DD24.**

## RETURN

**Lead with ONE word: UNTRUNCATED, NOT-NEEDED, WALLED or STATEMENT-LEVEL**,
where NOT-NEEDED means the consumers accept the truncated law. Then whether my
premise about the well-order holds. Then the term or the wall at `file:line`.
Then lines, seconds and load, with the untruncated control beside them (C-56).
Then your negative controls and what they named. Then what remains of
`[LJ-1.8]`'s blocker. **Mark every negative MEASURED or INFERRED.**
