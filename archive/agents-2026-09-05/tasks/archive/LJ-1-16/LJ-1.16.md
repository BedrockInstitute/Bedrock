# LJ-1.16: the criterion at hull parameters, the last standing piece of the hull

tier: codex (default)

## GOAL

Close the hull's remaining elementarity leg: the Tarski-Vaught criterion **at
hull parameters**, not only at X-parameters. **Price the substitution route
against the alternatives before you build**, and refuse with numbers if none
pays.

## CWD

`/Users/alsg/Agentic/Bedrock`, on branch `two-tower-bridge`.

## WHY THIS IS OWED AND WHY IT IS NOT OPTIONAL

`[LJ-1.14]` delivered TV at any carrier and then named what still stands, at
`_build/lj-1.14-report.md:83-87`:

> `hull-closed` gives the criterion at X-parameters. `TV→elem` at the hull
> needs the criterion at hull parameters. The bridge is the substitution step.
> That is route 2's content. The price is 210 to 430 lines.

**`[LJ-1.12]` then confirmed it is not avoidable.** Its recommended crossing,
Route A at 3.3k, still needs this bridge: it feeds the Σ₁ transfer at hull
parameters. So the piece is owed whichever crossing wins, which is why it can
run before `[LJ-1.15]`'s probe reports.

## WHY IT IS EXPENSIVE, AND THE REASON IS A DESIGN FACT

The n-ary criterion needs **the environment baked into constants**. This tree
has **renaming, not substitution**, and `src/FOL/Manipulation/Renaming.lagda.md`
states that design in its opening lines. So the bridge is not a lemma, it is a
missing capability.

That is why `[LJ-1.14]` priced it at 210 to 430 and called it `[LJ-1.3]`
pieces one to three.

**Price at least these three shapes before building any of them:**

1. **Full substitution** for the fragment the criterion needs. The honest
   general answer, and the most expensive.
2. **Constants-only substitution**: bake a hull parameter in as a CONSTANT,
   which is all the criterion needs, avoiding a general substitution operator.
   `FOL.Manipulation.Parameters` already moves constants into environments and
   back; **read it before pricing, because the inverse may be most of this.**
3. **A leastness-encoding route**: reduce hull parameters to X-parameters by
   the encoding the hull already uses, which is Devlin 5.3's implicit
   substitution step. `hull-closed` is the X-parameter half already delivered.

**One best-effort number per shape, naming its basis (DD8).** If all three
price above 430, say so; that re-prices `[LJ-1.5]` and is a full deliverable.

## THE THRESHOLD

DD24 is the wing's ONLY threshold and it GATES now: **0.011472 s per line at
the module caliber, times 1.15, so 0.013193.** The wing measures 0.0065
aggregate today, 0.57x the AC side, so there is room in the budget.

**There is NO line cap on this wing**, by DD24's deliberate omission, because
the wing exists to MEASURE what GCH costs. So do not compress at the expense
of content, and report your module's rate.

**The risk is the content class, not the length.** `dev/LESSONS.md` P-m:
parameterized work runs 0.010 to 0.013 s per line, instantiation 0.22 to
0.297. **A substitution operator that forces a concrete carrier lands in the
instantiation class and would blow the bar about seventeen times.** If your
cheapest shape does that, it is not the cheapest shape. Report the rate.

## DD4, AND IT ALREADY DECIDED ONE ROUTE

**Maximize the code the two proofs share, and write it generic.** One rule,
two ends. It has NO metric and no checker by the owner's ruling, so it is
stated in every brief and answered in every return; the repetition is its only
enforcement.

**`[LJ-1.14]` chose route 1 partly on DD4 and the reasoning applies to you.**
It left a model-theoretic equivalence the J tower can use at any carrier;
route 2's step is specific to how THIS hull encodes leastness, and the J tower
cannot reuse it.

**So prefer a shape whose result is stated about a general carrier**, even at
some line cost, and say per shape what the J tower could reuse.
`[LJ-0.7]` section 4 found the condensation template 5.1 to 5.6 is SHARED
between the towers and the per-tower content is exactly two objects, the
level-hood certificate and the definable well-order. **A substitution bridge
is neither of those two, so it SHOULD be template content.** If your cheapest
shape is not, say so plainly and give both numbers.

- **Parameterize the MODULE** (P-h), and keep stage presentations out of the
  types (P-l).

## LITERATURE (DD18)

- **`dev/literature/devlin-II5.md` section 1.3 and 2.4**, Devlin 5.3 and the
  hull with least witnesses. The substitution step is implicit there and the
  digest says so.
- `_build/literature/dev2.txt` at the 5.3 lines the digest cites.
- **`dev/literature/devlin-errata.md` does NOT cover Chapter II section 5**,
  which `[LJ-1.14]` checked at `_build/lj-1.14-report.md:107-108`. So no
  correction applies to 5.1 or 5.3 and you need not re-check that.

Return a **LITERATURE USED** section, with WHY NOT for anything skipped.

## ARCHIVE (DD18)

- **`_build/lj-1.14-report.md` sections 6 and 7. Your commissioning
  document**, and section 7 records where its reading of 5.3 sits.
- `_build/lj-1.3-report.md` section 6, the three standing pieces, which is
  where this price came from.
- `_build/lj-1.12-report.md`, which confirms the bridge is still needed by the
  recommended crossing.
- `archive/rud-route/` and `archive/dev/TASKS-archived.md`: **the retired
  route had a substitution question too.** Say what it decided and whether the
  decision transfers, because `FOL.Manipulation.Renaming`'s design note is
  older than the route change.
- `dev/LESSONS.md` is NOT archived and still binds. **P-h, P-l, P-m, P-n and
  D-10 decide this block.**

Return an **ARCHIVE USED** section at `file:line`.

## MANDATORY RULES FOR A BUILD

From `python3 scripts/rules.py --for build`. Run it and read each statement.

- **P-h. Definability walks are module-parameterized, never
  function-parameterized.**
- **P-l. A statement may be ABOUT a concrete stage without dragging that
  stage's PRESENTATION into its type.**
- **P-k. A read lemma is stated where its consumers use it.**
- **P-m. The check-cost rate is a content-class certificate.**
- **P-n. Satisfaction content at a concrete carrier is a payable floor**, 0.22
  to 0.297 s per line. **This is the law that decides your shape.**
- **R-35, R-38**: sealing and opacity.
- **R-40**: state a membership witness SHALLOW and climb.
- **I-5**: the inference trap this tree has paid for.
- **C-12.** `GHCRTS="-A64m -I0 -M8g" agda <file>`, ONE process. A sibling may
  hold the other slot. Heap exhaustion is a wall to report, never a cap to
  raise.
- **C-22. Write the deliverable incrementally**, so a killed task still leaves
  its three prices.
- **D-10. Price the truth of a recorded residue before pricing its proof.**
  The 210-to-430 figure is a residue from a report that did not build it.

## THE SIBLINGS

Check `python3 .claude/skills/codex-dispatch/dispatch.py status` before you
start and keep off any file another agent holds.

- **Never run `git checkout .`, `git stash`, `git reset --hard` or `git
  clean`.** Revert by exact path only.
- **Never commit and never push.**

## SCOPE (read)

`_build/lj-1.14-report.md` 6 and 7 first. Then `src/L/Hull.lagda.md`, the
`AtM` module and `hull-closed`. Then `src/FOL/Manipulation/Renaming.lagda.md`
and `src/FOL/Manipulation/Parameters.lagda.md`, which is where a
constants-only route would live.

## SCOPE (write)

`src/L/Hull.lagda.md`, `src/FOL/Manipulation/Renaming.lagda.md`,
`src/FOL/Manipulation/Parameters.lagda.md`, and **at most ONE new master under
`src/FOL/Manipulation/`**. Your report is `_build/lj-1.16-report.md`. Never
`src/Everything.lagda.md`.

## CONSTRAINTS

- **Do not weaken or delete what stands.** `TV-thm` now holds at any carrier
  and `hull-closed` gives the X-parameter criterion; both are correct.
- **Typecheck every file you edit AND every consumer you touch**, one process
  at a time. Do NOT run `make check` or a whole-tree check.
- **Count with `python3 scripts/ledger.py`'s caliber**, never by hand. DD26
  excludes the two catalogs from every size figure.
- **Report cold seconds and the RATE per file**, with the noise rule: under
  0.5 s or under 5 percent, whichever is larger, is flat.
- **Run `python3 scripts/lint-prose.py --check` and `python3
  scripts/lint-agda.py --check`.**
- **DD23 freezes mathematical prose.** Code and its own comments only.
- **Evidence is `file:line`.**
- **A refusal with three prices is a SUCCESS.**
- Write ASD-STE100 in the report.

## RETURN

Write `_build/lj-1.16-report.md` INCREMENTALLY, skeleton first.

1. **THE VERDICT**, first line: which shape, delivered with lines and rate, or
   refused with all three prices.
2. **THE THREE PRICES**, written BEFORE you built, each with its basis.
3. **THE STATEMENT**: the criterion at hull parameters, exactly as delivered.
4. **THE NUMBER**: in-fence lines per file, ledger caliber.
5. **SECONDS AND RATE**, against 0.013193 and against P-n's 0.22 floor.
6. **TEMPLATE OR PER-TOWER** (DD4): what the J tower reuses, per shape.
7. **WHAT THE RETIRED ROUTE DECIDED** about substitution, and whether it
   transfers.
8. **LITERATURE USED.**
9. **ARCHIVE USED.**
10. **WHAT I AM NOT SURE OF.**
