# LJ-1.14: Tarski-Vaught at a NON-transitive carrier

tier: codex (default)

## GOAL

Close the hull's elementarity leg. The delivered Tarski-Vaught equivalence
needs a transitive carrier and the hull is not transitive. **Deliver it at a
non-transitive carrier, or deliver Devlin 5.3's substitution route instead,
whichever prices lower.** Price both before you build either.

## CWD

`/Users/alsg/Agentic/Bedrock`, on branch `two-tower-bridge`.

## THE FINDING YOU ARE ANSWERING

`[LJ-1.11]`, an adversarial review, finding **F3**, at
`_build/lj-1.11-review.md:393-407`. Read it before anything else.

Its content, verified against the tree:

- **`TV-thm` requires a transitive carrier.** `TV→elem`'s bounded-quantifier
  cases spend `Mtr`, at `src/L/Hull.lagda.md:70,142-181`. `Mtr : isTransV M`
  is a parameter of `module AtM` at `:70`, and the whole equivalence lives
  inside it. `TV-thm` itself is at `:183`.
- **Devlin 5.1 needs no transitivity of N** (`dev2.txt:1071`).
- **The hull is not transitive.** So the condensation block cannot use the
  equivalence as delivered.

**The review is explicit that this is a PRICING gap and not a false claim.**
`[LJ-1.3]`'s report is honest that the leg is open. What was never priced is
the non-transitive TV inside it.

## THE TWO ROUTES, AND YOU PRICE BOTH BEFORE BUILDING EITHER

**ROUTE 1: re-prove the equivalence at a non-transitive carrier.** Route the
bounded-quantifier cases through the unbounded criterion instead of through
`Mtr`. Read `:142-181` and say exactly where `Mtr` is spent and what replaces
it.

**ROUTE 2: Devlin 5.3's implicit substitution step.** Work with hull
parameters reduced to X-parameters by the leastness encoding, so the carrier
never needs to be transitive. `[LJ-1.11]` names this as the alternative; the
source is `dev2.txt` at 5.3.

**Write both prices into the report BEFORE you build.** `[LJ-1.3]` section 6
prices the three standing pieces at 210 to 430 lines total and does not name
this gap inside piece three, so there is no usable prior estimate. Yours is
the first.

**If both routes price badly, STOP and report the two numbers.** A refusal
with two prices is exactly what `[LJ-1.12]` needs and it is a full
deliverable. Five of nine blocks refused this week and every refusal was worth
having.

## DD4, AND IT DECIDES BETWEEN THE ROUTES

**Maximize the code the two proofs share, and write it generic.** One rule,
two ends. It has NO metric and no checker by the owner's ruling, so it is
stated in every brief and answered in every return; the repetition is its only
enforcement.

**Tarski-Vaught is not about the Def tower.** It is a model-theoretic
equivalence, so route 1 delivers something the J tower can use unchanged,
while route 2 buys a step that is specific to how THIS hull encodes leastness.

**That is a real argument for route 1 and you should weigh it against the
price, not instead of it.** Say in the report what each route leaves the other
tower. If route 2 is much cheaper and route 1 much more general, give me both
numbers and your recommendation; the choice is mine to make.

- **Parameterize the MODULE, not the functions** (P-h).
- **Do not drag a stage presentation into a type** (P-l). `AtM` already takes
  its carrier abstractly; keep it that way.

## LITERATURE (DD18)

- **`dev2.txt:1071` is your target for route 1.** Devlin 5.1, which needs no
  transitivity. Quote it.
- **Devlin 5.3 is your target for route 2.** Find it in
  `_build/literature/dev2.txt` and quote the substitution step.
- `dev/literature/digest.md` for the orthodox route.
- `dev/literature/devlin-errata.md`: the book has known errors. 5.3 is inside
  the chapter the errata file concerns, so check before trusting a step.
- **`[LJ-0.7]` is digesting II.5 right now and its output is not available to
  you.** Work from the source, and say where your reading differs from the
  review's.

Return a **LITERATURE USED** section, with WHY NOT for anything skipped.

## ARCHIVE (DD18)

- `_build/lj-1.11-review.md:393-407`, F3, your commissioning document, and
  `:111` for how the review scored the hull against 5.3 and 5.4.
- `_build/lj-1.3-report.md`, especially section 4, which records that the hull
  is not transitive, and section 6, the three standing pieces.
- `archive/dev/TASKS-archived.md` and `archive/rud-route/`: the retired route
  had elementarity machinery. **Say whether its shape survives.**
- `dev/LESSONS.md` is NOT archived and still binds. **P-h, P-l, P-k, R-40 and
  D-10 decide this block.**

Return an **ARCHIVE USED** section at `file:line`.

## MANDATORY RULES FOR A BUILD

From `python3 scripts/rules.py --for build`. Run it and read each statement.

- **P-h. Definability walks are module-parameterized, never
  function-parameterized**, parameters ABSTRACT through the walk.
- **P-l. A statement may be ABOUT a concrete stage without dragging that
  stage's PRESENTATION into its type.**
- **P-k. A read lemma is stated where its consumers use it.**
- **P-m. The check-cost rate is a content-class certificate.**
- **P-n. Satisfaction content at a concrete carrier is a payable floor.**
- **R-35, R-38**: sealing and opacity.
- **R-40**: state a membership witness SHALLOW and climb.
- **I-5**: the inference trap this tree has paid for.
- **C-12.** `GHCRTS="-A64m -I0 -M8g" agda <file>`, ONE process. A sibling
  holds the other slot. Heap exhaustion is a wall to report, never a cap to
  raise.
- **C-22. Write the deliverable incrementally.** Fill each price as it lands,
  so a killed task still leaves its numbers.
- **D-10. Price the truth of a recorded residue before pricing its proof.** I
  verified F3's `file:line` claims. Its ROUTE suggestions are unpriced.

## THE SIBLING, AND THE TERRITORY RULE

`[LJ-1.13]` is building in `src/V/Collapse.lagda.md` right now. **Neither file
imports the other**, which I checked, so you are cone-disjoint and may both
measure. Keep it that way:

- **Write only `src/L/Hull.lagda.md`.**
- **Never run `git checkout .`, `git stash`, `git reset --hard` or `git
  clean`.** Revert by exact path only.
- **Never commit and never push.**

## SCOPE (read)

`_build/lj-1.11-review.md:393-407` first. Then `src/L/Hull.lagda.md:60-190` in
full, which is `AtM` and the equivalence. Then `dev2.txt` at 5.1 and 5.3. Then
`_build/lj-1.3-report.md` sections 4 and 6.

## SCOPE (write)

`src/L/Hull.lagda.md`. Your report is `_build/lj-1.14-report.md`. Never
`src/Everything.lagda.md`, and never `src/V/Collapse.lagda.md`.

## CONSTRAINTS

- **Do not weaken or delete what stands.** The transitive `TV-thm` is correct
  where it applies, and D-27 says a chapter's stated result is not deleted to
  make room for a generalization.
- **Typecheck every file you edit**, one process at a time. Do NOT run `make
  check` or a whole-tree check.
- **Count with `python3 scripts/ledger.py`'s caliber**, never by hand. DD26
  excludes the two catalogs from every size figure.
- **Report cold seconds**, before and after, with the noise rule: under 0.5 s
  or under 5 percent, whichever is larger, is flat.
- **Run `python3 scripts/lint-prose.py --check` and `python3
  scripts/lint-agda.py --check`.**
- **DD23 freezes mathematical prose.** Code and its own comments only.
- **Evidence is `file:line`.**
- **A refusal with two prices is a SUCCESS.**
- Write ASD-STE100 in the report.

## RETURN

Write `_build/lj-1.14-report.md` INCREMENTALLY, skeleton first.

1. **THE VERDICT**, first line: which route, delivered with a line count, or
   refused with both prices.
2. **THE TWO PRICES**, written BEFORE you built.
3. **WHERE `Mtr` IS SPENT**, at `file:line`, and what replaces it in route 1.
4. **THE NUMBER**: in-fence before and after, ledger caliber.
5. **SECONDS**: cold, before and after, with exit codes.
6. **WHAT EACH ROUTE LEAVES THE J TOWER** (DD4), and your recommendation.
7. **WHERE MY READING OF 5.1 AND 5.3 DIFFERS** from the review's, if it does.
8. **LITERATURE USED.**
9. **ARCHIVE USED.**
10. **WHAT I AM NOT SURE OF.**
