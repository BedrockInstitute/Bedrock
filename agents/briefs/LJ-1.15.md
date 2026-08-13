# LJ-1.15: the one-clause probe that gates the whole crossing

tier: codex (default). **THROWAWAY PROBE under D-1: nothing lands, nothing is
committed, the deliverable is a report with two numbers.**

## GOAL

Price the widest unmeasured term of the crossing: the bounded table clause at
the Σ₁ shape, with its two-way decode at a variable carrier. **GO or NO-GO
with numbers, then throw the code away.**

## CWD

`/Users/alsg/Agentic/Bedrock`, on branch `two-tower-bridge`.

## WHY ONE PROBE GATES 3.3k LINES

`[LJ-1.12]` priced three crossing routes and recommends Route A at **3.3k
non-blank in-fence lines**, band 2.0 to 4.5k. **Route C is 3.2k and Route B is
2.8k, and those gaps are inside the survey error.** So the choice barely
matters and the PRICE does.

**This probe gates all three**, because all three rest on the same deep layer:
the bounded substrate. `dev/PLAN.md` DD8 says gate every block before you fund
it, and measuring the widest unmeasured term is what turns a projection into a
price. **3.3k lines is far too much to fund on a survey**, and this campaign
tested eight survey bands in `[LJ-0.4]` and watched five fail.

## THE TWO STATEMENTS, from `[LJ-1.12]` section 6

**STATEMENT 1, and it is the hard one.** Write the EXISTENTIAL clause of the
satisfaction table as a Δ₀ matrix with the bound as a FREE VARIABLE, stack the
Σ₁ certificate, and prove the two-way decode at a VARIABLE carrier.

The existential clause is the hardest of the twelve because its witness
existential is unbounded in the delivered form. **Do not pick an easier
clause.** The point is to price the worst case, not the average.

**STATEMENT 2, the carrier fact.** For `δ < α` at a limit `α`, the level
sequence `hierL (Lset δ)` and the chosen bound live in `Lset α`. The bound
must contain the codes over the carrier and the table values.

## THE GATE, FIXED BEFORE YOU START, AND YOU MAY NOT MOVE IT

- **GO** needs BOTH: statement 1 closes at **40 lines or fewer**, and
  statement 2 closes at **100 lines or fewer**.
- **NO-GO** is either of: the existential clause's matrix cannot decode
  without a NEW carrier fact, or the bound cannot be placed in the carrier
  with the delivered closure lemmas.

**A NO-GO is a full deliverable and it is worth more than a strained GO.** It
re-prices the crossing at the substrate's full band and stops `[LJ-1.5]` for a
re-price under DD8. Five of nine blocks in `[LJ-0.4]` refused with numbers and
every refusal changed the plan.

**Report the line counts even if you stop early.** A partial number beats a
verdict word.

## WHY THE Σ₁ FINDING DID NOT MAKE THIS CHEAPER

`[LJ-0.7]` found that Devlin's level-hood is Σ₁ with a Σ₀ matrix, not Δ₀, and
that re-opened the crossing after `[LJ-1.2]`'s NO-GO. **It did not shrink the
substrate**, and `[LJ-1.12]` is explicit about why: the Σ₀ matrix of the Σ₁
form IS Δ₀, so the bounded rewrites of the code set and the twelve-clause
table are unchanged. What changes is the certificate SHAPE, and what is ADDED
is the carrier facts.

**So do not expect the Σ₁ framing to make statement 1 easy.** It makes it
possible. That is a different thing and confusing them would produce a
cheerful wrong number.

## THE DD24 RISK, WHICH IS THE REAL ONE

`[LJ-1.12]`: all three routes land in the parameterized class **only if the
substrate stays at variable slots.** The decode legs are the risk.

`dev/LESSONS.md` **P-n**: satisfaction content at a CONCRETE carrier is a
payable floor, measured at 0.22 to 0.297 s per line. The wing's bar is
**0.013193**. **A concrete-carrier decode would blow it about seventeen
times.**

**So measure and report the SECONDS of your probe, not only its lines.** If
your decode only closes by going to a concrete carrier, that is a NO-GO on the
content class even if the line count is small. Say so with the rate.

## DD4, WHICH GOES IN EVERY BRIEF

**Maximize the code the two proofs share, and write it generic.** One rule,
two ends. It has NO metric and no checker by the owner's ruling, so it is
stated in every brief and answered in every return; the repetition is its only
enforcement.

**`[LJ-1.12]` already answered DD4 for this layer and the answer is
uncomfortable:** no route puts the crossing's core into the shared template.
The certificate is per-tower content by D-26. The J tower gets the TECHNIQUE
free, not the lines, and its own certificate runs about 470 to 610 lines plus
sixteen unmeasured op-clauses, so the asymmetry is about 2 to 3x rather than
an order of magnitude.

**Your job for DD4 is narrow: keep the substrate at VARIABLE SLOTS.** That is
what keeps it parameterized, and parameterized is what the other tower can
reuse at all. Say in the return whether a variable slot survived statement 1.

## LITERATURE (DD18)

- **`dev/literature/devlin-II5.md` section 2.3**, the six-item requirement
  list with strengths. Your statement 2 is its item 2, the witness living
  inside the carrier.
- `_build/literature/dev2.txt:593-630`, where Devlin binds the unbounded
  quantifiers by `K(u)` to make the matrix Σ₀, and then asks what set the
  bound can be. **That is exactly your statement 2 in the source.**
- `dev/literature/devlin-errata.md`: the satisfaction layer behind II.2.4 is
  where the known errata bind, and that is your layer.

**If nothing else bears, say so in one line naming `dev/literature/`.**

Return a **LITERATURE USED** section, with WHY NOT for anything skipped.

## ARCHIVE (DD18)

- **`_build/lj-1.12-report.md` section 6. This is your commissioning
  document.** Sections 2 and 4 give the prices your number will move.
- `_build/lj-1.2-gate.md` sections 3 and 5: the earlier NO-GO and its missing
  facts, which are the analogues of Devlin's substrate.
- `archive/rud-route/` and `archive/dev/TASKS-archived.md`: the retired route
  crossed this gap and T130 warned the crossing must carry the internalized
  definable-powerset step. **`[LJ-1.12]` says that warning transfers.**
- `dev/LESSONS.md` is NOT archived and still binds. **P-n is the law this
  probe tests, P-l keeps the slot variable, D-1 makes it throwaway.**

Return an **ARCHIVE USED** section at `file:line`.

## MANDATORY RULES FOR A PROBE

From `python3 scripts/rules.py --for probe`. Run it and read each statement.

- **D-1. A probe prices THIS setting.** It never re-proves what the literature
  or the delivered tree settles. Build the smallest decisive miniature and
  throw it away.
- **P-l. A statement may be ABOUT a concrete stage without dragging that
  stage's PRESENTATION into its type.** This is the rule that decides your
  content class.
- **P-i.** normalisation and heap.
- **C-12.** `GHCRTS="-A64m -I0 -M8g" agda <file>`, ONE process. A sibling
  holds the other slot. Heap exhaustion is a wall to REPORT, never a cap to
  raise.
- **D-10. Price the truth of a recorded residue before pricing its proof.**
  `[LJ-1.12]`'s section 6 is a residue: check that the delivered closure
  lemmas it assumes actually exist before you build on them.
- **C-22. Write the deliverable incrementally.** Fill each line count as it
  lands, so a killed probe still leaves its numbers.
- **R-40**: state a membership witness SHALLOW and climb.

## SCOPE (read)

`_build/lj-1.12-report.md` section 6 first. Then
`dev/literature/devlin-II5.md` 2.3. Then `src/L/Coding/` for the delivered
table and code set, and `src/L/Coding/Sequence.lagda.md` for `LsetGraphAt` and
the closure lemmas.

## SCOPE (write)

**Probe files only, named `src/Probe*.agda`.** They are untracked by standing
rule and `scripts/check-probes.py` refuses a commit that contains one, even
through `git add -f`. Your report is `_build/lj-1.15-report.md`. **No master
under `src/` may be edited, for any reason.**

## CONSTRAINTS

- **Never commit and never push. Delete your probe files when you are done**,
  or leave them and say so; they are untracked either way.
- **Do NOT edit any `.lagda.md` master.** If the probe needs a lemma the tree
  does not export, that is a FINDING: report it, do not add it.
- **Do NOT run `make check` or a whole-tree check.**
- **Count probe lines the same way**: non-blank lines inside the code.
- **Report SECONDS and the rate**, against the 0.013193 bar and P-n's 0.22 to
  0.297 floor.
- **Evidence is `file:line`.**
- **A NO-GO with numbers is a SUCCESS.**
- Write ASD-STE100 in the report.

## RETURN

Write `_build/lj-1.15-report.md` INCREMENTALLY, skeleton first.

1. **THE VERDICT**, first line: GO or NO-GO, with both line counts.
2. **STATEMENT 1**: lines, against the 40 gate, and what the matrix looks
   like.
3. **STATEMENT 2**: lines, against the 100 gate, and which closure lemmas it
   used.
4. **SECONDS AND THE RATE**, against 0.013193 and against P-n.
5. **DID A VARIABLE SLOT SURVIVE?** (DD4, P-l.)
6. **WHAT A NEW CARRIER FACT WOULD COST**, if you needed one.
7. **THE RE-PRICE**: what Route A's 3.3k becomes at your measured rate, twelve
   clauses plus the fixed legs.
8. **LITERATURE USED.**
9. **ARCHIVE USED.**
10. **WHAT I AM NOT SURE OF.**
