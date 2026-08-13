# LJ-1.4: build the Mostowski collapse

tier: codex (default)

## GOAL

Deliver `src/V/Collapse.lagda.md`: the transitive collapse by membership
recursion, carrier-generic, with the transitive-fixing clause the archive
lacks. Target 230 to 330 non-blank in-fence lines.

## CWD

`/Users/alsg/Agentic/Bedrock`, on branch `two-tower-bridge`.

## CONTEXT

`src/` proves `L ⊨ ZF` and `L ⊨ ZFC` on the internalization tower: 76 masters,
17,271 non-blank in-fence lines, cold 132.87 s. Phase 1 builds a `L ⊨ GCH`
wing on it, planned by `[LJ-1.1]` in `_build/lj-1.1-recon.md`.

**You are block 2 of that plan.** The collapse is the second step of the
condensation argument: a Skolem hull is extensional and well-founded, so it is
isomorphic to a transitive set, and condensation then identifies that set as
an earlier L stage.

**No prose.** DD23 freezes mathematical prose until both trophies land. Write
the marker structure a master needs and the shortest honest catalog line, and
nothing more. **This is code.**

**A sibling agent, `[LJ-1.3]`, is building the Skolem hull into
`src/L/Hull.lagda.md` right now.** `dev/LESSONS.md` C-25: two writers may not
share a file. **Your territory is `src/V/Collapse.lagda.md` and nothing else.**
Do not touch `src/L/Hull.lagda.md`, and do not touch
`src/Everything.lagda.md`, which the orchestrator wires.

## THE STATEMENT, from `[LJ-1.1]` block 2

For a transitive set carrier `X`:

- the collapse `π` by membership recursion;
- the range `πX` is transitive;
- `π` is one-to-one on `X`;
- membership is preserved in both directions;
- the transitive image is unique;
- **and the clause the archive does NOT have:** if `Y ⊆ X` is transitive,
  then `π` fixes `Y` pointwise. This is Devlin 5.2(ii). `[L3.32-T91]` section
  1.4 records that it is missing, and prices it at 50 to 150 lines.

## THE ARCHIVE IS A DELIVERED COMPARABLE, AND IT IS PORTABLE

`archive/rud-route/src/V/Collapse.lagda.md`, **181 non-blank in-fence lines**.
`[LJ-1.1]` read it and gave it the verdict **PORTABLE**, the strongest verdict
it gave anything: "It is carrier-generic and imports V.Hierarchy,
V.Presentation, V.Smallness, FOL.ZFStructure, and the library."

**`V.Presentation` is now back in the tree** (`src/V/Presentation.lagda.md`,
restored by `[LJ-0.6]` precisely so this port would work), so the import that
was missing is there.

**DD13 still applies: price the port against a fresh write before you take
it.** Read the archived chapter, decide whether porting or rewriting is
cheaper for the same content, and SAY WHICH YOU CHOSE AND WHY in your report.
A port is not automatically right because a file exists. `dev/LESSONS.md` P-l:
a measured cure does not transfer by analogy, so re-verify at this site.

**What the archive was built for matters.** It served the rud/J tower. The
collapse itself is carrier-generic and tower-neutral, which is why the verdict
is PORTABLE rather than ADAPTABLE, but check that claim rather than trusting
it.

## DD4, WHICH GOES IN EVERY BRIEF

**Maximize the code the two proofs share, and write it generic.** One rule,
two ends. It has NO metric and no checker by the owner's ruling, so it is
stated in every brief and answered in every return; the repetition is its only
enforcement.

**For this block DD4 is nearly the whole design question, and `[LJ-1.1]` has
already priced both shapes.** Generic in the carrier: 181 to 357 lines. Fixed
at a concrete carrier: about 250 to 420 lines, and it checks at instantiation
rates, which P-m puts near 0.22 s per line against 0.01 for parameterized
work, a twentyfold gap. **Generic wins on both axes and the archive is already
generic.** Keep it that way.

**And it matters beyond this wing.** A carrier-generic collapse serves the GCH
wing here, and it serves the two-tower route later at whatever carrier that
needs, because a collapse is a collapse. If you find yourself specializing to
`Lset`, stop and say why. **A stop-line is never a reason to write fixed:** say
so and stop for a re-price.

## MANDATORY RULES FOR A BUILD

From `python3 scripts/rules.py --for build`. Run it yourself and read each
statement. These bind:

- **P-h. Definability walks are module-parameterized, never
  function-parameterized**, and the parameters stay ABSTRACT through the walk.
  **The archived chapter is already `module Collapse X`; that is P-h and it is
  why it is cheap. Do not turn the carrier into a function argument.**
- **P-l. A statement may be ABOUT a concrete stage without dragging that
  stage's PRESENTATION into its type.** Naming a transparent construction in a
  TYPE is what costs.
- **P-k. A read lemma is stated where its consumers use it**, not where its
  proof ends.
- **P-m. The check-cost rate is a content-class certificate.** Parameterized
  work runs about 0.010 to 0.013 s per line, instantiation about 0.22 to
  0.297. **Your chapter should check at the parameterized rate; if it does not, the
  content class is wrong and that is a finding.**
- **P-n. Satisfaction content at a concrete carrier is a payable floor**, not
  a defect.
- **R-35, R-38**: the sealing and opacity discipline.
- **R-40. A deep successor-chain membership witness normalizes
  super-linearly; climb by small closures.**
- **I-5**: the inference trap this tree has paid for.
- **C-12. Agda runs under a hard heap cap.** `GHCRTS="-A64m -I0 -M8g" agda
  <file>`, ONE process, and a sibling holds the other slot. Report a heap
  exhaustion as a wall and never raise the cap.
- **C-22. Write the deliverable incrementally.** The chapter and the report
  both.
- **D-10. Price the truth of a recorded residue before pricing its proof.**
  The transitive-fixing clause is a recorded TARGET, not a delivered theorem.
  Check it is true at the generality you need before you price its proof.

## ARCHIVE

Per DD18.

- `archive/rud-route/src/V/Collapse.lagda.md`, 181 in-fence. **Your primary
  comparable.** Read it in full.
- `_build/lj-1.1-recon.md` block 2 and section 8's archive verdicts.
- `archive/dev/TASKS-archived.md`: `[T39]` delivered the transitive collapse
  and its probe was green and carrier-neutral; `[T91]` section 1.4 records the
  missing transitive-fixing clause.
- `dev/LESSONS.md` is NOT archived and still binds.

Report an **ARCHIVE USED** section at `file:line`, with what you took and what
you rejected.

## SCOPE (read)

`archive/rud-route/src/V/Collapse.lagda.md` first. Then
`src/V/{Hierarchy,Smallness,Presentation}.lagda.md`,
`src/FOL/ZFStructure.lagda.md`. Then `dev/STYLE-agda.md` and
`dev/STYLE-i18n.md` for the master's shape. Then `_build/lj-1.1-recon.md`.

## SCOPE (write)

`src/V/Collapse.lagda.md`, new, and your report `_build/lj-1.4-report.md`.
Nothing else under `src/`.

## CONSTRAINTS

- **Never commit and never push.** Leave the tree as your report describes it.
- **Typecheck your chapter** with `GHCRTS="-A64m -I0 -M8g" agda
  src/V/Collapse.lagda.md`, ONE process. Report exit code and seconds. Do NOT
  run `make check` or a whole-tree check: the orchestrator schedules those,
  and a sibling holds the other Agda slot.
- **Do not touch `src/Everything.lagda.md`.** The orchestrator wires it after
  auditing your work. Your chapter will not be in the tree index until then,
  which is expected.
- **Run `python3 scripts/lint-prose.py --check` and `python3
  scripts/lint-agda.py`** on your file before you finish. Both are cheap.
- **Count with `python3 scripts/ledger.py`**, never by hand.
- **Evidence is `file:line`.**
- **A stop is a deliverable.** If the transitive-fixing clause is false at the
  generality the plan needs, or the port is dearer than a fresh write, say so
  with the evidence and stop.
- Write ASD-STE100 Simplified Technical English in the report: active voice,
  one instruction per sentence, 20 words or fewer, no em dash.

## RETURN

Write `_build/lj-1.4-report.md` INCREMENTALLY, skeleton first.

1. **WHAT LANDED**: the statements delivered, at `file:line` in your chapter.
2. **PORT OR FRESH WRITE** (DD13): which you chose, the price of each, why.
3. **GENERIC OR FIXED** (DD4): what you kept generic, and anything you had to
   fix to a carrier, with the reason.
4. **THE TRANSITIVE-FIXING CLAUSE**: delivered or not, and its price.
5. **THE MEASUREMENT**: in-fence lines from `ledger.py`, typecheck seconds,
   exit code. Compute your seconds per line and compare it to the tree's
   0.007693 baseline (`dev/ledger.toml` `[ratio]`), because DD24 will judge
   the wing on that.
6. **ARCHIVE USED.**
7. **WHAT I AM NOT SURE OF.**
