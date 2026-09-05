# LJ-1.540 report: B7 is paid, and it never wanted the subset hypothesis

## HEAD
head_slot: coder
machine: shared
verdict: GO

The report was written as a skeleton before any Agda and filled as each answer
landed (C-22). No commit, no push. I wrote only inside
`agents/tasks/LJ-1-540/`. Agda ran under the caliber the program set on this
pane, `GHCRTS="-A64m -I0 -M8g"`, ONE Agda process at a time. I did not set
`GHCRTS`. No heap event: peak footprint 1,495,991,952 bytes, about 1.4 GiB,
against an 8 GB cap (`runs/final-8.out`). Nothing is postulated and there is no
hole. The probe is a raw `.agda` file, so it carries no ` ```agda ` fence,
counts 0 in-fence lines,
and the ratio bar cannot fire on it.

**GATES RUN.** `lint-prose`, `lint-agda`, `check-probes`, `check-fences`,
`check-glossary`, `check-closure`, `check-spec-surface`, `weave-i18n --check`
and `ledger --check`: all clean. I did NOT run `make typecheck`. `git status`
shows one entry, the untracked `agents/tasks/LJ-1-540/`, so no master changed
and a whole-tree typecheck would measure nothing about this task. The worktree
carries no `.venv`, so every gate ran as
`/Users/alsg/Agentic/Bedrock/.venv/bin/python`, the pinned interpreter of the
main checkout, with the working directory left in this worktree.

## VERDICT

**GO. `AbsorbsAt` IS INHABITED** at the brief's type, letter for letter, at
`agents/tasks/LJ-1-540/Probe540.agda:359-365`. Exit 0 on every run, and the
runs are named by what each one measured:

| runs | what the file was | result |
|---|---|---|
| `runs/w3-1.out` to `runs/w3-3.out` | the W3 slice ALONE, kept at `runs/w3-slice.agda.txt` | exit 0, 0.84 to 0.89 s |
| `runs/full-1.out` to `runs/full-3.out` | the probe before section 1B was added | exit 0 |
| `runs/final-1.out` to `runs/final-4.out` | the same, with the probe's own interface removed first | exit 0 |
| `runs/final-5.out` to `runs/final-7.out` | with section 1B, before the header comment was extended | exit 0 |
| `runs/final-8.out` to `runs/final-10.out` | **the file exactly as this report describes it**, 376 lines | exit 0, 13.03 to 13.11 s |

Every `final-*` run, and `w3-2` and `w3-3`, deleted
`_build/2.8.0/agda/agents/tasks/LJ-1-540/Probe540.agdai` first, because Agda
skips a file whose content is unchanged and a run that skips measures nothing.
`runs/full-2.out` and `runs/full-3.out` are the two runs that did NOT delete it,
and they carry no "Checking" line for exactly that reason. They are used once
below, as the interface-load baseline, and nowhere else.

**NO `InjCode` AND NO `Formula` ENTER THE FILE.** The conclusion is the bare
ambient `_↪_` of `src/L/BoundedSubset.lagda.md:1043-1044`, which is the exact
type the consumer's parameter carries at `src/L/BoundedSubset.lagda.md:1392`.
Neither closed route of `[LJ-1.533]` and `[LJ-1.535]` is entered, so the coding
wall is not touched.

**THE ONE FINDING THAT CHANGES THE NEXT BRIEF: B7 DOES NOT NEED `x⊆Lα`.** The
fourth hypothesis of the type is bound and never used. This is measured by the
elaborator and not claimed in prose: `absorbs-needs-no-subset-hypothesis`
(`agents/tasks/LJ-1-540/Probe540.agda:371-376`) is the same term at the same
conclusion with that hypothesis deleted, and it typechecks. If any line
under `AbsorbsAt` consumed
`x⊆Lα`, that term would not exist.

**A SECOND FINDING, AND IT CONTRADICTS THE BRIEF'S ARITHMETIC.** The brief says
"THE JOIN HAS SIX UNPAID INPUTS AND FIVE OF THEM WANT A CODE". **Measured, only
two of the six want a code.** The count is in the required section below.

## D-10, BEFORE ANY AGDA

**THE QUESTION.** "Say at `file:line` whether `x` itself is in `Lset α`, and if
not, why adjoining it does not increase the cardinality."

**THE ANSWER: NO, AND THE WITNESS IS CHECKED RATHER THAN ASSERTED.**

The type gives only `x ⊆ Lset α`
(`agents/tasks/LJ-1-523/Probe523.agda:237`), never `x ∈ˢ Lset α`.
The gap is real, and `module D10`
(`agents/tasks/LJ-1-540/Probe540.agda:119-138`) exhibits it at
`α := ω` and `x := ω`, which satisfy every hypothesis of B7:

- `IsOrd ω` is `ω-ord` (`src/L/Ordinal.lagda.md:263-264`).
- `ω ∉ ω` is `∈-irrefl ω` (`src/V/Hierarchy.lagda.md:155-156`), so the third
  hypothesis holds.
- The fourth hypothesis HOLDS: `hypothesis-holds`
  (`agents/tasks/LJ-1-540/Probe540.agda:129-132`)
  gives `(z : S) → ⟨ z ∈ˢ ω ⟩ → ⟨ z ∈ˢ Lset ω ⟩`.
- The membership FAILS: `membership-fails`
  (`agents/tasks/LJ-1-540/Probe540.agda:137-138`) gives
  `⟨ ω ∈ˢ Lset ω ⟩ → Empty.⊥`, through `ord∈Lset→∈`
  (`src/L/Ordinal/Stages.lagda.md:265-266`) and irreflexivity.

**SO THE INJECTION MUST GENUINELY PLACE A NEW ELEMENT, AND IT STILL COSTS
NOTHING.** The reason is that `Lset α` is Dedekind-infinite for EVERY infinite
ordinal α: `num∈L` (`agents/tasks/LJ-1-540/Probe540.agda:90-92`) puts every
numeral in the stage, and
the numerals are the room the shift uses. The map sends the numeral `# k` to
`# (suc k)`, sends `x` to `# 0`, and fixes everything else.

**NO LIMIT HYPOTHESIS IS NEEDED, SO THIS IS NO FINDING AGAINST `[LJ-1.523]`'s
ROW.** The brief asked me to say so if a limit were needed. It is not: `α ∉ ω`
alone puts every numeral in α (`num∈α`,
`agents/tasks/LJ-1-540/Probe540.agda:79-84`), and that is the
whole supply the construction consumes. **`archive/dev/LJ-dispatch-index.md:179`
records that this premise was chosen for exactly this reason at `[LJ-1.103]`.**

## W3, AND IT RAN FIRST

**THE QUESTION.** "the image of `⁅ x ⁆s` under the injection, as a term".

**THE ANSWER, IN ONE SENTENCE. x GOES TO THE NUMERAL 0 OF THE STAGE, AND NOTHING
ABOUT x ENTERS THE ANSWER.**

`xImage` (`agents/tasks/LJ-1-540/Probe540.agda:97-98`) is `fiber (Lset α)
(num∈L 0) .fst`, the member
of `Lset α` whose value is `# 0`. Its whole cost is one fact about the stage,
`num∈L` (`:90-92`): an infinite ordinal's stage holds every numeral. That fact
is built in two steps, and neither mentions x:

1. `num∈α` (`:79-84`). Every numeral is a member of α. Trichotomy
   (`ord-tri`, `src/L/Ordinal/Linear.lagda.md:136`) against ω, with `α ∉ ω`
   killing the first branch. This is `one∈α`
   (`src/L/BoundedSubset.lagda.md:1206-1212`) at every k rather than at k = 1,
   and the generalization costs nothing.
2. `num∈L` (`:90-92`). The numeral sits at the stage after itself
   (`ord∈Lset-suc`, `src/L/Ordinal/Stages.lagda.md:434`) and monotonicity
   carries it up (`Lset-mono`, `src/L/Constructible.lagda.md:355`). This is the
   shape of `numeral∈limit` (`src/L/Choice/Name.lagda.md:121`) with ω replaced
   by α.

**THE BRIEF ASKED WHAT THE SHIFT COSTS IF NO PLACE CAN BE FOUND WITHOUT MOVING
THE REST. THE MEASURED ANSWER: THE REST DOES MOVE, AND IT COSTS 105 LINES.**
Only the numerals move, one step each. The non-numeral members are fixed. That
displacement is the whole content of `module Shift`
(`agents/tasks/LJ-1-540/Probe540.agda:217-347`),
105 non-blank non-comment lines, of which the injectivity matrix is 44.

**COST OF W3.** The slice was typechecked ALONE first, before the rest of the
file existed. It is kept at `runs/w3-slice.agda.txt` and its runs are
`runs/w3-1.out` to `runs/w3-3.out`: 0.84 s, 0.89 s and 0.89 s, exit 0 each. The
brief estimated about 25 lines and under 40 seconds. **Measured: 14 non-blank
non-comment lines and under 0.9 s.** The brief's estimate was high on both, and
the reason is the second half of the answer: nothing about x enters, so W3 never
had to reason about the adjoined element at all.

## WHAT TRANSFERS FROM `absorbs` AND WHAT DOES NOT

The brief ordered this said at `file:line`. C-42 is respected throughout: the
two statements are different and this file never reads one as the other.

**WHAT TRANSFERS, AND IT IS PART 1 OF THAT CHAPTER ONLY.** `ShiftAbs`
(`src/L/Absorption.lagda.md:74-192`) supplies the METHOD, not the statement:

| piece | there | here |
|---|---|---|
| three-case split, decided by `lem` | `shift-dec` (`:102-107`) | `shift-dec` (`agents/tasks/LJ-1-540/Probe540.agda:232-238`) |
| one readback lemma per case | `shift-top`, `shift-num`, `shift-other` (`:113-147`) | `agents/tasks/LJ-1-540/Probe540.agda:251-290` |
| injectivity, sixteen corners on four decisions | `shift-inj` (`:148-190`) | `shift-inj` (`agents/tasks/LJ-1-540/Probe540.agda:292-338`) |

**WHAT IS BORROWED WHOLE, AND THE ELABORATOR SETTLES IT.** Three numeral
lemmas, `numeralOf`, `numeralOf-spec` and `numeralOf-uniq`
(`src/L/Absorption.lagda.md:78-89`). They mention no module parameter, so
instantiating `ShiftAbs` at `γ := α` takes them at the identical type
(`agents/tasks/LJ-1-540/Probe540.agda:221`). Section 1 has already paid for
the four arguments that
instantiation needs.

**WHAT DOES NOT TRANSFER, and each is a line of this file.**

1. **`∈sucV-elim` (`src/V/Model.lagda.md:218-228`).** The domain here is a union
   with a singleton, not a successor. `Adjoin.X-elim`
   (`agents/tasks/LJ-1-540/Probe540.agda:172-186`) replaces it, and it is the
   ONE direction of the
   union this file uses.
2. **`numerals` AS A HYPOTHESIS.** `ShiftAbs` is handed it. B7 must DERIVE it
   for `Lset α`, which is section 1.
3. **`γ∉ω` AT THE TOP ELEMENT, AND THIS IS THE ONE REAL CHANGE.** `ShiftAbs`
   proves `shift-top` (`src/L/Absorption.lagda.md:113-122`) from "the top is not
   a numeral", discharging the numeral corner with `γ∉ω`. **B7 HAS NO SUCH
   HYPOTHESIS: its x may well be a numeral.** So `shift-top` here
   (`agents/tasks/LJ-1-540/Probe540.agda:251-261`) takes the case decision
   `¬v∈ω` as an ARGUMENT
   instead. Every call site already stands in an `inr` corner of `shift-inj`,
   so the argument is free at all four uses
   (`agents/tasks/LJ-1-540/Probe540.agda:314`, `:320`,
   `:324` and `:332`). **This is why B7 needs no hypothesis on x at all.**
4. **PARTS 2 to 4 of that chapter** (`ShiftFo`, `Carve`, `ShiftGraph`,
   `src/L/Absorption.lagda.md:193-626`). They build the `InjCode`. This
   obligation is ambient and enters none of them.

**`UnionKit` IS NOT REUSABLE AND I SAY WHY.** It has the elimination already,
as `X-mem` (`src/L/BoundedSubset.lagda.md:1171-1188`) and `sgl≡` (`:1167-1169`).
It also takes `lam`, `ordλ`, `α∈λ` and `x∈Lλ` as parameters
(`src/L/BoundedSubset.lagda.md:1145-1147`), and B7's type gives none of them.
So section 2 rewrites the one direction at B7's own hypotheses, 28 lines.

## CHOICE

**THE TERM IS CHOICE-FREE.** It spends the excluded middle and nothing else.

- `lem` is the module parameter, the same `LEM (ℓ-suc ℓ)` that
  `L.BoundedSubset` (`src/L/BoundedSubset.lagda.md:10`) and `L.Absorption`
  (`src/L/Absorption.lagda.md:10`) carry.
- The two decisions per member are `lem` applied to two hProps, membership in
  ω and equality with x (`agents/tasks/LJ-1-540/Probe540.agda:240-242`).
- `ord-tri` (`src/L/Ordinal/Linear.lagda.md:136`) spends `lem`.
- The only selection is `numeralOf`, and it is a DEFINABLE least element, not a
  choice: `leastOf` over `natOrder` (`src/L/WellOrder/Base.lagda.md:158-161`,
  `src/L/Choice/Finite.lagda.md:596`), whose result is unique
  (`isPropLeastOf`).
- Every truncation elimination in the file lands in an hProp: `X-elim`
  (`agents/tasks/LJ-1-540/Probe540.agda:172-186`) rec's into
  `⟨ z ∈ˢ Lset α ⟩`.

This matches `[LJ-1.528]`'s `CardAboveL` and `[LJ-1.94]`'s Hartogs, which the
brief names: no choice is taken.

## WHAT B6, B8 AND B10 WANT

Required section. **I built none of the three.** The verdict per row is a
TYPE-LEVEL question, and I answer it mechanically: does the row's conclusion
name `InjCode`, `InjL` or `Formula`? A count of those three tokens over each
row's own lines is the whole measurement.

| row | its lines | code tokens in the type | verdict |
|---|---|---|---|
| B6 `SubsetIntoStage` | `agents/tasks/LJ-1-523/Probe523.agda:224-228` | 0 | **AMBIENT** |
| B8 `LimitAbove` | `:244-251` | 0 | **AMBIENT** |
| B10 `SuccIntoPower` | `:266-269` | 1, `InjL` | **WANTS A CODE** |

**B6, `SubsetIntoStage`. AMBIENT.** Its conclusion is
`⟨ z ∈ˢ Lset (fst κ) ⟩` (`agents/tasks/LJ-1-523/Probe523.agda:227`) at the
V-carrier, opened from
`𝒮ᵥ` at `agents/tasks/LJ-1-523/Probe523.agda:35`. **Its HYPOTHESIS is model-side**,
`⟨ fst y ∈ˢ fst (𝒫 κ) ⟩` at `:226`, so it CONSUMES the L-model's power set. It
demands no code of its output. It is a crossing in the cheap direction: model
in, ambient out.

**B8, `LimitAbove`. AMBIENT, and it is the cleanest of the three.** Its
conclusion (`agents/tasks/LJ-1-523/Probe523.agda:247-251`) is a truncated Σ
of `IsOrd`, `∈ˢ` and
`Lset` facts, all at the V-carrier. Not one token of the coding vocabulary
appears in the row, hypothesis included. `⟨ isL x ⟩` at `:246` is a membership
in a stage by definition (`src/L/Constructible.lagda.md:377`), not a code.

**B10, `SuccIntoPower`. WANTS A CODE, AND IT IS THE ONLY ONE OF THE THREE THAT
DOES.** Its conclusion is `InjL δ (𝒫 κ)`
(`agents/tasks/LJ-1-523/Probe523.agda:268`), and `InjL a b`
unfolds to `∥ Σ[ F ∈ S ] InjCode F a b ∥₁` (`src/L/GCH.lagda.md:38`). So it
needs an L-ELEMENT `F` first, then the four conjuncts of `InjCode`
(`src/L/Cardinal.lagda.md:223-229`). `[LJ-1.535]` reported that B10 has no
shadow in `src/` to restate, and I confirm the type side of that: this is an
unbuilt leg, not a blocked one.

**WHERE `[LJ-1.523]` AND THIS MEASUREMENT DIFFER, AND WHY BOTH ARE RIGHT.**
`agents/tasks/LJ-1-523/lj-1.523-report.md:307` calls B6 "A CODING fact about the
stage tower". That classifies the SUBJECT: the row is about the constructible
tower. It does not say the row's type demands an `InjCode`, and the type does
not. **The two questions have different answers and the coding wall only cares
about the second one.**

**THE ARITHMETIC THE BRIEF ASKED FOR, RESTATED FROM MEASUREMENT.** Six inputs
were unpaid after `[LJ-1.528]` paid B4
(`agents/tasks/LJ-1-528/lj-1.528-report.md:339-340`): B5, B6, B7, B8, B9, B10
(`agents/tasks/LJ-1-523/lj-1.523-report.md:230-235`). **B7 is now paid, so five
remain.** Of those five:

- **B6 and B8 are AMBIENT.** Neither meets the coding wall.
- **B9 and B10 WANT A CODE.** B9 is priced by `[LJ-1.535]`: one new
  object-language formula at `L.StageCardinal`'s own site. B10 has no shadow.
- **B5 `AmbientSpentAtSucc` (`agents/tasks/LJ-1-523/Probe523.agda:218-220`) is
  a CROSSING and it is
  the hard direction.** Its conclusion `CardSpentAt (fst δ) (fst κ)`
  (`:215-216`) is an ambient refutation, but its hypothesis `SuccCardL δ κ`
  carries `IsCardinalL δ` (`src/L/GCH.lagda.md:46-52`), which quantifies over
  `InjCode` (`src/L/Cardinal.lagda.md:230-233`). So B5 consumes a code and must
  produce an ambient fact. `[LJ-1.523]` calls this "the row the whole bridge
  turns on" (`agents/tasks/LJ-1-523/lj-1.523-report.md:287`).

**SO THE BRIEF'S "FIVE OF SIX WANT A CODE" IS WRONG BY MEASUREMENT. TWO OF THE
FIVE REMAINING WANT A CODE, TWO ARE AMBIENT, AND ONE CROSSES.** That is the
split the brief said was worth the dispatch on its own.

## WHAT THE LANDING WOULD COST, MEASURED AND NOT GUESSED

I did NOT land anything. The brief forbids it and I obeyed. What I measured for
whoever writes that brief:

1. **THE FIT IS EXACT AND NEEDS NO ADAPTER.** `BoundedSubsetAt`'s telescope
   already binds all four arguments before the `absorbs` parameter:
   `α`, `ordα`, `α∉ω` at `src/L/BoundedSubset.lagda.md:1387`, `x` and `x⊆Lα` at
   `:1391`, and the parameter itself at `:1392`.
2. **THE IMPORT DIRECTION IS FREE.** `L.BoundedSubset` does not import
   `L.Absorption` today, and `L.Absorption`'s transitive import closure (50
   modules) does not contain `L.BoundedSubset` or `L.StageBound`. So
   `L.BoundedSubset` MAY import `L.Absorption` with no cycle. **The alternative
   is to inline `NP` and the three numeral lemmas
   (`src/L/Absorption.lagda.md:78-91`), 11 non-comment lines, and import
   nothing.**
3. **THE RATIO BAR IS A REAL RISK AT THAT SITE AND THE LANDING BRIEF MUST
   DESIGN FOR IT.** This probe elaborates in about 10.2 s (13.06 s total minus
   a 2.86 s interface-load baseline: `runs/final-8.out` against
   `runs/full-2.out`, which carries no "Checking" line because Agda skipped the
   unchanged file and only re-loaded interfaces) for 201
   non-blank non-comment lines. That is about 0.05 s per line, four times the
   0.0123 s bar. **THIS IS A PROBE FIGURE AND MUST NOT BE QUOTED AS A CHAPTER
   PRICE**: the divisor is different (in-fence lines, not file lines) and a
   chapter inside `L.BoundedSubset` would not pay to load that module's own
   interface. I did not measure the chapter form and nothing may be funded
   against this number.

## WHAT I DID NOT DO

- I did not land anything in `src/`. The tree is unchanged outside
  `agents/tasks/LJ-1-540/`.
- I did not discharge `BoundedSubsetAt`'s hypothesis
  (`src/L/BoundedSubset.lagda.md:1392`). That is a landing and this is a probe.
- I did not build an `InjCode` and did not look for a `Formula`. Both routes are
  closed by `[LJ-1.533]` and `[LJ-1.535]` and this obligation is ambient.
- I did not build B5, B6, B8, B9 or B10.
- I did not postulate, and I left no hole.
- I did not set `GHCRTS`, and I ran one Agda process at a time.
- **I did not prove that my `shift` is `absorbs`
  (`src/L/Absorption.lagda.md:635-638`) under any identification.** It is not:
  the domains differ. C-42 forbids reading one as the other and this file states
  the difference at `agents/tasks/LJ-1-540/Probe540.agda:188-215` rather than
  assuming it away.
- **I did not measure whether B6 and B8 are EASY, only that they are AMBIENT.**
  Ambient is a statement about the type, not about the price. B6 in particular
  consumes the L-model's power set and I did not price that consumption.
- I did not write `review-of-AbsorbsAt.md`. That file states a NO-GO and this
  is a GO.

## THE NUMBERS

| item | estimate | measured |
|---|---|---|
| probe, total | about 160 lines | 376 lines, 331 non-blank, 201 non-blank non-comment |
| the obligation `AbsorbsAt` alone | about 50 lines | 7 non-comment (`agents/tasks/LJ-1-540/Probe540.agda:359-365`) |
| the obligation's WHOLE chain | about 50 lines | 160 non-comment: W3 14, `Adjoin` 28, `Shift` 105, section 4 13 |
| the injectivity matrix alone | not estimated | 44 non-comment (`agents/tasks/LJ-1-540/Probe540.agda:292-338`) |
| the D-10 witness | not estimated | 11 non-comment (`agents/tasks/LJ-1-540/Probe540.agda:119-138`) |
| W3 | about 25 lines, under 40 s | 14 non-comment; 0.84, 0.89, 0.89 s (`runs/w3-1.out` to `runs/w3-3.out`) |
| typecheck, whole probe | not estimated | 13.06, 13.11 and 13.03 s; peak footprint about 1.4 GiB (`runs/final-8.out` to `runs/final-10.out`) |
| typecheck, cold `L.Absorption` | not estimated | 16.47 s (`runs/full-1.out`), the one run that compiled that chapter from source |
| attempts to green | not estimated | ONE. `runs/w3-1.out` and `runs/full-1.out` were both exit 0 at the first attempt, and no line was written to fix a type error |

**THE ESTIMATE SPLIT THE WRONG WAY.** The brief put 50 of its 160 lines on the
obligation. Measured, the obligation's own definition is 7 lines and its
supporting chain is 160. **The cost is not in stating the injection. It is in
the sixteen-corner injectivity matrix, which is 44 lines and which the brief did
not name.** The comparable the brief offered was of SHAPE only and nothing was
funded against it, as the brief required.

The typecheck figures are the probe alone with the tree's interfaces warm. They
are not a chapter price and must not be quoted as one.

## ARCHIVE USED

- `archive/dev/LJ-dispatch-index.md`: **READ AND USED, AND IT SETTLED THE D-10
  QUESTION.** `:179` is
  "| LJ-1.103 | Restate absorbs-subset and re-check Devlin55 | REPAIRED,
  MASTER GREEN | The premise is alpha not in omega, matching sq. My suggested
  premise was too strong: the site runs at omega |".
  That is the record of WHY this row carries `α ∉ ω` and no limit hypothesis,
  and my construction consumes exactly that premise and nothing more. `:177` is
  "| LJ-1.101 | Close the cardk type gap, then price sq | GAP CLOSED, GREEN |
  cardk checks at the master's IsCardinal, no transport. And absorbs-subset is
  REFUTED, so Devlin55 is vacuous |",
  a prior REFUTATION at this shape, and it is why I checked the D-10 witness in
  Agda rather than asserting it.
- `archive/dev/JOURNAL-archived.md`: **DECLINED.** `:1` is
  "# Archived journal: the retired route". B7 is on the live route. Not used.
- `archive/dev/JOURNAL.md`: **DECLINED.** `:1` is "# ARCHIVED 2026-08-20". The
  per-episode journal is retired in favour of `agents/tasks/<CODE>/`, and every
  predecessor this task needed was in those task directories. Not used.
- `dev/ARCHIVE.md`: **DECLINED.** `:1` is "# ARCHIVE.md: the archive registry".
  It registers retired MODULES. This task retires none and lands nothing. Not
  used.
- `archive/dev/DECISIONS-archived.md`: **DECLINED.** `:1` is
  "# Archived decisions: the D series". A bare `D<n>` is not a rule in force.
  Not used.

## LITERATURE USED

- `dev/literature/devlin-II5.md`: **READ AND USED.** `:274` is
  "Requirement: |ℒ_X| = max(|X|, ω), so the hull has at most max(|X|, ω)". That
  is the source's own form of B7: a union with a small set is absorbed because
  the other side is infinite. I read it to confirm that the source treats this
  step as a cardinal fact with no coding content, which is what the GO measures.
- `dev/literature/truncation-and-selection.md`: **READ AND USED.** `:110` is
  "**`Q` is leastness.** HoTT Book Exercise 3.19 is the instance over `ℕ`:".
  That is the law behind `numeralOf`, the one selection this term makes: a least
  natural number under a definable well-order, which is unique and therefore not
  a choice. It is why the CHOICE section above says the term is choice-free.
- `dev/literature/terms-2026-08.md`: **DECLINED.** `:1` is
  "# The terminology dossier: fourteen renderings for the owner's ruling". This
  report names no new term and adds no glossary entry. Not used.
- `dev/literature/digest.md`: **DECLINED.** `:1` is
  "# Digest: the orthodox form of the rud route, pinned from the collected literature".
  B7 sits on the `Def` tower and no claim here turns on a rud fact. Not used.
- `dev/literature/glossary-review-2026-08.md`: **DECLINED.** `:1` is
  "# Glossary review: the 119 pre-protocol entries". This task proposes no
  glossary entry. Not used.
