# LJ-1.353 report: how hard is `L ⊨ Cantor-Bernstein`?

Written incrementally from the first five minutes (C-22). All runs used one
Agda process with `GHCRTS="-A64m -I0 -M8g"`. The cap was never raised. The
slot count was read before every invocation (C-12) and was 0 each time.

## VERDICT

**EXPENSIVE for the internal statement: about 650 lines, SURVEY.**
**CHEAP for the ambient port: 80 code lines, MEASURED, and the miniature ran
green.**

The owner's correction split the question in two, and each half has its own
price. Read the two halves separately.

1. `L ⊨ Cantor-Bernstein` read literally demands a coded bijection inside L.
   That theorem costs about 650 lines. The basis is a survey over four
   measured comparables, listed in section 5.
2. The ambient theorem at the carrier costs 80 non-blank code lines. This is
   MEASURED twice. The archived route delivered it at
   `archive/src/2026-08-09-rud-route/L/Cardinal.lagda.md:89-190`, and a probe
   of the live series built 97 lines at
   `agents/tasks/LJ-1-107/lj-1.107-report.md:51`. My miniature copied the
   archived block onto the live tree. It typechecked on the first attempt:
   `agents/tasks/LJ-1-353/AmbCsb.agda`, exit 0, 1.65 s wall, empty-file floor
   0.63 s (C-53).

**The ruled trophy needs NEITHER.** The two-injection statement stands alone.
See section 6 for what each option would buy.

## 1. Does the tree already hold it? (D-10, C-57, C-44)

**MEASURED. The live tree holds no Cantor-Bernstein, and the repository holds
two ambient copies outside `src/`.** The brief searched `src/` with four
literal greps. The correction points at the archive, and the archive answers.

The semantic search over the live tree found the parts, not the theorem:

- The range machinery is delivered. `Range` builds the image set by
  replacement, and `RanHolds.holds` proves the built set satisfies the range
  formula. See `src/L/Coding/Injection.lagda.md:186-282`. The formula
  `ranAt` is two-directional and has three adequacy lemmas at
  `src/L/Coding/Injection.lagda.md:230-260`.
- Coded-injection arithmetic is delivered. `Comp` composes two coded
  injections, and `Carve` carves an inclusion as a coded injection. See
  `src/L/InjChain.lagda.md`, 502 code lines.
- The composite condition `compFo` is delivered with adequacy. It states
  `pr(x,z)` belongs to the composite through a middle witness. See
  `src/L/InjChain.lagda.md:213-261`.

**MEASURED absent in the live tree:** no bijection predicate, no `bijAt`
formula, no antisymmetry of `InjL`, no ambient Cantor-Bernstein. Greps for
`antisym`, `Bernstein`, `bijection`, `surject`, `Schroeder` over `src/`
return nothing that is this theorem. `≈ˢ` is structure equality, a field at
`src/FOL/ZFStructure.lagda.md:48`.

Outside `src/`, the repository holds the ambient theorem twice:

- The archived route delivered `csb` at
  `archive/src/2026-08-09-rud-route/L/Cardinal.lagda.md:89-190`. Two
  injections give a bijection as an injection plus mere surjectivity. The
  block is 80 non-blank code lines, 102 with blanks.
- The live series built it in a probe. `[LJ-1.107]` reports `CSB` at 97 lines
  plus 81 header and import lines, 2.03 s of a 117 s run. See
  `agents/tasks/LJ-1-107/lj-1.107-report.md:51`.

The task index closes the audit (C-44). Section 11 of `dev/PLAN.md` records
the question twice. Row `[LJ-1.156]` at `dev/PLAN.md:1068` dissolved the need:
leastness over injections closed all three CSB sites, so the live route
dropped it. Row `[LJ-1.157]` at `dev/PLAN.md:1069` found the archived CSB
"surfaced twice, lost twice".

## 2. What `L ⊨ ZFC` buys: the model record's fields

The record sits at `src/FOL/ZFModel.lagda.md:187-197`, and the instance at
`src/L/Model.lagda.md:83-100`. Cantor-Bernstein is a theorem of ZF, so the
axioms suffice in principle. In this tree every step must be a satisfaction
fact, so the honest question is which fields an internal proof consumes.

**The Tarski form of the proof needs `hasSeparation` and `hasPower`, and
nothing else.** Both are delivered as L theorems: `hasSeparationL` at
`src/L/Axioms/Full.lagda.md:144` and `hasPowerL` at
`src/L/Axioms/Power.lagda.md:187`.

- Separation carves the bad set from `a` itself, so `a` is the bound. No
  stage device is needed for it.
- The power field supplies `𝒫 a`, which bounds the one quantifier of the
  Tarski formula. See section 4.
- `hasChoice` is not needed. See section 5.
- `hasReplacement` is not needed by the Tarski form. The chain form of the
  classical proof would need it, or a coding of finite sequences. That
  difference is the reason the port should take Tarski.

The graph of the patched map needs a bound for its pairs. The delivered
`StageBound` device builds that bound with no axiom at all. See
`src/L/InjChain.lagda.md:73-102`.

## 3. The missing vocabulary, priced against `InjCode`

`InjCode` is a four-part product at `src/L/Cardinal.lagda.md:223-228`. The
fourth part is a one-directional range clause at the meta level.

**A bijection predicate is `InjCode` with the fourth clause replaced by one
satisfaction conjunct.** Write `BijCode F a b` as the first three conjuncts
plus `⟨ (F ∷ b ∷ []) ⊨ ranAt zero (suc zero) ⟩`. The formula `ranAt` states
the range of `F` IS `b`, in both directions, and it is delivered with its
adequacy lemmas. The old fourth clause follows from `ranAt-out`.

So the vocabulary costs about 20 lines, and the basis is MEASURED: the
delivered shape of `InjCode` and the delivered `ranAt` block. The ruling of
`[LJ-1.323]` section 7.4 said the same thing in one line: a coded bijection
is expressible today through `ranAt`. See
`agents/tasks/LJ-1.323/lj-1.323-ruling.md:382-385`.

## 4. Which proof to port, and what it assumes

**For the ambient port: the archived chain proof, verbatim.** My miniature
copied it onto the live tree with two edits. The carrier moved from the
retired `S` to `V ℓ`, and the imports moved to the live modules. Exit 0 on
the first attempt. The port is an import rewiring.

**For the internal theorem: the Tarski form, not the chain form.** The two
forms differ sharply in what they demand inside L.

- The chain form builds the bad set as a union over `ω`. Inside L that needs
  replacement over `ω`, or a coding of finite chains. Both are real chapters.
- The Tarski form defines the bad set as the union of every closed subset of
  `a`. One separation carves it, with one formula that quantifies over
  members of `𝒫 a`. The quantifier is first-order, because `𝒫 a` is a set.
- The closure condition reuses delivered vocabulary. "Closed under `g ∘ f`"
  is the chain shape of `compFo`, already written with adequacy at
  `src/L/InjChain.lagda.md:213-261`. "Outside the range of `g`" is the
  delivered `inRanAt` shape at `src/L/Coding/Injection.lagda.md:221-229`.

**Neither proof needs choice.** The miniature shows the mechanism. The
inverse of `g` is extracted by `fiberG`, and `fiberG` runs on the
propositionality of the fiber, which follows from injectivity. Excluded
middle enters through `lowerLEM`, and LEM is already the module parameter of
every L chapter. The first trophy proves choice, so this absence matters: the
port adds no circularity.

## 5. The internal price and its parts

The survey number is about 650 lines. Each part names its basis.

| Part | Lines | Basis |
|---|---|---|
| `BijCode` and `BijL` | 20 | MEASURED shape, `src/L/Cardinal.lagda.md:223-228` |
| The Tarski formula and its adequacy | 150 | MEASURED comparable, `ShiftFo` in `src/L/Absorption.lagda.md:228-379` |
| The bad set and its three closure facts | 250 | SURVEY, the archived 30 ambient lines times the internalization overhead of the delivered conjunct blocks |
| The graph carve and four conjuncts | 200 | MEASURED comparables, `Comp` and `Carve` in `src/L/InjChain.lagda.md` |
| Readback and assembly | 30 | MEASURED comparable, `Small` use sites |

The widest unmeasured term is row 3: the three closure facts restated as
satisfaction inferences. Rows 1, 2 and 4 are anchored on delivered code.

**The miniature that measures it:** write the Tarski formula and its
adequacy lemma alone, with no carve and no conjuncts. One formula, one
`⇔toPath`. If the adequacy proof needs no new vocabulary, the 650 stands and
the rest is the delivered carve pattern. If the closure condition forces
sequence coding, the Tarski form fails and the price rises by about 200. That
miniature is the gate a build brief must name.

## 6. What the ambient `csb` buys, and what it does not

**It buys a machine-checked reading of the trophy.** The set theorist in
`[LJ-1.323]` section 2.3 ends with "so `|𝒫(κ)| = κ⁺` in L by
Cantor-Bernstein", and the reader supplies that step. The delivered readback
turns each `InjL` into an ambient injection between the small types. The
ambient `csb` then turns the two injections into one ambient bijection
`⟪ fst (𝒫 κ) ⟫ ≃ ⟪ fst δ ⟫`. The step the reader supplies becomes a
corollary, checked by machine, at 80 lines.

**It does not discharge the trophy, and it does not touch the 600.** An
ambient map between small types is not a coded set of L. The two bounds of
the trophy are satisfaction facts about codes, so only the internal theorem
could restate the conclusion as a coded bijection. The reverse bound priced
at about 600 lines by `[LJ-1.325]` also stands untouched: its missing object
is a code in L. See `agents/tasks/LJ-1-325/lj-1.325-report.md:127-146`.

**The design fork has two recorded rulings, and they disagree on purpose.**
The retired route ruled equinumerosity as "there exists a bijection", never
"injections each way", because the latter turns every equality into a
per-consumer Cantor-Bernstein obligation. See
`archive/src/2026-08-09-rud-route/L/CardinalPredicates.lagda.md:10` and `:23`.
That route paid the ambient `csb` once, centrally, and every consumer
upgraded through it. The live route ruled the opposite in `[LJ-1.323]`
section 7.4: mutual injection IS cardinal equality under Cantor-Bernstein,
and a bijection spelling would force internal CSB into every proof while
adding no meaning. Each ruling is sound at its own packaging, because the
retired predicates were ambient formulas and the live predicates are
satisfaction facts.

## 7. DD4, placement and the ledger

**Axis (C-46): tower naming.** Both pieces are pure model-level mathematics
and name no tower, so both belong where the two trophies inherit them.

- The ambient `csb` belongs in a new `src/V/` chapter, for example
  `src/V/Bernstein.lagda.md`. It consumes only the carrier presentation and
  LEM. The V layer is substrate for both trophies, so the chapter lands
  inside both import closures.
- The internal theorem, if funded, belongs beside the coding vocabulary, in a
  new chapter consuming only `L.Coding` and the `InjChain` devices. It would
  sit in the same closure blind spot as `L.InjChain` and `L.Absorption`.

`dev/ledger.toml:195-215` records that blind spot: the GCH closure is read
from a statement whose proof is not wired, so it UNDERSTATES by about 1,027
lines, because the two chapters the proof needs most left the closure. An
internal CSB chapter would deepen that understatement. An ambient chapter in
`src/V/` would not.

## 8. Recommendation

Keep the ruled statement. Port the ambient `csb` into `src/V/` at about 100
delivered lines, and add one corollary after the trophy: the two injections
give an ambient bijection between the small types. That answers the owner's
original question by machine, without reopening the ruling. Fund the internal
theorem only if a future consumer needs coded bijections as objects, and gate
it on the section 5 miniature first.

## ARCHIVE USED

- `agents/tasks/LJ-1-323/lj-1.323-ruling.md:376-385`. Section 7.4 ruled the
  equality as mutual injections, and named `ranAt` as the bijection spelling
  if ever wanted.
- `agents/tasks/LJ-1-325/lj-1.325-report.md:146`. The reverse bound's price
  stood on a `src/`-only grep for Cantor, the same shape as this brief's
  error.
- `archive/dev/TASKS-archived.md:106`. Row `L3.32-T71` delivered Cantor and
  the ambient CSB on the retired route.
- `archive/src/2026-08-09-rud-route/L/Cardinal.lagda.md:89-190`. The `csb`
  block, 80 code lines, copied by the miniature.
- `archive/src/2026-08-09-rud-route/L/CardinalPredicates.lagda.md:23`. The
  scope-gate ruling for the bijection spelling.
- `archive/dev/JOURNAL-archived.md:1377`. The trap the ruling avoided: a
  raw-injection cardinality would force every consumer to re-derive the
  bijection.

**What would not transfer (DD18).** The retired carrier and its structure
instance. The retired predicates `HostBij` and `eqFo`, which belong to a
reification framework this tree replaced with satisfaction facts. The chain
shape of the proof for the internal port, which needs `ω`-iteration this tree
has not coded. The names themselves are retired, so every citation above
carries its home (C-41). The index-level proof body is the one thing that
transfers, and the miniature measured it.

## LITERATURE USED

- `dev/literature/truncation-and-selection.md:74-85`. HoTT Book 10.2.7: a
  cardinal inequality IS a truncated injection, so cardinal arithmetic never
  needs an injection as data. TOOK: the two-injection trophy is the canonical
  form, and no source asks for the untruncated bijection.
- `dev/literature/devlin-II5.md:145-166`. Devlin's chain 5.5 to 5.7. TOOK:
  the one-line answer, Devlin never needs Cantor-Bernstein relativized to L.
  He works with cardinal bounds and explicit bijections from counting, as
  this trophy does with two injections. WHY NOT: neither file supplies an
  internalized CSB, so neither prices the 650.

## Measurements

| Item | Value |
|---|---|
| Archived `csb` block | 80 non-blank code lines, `archive/src/2026-08-09-rud-route/L/Cardinal.lagda.md:89-190` |
| `[LJ-1.107]` probe CSB | 97 lines plus 81 header, 2.03 s, `agents/tasks/LJ-1-107/lj-1.107-report.md:51` |
| Miniature `AmbCsb.agda` | 98 non-blank non-comment lines, exit 0, 1.65 s |
| Empty-file floor | 0.63 s, `agents/tasks/LJ-1-353/Floor.agda` |
| Slot count before each run | 0 of 2 (C-12) |
