# LJ-1.350 report: shapedness is NOT the bound, and the tree already names the one that is

tier: opus (in-harness-subagent-mode), the switch's DEFAULT row. Probe, lands
nothing. Written incrementally (C-22). Every negative is MEASURED or INFERRED, in
those words.

## 0. LEAD

**ONE TIE COSTS 8 INSERTIONS, of which 7 are SHARED by all 28. The 28 now price
at about 43 insertions, against `[LJ-1.347]`'s about 280.** Basis: one measured
site, `agents/tasks/LJ-1-350/Cure350.agda:81-88`, plus one telescope line per
site.

**BUT THE BRIEF'S PREMISE AT RISK IS MEASURED FALSE, AND THAT IS THE REAL
FINDING.** **Shapedness is NOT the missing bound.**
`agents/tasks/LJ-1-350/Refute350.agda`, **exit 0 in 2.56 s**, refutes the
third-shape tie WITH the shapedness of the container ADDED. `[LJ-1.348]`'s
reading wins over `[LJ-1.347]`'s, and the two were not compatible.

**THE REAL BOUND IS DELIVERED, NAMED, AND PROVED IN BOTH DIRECTIONS TODAY.** It
is `arityNumAtL`, `src/L/Coding/CodeSet.lagda.md:185-188`, with
`arityNumAtL-out` at `:189-197` and `arityNumAtL-in` at `:201-207`.
`agents/tasks/LJ-1-350/Cure350.agda`, **exit 0 in 2.90 s**, supplies the tie's
last conjunct from it in **7 lines** and REFUTES the countermodel that
shapedness admits, at the same code, in the same file.

**AND THE TREE ALREADY SAID SO, IN ENGLISH, IN A DELIVERED CHAPTER.**
`src/L/Condensation/TwelveAgree.lagda.md:302-305` names `arityNumAtL` and
`pr-inj` as what closes `fst ar ≡ # n`. **Nobody had read it against these
ties.** This is the second time in three tasks that the answer was written in
the tree before the task started (`[LJ-1.348]` section 2.1).

**THE GATE IS THE SUPPLY, AND I MEASURED IT.**
`agents/tasks/LJ-1-350/MustFail350.agda`, **EXPECTED RED, exit 42 in 1.94 s**,
refused at `MustFail350.agda:60.22-25`. The chain's own call site,
`src/L/Condensation.lagda.md:6716-6732`, holds closedness and shapedness and
NOTHING else. **So the 43 is a floor and not a price:** the witness step must be
restated first, exactly as `[LJ-1.348]` concluded for `witK`.

**COST.** Seven agda invocations, longest 3.07 s. **No wall. No heap exhaustion.
The cap was never raised.** Nothing landed in `src/`.

## 1. THE ANSWER TABLE

| claim | verdict | basis |
|---|---|---|
| shapedness is the missing bound | **MEASURED FALSE** | `Refute350.agda`, exit 0, section 2 |
| the repaired tie is TRUE | **MEASURED FALSE** | `Refute350.agda:201-205` |
| the container of the countermodel is really shaped | **YES, MEASURED** | `Refute350.agda:173-179`, at every member |
| `arityNumAtL` closes the conjunct | **YES, MEASURED** | `Cure350.agda:81-88`, 7 lines |
| `arityNumAtL` excludes the countermodel | **YES, MEASURED** | `Cure350.agda:126-130` |
| the cure is vacuous | **MEASURED FALSE** | `Cure350.agda:154-155`, a term at a real code |
| the cure needs new mathematics | **MEASURED FALSE** | both directions delivered at `CodeSet.lagda.md:189-207` |
| the new hypothesis is free at the chain's call site | **MEASURED FALSE** | `MustFail350.agda`, exit 42 |
| the chain threads the bound from `witK` | **MEASURED FALSE** | sections 2.2 and 5.2 |
| the downstream count is 4 sites | **MEASURED FALSE** | 4 producers AND 12 consumers, section 5.3 |
| anything landed in `src/` | **MEASURED FALSE** | section 8 |
| a run hit a wall | **MEASURED FALSE** | longest 3.07 s, section 7 |

## 2. THE CONTRADICTION, SETTLED AGAINST `[LJ-1.347]`

### 2.1 The tie I picked, and why, from section 5.4

**`ShapesAgree.compK`, `src/L/Condensation.lagda.md:6268-6273`.** Third shape,
sub-family A, container a bare `C : S` at `:6262`. **I re-derived every line
number I use** (C-44); `module ShapesAgree` stands at `:6261` today.

**SECTION 5.4 PICKED IT.** `[LJ-1.347]` measures that `ShapedAgree:6667` and
`:6675` feed `ShapesAgree` 「at `ShapesAgree {n} (lookup C γ) ...`, which is
where sub-family A meets sub-family B」. **I re-read those two lines and they say
that.** So `ShapesAgree.compK` is the ONE site where both sub-families of the
third shape meet, and a verdict there is a verdict on both. **Its container is a
bare set, so the countermodel needs no environment surgery**, which is why one
tie was cheap enough to measure.

### 2.2 The repair under test, in its STRONGEST form

`[LJ-1.347]` section 6 adds the shapedness of the container. I add it **per
member**, as `∥ ShapeWit A γ c ∥₁`, which is what `shaped-out`
(`src/L/Coding/Shape.lagda.md:242-243`) delivers from `⟨ γ ⊨ shapedAt C A ⟩` at
each member. **A refutation of the strong form refutes the weak form too.**

**AND THE CONTAINER REALLY IS SHAPED.** `Refute350.agda:173-179` proves
`(c : S) → ⟨ fst c ∈ fst Cset ⟩ → ∥ ShapeWit A γ c ∥₁`, which is the exact
input `shaped-in` (`src/L/Coding/Shape.lagda.md:326-328`) takes to build
`⟨ γ ⊨ shapedAt C A ⟩`. **So this is not a countermodel that dodges the
hypothesis. It meets it.** MEASURED.

### 2.3 Why shapedness cannot bound the arity, read from the definitions

**TAG 2 CARRIES `noneB`, WHICH IS TOP.** `src/L/Coding/Shape.lagda.md:175-176`
reads `noneB = ⊤̇ {n = 4 + n}`, and `:184` puts `binForm 2 noneB` into `shapes`.
`BinWit 2 noneB γ c` (`:208-211`) is therefore
`Σ[ N ] Σ[ a ] Σ[ b ] ((fst c ≡ pr (fst N) (pr (# 2) (pr (fst a) (fst b)))) × ⊤)`.
**That is the tie's own equation and NOTHING else.** MEASURED, by reading the
three blocks.

**SO SHAPEDNESS ADDS NOTHING TO THIS TIE AT TAGS 2, 3 AND 4.** The hypothesis
hands back the premise the tie already has.

**AND `closedAt` DOES NOT REPAIR IT EITHER.**
`src/L/Coding/Model.lagda.md:2043-2045` reads
`binShapeAt C k rel = ∀̇∈ (var C) (∀̇ (∀̇ (∀̇ (arityTagPairAtL c4 n4 k a4 b4 ⇒̇ rel))))`.
**The arity `n4` is UNIVERSALLY quantified there**, and `closedAt` at `:2191-2193`
is the conjunction of eight such clauses. **Neither predicate says one word about
the arity.** MEASURED, by reading both definitions.

**THIS AGREES WITH `[LJ-1.348]` SECTION 2 AND CONTRADICTS `[LJ-1.347]` SECTION
6.** `[LJ-1.348]` measured the free arity slot at TAG 6. **I measured it at TAG
2, in the binary frame, at a different tie, and the reason is the same.** The two
readings were not compatible and `[LJ-1.348]` was right.

### 2.4 The refutation

`Refute350.agda:201-205`, **exit 0 in 2.56 s**. The countermodel is
`[LJ-1.344]`'s, moved to tag 2:

- `arS := sglS (numeralL 1)`, whose set is `⁅ # 1 , # 1 ⁆`, refuted as a numeral
  at every index by `agents/tasks/LJ-1-347/Elim347.agda`;
- `cS := prʟ arS (prʟ (numeralL 2) (prʟ u u))`, of exactly the tie's pair shape
  at `k := 2`;
- `Cset := sglS cS`, the container, which is SHAPED at every member.

**EVERY AMBIENT FACT COMES FROM THE CHAPTER'S OWN PUBLIC CODE.** `Z.pair∈pr` and
`Z.b∈pair` are `ChainZ` at `src/L/Condensation.lagda.md:2837-2844`; `sgltK` is
`KTies` at `:6227-6234`. **I did not re-write the four-line pair fact a sixth
time**, as the brief ordered, and I did not import
`agents/tasks/LJ-1-344/Supply344.agda`, which is RED today.

## 3. THE REAL BOUND, AND THE TREE ALREADY HAD IT

### 3.1 The predicate

**`arityNumAtL`, `src/L/Coding/CodeSet.lagda.md:185-188`:**

```agda
arityNumAtL c = ∃̇ (∃̇ (prAtL (suc (suc c)) (suc zero) zero
                     ∧̇ (var (suc zero) ∈̇ con ωʟ)))
```

**It says the code is a pair whose FIRST component is in omega.** That is the
tie's last conjunct, written as a formula. **Both adequacy directions are
delivered beside it:** `arityNumAtL-out` at `:189-197`, `arityNumAtL-in` at
`:201-207`.

**IT IS ALREADY THE FIRST CONJUNCT OF WHAT A CODE IS.**
`src/L/Coding/Powerset.lagda.md:297-298` reads
`isCodeAt c w = keyArityAtL c 1 ∧̇ hasWitnessAt w c`, and
`src/L/Choice/Faithful.lagda.md:281` records that `arityNumAtL` is the
arity-BOUND variant of that same first conjunct. **So the missing bound is half
of the delivered definition of a code, and the ties dropped it.**

### 3.2 The tree records the answer in English

**`src/L/Condensation/TwelveAgree.lagda.md:302-305`, delivered prose:**

> The restriction costs the consumers nothing, because the arity at every
> consuming site IS a numeral: `codesK` gives the code's shape, `arityNumAtL`
> (L.Coding.CodeSet) says its arity component is a numeral, and `pr-inj` closes
> both into `fst ar ≡ # n`.

**That is my cure, stated in English, in `src/`, before this task started.**
**And `src/L/Coding/CodeSet.lagda.md:21-27`, which `[LJ-1.348]` quotes, says the
same negative:** 「nothing in `closedAt` or `shapedAt` constrains the arity
slot」. **Two delivered chapters already contradicted `[LJ-1.347]` section 6, and
nobody had read either against these ties.**

### 3.3 The cure, MEASURED

**`agents/tasks/LJ-1-350/Cure350.agda:81-88`, exit 0 in 2.90 s. SEVEN LINES:**

```agda
  arity-cure : (k : ℕ) (c N a b : S)
             → ⟨ (c ∷ γ) ⊨ arityNumAtL zero ⟩
             → fst c ≡ pr (fst N) (pr (# k) (pr (fst a) (fst b)))
             → ∥ Σ[ m ∈ ℕ ] (fst N ≡ # m) ∥₁
  arity-cure k c N a b h e = PT.map
    (λ { (m , (z , q)) → m , pr-inj (sym e ∙ q) .fst })
    (arityNumAtL-out zero (c ∷ γ) h)
```

**IT IS GENERIC IN `n` AND IN THE ENVIRONMENT.** `module Cure` at `:79` takes
only `γ : S ^ n`. **So the seven lines are written ONCE and serve every site of
the family, in both sub-families and at both towers.**

**THE UNARY HALF IS THE SAME SEVEN LINES AT ONE COMPONENT FEWER**,
`Cure350.agda:91-98`. **Together the shared block is 15 lines**, counting the
`module Cure` line.

**THE CURE EXCLUDES THE COUNTERMODEL.** `Cure350.agda:126-130` derives `⊥` from
`⟨ (cS ∷ γ) ⊨ arityNumAtL zero ⟩` at the same code `Refute350.agda` builds.
**Shapedness admits it; `arityNumAtL` refutes it. Same code, two bounds, two
files.** MEASURED.

## 4. THE NEGATIVE CONTROLS AND NON-VACUITY

**CONTROL A, THE STANDARD THIS WEEK: ONE CONJUNCT, TWO ARGUMENTS, ONE FILE.**
`Refute350.agda:216-221`, inside the green file:

- `arity-holds` (`:216`) exhibits the tie's last conjunct HOLDING at the numeral
  arity `numeralL 1`.
- `arity-fails` (`:219`) refutes it at `sglS (numeralL 1)`.

**ONE ARGUMENT APART: `numeralL 1` against `sglS (numeralL 1)`.** So the conjunct
is satisfiable and the refutation measures the SITE, not the statement (C-42).
MEASURED.

**CONTROL B, THE SAME PAIR ON THE CURE SIDE.** `Cure350.agda:154-155` produces
the conjunct from the cure at a GOOD code `gS`, whose arity is `numeralL 1`;
`:159-161` refutes it at the countermodel's arity. **The good code differs from
the countermodel's code in ONE argument**, `numeralL 1` where the countermodel
writes `sglS (numeralL 1)`. MEASURED.

**CONTROL C, EXPECTED RED, AND IT FAILS AT THE LINE IT NAMES.**
`agents/tasks/LJ-1-350/MustFail350.agda`, **exit 42 in 1.94 s**, refused at
`MustFail350.agda:60.22-25`. The error prints `L.Coding.Shape.shapes (suc A)` on
one side and the `arityNumAtL` body with `∈ con (L.Axioms.Infinity.ωʟ lem)` on
the other. **The error NAMES the missing fact, which is membership in omega.**
**EXPECTED RED. DO NOT REPAIR THAT FILE.**

**NON-VACUITY, THREE LAYERS.**

1. **The tie's OTHER conclusions HOLD at the witnesses.**
   `Refute350.agda:193-194` is
   `⟨ fst arS ∈ K ⟩ × ⟨ fst u ∈ K ⟩ × ⟨ fst u ∈ K ⟩`. **The repaired tie dies at
   a point where every other conjunct is true, and ONLY the arity conjunct is
   refuted.**
2. **Every premise the repaired tie asks for is a CLOSED term**, built and never
   assumed: `cS∈Cset`, `Cset-shaped` and `codeEq`.
3. **THE REFUTATION RUNS ON THE DELIVERED RECORD.** `Refute350.Wire`
   (`:236-264`) opens `KValue` at its own frame parameters, takes its `facts`
   record, and produces `repaired-tie-false` (`:257-258`). **The six closure
   facts arrive from the chapter and nothing here restates one. This is not a
   parameters-green** (C-45). ONE hypothesis is mine, `#1∈γ`, which makes the
   carrier NON-EMPTY.

**AND THE CURE IS NOT VACUOUS EITHER.** `Cure350.agda:146-152` builds the cure's
hypothesis with `arityNumAtL-in` at a real code, and `:154-155` runs the cure on
it. **A cure whose hypothesis nothing meets would prove nothing.** MEASURED.

## 5. THE RE-PRICE OF THE 28

### 5.1 The arithmetic, with its basis named (DD8)

**BASIS: ONE MEASURED SITE**, `Cure350.agda:81-98`, not a comparable elsewhere.
P-l is honoured: I re-measured at this site instead of transferring
`[LJ-1.343]`'s number.

| what | count | insertions |
|---|---:|---:|
| the shared cure, both shapes, written ONCE | 1 | **15, MEASURED** |
| one line of telescope per producer site | 28 | **28, MEASURED at one** |
| **total** | | **about 43** |

**AGAINST `[LJ-1.347]`'s about 280. A factor of six and a half.** The reason is
not cleverness: **`[LJ-1.343]`'s comparable moved a bound site by site, and this
cure is ONE generic lemma.** That is the whole difference.

**THE 32 CONSUMER SLOTS COST NOTHING.** A repair that keeps the conjunct as a
conclusion and adds a hypothesis leaves every consumer untouched. **A repair that
DELETES the conjunct does not, and I priced neither of those.** INFERRED that
adding is cheaper, and I did not measure it. This agrees with `[LJ-1.347]`
section 6.

### 5.2 AND THE 43 IS A FLOOR, NOT A PRICE

**MEASURED: the new hypothesis has NO supplier at the chain's own call site.**
`src/L/Condensation.lagda.md:6716` reads `go (w , (hxw , (hcl , hsh))) =` and
`:6728-6732` hands `codesK w wK` to `ShapedAgree`. **The three things bound
beside `w` are the read membership, the closedness of `w` and the shapedness of
`w`.** Section 2.3 measures that neither of the last two bounds the arity.
`MustFail350.agda` offers the closest candidate and Agda refuses.

**SO THE CHAIN CANNOT THREAD THE BOUND FROM THE TOP, AND THE REASON IS TWOFOLD.**

1. **There is no bound at the top to thread.** `witK`'s premise at
   `src/L/Condensation.lagda.md:7233-7234` carries `closedAt ∧̇ shapedAt` and
   nothing else. MEASURED.
2. **`witK` is itself FALSE**, `[LJ-1.348]` section 2, `Refute348.agda:247-252`.
   **A repair that threads a hypothesis out of a false parameter buys nothing.**

**WHAT THE 43 THEREFORE BUYS.** It is the cost of stating the repaired
telescopes, once the witness step supplies the bound. **The witness step is
`hasWitnessAt` in `src/L/Coding/CodeSet.lagda.md`, and this task did NOT price
its restatement.** `[LJ-1.348]` section 6 names the two candidates and stops, and
so do I: DD23 reserves the chapter for the orchestrator.

### 5.3 THE DOWNSTREAM COUNT IS LARGER THAN `[LJ-1.347]` SAID

`[LJ-1.347]` section 5.5 read two blocks and claimed 4 more sites, saying plainly
it did not sweep. **I swept the two files by the conjunct's own text and read
every hit.**

| file | producers | consumers |
|---|---:|---:|
| `src/L/Condensation/LowerAgree.lagda.md` | 2, at `:116-121` and `:122-126` | 6, at `:141`, `:147`, `:153`, `:160`, `:167`, `:174` |
| `src/L/Condensation/UpperAgree.lagda.md` | 2, at `:116-121` and `:122-126` | 6, at `:141`, `:147`, `:153`, `:160`, `:167`, `:174` |

**MEASURED**, by reading `LowerAgree.lagda.md:110-178` whole and by reading the
eight named field lines of `UpperAgree.lagda.md`. **The producers are third
shape:** the container is `lookup (suc (suc zero)) γ`, an index into a bare `γ`.
**So `[LJ-1.347]`'s 4 producers stand and its report never counted the 12
consumers.** They do not change the insertion figure, because consumers take the
conjunct and do not build it.

**AND TWO MORE FILES CARRY THE CONJUNCT AND WERE NEVER COUNTED BY ANYBODY:**
`src/L/Condensation/TwelveAgree.lagda.md` (11 occurrences) and
`src/L/Coding/EnvSupply.lagda.md` (12 occurrences), MEASURED by grep of the
conjunct's text. **I did NOT read those 23 and I do not classify them.** The
chapter itself holds 56 occurrences of the text, against `[LJ-1.347]`'s
classified 32 producers and 20 consumers; **the remaining 4 I did not chase.**

### 5.4 Does the chain collapse the cost? YES, but not where anyone looked

**MEASURED: the collapse is in the CURE, not in the chain.** The cure is generic
in `n` and in `γ`, so 28 sites share 15 lines. **That is the collapse, and it is
worth about 237 insertions against the estimate.**

**MEASURED: the chain does NOT collapse it by threading.** Section 5.2. **This
is the opposite of what `[LJ-1.347]` section 6 expected**, and its own words were
「the repair adds the hypothesis at the top and threads it, rather than 24 times
over」. **That sentence is MEASURED FALSE: there is nothing at the top to
thread.**

## 6. DD4, WITH THE AXIS NAMED (C-46)

**THE AXIS IS AC-AGAINST-GCH, fixed at `scripts/measure/ledger.py:50`.**

**EVERY TERM I WROTE IS CLASS-FREE.** MEASURED, by reading all four files:
`arity-cure`, `arity-cure-un`, `sglS`, `Cset-shaped`, `compK⁺-false`,
`arity-holds`, `arity-fails` and the whole of `Test` name only `fst`, `∈`,
`lookup`, `pr`, `pr-inj`, `prʟ`, `numeralL`, `⁅_,_⁆`, `#_`, `ωʟ`,
`arityNumAtL` and six `KFacts` fields. **Not one mentions AC, GCH, a
well-ordering or a cardinal.**

**AND THE CURE IS THE SHARED KIND, WHICH IS WHAT DD4 ASKS FOR.** It is one
lemma, generic in the environment length and in the environment, sitting on
`L.Coding.CodeSet`, which is upstream of both ends. **So the repair is written
ONCE for `L ⊨ AC` and `L ⊨ GCH`, not once each.** That is the whole reason the
43 is not 280.

**WHAT THIS TASK REMOVES FROM THE SHARED SIDE.** Nothing lands, so no line is
shared or unshared. **What it removes is a WRONG CURE from the shared side:** a
shapedness hypothesis threaded through 28 telescopes would have been assumed at
both towers and would have bought nothing at either.

## 7. SECONDS, LOAD, RUNS

One agda process at a time, always `GHCRTS="-A64m -I0 -M8g"`, **cap NEVER
raised**. `ps aux | awk '/libexec.*bin\/agda/ && !/awk/' | wc -l` run before
every invocation: **0 every time**, seven counts, seven invocations.

**FLOOR (C-53).** `agents/tasks/LJ-1-350/Floor350.agda`, an empty module:
**0.72 s** first run, **0.79 s** second. **My floor disagrees with
`[LJ-1.348]`'s 0.07 s by ten times**, and `[LJ-1.348]` recorded the same
disagreement against `[LJ-1.346]` and `[LJ-1.344]`. **MEASURED: no seconds
figure of mine is comparable with any other task's, and I offer none as such.**

| run | exit | seconds |
|---|---:|---:|
| `Floor350.agda` (first) | 0 | **0.72** |
| `Refute350.agda` (first) | **0** | **3.07** |
| `Refute350.agda` (confirm) | **0** | **2.56** |
| `Cure350.agda` (scope slip, `⊨`) | 42 | 2.57 |
| `Cure350.agda` | **0** | **2.90** |
| `MustFail350.agda` (**EXPECTED RED**) | **42** | **1.94** |
| `Floor350.agda` (second) | 0 | **0.79** |

**NO INVOCATION CAME NEAR THE 30-MINUTE WALL; the longest was 3.07 s. NO heap
exhaustion. Nothing was interrupted. The cap was never raised.** **C-58 was never
needed:** I wrote no pattern-match case split on a numeral index, because
`Elim347.agda` already holds the eliminator form and I imported it.

**THE DELTAS ABOVE THE FLOOR ARE SMALL AND I SAY SO.** `Refute350.agda` at
2.56 s against a 0.72 s floor is a delta of 1.84 s. **The delta between
`Refute350.agda` and `Cure350.agda`, 0.34 s, is UNDER my own floor's own
spread and means nothing.**

**A CACHE WARNING, inherited from three siblings.** My files load
`L.Condensation`, `L.Coding.Shape` and `L.Coding.CodeSet` from their committed
interfaces. **No figure here is a cold check of the chapter, and none is offered
as one.** I ran no whole-chapter check, because nothing was landed.

## 8. PROHIBITIONS, ANSWERED

I wrote only inside `agents/tasks/LJ-1-350/`: this report, `Floor350.agda`,
`Refute350.agda`, `Cure350.agda` and `MustFail350.agda`. **`git status --short`
shows those five files and, beside them, a live sibling's
`agents/tasks/LJ-1-352/`, which is NOT mine and which I did not open.** **`src/`
holds no probe of mine
and I opened no file under `src/` for writing.** I READ
`src/L/Condensation.lagda.md`, `src/L/Condensation/LowerAgree.lagda.md`,
`src/L/Condensation/UpperAgree.lagda.md`,
`src/L/Condensation/TwelveAgree.lagda.md`, `src/L/Coding/Shape.lagda.md`,
`src/L/Coding/Model.lagda.md`, `src/L/Coding/CodeSet.lagda.md`,
`src/L/Coding/Powerset.lagda.md`, `src/L/Coding/EnvSupply.lagda.md`,
`src/L/Choice/Faithful.lagda.md`, `src/V/Coding.lagda.md`,
`src/FOL/Semantics.lagda.md`, `src/FOL/ZFStructure.lagda.md` and
`src/Base/Prelude.lagda.md`. **I READ and IMPORTED
`agents/tasks/LJ-1-347/Elim347.agda` and edited that directory NOT AT ALL.** **I
did not open `agents/tasks/LJ-1-344/Supply344.agda`, which is RED, and I did not
repair it.** I did not open `src/Everything.lagda.md`, `dev/`, `AGENTS.md` or
`.claude/` for writing. **I did not repair 24 sites. I measured one.** No commit,
no push, no `git checkout`, `stash`, `reset` or `clean`. **No `make check`.** No
em dash in any language.

## 9. WHAT I DID NOT SETTLE

- **The restatement of the witness step.** Section 5.2 says it is the gate and
  stops. `[LJ-1.348]` section 6 names the two candidates. **I priced neither.**
- **The other 27 sites, as repairs.** ONE was measured. **INFERRED that the
  other 27 cost one telescope line each**, because their telescopes differ only
  in the index form and the arity or unary shape. **I built no line at any of
  them.**
- **The 23 occurrences in `TwelveAgree.lagda.md` and `EnvSupply.lagda.md`.**
  Counted by grep, never read, never classified.
- **The four remaining occurrences in the chapter** past `[LJ-1.347]`'s
  classified 52. Not chased.
- **Whether the third-shape ties are false WITHOUT the shapedness hypothesis.**
  `[LJ-1.347]` section 13 says they are refutable more easily than `wCodesK` and
  built no term. **My refutation is of the REPAIRED tie, which is strictly
  stronger, so the unrepaired ties are false too.** MEASURED, by the same file.
- **Whether the delete-the-conjunct repair is cheaper.** Not priced.
- **The chapter's green with anything landed.** Nothing landed and I ran no
  chapter check.

## 10. ARCHIVE USED (DD18)

One line read per archived file, as the brief orders.

- **`agents/tasks/LJ-1-347/lj-1.347-report.md`, sections 2 and 5 read WHOLE,
  plus 6, 13 and 14.** **Line read:** section 5.4, 「`ShapedAgree:6667` and
  `:6675` feed `ShapesAgree` at `ShapesAgree {n} (lookup C γ) ...`, which is
  where sub-family A meets sub-family B」. **TOOK** that reading entire: it
  picked my tie, and I re-read both lines to confirm it. **TOOK** its warning
  about `Supply344.agda` and its 109-line drift, and re-derived every line
  number I use. **CORRECTED section 6:** 「the missing bound is shapedness」 is
  MEASURED FALSE, and 「the repair adds the hypothesis at the top and threads
  it」 is MEASURED FALSE. **Its own last sentence funded this task and was
  right.**
- **`agents/tasks/LJ-1-348/lj-1.348-report.md`, sections 1, 2 and 5 read
  WHOLE.** **Line read:** section 2, 「`shapes` is a twelve-fold disjunction and
  its tag-6 disjunct pins the PAYLOAD and leaves the ARITY component free」.
  **TOOK the reading and CONFIRMED it at a different tag and a different tie:**
  my tag 2 carries `noneB`, which is TOP, so it does not even pin the payload.
  **TOOK its load-bearing check**, that a cure is only cheap if the call site
  holds it, and got the same answer it got: it does not.
- **`agents/tasks/LJ-1-343/lj-1.343-report.md`, read the cost line.** **Line
  read:** `:72`, 「**20 insertions, 7 deletions, ONE file.**」 **REJECTED it as
  a basis**, which is what P-l orders: that repair moved a bound site by site,
  and this one is a single generic lemma, so the per-tie rate does not carry.
  **TOOK only its shape:** put the missing bound in the telescope.
- **`archive/dev/TASKS-archived.md`, read the header at `:1-12`.** **TOOK SHAPE
  ONLY:** 「The 264 rows below record every dispatch made on the retired
  route」, a dispatch index kept for which approaches were measured. **REJECTED
  every figure:** that route has a different carrier and no `KFacts` record, so
  no count and no seconds figure from it prices anything here.

## 11. LITERATURE USED (DD18)

**`dev/literature/devlin-II5.md`, read `:246-249`.**

**THE ONE LINE THE BRIEF ASKS FOR: a 24-site chain of unbounded conjuncts has NO
counterpart in Devlin's text, and it is wholly a port artefact.** `:246-249`
says 2.2 to 2.4 write `D(v, u) = "v = Def(u)"` as Σ₁ and then 「bind every
unbounded quantifier by the concrete set `K(u)`, **the finite sequences over the
formula set, the variables and the members of `u`**」.

**THE DECISIVE WORD IS 「SEQUENCES」.** Devlin's `K(u)` is built from finite
sequences, so **every member of it carries a natural-number index BY
CONSTRUCTION**. He never has to say that the arity of a member is a numeral,
because he never quantifies over a container that could hold anything else.
**Our ties quantify over a container that is only closed and shaped, and section
2.3 shows neither predicate is about arities at all.** **So `arityNumAtL` is not
an addition to Devlin: it is the port of what his construction gives for free.**

**WHY NOT the rest of the digest.** `:240-244` is the `[LJ-1.12]` Δ₀ question,
settled and not about this conjunct. `:258` onward is Step D, the definable
well-order, which no tie of this family reaches. **The cardinality halves are
another step, and C-46 forbids using Devlin's tower axis as DD4's.**
