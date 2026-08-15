# LJ-1.346 report: the tie supply is LANDED, and the private block STAYS private

tier: opus (in-harness-subagent-mode), the switch's DEFAULT row. Written
incrementally (C-22). Every negative is MEASURED or INFERRED, in those words.

## 0. LEAD

**BOTH TIES LAND GREEN, FIRST ATTEMPT.** `src/L/Condensation.lagda.md`, **exit 0
in 132.82 s**, a COLD check because the edit invalidated the interface. A second
cold run after a comment correction gave **exit 0 in 134.15 s**.

**THE COLD FIGURE PAST THE CACHE IS 132.82 s, AND THE DELTA IS UNMEASURABLE.**
The honest baseline is a verbatim copy of the pre-edit chapter with only the
module line renamed, `agents/tasks/LJ-1-346/CondCold346.lagda.md`: **exit 0 in
132.11 s**. **The delta is +0.71 s and the empty-file floor is 0.78 s
(`agents/tasks/LJ-1-346/Floor346.agda`), so the delta is UNDER the floor. It is
UNMEASURABLE, not small** (C-53 as `[LJ-1.344]` extended it).

**AND THE SECOND RUN PROVES THE POINT WITHOUT THE FLOOR.** Two cold runs of the
SAME landed content gave 132.82 s and 134.15 s, a spread of **1.33 s**, which is
larger than the 0.71 s delta. **So the delta sits inside the run-to-run spread.
I do not claim the landing is cheap in seconds; I claim its cost cannot be
separated from the noise.** `[LJ-1.345]` measured 132.93 s for the same baseline
copy yesterday, so the machine has not moved.

**THE TIES ARE NOT ONLY TYPED, THEY FIRE.**
`agents/tasks/LJ-1-346/Wire346.agda`, **exit 0 in 2.86 s**, asks the LANDED
`L.Condensation.KTies` for both ties at `KValue`'s concrete 14-slot environment
and closes both as terms.

**THE INTERFACE RULING: `src/V/Coding.lagda.md` STAYS PRIVATE, AND I DID NOT
OPEN IT FOR WRITING.** The supply carries no copy at all, because the chapter
already had a public access nobody used. Section 1.

## 1. THE ANSWER TABLE

| claim | verdict | basis |
|---|---|---|
| the supply lands and the chapter is green | **YES, MEASURED** | exit 0, 132.82 s |
| the delta over the baseline is measurable | **MEASURED FALSE** | +0.71 s against a 0.78 s floor |
| the site at `:6155` to `:6157` works | **YES, MEASURED** | section 2 |
| the site is all the landing needs | **MEASURED FALSE** | three imports were missing, section 2 |
| `src/V/Coding.lagda.md` must change | **MEASURED FALSE** | section 1, the count |
| the supply needs a fifth 4-line copy | **MEASURED FALSE** | `ChainZ.pair∈pr` is public, `:2837` |
| four tasks re-wrote the access | **MEASURED FALSE** | `[LJ-1.338]` imported it, section 3.3 |
| only one of the eight names is re-derived | **MEASURED FALSE** | six are, section 3.3 |
| both ties fire on real arguments | **YES, MEASURED** | `Wire346.agda`, exit 0 |
| the landed supply proves the PRE-repair tie | **MEASURED FALSE** | Control A, exit 42 |
| any environment meets the premise | **MEASURED FALSE** | Control B, exit 42 at one numeral |
| a consumer of the chapter breaks | **MEASURED FALSE** | all five, exit 0, section 6 |
| the supply is class-free | **YES, MEASURED** | section 8 |
| a run hit a wall | **MEASURED FALSE** | no run passed 135 s, section 9 |

## 2. THE ORDERING, CHECKED BEFORE ANYTHING WAS WRITTEN

**The brief's premise at risk was 「the site at `:6155` to `:6157` works」. It
HOLDS. One thing it needs is not in the sibling's account.**

- `KFactsCons` ended at `:6155`; `module ShapesAgree` began at `:6157`.
  MEASURED, by reading both boundaries.
- `module ChainZ` is at `:2820`, far above the site, so the supply can reach
  `pair∈pr`. MEASURED.
- `module DefinesAgree` is now at `:6882` and `module LeafAgree` at `:7224`,
  both BELOW the site, so both can open `KTies`. MEASURED.
- `module KValue` is at `:7380`, BELOW the site. **The supply never mentions
  it.** `[LJ-1.344]`'s ordering warning binds the WIRING only, and the wiring
  lives in my probe and not in the chapter. MEASURED.

**WHAT THE SIBLING'S ACCOUNT MISSED: the chapter did not import three names the
supply needs.** MEASURED, by reading the import block before the edit.
`:57` read `L.Coding.Powerset ... using ( isCodeAt; DefBody; DefinesAt;
envOneAt )`, with **no `envOne` and no `envOneAt-out`**. `:65` read
`Cubical.HITs.CumulativeHierarchy.Properties using ( ∈∈ₛ )`, with **no
`extensionality` and no `_⊆_`**. **So the landing is not 「insert one module」.
It is three import edits and one module.**

## 3. THE INTERFACE RULING: THE `private` BLOCK STAYS PRIVATE

**RULING: do NOT change `src/V/Coding.lagda.md`. The four re-writes are the
correct cost, and the supply does not even pay them.** The counts below decide it.

### 3.1 The tree ALREADY has a public access to the re-written fact

**`src/L/Condensation.lagda.md:2837-2839` is `ChainZ.pair∈pr`, inside `module
ChainZ` at `:2820`, a TOP-LEVEL module of the chapter that is NOT private.**
MEASURED, by reading every `private` line of the chapter above the site: `:118`,
`:316`, `:2232`, `:2788`, `:3691`, `:3774`, `:3891`, `:4004`, `:4456`, `:5072`,
`:5201`, `:5309`, `:5414`. **None encloses `:2820`.**

**An outside consumer already used it.**
`agents/tasks/LJ-1-105/ProbeLJ1105A.agda:42` reads
`using ( module ChainZ; module EnvSet; envSetB )`. MEASURED.

`ChainZ` also carries `a∈singl` (`:2827`), `singl∈pr` (`:2832`) and `b∈pair`
(`:2842`). **So `⁅ x , y ⁆ ∈ pr x y` is public in the tree today.** Exposing the
block would give one fact two public homes, which is worse and not better.

**THE COST OF USING IT: `ChainZ` takes `K`, `γ` and `arityK` as parameters, and
`pair∈pr` uses none of the three.** So a caller must have an `arityK` to name
it. Inside `KTies` that is free, because `arityK` is already a parameter. **For
a probe with no `arityK` it is a real friction, and that is why five probes
wrote their own instead. I record it and I did not fix it: splitting `ChainZ`
is a separate rewrite with its own price.**

### 3.2 What exposing the block would actually save: about ONE line in four

The block's names are stated at `_∈ₛ_` and every consumer works at `_∈_`.
`inr∈⁅,⁆` is `{a b x : S} → x ≡ b → ⟨ x ∈ₛ ⁅ a , b ⁆ ⟩`
(`src/V/Coding.lagda.md:149-150`). The re-written copy is four lines:

```agda
pair∈pr : (x y : V ℓ) → ⟨ ⁅ x , y ⁆ ∈ pr x y ⟩
pair∈pr x y =
  ∈∈ₛ {a = ⁅ x , y ⁆} {b = pr x y} .snd
    (pairing-ax ⁅ x ⁆s ⁅ x , y ⁆ ⁅ x , y ⁆ .snd ∣ inr refl ∣₁)
```

**With `inr∈⁅,⁆` public the last line becomes `(inr∈⁅,⁆ refl)`. The signature,
the `∈∈ₛ` conversion and the head all stay.** MEASURED, by reading both sites.
**The saving is one line of four, not four of four.**

### 3.3 THE COUNT

**The block holds EIGHT names** (`src/V/Coding.lagda.md:136-166`): `∈singl`,
`singl∈`, `self∈singl`, `inl∈⁅,⁆`, `inr∈⁅,⁆`, `mem⁅,⁆`, `singl-inj`,
`singl≡pair`.

**I FIRST COUNTED ONE SHAPE AND THE COUNT WAS TOO NARROW. THE FULL CENSUS IS
BELOW, AND IT MOVES THE ARGUMENT.** MEASURED, by grep of the four idioms the
eight names wrap, over `src/` and `agents/`, excluding `src/V/Coding.lagda.md`
itself and my own task directory.

| idiom | which of the eight it wraps | `src/` lines | `agents/` lines, chapter copies excluded |
|---|---|---:|---:|
| `pairing-ax … ∣ inr refl ∣₁` | `inr∈⁅,⁆` | 7 | 28 |
| `pairing-ax … ∣ inl refl ∣₁` | `inl∈⁅,⁆` | 5 | 22 |
| `pairing-ax … .fst` | `mem⁅,⁆` | 16 | 33 |
| `SingletonPackage` classification | `∈singl`, `singl∈`, `self∈singl` | 12 | 10 |

**SO SIX OF THE EIGHT ARE RE-DERIVED, not one.** `singl-inj` and `singl≡pair`
are re-derived nowhere: MEASURED, zero hits outside the chapter.

**AND THAT IS WHY THE BLOCK SHOULD STAY PRIVATE, not why it should open.**
**59 lines in `src/` alone call `pairing-ax` or `SingletonPackage` directly**,
across NINE chapters: `src/V/Model.lagda.md` (12), `src/L/Coding/Key.lagda.md`
(10), `src/L/Coding/EnvSupply.lagda.md` (10), `src/L/BoundedSubset.lagda.md`
(7), `src/L/Condensation.lagda.md` (6), `src/L/Coding/Base.lagda.md` (6),
`src/L/Coding/Descent.lagda.md` (3), `src/L/Axioms/Basic.lagda.md` (3),
`src/L/Constructible.lagda.md` (2). **Calling the library axiom is the tree's
NORMAL vocabulary, in nine chapters, and the eight names are one chapter's local
convenience over it.** Publishing them would not replace that vocabulary; it
would add a second one, stated at `_∈ₛ_` where the tree works at `_∈_`.

**THE SHAPE THIS TASK ACTUALLY NEEDED, `⁅ x , y ⁆ ∈ pr x y`, is narrower.**
MEASURED, by grep of `pairing-ax ⁅` and reading every hit: **4 lines over 3
files in `src/`** (`src/L/Condensation.lagda.md:2834` and `:2839`, the `inl` and
`inr` halves inside `ChainZ`; `src/L/Coding/Key.lagda.md:581`;
`src/L/Coding/EnvSupply.lagda.md:457`), and **78 lines over 45 files in
`agents/`**, of which **30 files carrying 62 lines contain `module ChainZ`** and
are whole-chapter copies that INHERIT the line. **That leaves 15 files and 16
lines.** Nine of the sixteen copy `src/L/Coding/Key.lagda.md:581` verbatim
inside a larger copied proof (`LJ-1-151`, `LJ-1-258`, `LJ-1-259`, `LJ-1-266`
twice, `LJ-1-275`, `LJ-1-292`, `LJ-1-311` twice). Two are
`agents/tasks/LJ-1-97/ProbeLJ197A.agda:112` and `:124`, the `inl` half at
`pr A A` and at `pr (sucV A) A`.

**THE GENUINELY INDEPENDENT `pair∈pr` LEMMAS ARE FIVE:**
`agents/tasks/LJ-1-104/ProbeLJ1104A.agda:393`,
`agents/tasks/LJ-1-302/ProbeLJ1302B.agda:105-108`,
`agents/tasks/LJ-1-341/ProbeTies341.agda:112`,
`agents/tasks/LJ-1-344/Supply344.agda:76`,
`agents/tasks/LJ-1-345/Refute345.agda:68`.

**THE BRIEF'S 「four tasks」 IS MEASURED FALSE IN ONE OF ITS FOUR.**
`[LJ-1.338]` did NOT re-write it; it IMPORTED `[LJ-1.302]`'s copy.
`agents/tasks/LJ-1-338/ProbeLeaf338.agda:55` reads
`import LJ-1-302.ProbeLJ1302B {ℓ} lem as P1302B`, and `:179` uses
`P1302.pair∈pr`. The same import is at `ControlB338.agda:179` and
`ControlC338.agda:179`. MEASURED. **The set is `[LJ-1.104]`, `[LJ-1.302]`,
`[LJ-1.341]`, `[LJ-1.344]`, `[LJ-1.345]`, and it is five, not four.**

### 3.4 What the chapter's own prose says, read before anything moved

**`src/V/Coding.lagda.md:17-21` gives the discipline and its reason**: 「Both
proofs are conducted entirely through the library's classification
specifications, transporting memberships along paths. At no point is a nested
brace expression handed to the typechecker to unfold, which is a discipline
rather than an aesthetic: these encodings nest three deep, and unfolding one is
how a proof about them stops terminating.」

**`:122-127` says why the eight names exist**: 「The classification
specifications, named once so the proof reads as membership reasoning rather
than as brace manipulation.」 **They are named for THIS chapter's proof.**

**And the Recap names the chapter's public interface exactly.** `:241-247`:
「Numerals are injective (`#-inj`) … and Kuratowski pairs are injective
(`pr-inj`) … so `VCode` is the previous chapter's coding applied to the
hierarchy.」 **Three names, and no member of the block is among them. The
chapter publishes two injectivity theorems and one instance; the block is the
proof of one of them. That is a design choice and the tree made it on purpose.**

### 3.5 THE SMALLEST CHANGE THAT STOPS THE RE-WRITING, and it is elsewhere

**The landed supply carries ZERO copies**, against the 4 lines the brief
budgeted for a fifth copy. `src/L/Condensation.lagda.md:6208` reads
`module Z = ChainZ {n} K γ arityK`, and `sgltK` calls `Z.pair∈pr`.

**And I stated ONE new PUBLIC lemma, in the chapter that owns the concept.**
`envOne-pair` at `src/L/Condensation.lagda.md:6166-6189`:

```agda
envOne-pair : (v : V ℓ) → envOne v ≡ ⁅ pr (# 0) v , pr (# 0) v ⁆
```

**That is the fact the five re-writes were building toward.** It is the joint
between `envOneAt-out`, which gives a bare set equation, and the singleton
closure, which needs a pair. It is public, so the sixth re-write is now
unnecessary. **What it exposes that was hidden: the shape of `envOne`, which
`src/L/Coding/Powerset.lagda.md:132-144` keeps private as `readEntry` and
`entry∈`.** The equation, not the fibre reading, is what a consumer wants, so
the exposure is the smaller of the two.

## 4. THE DIFF

`git diff --stat`: **`src/L/Condensation.lagda.md`, 128 insertions, 26
deletions.** Non-blank lines inside the fence: **+114, -26, net +102**. The
chapter goes from 7,332 raw lines to 7,434. Five hunks.

1. **`:57-59`.** `L.Coding.Powerset` gains `envOne` and `envOneAt-out`; one new
   import line `open import L.Coding.InL {ℓ} using ( sgl-in; sgl-out )`.
   **`L.Coding.InL` is already a transitive dependency** through
   `L.Coding.Shape` (`src/L/Coding/Shape.lagda.md:61`) and `L.Coding.CodeSet`
   (`src/L/Coding/CodeSet.lagda.md:88`), so no module compiles that did not
   compile before. MEASURED, by reading both import lines.
2. **`:67-68`.** `Cubical.HITs.CumulativeHierarchy.Properties` gains
   `extensionality` and `_⊆_`.
3. **`:6160-6189`, `envOne-pair`.** 22 non-blank code lines and 5 comment lines.
   It uses `sgl-in` and `sgl-out` rather than a fresh `pairing-ax` idiom, so it
   adds no sixth copy of anything.
4. **`:6191-6259`, `module KTies`.** The telescope is four `KFacts` field types;
   the body is `tagged`, `tagged-fst`, `tagged∈K` and `module Z = ChainZ` in a
   `private` block, then `sgltK`, `envK` and `defPairK` in public. **The three
   terms are `[LJ-1.344]`'s, unchanged except that `pair∈pr` is now
   `Z.pair∈pr`.**
5. **`:6882-6905` and `:7218-7323`.** The two telescopes, section 5.

**NO NEW `KFacts` FIELD. NO NEW `BoundOver` LEMMA.** MEASURED: the record at
`:6079-6115` is byte-identical to HEAD, and the chapter still does not import
`L.Coding.Bound` outside `:7376`.

## 5. THE TELESCOPES SHORTENED

**`module DefinesAgree` (`:6882`).** Lost the two tie parameters, 11 lines of
type. Gained three `KFacts` closure parameters, 8 lines: `pairK`, `carrierK`,
`arityK`. **Net minus one parameter and minus three lines.** The two ties are
now DERIVED, at `:6905`:

```agda
  open KTies {m} w K γ numK pairK carrierK arityK using ( envK; defPairK )
```

The body needed one rename, twice: the old tie was called `pairK` and the
`KFacts` field is also `pairK`, so the two body uses at `:6928` and `:6943`
became `defPairK`. MEASURED, exit 0.

**`module LeafAgree` (`:7224`).** Lost the two tie parameters, 6 lines of type,
and gained NOTHING, because it already carries the whole `KFacts` record as `f`.
The call at `:7323` changed from

```agda
                (f .tagEq0) (f .numK0) envK defPairK satK
```

to

```agda
                (f .tagEq0) (f .numK0) (f .pairK) (f .carrierK) (f .arityK) satK
```

**THE RESULT: `LeafAgree`, the outer interface, no longer asks any caller for a
tie that nothing could supply.** Two of `[LJ-1.338]`'s six residues are gone.

## 6. EVERY CONSUMER, VERIFIED (C-40)

**`DefinesAgree`, `LeafAgree`, `KTies`, `envOne-pair` and `ChainZ` have ZERO
uses outside `src/L/Condensation.lagda.md` in `src/`.** MEASURED, by grep of all
five names over `src/`: no hit outside the chapter.

**Five files import the chapter, and I typechecked all five.** Each names only
untouched exports, and each is green:

| consumer | imports | exit | seconds |
|---|---|---:|---:|
| `src/L/Condensation/LowerAgree.lagda.md:33` | `envHypB2` and 11 clause modules | 0 | 5.21 |
| `src/L/Condensation/UpperAgree.lagda.md:33` | `succU; keyU` and 12 clause modules | 0 | 5.51 |
| `src/L/Condensation/TwelveAgree.lagda.md:31` | `succU; keyU; module SatGraphB` | 0 | 8.23 |
| `src/L/Coding/EnvSupply.lagda.md:47` | `envSetB; module EnvSet` | 0 | 5.97 |
| `src/L/BoundedSubset.lagda.md:29` | `DefBodyB; Δ₀-DefBodyB; module GraphB` | 0 | 15.37 |

**I did NOT run `make check`; the orchestrator runs it.**
`.venv/bin/python scripts/gate/lint-prose.py --check`,
`scripts/gate/lint-agda.py --check`, `scripts/site/weave-i18n.py --check` and
`scripts/gate/check-probes.py --check` all **exit 0**.

## 7. THE NEGATIVE CONTROLS, BOTH MEASURING

**CONTROL A: THE REPAIR IS LOAD-BEARING IN THE PROOF, NOT ONLY IN THE TYPE.**
`agents/tasks/LJ-1-346/ControlA346.agda` asks the LANDED `KTies.envK` for the
PRE-repair unbounded tie, the one `[LJ-1.341]` proved FALSE, by dropping the
carrier hypothesis. **Exit 42 in 2.62 s**, refused at `ControlA346.agda:109.35-36`
with the satisfaction premise offered where `⟨ fst z ∈ fst (lookup A γ) ⟩` is
wanted. **So the landed supply does not accidentally prove the false statement.**
MEASURED.

**CONTROL B: THE PREMISE DISCRIMINATES.** `agents/tasks/LJ-1-346/ControlB346.agda`
is `Wire346.agda` with the entry tag changed from numeral ZERO to numeral ONE
and nothing else. **Exit 42 in 1.71 s**, refused at `ControlB346.agda:96.32-75`,
inside `liveE-eq`, with `⁅ # 0 , ⁅ # 0 ⁆s ⁆` against the numeral-zero shape.
**The tie is unchanged and still true; only the WITNESS dies.** So the premise
is a real constraint that some environments meet and others fail, which is what
a hypothesis that merely typechecks cannot tell you (C-45). MEASURED.

**THE POSITIVE HALF: `Wire346.agda`, exit 0 in 2.86 s.** It opens the LANDED
`KTies` at `KValue`'s own record, builds the one-entry environment as a carrier
element through `ChainZ.pair∈pr` and the new `envOne-pair`, and closes
`envK-fires : ⟨ fst (liveE (numeralL 0)) ∈ Lset lam ⟩` and
`defPairK-fires : ⟨ pr (# 0) (# 0) ∈ Lset lam ⟩`. **Every premise is discharged
except `KValue`'s own ordinal frame and one named hypothesis, `#1∈γ`, that the
carrier stage is at least 1.** That hypothesis is `[LJ-1.344]`'s and I did not
chase its supplier either.

## 8. DD4, WITH THE AXIS NAMED (C-46)

**THE AXIS IS AC-AGAINST-GCH, fixed at `scripts/measure/ledger.py:50`.**

**THE LANDED SUPPLY IS CLASS-FREE, and I re-measured it after landing.**
MEASURED, by grep over `src/L/Condensation.lagda.md:6160-6259` for `AC`,
`choice`, `GCH`, `wellorder`, `well-order`, `cardinal`, `aleph`, `ℵ` and `Card`:
**no hit.** The three terms name only `fst`, `∈`, `lookup`, `pr`, `prʟ`,
`numeralL`, `⁅_,_⁆` and four `KFacts` fields. **So the same 102 lines serve both
carriers, because `KFacts` is already generic.** One rule, two ends.

**AND THE LANDING MAKES THE SHARING BIGGER.** The 25 code lines of the two ties
were going to be paid once per carrier as an assumption at every call site; they
are now paid once, in a module both ends open. **`LeafAgree`'s telescope carries
two fewer things a future caller must invent.**

**`dev/ledger.toml:204` UNDERSTATES, as the brief notes.** The GCH closure is
read from a STATEMENT whose proof is not wired, and the row's own header says
the understatement grew by about 1,027 lines when `L.Absorption` and
`L.InjChain` left the closure. **I did not re-measure the ledger and I quote no
new figure from it.**

## 9. SECONDS, LOAD, RUNS

One agda process at a time, always `GHCRTS="-A64m -I0 -M8g"`, cap NEVER raised.
`ps aux | awk '/libexec.*bin\/agda/ && !/awk/' | wc -l` run before every
invocation: **0 every time**.

**THE FLOOR: 0.78 s**, `agents/tasks/LJ-1-346/Floor346.agda`, an empty module.

| run | exit | seconds |
|---|---:|---:|
| `agents/tasks/LJ-1-346/Floor346.agda` | 0 | 0.78 |
| `agents/tasks/LJ-1-346/CondCold346.lagda.md` (COLD BASELINE) | 0 | 132.11 |
| `src/L/Condensation.lagda.md` (COLD, LANDED) | 0 | **132.82** |
| `src/L/Condensation.lagda.md` (COLD, after a comment correction) | 0 | 134.15 |
| `agents/tasks/LJ-1-346/Wire346.agda` | 0 | 2.86 |
| `agents/tasks/LJ-1-346/ControlA346.agda` (EXPECTED RED) | 42 | 2.62 |
| `agents/tasks/LJ-1-346/ControlB346.agda` (EXPECTED RED) | 42 | 1.71 |
| `src/L/Condensation/LowerAgree.lagda.md` | 0 | 5.21 |
| `src/L/Condensation/UpperAgree.lagda.md` | 0 | 5.51 |
| `src/L/Condensation/TwelveAgree.lagda.md` | 0 | 8.23 |
| `src/L/Coding/EnvSupply.lagda.md` | 0 | 5.97 |
| `src/L/BoundedSubset.lagda.md` | 0 | 15.37 |

**NO RUN CAME NEAR THE 30-MINUTE WALL; the longest was 134.15 s. NO heap
exhaustion. The cap was never raised. Nothing was interrupted.**

**THE CACHE TRAP, honoured.** A plain re-check of the chapter before the edit
was a hit at about 2.4 s. **Every figure above is a real check**: the baseline
because the copy was new, the landed figure because the edit invalidated the
interface, the consumers because the chapter they depend on changed.

## 10. FROZEN RECORDS MY CHANGE MAKES STALER (named, NOT updated)

**AT HEAD THERE WAS EXACTLY ONE VERBATIM COPY OF THIS CHAPTER, NOT TWO.**
MEASURED, by diffing every `agents/` file containing `module ChainZ` against
`git show HEAD:src/L/Condensation.lagda.md`, ignoring the module line.

| record | diff-lines against HEAD before my edit | now |
|---|---:|---|
| `agents/tasks/LJ-1-345/CondCold345.lagda.md` | **0** | 102 lines behind |
| `agents/tasks/LJ-1-346/CondCold346.lagda.md` (mine) | **0** | 102 lines behind, frozen as my baseline |
| `agents/tasks/LJ-1-275/CondControlToday.lagda.md` | 27 | further behind |
| `agents/tasks/LJ-1-322/CondProbe.lagda.md` | 27 | further behind |
| `agents/tasks/LJ-1-266/CondensationControl.lagda.md` | 27 | further behind |

**The three 27-line records were ALREADY behind by `[LJ-1.343]`'s repair**, the
carrier hypothesis: their `DefinesAgree` still reads
`(envK : (E z : S) → ⟨ (E ∷ z ∷ γ) ⊨ envOneAt zero (suc zero) ⟩ → …)` with no
`⟨ fst z ∈ fst (lookup w γ) ⟩`. MEASURED, by reading the diff.

**Thirteen more `agents/tasks/LJ-1-331/Cond*.lagda.md` records and the
`LJ-1-266`, `LJ-1-204`, `LJ-1-209`, `LJ-1-214`, `LJ-1-99` and `LJ-1-306` probes
were already 135 to 7,312 lines apart and move no further in kind.** **I updated
NONE of them. A record is never rewritten.**

## 11. WHAT I DID NOT SETTLE

- **The four remaining ties.** `witK`, `graphWitK`, and the arity-numeral family
  `wCodesK` and friends. **Out of scope by the brief, and `[LJ-1.344]` marked
  the arity conjunct INFERRED FALSE, not MEASURED.** I did not touch them.
- **`ChainZ`'s three dead parameters.** `pair∈pr`, `singl∈pr`, `a∈singl` and
  `b∈pair` use none of `K`, `γ`, `arityK`, so an outside caller must invent an
  `arityK` to name them. **That friction is the real cause of the five
  re-writes, and lifting those four out of `ChainZ` is a separate rewrite.**
  INFERRED at about 10 lines moved and one chapter re-check. I did not build it.
- **`make check`.** Not run, by the brief.
- **The non-vacuity witnesses inside the chapter.** `Wire346.agda` holds them,
  and I did not land `sglS` or `liveE` into `src/`, because the chapter needs
  neither for the two ties.

## 12. ARCHIVE USED (DD18)

One line read per archived file, as the brief orders.

- **`agents/tasks/LJ-1-344/lj-1.344-report.md`, read WHOLE.** **Line read:** its
  section 7, 「ONE new module, immediately after `KFactsCons`, which ends at
  `src/L/Condensation.lagda.md:6155`, and before `module ShapesAgree` at
  `:6157`」. **TOOK** the site and all three terms, which land unchanged.
  **CORRECTED it twice:** its 「Better: make `inr∈⁅,⁆` public … That is a
  one-word edit」 is refused by section 3, and its account of the site omits the
  three missing imports of section 2.
- **`agents/tasks/LJ-1-345/lj-1.345-report.md`, read for the cache method.**
  **Line read:** its cold-figure protocol, 132.93 s against a 2.37 s floor from
  a verbatim copy with only the module renamed. **TOOK** the method exactly and
  reproduced the figure at 132.11 s. **REJECTED nothing.**
- **`agents/tasks/LJ-1-343/lj-1.343-report.md`, the landed repair.** **Line
  read:** the repaired telescope at `DefinesAgree`, 「`z` IS BOUND BY THE
  CARRIER SLOT `w`」, which is the comment now at
  `src/L/Condensation.lagda.md:6885-6892`. **TOOK** the hypothesis unchanged
  into `KTies.envK`. **KEPT its reason in the chapter**, rewritten around the
  new parameters rather than deleted.
- **`archive/dev/TASKS-archived.md`, read the header and the index shape.**
  **TOOK SHAPE ONLY:** a retired route's dispatch history. **REJECTED every
  figure:** that route has a different carrier and no `KFacts` record, so no
  count and no seconds figure from it prices anything here.

## 13. LITERATURE USED (DD18)

**`dev/literature/devlin-II5.md`, read `:238-256`.**

**THE ONE LINE THE BRIEF ASKS FOR: landing it puts the chapter's dependency
structure where Devlin's is, and this is the first time that is true of these
two ties.** `:246-249` says the argument binds every unbounded quantifier by the
concrete set `K(u)`, the finite sequences over the formula set, the variables
and the members of `u`. **Closure of `K(u)` under pairing and its transitivity
are properties Devlin ESTABLISHES of that construction, not premises he
assumes.** Until today the chapter ASSUMED the two ties, so it assumed what he
proves. **`KTies` derives them from `pairK`, `carrierK` and `arityK`, which are
the ports of exactly those two properties, so the chapter now proves what he
proves and assumes what he assumes.**

**WHY NOT the rest of the digest.** `:238-243` is the union law at limit stages
and the `[LJ-1.12]` Δ₀ question, both settled and neither about closure.
`:258` onward is Step D, the hull with least witnesses, which no tie of
`LeafAgree` reaches. **The cardinality halves of 5.5 and 5.6 are another step,
and C-46 forbids using Devlin's tower axis as DD4's.**

## 14. PROHIBITIONS, ANSWERED

I edited **`src/L/Condensation.lagda.md` only** in `src/`. **I did NOT open
`src/V/Coding.lagda.md` for writing**, because section 3 rules that it should
not change. I wrote nothing else in `src/`, nothing in `dev/`, nothing in
`AGENTS.md`, nothing in `.claude/`, and nothing in another task directory. I
READ and did not edit `agents/tasks/LJ-1-344/`, `LJ-1-345/`, `LJ-1-338/`,
`LJ-1-341/`, `LJ-1-302/` and `LJ-1-105/`. I did not touch
`src/Everything.lagda.md`. **No commit, no push, no `git checkout`, `stash`,
`reset` or `clean`. No `make check`.** No em dash in any language. `git status
--short` shows `src/L/Condensation.lagda.md` modified and six new files in
`agents/tasks/LJ-1-346/`, and nothing else.
