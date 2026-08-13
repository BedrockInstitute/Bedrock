# LJ-1.169 report: `powIter`, the last term with no provenance

tier: opus (version `override`). **No master is edited. `git status` shows two
new files, both mine, both in `agents/tasks/LJ-1-169/`. No commit, no push.**
Every negative is marked **MEASURED** or **INFERRED** (C-36). Written
incrementally (C-22).

## 0. HEADLINE, in the order the brief asked for it

1. **ALREADY DELIVERED, and it is the lead. The internal description of the
   definable power at a GENERAL carrier is built, two-way, and green
   (`DefAt`), and so is the whole satisfaction apparatus at a general
   carrier.** Six masters. Section 1.
2. **NO-GO, and by the brief's deepest clause: the rank accounting does NOT
   work in this tree's `𝒟ₒ`.** Section 3.
3. **The obstruction is MEASURED and it is ONE design decision, not a missing
   lemma. This tree's codes carry the carrier's members INSIDE the code tree.
   Devlin's do not.** `pr∈Lset-suc` shifts a stage by TWO for ONE Kuratowski
   pair, so the stage a code needs grows with the code's depth. **I proved that
   growth, and I proved that `+ω` absorbs it.** Section 3.2.
4. **The statement is NOT false.** It is INFERRED TRUE, by Devlin's own
   accounting, which costs a finite bump. **His accounting does not transfer to
   this coding**, and P-l is exactly why that matters. Section 3.4.
5. **The assembly above the gap is 12 lines and assumes nothing about `δ`.**
   The criterion was 80. **12 is below 80 and it is still a NO-GO**, because the
   12 lines buy the assembly and the unsupplied fact buys the rest. Section 2.
6. **The archive already answered this question, and its answer is `+ω`.**
   `archive/src/2026-08-09-rud-route/L/Rud/SatTable.lagda.md:214-220`. Section 6.
7. **`StageArith` now has its first consumer in the project.** Section 2.3.

## 1. WHAT I FOUND ALREADY DELIVERED

**The brief says `powIter` has "no source anywhere" and is "not in the tree as a
proof". The second half is right. The first half is not: most of the machinery a
proof needs is delivered, at a GENERAL carrier.**

### 1.1 The definable power is ALREADY DESCRIBED in the object language

**MEASURED. `src/L/Coding/Powerset.lagda.md` builds the description and both
readings.**

| name | `file:line` | what it is |
|---|---|---|
| `DefBody` | `src/L/Coding/Powerset.lagda.md:437-440` | "x is a definable subset of the carrier at slot w" |
| `DefAt` | `:442-443` | `DefAt u w = extAt u (∃̇ (∃̇ (DefBody w)))`, "u IS the definable power of w" |
| `DefAt-in` | `:645-648` | **UNCONDITIONAL** |
| `DefAt-out` | `:662-665` | the converse, **under `DefOK A`** |
| `DefAt-stage` | `:720-727` | at a stage the side condition is gone |
| `fill`, `read` | `:500-502`, `:546-548` | **both UNCONDITIONAL**, at a variable carrier |

**So `DefOK` is not a stray hypothesis. It is the elimination half of a delivered
two-way description**, and `DefAt-in` does not need it.

**Citation history, MEASURED.** `grep -rl DefAt agents/tasks/` returns
`[LJ-1.162]` and this task. **No task from `[LJ-1.165]` to `[LJ-1.168]` cited
it**, and those are the four gates that priced this supply chain.

### 1.2 The satisfaction layer at a GENERAL carrier is delivered, not pending

**MEASURED, and this corrects a reading the brief's table invites.** The brief
prices "the satisfaction layer" at about 270 from `[LJ-1.168]`. **That 270 is the
`TFacts` supply for the CONDENSATION layer.** The satisfaction machinery
`powIter` needs is a different thing and it stands green:

| name | `file:line` | carrier |
|---|---|---|
| `Sat : ∀ {n} → Formula S n → S` | `src/L/Coding/Sat.lagda.md:142` | **GENERAL `B : S`.** A SET |
| `Sat-mem` | `src/L/Coding/Sat.lagda.md:145-147` | GENERAL |
| `Adequate` / `Sat-spec` | `src/L/Coding/Bridge.lagda.md:295-297`, `:519` | GENERAL. Membership **IS** satisfaction in `(B, ∈)` |
| `defSet-Sat` | `src/L/Coding/Bridge.lagda.md:621-623` | GENERAL. **Bridges `defSet` to the satisfaction set** |
| `satGraph`, `satGraphAt` | `src/L/Coding/Graph.lagda.md:238`, `:204-205` | GENERAL, at a slot |
| `AllCodes` and its two directions | `src/L/Coding/CodeSet.lagda.md:440-461` | GENERAL |
| `satRec`, `val-sat` | `src/L/Coding/Uniform.lagda.md:342`, `:376-380` | GENERAL |
| `soundness` | `src/L/Coding/Sound.lagda.md:354` | GENERAL |

**MEASURED: not one of these files mentions `Lset` or `IsOrd`.** The stage enters
the coding layer at exactly three sites: `DefAt-stage`
(`src/L/Coding/Powerset.lagda.md:720`), the `PowOK` discharge
(`src/L/Hierarchy.lagda.md:167-171`), and `stageFor`
(`src/L/Coding/EnvSet.lagda.md:91-92`).

**Citation history, MEASURED.** `src/L/Coding/Sat.lagda.md`, `defSet-Sat`,
`carve∈𝒟ₒ` and `src/L/Axioms/Separation.lagda.md` are cited by **no** task in
`agents/tasks/LJ-1-15*/` or `LJ-1-16*/` before this one.

### 1.3 THE STRUCTURAL FACT THIS WING HAS NOT WRITTEN DOWN

**MEASURED, and it governs everything below.**

> **The whole coding layer is LEVEL-BLIND.** Every set it builds comes from
> separation or replacement over a bound that `smallDom` or `stageFor` invents.
> **No set in it carries a level stated in terms of the carrier's level.**

- `smallDom : (X : Type ℓ) (f : X → S) → Σ[ d ∈ S ] (...)`,
  `src/L/Recursion.lagda.md:133-134`. It returns `LsetS β oβ` for a `β` the
  replacement produces. **The level is an output, not a function of the input.**
- `stageFor`, `src/L/Coding/EnvSet.lagda.md:91-92`. Same shape.
- `L.Axioms.Power`'s `Bound.β`, `src/L/Axioms/Power.lagda.md:149-155`, and the
  file says so itself at `:25-28`: **"Condensation is not part of this."**
- `AllCodes` is separated from `smallAny = smallDom ...`,
  `src/L/Coding/CodeSet.lagda.md:304-311`, `:441`.

**Consequence.** `powIter` is a LEVELED statement. The coding layer can reach
`isL (𝒟ₒ y)` shapes; as delivered it cannot reach any `... ∈ˢ Lset (f δ)`.
**The gap is not one lemma. It is that a level-blind layer is asked for a
level.**

### 1.4 The two hypotheses, and their single discharge

**MEASURED, and it confirms the brief.** `DefOK`
(`src/L/Coding/Powerset.lagda.md:445-446`) and `PowOK`
(`src/L/Coding/Sequence.lagda.md:130-131`). **All three directions of `StepAt`
take `PowOK`** (`src/L/Coding/Sequence.lagda.md:217-228`), so nothing in that
file is unconditional in it. Its one discharge is
`src/L/Hierarchy.lagda.md:167-171`, and it rewrites the value to `Lset (fst c)`
first.

**Both are `isL` statements, not leveled ones. So discharging them does NOT give
`powIter`, and `powIter` is strictly stronger than either.** No brief has said
this, and it changes what a supply must buy.

### 1.5 `StageArith` was written for this and its comment states the answer

**MEASURED. `src/L/Ordinal/StageArith.lagda.md:84-85`:**

> The code set over the carrier at δ sits at stage **δ+ω**. Under closure, the
> stage δ+ω stays below α for every δ below α, so the bound lands in Lset α.

**Its author priced this at `+ω`, not at a finite bump, before this wing began.**

**And `envCloses` (`:92-96`) takes `env ∈ˢ Lset (sucIter 3 δ)` as a HYPOTHESIS.**
It is a climb, not a bound. **Nothing in the tree supplies its hypothesis.**

### 1.6 The miss this time is `src/L/Axioms/Separation.lagda.md`

**The brief names `src/L/Choice/` as one of two places this wing fails to look. I
looked. The load-bearing miss this time is elsewhere.**
`src/L/Axioms/Separation.lagda.md` holds the tree's only instantiation of the
relabelling into a stage's constant domain, and the bridge that reads inner
satisfaction as satisfaction in `L`:

| name | `file:line` |
|---|---|
| `module RL = Relabel {K = S} {K' = ⟪ Lset σ ⟫} ...` | `src/L/Axioms/Separation.lagda.md:131-135` |
| `satBridge` | `:150-153` |
| `carveSat` | `:163-166` |
| `carve∈𝒟ₒ : (ψ : Formula ⟪ Lset σ ⟫ 1) → ⟨ carve ψ ∈ 𝒟ₒ (Lset σ) ⟩` | `:198-199` |
| `liftFoTo`, `mkBoundedFo` | `:425-427`, `:449` |
| `separateAt`, `separateΔ₀` | `:281-283`, `:481-482` |

**`carve∈𝒟ₒ` with `satBridge` is the usable route into `𝒟ₒ (Lset σ)`: a Δ₀
formula of `L`'s object language with every constant below `σ` carves a member.**
Both conditions are where `powIter` fails, and section 3 says why.

### 1.7 Relativization is delivered and is NOT the gap

**MEASURED.** `relativize` (`src/FOL/Manipulation/Relativize.lagda.md:48`),
`Δ₀-relativize` (`:72`), `relativize-correct` (`:142-143`); `Relabel.liftFo`,
`liftFo-correct`, `Δ₀-liftFo` (`src/FOL/Manipulation/Bounding.lagda.md:162`,
`:198-199`, `:220`). **The SUBSET half of `powIter` has its tools. The
MEMBERSHIP half does not.**

## 2. THE ASSEMBLY, MEASURED

**`agents/tasks/LJ-1-169/ProbeLJ1169A.agda`, exit 0.**

### 2.1 One lemma serves both forms

```agda
Describes σ y = ∥ Σ[ ψ ∈ Formula ⟪ Lset σ ⟫ 1 ] (DefOf.defSet (Lset σ) ψ ≡ 𝒟ₒ y) ∥₁

defPow-at : (σ y : S) → Describes σ y → ⟨ 𝒟ₒ y ∈ˢ Lset (sucV σ) ⟩
```

`ProbeLJ1169A.agda:80-86`. **6 lines. It is `𝒟ₒ-intro` at the value `𝒟ₒ y`, then
the successor identity `Lset-suc`.** Nothing about `δ`, ordinality or limits
enters.

### 2.2 The brief's statement, from that one fact

| part | `ProbeLJ1169A.agda` | lines |
|---|---|---:|
| `Describes` and `defPow-at` | `:80-86` | 6 |
| `powIter-from` | `:91-96` | 6 |
| **`powIter` FROM THE ONE FACT** | | **12** |
| `powBlock-from`, the ω-block form | `:101-106` | 6 |
| `pow-closed`, the consumer under `closedω` | `:112-117` | 6 |
| `powAtBlock`, the reachable form | `:125-127` | 3 |
| `pow-closed-suc`, its consumer | `:129-136` | 8 |
| **BLOCK 1 total** | | **36** |

**`sucIter (suc k) δ` is `sucV (sucIter k δ)` by
`src/L/Ordinal/StageArith.lagda.md:34-36`, so no arithmetic is spent.**

### 2.3 `StageArith` has its first consumer

**MEASURED.** `powBlock-from` uses `+ω-iter`, `pow-closed` uses `boundCloses`,
and `prTower-ω` (section 3.2) uses `+ω-iter` again. **Before this probe the
module was imported only by `src/Everything.lagda.md:322`**
(`[LJ-1.167]` section 1.2, re-checked).

## 3. GO OR NO-GO, AND WHY THE RANK ACCOUNTING DOES NOT WORK HERE

### 3.1 The verdict

**NO-GO, by the brief's second clause. The rank accounting needs a fact nothing
supplies, and I name it: `Describes`.**

**The count is 12 against a criterion of 80. I did not move the criterion, and
12 is NOT a pass**, because the criterion prices a PROOF of `powIter` and 12 is
the price of everything except the fact. **I report it so the next brief can
subtract it, exactly as `[LJ-1.167]` reported its 24.**

**And the brief's deepest clause FIRES. I say it first, as instructed.**

### 3.2 THE RANK ACCOUNTING DOES NOT WORK IN THIS TREE'S `𝒟ₒ`, and here is the measurement

**The chain, every link at `file:line`.**

1. **A code is a nested Kuratowski pair.** `⌜ φ ∧̇ ψ ⌝ = mkTag 2 (pr ⌜ φ ⌝ ⌜ ψ ⌝)`
   and the same for every binary constructor, `src/FOL/Coding.lagda.md:124-136`.
   `⌜ con x ⌝ᵗ = mkTag 0 x`, `:105`. **So the code tree's nesting depth is the
   formula's depth, and the carrier's members sit at its leaves.**
2. **`key` wraps it once more.** `key {n} φ = pr (# n) VCode.⌜ mapFo f φ ⌝`,
   `src/L/Coding/InL.lagda.md:252-253`. `keyS A φ = key ι ιL φ`,
   `src/L/Coding/CodeSet.lagda.md:300-301`.
3. **The tree's pairing closure SHIFTS the stage by TWO.**
   `pr∈Lset-suc : (σ x y : V ℓ) → x ∈ Lset σ → y ∈ Lset σ → pr x y ∈ Lset (sucV (sucV σ))`,
   `src/L/Axioms/Basic.lagda.md:596-599`. **MEASURED.**
4. **`[LJ-1.166]` MEASURED that this is the tree's only pairing closure that is
   not pinned to `Lset ω`** (`agents/tasks/LJ-1-166/lj-1.166-report.md:185-192`).
   The one `κ → κ` closure is `pr∈limit` at `Lset ω`.
5. **So the stage a code needs grows with the code's depth. I proved the growth
   and I proved that `+ω` absorbs it.**

```agda
prTower-level : (n : ℕ) (σ x : S) → ⟨ x ∈ˢ Lset σ ⟩
              → ⟨ prTower n x ∈ˢ Lset (sucIter (dbl n) σ) ⟩

prTower-ω : (n : ℕ) (σ x : S) → ⟨ x ∈ˢ Lset σ ⟩
          → ⟨ prTower n x ∈ˢ Lset (+ω σ) ⟩
```

`ProbeLJ1169A.agda:150-182`, **19 lines, exit 0.** `dbl n` is the stage count and
it is the nesting depth doubled.

**The reading, stated so it cannot be overclaimed. MEASURED: the level the
delivered route produces for a code of depth `n` is `sucIter (dbl n) σ`, and
`dbl` is unbounded over `Formula`. INFERRED: therefore no fixed `sucIter k σ`
holds every code over a carrier at `σ`.** I did not prove a rank lower bound and
I do not claim one.

**`+ω σ` holds them all, uniformly in `n`, and that is MEASURED.**

### 3.3 Why the `+ω` form does not dodge the gap either, and what DOES

**MEASURED, from the probe.** `powBlock-from` takes the SAME hypothesis as
`powIter-from`: `Describes` at a finite iterate. **So restating the conclusion at
`+ω δ` buys nothing on its own.**

**What works is moving the CARRIER, not the conclusion.** `powAtBlock`
(`:125-127`) reads the description at the ω-block itself:

```agda
powAtBlock : (δ y : S) → Describes (+ω δ) y → ⟨ 𝒟ₒ y ∈ˢ Lset (sucV (+ω δ)) ⟩
```

**`Describes (+ω δ) y` is the version this tree can hope to supply**, because
`prTower-ω` puts every code over a carrier at `δ` inside `Lset (+ω δ)`. The price
at the consumer is one extra hypothesis: `pow-closed-suc` (`:129-136`, 8 lines)
needs `closedω lam` **and** successor closure, where `[LJ-1.167]`'s
finite-iterate reduction needed successor closure alone.

**So the honest restatement is not a weakening of the conclusion. It is a
strengthening of the carrier, and it costs the consumer one hypothesis.** I did
not weaken `powIter`; I measured which of its two readings this coding can reach.

### 3.4 The statement is TRUE. Devlin's accounting is right and does not transfer

**INFERRED TRUE, and the reason it does not transfer is one design decision.**

**Devlin's bound, verbatim, `_build/literature/dev2.txt:600-608`:**

> K(u) = [the set of finite sequences of members of the set 𝓕 ∪ {vᵢ | i ∈ ω} ∪
> {x | x ∈ u}] ∪ [the set of finite sequences of finite sequences of members of
> the set ...] ∪ [the set of finite sequences of finite subsets of the set ...]

**Read what that says. His formulas live in a FIXED set `𝓕` that does not depend
on `u`. The dependence on `u` is carried by finite SEQUENCES over `u`.**

**And a finite sequence costs a UNIFORM finite bump, which this tree proves.**
`finSet∈𝒟ₒ` (`src/L/Axioms/Basic.lagda.md:352-354`) puts any finite family of
members of a stage in `𝒟ₒ` of that stage, and its own prose at `:257-268` says
"a finite table drawn from a stage is a set of `L` without any further
argument". **A finite set of members of `Lset σ` costs ONE stage whatever its
length. A nested pair of depth `n` costs `2n`.**

**THE DIVERGENCE, stated once:**

| | where the parameters live | cost above the carrier |
|---|---|---|
| **Devlin** | in a finite SEQUENCE, beside a code drawn from a fixed `𝓕` | **uniform finite** |
| **this tree** | at the LEAVES of the code tree, `⌜ con x ⌝ᵗ = mkTag 0 x` | **grows with formula depth** |

**So the rank accounting `[LJ-1.167]` inferred is sound mathematics and it is
Devlin's. It is not this tree's.** P-l is exactly this law: a measured cure does
not transfer by analogy, and `[LJ-1.167]` marked its own accounting INFERRED for
this reason.

**This is the finding the brief asked me to say first if I found it, and I have
put it in the headline.**

### 3.5 The second unsourced term, named and split

**`Describes σ y` is the fact. It splits, and the two halves have different
obstructions.** `ProbeLJ1169A.agda:209-234`, 16 lines, exit 0.

| half | statement | obstructed by BLOCK 2? |
|---|---|---|
| **HALF 1, the SUBSET half** | `SubsetHalf σ y = (x : S) → x ∈ˢ 𝒟ₒ y → x ∈ˢ 𝒟ₒ (Lset σ)` | **NO.** One formula in, one formula out, per definable subset. No quantification over codes |
| **HALF 2, the MEMBERSHIP half** | one formula of the stage carves the WHOLE of `𝒟ₒ y` | **YES.** Its `∃̇ c` must reach every code |

**`subsetHalf-from` (`:225-234`) reduces HALF 1 to a purely formula-level fact:
given `χ : Formula ⟪ y ⟫ 1`, produce `ψ : Formula ⟪ Lset σ ⟫ 1` with the same
`defSet`.** That is `relativize` composed with `Relabel.liftFo`, both delivered
(section 1.7). **MEASURED: HALF 1 is the leveled form of `DefOK`, and it is
reachable with delivered tools.** I did not build it; I built its assembly and
named its one obligation.

**HALF 2 is the term with no source, and it stays unsourced.**

## 4. WHAT THE WHOLE SUPPLY CHAIN COSTS END TO END

| | in-fence lines | state |
|---|---:|---|
| the assembly, `levelIn` and `cover` from one face | 17 | MEASURED GREEN, `[LJ-1.165]` |
| `K(u)`'s closure layer | 88 | MEASURED GREEN, `[LJ-1.166]`, at a LIMIT parameter |
| pairing at an arbitrary limit | 35, net +15 | MEASURED GREEN, `[LJ-1.166]`, `[LJ-1.167]` |
| the satisfaction layer (`TFacts`) | about 270 | priced, `[LJ-1.168]` |
| `pow∈λ` from `powIter` | 24 | MEASURED GREEN, `[LJ-1.167]` |
| **`powIter` from `Describes`** | **12** | **MEASURED GREEN, this task** |
| **`Describes`, HALF 1** | **not priced** | reachable; `relativize` and `liftFo` delivered |
| **`Describes`, HALF 2** | **NOT PRICEABLE TODAY** | **it needs a coding decision, not a lemma** |

**I do NOT publish an end-to-end total, and DD8 is why.** HALF 2's price is not a
line count waiting to be estimated. **It is a fork:**

- **Fork A, re-code.** Split the code from its parameters, as Devlin does: a
  fixed formula set plus a finite environment over the carrier. Then the finite
  bump is available and `powIter` holds as stated. **This touches
  `src/FOL/Coding.lagda.md` and every master above it.**
- **Fork B, move the carrier.** Supply `Describes (+ω δ) y` instead, pay
  `closedω` at the consumer, and keep the coding. **`StageArith` was written for
  this fork and the retired route took it (section 6).**

**A brief that funds HALF 2 without ruling this fork will get a number for a
variant nobody chose.** I recommend Fork B and I say why in section 5: it is the
one the delivered kit already serves, and the retired route measured it once.

**What IS now closed.** Every term in the chain except HALF 2 has either a
measured price or a delivered supplier. **`[LJ-1.7]` does not yet have a number
with no gap in it, and the gap is one term wide.**

## 5. DD4

**Maximize the code the two proofs share, and write it generic. One rule, two
ends, no metric and no checker.**

### 5.1 The measurement

Tokens counted: `Lset`, `𝒟ₒ`, `+ω`, `sucIter`, `defSet`.

| block | lines | naming a tower | tower-blind |
|---|---:|---:|---:|
| BLOCK 1, the assembly | 36 | 30 | 6 |
| BLOCK 2, the obstruction | 19 | 8 | 11 |
| BLOCK 3, the gap named | 16 | 12 | 4 |

### 5.2 Which side this falls on, and I say it plainly

**BLOCK 2 is TOWER CONTENT and it is the strongest DD4 item this wing has
produced.** `dbl`, `prTower` and the pairing-growth law say nothing about `L`.
They are facts about a stage function, a Kuratowski pair and a successor. **The
J tower has the same pair, the same successor and the same growth**, so the
argument transfers whole and only the stage function's name changes.
**`prTower-ω` is the shape of every "the code set sits at `+ω`" argument either
tower will ever need.**

**BLOCK 1 is NOT template as written, and the reason is structural.** Thirty of
its 36 lines name a tower because the STATEMENT does: `powIter` is about `𝒟ₒ` and
`Lset`. **But the SHAPE is one move — describe at a carrier, land one stage up
by the successor identity — and nothing in that move is L-specific.**
Parameterise over the stage function, the definable-power operator and the
successor identity, and the same 12 lines serve the J tower.

**I do NOT price the generic variant, because I did not write it** (DD8, C-36).

**`[LJ-1.168]` recommended writing the SUPPLY fixed. My work does not contradict
that and does not confirm it**: `[LJ-1.168]` measured the STATEMENT layer, and
this task measured the ASSEMBLY and the CODING. **The coding is the one place
where writing generic would pay twice, because the growth law is the same on
both towers.**

**No stop-line pushed me toward writing fixed.** I wrote against the L names
because the probe's job was to name the missing fact, and a generic wrapper would
have added elaboration cost to the thing under measurement.

## 6. ARCHIVE USED (DD18)

- **`archive/src/2026-08-09-rud-route/L/Rud/SatTable.lagda.md`, READ. THE
  DECISIVE ARCHIVE FIND, and the brief did not name this file.**
  - `Pow.pow≡` (`:119`) and `Pow.pow∈J` (`:143-145`) prove the definable power
    **at a GENERAL carrier `C`**, taking a code set `K` and a satisfaction
    relation `R` already inside the target stage as hypotheses.
  - **`blockPow-at-limit` (`:214-220`) concludes `⟨ 𝒟ₒ C ∈ˢ Sset (+ω δ) ⟩`.**
  - `BlockPowLim` (`:210-212`) is a named `Type`, so a hypothesis, not a
    theorem.
  - **TAKEN: the SHAPE and the BOUND.** `[LJ-1.11]` ruled that route's
    condensation target classically false, so I take no claim. **The bound is a
    shape fact, not a claim about condensation**, and it agrees with
    `StageArith`'s own comment and with my BLOCK 2. **The retired route reached
    `+ω`, never a finite iterate.**
- **`archive/src/2026-08-09-rud-route/L/Definability.lagda.md`, checked. It
  builds NO closure at a general argument**, which confirms `[LJ-1.167]`
  section 10. **The brief pointed at this file; the content is in
  `L/Rud/SatTable.lagda.md`.**
- **`archive/src/2026-08-09-rud-route/L/Axioms/`: no general-limit closure**,
  as `[LJ-1.167]` MEASURED. Re-checked, unchanged.
- **`agents/tasks/LJ-1-167/lj-1.167-report.md`, READ WHOLE.** TOOK the `powIter`
  statement (`:139-144`), the two hypotheses (`:146-160`), the Devlin reading
  (`:165-183`), the rank accounting (`:186-209`) and the two reductions
  (`:212-235`). **Section 3.4 says its accounting is Devlin's and does not
  transfer to this coding, and marks that INFERRED.**
- **`agents/tasks/LJ-1-166/lj-1.166-report.md`, READ WHOLE.** TOOK the `KFacts`
  field classes (`:100-119`), `K(u) := Lset λ` (`:132-137`), the delivered
  closure trio (`:151-163`) and **the one-`κ→κ`-closure count (`:185-192`)**,
  which is link 4 of section 3.2.
- `agents/tasks/LJ-1-168/lj-1.168-report.md`, READ. TOOK the four delivered
  suppliers (`:27-108`) and the `TFacts` price (`:21-23`). **Section 1.2 says
  its 270 prices a different layer from the one `powIter` needs.**
- **`dev/LESSONS.md`: D-1, P-l, P-i, C-36, C-38 as extended, C-12, C-22, D-10,
  R-40 read through `.venv/bin/python scripts/rules.py --for probe`.** **P-l is
  the load-bearing one this task and section 3.4 spends it.**
- `archive/dev/`: **NOT read.** No `D`-series ruling bears on a coding decision
  or a line count, and I mark the omission rather than imply a survey.

## 7. LITERATURE USED (DD18)

- **`_build/literature/dev2.txt:593-637`, READ VERBATIM. It answers the brief's
  question and it answers it against the brief's expectation.**
  - **`K(u)` is the set of finite SEQUENCES over `𝓕 ∪ {vᵢ | i ∈ ω} ∪ {x | x ∈ u}`**
    (`:600-608`). **The formula set `𝓕` does not depend on `u`.** Section 3.4.
  - `D(v, u) = ∃w [K(w, u) ∧ C(w, v, u)]` (`:620-623`), and `C` is `B` with every
    unbounded quantifier bound by `w`.
  - **2.4's proof is "As in 2.2 and 2.3. (The details are left as an exercise
    for the reader.)"** (`:632`). Confirmed, and the line number matches
    `[LJ-1.167]`'s correction.
- **`_build/literature/dev2.txt:466-478` and `:548-556`, READ. This is the
  brief's literature question, answered.**
  - **2.2 is `Seq(y, x)`: "y is the set of all finite sequences from x"**
    (`:468-469`). Proved Δ₁ and uniformly Δ₁ over `L_α` for limit `α > ω`.
  - **2.3 is `Pow(y, x)`: "y is the set of all finite subsets of x"**
    (`:549-555`).
  - **Does the pattern carry the general case? YES for Devlin, NO for this
    tree.** `K(u)` is built by applying exactly `Seq` and `Pow` to
    `𝓕 ∪ {vᵢ} ∪ u`, so 2.4 needs 2.2 and 2.3 and nothing else. **Both are
    finite-bump constructions over the carrier.** This tree has the same
    constructions (`finSet∈𝒟ₒ`), **but its codes are not drawn from a fixed
    `𝓕`**, so the two lemmas do not bound its code set. Section 3.4.
- **`dev/literature/devlin-II5.md:240-260`, READ.** `:245-255` records that the
  substrate needs "some bounded description with a bound inside the carrier",
  and that the argument "does not require them to have any particular shape".
  **MEASURED: the digest names `K(u)` as "the finite sequences over the formula
  set, the variables and the members of u" at `:247-249`, so it DOES carry the
  shape.** `[LJ-1.167]` reported that the digest drops the closure fact; **that
  is right about the CLOSURE and wrong about `K(u)`'s shape**, and the shape is
  what section 3.4 turns on.
- `dev/literature/devlin-errata.md`: **NOT read**, on `[LJ-1.136]`'s measurement
  that the errata touch no part of II.5.

## 8. RUN LOG, criterion fixed in writing before the first run

**The criterion is in the probe's own header, `ProbeLJ1169A.agda:5-15`, written
before any Agda ran: 10 minutes of wall time per invocation,
`GHCRTS="-A64m -I0 -M8g"`, ONE process, cap NEVER raised.**

| run | file state | exit | wall | resident set |
|---|---|---|---:|---:|
| 1 | BLOCKS 1 to 3 | 0 | **9.44 s** | 489 MB |
| 2 | unchanged, exit code confirmed alone | **0** | not timed | not timed |
| 3 | `powAtBlock` and `pow-closed-suc` added | **0** | **12.17 s** | 492 MB |

**ONE agda process at a time. No heap exhaustion. Cap never raised. The
10-minute criterion was not approached.** Basis: `/usr/bin/time -l`, warm
dependencies, the whole file.

**DD24 is not usefully answered at this size and I say so rather than publish a
ratio that means nothing:** the numerator is import loading.

**P-i's implicit-index repair: applied prophylactically, never tested.** Every
implicit set index at a concrete argument is written out
(`ProbeLJ1169A.agda:104-106`, `:135-136`, `:173-174`). **No run walled, so this
task does NOT give the repair a measurement**, and I will not manufacture one.

| checker | result |
|---|---|
| `scripts/lint-agda.py --check` | **exit 0** |
| `scripts/check-probes.py --check` | **clean, 1,787 tracked files** |
| `scripts/lint-prose.py --check` on this report | run at close |
| `make check` | **NOT RUN.** The orchestrator runs it |

**Prohibitions, answered one by one.** **No master edited**; `git status` shows
exactly two new files, `agents/tasks/LJ-1-169/ProbeLJ1169A.agda` and this report.
`src/Everything.lagda.md` never opened. The three `*Agree` masters and
`src/L/Coding/Graph.lagda.md` read by `grep` only, never edited. `[LJ-1.164]`'s
move untouched. **No commit, no push, no `git checkout .`, no `stash`, no
`reset`, no `clean`.** No probe under `src/`. **No `postulate`, no hole, no
unsolved meta**, and `--safe` is on. I did not edit an earlier probe; I wrote a
new file.

## 9. EVERY NEGATIVE, CLASSIFIED

| statement | class |
|---|---|
| `powIter` is proved | **MEASURED FALSE. NO-GO.** Only the assembly is proved, 12 lines, resting on `Describes` |
| the assembly needs a hypothesis on `δ` | **MEASURED FALSE.** `defPow-at` and `powIter-from` assume nothing about `δ` |
| the tree has no internal description of the definable power | **MEASURED FALSE.** `DefAt`, `src/L/Coding/Powerset.lagda.md:442-443`, two-way, at a GENERAL carrier |
| the satisfaction machinery must be written | **MEASURED FALSE at a general carrier.** `Sat`, `Sat-spec`, `defSet-Sat`, `satGraph`, `AllCodes`, `satRec`, `soundness` all stand at a general `B : S` |
| any of those files mentions `Lset` or `IsOrd` | **MEASURED FALSE.** None does |
| the coding layer can state a level in terms of the carrier's level | **MEASURED FALSE.** `smallDom` and `stageFor` invent the bound. Section 1.3 |
| discharging `DefOK` and `PowOK` gives `powIter` | **MEASURED FALSE.** Both are `isL` statements with no level in them |
| the rank accounting works in this tree's `𝒟ₒ` | **MEASURED FALSE, and this is the brief's deepest clause.** Section 3.2 |
| the statement `powIter` is false | **INFERRED FALSE.** Devlin's accounting makes it true; it needs his coding |
| the code's stage cost grows with formula depth | **MEASURED TRUE.** `prTower-level`, `dbl n` stages for depth `n`, exit 0 |
| `+ω σ` absorbs every code depth at once | **MEASURED TRUE.** `prTower-ω`, exit 0 |
| some fixed `sucIter k σ` holds every code | **INFERRED FALSE.** `dbl` is unbounded. **I proved NO rank lower bound and claim none** |
| the tree has a `κ → κ` pairing closure above `ω` | **MEASURED FALSE.** `[LJ-1.166]:185-192`. The only one is `pr∈limit` at `Lset ω` |
| restating the conclusion at `+ω δ` dodges the gap | **MEASURED FALSE.** `powBlock-from` takes the same hypothesis |
| moving the CARRIER to `+ω δ` reaches a supplied form | **MEASURED TRUE as an assembly.** `powAtBlock`, 3 lines. **The supply itself is still unbuilt** |
| the SUBSET half is obstructed by the code growth | **MEASURED FALSE.** It quantifies over no codes. Section 3.5 |
| the SUBSET half is built | **MEASURED FALSE.** Only its assembly and its one obligation are written |
| Devlin proves the closure | **MEASURED FALSE.** `dev2.txt:632`, "left as an exercise for the reader" |
| Devlin's 2.2 and 2.3 are about satisfaction | **MEASURED FALSE.** 2.2 is `Seq`, 2.3 is `Pow`, both about finite sequences and finite subsets |
| Devlin's pattern carries the general case | **MEASURED TRUE for his coding, MEASURED FALSE for this one.** Section 3.4 |
| the digest drops `K(u)`'s shape | **MEASURED FALSE.** `devlin-II5.md:247-249` carries it. It drops the CLOSURE, which is `[LJ-1.167]`'s point |
| the archive holds no general-carrier definable-power closure | **MEASURED FALSE.** `archive/.../L/Rud/SatTable.lagda.md:119`, `:143-145`, `:214-220`, and it lands at `+ω` |
| `[LJ-1.168]`'s 270 prices what `powIter` needs | **MEASURED FALSE.** It prices the `TFacts` supply for condensation |
| `StageArith` had a consumer before this task | **MEASURED FALSE.** Only `src/Everything.lagda.md:322` |
| P-i's repair fired | **MEASURED FALSE.** No run walled. This task gives the law no measurement |
| anything walled | **MEASURED FALSE.** Three runs, longest 12.17 s, against a 10-minute criterion |
| an end-to-end total exists today | **NOT CLAIMED, and section 4 says why.** HALF 2's price is a fork, not a line count |
| the generic two-tower variant is cheaper | **NOT CLAIMED, and NOT TESTED.** I did not write it |
