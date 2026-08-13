# R5-G3G4G5: the bridge assembly

One new file, `src/L/Rud/Bridge.lagda.md`, 338 code lines, 561 file lines, green
at **40.8 s cold** (`GHCRTS=-M12g`), lint-agda / lint-prose / i18n markers /
glossary all clean. No other file touched, no commit, `Everything` untouched
(the next batch must add the import line there).

The headline is a **D-10 finding that changes the shape of the batch**: the
recon's expected mutual induction is not merely expensive, its *target as
recorded is false*, and the true target is walled by a fact neither delivered
pillar supplies. Everything reachable was built; the endpoints are packaged over
the one honest hypothesis.

---

## 1. G5: the offset, verified and proved

**What was asked.** For `U = Jset μ` at a limit, every image-arm value
`Fof i a b` with `a, b ∈ U ∪ {U}` lands in `Lset` at the right offset; verify the
offset before proving.

**What is true, and proved.** Read against the Def tower the junk/plain
distinction *disappears*: the only thing that matters is that some stage holds
`U` as a **member**. Three facts, each proved:

| export | statement | file |
|---|---|---|
| `Arms.imgArm` | at any transitive carrier `C` with `A ∈ C`: for `a, b ∈ C` and `Fof i a b ⊆ C`, a Δ₀ formula over `⟪ C ⟫` whose definable subset **is** `Fof i a b` (all sixteen) | Bridge:196-266 |
| `Lval` | `a, b ∈ Lset ζ`, value's members `∈ Lset ζ` ⟹ `Fof i a b ∈ Lset (sucV ζ)` | Bridge |
| `Ljunk` | `U ∈ Lset ζ`, `a, b ∈ U ∪ {U}`, value's members `∈ Lset ζ` ⟹ `Fof i a b ∈ Lset (sucV ζ)` | Bridge |

**The honest offset.** Not "one or two Def steps above the stage holding
`U ∪ {U}`" flat, but a two-part count, and the first part is forced by
irreflexivity:

- `U = Lset μ` is **never** a member of `Lset μ`, so the stage that holds
  `U ∪ {U}` is `Lset (sucV μ)`, not `Lset μ`. (This was caught by a hole in the
  first draft of `Lstep-absorb`, which asked for `Lset μ ∈ Lset μ`.)
- the value is definable over the stage that holds *both arguments and all the
  value's members*, and lands one stage above it.
- for the **flat** values (`F1`, `F5`, `F6`, `F15`, and the member arm) the
  value's members are already in `Lset (sucV μ)` by transitivity, so the offset
  is **two** stages above the matched index: `Lset (sucV (sucV μ))`.
- for the **pair-valued** values (`F0`, `F9`, `F2`, `F3`, `F4`, `F7`, `F11`-`F14`)
  the members are Kuratowski pairs of things in `Lset (sucV μ)`, and pairing
  costs one stage (`Lpair`), so the offset is **three**.
- all of it is absorbed by the next limit stage, which is why the final export
  `Lstep-absorb` is stated at an arbitrary target stage `ζ` rather than at a
  fixed offset: `ζ` holds `U`, the step lands in `Lset (sucV ζ)`.

**Why the sixteen arms had to be rebuilt rather than reused.** `LevelDesc`'s
plain-argument cases are one-liners (`memberArm` after `Urud`) because the rud
level is closed under the sixteen operations; a *constructible* stage is not
(that is what the bridge is trying to prove), so every arm here is the genuine
description from `L.Rud.Describe`. That chapter turned out to state all sixteen
descriptions **at an arbitrary transitive carrier** (`F0Desc … F15Desc`, plus
`Switch.Hops` for the `out` directions of `F2/F3/F4/F6/F7`), which is what made
120 lines enough. Six of the sixteen (`F9`, `F11`-`F14`, and `F0` itself) go
through the pairing arm, because their values are literally `F0` of two named
sets. The one side condition is the relativization slot, `A ∈ C`, exactly as in
`LevelDesc` minus its level case; it is an argument of `imgArm`, not a module
parameter, so `pairArm` stays usable where `A` is not yet in the stage.

**Left open, deliberately** (`ValuesIn`, a named hypothesis in the file): the
subset side, "each value's members are already in the stage". It is sixteen
mechanical discharges, one member characterization each (`F1-spec`, `F5-spec`,
`F6-read`, `F8-spec`, `F10`'s read, `F2-read`, `F3-read`, `F4-read`, `F7-read`,
`F15A-spec`, the `left`/`right` junk lemmas for `F11`-`F14`), plus `Lpr-limit`
for the pair-valued ones. `Lpair-limit` and `Lpr-limit` (proved here) are the
engine for that: **a limit stage is closed under pairing and under the
Kuratowski pair**, via a common-stage lemma (`Lstage₂`) and ordinal trichotomy.
Estimated 150-250 lines, no new risk class.

## 2. The mutual induction: D-10, twice

### 2a. The recon's target is false

The recon expected `Lset α ≡ Jset (b α)` at every ordinal `α`, with `b α = ω·α`.
Counterexample at `α = 1`:

- `Lset 1 = 𝒟ₒ (Lset ∅) = Def ∅ = {∅}` (every definable subset of `∅` is `∅`).
- `Jset (b 1) = Sset ω = J₁ = V_ω` (the rud closure of `{∅}` is the hereditarily
  finite sets).

`{∅} ≠ V_ω`. The classical theorem is `J_α = L_{ω·α}`, i.e. the rud tower at
index `ω·α` matches the Def tower at index `ω·α`, **not** at index `α`.

### 2b. The corrected target, and why the block map is not what states it

Every limit ordinal is `ω·α` for some `α`, so the corrected statement is:

> **Matching:** for every limit `γ`, `Lset γ ≡ Jset γ limγ`.

This is the `Matching` type exported in the file. It needs no index translation
at all: the two towers are read at the **same** index, restricted to limits. The
block map `b` of `OrdBlocks` is therefore not consumed by the bridge as
delivered; what the endpoints consume from that chapter is `+ω`, `+ω-mem`,
`+ω-limit` (an arbitrary ordinal's `ω`-extension is a limit above it), three
lines' worth. `b` remains correct and is the right object if a later chapter
wants the matched limits enumerated by an ordinal index.

### 2c. Why the corrected target is walled

Both halves of an interleaving need **the levels of one tower as members of the
other**, and each of those is a definability statement about a *hierarchy*, not
about a step. Measured against the delivered surfaces:

- **Def → rud.** `Sat` (SatSets) is abstract in its carrier: it needs `U`
  transitive, the class rud-closed and transitive, and `U ∈ J`. Instantiating at
  `U = Lset β`, `J = Jset γ` gives `𝒟ₒ (Lset β) ⊆ Jset γ` **provided
  `Lset β ∈ Jset γ`** — this is `Ldef→J`, proved here, 15 lines. The hypothesis
  is not removable: relativizing a formula with parameters from `Lset β` to the
  rud closure needs `Lset β` as a parameter. At a *matched* limit it is free
  (`Lset μ = Jset μ ∈ Jset (sucV μ)`, the self arm); at the successor stages
  inside a block it asks for `Def(u) ∈ rud tower`, which the delivered one-step
  switch (`full-switch-⊇` lands in a limit level, `closure→definable-tower` is
  sharp at one block) does not give.
- **rud → Def.** The self arm of `step u` needs `Sset δ ∈ Lset γ`. For matched
  limit indices this is free (equality plus `Lset∈Lsuc`); for the intra-block
  indices it needs `step (Lset ζ) ∈ Lset (ζ+k)`, i.e. `values u` as an element,
  i.e. the **graphs** of the sixteen operations as formulas over an L stage
  (`∃ a,b ∈ u′. y = F_i(a,b)`), not their values at fixed arguments. `Describe`
  delivers the values; `Graphs` delivers the image principle for the *rud*
  closure, not for the Def tower.
- Both blockers reduce to the same missing chapter: **the uniform definability
  of one hierarchy inside the other**. Cost class: the `Graphs` element-relation
  induction (≈960 lines) re-run on the Def side, i.e. the same wall class the
  recon flagged for G2, arriving through G3/G4 instead.

A cofinality dodge fails at the base: a limit-of-limits `γ` can be handled from
matching below, but `γ = μ + ω` cannot, and the very first block (`L_ω = J_1 =
V_ω`) is exactly the case with no limits below it.

### 2d. What was built instead

`Bridged`, a module over `Matching`, with the endpoints proved in a few lines
each. Discharging one hypothesis delivers the whole class equivalence. This is
the honest packaging: the mathematics that is reachable is proved outright, and
the one unreachable fact is named, typed, and isolated.

## 3. Exports (types as proved)

```
𝒟ₒ⊆Lsuc  : (ξ x : S) → ⟨ x ∈ˢ 𝒟ₒ (Lset ξ) ⟩ → ⟨ x ∈ˢ Lset (sucV ξ) ⟩
Lset∈Lsuc : (ξ : S) → ⟨ Lset ξ ∈ˢ Lset (sucV ξ) ⟩
Ldef→J   : (β γ : S) (limγ : ⟨ isLimit γ ⟩) → ⟨ Lset β ∈ˢ Jset γ limγ ⟩
         → (x : S) → ⟨ x ∈ˢ 𝒟ₒ (Lset β) ⟩ → ⟨ x ∈ˢ Jset γ limγ ⟩
module Arms (C : S) (Ctr : Transitive 𝒮ᵥ (λ x → x ∈ˢ C))
  Arm     : S → Type _            -- sub → Σ Φ, defSet Φ ≡ W
  pairArm : (c d : S) → Arm (F0 c d)
  relArm  : (a : S) → ⟨ a ∈ˢ C ⟩ → ⟨ A ∈ˢ C ⟩ → Arm (F15A a)
  imgArm  : ⟨ A ∈ˢ C ⟩ → (i : Op16) (a b : S)
          → ⟨ a ∈ˢ C ⟩ → ⟨ b ∈ˢ C ⟩ → Arm (Fof i a b)
Ltr      : (ξ : S) → Transitive 𝒮ᵥ (λ x → x ∈ˢ Lset ξ)
Lval     : (ζ : S) → ⟨ A ∈ˢ Lset ζ ⟩ → (i : Op16) (a b : S)
         → ⟨ a ∈ˢ Lset ζ ⟩ → ⟨ b ∈ˢ Lset ζ ⟩
         → ((v : S) → ⟨ v ∈ˢ Fof i a b ⟩ → ⟨ v ∈ˢ Lset ζ ⟩)
         → ⟨ Fof i a b ∈ˢ Lset (sucV ζ) ⟩
Lpair    : (ζ p q : S) → ⟨ p ∈ˢ Lset ζ ⟩ → ⟨ q ∈ˢ Lset ζ ⟩
         → ⟨ F0 p q ∈ˢ Lset (sucV ζ) ⟩
Lstage   : (γ : S) → ⟨ isLimit γ ⟩ → (x : S) → ⟨ x ∈ˢ Lset γ ⟩
         → ∥ Σ[ ξ ∈ S ] (⟨ ξ ∈ˢ γ ⟩ × ⟨ x ∈ˢ Lset ξ ⟩) ∥₁
Lstage₂  : … → ∥ Σ[ ξ ∈ S ] (⟨ ξ ∈ˢ γ ⟩ × ⟨ x ∈ˢ Lset ξ ⟩ × ⟨ y ∈ˢ Lset ξ ⟩) ∥₁
Lpair-limit : (γ : S) → ⟨ isLimit γ ⟩ → (p q : S) → … → ⟨ F0 p q ∈ˢ Lset γ ⟩
Lpr-limit   : (γ : S) → ⟨ isLimit γ ⟩ → (p q : S) → … → ⟨ pr p q ∈ˢ Lset γ ⟩
Ljunk    : (ζ : S) → ⟨ A ∈ˢ Lset ζ ⟩ → (U : S) → ⟨ U ∈ˢ Lset ζ ⟩
         → (i : Op16) (a b : S)
         → (⟨ a ∈ˢ U ⟩ ⊎ (a ≡ U)) → (⟨ b ∈ˢ U ⟩ ⊎ (b ≡ U))
         → ((v : S) → ⟨ v ∈ˢ Fof i a b ⟩ → ⟨ v ∈ˢ Lset ζ ⟩)
         → ⟨ Fof i a b ∈ˢ Lset (sucV ζ) ⟩
ValuesIn : (μ : S) → ⟨ isLimit μ ⟩ → (ζ : S) → Type _
Lstep-absorb : (μ : S) (limμ : ⟨ isLimit μ ⟩) (ζ : S)
             → ⟨ A ∈ˢ Lset ζ ⟩ → ⟨ Jset μ limμ ∈ˢ Lset ζ ⟩ → ValuesIn μ limμ ζ
             → (x : S) → ⟨ x ∈ˢ step (Jset μ limμ) ⟩ → ⟨ x ∈ˢ Lset (sucV ζ) ⟩
matched-level∈L : (μ : S) (limμ : ⟨ isLimit μ ⟩) → Lset μ ≡ Jset μ limμ
                → ⟨ Jset μ limμ ∈ˢ Lset (sucV μ) ⟩
Matching : Type _   -- (γ : S) (limγ : ⟨ isLimit γ ⟩) → Lset γ ≡ Jset γ limγ
module Bridged (match : Matching)
  bridge-isL→isJ : (x : S) → ⟨ isL x ⟩ → ⟨ isJ x ⟩
  bridge-isJ→isL : (x : S) → ⟨ isJ x ⟩ → ⟨ isL x ⟩
  bridge-level   : (x : S) → ⟨ isL x ⟩
                 → ∥ Σ[ γ ∈ S ] (Σ[ lim ∈ ⟨ isLimit γ ⟩ ] ⟨ x ∈ˢ Jset γ lim ⟩) ∥₁
  level-bridge   : (γ : S) (lim : ⟨ isLimit γ ⟩) (x : S)
                 → ⟨ x ∈ˢ Jset γ lim ⟩ → ⟨ isL x ⟩
```

`bridge-level` is the corollary the choice re-home needs: a constructible set
lies in a limit `Jset` level, with the limit certificate in the witness.

## 4. Sizes and timings

| part | code lines | note |
|---|---|---|
| header and imports | 52 | |
| `𝒟ₒ⊆Lsuc`, `Lset∈Lsuc` | 6 | the true formula, once |
| `Ldef→J` (Def step → rud tower) | 15 | `Sat` at a non-level carrier |
| the sixteen arms (`Arms`) | 120 | G5 core |
| `Ltr`, `Lval`, `Lpair` | 28 | the offset |
| `Lstage`, `Lstage₂`, `Lpair-limit`, `Lpr-limit` | 49 | common stage, pairing inside a limit |
| `Ljunk` | 11 | junk = plain, once `U` is a member |
| `ValuesIn`, `Lstep-absorb`, `matched-level∈L` | 27 | the consumer |
| `Matching`, `Bridged` | 30 | endpoints |
| **total** | **338** | stop-line was 1,400 |

Check timings (cold, `-M12g`, one at a time): stage 1 (`Ldef→J`) 6.7 s; +16 arms
20.5 s; +offsets and pairing 38.6 s; +endpoints 39.7 s; final 40.8 s. No wall, no
heap event, no rerun needed. Three scope errors and one type error total across
the whole batch, each fixed in one edit.

## 5. Which mitigations carried weight

- **P-i [A] / R-37 (decisive).** Every membership hypothesis in every statement
  is a **variable** (`⟨ Lset β ∈ˢ Jset γ limγ ⟩`, `⟨ U ∈ˢ Lset ζ ⟩`), never a
  transported one, and every carrier in a module application is a *stuck* term
  (`Lset ζ` is sealed opaque upstream). Instantiating the 1,400-line `Sat` and
  the sixteen `Describe` modules at such carriers cost 6 s and 14 s
  respectively. This is the reason the file has no wall trail at all.
- **P-i [A] again, as a design choice.** The sixteen arms are stated at an
  **abstract** transitive carrier `C`, not at `Lset ζ`; the L-side instantiation
  is one line per consumer. Had the arms been written directly at `Lset ζ`, all
  sixteen goal types would have carried the tower.
- **D-10 (the batch's main product).** Pricing the truth first killed the
  recorded target in five minutes of arithmetic (`L_1 = {∅}` against
  `J_1 = V_ω`), and the same discipline then caught the *offset* error inside
  G5: `U ∈ Lset μ` is false by irreflexivity, so the honest offset is two stages,
  three for pair values. Both corrections are recorded beside the originals.
- **C-11.** `module Arms (C) (Ctr) where` with the body indented one level; the
  parameters survive past the first declaration.
- **C-12.** Every run at `GHCRTS=-M12g`, one at a time, only on `Bridge`.
- **R-36 shape (not needed).** No seal had to be opened: `𝒟ₒ-intro`/`𝒟ₒ-inv` and
  `Lset-in`/`Lset-out` were already the read lemmas this batch needed, which is
  the lesson paying off one chapter later.
- **R-27's predictor** was not exercised: the batch has **no** induction and no
  ordinal recursion, because the mutual induction turned out to be walled. That
  is itself the measurement: the reachable content of the bridge is
  induction-free.

## 6. Residues, exactly stated

1. **`ValuesIn` discharge** (mechanical, 150-250 lines): for each of the sixteen,
   the members of `Fof i a b` with `a, b ∈ U ∪ {U}` lie in `Lset (sucV μ)` (flat
   ops) or `Lset (sucV (sucV μ))` (pair-valued ops, via `Lpr-limit`). No new risk.
2. **`Lset β ∈ Jset γ`** for non-limit `β` inside a block (Def → rud): needs
   `Def(u) ∈ rud tower`, i.e. the element form of the switch.
3. **`Sset δ ∈ Lset γ`** for non-limit `δ` inside a block (rud → Def): needs the
   sixteen operation **graphs** as formulas over a Def stage, i.e. the `Graphs`
   construction re-run on the L side (≈1k lines, the G2 wall class).
4. Discharging (2) and (3) yields `Matching`, and `Bridged` then delivers
   `isL ↔ isJ` with no further work.
5. `src/Everything.lagda.md` does not yet import `L.Rud.Bridge` (this batch was
   forbidden to touch it); `make check` does not cover the new file until it does.

## 7. Lesson candidates (measured)

- **D-10 extension, second instance in two days.** "Price the truth of a recorded
  residue" now has a second measured case, and a sharper form: *price the truth
  of the recorded target's index translation too*. The r5recon's
  `Lset α ≡ Jset (b α)` is false at `α = 1` by a one-line arithmetic check
  (`{∅}` vs `V_ω`), while the corrected statement (`Lset γ ≡ Jset γ` at limits)
  needs no translation at all and made a 100-180 line chapter (`OrdBlocks`'s `b`)
  unnecessary for the bridge. Cost of the check: five minutes. Cost of not
  checking: an induction on a false statement.
- **New (D-series candidate): a self-containing operator's junk is junk only
  relative to the tower reading it.** The rud step's junk (values with the level
  in an argument slot) is irreducible against the *rud* level, which cannot
  contain itself, and evaporates against the *Def* tower the moment a stage holds
  the level as a member: `Ljunk` is 11 lines and its whole content is a two-case
  split feeding `Lval`. Measurement: `LevelDesc` spends ~700 lines on the level
  cases of the same sixteen operations; here they cost nothing, because the
  carrier changed. Sibling of D-9 (choose the carrier by which operations act
  homomorphically): choose the carrier by *what it can contain*.
- **P-i [A] as a prophylactic, second datum after R5a's.** Sixteen heavy
  description modules and one 1,400-line satisfaction module, all instantiated at
  abstract or opaque carriers, checked in 40 s total with zero walls. The rule
  "heavy values never sit in conversion positions; state at abstract carriers and
  bridge by one `subst`" now has a case where it was applied before any wall and
  the wall never came.

---

# Part M: discharging `Matching` (appended)

Same file, appended: **555 code lines total** (part 1 was 338, so **+217**, against a
+900 stop-line), 836 file lines, green at **43.9 s cold** (`-M12g`), all four
linters clean. No other file touched.

**Result: `Matching` is not discharged, but it is reduced — with the whole
induction done — to three named hypotheses, two of which are the campaign's real
residue and one of which is mechanical.** The separation route was tried first as
mandated and died on a measured, exactly-located gap, described below.

## M1. The separation route, priced (D-10 first, no Agda spent)

The route asks for `Def C` extensionally as a Δ₀ separation `{y ∈ F : y ⊆ C}`
from a J-fragment `F`. Such an `F` must satisfy **both**:

- (i) `Def C ⊆ F`. Delivered only by `full-switch-⊇`, which places a `defSet` in
  a **limit** level `Jset α` with `μ ∈ α`: it spends the whole ω-block, because a
  formula's realization is an arbitrarily deep rud composite. So (i) forces
  `F ⊇ Sset (μ + ω)`.
- (ii) `F ∩ P(C) ⊆ Def C`. Delivered only by `closure→definable-tower`, whose
  bound is "every index below the stage is below `μ` or is `μ`", i.e. **one** rud
  step: `F ⊆ Sset (sucV μ)`.

The two admissible ranges are **disjoint** (`μ+1` against `μ+ω`), so no delivered
`F` witnesses the separation. Closing the gap means extending (ii) from one step
to a whole block: `Sset (μ+ω) ∩ P(Sset μ) ⊆ Def (Sset μ)`, the classical
"rud closure of `U ∪ {U}` meets `P(U)` in `Def U`". That is the Σ_ω-over-`U`
content, proved classically by induction over **rud terms**, i.e. the same
construction class as the graphs, relocated. The route therefore does not dodge
the wall; it renames it.

Worth recording precisely, because the delivered chapter's own prose invites the
confusion: LevelDesc's sharpness note ("two blocks up the statement is false, by
Tarski") is about **blocks**, while its delivered bound is **one step**. The
truth is between them: the whole next block is correct, and only from two blocks
up does Tarski bite. So (ii)'s missing extension is *true*, just unproved.

The mirror bullet (the rud step as a definable **set** over an L stage) is the
same shape from the other side: `step C = C ∪ {C} ∪ {F_i(a,b) : a,b ∈ C ∪ {C}}`,
and the third disjunct needs the **graphs** `y = F_i(a,b)` with `a,b` quantified.
Part 1 delivers the sixteen descriptions at *fixed* arguments, which is what
`Ljunk` consumes; the quantified form is a different object.

## M2. What was built instead: the reduction

`module Reduce`, a joint induction along the membership relation. At each ordinal
index it carries three statements:

1. `Lset β ∈ˢ Sset γ` for every limit `γ ∋ β`;
2. `Lset β ≡ Sset β` when `β` is a limit (this **is** `Matching` at `β`);
3. `Sset β ⊆ Lset γ` **and** `Sset β ∈ˢ Lset γ` for every limit `γ ∋ β`.

Clause 2 uses only the induction hypothesis, so clauses 1 and 3 may use it at
their own index; there is no circularity and the dependency was checked before
writing. The case analysis is the plain ordinal split (`ord-case`: zero,
successor, limit) at every clause. **No ordinal arithmetic enters**: no block
map, no "every limit is a limit of limits or an ω-extension" dichotomy (which
would itself have been 150-250 lines of missing division-by-ω), no `sucIter`
induction. This is the structural payoff of the corrected target from part 1
(`Lset γ ≡ Jset γ` at limits, same index): the block map's absence is what makes
the induction one clean ∈-recursion.

Hypotheses, and what each is:

| hypothesis | statement | status |
|---|---|---|
| `defStage∈J` | `Lset ζ ∈ Sset γ → Lset (sucV ζ) ∈ Sset γ` (`γ` limit, `ζ ∈ γ`) | **residue**: needs (ii)'s block extension (M1) |
| `stepSet∈L` | `u ∈ Lset ζ`, `step u ⊆ Lset ζ` ⟹ `step u ∈ Lset (sucV ζ)` | **residue**: needs the sixteen graphs |
| `values∈L` | `u ∈ Lset ζ` ⟹ members of every `Fof i a b` with `a,b ∈ u ∪ {u}` lie in `Lset (suc⁴ ζ)` | mechanical: the sixteen reads (part 1's `ValuesIn`, folded in here with its offset fixed) |
| `slot∈L` | `A ∈ Lset γ` at limits | immediate for the trunk (`A = ∅`) |

Given them, `matching : Matching` and `open Bridged matching public` re-export
the endpoints **unconditionally inside `Reduce`**: `bridge-isL→isJ`,
`bridge-isJ→isL`, `bridge-level`, `level-bridge`.

## M3. `ValuesIn`'s record: the offset is four, not two

Folding the residue in immediately corrected it. The first formulation asked for
the values' members two stages above `ζ`; that is **not dischargeable**, and a
non-dischargeable hypothesis would have made the whole reduction vacuous. Counted
per operation, with `a, b ∈ u ∪ {u} ⊆ Lset ζ`:

| operation | value's members | stages needed |
|---|---|---|
| `F1`, `F5`, `F6`, `F15`, member/self arms | already in `Lset ζ` by transitivity | 0 |
| `F0` | `a`, `b` | 0 |
| `F9`, `F8`, `F10` | `⁅a⁆s`, `⁅a,b⁆`; image values via part 1's own `Lval` at `op10` | 1 |
| `F2`, `F7` | Kuratowski pairs `pr p q` of members | 2 |
| `F11`-`F14` | `⁅left y⁆s`, `⁅left y , pr x (right y)⁆` | 3 |
| `F3`, `F4` | `pr u (pr z w)`, two **nested** pairs | **4** |

So the honest uniform offset is four, and the module now states it that way. Each
pair costs two stages (`⁅p⁆s` and `⁅p,q⁆` at one, the outer `F0` at the next),
which is `Lpair` from part 1; part 1's claim of "three" was counted for a single
pair and is corrected here for the nested case.

## M4. Sizes, timings, and one measured performance datum

| part | code lines |
|---|---|
| `ext-⊆`, `empty-⊆`, `Lset-zero`, `Sset-zero`, `∅∈Sset`, `∅∈Lset` | 26 |
| `ValuesInU`, `Lstep⊆` (absorption at an arbitrary set) | 24 |
| `suc⁴` seal and its two read lemmas | 18 |
| `module Reduce` (the joint induction) | 149 |
| **part M total** | **217** |

Check times, cold, one at a time: reduction first try **44.2 s** (green on the
first compile, no wall, no error); after widening the values offset to four
stages **90.1 s**; after sealing the successor tower **43.9 s**.

**That middle number is the datum.** Exposing four `Lset ∘ sucV` layers in a
*hypothesis type* doubled the whole file's check (44 s → 90 s, +45 s for four
layers); one `opaque suc⁴` alias with two `opaque unfolding` read lemmas (R-36
shape, 18 lines) took it back to baseline. This is P-i's layer-cap sub-rule
("costs multiply per exposed layer") measured on this codebase for the first
time, and the first instance where the layers were in a **hypothesis type**
rather than in a term.

## M5. Final state of the campaign's last gap

Two lemmas remain, both element-statements, both about a *hierarchy* rather than
a step:

1. `defStage∈J` ⟸ `Sset (μ+ω) ∩ P(Sset μ) ⊆ Def (Sset μ)` (the block extension of
   `closure→definable`; rud-term induction).
2. `stepSet∈L` ⟸ the sixteen graphs `y = F_i(a,b)` as Δ₀ formulas over a
   transitive carrier (the `Graphs` construction on the Def side).

plus `values∈L` (mechanical, ~150-250 lines, engine already delivered: `Lpair`,
`Lpr-limit`, and part 1's arms) and `slot∈L` (immediate at `A = ∅`).

Against the "~1k lines, re-run Graphs" estimate from part 1: the reduction shows
that **only one of the two directions actually needs graph-shaped work**
(`stepSet∈L`), and the other needs a term induction inside the *delivered* switch
machinery (`defStage∈J`), which is a different and probably cheaper object than a
Graphs re-run. Everything else that stood between the delivered pillars and
`isL ↔ isJ` is now proved.

## M6. Lessons (measured, part M)

- **P-i layer cap, first hypothesis-type instance.** 44 s → 90 s → 44 s across
  four exposed `Lset ∘ sucV` layers and one 18-line seal. Extends P-i [B]'s layer
  cap with a new trigger: the layers need not be in a term, a *hypothesis type in
  a module telescope* is enough, and the cost is paid by every clause that
  mentions the module.
- **A hypothesis must be priced for dischargeability, not just for truth.**
  The two-stage `values∈L` was true-looking, provable-looking, and
  **underspecified**: `F3`/`F4` nest two pairs. A reduction to hypotheses is only
  as honest as the weakest hypothesis's dischargeability, so each one gets the
  same D-10 treatment as a target. (Candidate D-series entry; sibling of D-10.)
- **Reformulating the target can delete a chapter.** Part 1's correction
  (`Lset γ ≡ Jset γ` at limits, same index, instead of `Lset α ≡ Jset (b α)`) is
  what let part M's induction avoid ordinal division by ω entirely. Measured: the
  induction is 149 lines and mentions no arithmetic; the block-indexed version
  would have needed the missing dichotomy (150-250 lines) before it could even be
  stated.
- **Mandated-first-formulation paid negatively, and that is a result.** The
  separation route cost zero Agda: the two delivered directions' index ranges
  were read off their statements and found disjoint. Recording *why* a proposed
  route cannot close is cheaper than trying it, when the obstruction is an index
  arithmetic mismatch rather than a formulation problem.
