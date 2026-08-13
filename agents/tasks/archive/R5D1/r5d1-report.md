# R5-D1: `defStage∈J`, the first genuine residue of the bridge

Target (verbatim from `src/L/Rud/Bridge.lagda.md:687-690`, `module Reduce`'s first
hypothesis, unchanged by the concurrent R5-D2 edit of that telescope):

```
defStage∈J : (ζ γ : S) → (limγ : ⟨ isLimit γ ⟩) → ⟨ ζ ∈ˢ γ ⟩
           → ⟨ Lset ζ ∈ˢ Sset γ ⟩ → ⟨ Lset (sucV ζ) ∈ˢ Sset γ ⟩
```

One new file, `src/L/Rud/DefInJ.lagda.md`, **231 code lines**, 388 file lines,
green at **8.4 s cold** (`GHCRTS=-M12g`), all four linters clean. No other file
touched, no commit, `Everything` untouched.

**Result: `defStage∈J` is exported at Reduce's exact type over one named
hypothesis (`DefFragment`), and the whole chain around that hypothesis is
proved.** The hypothesis is not discharged, and section 1 says exactly why, with
two corrections to the recorded reduction that were found by the mandated D-10
pricing before any Agda was spent.

The export was verified by the decisive probe rather than by reading: a
scratchpad module applies `Bridge.Reduce` to it,

```
module R = Reduce defStage∈J stepSet∈L values∈L slot∈L
matched : Matching
matched = R.matching
```

with the other three hypotheses as module parameters. It typechecks (1.7 s), so
the export is accepted where it is meant to be consumed. (The probe also caught
that `Reduce`'s `stepSet∈L` had gained an `⟨ A ∈ˢ Lset ζ ⟩` argument in commit
`f3ad704` while this batch was reading; `defStage∈J`'s type is unchanged.)

---

## 1. D-10 first: the identity, its truth, and the offset

### 1.1 The set-level identity, as written down before building

Write `C = Lset ζ`. Three set-level equalities carry the whole statement:

1. **The successor collapse.** `Lset (sucV ζ) ≡ 𝒟ₒ C`: one Def step up *is* the
   set of all definable subsets of `C`. (`⊇` is `Lset-in` at `self∈sucV`; `⊆`
   splits `δ ∈ sucV ζ` and absorbs the strict case through `Lset-in` and
   `Lset⊆𝒟ₒ`.) So the target is exactly **`𝒟ₒ C ∈ˢ Sset γ`**: the SET of
   definable subsets is a rud member.
2. **The fragment identity.** `𝒟ₒ C ≡ { y ∈ F : y ⊆ C }` for a set `F` with
   (i) `𝒟ₒ C ⊆ F` and (ii) `F ∩ P(C) ⊆ 𝒟ₒ C`. One side of the separation is
   free (`𝒟ₒ∋⊆`: a definable subset is a subset).
3. **The separation is a `defSet`.** With `W = Sset δ` for a stage `δ ∈ γ`
   holding `C` and `F` as members, `{ y ∈ F : y ⊆ C }` is `DefOf.defSet W Φ` for
   `Φ = (var zero ∈̇ con F) ∧̇ ∀̇∈ (var zero) (var zero ∈̇ con C)`,
   and `Sat` (SatSets, at carrier `W`, class `∈ˢ Sset γ`, closure
   `Jset-rud γ limγ`) puts every `defSet` of the carrier into `Sset γ`. The
   bounded quantifier is complete because `F ∈ W` and `W` is transitive.

**Checked: the identity is true.** All three are proved in the file; 1 and 3
outright, 2 as the equality driving the final `subst`.

### 1.2 The offset the hypothesis states is right

`γ` is a limit and `ζ ∈ γ`, so `ζ+1 ∈ γ` and `L_{ζ+1} ∈ L_{ζ+2} ⊆ L_γ = J_γ`.
The conclusion needs no block, no successor, and no second limit: the
hypothesis's shape (same `γ`, same limit certificate) is **correct as recorded**,
and a wrong-offset hypothesis would have poisoned the reduction. This was the
first thing checked and it cost ten minutes.

### 1.3 Two corrections to the recorded route (both new)

The g3g4g5 report, M5.1, records:

> `defStage∈J` ⟸ `Sset (μ+ω) ∩ P(Sset μ) ⊆ Def (Sset μ)` (the block extension of
> `closure→definable`; rud-term induction).

That implication does not hold, for two independent reasons.

**(a) The carrier is an L stage, not a J level.** `defStage∈J` asks for the
definable power of `C = Lset ζ`, an arbitrary constructible stage that the rud
tower happens to hold as a member. The recorded lemma is stated at `C = Sset μ`,
a level. The member form is not an instance of the level form: the fragment
around a *member* is a strictly smaller object than the next level, and the
delivered `closure→definable` (one rud step over a level) does not see it.

**(b) The block route has no room at the top block, and none at all at `ω`.**
Suppose (a) repaired and the witness taken to be `F = Sset (δ +ω)`, the ω-block
above `C`'s entry stage `δ ∈ γ` (which is what half (i) needs if it is to come
from the delivered whole-block switch, M1(i): a formula's realization is an
arbitrarily deep rud composite, so (i) spends the whole block). Then
`F ∈ˢ Sset γ` demands `δ +ω ∈ γ`. That fails for a cofinal class of the limits
the hypothesis quantifies over:

- `γ = ω`: there is no limit below `ω` at all, and the instance is real
  (`Lset ∅ ≡ ∅ ∈ˢ Sset ω`, so the antecedent is satisfiable and
  `𝒟ₒ ∅ = {∅} ∈ Sset ω` is a genuine obligation).
- `γ = ω·(β+1)`, any `β`: a stage `C = Lset ζ` with `ζ` inside the last block
  first enters at some `δ ∈ [ω·β, ω·(β+1))`, and `δ +ω = γ ∉ γ`.

So a block-offset lemma reaches only the `γ` that are limits of limits, while
`Reduce`'s consumer (`Bridge:748-755`) calls `defStage∈J` at an arbitrary limit.

**(c) The generalization of (b): no rud-closed fragment exists at `ω`.** The
failure is not an artefact of the block indexing. Any route that asks the
bounding fragment `F` to be closed under the sixteen operations dies at `γ = ω`:
a rud-closed nonempty `F` contains `F0 a a = {a}` for each of its members, hence
an infinite rank-increasing chain, hence is infinite; but every member of
`Sset ω` lies in some `S_n`, and every `S_n` is finite (`S_0 = ∅`, and
`step u = u ∪ {u} ∪ {F_i(a,b)}` is finite for finite `u`). So `Sset ω` contains
no rud-closed set at all, and the base block's instance of `defStage∈J`
(`P(L_n) ∈ HF`) has to be discharged by hereditary finiteness, not by a closure
fragment. **This is why the batch did not build the `rudCl` (ω-iterated `step`)
layer**: it would have been about 150 lines whose only product is a residue
refutable at the first limit.

**What the honest witness is.** Above the base block the classical witness is
`F = rud(C ∪ {C})` sitting at a **finite** rud offset above `C`'s entry stage,
which is the rudimentary-satisfaction theorem (formula codes internal, the Σ₀
satisfaction relation of a transitive set rudimentary in it), not the block
extension of `closure→definable`. The delivered `SatSets` realizes the
satisfaction set of one **external** formula at a time (`T n φ`), whose rud depth
grows with `φ`. Collecting that family is where internal syntax enters, and no
image or separation of the delivered `T`-sets can do it: `Def C` is a `sett` over
the external type `Formula ⟪ C ⟫ 1` (`L.Definability:114`), while
`F8 (T (suc n) φ) (Us n)` collects the **parameters** of one fixed `φ` (one rud
value, in the closure) and never the formulas. The brief's expectation that
SatSets already has "the satisfaction relation at each arity as one set" is the
one premise that does not hold as delivered.

---

## 2. What is proved (`src/L/Rud/DefInJ.lagda.md`)

| export | statement |
|---|---|
| `ext-⊆` | extensionality from two inclusions (local, as in Bridge) |
| `Lsuc≡Def` | `Lset (sucV ζ) ≡ 𝒟ₒ (Lset ζ)`, the successor collapse |
| `Sstage` | a member of a limit rud level lies in a level strictly below |
| `Sstage₂` | two members lie in one common level strictly below |
| `module Sep` | at `W = Sset δ`, `δ ∈ γ`, with `C F ∈ W`: the Δ₀ separation `sep`, its membership `sep∈J : ⟨ sep ∈ˢ Sset γ ⟩`, and its two reads `sep-write` / `sep-read` |
| `defs-in-limit` | `Lset ζ ∈ˢ Sset μ` (μ limit) ⟹ every definable subset of `Lset ζ` is in `Sset μ` (the engine at a fragment, half (i) where a limit is available) |
| `DefFragment` | the residue: a bounding fragment `F ∈ˢ Sset γ` with `𝒟ₒ (Lset ζ) ⊆ F` and `F ∩ P(Lset ζ) ⊆ 𝒟ₒ (Lset ζ)` |
| `LimitFragment`, `fragment-from-limit` | the sharpened (sufficient, not necessary) form: a limit level `μ ∈ γ` holding the carrier, at which half (i) is free and only the block statement remains |
| `Discharge.defStage∈J` | the target, at Reduce's exact type, over `DefFragment` |

**Honesty note, recorded in the file's prose too.** `DefFragment` is
*equivalent* to the target (take `F = 𝒟ₒ C`), not weaker. Its content is that
the residue may be discharged by an approximation loose in both directions,
which is how the classical argument proceeds; the chain around it (collapse,
common stage, separation, engine) is what this batch removes from the residue's
price. `LimitFragment` is a genuine strengthening, and by 1.3(b) it is refutable
at `γ = ω`; it is kept because it is the recorded route, now typed, with its
room condition visible in its own statement.

## 3. Price table

| part | code lines |
|---|---|
| header and imports | 36 |
| `ext-⊆`, `Lsuc≡Def` (successor collapse) | 18 |
| `Sstage`, `Sstage₂` (stage bounding, trichotomy) | 31 |
| `module Sep` (separation, engine instantiation, two reads) | 71 |
| `defs-in-limit` (the engine at a fragment) | 14 |
| `DefFragment`, `LimitFragment`, `fragment-from-limit`, `Discharge` | 61 |
| **total** | **231** |

Stop-line was 1,200 with a pause gate at 700; neither was approached, because
the family-collection half is not a coding problem but the missing chapter of
1.3.

## 4. Timings

| run | time |
|---|---|
| first compile of the file (green, no error) | 8.1 s |
| cold recheck (interface deleted) | 8.6 s |
| after the two prose corrections | 8.4 s |
| the `Reduce` probe (scratchpad, imports Bridge) | 1.7 s |

No wall, no heap event, no rerun. Errors across the whole batch: one lint
violation (an unused `∣_∣₁`), one parse error and two scope/type errors **in the
probe** (the probe's own copy of a sibling hypothesis type, which is how the
`f3ad704` telescope change was detected). The Agda file itself compiled green on
the first attempt.

## 5. Which mitigations carried weight

- **P-i [A], decisive again.** Every carrier fed to `Sat` is a stuck term
  (`Sset δ`, `Lset ζ`, both sealed upstream) and every membership hypothesis is
  a variable. Instantiating the 1,677-line satisfaction engine twice cost
  nothing measurable: the whole file is 8.4 s.
- **P-i [B] layer cap, watched not spent.** `Lset (sucV ζ)` appears in exactly
  two positions (the collapse's statement and the final `subst`), one exposed
  layer, so no `opaque` alias was needed. The M4 datum (four layers doubling a
  check) predicts the cap only above one layer, and that held.
- **C-11.** `module Sep (…) where` with the body indented one level; eight
  parameters survive past the first declaration.
- **C-12.** Every run at `GHCRTS=-M12g`, one at a time, only on this file (the
  probe run also single).
- **D-10, the batch's main product.** Pricing the truth first (ten minutes of
  ordinal arithmetic) confirmed the offset and killed the recorded route twice,
  which is what stopped this batch from spending 150 lines on a `rudCl` layer
  whose residue is refutable at the first limit.
- **R-35 avoided by not entering it.** The `rudCl` design would have needed a
  union representation over `ℕ` with fiber extraction, exactly the shape R-35
  warns about; the D-10 finding removed the need before the risk was taken.
- **C-8 (false greens).** The file compiled green on the first attempt, which is
  the classic false-green shape, so the export was checked by applying
  `Bridge.Reduce` to it rather than by reading the type.

## 6. Residue, exactly stated

One hypothesis, `DefFragment`, and per 1.3 it splits by block:

1. **Base block (`γ = ω`).** `𝒟ₒ (Lset ζ) ∈ Sset ω` for `Lset ζ ∈ Sset ω`, i.e.
   `P(x) ∈ HF` for `x ∈ HF`. No fragment route reaches it (1.3c); it needs the
   hereditary finiteness of `Sset ω` (every member lies in a finite `S_n`, and a
   finite set of members of `Sset ω` is a member). Estimated a chapter of its
   own, and it is a **new** residue: the campaign has not recorded it before.
2. **Above the base block.** `F = rud(C ∪ {C})` at a finite rud offset above
   `C`'s entry stage. Two facts: the fragment is a **member** of the tower (the
   rudimentary-satisfaction theorem, internal formula codes), and
   `F ∩ P(C) ⊆ Def C` (the block extension of `closure→definable`, the rud-term
   induction M1 already named). The recorded residue covers only the second.
3. `src/Everything.lagda.md` does not import `L.Rud.DefInJ` (this batch was
   forbidden to touch it); `make check` does not cover the new file until it
   does.

## 7. Lesson candidates (measured)

- **D-10 extension: price the residue's WITNESS, not only its statement.** The
  recorded reduction named a true lemma (the block extension) that does not
  imply the target, because the object it produces is not a member of the level
  the target is stated at. Both failures (carrier is a member not a level; the
  block has no room at the top block, none at `ω`) are visible from the types
  plus ten minutes of ordinal arithmetic, and both were invisible in the
  statement of the residue itself. Sibling of M6's "a hypothesis must be priced
  for dischargeability", one level up: *price the hypothesis's intended witness
  for existence at the target index.*
- **New (D-series candidate): a closure fragment cannot live inside the block it
  closes.** Any bounding object asked to be closed under the sixteen operations
  is infinite (singletons), so it is never a member of the first rud level
  `Sset ω`, whose members are all finite. Consequence for the campaign: the
  base block of every rud-versus-Def statement is a **separate theorem** with a
  finiteness proof, and no amount of offset engineering merges it with the
  general case. Measured negatively: it removed a 150-line planned layer.
- **The equivalence test for a reduction.** Before reporting a residue as a
  reduction, check whether the residue implies the target *and* the target
  implies the residue. `DefFragment` fails the test (it is equivalent), and
  saying so is what keeps the reduction honest: the batch's product is the chain
  around the hypothesis, not a weakening of it. Cheap test, one line of
  reasoning, and it changed how this report states its own result.
- **The probe as the type check.** A scratchpad module that applies the
  consuming module (`Bridge.Reduce`) to the new export is 25 lines, runs in
  1.7 s off the existing interfaces (an `.agda-lib`-free invocation with three
  explicit `-i` roots), and catches exactly the class of drift a same-wave
  sibling can cause: it detected `f3ad704`'s telescope change to a *neighbouring*
  hypothesis mid-batch. Recommended as the standing close-out step for any batch
  that exports into a fixed telescope.
