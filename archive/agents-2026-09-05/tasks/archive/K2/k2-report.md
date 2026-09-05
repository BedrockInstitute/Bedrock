# R5-K2: the code set chapter (`src/L/Rud/CodeSet.lagda.md`)

The internal-codes route's first pillar: the codes of the formulas over a carrier, gathered as ONE
set, and its relation to the rud tower. Reads done in the mandated order (kernel-recon §1 and §4,
`FOL/Coding` and `V/Coding` in full, the retiring `L/Coding/CodeSet` for shape only, `Step` and the
`Graphs`/`SatSets` surfaces the closure machinery exposes, `DefInJ` as the consumer, and the LESSONS
entries R-35/R-36/R-37/R-38, I-2/I-3/I-4, P-c/P-h/P-i, C-11/C-12, D-7 to D-10 plus the r5d2
inner-world headline). Two files touched, both mine: `src/L/Rud/CodeSet.lagda.md` (new) and this
report. `Everything` untouched, no commits, siblings (`BaseBlock`, `StepInL`) neither read for code
nor imported.

**Headline.** The chapter goes green (193 code lines, 18.2 s, one syntax error and no walls), and it
goes green on **half** the recorded target. The half that is provable is proved; the half that was
recorded, "the code set is a member of the tower at a finite offset", is **false**, and the D-10
check that killed it is the arithmetic the batch was told to do first. The member form survives only
at a limit level and only as a satisfaction obligation, which is re-priced below at 3-4x the recon's
figure. The fork's commit signal does not fire as designed.

---

## 1. D-10 first: the target, its offset, and the offset's truth

**The set built.** Over a carrier `C` that is a member of a level of the S-tower, with
`ι = ⟪ C ⟫↪` the presentation of `C` by its own members:

```agda
code     : ∀ {n} → Formula ⟪ C ⟫ n → S        -- code φ = VCode.⌜ mapFo ι φ ⌝
codeSet  : ℕ → S                              -- sett (Formula ⟪ C ⟫ k) code
allCodes : S                                  -- sett (Σ[ k ∈ ℕ ] Formula ⟪ C ⟫ k) (code ∘ snd)
```

`codeSet 1` is what the fragment needs (`Def A = sett (Formula ⟪A⟫ 1) defSet` indexes by exactly
that class); `allCodes` is what a recursion over subcodes needs, since a quantifier's subformula
lives one arity up. This is the retiring `L/Coding/CodeSet`'s pair of sets (`Codes`/`AllCodes`)
ported in **shape only**: nothing is imported from the L-side tree, and the construction is a
small-indexed `sett` over the external `Formula` type rather than a separation out of `smallDom`,
because the rud side has no separation to spend.

**The intended offset, counted per constructor.** A code is an iterated Kuratowski pair of numerals
and members of `C`:

| code | shape | pair layers added |
|---|---|---|
| `⌜ con x ⌝ᵗ` | `pr (# 0) x` | 1 |
| `⌜ var i ⌝ᵗ` | `pr (# 1) (# (toℕ i))` | 1 |
| `⌜ t ∈̇ u ⌝`, `⌜ t ≐ u ⌝` | `pr (# k) (pr ⌜t⌝ᵗ ⌜u⌝ᵗ)` | 2 over the term codes (3 total) |
| `⌜ φ ∧̇ ψ ⌝`, `∨̇`, `⇒̇` | `pr (# k) (pr ⌜φ⌝ ⌜ψ⌝)` | +2 |
| `⌜ ¬̇ φ ⌝`, `⌜ ∃̇ φ ⌝`, `⌜ ∀̇ φ ⌝` | `pr (# k) ⌜φ⌝` | +1 |
| `⌜ ∀̇∈ t φ ⌝`, `⌜ ∃̇∈ t φ ⌝` | `pr (# k) (pr ⌜t⌝ᵗ ⌜φ⌝)` | +2 |
| `⌜ ⊤̇ ⌝`, `⌜ ⊥̇ ⌝` | `pr (# k) (# 0)` | 1 |

Against the step's arms: one Kuratowski pair is exactly one step (`Fof f9 a b = F9 a b = pr a b`
through `step-in-img` at `a, b ∈ u ∪ {u}`), the same unit the part-M/`values∈L` audit measured on
the Def side (r5d2 §1: `F9` one stage, `F2`/`F7` two, `F3`/`F4`/`F11`/`F12` four, one stage per pair
layer with four as the per-arm ceiling). A numeral costs three arms per unit
(`sucV x = F5 (F0 x (F0 x x)) x`, verified and proved here as `sucV-rud`), and `∅ = F1 a a` costs
one (`empty-rud`). So per code:

> `⌜ φ ⌝` enters at offset `O(size φ)` above the carrier's stage, `c ≤ 3` per node.

**The offset's truth, checked before writing code. The recorded target is false.**

1. `Sset α` is transitive at every index (`Sset-trans`). So `codeSet ∈ Sset (δ+n)` forces
   `codeSet ⊆ Sset (δ+n)`: **every** code would have entered by that stage.
2. The table gives codes of unbounded pair depth (`⌜ ¬̇ⁿ ⊤̇ ⌝` adds one layer per `¬̇`), and one
   pair layer adds two to the rank (`pr a b = ⁅ ⁅a⁆s , ⁅a,b⁆ ⁆`), so
   `rank ⌜ ¬̇ⁿ ⊤̇ ⌝ = rank ⌜ ⊤̇ ⌝ + 2n`.
3. One step raises rank by a bounded amount: the highest-rank member of `step u` is
   `F9 u u = pr u u` at rank `rank u + 2`, so `rank (Sset (δ+n)) ≤ rank (Sset δ) + 3n`.

No finite `n` holds the family: the codes are **cofinal in `δ + ω`**. The corrected target is two
statements, and only the first is an arm obligation:

- **(K-a) the containment half, unconditional.** `codeSet k ⊆ Sset γ` for **any** limit `γ` with
  `C ∈ Sset γ`; no room condition beyond that (the closure is applied inside the level and never
  climbs, so r5d1 §1.3b's `δ+ω ∈ γ` block condition does **not** appear here). **Proved.**
- **(K-b) the member half.** Membership in a limit level still factors through one arm at one stage
  (`Sset-out`), so it asks for a **rud value equal to the code set**. The only delivered machine
  that manufactures such a value from a description is the satisfaction engine (`Sat.defSet-InJ`).
  So (K-b) reduces, with no loss, to **the code predicate as one formula over a level** plus both
  directions of its adequacy. **Reduced, not built.**

This is D-10's own shape, second instance after r5b: the recorded residue named a target, the target
as recorded is false at the intended generality (here by a rank/cofinality obstruction rather than a
Tarskian one), and the corrected target was provable the same day.

---

## 2. The construction's shape

Module telescope `L.Rud.CodeSet {ℓ} (lem : LEM (ℓ-suc ℓ)) (A : V ℓ)`, matching `Step`/`DefInJ`, with
three inner modules and three top-level equations.

1. **`module Codes (C : S)`.** `codeTm`/`code` (the delivered coding after `mapFo ι`), the two
   classes `IsCodeAt k` / `IsCodeAny` as hProps, and the two sets sealed in one `opaque` block with
   their in/out lemmas inside (P-c/P-i [B]: the heavy thing is the SET, so the set is sealed, not a
   bridge). Membership in a `sett` is definitionally the truncated fiber, so `code∈codeSet` is
   `∣ φ , refl ∣₁` and `codeSet-out` is the identity: **R-35 discipline pays for itself here.** The
   `-in` directions and the `-spec` equations (`⇔toPath`) sit outside the seal, R-36 shape.
2. **The decode.** `codeSet-decode : ⟨ x ∈ˢ codeSet k ⟩ → Σ[ χ ∈ Formula S k ] (VCode.⌜ χ ⌝ ≡ x)`,
   **untruncated**, because at a fixed arity the pair is a proposition by `VCode.⌜⌝-inj` plus
   `isSetS` (`Σ≡Prop`, five lines). This is the second consumer of the recon's "one consumer wants
   the equation" investment, and it is what makes the code set adequate in the strong sense: a
   member IS a code, and the formula it codes is unique over the hierarchy. It stays truncated over
   `⟪ C ⟫` (the presentation is not injective) and must stay truncated over `allCodes` (a code does
   not carry its arity; a variable-free formula has the same code at every arity), both recorded in
   the prose.
3. **`module InLevel (γ) (limγ)`.** The level arithmetic a code needs, all through the sealed `Fof`
   family and never through an operation's body: `pr∈J` (f9), `∅∈J` (f1 plus `empty-rud`), `sucV∈J`
   (f5 ∘ f0 ∘ f0 plus `sucV-rud`, reusing `Step`'s `singl≡pair`), `numeral∈J` by induction.
4. **`module Carrier (γ) (limγ) (C) (C∈)`.** `member∈J` (level transitivity), `mkTag∈J` (one lemma
   for all twelve tags), `codeTm∈J` (2 clauses), `code∈J` (12 clauses, one per code function clause),
   and the containment halves `codeSet⊆J` / `allCodes⊆J`.
5. **The residue.** `defSet∈J` instantiates `Sat` at `U = Sset δ`, `InJ = (· ∈ˢ Sset γ)` exactly as
   `DefInJ.Sep` does; `Description y` is the truncated "some formula over some level below defines
   `y`"; `described∈J` discharges membership from it; `description-write` is the loose entry point
   (two containments at a variable member instead of an equation between sets, the same shape as
   `DefFragment`); `codeSet∈J` and `allCodes∈J` are the two instances.

No LEM is spent inside the chapter (`lem` only instantiates the imported modules). No new opaque
surface beyond the two sets. No `Graphs` import was needed: the code set is not an image.

---

## 3. Price table against the 250-450 calibration

| part | code lines | note |
|---|---|---|
| header and imports | 28 | |
| `Codes`: coding, the two classes, the two sealed sets, in/out/spec both ways | 45 | R-35 small-indexed |
| the untruncated decode (`⌜⌝-inj` + `Σ≡Prop`) | 9 | |
| level arithmetic (`empty-rud`, `singleton-rud`, `sucV-rud`, `ext-⊆`, `InLevel`) | 40 | |
| codes are members (`member∈J`, `mkTag∈J`, 2 + 12 clauses, two containment halves) | 41 | |
| the residue and its reduction (`defSet∈J`, `Description`, `described∈J`, `description-write`, 2 instances) | 30 | |
| **total** | **193** | file 489 lines |

**Against the recon.** The recon priced "code set as a level member (arity-1 + all-arity, both
directions of adequacy)" at 250-450. What 193 lines buy is everything on that list **except the
member form**, which was the point of the line item. The member form's re-price:

| component of (K-b) | estimate | calibration |
|---|---|---|
| object-language readers (pair, tag, key-at-arity) | 150-250 | retiring `Model` readers ≈ 300 of its 1,289 code lines; `Base` 187 |
| `closedAt` + `shapedAt` (twelve tag-keyed clauses) plus their adequacy | 300-450 | retiring `Shape` 354 + `Closed` 171 + `Slot` 187 |
| the decode inside the tower (`recover`, rank descent) | 200-300 | retiring `Recover` 190 + `InL` 330, minus the Δ₀ hops the inner reading removes |
| the separation and the two adequacy halves (this chapter's residue, discharged) | 80-120 | retiring `CodeSet`'s own 200, of which ~80 are already delivered here |
| **(K-b) total** | **730-1,120** | |

So the honest figure for the whole line item is **≈930-1,310**, against a recorded 250-450. The
mis-price has one identifiable cause and it is worth recording: the recon calibrated against the
retiring `CodeSet`'s own file (616 file lines, 200 code lines) while that chapter **imports its
entire predicate stack** (`Base`, `Shape`, `Closed`, `Slot`, `Recover`, `InL`, part of `Model`
≈ 1,400 code lines) from the same era. Calibrating against a retiring chapter has to count the
transitive closure of what it imports from its own era, not its own file.

---

## 4. Verdict on the fork

The recon's batch-order design made this chapter the commit signal: "if the code-set chapter goes
clean, commit to the internal-codes route; if it walls, the T-route's iteration graph is the
fallback."

**The signal does not fire, and it does not fire in the way that matters most: not by walling, but
by re-pricing.** Nothing in the chapter was hard; there were no conversion walls, no heap events,
one syntax error, and the whole provable content came in at 193 lines. What the chapter found is
that the recorded target's member half is not a chapter-sized obligation at all. It is the same
object as the second pillar: the twelve-clause code predicate the coded-satisfaction table also
needs. The two pillars are not 250-450 plus 700-1,200; they share their expensive half, and the
route's total is roughly **2,000-2,600** rather than 1,300-2,200.

Three riders, in decreasing order of importance to the fork:

1. **The cofinality obstruction is route-neutral.** The T-route's iterate family `{T^n(u) : n}` is
   cofinal in exactly the same way and for exactly the same reason: `rank (T^n u)` grows with `n`,
   levels are transitive, so no finite offset holds that family either, and its range-union needs
   the same definable-subset move. The obstruction the recon filed under R-35 ("union
   representations") and the one found here are the same phenomenon. **This finding removes the
   cofinality question from the fork**: it is a shared toll, not a discriminator.
2. **What the internal-codes route still has over the T-route** is that its expensive object is
   shared between its two pillars and is a *predicate over a fixed alphabet* (twelve clauses,
   mechanical, with a delivered decoder as its adequacy engine), whereas the T-route's expensive
   object is an internal recursion over the internal ω, which is a different and less mechanical
   class of work and additionally re-imports the `δ+ω ∈ γ` room condition that this chapter's
   containment half does **not** need.
3. **The residue is now a single named object with a mechanical discharge path.** Whoever builds the
   code predicate gets `codeSet∈J` and `allCodes∈J` for free, and gets them through the entry point
   that asks for two containments rather than a set equation. That is the cheapest possible shape
   for the next batch's target, and it is the reason not to re-open the route decision: the next
   batch should be "the object-language code predicate at a level, both directions", priced at
   730-1,120, and it is common to both routes' first pillar.

**Recommendation:** keep the internal-codes route, re-price it in PLAN to ≈2,000-2,600, and dispatch
the code-predicate batch (K-3) with the twelve-clause reader stack as its explicit target, with the
retiring `Shape`/`Closed`/`Slot`/`Recover` read for pattern under the inner-world reading. Do not
dispatch a "code set membership" batch: this chapter already contains everything about that
membership except the predicate.

---

## 5. Process

**Timings** (all runs `GHCRTS="-A64m -I0 -M12g"`, one check at a time, never parallel):

| run | result | wall |
|---|---|---|
| 1 | `NoParseForApplication` (a `Σ[_∈_]` at level 2 under an infixr `×` at level 5, needs parentheses) | 1.0 s |
| 2 | green, whole chapter | 9.8 s |
| 3 | green after the residue was generalized to an arbitrary target | 18.2 s |
| 4 | no-change re-run | 0.9 s |

One failure total, syntactic, fixed in one edit; three-failure stop never approached; no heap event,
no hang, no bisect. `lint-agda --check`: clean for this file (the one repo violation is in the
sibling `BaseBlock`, an in-flight file that I did not touch). `lint-prose`, `weave-i18n --check`,
`check-glossary`: clean. Stop-line 800 code lines: used 193.

**Lesson candidates** (IDs to be assigned by the owner):

1. **D-series (new): a family indexed by an inductive type is cofinal, so "member at a finite
   offset" is never its target.** Rule: before pricing a "gather the family as one set" residue,
   count the constructor cost per member against the step's arms; if the cost grows with the index,
   transitivity of the levels refutes every finite offset, and the only surviving target is
   "definable over a level", which is a satisfaction obligation and not an arm obligation. Measured
   here: the recorded finite-offset target was refuted in the five minutes D-10 asks for, before any
   code, and the corrected pair of targets (containment proved, membership reduced) came in at 193
   lines with no walls. Companion to D-10 and R-35.
2. **D-10 sub-rule: calibrate against a retiring chapter's transitive closure, not its file.** The
   250-450 estimate came from a 616-line retiring chapter that imports ≈1,400 code lines of
   same-era predicate stack; the honest figure is 3-4x. Every "port the pattern" estimate against
   the retiring tree is exposed to this.
3. **R-35 positive datum.** The small-indexed `sett` over external syntax gave both membership
   directions definitionally (introduction `∣ φ , refl ∣₁`, elimination the identity) at 45 lines
   and zero walls, where the retiring chapter's superset-plus-separation form of the same class
   needed its whole predicate stack. First case in this development where R-35's cure was applied
   before any wall on a syntax-indexed family.
4. **A reduction is a deliverable.** Stating the residue for an arbitrary target with an extensional
   entry point (`description-write`: two containments at a variable member instead of an equation
   between sets) costs 30 lines and makes the residue dischargeable without ever building a set
   equation. Second instance of the `DefFragment`/`Discharge` pattern from `DefInJ`, and it should
   be treated as the standing shape for "named and left standing".
5. **`⌜⌝-inj` has its second consumer.** The coding chapter's injectivity, added for the
   recursion-table consumer, is exactly what makes this chapter's decode untruncated at a fixed
   arity. Recording it because the investment was made against an estimate that assumed one
   consumer.
