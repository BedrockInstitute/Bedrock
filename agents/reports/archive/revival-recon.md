# L3.31-revival recon: the internalization-revival route to L ⊨ ZFC ∧ L ⊨ GCH

**Headline, verified against the tree:** the orchestrator's increment band ◇1.5-3.5k is honest at its center (measured-calibrated center ≈ 2.5k), but the endpoint band ◇17-19k is **refuted as an increment-inclusive endpoint**: the standing internalization route already measures **18.1k code lines** before any GCH work, so an increment of 1.5-3.5k lands at **19.6-21.6k**. The 17-19k band only coheres if it names the standing tree *without* the increment, or if someone prices a 1-2k compression of L/Coding + L/Choice, which no document in the tree has.

All line counts below are non-blank lines inside ```agda``` fences, measured today with the same convention as the pinned accounting: L/Coding 6,441, L/Choice 6,050, L/Rud 14,563, L/Godel 13,992, L total 44,614, whole src 46,753, shared (everything else) 5,596 by the pinned figure ([gch-projection-recon.md](/Users/alsg/Agentic/Bedrock/_build/gch-projection-recon.md)).

---

## STEP 1. The stock audit (the heart of the recon)

### W1, uniform satisfaction: **ON-PATH as delivered**, no upgrade

The trap the rud-side audit caught (external faces posing as internal stock) does not fire here. The satisfaction recursion's domain is the whole code set at a stage, one relation, code quantified inside the domain:

```agda
satRec : Recursion
Recursion.dom satRec = AllCodes A
Recursion.graph satRec = satGraph B
Recursion.funct satRec x x∈ = mereFunct (satGraph B) x …
```
[Uniform.lagda.md](/Users/alsg/Agentic/Bedrock/src/L/Coding/Uniform.lagda.md:289)

A member arrives as a *mere key* of a formula over the alphabet and the value at it is the formula's own satisfaction:

```agda
val-at : ∀ {n} (ψ : Formula ⟪ fst A ⟫ n) (x : S) (x∈ : ⟨ x ∈ˢ AllCodes A ⟩)
       → fst x ≡ fst (keyS A ψ) → Table.val x x∈ ≡ Sat B (toS ψ)
```
[Uniform.lagda.md](/Users/alsg/Agentic/Bedrock/src/L/Coding/Uniform.lagda.md:343)

with the adequacy against the meta relation, `val-sat` (:380: the table's value at a key *is* satisfaction over the carrier), and the definable-powerset specialization `val-defSet` (:390). The chapter explicitly retired the per-formula-slot instance that would have been the external face ([Uniform.lagda.md](/Users/alsg/Agentic/Bedrock/src/L/Coding/Uniform.lagda.md:6)), and its recorded law, "every reading takes the member as a variable and reaches its key by an equation" (recap), is exactly the uniformity discipline. The object-language side is equally uniform: `DefAt` quantifies the code and the value *inside* the formula, with the carrier at a slot ([Powerset.lagda.md](/Users/alsg/Agentic/Bedrock/src/L/Coding/Powerset.lagda.md:442)), and `DefAt-stage` discharges the side condition once at a stage:

```agda
DefAt-stage : (β : V ℓ) (oβ : IsOrd β) → ∀ {n} (u w : Fin n) (γ : S ^ n)
            → fst (lookup w γ) ≡ Lset β
            → (γ ⊨ DefAt u w) ≡ ((fst (lookup u γ) ≡ 𝒟ₒ (Lset β)), …)
```
[Powerset.lagda.md](/Users/alsg/Agentic/Bedrock/src/L/Coding/Powerset.lagda.md:720)

Nothing is missing for the machine route. The only fresh item is optional packaging: no Levy-class judgment (Σ₁/Δ₁ witnesses in the style of Devlin 2.4-2.5) is stated anywhere, and the machine does not need it, since satisfaction here is uniform across formulas. Stating the paper-shape claims is new statement work, est. **150-400 lines**, anchored to the delivered `BoundedFo`/`Δ₀-relativize` kit ([Relativize.lagda.md](/Users/alsg/Agentic/Bedrock/src/FOL/Manipulation/Relativize.lagda.md:18), consumed at [Full.lagda.md](/Users/alsg/Agentic/Bedrock/src/L/Axioms/Full.lagda.md:44)).

### W2, the uniform level formula "x = L_α" (Devlin 2.7): **ON-PATH as delivered**

The approximation sentence is a single first-order sentence at slot positions, not a level-indexed external family:

```agda
ApproxAt : ∀ {n} → Fin n → Fin n → Formula S n
ApproxAt f a = domAt f a ∧̇ ∀̇ (∀̇ (appAt (sh2 f) (suc zero) zero ⇒̇ StepAt zero (suc zero) (sh2 f)))
```
[Sequence.lagda.md](/Users/alsg/Agentic/Bedrock/src/L/Coding/Sequence.lagda.md:281)

and the level formula itself:

```agda
LsetGraphAt : ∀ {n} → Fin n → Fin n → Formula S n
LsetGraph : Formula S 2
LsetGraph = LsetGraphAt zero (suc zero)
```
[Sequence.lagda.md](/Users/alsg/Agentic/Bedrock/src/L/Coding/Sequence.lagda.md:361)

The chapter's own summary is the uniformity claim: "`LsetGraph` is the object-language sentence 'the value is the stage at the argument', written without naming a stage, a tower, or an ordinal" (recap; the design note "The tower … cannot be internalized the way the satisfaction recursion was … an approximation … a first-order sentence about `f` alone" is at the head). Adequacy is both directions against the meta tower: `Lset-only` ("nothing else satisfies it", [Hierarchy.lagda.md](/Users/alsg/Agentic/Bedrock/src/L/Hierarchy.lagda.md:333)) and `Lset-defines` (:678), plus `hierL` (:653): "the internal hierarchy, an element of `L` whose members are exactly the pairs of an ordinal with the tower's value at it, unique because its specification is a membership equivalence" (recap :703). The level is a first-class member of `L`, so there is no external α-indexing to repair. Devlin 2.6(ii)/2.8's sequence-as-member statements are not delivered in Levy-class form, but `hierL` is the machine-side content of them; anything further is the same optional packaging as W1.

### W3, the internal <_L (Devlin 3.4-3.5): **delivered, both shapes; one uniformity upgrade needed for the hull's formula**

The trap named in the brief (external order + per-stage tables) does not apply. The order at a stage is an internal formula with a both-ways adequacy:

```agda
CondCore : ∀ {n} → Fin n → Term S n → Fin n → Formula S n
…
CondCore-spec : (γ ⊨ CondCore z tb f) ≡ Related α (fst (lookup z γ))
…
Cond₀ : S → S → Formula S 1
…
cond₀-spec : (B F : S) → IsOrd (fst B) → … → ((z ∷ []) ⊨ Cond₀ B F) ≡ Related (fst B) (fst z)
```
[Faithful.lagda.md](/Users/alsg/Agentic/Bedrock/src/L/Choice/Faithful.lagda.md:550), (:827), (:858), (:893)

and the order is simultaneously materialized as an element of the model (the D-4 collector shape), with bidirectional representation lemmas:

```agda
relL : (α : V ℓ) → ⟨ isL α ⟩ → IsOrd α → S
relL-spec : … → IsRel α (relL α hα oα)
relL-fill / relL-rep : membership in relL reads the meta order both ways
```
[Table.lagda.md](/Users/alsg/Agentic/Bedrock/src/L/Choice/Table.lagda.md:864), (:867), (:894), (:898); the endgame instance at [Order.lagda.md](/Users/alsg/Agentic/Bedrock/src/L/Choice/Order.lagda.md:693) (`orderL`, `orderL-fill`, `orderL-rep`), consumed by `hasChoiceL` ([Transversal.lagda.md](/Users/alsg/Agentic/Bedrock/src/L/Choice/Transversal.lagda.md:382)).

The upgrade: Devlin 5.3's hull puts the <_L predicate *inside a defining formula over the structure (L_α, ∈)*, which requires the order as an internal formula with the carrier at a slot and constants drawn from the carrier (the DefAt relocation). The delivered `Cond₀` carries the stage as an *outer constant of the ambient model* (the tree's own R-23 law: "the stage arrives as a term, not a slot", [Faithful.lagda.md](/Users/alsg/Agentic/Bedrock/src/L/Choice/Faithful.lagda.md:958)). That is the one genuine uniformity upgrade on the whole stock list: a `WOAt` slot-form with adequacy, plus Devlin 3.4(i)-style initial-segment facts. Calibrate **300-700 lines** against the one precedent of exactly this relocation, [Powerset.lagda.md](/Users/alsg/Agentic/Bedrock/src/L/Coding/Powerset.lagda.md:442) (771 file lines for the same move on the definable powerset), with the order description heavier but its machinery already sealed. This is a DefAt-class chapter; the D-10 truth check on the target comes first, and R-21/R-26 (seal the frame's conclusion type where built; parameter plus seal both needed) apply.

### W5, collapse + condensation (Devlin 1.7.1, 5.1-5.2): **ABSENT, fresh**

Re-verified cheaply: no Mostowski collapse, no transitive-collapse, no elementary-substructure/embedding machinery anywhere in `src/L` (grep "Mostowski": 0; every "collapse" hit is a proof verb or the pair/⋂ collapse; the sibling recon's 0 holds). The tree itself flags the gap: "Condensation is not part of this … it is what a cardinal arithmetic would want" ([Power.lagda.md](/Users/alsg/Agentic/Bedrock/src/L/Axioms/Power.lagda.md:25)).

What the Def side has that helps: well-founded machinery ([WellOrder/Base.lagda.md](/Users/alsg/Agentic/Bedrock/src/L/WellOrder/Base.lagda.md) 616 file lines, [Tree.lagda.md](/Users/alsg/Agentic/Bedrock/src/L/WellOrder/Tree.lagda.md) 378), the level formula (W2) that Devlin 5.2's Σ₀-formula argument needs, and the internal order (W3) for 5.2(iii) and 5.3. Fresh estimate **650-1,250 code lines**: the V-side transitive collapse of an extensional well-founded relation at 300-600 (a new foundational chapter: ∈-recursion over the transitive closure, Mostowski isomorphism, uniqueness; the same band the projection recon priced for every route, [gch-projection-recon.md](/Users/alsg/Agentic/Bedrock/_build/gch-projection-recon.md) W5), plus the condensation theorem at 350-650 (π : X ≅ L_β for X ≺₁ L_α, β ≤ α, π(x) ≤L x). This is the least calibrated item on the list: no probe exists for the collapse (a D-1 probe is the standing doctrine for exactly this), and R-27 ("the predictor is induction count times truncation elimination", [LESSONS.md](/Users/alsg/Agentic/Bedrock/dev/LESSONS.md:635)) names the check-time risk of the collapse recursion and the elementarity induction.

### W7, hull + cardinals + 5.5-5.6: **cardinals ABSENT, fresh; hull partially stocked**

Cardinal machinery: **0 hits**; the only mentions in the tree are "inaccessible cardinal" (a caveat about the theorem's strength, [Model.lagda.md](/Users/alsg/Agentic/Bedrock/src/L/Model.lagda.md:15)) and "what a cardinal arithmetic would want" (a statement that it is *not* built, [Power.lagda.md](/Users/alsg/Agentic/Bedrock/src/L/Axioms/Power.lagda.md:27)). No |·|, no initial ordinals, no κ⁺.

The hull is partially stocked: per-formula definable subsets over a carrier exist (`DefOf`/`defSet`, [Definability.lagda.md](/Users/alsg/Agentic/Bedrock/src/L/Definability.lagda.md)), and the elementarity side has the reflection tower ([Reflect.lagda.md](/Users/alsg/Agentic/Bedrock/src/L/Reflect.lagda.md), [ReflectFo.lagda.md](/Users/alsg/Agentic/Bedrock/src/L/ReflectFo.lagda.md), with `FOL.Manipulation.Relativize` already in use at [Full.lagda.md](/Users/alsg/Agentic/Bedrock/src/L/Axioms/Full.lagda.md:44)). Fresh band **600-1,300**: hull + Tarski criterion + smallest substructure + |M| = max(|X|,ω) at 250-500; a cardinal chapter including |L_α| = |α| (the raw material is the delivered order enumeration and `hierL`; anchored against [Ordinal.lagda.md](/Users/alsg/Agentic/Bedrock/src/L/Ordinal.lagda.md) 323 and [Stage.lagda.md](/Users/alsg/Agentic/Bedrock/src/L/Stage.lagda.md) 215) at 200-450; 5.5 bounded-subsets + 5.6 GCH assembly plus the *internal* GCH sentence for the model (IsCard inside L) at 150-300. This matches the projection recon's W7 band ([gch-projection-recon.md](/Users/alsg/Agentic/Bedrock/_build/gch-projection-recon.md)).

**Increment total, calibrated: W5 650-1,250 + W7 600-1,300 + W3 upgrade 0-700 + Levy packaging 0-400 = 1,250-3,650, center ≈ 2.5k.** The orchestrator's ◇1.5-3.5k is verified at center; the low end (1.5k) assumes the W3 upgrade is free and the collapse lands at the cheap end, both unprobed assumptions.

---

## STEP 2. The wall-risk ledger

Measured record of this stack, from the chapters' own `-- perf:` markers (47 across `src/L`; the heavy chapters: Limit 5, Faithful 4, Order 3, Sequence 2, Before 2, Adequate 2, plus one each in Transversal/Table/Name/Internal):

- Satisfaction-head statements at written keys: 6 minutes against 4 s at a variable member, and the same as a corollary ([Uniform.lagda.md](/Users/alsg/Agentic/Bedrock/src/L/Coding/Uniform.lagda.md:445)).
- Two spellings of one formula compared by normalizing a satisfaction carrying the whole definable-powerset description: 98 s against an alias, 15 s per environment abbreviation, then under 2 s when the two sides are the same expression ([Sequence.lagda.md](/Users/alsg/Agentic/Bedrock/src/L/Coding/Sequence.lagda.md:431)).
- Frames instantiated at concrete elements, conclusion types unsealed: over 200 s against 7 s for the whole chapter ([Order.lagda.md](/Users/alsg/Agentic/Bedrock/src/L/Choice/Order.lagda.md:519)); the family at 376 s against 3.79 s with five descriptions sealed ([LESSONS.md](/Users/alsg/Agentic/Bedrock/dev/LESSONS.md) R-26); `with`-splits concluding in satisfactions past 300 s (Faithful).
- `PT.rec` payloads left to inference: over 140 s against 2 s ([Powerset.lagda.md](/Users/alsg/Agentic/Bedrock/src/L/Coding/Powerset.lagda.md:771) recap; Rule 8); the envOne library round-trip over 8 minutes against hand-written clauses (Powerset); the decode chain 2,237 s to 1.5 s (PLAN row L3.21).
- Cross-tree cold anchors on record: `L.Choice.Faithful` 525 lines, cold 3.5 s; whole tree cold 154 s at 15,435 code lines, 2026-07-30 ([PLAN.md](/Users/alsg/Agentic/Bedrock/dev/PLAN.md:1354)). No current whole-tree cold number is in-tree, and no agda runs were permitted here, so the re-check cost of the increment is anchored to these figures, not re-measured.

The -M28g/Makefile-gate history: P-i was imported whole on 2026-08-02 by owner direction from the antecedent project's worklog, `../fol-reification/docs/WORKLOG.md` §5, including the **twenty-case conversion table (§5.4, verified here: one line per case; e.g. case 12 layer cap, 16 explicit indices 74 min to 69 s, 17 seal terminal exports 662 to 153 s, 19 grid dispatcher 486 to 120 s)** and the decision tree §5.5 ([LESSONS.md](/Users/alsg/Agentic/Bedrock/dev/LESSONS.md:206)). The source project's standard gate was `GHCRTS="-A64m -I0 -M28g"` (WORKLOG, after the SubBridge surgery). Bedrock's Makefile now exports `GHCRTS ?= -A64m -I0 -M16g` with the -M28g override documented ([Makefile](/Users/alsg/Agentic/Bedrock/Makefile:19)), added (commit `facbc6f`) after the 2026-08-02 OOM crash killed four in-flight writers; the tiered concurrency caps and the 14 GB/process watchdog are C-12 ([LESSONS.md](/Users/alsg/Agentic/Bedrock/dev/LESSONS.md:1317)).

**Do the rud-era disciplines retrofit?** Yes, with two qualifications. Mechanism check: I-5 (written branch types inside `PT.rec` in the inner world) is Rule 8's mechanism measured at a new spot; R-36/R-38 are P-c/R-2 extensions (seal at birth, consumer aliases are birth sites); R-35 is P-b/P-c's cousin for union representations; I-4 (carrier-level combinators, never hProp-level implicits under content-of) is genuinely new and general. The disciplines are conversion-law classes, not Rud-specific, and the internalization stack's own laws (Rules 1-16, R-21-30, P-c) are the same classes with their own measurements. The direct evidence that they hold on wall-class territory over this stack's shared machinery: the G2 bridge (1,285 lines, no wall; its probe 1.8 s, "the law-book-first discipline left the B4e class nothing to fire on") and K3 (1,347 lines, six I-5 walls cured), both over the non-retiring FOL/V assets. The qualifications: I-4's A/B/C refuted abstraction-as-cure for its class, and P-h's abstractness must be applied in situ (bisects for that class must run in the real file context); the disciplines cut each measured wall class but are not a guarantee on new recursion territory (the collapse, the cardinal chapter).

**Which old chapters would the GCH increment force open?** None, if the increment is additive, and the tree's own history makes additive the natural shape: the W3 upgrade is a new slot-form chapter over the sealed `Cond₀`/`relL` exports, exactly as `DefAt` was built as a slot-form without editing the constant-form chapters; cardinals, collapse, hull, and the internal GCH sentence are new chapters; `Transversal` is not re-pointed (choice is already delivered through `Bound.orderL`). The edits are Everything wiring plus the GCH milestone/Landmarks. The re-check cost is the downstream cone re-check after each new chapter, anchored to the recorded figures above.

---

## STEP 3. The rud-trunk fate

**Delete (14,563 paid lines).** The figure is exact today (measured: L/Rud = 14,563 non-blank fence lines). Zero imports from the surviving internalization chapters: the only non-Rud importers of `L.Rud` are [Everything.lagda.md](/Users/alsg/Agentic/Bedrock/src/Everything.lagda.md:1230) (wiring) and nothing else; `rg "import L.Rud" src` matches only Everything outside `src/L/Rud/`. The dependency direction is Rud consuming the internalization stack (Describe, BaseBlock, LevelDesc import `L.Coding`/`L.Choice`), never the reverse; `L/Godel` (which retires independently) also imports only Coding/Choice. Deletion removes 14,563 checked lines and their ~21,831 file lines of trilingual prose, with no surviving importer to fix.

**Freeze.** Kept wired: make-check keeps paying the Rud cone's check cost; per-file anchors on record: Images 54.6 s cold, K3 1,347 lines (PLAN L3.31 rows); no current aggregate is measured. Kept unwired: Everything drops the 21 imports, the gate stops checking the trunk (it rots; nothing catches it), and the D15 coexistence premise is dropped while 14.6k of unverified weight stays in the tree. Neither option contributes anything to the GCH route.

**Partial-keep.** Named candidates with consumers:

- BaseBlock (453 code lines): the HF power facts at Sset ω (`basePow`, [BaseBlock.lagda.md](/Users/alsg/Agentic/Bedrock/src/L/Rud/BaseBlock.lagda.md:566)). Its content's L-side twin is already delivered: `L.Choice.Finite` (1,155 file lines, wired at [Everything.lagda.md](/Users/alsg/Agentic/Bedrock/src/Everything.lagda.md:364); "L-side twin delivered in L.Choice.Finite", PLAN K1). Def-side consumer: none beyond the twin.
- OrdArith (98): the S-recursion's ordinal gap module; consumers are Rud-only; `L.Ordinal`/`L.Ordinal.Stages` already cover the Def tower.
- Switch (911) + Graphs (2,127): the only named-theorem material (Δ₀ comprehension in the SZ 1.4 shape, P(U) ∩ rudcl = Def U); but both are consumed by and consume the whole J cone, so keeping the theorem means keeping the cone.
- Order (644): the external producer order; it is external by its own admission ("Nothing internal is claimed: the order is a bundle of the ambient theory, not an element of the level, and no formula defines it", [Order.lagda.md](/Users/alsg/Agentic/Bedrock/src/L/Rud/Order.lagda.md:1016)) and superseded on the Def side by the delivered internal order.
- SatTable (246): fragment identity "conditional on" a coded satisfaction relation that is not built (its recap names "the one missing object is the relation", [SatTable.lagda.md](/Users/alsg/Agentic/Bedrock/src/L/Rud/SatTable.lagda.md:444)); zero Def-side consumer.
- ClassJ (37): packaging; zero consumers.

Net: partial-keep is ≈ nothing on the Def side; the honest options are freeze-the-cone or delete.

---

## STEP 4. The verdict table

All endpoints in thousands of non-blank agda-fence lines, this recon's measurement; 乙-B figures from [gch-projection-recon.md](/Users/alsg/Agentic/Bedrock/_build/gch-projection-recon.md) (forward = remaining spend from today; endpoint = L ⊨ ZFC ∧ L ⊨ GCH, post-everything).

| Row | Forward-spend to GCH | Endpoint | Basis |
|---|---|---|---|
| Orchestrator band | ◇1.5-3.5k | ◇17-19k | **increment verified at center (≈2.5k); endpoint refuted as increment-inclusive** (standing base alone is 18.1k) |
| Revival, rud deleted | 1.25-3.65k (center ≈2.5k) | 19.6-21.6k | 5,596 shared + 6,441 Coding + 6,050 Choice + increment; 14,563 Rud + 13,992 Godel retired |
| Revival, rud frozen (wired) | 1.25-3.65k | 19.6-21.6k, plus 14.6k kept, checked | same arithmetic; the frozen cone adds only check weight, never endpoint math |
| Revival, rud frozen (unwired) | 1.25-3.65k | 19.6-21.6k, plus 14.6k kept, unverified | cone rots; D15 coexistence dropped |
| Revival, rud partial-keep | 1.25-3.65k | 19.6-21.6k, plus the kept cone (≈ none defensible) | all candidates have a Def-side twin or a cone dependency |
| **乙-B** (comparison line) | **3.5-6.5k** | **21.3-24.5k** | bridge remainder 980-1,450 + wing 2,535-5,000; endpoint from the recon table |

**Honest comparison against 乙-B:** the revival is cheaper in both columns, forward 1.25-3.65k against 3.5-6.5k and endpoint 19.6-21.6k against 21.3-24.5k, because the trophy is already green on this stack (no bridge spend) and because W1-W2 are delivered internal stock that the rud side had to build fresh at 1,185-2,300 ([gch-projection-recon.md](/Users/alsg/Agentic/Bedrock/_build/gch-projection-recon.md) W1-W2). The caveat is symmetric in the other direction: the revival's new chapters sit on the exact machinery whose wall classes this project measured (the 6-minute key, the 376 s family, the 2,237 s decode, the deep-satisfaction B4e class), while the rud wing's own satisfaction chapters (SatSets 1,443, StepInL 2,124) landed with zero walls under the inner-world discipline; and the collapse and cardinal chapters are genuinely new to *every* route (the recon priced them identically for 乙-B, 甲, and C′). Also honest: the revival endpoint carries 18.1k of standing internalization weight where 乙-B carries 14.6k of trunk, so the endpoint gap (≈1.7-2.9k) is the price of the already-paid choice machinery, not a structural win; it flips only if the W5/W7 chapters land at the low ends.

**Top three risks by LESSONS class:**

1. **D-10 + R-27, the collapse and the cardinal chapter.** Both are absent from the entire tree; the collapse is the first transfinite image-recursion of its kind in the book (the closest precedent, `Lset` itself by ∈-induction, [Constructible.lagda.md](/Users/alsg/Agentic/Bedrock/src/L/Constructible.lagda.md:222), and WellOrder.Tree at 279 lines for one well-foundedness). D-10 (price the target's truth before its proof) is the mandated first pass; R-27 predicts check time by induction-count times truncation-elimination. No probe exists; the projection recon priced the same band for every route without one.
2. **P-i [F]/[A]-class plus I-4/I-5, the new satisfaction-head formulas.** The W3 slot-form, the hull formula with the <_L-least-witness trick, and the internal GCH sentence are precisely the objects whose walls this stack measured (written-key readings, alias conversions, payload inference). The disciplines retrofit (G2, K3 evidence), but every new satisfaction-head statement is a new wall candidate: P-h in situ, explicit indices under satisfaction heads, written branch types, and R-21/R-26 seals at birth are the standing mitigations, not decorations.
3. **R-21/R-26/R-37, the condensation assembly.** 5.2 instantiates the sealed level formula and the order machinery at concrete elements; that is the class that walled Order past 200 s unsealed and Before at 376 s, and transported memberships at concrete indices (R-37) re-fire the tower. The endpoint arithmetic is the third risk in the ledger sense: the 17-19k band only lands with a 1-2k compression of Coding/Choice that no recon has priced.

**Post-GCH consequence, one paragraph (facts only).** With GCH in L on the Def tower, the fine-structure wing's first ingredients are already paid: the uniform satisfaction, level formula, and internal order that Devlin II.5's own next section consumes ("Σn Skolem Functions", 5.9-5.11: the <_L-least witness is Σ₁-definable, countable transitive substructures, X ∩ L_{ω₁} = L_α for X ≺₁ L_κ, dev2.txt:1421 ff.). The literature's route beyond GCH is the acceptability complement, not a new GCH route: SZ's acceptability ("a strong version of GCH", [digest.md](/Users/alsg/Agentic/Bedrock/dev/literature/digest.md:255)) with the consequences 1.23-1.27, and J_α acceptable and sound by the zig-zag induction (SZ 9.1-9.2, [digest.md](/Users/alsg/Agentic/Bedrock/dev/literature/digest.md:232)); the master-code reduction is SZ Lemma 5.6 + 5.9, conditioned on acceptability plus a very good parameter plus soundness, and SZ never use the term "master code" ([fine-structure.md](/Users/alsg/Agentic/Bedrock/dev/literature/fine-structure.md:204)); Σ*-definability is explicitly deferred to Zeman/Welch (PLAN L3.30-X1). On the Def tower, acceptability's own statements (a new subset of τ at J_{ξ+ω} gives a surjection τ → ξ) presuppose the J-side objects that the rud trunk was to provide, so the wing's Def-side form is an open design question, not a fetched theorem; and the GCH-in-L derivation itself was the corpus's OPEN item, settled only by the Devlin II.5 fetch, which is OCR-degraded and outside the errata audit ("to be read with the errata list open since WS's inventory covers chs. I and VI, not II.5", [digest.md](/Users/alsg/Agentic/Bedrock/dev/literature/digest.md:513)).