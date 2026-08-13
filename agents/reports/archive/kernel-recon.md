# L3.31-R5-K recon: the DefFragment discharge and the hereditary-finiteness base block

Read-only recon, no edits, no Agda runs, no git. All five reading items were covered: both `_build/` reports in full, `src/FOL/Coding.lagda.md` and `src/V/Coding.lagda.md` in full, the retiring `L/Coding` tree by TOC only (headers/export lists, no bodies), `Graphs` and `SatSets` fully, and `rudimentary-functions.md` §2 plus the supporting chapters needed for the base block and the iterate-family question.

One current-state correction to the reports before anything else: `src/Everything.lagda.md` now imports both `L.Rud.DefInJ` and `L.Rud.StepInL` (Everything.lagda.md:1227-1228), so the r5d1/r5d2 "Everything untouched, file not in `make check`" caveats are stale. `StepInL` has also grown from the r5d2 count of 1,371 file lines to 2,230: it now carries all sixteen membership formulas plus the sixteen-fold `bigOr` disjunction frame (StepInL.lagda.md:2050-2230), with the `F15` relativization slot still a module parameter (`F15Of A`, StepInL.lagda.md:1435,1444) and no `stepSet∈L` assembly theorem under that name. The `Bridge.Reduce` telescope has the slot form: `stepSet∈L` now includes `⟨ A ∈ˢ Lset ζ ⟩` (Bridge.lagda.md:693-696), i.e. fix (a) from r5d2 §2 is the live one.

---

## 1. The internal-codes route

**What `FOL.Coding` already gives (read in full, 416 lines).** A generic, deliberately non-arithmetized coding:

- The module is parameterized by exactly what coding needs: an injective pairing `pr`/`pr-inj` and an injection of the naturals `encℕ`/`encℕ-inj`, over any `ZFStructure` (FOL/Coding.lagda.md:47-58). Tags are `mkTag k x = pr (encℕ k) x` (FOL/Coding.lagda.md:79-80).
- Terms: `⌜ con x ⌝ᵗ = mkTag 0 x` (constants are their own codes) and `⌜ var i ⌝ᵗ = mkTag 1 (encℕ (toℕ i))` (FOL/Coding.lagda.md:104-106). Formulas: twelve constructors, twelve tags, binary/unary/constant/bounded shaped (FOL/Coding.lagda.md:124-135). Codes are **sets**, not numerals: numerals appear only as tags and variable indices.
- The real interface is the inductive relation `Codes`/`CodesT` with sub-derivations at sub-code positions (FOL/Coding.lagda.md:139-171), with `codes-complete` and `codes-canon` tying it to the function (FOL/Coding.lagda.md:173-205).
- The final section is the one consumer that wants an equation rather than the relation: `⌜⌝-inj`, codes determine formulas, built by computing the constructor from the tag (`tagOf`, `Match`, `matches`, FOL/Coding.lagda.md:310-412). The prose is explicit about why: "a recursion's table is a **set**, so if two occurrences of different subformulas shared a code the table would be genuinely multi-valued" (FOL/Coding.lagda.md:222-229).

`V.Coding` discharges both parameters for the hierarchy: `#-inj` through monotonicity plus irreflexivity (V/Coding.lagda.md:106-115), Kuratowski `pr`/`pr-inj` through the classification specifications (V/Coding.lagda.md:175-178), and the instance `module VCode = FOL.Coding 𝒮ᵥ pr pr-inj #_ #-inj′` (V/Coding.lagda.md:231). That is the whole non-retiring coding asset: **codes for formulas and terms, injective, relation-first, and nothing else.** No sequence coding, no environments, no code sets, no internal satisfaction, no decode: all of those live in the retiring `L/Coding` tree, whose TOC inventory (module headers and export lists only) is:

- **Coded satisfaction**: `Sat` (one formula at a time, external recursion; L/Coding/Sat.lagda.md:32), `Table` (`keyʟ`, finite key/value table per formula; L/Coding/Table.lagda.md:34,82-83), `Graph` (graph frame with existentially bound table and index set; L/Coding/Graph.lagda.md:37), `Sound` (table satisfies the clauses; L/Coding/Sound.lagda.md:34), `Unique` (single-valuedness; L/Coding/Unique.lagda.md:35), `Uniform` (satisfaction over the whole code set, `AllCodes` domain; L/Coding/Uniform.lagda.md:60), `Recover` (decode: key to formula over a carrier, `keyOf`; L/Coding/Recover.lagda.md:57,112-113).
- **Sequence coding**: `Environment` (environment as its graph, `lookup-spec`, and `seqSet A = sett (Σ[ n ∈ ℕ ] (Fin n → ⟪ A ⟫)) …` as the set of all finite sequences; L/Coding/Environment.lagda.md:36,110-112,256-257), `Sequence` (the L-tower as a first-order "approximation" sentence; L/Coding/Sequence.lagda.md:41).
- **Truth predicates / shape readers**: `Base` (Δ₀ readers: singleton, unordered pair, Kuratowski pair, tagged; L/Coding/Base.lagda.md:44), `Shape` (`closedAt` eight tag-keyed implications plus shapedness; L/Coding/Shape.lagda.md:40), `Closed`/`Slot` (closedness discharged; L/Coding/Closed.lagda.md:28, L/Coding/Slot.lagda.md:27), `CodeSet` (the codes as one set: `smallDom`, keys at every arity; L/Coding/CodeSet.lagda.md:78), `InL` (each code is constructible, `isL`; L/Coding/InL.lagda.md:39), `Descent` (the rank-descent recursion vehicle, four membership steps per pair, and the seal on `rank`; L/Coding/Descent.lagda.md:30), `Model` (readers carried across the bridge, second coding instantiation `LCode`; L/Coding/Model.lagda.md:32,374), `Powerset` (`DefAt` at a carrier slot; L/Coding/Powerset.lagda.md:41), `EnvSet` (environments over a set form a set; L/Coding/EnvSet.lagda.md:26).

**What is missing on the Rud side.** Three things, exactly as r5d1 priced:

1. **The code set as a level member.** `Def A = sett (Formula ⟪ A ⟫ 1) defSet` is indexed by the **external** formula type (L/Definability.lagda.md:114-115), and `SatSets`' `T n φ` is one set per external formula (SatSets.lagda.md:1249-1264). Nothing in `L.Rud` gathers the codes of formulas over a carrier into one set that is a member of `Sset γ`. The pattern exists (CodeSet's `AllCodes`, InL's constructibility), but is L-side, Δ₀-era, and not wired to the rud tower.
2. **Satisfaction as one set over all codes**, not per formula. r5d1 §1.3 states this precisely: `Def C` is a `sett` over the external type `Formula ⟪ C ⟫ 1`, and `F8 (T (suc n) φ) (Us n)` collects the parameters of one fixed `φ`, never the formulas (r5d1-report.md §1.3). The retiring `Uniform`/`Graph`/`Table`/`Sound`/`Unique` are the exact pattern for the missing object (a table over the code set with twelve clauses, existence and uniqueness halves), but they belong to the internalization era and are not discharged at the Rud tower.
3. **The fragment-cap** `F ∩ P(C) ⊆ Def C`: the rud-term induction (M1), still open; r5d1 records only that the residue covers it, not that it is built (r5d1-report.md §6.2).

**Does the inner-world reading let the coded relation live inside without Δ₀ bookkeeping?** Yes for the *descriptions*, no for the *existence*:

- r5d2's headline is that Δ₀ is only a crossing tax: a proof written entirely inside the inner semantics of a transitive carrier never crosses, and the whole Describe-class bounded-descent apparatus (~700 lines in `LevelDesc` alone) is replaced by a 36-line equality frame plus a 165-line pair kit (r5d2-report.md §3, §7). The delivered `SatSets` engine already reads inner: `T`'s clauses and `adeq-mem`/`adeq-set` work at `⊨ᵐ` over `DefOf` (SatSets.lagda.md:202-231, 1326-1557), and StepInL's `Desc` is literally titled "The inner world, read directly" (StepInL.lagda.md:437-469).
- But "the coded relation as ONE set" is an existence obligation at the target index, not a description obligation. It needs the recursion vehicle (rank descent, Descent's pattern) or the approximation/bound argument (Sequence's pattern, Before's `approxSet`), and a proof that the assembled table is a member of the level. The inner reading removes the Δ₀ descent cost of the *readers*; it does not remove the *set-existence* cost. This is the same distinction r5d1 drew when it killed the block route: "the family-collection half is not a coding problem but the missing chapter" (r5d1-report.md §3).

**Estimate (calibrated).**

| component | estimate | calibration anchor |
|---|---|---|
| code set as a level member (arity-1 + all-arity, both directions of adequacy) | 250-450 code lines | CodeSet (616 file lines, L-side, Δ₀); DefInJ's whole member-obligation chain is 231 code lines (r5d1 §3); the inner reading cuts the reader cost |
| coded satisfaction table as one set (twelve clauses, adequacy, uniqueness) | 700-1,200 code lines | StepInL: 1,203 code lines for sixteen arms + adequacy (r5d2 §5); retiring Uniform+Graph+Table+Sound+Unique ≈ 3,040 file lines with Δ₀ discipline, the described cost being the dominant part |
| the image of the code set (fragment) | 20-60 code lines | Graphs' `Jimg` is a single `F8` instantiation (Graphs.lagda.md:2487-2505) |
| the fragment-cap (rud-term induction, M1) | 300-500 code lines | Graphs' ten-clause induction `elemRel` (Graphs.lagda.md:2432-2483) plus the realizability counterpart in `Realize` (Switch.lagda.md:544-565,629) |
| **total** | **≈1,300-2,200** | same order as StepInL (1,203) + DefInJ (231) |

---

## 2. The T-function route

**The mathematics.** WS 2.73: `T(u) = u ∪ {u} ∪ [u]^1 ∪ [u]^2 ∪ {x \ y | x,y ∈ u} ∪ {union x | x ∈ u} ∪ {Dom(x) | x ∈ u} ∪ {u ∩ (x × y) | x,y ∈ u} ∪ {x ∩ {(a,b)₂ | a ∈ b} | x ∈ u} ∪ {u ∩ {(b,a,c)₃ | (a,b,c)₃ ∈ x} | x ∈ u} ∪ {u ∩ {(b,c,a)₃ | (a,b,c)₃ ∈ x} | x ∈ u} ∪ {x"{w} | x,w ∈ u} ∪ {u ∩ {x"{w} | w ∈ y} | x,y ∈ u}` (rudimentary-functions.md §2, WS 2.73); T is rud, `u ⊆ T(u)`, `u ∈ T(u)`, transitive input gives a transitive set of subsets (WS 2.75); and for transitive `u`, `⋃_{n∈ω} T^n(u)` is the rudimentary closure of `u ∪ {u}` (WS 2.82). Rank bounds: each rud function has a finite "rudimentary constant" (MB 6.13; `cRi = 1,1,1,1,3,1,5,5,2` for R0..R8), and `Jν = T_{ων}` (MB 0.3).

**The summands against the delivered sixteen ops.** The delivered basis is exactly SZ's F0-F15, all with extensional specifications: F0 (Ops.lagda.md:127-128), F1 (160-161), F2 (210-211), F3 (277-278), F4 (366-367), F5 (452), F6 (497-498), F7 (569), F9 (647-648), F8 (Images.lagda.md:336-339), F10 (291-292), F11/F12 (369-373), F13/F14 (375-379), F15 = `A ∩ x` as the relativization slot (Images.lagda.md:420-424). Mapping T's summands (13 as written; "twelve" if `[u]^1 ∪ [u]^2` is one clause or `u ∪ {u}` is one):

| T summand | delivered realization |
|---|---|
| `u`, `{u}` | the step's cumulative arms verbatim (Step.lagda.md:391-398) |
| `[u]^1`, `[u]^2` | F0 collected over u / u² (F0: Ops.lagda.md:127) |
| `{x \ y}`, `{union x}`, `{Dom x}` | F1, F5, F6 collected over u / u² (Ops.lagda.md:160,452,497) |
| `{u ∩ (x × y)}` | F15 (A = u) applied to F2 (Images.lagda.md:421-422; F2: Ops.lagda.md:210) |
| `{x ∩ {(a,b)₂ | a ∈ b}}` | F15/F1 against F7 (Ops.lagda.md:569) |
| the two swap restrictions | F11/F12 applied over u (Images.lagda.md:369-373); the step's transitivity cases already use exactly `f11 z (pr p q)` / `f12 z (pr p q)` (Step.lagda.md:617,633) |
| `{x"{w} | x,w ∈ u}`, `{u ∩ {x"{w} | w ∈ y}}` | F10, F15∘F8 over u / u² (Images.lagda.md:291,336) |

So every summand is a bounded composite of delivered ops, and `T(u) ⊆ step u` pointwise (Step.lagda.md:338-339 is the union of all sixteen images over `(u ∪ {u})²`; Fof: Step.lagda.md:230-246). The **composite itself is cheap**: the tower's step already dominates T. The cost is never "realize T"; it is "realize the family".

**The crux: the iterate family `{T^n(u) : n}` as one set.** The delivered element-relation calculus cannot build it as delivered, for a structural reason: the Graphs machinery is a **structural recursion over the external composite type** `Comp` (Switch.lagda.md:544-565) at a record set `D` that is already a member of the closure (`IsGraph`/`Args`/`IsElemRel`/`ElemRel`/`graphOf`/`elemRel`/`Jimg`, Graphs.lagda.md:1548-2508; `Jimg` is a single `F8` of the element relation, Graphs.lagda.md:2487-2505). The family `n ↦ T^n(u)` is an **internal recursion over numerals**, not a composite: no `Comp` has arity `ω`, and the argument family cannot be given as a graph over a record set unless the record set is the internal `ω` itself. Two obstacles:

1. **The index set**: the internal ω (numerals as one set) is not a member of `Sset γ` at the base block or the top block. Content shape: `Sset ω = ⋃_{δ ∈ ω} Sset δ` (Hierarchy.lagda.md:483; `Sset-out` 320), every `Sset (# n)` is finite, so no member of `Sset ω` is infinite and ω ∉ Sset ω (r5d1 §1.3c). Above ω the index set needs `δ+ω ∈ γ` to hold, which fails at `γ = ω·(β+1)` for stages in the last block (r5d1 §1.3b). So the T-route inherits the block condition verbatim; it does not remove it.
2. **The recursion itself**: an internal finite-recursion graph (a relation `{⟨# n, T^n(u)⟩}` over the internal ω) is exactly the "approximation" pattern, and it is *not* in `L.Rud`. The delivered cousins are: `OrdBlocks`' `sucIter`/`+ω`, the ω-indexed iterate family gathered as a set by `sett (Lift ℕ)` over the **external** naturals, with membership read both ways (OrdBlocks.lagda.md:80-130) and the block map `b` (OrdBlocks.lagda.md:190-240); `L.Coding.Sequence`'s approximation frame (Sequence.lagda.md:41, "a graph may not name the object it defines"); and `L.Choice.Before`'s `approxSet k = finSet k (famOf k …)`, the finite tables of pairs below each numeral, spanned by a finite family of elements of L (Before.lagda.md:1030-1101, 1674 file lines). Any of these is portable in pattern, none is delivered on the Rud side. Note the subtlety the reports already flagged: the external-ℕ family `sett (Lift ℕ) F` is a small-indexed V-set (which is how OrdBlocks gathers it), but *being a member of the tower* still needs the family definable/representable inside one stage; the external index is not a substitute for the internal recursion, because the membership proof must land at a single `S_δ`.

**Estimate (calibrated).**

| component | estimate | calibration anchor |
|---|---|---|
| T as a composite / summand containment | 150-250 code lines | per-op transitivity cases in Step (Step.lagda.md:544-870, ~330 lines for sixteen) |
| the iteration graph over internal ω (finite-recursion graph, range-union) | 500-900 code lines | Before's approxSet machinery (1,674 file lines), Sequence (431), OrdBlocks' `+ω` family (~110 code lines) |
| fragment = range-union, cap | 300-500 code lines | Graphs' `Jimg` + the M1 induction (as in Q1) |
| **total** | **≈1,000-1,700, plus the unchanged base block** | DefInJ 231, StepInL 1,203 |

The T-route therefore buys nothing over the internal-codes route in either risk or size: it replaces the code-set work with iteration-graph work of comparable scale, keeps the same block condition, and leaves the base block untouched.

---

## 3. The base block: `γ = ω`

**What is actually needed.** `defStage∈J ζ ω limω` with `ζ ∈ ω`: `Lset (sucV ζ) ∈ˢ Sset ω` given `Lset ζ ∈ˢ Sset ω`. Since `Lset (sucV σ) ≡ 𝒟ₒ (Lset σ)` (Axioms/Basic.lagda.md:196-197; DefInJ proves the same collapse as `Lsuc≡Def`, r5d1 §2), this is `𝒟ₒ (Lset ζ) ∈ Sset ω`, i.e. the definable power of a member of `Sset ω` is again a member. With `ζ = # n` finite and `Lset ζ` finite, `𝒟ₒ (Lset ζ) = P(Lset ζ)`, so the obligation is: **the power set of a hereditarily finite member of `Sset ω` is a member of `Sset ω`**, split into (a) every subset of `C` is definable and finite, (b) finite sets of members of `Sset ω` are members of `Sset ω`, (c) the set of all such subsets is itself a member. None of (a)-(c) needs a rud-closed fragment, and none can have one: no member of `Sset ω` is closed under the sixteen ops (r5d1 §1.3c).

**Is the statement true in the delivered indexing? Yes, and the content shape is checkable now.** `Sset ω = ⋃_{δ∈ω} Sset δ` (Hierarchy.lagda.md:483), each `Sset (# n)` is finite by induction on `step` (`step u = ⋃ ⁅ u' u , values u ⁆`, Step.lagda.md:338-339; the sixteen images over the finite square `(u ∪ {u})²`), and `Sset ω` is transitive (Hierarchy.lagda.md:285-286). The concrete instance is satisfiable: `Lset ∅ = ∅` (Bridge.lagda.md:593-594), `∅ ∈ Sset ω` (Bridge.lagda.md:603-604), and `𝒟ₒ ∅ = {∅} ∈ Sset ω` is a genuine obligation with a genuine proof. The L-side twin of the whole statement is **already delivered**: `L.Choice.Finite` proves tallies at every finite stage (`finiteStage n = Lset (# n)`, Finite.lagda.md:822-823; `stageOrder`, 920-935), that the power set of a tallied stage is tallied (`PowerStep`/`powerTally`, Finite.lagda.md:351-424), and that every member of `Lset ω` appears at some finite stage (`Limit`, `inSome`, `level`, Finite.lagda.md:984-1008). The missing S-side pieces are: `Tally (Sset (# n))` (the step tower, not the Def tower), the "finite set of members of `Sset ω` is a member" lemma, and `isLimit ω` (`ω-ord : IsOrd ω` is delivered, L/Ordinal.lagda.md:263; `numeral-ord`, `#∈ω` at 244-249; but no `ω ≢ ∅`/`ω`-not-a-successor anywhere, grep confirmed empty). `FinOf` is exactly where the recon-A inventory said it would be: `finSet`/`finSet-in`/`finSet-out` (Axioms/Basic.lagda.md:285-294), `module FinOf (σ) (oσ)` with the finite disjunction and `finSet∈𝒟ₒ : finite family from a stage spans a definable subset` (Axioms/Basic.lagda.md:296-354).

**D-10 verdict.** The base-block statement is true in the delivered indexing; no counterexample at `Sset ω`'s content shape. The risk is not falsehood but **mis-pricing**: the recorded route ("block extension of `closure→definable`", M5.1) is refuted at `ω` for two independent reasons already priced in r5d1 §1.3 (carrier is a member, not a level; no room at the top block, none at `ω`). The kernel batch should price the *witness* (tallies + `finSet∈𝒟ₒ` + S-side finite-set lemma), not re-enter the rud-closure layer: r5d1 measured that a `rudCl` layer would have been ~150 lines whose only product is refutable at the first limit (r5d1 §1.3c, §5).

**Estimate (calibrated).** 200-400 code lines: the `PowerStep` pattern for one stage is ~100 file lines (Finite.lagda.md:351-424), DefInJ's comparable member-obligation chain is 231 code lines (r5d1 §3), and the new lemmas (`isLimit ω`, S-side finite-set-of-members, `Tally (Sset (# n))`) are small. The L-side `Finite` chapter (1,155 file lines) is the calibrated ceiling for the full HF treatment, but the kernel batch only needs the S-side slice of it.

---

## 4. The verdict

**Recommended kernel batch: the internal-codes route, with the base block as the first, shared chapter.** Reasons, in order of weight:

1. **Half the fragment identity is already free at limits.** Wherever a limit `μ ∈ γ` holds the carrier, `defs-in-limit` delivers every definable subset of `C` into `Sset μ` (r5d1 §2; the engine is SatSets' `full-switch-⊇`, SatSets.lagda.md:1650-1651, discharged at `Jset-rud`). The residue is then only the *member* form (the fragment as a level member) and the *cap* (M1). The internal-codes route is the classical rudimentary-satisfaction theorem that supplies exactly the member form at a finite offset.
2. **The scaffold is all in the tree.** `FOL.Coding` + `V.Coding` (delivered, non-retiring), the retiring `L/Coding` coded-satisfaction/sequence/decode patterns, the `L/Choice` internalization era (including the satisfaction graph at a carrier slot: `graphAt-value`/`graphAt-only` via `satTable`/`soundness`/`keyBridge`, Internal.lagda.md:500-570; `isCodeAnyAt`, Faithful.lagda.md:262-326), the SatSets engine, and the Graphs calculus. The r5d2 inner-world reading removes the Δ₀ descent cost that made the retiring tree expensive.
3. **The T-route shares the T-route's own blocker.** It inherits the `δ+ω ∈ γ` room condition (r5d1 §1.3b) and adds an iteration-graph chapter of the same order as the code-set chapter, without removing the base block. It is the natural fallback, not the main line.

**Fallback, named:** the T-function route (iteration graph over the internal ω via the approximation pattern, range-union as the fragment), same base block first; if the internal recursion walls on the union-representation shape, drop to the recorded `LimitFragment` form, which is true but only at limits-of-limits, and is refuted at `ω` (r5d1 §1.3b, §2).

**Risk register by LESSONS class** (dev/LESSONS.md series):

- **D-10 (price the witness, not the statement):** the base block's witness must be priced against `FinOf` before any code (its L-side twin is delivered, so the price is checkable in minutes). Second instance of r5d1's new D-series candidate: a closure fragment cannot live inside the block it closes; the base block of every rud-versus-Def statement is a separate finiteness theorem (r5d1 §7).
- **R-35 (union representations):** the iterate family and the code family are exactly the "union representation over ℕ with fiber extraction" shape R-35 warns about. The delivered cure is to state the family as a small-indexed `sett (Lift ℕ)` (OrdBlocks.lagda.md:84-130) or a `finSet` table (Before.lagda.md:1080-1101) and read memberships at small indices; r5d1 avoided R-35 by not entering `rudCl` at all, and the kernel batch should keep that discipline for the code set.
- **P-i [A] (conversion explosion):** the coded-satisfaction recursion will mention codes, ranks, or both; the tower must enter once, inside a single `opaque` block (StepInL's pattern, r5d2 §1), and `rank`'s seal exists precisely for this (L/Coding/Descent.lagda.md:1-4).
- **R-38 / D-7:** seal every derived op at its birth site (`ranOp`, `capOp`, `cupOp`; SatSets.lagda.md:151,60-78,81-87); the one LEM spend stays at the intersection-as-double-difference birth site.
- **C-8/C-11/C-12 (process):** the close-out is the `Bridge.Reduce` probe (25 lines, ~1.7 s, r5d1 §7); runs single, `-M12g`.
- **I-4:** the `↾-reflects` class implicit is expected to recur wherever the coded relation is read at a restricted structure (r5d2 §7).
- **M-series:** the base block is a **new** residue, never recorded before r5d1 §6; it must be registered as a separate theorem with its own batch, not merged into the general case.

**Shared machinery, and the batch order.** Both routes lean on the same spine: `FOL.Coding`/`V.Coding`, the Graphs element-relation calculus (`Kit`/`Cases`/`Jimg`, Graphs.lagda.md:1245-2508), the SatSets engine, OrdBlocks, and `FinOf`/`L.Choice.Finite`. A single kernel batch should therefore build the shared part first: (1) the base-block chapter (HF at `Sset ω`, ~200-400 lines), (2) the code-set-as-member chapter (~250-450 lines). The two routes then diverge only at the recursion vehicle: the coded satisfaction table (Q1, ~700-1,200) versus the T-iteration graph (Q2, ~500-900), with the cap (M1, ~300-500) common to both. Building the shared part first also de-risks the fork decision: if the code-set chapter goes clean, commit to the internal-codes route; if it walls, the T-route's iteration graph is the fallback and the shared base block is already spent either way.