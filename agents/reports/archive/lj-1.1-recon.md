# LJ-1.1 recon: the GCH route on the internalization tower

Status: COMPLETE. Read-only. No tree edit, no commit, no push.

## 1. VERDICT

Yes, the wing is buildable on this tree. The route is Devlin 5.3 to 5.6, on the delivered internalized graph. The hull is a least-witness search over the delivered stage well-order. The collapse is the archived carrier-generic recursion. The condensation rides the delivered level sentence `LsetGraphAt`. The counting rides the archived cardinal chain.

The unbuilt, unmeasured piece is the crossing: the Levy certification of the level story and its four transfers. The wing costs about 8.0 to 10.8 thousand non-blank in-fence lines. The probe for the crossing is in section 5.

## 2. WHAT THE DELIVERED TREE ALREADY GIVES

### 2.1 The coded-formula tower

The tower is 20 masters in `src/L/Coding/`, not the 24 the brief names. `git ls-files` counts 75 masters in `src/`, and `scripts/ledger.py --brief` reports 17,492 lines. The masters are Base, Bridge, Closed, CodeSet, Descent, EnvSet, Environment, Graph, InL, Model, Powerset, Recover, Sat, Sequence, Shape, Slot, Sound, Table, Uniform, Unique.

`Sat` (L.Coding.Sat.lagda.md:140-142) delivers `cond : Formula S n → Formula S 1` and `Sat : Formula S n → S`. These make satisfaction a formula and its value an element of L.

`Bridge` (L.Coding.Bridge.lagda.md:519-531) delivers `Sat-spec`. It says membership in `Sat B φ` is satisfaction of `φ` in the world `(B, ∈)`. `Sat-out` (:577-580) says a member is a witness. `defSet-Sat` (:621-624) connects the recursion's value to the meta definable powerset. This is the bridge the brief names, and it is delivered.

`Powerset` (L.Coding.Powerset.lagda.md:442-445) delivers `DefAt` and `DefOK`. `DefAt` is the definable powerset as an object-language description at a slot. The wing's level story uses `DefAt` to say "d is the definable powerset of w".

`Sequence` (L.Coding.Sequence.lagda.md:361-364) delivers `LsetGraphAt` and `LsetGraph`. The graph is one existential over an approximation and a step. The approximation is at :281-282, the step at :119-120. This sentence is the level-hood sentence the condensation argument can use.

`CodeSet` (L.Coding.CodeSet.lagda.md:311-315) delivers `codeS` and `keyS`. These make codes and keys elements of L. `isCode` and `isCodeAny` (:257-261) say what a code is. This is the syntax-as-index machinery D-26 demands.

`Model` (L.Coding.Model.lagda.md:662) delivers `extAt`, the frame every set-valued clause uses. The adequacy tail lives in Sound (1,048 lines), Unique (908), Table (396), Slot (265), Graph (238). The tail closes with `Lset-only` (L.Hierarchy.lagda.md:333).

### 2.2 The FOL layer

`FOL.LevyHierarchy` (src/FOL/LevyHierarchy.lagda.md:47-80) delivers `Δ₀`, `Σ₁`, `Π₁` as inductive witnesses. `FOL.Absoluteness` (src/FOL/Absoluteness.lagda.md:122-190) delivers `abs₀`, `σ₁-up`, `π₁-down` at a transitive class. These are the transfer theorems the hull argument uses.

The tree has the certification language. The tree does not certify `LsetGraphAt` in any of the three classes. T257 §3.3 and T263 record this. The raw graph carries unbounded quantifiers of both kinds, so none of the three transfers applies to it. That gap is the crossing.

### 2.3 The tower and its indices

`L.Constructible` (src/L/Constructible.lagda.md:319-356) delivers `Lset-in`, `Lset-out`, `Lset-mono`, and `isL` at :376. `L.Ordinal.Stages` (src/L/Ordinal/Stages.lagda.md) delivers `Lset-cumul` (:164), `rank-Lset` (:190), `ord∈Lset-suc` (:434). `L.Ordinal` (src/L/Ordinal.lagda.md) delivers `#∈ω` (:248), `ω-ord` (:263), `∈#-elim` (:291). `L.Ordinal.Linear` (:133-136) delivers trichotomy.

`L.Hierarchy` (src/L/Hierarchy.lagda.md) delivers `Lset-only` (:333), `hierL` (:653), `Lset-defines` (:678). The graph determines the meta tower, and the internal hierarchy is an element of the model.

### 2.4 Reflection and stages

`L.Stage` (src/L/Stage.lagda.md:149-180) delivers `leastOrd`, `theEarliest`, `stage`. These pick the least stage holding a witness, by well-founded descent.

`L.Reflect` (src/L/Reflect.lagda.md:411, :495-498) delivers single-matrix reflection. `L.ReflectFo` (src/L/ReflectFo.lagda.md:525-530) delivers `mkReflect`: full reflection for any formula at a stage containing a given ordinal.

The archived Hull priced reflection as the wrong instrument for building a hull. Its closures cannot be iterated into a hull (archive/rud-route/src/L/Hull.lagda.md:5-9). The hull uses the meta well-order instead. Whether the wing consumes reflection elsewhere is open.

### 2.5 The well-order and smallness

`L.WellOrder.Base` (src/L/WellOrder/Base.lagda.md:158) delivers `leastOf` over any strict well-order. `L.Choice.Step` (src/L/Choice/Step.lagda.md:740-749) delivers `orderAt` and `stageOrder`, the well-order on each stage's carrier. `L.Choice.Order` (src/L/Choice/Order.lagda.md:693-702) delivers `orderL`, the order as an element.

`V.Smallness` (src/V/Smallness.lagda.md:41) delivers the smallness atoms, `∈-asFiber` among them. `V.Hierarchy` (src/V/Hierarchy.lagda.md:177-184) delivers `∈-induction` and `∈-induction-compute`, the collapse's recursor. `V.Model` (src/V/Model.lagda.md:280-329) delivers `Power` and `𝒫V`, the powerset object Cantor's theorem needs.

### 2.6 The AC wing

`L.Model` (src/L/Model.lagda.md:83-99) delivers `L⊨ZF` and `L⊨ZFC`. `L.Choice.Transversal` (src/L/Choice/Transversal.lagda.md:372-382) delivers `ChoiceStatement` and `hasChoiceL`. This is the pattern for stating an internal axiom and proving it.

The Coding and Choice chapters deliver the idiom the wing should copy: formulas at variable slots, adequacy lemmas, sealed definitions. The wing generalizes this idiom. It does not copy chapters whole.

### 2.7 The answer to the central question

The internalization tree already gives the GCH wing what a fresh tower would not have.

1. The level-hood sentence is a delivered formula. `LsetGraphAt` (Sequence.lagda.md:361-364) says "v is the tower's value at b" in the object language. `Lset-only` (Hierarchy.lagda.md:333) and `Lset-defines` (Hierarchy.lagda.md:678) prove the graph agrees with the meta tower at every ordinal. A fresh tower would write this sentence and its adequacy. The archived crossing-rebuild measured that cost at 5,047 lines (T257 §4.2). On this tree the supplier stands.
2. The coded satisfaction is delivered. A Def-stage's members carry no generation data (D-26). Their only well-founded key is syntax. The coding makes syntax an element of L (`codeS` and `keyS`, CodeSet.lagda.md:311-315) and satisfaction a formula (`Sat`, Sat.lagda.md:142). The Σ₁ hull argument needs "x is definable from parameters" as an object-language statement. The coded satisfaction is that statement.
3. The stage well-order is delivered. `orderAt` (Choice/Step.lagda.md:740) and `leastOf` (WellOrder/Base.lagda.md:158) make the hull's witness search a meta-level search. No order formula is needed. The W3 row collapses from 760-1,750 to 100-300 lines (T257 §3.2).
4. The least-stage machinery is delivered. `leastOrd` (Stage.lagda.md:149) and `stage` (:180) pick canonical witnesses without a well-ordering of L.
5. The AC idiom is delivered. The wing writes its formulas and certificates the way Choice and Coding do. The certified-predicate pattern in the archived CardinalPredicates is the same pattern Choice uses.

## 3. THE CONDENSATION LEMMA, STATED PRECISELY

The lemma the wing needs, stated for the plan:

Let β be a limit ordinal. Let M be a set with M ⊆ Lset β. Let (M, ∈) be Σ₁-elementary in (Lset β, ∈) at parameters from M, in the sense of the hull chapter's `Elementary`. Let π be the Mostowski collapse of M and let N be its transitive image. Then there is an ordinal γ ≤ β with N = Lset γ.

The wing instance: let κ be an infinite cardinal. Take X = Lset κ ∪ {A}, where A ⊆ Lset κ and A ∈ L. Take β a limit ordinal with κ < β and A ∈ Lset β. The least-witness hull M of X in Lset β is Σ₁-elementary at hull parameters. Its collapse N is Lset γ with |γ| ≤ |M| ≤ max(|X|, ω) = κ. The initial-ordinal fact gives γ < κ⁺. Then A ∈ Lset γ ⊆ Lset κ⁺.

Why the plan believes the lemma is true of the Def tower (D-10):

- The Def operator is the textbook one. `Def A` collects `defSet φ` over `Formula ⟪A⟫ 1` (Definability.lagda.md:111-114). `Lset-suc` says `Lset (sucV σ) ≡ 𝒟ₒ (Lset σ)` (Axioms/Basic.lagda.md:196). The tower is the standard L hierarchy.
- Devlin VI.4.1 is a classical ZF theorem. The tree is classical: LEM is a module parameter (L.Model.lagda.md:83-99).
- The internalized story exists. `LsetGraphAt` (Sequence.lagda.md:361-364) is the level-hood sentence. The graph's correctness and completeness against the meta tower are delivered (Lset-only:333, Lset-defines:678).
- The lemma is not Devlin VI.2.4, the classically false kernel the campaign lost. The failure modes the plan must respect are named. β must be a limit, and the limit case of the condensation induction is missing (priced at 30-90 lines). M itself is not transitive; only the collapse is. The initial-ordinal fact "|γ| ≤ κ implies γ < κ⁺" is not in the tree (T91 §1.4).
- The two load-bearing subclaims the tree lacks are small and priced. The satisfaction iso-invariance under the collapse costs 0.08-0.14k (T51 §2). The limit case costs 30-90 lines (T64). Neither is known false.

## 4. THE BLOCK PLAN

One block per deliverable chapter. Each block states its statement, dependencies, delivered modules it rides, generic-or-fixed prices, and size basis. The mapping to the [LJ-1.x] rows is at the end of each block.

### Block 1. Skolem hull, [LJ-1.3]

Statement: `Elementary` and `TarskiVaught` are equivalent at a transitive set carrier inside a stage. The hull of a parameter set X inside Lset α is the sett over pairs of a formula and a small witness. The value at a pair is the least witness in the meta well-order. The hull contains X. The hull satisfies the Tarski-Vaught criterion at its own parameter source.

Dependencies: FOL.LevyHierarchy, FOL.Absoluteness, L.WellOrder.Base, L.Choice.Step, V.Smallness, L.Constructible.

Rides: `abs₀`/`σ₁-up`/`π₁-down` (FOL/Absoluteness.lagda.md:122-190); `leastOf` (WellOrder/Base.lagda.md:158); `orderAt` (Choice/Step.lagda.md:740); `stageOrder` (:748); `∈-asFiber` (V/Smallness.lagda.md:41); `Lset-layer` (Constructible.lagda.md:246).

Generic or fixed: the archived shape is generic in α and X (archive/rud-route/src/L/Hull.lagda.md, modules `AtStage` and `Hull`). The generic price is 241-388 non-blank lines. The fixed price is the same content at a concrete stage, about 300-450 lines. It checks at about 20 times the seconds (P-m at 0.01, P-n at 0.22 s per line, dev/LESSONS.md:2254, :2277). Generic wins. The one fixed atom is the order membership `pr x y ∈̇ con orderL` at hull parameters, with its adequacy from `orderL-fill` and `orderL-rep` (Choice/Order.lagda.md:696-702).

Size: 340-540 naive. Basis: delivered comparable (the archived L.Hull at 241 in-fence, T257 B1) plus survey (the W3 residue at 100-300, T257 §3.2).

### Block 2. Mostowski collapse, [LJ-1.4]

Statement: for a transitive set carrier X, the collapse π by ∈-recursion; the range πX is transitive; π is one-to-one on X; membership is preserved both ways; the transitive image is unique. Add the transitive-fixing clause: if Y ⊆ X is transitive, π fixes Y pointwise (Devlin 5.2(ii)).

Dependencies: V.Hierarchy, V.Smallness, FOL.ZFStructure, the V.Presentation shim.

Rides: `∈-induction` and `∈-induction-compute` (V/Hierarchy.lagda.md:177-184); extensionality; the library presentation.

Generic or fixed: the archived chapter is carrier-generic (archive/rud-route/src/V/Collapse.lagda.md, module `Collapse X`). The generic price is 181-357 lines. The fixed price is about 250-420 lines at instantiation-rate seconds. Generic wins.

Size: 230-330 naive. Basis: delivered comparable (the archived V.Collapse at 181 in-fence; T39 delivered, probe green and carrier-neutral) plus survey (the transitive-fixing clause at 50-150, T91 §1.4).

### Block 3. Condensation, [LJ-1.5]

This block splits into five sub-blocks.

Sub-block 3a, the level story substrate. Statement: the parameter-free structural formulas (singleton, pair, zero, domain, limit, range) with Δ₀ witnesses, and the order combinators. Rides: the delivered pair atoms in Coding/Base.lagda.md:288-371, `mapΔ₀` and `embed` (FOL/Manipulation/Relabelling.lagda.md:117-118, :209-221). Generic: written once at the empty constant domain, embedded at every carrier. Fixed: one carrier's copy, duplicated. Size: 1,459 naive. Basis: delivered comparable (T257 B1: LevelKit 587, LevelFormula 258, PairAtoms 219, InitialSegment 114, WellOrder.Combinators 263, V.Presentation 18, all in-fence). The adaptation headroom is in section 9.

Sub-block 3b, the condensation core. Statement: `Believes`, `CrossOut`, `HasLevels`, `Covered`, `SucClosed`, `Condenses`; the successor case `succ-step`; `level-in`; `M⊆L`; the meaning-preserving transport `amb-agree`. Rides: `ord∈Lset-suc` (Ordinal/Stages.lagda.md:434), `Lset-suc` (Axioms/Basic.lagda.md:196), `Lset→isL` (Constructible). Generic: stated at an abstract transitive carrier M, with the stage opaque. Fixed: one carrier's copy, duplicated. Size: 514-600 naive. Basis: delivered comparable (the archived L.Condensation core at 514 in-fence).

Sub-block 3c, the structural story assembly. Statement: the level story `levelStory : Formula (⊥* {ℓ}) 2`, embedded at both carriers, with its two-way decodes. Size: 515-688 naive. Basis: x1.3 survey (T257 structural-story).

Sub-block 3d, the crossing transfers. Statement: `TransferM`, `TransferL`, `ValueIsL`, `AmbientOnly` for the certified level story, and the equivalence against the delivered description at both carriers. This is the widest unmeasured term; the probe in section 5 prices it. Size: 700-1,720 naive. Basis: survey, class x3 (T257 W1p; T51).

Sub-block 3e, the limit case and the transport certificate. Statement: the limit case of the condensation induction; the certificate `BoundedFo InM (LsetGraphAt {2} zero (suc zero))`. Size: 180-390 naive. Basis: survey (30-90 from T33/T64, 150-300 from T51/T64).

Block 3 total: 3,368-4,857 naive. Center about 4,110.

Generic or fixed for the whole block: the story and transfers are stated at abstract transitive carriers with the stage opaque (P-l, dev/LESSONS.md:2099). The fixed shape duplicates the story per carrier. Generic wins. The one measured exception: the archived transfer obligations were stated at the concrete formula `LsetGraphAt {2} zero (suc zero)`, and the archive measured statement-bound seconds there (T96-T106). P-t says the cost class follows the formula, not the carrier (dev/LESSONS.md:2395). The probe must measure whether the abstract form avoids that cost.

### Block 4. The cardinal chain and stage cardinality, [LJ-1.6]

This block splits into seven chapters.

4a. FOL.Count. Statement: `shape-count-inj` and `count-inj`, the injection of `Formula K 1` into the disjoint union of parameter-free shapes with constant tuples. Generic in K. Rides: `FOL.Manipulation.Parameters` (src/FOL/Manipulation/Parameters.lagda.md:22-77), delivered. Size: 588-700. Basis: delivered comparable (the archived FOL.Count at 588 in-fence).

4b. Cardinal predicates. Statement: `HostBij`, `HostEq`, `IsCard`, `IsSuccCard` as formulas with adequacy certificates. Generic in de Bruijn positions. Size: 399-500. Basis: delivered comparable (the archived CardinalPredicates at 399 in-fence).

4c. Ordinal pairing. Statement: the injective pairing on an infinite ordinal's index. Rides: `ord-tri` (Ordinal/Linear.lagda.md:136), `leastOf`, `V.Model`. Size: 376-500. Basis: delivered comparable (the archived Pairing at 376 in-fence).

4d. Square law. Statement: `sq`, `Init`, `initial-bound`, `initial-bound-inj`, `initial-square-law` at initial ordinals. Size: 907-1,100. Basis: delivered comparable (the archived SquareLaw at 907 in-fence). Seconds warning: the archived module measured 856 s cold on the comparable tree, was cut to 61.9 s, and its abstract restatement heap-exhausted at -M8g (T98). The seconds must be re-measured at this site (P-l).

4e. The counting bound. Statement: `composed-count`, `formula-bound`, and the `Bound` module at an infinite ordinal β under a pairing hypothesis. Size: 166-250. Basis: delivered comparable (the archived CardinalCount at 166 in-fence).

4f. The cardinal chapter. Statement: `csb`, `csb-eq` (`HostEq`), `cantor`, and the lower bound into the hull (X ⊆ M, ω ⊆ M). Rides: `Power` and `𝒫V` (V/Model.lagda.md:280-329), `#∈ω` (Ordinal.lagda.md:248). Size: 299-400. Basis: delivered comparable (the archived Cardinal at 299 in-fence).

4g. Stage cardinality assembly. Statement: |Lset α| = |α| for infinite α, and the initial-ordinal facts (|γ| ≤ κ implies γ < κ⁺). Size: 200-500. Basis: survey (part of the w7-residue row at 650-1,320, T257 §3.4; T91 §1.4).

Block 4 total: 2,935-3,950 naive.

Generic or fixed: the count and the bound are generic in K and β (the archived shapes). The square law is the measured exception: the archived abstract restatement failed, so the plan prices the delivered shape and re-measures its seconds at this site.

### Block 5. Subsets appear early, [LJ-1.7]

Statement: for an infinite cardinal κ, every constructible subset of Lset κ lies in Lset κ⁺. The step consumes the hull, the collapse with its transitive-fixing clause, the condensation, the stage cardinality, and the initial-ordinal facts.

Dependencies: Blocks 1 to 4.

Size: 480-1,020 naive. Basis: survey, class x3 (T257 gch-proof-steps; T91 §1.1 prices the bounded-subsets step at 0.08-0.25k inside it).

Generic or fixed: the step is stated at an abstract infinite ordinal κ with the stage opaque (P-l). A fixed statement at a concrete cardinal duplicates the proof per instance. Generic wins.

### Block 6. Assemble L models GCH, [LJ-1.8]

Statement: the internal GCH sentence via the certified predicates, and the proof that 𝒮ʟ satisfies it, in the shape of `ChoiceStatement` (Choice/Transversal.lagda.md:372-382).

Dependencies: Block 5, L.Model, FOL.ZFModel, the certified predicates.

Size: 150-350 naive. Basis: survey (T257 §3.4: the sentence assembly uses the meta-level relation in FOL.Semantics, not a new satisfaction set).

Generic or fixed: the sentence is written once at the model carrier. The statement pattern is the delivered `ChoiceStatement` shape. Generic.

### Wiring

Statement: `src/Everything.lagda.md` imports, ledger rows, `check-ratio.py` entries. Size: 50-150. Basis: survey.

### DD4, stated once for the whole wing

The wing generalizes the delivered idiom: formulas at variable slots, adequacy lemmas, sealed definitions, and the `ChoiceStatement` pattern. It writes the level story and the cardinal predicates once, parameter-free or at de Bruijn positions, and embeds them at each carrier. It leaves the delivered machinery alone: L.Hierarchy, L.Coding.Sequence, L.Coding.Powerset, FOL.Absoluteness, FOL.LevyHierarchy are consumed as delivered, never copied.

Two measured exceptions bind. P-r: do not fold the level story's clauses into a clause-list fold; the hand-written conjunction costs about a third of the fold (dev/LESSONS.md:2327). The square law resists the abstract-carrier discipline: the archived restatement heap-exhausted, so the plan prices the delivered shape (section 4, 4d).

## 5. THE WIDEST UNMEASURED TERM AND ITS PROBE

The widest unmeasured term is the crossing: the Levy certification of the level story and the four transfer obligations (`TransferM`, `TransferL`, `ValueIsL`, `AmbientOnly`). The archive priced it at 700-1,720 naive, class x3, and no probe has run at this site. D38 records T130's status line as "no probe, no Agda run". T261 is queued for the same site. The term is unmeasured anywhere: the archived condensation left the crossing standing, and the four obligations are not in the delivered tree.

Why it is first: it is the load-bearing step of the whole wing. The delivered description `LsetGraphAt` is neither Δ₀, Σ₁, nor Π₁ in the delivered certification (T257 §3.3), so none of the three transfer theorems applies to it. The certification is the obstacle, not the count (T51 §2). The raw-form obligations are not a sound target at arbitrary carriers: inner truth of a formula with an unbounded universal carries no information about ambient elements outside the carrier (T51 §2, D-10).

The second-ranked term is the square law. It has a delivered comparable with a measured cost (907 in-fence lines, 856 s cold, cut to 61.9 s on the comparable tree). Its content class is known: presentation-bound, statement-bound, with an abstract restatement that heap-exhausted (T98). It is not on the condensation critical path; it serves the counting bound. Its seconds ratio is the wing's largest DD24 risk, and the plan re-measures it at its own site.

The probe, specified for [LJ-1.2]:

- File: a probe master at `src/ProbeLJ12.lagda.md`, never committed (D-1). It imports L.Coding.Sequence, L.Hierarchy, FOL.LevyHierarchy, FOL.Manipulation.Relabelling, L.Constructible.
- Statement 1: certify the level story at the class carrier. Write the bounded rewrite of each clause at the exact shape `LsetGraphAt {2} zero (suc zero)` (Sequence.lagda.md:361-364). Give each rewrite a Δ₀ witness. Assemble the Σ₁ witness `levelΣ₁ : Σ₁ (embed levelStory)` at the class carrier.
- Statement 2: the class-carrier equivalence. Prove `(v ∷ b ∷ []) AbsL.⊨ᵐ σL` is equivalent to `fst v ≡ Lset (fst b)` for `IsOrd b`, riding `Lset-only` (Hierarchy.lagda.md:333) and `Lset-defines` (Hierarchy.lagda.md:678). No re-proved graph theorem may enter.
- GO: all clauses certify at or below 25 non-blank lines each. The Σ₁ witness assembles. The equivalence closes at or below 350 non-blank lines total. Then the per-combinator rate is measured. The crossing row moves from class x3 to about x1.3. [LJ-1.5] is funded at the survey band.
- NO-GO: at least one clause resists bounding without a new carrier fact. The step's code and value existentials may need the code set as a level member. The `DefAt` leaves may need the twelve-clause table. Then the crossing re-prices at the D32 Build A band of about 5.0-5.1k. The plan stops for a re-price (DD8).
- Cost: one dispatch, and the probe is 250-400 non-blank lines. One Agda process at `GHCRTS=-M8g`. The certification checks at the parameterized rate of about 0.01-0.13 s per line (P-m, P-t). The equivalence checks at P-n's floor. The expected wall is 2-15 s plus elaboration risk, and the dispatch is one agent-slot.

## 6. ONE BEST-EFFORT PROJECTION FOR THE WING

Projection: 8.0 to 10.8 thousand non-blank in-fence lines, center about 9.4 thousand.

Basis per block, named:

| Block | Naive band | Basis |
|---|---:|---|
| 1 Hull | 340-540 | Delivered comparable (241), survey (100-300) |
| 2 Collapse | 230-330 | Delivered comparable (181), survey (50-150) |
| 3 Condensation | 3,368-4,857 | Delivered comparables (1,973), x1.3 survey (515-688), x3 surveys (880-2,110) |
| 4 Cardinal chain | 2,935-3,950 | Delivered comparables (2,735), survey (200-500) |
| 5 Subsets early | 480-1,020 | Survey, x3 |
| 6 L models GCH | 150-350 | Survey |
| Wiring | 50-150 | Survey |
| Total | 7,553-11,197 | Block sum |

The projection is the T257 independent survey band, 8.0-10.8k, which sits inside my block sum. About 5.1k of the total rests on delivered comparables: the archived modules at their measured in-fence sizes. The rest rests on surveys. No block is UNPRICED.

The seconds dimension is not part of this projection. DD24's bar is 0.008756 s per line (the AC wing's 0.007614 times the 1.15 tolerance, dev/ledger.toml:2412-2440). The square law at its archived seconds would break that bar if the cost transfers. The plan re-measures it at its own site.

## 7. WHERE I DISAGREE WITH THE LJ-1.x ROWS

1. [LJ-1.6] claims stage cardinality runs in parallel with [LJ-1.3] to [LJ-1.5]. The machinery is parallel; the assembly is not. The counting bound consumes the square law and its pairing chapter, so those two must land before [LJ-1.7]. The initial-ordinal facts (|γ| ≤ κ implies γ < κ⁺) appear on no row and block [LJ-1.7].
2. [LJ-1.3] should not plan a fresh Σ₁ machinery build. The delivered order gives the hull's witness search. The coded satisfaction is the supplier, not the method. The archived Hull prices reflection as the wrong instrument (Hull.lagda.md:5-9 in the archive). [LJ-1.3] rides the AC wing's well-order.
3. [LJ-1.5] understates the block. The row reads as one chapter. The archive shows the delivered core is half the block: the crossing is deleted (D32), the limit case is unbuilt, and the crossing transfers are unmeasured. [LJ-1.5] splits into substrate, core, story, transfers, and limit case.
4. [LJ-1.4] misses the transitive-fixing clause. Even the archive lacks it (T91 §1.4).
5. [LJ-1.8] is smaller than a coded-formula build. The sentence uses the meta-level relation with the certified predicates (T257 §3.4).
6. The rows fold the counting machinery into [LJ-1.6]. The block plan splits it into six chapters and names each basis.
7. Minor: the brief names 24 masters in `src/L/Coding/`. The tree has 20.

## 8. ARCHIVE USED

### 8.1 The archived modules

`archive/rud-route/src/L/Hull.lagda.md` (388 lines): ADAPTABLE. The shape (Elementary, TarskiVaught, TV-thm, Hull as a sett over formula-and-witness pairs, leastWit via leastOf over orderAt) rides the current tree. The imports need re-pointing: `V.Presentation` is missing, and the tree uses `∈-asFiber` instead. In-fence 241.

`archive/rud-route/src/V/Collapse.lagda.md` (357 lines): PORTABLE. It is carrier-generic and imports V.Hierarchy, V.Presentation, V.Smallness, FOL.ZFStructure, and the library. Add the missing V.Presentation shim (42 file lines in the archive) and the transitive-fixing clause. In-fence 181.

`archive/rud-route/src/L/Condensation.lagda.md` (751 lines): ADAPTABLE IN SHAPE ONLY. The delivered core (Believes, CrossOut, HasLevels, Covered, SucClosed, Condenses; succ-step, level-in, M⊆L; amb-agree; σᴹ and σL with level-transfer) is usable. The crossing application was deleted by D32 and never rebuilt. The limit case is unbuilt. On this tree the delivered description is `LsetGraphAt` and `hierL`, so the crossing is the W1p row. In-fence 514.

`archive/rud-route/src/L/Cardinal.lagda.md` (409 lines): ADAPTABLE. `csb`, `csb-eq`, `hostBij`, `cantor` and the lower bound. Imports `V.Model` and `L.Ordinal`, both delivered. In-fence 299.

`archive/rud-route/src/L/CardinalPredicates.lagda.md` (547 lines): PORTABLE. It is pure FOL plus V.Coding plus L.Constructible, generic in de Bruijn positions. In-fence 399.

`archive/rud-route/src/L/CardinalCount.lagda.md` (301 lines): ADAPTABLE. The counting bound stops at the square law. The `Bound` module takes the pairing at β as a parameter. In-fence 166.

`archive/rud-route/src/FOL/Count.lagda.md` (917 lines): PORTABLE. Its dependency `FOL.Manipulation.Parameters` is delivered (src/FOL/Manipulation/Parameters.lagda.md:22-77). In-fence 588.

`archive/rud-route/src/L/Ordinal/Pairing.lagda.md` (633 lines): ADAPTABLE. It depends on L.Ordinal.Linear, L.WellOrder.Base, V.Model, all delivered. In-fence 376.

`archive/rud-route/src/L/Ordinal/SquareLaw.lagda.md` (1,299 lines): ADAPTABLE WITH WARNING. It is presentation-bound. It measured 856 s cold on the comparable tree and 61.9 s after a thirteenfold cut. Its abstract restatement heap-exhausted at -M8g (T98). In-fence 907. Re-measure the seconds at this site.

`archive/rud-route/src/L/LevelKit.lagda.md` (859), `LevelFormula.lagda.md` (492), `InitialSegment.lagda.md` (290), `PairAtoms.lagda.md` (386), `WellOrder/Combinators.lagda.md` (417), `V/Presentation.lagda.md` (42): ADAPTABLE. They are the level-story substrate and carry no rud imports (T257 §5.2). In-fence 587, 258, 114, 219, 263, 18.

`archive/rud-route/README.md`: the four things. The generic machinery lives in StepStory and Bridge, both rud-specific and DEAD for this wing. What the route could not do is priced in the archives. A measured cure does not transfer by analogy.

### 8.2 The archive records

`archive/dev/TASKS-archived.md`: [T9] at :44, the W7 cardinal gate, RED. The journal explains it (archive/dev/JOURNAL-archived.md:1212-1258): the count is green on the mathematics but costs 448 lines over the 400-line stop-line; the product bound walls on the ordinal pairing theorem, for which the tree had no raw material; the payoff adds a shape-count the plan never itemized. The owner ruled to build the pairing chapter (T16) and the shape-count probe (T17).

Other rows read: [T40] hull delivered (:75), [T43] counting calls the square law, RED (:78), [T47] truncated square law delivered with a D-10 record (:82), [T84] condensation story STOP, D-10 (:119), [T91] the whole path walked, COMPLETE with owed gaps (:126), [T96] condensation seconds priced refusal (:131), [T257]-[T261] the route pricing and crossing gates (:262-266).

`archive/dev/DECISIONS-archived.md`: D31 and D32 (:51-52) severed the condensation crossing and deferred its rebuild to the GCH resume. D33 (:53) split the trophy. D38 and D39 (:57-58) ruled the two-tower bridge route and the relative constraints. The internalization Phase 1 exists to measure the wing (dev/PLAN.md:74-90).

`dev/LESSONS.md`: P-m (:2254), P-n (:2277), P-r (:2327), P-s (:2363), P-t (:2395), P-q (:2427), P-l (:2099). The pricing in section 4 uses these.

`dev/ledger.toml` [ratio] block (:2412-2440): the baseline 0.007614 s per line, the tolerance 1.15, the empty `gch_wing` list.

## 9. WHAT I AM NOT SURE OF

1. Whether the level story on this tree is the archived structural story or a fresh certification of `LsetGraphAt`. The probe in section 5 decides.
2. Whether `mkReflect` is consumed by the wing. The archived hull did not use it. The bounded-subsets step may.
3. The exact shape of the GCH sentence: the meta-level relation (T257 §3.4) or a coded formula. The [LJ-1.8] row implies coded.
4. The W3 residue at 100-300 is the least supported figure in the plan. T257 §3.2 flags it as a pure survey.
5. The square law's seconds on this tree. The archive measured them on a comparable tree, not here (P-l).
6. Whether the delivered pair atoms (Coding/Base.lagda.md:288-371) replace PairAtoms. The adaptation headroom in sub-block 3a covers the difference.
7. Where the satisfaction iso-invariance under the collapse lives. It is priced at 0.08-0.14k (T51 §2) and may sit in Block 2 or Block 3.
8. The DD24 ratio for the wing. The seconds dimension is unmeasured, and the square law is the largest single risk. Evidence that would close it: a cold check of the square law at this site, whole.

Evidence that would close item 1: the probe's GO or NO-GO. Evidence for item 5: one cold check of the square law master at this site. Evidence for item 3: a statement of the GCH sentence in the shape of `ChoiceStatement`.
