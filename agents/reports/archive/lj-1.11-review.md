# [LJ-1.11] Adversarial review of phase 1 against the literature route

Status: COMPLETE. Read-only on `src/`. No agda run, no commit, no push.
Reviewer tier: fable 5, owner-named 2026-08-10. Written incrementally (C-22).

Authority marks used below: [LIT] is what the literature says. [REP] is what a
phase-1 report or an archive record says. [INF] is my own inference. The brief
demands the separation, so every load-bearing claim carries one mark.

## 1. VERDICT

Phase 1 follows the literature's route in its skeleton and in both delivered
chapters. The hull, the collapse, the counting chain and the assembly map onto
Devlin II.5 step for step, with no step skipped or merged. The two delivered
chapters are honest ports, generic as claimed, and inside their bands. But the
review finds two mathematical defects, and they outrank everything else. First:
`[LJ-1.10]`'s route C rests on an equivalence that is classically false. The
structural story with its Def-step collapsed to `⊤̇` cannot recognize levels,
at any carrier, and an explicit counterexample refutes it (section 7, F1). The
literature carries the successor content inside the certified formula in BOTH
of its condensation engines, and no fetched text drops it. Second: the
delivered collapse proves its injectivity half only at a TRANSITIVE carrier,
where the collapse is provably the identity. The condensation step collapses
the non-transitive hull, so the needed extensional-carrier version is neither
delivered nor priced (section 7, F2). `[LJ-1.5]` as registered aims at F1's
false target and must not be funded as planned.

## 2. THE ORTHODOX ROUTE, pinned from the corpus

The corpus pins TWO condensation engines, one per tower. The notes carry the
J-side engine in full and the Def-side engine only as a record; the fetched
Devlin ch. II text itself carries the Def-side derivation, and I read it there.

### 2.1 The Def-side chain: Devlin II.5 [LIT]

Source: the fetched scan's extraction, `_build/literature/dev2.txt`. The
chapter is "5. The Condensation Lemma. The GCH in L" (`dev2.txt:1066`).

| Step | Statement | Source |
|---|---|---|
| 5.1 | Tarski-Vaught at Σn: for amenable M and substructure N, `N ≺ₙ M` iff every nonempty Σn(N) subset of M meets N | `dev2.txt:1071` |
| 5.2 | Condensation: α limit, `X ≺₁ L_α` gives unique π, β ≤ α with (i) `π : X ≅ L_β`, (ii) π fixes transitive `Y ⊆ X` pointwise, (iii) `π(x) ≤_L x` | `dev2.txt:1148-1155` |
| 5.3 | The definable hull: M = the elements of L_α definable from X satisfies `M ≺ L_α`, smallest such | `dev2.txt:1329` |
| 5.4 | The hull's size: `\|M\| = max(\|X\|, ω)`, by counting formulas | `dev2.txt:1357` |
| 5.5 | Subsets appear early: V=L, κ a cardinal, `x ⊆ L_α` for α < κ gives `x ∈ L_κ` | `dev2.txt:1373` |
| 5.6 | V=L implies GCH: `P(κ) ⊆ L_{κ⁺}` and `\|L_{κ⁺}\| = κ⁺` | `dev2.txt:1386` |
| 5.7-5.8 | Relativization: `ZF ⊢ GCH^L`; Con(ZF) → Con(ZFC+GCH) | `dev2.txt:1394,1403` |

Three mechanisms inside the chain, each load-bearing:

1. **The certified level formula.** The 5.2 proof takes from II.2.7 a Σ₀
   formula `Φ(z, v, γ)` with: meta-level truth of `∃z Φ` says exactly
   `v = L_γ`, and satisfaction of `∃z φ` inside `L_α` matches it
   (`dev2.txt:1186-1194`). II.2.7 defines `H(x, α)` as
   `∃f [G(f, α) ∧ x = f(α)]`, where `G` is the graph of the FULL level
   recursion, Def-step included, and proves it uniformly Δ₁ (`dev2.txt:682-686`,
   with `G` from 2.4-2.6 at `:663-676`). The witness `z`/`f` bundles the level
   sequence with its certifying data. **The successor clause is inside the
   certified matrix.** The proof then runs Σ₀ absoluteness (1.9.15) at the
   transitive collapse in BOTH directions (`dev2.txt:1200-1290`).
2. **The definable hull with least witnesses.** 5.3's proof verifies Tarski's
   criterion by choosing, for each formula, the `<_L`-least witness:
   `φ(v₀) ∧ ∀v₁(v₁ <_L v₀ → ¬φ(v₁))` (`dev2.txt:1340-1350`). So the
   literature's hull IS a least-witness hull over the definable well-order.
3. **The collapse for an extensional substructure.** 5.2 first shows X is
   extensional from `X ≺₁ L_α`, then applies the Collapsing Lemma 1.7.1 to the
   NON-transitive X (`dev2.txt:1173-1183`). Clause (ii), the transitive-fixing
   clause, is what 5.5 spends: `L_α ∪ {x}` is a transitive subset of M, so π
   fixes it, so `π(x) = x` (`dev2.txt:1378-1380`).

Caution [LIT]: the II.5 scan is OCR-degraded, and the Wilkie-Stanley errata
inventory covers chapters I and VI, not II.5 (`devlin-errata.md:41`,
`digest.md:513-518`). But II.2.7's Δ₁ claim rests on the I.9 satisfaction
machinery, which IS errata territory: Sat has no correct Δ₁ version inside BS
and needs the cure systems (`devlin-errata.md:117-122`, WS 10.18/10.23). Our
ambient theory is strong, so the errata bind the internalized layer only
(`digest.md:416-421`). The lesson stands: the Δ₁-ness of a Def-side level
formula is exactly satisfaction internalization, and it is the step Devlin
himself got wrong once.

### 2.2 The J-side engine: SZ 1.16 [LIT]

Condensation lives at Σ₁: a Σ₁-preserving embedding of a transitive M̄ into a
J-structure makes M̄ a J-structure (`j-hierarchy.md:88-101`, SZ Theorem 1.16).
Its three dependencies: rud closedness, the uniform Σ₁ definition of the
S-sequence (SZ 1.10), and the Σ₁ Skolem function (SZ 1.15)
(`j-hierarchy.md:103-113`, `digest.md:341-344`). The proof pulls the hierarchy
back along π and runs Lemma 1.10 in both directions (`j-hierarchy.md:99-101`).
"x = S_γ" is Σ₁ by a formula independent of α (`j-hierarchy.md:69-71`). The
S-step is the sixteen-function image step (`j-hierarchy.md:50`), so the
successor content of the J-side level formula is structural and syntax-free.
SZ do NOT derive GCH in the fetched chapter; they stop at acceptability as "a
strong version of GCH" (`j-hierarchy.md:151-161,183-195`, `digest.md:255-261`).

### 2.3 What the two engines share [INF, from LIT]

Both engines certify a level formula whose successor clause is real content.
Devlin pays for it with internalized satisfaction. SZ pay for it with the
sixteen op-graphs. No fetched text certifies a level formula with the
successor clause dropped. This is D-26's dichotomy appearing at the level
formula rather than at the well-order, and it decides section 7's F1.

## 3. STEP BY STEP

One row per phase-1 item. "Matches" means: same mathematical object, at the
literature's generality, or stronger.

| Item | Literature step | Verdict | Notes |
|---|---|---|---|
| `[LJ-1.1]` recon route | II.5 chain | MATCHES in skeleton | Blocks 1-6 map onto 5.3/5.4, 5.2(i,ii), 5.2's engine, 5.4+cardinality, 5.5, 5.6. Nothing skipped, nothing merged. One wrong citation (section 4, DEV-5; section 7, F5) |
| `[LJ-1.3]` hull | 5.3 + 5.4's counting shape | MATCHES, with an owed leg | Least-witness search IS 5.3's mechanism (`dev2.txt:1340-1350`). The hull-as-sett over formula pairs serves 5.4's counting directly. The elementarity AT HULL PARAMETERS is owed, priced, and carries a hidden cost (F3) |
| `[LJ-1.4]` collapse | 5.2(i)(ii) via 1.7.1 | MATCHES in part; one half misses the target | `π`, `πX-trans`, `fixes` match and `fixes` closes a gap the archive had. The injectivity/iso half is hypothesized on a transitive carrier and misses 5.2's object (F2) |
| `[LJ-1.2]` gate | II.2.7's certification | SOUND probe, correct NO-GO | The probe asked the right question. The NO-GO is what II.2.7 read with the errata predicts: the Def-side certificate needs satisfaction internalization |
| `[LJ-1.10]` route C | no literature analogue | DEVIATES, and the deviation is unsound | No fetched engine drops the successor clause. The recognition target is false (F1) |
| `[LJ-1.5]` planned | 5.2's engine | DEVIATES as registered | The row builds route C. Blocked by F1 until re-targeted |
| `[LJ-1.6]` planned | `\|L_α\| = \|α\|` (Devlin 1.1(vii), consumed at `dev2.txt:1380-1383`) | MATCHES | The archived chain (Count, predicates, pairing, square law, bound) is standard cardinal arithmetic. The square law's seconds risk is a threshold matter, flagged |
| `[LJ-1.7]` planned | 5.5 | MATCHES | Stated at κ⁺ over subsets of Lset κ, which is 5.6's instance of 5.5. Consumes the initial-ordinal fact, on no row, flagged by `[LJ-1.1]` §7.1 |
| `[LJ-1.8]` planned | 5.6 + internal statement | MATCHES plus formalization-specific content | The internal GCH sentence has no literature analogue and needs none; DD2 requires it |

An agreeing result, stated plainly: apart from route C, the phase's route IS
the literature's route. The recon reached Devlin's chain through the archive
without reading the corpus, because the archive itself was built on Devlin.
The agreement is real and I did not manufacture deviations to fill this table.

## 4. DEVIATIONS

Each deviation gets both tests. THRESHOLD: DD5's suspended relative
constraints, DD5 measure 1's a-priori ceiling (8.0-10.8k, `[LJ-1.1]` §6,
fixed), DD24's ratio bar 0.007693 s/line with tolerance 1.15. DD: the ruling
must actually say what is claimed.

### DEV-1. Hull by meta-level least-witness search, not by internal Skolem functions

[REP] `[LJ-1.3]` §2-3; archive design note (`archive/rud-route/src/L/Hull.lagda.md:5-9`).
[LIT] Devlin 5.3 chooses least witnesses in the object language via `<_L`;
SZ 1.15 builds an internal Σ₁ Skolem function.
[INF] The delivered hull computes the least witness at the meta level
(`src/L/Hull.lagda.md:235-237`, `leastOf` over `orderAt`). The OBJECT is
Devlin's: the set of least witnesses equals the set of X-definable elements,
once the leastness is encoded internally. That encoding is the owed piece
(`_build/lj-1.3-report.md` §6, 80-150 lines).

- THRESHOLD: PAID. Delivered 343 lines in band 340-540; measured 0.00700
  s/line, 0.91x the bar (`_build/lj-1.3-report.md` §5). Warm-cache protocol,
  self-flagged, re-measure scheduled.
- DD: PAID. DD13's port-vs-fresh comparison is in §2. DD4's generic claim
  checks against the code: `α`, `X` are module parameters
  (`src/L/Hull.lagda.md:57,190`); the one fixed atom is named and isolated
  (`:341-428`). P-l checks: `Lset` is opaque upstream
  (`src/L/Constructible.lagda.md:221`), so the abstract stage is an atom.
- VERDICT: JUSTIFIED. Residual risk in F3, which is a pricing gap, not a
  missing reason.

### DEV-2. Collapse carrier-generic over the HIT, no extensionality hypothesis

[REP] `[LJ-1.4]` §1-3. [LIT] Devlin 1.7.1 collapses an extensional X.
[INF] Defining π by ∈-recursion over the whole hierarchy is stronger and
cleaner than the literature's statement, and it is the right generic shape.
The deviation is fine; what is missing is one instance (F2).

- THRESHOLD: PAID. 239 lines in band 230-330; 0.00798 s/line inside tolerance
  (`_build/lj-1.4-report.md` §5).
- DD: PAID. DD13 comparison in §2; DD4 generic with carrier a module
  parameter; the fixing clause D-10-checked at its generality (§4).
- VERDICT: JUSTIFIED as delivered, but see F2: the injectivity half is
  instantiated at the hypothesis that trivializes it.

### DEV-3. Route C: the ⊤̇-step structural story as the crossing's vehicle

[REP] `_build/lj-1.10-reprice.md` §1, §4. [LIT] section 2.3 above: both
engines carry the successor clause; none drops it.

- THRESHOLD: CLAIMED, NOT REAL. `[LJ-1.10]` §5 keeps the wing at 8.0-10.8k by
  keeping the crossing at 0.7-1.72k. That figure prices the transfers and
  equivalence legs of a target that is false (F1), so the threshold reason
  evaporates with the target. The honest crossing price is route A's 1.7-3.8k
  band or an unpriced iso-commutation route, and the wing then crosses the DD5
  measure-1 ceiling. `[LJ-1.10]` §5 itself states the rule: the ceiling does
  not move, and the gap is the finding.
- DD: MISSING. No ruling licenses building toward a classically false lemma.
  D-10 (`dev/LESSONS.md:1302-1348`) commands the opposite: price the truth of
  a residue before pricing its proof, and truth-check the CHAIN'S ROOT.
  `[LJ-1.10]` D-10-checked the 5,047 anchor (§2.2) but never D-10-checked its
  own route's load-bearing equivalence. The archive had the warning on file:
  `[T130]` states the crossing's story "would have to carry at the class level
  the internalized definable-powerset step"
  (`_build/l3.32-t130-report.md:26-33`), and `[LJ-1.10]` cites T130's row
  without applying it.
- VERDICT: NOT JUSTIFIED. Both reasons fail. Full mathematics in F1.

### DEV-4. The internal GCH statement via certified predicates

[REP] `[LJ-1.1]` block 6, T257 §3.4. [LIT] Devlin states GCH meta-level; no
analogue. [INF] DD2 rules the trophy "stated in L", so the internal statement
is required content, not a deviation from the route.
- THRESHOLD: priced (150-350, survey). DD: DD2 licenses it directly.
- VERDICT: JUSTIFIED.

### DEV-5. Phase-1 briefs cite Devlin by number with the corpus unopened

[REP] The recon cites "Devlin 5.3 to 5.6", "5.2(ii)", "VI.2.4", "VI.4.1"
(`_build/lj-1.1-recon.md` §1, §3); the builds cite "Devlin 5.2(ii)". None
cites `dev/literature/`. [INF] I checked every number against the fetched
text. "5.2(ii)", "5.3 to 5.6", "VI.2.4" are right. "VI.4.1" is wrong: it is a
projectum lemma (`_build/literature/dev6.txt:2301`), not the condensation
warrant. The intended citation is II.5.2 (`dev2.txt:1148`) or VI.2.9
(`dev6.txt:1844`).
- THRESHOLD: n/a. DD: DD18's literature half postdates the briefs
  (2026-08-10), so no ruling was broken. The mis-citation is the cost of
  working from memory in errata territory, which `devlin-errata.md` exists to
  prevent.
- VERDICT: the deviation is excused by timing; this review is the compensating
  pass DD18 now mandates. One wrong citation found; the mathematics it
  vouched for is nonetheless true (II.5.2).

### DEV-6. DD4 across the wing: where genericity is applied and skipped

[REP] Both chapters claim fully generic, one named atom. [INF] Checked
against the code, the claims hold (DEV-1, DEV-2). The harder question: the
literature suggests the SHARED core of the two proofs is the hull, the
collapse, the counting chain, and the Tarski-Vaught equivalence, because both
towers consume them unchanged. Phase 1 built exactly those first, generic.
That is DD4 applied where it pays. The level formula is the one place
genericity CANNOT be shared across the towers, because D-26 makes the two
step clauses different content. The parameter-free story axis
(`archive/rud-route/src/L/Condensation.lagda.md:330-604`) is genuinely shared
substrate, but only for the clauses BOTH towers keep; the successor clause is
per-tower by structure. No finding; the wing's generic/fixed split is the one
the literature supports.

## 5. WHAT THE LITERATURE WOULD HAVE CHANGED

Concrete instances, ranked.

1. **Route C would not have been proposed in its delivered form.** Devlin
   II.2.7 plus the errata's Sat inventory show the Def-side level formula's
   certificate IS satisfaction internalization. A reader of `digest.md:508-520`
   and `devlin-errata.md:117-122` prices the substrate as the orthodox cost
   from day one. The NO-GO then arrives as confirmation, not surprise, and the
   re-price step compares route A against the J-side directly.
2. **The probe's GO criterion would have been written differently.**
   `[LJ-1.1]` §5 set GO at "all clauses certify at ≤ 25 lines". The
   literature says the step clause certifies only through the bundled witness
   (II.2.7's `G`), so the criterion would have separated the structural
   clauses, expected cheap, from the step clause, expected to need the
   substrate. Same probe, sharper read-out, one dispatch saved.
3. **F2 would likely have been caught at build time.** Devlin 5.2's proof
   opens by deriving extensionality of X from `X ≺₁ L_α` and collapsing the
   NON-transitive X (`dev2.txt:1173-1183`). A builder with that page open
   does not park injectivity under a transitivity hypothesis without flagging
   the gap.
4. **The D-26 evidence for `[LJ-2.5]` would be stronger.** SZ 1.10/1.16 is a
   literature-level confirmation that the J-side certification is structural
   and syntax-free. `[LJ-1.10]` §6 argues this from project measurements
   alone; the citation was available and would have anchored it.
5. **One citation error avoided** (DEV-5).

What the literature would NOT have changed: the hull design, the collapse's
generic shape, the block order, the counting chain, and the decision to state
GCH internally. Those match already.

## 6. IS THE CORPUS SUFFICIENT for [LJ-1.5] to [LJ-1.9]

Not yet, and `[LJ-0.7]` as registered closes most but not all of the gap.

1. **Devlin II.5's derivation is in the fetched text but not in the notes.**
   The notes record its existence (`digest.md:513-518`); no note carries the
   chain. `[LJ-0.7]` is registered to digest it and gates `[LJ-1.5]`
   (`dev/PLAN.md:426-427`). Right task, right gate. Its scope should name:
   5.1 through 5.11 INCLUDING the special cases 5.9-5.11 (`dev2.txt:1409,
   1425, 1437`), because 5.10-5.11 are the cheap condensation instances a
   formalization may prefer for the wing's single application.
2. **II.2.4-2.7 must enter the digest with II.5.** The condensation proof
   consumes `Φ` from 2.7 (`dev2.txt:1186`), and 2.7's Δ₁ proof is where the
   satisfaction internalization sits. A digest of II.5 without 2.7 records the
   consumer and omits the engine. This is the gap that fed F1.
3. **Devlin II.1.1(vii), `|L_α| = |α|`, is consumed at `dev2.txt:1380-1383`**
   and is the target of `[LJ-1.6]`/block 4g. It is in the fetched ch. II but
   in no note. Add it to `[LJ-0.7]`'s scope.
4. **The OCR caution stands.** II.5 is legible in `dev2.txt` for statements
   and proof skeletons; single glyphs are corrupt throughout. The errata
   inventory does not cover II.5 (`devlin-errata.md` covers I.9, II amenability
   remarks, VI.1). `[LJ-0.7]` should cross-check 5.2's proof against Jech 13
   (fetched, typed PDF, `jech13.txt`) where the glyphs are in doubt.
5. **For `[LJ-1.8]` nothing is missing:** the internal statement is
   formalization-specific.
6. **For `[LJ-2.5]`'s use of phase-1 evidence:** the J-side comparison rests
   on T84's and T263's figures, which are archive records, not literature. The
   corpus supports the direction (section 2.2); no fetched text prices either
   side. See F4.

## 7. MATHEMATICAL DEFECTS

Ranked. F1 and F2 outrank every process observation in this report.

### F1. Route C's recognition target is classically false [INF, against LIT]

**The target.** `[LJ-1.10]` §1 rules: port the archived structural story and
prove its equivalence against the delivered description
(`_build/lj-1.10-reprice.md:8-15`). The story is `levelStory = Ap ∧̇ (Cl ∧̇ Rg)`
with `Cl = ⊤̇` (`archive/rud-route/src/L/Condensation.lagda.md:585-604`). Its
clauses say: f is a set of Kuratowski pairs (`:487-491`), single-valued
(`:520-525`), with `pr a a ∈ f` for a memberless a (`:529-534`), first
components an ordinal (`:498-517`), continuous at limit indices (`:563-575`),
and the read member is a value of f (`:578-582`). The successor clause says
nothing.

**The counterexample.** Take `f₀ = {pr ∅ ∅, pr 1 w}` for ANY set w. Every
clause holds ambiently: both members are pairs; first components 0 and 1 are
distinct, so single-valuedness holds; `pr ∅ ∅ ∈ f₀`; {0, 1} is an ordinal;
no first component is a limit, so continuity is vacuous; `Cl = ⊤̇`; w is a
value. So the story believes `f₀` with value w at index 1, while
`Lset 1 = 𝒟ₒ(∅) = {∅}`. Choose any constructible `w ≠ {∅}`: the story is
satisfied at every carrier containing the (constructible, hereditarily small)
data, and the recognition conclusion `v ≡ Lset b` is false. The story is
strictly weaker than level-hood at successor indices, at the ambient reading,
at the class carrier's inner reading, and at any transitive set carrier. In
particular the collapsed image N of the wing's hull contains such `f₀` as soon
as N is infinite, so the crossing hypothesis `CrossOut` for this story
(`archive/rud-route/src/L/Condensation.lagda.md:168-171`) is refuted at the
exact carrier the wing needs it.

**Why no repair inside route C exists.** The story is parameter-free by
design, so that `embed` moves it between carriers
(`archive/.../Condensation.lagda.md:303-315`). Binding the witness to a
constant set K of true level sequences (the `con K` shape in T51 §4,
`_build/l3.32-t51-report.md:277-279`) restores adequacy at the class carrier
and destroys it at the collapsed image, because π does not preserve K's
meaning. Parameter-free is too weak; parameter-bound does not transfer. The
gap is exactly the successor content, and D-26 names its price on this tower:
codes, an order on codes, and satisfaction (`dev/LESSONS.md:1662-1674`).

**What the literature says [LIT].** Devlin's engine certifies the FULL
recursion: `H(x, α) = ∃f[G(f, α) ∧ x = f(α)]` with G the level-sequence graph
including the Def clause (`dev2.txt:679-686`). SZ's engine certifies
"x = S_γ" with the sixteen-op step inside (`j-hierarchy.md:69-71,50`). No
fetched text certifies a level formula whose successor clause is trivial.

**What the archive already said [REP].** T130, verdict item 2: the story the
crossing rides "would have to carry at the class level ... the internalized
definable-powerset step, which the rud side does not have"
(`_build/l3.32-t130-report.md:26-33`). The archived chapter itself never
claims the story recognizes levels: it takes `CrossOut` as a hypothesis and
lists the equivalence among the obligations left standing
(`archive/.../Condensation.lagda.md:857-882`). The false step is
`[LJ-1.10]`'s alone: it substituted the weak story into an equivalence slot
that `[LJ-1.1]`'s probe spec had reserved for a FAITHFUL bounded rewrite of
the delivered description (`_build/lj-1.1-recon.md` §5, statement 2), and the
shared name `σL` masked the substitution.

**Internal inconsistency in `[LJ-1.10]` [REP].** Its §6.3 concedes the J
tower's story needs its bounded step clauses, 470-610 lines plus sixteen
unmeasured op-clauses (`_build/lj-1.10-reprice.md:296-301,305-310`). Its §4
proposes the Def tower's story with NO step content at all. The same report
requires the successor clause on one tower and drops it on the other.

**Consequence.** `[LJ-1.5]` as registered (`dev/PLAN.md:427`) builds toward
F1's target and must be re-targeted before funding. The honest crossing price
reverts to route A's 1.7-3.8k band (`_build/lj-1.10-reprice.md` §2.3), or to
an alternative that nobody has priced: prove `π(Lset δ) = Lset(π δ)` by
induction along the collapse, consuming satisfaction iso-invariance
(T51's 0.08-0.14k, `_build/l3.32-t51-report.md:173-191`) plus code-fixing
under π plus Def-commutation. Both alternatives carry the successor content;
they relocate it. DD5 measure 1 then applies: the ceiling stays at
`[LJ-1.1]`'s 8.0-10.8k, the wing's honest projection moves above it, and the
gap is recorded as a finding, exactly as `[LJ-1.10]` §5 states the rule.

### F2. The delivered collapse's injectivity half misses the condensation target [INF, against LIT]

The `Inj` module hypothesizes `Xtr : isTrans X` and everything downstream
lives inside it: `π-inj`, `π∈-bwd`, `iso`, `Mostowski`, `mostowski`
(`src/V/Collapse.lagda.md:109,170-205`). But for a transitive carrier the
chapter itself proves the collapse is the identity:
`fixes-X : isTrans X → ∀ y ∈ᵗ X → π y ≡ y` (`src/V/Collapse.lagda.md:272-273`).
So the delivered Mostowski package holds only where it is trivial. The
condensation step collapses the HULL, which is not transitive
(`_build/lj-1.3-report.md` §4), and Devlin 5.2 collapses an EXTENSIONAL
substructure, deriving extensionality from `X ≺₁ L_α` (`dev2.txt:1178-1183`).
The extensional-carrier injectivity, and the backward membership direction
that rides it, are neither delivered nor priced in any block: block 2's
statement says "for a transitive set carrier X" (`_build/lj-1.1-recon.md`
block 2), and block 3's sub-blocks do not carry a collapse item. The delivered
`in⊆`/`out⊆` proofs pull members of x into X through `Xtr`
(`src/V/Collapse.lagda.md:115-155`), which is false at a non-transitive
carrier, so the proof shape does not adapt by weakening a hypothesis; it needs
the structure-extensionality argument. Estimated cost is one ∈-induction of
the same size class as `Inj`, roughly 80-200 lines [INF, survey]; the point is
not the size but that the reports read as if the collapse leg were closed.
What stays sound: `π`, `π-compute`, `πX`, `πX-trans`, `π∈-fwd`, `unique`, and
`fixes` are delivered without `Xtr` and match the literature, and `fixes` is
exactly 5.2(ii).

### F3. The hull's elementarity leg needs a TV theorem the tree does not have [INF]

`TV-thm` requires a transitive carrier: `TV→elem`'s bounded-quantifier cases
spend `Mtr` (`src/L/Hull.lagda.md:70,142-181`). Devlin 5.1 needs no
transitivity of N (`dev2.txt:1071`). The hull is not transitive, so the
condensation block must either re-prove the equivalence at a non-transitive
carrier, routing the bounded cases through the unbounded criterion, or work
with hull parameters reduced to X-parameters by the leastness encoding, which
is Devlin 5.3's implicit substitution step. `[LJ-1.3]` §6 prices the three
standing pieces at 210-430 lines total but does not name the non-transitive
TV gap inside piece three. Not a false claim anywhere, the report is honest
that the leg is open; the price is the risk. [REP for the residue; INF for
the gap inside it.]

### F4. The D-26 asymmetry claim is directionally right and quantitatively unsupported [INF]

The coordinator ordered this tested. The claim (`_build/lj-1.10-reprice.md`
§6, imported into DD2's row, `dev/PLAN.md:161`): level-story certification is
a few hundred lines on the J tower and substrate-scale on the Def tower.

- The DIRECTION holds, on three independent legs. D-26's measured mechanism
  (`dev/LESSONS.md:1662-1687`). `[LJ-1.2]`'s probe: the blocker is the
  satisfaction leaves' quantifier structure, generic in the carrier
  (`_build/lj-1.2-gate.md` §3). The literature: SZ's Σ₁ engine exists
  because the S-step is finitely generated and syntax-free (section 2.2),
  while Devlin's Def-side engine pays satisfaction internalization
  (section 2.1). This review ADDS the third leg; phase 1 had only two.
- The MAGNITUDE is not measured. The J-side figure conflates two sources:
  T84's 470-610 priced the bounded layer for the SIX structural clauses
  (`_build/l3.32-t84-report.md:33-36`, route b), and T263 calls the sixteen
  op-graph clauses "new and unmeasured" while failing all sixteen delivered
  formulas at Δ₀ (`_build/l3.32-t263-fof.md`, PLAN row
  `archive/dev/TASKS-archived.md:268`). The Def-side figure, route A's
  1.7-3.8k, is a survey band. If the sixteen clauses land near the archive's
  ~40-line decode rate, the J side totals roughly 1.1-1.25k against the Def
  side's 1.7-3.8k: a real gap, but nearer 2x than "hundreds against
  thousands". DD2's row states the 470-610 as if it covered the J-side story
  whole; it does not.
- What would strengthen it for `[LJ-2.5]`: run the queued T261-class probe on
  the current tree; price one bounded op-clause and multiply by sixteen; then
  restate the asymmetry with both sides on measured rates. Also state D-26's
  extension explicitly: the law's text is about well-ordering, and phase 1 now
  applies it to level-hood. The extension is sound, same root cause, but it
  should be recorded as an extension, with `[LJ-1.2]`'s probe as its
  measurement.

### F5. Minor: the recon's condensation warrant cites the wrong theorem

"Devlin VI.4.1 is a classical ZF theorem" (`_build/lj-1.1-recon.md` §3).
VI.4.1 is a projectum lemma (`dev6.txt:2290-2301`). The true warrant is
II.5.2 (`dev2.txt:1148`) or VI.2.9 for the J-hierarchy (`dev6.txt:1844`).
The warranted CLAIM is true, so nothing downstream breaks. Ranked last.

## 8. LITERATURE USED

- `dev/literature/digest.md`: read in full. Took: the orthodox form Q1-Q7;
  the GCH-derivation record at :508-520; the acceptability complement
  :255-261; the errata scoping note :416-421; section 4 items 7-8.
- `dev/literature/j-hierarchy.md`: read in full. Took: SZ 1.16 with proof
  shape and dependencies (section 2); the S-step and uniform Σ₁ (:50,69-71);
  the no-GCH-in-SZ note (:183-195).
- `dev/literature/devlin-errata.md`: read in full. Took: the Sat inventory
  :117-122; the coverage bound (chapters I and VI, not II.5); checklist items
  1, 4, 7.
- `dev/literature/primary-sources.md`: read in full. Took: what the Dev/Jech/JM
  fetches contain; the OCR caveats; Jech 13.14's Δ₁ statement as the
  cross-check anchor (:264-266).
- `_build/literature/dev2.txt` (fetched Devlin ch. II, the corpus's own
  artifact): read II.2.4-2.9 and II.5 in full. Took: the whole of section 2.1
  and the F1/F2 literature legs. This is the review's primary source; the
  notes record it but do not carry it.
- `_build/literature/dev6.txt`: consulted for VI.2.9 and VI.4.1 (F5).
- `dev/literature/BIBLIOGRAPHY.md`: NOT read beyond its role in digest
  citations. WHY NOT: the review needed content, not provenance chains, and
  `primary-sources.md` carries the fetch map.
- `dev/literature/fine-structure.md`: NOT read. WHY NOT: master codes and
  projecta enter no phase-1 block; the wing stops before fine structure.
- `dev/literature/formalizations-landscape.md`: skimmed via digest section 6.
  Took: the GCH-in-L virginity verdict as context. WHY NOT deeper: prior art
  bears on no deviation judged here.
- `dev/literature/rudimentary-functions.md` and `owner-notes-rud.md`: NOT
  read in full. WHY NOT: the J-side comparison needed only the S-step's
  structural character, which `j-hierarchy.md:50` and `digest.md` section 3
  already pin; the basis-choice fork is phase-3 material.
- `dev/literature/geology.md`, `glossary-review-2026-08.md`,
  `terms-2026-08.md`, `formalizations.md`: NOT read. WHY NOT: out of scope
  for a route review (geology, terminology, and the landscape's superseded
  half).

## 9. ARCHIVE USED

- `archive/rud-route/src/L/Condensation.lagda.md`: read in full (886 lines).
  Took: the story's six clauses and `Cl = ⊤̇` (:487-604) for F1's
  counterexample; `CrossOut`-as-hypothesis (:168-171, :208-224); the
  parameter-free axis (:303-315); the D32 recap (:857-882). The review turned
  on this file, as the brief said it would: it is NOT the literature's object,
  it is the literature's object minus the successor clause, and the file
  itself is honest about what it left standing.
- `archive/rud-route/src/L/Hull.lagda.md`: compared against the delivered
  port. Took: the design note (:5-9) and the module shapes for DEV-1.
- `archive/rud-route/src/V/Collapse.lagda.md`: compared via `[LJ-1.4]` §6's
  line map. Took: the absence of the fixing clause, confirming the delivered
  chapter's addition.
- `archive/dev/TASKS-archived.md`: rows read at :86 (T51), :119 (T84 STOP
  D-10), :126 (T91), :163 (T128), :165 (T130), :262 (T257), :264 (T259),
  :266 (T261 QUEUED), :268 (T263). Took: the STOP and QUEUED states that
  F1 and F4 turn on.
- `_build/l3.32-t51-report.md`: read in full. Took: the four transfer
  obligations as types (:50-55); the D-10 correction that raw transfers are
  unsound targets (:127-141); the iso-invariance pricing (:173-191); the
  probe spec with `Cl = ⊤̇` and `con K` (:256-282), which is where the weak
  story entered the pipeline unexamined.
- `_build/l3.32-t130-report.md`: read sections 1-2. Took: verdict item 2
  (:26-33), the archived anticipation of F1.
- `_build/l3.32-t84-report.md`: read section 1 and 2.1. Took: the 470-610
  route-b price and WHAT it covers (six clauses, not sixteen), for F4.
- `_build/l3.32-t263-fof.md`: read the per-function verdicts (:80-115). Took:
  all sixteen delivered formulas fail Δ₀; the pass is set-level and
  conditional, for F4.
- `dev/LESSONS.md`: D-10 (:1302-1361), D-26 (:1662-1687), P-l (:2099-2158),
  C-22 (:2031). All four bind this review and are applied above.
- `dev/PLAN.md`: sections 0 (:35-115), 3 (:153-174), 11 (:306-447). Took:
  DD2/DD4/DD5/DD8/DD13/DD17/DD18/DD23/DD24 texts for section 4; the LJ rows;
  DD2's imported D-26 claim for F4.

## 10. WHAT I AM NOT SURE OF

1. **F1's counterexample against an unseen assembly.** The archived file
   never assembles the story into the two-slot level-hood formula; the
   crossing section is deleted. I refuted every assembly that pins values
   only through the six clauses plus domain-exactness. A future assembly that
   smuggles successor content back in would evade the counterexample, and
   would then face `[LJ-1.2]`'s NO-GO on that content. The dichotomy is the
   claim I am sure of; the exact doomed formula is not on disk to point at.
2. **F2's cost.** The 80-200 line estimate for extensional-carrier
   injectivity is my survey figure, unprobed. P-l forbids transferring the
   delivered `Inj`'s cost by analogy; a one-lemma probe would price it.
3. **The iso-commutation alternative in F1's consequence.** I did not find a
   fetched text that runs condensation through `π(Lset δ) = Lset(π δ)`
   without a certified level formula; Devlin 5.2(iii) uses `<_L`'s uniform
   Σ₁-ness, which is again certified content. If such a route exists, it
   would change F1's consequence, not F1 itself.
4. **The J-side magnitude in F4.** My 1.1-1.25k reconstruction multiplies an
   archived decode rate by sixteen. It is exactly the kind of
   analogy-anchored figure P-l warns about, and I present it only to show the
   spread of the unmeasured band, not as a price.
5. **OCR fidelity of II.5's proof details.** I trust the statement-level
   chain in `dev2.txt`; glyph-level details (for example 5.2(iii)'s exact
   inequality) I read through degradation. `[LJ-0.7]` should confirm against
   Jech 13 where it matters.
6. **DD24 measurements.** Both delivered ratios come from warm-dependency
   protocols, self-flagged in the reports. The scheduled cold run decides;
   I did not run Agda, per the brief.
