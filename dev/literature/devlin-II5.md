# Devlin II.5: the Condensation Lemma and the GCH in L

Task `[LJ-0.7]`. Primary source: `_build/literature/dev2.txt`, the OCR of
Devlin, "Constructibility" (1984), Chapter II. Cite it as `dev2.txt:NNNN`.
Cross-check source: `_build/literature/jech13.txt`, the typed PDF of Jech,
"Set Theory" (3rd ed.), Chapter 13. Cite it as `jech13.txt:NNNN` with the
printed page number where relevant.

Reading instruction (DD4, D-26): for each step of II.5, this digest asks
whether the step needs a property of the Def tower only, or whether the J
tower would supply the same property. D-26 asks which carrier the step leans
on: syntax (Def tower) or generation data (J tower).

## 0. What the corpus already had, and what this digest adds

Existing coverage, checked before writing:

- `digest.md:513-518` records that Devlin ch. II section 5, "The Condensation
  Lemma. The GCH in L", was fetched, with Theorem 5.6 as the sourced
  GCH-in-L derivation. It carries no part of the chain. This digest adds the
  chain.
- `j-hierarchy.md` section 2 carries the J-side engine (SZ 1.16) in full,
  with its dependencies (rud closedness, uniform Σ₁ of the S-sequence,
  Σ₁ Skolem functions). The Def-side engine existed only as a record; this
  digest adds it (sections 1 to 3).
- `fine-structure.md` and `rudimentary-functions.md` reference lemmas named
  "5.2", "5.3" and "5.4", but those are SZ projecta and reducibility lemmas
  (SZ pp. 32-34), not Devlin II.5's items. There is no overlap to extend;
  the numbering coincidence is noted so no later reader pays twice.
- `devlin-errata.md` scopes the WS inventory to Chapter I.9 and Chapter
  VI.1 (`devlin-errata.md:41-42`), with a short Chapter II list that does
  not reach II.5 (`devlin-errata.md:125-140`). Section 7 of this digest
  keeps that boundary.
- `primary-sources.md` records the fetch map and the OCR caveats for the
  Dev chapters (`primary-sources.md:26-34`).
- `BIBLIOGRAPHY.md` entries 13 (Devlin) and 18 (Jech) predate the second
  fetch round and still read cite-only; this task's BIBLIOGRAPHY rows
  record the fetched artifacts.

## 1. THE SPINE: 5.1 to 5.8

### 1.1 5.1: Tarski-Vaught at level n

The section opens at `dev2.txt:1066`. 5.1 is a lemma about elementary
substructures of an amenable structure. The OCR statement, with glyphs
restored where the context is unambiguous:

> 5.1 Lemma. Let M = ⟨M, ∈, A₁, ..., Aₙ⟩, where M is an amenable set, and let
> N = ⟨N, ...⟩ be a substructure of M. Let n > 0. The following are
> equivalent:
> (i) N ≺ₙ M;
> (ii) if A is a non-empty Σⁿ₁(N) subset of M, then A ∩ N ≠ ∅.
> (`dev2.txt:1071-1078`)

The OCR prints the hypothesis "amenable" legibly and the class "Σj1(N)" in
degraded glyphs (`dev2.txt:1074`); the proof's own usage ("φ(x, y) is a Πₙ₋₁
formula", "3yφ(x, y) is a Σₙ formula") pins the class as Σ₁ with a Πₙ₋₁
matrix, parameters from N. See section 6 for the OCR note.

The proof is in `dev2.txt:1080-1130`. Both directions are shown by induction
on formula length. The (i) to (ii) direction uses the amenability hypothesis
of M; the (ii) to (i) direction uses the hypothesis on A with a witness
choice. 5.1 is proved in the chapter, not assumed. Its role in the spine is
to license the equivalence between elementarity and the "every definable
non-empty set meets the substructure" criterion, which 5.3 uses in its
Tarski-criterion form.

### 1.2 5.2: the Condensation Lemma

The statement, quoted from the scan and restored where the scan is degraded:

> 5.2 Theorem (The Condensation Lemma). Let α be a limit ordinal. If
> X ≺₁ L_α, then there are unique π and β such that β ≤ α and:
> (i) π : ⟨X, ∈⟩ ≅ ⟨L_β, ∈⟩;
> (ii) if Y ⊆ X is transitive, then π ↾ Y = id ↾ Y;
> (iii) π(x) ≤_L x for all x ∈ X.
> (`dev2.txt:1148-1155`; part (iii)'s inequality restored from the proof,
> see section 6)

The object X is an EXTENSIONAL substructure, not a transitive one. The proof
derives extensionality of X from X ≺₁ L_α (`dev2.txt:1173-1183`):

> Note first that X is extensional. For suppose that x, y ∈ X, x ≠ y. Then
> ... so as X ≺₁ L_α, ... which means that for some z ∈ X, z ∈ x ↔ z ∉ y.
> Since X is extensional, by the Collapsing Lemma (1.7.1) there is a unique π
> and a unique transitive set M such that π : X ≅ M.
> (`dev2.txt:1173-1183`)

The 1.7.1 citation is to Chapter I, which is not in `dev2.txt`; it is the
Mostowski collapse of a well-founded extensional relation. See section 3.

The proof then shows M = L_β. The level-hood engine enters at
`dev2.txt:1186-1194`:

> By 2.7 there is a Σ₀ formula Φ(z, v, γ) of LST such that
> (a) ∀v∀γ [v = L_γ ↔ ∃z Φ(z, v, γ)]
> and moreover, if φ(z, v, γ) is the ℒ-analogue of Φ(z, v, γ), then (using
> 1.9.15)
> (b) (∀γ < α)(∀v)[v = L_γ ↔ v ∈ L_α ∧ L_α ⊨ ∃z φ(z, v, γ)].
> (`dev2.txt:1186-1194`)

The chain (c) to (q) then runs: for each ordinal γ of the collapse, the Σ₁
statement "∃v∃z φ(z, v, γ)" is transferred from L_α to X (Σ₁-elementarity,
downward) and along the collapse to M; 1.9.15 converts M's satisfaction of
the Σ₀ matrix into ambient Φ; (a) turns Φ into "v = L_γ", giving
L_γ ∈ M for every γ < β, hence ⋃_{γ<β} L_γ ⊆ M (`dev2.txt:1200-1240`).
The reverse inclusion M ⊆ ⋃_{γ<β} L_γ runs the same transfer on the
statement "∃γ∃v∃z(φ(z,v,γ) ∧ x ∈ v)" (`dev2.txt:1245-1290`). Finally
lim(α) implies lim(β) via the Σ₁ statement "∃τ(v < τ)", so
M = ⋃_{γ<β} L_γ = L_β (`dev2.txt:1290-1301`).

Part (ii) is one line: it follows from 1.7.1 (`dev2.txt:1302`). Part (iii)
supposes π(x) >_L x and takes the <_L-least such x₀; it uses 3.4(i)
(downward closure of <_L), the uniform Σ₁-ness of <_L at limit levels
(3.3(ii)), and the Σ₁-elementarity of π⁻¹ : L_β → L_α to transfer the
inequality and contradict minimality (`dev2.txt:1302-1319`).

### 1.3 5.3: the definable hull

> 5.3 Lemma. Let α be a limit ordinal, and let X ⊆ L_α. Let M be the set of
> all elements of L_α which are definable in L_α from elements of X. (i.e.
> a ∈ M iff for some formula φ(v₀) of ℒ_X, a is the unique element of L_α
> such that L_α ⊨ φ(a).) Then M ≺ L_α, and moreover M is the smallest
> elementary substructure of L_α which contains all elements of X.
> (`dev2.txt:1329-1335`)

The proof verifies Tarski's criterion by a least-witness argument over the
<_L order: for a formula φ(v₀), form
ψ(v₀) = φ(v₀) ∧ ∀v₁(v₁ <_L v₀ → ¬φ(v₁))
(`dev2.txt:1340-1350`, glyphs degraded in the OCR). The least witness is the
unique witness of ψ, so it is definable from the same parameters. The
smallestness half shows M ⊆ N for any X ⊆ N ≺ L_α (`dev2.txt:1351-1356`).

### 1.4 5.4: the counting

> 5.4 Corollary. Let α be a limit ordinal. For any X ⊆ L_α there is a unique
> smallest M ≺ L_α such that X ⊆ M. For this M, |M| = max(|X|, ω).
> (`dev2.txt:1357-1360`)

The proof is one line: the language ℒ_X has max(|X|, ω) many formulas, so
the hull M has at most that many definable elements (`dev2.txt:1360`). This
is the counting step that makes the hull small enough for the cardinal
argument in 5.5.

### 1.5 5.5 to 5.8: the GCH chain

> 5.5 Lemma. Assume V = L. Let κ be a cardinal. If x is a bounded subset of
> κ (or more generally if x ⊆ L_α for some α < κ), then x ∈ L_κ.
> (`dev2.txt:1369-1371`; the second clause's bound is "α < κ" per the
> printed page, section 6)

The proof (`dev2.txt:1372-1384`): pick α < κ with x ⊆ L_α; take a limit λ
with x ∈ L_λ; by 5.4 take M ≺ L_λ with L_α ∪ {x} ⊆ M and
|M| = |L_α|; collapse M to L_γ by condensation; L_α ∪ {x} is transitive, so
part (ii) fixes it pointwise, in particular π(x) = x; by 1.1(vii),
|L_α| = |α| and |L_γ| = |γ|, so |γ| = |M| = |α| < κ, hence γ < κ and
x ∈ L_γ ⊆ L_κ.

> 5.6 Theorem. V = L implies GCH.
> Proof. By 5.5, 𝒫(κ) ⊆ L_{κ⁺} for all infinite cardinals κ. So by 1.1(vii),
> ... The result follows at once.
> (`dev2.txt:1386-1388`)

The application of 5.5 in 5.6 is at the cardinal κ⁺ with α = κ: every
x ⊆ κ satisfies x ⊆ L_κ, and κ < κ⁺, so x ∈ L_{κ⁺}. 1.1(vii) gives
|L_{κ⁺}| = κ⁺.

5.7 and 5.8 are the relativization corollaries: ZF ⊢ (GCH)^L and, if ZF is
consistent, so is ZFC + GCH (`dev2.txt:1390-1406`).

## 2. WHAT THE ARGUMENT REQUIRES OF THE LEVEL STORY

This section answers the question `[LJ-1.12]` will ask. The question: the
`[LJ-1.2]` probe measured that the step clause of `LsetGraphAt` has no Δ₀
witness at any carrier, because its satisfaction leaves carry unbounded
existentials (`agents/reports/archive/lj-1.2-gate.md` section 2). Does Devlin's condensation
argument need such a witness? If it does, the crossing needs different
content; if it does not, the digest must say what it needs instead and at
what strength.

The short answer: Devlin's argument needs level-hood at Σ₁ strength with a
Σ₀ matrix, uniformly Δ₁ at limit levels, and it needs the Σ₀ matrix to
contain a BOUNDED object-level description of the Def step. It does not need
a Δ₀ witness for the unbounded satisfaction existentials of the project's
`LsetGraphAt`. Each requirement is listed below with the step that makes it.

### 2.1 Step A: extensionality of X from X ≺₁ L_α

Requirement: elementarity at one unbounded existential. The separating
statement "∃z(z ∈ x ↔ z ∉ y)" is Σ₁ with parameters x, y ∈ X; X ≺₁ L_α
reflects it down, so the witness z lies in X (`dev2.txt:1173-1183`).

Strength needed: Σ₁-elementarity at quantifier-free matrices. This is
strictly weaker than full Σ₁-elementarity; the proof states it as part of
the hypothesis.

### 2.2 Step B: the collapse of an extensional X

Requirement: the Collapsing Lemma 1.7.1 for a well-founded extensional
relation: a unique π, a unique transitive M, an isomorphism
π : ⟨X, ∈⟩ ≅ ⟨M, ∈⟩, and the transitive-fixing clause π ↾ Y = id ↾ Y for
transitive Y ⊆ X (`dev2.txt:1182-1183`, `dev2.txt:1302`).

Strength needed: extensionality of X plus well-foundedness of ∈ on X. No
level-story content enters. The object is the non-transitive extensional
substructure; the transitive carrier is the collapse's IMAGE, never the
source (`[LJ-1.11]` F2).

### 2.3 Step C: level-hood transfer (the heart)

This is the step that uses II.2.7's level formula. Requirement list, in the
order the proof consumes it:

1. Level-hood as Σ₁ with a Σ₀ matrix: there is a Σ₀ formula Φ(z, v, γ) of
   LST with ambient truth ∀v∀γ [v = L_γ ↔ ∃z Φ(z, v, γ)] (`dev2.txt:1186-1194`,
   from 2.7). The witness z bundles the level sequence and its bound.
   Strength: the existential over z is UNBOUNDED at the ambient level.
2. Uniform Δ₁ at limit α > ω (`dev2.txt:674-686`, 2.6-2.7): for γ < α,
   v = L_γ iff v ∈ L_α and L_α ⊨ ∃z φ(z, v, γ)
   (`dev2.txt:1191-1194`, (b)). The forward half needs the witnessing z to
   live inside L_α; that is 2.6(ii), the sequence (L_δ | δ ≤ γ) ∈ L_α for
   γ < α. Strength: the Σ₁ form is "witnessed inside the carrier", not
   merely in V.
3. Σ₀ absoluteness for the matrix: 1.9.15 moves L_α's (or M's) satisfaction
   of φ to ambient Φ and back, at every transitive carrier, in both
   directions (`dev2.txt:1219`, `dev2.txt:1267`). Strength: the matrix is
   Σ₀ and absolute for transitive sets.
4. Transfer along elementarity and the collapse: the Σ₁ statement
   "∃v∃z φ(z, v, γ)" (parameter γ) moves from L_α to X (downward, parameters
   in X) and along π : X ≅ M and π⁻¹ : M → X (`dev2.txt:1200-1215`). The
   collapse is an isomorphism, so it preserves all first-order truth; the
   Σ₁-elementarity of X in L_α preserves Σ₁ truth with parameters in X.
   Strength: Σ₁-elementarity, both directions.
5. Ordinal bookkeeping: M ∩ On = β (transitivity of M, ordinals absolute),
   and lim(β) from lim(α) via the Σ₁ statement "∃τ(v < τ)" with parameter
   v (`dev2.txt:1290-1300`). Strength: Σ₀ absoluteness of "is an ordinal"
   and "<" at transitive carriers.
6. The union law L_β = ⋃_{γ<β} L_γ at limit β (`dev2.txt:1298-1301`).
   Strength: the definition of the hierarchy at limit stages. No
   level-story content.

The direct answer to `[LJ-1.12]`: a Δ₀ witness for the satisfaction leaves
is NOT what Devlin's argument needs. Level-hood is used at Σ₁ strength
(∃z with a Σ₀ matrix), and the proof's satisfaction steps concern the Σ₁
statement inside L_α, not a Δ₀ certificate. What IS required is a bounded
description of the Def step inside the Σ₀ matrix: 2.2-2.4 write
D(v, u) = "v = Def(u)" as Σ₁, then bind every unbounded quantifier by the
concrete set K(u), the finite sequences over the formula set, the variables
and the members of u (`dev2.txt:593-630`). The Σ₀ matrix C(w, v, u) with
w = K(u) is the bounded satisfaction substrate of Devlin's engine. The
`[LJ-1.2]` probe's missing facts, a bounded object-level description of the
code set and of the satisfaction table (`agents/reports/archive/lj-1.2-gate.md` section 5),
are exactly the analogues of this substrate on the project's coding; the
argument does not require them to have any particular shape, only that some
bounded description with a bound inside the carrier exists.

### 2.4 Step D: the hull with least witnesses

Requirement: a definable well-order of L_α, used to pick the <_L-least
witness of each formula (`dev2.txt:1340-1350`). Devlin's own gloss says the
lemma is "really a result about structures with definable wellorders"
(`dev2.txt:1328-1329`). The order must be definable by a formula of low
complexity because the hull's definability and the transfer in part (iii)
consume it; Devlin's <_L is uniformly Δ₁ at limit levels (`dev2.txt:927-940`,
3.3). The smallestness half needs elementarity of the containing N
(`dev2.txt:1351-1356`).

Strength needed: a uniformly-Δ₁ (hence uniformly-Σ₁) definable well-order of
each limit level, with the leastness encoded as
φ(v₀) ∧ ∀v₁(v₁ <_L v₀ → ¬φ(v₁)).

### 2.5 Step E: the counting

Requirement: |ℒ_X| = max(|X|, ω), so the hull has at most max(|X|, ω)
elements (`dev2.txt:1357-1360`). Strength: cardinal arithmetic on a
countable formula set with parameters from X. No level-story content.

### 2.6 Step F: subsets appear early

Requirement: 5.4's hull, condensation with the transitive-fixing clause
(ii), |L_α| = |α| for infinite α (1.1(vii)), and the cardinal fact
|γ| = |α| < κ with κ a cardinal implies γ < κ (`dev2.txt:1372-1384`).
Strength: parts (i) and (ii) of condensation only, plus the level-size
equation and initial-ordinal arithmetic. No part (iii) content, and no
additional level-story content beyond Step C.

### 2.7 Step G: the well-order transfer in part (iii) and 5.9-5.11

Part (iii) needs <_L uniformly Σ₁ at limit levels (3.3(ii)), the downward
closure 3.4(i), and the transfer of the Σ₁ inequality along
π⁻¹ : L_β → L_α (`dev2.txt:1302-1319`). 5.9 needs the predecessor function
pr, uniformly Δ₁ at limit levels (3.5, `dev2.txt:961-975`). 5.10 and 5.11
need condensation, 5.5, and the same order machinery (`dev2.txt:1408-1470`).
Strength: the tower's well-order is uniformly Σ₁/Δ₁ at limit levels, and
Σ₁ statements transfer along Σ₁-elementary embeddings.

### 2.8 Summary of strengths

The level story must supply: (1) level-hood as Σ₁-with-Σ₀-matrix, uniform Δ₁
at limit levels, with the Σ₁ witness inside the carrier; (2) a bounded
object-level description of the Def step with its bound inside the carrier;
(3) Σ₀ absoluteness of the matrix at transitive carriers. The proof does
not pin the presentation: any formula with these properties works. Jech's
Chapter 13 shows an alternative engine, a Π₂ adequacy sentence absolute for
adequate transitive sets, where Σ₁-elementarity of the substructure
suffices because Π₂ sentences reflect down to Σ₁-elementary substructures
(`jech13.txt:608-625`). The two presentations have different quantifier
shapes; both place the level-hood content at low complexity and make the
carrier closure (witness inside the carrier, or adequacy) the load-bearing
hypothesis.

## 3. THE ENGINE: what II.5 assumes and does not prove

II.5 cites, without proving, a body of machinery. A later brief can cite
this list by name. Items 1 to 6 are Chapter I content, absent from
`dev2.txt`; items 7 to 12 are Chapter II content, present in `dev2.txt`.

1. The Collapsing Lemma 1.7.1: the unique transitive collapse of a
   well-founded extensional relation, with the transitive-fixing property.
   Cited at `dev2.txt:1182`, `dev2.txt:1302`. Chapter I, not in `dev2.txt`.
2. Σ₀ absoluteness 1.9.15: Σ₀ formulas of the ℒ-analogue are absolute for
   transitive sets. Cited at `dev2.txt:1193`, `dev2.txt:1219`,
   `dev2.txt:1267`. This is the bridge between satisfaction inside a
   transitive carrier and ambient truth.
3. The ℒ-analogue translation 1.9.11: each LST formula has an ℒ-formula
   with the same meaning over transitive sets. Cited at `dev2.txt:1192-1193`
   and in 1.1's proof at `dev2.txt:173`.
4. The satisfaction machinery 1.9.10 and the Sat formula: behind D(v, u)
   in 2.2-2.4. Not named in II.5 directly; the errata territory of
   Chapter I.9 covers its correctness (section 7).
5. The KP-Recursion Theorem 1.11.8: used in 2.6's proof to construct the
   level sequence within KP (`dev2.txt:686-690`).
6. Reflection 1.8.x and amenability 1.10: amenability is 5.1's hypothesis
   and 2.1's conclusion; the definition is recalled at `dev2.txt:365-375`.
7. The level-recursion machinery 2.2-2.8, the Def-side engine:
   - D(v, u) = "v = Def(u)", Σ₁ and Δ₁^p (2.4, `dev2.txt:625-633`), with
     the Σ₀ matrix C(w, v, u) and the bound set K(u), the finite sequences
     over formulas, variables and members of u (`dev2.txt:593-630`).
   - Def uniformly Δ₁^α at limit α > ω (2.5, `dev2.txt:663-666`).
   - E(f, α), the level-recursion formula, and
     G(f, α) = ∃w[K(w, ⋃ran(f)) ∧ F(w, f, α)], Δ₁^p and uniformly Δ₁^α
     (2.6, `dev2.txt:659-678`). G says "f is the sequence (L_γ | γ ≤ α)".
   - H(x, α) = ∃f[G(f, α) ∧ x = f(α)], Δ₁^p and uniformly Δ₁^α
     (2.7, `dev2.txt:679-686`). H says "x = L_α".
   - γ ↦ L_γ uniformly Δ₁^α for limit α > ω (2.8, `dev2.txt:690-693`).
8. The hierarchy basics 1.1: transitivity, monotonicity, L_α ∩ On = α,
   L_α = V_α for α ≤ ω, |L_α| = |α| for α ≥ ω (`dev2.txt:109-130`,
   `dev2.txt:200-240`).
9. The well-order of L 3.1-3.5: WO(x, y) is Σ₁ and Δ₁ under V = L
   (`dev2.txt:838-925`), uniformly Δ₁^α at limit levels
   (`dev2.txt:927-940`), downward closure 3.4 (`dev2.txt:955-959`), and the
   predecessor function pr uniformly Δ₁^α (3.5, `dev2.txt:961-975`).
10. 5.1 itself, the Tarski-Vaught equivalence, proved in the chapter
    (`dev2.txt:1071-1130`) on the amenability hypothesis.
11. The definition of the hierarchy at limits: L_λ = ⋃_{γ<λ} L_γ, used at
    `dev2.txt:1298-1301` and in 5.5.
12. The cardinal arithmetic of 1.1(vii) and the initial-ordinal facts in
    5.5's proof (`dev2.txt:1372-1384`).

The single engine II.5 leans on most is item 7: the uniformly-Δ₁ level
formula whose Σ₁ witness is the level sequence with its K(u)-bound. The
whole of 5.2's part (i) is that engine plus the transfer steps.

## 4. DEF TOWER OR EITHER TOWER, PER STEP

DD4's reading instruction: for each step, does the property belong to the
Def tower only, or would the J tower supply it too? D-26's question: does
the step lean on syntax (Def tower) or on generation data (J tower)?

| Step | Property needed | Def tower only, or either tower? | D-26 carrier |
|---|---|---|---|
| A: extensionality of X | Σ₁-elementarity at one existential | EITHER | neither tower; pure elementarity |
| B: collapse | Collapsing Lemma 1.7.1, transitive-fixing | EITHER | neither tower; general set theory |
| C1: level-hood formula | Σ₁-with-Σ₀-matrix, uniform Δ₁, witness in carrier | PER-TOWER content, same shape | Def: syntax (satisfaction); J: generation data (SZ 1.10) |
| C2: bounded Def-step matrix | bounded object-level description of the step, bound inside carrier | PER-TOWER content | Def: satisfaction bound K(u) or its coding analogue; J: the sixteen op-graphs, syntax-free (SZ p. 10) |
| C3: Σ₀ absoluteness of the matrix | 1.9.15 at transitive carriers | EITHER | neither tower; general absoluteness |
| C4: transfer along Σ₁-elementarity and the collapse | Σ₁ statements preserved both ways | EITHER | neither tower |
| C5: ordinal bookkeeping, lim(β) | Σ₀ absoluteness of On, "<" | EITHER | neither tower |
| C6: union law at limits | L_λ = ⋃ L_γ | EITHER | neither tower |
| D: hull with least witnesses | a definable well-order of the level | PER-TOWER content, both towers carry one | Def: <_L from satisfaction (3.3); J: <^A from producer triples (SZ 1.11) |
| E: counting | |ℒ_X| = max(|X|, ω) | EITHER | neither tower |
| F: 5.5 | condensation (i)(ii), |L_α| = |α|, initial ordinals | EITHER; |L_α| = |α| per-tower size, both towers have it (SZ 1.27) | neither tower |
| G: part (iii), 5.9-5.11 | well-order uniformly Σ₁/Δ₁, pr, transfer | PER-TOWER content, both towers carry one | Def: <_L; J: <^A |

The verdict for DD4: the condensation TEMPLATE (5.1 to 5.6) is shared. The
collapse, the hull mechanism, the counting, the ordinal bookkeeping and the
cardinal chain are either-tower steps. The per-tower content is exactly two
objects: the level-hood certificate (Step C) and the definable well-order
(Steps D, G). On the Def tower, both are satisfaction-based; on the J tower,
both are structural and syntax-free. This is D-26's dichotomy applied at
the level formula and at the well-order, and it matches `[LJ-1.11]`'s
reading (section 2.3 there): both engines carry the successor clause, one
through internalized satisfaction, the other through finitely many
operation graphs.

## 5. THE WIDENED SECTIONS: II.2.4-2.7, II.1.1(vii), 5.9-5.11

`[LJ-1.11]` widened this task to three groups. Verdicts:

### 5.1 II.2.4 to II.2.7: BEARS DIRECTLY, it is the engine

5.2's proof consumes the Σ₀ formula Φ from 2.7 (`dev2.txt:1186-1194`). The
chain 2.4-2.7 is where the Def-side level story is built: D (definability)
at 2.4, Def at 2.5, the level-sequence graph G at 2.6, level-hood H at 2.7.
The uniform-Δ₁ claim at 2.6/2.7 is the satisfaction-internalization step,
and it is exactly the step `[LJ-1.2]`'s probe found blocked on the
delivered tree. A brief for `[LJ-1.12]` can cite 2.4-2.7 as the engine the
crossing must supply, with the K(u) bound as the shape of the bounded
substrate.

### 5.2 II.1.1(vii): BEARS, as the counting half of 5.5 and 5.6

|L_α| = |α| for α ≥ ω (`dev2.txt:117`, `dev2.txt:200-240`) is consumed at
`dev2.txt:1379-1383` (5.5) and `dev2.txt:1386-1388` (5.6). It is generic
cardinal arithmetic over the level-size equation; the J tower has the
analogue |J_ρ^A| = H_ρ^M (SZ 1.27, in `j-hierarchy.md` section 4). It bears
on the crossing only through 5.5's cardinal conclusion, not through the
level-story certificate.

### 5.3 5.9 to 5.11: BEAR, as the cheap condensation instances

5.9 (the least element of a non-empty Σ₀ predicate is Σ₁-definable from its
parameters, `dev2.txt:1408-1423`), 5.10 (X ≺₁ L_ω₁ implies X = L_α for some
α ≤ ω₁, `dev2.txt:1425-1435`) and 5.11 (if ω₁ ∈ X ≺₁ L_κ for κ > ω₁ a
cardinal, then X ∩ L_ω₁ = L_α for some α ≤ ω₁, `dev2.txt:1437-1463`) are
the special cases `[LJ-1.11]` section 6 item 1 names as the cheap
condensation instances a formalization may prefer for the wing's single
application. They consume condensation, 5.5, the well-order and pr; they
add no new requirement to the level story beyond Step C of section 2.
5.11's closing remark (`dev2.txt:1463-1471`) shows L_ω₁ definable in L_κ by
a Σ₂ formula, which is the only Σ₂ content in the group.

## 6. UNRESOLVED OCR, WITH BOTH CANDIDATES, AND THE JECH 13 CROSS-CHECK

Every load-bearing reading below was checked against the printed page via
tesseract on `devlin-ch2.pdf` or against `jech13.txt`. Items 6.1 to 6.4 are
resolved; items 6.5 and 6.6 are UNRESOLVED, with both candidates.

### 6.1 Resolved: 5.2's hypothesis and part (iii)'s inequality

The OCR of 5.2's statement drops the hypothesis and prints part (iii) as
"π(x) ^_L x" (`dev2.txt:1148-1155`). The printed page (tesseract) reads
"If X ≺₁ L_α" and "π(x) ≤_L x". The proof settles the direction: it assumes
π(x) >_L x and derives a contradiction (`dev2.txt:1302-1319`), so the
statement is π(x) ≤_L x, the collapse never raises the <_L-rank.

### 6.2 Resolved: 5.5's second clause is "α < κ"

The OCR reads "x ⊆ L_α for some α < κ" (`dev2.txt:1369-1371`). The printed
page (tesseract) agrees. 5.6 applies 5.5 at the cardinal κ⁺ with α = κ, so
every constructible x ⊆ κ lands in L_{κ⁺}; this resolves how the bounded
statement yields P(κ) ⊆ L_{κ⁺}.

### 6.3 Resolved: 5.3's least-witness formula

The OCR garbles the leastness encoding (`dev2.txt:1340-1350`); the restored
form is φ(v₀) ∧ ∀v₁(v₁ <_L v₀ → ¬φ(v₁)). The proof's own words ("there is
clearly just one x such that ...") pin it, and Jech's note on writing the
least witness with a universal guard matches the shape
(`jech13.txt:756-760`).

### 6.4 Resolved: 5.9's and 5.11's degraded classes

5.9's "Σo α (N)" restores to "Σ₀^α(N)", a Σ₀ predicate of the L_α language
with parameters from N; the proof's "By 3.5, this is Σ₁" pins it
(`dev2.txt:1409-1423`). 5.11's "ωγ ∈ X ≺γ Lκ" restores to "ω₁ ∈ X ≺₁ Lκ"
from the proof's use (`dev2.txt:1437-1463`).

### 6.5 UNRESOLVED: the carrier subscripts in 5.2's lines (c) and (j)

Line (c) reads "(∀γ < α)[⊨? ∃v∃z φ(z, v, γ)]" (`dev2.txt:1200-1203`); the
subscripted carrier after the turnstile is unreadable in the scan and in
tesseract at 400 dpi. Line (j) reads "∀x ∈ L_? [⊨_? ∃γ∃v∃z(φ(z,v,γ) ∧
x ∈ v)]" (`dev2.txt:1245-1248`), with both subscripts unreadable.

For (c), the candidates consistent with the proof flow are "L_α ⊨" and
"X ⊨". For (j), the candidates are "L_α ⊨" and "M ⊨"; the printed
"applying π⁻¹" between (j) and (k) is loose on either reading, since the
full path runs L_α to X (downward, Σ₁) and X to M (along the collapse).

The mathematics that follows is identical on every candidate: the Σ₁
statement transfers to M, and the witness v decodes as L_γ via (a) and
1.9.15, giving L_γ ∈ M and then M ⊆ ⋃_{γ<β} L_γ. The digest does not rely
on either glyph; the transfer content is in steps (d) to (q), which are
legible.

### 6.6 UNRESOLVED: the displayed matrix of 2.2's A(v, u)

The displayed formula for "v = Def(u)" at `dev2.txt:563-590` is heavily
degraded. The statement-level content that this digest uses, that A is Σ₁
and Δ₁^p (2.4) and that the Σ₀ matrix C(w, v, u) arises by binding all
unbounded quantifiers with w = K(u) (`dev2.txt:593-630`), is legible. No
claim here depends on the degraded glyphs; a builder who needs the exact
matrix should re-OCR the printed page 67.

### 6.7 The Jech 13 cross-check

| Devlin II.5 item | Jech 13 parallel | Verdict |
|---|---|---|
| 5.2: X ≺₁ L_α collapses to L_β, β ≤ α | 13.17: for limit δ, M ≺ (L_δ, ∈) collapses to L_γ, γ ≤ δ (`jech13.txt:617`); the remark adds that Σ₁ suffices because the adequacy sentence is Π₂ (`jech13.txt:621-625`) | AGREES; Jech's engine is the Π₂ adequacy sentence σ (`jech13.txt:608-616`), Devlin's is the Σ₁-with-Σ₀-matrix level formula; both place the level-hood content at low complexity |
| 5.3-5.4: hull size max(|X|, ω) | 13.20's proof takes M with |M| = ℵ_α (`jech13.txt:770-779`) | AGREES in shape |
| 5.5-5.6: P(κ) ⊆ L_{κ⁺}, GCH | 13.20: P^L(ω_α) ⊂ L_{ω_{α+1}}, |L_{ω_{α+1}}| = ℵ_{α+1} (`jech13.txt:762-779`) | AGREES |
| 5.2(iii): π(x) ≤_L x | not stated in ch. 13; the γ ≤ δ of 13.17 is the same non-increase | CONSISTENT, resolved from Devlin's own proof (6.1) |
| 5.9-5.11: least-witness and ω₁ instances | not in ch. 13 | no conflict; standard |

The one genuine divergence is the engine: Devlin certifies level-hood
through internalized satisfaction with the K(u) bound; Jech certifies it
through the Gödel-operation closure and adequacy (`jech13.txt:586-616`),
which is syntax-free. That divergence is D-26's dichotomy, and it supports
the reading that the J tower's level story is the structural analogue.

## 7. ERRATA: SEPARATE FROM OCR DOUBT

The known-book-error list does not reach II.5. WS section 10 scopes the
inventory to Chapter I.9 and Chapter VI.1 (`devlin-errata.md:41-42`); the
Chapter II entries cover amenability (p. 45), the uniformity claim (p. 65)
and the p. 66 remark (`devlin-errata.md:125-140`). None of section 6's OCR
items is a documented Devlin error.

The error class that DOES bear on II.5's engine is the satisfaction layer
behind II.2.4: Sat has no correct Δ₁ version inside BS, and uniform Δ₁
truth requires S-amenability (`devlin-errata.md:117-122`, `devlin-errata.md:
127-133`). II.2.4's Δ₁ claim for D(v, u) hands the details to the reader
("As in 2.2 and 2.3", `dev2.txt:633`), and those details are exactly
where the errata bite. The scoping note in `digest.md:416-421` applies: the
errata bind the internalized layer, not the ambient mathematics. The
condensation ARGUMENT of II.5 is classical mathematics and is not touched
by the errata; the internalized CERTIFICATE it rides is the errata
territory. That is the literature-side statement of `[LJ-1.2]`'s NO-GO.

## 8. WHAT THE RETIRED ROUTE CONCLUDED, AND WHETHER IT SURVIVES

The retired rud route read the same chapter. Its conclusions, from the
archived records:

1. T5 (`archive/dev/JOURNAL-archived.md:1022`): the minimal classical path
   is Devlin II.5 chapters 5.1-5.6, decomposed into elementarity and
   Tarski-Vaught, the definable hull, the cardinal chapter, bounded
   subsets, and the GCH assembly. SURVIVES the route change in shape:
   `[LJ-1.11]` section 1 confirms the phase-1 blocks map onto the same
   chain, and this digest's sections 1 and 2 pin the chain from the source.
2. T84 (`archive/dev/TASKS-archived.md:119`): "Lever B: condensation story
   onto the kit", STOP under D-10. The archived story carried the Def-step
   as ⊤̇, so its successor clause said nothing. DO NOT SURVIVE: `[LJ-1.11]`
   F1 refuted the recognition claim with an explicit counterexample, and
   this digest confirms the literature never drops the successor content
   (section 2.3 of `[LJ-1.11]`; section 3, item 7 here).
3. T130 (`archive/dev/TASKS-archived.md:165`): the tower-graph crossing
   cannot ride the rud-side story, because of the index question and the
   S-versus-L tower mismatch. SURVIVES as a warning: the Def-side level
   story must carry the internalized definable-powerset step
   (`agents/reports/archive/l3.32-t130-report.md:26-33`), which is exactly the C2
   requirement of section 2 here.
4. T259 (`archive/dev/TASKS-archived.md:266`): re-targeting the description
   to the S-tower is viable and ungated. SURVIVES as the J-side direction,
   consistent with DD2's two-tower route.
5. T263 (`archive/dev/TASKS-archived.md:268`): all sixteen op-graph
   formulas fail Δ₀ as delivered; a set-level conditional pass. SURVIVES as
   the D-26 magnitude evidence; it does not change the direction.
6. D31/D32 (`archive/dev/DECISIONS-archived.md:51-52`): the condensation
   crossing was severed and its rebuild deferred to the GCH resume.
   SURVIVES: the crossing is still the open term `[LJ-1.12]` prices.

The route change does not revive the ⊤̇-step story. The retired route's
useful residue is the route decomposition, the crossing as the widest
unmeasured term, and the T130 warning; its failed residue is the
successor-free story and the 700-1,720 crossing band that rode it (the
`[LJ-1.2]` NO-GO re-priced the crossing at 5.0-5.1k).

## 9. LITERATURE USED

Read in full: `dev/literature/digest.md`, `dev/literature/j-hierarchy.md`,
`dev/literature/primary-sources.md`, `dev/literature/devlin-errata.md`,
`dev/literature/BIBLIOGRAPHY.md`, `_build/literature/dev2.txt` (II.1.1,
II.2.1-2.9, II.3.1-3.6, II.5), `_build/literature/jech13.txt` (13.12-13.21),
and the printed pages 78-85 of `_build/literature/devlin-ch2.pdf` via
tesseract.

Consulted: `dev/literature/fine-structure.md` and
`dev/literature/rudimentary-functions.md` for the SZ "5.2-5.4" references
(they are SZ projecta, not Devlin II.5; no overlap). NOT read:
`dev/literature/geology.md`, `glossary-review-2026-08.md`,
`terms-2026-08.md`, `formalizations.md`, `formalizations-landscape.md`,
`owner-notes-rud.md`: none bears on the condensation chapter's content.

Took: the J-side engine summary (`j-hierarchy.md:88-113`); the errata
scoping (`devlin-errata.md:41-42`, `:117-133`); the corpus record of the
II.5 fetch (`digest.md:513-518`); the fetch map and OCR caveats
(`primary-sources.md:26-34`, `:139-191`); the Jech 13 anchors
(`jech13.txt:586-625`, `:762-779`).

## 10. ARCHIVE USED

- `archive/dev/TASKS-archived.md`: rows at `:119` (T84), `:165` (T130),
  `:266` (T259), `:268` (T263). Took the route's condensation verdicts for
  section 8.
- `archive/dev/JOURNAL-archived.md`: `:1022` (T5's II.5 decomposition),
  `:492-498` (the GCH wing price with the collapse as driver),
  `:1756-1760` (T48: 5.5 consumes condensation parts (i)(ii) only). Took
  the retired route's reading for section 8.
- `archive/dev/DECISIONS-archived.md`: `:51-52` (D31/D32 sever the crossing;
  D33 splits the trophy). Took the deferral for section 8.
- `agents/reports/archive/l3.32-t130-report.md:26-33`: the crossing must carry the
  internalized definable-powerset step. Took the T130 warning.
- `dev/LESSONS.md`: D-10 (`:1302-1361`), D-26 (`:1662-1687`), P-l
  (`:2099-2158`), C-22 (`:2031`). D-26 is the law this digest's section 4
  tests; C-22 produced the incremental skeleton.

## 11. WHAT I AM NOT SURE OF

1. The (c)-line carrier (section 6.5). The proof's mathematics does not
   change between the two candidates; a sharper scan could settle the glyph.
2. Whether the project's coding can supply the bounded Def-step description
   at the strength of section 2.3. The digest states the requirement; the
   price is `[LJ-1.12]`'s job.
3. Whether Devlin's "Σ₀" in 2.2-2.7 means the same class the project's Δ₀
   means. Devlin calls Δ₀ formulas "Σ₀" (`devlin-errata.md:58-66`); the
   digest uses Devlin's own names and flags the convention difference in
   section 7 rather than choosing.
4. The exact displayed matrix of 2.2 (section 6.6). No load-bearing claim
   here uses it; the K(u) bound's exact shape would matter to a builder who
   mirrors Devlin's matrix instead of the project's coding.
5. Whether 5.1's proof needs amenability in the (ii) to (i) direction or
   only in (i) to (ii). The OCR of the proof is cut at `dev2.txt:1085-1095`;
   the digest records 5.1 as proved in the chapter and does not depend on
   where amenability fires.
