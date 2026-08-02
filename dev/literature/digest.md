# Digest: the orthodox form of the rud route, pinned from the collected literature

Task `[L3.30-D1]`. Authored by the orchestrator directly (per the owner's
2026-08-02 instruction) from the collection files in this directory and the
collection report `_build/l1-report.md`; an independent adversarial audit
(codex, read-only) then returned 16 findings, all verified against the
collection and applied, and later extraction/fetch tasks update the OPEN
items in place (the git history records each pass). Authority order:
primary sources beat the collection notes, the collection notes beat the
owner's exploration note (`owner-notes-rud.md`), and nothing mathematical
here rests on model memory: every mathematical claim carries a citation
through the collection files, project-internal statements (probe history,
measured prices) are marked as such, and what the fetched corpus cannot
settle is an OPEN item, not a fact. Source abbreviations (SZ, MB, WS, Fr, W) are those of
`BIBLIOGRAPHY.md` and the collection files.

Purpose: this document pins the orthodox contemporary form of the rudimentary
functions architecture, as evidence for the design memo `[L3.30-M]` and the
owner's ruling. It lays out; the memo decides.

## 1. The orthodox form, pinned (Q1-Q7)

Definitive short answers, each with its citation trail. Where the collection
report marked a point UNVERIFIED, the ruling made here is stated with its
evidence; what genuinely cannot be settled from the fetched corpus stays OPEN
(collected again in section 7).

- **Q1 (the basis).** Two contemporary presentations coexist. Schindler-Zeman
  define rud_A by six schemata: projection, set difference, unordered pair,
  tuple/composition, bounded union, and x ∩ A (SZ Definition 1.1, p. 6), and
  for the S-hierarchy use the sixteen-function finite basis F0..F15 (SZ
  p. 10), stated to enlarge Jensen's [3, Lemma 1.8] list precisely so that
  every S-level is transitive (SZ footnote 5, p. 10). Mathias-Bowler / Weak
  systems use the nine-function list R0..R8 closed under composition, where
  R0..R7 generate the Delta-0 separators and R8 = {x"{w} | w ∈ y} is the
  single function distinguishing GJ0 from the Devlin Basic system (MB 2.0,
  p. 13; WS 1.12, p. 11; WS 2.61-2.68, pp. 19-20). Jensen's own verbatim 1972
  list is OPEN: it is not reproduced anywhere in the fetched material
  (rudimentary-functions.md section 1.2).
- **Q2 (hierarchy, condensation, acceptability).** The J-hierarchy is indexed
  by limit ordinals: J_0 = ∅, J_{α+ω}^A = rud_A(J_α^A ∪ {J_α^A}), unions at
  limits (SZ Definition 1.6, p. 9; footnote 4 marks the indexing as a
  deliberate contrast with Jensen 1972). The auxiliary S-hierarchy steps one
  level at a time via S^A(U) = ⋃_{i≤15} F_i"(U ∪ {U})², and J_α^A = S_α^A at
  limit α (SZ pp. 9-10, equation I.1). Condensation is at the Sigma-1
  level: the transitive domain of a Sigma-1 preserving embedding into a
  J-structure is itself a J-structure (SZ Theorem 1.16, p. 14). Acceptability (SZ Definition 1.20, p. 16) is "a strong
  version of GCH" (SZ's own remark, p. 16) and is a Q-property (SZ 1.21).
- **Q3 (the comprehension theorem).** The modern statement is SZ Lemma 1.4
  (p. 8): for transitive U (and A with A ∩ V^{rk(U)+ω} ⊆ U),
  P(U) ∩ rud_A(U ∪ {U}) = P(U) ∩ Σ_ω^{<U,∈,A>}; the proof is one page with
  no syntactic machinery (rudimentary-functions.md section 4.1). The
  Mathias route reaches the same ground through the Bernays theorem (all
  Delta-0 separation in DB0, MB 1.43) plus the uniformly-Delta-1 truth
  predicate for Delta-0 sentences over transitive models of MW (MB 9.0-9.2,
  pp. 37-38). Welch's draft spells out the term-simulation with explicit
  code trees (W Theorem 2, Lemmas 7 and 10; secondary source).
- **Q4 (the canonical well-order).** Stage-first, then minimal producer
  triple: older S-stages precede, and within a new stage x precedes y iff
  the lexicographically minimal (i, u, v) with x = F_i(u, v) precedes y's
  minimal triple, over 16 × S_{β̄}^A × S_{β̄}^A (SZ p. 11, verbatim in
  j-hierarchy.md section 3). The order is uniformly Sigma-1 over J_α^A (SZ
  Lemma 1.11).
- **Q5 (relativization).** One added schema, x ∩ A, in the schemata
  presentation (SZ Definition 1.1); equivalently the basis function F15 =
  A ∩ x (SZ p. 10). The unrelativized R0..R8 has no A-function; Welch's
  draft adds one function per predicate (W Definition 5, p. 6; secondary).
- **Q6 (what broke in Devlin).** Seven documented error classes, all with
  Mathias's WS section 10 as the inventory: false Delta-0 claims for syntax
  operations, unbounded finite-sequence formation in a weak system,
  ambiguous "Sigma-0 function" definitions equivalent only under TCo,
  failure of uniform truth over merely amenable sets, proof reuse of the
  false Lemma 9.3, assorted arity/reference slips, and an unprovable
  transitive-closure existence claim. Condensed actionable list in section 5
  below; full inventory in devlin-errata.md.
- **Q7 (the formalization landscape).** Paulson formalized the relative
  consistency of AC in Isabelle/ZF via satisfaction internalization
  following Kunen; GCH is ruled NOT mechanized there by artifact evidence
  (section 6 below states the ruling and the one ambiguous sentence).
  Flypitch proved the independence of CH in Lean 3 via Boolean-valued
  models, both directions, and did NOT construct L (its README lists the
  constructible universe as possible future work). No formalization of
  GCH-in-L, and no rud-based formalization at all, appears anywhere in the
  fetched material (formalizations.md; the precise wording of this
  "virginity" claim is in section 6).

Rulings on the collection report's six UNVERIFIED marks:

1. *Jensen's verbatim 1972 list*: PARTIALLY SETTLED by [L3.30-L2]
   (primary-sources.md): Jensen's own author manuscript (Bonn archive;
   manuscript provenance flagged, not the 1972 journal wording) states the
   Basis Theorem with F0..F8 identical to SZ's F0..F8 (JM 2.2.15, p. 56),
   so SZ's enlargement is exactly F9..F15; independently, Devlin's Basis
   Lemma VI.1.11 (p. 236) gives the same nine, with the Extended Basis
   Lemma VI.1.12 adding F9 = A ∩ x for rud_A. The 1972 journal text itself
   remains unfetched (open archive but bot-walled).
2. *Stanley's exact review text*: stays OPEN (paywalled); his role is
   attested secondhand: Mathias credits the review with drawing attention to
   the flaws (WS p. 56), Welch credits Stanley with proposing BS + rud as
   the cure (W p. 1).
3. *The sweep's "minimal model J_omega" phrasing*: not in the fetched MB
   text; the nearest true statements are Fr slide 28 ("J_ω is provident. The
   next one will be J_{ω²}") and MB 5.9 (rudimentary-functions.md section 3).
4. *Paulson's GCH scope*: RULED by artifact evidence, GCH not mechanized;
   which reading the contrary section 2.7 sentence intends stays OPEN; see
   section 6.
5. *Mizar/Metamath/Naproche*: since SETTLED by the [L3.30-L3] sweep
   (formalizations-landscape.md); see section 6.
6. *Any rud-based formalization*: nothing found in the fetched material;
   bounded claim, see section 6.

## 2. The basis decision, laid out (not decided)

The genuine fork for the formalization is which finite generating apparatus
to build on. The memo decides; this section lays out both options with their
exact function lists, what each buys, and what each costs.

### Option S: the Schindler-Zeman package (six schemata + F0..F15)

The definition of rud_A is by the six schemata (SZ Definition 1.1, p. 6):

    f(x1..xk) = xi                          (projection)
    f(x1..xk) = xi \ xj                     (difference)
    f(x1..xk) = {xi, xj}                    (pair)
    f(x1..xk) = <g1(x~), ..., gl(x~)>       (tuple/composition)
    f(x1..xk) = ⋃_{y ∈ x1} g(y, x2..xk)     (bounded union)
    f(x)      = x ∩ A                       (relativization)

and the S-hierarchy step uses the sixteen-function basis (SZ p. 10):

    F0(x,y)  = {x, y}                F8(x,y)  = {x"{z} ; z ∈ y}
    F1(x,y)  = x \ y                 F9(x,y)  = <x, y>
    F2(x,y)  = x × y                 F10(x,y) = x"{y}
    F3(x,y)  = {<u,z,v> ; z ∈ x      F11(x,y) = <left(y), x, right(y)>
                ∧ <u,v> ∈ y}         F12(x,y) = <left(y), right(y), x>
    F4(x,y)  = {<u,v,z> ; z ∈ x      F13(x,y) = {left(y), <right(y), x>}
                ∧ <u,v> ∈ y}         F14(x,y) = {left(y), <x, right(y)>}
    F5(x,y)  = ⋃ x                   F15(x,y) = A ∩ x
    F6(x,y)  = dom(x)
    F7(x,y)  = ∈ ∩ (x × x)

What it buys: every S-level is transitive by construction, which is exactly
what the enlargement over Jensen's list was engineered for (SZ footnote 5,
p. 10); the entire downstream package (uniform Sigma-1 of the S-sequence, SZ
1.10; the canonical well-order over 16 × S × S, SZ p. 11; Sigma-1
satisfaction and Skolem functions, SZ 1.14-1.15; condensation, SZ 1.16;
acceptability and the fine structure, SZ 1.20 ff.) is stated in the
literature for precisely this apparatus, so the formalization can follow the
survey clause by clause.

What it costs: sixteen basis functions to verify as rud_A, and the basis
completeness lemma ("every rud_A function is generated from this list") is
asserted with "a little bit more work is necessary" and a citation to
[3, Lemma 1.8] but NOT proved in the fetched SZ text (SZ p. 10). UPDATE
[L3.30-L2]: the completeness proof now has two fetched blueprints: Jensen's
manuscript proves the Basis Theorem for F0..F8 (JM 2.2.15, with the simple
functions 2.2.2-2.2.8 as the engine) and Devlin proves the same as VI.1.11;
since a superset of a basis whose extra members are themselves rud is again
a basis, the F0..F8 proof carries the F0..F15 list once each of F9..F15 is
checked rud, so the from-scratch risk on this leg drops to
blueprint-following.

### Option R: the Mathias package (R0..R8 + GJ0 + the T function)

The corrected modern list (MB section 2, p. 13; WS 2.61; Fr slide 6):

    R0(x,y) = {x, y}          R5(x)   = x ∩ {(a,b) | a ∈ b}
    R1(x,y) = x \ y           R6(x)   = {(b,a,c) | (a,b,c) ∈ x}
    R2(x)   = ⋃ x             R7(x)   = {(b,c,a) | (a,b,c) ∈ x}
    R3(x)   = Dom(x)          R8(x,y) = {x"{w} | w ∈ y}
    R4(x,y) = x × y

R = the closure of R0..R8 under composition; B = the closure of R0..R7
(MB 2.0). What it buys: nine functions instead of sixteen; a clean axiomatic
counterpart (a transitive set is rud closed iff it models GJ0, the
Gandy-Jensen proposition WS 2.85, with GJ0 = DB0 + the single axiom R8, WS
1.12); the closure of R0..R7 generates the Delta-0 separators (MB 2.1, WS
2.61-2.68); and the single unary function T with u ⊆ T(u), u ∈ T(u), T
preserving transitivity, ⋃_n T^n(u) the rud closure of u ∪ {u} (WS
2.73-2.82), giving J_ν = T_{ων} (MB 0.3, p. 2) and the whole provident-sets
theory (MB sections 6-7) on top.

What it costs: the fine-structure literature in the collection (the SZ
chapter) speaks F0..F15, so the S-hierarchy statements, the well-order's
16-way lexicographic step, condensation's proof bookkeeping, and the
acceptability rephrasing (I.2) would all need re-derivation against R0..R8
or against T; and the ordinal bookkeeping around T is delicate (ν -> ων is
not rud rec, Fr slide 14). Mathias himself flags that no single rud function
gives the rud closure of u (as opposed to u ∪ {u}) in the same fashion (WS
2.83, an open problem there); the sharp boundary fact nearby: for any
α > 0, J_α ∉ rud cl(J_α ∪ {ωα}) (WS 14.5).

### What the sources say about the relation

R8 is the one function separating the Gandy-Jensen world from the Devlin
Basic world (WS 1.12; MB 1.49-1.55 gives the history: Gandy's "basic" =
Jensen's "rudimentary", discovered independently). F0..F15 is an enlargement
of Jensen's own basis, made for S-level transitivity (SZ footnote 5). The
two packages describe the same class of functions (SZ cite Jensen's
[3, Lemma 1.8] basis theorem; MB/WS bridge through the Gandy-Jensen
characterization, WS 2.85, and MB 0.3's citation of Jensen [J2]); the fork
is which generating presentation the formalization commits to, not which
class it gets. [L3.30-L2] pins the family tree: Jensen's own basis is
F0..F8, nine functions (JM 2.2.15; Devlin VI.1.11 verbatim agreement, with
VI.1.12 adding F9 = A ∩ x for rud_A), Jech's Gödel operations are the ten
G1..G10 (Def 13.6), Mathias's R0..R8 are nine, and SZ's F0..F15 is the
S-transitivity enlargement of Jensen's nine.

## 3. The hierarchy and the order

The stratification to pin (SZ Definition 1.6, p. 9, and pp. 9-10):

- J indexed by limit ordinals: J_0^A = ∅, J_{α+ω}^A = rud_A(J_α^A ∪
  {J_α^A}), unions at limit-of-limits, L[A] = ⋃_α J_{ωα}^A. Every J-level is
  rud_A closed and transitive; J_α^A ∩ On = α for limit α (SZ p. 10).
- S steps one at a time: S_0 = ∅, S_{α+1}^A = S^A(S_α^A) with S^A(U) =
  ⋃_{i≤15} F_i"(U ∪ {U})², unions at limits. Every S-level is transitive,
  and J_α^A = S_α^A at limit α (I.1); the rank jump per S-step is finite.
- The S-sequence is internal and uniform: <S_γ^A ; γ < β> ∈ J_α^A for β <
  α, and "x = S_γ^A" is uniformly Sigma-1 over J_α^A, witnessed by a
  formula independent of α (SZ Lemma 1.10). This uniformity is the engine
  for everything downstream (the well-order's Sigma-1-ness, the Skolem
  functions, condensation's proof).

Condensation (SZ Theorem 1.16, p. 14): if M = <J_α^A, B> is a J-structure
and π : M̄ ->_Σ1 M with M̄ transitive, then M̄ = <J_ᾱ^Ā, B̄> for some ᾱ ≤ α.
The proof sets ᾱ = On ∩ M̄, pulls A and B back along π, and runs Lemma 1.10
in both directions (j-hierarchy.md section 2). The supporting machinery is
the uniformly Sigma-1 satisfaction relation (SZ 1.14) and the Sigma-1
definable Sigma-1 Skolem function every J-structure carries (SZ 1.15).
Acceptability is preserved down Sigma-1 embeddings and up Q-embeddings (SZ
1.22); for L itself, every J_α is acceptable and sound, proved in a zig-zag
induction (SZ 9.1-9.2, p. 52).

The canonical well-order (SZ p. 11): <^A_β is defined recursively; at
successors, x <^A_{β̄+1} y iff x appears in the older stage and y does not,
or both are old and x <^A_{β̄} y, or both are new and the lexicographically
minimal producer triple (i, u, v) with x = F_i(u, v) precedes y's minimal
triple in 16 × S_{β̄}^A × S_{β̄}^A. The whole sequence of orders is
uniformly Sigma-1 over J_α^A (SZ Lemma 1.11), and drives the Sigma-1
surjection g : α -> J_α^A when α is closed under Gödel pairing (SZ 1.17).

**Correspondence with this project's order probe.** The order-probe's
candidate 1 (the stratified producer order: compare stage of first
appearance first; within a stage, compare the lexicographically minimal
(operation index, arguments) producer) is, clause for clause, SZ's <^A_β:
stage comparison is the first two disjuncts, the minimal producer triple is
the third, and the lexicographic base is the operation-indexed product. The
probe's candidate predates the fetch of this text (the project-internal
record is the order-probe section of dev/memos/L3.29-b-pivot.md; this
design-history statement is project context, not a literature claim); the
match with the SZ text quoted in j-hierarchy.md section 3 means candidate 1
is the orthodox order, not merely an admissible one.

Acceptability (SZ Definition 1.20, p. 16): M = <J_α^A, B> is acceptable iff
whenever a new subset of some τ < ξ appears at J_{ξ+ω}, there is a
surjection τ -> ξ in J_{ξ+ω}. SZ's own gloss: "acceptability can be
considered as a strong version of GCH" (p. 16). Note carefully: the fetched
chapter does NOT itself derive GCH-in-L; the GCH connection in the corpus is
this remark plus the consequences 1.23-1.27 (j-hierarchy.md section 4). The
actual GCH-in-L derivation is an OPEN item for the memo (section 7).

## 4. Reconciliation against the owner's note

Point by point against `owner-notes-rud.md`; where the note and the fetched
sources disagree, the source wins and the discrepancy is flagged.

1. **"Gandy-Jensen: F is rud iff F is a composite of Gödel operations."**
   The content is supported in two halves: rud = closure of a finite list
   under composition (MB 2.0 for R0..R8; SZ p. 10 for F0..F15 as a basis),
   and the Gandy-Jensen characterization of rud closure (WS 2.85: a
   transitive set is rud closed iff it models GJ0; MB 2.17 gives Gandy's
   three equivalent characterizations via companions). But the specific
   statement "rud = compositions of the Gödel operations", under that name
   and as a named theorem, is NOT verbatim anywhere in the fetched corpus;
   the phrase "Gödel operations" occurs in the collection only in
   BIBLIOGRAPHY.md's role line for the cite-only Jech entry, and no fetched
   text states the theorem under that name. UPDATE [L3.30-L2]: the named
   pieces are now in hand (Jech's Gödel operations = compositions of
   G1..G10, Def 13.6 and p. 177, with Cor 13.8 as the Jech-side parallel
   of SZ 1.4; Devlin's Basis Lemma VI.1.11, rud = compositions of F0..F8),
   so the note's claim decomposes into the two basis lemmas plus the
   parallel comprehension statements; the literal iff under the
   Gandy-Jensen name is still in no fetched text (Gandy's paper remains
   paywalled). Residual FLAG narrowed to that attribution only.
2. **The rud family disambiguation** (rud functions / rud closure / rud_A /
   simple functions / S-hierarchy): confirmed as a real and necessary
   distinction. The key lemma the note cites as rud(X) ∩ P(X) = Def(X) is
   fetched in the form P(U) ∩ rud_A(U ∪ {U}) = P(U) ∩ Σ_ω^{<U,∈,A>} (SZ
   1.4); note the argument is U ∪ {U}, not U, a detail the formalization
   must not drop (Mathias makes the same distinction load-bearing: WS 2.82
   vs WS 2.83). "Simple functions" are confirmed as the proof device of SZ
   Lemma 1.4's ⊆ direction; the note's further claim that they preserve
   Sigma-n definability and serve the Sigma-star theory is NOT in the
   fetched text. FLAGGED: partial support; the [L3.30-X1] extraction has
   since checked SZ's later sections with a negative result (no Sigma-n
   role for "simple" there; the Sigma-star machinery is explicitly
   excluded, SZ p. 5, deferring to Zeman's book and Welch's chapter), and
   the [L3.30-L2] fetch of Jensen's manuscript has since CONFIRMED the
   note's core: simple functions preserve Sigma-0 (JM 2.2.2), every rud
   function is simple (JM 2.2.3), rud relations are Sigma-0 and rud_A
   relations Sigma-1 (JM 2.2.4, 2.2.8). Only the "serves the Sigma-star
   theory" clause still hangs on Zeman's book (paywalled).
3. **The S-step formula.** The note writes S_{ν+1} = S_ν ∪ {S_ν} ∪
   ⋃_i G_i"(S_ν × S_ν); SZ's actual step is S^A(U) = ⋃_{i≤15} F_i"(U ∪
   {U})² (SZ p. 9-10). The shapes differ (SZ folds U and {U} into the
   argument square rather than unioning them in); the collection records no
   comparison of the two shapes, so no equivalence between them is claimed
   here. The formalization should pin SZ's exact form. FLAGGED:
   presentational discrepancy, SZ's form wins.
4. **The operation count.** The note says the well-order's index i runs
   over "9 or 10" indices and its table says "10 G_i"; SZ's basis has 16
   functions and the well-order is lexicographic over 16 × S × S (SZ pp.
   10-11); Mathias's list has 9 functions R0..R8, and GJ0 has ten axioms
   (the nine DB0 axioms plus R8, MB 7.3). RESOLVED by [L3.30-L2]: the
   count discrepancy dissolves once the lists are aligned: Jensen's own
   basis is F0..F8, NINE functions (JM 2.2.15; Devlin VI.1.11 agrees), and
   Jech's Gödel operations are TEN (G1..G10, Def 13.6), so the note's "9
   or 10" tracks the classical bases exactly; SZ's SIXTEEN is the
   S-hierarchy-engineered enlargement (F9..F15 added for S-level
   transitivity, footnote 5). FLAG retained in one direction only: if the
   memo adopts the SZ S-step, the order is lexicographic over 16 indices,
   not 9 or 10.
5. **The S-hierarchy as the pivot; "y = S_ν" uniformly Sigma-1.**
   Confirmed exactly (SZ Lemma 1.10; the note's emphasis that all
   downstream definability dividends flow from this is borne out by the SZ
   proof structure, section 3 above).
6. **AC without satisfaction; the well-order as a purely algebraic
   recursion.** Confirmed in substance: the canonical well-order is built
   from the finite basis with no syntax (SZ p. 11), is uniformly Sigma-1
   (SZ 1.11), and yields the Sigma-1 surjection (SZ 1.17). The fetched
   corpus does not itself state "L ⊨ AC" as a theorem of the chapter; that
   the well-order construction is the substance of that argument is this
   digest's own analysis, not a sourced claim.
7. **Condensation's three dependencies** (rud closedness; uniform Sigma-1 of
   the hierarchy; Sigma-1 Skolem functions): confirmed, they are visibly
   the three ingredients of SZ's proof (Theorem 1.16 using Lemma 1.10;
   Theorems 1.14-1.15).
8. **GCH via Skolem hull and collapse; |J_α| = |α|.** The argument shape is
   textbook-standard but NOT in the fetched corpus: SZ stop at
   acceptability-as-strong-GCH (Definition 1.20 remark) and the
   consequences 1.23-1.27, and prove J_α acceptable for L (9.1), without
   deriving GCH-in-L in the chapter. The cardinality bookkeeping is
   supported through the Sigma-1 surjections of SZ 1.17. FLAGGED: the
   GCH-in-L derivation itself is an OPEN item to source for the memo.
9. **Master codes: Sigma-n over J_α reduced to Sigma-1 over (J_{ρ_n},
   A_n).** SETTLED by the [L3.30-X1] extraction (fine-structure.md): the
   reduction is in the SZ chapter, in the form of Lemma 5.6 (p. 34: for
   acceptable M and a very good parameter p, Sigma-{n+1}^M subsets of the
   n-th reduct M^{n,p} are Sigma-1 over it) with Lemma 5.9's embedding
   extension, summarized by SZ themselves as "under favourable
   circumstances Σn over M can be viewed as Σ1 over a 'reduct' of M"
   (p. 14). Two corrections to the note's shorthand: SZ never use the
   term "master code" (their term is the standard code A_M^{n,p} over the
   n-th reduct M^{n,p}), and the reduction is not parameter-free: it needs
   acceptability plus a very good parameter, and the standard-parameter
   form additionally needs soundness (Lemma 6.8, p. 37; J_α is sound,
   Lemma 9.2, p. 52). The formalization dividend the note claims survives
   in this conditioned form.
10. **The geology verdict** (rud provides no leverage for set-theoretic
    geology; the syntax burden sits in forcing itself). This is the owner's
    analysis, not literature: no geology source was fetched in L1. Marked
    as analysis; it goes to the memo as a design consideration, not as a
    sourced fact.
11. **The Devlin warning.** Confirmed and amplified: the collection's
    errata inventory (devlin-errata.md, summarized in section 5) documents
    exactly the failure classes the note gestures at, with Mathias's WS as
    the inventory and MB section 9 as the repaired Delta-0-truth proof.
12. **The Cubical pitfalls** (LEM for the order's linearity; the
    well-foundedness cost of J_α = S_{ωα} over a HIT-represented cumulative
    hierarchy; the advice to split the S-recursion from ordinal
    arithmetic). Analysis, not literature; the adjacent fetched fact is
    that ν -> ων is not rud rec (Fr slide 14), which independently
    motivates keeping the ordinal bookkeeping outside the rud machinery.
    Goes to the memo as probe candidates (the J = S_{ωα} well-foundedness
    probe is already registered in the L3.30 task register).

## 5. What the errata mean for us

The full inventory is devlin-errata.md; its distilled do-not-repeat
checklist (section 5 there, eleven items) is the normative artifact. The
actionable core for this project:

- **Never claim Delta-0-ness for syntax operations, and grade the repairs
  honestly.** F∧ and Build need an addition mechanism and are Delta-1, not
  Delta-0, in BS (WS 10.3-10.4, Lemma 9.3); Seq is correctly Sigma-1 but
  its Delta-1 claim is FALSE in BS (WS 10.5, Solovay's forcing argument);
  Sat has no correct Delta-1 version inside BS at all (Lemma 9.10 false,
  "no cure in BS"; Sat becomes Delta-1 only in the cure systems DS and GJI,
  WS 10.18, 10.23). If we internalize syntax, its complexity claims must be
  proved, not assumed.
- **Unbounded finite-sequence formation is a theorem, not a triviality**:
  BS proves [ω]¹ and [ω]² exist but not [ω]³ (MB 1.46). Any "set of all
  finite sequences" step in a weak ambient theory must be justified.
- **Transitive closure is not free**: TCo is unprovable even in Zermelo set
  theory (SZ footnote 3, p. 9; WS section 12's model), and two natural
  definitions of "Sigma-0 function" are equivalent only under TCo (WS
  10.1). Our development should make its TCo usage explicit.
- **Uniform truth needs S-amenability**, not mere amenability (WS
  10.12); the correct uniformly-Delta-1 truth proof is MB 9.0-9.2, not
  Devlin's I.9.
- **Devlin is not a line-by-line blueprint.** Use SZ (and Zeman's book,
  once fetched) for the J-hierarchy and fine structure, MB/WS for the weak
  systems and the corrected proofs; consult Devlin only with the errata
  list open. (This confirms the owner's note, item 11 of section 4.)
- Two bookkeeping slips to avoid repeating verbatim: the Stanley review is
  JSL 52(3), 1987, 864-867 (not volume 53), and Devlin-style arity slips
  are cheap to make and expensive to find (checklist items 9-10).

A scoping note: several errata classes are about what a WEAK object theory
can prove. Our ambient metatheory (Cubical Agda over the HIT V with LEM
assumed) is not weak in that sense; the errata bind us wherever we
internalize (satisfaction, definability, levels), which is exactly the
rud route's territory. They are constraints on the internalized layer, not
on the Agda metalanguage.

## 6. The formalization landscape verdict

**Paulson (Isabelle/ZF).** Route: satisfaction internalization following
Kunen, with DPow matched to Kunen's Definition VI 1.1 (P sections 2 and 6;
P p. 32). Scope: the relative consistency of AC. His own verdict on the
proof: "unusually long, and not entirely satisfactory: two parts of the
proof do not fit together" (P abstract, p. 1); the comprehension scheme is
not proved schematically, with about 35 instances proved separately (P
p. 65; the slides say 40, a counted discrepancy). A second limitation is
load-bearing for this project's AC goal: "The proof that L satisfies V = L
cannot be combined with the proof that V = L implies the axiom of choice in
order to conclude that L satisfies the axiom of choice", because the two
instances of V = L are formalized differently (P p. 65; formalizations.md
section 1). GCH: ruled NOT mechanized,
by artifact evidence: the library outline's theory graph terminates in
AC_in_L and Internalize with no GCH theory (PI p. 8); the conclusions list
GCH and diamond as work for "future investigators" (P p. 65); the slides
list "Prove generalized continuum hypothesis" as a future challenge (PS
slide 19). One sentence cuts the other way and is quoted in full so the
ambiguity is on the record: "We prove ZFL ⊢ AC, ZFL ⊢ GCH and ZFL ⊢ ♦, but
we do not prove ZF ⊢ AC^L, ZF ⊢ GCH^L and ZF ⊢ ♦^L" (P section 2.7, p. 11).
Two readings: a paper-internal inconsistency, or a reference to informal
mathematics rather than the formal development. The ruling here covers only
the mechanization question and stands on the artifacts; which reading the
sentence intends stays OPEN, exactly as the collection report marks it
(formalizations.md section 1.1).

**Flypitch (Lean 3).** The independence of CH, both directions, via
Boolean-valued models: Cohen forcing for the failure of CH, a sigma-closed
collapse for CH itself (FC abstract), over a deep embedding of first-order
logic with a Boolean-valued soundness theorem, on bSet B, the Aczel
encoding of set theory (FC pp. 2-3). The constructible universe: NOT
constructed; "Consistency of CH via construction of the constructible
universe" is listed as possible future work (FG README). The ITP 2019 paper
covers only the negation direction (FI abstract).

**Everything else.** The only other formalization the fetched corpus
mentions is Gunther-Pagano-Terraf's first steps toward forcing via generic
extensions of countable transitive models (FC's related-work line, p. 4).
The wider landscape was swept by [L3.30-L3] (formalizations-landscape.md,
indices fetched 2026-08-02): Metamath, Mizar, Lean mathlib, Coq/Rocq, and
Naproche contain no constructible universe as a formal object at all (each
absence bounded by the index searched); the only formal L found in the six
systems is Paulson's Isabelle/ZF Constructible session, exporting ZF-in-L
and AC-in-L and nothing beyond; GCH appears in those libraries only as an
assumed axiom or as ambient theorems (Metamath's GCH-implies-AC corpus,
Kirst-Rech's GCH-to-AC in Coq, Naproche's GCH axiom atom), never as
"L models GCH".

**The GCH-in-L virginity claim, worded exactly.** Within the fetched
corpus: no mechanized proof of GCH in L exists; the two formalization
projects in the fetched corpus that touch this territory both name it as
future work (P p. 65; PS slide 19; FG README); and no rud-based formalization of
constructibility appears at all. The [L3.30-L3] sweep then widened the
bound from the fetched corpus to the six systems' own indices as of
2026-08-02, with the same negative result everywhere, so the claim now
stands as: not found in the fetched corpus NOR via the searched indices of
Metamath, Mizar, Isabelle AFP + distribution, Lean mathlib, Coq/Rocq, and
Naproche. Absence of mention is still not proof of absence (unindexed
personal repositories and post-2022 MML additions are outside the sweep's
reach, per its own caveats). As far as the evidence carries: GCH-in-L via
the rud route is unclaimed territory, and the claim has now survived one
deliberate refutation attempt.

## 7. Open items

Each with what would settle it.

1. **Jensen's verbatim 1972 basis list**: PARTIALLY SETTLED by [L3.30-L2]
   (ruling 1 in section 1: the author manuscript's F0..F8 and Devlin's
   VI.1.11 agree; SZ's enlargement is exactly F9..F15). Residue: the 1972
   journal wording itself (open archive, bot-walled; a library copy would
   close it).
2. **Stanley's review, full text** (JSL 52(3), 1987, 864-867): library
   access; the role attribution currently rests on WS p. 56 and W p. 1.
3. **The Gandy-Jensen "Gödel operations" statement**: LARGELY SETTLED by
   [L3.30-L2] as a decomposition rather than one named theorem: Jech
   defines "Gödel operations" as the compositions of G1..G10 (p. 177, Def
   13.6) with the Normal Form Theorem 13.4 and def(M) = cl(M ∪ {M}) ∩ P(M)
   (Cor 13.8, the Jech-side parallel of SZ 1.4); Devlin's Basis Lemma
   VI.1.11 gives rud = compositions of F0..F8. The literal sentence "F is
   rud iff F is a composite of the Gödel operations" appears in NO fetched
   text. Residue: Gandy's paper (paywalled) for his side and for any named
   iff.
4. **Simple functions' Sigma-n role**: the SZ side is now settled
   negatively by [L3.30-X1] (see section 4, item 2); the residue is Zeman,
   "Inner Models and Large Cardinals" ch. 1 (cite-only in the collection;
   the owner's note names chs. 1-2).
5. **The master-code reduction**: SETTLED by [L3.30-X1]; see
   fine-structure.md and section 4, item 9 above.
6. **A sourced GCH-in-L derivation**: SETTLED by [L3.30-L2]'s Devlin ch. II
   fetch: section II.5 "The Condensation Lemma. The GCH in L" is in hand,
   with Theorem 5.6 (V = L implies GCH) and Corollary 5.7 (orchestrator
   verified the section in the fetched text; OCR-degraded scan, to be read
   with the errata list open since WS's inventory covers chs. I and VI,
   not II.5, but the chapter is Devlin's and caution is cheap). SZ's
   consequences chain (1.23-1.27 with 9.1) remains the acceptability-side
   complement.
7. **The Mizar/Metamath/Naproche/AFP landscape**: SETTLED-as-hardened by
   [L3.30-L3] (formalizations-landscape.md): no constructible universe in
   any of the six systems' indices; the virginity claim survives with its
   bounds widened (see section 6). Residual reach limits: post-2022 MML
   additions and unindexed personal repositories.
8. **Zeman's book chs. 1-2** (the owner's note recommends them as the
   reliable fine-structure blueprint): fetch or library; currently
   cite-only.
9. **Jensen's original J-indexing convention**: SETTLED by [L3.30-L2]: the
   manuscript states "In [FSC] we indexed by all ordinals, so that our
   J_{ωα} corresponds to the J_α of [FSC]" (JM p. 49), consistent with SZ
   footnote 4's contrast; Devlin VI.2 (p. 251) agrees.
