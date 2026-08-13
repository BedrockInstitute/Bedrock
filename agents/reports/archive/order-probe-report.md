# Probe report: the order's internal side under the kinded closure (the hole in option B)

Probe run 2026-08-01 on the working tree of `godel-route`. Deliverable:
`_build/probe2/OrderProbe.agda` (green) and this report. No `src/` file
was touched, no git state was changed; the two mid-edit files
(`L.Godel.Name`, `L.WellOrder.Base`) were read only via `git show HEAD:`.
No transient interface errors occurred, so the 60 s retry rule (max 3)
never triggered.

## 1. Verdict

**The hole closes, with candidate 1 (the stratified producer order).**
The paper argument holds: the level-indexed induction is honest because
the kinded step's producers always draw their arguments from the previous
level (verified against the prior probe's layer, `_build/probe/StepProbe.agda:94-206`),
the least producer triple exists under LEM (the triple order is a
lexicographic strict well-order), and the triple determines its member,
so trichotomy follows by pullback; the crux formula (the least-producer
condition for the intersection clause over the previous-level order slot,
the level slot, and the two compared members) typechecks with its
out-reader against the delivered `interAt-out`. **Final A-versus-B
recommendation: build B (the kinded closure tower) with candidate 1**,
the one decisive reason being that B's closure swap nets roughly −1,000
to −2,000 lines against the delivered certificate cluster
(`_build/cut-probe-report.md` §5) while candidate 1's order side is a
wash against A's M5b-d band (≈ +50 to +650 over the memo's 550-1,150,
off by a −210 to +40 Naming swap) and retires A's one unpriced risk, the
skeleton order's own internalization, entirely, because it never mentions
skeletons; the decision stands or falls on the unmeasured 10-clause
kinded step and its Sequence-class assembly, not on the order.

## 2. Candidate 1: the stratified producer order

### 2.1 The paper well-foundedness and trichotomy argument

Fix a stage carrier `A` with the order hypothesis `w` on its members, and
the kinded closure over `A`: cumulative levels `L₀ ⊆ L₁ ⊆ …`, each level a
table of arity-indexed families, with `L_{n+1} = Lₙ ∪ { op-images over
Lₙ }` and the step's clauses drawing every producer's arguments from the
previous level. The order family is defined level by level:

- `ord₀` = `w` (the stage's own order, the step's hypothesis);
- `ord_{n+1}` compares `x, y ∈ L_{n+1}` by first key the first level of
  appearance `firstApp(x) : ℕ` (recovered internally from the level
  table), then by the **least producer triple** `(tag-with-parameters,
  arg₁, arg₂)` in the lexicographic order: tags by the finite tag order
  with numeral parameters by the numeral order and carrier parameters by
  `w` (the delivered Codes parameter-leaf pattern,
  `src/L/Godel/Codes.lagda.md`), then `arg₁`, then `arg₂`, each compared
  by `ordₙ`.

**Well-foundedness.** The induction is on the level index `n`: assume
`ordₙ` is a strict well-order on `Lₙ`. The triple order at level `n+1` is
a lexicographic product of a well-founded tag order (finite, with
numerals and carrier parameters by the well-founded stage order) and
`ordₙ × ordₙ`, hence a strict well-order on the triple type over `Lₙ`;
the least triple of each member exists by `leastOf` under LEM
(`src/L/WellOrder/Base.lagda.md:162`, HEAD). Then `ord_{n+1}` is the
lexicographic product of the natural order on `firstApp` and the
per-level triple order, with the argument descent bounded by `ordₙ` (the
induction hypothesis), so `ord_{n+1}` is well-founded. There is no
circularity: `ord_{n+1}` is defined entirely from `ordₙ` and the level
tables, and the argument recursion is honestly stratified because a
producer's arguments live at level `n`, one below the produced member's
level `n+1` (stress point s1 below).

**Trichotomy.** Map each member to `(firstApp(x), leastTriple(x))`. The
map is injective: equal least triples give equal members, because the
triple records the tag, the parameters, and the arguments, and the member
is the operation applied to them, a function of the triple. `ord_{n+1}`
is the pullback of the lexicographic strict well-order on
`ℕ × (triples)` along this injection, so trichotomy, irreflexivity,
transitivity and well-foundedness all follow from the pullback combinator
(`src/L/Godel/Step.lagda.md:154-167`).

**The two stress points, answered.**

(s1) **Arguments are always previous-level members.** The kinded step's
clauses, as validated by the prior probe's `LayerAt`, apply each
operation to members of the previous level only: intersection, union,
difference and the selections to same-arity members of the previous
level, `values` to an arity-one member of the previous level,
`extendFamily`/`shiftDown` to members of the previous level, and
`allTuples` to the ambient carrier with only a numeral parameter
(`_build/probe/StepProbe.agda:94-206`; `Layer-inter-out`,
`StepProbe.agda:206`). Hence a member first appearing at level `n+1` has
all producer arguments at level `≤ n`, so the recursion is honestly
stratified; the worry that "an argument's own producers tie into the same
level again" is about the argument's *producers*, which draw from one
level below the argument, not about the comparison, which uses the
previous-level order `ordₙ` by definition.

(s2) **Equal least triples give equal members.** Verified: the producer
triple `(tag, params, arg₁, arg₂)` determines the member
`x = op_tag(params, arg₁, arg₂)`, a function of the triple, so if the
least triples of `x` and `y` are equal, `x ≡ y`, and trichotomy holds.
Two gaps beyond the brief's formulation surfaced, both small:
1. **Level-0 (seed) members have no producers.** They are embedded as
   the seed-tag with the carrier member as a parameter (the delivered
   Codes parameter-leaf pattern), which makes the seed map injective and
   gives every seed member a definite, least triple; the parameter
   comparison uses `w`, available at level 0.
2. **Unary/nullary shapes need a canonical filler** to fit the triple
   format. The honest fix is a fixed filler member of the closure present
   at every level `≥ 1` (e.g., the canonical nullary-produced member), by
   cumulativity; over a nonempty stage the seed provides one at level 0.
   A small lemma, not a structural break; the report prices it below.

**The internal side, and why it needs no certificate.** The successor
clause of the order-family table is a direct formula over the closure
level tables, the previous-level order set, and the two compared members:
`firstApp` is expressible as a least-numeral bounded formula, "producer
of x" as a formula over the delivered op descriptions plus membership
atoms (`interAt`, `valuesAt`, `allTuplesAt`, `src/L/Godel/Definable.lagda.md:387-412,
578-641, 665-844`), "least" as the bounded quantification "no producer
triple is strictly below", and the triple comparison as lexicographic
atoms in the previous-level order set. The step condition quantifies an
inner order-family table (level number ↦ order set) alongside the
closure's level table, with functionality, the base clause (level-0
order = the order-below slot), and the successor clause; junk inner
tables are excluded because the successor clause is a definite
description (a comprehension over the level tables and the previous
value), so functionality plus the base and successor clauses determine
the table uniquely by meta-induction on the level number (the same
discipline as the closure's own level table, no per-member provenance,
no certificate).

### 2.2 What `OrderProbe.agda` proves

`_build/probe2/OrderProbe.agda` (317 lines) validates the crux:

1. **The first-appearance comparison atom.** `LevelLtAt`
   (`OrderProbe.agda:59`) is the formula over two level-number slots
   saying the numeral at slot `b` is a member of the numeral at slot `a`
   (the von Neumann order, "b < a as numerals"); its reader
   `LevelLt-out` (`OrderProbe.agda:69`) recovers the model-level fact
   `⟨ fst y ∈ fst x ⟩` with both values pinned to the slots, and
   `numeralL-mem` (`OrderProbe.agda:85`) translates the internal numeral
   membership back to the host naturals (`q < p`), by induction on `p`
   through `numeralL-suc`/`numeralL-zero` and `#-inj′`.
2. **The least-producer condition for the intersection clause.**
   `LeastProdInterAt` (`OrderProbe.agda:200`) is the full formula over
   the slots (previous-level order slot `o`, level slot `p`, the two
   compared members `x`, `y`): both members arise at the next level by
   the intersection clause from same-arity members of the previous level,
   the triple of `x` is lexicographically below the triple of `y`
   (numeral `k` first, then the arguments in the previous-level order
   `o`), and each triple is **least** among its member's intersection
   producers (the `leastXAt`/`leastYAt` conjuncts, `OrderProbe.agda:163-195`,
   are unbounded ∀-quantifiers over the model with the production
   condition as antecedent). Its out-reader `LeastProdInter-out`
   (`OrderProbe.agda:219`) unpacks satisfaction to the two producer
   triples with `x = pr k (X ∩ Y)` and `y = pr k' (X' ∩ Y')`, the four
   same-arity previous-level memberships, and the lexicographic
   comparison data, discharging the intersection equations through the
   delivered `interAt-out` (`src/L/Godel/Definable.lagda.md:406`) and the
   pair/application readers `prAtL-adequate`/`appAt-adequate`
   (`src/L/Coding/Model.lagda.md:125-166`), in the style of the prior
   probe's `InterDisj-out` (`StepProbe.agda:102-123`). The least-ness
   conjuncts are projected away by the reader, exactly as the layer
   readers of the prior probe project their disjunctive branches.

Timings (wall clock, probe checked from scratch, warm tree; the 180 s
wall never approached):

| run | wall |
|---|---:|
| first full check after the final edit | ~2.1-2.3 s |
| three consecutive warm runs | 1.52, 1.53, 1.45 s |

The prior probes (`StepProbe`, `CutProbe`) re-check green; the working
tree's `L.Godel.*` interfaces used by the probe are those of HEAD (the
two mid-edit files were not imported by the probe).

### 2.3 The priced internal side

| chapter | estimate (Agda lines) |
|---|---:|
| Naming re-implementation: `Name` = producer triples at the birth (Σ over tags with numeral and carrier parameters and two closure members), `denote` = op application (10-branch case), `names-complete` = closure completeness at the values cut (transport through the closure's terms-to-levels lemma), `nameOrder` = the stratified order at the birth level (tag lex with the stage order on carrier parameters and the closure order on arguments, packaged as one SWO over the level family), `leastName` = `leastOf` | 350-600 |
| the Cond supplier (M5b-equivalent): the step condition over the closure level table and the order-family table with functionality, base clause, successor clause, and the firstApp/least-producer comparison | 250-400 |
| the order-family table itself: the ω-recursion (Sequence-class), functionality, base/successor clauses, uniqueness by meta-induction on level numbers | 250-400 |
| adequacy against the scaffold (`orderL-fill`/`orderL-rep` at M5d): the two readings plus the level-by-level induction matching the internal table to the meta stratified order | 200-400 |
| the canonical-filler lemma (unary/nullary shapes, empty-stage case) | 20-50 |
| **order-side total** | **1,070-1,850** |

The collector (`module Described`, `src/L/Choice/Table.lagda.md:348`)
and the Bound assembly are shared with option A; only the Cond changes
content. The Naming interface is verified compatible with the untouched
scaffold `src/L/Godel/Step.lagda.md` at its six consumption sites
(`Name`, `denote`, `names-complete`, `nameOrder`, `leastName`, `_≺ₙ_`,
`Step.lagda.md:186-256`, against the interface at
`src/L/Godel/Name.lagda.md:95-106, 522-543`), same names, same
signatures, `Name : Type ℓ`, `denote : Name → S`.

**What candidate 1 retires** (all priced honestly as sunk): the M5a
skeleton re-cut (~560 working-tree lines in flight, `_build/cut-probe-report.md`
§3.3), the tree chapter (`Tree`, 378 lines, `_build/deep-levers.md` §2),
and the tree/skeleton order; with them, the unpriced risk that the
skeleton order's own internalization re-grows a Limit/Before-class
recursion (`_build/deep-levers.md:92-93` and §6.1, priced there at
1,000-1,600 if required) is gone, because candidate 1 never mentions
skeletons or `limitOrder`.

## 3. Candidate 2: the skeleton-directed evaluation table

**NO-GO: it converges back to option A's certificate.** The evaluation
table keyed by a skeleton `s`'s own subtree positions has junk keys
impossible (positions come from `s`), but junk *skeletons* are not
excluded by reading `s` with pair projections: a non-skeleton set (not a
well-founded, finite, correctly labelled tree code) satisfies every
finite-depth projection reading, and "`s` is a bona fide skeleton" is
not first-order definable in the object language without a finiteness or
rank predicate. Excluding junk skeletons requires either quantifying over
a definable skeleton code set (the old route's finite subterm-code set,
which is the deleted `Codes` chapter and is unpinnable under route C
because the codes embed carrier parameters (`dev/PLAN.md:1123`, the
junk-table finding that created `CertAt`), or a decode certificate
witnessing `s`'s finite decoding, which is precisely the Tower honesty
machinery (`CertAt`, `src/L/Godel/Tower.lagda.md:1204-1230`; the honesty
induction at `Tower.lagda.md:1241-1269`). Either way the design re-grows a
large fraction of the deleted `Codes`+`Tower` content (the per-entry
annotation table and its honesty induction) for the skeleton side, on top
of the closure swap it was meant to save. There is no honest cheap
version of "the formula reads `s`'s structure"; candidate 2 does not beat
option A's certificate, it rebuilds it.

## 4. The A-versus-B table

| | A: delivered route (certificate + skeleton order) | B: kinded closure tower + candidate 1 |
|---|---|---|
| closure side remaining work | none (Codes+Table+Tower delivered green) | new closure chapters 1,220-2,060 (`cut-probe-report.md` §2.4) replacing Codes 277 + Table 1,562 + Tower 2,130 (≈3,000 Agda lines, §5) |
| order-internal side (M5b-d) | 550-1,150 (memo price minus Tower reuse, `PLAN.md:1123`), plus unpriced skeleton-internalization risk 0-1,600 (`deep-levers.md:92-93`, §6.1) | Cond + order-family table 700-1,200; Naming re-implementation 350-600 (replaces the sunk ~560-line skeleton Naming and the 378-line Tree chapter) |
| collector + Bound (M5c/d) | shared | shared (unchanged) |
| total remaining work | 550-1,150 (+ 0-1,600 risk) | 2,290-3,910 (closure 1,220-2,060 + Cond/O-table 700-1,200 + Naming 350-600 + filler lemma 20-50) |
| landing | 15,000-15,700 (post-compression, `PLAN.md:1123`); with the skeleton risk, 16,000-17,300 | ≈13,200-14,500 closure anchor (`cut-probe-report.md` §5) + order drift (−160 to +690) ≈ **13,400-14,800** (honest range 13,040-15,190) |
| net vs A | baseline | **−1,000 to −2,000 on the closure swap, order side a wash**; vs A-with-risk, −2,300 to −3,900 |
| risk list | skeleton internalization unpriced (the Limit/Before-class recursion); certificate is green | the full 10-clause kinded step and its Sequence-class assembly unmeasured (largest item, from `cut-probe-report.md` §5); the successor clause's unbounded ∀-least conjuncts are the check-time hazard class (the route's P-d wall class for satisfactions of concrete formulas); the fill direction and the other clauses' out-readers unproved; the empty-stage filler lemma unproved |

**Pedagogy note.** The stratified producer order's story is the closure's
own recursion told again: each level's order is a strict well-order given
the previous level's, and the tie-break is "the least construction of the
member", recovered by formula from the level tables rather than stored.
That is one induction the reader already carries from the closure
chapter, and the spine's least-name idea survives unchanged (the name is
the producer triple, the least name is the least producer). The
certificate's story is "provenance is recorded and audited": honest, but
it asks the reader to accept a per-member annotation table and an honesty
induction as the price of the same mathematics. For the book's stated
pedagogy gate, candidate 1 is the more teachable story; its honest cost
is that the reader must also accept the order-family ω-recursion beside
the closure's own level recursion, which is one more Sequence-class
object in the same chapter family.

## 5. What remains unprovable/unmeasured after this probe

1. **The full 10-clause kinded step and its Sequence-class assembly**
   (the closure chapter's measured line count and cold-check time); the
   probe validated one clause of the order condition, and the prior probe
   validated three closure clauses (`StepProbe.agda:62-131`).
2. **The order-family table's measured cost and cold-check time**; the
   successor clause's unbounded ∀-least conjuncts are the largest
   check-time question (the route's measured wall class for satisfactions
   of concrete formulas, memo §9's P-d, is exactly the shape the adequacy
   proofs will hit).
3. **The adequacy of the internal order-family table against the meta
   stratified order** (only the inter-clause out-reader is green; the
   fill direction, the other clauses' out-readers, and the
   `orderL-fill`/`orderL-rep` assembly at M5d are priced, not proved).
4. **The Naming meta assembly** (the whole-closure stratified order
   packaged as one SWO over the level family) is priced at 350-600, not
   measured.
5. **The empty-stage canonical-filler lemma** (whether the nullary
   producer provides a uniform filler at every level) is assessed
   meta-theoretically and priced at 20-50 lines, not proved.
6. **Candidate 2's junk-skeleton exclusion** is settled meta-theoretically
   (it re-grows the certificate); no Agda was spent on it, since the
   verdict is negative on its face.
7. The scaffold's `Naming` interface compatibility is verified against the
   consumption sites (`src/L/Godel/Step.lagda.md:186-256`), but the
   working-tree M5a re-cut itself is mid-edit and was not re-checked
   against candidate 1's interface (it is retired by candidate 1 anyway).

The mathematics on the record: the stratified producer order is
well-founded and trichotomous (paper argument in §2.1), its least-name
tie-break is expressible over the kinded closure with a direct-formula
successor clause and no certificate (crux green in `OrderProbe.agda`),
the skeleton alternative converges back to the certificate (§3), and the
A-versus-B decision is carried by the closure swap, which favors B by
1,000-2,000 lines with the order side a wash (§4).
