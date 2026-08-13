# Geology dossier: set-theoretic geology sources and the five questions

Task `[L3.32-T12]`, attempt 2. Purpose: fetch and pin the set-theoretic
geology primary sources that the in-repo corpus currently lacks (zero hits
for mantle, grounds, Hamkins, Usuba, Laver, approximation across all 13,645
lines of primary sources, per `agents/tasks/archive/L3-31-GLPROBE/l3.31-glprobe-report.md`), and answer
the five questions the geology phase of `dev/PLAN.md` section 6.1 `[L6]`
needs answered. House rules: every claim carries its source and location; no
memory-sourced claims (anything uncited is marked UNVERIFIED with what would
settle it); no em dash; English only; paywalled material reported as
paywalled, never worked around.

This file is written incrementally: sections below are filled as each answer
lands, so an interruption leaves a partial but real deliverable.

## Sources

Targets, in priority order:

1. Fuchs, Hamkins, Reitz, "Set-theoretic geology" (arXiv:1107.4776).
2. Laver, and Woodin, on ground model definability (approximation and cover
   properties).
3. Usuba, "The downward directed grounds hypothesis and very large
   cardinals" (arXiv:1707.05132).
4. Reitz on the Ground Axiom; Hamkins on the approximation and cover
   properties, if reachable.

Per-source entries go here as they are fetched or ruled out: citation, URL,
access status (open / paywalled / cite-only), what was read, and which
sections of this dossier consume it.

### S1. Fuchs, Hamkins, Reitz, "Set-theoretic geology"

Citation: Gunter Fuchs, Joel David Hamkins, Jonas Reitz, "Set-theoretic
geology", arXiv:1107.4776 (v1 24 Jul 2011, v2 18 Nov 2014); published in
Annals of Pure and Applied Logic 166(4):464-501, 2015 (PhilPapers citation
metadata).
- arXiv abstract page (fetched 2026-08-04): https://arxiv.org/abs/1107.4776
- ar5iv HTML rendering (fetch timed out through the page tool; quoted via
  search-indexed snippets only): https://ar5iv.labs.arxiv.org/html/1107.4776
- Access: open (arXiv preprint; full text not machine-fetchable by the
  available page tool, see "Paywalled or unfetched").
- Read: the complete abstract verbatim (ground, GA, bedrock, mantle, generic
  mantle, generic HOD; the mantle/generic mantle/ZFC theorems; inner mantles
  and the outer core), plus ar5iv-indexed snippets on the ground-model
  definability theorem and the GA/bedrock wording.
- Consumed by: sections 1, 2, 5.

### S2. Laver; Woodin: ground model definability

Laver, Richard. "Certain very large cardinals are not created in small
forcing extensions." Annals of Pure and Applied Logic 149(1-3):1-6, 2007.
DOI 10.1016/j.apal.2007.07.002.
- ScienceDirect article page (volume listing marks it open archive; the
  article body is PDF, not machine-fetchable by the available page tool):
  https://www.sciencedirect.com/science/article/pii/S0168007207000607
- zbMATH review record (Zbl 1128.03046; page returned HTTP 403; metadata
  via search snippet): https://zbmath.org/1128.03046
- Access: open archive at the publisher for the article page; the theorem
  statements used here are quoted from Gitman-Johnstone (S5) and Hamkins'
  Ground Axiom talk (S6), both open.
- Role: the paper in which Laver published the positive answer that a ground
  model is definable in its set-forcing extensions, as a by-product of a
  study of whether very large (rank-into-rank style) cardinals can be
  created by small forcing. The paper's own abstract (PhilPapers indexed
  snippet): "The large cardinal axioms of the title assert, respectively,
  ... which extends to an elementary j: V_{lambda+1} -> V_{lambda+1}. It is
  known that these axioms are preserved in passing from a ground model to a
  small forcing extension. In this paper the reverse directions of these
  preservations are proved." (S5's account adds that the ground model
  definability result is published in this same paper.)
- Consumed by: sections 2, 5.

Woodin, W. Hugh. "Recent developments on Cantor's Continuum Hypothesis."
In Proceedings of the Continuum in Philosophy and Mathematics, Carlsberg
Academy, Copenhagen, November 2004. Woodin's independent proof of ground
model definability appeared in the appendix of this paper (S5's account).
Cite-only: proceedings text not located open.
- Consumed by: section 2 (attribution line only).

### S3. Usuba, "The downward directed grounds hypothesis and very large cardinals"

Citation: Toshimichi Usuba, "The downward directed grounds hypothesis and
very large cardinals", arXiv:1707.05132 (v1 17 Jul 2017, v2 20 Jul 2018);
published in Journal of Mathematical Logic 17(2):1750009, 2017 (PhilPapers
metadata).
- arXiv abstract page (v2 fetched 2026-08-04): https://arxiv.org/abs/1707.05132
- ar5iv HTML rendering (fetch timed out through the page tool; quoted via
  search-indexed snippets only): https://ar5iv.labs.arxiv.org/html/1707.05132
- Access: open (arXiv preprint).
- Read: the complete v2 abstract verbatim; search-indexed snippets of the
  introduction (Laver/Woodin attribution and the FHR uniform definability
  refinement).
- Consumed by: sections 1, 3, 5.

### S4. Reitz on the Ground Axiom

Reitz, Jonas. "The Ground Axiom." Ph.D. dissertation, CUNY Graduate Center,
June 2006. Abstract reproduced on Hamkins' site (fetched 2026-08-04):
https://jdh.hamkins.org/jonas-reitz/

Reitz, Jonas. "The Ground Axiom" (paper; arXiv:math/0609270). The ar5iv
rendering is indexed and states that L, L[0#] and L[mu] satisfy the Ground
Axiom (quoted in section 4):
https://ar5iv.labs.arxiv.org/html/math/0609270
- Access: open (arXiv).
- Consumed by: sections 1, 4.

### S5. Gitman, Johnstone, "On ground model definability"

Citation: Victoria Gitman and Thomas A. Johnstone, "On ground model
definability", in Infinity, Computability, and Metamathematics: Festschrift
in honour of the 60th birthdays of Peter Koepke and Philip Welch, College
Publications, 2014.
- Author page with full text (fetched 2026-08-04):
  https://victoriagitman.github.io/publications/2013/06/25/on-ground-model-definability.html
- Author talk page "Ground model definability in ZF" (fetched 2026-08-04),
  quoted for the uniform formula, the good-model test, and Usuba's ZF
  result: https://victoriagitman.github.io/talks/2019/10/10/ground-model-definability-in-zf.html
- Access: open.
- Read: the Laver-Woodin theorem verbatim with its parameter, Hamkins'
  delta-cover and delta-approximation definitions, the uniqueness theorem,
  and Laver's proof outline.
- Consumed by: section 2.

### S6. Hamkins, "The Ground Axiom" talk (arXiv:1607.00723)

Citation: Joel David Hamkins, "The Ground Axiom" (talk/notes page,
arXiv:1607.00723). Fetched 2026-08-04:
https://ar5iv.labs.arxiv.org/html/1607.00723
- Access: open.
- Read: the Ground Axiom and Bedrock Axiom definitions verbatim; Theorem 1
  (Reitz, Woodin: GA is first-order expressible); Theorem 2 (Laver: the
  ground model is a definable class in its set-forcing extension); Key
  Definition 3 (delta-covering, delta-approximation); Theorem 4 (extensions
  with the properties have no new large cardinals); Theorems 5-7 (Reitz's
  consistency results); Question 8 (uniqueness of bedrock); the first-order
  treatment of the spectrum of grounds.
- Consumed by: sections 1, 2, 4, 5.

### S7. Hamkins, "Approximation and cover properties propagate upward"

Citation: Joel David Hamkins, "Approximation and cover properties propagate
upward", jdh.hamkins.org, 30 June 2013. Fetched 2026-08-04:
https://jdh.hamkins.org/approximation-and-cover-properties-propagate-upward/
- Access: open.
- Read: verbatim definitions of the delta-approximation and delta-cover
  properties for transitive inner models, and the upward propagation
  theorem with proof.
- Consumed by: sections 2, 5.

### S8. Hamkins, Bonn Logic Seminar talk, January 2017

Citation: Joel David Hamkins, "Set-theoretic geology and the downward
directed grounds hypothesis", Bonn Logic Seminar, 13 January 2017. Fetched
2026-08-04:
https://jdh.hamkins.org/set-theoretic-geology-and-the-downward-directed-grounds-hypothesis-bonn-2017/
Same-titled CUNY Set Theory seminar page, September 2016 (fetched
2026-08-04), quoted for the full consequence list and the comment thread:
https://jdh.hamkins.org/set-theoretic-geology-and-the-downward-directed-grounds-hypothesis-cuny-set-theory-seminar-september-2016/
- Access: open.
- Read: the abstract with Usuba's strong downward directed grounds result
  and the hyper-huge cardinal consequence.
- Consumed by: sections 1, 3.

### S9. Fuchs' talk slides on set-theoretic geology

Citation: Gunter Fuchs, "Set-theoretic geology" (talk slides, University of
Bern; retrieved via search snippet):
https://www.lc08.iam.unibe.ch/slideUpload/talks/Fuchs07071846.pdf
- Access: open PDF, not machine-fetchable by the available page tool; one
  sentence quoted via search snippet only.
- Consumed by: sections 1, 5.

### S10. Hamkins, "Extensions with the approximation and cover properties have no new large cardinals"

Citation: Joel David Hamkins, Fundamenta Mathematicae 180(3):257-277, 2003.
Not fetched; cited by S6 and S7 as the origin of the approximation and
cover properties. Cite-only.
- Consumed by: section 2 (attribution line only).

### S11. MathOverflow, revision notes on "Concept of bedrock and mantle in the multiverse view"

Question 459136 revision notes (public content; located via search snippet;
the page HTML returns HTTP 403 to the page tool, and the StackExchange API
returns BAD_CONTENT; the quote in section 4 comes from three consistent
revision snapshots indexed by search):
https://mathoverflow.net/posts/459136/revisions
- The answer claims the mantle of L[G] is L; section 4 uses it with this
  verification caveat.

## 1. The definitions

The exact definitions this development would have to formalize: ground,
mantle, generic mantle, bedrock, the Ground Axiom, as stated in the sources,
not as remembered.

The founding paper's abstract states them in the authors' own words (S1,
https://arxiv.org/abs/1107.4776). Verbatim:

- **Ground.** "A ground of the universe V is a transitive proper class W
  subset V, such that W is a model of ZFC and V is obtained by set forcing
  over W, so that V = W[G] for some W-generic filter G subset P in W." (S1,
  abstract.) Usuba's abstract opens with the same notion: "A transitive
  model M of ZFC is called a ground if the universe V is a set forcing
  extension of M." (S3, abstract.)
- **The Ground Axiom (GA).** "The model V satisfies the ground axiom GA if
  there are no such W properly contained in V." (S1, abstract.) Hamkins'
  Ground Axiom talk gives the same assertion in full: "The universe is not a
  forcing extension of any inner model by nontrivial set forcing.
  Specifically, if W is a transitive inner model of ZFC properly contained
  in V and G subset P in W is W-generic, then V is not W[G]." (S6, Ground
  Axiom box; the ar5iv rendering there garbles the subset symbols, restored
  here.) The FHR ar5iv rendering reads: "The ground axiom GA is the
  assertion that the universe is not obtained by set forcing over any
  strictly smaller ground model." (S1, ar5iv-indexed snippet.)
- **Bedrock.** "The model W is a bedrock of V if W is a ground of V and
  satisfies the ground axiom." (S1, abstract.) Hamkins' talk spells out the
  intended meaning: "The model W is a bedrock model for V in the sense that
  it is a minimal ground model for V, having no ground model below it. This
  axiom is first order expressible for the same reasons that the Ground
  Axiom was. Since V = W is allowed, we have GA implies BA." (S6, Bedrock
  Axiom box.) Reitz's dissertation abstract defines the related Bedrock
  Axiom: "the universe is a set-forcing extension of a model satisfying the
  Ground Axiom" (S4).
- **The mantle.** "The mantle of V is the intersection of all grounds of V."
  (S1, abstract; same wording in Hamkins' Bonn talk, S8.) Fuchs' slides add
  the point that makes the definition usable: "The Mantle M is the
  intersection of all grounds. This mere definition is already an
  application of the uniform definability of grounds: The Mantle is a first
  order definable transitive class." (S9.)
- **The generic mantle.** "The generic mantle of V is the intersection of
  all grounds of all set-forcing extensions of V." (S1, abstract.)
- **The generic HOD.** "The generic HOD, written gHOD, is the intersection
  of all HODs of all set-forcing extensions." (S1, abstract.) A related but
  distinct intersection, included for completeness of the definition layer.
- **The inner mantles and the outer core.** "Iteratively taking the mantle
  penetrates down through the inner mantles to what we call the outer core,
  what remains when all outer layers of forcing have been stripped away."
  (S1, abstract.)

Companion facts stated in the same abstract (S1): "The generic HOD is always
a model of ZFC, and the generic mantle is always a model of ZF. Every model
of ZFC is the mantle and generic mantle of another model of ZFC. We prove
this theorem while also controlling the HOD of the final model, as well as
the generic HOD."

Definition locations inside the 44-page paper (section and definition
numbers) are NOT yet pinned: the ar5iv full text is not machine-fetchable by
the available page tool, and only search-indexed snippets have been quoted.
This is recorded under "Paywalled or unfetched" with what would settle it.
The wording above is the authors' own (abstract and indexed snippets), not a
memory reconstruction.

## 2. Ground model definability

The exact statement of the Laver-Woodin theorem, its hypotheses, what its
proof needs, and precisely what it buys (in particular for the mantle's
universe-size wall measured in `agents/tasks/archive/L3-31-GLPROBE/l3.31-glprobe-report.md` section 2.3).

The theorem, verbatim from Gitman and Johnstone (S5, "Theorem 1 [Laver,
Woodin]"):

> Suppose V is a model of ZFC, P is a forcing notion in V, and G subset P is
> V-generic. Then in V[G], the ground model V is definable from the
> parameter P(gamma)^V, where gamma = |P|^V.

Hamkins' Ground Axiom talk states it without the parameter detail (S6,
"Theorem 2 (Laver)"): "If V is a set forcing extension of V[G], then V is a
definable class in V[G], using parameters in V." The ar5iv rendering there
swaps the two model symbols; the surrounding sentence and S5 make the
direction unambiguous: the ground V is definable inside its extension V[G].
The same talk records: "This result was also observed independently by
Woodin." (S6.) The FHR paper's ar5iv-indexed sentence (S1): "The
ground-model definability theorem was proved independently by Laver and
Woodin, and proved by Hamkins in the strengthened form of theorem 6, below,
which extends the result beyond set-forcing to include also many natural
instances of class forcing and non-forcing extensions."

**Uniformity and the refined parameter.** The definition is uniform across
all ZFC-universes. Gitman's talk page states it verbatim: "there is a single
formula phi(x,y) such that whenever V models ZFC and V[G] is a set-forcing
extension of V by a poset P in V of size |P|^V = gamma, then V is defined in
V[G] by phi(x, P^V(delta)) with delta = (gamma+)^V = (gamma+)^V[G]" (S5,
"Ground model definability in ZF" talk page, symbols restored). Gitman and
Johnstone add: "Indeed, this definition of the ground model is uniform
across all its set-forcing extensions. There is a first-order formula
which, using a ground model parameter, defines the ground model in any
set-forcing extension." (S5.) The FHR refinement is a uniform definition of
all ground models of the universe at once, as Usuba's introduction puts it:
"a ground model is definable in its set-forcing extension. Later,
Fuchs-Hamkins-Reitz refined Laver and Woodin's result, and they give a
uniform definition of all ground models of the universe" (S3,
ar5iv-indexed snippet).

**Hypotheses.** The base theorem assumes V models ZFC, P a set forcing
notion in V, G V-generic. The proof needs only a finite fragment ZFC* of
ZFC at reflected levels (S5's talk page describes the "good model" test:
transitive M with M models ZFC*, P^M(delta) = P^V(delta),
(delta+)^M = (delta+)^V[G], and the pair M subset V[G]_lambda satisfying
delta-cover and delta-approximation). No inaccessible or other large
cardinal hypothesis is needed (S5).

**What the proof needs: the approximation and cover properties.** The
technical core is Hamkins' delta-approximation and delta-cover properties,
defined verbatim (S7, jdh.hamkins.org, 30 June 2013):

- The extension W subset V satisfies the delta-approximation property if
  whenever A subset W is a set in V and A intersect a is in W for any a in
  W of size less than delta in W, then A is in W.
- The extension W subset V satisfies the delta-cover property if whenever A
  subset W is a set of size less than delta in V, then there is a covering
  set B in W with A subset B and |B|^W less than delta.

S5 renders the same properties for pairs V subset W with cardinalities taken
in W and V respectively; S6's Key Definition 3 phrases them for V subset
V[G] (delta-covering and delta-approximation, with A a set of ordinals in
the covering clause). The notions are due to Hamkins (S10), per S5 and S6.
Hamkins' theorem on when they hold (S5, Theorem 2): if P factors as
R * Q-dot where R is nontrivial of size less than delta and R forces Q-dot
to be strategically less-than-delta closed, then V subset V[G] satisfies
delta-cover and delta-approximation (in particular any forcing of size less
than delta does; S6). The uniqueness theorem that makes definability go (S5,
Theorem 3): if V, V' and W are transitive ZFC models, delta is regular in W,
both pairs V subset W and V' subset W have delta-cover and
delta-approximation, P(delta)^V = P(delta)^V', and (delta+)^V = (delta+)^W,
then V = V'.

Laver's proof combines these (S5, verbatim outline): a forcing extension
V[G] by a poset of size gamma has the delta-cover and delta-approximation
properties for delta = gamma+, and (delta+)^V = (delta+)^V[G]; there is an
unbounded definable class C of ordinals on which both properties reflect
down to V_lambda subset V[G]_lambda with a large enough fragment ZFC*; the
V_lambda are then defined in V[G] as the unique transitive ZFC* models M of
height lambda with P(delta)^M = s and the pair M subset V[G]_lambda having
the properties; and the parameter s = P(delta)^V is reduced to P(gamma)^V
using the delta-approximation property.

**Precisely what it buys.** Three things, each load-bearing for this book:

1. The collection of all grounds becomes first-order: "One important
   consequence of uniform ground model definability is that it makes it
   possible to define in a first-order way the collection of all grounds of
   a ZFC-universe. A priori this is a collection of classes, a second-order
   notion, but using ground model definability we can write down a
   first-order formula psi(x,y) such that for every set a, the class
   W_a = {x | psi(x,a)} is a ground of V and for every W ground of V, there
   is a set a such that W = W_a." (S5, "Ground model definability in ZF"
   talk page.) Hamkins' talk says the spectrum of possible ground models is
   "entirely a first order affair of ZFC" (S6).
2. The mantle becomes a first-order definable transitive class (S9, Fuchs'
   slides). The Ground Axiom becomes first-order expressible (S6, Theorem 1,
   credited to Reitz and independently Woodin), and the Bedrock Axiom with
   it (S4, S6).
3. Against the POC's measured wall: the probe's mantle
   `Mantle x = (W : Class) -> IsGround W -> < W x >` lands in
   `Type (ell-suc (ell-suc ell))`, one universe too big to be a Class,
   because it quantifies over `Class` (glprobe report, section 2.3). The
   definability theorem is what replaces that class quantification with a
   first-order formula over set parameters, discharging the `MantleIsClass`
   debt: the report prices that discharge at 0.8-1.6k lines "via the
   definability theorem" against 0.05k "via Base.Impredicativity" (glprobe
   report, section 2.4). In other words, the theorem does not shrink the
   universe: it converts a type-theoretic universe-level obligation (the
   mantle is not small enough to be a class predicate) into a definability
   obligation (there is a first-order formula coextensive with the
   intersection of all grounds).

Status: filled. Open item: the FHR paper's theorem 6 statement (Hamkins'
strengthened class-forcing version) is quoted only from the indexed
snippet; its full statement needs the ar5iv text.

## 3. Downward directed grounds

Statement, status, what Usuba proved and under what hypotheses.

**The definition (Fuchs, Hamkins, Reitz).** Usuba's paper states it verbatim
(S3, ar5iv-indexed introduction): "The downward directed grounds hypothesis,
DDG, is the assertion that every two ground models have a common ground
model. The strong DDG is the assertion that every collection of ground
models indexed by some set {Wr : r in X} has a common ground model." Usuba's
slides attribute the notion to the founding paper (Fuchs, Hamkins, Reitz):
"Definition (Fuchs-Hamkins-Reitz) The downward directed grounds hypothesis
(DDG, for short) is the assertion that every two ground models have a common
ground model" (Usuba's NUS slides, imsarchives.nus.edu.sg, search-indexed
snippet). Hamkins' account adds the history: "Reitz had inquired in his
dissertation whether any two grounds of V must have a common deeper ground.
Fuchs, myself and Reitz introduced the downward-directed grounds hypothesis
DDG and the strong DDG, which asserts a positive answer, even for any
set-indexed collection of grounds, and we showed that this axiom has many
interesting consequences for set-theoretic geology." (S8, CUNY seminar page,
September 2016.)

**Status: a ZFC theorem, not a hypothesis.** Usuba proved the strong DDG
unconditionally. The paper's abstract (S3): "We show that the grounds of V
are downward set-directed." Hamkins (S8, CUNY page): "Last year, Usuba
proved the strong DDG, and I shall give a complete account of the proof,
with some simplifications I had noticed." And: "This breakthrough result
answers what had been for ten years the central open question in the area of
set-theoretic geology and leads immediately to numerous consequences that
settle many other open questions in the area, such as the fact that the
mantle coincides with the generic mantle and is a model of ZFC." (S8, CUNY
page.) So DDG and strong DDG are theorems of ZFC (Usuba 2016, published
2017), not axioms one assumes.

**Consequences, verbatim from Hamkins' CUNY seminar page (S8):**

- Bedrock models are unique when they exist.
- The mantle is absolute by forcing.
- The mantle is a model of ZFC.
- The mantle is the same as the generic mantle.
- The mantle is the largest forcing-invariant class, and equal to the
  intersection of the generic multiverse.
- The inclusion relation agrees with the ground-of relation in the generic
  multiverse. That is, if N subset M are in the same generic multiverse,
  then N is a ground of M.
- If ZFC is consistent, then the ZFC-provably valid downward principles of
  forcing are exactly S4.2.
- (Usuba) If there is a hyper-huge cardinal, then there is a bedrock for the
  universe.

The paper's own abstract adds two corollaries stated without hypotheses (S3):
"(1) the mantle, the intersection of all grounds, must be a model of ZFC.
(2) V has only set many grounds if and only if the mantle is a ground."
Hamkins' Bonn talk adds the forcing-size sharpening (S8): "if there is a
hyper-huge cardinal kappa, then the universe indeed has a bedrock and all
grounds use only kappa-small forcing."

**What Usuba proved about large cardinals, and the exact hypotheses.** The
2017 paper's abstract states only: "We also show that if the universe has
some very large cardinal, then the mantle must be a ground." (S3.) The named
cardinal in Hamkins' account of Usuba's result is hyper-huge (S8, CUNY and
Bonn pages). Usuba's own follow-up paper proves the theorem for the weaker
extendible hypothesis: "Extendible cardinals and the mantle", Archive for
Mathematical Logic 58(1-2):71-75, 2019 (arXiv:1803.03944), whose abstract
reads "The mantle is the intersection of all ground models of V. We show
that if there exists an extendible cardinal then the mantle is the smallest
ground model of V." (arXiv abstract via ADS/scholar.archive indexed
snippets; the paper's Theorem 1.3 is quoted in Lietz's thesis as "Suppose
there exists an extendible cardinal. Then the mantle is a ground of V.")
The same paper notes the hierarchy: "Every hyper-huge cardinal is an
extendible cardinal limit of extendible cardinals" (arXiv:1803.03944
indexed snippet), so extendible is the weaker hypothesis of the two.
Goldberg states the consequence as: "A consequence of Usuba's Theorem is
that if there is an extendible cardinal, the mantle satisfies the Ground
Axiom." (arXiv:2108.06903, ar5iv-indexed snippet.)

**A discrepancy to flag for the owner.** PLAN section 6.1's far horizon
describes "Usuba's bedrock theorem (strongly compact implies the mantle is a
ground)". None of the sources fetched for this dossier state that. The named
hypotheses in the fetched literature are hyper-huge (Hamkins' account of
Usuba 2017) and extendible (Usuba 2019, Theorem 1.3). Strongly compact
appears in the fetched material only in a different context, an improvement
of Woodin's HOD dichotomy to a strongly compact cardinal (PhilPapers
indexed snippet on extendible cardinals), which is not the mantle-is-a-ground
theorem. The PLAN's phrase is therefore UNVERIFIED against the fetched
sources; what would settle it: the exact statement in the 2017 JML paper
(full text not machine-fetchable here, see "Paywalled or unfetched"), or an
owner ruling on whether the far horizon should say extendible/hyper-huge.

Status: filled, with the one flagged discrepancy and the open item that the
2017 paper's own theorem numbering was not pinned (quoted via the abstract
and Hamkins' accounts).

## 4. "L is a bedrock" in the literature

Is the meeting theorem this book aims at stated anywhere in the literature?
If so, where and in what form; if folklore, the nearest cited statement.

**The exact trophy statement, verbatim, is NOT located as a standalone
theorem in the fetched primary sources.** What is located, in increasing
proximity to the book's "L is a bedrock":

1. **L satisfies the Ground Axiom (Reitz).** Reitz's paper "The Ground
   Axiom" (arXiv:math/0609270) proves: "The constructible universe L, the
   model L[0#], and the canonical model of a measurable cardinal L[mu] all
   satisfy the Ground Axiom. Proof. In each case ..." (arXiv PDF of
   math/0609270, page-indexed search snippet; the ar5iv rendering of the
   same sentence is garbled by symbol swaps, and the ar5iv page itself
   times out through the page tool). Since the Ground Axiom asserts there is
   no proper ground, "L satisfies GA" is exactly "L has no proper ground",
   i.e. L is a bedrock of itself (V = W allowed in the Bedrock Axiom, S6).
   Hamkins' Ground Axiom talk lists L among the models "not obtainable by
   nontrivial forcing over an inner model" (S6, fetched).
2. **The mantle of a set-generic extension of L is L (MathOverflow, by one
   of the FHR authors).** In the discussion "Concept of bedrock and mantle
   in the multiverse view in the philosophy of mathematics" (MathOverflow
   question 459136, revision notes dated 2023-11-24; page HTML returns
   HTTP 403 to the page tool, quoted via three consistent revision
   snapshots indexed by search), the answer reads: "Every ground model of
   L[G] will contain some final segment of the overall forcing, and one can
   always peel off a few more factors. So the mantle of L[G] will be L
   itself. In the general case, we proved in the geology paper that every
   model of ZFC arises as the mantle of another model of ZFC." The
   first-person "we proved in the geology paper" plus the appended citation
   (Fuchs, Hamkins, Reitz, Set-theoretic geology) identifies the answer as
   the FHR authors'. This is the nearest stated form of the meeting theorem
   found; the general case (any set-generic extension of L) follows from
   item 3.
3. **The derivation is a two-line consequence of two cited theorems.** (a)
   L satisfies GA (Reitz, item 1), so L has no proper ground; (b) L is the
   smallest inner model: Jech, Set Theory, Theorem 13.16 (Gödel) proves
   "L is the smallest inner model of ZF", with the proof that for any inner
   model M, "L^M (the class of all constructible sets in M) is L and so
   L subset M" (Jech Chapter 13, as pinned in this corpus's
   `_build/literature/jech13.txt`, Theorem 13.16(ii); the lines just before
   it show the absoluteness step, "(x is constructible)^M iff x is
   constructible", for M with M superset Ord). A ground W of L[G] is an
   inner model with the same ordinals, so L subset W by (b); hence every
   ground of L[G] contains L, so L subset mantle(L[G]); and L is itself a
   ground of L[G], so mantle(L[G]) subset L. Hence mantle(L[G]) = L. The
   PLAN section 6.1 argument ("constructibility is absolute between
   transitive class models with the same ordinals, so a ground W of L
   satisfies L = L-of-W contained in W contained in L") is this same
   argument applied to grounds of L. No fetched primary source states this
   derivation as a numbered theorem; it is recorded here as a consequence
   of Reitz's GA theorem and Jech 13.16(ii), not as a located primary
   statement.

**Related statements found.** Usuba's consequences make the trophy robust:
"Bedrock models are unique when they exist" (S8, CUNY page), so if L[G]
has a bedrock it is unique; and "the mantle is a model of ZFC" (S3, S8).
Reitz's dissertation also constructs "bottomless models" with no minimal
grounds (S8, CUNY comment: "in his dissertation, Reitz constructed
bottomless models of set theory, which have no minimal grounds"), so "every
universe has a bedrock" is false; the L-phenomenon is special.

**Verdict.** The component statements are in the literature (Reitz: L
satisfies GA; MathOverflow answer by the FHR authors: the mantle of L[G] is
L). Whether the FHR paper itself states "L is a bedrock" or the mantle of
forcing extensions of L verbatim is UNVERIFIED: the ar5iv full text is not
machine-fetchable in this session (see "Paywalled or unfetched"), and the
indexed snippets do not show it. What would settle it: the ar5iv text of
arXiv:1107.4776, or the published APAL text.

Status: filled, with the UNVERIFIED flag on the FHR-internal wording.

## 5. First-order expressibility

What of the above is first-order expressible and what needs a
class-quantifier workaround, since this decides what the formalization can
even state.

**What is first-order expressible (with the sources):**

- **"W is a ground of V" and the enumeration of all grounds.** Uniform
  ground model definability gives a first-order formula psi(x,y) such that
  for every set a, W_a = {x | psi(x,a)} is a ground of V, and every ground
  W of V is some W_a (S5, "Ground model definability in ZF" talk page,
  verbatim). Hamkins' talk: "the treatment of the spectrum of possible
  ground models is entirely a first order affair of ZFC" (S6). Usuba's
  paper makes the same point in its introduction: uniform definability
  "allows us to treat ground models within the first order set theory ZFC"
  (S3, ar5iv-indexed snippet).
- **The mantle.** FHR's own statement, via the ar5iv-indexed snippet of
  arXiv:1107.4776: "The mantle of any model of set theory is a
  parameter-free uniformly first-order-definable transitive class in that
  model, containing all ordinals. Proof." (S1.) Fuchs' slides: "This mere
  definition is already an application of the uniform definability of
  grounds: The Mantle is a first order definable transitive class." (S9.)
  Note the strength: parameter-free, uniformly across models.
- **The generic mantle.** FHR proved both the mantle and the generic mantle
  are definable classes: Usuba's slides record "Theorem 21 (Fuchs-
  Hamkins-Reitz): 1. M and gM are definable classes and gM subset M."
  (Usuba's CTFM 2015 slides, jaist.ac.jp, search-indexed snippet.) Post-
  Usuba the distinction collapses: "the mantle is the same as the generic
  mantle" and both equal the largest forcing-invariant class and the
  intersection of the generic multiverse (S8, CUNY page).
- **The Ground Axiom and the Bedrock Axiom.** "The Ground Axiom is first
  order expressible in the language of ZFC" (S6, Theorem 1, credited to
  Reitz and independently Woodin); "The related Bedrock Axiom ... is also
  first-order expressible, and its negation is consistent" (S4, Reitz's
  dissertation abstract; S6, Bedrock Axiom box).
- **DDG and its consequences.** DDG and strong DDG are first-order
  assertions (every two grounds, or every set-indexed family of grounds,
  has a common ground; S3's introduction), and so are Usuba's corollaries
  "the mantle is a model of ZFC", "V has only set many grounds if and only
  if the mantle is a ground" (S3, abstract), and "the mantle is a ground"
  once the parameterized enumeration is in hand. Hamkins' consequence list
  (S8, CUNY page) is a list of first-order theorems of ZFC.
- **HOD as a contrast.** "HOD is a first order definable model of ZFC"
  (Usuba's NUS slides, ims.nus.edu.sg, search-indexed snippet), but unlike
  the mantle its definition needs ordinal parameters.

**What needs a class-quantifier workaround:**

- **The collection of all grounds is a proper class of proper classes.** A
  priori "the intersection of all grounds" is a second-order notion. The
  workaround that makes it first-order is exactly the parameterized
  enumeration: grounds are coded by set parameters via the uniform
  definability formula, and "all grounds" becomes "all parameters a in the
  definable index class I". Hamkins' talk makes the residual object
  explicit: "the class I of parameters p giving rise to a ground model W_p
  such that V is a forcing extension V = W_p[G_p] is definable, and the
  corresponding meta-class of possible ground models is in effect definable
  as {<p,x> | x in W_p and p in I}. Thus, the treatment of the spectrum of
  possible ground models is entirely a first order affair of ZFC." (S6.)
- **The generic multiverse and forcing-invariance.** Statements about all
  forcing extensions ("the mantle is the intersection of the generic
  multiverse", "the mantle is the largest forcing-invariant class", S8) are
  first-order only because both "G is generic over V" and "W is a ground of
  V[G]" are first-order and the ground enumeration is uniform across
  extensions (S6's uniform formula; S5). Without that uniformity, these are
  class-quantifier statements.
- **The definability is genuinely load-bearing, not cosmetic.** Hamkins
  says directedness cannot be expected for grounds that are not first-order
  definable: in reply to a question about a fully second-order setting
  "where we don't require first-order definability of the ground model in
  the extension (so going way beyond pseudo-grounds)", he answers "I don't
  think we can expect to have directedness in that generality ... I don't
  think we get it even for class forcing grounds." (S8, CUNY page,
  comment thread.)
- **Class forcing stays outside the first-order core.** Reitz's
  consistency results (every ZFC model has a class-forcing extension
  satisfying GA; bottomless models; independence of GA from GCH, V=HOD,
  large cardinals) are proved by proper class forcing, and Reitz's
  dissertation carries an appendix expounding proper class forcing (S4).
  Class forcing is a metatheoretic apparatus, not a first-order statement
  inside ZFC; the formalization would treat these as metatheorems if at
  all.

**What this means for the formalization (measured in this repo).** The
probe's `Mantle x = (W : Class) -> IsGround W -> < W x >` lands in
`Type (ell-suc (ell-suc ell))`, one universe too big to be a `Class`,
because it quantifies over `Class` (glprobe report, section 2.3). The
literature-side fix is the definability theorem: the mantle is first-order
definable, so the class-quantifier form is replaceable by a first-order
formula, discharging the `MantleIsClass` debt at a quoted price of 0.8-1.6k
lines "via the definability theorem" versus 0.05k "via
Base.Impredicativity" (glprobe report, section 2.4). A second wall is the
approximation/cover proof itself: "internal cardinality at a class carrier
(|a|^W < delta), needed for delta-approximation and delta-cover" is
reported as not stateable with the current function-set and cardinality
apparatus at a class carrier (glprobe report, section 2.4); the Laver proof
outline (S5) confirms cardinalities are intrinsic to the properties, which
is the same wall Usuba's ZF workaround (a rough measure replacing
cardinality) exists to climb (S5, talk page).

Status: filled. Open item: FHR's formal definition of "forcing-invariant
class" is used by S8 but not quoted here; it needs the ar5iv text of
arXiv:1107.4776.

## Paywalled or unfetched

Entries here as they are ruled out, each with what was attempted and what
would settle it.

Status: complete for this pass.

- ar5iv full text of FHR (arXiv:1107.4776) and of Usuba (arXiv:1707.05132):
  open_page and find_in_page both timed out on both pages repeatedly
  (2026-08-04). The search index quotes them, so the text is public but not
  machine-fetchable through the available tools in this session. Settle by
  retrying ar5iv from a network-enabled tool, or by fetching the arXiv PDF
  and extracting text. Consequence: the FHR paper's section/definition
  numbers, its theorem 6 statement in full, and its formal definition of
  "forcing-invariant class" are not pinned here.
- Laver (2007) full text: publisher page exists (open archive, PII
  S0168007207000607) but the article body is PDF, which the page tool does
  not parse. The theorem statement used here is quoted from open secondary
  sources (S5, S6). Settle by PDF text extraction.
- Woodin (2004) "Recent developments on Cantor's Continuum Hypothesis":
  proceedings paper, not located open. The attribution (independent proof
  in its appendix) is from S5. Settle by locating an open copy.
- zbMATH review of Laver (Zbl 1128.03046): page returned HTTP 403. Metadata
  obtained via search snippet. Settle by fetching from another mirror.
- arXiv v1 abstract page for Usuba (1707.05132v1): fetch timed out.
  Settle by retry.
- Reitz, "The Ground Axiom" (arXiv:math/0609270): the arXiv abstract page
  was fetched in full; the ar5iv rendering of the body timed out through
  the page tool, and the body's theorem ("L, L[0#], L[mu] satisfy GA") is
  quoted from a page-indexed snippet of the arXiv PDF. Settle by PDF text
  extraction.
- Usuba, "Extendible cardinals and the mantle" (arXiv:1803.03944): arXiv
  abstract page fetch timed out; the abstract and Theorem 1.3 are quoted
  from indexed snippets (ADS, scholar.archive, Lietz's thesis). Settle by
  retry.
- MathOverflow question 459136 and its revision pages: page HTML returns
  HTTP 403 to the page tool, and the StackExchange API returned BAD_CONTENT.
  The answer quoted in section 4 comes from three consistent revision
  snapshots indexed by search. Settle by a network-enabled tool or the API
  from a permitted host.
- Talk-slide PDFs (Fuchs' slides at unibe.ch, Usuba's slides at
  imsarchives/ims.nus.edu.sg, jaist.ac.jp): open PDFs, not machine-fetchable
  by the available page tool; quoted via search-indexed snippets only.
  Settle by PDF text extraction.
- Hamkins, "Extensions with the approximation and cover properties have no
  new large cardinals" (Fund. Math. 180, 2003): not fetched at all; cited
  by S6 and S7 as the origin of the properties. Settle by locating an open
  copy (the publisher is Polish Academy of Sciences, Fund. Math. is open).

Nothing in this dossier was obtained through a paywall workaround. Paywalled
or bot-blocked material is either reported here or quoted from open
author-maintained sources.
