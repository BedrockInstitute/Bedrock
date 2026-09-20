# Ground-model definability: proof architecture and formalization route

Date of audit: 2026-09-08. Scope: the Laver-Woodin ground-model
definability theorem, Hamkins's approximation-cover uniqueness argument, and
the uniform family of grounds used by Fuchs-Hamkins-Reitz (FHR). This note is
an implementation brief, not a claim that Bedrock already contains forcing or
geology.

The system architecture, work-package names and acceptance criteria are owned
by [Forcing and ground model definability: system design](forcing-geology-design-2026-09.md).
This companion note supplies the exact geology statements and proof
decomposition. Where its application-oriented order differs from the master
design, the master design controls implementation order and interface
ownership.

## Executive verdict

There are three results that should not be conflated.

1. A particular ground $W$ is definable in its set-forcing extension
   $V=W[G]$ from a set parameter in $W$. This is the Laver-Woodin theorem,
   stated as FHR Theorem 5.
2. A more general pseudo-ground $W\subseteq V$ is definable when the pair has
   the $\delta$-approximation and $\delta$-cover properties and computes
   $\delta^+$ correctly. This is FHR Theorem 6. Its proof uses rank-local
   candidate models and Hamkins's uniqueness lemma, FHR Lemma 9.
3. All grounds can be placed into one total, parameter-indexed, uniformly
   definable family $\{W_r:r\in V\}$. This is FHR Theorem 12. It requires an
   additional predicate saying that a candidate class really is a ground and
   a fallback value for bad parameters. Clauses (5) and (6), downward and
   upward relativization, add the intermediate-model theorem and iteration
   bookkeeping. They are stronger than the definability of one ground.

For a formalization, the real bottleneck is not the final class definition.
It is the package beneath it: small forcing gives approximation and cover;
rank initial segments satisfy the right finite-looking theory; the uniqueness
argument reconstructs all sets from small ordinal codes; and the candidate
predicate is first-order expressible. The forcing theorem, satisfaction for
set-sized structures, cardinal arithmetic, coding by ordinals, and reflection
must therefore precede ground definability.

## Exact statements and parameters

Let $W\subseteq V$ be transitive models of an appropriate fragment of ZFC.
For a cardinal $\delta$ of the ambient model:

- $W\subseteq V$ has the $\delta$-approximation property when, for every
  $A\in V$ with $A\subseteq W$, if $A\cap B\in W$ for every $B\in W$ with
  $|B|^W<\delta$, then $A\in W$.
- It has the $\delta$-cover property when every $A\in V$ with $A\subseteq W$
  and $|A|^V<\delta$ is contained in some $B\in W$ with $|B|^W<\delta$.

These are FHR Definition 7 and Reitz Definition 5. The model superscripts on
the two size comparisons matter.

FHR Theorem 6 assumes that $W$ is an inner model of ZFC, that the two
properties hold for some regular cardinal $\delta$ of $W$, and that
$(\delta^+)^W=(\delta^+)^V$. It defines $W$ using

$$r=({}^{<\delta}2)^W.$$

FHR first discusses $\mathcal P(\delta)^W$ as the parameter in the published
Hamkins-Laver argument, then records the Hamkins-Johnstone reduction to
$({}^{<\delta}2)^W$. The latter determines the former using approximation.
When $\delta=\gamma^+$, $({}^{<\delta}2)^W$ is equidefinable with
$\mathcal P(\gamma)^W$. For ordinary forcing $V=W[G]$ by
$\mathbb P\in W$, FHR Lemma 8 permits $\delta=|\mathbb P|^+$, and any larger
cardinal also suffices for the basic set-forcing case. FHR additionally notes
the natural parameter $\mathcal P(\mathbb P)^W$.

The Boolean completion changes the cleanest size bound in some presentations.
FHR's discussion of the uniform family later chooses
$\delta>|\operatorname{ro}(\mathbb P)|$. This is a deliberately safe bound
for relativization through complete subalgebras, not a contradiction of
Lemma 8's $|\mathbb P|^+$ bound.

Laver's published paper states a larger parameter in its abstract: the ground
is definable from $V_{\delta+1}^W$, where $\delta=|\mathbb P|^+$. FHR reports
that Laver's original proof used a sufficiently high $V_\theta^W$, while the
approximation-cover argument reduced the parameter first to
$\mathcal P(\delta)^W$ and later to $({}^{<\delta}2)^W$. These accounts use
different snapshots of the proof and should be cited with their exact source.

Woodin independently obtained ground definability. FHR cites Woodin's 2004
conference contributions, but this audit did not recover an open primary text
with a numbered theorem or appendix statement. The attribution is verified
through FHR; the exact Woodin theorem number and parameter are **UNVERIFIED**.

## The rank-local theory $\mathrm{ZFC}_\delta$

FHR and Reitz avoid asking a set $M\subseteq V_\theta$ to model full ZFC.
Their $\mathrm{ZFC}_\delta$ is a theory in the language of set theory with a
constant for $\delta$. It contains:

- Zermelo set theory, foundation, and choice;
- the assertion that $\delta$ is regular;
- $\leq\delta$-replacement, described as replacement for functions whose
  domain has size at most $\delta$;
- the assertion that every set is coded by a set of ordinals, stated by
  Reitz using a relation on an ordinal isomorphic to the membership structure
  of the transitive closure of the singleton of the set.

There is a minor wording difference worth preserving. FHR says
"functions with domain $\delta$" while naming $\leq\delta$-replacement;
Reitz's Definition 6 gives the formal theory and the coding axiom. A
formalization should define the exact schema once and prove the equivalent
smaller-domain forms, rather than rely on the parenthetical gloss.

If $\theta=\beth_\theta$ and $\operatorname{cf}(\theta)>\delta$, then
$V_\theta\models\mathrm{ZFC}_\delta$. The two conditions do separate jobs.
The beth fixed point makes the transitive closure of every member of
$V_\theta$ small enough to code below $\theta$. The cofinality bound keeps
the range of a function of size at most $\delta$ bounded below $\theta$, so
replacement remains inside $V_\theta$. These are not decorative reflection
hypotheses.

The ranks used by the candidate definition range over such beth fixed points,
not merely over arbitrary limits satisfying a finite fragment. There must be
unboundedly many of them above any prescribed rank so that every $x\in W$ is
eventually seen.

## Hamkins's uniqueness lemma

The exact FHR Lemma 9 hypothesis is: $W,W',U$ are transitive models of
$\mathrm{ZFC}_\delta$ for the same fixed regular $\delta$;
$W\subseteq U$ and $W'\subseteq U$ both have approximation and cover;

$$({}^{<\delta}2)^W=({}^{<\delta}2)^{W'}$$

and

$$(\delta^+)^W=(\delta^+)^{W'}=(\delta^+)^U.$$

Then $W=W'$. Reitz Lemma 7.2 states the older version with
$\mathcal P(\delta)^W=\mathcal P(\delta)^{W'}$. Therefore a development that
formalizes Reitz's proof literally should first use $\mathcal P(\delta)$ and
then add a separate reduction from $({}^{<\delta}2)$.

The proof has four reusable layers.

1. Approximation and cover make the statements $|A|<\delta$ absolute among
   the three models for shared sets of ordinals. Agreement on $\delta^+$
   similarly controls size $\delta$.
2. For a small ambient set of ordinals $A$, build a length-$\delta$ chain
   alternating covers from $W$ and $W'$. Regularity keeps intermediate unions
   small. Approximation puts the final union into both models. This is the
   simultaneous-cover lemma.
3. If $A\in W$ is a small set of ordinals, simultaneously cover it by
   $B\in W\cap W'$ of size at most $\delta$. Code a well-order/enumeration of
   $B$ by a subset of $\delta$. Equality of the power sets of $\delta$ moves
   that code, and hence $A$, into $W'$. Symmetry gives equality of all small
   sets of ordinals.
4. For an arbitrary set of ordinals $A\in W$, every small $W'$-test set is
   also in $W$, and its intersection with $A$ is a small set common to both.
   The $\delta$-approximation property of $W'\subseteq U$ yields $A\in W'$.
   Symmetry gives equality of all sets of ordinals. The coding axiom in
   $\mathrm{ZFC}_\delta$ then upgrades equality of ordinal sets to $W=W'$.

The formal version should state common ordinal height explicitly, as its rank-local application does, or derive the required ordinal agreement before transporting codes.

The proof uses choice to well-order relevant power sets and coding structures.
It uses $\leq\delta$-replacement to construct the alternating sequence and
enumerations. These uses explain the local theory rather than merely accompany
it.

## The defining formula for one pseudo-ground

Fix $r=({}^{<\delta}2)^W$. In $V$, define $x\in W$ by the existence of a
cardinal $\theta$ and a set $M\subseteq V_\theta$ such that:

1. $\theta=\beth_\theta$ and $\operatorname{cf}(\theta)>\delta$;
2. $M$ is transitive, has height $\theta$, and
   $M\models\mathrm{ZFC}_\delta$;
3. $M\subseteq V_\theta$ has the $\delta$-approximation and
   $\delta$-cover properties, interpreted inside $V_\theta$;
4. $({}^{<\delta}2)^M=r$;
5. $(\delta^+)^M=\delta^+$, where the right side is the ambient successor;
6. $x\in M$.

FHR writes this definition immediately after Lemma 9. The intended witness is
$M=V_\theta^W$. Lemma 9, applied with ambient $U=V_\theta$, forces every
candidate to be that witness. The forward direction chooses a sufficiently
large $\theta$ above the rank of $x$; the reverse direction uses uniqueness.

The phrase "successor correctness" must mean the three-way equality required
by Lemma 9. Merely asserting that $M$ believes some ordinal is $\delta^+$ is
too weak. In a bounded candidate predicate, the ambient $V_\theta$ must also
compute the same successor. Choosing $\theta>\delta^+$ and stating
$(\delta^+)^M=(\delta^+)^{V_\theta}$ makes the dependency explicit.

Reitz's earlier Ground Axiom formula uses a different parameter package:
$z=(H_{\delta^+})^W$, together with $\mathbb P$ and $G$. Reitz Theorem 7 asks,
for every suitable beth fixed point $\gamma$, for a unique transitive $M$ of
height $\gamma$ satisfying $M\models\mathrm{ZFC}_\delta$,
$z=(H_{\delta^+})^M$, $M[G]=V_\gamma$, and approximation-cover. Equality of
$H_{\delta^+}$ implies the needed power-set and successor agreement. The
coherent union of these $M_\gamma$ is the ground. This route proves that GA is
first-order expressible and yields definability from
$\delta,(H_{\delta^+})^W,\mathbb P,G$ before quantifying away $G$. It should
not be silently substituted for FHR's smaller-parameter formula.

## From one ground to a total uniform family

FHR Theorem 12 begins with the fixed formula from Theorem 5. For a parameter
$r$, let the raw section be $U_r=\{x:\phi(r,x)\}$. First-order set theory can
express that $U_r$ is a transitive proper class containing all ordinals and is
an inner model of ZFC; FHR Fact 10 packages the latter using closure under
Gödel operations, almost universality, and choice. One can also quantify over
a poset and a generic filter and express that $V$ is a forcing extension of
$U_r$.

Totalize by setting $W_r=U_r$ when $U_r$ is a ground, and $W_r=V$ otherwise.
This gives every parameter a ground and makes all actual grounds occur. To
ensure FHR Theorem 12(1), $r\in W_r$, the good-parameter branch must include
the property delivered by the ground-definability construction that its
parameter belongs to its candidate ground. A robust formal definition should
guard this explicitly:

$$W_r=U_r\quad\text{if }U_r\text{ is a ground and }r\in U_r;\qquad
W_r=V\quad\text{otherwise}.$$

This guard does not exclude the canonical parameters, all of which lie in
their grounds. It avoids relying on an implicit property of an arbitrary raw
section.

Theorem 12(1)-(4) supplies a total uniform family, exhaustiveness, a
parameter-free definition of the membership relation $x\in W_r$, and a
first-order forcing-extension relation in $(r,G,\mathbb P)$. Clauses (5) and
(6) are additional geology infrastructure. Downward relativization uses the
intermediate-model theorem and a parameter chosen above the size of the
Boolean completion. Upward relativization reindexes the same ground in a
forcing extension and then applies downward relativization. These clauses
should be a later milestone.

Ground definability alone does not prove downward directedness of grounds,
that the mantle satisfies ZFC, that the mantle is a ground, or the later
generic-mantle and outer-core results. Those need separate geology theorems,
including later work of Usuba. FHR itself uses uniformity to make the mantle a
first-order definable class, but its 2014 version still reports only that the
generic mantle is always a model of ZF. Later conclusions must not be imported
back into the ground-definability milestone.

## Place in the shared formalization architecture

The geology development is an application branch of the shared architecture,
not the owner of a private forcing representation. The public framework must
provide the full ground-relative poset interface and the full Boolean
interface described by the master design. Their systematic equivalence bridge
is required: regular-open completion in the ground, dense-map transport of
names and generics, agreement of valuations, and agreement between poset
forcing and Boolean values. A pair of unrelated implementations does not meet
that requirement. Ground definability itself remains representation
independent and consumes the abstract forcing consequences it needs; its
formula and parameter may not mention the chosen poset, Boolean completion or
generic.

Reusable results have one canonical proof owner. Model-relative cardinal and
coding results, set-sized satisfaction, rank recursion, forcing syntax and
semantics, and extension-ZFC proofs live in shared foundations. Poset and
Boolean clients obtain them through proved transport along the equivalence
bridge rather than duplicating their theories. Host-level constructions may
maximize witnesses when the semantic profile permits it, but every theorem
advertised as internal must also provide the corresponding coded construction
and satisfaction or absoluteness bridge. In particular, a host-selected name,
cover, ordinal code or rank candidate cannot silently discharge an internal
choice, collection or replacement obligation.

The geology obligations align with the master work packages by name:

1. **Reusable internal set theory** owns regular and successor cardinals,
   $H_\kappa$, beth fixed points, cofinality, model-tagged size comparisons,
   transitive-closure codes, collapse recovery, set-sized satisfaction,
   formula and schema relativization, and the exact $\mathrm{ZFC}_\delta$
   package. Its rank-fragment theorem supplies the eligible $V_\theta$ models.
2. **Definable forcing theorem**, **extension ZFC**, and **small forcing
   estimates** own the forcing theorem, internal formula translation, name
   rank bounds, preservation, and the global approximation-cover theorem for
   small set forcing. FHR Lemma 8's two-step strategic-closure generalization
   remains a later extension. The Boolean comparison package is a required
   shared interface, while the geology theorem depends only on transported,
   representation-independent consequences.
3. **Uniqueness from approximation/cover** formalizes Reitz Lemma 7.2 first
   with $\mathcal P(\delta)$, exposing simultaneous cover and agreement on
   small ordinal sets as named lemmas, and then derives FHR Lemma 9 from
   agreement on $({}^{<\delta}2)$. This theorem has no forcing hypothesis.
4. **Rank localization and definability** localizes the pair properties,
   verifies $V_\theta^W$ as a candidate, applies uniqueness, and constructs a
   constant-free object-language formula with a semantic equivalence theorem.
   The bottleneck is preserving internal size witnesses while transporting
   enumerations and codes, not merely writing the final class predicate.
5. **Ground definability** joins small forcing estimates to the abstract
   rank-local theorem. It proves both directions of membership using one
   formula and a parameter in the ground, independently of the forcing
   representation.
6. **All-grounds interface** implements FHR Fact 10, the internal
   forcing-extension test, the explicit $r\in U_r$ guard, totalization and
   Theorem 12(1)-(4). This is the framework acceptance endpoint for geology;
   approximation-cover uniqueness is a valuable intermediate theorem, but is
   not acceptance for the full framework.
7. **Reusable extension calculus** owns iterations, quotients, complete
   subalgebras and reindexing used for Theorem 12(5)-(6). Later mantle or
   generic-multiverse work may depend on stable ground indices only after the
   all-grounds interface and the required relativization results are proved.

## Citation ledger and verification status

| ID | Primary source | Exact locations used | Status |
|---|---|---|---|
| FHR | Gunter Fuchs, Joel David Hamkins, Jonas Reitz, *Set-theoretic geology*, Annals of Pure and Applied Logic 166 (2015), 464-501; arXiv:1107.4776v2, https://arxiv.org/html/1107.4776v2 | Definition 7; Theorems 5, 6, 12; Lemmas 8, 9; Fact 10; discussion immediately after Lemma 9 | Verified in full-text primary source |
| Reitz | Jonas Reitz, *The Ground Axiom*, Journal of Symbolic Logic 72 (2007), 1299-1317, https://openlab.citytech.cuny.edu/jonasreitz/files/2024/06/GroundAxiomPaper.pdf | Definitions 5, 6; Theorem 7; Lemmas 7.1, 7.2, 7.3; Theorem 8 | Verified in author-hosted primary PDF |
| Laver | Richard Laver, *Certain very large cardinals are not created in small forcing extensions*, Annals of Pure and Applied Logic 149 (2007), 1-6, DOI 10.1016/j.apal.2007.07.002 | Published abstract for $V_{\delta+1}$ parameter; theorem attribution and parameter refinements cross-checked in FHR | Abstract verified; internal theorem number and full proof text **UNVERIFIED** |
| Hamkins | Joel David Hamkins, *Extensions with the approximation and cover properties have no new large cardinals*, Fundamenta Mathematicae 180 (2003), 257-277, DOI 10.4064/fm180-3-4 | [arXiv:math/0307229v2](https://arxiv.org/pdf/math/0307229), Definition 12 and Lemma 13, printed pages 11-12; origin of approximation and cover | Coordinator verified the full Lemma 13 statement and proof; its closure-point parameter is one cardinal below the approximation parameter |
| Woodin | W. Hugh Woodin, 2004 conference work on CH and the generic multiverse, as cited by FHR | Independent attribution to ground definability | Attribution verified through FHR; primary theorem number, exact parameter, and proof text **UNVERIFIED** |

Later sources such as Usuba are relevant to downward directedness and mantle
theorems, but they are not proof dependencies of the ground-model definability
theorem audited here.
