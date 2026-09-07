# Formalization landscape sweep: L, V=L, condensation, AC-in-L, GCH-in-L, rud (2026-08-02 survey)

Current Bedrock status (2026-09-06): `L⊨ZFC` and `L⊨GCH` are proved and
registered in [Landmarks](../../src/Landmarks.lagda.md). The research and route
assessments below are historical; they do not describe open Bedrock proof goals.

Developer notes for the rud-route formalization. This file closes digest.md
OPEN item 7 (the Mizar/Metamath/Naproche/AFP landscape) and extends it to Lean
mathlib and its community projects, and to Coq/Rocq, per the sweep brief of
2026-08-02. Paulson (Isabelle/ZF) and Flypitch (Lean 3) are settled in
formalizations.md and are NOT redone here: this file cross-references them and
adds a direct check of the exported contents of the Isabelle/ZF Constructible
session (the library artifact behind Paulson's work).

Method: every system below was searched through its OWN index or repository,
all fetched on 2026-08-02. Every positive claim carries the URL actually
fetched and an identifier or quote from that page. Absence claims are worded
as "not found via <the index searched on date>", never as flat nonexistence.
The date-bound caveat applies to every row: a later version of any library
could add this material.

## 1. The per-system table (a)-(d)

Legend: (a) constructible universe as a formal object (and definition route);
(b) AC-in-L proved; (c) GCH-in-L proved; (d) any rud-functions-based
development. "No" means "not found via the index cited in the system section,
on 2026-08-02".

| System | (a) L exists | (b) AC-in-L | (c) GCH-in-L | (d) rud |
|---|---|---|---|---|
| Metamath (set.mm) | No | No | No | No |
| Mizar (MML 5.68) | No | No | No | No (Godel/Mostowski operations A1-A7 exist in ZF_FUND1/2, but no rud) |
| Isabelle AFP | No entry; ZF-Constructible session (distribution, not AFP) has L | Yes, in ZF-Constructible (AC_in_L, L_implies_AC) | No (not in session; Paulson's own text says future work) | No |
| Lean mathlib4 + community | No (mathlib4 declaration index and repo tree) | No | No | No |
| Coq/Rocq (opam archive) | No | No | No | No |
| Naproche | No | No | No (GCH exists only as an assumed axiom, L13-GCH.ftl) | No |

Evidence URLs: Metamath gchac
(https://us.metamath.org/mpeuni/gchac.html), set.mm source
(https://raw.githubusercontent.com/metamath/set.mm/develop/set.mm), theorem
list (https://us.metamath.org/mpeuni/mmtheorems107.html). Mizar mirror article
pages (https://mirror.mizar-jp.org/version/current/html/zf_fund1.html,
.../zf_fund2.html, .../zf_colla.html, .../zf_refle.html) and JFM summaries
(https://mirror.mizar-jp.org/JFM/Vol2/zf_fund1.html,
https://mirror.mizar-jp.org/JFM/Vol3/zf_fund2.html). AFP topic index
(https://isa-afp.org/topics/logic/set-theory/), entries Forcing
(https://isa-afp.org/entries/Forcing.html), Independence_CH
(https://isa-afp.org/entries/Independence_CH.html), Transitive_Models
(https://isa-afp.org/entries/Transitive_Models.html); ZF-Constructible session
index (https://isabelle.in.tum.de/library/FOL/ZF-Constructible/index.html),
AC_in_L (https://isabelle.in.tum.de/library/FOL/ZF-Constructible/AC_in_L.html),
L_axioms (https://isabelle.in.tum.de/library/FOL/ZF-Constructible/L_axioms.html),
document (https://isabelle.in.tum.de/library/FOL/ZF-Constructible/document.pdf).
Lean declaration index
(https://leanprover-community.github.io/mathlib4_docs/declarations/declaration-data.bmp),
ZFC model file
(https://raw.githubusercontent.com/leanprover-community/mathlib4/master/Mathlib/SetTheory/ZFC/Basic.lean),
con-nf README
(https://raw.githubusercontent.com/leanprover-community/con-nf/main/README.md).
Coq opam archive tree
(https://api.github.com/repos/coq/opam-coq-archive/git/trees/master?recursive=1),
coq-zfc opam
(https://raw.githubusercontent.com/coq/opam-coq-archive/master/released/packages/coq-zfc/coq-zfc.8.10.0/opam),
Kirst-Rech GCH-to-AC project page
(https://www.ps.uni-saarland.de/extras/sierpinski/). Naproche formalizations
page (https://naproche.github.io/formalizations.html), FLib SetTheory GCH file
(https://raw.githubusercontent.com/naproche/FLib/master/SetTheory/Library/L13-GCH.ftl),
Silver file
(https://raw.githubusercontent.com/naproche/FLib/master/SetTheory/Library/L20-Silvers_Theorem.ftl).

## 2. Metamath (set.mm)

Indexes searched: the set.mm source file itself, fetched from the
metamath/set.mm repository (develop branch, 874,496 lines, fetched
2026-08-02), plus the Proof Explorer theorem list
(https://us.metamath.org/mpeuni/mmtheorems107.html) and the pages it links for
the GCH section.

(a) Constructible universe as a formal object: NOT FOUND via the set.mm source
on 2026-08-02. A byte-level search of the whole file for the strings
"constructible universe", "axiom of constructibility", "V = L" and "V=L"
returns zero matches. The only "constructible" content in set.mm is the
straightedge-and-compass constructible numbers (section at set.mm line 540100,
"This section defines the set of constructible points as complex numbers
which"). There is no class constant for L: the only "$f class L $." is a
floating variable hypothesis (set.mm line 25460, `cL $f class L $.`), and no
definition label df-L or df-l exists anywhere in the file.

(b) AC-in-L: NOT FOUND via the same source. The GCH-implies-AC corpus exists
but is a theorem of the ambient theory, not a theorem about L: the theorem
page (https://us.metamath.org/mpeuni/gchac.html) reads "The Generalized
Continuum Hypothesis implies the Axiom of Choice. The original proof is due
to Sierpinski (1947); we use a refinement of Sierpinski's result due to
Specker", with statement "(GCH = V -> CHOICE)".

(c) GCH-in-L: NOT FOUND via the same source. The definition page
(https://us.metamath.org/mpeuni/df-gch.html) reads "Define the collection of
'GCH-sets', or sets for which the generalized continuum hypothesis holds" and
the theorem list section (https://us.metamath.org/mpeuni/mmtheorems107.html)
is "3.4 The Generalized Continuum Hypothesis" with subsections "3.4.1 Sets
satisfying the Generalized Continuum Hypothesis" and "3.4.2 Derivation of the
Axiom of Choice" (gchac, gchacg, gch-kn, and related theorems, labels 10600
through 10661). No theorem mentions L, and there is no object L to state
GCH-in-L about.

(d) Rud-based development: NOT FOUND via the same source. The string "rud"
occurs only inside unrelated tokens (biantrud, trud, mnugrud, inagrud and
similar, i.e. Grothendieck-universe mathbox material and logic lemmas), and
"Godel operation"/"Goedel operation"/"Godel operation" does not occur.

## 3. Mizar (MML)

Index searched: the MML article and abstract corpus of the official mirror
https://mirror.mizar-jp.org/version/current/ (mml.ini fetched 2026-08-02
reports Mizar 8.1.11, MML 5.68, NumberOfArticles=1412; the html files carry
last-modified dates of 2022-03-02). The official hosts mizar.uwb.edu.pl and
mizar.org timed out from this environment on 2026-08-02, and
mmlquery.mizar.org was unreachable; the mirror is the library's own index.
All 1413 downloadable abstract/source files under /version/current/abstr/
were fetched and searched on 2026-08-02.

(a) Constructible universe as a formal object: NOT FOUND via the MML 5.68
article index and full abstract corpus on 2026-08-02. The article list has no
ZF_L, no L, and no article whose title mentions constructibility. The word
"constructible" appears in exactly one MML article, MUSIC_S1, as the music-
theoretic attribute "satisfying_fifth_constructible" (MUSIC_S1:def 42), which
is unrelated. The closest content is the scaffolding for the Godel route:
ZF_FUND1, "Mostowski's Fundamental Operations - Part I" (Andrzej Kondracki,
received 1990-12-17, https://mirror.mizar-jp.org/version/current/html/zf_fund1.html),
defines closure of a class under the seven Mostowski operations A1-A7
(attributes closed_wrt_A1 through closed_wrt_A7, ZF_FUND1:def 6 through def
13). The JFM summary (https://mirror.mizar-jp.org/JFM/Vol2/zf_fund1.html)
says: "In the chapter II.4 of his book A. Mostowski introduces what he calls
fundamental operations: A1(a,b) = { {<0,x>,<1,y>}: x in y /\ x in a /\ y in a
}, A2(a,b) = {a,b}, A3(a,b) = union a, ..., A7(a,b) = { x o y : x in a /\ y
in b }." ZF_FUND2, "Mostowski's Fundamental Operations - Part II"
(Bancerek and Kondracki, received 1991-02-15,
https://mirror.mizar-jp.org/version/current/html/zf_fund2.html), defines
Section(H,v) (ZF_FUND2:def 1) and predicative closure (ZF_FUND2:def 2) and
proves the model criterion ZF_FUND2:6: "Union L is closed_wrt_A1-A7 implies
Union L is being_a_model_of_ZF" (under epsilon-transitivity and limit
conditions on the domain sequence L). This is the classical "a class closed
under the Godel operations and the hierarchy conditions is a model of ZF"
theorem, but L(alpha) itself (the definable-subset hierarchy) and V = L are
never defined.

(b) AC-in-L: NOT FOUND via the same index and corpus on 2026-08-02. No MML
article proves the axiom of choice inside a constructible hierarchy.

(c) GCH-in-L: NOT FOUND via the same index and corpus on 2026-08-02. The full
abstract corpus contains no "generalized continuum hypothesis" text at all;
the only "continuum" hits are cardinality-of-the-continuum statements in
topology, e.g. TOPGEN_5:16 "card y=0-line = continuum", and no GCH theorem of
any kind exists in MML 5.68.

(d) Rud-based development: NOT FOUND via the same index and corpus on
2026-08-02. The MML contains no rud functions, no J-hierarchy, and no fine
structure. The A1-A7 closure operations of ZF_FUND1 are the classical
Godel/Mostowski precursors of the rud route, not a rud-based development; no
article in the corpus matches "rud", "fine structure" or "Jensen" in the
set-theoretic sense (the matches found are the author surname Rudnicki and
Jensen's inequality in convex analysis, RFUNCT_4).

Related MML articles inventoried for orientation: ZF_MODEL "Models and
Satisfiability" (Bancerek), ZFMODEL1 "Properties of ZF Models" (Bancerek),
ZFMODEL2 "Definable Functions" (Bancerek), ZF_REFLE "The Reflection Theorem"
(Bancerek, received 1990-08-10, proves e.g. ZF_REFLE:1 "for W being Universe
holds W |= the_axiom_of_pairs"), ZF_COLLA "The Contraction Lemma" (Bancerek,
received 1989-04-14, defines func Collapse(E,A) at ZF_COLLA:def 1, the
Mostowski collapse), CLASSES1 "Tarski's Classes and Ranks", CLASSES2
"Universal Classes", CLASSES3 "Grothendieck Universes". Note in particular
that ZF_COLLA is the Mostowski collapse lemma, not Jensen's condensation
lemma; "condensation" occurs in the MML corpus only in the topology article
TOPGEN_4.

## 4. Isabelle AFP and the Isabelle/ZF Constructible session

Indexes searched: the AFP topic index for set theory
(https://isa-afp.org/topics/logic/set-theory/, fetched 2026-08-02), the
individual entry pages it lists, and the published Isabelle library browser
for the ZF-Constructible session
(https://isabelle.in.tum.de/library/FOL/ZF-Constructible/index.html and its
theory pages and document.pdf, fetched 2026-08-02).

The AFP topic "Set theory" lists 18 entries: CZH_Foundations,
Cardinality_Continuum, Category_Set, Delta_System_Lemma, Forcing,
HereditarilyFinite, Independence_CH, MLSS_Decision_Proc, MLSSmf_to_MLSS,
Mostowski_Collapse, Ordinal, Ordinal_Partitions, Ordinals_and_Cardinals,
Recursion-Addition, Transitive_Models, Wetzels_Problem, ZFC_in_HOL,
ZF_finite. There is no constructibility entry. The forcing entries are the
Argentinian group's work over countable transitive models: Forcing
(https://isa-afp.org/entries/Forcing.html) "We formalize the theory of
forcing in the set theory framework of Isabelle/ZF. Under the assumption of
the existence of a countable transitive model of ZFC, we construct a proper
generic extension and show that the latter also satisfies ZFC";
Independence_CH (https://isa-afp.org/entries/Independence_CH.html) "we
construct proper generic extensions that satisfy the Continuum Hypothesis
and its negation" (collapse forcing, not L); Transitive_Models
(https://isa-afp.org/entries/Transitive_Models.html) "We extend the
ZF-Constructibility library by relativizing theories of the Isabelle/ZF and
Delta System Lemma sessions to a transitive class" (its theory list contains
relative copies of the Constructible machinery such as DPow_absolute,
Internalize, Satisfies_absolute, but no L theory and no GCH theory).

(a) Constructible universe as a formal object: YES, in the Isabelle/ZF
Constructible session of the Isabelle distribution (not in AFP). The session
index lists the theories Formula, Relative, Wellorderings, WFrec,
WF_absolute, Datatype_absolute, Normal, Reflection, MetaExists, L_axioms,
Separation, Internalize, Rec_Separation, Satisfies_absolute, DPow_absolute,
AC_in_L, Rank, Rank_Separation. The definition route is the satisfaction-
internalization route (Kunen-style): Lset is built from DPow, and the
generated document (https://isabelle.in.tum.de/library/FOL/ZF-Constructible/document.pdf)
quotes "DPow :: "i => i" where "DPow(A) == {X : Pow(A). ... }" with the
internalized satisfaction relation sats(A, p, Cons(x,env)) in the membership
condition. L_axioms.html (https://isabelle.in.tum.de/library/FOL/ZF-Constructible/L_axioms.html)
is headed "The ZF Axioms (Except Separation) in L" and exports theorem
identifiers upair_ax, Union_ax, power_ax, foundation_ax, replacement
(relativized to L), plus M_trivial_L and "interpretation L : M_trivial L".

(b) AC-in-L: YES, same session, theory AC_in_L
(https://isabelle.in.tum.de/library/FOL/ZF-Constructible/AC_in_L.html),
section "The Axiom of Choice Holds in L!", with the theorem statement
"theorem L_implies_AC : assumes x : "L(x)" shows "EX r. well_ord(x,r)"" and
the surrounding text "Every constructible set is well-ordered! Therefore the
Wellordering Theorem and the Axiom of Choice hold in L!".

(c) GCH-in-L: NOT FOUND via the session index, theory pages, and the full
generated document.pdf on 2026-08-02. The session contains no GCH theory; the
word "condensation" does not occur in document.pdf; "continuum hypothesis"
occurs only in the introduction's background sentence about Hilbert's first
problem and in the bibliography entry for Godel's 1938/1940 papers, never as
a theorem. This is consistent with formalizations.md section 1.1: Paulson's
own conclusions list GCH as work for "future investigators" (P p. 65).

(d) Rud-based development: NOT FOUND via the same sources on 2026-08-02. The
string "rud" does not occur in document.pdf, and no AFP set-theory entry
name matches.

## 5. Lean: mathlib4, mathlib3, and community projects

Indexes searched: the mathlib4 repository tree and the full declaration index
of the mathlib4 docs site
(https://leanprover-community.github.io/mathlib4_docs/declarations/declaration-data.bmp,
66,314,107 bytes, fetched 2026-08-02, covering all declarations and their
source modules), the mathlib4 SetTheory tree (62 paths via the GitHub tree
API), the Lean 3 mathlib tree, and the leanprover-community GitHub
organization's repository list (107 repos, two pages, fetched 2026-08-02).

(a) Constructible universe as a formal object: NOT FOUND via the mathlib4
declaration index and both mathlib trees on 2026-08-02. The declaration
index has no Lset, no DPow, and no set-theoretic "L" declaration: the only
exact declaration named "L" lives in the Archive (Archive/Hairer.html#L), an
analysis example unrelated to constructibility. All "Constructible" hits in
the index are topology and algebraic-geometry material
(Topology/Constructible.html, Topology/Spectral/ConstructibleTopology.html,
AlgebraicGeometry ... isConstructible_image), not the constructible
universe. The mathlib4 set-theory content is Mathlib/SetTheory/{Cardinal,
Ordinal, ZFC, Descriptive, Lists.lean}; Mathlib/SetTheory/ZFC/Basic.lean is
headed "# A model of ZFC" and its main definitions are "ZFSet: ZFC set.
Defined as PSet quotiented by PSet.Equiv" and "ZFSet.choice: Axiom of choice.
Proved from Lean's axiom of choice". Flypitch (Lean 3) is the other large
set-theory formalization and it does not construct L either; its README
lists "Consistency of CH via construction of the constructible universe" as
possible future work (cross-reference formalizations.md section 2.1).

(b) AC-in-L: NOT FOUND via the same index and trees on 2026-08-02.

(c) GCH-in-L: NOT FOUND via the same index and trees on 2026-08-02. The
declaration index contains no GCH declarations; the "continuum" declarations
are all in SetTheory/Cardinal/Continuum.lean (Cardinal.continuum and its
arithmetic, i.e. the cardinality of the continuum, not CH or GCH).

(d) Rud-based development: NOT FOUND via the same index and trees on
2026-08-02; no file path in either mathlib tree contains "rud".

Community projects: the leanprover-community organization listing shows no
set-theory or constructibility project besides con-nf. con-nf is the New
Foundations consistency project; its README
(https://raw.githubusercontent.com/leanprover-community/con-nf/main/README.md)
says "We have formally constructed a model of TTT in Lean, thus proving (on
paper) that New Foundations is consistent, or in short, Con(NF)" and contains
no constructible universe. No other community project with L was surfaced by
the searches on 2026-08-02.

## 6. Coq/Rocq

Index searched: the official opam-coq-archive repository tree (636 package
directories under released/core-dev/extra-dev, fetched via the GitHub tree
API on 2026-08-02) plus the source repositories the relevant opam files point
to. The web search UI at coq.inria.fr/opam/www is JavaScript-driven and
returned no static results (see section 8).

Package names matching set theory: coq-zfc, coq-cats-in-zfc,
coq-functions-in-zfc, coq-ordinal, coq-gaia-ordinals,
coq-mk-choice-axiom-and-equivalent-propositions. There is no coq-constructible
package and no GCH package.

(a) Constructible universe as a formal object: NOT FOUND via the opam-coq-
archive package index on 2026-08-02. The opam package coq-zfc
(https://raw.githubusercontent.com/coq/opam-coq-archive/master/released/packages/coq-zfc/coq-zfc.8.10.0/opam)
is Benjamin Werner's 1996 contribution "An encoding of Zermelo-Fraenkel Set
Theory in Coq ... The axioms of ZFC are then proved and thus appear as
theorems in the development"; its repository file list (Axioms.v, Cartesian.v,
Constructive.v, Hierarchy.v, Omega.v, Ordinal_theory.v, Plump.v,
Replacement.v, Russell.v, Sets.v, zfc.v) contains no L file, and Hierarchy.v
is the von Neumann hierarchy (rank) development, not the constructible
hierarchy. Carlos Simpson's ZFC-related packages (coq-cats-in-zfc,
coq-functions-in-zfc) develop "basic set theory, ordinals, cardinals and
transfinite induction" per their opam descriptions, with no constructible
universe.

(b) AC-in-L: NOT FOUND via the same index on 2026-08-02.

(c) GCH-in-L: NOT FOUND via the same index on 2026-08-02. The only GCH
mechanization found is GCH-implies-AC, not GCH-in-L: Kirst and Rech, "The
generalised continuum hypothesis implies the axiom of choice in Coq" (CPP
2021), project page (https://www.ps.uni-saarland.de/extras/sierpinski/):
"We discuss and compare two Coq mechanisations of Sierpinski's result that
the generalised continuum hypothesis (GCH) implies the axiom of choice (AC)."
That result is a theorem of the ambient set theory (matching the Metamath
gchac corpus), with no L involved.

(d) Rud-based development: NOT FOUND via the same index on 2026-08-02.

## 7. Naproche

Indexes searched: the naproche/naproche repository tree (493 files, fetched
via the GitHub tree API on 2026-08-02), the formalizations gallery page
(https://naproche.github.io/formalizations.html), and the naproche/FLib
library repository (594 files) that hosts the set-theory formalization.

The shipped examples and library contain no constructibility content: the
set-theory library lives at math/archive/libraries/set-theory/source/ and
covers the ZFC axioms (axioms/choice.ftl.en.tex through axioms/union.ftl.en.tex),
ordinals, cardinals, cofinality, countable and uncountable sets, transitive
classes, transfinite induction, and the module zfc.ftl.en.tex, which imports
the nine axiom modules plus pairs-and-products and invertible-maps. The
examples directory (100_theorems.ftl.tex, cantor, tarski, koenig, and others)
contains no L.

(a) Constructible universe as a formal object: NOT FOUND via the naproche
repository tree and examples on 2026-08-02. The Von Neumann hierarchy exists
(FLib SetTheory/Library/L03-Von_Neumann_Hierarchy.ftl), but no L(alpha), no
V = L, and no definability-based hierarchy.

(b) AC-in-L: NOT FOUND via the same sources on 2026-08-02.

(c) GCH-in-L: NOT FOUND via the same sources on 2026-08-02, and this is the
one place where a "GCH" file does exist. The gallery page says "In 2020 Jan
Penquitt formalized set theory in Naproche up to Silver's theorem about the
continuum function at singular cardinals of uncountable cofinality", and the
corresponding FLib SetTheory library contains L13-GCH.ftl and
L20-Silvers_Theorem.ftl. But the GCH there is an assumed axiom of the
ambient set theory, not a theorem about L: L13-GCH.ftl reads "Signature. GCH
is an atom. Axiom. GCH iff forall kappa /in /Card 2 ^ kappa = Plus[kappa]",
followed by lemmas on the Gimel function and cardinal exponentiation under
GCH; L20-Silvers_Theorem.ftl reads "Theorem Silver. Let kappa /in
/BigSingCard. Let GCH below kappa. Then 2 ^ kappa = Plus[kappa]". No
constructible universe is involved.

(d) Rud-based development: NOT FOUND via the same sources on 2026-08-02.

## 8. Searches that failed or were inconclusive

- mizar.uwb.edu.pl (official MML host) and mizar.org: connection timeouts on
  2026-08-02; the Mizar sweep used the official mirror
  mirror.mizar-jp.org/version/current/ instead. The mirror serves MML 5.68
  (Mizar 8.1.11, 1412 articles, html dated 2022-03-02). Newer MML versions
  (2023 onward) could not be checked directly; the official
  mizar.uwb.edu.pl/version/current/abstr/zf_fund1.abs is indexed by search
  engines with 2025 copyright lines, but was not fetchable from here.
- mmlquery.mizar.org and mmlquery.mizar.uwb.edu.pl: unreachable on
  2026-08-02; the full abstract/source corpus of the mirror was searched
  directly instead (1413 files fetched).
- The AFP search page (isa-afp.org/search/?q=...) is a JavaScript shell and
  returned no static results; the topic index (isa-afp.org/topics/logic/set-theory/)
  was used as the library's own index instead.
- The mathlib4 docs "find" endpoint (mathlib4_docs/find/) is JavaScript-
  driven; its underlying declaration index (declarations/declaration-data.bmp)
  was fetched and searched directly instead.
- The Rocq package web search (coq.inria.fr/opam/www autocomplete and search
  endpoints) returned only the JavaScript shell; the opam-coq-archive
  repository tree was used as the authoritative package index instead.
- Lean community sweep: limited to the leanprover-community organization
  listing and the READMEs surfaced by it (con-nf) plus Flypitch (cross-
  referenced); no claim is made about unindexed personal repositories.

## 9. The GCH-in-L virginity verdict, as far as this sweep carries

Not refuted; hardened. Across the six searched systems, on 2026-08-02, the
only formal object L (the constructible universe) lives in the Isabelle/ZF
Constructible session, which proves ZF-in-L and AC-in-L but contains no GCH
theory and no condensation lemma, and whose author lists GCH as future work
(formalizations.md section 1.1). GCH itself appears in Metamath (as the
GCH-sets definition plus the Specker/Sierpinski GCH-to-AC theorem), in Coq
(Kirst and Rech, GCH-to-AC), and in Naproche (as an assumed axiom in the
Penquitt set-theory library), but in none of them as a theorem that L models
GCH. Mizar, Lean mathlib, and the Coq opam archive show no constructible
universe at all. So the digest's claim that no mechanized proof of GCH-in-L
exists survives this sweep, now bounded by the indices and repositories
searched on 2026-08-02 rather than by the earlier fetched corpus. The
absence wording remains "not found via ...", not nonexistence, and any
rud-based development anywhere remains unclaimed.

## 10. Source-consumption map

- Metamath: set.mm raw source (grep evidence), df-gch.html, gchac.html,
  mmtheorems107.html.
- Mizar: mirror.mizar-jp.org/version/current/html/{zf_fund1,zf_fund2,
  zf_colla,zf_refle,zf_model}.html, JFM/Vol2/zf_fund1.html,
  JFM/Vol3/zf_fund2.html, mml.ini, all 1413 fetched .abs files.
- Isabelle: isa-afp.org/topics/logic/set-theory/, entries Forcing,
  Independence_CH, Transitive_Models, Mostowski_Collapse, ZFC_in_HOL,
  Cardinality_Continuum, browser_info of Transitive_Models, and
  isabelle.in.tum.de/library/FOL/ZF-Constructible/{index.html, AC_in_L.html,
  L_axioms.html, document.pdf}.
- Lean: mathlib4 declaration-data.bmp, mathlib4 tree, mathlib3 tree,
  Mathlib/SetTheory/ZFC/Basic.lean, con-nf README, leanprover-community org
  listing.
- Coq: opam-coq-archive tree, coq-zfc opam file and repository listing,
  ps.uni-saarland.de/extras/sierpinski/.
- Naproche: naproche/naproche tree, naproche.github.io/formalizations.html,
  naproche/FLib tree, SetTheory/Library/L13-GCH.ftl,
  SetTheory/Library/L20-Silvers_Theorem.ftl, SetTheory/README.md,
  set-theory library sources.
