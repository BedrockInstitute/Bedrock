# Formalization landscape: Paulson, Flypitch, and what else the fetched material shows

Developer notes for the rud-route formalization. Sources fetched in full:

- P = Paulson, "The Relative Consistency of the Axiom of Choice Mechanized
  Using Isabelle/ZF", arXiv:2104.12674v1 (26 Apr 2021), 67 pages (PDF page
  numbers cited below).
- PI = Paulson, "The Constructible Universe and the Relative Consistency of
  the Axiom of Choice", Isabelle/ZF library outline, Feb 20 2021 (outline.pdf,
  202 pages; section numbers cited below).
- PS = Paulson, slides "The Relative Consistency of the Axiom of Choice
  Mechanized Using Isabelle/ZF" (slide numbers cited below).
- FC = Han & van Doorn, "A Formal Proof of the Independence of the Continuum
  Hypothesis", CPP 2020 (14 pages).
- FI = Han & van Doorn, "A formalization of forcing and the unprovability of
  the continuum hypothesis", ITP 2019 (19 pages).
- FG = Flypitch GitHub README (fetched from github.com/flypitch/flypitch).

## 1. Paulson: scope (Q7)

P's abstract (p. 1), verbatim:

> The proof of the relative consistency of the axiom of choice has been
> mechanized using Isabelle/ZF. The proof builds upon a previous mechanization
> of the reflection theorem. The heavy reliance on metatheory in the original
> proof makes the formalization unusually long, and not entirely satisfactory:
> two parts of the proof do not fit together. It seems impossible to solve these
> problems without formalizing the metatheory. However, the present development
> follows a standard textbook, Kunen's Set Theory, and could support the
> formalization of further material from that book.

Route (satisfaction internalization, following Kunen):

- P section 2.1 (p. 7): "Because L is a proper class, we cannot adopt the usual
  notion of satisfaction... If M is a proper class, then the obvious definition
  of M |= p(m~) cannot be formalized in set theory" (Tarski non-definability,
  cited to Kunen [9, p. 41]).
- P section 2.2 (pp. 7-8): "Gödel instead expressed satisfaction for class
  models syntactically" via relativization, which "can only be defined in the
  metalanguage: it combines two arguments, φ and M, which lie outside ZF."
- P sections 6.1-6.7 (pp. 25-32): L is built from an internalized datatype of
  first-order formulae (de Bruijn indices), a primitive recursive satisfaction
  function sats, and the definable powerset DPow(A) = {X ∈ Pow(A) ; ∃ env ∈
  list(A). ∃ p ∈ formula. arity(p) ≤ succ(length(env)) & X = {x∈A. sats(A, p,
  Cons(x,env))}}. The DPow definition is explicitly matched to "Definition VI
  1.1 of Kunen [9, p. 165]" (P p. 32). P p. 25: "Neither Gödel nor Kunen
  actually use first-order formulae, preferring more abstract constructions...
  However, Isabelle/ZF's recursive datatype package automates the task of
  defining the set of first-order formulae and the satisfaction relation on
  them."
- P section 2.5 (p. 10): "Defining the Class L"; 2.6 (pp. 10-11): "Absoluteness:
  Proving (V=L)^L"; 2.7 (p. 11): "The Consequences of V=L".

Results proved (P section 11 Conclusions, p. 64), verbatim:

> 1. defining the class L within ZF
> 2. proving, for every ZF axiom φ, that φ^L is a ZF theorem
> 3. proving (V = L)^L in ZF
> 4. proving that ZF + V = L implies the axiom of choice

The well-ordering of L is via the lexicographic order on tuples <p, a1, ..., ak>
for p ∈ F and ai ∈ A, lifting a well-ordering of A to one of DPow(A) (P section
2.7, p. 11; sections 10.1-10.5, pp. 59-63; PI sections 15.1-15.5). P p. 11:
"So if L_α is well-ordered, so is L_{α+1}. By transfinite induction, each level
of the construction of L is well-ordered."

Paulson's own verdict (P section 11, pp. 64-65), verbatim:

> The formal proof is much longer than the textbook version because it is
> complete in all details and uses no metatheoretical reasoning.
> ...
> The proof that L satisfies V = L is by far the largest and most difficult
> part of the development.

The metatheory problem (P section 11, p. 65), verbatim:

> My formalization has two limitations. First, I am not able to prove that L
> satisfies the axiom scheme of comprehension. Although Isabelle/ZF handles
> schematic proofs easily, the proof of comprehension for the formula φ requires
> an instance of the reflection theorem for φ. Each instance of comprehension
> therefore has a different proof and must be proved separately... There are
> about 35 such instances.
> My formalization has another limitation. The proof that L satisfies V = L
> cannot be combined with the proof that V = L implies the axiom of choice in
> order to conclude that L satisfies the axiom of choice. The reason is that the
> two instances of V = L are formalized differently: one is relativized and the
> other is not.
> We could remedy both limitations by tackling the whole problem in a quite
> different way, by formalizing set theory as a proof system and working
> entirely in the metatheory. I leave this as a challenge for the theorem-
> proving community.

Sizes (PS slide 17): "Reflection theorem 3400 [tokens]; Definition of L 4140;
ZF holds in L (excluding separation) 5100; V=L holds in L 29700; V=L implies AC
1769." PS slide 19: "Big: 12000 lines or 49000 tokens." PS slide 15: "40
separate instances proved" (of separation; the paper text says "about 35",
discrepancy noted: PS says 40, P says about 35).

### 1.1 GCH status in Paulson (Q7)

The definitive statements are in the conclusions and the library:

- P section 11 (p. 65): "Future investigators might also try formalizing the
  proof that L satisfies the generalized continuum hypothesis and the
  combinatorial principle ♦."
- PS slide 19, future challenges: "Repeat, with a formalized metatheory;
  Prove generalized continuum hypothesis; Formalize forcing proofs:
  independence of AC."
- PI theory graph (p. 8): the development terminates in AC_in_L and
  Internalize; there is no GCH theory in the outline.

Therefore: GCH was NOT formalized in the fetched development (v1 paper +
Feb 2021 outline + slides). GCH-in-L is listed by Paulson as open future work.

DISCREPANCY (flagged, not smoothed over): P section 2.7 (p. 11) contains the
sentence "We prove ZFL ` AC, ZFL ` GCH and ZFL ` ♦, but we do not prove ZF `
AC^L, ZF ` GCH^L and ZF ` ♦^L." This contradicts the Conclusions (GCH and ♦ as
future work) and the slides (GCH as a future challenge). Marked UNVERIFIED
which reading is intended: the only verifiable artifacts (outline theory graph,
slides, conclusions) are consistent with GCH and ♦ being NOT part of the
mechanized development; the section 2.7 sentence is a paper-internal
inconsistency.

### 1.2 Paulson extras

- P p. 1: "A by-product of the work is a general theory of absoluteness for
  arbitrary class models of ZF." (P p. 65: "A by-product of the work is a
  general theory of absoluteness for arbitrary class models of ZF. It could be
  used for other formal investigations of inner models.")
- P Acknowledgements (p. 65): "Krzysztof Grabczewski devoted much effort to an
  earlier, unsuccessful, attempt to formalize this material."
- PI abstract (p. 1): "This formalization is by far the deepest result in set
  theory proved in any automated theorem prover."

## 2. Flypitch: scope (Q7)

FC abstract (p. 1), verbatim:

> We describe a formal proof of the independence of the continuum hypothesis
> (CH) in the Lean theorem prover. We use Boolean-valued models to give forcing
> arguments for both directions, using Cohen forcing for the consistency of ¬CH
> and a σ-closed forcing for the consistency of CH. We then combine this with a
> deep embedding of first-order logic, including a proof system and the axioms
> of ZFC, to verify that CH is neither provable nor disprovable from ZFC.

So: BOTH directions via Boolean-valued models (yes), Cohen forcing for ¬CH and
a σ-closed (collapse) forcing for CH. Details:

- FC section 1.1 (p. 3): "If we can construct two Boolean-valued models of ZFC,
  one where CH is true ⊤, and one where CH is false ⊥, then by the Boolean-
  valued soundness theorem, CH is independent from ZFC."
- FC p. 2: "the main reason is the directness of forcing with Boolean-valued
  models, which bypasses the need for the Löwenheim-Skolem theorems, Mostowski
  collapse, countable transitive models, or genericity considerations for
  filters."
- FC p. 3: "Our main novel contribution is a formalization of collapse forcing
  and the unprovability of ¬CH, thereby providing the first formalization of
  the independence of CH in a single theorem prover. For reasons we will see in
  Section 5, the forcing argument for CH requires far more set theory and is
  harder to formalize than the forcing argument for ¬CH."
- FC p. 3 (sources): "Our strategy for forcing ¬CH is a synthesis of the proofs
  in the textbooks of Bell ([4], Chapter 2) and Manin ([27], Chapter 8). For
  the Δ-system lemma... we follow Kunen ([26], Chapters 1 and 5). We were
  unable to find a reference for a purely Boolean-valued account of forcing CH.
  We loosely followed the conventional arguments given by Weaver ([45], Chapter
  12) and Moore ([30]), and base our construction of B_collapse on the collapse
  algebras defined by Bell ([4], Exercise 2.18)."
- FI abstract (p. 1): the earlier work covers "the fundamental theorem of
  forcing and a deep embedding of first-order logic with a Boolean-valued
  soundness theorem" and "the failure of the continuum hypothesis in the
  resulting model" built on "the Boolean algebra of regular opens of the Cantor
  space 2^ω". So FI 2019 covers only the ¬CH direction.

Formal statement (FG README, verbatim):

> theorem independence_of_CH : independent ZFC CH_f

with "independent" = "a sentence is neither provable nor disprovable from a
theory" and CH_f = "∀x, x is an ordinal ⟹ x ≤ ω ∨ P(ω) ≤ x where a ≤ b means
that there is a surjection from a subset of b to a" (FG README).

What the models contain: the Boolean-valued universe V^B is implemented as
bSet B, generalizing "the Aczel encoding of set theory" (FC p. 2: "our
Boolean-valued models of set theory are inductive types generalizing the Aczel
encoding of set theory into dependent type theory"); the fundamental theorem
of forcing states "bSet B is a B-valued model of ZFC" (FC p. 3).

### 2.1 What Flypitch's "constructible universe" contains

Answer from the fetched material: Flypitch does NOT construct the constructible
universe. Neither FC nor FI mentions L beyond Gödel's 1938 consistency theorem
(FC p. 1: "Gödel [14] proved in 1938 that CH was consistent with ZFC"); the
consistency of CH is obtained by σ-closed collapse forcing in V^B, not by L.
The GitHub README lists as possible future work: "Formalizing the reduction
from ZFC to ZFC without function symbols; Consistency of CH via construction
of the constructible universe; Proof transfer using the completeness theorem;
Forcing over countable transitive models; Forcing using modal logic; Forcing
using sheaves." So the constructible-universe route to CH is explicitly
unformalized in Flypitch.

## 3. Anything else verifiable from the fetched material (Q7)

- FC related work (p. 4): "A large body of formalized set theory has been
  completed in Isabelle/ZF, led by Paulson and his collaborators, including the
  relative consistency of AC with ZF [34]. Building on this, Gunther, Pagano,
  and Terraf have taken some first steps towards formalizing forcing [15, 16],
  by way of generic extensions of countable transitive models." (This is the
  only mention in the fetched material of other forcing formalizations.)
- P references include the earlier JAR paper: Paulson & Grabczewski,
  "Mechanizing set theory: Cardinal arithmetic and the axiom of choice",
  Journal of Automated Reasoning 17(3):291-323, 1996 ([19] in P's reference
  list, p. 67), cited at P p. 2.
- Mizar, Metamath, Naproche: NONE of the fetched texts mention them (PS slide
  1 mentions "thousands of Mizar proofs" only as a count of mechanized proofs,
  not as a set-theory development). Status: not determinable from fetched
  material.
- A rud-based development (rud functions, J-hierarchy fine structure) in any
  theorem prover: NO fetched source reports one. Status: not determinable from
  fetched material (absence of mention, not a proof of absence).

## 4. Q7 synthesis (per fetched material only)

- Paulson: AC-in-L yes; GCH-in-L and ♦ no (future work per P conclusions and
  PS; no GCH theory in PI outline); route = satisfaction internalization per
  Kunen; verdict = "unusually long", "not entirely satisfactory", two parts do
  not fit together, metatheory not formalized.
- Flypitch: independence of CH, both directions, via Boolean-valued models
  (Cohen for ¬CH, σ-closed collapse for CH); no constructible universe, no L,
  no GCH-in-L.
- GCH-in-L appears to be virgin territory relative to these two projects: both
  explicitly list it as future work (P p. 65; FG README). Caveat: this is a
  statement about the fetched documents (2020-2021), not a survey of all
  systems.
- Any rud-based development: nothing found in the fetched material.

## 5. Source-consumption map

- P: sections 1, 1.1, 1.2.
- PI: section 1.1 (theory graph, DPow, well-ordering sections).
- PS: sections 1.1 (sizes, 40 instances), 1.1 GCH.
- FC: sections 2, 2.1, 3.
- FI: section 2.
- FG: sections 2, 2.1, 3.
