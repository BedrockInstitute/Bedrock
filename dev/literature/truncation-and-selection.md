# Truncation and selection: how the two literatures pick a witness

Task `[LJ-1.316]`, landed 2026-08-15 by the `[LJ-1.319]` ruling.

**The question.** A proof needs an object. The object exists. In classical set
theory the proof takes it. In cubical type theory the existence can arrive as
`∥ A ∥₁`, and then the proof may not take it. **This file records what each
literature does at that point, and what the exact condition is.**

**Scope.** This digest is route-neutral. It says nothing about the two towers,
about `Def` against `J`, or about the crossing. It is about selection, and it
stays true whatever the route.

## 1. THE SET-THEORY SIDE: the least element under a definable well-order

**No classical source at this step uses choice.** Three of them select the
LEAST witness under a definable well-order, and all three write leastness with
the same universal guard.

### 1.1 Devlin

Lemma II.5.3, the definable hull. The proof verifies Tarski's criterion by
forming, for each formula `φ`,

    ψ(v₀) = φ(v₀) ∧ ∀v₁(v₁ <_L v₀ → ¬φ(v₁))

`dev/literature/devlin-II5.md:127-131`, quoting
`_build/literature/dev2.txt:1340-1350`. The least witness is the UNIQUE witness
of `ψ`, so it is definable from the same parameters.

Devlin's own gloss on the lemma: it is "really a result about structures with
definable wellorders" (`dev/literature/devlin-II5.md:262-263`, quoting
`_build/literature/dev2.txt:1328-1329`).

Lemma II.5.9 states the selection as a theorem in its own right: the least
element of a non-empty Σ₀ predicate is Σ₁-definable from its parameters
(`dev/literature/devlin-II5.md:422-423`, quoting
`_build/literature/dev2.txt:1408-1423`).

### 1.2 Jech

Lemma 13.19's proof, `_build/literature/jech13.txt:744-753`. Jech makes the
same move explicit because he must show the canonical well-order is Σ₁:

> The only potential difficulty might be the use of the words "the <-least,"
> and that can be overcome as follows: ...
> [the <ⁿ-least v such that x = G_i(u,v)] < [the <ⁿ-least t such that
> y = G_i(u,t)]
> can be written as
> (∃v ∈ Wⁿ_α)[x = G_i(u,v) ∧ (∀t ∈ Wⁿ_α)(y = G_i(u,t) → v <ⁿ_{α+1} t)].

Exercise 13.24, `_build/literature/jech13.txt:1141-1144`, is Devlin II.5.3 in
Jech's hand:

> If δ is a limit ordinal, then the model (Lδ, ∈) has definable Skolem
> functions. ... [The well-ordering <δ is definable in (Lδ, ∈). Let h_φ(x) =
> the <δ-least y such that (Lδ, ∈) ⊨ φ[x, y].]

### 1.3 Schindler and Zeman

Theorem 1.15, `_build/literature/sz-full.txt:527-528`: "Let M be a
J-structure. There is a Σ1 Skolem function h_M which is uniformly Σ^M_1." The
canonical well-order's own definition uses "the <-least" at
`_build/literature/sz-full.txt:697-705`.

### 1.4 What the three agree on

**The selection device is a definable well-order plus a universal guard.** The
guard turns "some witness" into "THE witness", and that is what makes the
selection a function rather than a choice.

### 1.5 The classical conclusion is proposition-valued, and this matters

Devlin's chain 5.5 and 5.6 concludes cardinal equations, and so does Jech's
13.20 (`dev/literature/devlin-II5.md:145-166`). **A cardinal inequality is a
truncated existence of an injection.** That is the HoTT Book's own definition,
not a reading imposed on the set theorists:

> `card(A) ≤ card(B) :≡ ∥ inj(A,B) ∥` ... "In other words, `card(A) ≤ card(B)`
> means that there merely exists an injection from A to B."
> (HoTT Book, Definition 10.2.7)

**So a proof that only needs cardinal arithmetic never needs an injection as
data, and the untruncation question does not arise in the classical texts.** A
formalization that states its conclusion with the injection as data is asking
for something the sources do not supply.

## 2. THE TYPE-THEORY SIDE: when a truncation can be untruncated

### 2.1 The free case: unique choice

HoTT Book Lemma 3.9.1: if `P` is a mere proposition then `P ≃ ∥P∥`.
HoTT Book Corollary 3.9.2, the principle of unique choice.

**This is the only free case.** Everything below is about paying for the rest.

### 2.2 The documented route is exactly the set theorists' route

The paragraph after HoTT Book Corollary 3.9.2, verbatim:

> Namely, suppose we know that ∥A∥, and we want to use this to construct an
> element of some other type B. ... Instead, we can extend B with additional
> data which characterizes UNIQUELY the object we wish to construct.
> Specifically, we define a predicate Q : B → Type such that Σ(x:B) Q(x) is a
> mere proposition. Then from an element of A we construct an element b : B
> such that Q(b), hence from ∥A∥ we can construct ∥Σ(x:B) Q(x)∥, and because
> ∥Σ(x:B) Q(x)∥ is equivalent to Σ(x:B) Q(x) an element of B may be projected
> from it. An example can be found in Exercise 3.19.

**`Q` is leastness.** HoTT Book Exercise 3.19 is the instance over `ℕ`:

> Suppose P : ℕ → Type is a decidable family of mere propositions. Prove that
> ∥ Σ(n:ℕ) P(n) ∥ → Σ(n:ℕ) P(n).

And the general form, for an arbitrary ordinal, is in the proof of HoTT Book
Theorem 10.4.3:

> But trichotomy implies that any minimal element is a least element.
> Moreover, least elements are unique when they exist, **so merely having one
> is as good as having one.**

Escardó's lecture notes give the same route as running Agda, in the section
"Exiting truncations": `find-∥∥-existing-root` finds the MINIMAL root of
`f : ℕ → ℕ` from `∃ n, f n = 0`, and `∥∥-recursion-set` eliminates a truncation
into a SET when the map is weakly constant
(`cs.bham.ac.uk/~mhe/HoTT-UF-in-Agda-Lecture-Notes/HoTT-UF-Agda.html`, the
`exit-∥∥` module region).

### 2.3 The project already has the route

`src/L/WellOrder/Base.lagda.md:158-160`:

```agda
leastOf : {ℓ'' : Level} → LEM (ℓ-max ℓc (ℓ-max ℓₚ ℓ''))
        → (P : A → hProp ℓ'')
        → ∥ Σ[ a ∈ A ] ⟨ P a ⟩ ∥₁ → Σ[ a ∈ A ] IsLeast P a
```

with `IsLeast P a = ⟨ P a ⟩ × ((b : A) → ⟨ P b ⟩ → ¬ b <∙ a)`
(`src/L/WellOrder/Base.lagda.md:131`). **That is Devlin's `ψ` and Jech's
universal guard, in Agda.** The absorber is `isPropLeastOf`
(`src/L/WellOrder/Base.lagda.md:136-139`), and the chapter's own prose names
the reason: "a proposition-valued goal absorbs the truncation"
(`src/L/WellOrder/Base.lagda.md:120-121`).

**The constraint the route carries: `P` must be `hProp`-valued.** So `leastOf`
delivers the least INDEX untruncated, and any payload it delivers with the
index is a proposition. **A data payload does not come out.**

### 2.4 The exact criterion, necessary and sufficient

Kraus, Escardó, Coquand and Altenkirch, "Notions of Anonymous Existence in
Martin-Löf Type Theory", LMCS 13(1), 2017, arXiv:1610.03346.

- `splitSup X :≡ ∥X∥ → X` (section 3, equation (29)).
- Lemma 12, the Fixed Point Lemma: for a weakly constant `f : X → X`, the type
  `fix f` is a proposition.
- **Theorem 16: "A type X has a constant endomap if and only if it has split
  support in the sense that ∥X∥ → X."** ("Constant" means weakly constant:
  `f x = f y` for all `x, y`.)
- Theorem 17: a MERELY weakly constant endomap is enough.

**So the question "can this truncation be lifted" is always the question "does
this type have a weakly constant endomap".** The least-element route is one way
to build one: normalize any witness to the least one.

### 2.5 The eliminator the cubical library actually has

The propositional truncation's eliminator into a PROPOSITION is not the only
one. In the cubical library this project builds against, Agda 2.8.0 at
`/opt/homebrew/Cellar/agda/2.8.0-r3/share/agda/cubical`:

```agda
module SetElim (Bset : isSet B) where
  rec→Set : (f : A → B) (kf : 2-Constant f) → ∥ A ∥₁ → B
```

`Cubical/HITs/PropositionalTruncation/Properties.agda:181-190`, exported at
`:268`. `2-Constant f = ∀ x y → f x ≡ f y`
(`Cubical/Foundations/Function.agda:106-107`). The library's own comment cites
Kraus, arXiv:1411.2682.

And the condition is not only sufficient:

```agda
trunc→Set≃ : (∥ A ∥₁ → B) ≃ Σ (A → B) 2-Constant
```

`Properties.agda:225`, exported `:268`. **For a set `B`, the maps out of
`∥ A ∥₁` ARE the weakly constant maps `A → B`.** `elim→Set`
(`Properties.agda:270-274`) does the same for a dependent set-valued motive.

**The practical rule this gives.** When a proof stalls at "`PT.rec` demands a
propositional motive" and the motive is a SET, the obligation is not a new
principle. **It is a `2-Constant` proof.** Discharge it or refute it before
pricing anything else.

### 2.6 What the GLOBAL form costs, and what it does not touch

Kraus et al., section 7.1: "if we assume that all types have split support,
then this in particular holds for path spaces, and by Theorem 7, every type is
a set. This assumption also implies the axiom of choice ... this allows us to
use Diaconescu's proof of LEM." Theorem 29: "If every type has a constant
endofunction then every type has decidable equality."

The HoTT Book gives the same taboo in its own words. Theorem 3.2.2: "It is not
the case that for all A : U we have ¬(¬A) → A." The Remark right after:

> In particular, this implies that there can be no Hilbert-style "choice
> operator" which selects an element of every nonempty type. The point is that
> no such operator can be natural, and under the univalence axiom, all
> functions acting on types must be natural with respect to equivalences.

Corollary 3.2.7: "It is not the case that for all A : U we have A + (¬A)."

**These refute the UNIVERSALLY QUANTIFIED form. They do not reach a family
indexed by a set.** The refutation runs on a fixed-point-free autoequivalence
supplied by univalence. A family indexed by `V ℓ`, which is a set, offers no
such autoequivalence, so the argument has no handle. **A principle of that
shape is therefore not refuted by the standard taboo, and it is also not
proved. It must be ruled on.**

### 2.7 The axiom of choice does NOT give an untruncated selection

HoTT Book (3.8.1) and Lemma 3.8.2 both have a TRUNCATED conclusion:

    (∏x ∥Y x∥) → ∥∏x Y x∥

So AC delivers `∥ f ∥₁` for a selection function `f`, never `f`. **If the goal
that consumes `f` is not a proposition, AC does not help.** This is worth
writing down because it is easy to assume that assuming choice settles the
matter. It does not.

HoTT Book Lemma 3.8.5 adds that the index must be a SET: there is a type `X`
and a family of sets over it for which the choice statement is false.

## 3. WHAT OTHER FORMALIZATIONS DID

### 3.1 A classical formalization cannot meet the question

Paulson's Isabelle/ZF proves `L_implies_AC`
(`dev/literature/formalizations-landscape.md:216-221`). The logic is classical
first-order ZF. **In classical first-order logic, existential elimination
supplies a fresh witness with no truncation and no side condition.** So the
selection question cannot be stated there.

**A formalization that cannot face the question is not evidence that the
question is easy.** Paulson also did not do GCH: he lists it as future work
(`dev/literature/formalizations.md:104-106`).

### 3.2 No constructive or type-theoretic formalization of `L` exists

MEASURED against `dev/literature/formalizations-landscape.md:25-32`, the
six-system table of 2026-08-02: Metamath, Mizar, Isabelle AFP, Lean mathlib4
and community, Coq/Rocq opam, Naproche. The only formal `L` anywhere is
Isabelle/ZF's, which is classical. The absence wording stays "not found via
the index cited on that date".

The closest thing that exists is a PAPER, not a formalization: Matthews,
Richard and Rathjen, Michael, "Constructing the Constructible Universe
Constructively", Annals of Pure and Applied Logic 175 (2024), no. 3, article
103392; arXiv:2206.08283v3, 26 Sep 2023. Abstract, verbatim:

> We study the properties of the constructible universe, L, over intuitionistic
> theories. We give an extended set of fundamental operations which is
> sufficient to generate the universe over Intuitionistic Kripke-Platek set
> theory without Infinity. Following this, we investigate when L can fail to be
> an inner model in the traditional sense. Namely, we show that over
> Constructive Zermelo-Fraenkel (even with the Power Set axiom) one cannot
> prove that the Axiom of Exponentiation holds in L.

Two of its remarks bear on any constructive `L`:

- The Axiom of Choice implies the Law of Excluded Middle over very weak
  theories (section 1). So an ambient choice principle is not a small thing in
  a constructive base.
- "if Excluded Middle were to fail, then the ordinals can no longer be linearly
  ordered so while we may have no gaps in the ordinals, our 'tree' of ordinals
  could be missing branches from the ground model" (section 6).

This project spends LEM explicitly, so it is not in the failing regime. **The
paper is a warning about the cost of a constructive `L`, not a precedent for
any ruling here.**

## 4. THE CHECKLIST THIS DIGEST EXISTS TO SUPPLY

When a proof in this tree stalls on `∥ A ∥₁`, ask in this order.

1. **Is the goal a proposition?** Then `PT.rec` applies and there is nothing to
   discuss.
2. **Is `A` a proposition?** Then unique choice applies (HoTT Book Corollary
   3.9.2), and the truncation was never needed.
3. **Is the goal a SET, and is there a `2-Constant` map `A → goal`?** Then
   `rec→Set` applies (`Properties.agda:185`). By `trunc→Set≃` this is not only
   sufficient: it is what any such map amounts to. **This step is easy to skip
   and it is the one that most often has an answer.**
4. **Does `A` decompose as an index over a well-order plus a
   PROPOSITION-valued payload?** Then `leastOf` applies
   (`src/L/WellOrder/Base.lagda.md:158-160`), and this is Devlin's, Jech's and
   Schindler and Zeman's own device.
5. **Does `A` have a weakly constant endomap by any other route?** That is
   necessary and sufficient (Kraus et al., Theorem 16).

**A DEFECT IN STEP 4, MEASURED 2026-08-16 by `[LJ-1.334]`, and it fired on a
real candidate.** **Step 4 prices whether a canonical map can be DEFINED. It
does not price whether that map has the property the deliverable needs.** A
pointwise-least pairing passes step 4, is TOTAL, and compiles. It is then
REFUTED because it is SYMMETRIC, so it is injective only if the carrier is a
proposition. **The whole refutation is the flip of a pair and it uses no
excluded middle.**

**AND THE REFUTATION CLOSES A FAMILY, not one recipe.** **Every canonical
pairing that reads only the reachable set is symmetric, hence not injective:
least, greatest or any other reader dies the same way.** The cause is stated
with a term: the witness family carries an action of the carrier's
self-injections, and a canonical reader inherits that invariance.

**SO ADD STEP 6, and it is the one this project needed.** **Does the canonical
map have to BREAK a symmetry the family carries?** **If it does, no reader of
the family can serve, and the missing datum is a symmetry-breaking one on the
WITNESSES rather than a well-order on the targets.** **This is the digest's own
next sentence made operational:** a well-order on the targets is not enough, and
what is missing is a well-order on the INJECTIONS.
6. **Only then is a new principle in question.** State it as a module
   parameter, never a postulate (DD9), and expect to rule on it, because the
   literature neither proves nor refutes a set-indexed instance.

## 5. WHAT THIS DIGEST DOES NOT SETTLE

1. Whether a given payload has a weakly constant endomap. That is a per-site
   question and this file gives only the criterion.
2. Whether a well-order on the two carriers yields a canonical injection
   between them. It does not, in general: the greedy construction that sends
   each element to the least unused target fails at order type `ω · 2` into
   `ω`. **A canonical injection needs a well-order on the INJECTIONS, which is
   what `<_L` supplies classically and what an ambient function type does not
   have.**
3. Whether any trophy statement in this project must carry data rather than a
   truncation. That is the owner's, and section 1.5 is the evidence he should
   see when he rules.

## 6. SOURCES, WITH STATUS

READ: HoTT Book chapters 3 and 10, from the `HoTT/book` LaTeX source
(`logic.tex`, `setmath.tex`), with every number checked against the book's own
`main.labelnumbers.first-edition`. Kraus, Escardó, Coquand and Altenkirch,
arXiv:1610.03346, sections 3, 4 and 7.1. Matthews and Rathjen,
arXiv:2206.08283v3, abstract and sections 1 and 6. Escardó, "Introduction to
Univalent Foundations of Mathematics with Agda", the "Exiting truncations"
section. Jech ch. 13 at `_build/literature/jech13.txt`. Schindler and Zeman at
`_build/literature/sz-full.txt`. Devlin ch. II through
`dev/literature/devlin-II5.md` and `_build/literature/dev2.txt`. The cubical
library at `/opt/homebrew/Cellar/agda/2.8.0-r3/share/agda/cubical`.

POINTER-ONLY: Kraus, arXiv:1411.2682, named in the cubical library's own
comment as the source of `rec→Set`. Kunen, "Set Theory", not fetched: Jech and
Schindler and Zeman gave the same universal guard from disk.

Exercise numbers in HoTT Book chapter 3 past 3.20 are edition-dependent. The
exercise labelled `ex:decidable-choice-strong` in the current book source
("Show that the conclusion of Exercise 3.19 is true if `P : ℕ → Type` is any
decidable family") is NOT in the first-edition label table, so it is cited by
label and by content, never by number.
