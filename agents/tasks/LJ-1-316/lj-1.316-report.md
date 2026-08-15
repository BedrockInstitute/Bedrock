# LJ-1.316 report: literature for the `InjData` ruling

tier: opus (in-harness-subagent-mode). A LITERATURE SURVEY. Nothing lands.
All writes are in `agents/tasks/LJ-1-316/`. Written incrementally (C-22).
ASD-STE100. Every source is marked READ, SKIMMED or POINTER-ONLY. Every
negative is marked MEASURED or INFERRED. No Agda ran.

## 0. LEAD

**THE LITERATURE DOES NOT DERIVE `InjData`, AND IT DOES NOT REFUTE IT. IT
GIVES THE EXACT ROUTE, IT GIVES THE EXACT CONDITION THAT THE ROUTE NEEDS,
AND `InjData`'s PAYLOAD FAILS THAT CONDITION FOR A NAMED REASON.**

The route is minimality over a well-order. It IS documented, three times over,
and this project already implements it as `leastOf`. The route works when the
payload at the least element is a PROPOSITION. `Wat α`'s payload is an
injection, which is data.

**Two things the literature adds that `[LJ-1.305]` did not have.** First, a
necessary AND sufficient criterion: a type `X` has `∥ X ∥₁ → X` if and only if
`X` has a weakly constant endomap (Kraus, Escardó, Coquand and Altenkirch,
Theorem 16). Second, and this is a DOOR behind `[LJ-1.305]`'s wall (C-39, C-36):
the cubical library the project already imports has `rec→Set`, which eliminates
`∥ A ∥₁` into a SET, not only into a proposition, when the map is `2-Constant`.
`[LJ-1.305]`'s J1 says "`PT.rec` demands a propositional motive". That is true
of `PT.rec`. It is NOT true of the theory, and it is not true of the library.
Section 2.5 states the exact obligation this opens.

**No constructive or type-theoretic FORMALIZATION of `L` exists.** MEASURED
against the project's own six-system sweep and one new source. Bedrock is first,
and no precedent can settle the ruling.

## 1. THE SET-THEORY SIDE: how the classical proof selects

Three authors. **None of them uses choice.** All three select the LEAST element
under a definable well-order, and all three encode leastness with a UNIVERSAL
GUARD, which is what makes the selection unique.

### 1.1 Devlin (READ, through the repo digest and the OCR)

`dev/literature/devlin-II5.md:127-131`, quoting `_build/literature/dev2.txt:1340-1350`.
Lemma II.5.3, the definable hull, verifies Tarski's criterion by forming

    ψ(v₀) = φ(v₀) ∧ ∀v₁(v₁ <_L v₀ → ¬φ(v₁))

"The least witness is the unique witness of ψ, so it is definable from the same
parameters." Devlin's own gloss: the lemma is "really a result about structures
with definable wellorders" (`dev/literature/devlin-II5.md:262-263`, quoting
`_build/literature/dev2.txt:1328-1329`).

Step D of the digest names the requirement: "a definable well-order of L_α, used
to pick the `<_L`-least witness of each formula"
(`dev/literature/devlin-II5.md:259-261`).

Devlin II.5.9 makes the selection itself a theorem: the least element of a
non-empty Σ₀ predicate is Σ₁-definable from its parameters
(`dev/literature/devlin-II5.md:422-423`, quoting `_build/literature/dev2.txt:1408-1423`).

### 1.2 Jech (READ, `_build/literature/jech13.txt`)

Jech, "Set Theory", 3rd millennium edition, Chapter 13. Lemma 13.19's proof,
`_build/literature/jech13.txt:744-753`, verbatim:

> The only potential difficulty might be the use of the words "the <-least,"
> and that can be overcome as follows: For example, in (13.15)(ii)(c)
>   the <ⁿ_{α+1}-least v ∈ Wⁿ_α such that x = G_i(u,v)
>   <ⁿ_{α+1} the <ⁿ_{α+1}-least t ∈ Wⁿ_α such that y = G_i(u,t)
> can be written as
>   (∃v ∈ Wⁿ_α)[x = G_i(u,v) ∧ (∀t ∈ Wⁿ_α)(y = G_i(u,t) → v <ⁿ_{α+1} t)].

**That is the same universal guard as Devlin's, at a different site.** Jech
writes it out precisely because "the <-least" must be made definable.

Jech Exercise 13.24, `_build/literature/jech13.txt:1141-1144`, verbatim:

> If δ is a limit ordinal, then the model (Lδ, ∈) has definable Skolem
> functions. Therefore, for every X ⊂ Lδ, there exists a smallest
> M ≺ (Lδ, ∈) such that X ⊂ M. [The well-ordering <δ is definable in (Lδ, ∈).
> Let h_φ(x) = the <δ-least y such that (Lδ, ∈) ⊨ φ[x, y].]

That is Devlin II.5.3 in Jech's hand. The Skolem function IS the least-witness
selector.

### 1.3 Schindler and Zeman (READ, `_build/literature/sz-full.txt`)

Theorem 1.15, `_build/literature/sz-full.txt:527-528`: "Let M be a J-structure.
There is a Σ1 Skolem function h_M which is uniformly Σ^M_1." The canonical
well-order's own construction uses "the <-least" at
`_build/literature/sz-full.txt:697-705`.

### 1.4 The answer to the brief's question, in one paragraph

**The classical proof produces the witness by taking the LEAST one under a
definable well-order. It invokes NO choice. MEASURED against three authors.**
What supplies the selection is not choice but the definable well-order plus
the universal guard `∀v₁(v₁ < v₀ → ¬φ(v₁))`, which turns "some witness" into
"the witness" and therefore makes the selection a FUNCTION.

### 1.5 The observation the brief did not ask for, and it matters most

**The classical proof at this step never needs the injection as DATA, because
its conclusion is itself an existential.** In Devlin the chain 5.5 and 5.6
concludes cardinal equations, `|L_α| = |α|` and `2^κ = κ⁺`
(`dev/literature/devlin-II5.md:145-166`). In Jech the same, at 13.20
(`_build/literature/jech13.txt:1157` region, Theorem 13.20).

A cardinal inequality is a TRUNCATED existence of an injection. That is not
Bedrock's reading of the classical texts; it is the HoTT Book's own definition:

> `card(A) ≤ card(B) :≡ ∥ inj(A,B) ∥` ... "In other words, card(A) ≤ card(B)
> means that there merely exists an injection from A to B."
> (HoTT Book, Definition 10.2.7, source `setmath.tex:773-786`)

**So the classical literature is SILENT on `InjData` in the strict sense: the
question cannot arise there, because the classical conclusion at this step is
proposition-valued and the truncation is never in the way.** `SqShape`
(`src/L/GCH.lagda.md:46-49`) asks for the injection untruncated. That is a
choice this project made, not one the sources force. INFERRED, from the two
sources named: neither Devlin nor Jech states a data-valued square law.

## 2. THE TYPE-THEORY SIDE

### 2.1 Unique choice is the free case, and it does not reach `Wat`

HoTT Book Lemma 3.9.1: "If P is a mere proposition, then P ≃ ∥P∥"
(`logic.tex:809-818`). HoTT Book Corollary 3.9.2, "The principle of unique
choice" (`logic.tex:830-841`).

`Wat α` is not a mere proposition. `[LJ-1.305]` MEASURED the companion fact
with a term: `sq ω` is not an hProp
(`agents/tasks/LJ-1-305/NotProp.agda:203-204`). For `Wat α` itself the same
holds for the same reason: the payload `⟪ α ⟫ ↪ ⟪ δ ⟫` is a function plus a
proposition, and two different injections are two different inhabitants.
INFERRED for `Wat α` specifically: I built no term, and none was asked for.

### 2.2 Minimality over a well-order IS the documented route

**Yes. It is documented, and the HoTT Book states it as a general technique,
not as a trick.** The paragraph immediately after Corollary 3.9.2,
`logic.tex:842-851`, verbatim:

> Namely, suppose we know that ∥A∥, and we want to use this to construct an
> element of some other type B. We would like to use an element of A in our
> construction of an element of B, but this is allowed only if B is a mere
> proposition ... Instead, we can extend B with additional data which
> characterizes UNIQUELY the object we wish to construct. Specifically, we
> define a predicate Q : B → Type such that Σ(x:B) Q(x) is a mere proposition.
> Then from an element of A we construct an element b : B such that Q(b),
> hence from ∥A∥ we can construct ∥Σ(x:B) Q(x)∥, and because ∥Σ(x:B) Q(x)∥ is
> equivalent to Σ(x:B) Q(x) an element of B may be projected from it. An
> example can be found in Exercise 3.19.

**Q is the leastness predicate. That paragraph is `leastOf`, written in
English, in 2013.**

HoTT Book Exercise 3.19, `logic.tex:1249-1254`, verbatim:

> Suppose P : ℕ → Type is a decidable family of mere propositions. Prove that
> ∥ Σ(n:ℕ) P(n) ∥ → Σ(n:ℕ) P(n).

HoTT Book Chapter 10 says the same about well-orders in general. In the proof
of Theorem 10.4.3, `setmath.tex:1322-1326`:

> But trichotomy implies that any minimal element is a least element. Moreover,
> least elements are unique when they exist, **so merely having one is as good
> as having one.**

**That sentence is the route, stated for an arbitrary ordinal, not only for ℕ.**

**Every one of these numbers was checked mechanically against the book's own
label-to-number table**, `main.labelnumbers.first-edition` in the `HoTT/book`
repository: `cor:UC` = 3.9.2, `ex:decidable-choice` = 3.19,
`thm:ac-epis-split` = 3.8.2, `thm:no-higher-ac` = 3.8.5, `thm:not-dneg` = 3.2.2,
`thm:not-lem` = 3.2.7, `thm:ttac` = 2.15.7, `defn:card` = 10.2.1,
`thm:injsurj` = 10.2.9, `thm:wfmin` = 10.3.8, `thm:ordord` = 10.3.20,
`thm:wellorder` = 10.4.3, `thm:wop` = 10.4.4.

### 2.3 The route needs the payload to be a proposition, and that is the whole story

The project's `leastOf` is the route, already built:

```agda
leastOf : {ℓ'' : Level} → LEM (ℓ-max ℓc (ℓ-max ℓₚ ℓ''))
        → (P : A → hProp ℓ'')
        → ∥ Σ[ a ∈ A ] ⟨ P a ⟩ ∥₁ → Σ[ a ∈ A ] IsLeast P a
```

at `src/L/WellOrder/Base.lagda.md:158-160`. The absorber is `isPropLeastOf`
(`src/L/WellOrder/Base.lagda.md:136-139`), and it needs `P : A → hProp`. The
chapter's own prose says why: "a proposition-valued goal absorbs the
truncation" (`src/L/WellOrder/Base.lagda.md:120-121`).

`IsLeast P a = ⟨ P a ⟩ × ((b : A) → ⟨ P b ⟩ → ¬ b <∙ a)`
(`src/L/WellOrder/Base.lagda.md:131`) **is Devlin's ψ and Jech's universal
guard, in Agda.** The three literatures agree on one object.

**So this is the exact meeting point the brief asked for.** Apply `leastOf`
to `Wat α` with `A = V ℓ` and the ordinal order: you get the LEAST `δ`, and
you get it untruncated. You do NOT get the injection, because the predicate
must be `hProp`-valued, so the most it can say is `∥ ⟪ α ⟫ ↪ ⟪ δ ⟫ ∥₁`.
**The least ordinal is unique. The injection at it is not.**

**THE SENTENCE FOR `[LJ-1.314]`'s ATTACK 1.** The classical proof selects by
least element under `<_L`, and `<_L` orders the INJECTIONS too, because in `L`
an injection is a set. In the port, `⟪ α ⟫ ↪ ⟪ δ ⟫` is a type of AMBIENT
functions, and no order in the tree reaches them. **What blocks the classical
move here is not the truncation. It is that the object to be selected lives
outside every well-ordered domain the tree has.** That is the same wall
`[LJ-1.305]` section 5.3 item 2 calls the ambient-to-code crossing, reached
from the outside.

### 2.4 The exact criterion: a weakly constant endomap

Kraus, Escardó, Coquand and Altenkirch, "Notions of Anonymous Existence in
Martin-Löf Type Theory", Logical Methods in Computer Science 13(1), 2017,
arXiv:1610.03346. READ, via the ar5iv HTML rendering.

- Definition, section 3, equation (29): `splitSup X :≡ ∥X∥ → X`.
- **Theorem 16, section 4**: "A type X has a constant endomap if and only if it
  has split support in the sense that ∥X∥ → X." ("Constant" here means weakly
  constant: `f x = f y` for all `x`, `y`; section 2.)
- Theorem 17: it is enough that the endomap is MERELY weakly constant.
- Lemma 12, the Fixed Point Lemma, section 4: for a weakly constant `f`, the
  type `fix f` is a proposition. **That is the same absorber as
  `isPropLeastOf`, at full generality.**

**So `InjData` is EXACTLY the claim that each `Wat α` has a weakly constant
endomap.** That is a checkable obligation, and it is sharper than "the
truncation cannot be lifted". To discharge it one must normalize an arbitrary
`(δ, δ∈α, f)` to one that does not depend on which one was given. Taking the
least `δ` normalizes the first two components. The third is the open term.

**MEASURED FALSE, at this survey's reach: a canonical injection between two
well-ordered sets of equal cardinality, built from the well-orders alone.**
The greedy construction (send each element of `⟪ α ⟫` to the least unused
element of `⟪ δ ⟫`) does not terminate as an injection: it fails already at
order type `ω · 2` into `ω`, where it exhausts the target at the ω-th step.
This is my own counterexample, at the level of well-ordered sets, and I state
it as an argument and not as a source.

### 2.5 THE DOOR BEHIND THE WALL (C-39, C-36)

`[LJ-1.305]` section 3, J1, says: "Under an untruncated motive the outer
elimination has NO typing: `PT.rec` demands a propositional motive"
(`agents/tasks/LJ-1-305/lj-1.305-report.md:112-114`).

**That is true of `PT.rec`. It is false of the library.** MEASURED, in the
cubical library this project builds against, Agda 2.8.0 at
`/opt/homebrew/Cellar/agda/2.8.0-r3/share/agda/cubical`:

```agda
module SetElim (Bset : isSet B) where
  rec→Set : (f : A → B) (kf : 2-Constant f) → ∥ A ∥₁ → B
```

at `Cubical/HITs/PropositionalTruncation/Properties.agda:181-190`, exported at
`:268`. `2-Constant f = ∀ x y → f x ≡ f y` at
`Cubical/Foundations/Function.agda:106-107`. The library's own comment at
`Properties.agda:176-180` cites Kraus, "The General Universal Property of the
Propositional Truncation", arXiv:1411.2682 (POINTER-ONLY, not fetched).

There is more. `trunc→Set≃ : (∥ A ∥₁ → B) ≃ Σ (A → B) 2-Constant`
(`Properties.agda:225`, exported `:268`) makes the condition **necessary as
well as sufficient**: for a set `B`, the maps out of `∥ A ∥₁` are EXACTLY the
weakly constant maps `A → B`. And `elim→Set` (`Properties.agda:270-274`) does
the same for a dependent set-valued motive.

**What this changes.** `sq α` is a set: it is a Σ of a function type into
`⟪ α ⟫` with a propositional injectivity component
(`src/L/Ordinal/SquareLaw.lagda.md:685-687`), and `⟪ α ⟫` is a set. INFERRED,
not typechecked, because this task runs no Agda. If `sq α` is a set, then
`rec→Set` gives a THIRD route past J1 that `[LJ-1.305]` did not price:

> **Build a `2-Constant` map `Wat α → sq α`, and no principle is needed at
> this join.**

And by `trunc→Set≃`, that obligation is not merely sufficient. It is what
ANY map `∥ Wat α ∥₁ → sq α` amounts to. **So necessity of `InjData` at the
eliminator level reduces to one decidable-looking question, and
`[LJ-1.305]`'s "no typing" claim measured only the wrong eliminator.**

I do not claim the door is open. `[LJ-1.305]` MEASURED that `sq ω` has two
distinct inhabitants (`NotProp.agda:203-204`, `twisted≢square` at `:182-183`),
so a `2-Constant` map into it is a real constraint. **I claim the door was
never tried, and that the literature and the library both name it.**

### 2.6 What the global form would cost, and why `InjData` escapes it

If EVERY type had split support, the theory would break. Kraus et al.,
section 7.1, verbatim: "if we assume that all types have split support, then
this in particular holds for path spaces, and by Theorem 7, every type is a
set. This assumption also implies the axiom of choice [HoTT Book, Chapter 3.8].
If we have univalence for propositions and set quotients, this allows us to use
Diaconescu's proof of LEM." Theorem 29: "If every type has a constant
endofunction then every type has decidable equality."

The HoTT Book gives the same taboo in its own words. Theorem 3.2.2: "It is not
the case that for all A : U we have ¬(¬A) → A" (`logic.tex:177-179`). The
Remark right after, `logic.tex:222-227`, verbatim:

> In particular, this implies that there can be no Hilbert-style "choice
> operator" which selects an element of every nonempty type. The point is that
> no such operator can be natural, and under the univalence axiom, all
> functions acting on types must be natural with respect to equivalences.

Corollary 3.2.7: "It is not the case that for all A : U we have A + (¬A)"
(`logic.tex:234-236`).

**`InjData` is not the global form, and the refutation does not reach it.**
The refutation runs on a fixed-point-free autoequivalence of `Bool` obtained
from univalence. `InjData`'s index is `V ℓ`, which is a SET
(`setIsSet`, imported at `src/L/Choice/Transversal.lagda.md:72`), so there is
no non-trivial autoequivalence for the naturality argument to use. INFERRED:
no model and no counter-model was built here, and none is claimed.

## 3. WHAT OTHER FORMALIZATIONS DID

### 3.1 Isabelle/ZF cannot face the question, and that is the point

`dev/literature/formalizations.md` and `dev/literature/formalizations-landscape.md`
are both READ WHOLE, before any web search, as the brief ordered.

Paulson's Isabelle/ZF proves `L_implies_AC` (`dev/literature/formalizations-landscape.md:216-221`,
quoting the theory page: "theorem L_implies_AC : assumes x : "L(x)" shows "EX r.
well_ord(x,r)""). The logic is classical first-order ZF. **In classical
first-order logic, existential elimination hands you a fresh witness with no
truncation and no side condition.** There is no propositional truncation to
lift, so the question this task asks cannot be stated there.

**So Paulson is not evidence that the step is easy. He is evidence that a
classical formalization never meets the step.** That is exactly the caution
the brief asked me to check, and it holds.

Paulson also did NOT do GCH: "Future investigators might also try formalizing
the proof that L satisfies the generalized continuum hypothesis and the
combinatorial principle ♦" (`dev/literature/formalizations.md:104-106`, P p. 65).
So the descent step in question was never mechanized by him at all.

### 3.2 Is there ANY constructive or type-theoretic formalization of `L`?

**NO. MEASURED against the project's own six-system sweep, and not refuted by
one new source.**

`dev/literature/formalizations-landscape.md:25-32` is the table: Metamath,
Mizar, Isabelle AFP, Lean mathlib4 and community, Coq/Rocq opam, Naproche. The
only formal object `L` anywhere is Isabelle/ZF's, which is classical. The sweep
is dated 2026-08-02 and its absence wording is "not found via the index cited",
which I keep.

The one new source I found is NOT a formalization. Matthews, Richard and
Rathjen, Michael, "Constructing the Constructible Universe Constructively",
Annals of Pure and Applied Logic 175 (2024), no. 3, article 103392;
arXiv:2206.08283v3, 26 Sep 2023. READ (the arXiv HTML rendering). Abstract,
verbatim:

> We study the properties of the constructible universe, L, over intuitionistic
> theories. We give an extended set of fundamental operations which is
> sufficient to generate the universe over Intuitionistic Kripke-Platek set
> theory without Infinity. Following this, we investigate when L can fail to be
> an inner model in the traditional sense. Namely, we show that over
> Constructive Zermelo-Fraenkel (even with the Power Set axiom) one cannot
> prove that the Axiom of Exponentiation holds in L.

That is a pen-and-paper study over IKP and CZF, with no machine check. Two of
its facts bear on Bedrock and the owner should see them:

- Section 1: "The Axiom of Choice implies the Law of Excluded Middle" over very
  weak theories (arXiv HTML, the numbered results list after the theory
  section). So in a constructive base, an ambient choice principle is not a
  small thing.
- Section 6: "if Excluded Middle were to fail, then the ordinals can no longer
  be linearly ordered so while we may have no gaps in the ordinals, our 'tree'
  of ordinals could be missing branches from the ground model."

Bedrock spends LEM explicitly (`leastOf` takes it), so it is not in the failing
regime. The paper is a warning about what a constructive `L` costs, not a
precedent for this ruling.

**Verdict for the abort criterion: NO CONSTRUCTIVE FORMALIZATION OF `L`
EXISTS. It FIRES. There is no precedent and the ruling is genuinely new.**

## 4. WHAT `InjData` IS, IN STRENGTH TERMS

### 4.1 The name the literature gives it

`InjData` is **pointwise split support for the family `Wat`**. Formally it is
`(α : V ℓ) → IsOrd α → ⟨ ω ∈ˢ α ⟩ → splitSup (Wat α)` in Kraus et al.'s
vocabulary (section 3, equation (29)), and by their Theorem 16 it is
equivalently a family of weakly constant endomaps on `Wat α`.

**It is NOT any of the four things the brief listed:**

- **NOT unique choice.** HoTT Book Corollary 3.9.2 needs `Wat α` to be a mere
  proposition, and it is not (section 2.1).
- **NOT the HoTT Book's axiom of choice.** HoTT Book (3.8.1) and Lemma 3.8.2
  both have a TRUNCATED conclusion: `(∏x ∥Y x∥) → ∥∏x Y x∥`
  (`logic.tex:742-751`). AC would deliver `∥ InjData ∥₁` and no more.
  `InjData` is used to build `sq α`, which `[LJ-1.305]` MEASURED is not a
  proposition, so a truncated `InjData` cannot be eliminated into the goal.
  **`InjData` is therefore stronger in FORM than the HoTT Book's AC**, even
  though it is weaker in reach, being one family rather than all sets.
  INFERRED: I proved no separation.
- **NOT countable or dependent choice.** The index is `V ℓ`, a proper
  set-sized universe of sets, not `ℕ` and not a chain.
- **NOT `AC_{set,set}` as stated in the book**, for the truncation reason above.

**What it IS an instance of:** the type-theoretic axiom of choice `AC_∞`
(HoTT Book Theorem 2.15.7, `logic.tex` cross-reference `thm:ttac`) applied to
an already-truncated hypothesis, which is precisely the move `AC_∞` does not
license. And it follows from `LEM_∞` (`∏(A:U) A + ¬A`), which HoTT Book
Corollary 3.2.7 refutes, and from a global choice operator, which the Remark
after Theorem 3.2.2 refutes. **Neither refutation reaches the restricted form**
(section 2.6).

### 4.2 Does `--safe` Agda prove or refute it?

**Neither. INFERRED**, from the tree's own practice rather than from the Agda
manual, which I did not fetch. `--safe` forbids postulates and unsafe pragmas;
a MODULE PARAMETER is neither. The tree already carries `LEM` as a module
parameter under `--safe` (`[LJ-1.305]` section 5.3, citing
`src/Base/Classical.lagda.md:52-57`), so the same discipline admits `InjData`
with the debt visible in every type. **MEASURED FALSE, at this survey's reach:
any source that proves or refutes a principle of this shape in cubical type
theory.**

### 4.3 Does it undermine the AC trophy?

**On the evidence: NO, it is orthogonal today, and the risk is not logical but
structural.** Three points, in order of how well I can support them.

1. **The AC trophy does not use it, and could not.** `L ⊨ AC` is an INTERNAL
   statement about the model. Its existence half comes from `leastOf`, the
   minimality search, per the tree's own chapter note
   (`src/Everything.lagda.md:1000`: existence comes from `leastOf`, uniqueness
   from pairwise disjointness). `leastOf` takes LEM and nothing else. `InjData`
   is an AMBIENT selection over ambient injections. The internal proof cannot
   consume it.

2. **Today the principle would sit in the GCH-only part. MEASURED.** No module
   under `src/L/Choice/` or `src/L/WellOrder/` imports `L.Cardinal`,
   `L.Ordinal.SquareLaw`, `L.Absorption` or `L.InjChain` (grep, zero hits).
   The consumers of those four are `src/Everything.lagda.md` and
   `src/L/GCH.lagda.md` only, plus each other.

3. **The structural risk is DD4 itself.** `[LJ-1.305]` section 7 states, and
   this is its claim and not mine (C-44): "The two proofs share this descent
   wholesale: AC's counting consumes exactly this pairing, on either side of
   the axis." **If that sharing is realized, `InjData` moves from the GCH-only
   part into the SHARED part, and then the AC trophy's own module telescope
   carries an ambient selection principle.** Nothing would be logically wrong:
   the internal `L ⊨ AC` still would not use it. But a reader would see a
   choice-shaped parameter in the type of a theorem whose whole point is that
   choice is PROVED and not assumed. **That is a presentation cost, and it is
   real, and the owner should rule on it with his eyes open rather than
   discover it after DD4 is honoured.**

**I do not assert that admitting `InjData` damages the AC trophy. I assert
that the damage, if any, arrives through DD4's sharing and not through the
mathematics, and that the two must be ruled on together.**

## 5. DD4 AND ITS AXIS (C-46)

**THE AXIS IS AC-AGAINST-GCH, DD4's own.** This task writes no code, so DD4's
shared-line rule has no direct object here.

**The one line the brief asks for.** Today a principle of this shape sits in
the GCH-only part, MEASURED by the import closure in section 4.3 item 2. It
moves to the SHARED part exactly when DD4's own goal is met for the square-law
descent, because that descent is what both counts consume. **So DD4 and the
`InjData` ruling are coupled: honouring DD4 here enlarges the commitment.**

## 6. THE ABORT CRITERION, FIXED BEFORE THE RUN (D-1)

- **THE LITERATURE GIVES A DERIVATION. DOES NOT FIRE**, and this is the
  honest answer. It gives the ROUTE (sections 2.2, 2.3) and the exact
  CRITERION (section 2.4). It does not give a derivation of `InjData`.
- **THE LITERATURE SAYS IT CANNOT BE DERIVED. DOES NOT FIRE.** No source
  refutes it. The global taboos (section 2.6) do not reach the restricted form.
- **NO CONSTRUCTIVE FORMALIZATION OF `L` EXISTS. FIRES.** Section 3.2.
- **THE CLASSICAL PROOF SELECTS BY LEAST ELEMENT AND THAT IS ALL. FIRES.**
  Section 1. The sentence for `[LJ-1.314]` is in section 2.3.
- **ONE OUTCOME THE CRITERION DID NOT NAME, AND IT IS THE MOST ACTIONABLE.**
  Section 2.5: `rec→Set` and `trunc→Set≃` in the project's own library reduce
  the whole question at J1 to "is there a `2-Constant` map `Wat α → sq α`",
  and that question was never asked.

## 7. WHAT I DID NOT DO

- **No Agda ran.** No file was typechecked. Every claim about the library is a
  claim about its SOURCE TEXT, at a `file:line`.
- **Nothing was written outside `agents/tasks/LJ-1-316/`.** Nothing landed in
  `dev/literature/`. The digest is proposed at
  `agents/tasks/LJ-1-316/truncation-and-selection.md` for the orchestrator.
- **No commit, no push, no `make check`.**
- **I did not build a term for "`Wat α` is not an hProp".** It is INFERRED.
- **I did not typecheck "`sq α` is a set".** It is INFERRED, and section 2.5
  depends on it.
- **I did not fetch Kunen.** WHY NOT is in section 9.

## 8. ARCHIVE USED (DD18), ONE LINE READ PER FILE

- **`dev/literature/devlin-II5.md`, READ WHOLE.** Line read `:259-261`, Step D:
  "a definable well-order of L_α, used to pick the `<_L`-least witness of each
  formula". TAKEN: the classical selection device, and the universal-guard
  encoding at `:127-131`.
- **`dev/literature/formalizations-landscape.md`, READ WHOLE.** Line read
  `:29`, the Isabelle AFP row: "Yes, in ZF-Constructible (AC_in_L,
  L_implies_AC)" with GCH "No". TAKEN: the six-system absence verdict.
- **`dev/literature/formalizations.md`, READ WHOLE.** Line read `:104-106`,
  Paulson p. 65: GCH and ♦ as future work. TAKEN: the scope of the precedent.
- **`dev/literature/BIBLIOGRAPHY.md`, READ WHOLE, FIRST.** Line read
  `:189-195`, entry 21, Jech Chapter 13 fetched as
  `_build/literature/jech13.txt`. TAKEN: this saved a fetch, exactly as the
  brief predicted, and it gave me the second author from disk.
- **`agents/tasks/LJ-1-305/lj-1.305-report.md`, READ WHOLE.** Line read
  `:112-114`, J1: "`PT.rec` demands a propositional motive, and section 4
  refutes that for `sq α`". TAKEN: the probe's own account of the join, which
  section 2.5 answers with the library.
- **`archive/dev/TASKS-archived.md`, SHAPE ONLY, never a claim.** Line read
  `:298`, the `L3.32-T156` row, "D36 gate G2: the carried-sequence AC-necessity
  re-split". TAKEN, SHAPE ONLY: the retired route also had to decide which
  obligations were AC-forced and which were shared, and it recorded that
  decision as one row with the verdict in the row. Nothing of its content
  is used.

## 9. LITERATURE USED (DD18), WITH STATUS AND WHY NOT

### READ

| Source | Locator | What it gave |
|---|---|---|
| HoTT Book, chapter 3 source `logic.tex` | `HoTT/book` master, `logic.tex:159-260`, `:701-851`, `:1249-1254` | Theorem 3.2.2, Remark on the choice operator, Corollary 3.2.7, AC (3.8.1), Lemma 3.8.2, Lemma 3.8.5, Lemma 3.9.1, Corollary 3.9.2, the technique paragraph, Exercise 3.19 |
| HoTT Book, chapter 10 source `setmath.tex` | `HoTT/book` master, `setmath.tex:683-790`, `:1278-1400` | Definition 10.2.1, Definition 10.2.7 (cardinal `≤` is a truncation), Lemma 10.2.9, Theorem 10.4.3 and its "merely having one is as good as having one", Theorem 10.4.4 |
| HoTT Book label-to-number table | `HoTT/book` master, `main.labelnumbers.first-edition` | Mechanical confirmation of all thirteen numbers in section 2.2 |
| Kraus, Escardó, Coquand, Altenkirch, "Notions of Anonymous Existence in Martin-Löf Type Theory", LMCS 13(1), 2017 | arXiv:1610.03346, via `ar5iv.labs.arxiv.org/html/1610.03346`; sections 3, 4, 7.1 | `splitSup` (29), Lemma 12, Theorem 16, Theorem 17, Theorem 29, the global taboo |
| Matthews and Rathjen, "Constructing the Constructible Universe Constructively", APAL 175 (2024) 103392 | arXiv:2206.08283v3, via `arxiv.org/html/2206.08283`; abstract, sections 1 and 6 | The only constructive study of `L`, and its negative for CZF |
| Escardó, "Introduction to Univalent Foundations of Mathematics with Agda", section "Exiting truncations" | `cs.bham.ac.uk/~mhe/HoTT-UF-in-Agda-Lecture-Notes/HoTT-UF-Agda.html`, the `exit-∥∥` module region | `find-∥∥-existing-root`, `wconstant-endomap-gives-∥∥-choice-function` and its converse, `∥∥-recursion-set`: the whole route, in Agda |
| Jech, "Set Theory", 3rd millennium ed., ch. 13 | `_build/literature/jech13.txt:744-753`, `:1141-1144` | Lemma 13.19's "the <-least" encoding, Exercise 13.24's Skolem functions |
| Schindler and Zeman, "Fine structure" | `_build/literature/sz-full.txt:527-528`, `:697-705` | Theorem 1.15, the Σ1 Skolem function; "the <-least" in the canonical order |
| Devlin, "Constructibility", ch. II | through `dev/literature/devlin-II5.md`, and `_build/literature/dev2.txt:1340-1350`, `:1408-1423` | II.5.3's ψ, II.5.9's Σ1 least element |
| Cubical library, `Cubical/HITs/PropositionalTruncation/Properties.agda` | `/opt/homebrew/Cellar/agda/2.8.0-r3/share/agda/cubical/...:176-190`, `:225`, `:268`, `:270-274` | `rec→Set`, `trunc→Set≃`, `elim→Set`: the door of section 2.5 |
| Cubical library, `Cubical/Foundations/Function.agda` | same tree, `:105-110` | `2-Constant` and `2-Constant-isProp` |

### SKIMMED

| Source | Locator | Why only skimmed |
|---|---|---|
| Escardó, TypeTopology index | `martinescardo.github.io/TypeTopology/index.html` | The page lists module names without descriptions, so it could not be searched for the untruncation modules. The lecture notes gave the same content in readable form. |

### POINTER-ONLY

| Source | Locator | Why |
|---|---|---|
| Kraus, "The General Universal Property of the Propositional Truncation" | arXiv:1411.2682 | Named in the cubical library's own comment at `Properties.agda:179` as the source of `rec→Set`. Not fetched. The library's code is the artifact that matters here, and I read that. |
| Kraus, "Truncation Levels in Homotopy Type Theory" (thesis) | `nicolaikraus.github.io/docs/thesis_nicolai.pdf` | Surfaced by search. Superseded for this question by the LMCS paper, which I read. |
| Devlin, "Constructibility", Chapter I (1.7.1, 1.9.15) | not in `_build/literature/` | The digest records the citations; the chapter is not on disk and nothing in this task depends on it. |

### NOT READ, WITH WHY NOT (DD18 makes this the section that matters)

- **Kunen, "Set Theory: An Introduction to Independence Proofs".** WHY NOT: the
  brief asked for Jech OR Kunen, and Jech was already on disk as
  `_build/literature/jech13.txt` (BIBLIOGRAPHY entry 21). Fetching Kunen would
  have cost a paywall or a scan and would have added a third statement of the
  same universal guard. **Schindler and Zeman, also on disk, gave that third
  statement for free.** I judge the marginal value zero and record the
  decision here so the owner can overrule it.
- **Paulson's Isabelle/ZF `AC_in_L.thy` source.** WHY NOT:
  `dev/literature/formalizations-landscape.md:216-221` already quotes the
  theorem statement from the published library page. The question is whether
  classical logic FACES the truncation problem, and that is answered by the
  logic, not by the file.
- **The Flypitch sources.** WHY NOT: `dev/literature/formalizations.md:188-199`
  records that Flypitch builds no `L` at all. Nothing there can bear on a step
  inside `L`.
- **The HoTT Book's `exercise_solutions.tex`.** WHY NOT: fetched but not read.
  The exercise STATEMENT is what bears, and a community solution file is not a
  source I would cite for a ruling.
- **`dev/literature/fine-structure.md`, `j-hierarchy.md`,
  `rudimentary-functions.md`, `devlin-errata.md`, `geology.md`,
  `owner-notes-rud.md`, `digest.md`, `primary-sources.md`,
  `glossary-review-2026-08.md`, `terms-2026-08.md`.** WHY NOT: C-41. These were
  written for the RETIRED rud route. Their mathematics is about rud closure,
  the J-hierarchy and Devlin's errata. **None of them touches truncation, data
  against proposition, or witness selection**, which is what
  `dev/literature/devlin-II5.md:581-584` itself says of the same set. I read
  `BIBLIOGRAPHY.md` to find what was already fetched, and that was the value.
- **`dev/literature/formalizations-landscape.md` section 8's failed indexes.**
  WHY NOT re-run: the sweep is 13 days old and its absence wording is already
  index-bound. Re-running six library indexes was not this task's question.

### CANDIDATE, NOT PURSUED

- **de Jong, Kraus, Nordvall Forsberg, Xu, "Set-Theoretic and Type-Theoretic
  Ordinals Coincide"**, and Escardó's `Ordinals` development in TypeTopology.
  POINTER-ONLY, not fetched. WHY NOT: the question is whether a well-order
  untruncates an injection, and section 2.4's counterexample at order type
  `ω · 2` says the well-orders alone cannot. A deeper ordinal library would
  sharpen the constructive ordinal story, which is not what the ruling needs.
  **If the owner wants the ordinal side pressed, that is the next fetch.**

## 10. FOR THE ORCHESTRATOR

1. **The ruling does not have a literature answer, and now it has a literature
   CRITERION.** `InjData` holds for a family iff each member has a weakly
   constant endomap (Kraus et al., Theorem 16). That is what to attack or
   discharge, not "the truncation".
2. **Section 2.5 is the finding to act on.** `rec→Set` and `trunc→Set≃` are in
   the library the project already imports. They make J1's obligation exactly
   "a `2-Constant` map `Wat α → sq α`", necessary and sufficient. Send that to
   `[LJ-1.314]` or to a fresh probe. **It costs one file and it decides
   necessity at the eliminator level for good.**
3. **The sentence for `[LJ-1.314]`'s attack 1 is section 2.3's last paragraph.**
   The classical move is blocked not by the truncation but because the
   injection lives outside every well-ordered domain the tree has.
4. **No precedent exists.** Section 3.2. Whatever the owner rules, he rules
   first.
5. **The proposed digest is `agents/tasks/LJ-1-316/truncation-and-selection.md`.**
   It is written to land in `dev/literature/` unchanged if the orchestrator
   accepts it. I landed nothing (DD19).

## 11. CHECKS RUN

- `.venv/bin/python scripts/gate/lint-prose.py --check` on both files I wrote.
- MEASURED: no em dash in any file I wrote.
- No Agda invocation of any kind.
