# review-of-site-facts: the obligation is FALSE, and this file is the stop

**VERDICT: NO-GO.** `site-facts` is not delivered, and it is not
delivered because **it cannot be**. The first site fact, `fK`, is
refuted in the tree, at `agents/tasks/LJ-1-691/Probe691.agda:114-131`,
exit 0.

    fK-void : (w b K : Fin 2) → (ψs ψa : ...)
            → (the two Lset-defines hypotheses)
            → Facts.SiteFacts {2} w b K (∅ʟ ∷ ∅ʟ ∷ []) ψs ψa
            → Empty.⊥

The brief's own stop condition is met: the obligation is false at a
site the obligation allows, and this file says exactly why.

## THE STATEMENT THAT IS REFUTED

`agents/tasks/LJ-1-691/Probe691.agda:67-103`, the frame of `[LJ-1.681]`'s
`bnd-vs-unbnd`, copied verbatim:

    module Facts {n : ℕ} (w b K : Fin n) (γ : S ^ n)
      (ψs : Formula S (8 + n)) (ψa : Formula S (10 + n)) where
      fK = (f₀ : S) → ⟨ fst f₀ ∈ fst (lookup K γ) ⟩
      ...
      SiteFacts = fK × (domOut × (stepBwd × (stepFwd × (apxStepBwd × apxStepFwd))))

The frame is UNIVERSAL in the environment. The source frame is
`agents/tasks/LJ-1-681/Probe681.agda:56-57`, one anonymous module over
`{n} (w b K : Fin n) (γ : S ^ n) (ψs ψa)`. `bnd-vs-unbnd` takes the six
rows as hypotheses (Probe681.agda:67-95) and prices them as the cost of
the composition (Probe681.agda:12-15). Any fact this brief asks to be
built must hold at every allowed `(w, b, K, γ, ψs, ψa)`, and one
disallowed-at-nothing environment kills the universal term.

## WHY IT IS FALSE

**`fK` BOUNDS EVERY MEMBER OF THE CARRIER BY THE K SLOT.** `fK` says:
for every `f₀ : S`, `fst f₀ ∈ fst (lookup K γ)`. The carrier `S` has no
bound in its definition, so `fK` must hold even for the smallest coded
set the carrier contains, the coded empty set `∅ʟ`.

**THE COUNTEREXAMPLE ENVIRONMENT IS ALLOWED.** Take `n = 2` and
`γ = ∅ʟ ∷ ∅ʟ ∷ []`. Nothing in the frame forbids it: the frame carries
no hypothesis on `γ` other than the two `Lset-defines` rows, and those
constrain the `w` and `b` slots, not `K`. `∅ʟ` is an element of the
class carrier: `∅ʟ = ∅ , ∅∈L` at `src/L/Axioms/Basic.lagda.md:507-508`.

**AT THAT ENVIRONMENT THE K SLOT IS THE CODED EMPTY SET.** For both
values of `K : Fin 2`, `lookup K γ` is `∅ʟ` by definition, and
`fst ∅ʟ ≡ ∅`. So `fK` at `f₀ = ∅ʟ` asserts `⟨ ∅ ∈ ∅ ⟩`.

**`∅ ∈ ∅` IS DISCHARGED TO A CONTRADICTION BY LANDED THEORY.** The
refutation clause (`Probe691.agda:120-131`):

      h0 = ∈∈ₛ {a = ∅} {b = ∅} .fst (fst s ∅ʟ)
      ... Empty.rec (∅-empty ∅ h0)

`∈∈ₛ` converts the raw membership proof to the internal `∈ₛ` form
(`/opt/homebrew/Cellar/agda/2.8.0-r3/share/agda/cubical/Cubical/HITs/CumulativeHierarchy/Properties.agda:251`),
and `∅-empty` is the landed no-membership fact of the coded empty set
(`.../Constructions.agda:86-87`). This is the codebase's own idiom;
`numeralL-zero` uses the same two-term pattern at
`src/L/Axioms/Numerals.lagda.md:202-206`.

**THE Lset-defines CONTEXT SAVES IT NOT AT ALL.** `fK-void` carries both
hypotheses of the composition context, `IsOrd (fst (lookup b ...))` and
`fst (lookup w ...) ≡ Lset (fst (lookup b ...))`
(`Probe691.agda:116-117`), and neither is used in the body. They
constrain the `w` and `b` slots. The refutation reads the `K` slot only.

## WHAT THE NO-GO MEASURES, AND WHAT IT DOES NOT

Per law C-42, this refutation measures ONE site: the universal
`site-facts` frame at the all-`∅ʟ` environment. It says nothing about
how many other environments carry the same false shape. The count of
sites where `fK` does hold (for instance at the canonical bounded-graph
environment of the composition) is not measured here, and no cure is
priced against a number nobody has counted.

`[LJ-1.681]` already names the corrected direction: its own comment on
`fK` reads "the corrected statement is that this is the canonical
approximation, not an arbitrary one" (`Probe681.agda:68-69`), and the
header attributes the priced leaf rows to the `KFacts` wall "at the
class carrier" (`Probe681.agda:12-15`). The next brief should price the
composition against a CANONICALITY hypothesis in place of the
unbounded `fK`, not against `fK` as stated.

## COST FACTS FOR THE NEXT ATTEMPT

Two measured facts, each at its own site, neither transferred by
analogy:

1. **The refutation itself is cheap.** The full file, six site-fact
   rows and the refutation, typechecks in 2.50 s at 576 MiB under the
   wide caliber. `runs/p-1.out`.
2. **One spelling of the same proof is a heap wall.** Passing the
   membership proof to `∈∈ₛ .fst` through a `subst` redex in body
   position drives the checker past the 2.1 GiB wall in 80 to 103
   seconds (`runs/V5.out`, `runs/V5d.out`, `runs/V5b.out`). Passing the
   neutral `fst s ∅ʟ` from a `K`-split clause is fast
   (`runs/V5e.out`, 2.02 s). The next body at this site should keep
   the witness neutral, or price the `subst` spelling separately.

## WHAT I DID NOT DO

I did not build `site-facts`. I did not land anything in `src/`. I did
not postulate: `grep -c postulate agents/tasks/LJ-1-691/Probe691.agda`
returns 0, and the file carries `--safe`. I did not measure any site
other than the one named. Scratch probes are deleted; their measured
outputs stand in `agents/tasks/LJ-1-691/runs/`.
