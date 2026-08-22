# LJ-1.520 report: a Levy grade for the level graph

**VERDICT: GO.** The obligation is written and it typechecks.
`agents/tasks/LJ-1-520/Probe520.agda:171-172`, exit 0, `runs/full-t2.out`.

    levelFo-Σ₁ : {n : ℕ} (w b : Fin n) → Σ[ ψ ∈ Formula S n ] Σ₁ ψ

**W3 IS GO, ON THE FIRST GREEN RUN.** The existential of the graph accepts a
term as its bound. `agents/tasks/LJ-1-520/runs/W3.agda:69-70` and `:73-74`, exit 0.

**THE ONE SENTENCE FOR THE NEXT BRIEF.** The brief says the Levy grade is what
`[LJ-1.516]` could not get. **The tree already had one.**
`Σ₁-levelHood` is delivered at `src/L/BoundedSubset.lagda.md:145-146` and
`Σ₁-Σ₂` at `:858-859`, both green in `src/`, both without a consumer
(`agents/tasks/LJ-1-228/lj-1.228-report.md:36-37`, `:58-61`). **What was
missing is not the grade. It is a graded formula that leaves only the value and
the ordinal free and that discharges its own twelve tag site facts.** This task
delivers that. **The residue is the bound, and it is now the only one.**

## D-10, BEFORE ANY AGDA

The brief ordered this first, and it changed the task twice.

### Which constructors Σ₁ admits

`src/FOL/LevyHierarchy.lagda.md:73-75`:

    data Σ₁ {ℓc} {K : Type ℓc} : ∀ {n} → Formula K n → Type ℓc where
      σ-Δ₀ : ∀ {n} {φ : Formula K n} → Δ₀ φ → Σ₁ φ
      σ-∃  : ∀ {n} {φ : Formula K (suc n)} → Σ₁ φ → Σ₁ (∃̇ φ)

**Two constructors, and they permit exactly one shape: a prenex block of
unbounded existentials on a Δ₀ core.** `σ-∃` strips one `∃̇` from the front. No
constructor puts an `∃̇` under a connective or under a bounded quantifier. So a
Σ₁ formula is `∃̇ … ∃̇ (core)`, and the core must satisfy `Δ₀`.

**The brief's premise 5 is about `Δ₀` and not about `Σ₁`.** It cites
`src/FOL/LevyHierarchy.lagda.md:47`, which is the `Δ₀` declaration. `Δ₀` at
`:47-57` has ten constructors and none for `∃̇` or `∀̇`. That is correct. `Σ₁`
DOES admit an unbounded existential, one per `σ-∃`. The premise reads as though
no unbounded quantifier is admitted anywhere. **The distinction is the whole
task**, so I state it rather than pass it.

### Whether the tree can express `v = Lset γ` with a bounded existential

**YES, and the tree already writes the matrix.** `src/L/Condensation.lagda.md`
carries the bounded restatement of the whole sequence chapter:

| object | at | what it bounds |
|---|---|---|
| `extAtB` | `:103-105` | the two-way extension frame, second half bounded by `K` |
| `Δ₀-extAtB` | `:107-109` | its `Δ₀` witness |
| `domB` | `:1749-1755` | `domAt`, both directions bounded by `K` |
| `StepB.stepBndAt` | `:2417-2418` | `StepAt` |
| `ApproxB.approxBndAt` | `:2471-2477` | `ApproxAt`, the two unbounded universals bounded by `K` |
| `GraphB.graphBndAt` | `:2492-2493` | `LsetGraphAt`, the one existential bounded by `K` |
| `Δ₀-graphBndAt` | `:2495-2497` | its `Δ₀` witness |

`GraphB.graphBndAt = ∃̇∈ (var K) (A.approxBndAt ∧̇ S.stepBndAt)`. **That is the
briefed object, and it was in `src/` before this task started.**

**So the Levy hierarchy as delivered CAN state the source's formula, and this
task does not stop.** No constructor is missing. The D-10 stop the brief
prepared does not fire.

### The second thing D-10 found, and it corrects the brief

The brief says the transport machinery has no formula it accepts. **The tree
already applies `GraphB` and already builds a Σ₁ certificate over it.**

    src/L/BoundedSubset.lagda.md:81      module G = GraphB {m} …
    src/L/BoundedSubset.lagda.md:142-143 levelHoodΣ₁ = ∃̇ levelHoodB
    src/L/BoundedSubset.lagda.md:145-146 Σ₁-levelHood = σ-∃ (σ-Δ₀ Δ₀-levelHoodB)
    src/L/BoundedSubset.lagda.md:855-859 Σ₂ and Σ₁-Σ₂ at arity 1

`src/L/Condensation.lagda.md:269-273` carries the same pattern for the clause
matrix: `existCertAt C T B N = ∃̇ (Clause.existBndAt C T B N)` with
`Σ₁-cert = σ-∃ (σ-Δ₀ …)`. **The shape this task was asked to invent is the
tree's own delivered shape.** I did not invent it. I instantiated it at the
briefed type and I closed what it leaves open.

`[LJ-1.228]` measured that both level-hood certificates are unconsumed
(`agents/tasks/LJ-1-228/lj-1.228-report.md:59-61`). **They are not consumed
because of what they leave free, and that is the finding this task adds.**

## W8, THE SOURCE AND ITS ERRATA

**I read `dev/literature/devlin-II5.md` and checked it against
`dev/literature/devlin-errata.md` before relying on either.**

What I take from the source, quoted at its line:

- `dev/literature/devlin-II5.md:217`: `Strength: the existential over z is UNBOUNDED at the ambient level.`
- `dev/literature/devlin-II5.md:222`: `γ < α. Strength: the Σ₁ form is "witnessed inside the carrier", not`

**The second is the one the brief did not quote and it is the load-bearing
one.** The source's Σ₁ form is witnessed INSIDE the carrier. `:220-223` says the
forward half needs the witnessing `z` to live inside `L_α`, and names 2.6(ii)
as the fact that supplies it. **So the source does not close its bound by a
bare existential over the ambient universe. It relies on the carrier being a
limit level.**

The errata bear on this and the brief was right to order the check.

- `dev/literature/devlin-errata.md:133`: `- Uniformity claim (Devlin p. 65): the claim that Sat is uniformly Δ^M_1 for`
  The claim is FALSE as printed. `:137-138` gives the fix: it holds for
  S-amenable sets, that is amenable plus closure under `S`. **The correction is
  a CLOSURE condition on the carrier**, which is the same shape as the residue
  this task measures.
- `dev/literature/devlin-errata.md:139`: `- Claim on p. 66: "The discussion on page 66 seems to suggest that any`
  The warning is that a Σ₁ statement of one system is NOT automatically Σ₁ over
  every `L_λ` for limit `λ > ω`. **So "at a limit" does not by itself grant the
  grade.** I do not use p. 66 for anything.

**Neither erratum refutes what I take.** I take only the two `devlin-II5.md`
lines above, and both are about the shape of the witness rather than about
Sat's uniformity in BS. **`[LJ-1.519]` reads the same source for a different
statement. I did not read its work and I assume nothing from it.**

## W3, THE WIDEST UNMEASURED TERM

The brief named it: the bound on the existential. **I wrote it first, alone, in
its own file, and typechecked it before `Probe520.agda` existed.**

`agents/tasks/LJ-1-520/runs/W3.agda:69-70` and `:73-74`:

    w3 : Formula CS.S m
    w3 = G.graphBndAt

    w3-Δ₀ : Δ₀ w3
    w3-Δ₀ = G.Δ₀-graphBndAt …

**IT BOUNDS.** The first run failed on a missing `_+_` import and nothing else.
The second run was green. **No mathematics resisted.**

The file is generic in the arity `m` and in every slot. It is not about a
stage, and `LsetGraphAt` is not named in it.

**What W3 measured that the brief did not know:** the arity arithmetic of the
two leaf environments. `StepB` puts its leaf at `v' ∷ c' ∷ x ∷ d ∷ w ∷ c ∷ z ∷ γ'`
(`src/L/Condensation.lagda.md:2394-2397`). The graph's own step sits one binder
above the ambient environment and the step under the approximation sits three,
so an ambient slot travels **five** binders at one leaf and **seven** at the
other. That is `sh5` and `sh7` at `runs/W3.agda:43-47`. **A wrong shift is a
type error and not a wrong formula**, so the file is the proof of the
arithmetic.

## WHAT WAS BUILT

### The obligation

`agents/tasks/LJ-1-520/Probe520.agda:171-172`:

    levelFo-Σ₁ : {n : ℕ} (w b : Fin n) → Σ[ ψ ∈ Formula S n ] Σ₁ ψ
    levelFo-Σ₁ w b = Slots.levelFo w b , Slots.Σ₁-levelFo w b

**The type is the brief's, character for character.**

### The matrix, generic in every slot

`Probe520.agda:53-128` is `module Matrix`, at a generic arity `m` and generic
slots `w b K N0 … N11`. It builds:

| term | at | what it says |
|---|---|---|
| `ψs`, `ψa` | `:65`, `:71` | the bounded code-set description at the two leaves |
| `G.graphBndAt` | `:77` | the bounded graph, `∃̇∈ (var K) (…)` |
| `transK` | `:95` | `K` is transitive |
| `pins` | `:108` | the twelve slots hold the twelve numerals |
| `matrix` | `:124` | `transK ∧̇ (pins ∧̇ G.graphBndAt)` |
| `Δ₀-matrix` | `:127-128` | its `Δ₀` witness |

### The prenex block

`Probe520.agda:137-167` binds thirteen variables and grades the result:

    levelFo    = ∃̇ (∃̇ (… thirteen …  Mx.matrix …))
    Σ₁-levelFo = σ-∃ (σ-∃ (… thirteen … (σ-Δ₀ Mx.Δ₀-matrix) …))

The outermost binds the bound `K`. The twelve tag binders follow, `N11` first,
so `N_k` lands at slot `k`.

### Three things this delivers that the tree did not have

**FIRST, THE TWELVE TAG SITE FACTS ARE NOW CONSEQUENCES OF THE FORMULA.**
The bounded rows take the tag as a slot and ask the consumer for a hypothesis:
`tagEq : fst (lookup N γ) ≡ fst (numeralL 0)`
(`src/L/Condensation.lagda.md:4413`), and the two term tags likewise,
`t0eq` and `t1eq` at `:4431-4432`. **`pins` says the same thing in the object
language**, in two clauses that are both `Δ₀`:

- `∀̇∈ (var N0) ⊥̇`, so `N0` has no member. `δ-∀∈ δ-⊥`.
- `sucAtL N_k N_{k+1}` eleven times, and `sucAtL i j` says
  `j ≡ sucV i` (`src/L/Coding/Model.lagda.md:1398-1399`). `Δ₀-sucAtL` is
  delivered at `src/L/Condensation.lagda.md:94-95`.

The numerals are von Neumann (`# 0 = ∅`, `# (suc n) = sucV (# n)`, cubical
`Cubical/HITs/CumulativeHierarchy/Constructions.agda:163-165`), so the two
clauses pin every slot up to extensionality. The twelve machine rows carry the
numerals 0 through 11 in the order `SatGraphB.twelveB` lists them
(`src/L/Coding/Model.lagda.md:1788`, `:1791`, `:1118`, `:1121`, `:1276`,
`:1172`, `:1279`, `:1282`, `:1615`, `:1618`, `:1947`, `:1950`).

**SECOND, THE TWO TERM TAGS NEED NO SLOT OF THEIR OWN.** `t0eq` and `t1eq`
(`src/L/Condensation.lagda.md:4431-4432`) ask for the numerals 0 and 1, which
are what `N0` and `N1` already hold. So the fourteen tag slots of `DefBodyB`
reduce to twelve binders. `Probe520.agda:65-75` passes `N0` and `N1` again in
the `t0` and `t1` positions. **The tree's own `LevelHood` gives the two leaves
two separate families of fourteen slots** (`src/L/BoundedSubset.lagda.md:75-76`,
twenty-eight slots in all). **The same twelve serve both leaves**, because both
leaves read the same twelve rows.

**THIRD, THE FORMULA CARRIES NO CONSTANT.** `runs/CountCheck.agda:18-19`:

    no-constant : {n : ℕ} (w b : Fin n) → countFo (fst (levelFo-Σ₁ w b)) ≡ 0
    no-constant w b = refl

Exit 0, `runs/count-0.out`. **`refl` proves it**, so `EraseTransfer`, whose one
hypothesis is `countFo φ ≡ 0` (`src/L/Condensation.lagda.md:287`), is open at
this formula. `[LJ-1.514]` measured `countFo (LsetGraphAt w b) = 664`
(`agents/tasks/LJ-1-514/lj-1.514-report.md:30`). **The pins are why the count
is zero: a numeral written as a constant would have cost 664 again, and a
numeral pinned by a quantifier costs nothing.** I do not claim this is new
to the tree: `Clause.existBndAt` is constant-free too and proves it by `refl`
(`src/L/Condensation.lagda.md:365`).

### The contrast, rerun in this file

`Probe520.agda:202-204` reruns `[LJ-1.516]`'s refutation of the grade at the
delivered formula, so the refuted term and the graded term stand in one run:

    no-Σ₁-graph : {n : ℕ} (w b : Fin n) → Σ₁ (LsetGraphAt w b) → ⊥* {ℓ}

Agda checks it by absurd pattern. **`LsetGraphAt` still has no Σ₁ witness, and
`levelFo` has one.**

## WHAT THE GRADE COSTS

**Every hypothesis the graded formula needs that `LsetGraphAt` does not.** Each
row says where the tree states it and whether the tree delivers it.

| hypothesis | stated at | delivered |
|---|---|---|
| the twelve tag slots hold the numerals 0 to 11 | `src/L/Condensation.lagda.md:4413` | **NO LONGER NEEDED.** `pins` says it, `Probe520.agda:108` |
| the two term tags hold 0 and 1 | `src/L/Condensation.lagda.md:4431-4432` | **NO LONGER NEEDED.** same |
| the numerals lie in `K` | `src/L/Condensation.lagda.md:4414`, `:4434` | NOT said by the formula. A hypothesis on `K` |
| `K` is closed under pairing | `src/L/Condensation.lagda.md:4417-4418` | NOT said. A hypothesis on `K` |
| the codes and recorded values of a shaped code lie in `K` | `src/L/Condensation.lagda.md:4422-4430` | NOT said. A hypothesis on `K` |
| the environment sets and their members lie in `K` | `src/L/Condensation.lagda.md:4435-4445` | NOT said. A hypothesis on `K` |
| the term values lie in `K` | `src/L/Condensation.lagda.md:4446-4457` | NOT said. A hypothesis on `K` |
| a satisfier reached through a member of `K` lies in `K` | `src/L/Condensation.lagda.md:2517` | **SAID.** `transK`, `Probe520.agda:95` |
| **`K` is closed under the definable powerset of its members** | nowhere in the tree | **NOT SAID AND NOT SAYABLE.** See below |

**THE LIMIT IS ONE OF THEM.** The brief expected it and it is. The last row is
the limit hypothesis in the tree's own vocabulary: `leafB` describes `d` as the
definable powerset of `w`, and its second half is bounded by `K`
(`src/L/Condensation.lagda.md:2398-2402`). For that half to say what the
unbounded `extAt` says, `K` must already hold every definable subset of every
member of `K` that has a code and an environment in `K`. **A transitive `K`
does not give this. A limit level does.**

**AND IT CANNOT BE ADDED TO THE MATRIX.** To say "`K` holds the definable
subsets of its members" needs a quantifier over those subsets, and the only
term available to bound it is `K` itself. That is circular. **So the closure
cannot be written `Δ₀` with `K` as the sole bound**, and no amount of work on
this formula will change that. **I did not build a term of the negation and I
do not claim one.** What I claim is that the four `Δ₀` constructors for a
bounded quantifier (`src/FOL/LevyHierarchy.lagda.md:56-57`) take a `Term`, and
a `Term` is a variable or a constant (`src/FOL/Syntax.lagda.md:42-44`), so the
bound must already be named.

**WHAT `transK` BUYS, AND WHAT IT DOES NOT.** I argue this from the definitions
and I did not machine-check it, because proving it is the transport and the
brief forbids the transport.

- The step's second half is `∀̇∈ K (witB ⇒̇ z ∈̇ v)`
  (`src/L/Condensation.lagda.md:2418`, `:104-105`). `witB`'s last conjunct is
  `z ∈̇ d` with `d` bound by `∃̇∈ (var K)` (`:2408`, `:2414`). So a satisfier
  `z` lies in a member of `K`. **With `transK` it lies in `K`**, and the
  bounded half says what the unbounded half says.
- `domB`'s second half needs the value at an argument to lie in `K`
  (`:1754-1755`). The approximation `f` lies in `K` by the graph's own bounded
  existential (`:2493`). A recorded pair lies in `f`, and its two components
  lie two levels down. **Transitivity reaches them.**
- **The leaf is the one it does not reach**, for the reason above.

## THE EQUIVALENCE, AS A TYPE

The brief requires this whether or not it is proved. **It is not proved. Both
statements are types and neither has a term**, because the proof is the
transport and AD12 gives this brief one obligation.

`Probe520.agda:183-190`, the semantic reading, in the shape the tree uses for
the delivered graph (`src/L/Condensation.lagda.md:422-431`):

    SaysLevel : {n : ℕ} (w b : Fin n) (γ : S ^ n) → Type (ℓ-suc ℓ)
    SaysLevel w b γ =
        ( ⟨ γ ⊨ fst (levelFo-Σ₁ w b) ⟩ → IsOrd (fst (lookup b γ))
          → fst (lookup w γ) ≡ Lset (fst (lookup b γ)) )
      × ( IsOrd (fst (lookup b γ)) → fst (lookup w γ) ≡ Lset (fst (lookup b γ))
          → ⟨ γ ⊨ fst (levelFo-Σ₁ w b) ⟩ )

`Probe520.agda:192-196`, the syntactic reading:

    SameAsGraph : {n : ℕ} (w b : Fin n) (γ : S ^ n) → Type (ℓ-suc ℓ)
    SameAsGraph w b γ =
        ( ⟨ γ ⊨ fst (levelFo-Σ₁ w b) ⟩ → ⟨ γ ⊨ LsetGraphAt w b ⟩ )
      × ( ⟨ γ ⊨ LsetGraphAt w b ⟩ → ⟨ γ ⊨ fst (levelFo-Σ₁ w b) ⟩ )

**BOTH TYPES FORM. NEITHER HALF IS EQUALLY PRICED, AND THE NEXT BRIEF MUST
KNOW WHICH IS WHICH.**

- **The second half of each is the cheap one.** From the true graph, pick a `K`
  that is adequate. Every bounded quantifier is then a weakening of an
  unbounded one, and `extAt→extAtB` (`src/L/Condensation.lagda.md:2524-2530`)
  needs no site fact at all. **What it needs is that an adequate `K` EXISTS in
  the model, which is the limit hypothesis and nothing more.**
- **The first half of each is the expensive one.** It consumes a `K` the
  formula produced, and that `K` is only transitive. `extAtB→extAt`
  (`:2514-2518`) needs the satisfiers-in-`K` fact, and at the leaf `transK`
  does not supply it. **So the first half is NOT free, and it is the half the
  grade is spent on.**

**WHY THAT MATTERS FOR THE USE.** `σ₁-up` carries satisfaction from the inner
model outward (`src/FOL/Absoluteness.lagda.md:182-183`), and
`transports-Σ₁` rides it (`agents/tasks/LJ-1-516/Probe516.agda:130-135`). A
consumer gets `levelFo` true outside and then needs the FIRST half to conclude
`w ≡ Lset b`. **The expensive half is exactly the one the transport needs.**

**AND THE LITERATURE NAMES THE CURE.**
`dev/literature/level-formula-slot-roles.md:60`:

    Devlin's `∃w` carries the conjunct `K(w,u)`, "which says `w = K(u)`"

The scan carries it at `_build/literature/dev2.txt:611`, which prints
`Let K(w, u) be the LST formula which says "w = K(ύf\ namely:` under OCR. **The
orthodox bound is DETERMINED by a conjunct, not chosen by a bare existential.**
The digest states at `:124` that it `does not settle whether an undetermined
bound is sound (section 2.3).` **This task settles it in one direction: an
undetermined bound costs the first half of the equivalence.** The digest also
records at `:55` that `**No source uses two independent bounds.** A formula with two independent bound`
**This task uses one bound, so it agrees with every source in the digest's
table.**

## WHAT THE BRIEFED TYPE FORCES, AND WHY IT IS WORTH SAYING

`Σ[ ψ ∈ Formula S n ] Σ₁ ψ` with only `w` and `b` in hand **leaves no slot for
a bound**. So the type forces the bound to be closed, and closing it by a bare
existential is the only closure available without a determining conjunct.

**The tree's `Σ₁-levelHood` avoids the cost by leaving `K` FREE**
(`src/L/BoundedSubset.lagda.md:142-146`, the environment is `v ∷ γ ∷ K ∷ δ` per
the comment at `:69-73`). A consumer then supplies an adequate `K` and the site
facts hold by hypothesis. **That is honest and it is why the tree wrote it that
way.** It is also why it has no consumer: the twenty-eight tag slots are still
free beside `K`.

`LevelHood0.Σ₂` closes `K` and the value at arity 1
(`src/L/BoundedSubset.lagda.md:855-859`), and its tag slots are then `Fin 5` and
`Fin 7` pointing into an environment of four. **Twelve distinct numerals cannot
live in four slots**, so the closed form there cannot have all twelve site facts
at once. **The pins are what makes a closed form non-degenerate**, and that is
this task's contribution to the shape.

## CORRECTIONS TO THE BRIEF

1. **Premise 5 is right about `Δ₀` and misleading about the Levy hierarchy.**
   `src/FOL/LevyHierarchy.lagda.md:47` is the `Δ₀` declaration. `Σ₁` has an
   unbounded-existential constructor at `:75`. The premise as written would
   have stopped the task at D-10.
2. **"THE TRANSPORT MACHINERY IS COMPLETE AND UNUSED. What is missing is a
   formula they accept" is not accurate.** `src/L/BoundedSubset.lagda.md:145-146`
   is a delivered Σ₁ certificate at the class carrier, green in `src/`, and
   `[LJ-1.228]` recorded it a long time ago
   (`agents/tasks/LJ-1-228/lj-1.228-report.md:36`). **The premise's substance
   survives**: no graded formula had the briefed free-slot discipline. The
   sentence overstates it.
3. **"Nine dispatches transported the wrong object" is not what I measured.**
   I did not audit the nine. What I measured is that the right object exists in
   two places in `src/` and is unconsumed in both.
4. **Premises 1, 2, 3, 4, 6, 7, 8 and 10 through 12 held as written.** I
   checked each at its cited line. Premise 9 I did not use.
5. **The brief's W3 estimate of "about 20 lines and under 35 seconds" came in
   at 43 non-blank non-comment lines and 2.43 s.** The line estimate is low
   because the two leaf shifts and the two leaf contents are four declarations
   that cannot be shortened.

## C-42, THE SWEEP

C-42 (`dev/LESSONS.md:3752`) applies to a refutation. **This task refutes
nothing.** It reruns one refutation that `[LJ-1.516]` measured and it adds no
new one, so there is no new shape to sweep.

**What I did sweep is the opposite question: how many places in `src/` already
carry the bounded matrix.** The count is **two consumers of `GraphB` and one
definition**, machine-listed by `grep -rn "GraphB" src/`:

| site | verdict |
|---|---|
| `src/L/Condensation.lagda.md:2486` | the definition |
| `src/L/BoundedSubset.lagda.md:81` | the one consumer in `src/` |
| `agents/tasks/LJ-1-520/runs/W3.agda:64`, `Probe520.agda:77` | this task |

**`ApproxB` and `StepB` have no consumer outside `GraphB` and `StepAtB`.**
Same method.

## W2, THE GENERIC CARRIER

**The brief did not state W2 and I answer it.** Nothing here is written twice.

`module Matrix` (`Probe520.agda:53`) is stated at a generic arity `m` and at
generic slots. `module Slots` (`:137`) is its one instantiation, and it adds
only the thirteen binders and the slot names. **The two leaf contents `ψs` and
`ψa` are the same `DefBodyB` at two arities**, not two hand-written formulas.
**The twelve numerals serve both leaves**, which is where the tree writes
twenty-eight slots and this task writes twelve.

`runs/W3.agda` repeats the two leaf declarations, and that is deliberate: W3
had to typecheck ALONE, before `Probe520.agda` existed, and a probe may not
import a probe for that purpose. **The repeat is four declarations and it buys
the isolated measurement the brief ordered.**

**No deadline forced a fixed form.**

## W4, THE RETIREMENT CLAUSE

Not applicable. No module was retired and nothing under `src/` changed.

**One archive note, and it is not a defect.** `archive/src/2026-08-09-rud-route/`
holds a whole retired route including `L/LevelFormula.lagda.md` and
`L/Rud/LevelSigma.lagda.md`. Those two modules have no row in `dev/ARCHIVE.md`,
because the route is archived as a snapshot with its own `README.md` and its own
patch rather than module by module. **That is a different archival form and not
a missing row.** `archive/src/2026-08-09-rud-route/README.md:1` states it.

## PRICE

One Agda process per run, `GHCRTS="-A64m -I0 -M8g"`, the wide caliber, set on
the pane by the program and untouched. **No heap wall. No rerun of a walled
run.** Three forced rechecks each: the module's build output is removed before
every timed run.

| measurement | median wall | median peak RSS | basis |
|---|---|---|---|
| W3 alone | 2.43 s | 512,409,600 bytes | `runs/w3-t1.time`, `runs/w3-t2.time`, `runs/w3-t3.time` |
| full file | 2.55 s | 639,008,768 bytes | `runs/full-t1.time`, `runs/full-t2.time`, `runs/full-t3.time` |
| constant count | 2.71 s | 553,271,296 bytes | `runs/count-0.time`, ONE run and not three |

**The full file is 0.12 s above W3 alone.** The obligation, the thirteen
binders, the pins, the two equivalence types and the rerun refutation together
cost about a tenth of a second over the bounded matrix. **The matrix is the
whole price**, and the matrix is `src/`'s.

**The task cost four failing runs in total.** One missing `_+_` import in W3,
two parenthesis miscounts in the hand-written quantifier stacks, and one shell
error from a stale working directory. **The two miscounts are a method note:
write a thirteen-deep constructor stack with a generator, not by hand.** I
generated both stacks after the second failure and neither failed again.

## THE ESTIMATE AGAINST THE MEASUREMENT

| quantity | brief | measured |
|---|---|---|
| probe, non-blank non-comment | about 170 | 114 |
| obligation block, non-blank non-comment | about 45 | 29 |
| W3, non-blank non-comment | about 20 | 43 |
| W3, wall | under 35 s | 2.43 s |

**The probe came in at two thirds of the estimate**, because `GraphB` and
`Δ₀-graphBndAt` were already written and this task cites them rather than
rebuilding them. **The brief funded a build and paid for a citation.**

## RATIO BAR

The bar is 0.0123 seconds per in-fence line and its divisor is the in-fence line
count of this task's write scope, counted the ledger's way. **This task's write
scope holds no `.lagda.md` master and no ` ```agda ` fence, so the divisor is 0
and the bar cannot fire.** The task landed nothing in `src/`, as the brief
required.

## ARCHIVE USED

Every CANDIDATE the block named is answered.

- **`archive/dev/LJ-dispatch-index.md`. READ AND USED.** `:242`:
  `| LJ-1.166 | Gate K(u), the SUPPLY that six gates never priced | GO: 88 LINES, 2.69 s, BOUND FITS | Devlin's engine transfers. Three of four closure classes were proved and no gate cited them |`
  **This row is the reason I did not treat the bound as a new object.**
  `[LJ-1.166]` priced Devlin's `K(u)` at 88 lines and found the bound fits, and
  it records that three of four closure classes were proved. **Those closure
  classes are the rows of my "WHAT THE GRADE COSTS" table that `transK` does
  not reach**, so the cure has a measured price and it is not this task's 170
  lines.
- **`archive/dev/JOURNAL.md`. READ AND USED.** `:809`:
  `missing `Δ₀` cure**, because the tree already carries `Δ₀-extAtB`,`
  This is the passage that says the tree spends absoluteness on BOUNDED
  rewrites rather than on the original formulas. It is what sent me to
  `src/L/Condensation.lagda.md:103-109` and from there to `GraphB`. Also
  `:1076`: `K(u) or its coding analogue」against「the sixteen op-graphs」.`
  **"or its coding analogue" is the tree's own name for what `K` is here.**
- **`archive/dev/JOURNAL-archived.md`. READ, USED LIGHTLY.** `:732`:
  `revival is to be kept alive: a D-1 probe of the Σ₁ rewriting of one DefAt`
  It records that a Σ₁ rewriting of `DefAt` was kept alive as a live option.
  **The tree since built it as `DefBodyB`**, which is what this task consumes.
  I claim nothing from the line beyond that agreement.
- **`archive/dev/DD-archived.md`. NOT USED, DECLINED.** `:1`:
  `# THE `DD` RULING SERIES, archived in full 2026-08-18`
  It is the archived ruling series. This task proposes no rule and cites no
  `DD` row.
- **`archive/dev/ORCHESTRATION.md`. NOT USED, DECLINED.** `:1`:
  `# ORCHESTRATION: the orchestrator's operating rules`
  It is the archived orchestration document. This task is one coder dispatch
  and it changes no operating rule.

**AND ONE THE BLOCK DID NOT NAME, WHICH I FOUND AND READ.**
`archive/src/2026-08-09-rud-route/L/LevelFormula.lagda.md`. **READ, USED AS
EVIDENCE ONLY.** Its `limIn` and `limOut` (`:168-178`) are unbounded `∀̇`
under a carrier `⟪ u ⟫` that is itself a level. **So the retired route made the
CARRIER the bound and left no bound slot at all.** That is a third shape beside
the tree's free bound and this task's closed bound, and it agrees with
`dev/literature/level-formula-slot-roles.md:55` that no source leaves a bound
free. `archive/src/2026-08-09-rud-route/README.md:1` is its provenance:
`# The rud route's `src/`, archived 2026-08-09`

## LITERATURE USED

Every CANDIDATE the block named is answered.

- **`dev/literature/devlin-II5.md`. READ AND USED.** `:217`:
  `   Strength: the existential over z is UNBOUNDED at the ambient level.`
  and `:222`:
  `   γ < α. Strength: the Σ₁ form is "witnessed inside the carrier", not`
  The first is the brief's quotation and it is correct. **The second is the one
  the brief did not quote**, and it is what tells me the source's bound is the
  carrier rather than a chosen set.
- **`dev/literature/level-formula-slot-roles.md`. READ AND USED, HEAVILY.**
  `:60`: `Devlin's `∃w` carries the conjunct `K(w,u)`, "which says `w = K(u)`"`
  and `:55`: `**No source uses two independent bounds.** A formula with two independent bound`
  and `:124`: `2. It does not settle whether an undetermined bound is sound (section 2.3).`
  **This digest names the exact residue this task measured, and says it did not
  settle whether it matters. This task's "WHAT THE GRADE COSTS" section is the
  answer to that open question.**
- **`dev/literature/devlin-errata.md`. READ AND USED.** Not a CANDIDATE, and
  W8 required it. `:133` and `:139`, quoted in the W8 section above.
- **`dev/literature/truncation-and-selection.md`. READ, NOT USED.** `:43`:
  `same move explicit because he must show the canonical well-order is Σ₁:`
  It confirms that the literature works this leg at Σ₁ rather than at Δ₀, which
  agrees with what this task built. **It settles nothing this task measured, so
  I claim nothing from it beyond agreement.**
- **`dev/literature/digest.md`. READ, NOT USED.** `:45`:
  `  limit α (SZ pp. 9-10, equation I.1). Condensation is at the Sigma-1`
  It places condensation at the Σ₁ level in Schindler and Zeman. **That is the
  same grade this task delivered, from a different source.** It gives no slot
  arithmetic and no bound, so nothing here rests on it.
- **`dev/literature/terms-2026-08.md`. READ, NOT USED, AND IT CARRIES A STALE
  PATH.** `:473`:
  `object-language atoms under a bounded existential (`src/L/LevelFormula.lagda.md:173`).`
  **`src/L/LevelFormula.lagda.md` does not exist.** The file is at
  `archive/src/2026-08-09-rud-route/L/LevelFormula.lagda.md`. `:472` names
  `src/L/PairAtoms.lagda.md:11-14` and `:476` names
  `src/L/Rud/LevelSigma.lagda.md:146`; both are archived at the same place.
  **Three dead paths in a live document. I did not repair them: the file is
  outside this task's write scope.**

## WHAT THE STATEMENT COST, WHAT RESISTED, WHAT I WEAKENED

- **What it cost.** 114 non-blank non-comment lines in the probe, 43 in W3, 9
  in the count check. 2.55 s median for the full recheck. Four failing runs.
- **What resisted.** **Nothing mathematical, and that is the finding.** Three
  of the four failures were clerical: a missing import and two hand-counted
  parenthesis stacks. The fourth was a shell error. **The arity arithmetic of
  the two leaves is the only thing that needed thought, and W3 settled it in
  one run.** The bounded matrix accepted the thirteen binders without a single
  type error.
- **What I had to weaken.** **The bound, and the briefed type forced it.**
  Closing `K` by a bare existential loses the first half of the equivalence,
  and the tree's own `Σ₁-levelHood` keeps that half by leaving `K` free. **I
  did not hide this and I did not weaken the CONTENT to buy the grade:** the
  matrix is the tree's bounded graph unchanged, plus two conjuncts that only
  make it stronger.
- **What I could not close.** The equivalence. Both halves are types with no
  term, and the transport that would give them terms is another task's
  obligation.

## WHAT THE NEXT BRIEF NEEDS

1. **DO NOT ORDER A Σ₁ GRADE FOR THE LEVEL AGAIN.** Three now exist:
   `src/L/BoundedSubset.lagda.md:145-146`, `:858-859`, and
   `agents/tasks/LJ-1-520/Probe520.agda:171-172`. **The grade is not the
   residue.**
2. **THE RESIDUE IS THE BOUND, AND IT HAS TWO POSSIBLE CURES. NAME ONE BEFORE
   WRITING THE BRIEF.**
   - **The determined bound.** Add a conjunct that says `K` IS the canonical
     bound, in Devlin's shape `K(w,u)`
     (`dev/literature/level-formula-slot-roles.md:60`). `[LJ-1.166]` priced
     that engine at 88 lines and found the bound fits
     (`archive/dev/LJ-dispatch-index.md:242`). **That price is for Devlin's
     `K(u)`, not for the coding analogue, and it must be re-measured here
     (Boundary: a measured cure does not transfer by analogy).**
   - **The free bound.** Keep `K` a slot, as `src/L/BoundedSubset.lagda.md:74-146`
     already does, and give the consumer the site facts. **Then the briefed
     type is the wrong type**, and the right one leaves three slots free.
3. **THE TWELVE TAG SITE FACTS ARE PAID AND THEY STAY PAID.** Any brief that
   uses `pins` (`Probe520.agda:108`) inherits `tagEq`, `t0eq` and `t1eq`
   (`src/L/Condensation.lagda.md:4413`, `:4431-4432`) for free. **Do not order
   them as hypotheses again.**
4. **THE FOURTEEN TAG SLOTS ARE TWELVE.** `t0` and `t1` hold the numerals 0 and
   1, which `N0` and `N1` already hold. `src/L/BoundedSubset.lagda.md:75-76`
   carries twenty-eight where twelve suffice. **That is a simplification
   available in `src/` today and this task did not take it, because it lands
   nothing in `src/`.**
5. **`GraphB` HAS ONE CONSUMER IN `src/` AND IT IS UNCONSUMED ITSELF.**
   `src/L/BoundedSubset.lagda.md:81` feeds `LevelHood`, and `[LJ-1.228]`
   measured that `LevelHood0` has no consumer
   (`agents/tasks/LJ-1-228/lj-1.228-report.md:59-61`). **A brief that wants the
   transport should ask why the delivered certificate was never spent, before
   it builds a fourth one.**
6. **THE FIRST HALF OF THE EQUIVALENCE IS THE HALF THE TRANSPORT NEEDS.**
   `σ₁-up` (`src/FOL/Absoluteness.lagda.md:182-183`) carries satisfaction
   outward, and a consumer then needs `levelFo ⇒ w ≡ Lset b` in the ambient.
   **Do not order the cheap half and call the leg closed.**
7. **`countFo (fst (levelFo-Σ₁ w b)) ≡ 0` BY `refl`** (`runs/CountCheck.agda:18-19`).
   The erase route (`src/L/Condensation.lagda.md:287-308`) is open at this
   formula at the cost of one citation.

## FILES

Everything is inside the task's write scope. **Nothing under `src/` changed. I
did not commit and I did not push.**

| file | state |
|---|---|
| `agents/tasks/LJ-1-520/Probe520.agda` | new, green, exit 0 |
| `agents/tasks/LJ-1-520/lj-1.520-report.md` | new, this file |
| `agents/tasks/LJ-1-520/runs/W3.agda` | new, green, the W3 measurement |
| `agents/tasks/LJ-1-520/runs/CountCheck.agda` | new, green, the constant count |
| `agents/tasks/LJ-1-520/runs/*.out`, `*.time` | new, the runs |

**`agents/tasks/LJ-1-520/review-of-levelFo-sigma1.md` IS NOT WRITTEN.** It is
in the write scope and it is the way a coder states a NO-GO. **This task is a
GO**, so the file would misreport the return.

`make check` was not run: it is the gate before a commit and this task commits
nothing. The three gates that bear on the files I wrote were run and are clean:
`scripts/gate/check-probes.py`, `scripts/gate/lint-agda.py` and
`scripts/gate/lint-prose.py`, all exit 0.
