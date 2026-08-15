# LJ-1.321 report: is there a `2-Constant` map `Wat α → sq α`?

## 0. LEAD

**NARROWED.**

**The naive map is REFUTED by a term. The canonical injection WALLS at the
limit non-initial ordinal. And the search narrowed to an obligation of a
NEW SHAPE that is strictly easier than the one the ruling named.**

Four things stand, all typechecked in
`agents/tasks/LJ-1-321/Door.agda`, exit 0, 3 s, machine 1-minute load 7.08,
0 agda slots before the run, `GHCRTS="-A64m -I0 -M8g"`, cap never raised.

1. **The `2-Constant` obligation is never about `Wat α`.** Any map that
   reads only the TRUNCATION of its input is `2-Constant` for free
   (`Door.agda:126-129`). So the whole question is split support for the
   TARGET.
2. **The member half discharges with no new principle**, by `leastOf`
   over the ordinal's own well-order (`Door.agda:156-179`). MEASURED.
3. **The naive map is NOT `2-Constant`** (`Door.agda:355-369`). MEASURED
   by a term, at every site holding a witness and two distinct points.
4. **A well-order on `sq α` gives the map outright, with no `Wat` at
   all** (`Door.agda:404-412`), and `pullOrder` reduces that well-order
   to an injection of `sq α` into any well-ordered carrier
   (`Door.agda:415-418`). **That injection is the ambient-to-code
   crossing.**

**THE TREE OWES THE CROSSING, NOT A MAP.**

**THE DOOR IS NOT CLOSED (C-36).** Section 8 writes the four maps I
could not write.

## 1. THE PREMISE RE-RUN: VERIFIED

`agents/tasks/LJ-1-319/SqIsSet.agda` re-runs green under my own hand.
Exit 0. Elapsed 2 s. Agda slots before the run: 0, by the awk command.
Machine 1-minute load 9.07. Cap `GHCRTS="-A64m -I0 -M8g"`, never raised.
Dependencies were warm.

So `sq-set : (α : V ℓ) → isSet (sq α)` stands, at
`agents/tasks/LJ-1-319/SqIsSet.agda:37-41`.

**And it stands twice.** `Door.agda:51` imports `sq-set` and uses it at
`Door.agda:140`. My own build compiles the premise. It is not quoted.

## 2. THE LIBRARY DOOR: VERIFIED BY READING (C-44)

Read in
`/opt/homebrew/Cellar/agda/2.8.0-r3/share/agda/cubical/Cubical/HITs/PropositionalTruncation/Properties.agda`:

- `module SetElim (Bset : isSet B)` opens at `:181`.
- `rec→Set : (f : A → B) (kf : 2-Constant f) → ∥ A ∥₁ → B` is at `:185`,
  with its clauses at `:189-190`.
- `trunc→Set≃ : (∥ A ∥₁ → B) ≃ (Σ (A → B) 2-Constant)` is at `:225-227`.
- `open SetElim public using (rec→Set; trunc→Set≃)` is at `:268`.
- `elim→Set` is at `:270-274`.
- `2-Constant f = ∀ x y → f x ≡ f y` is at
  `Cubical/Foundations/Function.agda:106-107`; `2-Constant-isProp` at
  `:109-112`.

**All three cited objects exist with the cited types at the cited lines.
The brief's citation is correct.** I used `rec→Set` at `Door.agda:140`
and it typechecks, so the door is open as a tool, not only as a reading.

**Consequence, and it is an equivalence, not an implication.** `sq α` is
a set. So by `trunc→Set≃` the maps `∥ Wat α ∥₁ → sq α` ARE exactly the
`2-Constant` maps `Wat α → sq α`. The brief's question is therefore
necessary AND sufficient for J1.

## 3. THE FIRST RESULT, AND IT REDIRECTS THE WHOLE TASK

**A map that factors through ANY proposition is `2-Constant`.**

```agda
factor-2Const : isProp P → (u : A → P) (v : P → B) → 2-Constant (λ a → v (u a))
factor-2Const pp u v x y = cong v (pp (u x) (u y))
```

`Door.agda:126-129`. One line of proof.

**What this measures.** The `2-Constant` condition places NO constraint
on how a construction reads its witness, as long as it reads the witness
only through a proposition. Taking `P = ∥ Wat α ∥₁` gives both directions
at once (`Door.agda:133-140`):

```agda
untrunc→2Const : (α : V ℓ) (s : ∥ Wat α ∥₁ → sq α)
               → Σ[ f ∈ (Wat α → sq α) ] 2-Constant f
2Const→untrunc : (α : V ℓ) (f : Wat α → sq α) → 2-Constant f
               → ∥ Wat α ∥₁ → sq α
```

**So the brief's question is not a question about `Wat α`. It is the
question of split support for `sq α`, wearing a different hat.** That is
Kraus, Escardó, Coquand and Altenkirch Theorem 16 read at this site, and
it is why section 7's route bypasses `Wat` entirely.

## 4. THE MEMBER HALF DISCHARGES. MEASURED.

`leastWat` at `Door.agda:156-179`:

```agda
leastWat : (α : V ℓ) (oα : IsOrd α) → ∥ Wat α ∥₁
         → Σ[ m ∈ ⟪ α ⟫ ] ∥ ⟪ α ⟫ ↪ ⟪ ⟪ α ⟫↪ m ⟫ ∥₁
```

Green. It is the delivered `LeastCardInjL` pattern
(`src/L/Cardinal.lagda.md:116-134`) moved from `sucV α` to `α` itself.
The predicate is the TRUNCATED injection, an `hProp`, which is all
`leastOf` allows (`src/L/WellOrder/Base.lagda.md:158-161`, read).

The order is SEALED under `opaque` (`Door.agda:163-165`), the medicine of
`src/L/Cardinal.lagda.md:85-92` and of
`agents/tasks/LJ-1-305/Untruncated.agda:135-137`. **C-51 and P-i: I hit
no heap wall and I did not test whether the unsealed form walls. INFERRED
that it would, from the two sites that measured it.**

**Note the shape, and it is the whole reason the residue is small.**
`leastWat` takes `∥ Wat α ∥₁`, not `Wat α`. So by section 3 every
construction built on it is `2-Constant` for free.

## 5. THE RESIDUE, NAMED, AND WHERE IT WALLS

### 5.1 The residue

```agda
CanonInj = (α : V ℓ) (m : ⟪ α ⟫) → IsOrd α
         → ∥ ⟪ α ⟫ ↪ ⟪ ⟪ α ⟫↪ m ⟫ ∥₁ → ⟪ α ⟫ ↪ ⟪ ⟪ α ⟫↪ m ⟫
```

`Door.agda:193-195`. **Given it, the `2-Constant` map is BUILT, with its
`2-Constant` proof**, at `Door.agda:211-213`:

```agda
canon→door : CanonInj → (α : V ℓ) → IsOrd α → IH α
           → Σ[ f ∈ (Wat α → sq α) ] 2-Constant f
```

**C-45 applies and I state it.** `CanonInj` is ASSUMED there. Nothing
proves it. The value of the part is the REDUCTION, and the reduction is
the term.

### 5.2 How far the ordinal machinery reaches. MEASURED.

**The tree builds exactly ONE canonical injection of a carrier into the
carrier of one of its members, and it is the SUCCESSOR case.**

```agda
absorbs : (γ : S) → IsOrd (fst γ) → (⟨ fst γ ∈ ω ⟩ → Empty.⊥)
        → ((k : ℕ) → ⟨ # k ∈ fst γ ⟩)
        → ⟪ sucV (fst γ) ⟫ ↪ ⟪ fst γ ⟫
```

`src/L/Absorption.lagda.md:613-615`. It reads no witness. It is built
from the shift graph on the ordinal. I typechecked that reading at
`Door.agda:227-230`.

**MEASURED by a COMPLETE census, not a sample.**
`grep -rn "↪ ⟪" src/ | grep -v "⟫↪"` returns 38 lines. I classified all
38. Exactly TWO carry the shape `⟪ β ⟫ ↪ ⟪ member of β ⟫` as a DELIVERED,
UNTRUNCATED conclusion, and both are the same term:

- `src/L/Absorption.lagda.md:189`, `shift↪ : ⟪ sucV γ ⟫ ↪ ⟪ γ ⟫`.
- `src/L/Absorption.lagda.md:615`, `absorbs`, which exports it.

Every other line of that shape is one of four things:

- A HYPOTHESIS. `src/L/GCH.lagda.md:55`, the trophy's own absorption
  hypothesis; `src/L/BoundedSubset.lagda.md:1392`, a module parameter
  named `absorbs`.
- A SEARCH PREDICATE. `src/L/Cardinal.lagda.md:64`, the `Inj` predicate
  `leastOf` runs over.
- A REFUTATION TARGET. `src/L/Cardinal.lagda.md:141`;
  `src/L/BoundedSubset.lagda.md:1047`, `IsCardinal`, which is the
  NEGATION of the target at every member.
- A TRUNCATED existence. `src/L/Cardinal.lagda.md:133`, `κ-inj`, which is
  the debt the plan already records.

### 5.3 THE WALL, at `file:line`

**`CanonInj` at a LIMIT non-initial ordinal has no supplier in this
tree.** `absorbs` covers `α ≡ sucV γ` and nothing covers the limit case.
The wall is `src/L/Absorption.lagda.md:613-615`: that is where the only
canonical big-into-small injection lives, and its type names `sucV`.

**This is the case the ruling predicted**, and the mathematics agrees.
`[LJ-1.316]` section 2.4, at
`agents/tasks/LJ-1-316/lj-1.316-report.md:237`: the greedy construction
from the two well-orders alone fails at order type `ω · 2` into `ω`,
where it exhausts the target at the ω-th step.

**What would build it, priced.** A canonical injection `α ↪ |α|` for
every infinite ordinal α is the choice-free ZF fact the brief names. **I
did not build it and I did not price it in lines, because I measured
something that changes the question: it is not available from ordinal
structure alone.** INFERRED, by a model argument and not by a term: a
uniformly definable family `α ↦ (α ↪ ω)` over the countable ordinals
would give a definable injection `ω₁ → ℝ`, and `L(ℝ)` under determinacy
has none. That is the same class of argument `[LJ-1.314]` section 4.1
used against `InjData`, and it is INFERRED, not MEASURED. **It does not
apply inside L**, where `<_L` orders the injections. **So the residue is
the crossing into L, exactly as the diagnosis at
`agents/tasks/LJ-1-316/lj-1.316-report.md:203-207` says.**

## 6. THE NAIVE MAP IS REFUTED. MEASURED.

`naive-not-2Const` at `Door.agda:314-351` and its corollary
`naive-refuted` at `Door.agda:363-369`:

```agda
naive : (α : V ℓ) → IsOrd α → IH α → Wat α → sq α
naive α oα ih w =
  sq-transport α (fst w) oα (fst (snd w)) (snd (snd w))
    (ih (fst w) (fst (snd w)))

naive-refuted : (α : V ℓ) (oα : IsOrd α) (ih : IH α)
              → (δ : V ℓ) (δ∈α : ⟨ δ ∈ˢ α ⟩) (e : ⟪ α ⟫ ↪ ⟪ δ ⟫)
              → (a₀ a₁ : ⟪ α ⟫) → ((a₀ ≡ a₁) → Empty.⊥)
              → 2-Constant (naive α oα ih) → Empty.⊥
```

**MEASURED. The ruling's INFERRED prediction is confirmed.** Two
witnesses with the SAME member and injections differing by ONE
transposition already break `2-Constant`. The proof reads the composite
at the diagonal point `(a₀ , a₀)`, cancels `include` and `sqδ` by
injectivity, and lands on `swap (e a₀) ≡ e a₀`, which the transposition
refutes.

The transposition is `NotProp`'s `swap`
(`agents/tasks/LJ-1-305/NotProp.agda:99-165`) made generic in its two
points, at `Door.agda:250-298`. Every clause matches a decision passed as
an ARGUMENT, never a `with`-abstraction, because the `with` form
exhausted an 8 GB heap at the original site (P-i, C-51).

**The hypotheses are satisfiable and I say where.** They are exactly the
non-initial branch's own context: a witness `(δ , δ∈α , e)` and two
distinct points of `⟪ α ⟫`. Every ordinal the descent visits holds ω, so
it holds two distinct numerals
(`agents/tasks/LJ-1-305/NotProp.agda:53-64`).

**A refuted naive map NARROWS THE SEARCH. It does not close the door.**
C-36.

## 7. THE ROUTE THE SEARCH NARROWED TO, and it is the finding

**A well-order on `sq α` gives the `2-Constant` map outright, with no
`Wat` and no canonical injection.**

```agda
least-elt : {A : Type ℓ} → SWO {ℓ} A → ∥ A ∥₁ → A
sq-split  : (α : V ℓ) → SWO {ℓ} (sq α) → ∥ sq α ∥₁ → sq α
order→door : (α : V ℓ) → SWO {ℓ} (sq α) → (Wat α → ∥ sq α ∥₁)
           → Σ[ f ∈ (Wat α → sq α) ] 2-Constant f
```

`Door.agda:394-412`. All green.

**Why this is strictly better than `CanonInj`.** The delivered descent
ALREADY produces `∥ sq α ∥₁` at every α with no new principle:
`SqI α = ... → (IsCardinal α → sq α) × ∥ sq α ∥₁` at
`agents/tasks/LJ-1-305/Untruncated.agda:207-209`, green at that task.
**So `sq-split` alone finishes the untruncated square law.** It does not
need `Wat`, it does not need the least member, and it does not need the
canonical injection. It needs one thing: a well-order on `sq α`.

**And the tree reduces that on demand.** `pullOrder`
(`src/L/Choice/Step.lagda.md:252-258`) is generic:

```agda
code→order : (α : V ℓ) (C : Type ℓc) (w : SWO {ℓc} C)
           → (c : sq α → C) → ((u v : sq α) → c u ≡ c v → u ≡ v)
           → SWO {ℓ} (sq α)
```

`Door.agda:415-418`, green. **An injection of `sq α` into ANY
well-ordered carrier well-orders `sq α`.** The chapter says so itself:
"`pullOrder` moves a well-order along an injection and is the only
transfer", `src/L/Choice/Step.lagda.md:866`. The carrier the tree offers is
`Mem (Lset β)`, ordered by `orderAt`
(`agents/tasks/LJ-1-314/CodeUntrunc.agda:71-72`). So the obligation is:
**code the ambient pairing function as an L-set at a bounded stage.**
That is the ambient-to-code crossing, in the shape
`agents/tasks/LJ-1-314/CodeUntrunc.agda:145-148` already gives it for
injections.

### 7.1 The SWO census, VERIFIED with one refinement

The brief's premise says `leastOf` demands `P : A → hProp` and no `SWO`
in the tree carries a function type, census of all 14 by `[LJ-1.314]`.

**VERIFIED as to the claim. MEASURED that the count is not 14.**
`grep -rn ": SWO" src/` returns 35 lines, of which 19 are constructions
and the rest are parameters or projections. The constructed carriers are
`⟪ x ⟫`, `⟪ Lset δ ⟫`, `Mem (Lset β)`, `ℕ`, `Name`, `New δ`, `Point n`,
`Limit`, `SL`, and products of those. **NONE is a function type.
MEASURED.**

**THE REFINEMENT, and it is what section 7 rests on.** `pullOrder`
(`src/L/Choice/Step.lagda.md:236-258`) is GENERIC in its carrier `B`. So
the tree does not merely lack a well-order on a function type. **It has a
factory for one, and the factory's input is an injection.** The census
answer "no SWO carries a function type" is true and it is not the end of
the question.

## 8. THE MAP I COULD NOT WRITE (C-36)

Four candidates. None is refuted. I state each and what stopped it.

1. **The pointwise-least pairing.** `⟪ α ⟫` is well-ordered, so define
   `h (a , b)` as the LEAST `c : ⟪ α ⟫` for which some witness's
   composite sends `(a , b)` to `c`. The predicate
   `∥ Σ[ e ∈ ⟪ α ⟫ ↪ ⟪ δ₀ ⟫ ] (T e .fst (a , b) ≡ c) ∥₁` is an `hProp`,
   `leastOf` applies, and the resulting `h` reads only truncations, so it
   is canonical and `2-Constant` for free. **What stopped it: INJECTIVITY
   does not follow.** Two arguments can reach the same least value
   through two different witnesses. I did not build it, because the
   deliverable is `sq α` and `h` without injectivity is not one. **This
   is not refuted. A proof that the pointwise-least map collides, or a
   proof that it does not, is a real next probe and it is cheap.**
2. **A weakly constant endomap of `sq α` by any other route.** Kraus et
   al. Theorem 16 says this is exactly equivalent to what is wanted. A
   well-order is one supplier (section 7). **No argument here says it is
   the only one.**
3. **The canonical injection at a limit non-initial ordinal.** Section
   5.3. The wall is that ordinal structure alone does not build it. **A
   Gödel pairing on the ordinal itself would be the classical device;
   the tree has `godSWO` (`src/L/Ordinal/SquareLaw.lagda.md:308`) and
   `god` (`:755`) already, and neither was tried against this target. I
   did not price that attempt.**
4. **The stage-cardinal technique, re-run at a new pair. THIS IS THE
   STRONGEST LEAD AND I FOUND IT LATE.** The census of section 5.2 turned
   up a family I did not expect: `stage-card-upper`,
   `⟪ Lset α ⟫ ↪ ⟪ α ⟫` at `src/L/StageCardinal.lagda.md:564-566` and
   `:396-399`. **That IS a canonical, witness-free injection of one
   carrier into another of the same cardinality**, built by
   `∈-induction` over the ordinal with a coding and counting argument,
   with a limit step at `:396-399`. It is the exact shape `CanonInj`
   wants, at a different pair of carriers. **What stopped me: I did not
   attempt the transplant, and P-l forbids me from pricing it by
   analogy.** A judgement at one site is a hypothesis at another, and a
   re-measurement at `CanonInj`'s own site is the honest next step.

**MEASURED FALSE, at this probe's reach: any proof that no `2-Constant`
map exists.** No such proof can arrive in-theory, by
`agents/tasks/LJ-1-319/lj-1.319-ruling.md:71-75`.

## 9. THE CODED COMPOSITE: BUILT

`[LJ-1.314]` section 1.4 left the join INFERRED and priced it at about 20
lines. It is built at `Door.agda:435-458`, and it is 9 non-comment lines:

```agda
InjDataL = (α : V ℓ) → IsOrd α → ⟨ isL α ⟩ → ∥ Wat α ∥₁ → Wat α

bounded→injdata : BoundedToCode → InjDataL
bounded→2Const : BoundedToCode → (α : V ℓ) → IsOrd α → ⟨ isL α ⟩ → IH α
               → Σ[ f ∈ (Wat α → sq α) ] 2-Constant f
```

Green. `leastWat` takes the member half and `bridge→data`
(`agents/tasks/LJ-1-314/CodeUntrunc.agda:150-155`) takes the injection at
it.

**ONE DEVIATION, stated plainly.** The composite needs `⟨ isL α ⟩`, which
`InjData` (`agents/tasks/LJ-1-305/Untruncated.agda:114-115`) does not
carry, because `bridge→data` speaks of `S`. **The call site has it:**
`stepU` holds `isLα` in scope where `injdata` is applied
(`agents/tasks/LJ-1-305/Untruncated.agda:293` and `:314-316`). So the
composite is usable exactly where `InjData` was used. **I did not build a
version without `⟨ isL α ⟩` and I do not claim one exists.**

I imported `agents/tasks/LJ-1-314/CodeUntrunc.agda` rather than copying
it (`Door.agda:54`). **That re-compiles it under my own hand, so its
green is measured here too.** I changed no line of it.

## 10. THE VERDICT, in the ruling's vocabulary

`[LJ-1.305]`'s NEEDS-A-PRINCIPLE was downgraded by `[LJ-1.319]` to
**NEEDS-A-2-CONSTANT-MAP-OR-THE-CROSSING**.

**THE TREE NOW OWES THE CROSSING.**

Stated exactly: the tree owes an injection of `sq α`, or of
`⟪ α ⟫ ↪ ⟪ δ₀ ⟫`, into a carrier the tree already well-orders. Given it,
`pullOrder` and `leastOf` finish, with no new principle and no
`2-Constant` reasoning at all.

**The map half is not refuted and must not be recorded as refuted.** What
is refuted is ONE map, the naive `sq-transport` composite (section 6).
Section 8 lists three live candidates.

## 11. DD4, STATED AND ANSWERED, WITH MY AXIS (C-46)

**DD4: maximize the code the two proofs share, and write it generic.**
One rule, two ends, no metric and no checker. DD4's own axis is
AC-against-GCH, fixed in code at `scripts/measure/ledger.py:50`.

**MY AXIS: does the construction name a tower?**

**Answer: the whole positive machinery is tower-blind, MEASURED by
reading my own types.**

- `factor-2Const` (`Door.agda:126`), `least-elt` (`:394`),
  `order→wconst` (`:400`), `code→order` (`:415`): generic in the carrier.
  No `V`, no `L`, no ordinal. They would compile against any type.
- `leastWat` (`:156`), `CanonInj` (`:193`), `naive-not-2Const` (`:314`):
  name `V ℓ` and `IsOrd`, so they name the AMBIENT ordinals. They do not
  name `L`, `Lset` or any stage.
- `succCanon` (`:227`) and PART 6 (`:435-458`) name `L`, through
  `absorbs`' `S` and through `isL`.

**So the cure that the search points at is generic by construction, and
it costs the AC trophy nothing.** This is the axis the ruling flagged at
`agents/tasks/LJ-1-319/lj-1.319-ruling.md:189-201`: a module-parameter
`InjData` would seat a choice-shaped assumption in the shared telescope,
and a canonical construction does not.

**AND THERE IS A DD4 GAIN I DID NOT EXPECT.** `pullOrder`, the factory
section 7 rests on, lives in `src/L/Choice/Step.lagda.md`, which is the
AC trophy's own machinery. **The GCH descent's cure re-uses SHARED code
instead of adding a GCH-only import.** MEASURED by the file's home
directory, not by a closure count.

**I did not run `ledger.py` and I quote no size figure.** `dev/ledger.toml:204`
records that the GCH closure is read from a STATEMENT whose proof is not
wired, so it UNDERSTATES.

## 12. SIZE AND TIMING (DD24, DD8)

`agents/tasks/LJ-1-321/Door.agda`: 464 lines, 399 non-blank, **239
non-blank non-comment**. The comment share is high on purpose: this is a
probe whose deliverable is a reading as much as a term.

Runs, every one with 0 agda slots counted before it by
`ps aux | awk '/libexec.*bin\/agda/ && !/awk/' | wc -l`:

| run | exit | elapsed | 1-minute load |
|---|---|---|---|
| `SqIsSet.agda` re-run | 0 | 2 s | 9.07 |
| `Door.agda` first green | 0 | 2 s | 6.84 |
| `Door.agda` final | 0 | 3 s | 7.08 |
| `Door.agda` confirmation, after the report was written | 0 | 2 s | 4.78 |

**MEASURED FALSE: any invocation past 30 minutes, and any heap
exhaustion.** Cap `GHCRTS="-A64m -I0 -M8g"` on every run, never raised.
Dependencies were warm throughout, so **these seconds price a warm
incremental check and nothing else.** The load figures are the machine's,
which was not quiet; my deliverable is a TERM, so they do not bear.

## 13. THE ABORT CRITERION, FIXED BEFORE THE RUN (D-1)

The brief fixed five. Which fired:

1. **The map exists and I build it.** DID NOT FIRE. I built it three
   times over, each time conditional on a named hypothesis.
2. **The canonical injection walls.** FIRED. Section 5.3, at
   `src/L/Absorption.lagda.md:613-615`.
3. **The naive map is refuted and no other is found.** FIRED. Sections 6
   and 8. **NARROWED SEARCH, not a closed door.**
4. **`sq-set` fails on re-run.** DID NOT FIRE. Section 1.
5. **A wall past 30 minutes.** DID NOT FIRE. Section 12.

## 14. WHAT I DID NOT DO

- I did not build the pointwise-least map of section 8 item 1, and I did
  not test whether it collides.
- I did not try `godSWO` or `god` against `CanonInj` (section 8 item 3).
- I did not build a concrete non-initial `α` with a concrete `Wat α`
  witness. The refutation is stated at hypotheses that the branch
  supplies; **I did not typecheck an instance of those hypotheses.**
- I did not price the canonical injection in lines. Section 5.3 says why.
- I did not run `make check`, did not commit, did not push.
- I wrote only inside `agents/tasks/LJ-1-321/`. I edited nothing in
  `src/`, `dev/`, `AGENTS.md`, `.claude/` or any sibling task directory.

## 15. ARCHIVE USED (DD18), ONE LINE READ PER FILE

- `agents/tasks/LJ-1-319/lj-1.319-ruling.md:112-113`: the question,
  stated exactly, which section 0 answers. Sections 1 and 2.3 read whole.
- `agents/tasks/LJ-1-316/lj-1.316-report.md:237`: the `ω · 2` greedy
  failure, which is why section 5.3 does not attempt the well-order
  route.
- `agents/tasks/LJ-1-314/lj-1.314-report.md:150-154`: the INFERRED join
  and its 20-line price, which section 9 discharges at 9 lines.
- `agents/tasks/LJ-1-305/lj-1.305-report.md:112-114`: the J1 sentence
  that measured `PT.rec`, which section 2 replaces.
- `archive/dev/TASKS-archived.md:300` (L3.32-T158), **taken as SHAPE**:
  the retired route met its choice-shaped obligation by re-entering L
  through the description side, not by an ambient principle. **The same
  shape as section 10's crossing.** Also `:192` (L3.32-T162): the
  retired route kept `pullSWO` as shared machinery, which is
  `pullOrder`'s ancestor.
  **WHAT WOULD NOT TRANSFER:** every figure in those rows is a naive-line
  price for J-tower modules that no longer exist, and `:274`
  (L3.32-T203)'s CROSS verdict is about the AC route's bridge, a
  DIFFERENT crossing from the ambient-to-code one this task prices. A
  verdict on one crossing is not a verdict on another (P-l).

## 16. LITERATURE USED (DD18)

### READ

- `agents/tasks/LJ-1-316/truncation-and-selection.md`, the proposed
  digest, sections 2.3 to 2.7, 4 and 5. **Its section 5 item 2 states in
  words what my section 7 turns into a term: a canonical injection needs
  a well-order on the INJECTIONS, which `<_L` supplies and an ambient
  function type does not.**
- The installed cubical library, `PropositionalTruncation/Properties.agda`
  and `Foundations/Function.agda`, at the lines in section 2.

**THE BRIEF'S ONE-LINE QUESTION.** **Kraus, Escardó, Coquand and
Altenkirch Theorem 16 is usable CONSTRUCTIVELY here in one direction and
is only a classification in the other:** exhibiting the endomap builds
the untruncation, and `order→wconst` (`Door.agda:400-402`) is that
direction typechecked; the converse direction tells you an endomap exists
once you already have the untruncation, so it never supplies one.

### NOT READ, WITH WHY NOT

- Kraus arXiv:1411.2682, the library's own citation for `rec→Set`. NOT
  READ: I use the library's term, which typechecks, so the paper's proof
  is not load-bearing for me.
- Devlin, Jech, Schindler and Zeman. NOT READ at this task: `[LJ-1.316]`
  read them and my question is about the type theory, not about which
  classical device selects.
- HoTT Book Theorem 10.4.3 and section 3.9. NOT READ directly: the digest
  quotes what bears, and nothing in my sections turns on a number from
  the book.

## 17. FOR THE ORCHESTRATOR

1. **Do not record the door as closed.** Record: naive map refuted,
   canonical injection walled at the limit case, obligation narrowed to a
   well-order on `sq α`.
2. **The next probe is cheap and it is section 8 item 1**: does the
   pointwise-least pairing collide? A term either way settles a live
   candidate.
3. **Section 8 item 4 is the lead I would fund first**, and it was not
   in the brief: `stage-card-upper` (`src/L/StageCardinal.lagda.md:564-566`)
   is a delivered canonical injection of the same SHAPE as `CanonInj`,
   built by `∈-induction` with a limit step. P-l says re-measure it at
   its own site; nothing here prices it.
4. **The crossing is now the single named debt**, and section 7 shows it
   is smaller than the ruling assumed: it needs to code ONE pairing
   function, not an injection at every member.
5. **Two LESSONS candidates, with measurements, at your numbering.**
   First: **a `2-Constant` obligation at a set motive is split support
   for the TARGET, never a condition on the witness**; measurement,
   `factor-2Const` at `Door.agda:126-129` plus `untrunc→2Const` and
   `2Const→untrunc` at `:148-158`, all green. Second: **when a truncation
   stalls and no well-order carries the type, look for `pullOrder` before
   looking for a principle**; measurement, `code→order` at
   `Door.agda:415-418` green against `src/L/Choice/Step.lagda.md:252-258`.

## 18. CHECKS RUN

- `.venv/bin/python scripts/gate/lint-agda.py --check agents/tasks/LJ-1-321/Door.agda`:
  exit 0.
- `.venv/bin/python scripts/gate/lint-prose.py --check` on this file:
  recorded in section 19.
- `grep -n "postulate\|TERMINATING\|{!\|trustMe" agents/tasks/LJ-1-321/Door.agda`:
  0 hits. The file is `--safe` with no holes and no postulate.
- MEASURED: no em dash in either file I wrote.

## 19. LINT RESULT

`.venv/bin/python scripts/gate/lint-prose.py --check agents/tasks/LJ-1-321/lj-1.321-report.md`: exit 0.
`.venv/bin/python scripts/gate/lint-agda.py --check agents/tasks/LJ-1-321/Door.agda`: exit 0.
Em dash count in both files: 0, by `grep -c`.
