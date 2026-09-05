# LJ-1.334 report: item 1, the pointwise-least pairing. The last untried candidate

tier: opus (in-harness-subagent-mode), the switch's DEFAULT row. Probe. It lands
nothing. Written incrementally (C-22).

## VERDICT: ESCAPES, AND ITEM 1 IS REFUTED ANYWAY

**Item 1 ESCAPES the digest's counterexample. Then two terms refute it.**

**THE DIGEST'S COUNTEREXAMPLE IS A DIFFERENT CONSTRUCTION.** The digest names
the GREEDY map, which sends each element to the least UNUSED target
(`dev/literature/truncation-and-selection.md:312-314`). Item 1 sends each pair to
the least REACHABLE value (`agents/tasks/LJ-1-321/lj-1.321-report.md:309-315`).
**The greedy map fails by running out of targets. Item 1's map never runs out:
it is TOTAL, and `item1-h` compiles**, `ProbeLJ1334A.agda:79-80`. **So the
digest's paragraph could not have closed this task, and negative control 5 puts
that difference in one error message.**

**ITEM 1 IS REFUTED, MEASURED, at BOTH readings, and the reason is neither the
band nor the order type.** Item 1's map is symmetric in its two arguments, so it
is injective only if the carrier is a proposition. In the band the carrier holds
`ω` and `sucV ω`, so it is not.

- **Reading A, the reachable set over all of `sq α`:** `item1-symmetric`,
  `ProbeLJ1334A.agda:131-141`; `item1-refuted`, `:170-176`. The whole argument is
  the FLIP of a pair, and it costs no excluded middle.
- **Reading B, `[LJ-1.321]`'s own wording, over the composites of ONE injection
  type with the inner pairing FIXED:** `item1-refuted-composites`,
  `ProbeLJ1334B.agda:224-233`. **The flip does not act on that family**, and
  `comp-not-flip-closed` (`ProbeLJ1334B.agda:76-90`) MEASURES it. **The extra
  cost is one transposition**, `ProbeLJ1334B.agda:103-148`.

**`[LJ-1.321]` ASKED FOR EXACTLY THIS AND PRICED IT CHEAP.** Its section 17 item
2 reads 「The next probe is cheap and it is section 8 item 1: does the
pointwise-least pairing collide? A term either way settles a live candidate」,
`agents/tasks/LJ-1-321/lj-1.321-report.md:535-537`. **IT COLLIDES. The price was
two files and 2 seconds each.**

**THE BRIEF'S PREMISE IS TRUE, AND IT WAS NOT THE LOAD-BEARING ONE.** `ω · 2` is
a non-initial limit and it is in the band. Section 1 marks each row MEASURED or
INFERRED. **But the premise does not decide the task**, because the digest's
counterexample fails to reach item 1 for a reason that has nothing to do with the
order type.

## 1. THE BRIEF'S PREMISE, ANSWERED FIRST

The premise: 「`ω · 2` is a non-initial limit, which is exactly this band」.

**THE BAND, as `[LJ-1.332]` defines it** (`agents/tasks/LJ-1-332/ProbeLJ1332A.agda:196-204`):
an ordinal `α` with four conditions. Rows 1 to 3 are `IsOrd α`, `⟨ ω ∈ˢ α ⟩` and
successor closure. Row 4 is `Init α → Empty.⊥`. Because rows 1 to 3 already give
the first three rows of `Init` (`src/L/Ordinal/SquareLaw.lagda.md:690-698`), row
4 says exactly that `Init`'s FOURTH row fails: the site's index injects into some
infinite member's square.

**`ω · 2` is `+ω ω` in this tree's arithmetic**, `src/L/Ordinal/StageArith.lagda.md:40-42`.
The retired route read it the same way,
`agents/tasks/archive/L3-32-T90/l3.32-t90-report.md:98`.

| row | the claim about `ω · 2` | status |
|---|---|---|
| 1 | `IsOrd (+ω ω)` | **MEASURED.** `ω2-ord`, `ProbeLJ1334A.agda:259-260` |
| 2 | `⟨ ω ∈ˢ +ω ω ⟩` | **MEASURED.** `ω∈ω2`, `ProbeLJ1334A.agda:262-263` |
| 3 | successor closure | **INFERRED.** `ω · 2` is a limit. No term of mine reaches it. Section 1.1 says why |
| 4 | `Init (+ω ω) → Empty.⊥` | **INFERRED.** `ω · 2` injects into `ω × ω`, a counting fact this tree does not deliver |

**ANSWER: YES. `ω · 2` is a non-initial limit and it is in the band.** Rows 1 and
2 MEASURED, rows 3 and 4 INFERRED. **The brief's premise stands.**

**AND ROW 4 IS THE DIGEST'S OWN SENTENCE.** The digest asserts that `ω · 2`
injects into `ω`. That assertion IS row 4's failure at `β = ω`. **So the digest
does not merely mention the band's first member. It asserts the band's defining
condition there.**

**I also MEASURED the two members that the refutation needs**, and they need no
band hypothesis: `sucω∈ω2 = +ω-iter 1 ω`, `ProbeLJ1334A.agda:265-266`.

### 1.1 Why rows 3 and 4 are INFERRED and not MEASURED

**`+ω` is opaque by R-38**, `src/L/Ordinal/StageArith.lagda.md:38-39`: 「The union
representation is sealed at birth. Consumers see an atom」. **MEASURED, by
reading the module: `L.Ordinal.StageArith` exports five facts about `+ω`**, at
`:48`, `:62`, `:65`, `:68` and `:76`. `+ω-in` puts a member IN. **No exported
fact takes a member OUT.** Successor closure needs the union's reverse direction,
which the module seals. **I did not unseal it**, because the seal is a ruling and
my task is not to change it.

**Row 4 needs `|ω · 2| = ℵ₀`.** That is a counting theorem about the carrier of
`+ω ω`, and no chapter delivers it. **I claim no term.**

### 1.2 The premise was true and it did not decide

**The brief expected the premise to decide the task.** It does not. **The
refutation uses rows 1 to 3 only, never row 4, and never the order type.**
`item1-refuted-in-band`, `ProbeLJ1334A.agda:183-190`. **So item 1 dies at every
ordinal that holds `ω` and `sucV ω`, INITIAL or not, and at `ω · 2` in
particular** (`item1-refuted-at-ω2`, `ProbeLJ1334A.agda:270-274`).

**THAT IS A SEVENTH CHECK IN A ROW THAT FOUND SOMETHING, and what it found is
not the shape the brief predicted.** The premise was right. **The inference from
it was wrong.**

## 2. WHY THE DIGEST'S COUNTEREXAMPLE DOES NOT REACH ITEM 1

**Two constructions, and they fail in opposite halves.**

| | the digest's map | item 1's map |
|---|---|---|
| recipe | least **UNUSED** target | least **REACHABLE** value |
| reads | the values already assigned | the truncated witness supply |
| injective | by construction | **not**, and section 3 measures it |
| total | **not**, and that is the `ω · 2` failure | **yes**, MEASURED |

**The digest's map buys injectivity and loses totality. Item 1's map buys
totality and loses injectivity.** The digest's paragraph prices the first trade.
**It says nothing about the second, and the second is item 1.**

**MEASURED: item 1's map is total.** `item1-h`, `ProbeLJ1334A.agda:79-80`, green.
It takes any ordinal, any well-order on its carrier and the truncated supply, and
it returns a value at every pair. **A map that compiles cannot run out of
targets.**

**AND THE MACHINE STATES THE DIFFERENCE.** Negative control 5 offered the greedy
recipe where a pointwise reader is wanted. Agda answered
`⟪ α ⟫ → hProp ℓ !=< Σ ⟪ α ⟫ (λ _ → ⟪ α ⟫)`: the greedy recipe takes the PAIR
first, a reader takes the PREDICATE first. **They are different constructions.**

**WHAT THE DIGEST STILL GETS RIGHT, and it is the important half.** Its next
sentence is 「A canonical injection needs a well-order on the INJECTIONS, which
is what `<_L` supplies classically and what an ambient function type does not
have」, `dev/literature/truncation-and-selection.md:314-316`. **That sentence
covers item 1 and it is correct.** Item 1 well-orders the TARGETS. **Section 3
measures that ordering the targets is exactly what cannot work.** **The digest
states the principle. It does not prove it here. This probe proves it here.**

## 3. THE REFUTATION, READING A

### 3.1 Item 1's map exists and it is canonical

**Both halves of `[LJ-1.321]`'s positive claim are green.**

`item1-h`, `ProbeLJ1334A.agda:79-80`:

```agda
item1-h : (α : S) → SWO ⟪ α ⟫ → ∥ sq α ∥₁ → ⟪ α ⟫ × ⟪ α ⟫ → ⟪ α ⟫
item1-h α w t p = leastOf w lem (Reach α p) (reach-ne α t p) .fst
```

`item1-canonical`, `ProbeLJ1334A.agda:85-87`, one line: two proofs of the
truncation give the same map. **No choice is spent.**

**THE WELL-ORDER IS A HYPOTHESIS, not the delivered one.** So everything below
refutes item 1 for EVERY well-order on the carrier. `OrdSWO.ordSWO`
(`src/L/StageCardinal.lagda.md:258-263`) shows the hypothesis is inhabited at
every ordinal, so the generality costs nothing.

**AND ITEM 1 OWES EXACTLY ONE THING.** `item1-sq`, `ProbeLJ1334A.agda:92-96`:
injectivity of `item1-h` closes `sq α` and nothing else is missing. **That
compiles `[LJ-1.321]`'s own diagnosis.**

### 3.2 The flip, and the collapse

`sq α` is closed under precomposition with the flip of a pair. `flip-sq`,
`ProbeLJ1334A.agda:109-113`:

```agda
flip-sq : (α : S) → sq α → sq α
flip-sq α (f , finj) = (λ p → f (swap p)) , inj
  where
  inj : (u v : ⟪ α ⟫ × ⟪ α ⟫) → f (swap u) ≡ f (swap v) → u ≡ v
  inj u v e = cong swap (finj (swap u) (swap v) e)
```

**The flip is an involution, so it needs no decidable equality, no order and no
excluded middle.** That is why reading A is cheap.

`reach-flip`, `ProbeLJ1334A.agda:118-120`, one line: the reachable set at `p` and
the reachable set at `swap p` are the same set.

`item1-symmetric`, `ProbeLJ1334A.agda:131-141`. **The proof is `isPropLeastOf`**,
`src/L/WellOrder/Base.lagda.md:136-139`: a least element is unique. Two logically
equivalent predicates have the same least element, and `least-transfer`
(`ProbeLJ1334A.agda:124-128`) moves leastness across the equivalence without any
path between propositions.

### 3.3 The refutation itself

`item1-inj→prop`, `ProbeLJ1334A.agda:149-154`: a symmetric pairing is injective
only if `(a , b) ≡ (b , a)` for all `a` and `b`, that is, only if the carrier is
a proposition.

`two-members`, `ProbeLJ1334A.agda:158-167`: the carrier of a set that holds `ω`
and `sucV ω` is not a proposition. The proof is `fiber`, the embedding's
injectivity and `∈-irrefl`.

`item1-refuted`, `ProbeLJ1334A.agda:170-176`, and `item1-refuted-in-band`,
`ProbeLJ1334A.agda:183-190`. **The band's first three rows supply the two
members. Row 4 is never used.**

**AND THE TRUNCATION IS NOT THE CAUSE (C-56).**
`control-untruncated-collapses`, `ProbeLJ1334A.agda:195-199`: the same collapse
happens with an untruncated `sq α` in hand. **So the defect is in the RECIPE, not
in the truncation and not in my assembly.**

## 4. THE REFUTATION, READING B, WHICH IS `[LJ-1.321]`'s OWN WORDING

**`[LJ-1.321]` writes 「some witness's composite」 with the target member and the
inner pairing FIXED**, `agents/tasks/LJ-1-321/lj-1.321-report.md:309-315`. **That
family is NOT all of `sq α`, and probe A does not reach it. I did not assume it
did.**

**MEASURED, and this is why probe B exists.** `comp-not-flip-closed`,
`ProbeLJ1334B.agda:76-90`: if the composite family were closed under the flip,
the carrier would be a proposition. **So the flip does not act on it.** Negative
control 7 says the same thing in one error message.

**THE CURE IS A TRANSPOSITION, and I built it.** `module Transp`,
`ProbeLJ1334B.agda:103-148`. It spends the excluded middle once, through
`lowerLEM` (`src/Base/Classical.lagda.md:75-76`) and `[LJ-1.319]`'s `carrier-set`
(`agents/tasks/LJ-1-319/SqIsSet.agda:30-32`). **`[LJ-1.319]`'s file re-compiled
under my own hand: probe B IMPORTS it and does not copy it**
(`ProbeLJ1334B.agda:32`).

**THE CONDITION, NAMED ONCE.** `Precomp`, `ProbeLJ1334B.agda:157-160`: the family
is closed under precomposition of the witness with an injective self-map of the
carrier, and the value moves the way the map moves the pair.

- **`[LJ-1.321]`'s family satisfies it BY `refl`.** `comp-precomp`,
  `ProbeLJ1334B.agda:216-221`.
- **The refutation over any such family:** `itemW-refuted`,
  `ProbeLJ1334B.agda:202-210`.
- **Item 1 refuted at `[LJ-1.321]`'s reading:** `item1-refuted-composites`,
  `ProbeLJ1334B.agda:224-233`.

**Negative control 8 measured why the self-map must be INJECTIVE:** Agda answered
`σ x != x`. **A transposition is such a map, and that is where the excluded
middle goes.**

## 5. HOW WIDE THIS REACHES, AND WHERE IT STOPS (C-36, C-42)

**The well-order plays NO part.** PART 4 of probe A measures that.

`Reader α` (`ProbeLJ1334A.agda:209-211`) is any map that takes a predicate on the
carrier and its non-emptiness and returns a value. `Respects` (`:213-219`) says
the map does not distinguish logically equivalent predicates. **`leastOf` is one
such reader, by `isPropLeastOf`.** `reader-symmetric`, `ProbeLJ1334A.agda:221-228`,
and `reader-refuted`, `:230-239`.

**SO THE REFUTED OBJECT IS A FAMILY, and I name its edge exactly.**

- **REFUTED, MEASURED:** every pairing built by reading the set of values that a
  witness family reaches at a pair, when the family is closed under the flip
  (reading A) or under precomposition with an injective self-map (reading B).
  **Least is one reader among many and it is not special.**
- **NOT REFUTED, and I claim nothing about it:** a pairing that reads MORE than
  the reachable set. A recipe that also reads the pair's POSITION, or the values
  at other pairs, is outside the family. **The digest's greedy map is exactly
  such a recipe**, and it dies of the digest's own defect instead.
- **NOT REFUTED (C-36):** the untruncation of `sq α` at the limit band. **I
  refuted item 1 and nothing wider.**
  `agents/tasks/LJ-1-319/lj-1.319-ruling.md:71-75` records that no in-theory term
  can refute the door, and I claim no such term.
- **NO SWEEP RUN (C-42).** I did not search `src/` for other pointwise-least
  constructions that this shape would break. **I claim no count.**

## 6. LINES, SECONDS AND LOAD, WITH THE UNTRUNCATED CONTROL BESIDE THEM (C-56)

Two files, both in `agents/tasks/LJ-1-334/`.

| file | total | non-blank | code |
|---|---:|---:|---:|
| `ProbeLJ1334A.agda` | 340 | 303 | 144 |
| `ProbeLJ1334B.agda` | 273 | 240 | 154 |

**Counted with `wc -l`, `grep -cv` on blank lines, and `grep -vc` on comment
lines.** The comment blocks hold the eight negative controls, because nothing
typechecks these files once the task closes.

Load counted before EVERY invocation with the brief's command,
`ps aux | awk '/libexec.*bin\/agda/ && !/awk/' | wc -l`. `GHCRTS="-A64m -I0 -M8g"`
on every run. ONE process. Cap never raised. **No heap exhaustion and no wall.**

| run | what | exit | real s | agda slots before | 1-minute load |
|---|---|---:|---:|---:|---:|
| 1 | A, **GREEN on the first attempt** | **0** | 2 | 0 | 16.83 |
| 2 | A, GREEN, exit code captured | **0** | 2 | 0 | n/a |
| 3 | A, **NEGATIVE CONTROL 1** | error | 2 | 0 | n/a |
| 4 | A, **NEGATIVE CONTROL 2** | error | 2 | 0 | n/a |
| 5 | A, **NEGATIVE CONTROL 3** | error | 2 | 0 | n/a |
| 6 | A, **NEGATIVE CONTROL 4** | error | 2 | 0 | n/a |
| 7 | A, **NEGATIVE CONTROL 5** | error | 2 | 0 | n/a |
| 8 | A, controls recorded, **GREEN** | **0** | 2 | 0 | 7.24 |
| 9 | B, **GREEN on the first attempt** | **0** | 2 | 0 | n/a |
| 10 | B, GREEN, exit code captured | **0** | 2 | 0 | n/a |
| 11 | B, control 6, first form | error | 2 | 0 | n/a |
| 12 | B, **NEGATIVE CONTROL 6** | error | 2 | 0 | n/a |
| 13 | B, **NEGATIVE CONTROL 7** | error | 2 | 0 | n/a |
| 14 | B, **NEGATIVE CONTROL 8** | error | 2 | 0 | n/a |
| 15 | B, controls recorded, **GREEN** | **0** | 2 | 0 | 9.28 |
| 16 | A, re-run after B landed, **GREEN** | **0** | 1 | 0 | 9.28 |
| 17 | A, one comment citation corrected, **GREEN** | **0** | 2 | 0 | 15.28 |
| 18 | B, re-run after that, **GREEN** | **0** | 1 | 0 | 15.28 |

**C-56 HELD, AND IT PAID.** `control-untruncated` (`ProbeLJ1334A.agda:60-61`) was
written before any truncated term. **Then `control-untruncated-collapses`
(`:195-199`) turned the control into a MEASUREMENT: the collapse happens with an
untruncated witness in hand.** **So this probe's failure is not an assembly cost
and C-56's usual diagnosis does not apply here.** I report that as a second data
point for the law and not as a new law.

**MEASURED: no run exceeded 2 seconds.** **Every figure is WARM.** Every
interface under `src/` was already built, and `[LJ-1.319]`'s probe was already
compiled. **No cold cost is measured here** and P-l forbids pricing a landing
from these seconds.

**The machine was NOT quiet.** The 1-minute load ran between 7.24 and 16.83, and
other work held it. **I measured no check time as a price, so the load damages no
figure I report.** **The agda slot count was 0 before every one of the eighteen
runs.**

## 7. THE EIGHT NEGATIVE CONTROLS, AND WHAT EACH ONE NAMED

Each control was applied, run and reverted. All eight are recorded in the probe
files, at `ProbeLJ1334A.agda:277-340` and `ProbeLJ1334B.agda:236-273`. **ALL
EIGHT MEASURE.**

**CONTROL 1, ON THE FLIP.** I offered the SAME witness at the flipped pair. Agda
answered in 2 s:

```
error: [MismatchedProjectionsError]
The projections fst and snd do not match
when checking that the expression e has type s .fst (swap p) ≡ c
```

**The two reachable sets are not the same by triviality. `flip-sq` identifies
them.**

**CONTROL 2, ON WHAT THE REFUTATION RESTS.** I made `swap` a non-involution.
Agda refused inside `flip-sq`, 2 s: `cong swap (finj (swap u) (swap v) e) has
type u ≡ v`. **MEASURED: the refutation needs `sq α` closed under precomposition
with a PERMUTATION of the pair type, and nothing else. No order and no decidable
equality enter reading A.**

**CONTROL 3, ON WHETHER THE TWO MEMBERS ARE DISTINCT.** I offered `ω∈ω2` where
`⟨ sucV ω ∈ˢ ω2 ⟩` is wanted. Agda printed the two presentations side by side,
2 s: `(Lift ℕ) != (Σ ⟪ ⁅ ω , ⁅ ω ⁆s ⁆ ⟫ ...)`. **The refutation is not vacuous.**

**CONTROL 4, ON WHY ITEM 1'S PREDICATE MUST BE TRUNCATED.** I dropped the
truncation from `Reach`. Agda refused, 2 s:

```
error: [UnequalTerms]
Σ (sq α) (λ s → s .fst p ≡ c) !=< ∥ _A_36 ∥₁
when checking that the expression squash₁ has type
isOfHLevel 1 (Σ-syntax (sq α) (λ s → s .fst p ≡ c))
```

**THIS ONE CARRIES A ROUTE-LEVEL POINT.** The untruncated reachable set is NOT a
proposition, so `leastOf` does not apply to it. **Item 1's canonicity comes FROM
the truncation, and the same truncation is what makes the map blind to WHICH
witness supplied the value. That blindness is the flip.**

**CONTROL 5, ON THE DIGEST.** I offered the greedy recipe where a reader is
wanted. Agda refused, 2 s: `⟪ α ⟫ → hProp ℓ !=< Σ ⟪ α ⟫ (λ _ → ⟪ α ⟫)`. **THAT
IS THE ESCAPE, IN ONE ERROR MESSAGE.**

**CONTROL 6, ON THE TRANSPOSITION.** I kept precomposition and dropped its two
facts. Agda refused, 2 s: `b != τ0 a (...) (dec≡ α a b)`. **Precomposition alone
moves nothing. `τ-a` and `τ-b` carry the value.**

**CONTROL 7, ON READING B'S FAMILY.** I claimed the composite family is flip
closed. Agda refused, 2 s, on
`compT α D G ginj w .fst p ≡ compT α D G ginj w .fst (swap p)`. **With
`comp-not-flip-closed` green beside it: probe A does not reach reading B, and
probe B is not redundant.**

**CONTROL 8, ON THE PRECOMPOSED MAP.** I dropped `σinj`. Agda refused, 2 s:
`σ x != x`. **The family is closed under an INJECTIVE self-map only, which is why
the excluded middle is spent in probe B and not in probe A.**

## 8. WHAT REMAINS OF `[LJ-1.8]`'s BLOCKER, WITH ALL FOUR CANDIDATES SETTLED

**`[LJ-1.8]`'s blocker is that `[LJ-1.301]`'s descent concludes TRUNCATED**,
`dev/PLAN.md:68-72`. **`[LJ-1.321]` listed four candidate untruncations. They are
now all settled.**

| candidate | settled by | outcome |
|---|---|---|
| 1, the pointwise-least pairing | **THIS TASK** | **REFUTED, MEASURED, at both readings** |
| 2, a weakly constant endomap by another route | `[LJ-1.333]` | STATEMENT-LEVEL. Not refuted. The cheaper truncation makes its obligation strictly stronger |
| 3, the canonical injection at a limit | `[LJ-1.330]` | RETIRED |
| 4, the stage-cardinal transplant | `[LJ-1.332]` | RETIRED, circular |

**The four bands are UNCHANGED by me.** `[LJ-1.333]`'s table stands:
`agents/tasks/LJ-1-333/lj-1.333-report.md:315-320`. Only the non-initial limit
band is truncated, and `limit-truncated`
(`agents/tasks/LJ-1-332/ProbeLJ1332A.agda:196-204`) is where it sits.

**WHAT THIS TASK ADDS TO THE BLOCKER, and it is a narrowing rather than a
closing.**

1. **A whole recipe FAMILY is closed, MEASURED.** Every canonical pairing that
   reads only the values a witness family reaches at a pair is symmetric, so it
   is not injective. **A future brief must not propose another member of that
   family.** Least, greatest, first, or any other reader: they all die the same
   way, `reader-refuted`, `ProbeLJ1334A.agda:230-239`.
2. **The reason is a SYMMETRY, and it is now stated with a term.** The witness
   family carries an action of the carrier's self-injections
   (`Precomp`, `ProbeLJ1334B.agda:157-160`), the reachable set is invariant under
   that action, and a canonical reader inherits the invariance. **An injective
   pairing cannot be invariant.**
3. **SO THE MISSING INGREDIENT IS A SYMMETRY-BREAKING DATUM ON THE WITNESSES,
   and that is the digest's sentence with a proof under it.** `<_L` well-orders
   the INJECTIONS, which breaks the action. A well-order on the TARGETS does not.
   **`[LJ-1.329]` measured that this tree has 35 `SWO` instances and none with a
   function carrier**, so the datum is absent here.
4. **`[LJ-1.333]`'s named repair is untouched and still stands:** `ACBranch`,
   `agents/tasks/LJ-1-333/ProbeLJ1333A.agda:109-111`.

**WHAT I DID NOT SETTLE, and I name it rather than guess.**

- **The untruncation itself. NOT REFUTED. C-36 binds.** I refuted one candidate's
  two readings.
- **Whether a symmetry-breaking datum is derivable in this tree.** **NOT
  MEASURED**, and no Agda term can settle non-derivability.
- **Rows 3 and 4 of the band at `ω · 2`.** INFERRED, section 1.1.
- **The sweep (C-42).** No count claimed.
- **The landing cost.** Every second here is warm and this probe proposes nothing
  for landing.

## 9. DD4, STATED AND ANSWERED, WITH MY AXIS (C-46)

**DD4: maximize the code the two proofs share, and write it generic.** One rule,
two ends, no metric and no checker. DD4's own axis is AC against GCH, fixed in
code at `scripts/measure/ledger.py:50`.

**MY AXIS: does the term name a tower, a stage or a formula?**

**Answer: EVERY term in both files is TOWER-BLIND.**

- The files name `S`, `IsOrd`, ambient membership, `ω`, `sucV`, `+ω`, `⟪ ⟫`,
  `SWO` and `sq`. **They name no `Lset`, no `Formula`, no `𝒟ₒ` and no `⊨`.**
  **MEASURED by `grep`: zero occurrences of `Lset`, `Formula`, `𝒟ₒ` and `⊨` in
  either file.**
- **This is stronger than `[LJ-1.333]`'s answer**, whose PART 1 had to name
  `Lset` to measure the delivered descent. **Nothing here measures a descent, so
  nothing here needs a stage.**
- **THE GENERICITY IS REAL AND IT WAS NOT FREE.** The well-order is a HYPOTHESIS
  and not `OrdSWO`. The witness family is a HYPOTHESIS (`Precomp`) and not the
  band's own. **So one refutation covers every well-order and both readings, and
  it will cover a third reading if one appears.**

**THE BRIEF'S DD4 NOTE, ANSWERED HONESTLY.** The brief asks me to keep the leg's
property: take a POINT of a delivered injection type rather than a map out of
`sq α`. **I KEPT IT IN THE HALF THAT MATTERS AND I BROKE IT IN ONE PLACE, and I
say which.**

- **KEPT:** nothing here eliminates `∥ sq α ∥₁` into a non-proposition. The only
  eliminations are `PT.map` and `leastOf`, and `leastOf` eliminates into a
  proposition by `isPropLeastOf`.
- **BROKEN, ONCE, AND NAMED:** `flip-sq : sq α → sq α`
  (`ProbeLJ1334A.agda:109-113`) IS a map out of `sq α`. **It is an ENDOmap, it is
  applied under `PT.map`, and it is not `[LJ-1.329]`'s refuted object**, which
  was a map out of the ambient function type used to CANONICALIZE. **A natural
  operation on witnesses is not a canonicalizer**, and this one costs 4 lines.
- **MEASURED: I import no new module into either closure.** `L.Ordinal.StageArith`
  and `L.WellOrder.Base` are delivered chapters, and `LJ-1-319.SqIsSet` is a
  sibling probe.
- **INFERRED, and I mark it INFERRED:** this probe proposes nothing for landing,
  so it moves no ledger row. **The standing figure I quote comes from
  `ledger.py --brief` under my own hand: 32,474 lines over 94 masters, measured
  from HEAD.** The tool reports the endpoint REFUSED and the DD5 benchmarks NOT
  MEASURED, so I quote neither.

## 10. THE ABORT CRITERION, ANSWERED ROW BY ROW (D-1)

| the brief's row | outcome |
|---|---|
| **THE DIGEST ALREADY KILLS IT** | **NOT TAKEN, and I checked it FIRST as ordered.** The digest's COUNTEREXAMPLE is a different construction, section 2, and control 5 measures the difference. **The digest's next SENTENCE does cover item 1 and it is right, but it carries no proof for this recipe** |
| **IT ESCAPES THE DIGEST'S COUNTEREXAMPLE** | **TAKEN.** Section 2 says how |
| **IT BUILDS** | **NOT TAKEN.** I built item 1's MAP, which is canonical and total, and then measured that it is never injective. **`[LJ-1.8]`'s blocker is NOT gone** |
| **A WALL** | **NOT TAKEN.** No run passed 2 seconds. C-56 was obeyed, the untruncated control was written first, and it became a measurement |

**THE ABORT CRITERION WAS FIXED BEFORE THE RUN AND THE CHEAPEST CHECK RAN
FIRST.** I read `dev/literature/truncation-and-selection.md:305-320` before
writing a line of Agda, and section 2 was decided before probe A existed.

## 11. THE RULES THIS CHAIN EARNED, ANSWERED

- **C-36. A failed substitution is not a proof of impossibility.** **I refuted
  item 1 and nothing wider.** Section 5 draws the edge in both directions. **The
  untruncation is NOT refuted and I say so twice.**
- **C-42. A refutation measures the site it names.** I measured ONE candidate at
  TWO readings. **I ran no sweep and I claim no count.**
- **C-44. The brief warned about its own premise.** **The premise was TRUE this
  time**, and the false step was the inference drawn from it. **The warning still
  paid: checking it is what sent me to compare the two constructions.**
- **C-54. A truncation stall at a SET motive is a `2-Constant` obligation before
  it is a principle.** Item 1 IS a `2-Constant` construction and it compiles.
  **The stall is not the obligation. It is the INJECTIVITY of what the obligation
  produces**, and the law does not yet make that distinction.
- **C-56. Obeyed, and it produced a measurement.** Section 6.
- **D-10. Price the TRUTH of a recorded residue before pricing its proof.** I
  priced the premise first, section 1, before writing any map.
- **C-45. `exit 0` is not a supply.** Both probes are green and land nothing.
- **P-l.** I priced nothing by analogy. Section 6 marks every second warm. **In
  particular I did NOT carry `[LJ-1.333]`'s 2-second figures onto my own file: I
  measured mine.**
- **D-1.** Section 10.
- **C-12.** Section 6, eighteen runs, slot count 0 before each.

## 12. PROHIBITIONS, ANSWERED

- **Writes: `agents/tasks/LJ-1-334/` only**, three files: this report,
  `ProbeLJ1334A.agda` and `ProbeLJ1334B.agda`. Nothing in `src/`, nothing in
  `dev/`, no other task directory, no `.claude/`, no `AGENTS.md`.
- **I read the sibling probes and changed no line of them.** I IMPORTED
  `LJ-1-319.SqIsSet` rather than copying it, so it re-compiled under my own hand.
  **`git status --porcelain` lists my three new files and no modified tracked
  file.**
- **I did NOT re-derive what four siblings settled.** `[LJ-1.329]`'s refutation,
  `[LJ-1.330]`'s and `[LJ-1.332]`'s retirements and `[LJ-1.333]`'s
  statement-level verdict are cited, never repeated.
- **No commit, no push, no `make check`.** No `git checkout`, `stash`, `reset` or
  `clean`. **I ran no `git` command that writes.**
- **Agda: eighteen invocations, ONE process at a time.** `GHCRTS="-A64m -I0 -M8g"`
  on every run. Cap never raised.

## 13. ARCHIVE USED (DD18), ONE LINE READ PER FILE

- **`agents/tasks/LJ-1-333/lj-1.333-report.md`, READ WHOLE, as the brief
  ordered.** Line read `:192-195`: 「item 2 searches for a canonicalizer at
  exactly the ordinals where the tree's only canonicalizer is refuted by the
  band's DEFINITION, and not by an accident of proof or by a missing lemma」.
  **TOOK: the frame I had to escape, and I DID escape it. My refutation never
  touches `Init`'s fourth row and never touches `via-col-square`.** **So item 1
  did NOT die of section 3.2's mechanism.** It died of a symmetry that holds at
  every ordinal with two members, initial or not. **That is a genuinely different
  cause, and I mark it MEASURED.** I also took `:315-320`, the four-band table,
  unchanged into my section 8.
- **`agents/tasks/LJ-1-321/lj-1.321-report.md`, READ section 8 whole and section
  17.** Line read `:309-315`, item 1 as written: 「define `h (a , b)` as the
  LEAST `c : ⟪ α ⟫` for which some witness's composite sends `(a , b)` to `c`
  ... What stopped it: INJECTIVITY does not follow」. **TOOK: the exact statement
  of my target, INCLUDING the words 「some witness's composite」, which is why
  probe B exists.** Also `:535-537`, which asked for this term and priced it
  cheap.
- **`archive/dev/TASKS-archived.md`, SHAPE ONLY, never a claim.** Line read
  `:82` (L3.32-T47): 「Truncated square law at initial ordinals | DELIVERED」.
  **TOOK, SHAPE ONLY: the retired route also delivered this law TRUNCATED first,
  and at the INITIAL ordinals.** **WHAT WOULD NOT TRANSFER:** every figure in
  that row prices modules of a retired tower and its report lives in `_build/`,
  a temporary folder, so no figure of it is readable today and I quote none.
  **That row says nothing about a non-initial limit, which is my band, and
  nothing about a pointwise construction.**
- **`agents/tasks/archive/L3-32-T90/l3.32-t90-report.md`**, line read `:98`:
  「`ω·2`, in the tree's arithmetic `+ω ω` per `OrdBlocks:91-92`」. **TOOK,
  SHAPE ONLY: the reading of `ω · 2` as `+ω ω`, which I then re-measured against
  the LIVE `src/L/Ordinal/StageArith.lagda.md:40-42` and did not take on trust.
  The `OrdBlocks` module named there is a retired one and I did not open it.**

## 14. LITERATURE USED (DD18)

- **`dev/literature/truncation-and-selection.md`. IT BEARS, AND IT IS HALF RIGHT
  ABOUT ITEM 1.** READ `:287-320` whole, as the brief's SCOPE ordered, before any
  Agda.

  **Line read `:311-316`**, quoted in full in section 2. **THE SPLIT:**

  - **The counterexample, `:312-314`: DOES NOT REACH ITEM 1, MEASURED.** 「the
    greedy construction that sends each element to the least unused target fails
    at order type `ω · 2` into `ω`」. **A different recipe with a different
    failure mode.** Control 5 puts the difference in an error message. **This is
    the brief's own abort criterion and it does not fire.**
  - **The principle, `:314-316`: REACHES ITEM 1 AND IS CORRECT.** 「A canonical
    injection needs a well-order on the INJECTIONS ... and what an ambient
    function type does not have」. **Item 1 well-orders the TARGETS. Sections 3
    and 4 measure that this is exactly not enough, and section 8 states why: a
    well-order on the targets does not break the symmetry that the witness family
    carries.** **The digest asserts this. This probe proves it at one site.**

  **Line read `:297-300`, the digest's own checklist item 4:** 「Does `A`
  decompose as an index over a well-order plus a PROPOSITION-valued payload? Then
  `leastOf` applies」. **MEASURED against item 1: it DOES decompose that way, the
  payload IS proposition-valued by the truncation, and `leastOf` DOES apply.**
  `item1-h` is green. **So checklist item 4 FIRES here and it is not enough: it
  produces a map, and the map is not injective.** **That is a gap in the
  checklist and I state it as such:** the checklist prices whether a map can be
  DEFINED. It says nothing about whether the map has the property the deliverable
  needs. **Control 4 is the evidence, and section 8 item 1 is the consequence.**

  **WHY NOT re-fetched:** the digest carries the theorem numbers and the library
  path, and I take statement-level facts only.

- **Kraus, Escardo, Coquand and Altenkirch, Theorem 16. NOT FETCHED, and WHY
  NOT:** `[LJ-1.333]` compiled the criterion with the delivered eliminator at
  `agents/tasks/LJ-1-333/ProbeLJ1333A.agda:171-173`, and my question is not
  whether a `2-Constant` map exists. **Item 1's map IS canonical, MEASURED
  (`item1-canonical`). The failure is downstream of the criterion.**

- **Jech 13, Schindler and Zeman, Devlin. NOT READ, and WHY NOT:** they price the
  classical construction, which goes through the initial ordinal and through
  `<_L`. **My section 8 item 3 says the same thing the digest says about `<_L`,
  and a source cannot settle whether ONE map in THIS tree is injective. The type
  checker settles that.**

## 15. CHECKS RUN

- `GHCRTS="-A64m -I0 -M8g" agda agents/tasks/LJ-1-334/ProbeLJ1334A.agda`: exit 0,
  2 s.
- `GHCRTS="-A64m -I0 -M8g" agda agents/tasks/LJ-1-334/ProbeLJ1334B.agda`: exit 0,
  2 s.
- `.venv/bin/python scripts/gate/lint-agda.py --check` on both probe files: exit
  0.
- `.venv/bin/python scripts/gate/lint-prose.py --check` on this file: recorded in
  section 16.
- `.venv/bin/python scripts/gate/check-probes.py`: **clean, no probe outside
  `agents/tasks/` and no generated file.**
- `.venv/bin/python scripts/dispatch/rules.py --for probe`: run, every statement
  read. **I opened the full `dev/LESSONS.md` entry for D-1, C-42, C-12 and P-l.**
- `.venv/bin/python scripts/measure/ledger.py --brief`: run under my own hand, and
  section 9 quotes it and nothing else.
- MEASURED: no em dash in any of the three files I wrote, by `grep -c`, 0 in all
  three.
- MEASURED: `grep -c "postulate\|TERMINATING\|{!\|trustMe"` on both probe files:
  0. Both are `--safe` with no hole and no postulate.
- MEASURED: both probe files are byte-identical to their last GREEN form except
  for the added negative-control comment blocks, by `diff` against a copy taken
  at the green run. **No line of any term changed after its green run.**
- **Every `ProbeLJ1334A.agda:<line>` and `ProbeLJ1334B.agda:<line>` citation in
  this report was re-verified against the files after my last edit.**

## 16. LINT AND TREE STATE

- `.venv/bin/python scripts/gate/lint-agda.py --check agents/tasks/LJ-1-334/ProbeLJ1334A.agda agents/tasks/LJ-1-334/ProbeLJ1334B.agda`:
  exit 0.
- `.venv/bin/python scripts/gate/lint-prose.py --check agents/tasks/LJ-1-334/lj-1.334-report.md`:
  exit 0.
- `.venv/bin/python scripts/gate/check-probes.py`: clean.
- `git status --porcelain`: **my three new files only.** No tracked file is
  modified.
