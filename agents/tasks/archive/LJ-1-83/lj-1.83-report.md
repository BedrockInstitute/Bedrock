# LJ-1.83: supply the code set and its decomposition facts

Status: COMPLETE. Written incrementally per C-22. No commit, no push.
ASD-STE100. This report is `_build/lj-1.83-report.md`.

## 0. THE VERDICT

**`C`, `compK` and `unCompK` ARE supplied, at the stage.** The code set
is the stage's own bound: `C = K`. The facts are the stage's
transitivity applied to the nested Kuratowski pair. `ShapesAgree` is
fully instantiated, and the chain moves past it through `ShapedAgree`
and `ClosedAgree`, all green in `src/ProbeLJ183A.agda`.

**The chain stops at `WitnessAgree`'s `witK`.** That module's telescope
carries the fact "every witness code set lies in the K-slot"
(`src/L/Condensation.lagda.md:6227-6229`). No stage datum and no
delivered lemma supplies it. It is the next obligation, and it is
independent of the choice of `C`: at the `WitnessAgree` frame the code
set is the witness `w`, bound inside the existential, and the `C`
parameter is gone.

## 1. THE CODE SET `C` AND WHY THE CONSUMERS ACCEPT IT

**The value is `C = K`** (`src/ProbeLJ183A.agda:175-176`), where `K =
LsetS lam ordλ` is the stage's own bound, exactly the `K` of the stage
`KFacts` value (`src/ProbeLJ180A.agda:41-43`).

The consumers state their requirements at these lines, and each is
met:

| consumer | what it requires of the code set | where met |
|---|---|---|
| `ShapesAgree` (`src/L/Condensation.lagda.md:5816-5835`) | `compK`, `unCompK`: a code in `C` of shape `pr N (pr #k (pr a b))` or `pr N (pr #k a)` has its components in the K-slot | `compK` at `ProbeLJ183A.agda:74-110`, `unCompK` at `:112-136` |
| `ShapedAgree` (`:6198-6212`) | `codesK`, `unCodesK` at its `C` slot | the `C` slot and the `K` slot are both `suc K₀`, whose value is the stage's `K`; `codesK15 = compK` (`:205-211`) |
| `ClosedAgree` (`:6098-6110`) | `codesK`, `unCodesK`, and `entryK`: a pair in `C` has its components in the K-slot | `entryK` at `:138-146`; slot identity as above (`:220-224`) |
| `WitnessAgree` (`:6224-6239`) | no `C` at all: `witK`, `codesK w`, `unCodesK w`, `entryK w` at an arbitrary witness `w` | `witK` is the next blocker (section 4) |
| `SatGraphAgree` (`:6476-6512`) | the facts at the graph frame's witness `d`, env slot 2 | downstream of `WitnessAgree`; same witness-in-K content |

This is the D-30 reading. The consumers state only decomposition
facts about the code set. `C = K` makes the decomposition free: a
member of `K` with a code shape has its components in `K` by
transitivity. No consumer requires `C` to be a particular code set
such as the delivered `AllCodes` (`src/L/Coding/CodeSet.lagda.md:
434-461`); that object is the code set of a carrier at the real
instantiation, where the per-site content (section 4) lives.

The alternative `C = AllCodes` was considered and rejected for this
probe: its decomposition facts would need `AllCodes ⊆ K`, a code-depth
content fact, while `C = K` needs none. The choice does not change
where the chain stops, because `witK` is about witnesses, not about
`C` (section 4).

## 2. THE FACTS `compK` AND `unCompK`

**The core is generic over any transitive set.** `module CodeFacts
(T : V) (transT : ...)` (`src/ProbeLJ183A.agda:60`) supplies
`compK`, `unCompK` and `entryK` at `T`, from `transT` alone. The
membership chains are:

- `compK`: `N` is two steps down from the code (`N ∈ {N} ∈ c`), `a`
  and `b` are six steps down (`a ∈ {a,b} ∈ pr a b ∈ {#k, pr a b} ∈
  pr #k (pr a b) ∈ {N, pr #k (pr a b)} ∈ c`). Each step is one
  transitivity application (`:81-110`).
- `unCompK`: `N` two steps, `a` four steps (`:118-136`).
- `entryK`: `x ∈ {x} ∈ pr x y`, `y ∈ {x,y} ∈ pr x y`, two steps each
  (`:138-146`).

The base membership lemmas are the delivered singleton and pair
classifications (`∈sgl-intro`, `∈pair-introL`, `∈pair-introR`,
`src/L/Coding/Base.lagda.md:88-107`). The transitivity is the stage's
own (`layer-trans (Lset-layer lam)`, `src/L/Constructible.lagda.md:
183` and `:246`), instantiated at `T = fst K`
(`src/ProbeLJ183A.agda:179-181`). This is the same route `arityK`
took (`src/ProbeLJ180A.agda:173-175`).

At the 15-element chain frame, the K-slot and the code-set slot are
the same slot, `suc K₀`, whose value is definitionally the stage's
`K` (`lookup (suc K₀) (c ∷ γ) ≡ K`). So `codesK15`, `unCodesK15`
and `entryK15` are definitionally the generic facts
(`src/ProbeLJ183A.agda:205-224`).

## 3. HOW FAR THE CHAIN REACHED

The probe instantiates, all green at the C-12 cap:

| module | application | probe lines |
|---|---|---|
| `ShapesAgree {14}` | `S1` with `C`, `compK`, `unCompK` | `:194-197`, forced at `:199-200` |
| `ShapedAgree {15}` | `SA` with `codesK15`, `unCodesK15` | `:227-230`, forced at `:232-233` |
| `ClosedAgree {15}` | `CA` with `codesK15`, `unCodesK15`, `entryK15` | `:236-240`, forced at `:242-243` |

The KFacts value is `f1 c = KFactsCons ... kfacts`
(`src/ProbeLJ183A.agda:185-189`), the same extension the chain needed
in `[LJ-1.82]`.

Two swap controls confirm the applications are genuinely elaborated.
Swapping `compK` and `unCompK` in `S1` fails at the `compK` position.
Swapping `codesK15` and `unCodesK15` fails at the `codesK` position
of `ShapedAgree` and `ClosedAgree` (section 8).

## 4. THE NEXT BLOCKER

**`WitnessAgree`'s `witK`** (`src/L/Condensation.lagda.md:6227-6229`):

```agda
(witK : (w : S) → ⟨ (w ∷ γ) ⊨ ((var (suc x) ∈̇ var zero)
             ∧̇ (closedAt zero ∧̇ shapedAt zero (suc A))) ⟩
         → ⟨ fst w ∈ fst (lookup K γ) ⟩)
```

At the stage frame this states: every closed, shaped code set over
the carrier `A = Lset α`, containing the formula code `x`, is a
member of `Lset lam`.

**The term that cannot be written is `witK` at the stage.** The
witness `w` is bound inside `hasWitnessAt`, so no choice of the
ShapesAgree-level `C` reaches it. The stage's seven parameters
(`src/ProbeLJ183A.agda:149-156`) and the twenty-nine `KFacts` fields
(`src/L/Condensation.lagda.md:5737-5768`) name only the stage's
closure: `A`, `K` and the twelve numerals. Nothing names a witness.
`witK` appears in the tree only as module parameters (`:6227`,
`:6509`, `:6714`); no definition supplies it. MEASURED by search.

What the stage would have to provide: a rank bound for the specific
code set at the site, its constructibility below `lam`. That is the
real condensation content, in the same class as the `levelIn` and
`cover` hypotheses (`src/L/BoundedSubset.lagda.md:916-917`).

The other `WitnessAgree` facts (`codesK w`, `unCodesK w`, `entryK w`)
are not the blocker: each follows from `witK w` plus the generic core,
because `c ∈ w ∈ K` gives `c ∈ K` by transitivity, and then the core
decomposes. So `witK` alone is the missing constructor.

## 5. THE DD4 ANSWER

**The supply is generic in the stage.** The code facts are stated at a
variable transitive set `T` with a variable transitivity witness
(`src/ProbeLJ183A.agda:60`); no concrete set body enters any type.
The L stage instantiates `T = fst K` with
`layer-trans (Lset-layer lam)` (`:179-181`). The J tower supplies its
own `T` and its own transitivity through the same module, exactly as
it supplies its own stage closure.

`C = K` is the canonical choice at any stage: the decomposition facts
are the stage's transitivity, so re-instantiation is nearly free. The
per-site content that is NOT generic is `witK`: the witness-in-bound
fact is each tower's own condensation content.

## 6. NEGATIVES AND THEIR STATUS

1. "`C`, `compK` and `unCompK` are supplied at the stage":
   **MEASURED TRUE**. The probe checks green at the C-12 cap
   (section 8).
2. "`ShapesAgree` is fully instantiated": **MEASURED TRUE**.
   `S1` applies with no hypothesis left (`:194-197`); the swap
   control fails, so the application is elaborated.
3. "The chain moves past `ShapesAgree`": **MEASURED TRUE**.
   `ShapedAgree` and `ClosedAgree` instantiate green (`:227-243`).
4. "The next blocker is `WitnessAgree`'s `witK`": **MEASURED**.
   The telescope carries `witK` as a parameter
   (`src/L/Condensation.lagda.md:6227-6229`), and no delivered term
   supplies it anywhere in `src/`.
5. "No stage datum can supply `witK`": **INFERRED**. The stage data
   constrain only the stage's closure, and no delivered lemma bounds
   witnesses below `lam`. This negative sets no verdict on its own;
   negative 4 carries the verdict.
6. "`C = K` makes the consumers unusable" (the D-30 defect the brief
   names): **MEASURED FALSE** for the modules reachable from
   `ShapesAgree`. `ShapedAgree` and `ClosedAgree` instantiate green.
   The next blocker is `witK`, which no choice of `C` fixes, because
   `WitnessAgree` has no `C` parameter (`:6224`).

## 7. ARCHIVE USED

- `src/ProbeLJ182A.agda`, read WHOLE. TOOK the frame arities, the
  `f1`/`f3` cons values (`:67-101`) and the `First` telescope
  (`:104-124`), which this probe fills.
- `src/ProbeLJ180A.agda`, read WHOLE. TOOK the stage `kfacts`
  (`:186-226`), `K = LsetS lam` (`:41-43`), and the transitivity
  route at `arityK` (`:173-175`), which `compK` copies.
- `src/L/Condensation.lagda.md`, read the telescopes and records:
  `ShapesAgree` (`:5815-5835`), `ClosedAgree` (`:6098-6110`),
  `ShapedAgree` (`:6198-6212`), `WitnessAgree` (`:6224-6246`),
  `SatGraphAgree` (`:6476-6512`), `KFacts` (`:5737-5768`),
  `KFactsCons` (`:5777-5814`). TOOK the exact consumer requirements
  on `C`.
- `_build/lj-1.82-report.md`, read WHOLE. TOOK the blocker location:
  `ShapesAgree`'s code-set datum was the first unsupplied hypothesis.
- `_build/lj-1.81-report.md`, read WHOLE. TOOK the site reading: the
  `K` slot is the bound, never the hull.
- `_build/lj-1.79-report.md`, read WHOLE. TOOK the guarded closure
  forms and the supply-point table.
- `dev/LESSONS.md`, read C-38 as extended (`:3427-3520`), C-35
  (`:3200-3242`), C-36 (`:3284-3332`), D-29 (`:3242-3284`), D-30
  (`:3332-3380`), whole. TOOK the discharge standard and the
  price-what-the-consumer-needs rule.
- `archive/rud-route/`, SHAPE only (`README.md`). Took nothing. WHY
  NOT more: the code-set supply is not a rud-route question, and the
  brief forbids taking a price from the retired route.

Also consulted: `src/L/Coding/Base.lagda.md:88-107` (singleton and
pair classifications), `src/L/Coding/CodeSet.lagda.md:441-470`
(`AllCodes`, the delivered code-set object, checked as the
alternative `C`), `src/L/Constructible.lagda.md:183,246`
(`layer-trans`, `Lset-layer`), `src/V/Coding.lagda.md:175-176`
(`pr`), `src/L/Coding/Descent.lagda.md:66-70` (the same singleton and
pair lemmas in rank form, not used).

## 8. GATES

- `scripts/check-fences.py --check`: clean, **87 masters**.
- `scripts/lint-prose.py --check` on `src/ProbeLJ183A.agda` and this
  report: exit 0.
- `scripts/lint-agda.py --check` on `src/ProbeLJ183A.agda`: exit 0.
- `src/ProbeLJ183A.agda`: GREEN at the C-12 cap, one process at a
  time. 1.61 s user, 2.51 s wall on the final run. Load average
  during the runs: 3.28 / 4.89 / 6.36 (1, 5, 15 minutes), four
  users. The machine was NOT quiet.
- The swap controls: `compK`/`unCompK` reversed in `S1` fails at
  `src/ProbeLJ183A.agda:194-197`; `codesK15`/`unCodesK15` reversed
  fails at `:227-240`. Both exit nonzero with a type mismatch.
  MEASURED. The control copies were removed after the check.
- Process discipline: this agent ran one `agda` invocation at a
  time. Process listing is denied by the sandbox (`ps` and `pgrep`
  return "operation not permitted"), so the one-process rule is
  enforced by sequential single invocations, not by observation.
- Masters: all green or untouched. `git status` is clean; the probe
  and this report are gitignored (`.gitignore:2`, `.gitignore:22`).
  HEAD `30f4fc8` on `two-tower-bridge`, unchanged.
- No `make check`. No commit, no push.

## 1. THE CODE SET `C` AND WHY THE CONSUMERS ACCEPT IT

TODO.

## 2. THE FACTS `compK` AND `unCompK`

TODO.

## 3. HOW FAR THE CHAIN REACHED

TODO.

## 4. THE NEXT BLOCKER

TODO.

## 5. THE DD4 ANSWER

TODO.

## 6. NEGATIVES AND THEIR STATUS

TODO.

## 7. ARCHIVE USED

TODO.

## 8. GATES

TODO.
