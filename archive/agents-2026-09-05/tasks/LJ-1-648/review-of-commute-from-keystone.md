# review-of-commute-from-keystone: a STATED NO-GO

## HEAD
head_slot: coder
machine: shared
agda_tier: wide
task: LJ-1.648
obligation: agents/tasks/LJ-1-648/Probe648.agda::commute-from-keystone
verdict: **NO-GO. The keystone does not produce clause (iii)'s commute,
and the fourth debt `[LJ-1.641]` said does not exist is real, is named,
and was already dispatched at `[LJ-1.489]`.**

The obligation term is NOT written. The witness meter reads
`1 UNRESOLVED of 1, 3.34 s, probe_red=False`
(`agents/tasks/LJ-1-648/runs/meter-obligation.out:2`). The probe is
green and carries no hole: `runs/p-final.out:EXIT=0`. Twenty other
delivered names meter `0 UNRESOLVED of 20`
(`runs/meter-names.out:21`).

**THIS IS NOT A REFUTATION OF `Commute`.** I did not build a term of its
negation, and I do not claim one exists. `Commute` is a true statement
about the real hull. What is refuted is the ROUTE the brief priced: that
`[LJ-1.646]`'s keystone is what produces it.

---

## 1. WHAT THE KEYSTONE IS, MEASURED AND NOT ASSUMED

`LsetCodeOrd` (`Probe648.agda:160-163`) is the type verbatim from
`[LJ-1.462]`'s D-10 correction (`agents/tasks/LJ-1-462/Probe462.agda:118-121`),
which is the source `dev/pod/queue.toml:6207` cites for the keystone.

Two green terms make a round trip:

- `keystone-closure` (`Probe648.agda:203-204`): the keystone closes the
  hull under `Lset` at ordinals.
- `closure-keystone` (`:210-213`): that closure gives the keystone back.

**So the keystone IS `HullClosedLset` at ordinals, up to the truncation
`[LJ-1.647]` measured to be free** (`hull-closed-lset∥`,
`agents/tasks/LJ-1-647/Probe647.agda:171-173`). The round trip costs no
formula and no search, because hull membership IS "is the value of a
code" (`src/L/Hull.lagda.md:337-339`, where `hull-member`'s proof is its
own argument).

## 2. AND `[LJ-1.477]` ALREADY RULED THAT OUT, AT THIS EXACT SITE

`agents/tasks/LJ-1-477/lj-1.477-report.md:308-310`:

> - Do not take `HullClosedLset` as a way to close `JoinSteps`.
>   Closure of the hull under `Lset` does not change `step` or
>   `LsetStep`.

That report's next bullet (`:311-316`) names what is needed instead:

> - A proof of the commutation at this site needs more than the two
>   laws: it needs `π` to commute with `𝒟ₒ`, and it needs
>   `Lset-out` witnesses to lie in `M`. ... Those needs
>   are elementarity plus the level formula, which is step 3, or they
>   are the collapse-image route that same report measured.

**Elementarity plus the level FORMULA.** The keystone is neither. It is
the formula's OUTPUT, a code map, and section 1 measures that this
output is exactly the closure `[LJ-1.477]` told the pod not to spend
here.

## 3. THE THREE GAPS, TAKEN ONE AT A TIME

The brief's premise 2, from `agents/tasks/LJ-1-641/lj-1.641-report.md:156`,
is that all three gaps ask for "a hull member picked out by a condition
naming `Lset` or `𝒟ₒ`". That reading is right once, half right once, and
wrong once.

**`IndexInHull`: THE READING IS RIGHT, AND THE KEYSTONE IS STILL THE
WRONG OBJECT.** `RankInHull` (`Probe648.agda:365-370`) is that gap with
`𝒟ₒ` and the stray `β` both removed, and `index-from-rank` /
`rank-from-index` (`:372`, `:376`) are an equivalence. What is left is
one sentence: a hull member of `Lset δ` has a level index inside the
hull. That is a SEARCH, its condition names `Lset`, and the hull's only
search rule is `hull-closed` (`src/L/Hull.lagda.md:415`), which takes a
`Formula Code 1`. **A code map is not a search.** The hull was built as a
least-witness search from the start (`archive/dev/LJ-dispatch-index.md:43`:
"| LJ-1.3 | Build: the Skolem hull, a least-witness search over the order |").
So this gap wants the keystone's INPUT, the `Formula Code 1` that names
`Lset`, and not the keystone's output.

**`DefFwd`: THE READING IS WRONG. NO HULL MEMBER IS ASKED FOR AT ALL.**
Its conclusion is `⟨ HS.C.π y ∈ˢ 𝒟ₒ (Lset (HS.C.π β)) ⟩`
(`agents/tasks/LJ-1-641/Probe641.agda:214`): one membership, no
existential, no `∈ˢ HS.M` anywhere on the right of the arrow. No closure
rule of any kind can be its producer, because there is nothing for a
closure rule to produce.

**`DefBwd`: THE SHAPE FITS AND THE LANGUAGE DOES NOT.** It does ask for a
hull member (`Probe641.agda:220-221`), but the condition on that member
includes `HS.C.π y ≡ z`. `hull-closed` answers a `Formula Code 1`
interpreted in `Lset lam`; `π` is a meta-level function `S → S`
(`src/V/Collapse.lagda.md:53`) and is not a term of that language. **No
formula expresses this condition**, so `hull-closed` cannot answer it
whatever formula is supplied.

## 4. THE TWO DEFINABILITY GAPS ARE THE OBLIGATION ITSELF

This is the measurement, and it is green.

- `𝒟-at-level` (`Probe648.agda:84`): `𝒟ₒ (Lset β) ≡ Lset (sucV β)`, from
  `Lset-suc` (`src/L/Axioms/Basic.lagda.md:196`), unconditionally.
- `π-sucV` (`Probe648.agda:230`): `HS.C.π (sucV β) ≡ sucV (HS.C.π β)` at
  any hull member `β`.
- `CommuteAtSuc` (`:288-291`) is the obligation's own conclusion read at
  `δ := sucV β` and rewritten by those two, and
  `commute-at-suc-is-an-instance` (`:336-343`) derives it from `Commute`
  and the three side conditions `Commute` itself carries.
- `fwd-from-commute-suc` (`:293`), `bwd-from-commute-suc` (`:298`) and
  `commute-suc-from-def-gaps` (`:303`) are an EQUIVALENCE between
  `CommuteAtSuc` and `DefFwdSuc × DefBwdSuc`.

**So `DefFwd` and `DefBwd` together are not below the obligation. They
are the obligation, at every successor of a hull member.** Anything that
produced them would prove clause (iii) there. A hypothesis that is
(section 1) exactly a closure property of `M` does not.

## 5. THE FOURTH DEBT, AND IT IS NOT NEW

`[LJ-1.641]`'s report says "SO THE COMMUTE IS NOT A FOURTH INDEPENDENT
DEBT. It is step 3's consumer." Sections 3 and 4 say it is, and name it:

> `piCommuteD : (y : S) → ⟨ y ∈ˢ M ⟩ → C.π (𝒟ₒ y) ≡ 𝒟ₒ (C.π y)`
> (`agents/tasks/LJ-1-489/lj-1.489-report.md:12`)

`[LJ-1.489]` is that dispatch and it returned a stated NO-GO
(`agents/tasks/LJ-1-489/lj-1.489-report.md:139-140`):

> **NO-GO at D-10 and at the join of `π-compute` with sealed `𝒟ₒ`.**
> The two sides cannot agree without elementarity.

`CommuteAtSuc` is `[LJ-1.489]`'s obligation restricted to `y := Lset β`.
That report also records, in its own list of what it did not settle
(`:354`), "It does not inhabit `HullClosedLset`" and (`:355`) "It does
not inhabit `lset-code`". **Neither would have helped it, and neither
helps here.**

Devlin does not commute the collapse with the stage operation either. He
transfers by elementarity: `dev/literature/devlin-II5.md:102`:

> The chain (c) to (q) then runs: for each ordinal γ of the collapse, the Σ₁

and concludes membership, not commutation, at `:106`:

> L_γ ∈ M for every γ < β, hence ⋃_{γ<β} L_γ ⊆ M (`dev2.txt:1200-1240`).

## 6. WHAT IS DELIVERED INSTEAD

`Residue = RankInHull × CommuteAtSuc` (`Probe648.agda:402-403`), and
`commute-from-residue` (`:405`) is the obligation from it.

`commute-from-keystone-and-residue` (`:411-412`) is the same term with
the keystone bound to an UNDERSCORE. **That underscore is the finding and
Agda checks it: no row of the assembly eliminates the keystone.**

The one place the keystone pays is `keystone-supplies-side` (`:426-433`):
it supplies `⟨ Lset (sucV β) ∈ˢ HS.M ⟩`, the third side condition of the
instance in section 4, from the first. It touches no gap.

## 7. WHAT THE NEXT BRIEF NEEDS

1. **`[LJ-1.646]` should deliver the FORMULA as well as the code map.**
   `RankInHull` needs `hull-closed` at a `Formula Code 1` naming `Lset`.
   `[LJ-1.462]`'s `feed` (`agents/tasks/LJ-1-462/Probe462.agda:101-102`)
   builds the code map from `LsetGraph` and a `Vec Code (countFo LsetGraph)`,
   and `[LJ-1.474]` delivered that vector. **The same two ingredients
   give the formula.** A brief that asks only for `Σ[ d ∈ Code ] ...`
   throws the ingredient away and keeps the part that this task measures
   to be insufficient.
2. **Do not re-dispatch `DefFwd` or `DefBwd` as separate objects.**
   Section 4 makes them one statement, and that statement is
   `[LJ-1.489]`'s stated NO-GO. Re-price THAT, at `y := Lset β`, where it
   may be easier than at a general hull member.
3. **`π-sucV` (`Probe648.agda:230`) is new, green, and needs no
   hypothesis.** `src/V/Collapse.lagda.md` may want it. This task's scope
   forbids `src/`.
4. **`[LJ-1.650]` should be re-read before it runs.** It takes the same
   keystone as a hypothesis. If its obligation contains a condition
   naming `π`, section 3's language argument applies there unchanged.
