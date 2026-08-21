# review-of-consK-exist-at-frame: the brief's literal target is FALSE

slot: `coder`, task `[LJ-1.510]`. This file states a NO-GO on the
statement the brief named, with `file:line`. The task's other half is a
GO and it is in `agents/tasks/LJ-1-510/lj-1.510-report.md`. Both are
true and neither replaces the other.

## WHAT WAS ASKED

> Build ONE term in `agents/tasks/LJ-1-510/Probe510.agda`:
>
>     consK-exist-at-frame : (TFacts's consK-exist, at KValue's frame)
>
> **or refute it and name the hypothesis it needs.**

The brief offers the disjunction. **The first disjunct is impossible and
the second is what this file delivers.** The obligation term that DOES
typecheck (`agents/tasks/LJ-1-510/Probe510.agda:277-282`) is the field
with one hypothesis restored, which is a weakening the brief did not
authorize in advance, so it is stated here as well as in the report.

## THE STATEMENT, AND WHY IT IS FALSE

`src/L/Condensation/TwelveAgree.lagda.md:317-321`:

    consK-exist : (ya yc a ar c E z x e' : S)
      → ⟨ (e' ∷ x ∷ z ∷ E ∷ ya ∷ yc ∷ a ∷ ar ∷ c ∷ γ') ⊨
            consAtL zero (suc zero) (suc (suc zero))
            ∧̇ (var zero ∈̇ var (suc (suc (suc (suc zero))))) ⟩
      → ⟨ fst e' ∈ fst (lookup (suc¹⁴ K) (x ∷ z ∷ E ∷ ya ∷ yc ∷ a ∷ ar ∷ c ∷ γ')) ⟩

`ya` is a bound variable of the field. **Nothing in the record, and
nothing in `KValue`'s frame, ties it to `K`.** The conclusion asks for
`e' ∈ K` and the only route to it from the membership atom `e' ∈ ya` is
transitivity of `K`, which needs `ya ∈ K`. The `consAtL` conjunct gives
`e'`'s SHAPE, not its location.

`no-yaK-is-not-a-theorem` (`agents/tasks/LJ-1-510/Probe510.agda:395-405`,
alias at `:407`) is the machine-checked counterexample, at `KValue`'s
frame and not at a generic one. Exit 0, full file median 4.44 s.
Its witness:

- `BB = sucʟ Lλ`, one cell above the bound, so `Lset lam` is a VALUE.
- `z` is the empty environment over `BB`, `e'` is `z` with the bound
  consed on. Both come from `envS` (`src/L/Coding/EnvSet.lagda.md:153-154`),
  where `fst (envS B g)` is `env` of the values DEFINITIONALLY.
- `consAtL-adequate` (`src/L/Coding/Model.lagda.md:1487-1498`) discharges
  the first conjunct with one `funExt`.
- `ya = sucʟ e'` discharges the membership atom by `self∈sucV`
  (`src/V/Model.lagda.md:236`).
- Then `e' ∈ Lset lam` would put `pr (# 0) (Lset lam)` in the bound by
  transitivity (`lookup-spec`, `src/L/Coding/Environment.lagda.md:102-104`),
  hence `Lset lam ∈ Lset lam` by `prK`
  (`src/L/Coding/EnvSupply.lagda.md:452-459`), refuted by `∈-irrefl`
  (`src/V/Hierarchy.lagda.md:155`).

## THE HYPOTHESIS IT NEEDS

    ⟨ fst ya ∈ fst (lookup (suc⁶ K) γ') ⟩

One membership. It **pins no slot**: `ya` is a bound variable, so nothing
fixes what occupies any cell of `γ'` and `[LJ-1.505]` is not pre-empted.

**IT IS NOT A NEW HYPOTHESIS. `src/` ALREADY TAKES IT.**
`src/L/Coding/EnvSupply.lagda.md:661-668` is the same field's honest form,
built by `[LJ-1.258]` and `[LJ-1.259]`, and its signature carries
`⟨ fst ya ∈ fst K ⟩` explicitly. Its whole body is
`consK-exist γ' ya yc a ar c E z x e' yaK h = Ktr (h .snd) yaK`
(`:667-668`). The same form appears again at `:742-748`. **The record
copied the conclusion and dropped the hypothesis.**

## THE CURE IS FREE AT THE CONSUMER, AND THAT IS MEASURED

`src/L/Condensation.lagda.md:4084` binds the existential clause:

    out h = λ c c∈ ar arK a aK yc ycK shB hc ya yaK E EK hsub henv →

`unFullAt` (`src/L/Condensation.lagda.md:689-698`) shows `ya` is bounded
by `var (suc (suc (suc (suc K))))`, so **`yaK` IS
`⟨ fst ya ∈ fst (lookup K γ) ⟩`**.

The call site is `src/L/Condensation.lagda.md:4062`, inside
`module Leaf (E ya yc a ar c : S)` (`:4023`), and `Leaf` is instantiated
at `:4096` by that same clause:

    module L = Leaf E ya yc a ar c

**`yaK` is in scope at `:4096`, bound twelve lines earlier at `:4084`
beside the very `ya` that is passed in.** So adding the hypothesis to the
record field (`:317-321`), to the telescope (`:4001-4005`) and to `Leaf`'s
parameters costs the consumer ONE extra argument that it is already
holding, at the one site that supplies it.

## THE SHAPE GOES FURTHER THAN THIS FIELD (C-42)

`dev/LESSONS.md:3752` says a refutation measures ONE site and never
measures how far the shape extends, so the COUNT comes before any cure.

| record | field | line | refuted here |
|---|---|---|---|
| `TFacts` | `consK-exist` | `src/L/Condensation/TwelveAgree.lagda.md:317` | YES, `Probe510.agda:395-405` |
| `TFacts` | `consK-forall` | `src/L/Condensation/TwelveAgree.lagda.md:322` | YES, `Probe510.agda:470-480` |
| `TFacts` | `consK-allin` | `src/L/Condensation/TwelveAgree.lagda.md:332` | YES, `Probe510.agda:494-504` |
| `UFacts` | `consK-exist` | `src/L/Condensation/UpperAgree.lagda.md:191` | no, same statement |
| `UFacts` | `consK-forall` | `src/L/Condensation/UpperAgree.lagda.md:196` | no, same statement |
| `UFacts` | `consK-allin` | `src/L/Condensation/UpperAgree.lagda.md:206` | no, same statement |
| telescope | `consK` (forall) | `src/L/Condensation.lagda.md:3889` | no |
| telescope | `consK` (exist) | `src/L/Condensation.lagda.md:4001` | no |
| telescope | `consK` | `src/L/Condensation.lagda.md:4183`, `:4817`, `:5070`, `:5199` | no |

**SIX RECORD FIELD POSITIONS AND SIX TELESCOPE POSITIONS CARRY THE
SHAPE, TWELVE IN ALL.** I refuted three, at one frame. I priced no cure
for the other nine, and this file does not.

`LFacts` (`src/L/Condensation/LowerAgree.lagda.md:95-225`) does NOT carry
the shape: grep count of `consK` there is **0**, and the fills at
`src/L/Condensation/TwelveAgree.lagda.md:478-481` belong to `uf : UFacts`
(`:445-446`), not to `lf : LFacts` (`:405-406`).

`consK-forall` and `consK-allin` need MORE than one membership: their
honest forms (`src/L/Coding/EnvSupply.lagda.md:631-645` and `:646-660`)
take four hypotheses each, an index function `g`, `fst z ≡ env g`,
`⟨ fst z ∈ fst K ⟩` and `⟨ fst x ∈ fst K ⟩`. **I did not check whether
those four are in scope at their consumers.** That is the next question
and I will not guess it.

## WHAT I DID NOT DO

I did not edit `src/`. I did not build `consK-forall` or `consK-allin`.
I did not build a `TFacts` value. I did not postulate. I did not use a
`TFacts` field to prove a `TFacts` field. I did not commit and I did not
push.
