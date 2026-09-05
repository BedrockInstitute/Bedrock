# review-of-tfacts-value: NO-GO. `TFacts` HAS NO VALUE AT ANY FRAME

This file is the coder slot's channel for a NO-GO
(`dev/pod/instructions/coder.md`, the module-hypothesis clause). It does not
close the task. The critic reads it.

## THE VERDICT

**The obligation `agents/tasks/LJ-1-575/Probe575.agda::tfacts-value` is NOT
delivered, and it is not delivered because the type has no value.**

`record TFacts` (`src/L/Condensation/TwelveAgree.lagda.md:129-335`) is
uninhabited. Not at `KValue`'s frame only: at every frame, for every `n`, for
every choice of the fifteen indices and of `γ'`. The proof is
`agents/tasks/LJ-1-575/Probe575.agda:170-176`:

    tfacts-absurd : {n : ℕ}
        (N0 N1 N2 N3 N4 N5 N6 N7 N8 N9 N10 N11 t0 t1 K : Fin (5 + n))
        (γ' : S ^ (11 + n))
      → TFacts N0 N1 N2 N3 N4 N5 N6 N7 N8 N9 N10 N11 t0 t1 K γ'
      → Empty.⊥

It typechecks under `--safe`, with no hole, no `postulate` and no
`TERMINATING` (`runs/full-0.out`, exit 0).

I did not write `tfacts-value`. A term of that type must be a `postulate`, a
hole or a false claim, and the brief forbids all three.

## WHY THE FIELD IS FALSE

`tmValAt` is a DISJUNCTION (`src/L/Coding/Model.lagda.md:1701-1702`):

    tmValAt t e v = ∃̇ (tagAtL (suc t) 1 zero ∧̇ appAt (suc e) zero (suc v))
                  ∨̇ tagAtL t 0 v

The right disjunct says only `T ≡ pr (# 0) Val`. It asks for NO membership: not
of the value, not of the environment, not of the tag.

The tree's own honest form knows this. `Fact.tmValK`
(`src/L/Coding/EnvSupply.lagda.md:575-579`) takes TWO memberships, `eK` and
`tK`, and its `conCase` (`:589-592`) is exactly where `tK` is spent: from
`T ≡ pr (# 0) Val` and `T ∈ K` it reads `Val ∈ K` off `prK`. Without `tK`
there is nothing to read.

`TFacts.valV` (`src/L/Condensation/TwelveAgree.lagda.md:244-249`) quantifies
over the tag cell `a` and over the value cell `v`, and takes NEITHER
membership. So one instance refutes it: put the K slot itself in the value
cell, and `prʟ (numeralL 0)` of the K slot in the tag cell. The field then
returns `K ∈ K`, and `∈-irrefl` (`src/V/Hierarchy.lagda.md:155-156`) closes it.

## SIX FIELDS, THREE RECORDS, AND EACH ONE ALONE IS ENOUGH

| record | field | at | refuted at |
|---|---|---|---|
| `TFacts` | `valV` | `src/L/Condensation/TwelveAgree.lagda.md:244` | `Probe575.agda:175-176` |
| `TFacts` | `valW` | `:250` | `Probe575.agda:183-184` |
| `TFacts` | `wKfact` | `:256` | `Probe575.agda:191-192` |
| `LFacts` | `valV` | `src/L/Condensation/LowerAgree.lagda.md:179` | `Probe575.agda:204-205` |
| `LFacts` | `valW` | `:185` | `Probe575.agda:212-213` |
| `UFacts` | `wKfact` | `src/L/Condensation/UpperAgree.lagda.md:179` | `Probe575.agda:220-221` |

Each refutation is ONE projection off the master's own record fed to ONE shape
lemma (`Probe575.agda:92-157`). Nothing is restated. If a field's type ever
drifts from the shape, the line stops checking.

## WHAT THE REPAIR IS, AND IT IS SMALL

The three fields need their two memberships back, and that is all. No new
lemma. `Fact.tmValK` is already generic in the vector length and in the three
slots, so each repaired field is one application of it
(`Probe575.agda:363-386`). The repaired block is collected at `KValue`'s frame
at `Probe575.agda:388-410`, and `Ktr` is paid from the tree.

`statement-matches` (`Probe575.agda:352-361`) is Agda's word that the three
repaired types are the master's own weakened by the two restored memberships
and by nothing else. It can never be called, because its argument type has no
value. That is what it is here to certify.

## WHAT THIS DOES NOT SAY

- **It does not say the condensation leg is wrong.** It says three fact-block
  fields dropped a hypothesis their honest form carries.
- **It does not price the fix in `src/`.** The statement change is the
  mathematician's under AD3, and a measured cure does not transfer by analogy
  (`AGENTS.md:45`).
- **It does not measure the eleven module parameters that carry the same
  shape.** The sweep counts them (`lj-1.575-report.md`, `THE C-42 SWEEP`). I
  refuted the six record fields and no more.
- **It does not measure an APPLICATION.** `archive/dev/LJ-dispatch-index.md:137`
  records a green collection whose application heap-walled. I built no value
  and I applied nothing.
