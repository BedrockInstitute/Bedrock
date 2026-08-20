# Review of `bound-into-ord`

The obligation `upper-from-rank` is a hole. This file is the obstruction,
for the branch `no-go-stated`.

## THE STATEMENT, AS THE BRIEF NAMES IT

```
bound-into-ord :
    (α : S) → IsOrd α → (⟨ α ∈ˢ ω ⟩ → Empty.⊥)
  → (β : S) → IsOrd β → (⟪ Lset α ⟫ ↪ ⟪ β ⟫)
  → ⟪ β ⟫ ↪ ⟪ α ⟫
```

Exact type used: `agents/tasks/LJ-1-419/Probe419.agda:63-66`. Generic
in `α` and in `β`. No cardinal. No numeral except `ω`. I did not
inhabit it. I did not weaken it in Agda. `upper-from-rank` is a hole
at `:99`. Agda reports `UnsolvedInteractionMetas`
(`runs/hole-2.out`, exit 42, 0.96 s).

## D-10. THE TARGET IS FALSE AT THIS GENERALITY

The statement is: every ordinal `β` that `⟪ Lset α ⟫` injects into
injects back into `α`.

That is false. An injection into `β` does not stop an injection into a
larger ordinal. If `|Lset α| ≤ |β|` and `|β| < |γ|`, then
`⟪ Lset α ⟫ ↪ ⟪ γ ⟫` still holds and `⟪ γ ⟫ ↪ ⟪ α ⟫` fails as soon as
`|γ| > |α|`.

The brief's gloss (`LJ-1.419.md:78-81`) says the hypothesis on the
embedding avoids 「every ordinal injects into `α`」, which is false.
The written type still quantifies over every `β` that merely receives
an embedding from the stage. That class is unbounded above `|Lset α|`.
The pullback of every such `β` into `α` is the same false claim in
other clothes.

Classical cardinality: the implication

    ∀ β. |Lset α| ≤ |β| → |β| ≤ |α|

is equivalent to `|Lset α| ≤ |α|` only if `β` is a *tight* bound.
As a `∀ β` over arbitrary ordinals it is equivalent to: no ordinal
strictly larger in cardinality than `α` receives an injection from
`Lset α`. That fails as soon as `|Lset α| ≤ |α|` (the consumer) holds,
because then `Lset α` injects into every larger cardinal.

The consumer already wants `|Lset α| ≤ |α|`
(`src/L/StageCardinal.lagda.md:564-565`). The unrestricted residue
is therefore either false, or it restates the consumer and then
denies the stage its further embeddings.

**A residue that is false measures nothing.** D-10, `dev/LESSONS.md:1375`.

## THE CORRECTED TARGET, BESIDE THE ORIGINAL

Original: `bound-into-ord` as above, `∀ β`.

Corrected, tight:

```
bound-into-ord-tight :
    (α : S) → IsOrd α → (⟨ α ∈ˢ ω ⟩ → Empty.⊥)
  → (β : S) → IsOrd β
  → (⟪ Lset α ⟫ ↪ ⟪ β ⟫) → (⟪ β ⟫ ↪ ⟪ Lset α ⟫)
  → ⟪ β ⟫ ↪ ⟪ α ⟫
```

The extra arrow makes `β` a true bound of the stage, not a larger
ordinal. Under a bijection, `|β| = |Lset α|`, and the conclusion is
`|Lset α| ≤ |α|`. That is the consumer
(`src/L/StageCardinal.lagda.md:565`).

Corrected, rank-specific (the `β` that `[LJ-1.418]` returns, and no
other):

```
bound-of-rank :
    (α : S) → IsOrd α → (⟨ α ∈ˢ ω ⟩ → Empty.⊥)
  → let pack = stage-into-bound α oα
    in ⟪ fst pack ⟫ ↪ ⟪ α ⟫
```

`[LJ-1.418]` produces some ordinal, not `α`, and states no size bound
(this worktree has no `LJ-1-418/`; opened `agents/tasks/LJ-1-418/LJ-1.418.md:74-77`
in the main tree; this brief `LJ-1.419.md:73-75`). The delivered `β` is
`boundingOrd` of `[LJ-1.416]`'s ranks (`Probe417.agda:83-85`,
`Probe418.agda:66`).
If that `β` is the order type of the stage well-order, Mostowski gives
a bijection and this type is again `|Lset α| ≤ |α|`.

Neither correction is an independent residue. Both are the consumer,
or they spend the pairing that proves the consumer. See
`lj-1.419-report.md`, section `## THE TWO BILLS`.

## LITERATURE (W8), BEFORE ANY AGDA

Read, in this order: `dev/literature/j-hierarchy.md`,
`dev/literature/digest.md`, `dev/literature/devlin-errata.md`,
`dev/literature/devlin-II5.md`, `dev/literature/BIBLIOGRAPHY.md`.

**Does the classical argument bound the order type of a level by the
level's own ordinal?** Yes, under a pairing-closure condition, and
with a surjection for the general case.

- SZ 1.17 (`dev/literature/j-hierarchy.md:147-149`;
  `dev/literature/digest.md:241`): if `α` is closed under the Gödel
  pairing function, then `otp(<^A_α) = α`, and there is a `Σ₁`
  surjection `g : α → J_α^A`. For arbitrary `α` there is still a
  `Σ₁` surjection `h : α → J_α^A`, by Jensen 1972 Lemma 2.10.
- SZ p. 10 (`dev/literature/j-hierarchy.md:60`): `J_α ∩ On = α` for
  limit `α`, so `|α| ≤ |J_α|`.
- Devlin II.1.1(vii) (`dev/literature/devlin-II5.md:413`):
  `|L_α| = |α|` for `α ≥ ω`. Consumed at II.5.5 and II.5.6.

**What it spends:** Gödel pairing (for `otp = α`), or Jensen 2.10
(for a surjection `α → J_α` at an arbitrary `α`). The finite-sequence
surjection `[α]^{<ω} → J_α` plus pairing-closure of `α` is the same
spend. This tree does not form the order type
(`src/L/Ordinal/SquareLaw.lagda.md:10-11`).

The unrestricted residue is not an axiom. It is false. The tight
form is a theorem that spends pairing-closure. That is a condition
this tree does not currently meet: the pairing route is the open
wall (`agents/tasks/LJ-1-414/lj-1.414-report.md:20`).

`dev/literature/devlin-errata.md` inventories errors in Devlin I.9
and VI.1, not in II.1.1(vii) or II.5. No erratum kills the `|L_α| = |α|`
claim. The errata do not license taking an order-type identity from
Devlin without the pairing-closure hypothesis SZ states.

## WHAT WAS NOT DONE

No axiom. No postulate. No module parameter that asserts the
unrestricted residue as true. `from-two-hyps` shows the composition
under the two hypotheses. `upper-from-rank` is not inhabited.
