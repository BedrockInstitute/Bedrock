# Review of `descent-from-internal`

The obligation `descent-from-internal` is not inhabited. This file is the
obstruction, for the branch `no-go-stated`.

## THE STATEMENT, AS THE BRIEF NAMES IT

```
descent-from-internal :
    (x : V ℓ) → IsOrd x → ⟨ ω ∈ˢ x ⟩
  → ((y : V ℓ) → ⟨ y ∈ˢ x ⟩ → IsOrd y → (⟨ y ∈ˢ ω ⟩ → Empty.⊥) → sq y)
  → sq x
```

Exact type used: `agents/tasks/LJ-1-427/Probe427.agda:99-102`. Generic
in `x`. No band. No cardinal. No numeral except `ω`. I did not inhabit
it. I did not weaken it in Agda. I did not smuggle an ordinality
hypothesis.

`coded-to-arrow` and `internal-nonempty` are module parameters at the
types their briefs name (`Probe427.agda:87-96`). `[LJ-1.424]` and
`[LJ-1.425]` have not run in this tree. Neither report exists. Neither
is NO-GO. Neither names its statement FALSE.

## VERDICT

**NO-GO.** The ambient least cardinal carries `IsOrd` by construction.
The internal least cardinal does not. The induction needs an ordinal
at that position twice. The tree does not deliver one from
`internal-nonempty`.

This is not a claim that `δᴸ` is never an ordinal. It is a claim that
`InternalLeastCard.Good` does not ask for ordinality, and that
`mem-ord` does not apply to a member of `Lset β`.

## D-10. THE TARGET IS NOT DELIVERED AS AN ORDINAL

W3, first. The type `IsOrd (fst δᴸ)` is well-formed
(`Probe427.agda:74-76`). The body is a hole. Agda reports
`UnsolvedInteractionMetas` at `Probe427.agda:76`
(`runs/w3-recheck-2.out:2`). The only other hole is the obligation
itself (`:103`).

What the ambient target carries, at `file:line`:

    oκ : IsOrd (fst κ)
    oκ = mem-ord {A = sucV (fst α)} (suc-ord oα) (fst κ)
           (member (sucV (fst α)) γ-card)

Cite: `src/L/Cardinal.lagda.md:125-127`. `κL` is a member of
`sucV (fst α)`. That container is an ordinal. `mem-ord` applies.

What the internal target carries, at `file:line`:

    Good : Mem (Lset β) → hProp (ℓ-suc ℓ)
    Good δ = (∥ Σ[ F ∈ Mem (Lset β) ] InjCode (up F) κ (up δ) ∥₁) , squash₁

    δᴸ : S
    δᴸ = up δ-card

Cite: `src/L/Cardinal.lagda.md:239-240` and `:253-254`. `δᴸ` is a
member of `Lset β`. `Good` asks for a truncated coded injection. It
does not ask for `IsOrd`.

`Lset-out` says a member of `Lset α` is merely a member of
`𝒟ₒ (Lset δ)` for some `δ ∈ α` (`src/L/Constructible.lagda.md:336-337`).
That is a definable subset, not an ordinal.

The two uses that need an ordinal:

1. Trichotomy. `ord-tri` takes `IsOrd` on both arguments
   (`src/L/Ordinal/Linear.lagda.md:136`). `[LJ-1.421]` splits with
   `ord-tri (fst κ) oκ (fst a) oa`
   (`agents/tasks/LJ-1-421/Probe421.agda:185`).
2. Init. The first conjunct is `IsOrd α`
   (`src/L/Ordinal/SquareLaw.lagda.md:693`). `[LJ-1.406]` fills it
   with `κoL` (`agents/tasks/LJ-1-406/Probe406.agda:187`).

Both break if the descent target is `δᴸ`.

## CORRECTED `Good`

The descent needs `Good` to carry an ordinality conjunct. One
corrected predicate is:

    Good δ = ( ∥ Σ[ F ∈ Mem (Lset β) ] InjCode (up F) κ (up δ) ∥₁
             × IsOrd (fst (up δ)) )

`[LJ-1.403]` already measured a stronger correction `Good⁺`, which
adds membership in `κ` and infiniteness
(`agents/tasks/LJ-1-403/Probe403.agda:46-52`). Membership in an
ordinal `κ` would give `IsOrd` by `mem-ord`. That is a different
object: the least member of `Lset β` that is also a member of `κ`
and infinite, not the least member that merely admits a code.

Adding a conjunct changes which `δ` is least. I did not inhabit
the original `δᴸ` by smuggling `IsOrd` as a hypothesis.

## THE SECOND QUESTION, SEPARATE

`init-at-kappa` spends `κ-min-atL`
(`agents/tasks/LJ-1-406/Probe406.agda:116`,
`src/L/Cardinal.lagda.md:140-141`): no member of `κ` by `∈` admits
an ambient truncated injection from `α`.

`δ-min` (`src/L/Cardinal.lagda.md:261-263`) says something else:
no member of `Lset β` that is strictly below `δ-card` in
`orderAt` admits a code.

The second does not give the first. What is lost:

1. The comparison. `∈` on the ordinal versus the stage well-order.
2. The domain. Members of `κ` versus members of `Lset β`.
3. The forbidden witness. An ambient truncated injection versus a
   coded `Good`.

Even a corrected `Good` that delivered `IsOrd` would still not
close Init's fourth conjunct from `δ-min`. That is a second
obstruction, named here, not used as a universal negative.

## WHAT WAS NOT DONE

No axiom. No postulate. No module parameter that asserts
`IsOrd (fst δᴸ)`. `delta-is-ordinal` is the W3 fragment. It does
not typecheck. `descent-from-internal` is the named obligation.
It is not inhabited. No `kappa-arrow-data`. No `amb-to-coded`.
No `coded-descent`. No `IsCardinalL`.
