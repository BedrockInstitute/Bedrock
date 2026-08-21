# Review of `residue-at-successor-446`

W3 does not typecheck. This file is the obstruction, for the branch
`no-go-stated`. The obligation is not a term.

## THE STATEMENT

```
residue-at-successor-446 :
    (γ : S) (oγ : IsOrd (fst γ)) (γ∉ω : ⟨ fst γ ∈ fst ωʟ ⟩ → Empty.⊥)
    (numerals : (k : ℕ) → ⟨ # k ∈ fst γ ⟩)
  → ⟨ fst (κC (sucʟ γ) (suc-ord oγ)) ∈ˢ fst (sucʟ γ) ⟩
```

`κC` is `[LJ-1.446]`'s coded selection (`Probe446.agda:194-195`).
It is not `[LJ-1.464]`'s.

## W3, THE SITE THAT DIES

`fits-446 : ⟨ CodedInjP' d ⟩` at `Probe465.agda:141-142`, with
`CodedInjP'` rebuilt from `Probe446.agda:158-160` at
`Probe465.agda:110-113`, and with `[LJ-1.460]`'s delivered type as
the module hypothesis `shift-coded` (`Probe460.agda:73-76`,
`Probe465.agda:64`).

Agda reports `UnequalTerms` at `Probe465.agda:158`:

```
fst F != fst IG.G of type V ℓ
when checking that the expression stage-mem (fst F) (snd F) has
type ⟨ fst F ∈ˢ Lset stgG ⟩
```

Exit 42 on three forced rechecks (`runs/w3-1.out`, `w3-2.out`,
`w3-3.out`). Class `other` (`UnequalTerms`,
`scripts/pod/facts.py:114`). No unsolved meta. No heap event.

## THE ONE DECLARATION THAT WOULD CLOSE THE CROSSING

```
place-shift :
    (γ : S) (oγ : IsOrd (fst γ))
    (F : S) (code : InjCode F (sucʟ γ) γ)
  → ⟨ fst F ∈ˢ Lset γB ⟩
```

where `γB` is 446's bound at `a := sucʟ γ`:
`bound2 β (sucV stgG)` for `G = InclGraph a a`
(`Probe446.agda:121-136`, rebuilt at `Probe465.agda:76-94`).

438's device (`Probe438.agda:89-93`) places `G`, not `F`. 464's
device (`Probe464.agda:87-92`) places `F` in `Lset (sucV (stage F))`,
not in `Lset γB`. 460's type names `F : S`. It does not name
`Mem (Lset γB)`.

## WHAT WAS NOT DONE

No axiom. No postulate. No module parameter that asserts
`place-shift` or `fst F ∈ Lset γB`. I did not rebuild
`ShiftGraph`. I did not change 446's bound to include `stage F`.
I did not inhabit the obligation. `fits-446` stays the failing
packing.

## THIS IS NOT A REFUTATION OF THE TYPE

The target can still be true of the carved `ShiftGraph.G`. 460's
delivered TYPE forgets the carve and keeps `F : S`. This NO-GO
says that type does not reach 446's predicate. It does not say
the membership is false.

## C-42

This NO-GO measures ONE site: 460's truncated `F : S` against
446's `CodedInjP'` at `d` the index of `γ`. It does not measure
464's F-stage selection. It does not measure Residue. It does
not measure the limit case. The sweep is in the report.
