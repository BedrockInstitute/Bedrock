# Review of `someEnv-at-K`

The obligation does not form. This file is the obstruction, for the
branch `no-go-stated`.

## THE STATEMENT

The brief names:

```
someEnv-at-K : someEnvDef {3} iK Kenv
```

It is `Probe450.agda:47-48`, inside `module W3` at a real `KValue`
frame (`src/L/Condensation.lagda.md:7380-7409`). `someEnvDef` is
`src/L/Condensation/LowerAgree.lagda.md:52-58`.

Agda reports `[UnequalTerms]` at `Probe450.agda:47.33-35`
(`runs/full-recheck-1.out`, exit 42, 1.96 s, caliber
`GHCRTS="-A64m -I0 -M8g"`):

```
14 != 8 of type ℕ
when checking that the expression iK has type
Fin (5 Agda.Builtin.Nat.+ 3)
```

`iK` is `Fin 14`. `someEnvDef {3}` wants `Fin (5 + 3) = Fin 8`.

## D-10

The two index conventions do not meet at any `n`. See
`lj-1.450-report.md` section D-10.

`someEnvDef {n}` takes `K : Fin (5 + n)` and `γ : S ^ (11 + n)`, and
it reads `lookup (suc^6 K) γ`. `KValue` delivers `iK : Fin 14` and
`Kenv : S ^ 14`, and it reads `lookup iK Kenv`.

1. `Fin (5 + n) = Fin 14` gives `n = 9`, then `γ : S ^ 20`.
2. `11 + n = 14` gives `n = 3`, then `K : Fin 8`.

No `n` solves both. At `n = 3`, `lookup (suc^6 K) Kenv` reads
positions 6 through 13. `iK` is position 1. `6 + k ≥ 6 > 1`. No
`Fin 8` index lands on the bound.

W3 measured the same split on the 24 `tagEq`/`numK` fields, as a
record inhabited from `KValue.facts`. See `runs/w3-1.out`. The
elaborator reduced TFacts's `suc^6` lookup on `Kenv` to a lookup in
the tail `numeralL 4 ∷ ... ∷ numeralL 11 ∷ []`, and
`KFacts.tagEq0 facts` is `fst (numeralL 0) ≡ fst (numeralL 0)`.

The break is the layout. It is not the mathematics of `envHypB2`.

## WHAT WAS NOT DONE

No re-layout of `Kenv` was written. The brief forbids that. No
`TFacts` record was written. The other 27 fields were not inhabited.
No postulate, no extra hypothesis, no module parameter that asserts
the frames meet.

`[LJ-1.113]` named `someEnv` NEEDS NEW CONTENT
(`agents/tasks/LJ-1-113/lj-1.113-report.md:52`) and INFERRED FALSE as
a derivation from delivered machinery (`:207-210`). It did not name
the statement FALSE. This NO-GO is the layout at a real `K`, not a
repeat of that inference.

## CORRECTED TARGET

Pad six values onto `Kenv` and raise `n` to 9, so the index types
and the env lengths meet at once:

```
someEnv-padded :
  (c0 c1 c2 c3 c4 c5 : S) →
  someEnvDef {9} iK (c0 ∷ c1 ∷ c2 ∷ c3 ∷ c4 ∷ c5 ∷ Kenv)
```

Because `5 + 9 = 14` and `11 + 9 = 20 = 6 + 14`, and
`lookup (suc^6 iK) (c0 ∷ ... ∷ c5 ∷ Kenv) = lookup iK Kenv`.

This file names that type. It does not inhabit it. A next brief that
wants the construction must accept this pad, or it must re-layout
`Kenv`, or it must re-index `someEnvDef`.

## C-42

The refutation is this one type: `someEnvDef {3} iK Kenv` at
`Probe450.agda:47`.

COUNT of `S ^ (11 + n)` in `src/`: 7. LowerAgree 3
(`LowerAgree.lagda.md:52`, `:97`, `:228`), TwelveAgree 2
(`TwelveAgree.lagda.md:131`, `:339`), UpperAgree 2
(`UpperAgree.lagda.md:94`, `:213`). All seven use `Fin (5 + n)` and
the `suc^6` lookup.

COUNT of `Kenv : S ^ 14`: 1 (`Condensation.lagda.md:7389`). `KFacts`
is the other convention: `Fin n` and `S ^ n`
(`Condensation.lagda.md:6079-6080`).

COUNT of the consumer's `S ^ (8 + n)`: 2 in Condensation
(`:6963` `SatGraphAgree`, `:7225` `LeafAgree`). That is a third
length. It is 3 conses on a `5 + n` frame, not 6.

A cure at `someEnv-at-K` alone does not close those seven sites. The
pad above is the adapter at this one type. It is not a measured cure
of `TFacts` or of `SatGraphAgree`.
