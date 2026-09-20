# Remaining Boolean CH obligation, 2026-09-20

The exact remaining input of `CohenBooleanCHBot.FromParts` is

```
CH.VS.val CH.CH-cons (CH.at2 booleanPowerNm) ≡ CH.⊥B
```

`CohenBooleanInnerBot.FromInjectables` is an existing proof of this conclusion
for `pω = booleanPowerNm`, given a name `x` and these four Boolean values:

| Injection formula | Required value |
| --- | --- |
| omega to x | top |
| x to pω | top |
| x to omega | bottom |
| pω to x | bottom |

This interface is not instantiated by the current active sources. The
coordinator read its actual proof and the following supplier definitions after
a read-only Sol audit; the missing work is more than connecting module aliases.

* `CohenBooleanInjWx.AtCardinal.ground-wx` proves the ground injection from omega
  into a supplied larger cardinal. `wx-top-from` still requires a name and a
  top-valued injection-body proof. The ground injection alone is not that proof.
* `CohenBooleanInjBot.AtCardinal.FromResidue.inj-xw-bot` consumes
  `BooleanResidue`: every candidate injection body must already have bottom
  value. The cardinal's ground non-injection theorem does not supply this
  semantic assertion by itself.
* `CohenBooleanInjFiber.CollapseWitness` is the outstanding bridge from a
  condition forcing such an injection body to a ground injection. An assumed
  witness can be contradicted using the cardinal hypothesis; the witness must
  still be constructed.
* The audited injection modules contain no supplier for either required
  power-name-facing value. Those two facts cannot be replaced by the already
  proved membership characterization of `booleanPowerNm`.

The current CHBot module does not assume the required cardinal facts about
`κ`. It cannot produce the final contradiction uniformly for arbitrary `κ`
merely because the Cohen construction and formula compiler are available.
Adding cardinal hypotheses to a future specialized theorem is appropriate;
adding the desired preservation or non-injection conclusion as a new supplied
capability would leave the acceptance obligation open.

The new internal check recursion improves one foundational supplier. It does
not prove any of these four Boolean injection values or discharge extension
Separation, Collection, Choice, or cardinal preservation.
