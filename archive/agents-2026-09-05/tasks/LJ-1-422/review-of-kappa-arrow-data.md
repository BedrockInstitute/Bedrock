# Review of `kappa-arrow-data`

The obligation `kappa-arrow-data` is not inhabited. This file is the
obstruction, for the branch `no-go-stated`.

## THE STATEMENT, AS THE BRIEF NAMES IT

```
kappa-arrow-data :
    (a : S) (oa : IsOrd (fst a))
  → ⟪ fst a ⟫ ↪ ⟪ fst (κL a oa) ⟫
```

Exact type used: `agents/tasks/LJ-1-422/Probe422.agda:70-72`. Generic
in `a`. No cardinal. No numeral. I did not inhabit it. I did not
weaken it in Agda.

`κL` and `κoL` are module hypotheses at `[LJ-1.406]`'s delivered types
(`agents/tasks/LJ-1-406/Probe406.agda:82` and `:85`). Predecessor
report: **GO** (`agents/tasks/LJ-1-406/lj-1.406-report.md:13`). The
truncated arrow `κ-injL` is at `Probe406.agda:88`. I did not inhabit
the truncated form as data.

## VERDICT

**NO-GO.** The untruncated arrow is a choice of one of several
injections. No live device names a canonical choice. The orthodox
size proof does not name this arrow as data.

## D-10. THE TARGET IS TRUE AS A TRUNCATION AND NOT AS DATA

The truncated form is delivered: `κ-inj` at
`src/L/Cardinal.lagda.md:133`, and `κ-injL` at
`agents/tasks/LJ-1-406/Probe406.agda:88`. The statement's truth, as a
cardinal inequality, is not in question.

The untruncated form is a Sigma of a function and an injectivity
proof (`src/L/Cardinal.lagda.md:47-48`). The chapter's own comment
says it is not an hProp (`src/L/Cardinal.lagda.md:132`). Many
injections exist whenever one does. A choice of one of several is
canonical only if some device picks THE injection.

Nothing in this tree makes that choice. The greedy map along the
domain order fails at order type `ω · 2` into `ω`
(`dev/literature/truncation-and-selection.md:332-337`). A well-order
on the two carriers is not enough. A well-order on the injections
is what `<_L` supplies classically, and what an ambient function
type does not have.

Corrected target: none. The truncated form stands. The data form is
not a statement the orthodox proof names.

## THE THREE DEVICES

1. **`PT.rec`.** The target is not an hProp. Basis:
   `src/L/Cardinal.lagda.md:132-133`. Not applied in Agda.
2. **`leastOf`.** Re-enumeration of `': SWO|SWO ('` over `src/`
   returns COUNT **49**, in six shapes, none of them a function type
   or `_↪_`. Details in `lj-1.422-report.md`. Not applied in Agda.
3. **`swo-into-ord`.** This is the one device applied. It ranks a
   carrier that already carries an `SWO` into SOME ordinal
   (`agents/tasks/LJ-1-417/Probe417.agda:80`). The carrier of the
   truncation does not carry an `SWO`. The elaborator rejects the
   delivered domain order at `Probe422.agda:65`.

## WHAT THE ORTHODOX PROOF NAMES THIS ARROW WITH

Devlin II.1.1(vii) is `|L_α| = |α|` for `α ≥ ω`
(`dev/literature/devlin-II5.md:413`). SZ 1.17 supplies a surjection
`α → J_α` and, under Gödel pairing-closure, the enumeration
`Φ : otp(<_α^A) → J_α` with `otp = α`
(`dev/literature/j-hierarchy.md:147-149`). Both are the size of a
LEVEL. Neither is an untruncated injection from an ordinal into its
least cardinal.

A cardinal inequality is a truncated existence of an injection
(`dev/literature/truncation-and-selection.md:75-86`, HoTT Book
Definition 10.2.7). The sources do not supply the injection as data.

The device that would make an injection canonical is a well-order on
the injections (`dev/literature/truncation-and-selection.md:335-337`).
That device is **absent** from the live tree. It is not the
archived condensation chapter: that chapter's first paragraph is the
recognition step of a collapse
(`archive/src/2026-08-09-rud-route/L/Condensation.lagda.md:4`), not a
well-order on injections.

The size-equation's pairing-and-enumeration device lives on the
retired route as the order-type reading
(`archive/src/2026-08-09-rud-route/L/Ordinal/Pairing.lagda.md:4`).
The live square-law chapter never forms that order type
(`src/L/Ordinal/SquareLaw.lagda.md:10-11`). That device names a
different arrow.

## THE ARCHITECTURE SENTENCE

The orthodox proof does not reach `α ↪ κ` as data; the device that
would, a well-order on the injections, is absent, and the archived
condensation chapter at
`archive/src/2026-08-09-rud-route/L/Condensation.lagda.md:4` is not
that device.

## WHAT WAS NOT DONE

No axiom. No postulate. No module parameter that asserts the
untruncated arrow. `device-covers-carrier` is the W3 fragment. It
does not typecheck. `kappa-arrow-data` is the same application at
the named target. It is not inhabited.
