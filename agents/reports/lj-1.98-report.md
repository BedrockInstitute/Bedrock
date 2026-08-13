# LJ-1.98: can the eleven refuted facts be TIED, and does the tie hold at the use site?

Status: ABORTED at the pre-fixed criterion (D-1). No commit, no push.
ASD-STE100. This report is `_build/lj-1.98-report.md`.

## 0. THE VERDICT

**The measurement supports the retirement side for `entryK`, and it
does not support the repair story.** The candidate tie for `entryK`
is the T-slot tie that `domEntryK` (`src/L/Condensation.lagda.md:6504-6506`)
states. At the row use site, the T-slot tie is NOT supplied, MEASURED.
The site binds the env-set membership `z ∈ E`, not the T-slot
membership `pr x y ∈ T`. The site-use lemma from the T-tied fact
cannot be written: the T-membership premise stays unsolved, exit 42
at `src/ProbeLJ198A.agda:87`. The tie the site does supply is the
env-set tie, and the shared frame has no env-set slot, so the frame
cannot state it. Per the abort criterion, STOP here. The other ten
facts are NOT ATTEMPTED.

## 1. THE COUNT

Measured supplied: 0. Measured not supplied: 1 (`entryK`). Not
attempted: 10. The deciding negative is MEASURED: the machine check
leaves the T-membership meta unsolved (`src/ProbeLJ198A.agda:87`,
exit 42), and the source listing shows the site's binders are
`z ∈ E` and `p : pr x y ∈ z`, never `pr x y ∈ T`.

## 2. THE TABLE

One row per fact. The use sites are read from the source at the cited
lines. TIED BUT NOT SUPPLIED means the tied form's premise is absent
from the site's binders. NOT ATTEMPTED means the abort criterion
stopped the dispatch before the machine check; the intended tie in
each row is read from the source and sets no verdict.

| fact | source | use site in the rows | intended tie | status |
|---|---|---|---|---|
| `tmKeyK` | `TwelveAgree.lagda.md:96` | `TmVal.in'` `Condensation.lagda.md:2948` (`kk k`), via the atom and bounded leaves at `:4206`, `:4227`, `:4772`, `:4803`, `:4894`, `:4925` | the keyValK shape: `(k : S) → ⟨ (k ∷ γ) ⊨ tagAtL (suc t) 1 zero ⟩ → k ∈ K`; the site binds the tag satisfaction `ht` | NOT ATTEMPTED |
| `entryK` | `:118-120` | `EnvSet` `Condensation.lagda.md:2815-2817` (`entryK z x y p`), also `:2825-2826`, `:2834`, `:2852`; the rows pass `entryK` at `:3512`, `:3588`, `:3696`, `:3870`, `:4201`, `:4769`, `:4891`, `:4996`, `:5023` | T-slot tie (`domEntryK`): `(x y : S) → ⟨ pr x y ∈ T ⟩ → x ∈ K × y ∈ K` | TIED BUT NOT SUPPLIED, MEASURED |
| `arSubK-mem` | `:121-123` | `EnvSet` `Condensation.lagda.md:2831` (`arSubK x hxar`); rows thread at `:3512`, `:3588`, `:3696`, `:3870`, `:4201`, `:4769`, `:4891`, `:4996` | `ar` tied to K: `x ∈ ar → ar ∈ K → x ∈ K` (the `transK` shape, `TwelveAgree.lagda.md:167-169`); the site binds `ar ∈ K` | NOT ATTEMPTED |
| `arSubK-neg` | `:124-126` | same EnvSet use, rows at `:3588`, `:3696`, `:3870`, `:4769`, `:4891`, `:4996`, `:5023` | same | NOT ATTEMPTED |
| `arSubK-top` | `:127-129` | same EnvSet use, rows at `:3512`, `:3588`, `:3696`, `:3870` | same | NOT ATTEMPTED |
| `arSubK-imp` | `:130-132` | same EnvSet use, rows at `:4769`, `:4891`, `:4996`, `:5023` | same | NOT ATTEMPTED |
| `keyK-neg` | `:201-204` | `SubValB2T` `Condensation.lagda.md:2989-3007`; NegAgree passes `keyK E ya yc a ar c` at `:3597`, `:3624` | `ar` and `a` tied to K; the site binds `ar ∈ K`, `a ∈ K` | NOT ATTEMPTED |
| `succK` | `:205-206` | `SubValSuccB2T` `Condensation.lagda.md:3027-3070`; ForallAgree `:3705-3706`, `:3738-3739`; ExistAgree `:3880-3881`, `:3909-3910` | `ar` tied to K; the site binds `ar ∈ K` | NOT ATTEMPTED |
| `keyK-un` | `:207-208` | same `SubValSuccB2T` uses | `ar` and `a` tied to K; the site binds `ar ∈ K`, `a ∈ K` | NOT ATTEMPTED |
| `succK-allin` | `:224-228` | AllInAgree `:4780-4781`, `:4811-4812`, `:4902-4903`, `:4933-4934` | `ar` tied to K; the site binds `ar ∈ K` | NOT ATTEMPTED |
| `keyK-allin` | `:229-235` | same AllInAgree uses | the conclusion reads positions 5 and 3 of `(E ∷ ya ∷ yc ∷ b ∷ a ∷ ar ∷ c ∷ γ)`, so `ar` and `a` are the free variables; both tied to K; the site binds `ar ∈ K`, `a ∈ K` | NOT ATTEMPTED |

## 3. THE DECIDING MEASUREMENT

The `entryK` use site is the generic `EnvSet` transfer. Every row
passes `entryK` into `EnvSet` (`Condensation.lagda.md:4201` is the
Mem row's instance). Inside `EnvSet`, the fact is applied at
`entryK z x y p` (`Condensation.lagda.md:2815-2817`). The variable
`z` is bound by `extAtB→extAt` (`Condensation.lagda.md:2508-2514`):
`z ∈ fst (lookup E γ)`, a member of the env-set slot `E`. The
variable `p` is the entry's pair membership `⟨ pr (fst x) (fst y)
∈ fst z ⟩`. So the site binds `z ∈ E` and `pr x y ∈ z`, and the row
needs `x ∈ K` and `y ∈ K`.

The T-slot tie's premise is `⟨ pr (fst x) (fst y) ∈ fst (lookup T γ)
⟩`. The site has no binder for it. The machine check
(`src/ProbeLJ198A.agda:87`) attempts the site-use lemma from the
T-tied fact and leaves exactly that T-membership unsolved: exit 42.
The deciding claim is MEASURED.

The term I could not write:

```agda
envEntry-use : (z x y : S)
  → ⟨ fst z ∈ fst (lookup E γ) ⟩
  → ⟨ pr (fst x) (fst y) ∈ fst z ⟩
  → ⟨ fst x ∈ fst (lookup K γ) ⟩ × ⟨ fst y ∈ fst (lookup K γ) ⟩
envEntry-use z x y z∈E p = domEntryK x y ?   -- the T-membership is absent
```

What the row would have to bind: the env-set membership `z ∈ E` as
the fact's premise. That is the env-set tie, and it closes at the
site (green, `src/ProbeLJ198B.agda:51`). The shared frame
(`TwelveAgree.lagda.md:45-243`) has no env-set slot among its 15
slots, so the frame cannot state the env-set tie. The T-slot tie is a
frame the consumer can hold (`domEntryK` is a consumer site fact), but
the rows cannot use it at the EnvSet site. The frame-level `entryK`
is not repairable by tying it to a slot the rows supply.

## 4. THE DD4 ANSWER

The tied frame for `entryK` is the env-set-tied frame: the fact's
premise is `z ∈ E` for the env-set slot. That frame is NOT a frame
the consumer can hold: `AbstractFrame` names `N0..N11 t0 t1 K` and no
env-set slot, and the consumer's `KFacts` plus six site facts
(`Condensation.lagda.md:5734-5770`, `:6492-6513`) hold only the
C-slot and T-slot entry facts. The T-slot tie is a frame the consumer
can hold, but the rows' EnvSet use does not supply its premise. The
shared frame and the row use do not meet at `entryK`: this is the
`[LJ-1.93]` frame-mismatch shape in one fact, now measured at the use
site. Sharing is only free when the shared frame is the frame the
consumer actually holds; for `entryK`, the frame the consumer holds
(T-slot tie) is not the frame the rows use.

## 5. ARCHIVE USED

- `_build/lj-1.97-report.md`, read WHOLE, and
  `src/ProbeLJ197A.agda`, read WHOLE. TOOK the ten refutations and
  the cycle lemmas; the `entryK` refutation at
  `ProbeLJ197A.agda:239-240`.
- `_build/lj-1.96-report.md`, read WHOLE, and
  `src/ProbeLJ196A.agda`, read WHOLE. TOOK the pattern to copy: the
  abstract-module site-use lemma from a tied fact
  (`ProbeLJ196A.agda:50-52`), and the `valK` use table. The
  `domEntryK` result there closes the `valK` use; this dispatch
  measures the same tied fact against the `entryK` use and finds the
  T-premise absent.
- `_build/lj-1.95-report.md`, read WHOLE, and
  `src/ProbeLJ195A.agda`, read. TOOK the `tmKeyK` refutation shape.
- `_build/lj-1.93-report.md`, read WHOLE, and the three probes. TOOK
  the 39-unsupplied table and the `entryK` no-home row.
- `src/L/Condensation/TwelveAgree.lagda.md:45-243`, read WHOLE. TOOK
  the eleven fact types and their line numbers.
- `src/L/Condensation.lagda.md`, read the row use sites: `EnvSet`
  (`:2764-2870`), `TopAgree` (`:3473-3536`), `NegAgree`
  (`:3552-3630`), `ForallAgree` (`:3655-3745`), `ExistAgree`
  (`:3761-3920`), `MemAgree` (`:4141-4240`), `AllInAgree`
  (`:4700-4950`), `SubValB2T` (`:2985-3010`), `SubValSuccB2T`
  (`:3027-3070`), `TmVal` (`:2894-2960`), `extAtB→extAt`
  (`:2508-2514`), `domEntryK` (`:6504-6506`), the consumer's frame
  (`:6476-6513`). TOOK every use line quoted in the table.
- `dev/LESSONS.md`, C-38 as extended (`:3427-3511`), C-35
  (`:3200-3242`), C-36 (`:3284-3332`), D-29 (`:3242-3284`), D-30
  (`:3332-3380`), read WHOLE. TOOK the conditional-closure standard:
  the tied fact must be conditional and the condition must be one the
  site can supply.
- `scripts/rules.py --for build` and `--for probe`, read all
  statements.
- `archive/rud-route/`, SHAPE only. Took nothing.

## 6. LITERATURE USED

Banked; nothing spent.

## 7. GATES

- `src/ProbeLJ198A.agda`: exit 42 as designed, 2 s total, one
  unsolved interaction meta at `:87` (the T-membership), load
  average 6.25 at start, 4.73 five-minute at finish. One agda
  process at the C-12 cap.
- `src/ProbeLJ198B.agda`: GREEN, exit 0, 1 s total, load average
  about 5 (4 users). One agda process at the C-12 cap.
- `scripts/lint-agda.py --check src/ProbeLJ198A.agda
  src/ProbeLJ198B.agda`: exit 0.
- `scripts/lint-prose.py --check _build/lj-1.98-report.md`: exit 0.
- No master was touched. `src/L/Condensation/`,
  `src/L/Coding/`, `src/V/` and `src/Everything.lagda.md` are
  untouched. No `make check`. No commit, no push.
