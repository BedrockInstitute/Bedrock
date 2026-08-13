# LJ-1.99: does transitivity of K close entryK, and the arSubK family?

Status: COMPLETE, written incrementally per C-22. No commit, no push.
ASD-STE100. This report is `_build/lj-1.99-report.md`.

## 0. THE VERDICT

**The four-step chain CLOSES `entryK`'s conclusion, MEASURED.**
`src/ProbeLJ199A.agda` builds the chain from `arityK` alone plus the
site's binders and one premise, `E ∈ K`: `Chain.entryK-tied`, GREEN,
exit 0, 2.16 s total, 1.92 s user, load average 3.7 to 4.6. Four
applications of `arityK` (`src/L/Condensation.lagda.md:5769-5770`),
each with its own membership, close the x component; the y component
climbs through the pair's second component, also four applications.

**The EnvSet module's own telescope does NOT supply `E ∈ K`,
MEASURED.** `src/ProbeLJ199B.agda` mirrors EnvSet's telescope
(`Condensation.lagda.md:2771-2778`) plus `arityK`, and the site-use
lemma's step 1 hole stays unsolved: exit 42, the meta
`⟨ fst (lookup E γ) ∈ fst (lookup K γ) ⟩` at
`ProbeLJ199B.agda:70`. **The rows that instantiate EnvSet DO supply
it**: all nine EnvSet-using row modules hold the frame's `envK-*`
family (`TwelveAgree.lagda.md:98-117`, unrefuted in `[LJ-1.97]`), bind
the `envSetAt` satisfaction `hE`, and bind or derive `EK : E ∈ K`.
Source-verified at the cited `out`/`back` lines. The back direction
closes WITHOUT `E ∈ K`: `over→bnd` binds the `envOverAt` satisfaction
for `z`, so `envInK z h` gives `z ∈ K` and three `arityK` steps close
(`BackSiteSupply`, GREEN).

**The `arSubK-*` tie is `arityK` exactly once, GREEN**
(`Chain.arSubK-tied`). EnvSet's telescope does not bind `ar ∈ K`
(MEASURED, exit 42, hole at `ProbeLJ199B.agda:90`); the rows bind
`arK` at every EnvSet site (source-verified).

**The five key facts' sites bind `ar ∈ K` and `a ∈ K` (or `b ∈ K`),
MEASURED by the source.** Every row `out` binds `arK`/`aK` at an
explicit λ-position and every `back` derives them from `codesK`; the
tied shapes instantiate at exactly those binders
(`SuccKeySite`, `KeyNegSite`, GREEN).

**The measurement supports REPAIR of the shared frame's ten refuted
facts at the row frame**: every refuted fact is tieable by memberships
the row sites hold. It does NOT change the consumer-side verdict of
`[LJ-1.96]`: the consumer's pinned frame (`SatGraphAgree`,
`Condensation.lagda.md:6476-6513`) has no env-set slot and no `envK`
family, so the repaired satisfier-in-K facts are not statable there.
The `[LJ-1.93]` test (statable at a frame the consumer holds) still
fails for the family, though the tie itself is now MEASURED generic.

## 1. THE FOUR-STEP CHAIN

`arityK : (N v : S) → ⟨ fst v ∈ fst N ⟩ → ⟨ fst N ∈ fst (lookup K γ) ⟩
→ ⟨ fst v ∈ fst (lookup K γ) ⟩` is transitivity into K, one step.
The brief's inferred chain climbs it four times:

1. `z ∈ E`, `E ∈ K` → `z ∈ K` (`arityK (lookup E γ) z`).
2. `pr x y ∈ z`, `z ∈ K` → `pr x y ∈ K` (`arityK z (prʟ x y)`,
   through `prʟ-fst`, `src/L/Coding/Model.lagda.md:329`).
3. `⁅ x ⁆ ∈ pr x y`, `pr x y ∈ K` → `⁅ x ⁆ ∈ K`
   (`arityK (prʟ x y) (pairʟ x x)`; `fst (pairʟ x x) ≡ ⁅ A , A ⁆`,
   `pairʟ-fst` at `src/L/Axioms/Numerals.lagda.md:127`, and
   `pair-singleton` gives `⁅ A , A ⁆ ≡ ⁅ A ⁆s`).
4. `x ∈ ⁅ x ⁆`, `⁅ x ⁆ ∈ K` → `x ∈ K` (`arityK (pairʟ x x) x`).

The y component climbs through the pair's second component: step 3 is
`⁅ A , B ⁆ ∈ pr A B` (`pairʟ x y`) and step 4 is `y ∈ ⁅ A , B ⁆`.
The naive `⁅ B ⁆s ∈ pr A B` is FALSE in general for `B ≠ A`, so the
second component is the correct route; the probe uses it.

The L-set memberships are transported along the delivered equalities;
the V-level memberships are `pairing-ax` applications exactly as
`src/ProbeLJ197A.agda` built them. Everything checks at
`src/ProbeLJ199A.agda:65-204` (the `ChainZ` and `Chain` modules):

```agda
entryK-tied : (z x y : S) → ⟨ fst z ∈ fst (lookup E γ) ⟩
            → ⟨ pr (fst x) (fst y) ∈ fst z ⟩
            → ⟨ fst x ∈ fst (lookup K γ) ⟩
              × ⟨ fst y ∈ fst (lookup K γ) ⟩
entryK-tied z x y z∈E p = Z.entryK-tied-zK z x y (z∈K z z∈E) p
```

GREEN, 2.16 s total, 1.92 s user (2.16 to 3.14 s across the runs), one
process at the C-12 cap, load average 3.7 to 4.6 (4 users). The
four-step chain is no longer
INFERRED; it is MEASURED in both directions of every step.

## 2. THE SITE SUPPLY OF E ∈ K

Two layers, measured separately.

**Inside EnvSet (`Condensation.lagda.md:2771-2778`): NOT SUPPLIED,
MEASURED.** The telescope is `(E ar B K : Fin n) (γ : S ^ n)` plus
`entryK`, `arSubK`, `envInK`. None of the three parameters concludes
`E ∈ K`: `entryK` concludes `x ∈ K × y ∈ K` from `pr x y ∈ z`;
`arSubK` concludes `x ∈ K` from `x ∈ ar`; `envInK` concludes `z ∈ K`
from an `envOverAt` satisfaction. `src/ProbeLJ199B.agda:70` writes
the site-use lemma from the chain and leaves exactly
`⟨ fst (lookup E γ) ∈ fst (lookup K γ) ⟩` unsolved: exit 42, 2.17 s.
The term I could not write:

```agda
envEntry-use z x y z∈E p = Chain.entryK-tied {n} E K γ arityK ? z x y z∈E p
```

**At the rows: SUPPLIED, MEASURED by the source.** Every one of the
nine EnvSet-using row modules holds an `envK` parameter of the frame's
family shape and either binds `EK` in `out` or derives it in `back`
from the bound `hE : ⟨ ... ⊨ envSetAt ... ⟩`:

| row | `out` binds `EK` | `back` derives `EK = envK ... hE` |
|---|---|---|
| TopAgree | `:3507` | `:3527` |
| NegAgree | `:3583` | `:3611` |
| ForallAgree | `:3691` | `:3725` |
| ExistAgree | `:3864` | `:3895` |
| MemAgree | `:4195` | `:4219` |
| AllInAgree | `:4763` | `:4796` (arK `:4791`) |
| ExInAgree | `:4885` | `:4918` (arK `:4913`) |
| ImpAgree | `:4989` | `:5019` (arK `:5013`) |
| EqAgree | `:5088` | `:5104` (arK `:5108`, `envK` param `:5054`) |

The `envK-*` facts themselves are the frame's unrefuted
`TwelveAgree.lagda.md:98-117`, concluding `E ∈ K` from an `envSetAt`
satisfaction at the same K slot as `entryK`'s conclusion. The chain's
`E ∈ K` premise is therefore a frame fact the rows already hold, not
an invented tie.

**The back direction supplies `z ∈ K` directly.** EnvSet's
`over→bnd` binds the `envOverAt` satisfaction for `z`
(`Condensation.lagda.md:2840`), and the module's own `envInK`
(`:2776-2777`) is exactly `(z : S) → ⟨ (z ∷ γ) ⊨ envOverAt ... ⟩ →
z ∈ K`. So `envInK z h` gives `z ∈ K`, and the three-step shape
`entryK-tied-zK` closes without `E ∈ K`:
`src/ProbeLJ199A.agda` module `BackSiteSupply`, GREEN. The out
direction (`bnd→over`, `:2812`) has no such binder: its `hb` is the
bounded satisfaction whose structure CONSUMES the very K-memberships
`entryK` produces, so there is no circular-free `z ∈ K` there; the
out direction needs the frame's `E ∈ K`.

## 3. THE arSubK FAMILY

The intended tie, `x ∈ ar → ar ∈ K → x ∈ K`, is `arityK` exactly
once. `Chain.arSubK-tied` (`src/ProbeLJ199A.agda`), GREEN.

The EnvSet use (`Condensation.lagda.md:2831`) binds `hxar : x ∈ ar`
only. EnvSet's telescope does not bind `ar ∈ K`: MEASURED,
`src/ProbeLJ199B.agda:90` leaves the meta
`⟨ fst (lookup ar γ) ∈ fst (lookup K γ) ⟩` unsolved, exit 42. The
term I could not write:

```agda
arSubK-use x hxar = arityK (lookup ar γ) x hxar ?
```

The rows bind `arK` at every EnvSet site (section 2 table's rows also
hold `arK` in `out`, and `back` derives it from `codesK`), so the
tie is supplied at the row level. Same answer as `entryK`: EnvSet's
telescope lacks the premise, the rows hold it.

## 4. THE FIVE KEY FACTS

`[LJ-1.98]`'s table claimed every one of these sites binds `ar ∈ K`,
and some also `a ∈ K`. Verified in the source. Each row `out` binds
`arK`/`aK`/`bK` at an explicit λ-position and each `back` derives them
from `codesK` (e.g. ForallAgree `out` `:3691`, `back` `:3720`;
NegAgree `:3583`/`:3606`; AllInAgree `:4763`, `back` `:4791`;
ExInAgree `:4885`/`:4913`; ImpAgree `:4989`/`:5013`). The transfers
`SubValB2T` (`:2989-3007`) and `SubValSuccB2T` (`:3027-3070`) consume
the conclusion memberships directly (`keyK`, `succK` parameters at
`:2991-2992`, `:3029-3030`); the rows pass the frame facts applied
(`keyK E ya yc a ar c` etc. at `:3588`, `:3705-3706`,
`:3738-3739`, `:3880-3881`, `:3909-3910`, `:4780-4781`,
`:4811-4812`, `:4902-4903`, `:4933-4934`).

| fact | source | site binds | status |
|---|---|---|---|
| `keyK-neg` | `TwelveAgree.lagda.md:201-204` | `arK`, `aK` (NegAgree `:3583`, `:3606`) | SUPPLIED, MEASURED; tied shape closes at the binders (`KeyNegSite`, GREEN) |
| `succK` | `:205-206` | `arK` (ForallAgree `:3691`/`:3720`, ExistAgree `:3864`/`:3890`) | SUPPLIED, MEASURED; `SuccKeySite`, GREEN |
| `keyK-un` | `:207-208` | `arK`, `aK` (same rows) | SUPPLIED, MEASURED; `SuccKeySite`, GREEN |
| `succK-allin` | `:224-228` | `arK` (AllInAgree `:4763`, ExInAgree `:4885`) | SUPPLIED, MEASURED by the source; NOT re-instantiated |
| `keyK-allin` | `:229-235` | `arK`, `bK` (positions 5 and 3 of the allin env) | SUPPLIED, MEASURED by the source; NOT re-instantiated |

For `succK-allin` and `keyK-allin` the source reading is the machine
check: the master is green, and the λ-binders at the cited lines are
explicit in the already-typechecked master. The two anchor modules
formalize the tied shapes for `succK`/`keyK-un`/`keyK-neg` only; the
allin pair is read, not rebuilt.

## 5. THE DD4 ANSWER

**The chain closes generically, MEASURED.** It uses one field
(`arityK`, or the frame's own `transK` at
`TwelveAgree.lagda.md:167-169`, which has the same type) and the pair
encoding (`pairʟ`, `prʟ`, `pair-singleton`, `pairing-ax`), nothing
about definability. The same lemmas serve both the x and the y
components, and the same `arityK`-once shape is the whole `arSubK`
tie. The frame's `transK` means the four-step chain is buildable from
the shared frame's OWN facts plus `E ∈ K`.

**Are the repaired facts statable at a frame the consumer holds? NO,
for the env-set family.** The consumer's pinned frame
(`SatGraphAgree`, `Condensation.lagda.md:6476-6513`) holds `KFacts`
(including `arityK`, `:5769-5770`) and the six site facts
`codesK`/`unCodesK`/`closedEntryK`/`domEntryK`/`domK`/`witK`. It has
no env-set slot `E`, no `ar` slot, and no `envK-*` family, so the tied
`entryK` (premise `E ∈ K`) and tied `arSubK` (premise `ar ∈ K`) are
not statable there. This is the `[LJ-1.93]` frame mismatch that
`[LJ-1.96]` measured; this dispatch adds the missing half of the
repair picture: the ties themselves are supplyable at the frame the
ROWS hold (the shared frame), which `[LJ-1.98]` could not see because
it stopped at the first candidate. Sharing is still only free when the
shared frame is the frame the consumer holds, and the consumer's frame
is still short of the satisfier-in-K family.

## 6. NEGATIVES AND THEIR STATUS

1. The four-step chain closes `entryK`'s conclusion given `E ∈ K`:
   **MEASURED TRUE** (`src/ProbeLJ199A.agda`, GREEN). This is the
   brief's inferred candidate, now replaced by a measurement.
2. The EnvSet telescope binds `E ∈ K`: **MEASURED FALSE**
   (`src/ProbeLJ199B.agda:70`, exit 42; telescope listed at
   `Condensation.lagda.md:2771-2778`).
3. The rows supply `E ∈ K` at every EnvSet site: **MEASURED TRUE by
   the source** (nine rows, `envK` + `hE`/`EK`, section 2 table).
4. The `arSubK` tie closes: **MEASURED TRUE** (`arityK` once,
   `Chain.arSubK-tied`).
5. The EnvSet telescope binds `ar ∈ K`: **MEASURED FALSE**
   (`src/ProbeLJ199B.agda:90`, exit 42).
6. The five key facts' sites bind `ar ∈ K` and `a`/`b ∈ K`:
   **MEASURED TRUE by the source**, with the tied shapes formally
   anchored for `succK`/`keyK-un`/`keyK-neg`
   (`SuccKeySite`, `KeyNegSite`, GREEN).
7. The repaired facts are statable at the consumer's pinned frame:
   **MEASURED FALSE by listing** (`SatGraphAgree`,
   `:6476-6513` holds no `E` slot, no `ar` slot, no `envK-*`);
   INFERRED that no derivation from the six site facts supplies
   them. No verdict rests on the inference alone.
8. A derivation of `E ∈ K` from EnvSet's three parameters exists:
   **INFERRED FALSE beyond the direct route** (each parameter's
   conclusion type is not `E ∈ K`); the direct route is MEASURED
   red. The row route (`envK` + `hE`) is MEASURED by the source.

## 7. ARCHIVE USED

- `_build/lj-1.98-report.md`, read WHOLE, and
  `src/ProbeLJ198A.agda`, `src/ProbeLJ198B.agda`, read WHOLE. TOOK
  the use-site table as the work list, the red-hole pattern for the
  site-supply check (`ProbeLJ198A.agda:87`), and the green
  env-set-tie control (`ProbeLJ198B.agda:51`). The T-slot tie stays
  NOT SUPPLIED; this dispatch measures the second candidate the
  abort criterion hid.
- `src/ProbeLJ197A.agda`, read WHOLE. TOOK the ten refutations, the
  `pairing-ax` membership recipes (`A∈pair`, `singl∈prAA`,
  `A∈singl`), and the `pairʟ`/`prʟ` lifting.
- `_build/lj-1.97-report.md`, read WHOLE. TOOK the refutation table
  and the NOT REFUTED rows for `envK-*`.
- `_build/lj-1.96-report.md`, read WHOLE, and
  `src/ProbeLJ196A.agda`, read WHOLE. TOOK the consumer-frame table
  and the `domEntryK` supply result; the consumer gap (no `E` slot,
  no `envK`) is unchanged by this dispatch.
- `src/L/Condensation.lagda.md`, read the row modules, `EnvSet`
  (`:2771-2874`), `SubValB2T` (`:2989-3007`), `SubValSuccB2T`
  (`:3027-3070`), `succU`/`keyU` (`:3635-3644`), `KFacts`
  (`:5734-5770`), `SatGraphAgree` (`:6476-6513`), `extAtB→extAt`
  (`:2508-2514`). TOOK every binder and derivation line quoted in
  sections 2 and 4.
- `src/L/Condensation/TwelveAgree.lagda.md:45-243`, read WHOLE.
  TOOK the fact types, the `transK` field (`:167-169`), and the
  `envK-*` lines (`:98-117`).
- `src/L/Coding/Model.lagda.md:483-485`, `:329`; read. TOOK
  `envOverAt`'s shape and `prʟ-fst`.
- `src/L/Axioms/Numerals.lagda.md:127`, read. TOOK `pairʟ-fst`.
- `dev/LESSONS.md`, C-38 as extended (`:3427-3511`), C-35
  (`:3200-3242`), C-36 (`:3284-3332`), D-29 (`:3242-3284`), D-30
  (`:3332-3380`), read WHOLE. TOOK the conditional-closure standard
  (the tie must be a premise the site supplies), the
  failed-substitution discipline (the red hole names the absent
  premise, not an impossibility), and the consumer-pricing rule.
- `scripts/rules.py --for build` and `--for probe`, read all
  statements.
- `archive/rud-route/`, SHAPE only. Took nothing.

## 8. LITERATURE USED

Banked; nothing spent.

## 9. GATES

- `src/ProbeLJ199A.agda`: GREEN, exit 0, 2.16 s total, 1.92 s user,
  one process at the C-12 cap, load average 3.7 to 4.6 (4 users).
  Warm dependencies from `_build`.
- `src/ProbeLJ199B.agda`: RED as designed, exit 42, 2.17 s total,
  one process at the C-12 cap, load average 3.7 to 4.6 (4 users).
  Two unsolved interaction metas: `:70.65-66` (`E ∈ K`) and
  `:90.51-52` (`ar ∈ K`).
- `scripts/lint-agda.py --check src/ProbeLJ199A.agda
  src/ProbeLJ199B.agda`: exit 0.
- `scripts/lint-prose.py --check _build/lj-1.99-report.md`: exit 0.
- No master was touched. `src/L/Condensation/`,
  `src/L/Coding/`, `src/V/`, `src/Everything.lagda.md` untouched.
  No `make check`. No commit, no push. The working tree carries the
  two probes and this report, gitignored by design. HEAD moved from
  `1c43837` to `9b51977` while this dispatch ran; the commit touches
  only `dev/PLAN.md`.
