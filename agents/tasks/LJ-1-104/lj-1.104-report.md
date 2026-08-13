# LJ-1.104: does the Mem row prove itself in tied form, with arityK?

Status: COMPLETE, written incrementally per C-22. No commit, no push.
ASD-STE100. This report is `_build/lj-1.104-report.md`.

## 0. THE VERDICT

**YES. The row proves BOTH directions in tied form. MEASURED.**
`src/ProbeLJ1104A.agda` is GREEN, exit 0, one process at the C-12
cap, 9.67 s total, 8.62 s user, 0.32 s sys, load average 3.60 at
start and 4.17 at finish (4 users). The out direction is
`MemAgreeTied.out`
(`src/ProbeLJ1104A.agda:628-645`). The back direction is
`MemAgreeTied.back` (`:646-676`). Both prove the SAME statements the
master row proves today (`src/L/Condensation.lagda.md:4202-4207` and
`:4209-4227`): `⟨ γ ⊨ memClauseAt C T B ⟩` against
`Mem.memBndAt C T B N K t0 t1`.

**The [LJ-1.102] obstacle is exactly what the brief said.** The
ChainZ tie (premise `z ∈ K`) closes EnvSet's SECOND component; the
first component climbs `z ∈ E` to `z ∈ K` by `arityK` and the row's
`EK` (`EnvSetTied.out`, `:233-235`; the climb is the first lambda at
`:234`). The back direction closes with the same two supplies
(`EnvSetTied.back`, `:239-241`).

**The tmKeyK repair in the starting material is REFUTED, MEASURED.**
`[LJ-1.102]`'s restated telescope carried the tied `keyValK` at the
row's 11-slot environment (`src/ProbeLJ1102A.agda:332-336`). That
type is empty at the abstract frame: the code slot (`a`) and the key
(`k`) are both quantified variables, so the tag satisfaction can be
forced at the K-slot element, and the conclusion is `X ∈ X`.
`RefuteKeyValK.keyValK-refutes` (`src/ProbeLJ1104A.agda:118-120`)
machine-checks the refutation, GREEN in the same run. The honest
repair is a DERIVATION, not a hypothesis: the tied AtomLeaf copy
derives `k ∈ K` from the code slot's membership (aK/bK), `arityK`,
and the tag satisfaction (`keyK-of`, `:405-427`). It costs zero
telescope hypotheses. This is the one correction to the starting
material; everything else in the telescope survives.

## 1. THE DIFF SIZE

All counts are non-blank lines.

| part | before | after |
|---|---:|---:|
| row telescope (`Condensation.lagda.md:4142-4185` vs `ProbeLJ1104A.agda:570-620`) | 44 | 51 |
| row module (`:4141-4240` vs `:570-676`) | 96 | 103 |

The telescope change is 44 to 51 lines, +7. The changes: `arityK`
added (+3), `tmKeyK` removed (-1), `entryK` gains the `z ∈ K`
premise (+1), `arSubK` gains the `ar ∈ K` premise (+2), and the
`where private` formatting (+1). The whole probe is 694 lines
(629 non-blank). `[LJ-1.102]`'s restated telescope was 53 lines;
this one is 51, because `keyValK` is gone.

The row's cold seconds in tied form: 9.67 s for the whole probe at
load 3.60 to 4.17 (section 8). The original's standalone seconds are
not separately measurable: the master's `MemAgree` checks as part of
`src/L/Condensation.lagda.md`, and no per-row profile exists. The
probe figure is the honest price of the restated row machinery:
`EnvSetTied`, the tied `TmVal`, the tied `AtomLeaf`, the refutation,
and the supply module.

## 2. EVERY HYPOTHESIS ADDED, AND WHAT SUPPLIES IT

One hypothesis added, two replaced:

| hypothesis | where | supplier |
|---|---|---|
| `arityK : (N v : S) → ⟨ fst v ∈ fst N ⟩ → ⟨ fst N ∈ fst (lookup K γ) ⟩ → ⟨ fst v ∈ fst (lookup K γ) ⟩` | `:577-580` | **SUPPLIED.** A `KFacts` field, `src/L/Condensation.lagda.md:5769-5770`, in the exact shape |
| `entryK` in the ChainZ tie (premise `z ∈ K`) | `:595-597` | **SUPPLIED by `arityK`.** The four-step pair chain, MEASURED at `TiesSupply.entryK` (`:685-688`), which is `ChainZ.entryK-tied-zK` applied to `arityK` |
| `arSubK` in the tied form (premise `ar ∈ K`) | `:598-602` | **SUPPLIED by `arityK`.** One application, MEASURED at `TiesSupply.arSubK-tied` (`:691-694`) |

**`tmKeyK` is not replaced by a hypothesis.** The starting
material's `keyValK` is refuted (section 0). The needed key
memberships are derived inside `AtomLeafTied` from `arityK`, the
code slot's membership (`aK` at `:506`, `bK` at `:519`), and the tag
satisfaction bound at the use (`keyK-of`, `:405-427`). `aK` and
`bK` are supplied by `codesK` in the back direction
(`Condensation.lagda.md:4215`, the `(arK , (aK , bK))` binding) and
by the row's own λ-binders in out (`:4195`). So the honest tied
form of `tmKeyK` costs zero hypotheses.

## 3. DID EACH TIE SURVIVE THE REFUTATION ATTEMPT?

1. `entryK` (ChainZ tie): **NOT REFUTED, INFERRED.** The
   `[LJ-1.97]` refutation of the untied form
   (`src/ProbeLJ197A.agda:239-240`) chose `z` = the singleton of
   `pr X X` to force the pair premise; the new `z ∈ K` premise is
   not forceable at the abstract frame (the only candidate, the
   K-slot element, fails `X ∈ X` by `∈-irrefl`). The tie is a
   hypothesis whose supply is MEASURED (`TiesSupply`, section 2).
2. `arSubK` (tied form): **NOT REFUTED, INFERRED.** The `[LJ-1.97]`
   refutation (`:251-254`) chose `ar` = the singleton of `X`; the
   new `ar ∈ K` premise is not forceable at the abstract frame.
   Supply MEASURED as above.
3. `keyValK` (the starting material's tied `tmKeyK`): **REFUTED,
   MEASURED.** `RefuteKeyValK.keyValK-refutes`
   (`src/ProbeLJ1104A.agda:118-120`), GREEN in the same check.
4. The derived `keyK-of`: a derivation, not a hypothesis. It is
   MEASURED inhabited (it typechecks); its premises are the code
   slot's membership (supplied by `codesK`), `arityK`, and the tag
   satisfaction.

No negative rests on an inference: the refutation of `keyValK` is
MEASURED, and the two ties' non-refutability is INFERRED only in
the sense that no refutation term was found; both are supplied by
MEASURED derivations from `arityK`, so their satisfiability does
not rest on the inference.

## 4. THE DD4 ANSWER

The restated row stays generic in its slots. Every set argument is
an `S` variable; the slots are `Fin` positions. The tied forms say
what they mean: `entryK` conditions the closure on `z ∈ K`,
`arSubK` on `ar ∈ K`, and the derived key membership on the tag
satisfaction. `arityK` is one hypothesis serving three facts
(`entryK`, `arSubK`, and the key derivation), exactly the DD4
shape.

**Should `EnvSet` carry `arityK` rather than every row? YES.**
`EnvSetTied` (`:132-251`) already takes `arityK`, `E ∈ K`, and
`ar ∈ K` as parameters and threads them through both directions.
The two tied facts (`entryK` ChainZ, `arSubK`) are then derivable
inside `EnvSet` from `arityK` alone, and stating them per row would
duplicate the same derivations at nine sites. The memberships
`E ∈ K` and `ar ∈ K` must stay parameters: they are row facts
(`EK` from `envK`, `arK` from `codesK` or the out binders), not
`EnvSet` facts. So the DD4 answer is: `EnvSet` should carry
`arityK` plus the two memberships, and derive the ChainZ tie once.
This probe does not rebuild that shape; it measures that the shape
with the row-level ties closes both directions, which is the
precondition for the cheaper one.

## 5. NEGATIVES AND THEIR STATUS

1. The row proves itself in tied form: **MEASURED TRUE.** Exit 0,
   both directions, `src/ProbeLJ1104A.agda`.
2. The out direction closes: **MEASURED TRUE** (`:628-645`).
3. The back direction closes: **MEASURED TRUE** (`:646-676`).
4. The `keyValK` tie of the starting material is satisfiable:
   **MEASURED FALSE** (`RefuteKeyValK`, `:118-120`).
5. The ChainZ tie and the tied `arSubK` are refutable: **INFERRED
   FALSE**; no refutation term was found. No verdict rests on this
   alone: both are supplied by MEASURED derivations from `arityK`.
6. `arityK` is supplied by the consumer: **MEASURED TRUE by the
   source** (`Condensation.lagda.md:5769-5770`).

## 6. ARCHIVE USED

- `_build/lj-1.102-report.md`, read WHOLE, and
  `src/ProbeLJ1102A.agda`, read WHOLE. TOOK the failing EnvSet
  copies, the restated telescope, the `keyValK` shape to refute, and
  the measured failure lines.
- `src/ProbeLJ199A.agda`, read WHOLE, and
  `_build/lj-1.99-report.md`, read WHOLE. TOOK `ChainZ` and its
  pair-chain lemmas; the supply of `entryK` from `arityK`.
- `src/ProbeLJ1100A.agda`, read WHOLE, and
  `_build/lj-1.100-report.md`, read WHOLE. TOOK the zero-cost
  derivations of the tied forms and the row-supply table.
- `src/ProbeLJ197A.agda`, read WHOLE. TOOK the refutation recipes
  and the pair memberships.
- `src/ProbeLJ195A.agda`, read. TOOK the `tmKeyK` refutation shape
  and `∈-irrefl`'s use.
- `src/L/Condensation.lagda.md:4141-4240`, read. TOOK the `MemAgree`
  telescope, out, and back, copied with the tied facts.
- `src/L/Condensation.lagda.md:2764-2874`, read. TOOK `EnvSet`'s
  telescope and both transfers, restated with `arityK`.
- `src/L/Condensation.lagda.md:5734-5770`, read. TOOK `arityK`'s
  exact field type.
- `src/L/Condensation.lagda.md:2884-2970`, `:3979-4140`, read. TOOK
  `TmVal` and `AtomLeaf`, restated with the tied `keyK`.
- `src/L/Condensation/TwelveAgree.lagda.md:167-169`, read. TOOK
  `transK`'s shape (same type as `arityK`).
- `dev/LESSONS.md`, C-38 as extended (`:3427-3511`), C-35
  (`:3200-3242`), C-36 (`:3284-3332`), D-29 (`:3242-3284`), D-30
  (`:3332-3380`), P-i (`:203-262`), P-w (`:3094-3164`), read WHOLE.
  TOOK the satisfiable-telescope standard, the refutation
  discipline, and the consumer-pricing rule.
- `scripts/rules.py --for build`, read all statements.
- `archive/rud-route/`, SHAPE only. Took nothing.

## 7. LITERATURE USED

Banked; nothing spent.

## 8. GATES

- `src/ProbeLJ1104A.agda`: GREEN, exit 0, one process at the C-12
  cap. Two cold runs with the probe interface moved aside: 9.69 s
  total at load 6.66 to 6.93, and 9.67 s total at load 3.60 to 4.17
  (4 users). The second is the figure quoted in section 0. No
  unsolved metas, no holes, no postulates, `--safe`.
- `scripts/lint-agda.py --check src/ProbeLJ1104A.agda`: exit 0.
- `scripts/lint-prose.py --check _build/lj-1.104-report.md`: exit 0.
- No master was touched. `src/L/Condensation/`,
  `src/L/Coding/`, `src/V/`, `src/Everything.lagda.md` untouched.
  `src/L/BoundedSubset.lagda.md` untouched (the sibling agent owns
  it). No `make check`. No commit, no push.
