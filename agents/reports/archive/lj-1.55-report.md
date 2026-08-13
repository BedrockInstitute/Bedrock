# LJ-1.55: the agreements' slot convention, and the last two atoms

Status: PARTIAL, written incrementally per C-22. ASD-STE100.
No commit. No push. The working tree carries two pre-existing edits:
`src/L/BoundedSubset.lagda.md` (the LJ-1.54 placement) and
`dev/PLAN.md` (the orchestrator's dispatch rows). This dispatch edits
`src/L/Condensation.lagda.md` (the slot generalization) and writes
`src/ProbeLJ155A.agda`, `src/ProbeLJ155B.agda`,
`src/ProbeLJ155C.agda`.

## 0. THE LEDGER (live)

| hypothesis | status | what it still needs |
|---|---|---|
| `levelIn` | NOT DISCHARGED | the adequacy chain after the leaf reduction |
| `cover` | NOT DISCHARGED | the adequacy chain plus the least-delta selection |

## 1. THE SLOT ANSWER: NO, K-ONLY DOES NOT REACH THE TWELVE FRAME

The answer is NO to the brief's literal question, and the test is
machine-checked in `src/ProbeLJ155A.agda`.

1. The K-only parameterization keeps the row at
   `(suc C) (suc T) (suc B) (suc N) (suc K)`.  The `twelveB` frame
   puts B at slot zero.  Matching them is the equation
   `suc B ≡ zero`, and `no-suc-zero` (`ProbeLJ155A:59`) proves it has
   no solution in Fin.  K is not the only hard-coded slot: the whole
   row tuple sits under the suc convention with slot 0 reserved for E.
   The N, t0, t1 and K lifts are `suc^6` at the twelve frame, so no
   frame of the suc-convention shape reproduces the twelve row either.
2. The fix that does reach the frame is the FULL slot
   parameterization: `(C T B N K t0 t1 : Fin m) (γ : S ^ m)`, row =
   `rowBndAt C T B N K t0 t1`, facts read `lookup C γ` and
   `lookup K γ`.  `BotAgreeGen` (`ProbeLJ155A:71`) typechecks with
   the master's `BotAgree` proof body verbatim, renamed slots only.
   `TwelveBot` (`ProbeLJ155A:104`) instantiates it at the twelve
   frame's Bot row, C = 2, T = 1, B = 0, N = `suc^6 N7`, K =
   `suc^6 K`, with no re-indexing, and proves both directions.

So the change is still a mechanical signature change with the proofs
untouched, but it is K-and-every-slot, not K alone.  This is also the
DD4 move: the agreement becomes instantiable at any frame, and the J
tower inherits a frame-generic agreement layer rather than a
class-carrier layer plus a re-indexing shim.

## 1b. THE MASTER CHANGE: DONE, GREEN

All thirteen agreement modules (`BotAgree`, `PropAgree`, `AndAgree`,
`OrAgree`, `TopAgree`, `NegAgree`, `ForallAgree`, `ExistAgree`,
`ClauseAgree`, `MemAgree`, `AllInAgree`, `ExInAgree`, `ImpAgree`,
`EqAgree`), the two shared `keyU`/`succU` helpers and the three leaf
modules (`AtomLeaf`, `ImpLeaf`, `BndLeaf`) now take the full row-slot
tuple `(C T B N K t0 t1 : Fin m)` at the row frame `γ : S ^ m`, read
`lookup C γ` / `lookup K γ`, and instantiate the row at the same
slots.  The proofs are unchanged apart from the slot renames
(`suc^(d+1) X` to `suc^d X` at depth-d frames, K-at-depth `suc^d zero`
to `suc^d K`).  `src/L/Condensation.lagda.md`.

Cold typecheck, C-12 caliber, one process, quiet machine:

| module | before (single run) | after (single run) |
|---|---:|---:|
| `L.Condensation` (cold, user s) | 56.43 | 53.63 |
| `L.BoundedSubset` (cold, user s) | 14.66 | 14.35 |

The three-run figures with spreads are in section 3; the single runs
above bracket the drift.

The consumer's import surface (`DefBodyB`, `Δ₀-DefBodyB`, `SatGraphB`)
is unchanged; `BoundedSubset` rechecks green.

## 1c. TWELVEAGREE COMPOSES AT THE CONSUMER'S FRAME: DONE, GREEN

`src/ProbeLJ155B.agda` instantiates all twelve generalized agreements
at the twelve frame (C = 2, T = 1, B = 0, N = `suc^6 Ni`,
K = `suc^6 K`, t0/t1 = `suc^6 t0`/`suc^6 t1`, arity `11 + n`), one
per-row module each collecting its own site facts, and `TwelveAgree`
threads the conjunction both directions against `twelveAt 2 1 0`.
No re-indexing layer exists anywhere: the slot fix removed it.  The
probe typechecks; the row instantiation is pure parameter passing and
the composition is conjunction projection.

## 2. THE TWO REMAINING ATOMS

## 2a. TWELVEAGREE: BUILT, GREEN (the slot fix's consumer test)

`src/ProbeLJ155B.agda` instantiates all twelve generalized agreements
at the `twelveB` frame and threads the conjunction.  Details in
section 1c.  The composition is conjunction projection only; no
re-indexing exists.

## 2b. WITNESSAGREE: BLOCKED, WITH EVIDENCE (C-36 terms)

The pieces of `hasWitnessBS A x K N0..N11` against
`hasWitnessAt A x` (`Condensation:1693`, `CodeSet:240`) decompose into
closedness, shapedness and the domain transfer.  The diagnostics are
machine-checked in `src/ProbeLJ155C.agda`:

1. `bothSameB C ≡ bothSameAt C` definitionally
   (`ProbeLJ155C:35`, `Condensation:1538`, `Model:2084`).
2. `oneSameB C` is NOT the machine's `oneSameAt C`:
   `Condensation:1549` reads `appAt (suc^3 C) (suc^2 zero) (suc zero)`
   (the pair (c, ar) at the frame `a ∷ ar ∷ c ∷ γ`), while
   `Model:2088` reads `appAt (suc^3 C) (suc zero) zero` (the pair
   (ar, a)).  The two definitions differ at the appAt argument slots,
   so no refl check passes; the observation is recorded at
   `ProbeLJ155C:40-44`.  The brief's premise for the eight frames,
   "the same formula on both sides", is FALSE for the oneSame frame:
   the story's closedness relation for the negation row reads the
   code slot where the machine reads the argument slot.  The story's
   `oneSuccB`/`succSndB` bodies agree with the machine's and differ
   only by the bounded quantifier, as expected
   (`Condensation:1554-1570`, `Model:2090-2094`).
3. The domain transfer is one-way at the generic frame: `domB f d K`
   (`Condensation:1727`) is the story's bounded form "x in K ->
   (x in dom f <-> x in d)"; `domAt f d` (`Model:279`) is the
   machine's unbounded form.  `domAt -> domB` is proved under a site
   fact giving the witness y in K (`ProbeLJ155C:66-86`); `domB ->
   domAt` needs every domain element in K and is false at the generic
   frame.  The graph frame's own bounded quantifiers must supply the
   missing memberships; that wiring is SatGraphAgree content, not a
   generic lemma.

The closedness transfer therefore cannot be built as the brief names
it: the story's `oneSameB` disagrees with the machine at the
appAt-argument slots.  The recommended cure is the one-line fix
`oneSameB C = appAt (suc^3 C) (suc zero) zero` (and its `Δ₀` copy at
`Condensation:1552`), which makes the frame "same formula on both
sides" and unblocks the eight-frame composition; then the eight frames
are the delivered `UnaryShape`/`BinaryShape` pattern plus the
bounded-existential rel transfers (the oneSucc/succSnd case).  I did
not edit the story's semantics without the ruling.

The shapedness transfer, `SatGraphAgree` (TwelveAgree + closedness +
domain + pin-equality + the three existential-frame transfers) and
`LeafAgree` rest on the blocked pieces and were not written; their
precise statements are in section 1 of `_build/lj-1.54-report.md`.

## 3. THE RATES

Caliber: C-12 `GHCRTS="-A64m -I0 -M8g"`, user seconds from
`/usr/bin/time -p`, cold module (the module's own interface moved
aside before EVERY run), dependencies warm, one process, quiet
machine.  Three completed runs each; no heap exhaustion, no
interruption.

| module | runs, user s | mean | spread | in-fence lines | rate |
|---|---:|---:|---:|---:|---:|
| `L.Condensation` (whole, cold) | 58.85 / 59.12 / 56.28 | 58.08 | 2.84 (4.9 pc) | 4,632 | 0.01254 |
| `L.Condensation` cone (warm) | 1.73 / 1.69 / 1.69 | 1.70 | 0.04 (2.4 pc) | 0 | n/a |
| `ProbeLJ155B` (TwelveAgree, cold) | 13.72 / 13.82 / 13.62 | 13.72 | 0.20 (1.5 pc) | 903 | n/a |
| `ProbeLJ155B` cone (warm) | 1.49 / 1.40 / 1.41 | 1.43 | 0.09 (6.3 pc) | 0 | n/a |

The whole-file rate 58.08 / 4,632 = 0.01254 s per line is under the
DD24 live bar 0.012716.  The change is line-neutral (4,632 in-fence
non-blank lines before and after) and check-cost-neutral within drift:
the same-day before figure was 56.43 s, and the three after runs span
56.28 to 59.12.  The marginal rate of the new composition content is
(13.72 - 1.43) / 903 = 0.0136 s per line, the instantiation class
(P-m), against the leaf atoms' parameterized 0.0013 of `[LJ-1.54]`.
The slot renames themselves are the parameterized class and cost
nothing measurable.

## 4. THE DD4 ANSWER

The fix is the DD4 move, bigger than the brief's K-only guess: the
agreement layer now takes the full row-slot tuple at the row frame, so
one copy serves the class carrier, the graph frame and any future
frame, with no re-indexing shim.  What the J tower inherits: the same
thirteen agreements, `keyU`/`succU` and the three leaf modules, all
frame-generic in the master; the twelve-row composition then threads
at any consumer frame without per-frame shims.  The oneSameB finding
shows the remaining per-tower residue: the story's closedness relation
body disagrees with the machine's, and the generic domB-to-domAt
direction needs the graph frame's own bounded quantifiers.  Both are
per-tower content that the J tower's own closedness/domain
restatements must get right at their own frame.

## 5. THE CONVERGENCE ANSWER

The first half is CLOSING.  The slot question is settled with a
machine-checked answer, the master change is green and line-neutral,
and the twelve agreements now compose at their consumer's frame with
no re-indexing.  That removes the single measured blocker named by
`[LJ-1.54]` and re-prices the composition as conjunction threading.

The second half is NOT closing yet, and the reason is new evidence,
not renaming: the closedness half of `WitnessAgree` rests on a false
premise (`oneSameB` reads different appAt slots than `oneSameAt`), and
the domain transfer's story-to-machine direction needs the graph
frame's memberships.  These are the same class of stop the brief's
rules want surfaced: a named shape that was never exercised because
the agreement layer had zero consumers.  The next dispatch is
well-defined: rule on the one-line `oneSameB` fix, then build the
eight-frame closedness transfer and the shapedness transfer, then
`SatGraphAgree` and `LeafAgree` on the now-green `TwelveAgree`.

## 6. ARCHIVE USED

- `_build/lj-1.54-report.md`, read WHOLE (`:1-200`).  Took the four
  built atoms, the `TwelveAgree` re-indexing finding (`:52-59`), the
  measurement protocol (`:135-145`), the DD4 split (`:180-193`).
- `src/ProbeLJ154A.agda`, read WHOLE.  Took the
  `TagAgree`/`KeyAgree`/`EnvOneAgree`/`DefinesAgree` shape and the
  import/usage conventions for a probe.
- `_build/lj-1.53-report.md`, read WHOLE.  Took the wall-1 residual
  statement (`:74-88`) and the wall-2 placement.
- `_build/lj-1.52-report.md`, read WHOLE.  Took the
  `StepAgree`/`ApproxAgree`/`GraphAgree`/`Adeq` decomposition
  (`:18-60`).
- `_build/gch-design-audit.md`, read the two-spelling section
  (`:300-380`).  Took the finding that the agreement layer has zero
  consumers (`:331`) and the "bounded form from birth" recommendation
  (`:360-380`).
- `src/L/Coding/Model.lagda.md`, read the clause/closedness/domain
  definitions (`:989-1030`, `:2043-2095`, `:2170-2195`, `:270-300`).
- `src/L/Coding/Graph.lagda.md`, read `twelveAt` (`:94-111`).
- `src/L/Coding/CodeSet.lagda.md`, read `hasWitnessAt` (`:240-245`).
- `archive/rud-route/`, SHAPE only, per the brief.

## 7. LITERATURE USED

None bears on the slot convention; it is this tree's own indexing
choice, settled by the frame arithmetic and the machine checks above.
`_build/literature/dev2.txt:1372-1385` and `dev/literature/devlin-II5.md`
Step C bear on the leaf's mathematics, which this dispatch did not
reach; one line spent, as the brief allows.
