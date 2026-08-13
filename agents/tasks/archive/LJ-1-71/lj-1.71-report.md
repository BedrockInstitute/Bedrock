# LJ-1.71: consume TwelveAgree, which nothing has ever consumed

Status: COMPLETE, written incrementally per C-22. No commit, no push.
ASD-STE100. This report is `_build/lj-1.71-report.md`.

## 0. THE VERDICT

**THE INSTANTIATION DOES NOT GO THROUGH. STOP, per the pre-fixed abort
criterion (D-1).** The first telescope fact of `TwelveAgree`
(`src/L/Condensation.lagda.md:6415`) cannot be discharged at
`SatGraphAgree`'s frame. The frame proves that fact's type uninhabited,
and the proof is machine-checked in `src/ProbeLJ171A.agda:142-146`
(`tagEq-refutes`).

The index that does not match: `tagEq` at the pair `(k = 1,
N = suc^6 N0)`. The frame pins `fst (lookup (suc^6 N0) (f ∷ e ∷ d ∷ γ))`
to `fst (numeralL 0)` (`KFacts.tagEq0`, `src/L/Condensation.lagda.md:
5678`), and the telescope's `tagEq 1 (suc^6 N0)` demands
`fst (numeralL 1)` at the same slot. The two together refute
`numeralL 0 ≡ numeralL 1`, so no term of the telescope's `tagEq` type
exists at the frame.

**The slot fix of [LJ-1.55] HOLDS.** The frame's row facts land at the
telescope's slots definitionally: `tagEq0'`, `numK0'`, `innerK'`,
`pairK'`, `num1K'`, `codesK'` and `codesK-un'` all check
(`src/ProbeLJ171A.agda:118-158`). The obstruction is the over-general
statements of the [LJ-1.70] telescope, not the slot convention.

`twelve-out` and `twelve-back` have NOT left `SatGraphAgree`'s
telescope. No master was edited. The tree is unchanged apart from this
report and the probe.

The measured-cost section does not exist: the abort criterion stops the
dispatch before any measurement. No profile ran, so the four built-tree
fact types are not re-attributed. `levelIn`, `cover` and the post-leaf
five are untouched.

## 1. THE TERM THIS DISPATCH TRIES TO WRITE

The change replaces `SatGraphAgree`'s two parameters `twelve-out`
(`src/L/Condensation.lagda.md:6770`) and `twelve-back` (`:6773`) with
an instantiation of `TwelveAgree` at the graph frame `(f ∷ e ∷ d ∷ γ)`,
using `T12.out` and `T12.back` in `body-out` (`:6876`) and `body-back`
(`:6928`).

The term this dispatch could not write is the `tagEq` argument of that
instantiation:

```text
(k : ℕ) (N : Fin (11 + n)) → fst (lookup N (f ∷ e ∷ d ∷ γ)) ≡ fst (numeralL k)
```

The frame's hypotheses make that type uninhabited. The term does not
exist, so neither does the instantiation.

## 2. THE EVIDENCE

The probe `src/ProbeLJ171A.agda` carries `SatGraphAgree`'s telescope
verbatim (`module Frame`, `:69-113`), including `twelve-out` and
`twelve-back`, so the frame is exactly the master's frame. It checks
GREEN at the C-12 cap:

```text
GHCRTS="-A64m -I0 -M8g" agda -i . -i _build/2.8.0/agda/src src/ProbeLJ171A.agda
exit 0, load 4.66 (4 users), warm dependencies, cold probe
```

The measured pieces:

1. `tagEq0'` (`:118-120`): the frame's `KFacts.tagEq0` is the
   telescope's `tagEq 0 (suc^6 N0)` at the graph frame, definitionally.
   The suc^6 lift of `N0` at `(f ∷ e ∷ d ∷ γ)` is the suc^3 lift at
   `γ`, which is exactly `KFacts`' `N0` slot. MEASURED.
2. `numK0'`, `innerK'`, `pairK'`, `num1K'`, `codesK'`, `codesK-un'`
   (`:122-158`): the same definitional lift holds for every fact the
   frame carries. MEASURED.
3. `numeral0≠numeral1` (`:128-129`): `fst (numeralL 0) ≢
   fst (numeralL 1)`, through the delivered `numeralL-inj`
   (`src/L/Coding/Model.lagda.md:370-372`). MEASURED.
4. `tagEq-refutes` (`:142-146`): given the frame and a hypothetical term
   of the telescope's `tagEq` type, `⊥`. The frame proves the type
   uninhabited. MEASURED.

The frame's telescope is `KFacts` (twenty-nine fields,
`src/L/Condensation.lagda.md:5677-5706`) plus `codesK`, `unCodesK`,
`closedEntryK`, `domEntryK`, `domK` and `witK` (`:6776-6805`).
`TwelveAgree`'s telescope is forty-seven facts (`:6415-6588`). The
frame supplies five fact types in full (`innerK`, `pairK`, `codesK`,
`codesK-un`, `num1K`, machine-checked), and the row instances of `tagEq`
and `numK` match by the same lift (`k = 0` machine-checked in the probe;
rows 1..11 are the same shape). The other forty fact types (`valK`
`:6428` through `consK-allin` `:6588`) are absent from the frame's
telescope.

The same fact in numbers: the frame has 35 facts. The telescope demands
47. The twelve row modules inside `TwelveAgree` (`MemAgree` `:4117`
through `ExInAgree` `:4788`) take the union telescope as parameters, so
no consumer can instantiate `TwelveAgree` with fewer than 47 facts.

## 3. NEGATIVES AND THEIR STATUS

1. The instantiation goes through: **MEASURED FALSE**. The frame proves
   the telescope's `tagEq` type uninhabited (`src/ProbeLJ171A.agda:
   142-146`). This negative sets the verdict.
2. The frame supplies `tagEq` as stated: **MEASURED FALSE**. Same
   refutation.
3. The frame supplies `numK` as stated: **INFERRED FALSE**. The frame
   has `numK0`..`numK11` only; the telescope demands `numK k` for every
   `k : ℕ`, and the frame's hypotheses say nothing about `numeralL k`
   for `k > 11`. Absence is not machine-checked, so this negative sets
   no verdict.
4. The frame supplies the other forty fact types: **INFERRED FALSE**.
   They are not parameters of the frame, and none is derivable from its
   hypotheses: they are site facts about arbitrary values in `K`. No
   verdict rests on this.
5. The slot fix of [LJ-1.55] fails at the graph frame: **MEASURED
   FALSE**. The lifts check definitionally (`tagEq0'` etc.). The fix
   holds.

The deciding claim of the verdict is item 1, MEASURED.

## 4. THE DD4 ANSWER

The [LJ-1.70] finding stands: the frame states its facts at the L
tower's slots, so the J tower needs a second statement rather than a
reuse. Wiring the consumption does NOT change that. The reason is
MEASURED at the L tower's own statement: the consumption could not be
wired, because `TwelveAgree`'s `tagEq` is false at the consumer's frame.
The J-tower consequence (a second statement) is unchanged, INFERRED.

The dispatch adds one fact to the DD4 ledger: the L tower's shared
statement carries a measured defect (`tagEq`), so a J tower that reused
the same statement shape would inherit it at every site at once (D-29).

## 5. THE CONVERGENCE ANSWER

NOT CLOSING. `TwelveAgree` remains unconsumed, and its first consumer
audit convicted its own statements: `tagEq`
(`src/L/Condensation.lagda.md:6415`) is false at the graph frame,
MEASURED, and `numK` (`:6416`) is stated beyond what any per-row fact
block supplies, INFERRED. The graph frame also carries only 35 of the
47 facts, INFERRED. This is the C-35 outcome the dispatch was built to
find: a green, cheap, unconsumed module whose first consumer asks it to
mean something.

The repair is not attempted, per the abort criterion. Its shape is
visible: state the tag-dependent facts per row, as `KFacts` already does
(twelve `tagEq` fields, twelve `numK` fields), and give the graph frame
the union telescope it lacks. Neither change is made here.

No measurement ran, so no verdict changes on the P-w class (c) question.

## 6. ARCHIVE USED

- `_build/lj-1.70-report.md`, read WHOLE. TOOK the frame shape, the
  forty-seven fact count, the P-w class (c) target and the heap walls.
  The telescope it delivered is what this dispatch convicts.
- `_build/lj-1.55-report.md`, read WHOLE, and
  `src/ProbeLJ155B.agda:788-979`. TOOK the slot fix and the composition
  this dispatch exercises for the first time in a master. The slot fix
  holds; the composition still cannot be fed.
- `_build/lj-1.54-report.md`, section 1. TOOK the frame mismatch
  (`suc B = zero`) that the slot fix repaired.
- `_build/lj-1.62-report.md`, sections 2-3. TOOK `SatGraphAgree`'s
  placement and the `KFacts` content-class change.
- `dev/LESSONS.md`, P-w as amended (`:3094-3256`), C-35 (`:3200-3242`),
  P-t (`:2601-2632`), P-o (`:2509-2532`), P-m (`:2460-2482`),
  P-n (`:2483-2508`), P-q (`:2633-2669`), P-c (`:71-94`), R-36
  (`:808-829`), R-38 (`:829-885`), R-35 (`:782-808`), R-40
  (`:929-982`), I-5 (`:1196-1223`), C-12 (`:2075-2102`), C-22
  (`:2237-2278`), C-31 (`:1855-1895`), C-32 (`:2947-2987`), C-33
  (`:2987-3037`), C-34 (`:3171-3200`), C-36 (`:3284-3332`), C-37
  (`:3381-3425`), D-1 (`:1038-1078`), D-8 (`:1377-1410`), D-10
  (`:1316-1377`), D-26 (`:1676-1702`), D-29 (`:3242-3284`), D-30
  (`:3332-3381`), P-u (`:2908-2947`), P-v (`:3037-3094`), each read
  WHOLE.
- `archive/rud-route/`, SHAPE only. Took nothing.

## 7. LITERATURE USED

Nothing in the literature prices a spelling. One line, nothing spent.

## 8. GATES

`scripts/check-fences.py --check` clean (84 masters).
`scripts/lint-prose.py --check` exit 0 on `src/L/Condensation.lagda.md`.
`scripts/lint-agda.py --check` exit 0 on `src/L/Condensation.lagda.md`.
`scripts/ledger.py --brief`: standing 27,673 lines over 82 masters,
measured from HEAD.
`src/ProbeLJ171A.agda` checks green at the C-12 cap, one process, load
4.66 (4 users).
No master was edited. No `make check`. No commit, no push. The working
tree carries this report and the probe, both gitignored by design
(`_build/`, `src/Probe*.agda`).
