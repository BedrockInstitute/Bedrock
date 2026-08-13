# LJ-1.95: refute tmKeyK, or show it inhabitable

Status: COMPLETE, written incrementally per C-22. No commit, no push.
ASD-STE100. This report is `_build/lj-1.95-report.md`.

## 0. THE VERDICT

**tmKeyK is REFUTED, MEASURED.** The type is empty at every frame. The
refutation typechecks at `src/ProbeLJ195A.agda:45-48` in 1.52 s total,
exit 0, one process, at the C-12 cap. Load average 3.75 (4 users) at
start and end. Per the pre-fixed abort criterion (D-1), STOP here.
`valK` was NOT attempted. The same-shape scan of the other 37 names
`valK-un` only. No master was touched.

The deciding negative is MEASURED: the hypothesis type has no
inhabitant at any `n`, any `K`, any `γ'`.

## 1. THE REFUTATION TERM

The hypothesis, read from the source at
`src/L/Condensation/TwelveAgree.lagda.md:96`:

```agda
(tmKeyK : (k : S) → ⟨ fst k ∈ fst (lookup (suc (suc (suc (suc (suc (suc K)))))) γ') ⟩)
```

It has no premise. Apply it at `k = lookup (suc⁶ K) γ'`, the element
at the K slot itself. Let `X = fst (lookup (suc⁶ K) γ')`. The
conclusion is `⟨ X ∈ X ⟩`, refuted by the delivered `∈-irrefl`
(`src/V/Hierarchy.lagda.md:155`). No other hypothesis of the frame is
used. `n`, `K` and `γ'` are arbitrary, so the type is empty at every
frame.

The term (`src/ProbeLJ195A.agda:37-48`):

```agda
module Refute (n : ℕ) (K : Fin (5 + n)) (γ' : S ^ (11 + n)) where

  X : S
  X = lookup (suc (suc (suc (suc (suc (suc K)))))) γ'

  tmKeyK-refutes : (tmKeyK : (k : S) →
                      ⟨ fst k ∈ fst (lookup (suc (suc (suc (suc (suc (suc K)))))) γ') ⟩)
                 → Empty.⊥
  tmKeyK-refutes tmKeyK = ∈-irrefl (fst X) (tmKeyK X)
```

The check:

```text
GHCRTS="-A64m -I0 -M8g" agda -i . -i _build/2.8.0/agda/src src/ProbeLJ195A.agda
exit 0, 1.52 s total, 0.68 s user, cold probe, warm dependencies,
load average 3.75 (4 users)
```

The blast radius, read from the source: all three split masters state
`tmKeyK` as a telescope hypothesis. `LowerAgree`
(`src/L/Condensation/LowerAgree.lagda.md:98`), `UpperAgree`
(`src/L/Condensation/UpperAgree.lagda.md:88`) and the composer
(`TwelveAgree.lagda.md:96`). The composer passes it into both sixes
(`TwelveAgree.lagda.md:253`, `:264`, and again in `out`/`back` at
`:279`, `:288`, `:300`, `:309`). No instantiation of any of the three
exists as stated.

## 2. THE SAME-SHAPE SCAN OF THE OTHER 37

The scan covers the 37 unsuppliable hypotheses left after removing
`tmKeyK` and `valK` from the 39 of `[LJ-1.93]`. The shape is: a
conclusion that is a membership `⟨ fst y ∈ slot ⟩` for a bound `y`
that appears in no premise.

One of the 37 has the shape:

- `valK-un`, `src/L/Condensation/TwelveAgree.lagda.md:89-91`. The
  conclusion is universal over `yc`; the premises mention `c`, `ar`,
  `a` and `k`, never `yc`.

`valK` itself (`:86-88`) has the same shape, but it is the brief's own
second candidate and is not one of the 37.

The other 36 do not have the shape. Either the conclusion has no free
variable (`t0eq` `:92`, `t1eq` `:93`, `t0K` `:94-95`, `keyK-neg`
`:201-204`, `succK-allin` `:224-228`, `keyK-allin` `:229-235`), or the
conclusion variable occurs in a premise. The satisfaction-premise
family (`envK-*`, `arSubK-*`, `envInK-*`, `valV`, `valW`, `wKfact`,
`subK-*`, `consK-*`) mentions its conclusion variable only as an
environment slot in the premise. That is not the same shape. `succK`
and `keyK-un` (`:205-208`) have no premise and no free-variable
membership conclusion.

This scan is a static reading of the source, not a machine check. The
negative "only `valK-un` has the shape" is INFERRED. It sets no
verdict.

## 3. THE DD4 ANSWER

The defect is in the shared frame. `tmKeyK` is one telescope fact of
the split's union statement and of both partials, so the L tower
inherits the empty type at three sites at once (D-29,
`dev/LESSONS.md:3242-3284`). The composer is generic in the 69 facts
and slots (`_build/lj-1.76-report.md` section 6). A J tower that
states the same telescope at its own frame would inherit the same
empty type. That J-side consequence is INFERRED: no J-site exists in
this tree, and nothing was machine-checked there. The L-side mechanism
is MEASURED.

The finding matches C-38 as extended
(`dev/LESSONS.md:3427-3511`): a closure hypothesis about a bounding
set `K` must be conditional, `(a : S) → a ∈ <bound> → a ∈ K`. A
quantifier over arbitrary sets with no membership premise is refuted
by regularity, always. `tmKeyK` is that unconditional shape, now
machine-checked at its own site.

A refutation is not shared code. The defect is in the frame's
telescope, which is the shared content, not in a proof body.

## 4. NEGATIVES AND THEIR STATUS

1. `tmKeyK` has an inhabitant at some frame: **MEASURED FALSE**. The
   type is empty at every `n`, `K`, `γ'`
   (`src/ProbeLJ195A.agda:45-48`). This negative sets the verdict.
2. `AbstractFrame` has an instantiation: **MEASURED FALSE**. The frame
   states the empty type as a parameter at
   `src/L/Condensation/TwelveAgree.lagda.md:96`, so no instantiation
   can supply it. The no-instantiation follows from the empty type.
3. `LowerAgree` and `UpperAgree` have instantiations: **MEASURED
   FALSE**. Same reason, at
   `src/L/Condensation/LowerAgree.lagda.md:98` and
   `src/L/Condensation/UpperAgree.lagda.md:88`.
4. Another of the other 37 has the same shape: **INFERRED FALSE**.
   The static scan names `valK-un` only. No verdict rests on it.
5. `valK` is refuted: **NOT CLAIMED**. It was not attempted, per the
   abort criterion. A refutation would need code-shaped members of the
   code slot, which the frame does not supply. Whether that block is a
   missing lemma or a real obstacle is undecided.
6. The brief's foundation reading: **MEASURED TRUE**. The argument
   applies, and it is simpler than the reading: the witness is the
   K-slot element itself, not a singleton over it.

## 5. ARCHIVE USED

- `_build/lj-1.93-report.md`, read WHOLE. TOOK the 39-fact
  unsupplied list, the 37 count, and the frame mismatch.
- `src/ProbeLJ193B.agda`, read WHOLE. TOOK the consumer's frame and
  the `tmKeyK` unsupplied position.
- `src/ProbeLJ193C.agda`, read WHOLE. TOOK the representative
  mismatch discipline.
- `_build/lj-1.77-report.md`, read WHOLE. TOOK the refutation shape
  and the C-12 invocation line. This probe is its one-step simpler
  cousin: `tmKeyK` needs no singleton construction.
- `_build/lj-1.71-report.md`, read WHOLE. TOOK the `tagEq`
  refutation pattern and the MEASURED/INFERRED split.
- `_build/lj-1.76-report.md`, read WHOLE. TOOK the 69-fact frame, the
  43/43 split, and the generic-frame DD4 claim.
- `src/L/Condensation/TwelveAgree.lagda.md`, read whole. TOOK the
  frame text at `:45-243` and every line number quoted here.
- `dev/LESSONS.md`, C-38 as extended (`:3427-3511`), C-35
  (`:3200-3242`), C-36 (`:3284-3332`), D-29 (`:3242-3284`), each read
  WHOLE. TOOK the discharge standard and the conditional-closure rule
  that `tmKeyK` violates.
- `dev/LESSONS.md`, the remaining briefed entries read WHOLE: D-8,
  D-10, D-26, D-30, C-31, C-32, C-33, C-34, C-37, P-c, P-i, P-o,
  P-q, P-t, P-u, P-v, P-w, R-36, R-38, plus the build and probe rule
  bundles via `scripts/rules.py`.
- `archive/rud-route/`, SHAPE only. Took nothing.

## 6. LITERATURE USED

Nothing in the literature prices a hypothesis in our own frame. This
is a fact about this tree's statements. Banked; nothing spent.

## 7. GATES

- `scripts/lint-agda.py --check src/ProbeLJ195A.agda`: exit 0.
- `scripts/lint-prose.py --check _build/lj-1.95-report.md`: exit 0.
- Probe check: exit 0, 1.52 s total, 0.68 s user, one process, cap
  `-M8g`, load average 3.75 (4 users) at start and end. The first
  attempt exited 42 on `NotInScope _^_`; the fix opened
  `FOL.Absoluteness.Single` for the environment power, as the masters
  do. That was a scope fix, not a wall.
- No `make check`. No commit, no push. No master was edited.
- The working tree carries the probe and this report, both gitignored
  by design, plus the pre-existing `dev/PLAN.md` modification.
  `src/Everything.lagda.md`, `src/L/Coding/` and `src/V/` are
  untouched.
