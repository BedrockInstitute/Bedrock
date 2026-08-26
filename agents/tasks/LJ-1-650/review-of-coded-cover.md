# review-of-coded-cover: the keystone does not reach `CodedCover`

**THIS IS A STOP, AND IT IS THE DELIVERABLE.** The brief orders one term,
`coded-cover-from-keystone`, from `[LJ-1.646]`'s `lset-code-ord` to
`[LJ-1.595]`'s `CodedCover`. **That term is not in `Probe650.agda` and this
file says why.** The probe is green and carries no hole
(`runs/p-final.out`, exit 0 in 2.88 s); the obligation reads `missing`
(`runs/meter-obligation.out`, `1 UNRESOLVED of 1`, `probe_red=False`).

## 1. THE TWO TYPES, AS MAPS

Read side by side, at the lines each was taken from.

```
lset-code-ord   (agents/tasks/LJ-1-462/Probe462.agda:118-121)
    (c : Code) → IsOrd (val c) → Σ[ d ∈ Code ] (val d ≡ Lset (val c))

CodedCover      (agents/tasks/LJ-1-595/Probe595.agda:353-357)
    (c : Code) → Σ[ d ∈ Code ] (IsOrd (val d) × val c ∈ Lset (val d))
```

**The keystone takes an ORDINAL code and returns a LEVEL code. `CodedCover`
takes ANY code and returns an ORDINAL code that covers it.** The keystone's
input slot is a hypothesis `CodedCover`'s caller does not carry, and the
keystone's output value is `Lset (...)`, which is not what `CodedCover`'s
output slot asks for.

## 2. AGDA SAYS IT, AND I DID NOT ARGUE IT

**FIRST SLICE, THE DIRECT APPLICATION** (`runs/NO-KEYSTONE-DIRECT.agda.txt`,
`runs/nokey-1.out`, exit 42 in 3.40 s). The obligation attempted the only
way the keystone can be applied at the code the consumer is given:

```
NoKeystone650.agda:36.36-40: error: [UnequalTerms]
IsOrd (fst (Q.T.val c)) →
Σ-syntax Q.T.Code (λ d → fst (Q.T.val d) ≡ Lset (fst (Q.T.val c)))
!=<
Σ Q.T.Code
(λ d →
   IsOrd (fst (Q.T.val d)) ×
   ⟨ fst (Q.T.val c) ∈ˢ Lset (fst (Q.T.val d)) ⟩)
```

**SECOND SLICE, WHERE THE KEYSTONE DOES APPLY** (`runs/NO-KEYSTONE-ORD.agda.txt`,
`runs/nokey-2.out`, exit 42 in 3.41 s). Restrict to an ordinal-valued code,
so the keystone's own hypothesis is paid, take its code, and offer the
caller's `IsOrd` to the ordinality slot:

```
NoKeystoneOrd650.agda:47.44-46: error: [UnequalTerms]
(Lset (fst (Q.T.val c))) != (fst (Q.T.val c)) of type
(Cubical.HITs.CumulativeHierarchy.Base.V ℓ)
when checking that the expression oc has type
IsOrd (Lset (fst (Q.T.val c)))
```

**The slot demands `IsOrd (Lset α)`.** The covering slot demands
`α ∈ Lset (Lset α)` beside it. Neither is in the tree, and
`keystone-row-at-ordinal` (`Probe650.agda:417-427`) is the whole keystone
route to one row of `CodedCover` with both of them ADDED as hypotheses: it
is green, and it shows exactly what the route costs.

## 3. AND THE ROW IT BUYS IS ALREADY FREE

`coded-cover-at-ordinal` (`Probe650.agda:235-260`) pays that same row,
**unconditionally, with no keystone, no level formula and no extra fact.**
So even where the keystone applies, the keystone route is strictly worse
than the route this task built.

## 4. WHAT THE TRACE GOT RIGHT, AND WHAT IT GOT WRONG

`[LJ-1.595]` traced its residue to "the level formula read at the stage"
(`agents/tasks/LJ-1-595/lj-1.595-report.md:171-179`). **The destination is
right. The address is wrong.**

- **`[LJ-1.646]` is a SEMANTIC statement.** It says a level HAS a code. It
  hands the consumer no syntax.
- **`CodedCover` can only be paid with SYNTAX.** The tree makes a code in
  exactly two ways, `base` and `wit` (`src/L/Hull.lagda.md:72-74`), and
  `wit` consumes a formula. `skolemCode` (`Probe650.agda:118-149`) is that
  route made untruncated, and it is this task's W3.
- **So the keystone sits BESIDE `CodedCover`, not above it.** Both are
  consequences of the level FORMULA, and neither is a consequence of the
  other.

`coded-cover-from-level` (`Probe650.agda:385-386`) is that claim, green:
one formula in two variables, sound and complete at the stage, gives the
WHOLE of `CodedCover`.

## 5. THE CORRECTION THE QUEUE NEEDS

**`[LJ-1.650]` IS CHEAPER FROM THE TRUE KEYSTONE THAN `[LJ-1.646]` IS.**
The level formula reaches `CodedCover` with `∃̇` and nothing else
(`internal-from-level`, `Probe650.agda:352-382`). It reaches
`lset-code-ord` only through a constant substituted for the index, which
`[LJ-1.595]` recorded as a renaming it did not price
(`agents/tasks/LJ-1-595/lj-1.595-report.md:167-169`). **The queue plans the
expensive one first.**

## 6. WHAT I DID NOT PROVE

**I did not prove `CodedCoverFromKeystone` FALSE.** I proved that no term
composes it out of the keystone and the tree, and I measured the two facts
any such term must add. A refutation of the type itself is a different
task and this one does not claim it.

**C-42.** A refutation measures the site it names. This one names ONE site,
`[LJ-1.650]`'s obligation. It says nothing about how many other queued
tasks take `[LJ-1.646]` as their keystone. `[LJ-1.647]` is one
(`agents/tasks/LJ-1-647/Probe647.agda:165-167`) and `[LJ-1.649]` measured a
second cost there (`agents/tasks/LJ-1-649/lj-1.649-report.md:190-197`).
**The sweep is the next action and it is not this task's scope.**
