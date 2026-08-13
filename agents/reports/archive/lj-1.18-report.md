# LJ-1.18: probe of the meta term algebra, fourth shape

## 1. THE VERDICT

**GO**, 116 probe lines. The arity-one case closes at hull parameters, up
to one missing export: the junk element `∅ ∈ˢ Lset α` (a finding, priced,
true at every limit stage). The probe is `src/ProbeLJ118.agda`, 116
non-blank lines. It is untracked and throwaway.

The three gate conditions, each with its number:

| gate | result |
|---|---|
| 120 probe lines | 116, PASS by 4 |
| `Code` plain inductive, termination and positivity accepted | PASS |
| rate under 0.013193 s per line | 0.0103, PASS |

## 2. TERMINATION AND POSITIVITY

Agda 2.8.0 accepted everything. No termination, positivity, or
universe error remains. `Code` is a plain inductive type:

```agda
data Code : Type ℓ where
  base : K → Code
  wit  : (k : ℕ) → Formula (⊥* {ℓ}) (suc k) → Vec Code k → Code
```

(`src/ProbeLJ118.agda:44-46`). The constructor `wit` is strictly positive:
`Code` occurs only under `Vec`.

**Finding F2: the termination is not "standard" the way the review said.**
The review's risk 1 reads "Termination of `val` through `Vec Code k`.
Standard, unchecked here" (`_build/lj-1.16-review.md` section 4.7). It is
not standard. A minimal test file with the same shape,
`f (w k cs) = h (map f cs)`, fails the termination checker when `map` is
the cubical library's `Cubical.Data.Vec.map`. The checker does not see the
recursive calls through that `map`. A hand-written recursion over the same
vector passes. The probe therefore defines `val` in a `mutual` block with a
hand-rolled `vals : Vec Code m → Vec S m` (`src/ProbeLJ118.agda:55-63`).
That form costs 4 lines. It is the only fix needed; no pragma, no
`--termination-depth`, no `TERMINATING`.

## 3. THE LINE COUNT

116 non-blank lines in `src/ProbeLJ118.agda`, counted with
`grep -cve '^[[:space:]]*$'`. The stop-line is 120. PASS by 4.

The review's read of 150 to 300 is for the BUILD, not the probe. The probe
is the decisive miniature. It proves the generic closure core (lines 33 to
112) and the hull instantiation (lines 114 to 143). The build inherits the
core and adds: the junk lemma (finding F1, 10 to 15 lines), the counting
site work (section 6), the master wiring, and prose. The 150 to 300 band
remains a plausible build estimate. The measured core is cheaper than the
band's low end.

## 4. SECONDS AND RATE

Measurement method: one Agda process, cold interface for the probe file,
warm dependency interfaces, under the brief's C-12 cap
`GHCRTS="-A64m -I0 -M8g"`. This matches the method `[LJ-1.16]` used for its
baselines (`_build/lj-1.16-report.md:92-101`).

| file | lines | seconds (real) | rate |
|---|---:|---:|---:|
| `ProbeLJ118` | 116 | 1.18 to 1.20 | 0.0102 to 0.0103 |
| `ProbeStub` (same imports, no content) | 28 | 0.96 to 1.01 | n/a |
| `L.Hull` (calibration) | 372 | 2.50 | 0.0067 |

The probe rate is 0.0103 s per line. The bar is 0.013193. PASS.

The marginal rate is far lower. The stub with the identical import cone
checks in about 1.0 second. The probe's own content therefore costs about
0.2 seconds over 116 lines, about 0.0017 s per line. The probe is small, so
the fixed cone cost dominates its aggregate rate. A 250-line build on the
same cone projects to about 1.4 to 1.6 seconds, a rate near 0.006, inside
the review's 0.005 to 0.013 band. P-n's floor, 0.22 to 0.297 s per line, is
not approached: the probe instantiates nothing at a concrete carrier in the
hot path.

One outlier is on record. The first-ever cold run took 2.17 seconds, 0.0187
s per line. That run generated the dependency interfaces in the build
directory. The stable cold measurement is 1.18 to 1.20 seconds.

## 5. DID THE DELIVERED FORWARD FACE SUFFICE?

Yes, for the closure core. The forward face of `FOL.Manipulation.Parameters`
is exactly the shape `wit` wants, and the probe uses it:

- `absFo` at `src/FOL/Manipulation/Parameters.lagda.md:260-261`, used as
  `ψ = absFo φ` (`src/ProbeLJ118.agda:95-96`).
- `⊨-abs` at `:421-429`, used twice in `closed`
  (`src/ProbeLJ118.agda:102,111`).
- `⊨-map` at `src/FOL/Manipulation/Relabelling.lagda.md:154-168`, used twice
  in `hullClosed` (`src/ProbeLJ118.agda:138,143`).
- `countFo` and `constantsFo` at Parameters `:74-86` and `:105-112`.
- `leastOf` and `SWO` at `src/L/WellOrder/Base.lagda.md:53-59,158-161`.
- `orderAt` at `src/L/Choice/Step.lagda.md:740-741`.

The untruncated `fiber` was NOT needed. Membership in `Hull` is by
construction: the code `wit (countFo φ) (absFo φ) (constantsFo φ)` is its
own membership certificate (`src/ProbeLJ118.agda:87-88,108-109`).

Two pieces the review did not price:

- **F3: `sum-stuck` (4 lines).** The junk split makes `val (wit k ψ cs)` an
  opaque `rec` on `lem`. The closure needs
  `val (wit k ψ cs) ≡ search k ψ (vals cs) w` when a witness `w` exists.
  This equality is provable because the `inr` branch carries `Wit → ⊥`,
  which contradicts the supplied witness. The review's "closed by
  construction" claim silently assumes this step.
  (`src/ProbeLJ118.agda:69-78`.)
- **F2's `vals` (4 lines).** See section 2.

## 6. THE COUNTABLE UNION

Not measured. The closure miniature has no counting step, so the probe
prices nothing here. What the probe can confirm is the mechanism the review
described: `Code` is a countably-branching least fixpoint, so counting it
needs one induction on code height and one union over ℕ. The one-step hull
escapes that step because its index is a single formula-and-witness pair,
countable in one shot. The review routes the cost to `[LJ-1.5]` or
`[LJ-1.7]`. The tree's counting kit injects the parameter-free formulas
into ℕ (`code` at `src/FOL/Count.lagda.md:81`, `code-inj` at `:171`), which
is the natural seed of that argument. The union step itself is not in the
tree. That is a build ingredient, not a closure-site cost.

## 7. DOES `FOL.Count`'s `encode` GIVE `wit` FOR FREE?

No. The payloads differ by one.

`encode : Formula K 1 → Σ[ k ∈ ℕ ] (Formula (⊥* {ℓ}) k × Vec K k)`
(`src/FOL/Count.lagda.md:654`). It returns a formula of arity `k` and a
vector of length `k`, with the last constant duplicated by `snoc`
(`codeByCount` at `:648-652`).

`wit` wants `Formula (⊥* {ℓ}) (suc k)` and `Vec Code k`
(`src/ProbeLJ118.agda:46`). The arity is one more than the vector length.

The free payload is `(countFo φ , absFo φ , constantsFo φ)` from
`FOL.Manipulation.Parameters` (`:260-261`, `:105`). The probe uses exactly
that. `encode` is structurally aligned with the shape, not definitionally
equal to it. The review's "exactly `wit`'s payload"
(`_build/lj-1.16-review.md` section 4.4) is loose. The counting kit's
`code` and `code-inj` remain the right instruments for counting `Code`
(section 6); `encode` is a counting-side injection, not the closure payload.

## 8. DD4: WHAT THE J TOWER SUPPLIES

The generic module `TermAlgebra` is parameterized by the structure, the
carrier embedding, the meta well-order, and the junk value
(`src/ProbeLJ118.agda:33-37`). No type in the core mentions `Lset`, a
stage presentation, or Def-tower content. That is P-l and P-h as written.

The J tower supplies four things at instantiation:

- its restricted structure `𝒮`, in place of `AbsL.𝒮M`;
- its meta well-order on its stage carrier, in place of `orderAt α ordα`;
- its junk element, the analogue of `∅ ∈ˢ Lset α` at its limit stages;
- `lem`, which every tower already carries.

`absFo`, `⊨-abs`, and `⊨-map` are already structure-generic. Nothing in
`Code`, `val`, `Hull`, or `closed` is per-tower. The closure theorem is
written once and instantiated twice. This is the review's DD4 finding,
confirmed: the term algebra is template content bought once, and the
definable well-order drops out of both towers.

The one per-tower leaf is the junk lemma. Each tower needs its own
`∅ ∈ stage` at limit stages. It is the same 10 to 15-line argument twice,
or one generic lemma over a stage predicate if the build writes it that
way. This replaces the twice-paid order object with a twice-paid trivial
membership, which is the whole point of the shape.

## 9. LITERATURE USED

- `dev/literature/devlin-II5.md:118-132` (section 1.3, the definable hull
  and the least-witness formula). Took the least-witness role that the junk
  value replaces: Devlin makes the least witness the unique witness with
  `ψ(v₀) = φ(v₀) ∧ ∀v₁(v₁ <_L v₀ → ¬φ(v₁))`.
- `:257-270` (section 2.4, Step D). Took that the order is required only to
  pick the least witness, which the meta well-order answers for.
- `:278-285` (section 2.6, Step F). Took that 5.5 consumes condensation
  parts (i) and (ii) only, so dropping the internal order costs nothing on
  the GCH chain.
- `_build/literature/dev2.txt:1327-1335` (5.3 statement and Devlin's gloss).
  Took the unique-witness role and the "definable wellorders" remark.
- `dev/literature/devlin-errata.md`. NOT read. WHY NOT: `[LJ-1.14]`
  verified it does not cover Chapter II section 5
  (`_build/lj-1.14-report.md:107-108`), and the review carried the same
  reason.

## 10. ARCHIVE USED

- `_build/lj-1.16-review.md`. Read sections 1 to 10. Took section 4.1 to
  4.3 (the shape and its price), 4.7 (risks 1 and 4, both probed here), and
  8 (the dispatch). Checked its `encode` claim and found it loose
  (section 7).
- `_build/lj-1.16-report.md:1-110`. Read the three refused shapes and the
  rate basis at `:92-101`. The probe's measurement method follows that
  basis.
- `_build/lj-1.3-report.md:114-131`. Read the standing pieces. The first
  piece, the order element's stage membership at 30 to 80 lines, is the
  same family as finding F1, and F1 is the smaller cousin: the junk needs
  only `∅ ∈ˢ Lset α`, not an order element's membership.
- `_build/l3.32-t49-report.md:53`. Read the "never priced" record. It
  matches the review's cite: no simultaneous closure form is priced because
  its only consumer was replaced.
- `_build/l3.32-t5-report.md:135-151`. Read the iterated-hull refusal.
  Checked it myself: `ClosedFor` is per-matrix, `Single`'s ladder is
  per-matrix, and `ReflectFo`'s ladder is per-formula. The fourth shape
  uses none of them. `search` calls `leastOf` over the meta well-order,
  which answers for every formula at every environment
  (`src/ProbeLJ118.agda:51-53`). T5's reason does not apply. The review's
  claim is verified.
- `dev/LESSONS.md`. D-1 at `:1038` (probe doctrine), P-h at `:174-197`
  (module parameters), P-n at `:2442-2466` (no concrete carrier in the hot
  path), D-10 at `:1316-1335` (price the truth of a residue). All four
  bound the probe's shape.

## 11. WHAT I AM NOT SURE OF

- **F1: the junk lemma is not in the tree.** `∅ ∈ˢ Lset α` at limit α is
  true (the least member of a limit ordinal is `∅`, and `∅ ∈ 𝒟ₒ (Lset β)`
  for any β). The tree delivers `∅∈𝒟ₒ` at
  `src/L/Axioms/Basic.lagda.md:490-491` and `Lset-in` at
  `src/L/Constructible.lagda.md:319-334`, but no lemma gives `∅ ∈ˢ α` for
  nonzero ordinals. The full proof needs a small foundation argument with
  `regularityV` and `lem`, about 10 to 15 lines. I did not write it in the
  probe: it would have blown the 120-line cap. The probe's hull
  instantiation takes junk as a module parameter
  (`src/ProbeLJ118.agda:125-126`). If the gate reads "closes at hull
  parameters" strictly, the closure is complete only up to that one lemma.
  The review's risk 4 is real but cheap.
- **The countable union is unpriced.** Section 6 names the mechanism, not a
  number. The counting site must price it before the build.
- **The rate has noise.** Single-file cold ratios on small files vary by
  about half a second. The stable number is 0.0103; the first-cold run was
  0.0187. The build's rate will depend on the build module's total size.
- **`sum-stuck` and `vals` are new.** The review did not price them. They
  are 8 lines total. They are probe-level; the build inherits them.
- **The seal.** The delivered `leastSearch` is `opaque` for measured
  reasons (`src/L/Hull.lagda.md:265-277`). The probe calls `leastOf`
  directly. The build must decide whether to seal the search.
- **The measurement cap.** The probe ran at `-M8g`, the brief's C-12 cap.
  The `[LJ-1.16]` baselines ran at `-M16g`. The rates are the same class;
  I did not re-measure at `-M16g`.
