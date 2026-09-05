# LJ-1.25 report: the measured cure lands in the limit half

## 1. THE VERDICT

Whole master cold: 11.22 s, then 12.62 s, rate about 0.024 s per line.
The old figure: 42.03 s at 0.087. The cure reproduced at the master.
The same machine measured 41.21 s before the cure. The rate stays above
DD24's bar of 0.013193. The gap is the descent and the assembly, not this
block.

## 2. DID THE CURE REPRODUCE

Yes. I re-verified the control first (D-10). The control probe ran cold at
32.35 s. That sits inside the 29.1 to 31.8 s band, slower by load. The
arm-1 probe ran cold at 2.28 s. LJ-1.24 measured 2.281 s. The delta holds.

The whole master ran cold at 41.21 s before the cure. It ran cold at
11.22 s, then 12.62 s, after the cure. The delta is about 29 s. The
block-level reduction is about 14x. The master-level reduction is about
3.5x.

The edit cost 7 lines, not 6. The module header gained 3 lines. The
instantiation in `limit-step` grew from 1 line to 5 lines. Seven statement
lines changed in place. The J bodies stayed generic, exactly as the probe
predicted.

The limit half dropped from about 31 s at 0.270 to about 1.7 s at 0.014.
That is inside the parameterized band (P-m). The remaining whole-master
cost is the descent and the assembly.

R-35. Arm 1 made the transports cheap. R-35's shape is already present.
`Lset-out` delivers `δ ∈ˢ α` and `x ∈ˢ 𝒟ₒ (Lset δ)` at the small index δ.
No restructure is indicated.

R-40. No witness is stated deeper than needed. The stage witness is
`member (Lset α) x`, the shallow fiber into the index. `Lset-out` climbs
to δ directly. There is no deep successor chain in the limit half.

I-5. Every truncation branch carries a written type. The branches are
`toWitness`, `mk`, `go₁`, and `go₂`.

R-38. I sealed nothing and unsealed nothing. `src/L/Definability.lagda.md`
is untouched.

## 3. DID ANY EXPORTED TYPE CHANGE

No. `stage-card-upper` is unchanged. `Upper` is untouched. Its call
`limit-step α oα infα (branch α oα infα IH)` keeps the same signature
(line 567). `limit-step` keeps its statement. `stage-card-suc`,
`stage-card-lower`, `op-step`, and `successor-step` are unchanged.

The `LimitStep` module gained two parameters, `D` and `inv` (lines 373 to
378). Only `src/Everything.lagda.md` imports this file. It checked green
at 2.79 s warm.

## 4. Successor.go₂

Left, with a reason. The same abstraction does not cheaply cover it.
`Successor` names `DefOf.defSet (Lset α)` at a fixed α. There is no
transport over δ. The measured cure abstracts a δ-indexed source across
transports. A fixed-stage `D` would be a new shape with a new price. The
brief says do not touch the descent. The descent runs at 0.061. The 4.5 s
of `go₂` stays open for a future brief.

## 5. THE NUMBER

484 in-fence lines before. 491 after. The caliber is the ledger's:
non-blank lines inside ` ```agda ` fences. My count reproduces LJ-1.21's
484 exactly. DD26's catalog exclusion does not bear. This file is not a
catalog.

## 6. DD4

The J tower now supplies the pair `(D, inv)`. `D` is the δ-indexed
operation. `inv` is its membership characterization. The instantiation
lives in `limit-step` at lines 495 to 499. The limit half stops naming
`DefOf.defSet` and stops applying `𝒟ₒ-inv`.

The shrink is partial. The parameter types still name `Lset`, `Formula`,
and `𝒟ₒ`. The body still uses `Lset-out` and `member (Lset α)`.

A second layer would remove the three names. It would abstract the family,
the operation, and the membership predicate. It would add a module layer
and instantiation sites for no measured gain. Arm 1 already prices the
block into the parameterized band. Do not build it here.

## 7. ARCHIVE USED

- `src/ProbeLJ124Arm1.agda:1-187`. The green cured form. Re-derived into
  the master, not copied.
- `_build/lj-1.24-report.md:30-45`. Arm 1, the cure.
- `_build/lj-1.24-report.md:77-87`. The line price.
- `_build/lj-1.24-report.md:137-157`. Section 10, the open thread on
  `go₂`.
- `_build/lj-1.21-report.md:86-133`. Section 5, seconds and profile.
- `_build/lj-1.21-report.md:216-250`. Section 9, the unmeasured pieces.
- `src/L/Definability.lagda.md:111-112`. The transparent birth of
  `defSet`.
- `src/L/Constructible.lagda.md:336-338`. `Lset-out` at the small index.
- `dev/LESSONS.md:2305-2400`. P-l.
- `dev/LESSONS.md:1316-1376`. D-10.
- `archive/rud-route/src/L/Ordinal/SquareLaw.lagda.md:213-242`. The
  abstract restatement shape.
- `scripts/rules.py --for build`. The mandatory rules bundle.
- `src/Everything.lagda.md:367`. The only consumer.
- Literature: `dev/literature/`. None bears. This is a check-cost edit on
  delivered code.

## 8. WHAT I AM NOT SURE OF

The machine was not quiet. Load average was 5.34 at the start and 4.72 at
the end. Process inspection is blocked in this sandbox. `ps` and `top` are
denied. I could not verify the sibling-slot claim. The control ran slower
than the LJ-1.24 band, which matches load.

The post-cure samples span 1.4 s, about 12 percent. The rate is a band,
not a point.

The whole master stays above DD24's bar. The rate is about 0.024; the bar
is 0.013193. The gap is the descent and the assembly. Whether a
fixed-stage `D` would remove `go₂`'s 4.5 s is unmeasured.

The pre-cure cold run left no interface file behind. The post-cure runs
wrote theirs. Both were cold checks with the interface absent. The seconds
align with the prior reports, so the numbers stand.
