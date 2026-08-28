# Review of `Sat-in-carrier-lim`

**NO-GO. The obligation's type is FALSE as stated, at the full ruled
scope.** The hypothesis set `closedω γ`, `ω ∈ˢ γ`, `fst A ∈ Lset γ`
does not rescue it, because the failure is not a failure of stage
height. It is the alphabet: the obligation quantifies over
`φ : Formula S n` (Probe736.agda:152), and `Formula S n` lets one
constant of `φ` name ANY `L`-set, of any rank. The atom clause of
`cond` transports that constant's global membership into `Sat`'s
extension, and `closedω γ` cannot absorb what never sits below `γ`.

The D-10 truth check (brief premise 4) was priced before any proof.
The 730 witness shape (`γ = sucV (sucV ω)`) is ROUTED by `closedω`:
that refutation needs a successor carrier, and a `closedω` carrier is
a limit. What kills the target here is a different, wider obstruction.

## The semantic fact, machine-checked

`agents/tasks/LJ-1-736/Probe736.agda` (green, EXIT=0,
`runs/p-32.out`, 1.27 s, 337,641,472 B peak, wide caliber
`-A64m -I0 -M2g`, no postulate, no hole, nothing in `src/`) carries,
for the atom `φ₀ = var 0 ∈̇ con c` and `Sat A φ₀`:

- `atom-in` (Probe736.agda:99): the environment entry tagged `# 0`
  lies in `c`, and the entry lies in `fst c` -- then `x ⊨ cond A φ₀`.
- `atom-out` (Probe736.agda:120): from `x ⊨ cond A φ₀`, a witness `w`
  with `pr (# 0) (fst w) ∈ fst x` and `fst w ∈ fst c`.
- `sat-atom-out` (Probe736.agda:132): the same for every member of
  `Sat A φ₀`, via the landed spec `Sat-mem`
  (src/L/Coding/Sat.lagda.md:145).

Both directions are composed from the chapter's own readers
(`cond∈-out`, src/L/Coding/Sat.lagda.md:217; `tmIs-var-out`, :96) --
no independent semantics was built. The reading behind them: `cond`'s
atom clause (src/L/Coding/Sat.lagda.md:149) exists the two term
slots through two existential witnesses and states `var 1 ∈̇ var 0`;
`tmIs (con c) v e = var v ≐ con c` pins the `u`-slot to the constant.
Satisfaction at `x` therefore says exactly: the `# 0`-tagged entry of
`x` lies in `c`. No stage hypothesis appears anywhere in the kernel.
The quantifiers of `cond` range over `L` as a whole
(`FOL.Absoluteness.Single`'s carrier `SM = Σ[ x ∈ S ] (x ∈ᶜ M)`,
src/FOL/Absoluteness.lagda.md:64-65), not over any `Lset`.

## Why the type is false

Fix `γ` with `closedω γ` and `ω ∈ γ` (for instance the V-value of
`ω · 2`), and `A` with `fst A = ω`, which satisfies
`fst A ∈ Lset γ`. For an ARBITRARY constant `c : S`, the kernel gives

    Sat A (var 0 ∈̇ con c)  =  the image, under the landed environment
                               embedding, of the trace  { a ∈ ω | a ∈ c }.

If `⟨ Sat A φ ∈ˢ LsetS γ oγ ⟩` held, then `Lset-out`
(src/L/Constructible.lagda.md:346) would make the image a definable
subset of some `Lset δ`, `δ ∈ γ`; decoding it back
(`envSet-out`, src/L/Coding/EnvSet.lagda.md:385: every member is,
up to a path, `envS A g`) would return the trace `ω ∩ c` as a
definable subset of a stage below `γ`, hence as a member of
`Lset γ`. Taking `c` to be a constructible real first constructed
above `γ` (such reals exist: `Lset (ω · 2)` is countable and
`P(ω) ∩ L` is not), the obligation would state that EVERY
constructible real sits in `Lset (ω · 2)`. That is false.

Honest accounting of what is and is not machine-checked: the kernel
(the transport of the constant's membership into `Sat`'s extension,
both directions, for every `A`, `x`, `c`) is machine-checked at
Probe736.agda:99-135. The refutation above is then a two-step
reduction whose ingredients are landed and cited (the image-decode),
but the diagonal -- exhibiting, inside the tree, one constructible
real of construction stage above `γ` -- is NOT landed, was not built
here, and is priced at far more than a probe. The verdict rests on
the machine-checked kernel plus this reduction, not on a
machine-checked `⊥`.

## Why the sibling scope works and this one does not

`keyS-in-carrier-lim` (agents/tasks/LJ-1-729/Probe729.agda, Section 4)
takes its formulas over `⟪ fst A ⟫` -- constants bounded by the
carrier, so all of them sit in one `Lset δ₀`, `δ₀ ∈ γ`, and the climb
plus `closedω` absorb the height. The Sat obligation's alphabet
`Formula S n` is strictly wider than its sibling's
`Formula ⟪ fst A ⟫ n`. That widening is the defect. It is not
compensable by closure, because the missing height is in a CONSTANT,
not in an iterate.

## Corrected targets, for ruling (the mathematician's call)

1. **Carrier-bounded alphabet**: state the obligation for formulas
   over `⟪ fst A ⟫` (relabelled along the fiber map, the 729 shape),
   or directly for `cond`'s inputs. All constants then sit below one
   stage in `γ`; the proof route is the 729 climb run on `cond`'s
   recursion, with the `Sat`-values of subformulas landing at finite
   iterates that `closedω` absorbs. This is the shape DefAt's second
   existential most likely wants; price after ruling, not before.
2. **Bounded-constants hypothesis**: keep `Formula S n`, add
   "every constant of `φ` lies in `Lset γ`". Same route, one extra
   hypothesis to discharge at each use.
3. **Δ₀-only**: do not prefer. The atom clause still transports
   constant-membership for Δ₀ formulas; the alphabet is the defect,
   not the quantifier structure.

## Do not re-fund

- The kernel (Probe736.agda:88-135). Reuse it; it is green.
- The 730 rank chain (green at two sites), the 729 climb,
  `relativize-correct`.
- Any attempt to inhabit the obligation at `Formula S n`. A future
  return that claims this exact type should be checked against this
  review's alphabet observation first.

## Price

| item | value |
|---|---|
| probe lines (raw `.agda`) | 153 total, 126 non-blank (in-fence count 0; the ratio bar cannot fire) |
| verdict run | 1.30 s, 337,625,088 B peak (`runs/p-33.out`) |
| floor run (frame, kernel absent) | 1.23 s, 340,230,144 B (`runs/p-31.out`) |
| runs this dispatch | p-1 to p-33, plus the T1 bisect (kept as `runs/T1.bisect.agda.txt`, never typechecked to green) |
| heap wall | none; peak is 15.7 percent of the 2,147,483,648-byte wide cap |
| caliber | `-A64m -I0 -M2g`, set on the pane by the program, never touched here |
