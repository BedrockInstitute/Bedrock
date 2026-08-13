# LJ-1.24 report: is the limit half's 31 seconds curable? Root cause first

## 1. THE VERDICT

ARM 1 WINS. The abstract-source restatement cuts the limit half from
29.1 s cold to 2.3 s cold. The block is curable. The delta is about
26.8 s, a 12.8x reduction. The cured rate is 0.019 s per line, inside
the parameterized band.

## 2. THE CONTROL

The control is a verbatim copy of the master's limit half
(`src/L/StageCardinal.lagda.md:363-492`) into
`src/ProbeLJ124Control.agda`. The shared descent lives in
`src/ProbeLJ124Base.agda` and is imported warm.

Each run deletes the file's own interface. Dependencies stay warm. One
Agda process runs under `GHCRTS="-A64m -I0 -M8g"`.

Control cold: 29.122 s, then 31.767 s. Base cold: 11.509 s. The block
has 118 non-blank in-fence lines. The rate is 0.247 to 0.269 s per
line. The reported 0.270 sits inside that range.

The 31.0 s figure was a within-file marginal. My figures are standalone
cold checks of the same content. Both confirm the block.

The control drifted by 2.6 s between runs. The sibling holds the other
Agda slot, so the machine is not quiet. The delta dwarfs the drift.

## 3. ARM 1

The source is abstracted. The module takes
`D : (δ : S) → Formula ⟪ Lset δ ⟫ 1 → S` and
`inv`, the D-shaped δ-witness. `inv` is instantiated with `𝒟ₒ-inv` at
the end of `limit-step`.

Every `DefOf.defSet (Lset ...)` mention in the limit half becomes a `D`
application. The transport terms stay in the statements, but they cross
an abstract index. The two stability proofs are unchanged: their J
bodies were already generic in the source.

Arm 1 cold: 2.281 s, then 2.325 s. Delta against the adjacent control:
29.122 minus 2.281, about 26.8 s, a 12.8x reduction. The cured rate is
0.019 s per line.

## 4. ARM 2

NOT RUN. The brief's stop rule says to stop early and report when arm 1
wins. Arm 1 won. Arm 2 would not change the verdict.

## 5. ARM 3

NOT RUN, for the same reason. The archive's zero-transplant result is
not re-tested at this site. The answer this brief needs is already
measured.

## 6. IS IT P-n's FLOOR OR R-38's CLASS?

It is R-38's class, not P-n's floor. Arm 1 changed only the statement
positions. The concrete `DefOf.defSet (Lset ...)` became an abstract
`D`. Every proof body stayed identical. The block fell from 0.247 to
0.269 s per line down to 0.019.

P-n's floor is satisfaction content at a concrete carrier. The limit
half proves no satisfaction decodes at all. It transports and counts
defSet values. The 0.270 rate sat inside P-n's band by coincidence of
the R-38 mechanism, exactly as LJ-1.21 argued.

The root-cause hypothesis is confirmed. The transport over a
transparent sett index unfolds the satisfaction tower. The same
transport over an abstract index unfolds nothing.

D-26 does not bear. The least-of runs over the ordinal's own well-order
on `⟪ α ⟫`, not over a key on the definable stage, so nothing forces
the limit half to touch `defSet` as a key.

## 7. WHAT THE CURE WOULD COST

About 6 extra lines on the master. The module header gains the `D` and
`inv` signatures, 3 lines. Seven one-line replacements change the
`defSet` and `𝒟ₒ-inv` mentions. They add no lines. The `limit-step`
body grows by 3 lines for the two instantiations.

No new lemma is needed. The stability proofs already work for any
source. No other consumer changes: `Upper` calls `limit-step` with the
same signature.

## 8. DD4

Partial. Arm 1 removes `DefOf.defSet` and the `𝒟ₒ-inv` application
from the limit half's body. The J tower must now supply the pair
`(D, inv)`: one operation and one membership characterization.

The abstract module still names `Lset`, `Formula`, and `𝒟ₒ` in its
parameter types and target. Those three stay L-specific until a second
layer abstracts the formula family and the stage family. `Lset-suc`
was never in the limit half. The operation-level list shrinks; the
carrier trio remains.

## 9. ARCHIVE USED

`dev/LESSONS.md:2330-2348`. The transplant table and the paragraph
under it. It says the abstract restatement is the only cure that ever
worked. It also says a cure does not transfer by analogy.

`dev/LESSONS.md:849`. R-38's own words: sealing only moves the cost.

`dev/LESSONS.md:2305-2400`. P-l, the full statement. Naming a
transparent construction in a statement's type is what costs.

`dev/LESSONS.md:2460-2508`. P-m and P-n. The parameterized band is
about 0.01 s per line. P-n's floor is 0.22 to 0.297 s per line at a
concrete carrier.

`dev/LESSONS.md:782-808, 885-928, 929-982`. R-35, R-37, R-40. The
small-index and variable-hypothesis shapes that arm 2 would use.

`dev/LESSONS.md:1676-1702`. D-26. The well-founded key question.

`dev/LESSONS.md:1316-1376`. D-10. Re-verify the control before curing.

`_build/lj-1.21-report.md:86-133`. Section 5, the seconds and the
profile. `:216-250`. Section 9, the R-38 seal priced but not applied.

`archive/rud-route/src/L/Ordinal/SquareLaw.lagda.md:213-242`. The
abstract restatement shape. The chase is stated against an abstract
family and instantiated at the numeral sites.

`_build/l3.32-t85-report.md:239-247`. The transport-stability wall
class. It is the same wall the limit half hit.

`src/ProbeTowerInd2.agda:99-159`. The earlier green successor shape.

`dev/literature/devlin-II5.md:140`. Devlin's one-line proof. No
literature bears on transport cost; none is used.

## 10. WHAT I AM NOT SURE OF

Arms 2 and 3 are not measured. The stop rule ended the run at arm 1.
Whether naming alone is expensive at this site stays open. The
descent's `Successor.go₂` cost 4.5 s and names `defSet` without a
transport, so naming alone costs something somewhere.

The control drifted by 9 percent between its two runs. The verdict
does not depend on the drift. The delta is 12.8x.

The probe measures the block in isolation. The master also carries the
descent and the assembly. A full-master check may shift the seconds a
little. The instantiation at `limit-step` passes `𝒟ₒ-inv` at a
concrete stage once. The probe shows that this is cheap.

The line count is 118 non-blank in-fence lines. LJ-1.21 reported 115.
The difference is the comment block at the head of the copy. The rates
do not depend on the choice.
