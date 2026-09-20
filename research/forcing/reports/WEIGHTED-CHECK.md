# Full-weight check recursion and K11 interface narrowing

The poset check operation is now constructed internally, with the actual equation

```
z ∈ chk a  iff  ∃ u ∈ a. ∃ p ∈ W. z = ordered (chk u) p.
```

`WeightedCheckRecursion` uses the same good-table compatibility argument as
`CheckRecursion`, but its local formula has an additional bounded weight
quantifier. At a stage, Collection and Separation realize the unique recorded
value at each member of `a`. The resulting set of values is multiplied by `W`
using the existing proved ground Cartesian-product operation. The weight
relation itself is not treated as a single-valued image.

The good-table agreement proof transports the child value while keeping the
same weight and its membership proof. Collection, filtering to good tables,
union, and root extension then produce an internal recursive graph. Unique
existence is eliminated into contractibility, so extracting `chk` uses no
choice principle. The graph's satisfaction theorem and both directions of the
recursive membership equation are checked.

The canonical table records `(x, chk x)`. A separately defined diagonal graph
records `(chk x, x)`; its image of `W` supplies the actual generic name. These
pair orders are intentionally different. `InternalWeightedCheck` transports
the ordered-pair presentation to `NameKernel.entry`, proves hereditary name
validity by membership accessibility, and defines `spread x` as `{x} × W`.

`K9.NameGround.Check` now uses this construction for `chk`, `chk-spec`, and
`spread`; `genericName` uses the proved diagonal graph. Its old arbitrary-image
module remains available to other consumers such as `IndexedNames` and
`RealNames`. Thus the complete `NameGround` parameter list still includes
`MemberImage`, but check, spreading, and the generic-name supplier no longer
use it. Their standalone module does not accept it.

The assumptions of the standalone construction are Extensionality, ground
identity realized as paths, host membership accessibility, Pairing, Union,
PowerSet, Separation, Collection, and the weight set. No LEM, choice axiom,
MemberImage, or pre-existing recursion table is supplied. PowerSet is used
by the ground Cartesian-product implementation. Host accessibility remains an
explicit hypothesis; this does not derive it from ordinary Foundation.

Separately, `K11.CohenGeneric` and `K11.Corollary` no longer take Accessibility
or MemberImage. They project the required ordinary ground operations directly
from Families and route the generic construction through `CountableCohen`.
The latter standalone interface already needs neither Families nor accessibility.
A search of actual imports found Corollary as the only CohenGeneric consumer
and no Corollary consumer requiring migration. Carrier enumeration and LEM
remain explicit. This is not a proof that a countable ground exists or that
all K10 inputs have been supplied.

A scoped read-only mathematical review checked the bounded-weight formulas,
image functionality, product introduction/elimination, table compatibility,
unique-existence extraction, recursive specification, and diagonal pair order.
Compiler checks and their source hashes are recorded in the validation report.

The next foundational obligations are the particular definable graphs for
recursive name translations and the real/indexed-name image families. Arbitrary
host images and arbitrary Boolean-value families have not been justified.
The endpoint extension axioms, preservation argument, and inner-bot supplier
remain open.
