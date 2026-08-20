# Review of `descent-case4-coded`

GO. The term is `agents/tasks/LJ-1-432/Probe432.agda:155-168`. It
typechecks. The conclusion is `sq x`. There is no `∥ ∥₁`.

W3 (`kappaC-not-fin`, `:132-147`) restates infinitude at `κC` from the
DATA arrow. Median 1.63 s on three forced rechecks, exit 0. The
induction hypothesis reaches `κC`.

Case four spends `d := κC`, membership as a hypothesis, the arrow from
`κC-arrow` (`:122`), and `sq` from the IH at `κC-ord` and W3. The
untruncated arrow the descent needs does not have to sit at the
ambient least cardinal.

Case three is not closed. The statement that would close it is conjunct
4 of `Init` at `fst (κC a oa)`, typed at
`src/L/Ordinal/SquareLaw.lagda.md:696`. `[LJ-1.406]` pays that conjunct
from ambient truncated-injection minimality
(`src/L/Cardinal.lagda.md:140`). A minimality that forbids a code does
not fire on the composition at `agents/tasks/LJ-1-406/Probe406.agda:118-122`.
This file does not build case 3.
