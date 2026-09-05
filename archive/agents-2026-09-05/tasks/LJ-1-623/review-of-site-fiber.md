# [LJ-1.623] stop: the residue is [LJ-1.618]'s wall, unchanged at the site grain

## THE STOP

**NO-GO, stated, on `site-fiber : SiteFiber α`.** The type is
`SiteFiber α` as `[LJ-1.621]` states it
(`agents/tasks/LJ-1-621/Probe621.agda:77-78`), imported and not
restated. One refl row of the probe proves that this type IS
`[LJ-1.618]`'s payload `PairingAt α`
(`agents/tasks/LJ-1-623/Probe623.agda:95-96`):

    site-is-pairing : P621.SiteFiber α ≡ P618.PairingAt α
    site-is-pairing = refl

`[LJ-1.618]` measured that payload NO-GO, with one named residue
(`agents/tasks/LJ-1-618/lj-1.618-report.md:11-12`). The brief ordered
a stop if the residue is that wall, unchanged. It is unchanged, and
this file says why with the probe's green rows as evidence. No term of
the probe carries the obligation's name and no term has its type.
Nothing was postulated. Nothing landed in `src/`. Nothing was
committed and nothing was pushed.

## THE RESIDUE, AND EXACTLY WHAT IT LEAVES OPEN

`Inj-extract` (`agents/tasks/LJ-1-618/Probe618.agda:151-154`), stated
at the site frame in this task's alone-checked W3
(`agents/tasks/LJ-1-623/runs/W3.agda:58-61`) and tied to `[LJ-1.618]`'s
spelling by one refl (`agents/tasks/LJ-1-623/Probe623.agda:104-105`):

    Inj-extract = (a : S) (oa : IsOrd (fst a))
                → ∥ ⟪ fst a ⟫ ↪ ⟪ fst (κL a oa) ⟫ ∥₁
                → ⟪ fst a ⟫ ↪ ⟪ fst (κL a oa) ⟫

What it leaves open is the DATA payload of the tree's own
least-cardinal search. The search
(`src/L/Cardinal.lagda.md:116-117`) feeds `leastOf` the truncated
predicate `InjP γ = ∥ Inj γ ∥₁` (`src/L/Cardinal.lagda.md:66-67`), so
the least INDEX comes out honest and the payload does not
(`src/L/Cardinal.lagda.md:133-134`). The residue asks for one honest
ambient injection read out of that truncation, at the ambient-least
ordinal. `dne` does not apply: the payload is a Sigma whose first
component is a function, so it is not a proposition
(`src/L/StageCardinal.lagda.md:416`;
`archive/dev/LJ-dispatch-index.md:183`).

## WHAT THE SECOND ATTEMPT MEASURED

**1. THE TWO GRAINS ARE ONE TYPE.** The refl row above is the
measurement: `[LJ-1.621]`'s site demand and `[LJ-1.618]`'s one-alpha
payload are the same type, so `[LJ-1.618]`'s wall applies verbatim.
The site grain does not buy a cheaper supply.

**2. THE RESIDUE ALONE FINISHES THE SITE.** Green
(`agents/tasks/LJ-1-623/Probe623.agda:115-116`):
`residue→site : P618.Inj-extract → P621.SiteFiber α` is
`[LJ-1.618]`'s own green recursion applied at this site. Nothing less
than the residue closes it.

**3. THE CODED ROUTE, WHICH `[LJ-1.618]` DID NOT SURVEY, PARKS AT OR
ABOVE THE AMBIENT LEAST.** The tree's readback turns an L-coded
injection held as DATA into an honest ambient injection (`readL`,
`src/L/CantorBernstein.lagda.md:33-36`, through `Small`,
`src/L/Coding/Injection.lagda.md:123-151`). Green rows:

- Codes as data at the ambient-least clear the residue outright
  (`agents/tasks/LJ-1-623/Probe623.agda:140-143`).
- Every coded target sits at or above the ambient-least cardinal
  (`agents/tasks/LJ-1-623/Probe623.agda:169-172`): a code at gamma
  carries an ambient injection at gamma, and the ambient search cannot
  stop above gamma.

So the coded route reaches the residue only through codes AT the
ambient-least ordinal, and the bridge from the truncated AMBIENT
statement to the truncated CODED statement
(`AmbientToCoded`, `agents/tasks/LJ-1-623/Probe623.agda:157-159`,
TYPE ONLY) is held by no row of the tree. Its truth price, checked
before any proof was attempted (D-10): the graph of an arbitrary
ambient injection is a subset of `a x b` that need not be
constructible. In a classical semantics where the ambient and the
constructible cardinality of one pair disagree (a collapse extension
at `a = ℵ₁^L`, `b = ω`), the ambient injection exists and no code
does, so the bridge is FALSE there. The coded route cannot be
completed without an axiom the ambient theory does not carry.

## THE SITE GRAIN IS CLOSED

`[LJ-1.617]` measured that the BILL pays in the site grain. That
demand-side measurement stands. What this task adds is the supply-side
answer: at the site grain the tree pays exactly through the initial
ordinals (`site-at-init`, `agents/tasks/LJ-1-623/Probe623.agda:200-201`,
from `via-col-square`, `src/L/Ordinal/SquareLaw.lagda.md:960-961`),
through the band product (`band-pays-site`,
`agents/tasks/LJ-1-623/Probe623.agda:206-207`, unchanged from
`[LJ-1.621]`), or through the residue. An arbitrary site is none of
the first two, and the third is `[LJ-1.618]`'s wall. So
`[LJ-1.617]`'s measurement buys the campaign nothing as a supply
route, and the mathematician must say that to the owner.

## WHAT WOULD REOPEN IT

- Codes at the ambient-least ordinal, as data. The probe consumes them
  (`agents/tasks/LJ-1-623/Probe623.agda:140-148`). Any future supply
  that produces code DATA at `κL` finishes ingredient (iii) for free.
- Or `AmbientToCoded` as an owner-ruled axiom. This stop measured that
  it is not a construction.
- Or a weakly constant endomap on the ambient payload at the
  single-pair grain, in the sense of Kraus Theorem 16
  (`dev/literature/truncation-and-selection.md:158`). The tree builds
  one at the CODE grain (the least-code selection,
  `src/L/Cardinal.lagda.md:194-195`) and none at the ambient grain.
