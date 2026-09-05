# [LJ-1.605] stop: the uniform supply IS the square law at the band, and the campaign has forbidden the dispatch that would build it

## THE STOP

**NO-GO on `uniform-pairing`.** The brief's obligation is a single supply
of `L.StageCardinal`'s `sq` that discharges every fiber of the band at
once, and that type is `SqParam α₀`
(`agents/tasks/LJ-1-594/runs/W3.agda:30-34`). By the no-coherence
identity, which this probe re-proves as a term at its own site
(`agents/tasks/LJ-1-605/Probe605.agda:84-88`), that type is
**definitionally the untruncated square law at every infinite ordinal of
the band, fiber by fiber**:

```
SqParam α₀ ≡ (δ : V ℓ) → ⟨ δ ∈ sucV α₀ ⟩
             → (⟨ δ ∈ ω ⟩ → ⊥) → sq δ
```

So the question "can one build the uniform pairing without the square
law" has a type-level answer: **a uniform pairing IS the square law at
the band, at the module grain `[LJ-1.604]` named.** Building it here
would not reduce the square law to anything. It would be the next
square-law dispatch, and it is forbidden.

## THE EVIDENCE, ALL AT `file:line`

**1. THE TREE HOLDS THREE SUPPLIES, AND THE ONLY BAND-SIZED ONE IS
TRUNCATED.** All three are re-ascribed at the band fiber, TYPE ONLY, in
`agents/tasks/LJ-1-605/runs/W3.agda`:

| supply | site | truncation | home |
|---|---|---|---|
| `squareω : sq ω` | ω, one site | none | `src/L/InjChain.lagda.md:184-185`, W3 row `supply-ω` |
| `via-col-square : (δ : S) → Init δ → sq δ` | the initial ordinals, only | none | `src/L/Ordinal/SquareLaw.lagda.md:960-961`, W3 row `supply-init` |
| `sq-trunc-closed` | every site of the band | **`∥ sq δ ∥₁`, in the type** | `src/L/SquareLawClosed.lagda.md:325-328`, W3 row `supply-band-truncated` |

The second supply is `Init`-restricted by the chapter's own prose, the
extraction wall: at a non-initial ordinal the honest equivalence needs
the least-of transfer, which the chapter does not build
(`src/L/Ordinal/SquareLaw.lagda.md:14-17`).

**2. THE MISSING DIRECTION IS NAMED AS A TYPE, AND THE TREE HOLDS NO
TERM OF IT.** `missing-direction-type`
(`agents/tasks/LJ-1-605/Probe605.agda:177-181`) states, at the type
level, the untruncation from the truncated band supply to the
obligation. No term of the probe has that type. The measurements that
say the tree holds none:

- the payload is data, and a data payload does not come out of a
  truncated selection (`dev/literature/truncation-and-selection.md:146-148`),
  with the exact necessary-and-sufficient criterion the `splitSup`
  form (same file, section 2.4);
- the truncated square law holds at every infinite ordinal, no choice,
  and the cheap cure is NO (`archive/dev/LJ-dispatch-index.md:187`,
  `[LJ-1.111]`);
- the threading of that truncation into the live consumer is a wall,
  route level, reverted, with the cause proved
  (`archive/dev/LJ-dispatch-index.md:190`, `[LJ-1.114]`);
- the non-initial untruncated witness was measured PARTIAL: initial
  ordinals only (`archive/dev/LJ-dispatch-index.md:183`, `[LJ-1.107]`).

**3. THE CAMPAIGN FORBID THE DISPATCH THAT WOULD BUILD IT.** The square
law at the campaign's own spelling reduces to B9, and the review of
`[LJ-1.593]` states the funding rule: **"DO NOT FUND THE SQUARE LAW
AGAIN. A fourth dispatch on this object buys nothing that is not in
this file. Fund B9, and the square law is a corollary already
written."** (`agents/tasks/LJ-1-593/review-of-square-coded.md:82-84`).
A uniform pairing that proves injectivity at every δ of the band is
the square law at the band: that is the object of this file, not a new
one.

**4. B9 BEHIND IT IS NO-GO.** The reduction runs one way
(`square-from-b9`, `agents/tasks/LJ-1-593/Probe593.agda:532-533`), and
the row it reduces to, `StageCountedCoded`
(`agents/tasks/LJ-1-564/Probe564.agda:127-130`), is NO-GO: nothing in
`src/` codes an arbitrary ambient injection, by a generator argument
(`agents/tasks/LJ-1-533/review-of-StageCountedCoded.md:107-111`): the
only two generators of an L-element set are `hasSeparationL` and
`hasReplacementL`, and both take a `Formula` in their type

## WHAT THE BRIEF WILL NOT HAVE FROM THIS TASK

- No term named `uniform-pairing` is written, because on a NO-GO the
  brief's type is not inhabited.
- Nothing is postulated, and nothing landed in `src/`.
- The probe is GREEN (`agents/tasks/LJ-1-605/runs/final-1.out` to
  `final-3.out`, exit 0), carries no hole and no postulate, so every
  row in it is a measurement and not a claim.

## THE RULING FOR THE OWNER

The brief said: **a NO-GO that shows the uniform supply needs the
square law is a ruling, and the mathematician carries it to the owner
rather than funding a fifth attempt at either object.** This is that
NO-GO. The uniform supply needs the square law in the strongest
sense: it is the square law at the band, by a `refl` identity of
types. The tree holds it at ω, at the initial ordinals, and truncated
at the band. The missing direction is the untruncation of a data
payload, the wall `[LJ-1.114]` already proved, at the B9 that
`[LJ-1.533]` already refuted.

## WHAT IS NOT CLAIMED

- The target is not false: classically, at every infinite ordinal the
  square is in bijection with the ordinal, and the endpoint is
  L ⊨ ZFC. The NO-GO is a funding and a dispatch-count statement
  about the tree, not a truth statement about set theory.
- This is not a fifth square-law dispatch. No construction of a
  pairing is attempted, and no injectivity proof for a new scheme is
  written. The probe re-ascribes what the tree holds and names what it
  does not.
- No route through ordinal arithmetic, via-collapse, or least-of is
  re-measured: the measurements above are the campaign's own, at their
  own sites, and a measured cure does not transfer by analogy, but
  neither does a measured wall need re-measuring at a site it
  already proved.
