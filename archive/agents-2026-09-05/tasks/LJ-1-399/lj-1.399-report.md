# [LJ-1.399] The cost of coding one ambient map at ω: a NO-GO

Date: 2026-08-20. Slot: `coder`. Probe:
[`Probe399.agda`](Probe399.agda). The file is GREEN except for one hole, red by
design, at `Probe399.agda:133`. The review is
[`review-of-omega-pair-code.md`](review-of-omega-pair-code.md).

## VERDICT

**NO-GO. The door+bridge assembly is built and green; the code itself is
blocked by two walls.**

- `omega-leg1`'s assembly is built: `leg1-gives-sq` at `Probe399.agda:106-121`
  is the door + bridge composition at `ωL`, the exact analogue of
  [LJ-1.386]'s `leg1-gives-sq` at `δ := +ω ω`, and it proves NOTHING NEW, which
  is what the brief requires it to do.
- `omega-pair-code` is NOT built. It is left as a hole at `Probe399.agda:133`.
  Two walls stop it, and both are named below with `file:line`.

**The most valuable thing this task can give is the gate, and this is it.** The
brief said a NO-GO earns the gate and that the gate is worth more than a
half-built code. The gate is real and it is two walls, not one.

## 1. What was asked, and what is delivered

| Deliverable | State | Where |
|---|---|---|
| `omega-pair-code` | NOT BUILT, hole by design | `Probe399.agda:131-133` |
| `omega-leg1` | BUILT, green | `Probe399.agda:141-142` |
| the assembly it runs through | BUILT, green | `leg1-gives-sq`, `Probe399.agda:106-121` |
| `ωL` | BUILT, green | `Probe399.agda:93-94` |

`omega-leg1` is `leg1-gives-sq (prodL ωL ωL) (prod-bridge ωL ωL)
omega-pair-code`. It is a closed term of `sq ω` once `omega-pair-code` fills its
hole, and it is built with the door (`code-untruncates`) and the bridge, never
with `squareω`. It lands in `sq (fst ωL)`, which is `sq ω` because
`fst ωL ≡ ω` by definition.

## 2. THE TWO WALLS

### W1. The hypotheses do not determine the members of the internal square

`prodL : S → S → S` and `prod-bridge` are the only hypotheses the brief hands
over. `prod-bridge` is an INJECTION:
`_↪_` is `Σ[ f ∈ (X → Y) ] ((x y : X) → f x ≡ f y → x ≡ y)` at
`src/L/Cardinal.lagda.md:47-48`. It is not a surjection.

`InjCode` has four conjuncts (`src/L/Cardinal.lagda.md:223-228`). The `dom`
conjunct demands a VALUE for EVERY member of the source. Here the source is
`prodL ωL ωL`, so the graph must assign a value to every member of the internal
square. To build that graph by replacement over `prodL ωL ωL`, the formula must
read a member `p` back as a pair `pr x y`. That reading is exactly the
membership reading `prodL-out` at `agents/tasks/LJ-1-388/Probe388.agda:307`,
and the brief did NOT hand it over. Without it, a member of `prodL ωL ωL` is
opaque, and there is no function from it to `ω`.

**This is a brief defect, not a gap in my work.** The coder clause says a brief
that names a statement the tree cannot support is a stop, and to never invent
the specification the brief failed to give. The two hypotheses constrain
`prodL ωL ωL` only to CONTAIN the bridge's image `⟪ω⟫ × ⟪ω⟫`; beyond that it
may be any constructible set, and in general it admits no injection into `ω`.
The statement is not derivable from the two hypotheses, and it is false under
instantiations where `prodL ωL ωL` is larger than countable.

### W2. The pairing formula needs arithmetic the tree does not hold

Even WITH `prodL-out` (W1 closed), the graph must carve the ambient pairing
`pairω` (`src/L/InjChain.lagda.md:184-185`). `pairω` is the Godel collapse: the
archived route names it "compare the larger coordinate, then the first, then
the second; with the order-type reading that collapses each pair to the ordinal
of its predecessors" (`archive/src/2026-08-09-rud-route/Everything.lagda.md:296-299`).

Its value at a pair `(a,b)` of numerals is the position of `(a,b)` in that
order, and the count is:

- if `a < b`: `col(a,b) = b² + a`
- if `a ≥ b`: `col(a,b) = a² + a + b`

That closed form is a direct read of the order (this report states it, with the
archived chapter as the source of the order). So an object-language formula for
the graph needs ADDITION and SQUARING of numerals.

**The tree's coding vocabulary has neither.** It has the successor atom
`sucAt` (`src/L/Coding/Environment.lagda.md:136`), the pair atoms `prAt`/
`pairAt` (`src/L/Coding/Base.lagda.md:254,285`), membership, equality and the
quantifiers. `grep` over `src/L` and `src/FOL` for an `addAt`/`multAt`/
`squareAt` formula returns NOTHING. The tree has no object-language addition
and no object-language multiplication, so the collapse cannot be written as a
`Formula`, and the graph cannot be carved as an L-element by `hasReplacementL`
or `hasSeparationL`. **So the brief's W3 probe `graph-lands` cannot even be
stated: the graph is what is missing, and its placement is downstream of it.**

## 3. The price

**Measured at the wide caliber `-A64m -I0 -M8g`, one Agda process, three runs:
1.72 s, 1.76 s, 1.71 s.** That is the price of the ASSEMBLY (the door + bridge
composition and `ωL`), not of the code. The empty-module floor on this machine
is 0.06 s (the [LJ-1.388] report's number, `agents/tasks/LJ-1-388/lj-1.388-report.md:23`),
so the assembly content costs about 1.65 s and about 60 code lines.

**The code itself is UNPRICED, because it is blocked.** The brief's estimate of
about 150 code lines rests on `IdGraph` at about 100 lines for the identity
(`agents/tasks/LJ-1-386/Probe386.agda:94-193`). That comparable has the wrong
shape: the identity graph's formula is trivial (`prAtL zero (suc zero) (suc zero)`),
while the pairing graph's formula is the Godel collapse. The estimate prices a
trivial formula, and this task found the real formula costs arithmetic the tree
does not have.

## 4. W2 (write-once), stated

The brief says the obligation is at ONE site by design, and that is a departure
from W2's write-once rule. Stated here as required:

- What IS generic in my construction: `leg1-gives-sq` is generic in the
  internal square `P` and in the code. It names no ordinal and no site.
- What IS specific to `ω`: `ωL`, and the pairing formula that W2 blocks. At a
  generic cardinal the collapse is not the numeral count but a full ordinal
  order-type, so the blocked formula is HARDER there, not easier. The finding
  is not "arithmetic is missing only at ω"; it is "the object language has no
  arithmetic, and the pairing needs it at every site".

## 5. C-42, stated

This measurement is at `ω` and it measures `ω`. It does NOT say how far the
wall extends. What it says is: at the cheapest site the campaign has, coding
one non-identity map is not free. The report does not extrapolate to a generic
cardinal; it only notes, in section 4, what WOULD change there.

## ARCHIVE USED

- `archive/src/2026-08-09-rud-route/Everything.lagda.md`: READ. `:296-299`:
  "the canonical well-ordering of a product of ordinals, due to Goedel: compare
  the larger coordinate, then the first, then the second; with the order-type
  reading that collapses each pair to the ordinal of its predecessors,
  bijectively." This is the source of W2's claim that the pairing is the Godel
  collapse.
- `archive/dev/JOURNAL-archived.md`: DECLINED. It is the loop's journal, and
  it holds no statement about the coding vocabulary or the collapse.
- `dev/ARCHIVE.md`: DECLINED. `grep -n "square law"` over it returns nothing,
  so it holds no statement that bears on this task.
- `archive/dev/DECISIONS-archived.md`: DECLINED. It is decision history, not
  a source for the collapse or the coding atoms.
- `archive/dev/TASKS-archived.md`: DECLINED. Task history; the live reports I
  cite are fresher and I do not need the archived copies.

## LITERATURE USED

- `dev/literature/terms-2026-08.md`: READ. `:37`:
  "square law | 平方律 | no literature under that name; the fact is 无穷基数的平方等于自身".
  It confirms the fact is a cardinal fact, which is the ambient side this task
  takes as delivered.
- `dev/literature/truncation-and-selection.md`: READ. `:83-84`:
  "So a proof that only needs cardinal arithmetic never needs an injection as
  data". It supports the framing that the ambient pairing is delivered while
  the CODE is the unpaid object; it does not price the code.
- `dev/literature/devlin-II5.md`: DECLINED. Its pairing/collapse lines are
  about condensation (`:90`, `:197`), not about coding a map into an ordinal.
- `dev/literature/digest.md`: DECLINED. Its Godel-pairing line (`:241`) is
  about a Skolem-hull surjection, a different route; it bears on nothing here.
- `dev/literature/geology.md`: DECLINED. `grep` over it for square, pairing or
  coding returns nothing.

## THE TREE AS I LEAVE IT

I changed two files, and both are mine: `agents/tasks/LJ-1-399/Probe399.agda`
and `agents/tasks/LJ-1-399/lj-1.399-report.md`, plus the review file
`agents/tasks/LJ-1-399/review-of-omega-pair-code.md`. No file outside
`agents/tasks/LJ-1-399/` moved. I ran no `git add`, no commit and no push.

The file's ONLY error is the unsolved meta at `Probe399.agda:133`, the hole
`omega-pair-code = ?`. Everything else is green.
