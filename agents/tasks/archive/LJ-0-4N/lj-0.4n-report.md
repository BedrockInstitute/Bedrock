# LJ-0.4n: the shape half of the recursion assembly, one parameter

Status: COMPLETE. No commit, no push. The four files carry the change.

## 1. THE VERDICT

**LANDED with a net of minus 104.** The floor is minus 60. The block
clears the floor by 44 lines. No file's seconds rose above the noise
rule. The Before gate passed first. Its numbers are in section 3.

## 2. THE SITE GREP, BEFORE THE KIT

The mechanism is the shape half of the recursion assembly. Its parts are
`ApproxAt`, the four reads, the graph with `GraphOf`, `Graph-in` and
`Graph-out`, and the pair graph with `PairOf` and its two reads.

The grep is `rg -n "ApproxAt :|GraphAt :|RelGraphAt :|PairGraphAt :|PairRelGraphAt :" src/ --glob '*.lagda.md'`. It found five defining sites.

| File | Block | Line | In-fence |
|---|---|---:|---:|
| `L.Coding.Sequence` | `ApproxAt` and four reads | :281-307 | 23 |
| `L.Coding.Sequence` | graph block | :361-379 | 15 |
| `L.Choice.Table` | shape block | :406-446 | 31 |
| `L.Choice.Table` | pair graph | :601-622 | 17 |
| `L.Choice.Before` | shape block | :714-746 | 27 |
| `L.Choice.Before` | graph block | :747-766 | 15 |
| `L.Choice.Before` | pair graph | :1213-1241 | 24 |
| `L.Hierarchy` | pair graph | :448-476 | 21 |
| **gross deletable** | | | **173** |

I re-verified every line number before editing. The counts match
`_build/lj-0.4f-review.md` section 6.3. The block count is the ledger
caliber. It counts non-blank lines inside the fence that holds the
block.

## 3. BEFORE'S SECONDS

One Agda process ran at a time. Cold means the file's own `.agdai`
moved aside. The dependencies' interfaces stayed. The heap cap was
`GHCRTS="-A64m -I0 -M8g"`.

The main tree had a live sibling edit during the first measurements.
The working tree's git status changed between two checks. I measured on
a snapshot clone at `/tmp/lj04n-clone` after that. The cone is warm
before each timed row. The timed file is cold.

| State | Cold seconds | Exit |
|---|---:|---:|
| Before, baseline | 4.73 | 0 |
| Before, after | 4.20 | 0 |
| Before, after, second run | 4.24 | 0 |

The delta is a saving of 0.53 seconds. It is not a rise. The noise rule
does not stop the block. I report this delta before I touch a second
file. Before went from 1110 to 1052 in-fence lines. Its net is minus 58.

### 3a. THE BREAK-EVEN GATE AND THE PROJECTION

The kit is 53 in-fence lines. It typechecks in Sequence. Before's
measured saving is 58 lines. The break-even is 53 divided by 58, which
is 0.91 sites. The site count is five. The gate passes.

The projection, written before I convert a second site:

| File | Net | Basis |
|---|---:|---|
| Sequence hosts the kit | +19 | measured |
| Before shape and pair | -58 | measured |
| Table shape and pair | -45 | estimated |
| Hierarchy pair | -20 | estimated |
| **total** | **-104** | projection |

The floor is minus 60. The projection clears it by 44 lines. The
measured total came in at minus 104.

## 4. THE NUMBER

The table is the ledger caliber. It counts non-blank lines inside
` ```agda ` fences.

| File | Before | After | Delta |
|---|---:|---:|---:|
| `L.Coding.Sequence` | 138 | 157 | +19 |
| `L.Choice.Table` | 463 | 418 | -45 |
| `L.Choice.Before` | 1110 | 1052 | -58 |
| `L.Hierarchy` | 350 | 330 | -20 |
| **total** | **2061** | **1957** | **-104** |

## 5. THE SECONDS, SUMMED

The kit lives inside Sequence. It is not a new module. Its own check
cost is Sequence's delta, which is 0.00 seconds. The table is the cold
check of each file on the clone.

| File | Before (s) | After (s) | Delta (s) |
|---|---:|---:|---:|
| `L.Coding.Sequence` | 1.38 | 1.38 | 0.00 |
| `L.Choice.Before` | 4.73 | 4.20 | -0.53 |
| `L.Choice.Table` | 2.24 | 2.39 | +0.15 |
| `L.Hierarchy` | 22.53 | 22.42 | -0.11 |
| `L.Choice.Order` (consumer) | 5.58 | 5.54 | -0.04 |
| **sum** | **36.46** | **35.93** | **-0.53** |

The tree-level delta is minus 0.53 seconds. Every per-file delta is
noise except Before's saving. No file rose above the noise rule. The
consumers Limit, Internal, Order and Faithful typecheck clean.

## 6. WHAT I SHARED, AND WHAT I LEFT

I shared the shape half. It lives in one generic module, `RecShape`,
with one parameter `Step`. The module hosts in `L.Coding.Sequence`. Its
content is `Domain₀`, `ApproxAt`, `GraphAt`, the four reads, the graph
triple and the pair graph. It has 53 in-fence lines.

I left the induction half at the sites. It includes the value lemmas,
the table lemmas, the uniqueness lemmas, and the sealed step machinery
in Before. Nothing in the kit mentions a recursion's value, its
uniqueness, or its induction.

The P-r reasoning: P-r bans a fold whose result type every consumer
must unfold. This kit is not that shape. The consumers see
`A.ApproxAt f a`, which is the same `Formula S n` as before. The read
lemmas keep their types. The seconds confirm it. Three sites are flat.
Before is faster.

D-27: nothing is deleted. Every block moved into the kit. `LsetGraph`
stays because the chapter prose names it.

## 7. DD4

One line: the shape half is generic in `Step` alone, and the wing value
is nil; this block pays for itself out of the four sites or it does not
pay at all.

## 8. LITERATURE USED

Read:

- `dev/literature/digest.md:209-262`, section 3. SZ Lemma 1.10 and
  Lemma 1.11 state two objects with one form.
- `dev/literature/j-hierarchy.md:118-150`, section 3. SZ 1.11 states
  the order sequence's two clauses.

The kit stayed on the SHAPE side of the SZ line. It shares the form the
literature states twice. It keeps the values apart. Nothing in the kit
names a value or its uniqueness.

WHY NOT:

- `rudimentary-functions.md`, `fine-structure.md`: the rud basis and
  fine structure. They do not bear on module shape.
- `geology.md`: set-theoretic geology. It does not bear on this block.
- `devlin-errata.md`, `primary-sources.md`, `BIBLIOGRAPHY.md`:
  provenance and corrections. They do not bear on code shape.
- `formalizations.md`, `formalizations-landscape.md`: other
  formalizations. They do not bear on this split.
- `owner-notes-rud.md`: reconciled inside `digest.md` section 4,
  already read there.
- `glossary-review-2026-08.md`, `terms-2026-08.md`: terminology. DD19
  forbids settling a term.

## 9. ARCHIVE USED

- `_build/lj-0.4f-review.md:469-585`: sections 6 and 7. Took the
  one-parameter kit, the site table, and the Before-first order.
- `_build/kits/lj-0.4f-recassembly.lagda.md:49-64,116-148,235-254`: the
  shape half's source. Took the content verbatim.
- `_build/kits/lj-0.4f-hierarchy-wiring.diff`: the rescued wiring.
  Read it. It proves eleven parameters work. This block needs one.
- `_build/lj-0.4f-report.md:1-120`: the refusal this block builds on.
  Read it.
- `_build/lj-0.8-review.md:340-379`: section 7.1, the standing gates.
  Applied the break-even gate and the staging gate.
- `dev/memos/simplification-register.md:33-38`: S13 to S18. Checked
  the shapes. None re-proposed.
- `dev/LESSONS.md:2469` P-q, `:2369` P-r, `:2141` P-l, `:2296` P-m,
  `:1689` D-27, `:1302` D-10. Applied each to this block.
- `scripts/rules.py --for build`: read every statement. P-h fixed the
  kit at one parameter. C-12 fixed the heap cap. D-10 fixed the line
  re-verification.

## 10. WHAT I AM NOT SURE OF

- The kit instances are transparent. The seconds at the four sites are
  flat or better. The remaining seals carry Before's cost. A future
  site with a heavier closed-sentence use may need its own seal. This
  block did not measure that.
- The main tree had a live sibling edit. I measured on a snapshot
  clone. The clone's dependency snapshot differs slightly from the
  final tree.
- The `LsetGraph` alias stays because the chapter prose names it.
  Deleting it would make the net minus 106. The review priced its
  deletion.
- Before's saving is 0.53 seconds. It sits just above the noise
  boundary. I ran the after state twice. I did not run the before state
  a third time.
