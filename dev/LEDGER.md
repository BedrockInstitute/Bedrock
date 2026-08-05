# The size ledger

How Bedrock counts what it has built, what it still owes, and what the two together come to.
This document explains the ledger; the canonical **data** is
[dev/ledger.toml](ledger.toml), and the tool that reads it is
[scripts/ledger.py](../scripts/ledger.py). The split follows the glossary's pattern
([dev/glossary.toml](glossary.toml) plus [dev/GLOSSARY.md](GLOSSARY.md)): machine-checked data
in one file, the prose that explains it in another, and nothing canonical in two places (PLAN
decision D24).

Run it:

```
python3 scripts/ledger.py            # the full ledger
python3 scripts/ledger.py --brief    # one line: standing, endpoint, overage
python3 scripts/ledger.py --check    # validate the declaration; this is what make check runs
```

## Why this exists at all

The goal register carried a standing figure of **12,633** for nine consecutive dispatches. On
2026-08-05 `[L3.32-T55]` went to check it and found it had **never been a measurement**. It was
a projection fixed at `[T25]`:

```
12,633 = 12,737 (a recon's retained-standing baseline)
       + 1,379 (a planned keep)
       - 1,289 (a planned retirement)
       -   141 (a planned re-type)
       -    67 (a planned re-home)
       +    14 (a delivered kit)
```

Some of those terms had executed, some were still planned, and none was re-measured afterwards.
Every ledger figure from `[T9]` to `[T49]` re-quoted it, including one report dated the same day
the tree already held a dozen chapters the figure did not know about. The true standing that day
was about **14,997**, and nobody had noticed the drift, because a number written in prose has no
way to notice anything.

**So the cure is not a tidier document.** The cure is that standing is **computed from the tree
and written nowhere**. `dev/ledger.toml` contains no standing figure and never will. If you find
one written down anywhere in this repository outside a dated historical record, it is stale by
construction; run the script instead.

## The caliber

One convention, pinned, and it is the only one:

> A size figure is the count of **non-blank lines inside ` ```agda ` fences**, over
> **git-tracked `*.lagda.md` under `src/`**.

Consequences worth stating, because each has bitten:

- **Prose is not counted.** A chapter's English and Chinese text costs real effort and appears
  nowhere in this ledger. The trilingual prose burden is tracked as an excluded row.
- **The archive is not counted.** `archive/` sits outside `src/` precisely so every gate is
  structurally blind to it (D20). Retired code leaves the ledger when it is archived.
- **Probes are not counted**, because probe files are never committed (D-1) and the script reads
  only git-tracked files. A probe that measured 395 lines contributes nothing to standing, which
  is correct: it was thrown away.
- **A file being in the tree does not mean it is standing.** See the retirement set below.

## Standing

**Standing = tracked total minus the booked retirement set.**

The retirement set is ruled by D18 and disposed of by D20 (archived, never deleted). It is
declared entry by entry in `dev/ledger.toml`, each with the authority that put it there, and
`scripts/ledger.py --check` verifies that every declared path still exists. That check is what
catches a declaration going stale after a file moves.

One trap is recorded in the data file itself and repeated here because it has already misled a
recon: the **R5-era census books a different retirement set**, since it was written under the
J-trophy route. Under D18 the bridge **survives** as the wing's corollary, while the census
retires it. When the two disagree, D18 wins.

## Remaining work

Every open block is a row in `dev/ledger.toml` carrying:

- both bands, **naive** and **calibrated** (PLAN section 6.2: naive is the component sum on
  delivered comparables, calibrated applies this project's measured underestimation, about
  **x1.3** for a row anchored by a probe or a delivered comparable and **x3** for a row only a
  survey could reach);
- its **class**, saying which of those applies and why;
- its **gate**, if D22 has assigned one, with the gate's current state;
- its **provenance**, the report or register entry the band comes from.

Two rules the checker enforces:

- **A row with no provenance is a defect.** An unpriced item is recorded as unpriced in the
  excluded list, never as zero. Silently omitting an unpriced block is how a projection becomes
  optimistic without anyone deciding that it should.
- **A calibrated band below its naive band is a defect.** Calibration prices ignorance; it never
  makes a row cheaper.

Rows deliberately kept **out** of the sum live in the `[[excluded]]` table with the reason. An
absence recorded there is a decision; an absence not recorded anywhere is an oversight.

## Derived rows

One row (W7's residue) is **derived by subtraction**: its booked band covers work that is now
partly delivered, so the residue is the band minus what landed. Derived rows are flagged
`derived = true` and print with a `(derived)` marker, because a derived figure is weaker evidence
than a cited one and should never be quoted as though a report had measured it.

## What the number is for, and what it is not for

The 25k figure is a **reference line and a best-effort compression target**. PLAN decision D26 is
canonical and says it plainly:

> Evidence may move a technique; a number alone moves nothing, and it may never put the campaign
> route back on the table.

So the obligation an overage creates is exactly threefold, and it stops there: **evaluate coolly,
record the overage in both calibers as a plain number, and work it down wherever real compression
exists.** The script prints the overage and draws no conclusion from it. Neither may any report:
a report that reasons from an overage to a route change is rejected at the return audit
(`dev/ORCHESTRATION.md` section 6).

This cuts both ways, and the second way matters more. Because the number cannot force a route
change, there is no reason to shade it, round it kindly, or leave an unpriced block off the
sheet. The ledger is free to be honest precisely because it is not a verdict.

## Keeping it current

**Enforcement point:** `scripts/ledger.py --check` runs inside `make check`, so a declaration that
names a file no longer in the tree, a row missing a band or a provenance, or an inverted or
impossible band, fails the commit gate.

What the gate cannot check, and what a contributor therefore owes:

- **When a chapter lands**, its work moves from a remaining row to standing. Standing updates
  itself; the remaining row does not. Narrow or close the row in `dev/ledger.toml` in the same
  commit, and say in the commit message whether the chapter came in inside its band. A chapter
  that lands over its band without that being recorded is exactly how an endpoint rises without
  anyone deciding it should.
- **When a gate returns**, move its row's class from x3 toward x1.3 if it went green, and record
  what the red left if it did not. That reclassification is the whole economic point of gating
  (D22): a green gate narrows the band's top, which is the edge that touches the reference line.
- **When a ruling changes what retires**, edit the `[[retire]]` table and cite the decision in the
  entry's `authority` field.
- **Never write a standing figure into prose.** Quote `ledger.py --brief`, or cite this document.
  A number copied into a paragraph is a number that will be wrong in a week and re-quoted for
  nine dispatches before anyone checks.
