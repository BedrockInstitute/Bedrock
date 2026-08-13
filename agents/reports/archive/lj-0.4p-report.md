# LJ-0.4p: the citation-protected names, re-tested read-only

Status: COMPLETE. No commit, no push. No edit under `src/`. No Agda ran.

## 1. THE TOTAL

Lines freed if every DELETE row is taken: **34**. Row 1 frees 27. Row 3 frees 7.
The count uses the ledger caliber: non-blank lines inside ` ```agda ` fences.
I counted with a script at `/tmp/fenceline.py`. I did not count by hand.
Line numbers are working-tree positions at read time. `[LJ-0.4n]` edits
Sequence, Table, Before and Hierarchy right now, so some numbers may drift.

## 2. THE TABLE

Ranked by lines freed. Every row states its references. A name dies only when
no code use exists outside its own declaration.

| # | Name and file:line | Fence lines freed | Code refs | Prose refs | D-27 class | Prose author and date | VERDICT |
|---|---|---:|---|---|---|---|---|
| 1 | `Codes-out`, `Codes-in`, `Codes`, `key∈Codes`, `IsKeyOver`; cascade `isCode`, `small`, `sep`. L/Coding/CodeSet.lagda.md:256-257, :317-321, :462-487 | 27 (isCode 2, small 2, sep 2, IsKeyOver 3, opaque block 18) | none in the tree. AllCodes pair is live and stays | own chapter: :4-5, :449-460, :495-515, :582-587, :604. Everything: :514-519, :962. dev: PLAN.md:415, JOURNAL.md:165, 0.4a-report section 3, 0.4m-report section 3 | 1, partly circular. The recap clause naming the pair was written today by `ab99b23`, which deleted `Codes-spec`. The opening and the Both-directions and Round-trip sections predate the campaign | `ab99b23` 2026-08-10 wrote :584-587 and :604. `ec3beb95` and `aa7967a3` 2026-07-28 wrote the opening and the two sections | DELETE WITH A CLAUSE CUT. Cut the arity-one narrative in the chapter and in Everything, both languages. The AllCodes pair proves the same characterization at every arity |
| 2 | `Codes`, `CodesT`, the `c-*` constructors. FOL/Coding.lagda.md:156-182 | 26 | none. V.Coding.lagda.md:231 instantiates the module as `VCode`, but no code uses the relation | own chapter: :22-29, :146-152, :194-198, :211-229. V/Coding.lagda.md:245-248. Everything: :212-213, :289. dev: 0.4m-report section 3 | 1, genuine. The opening calls the relation "the deliverable that matters most" | `42a8cfdf` 2026-07-25, before the campaign. Not circular | KEEP. Deleting it would make four documents assert what no longer exists. The recap would lose the relation's claims in both languages |
| 3 | `ix-fill`, `ix-rep`, and the renaming line. L/Choice/Table.lagda.md:836-844 | 7 (ix-fill 3, ix-rep 3, renaming line 1) | none. The general pair `ixRel-fill`/`ixRel-rep` is live at Order.lagda.md:59, :308. The siblings `relL-fill`/`relL-rep` are live at Hull.lagda.md:31, :348-352 and Order.lagda.md:698-702 | own chapter: :805-808, :884-886, :899. Order.lagda.md:639, :652. Limit.lagda.md:698-699, :705. Everything: :766, :975 | 1, but weak. The recap calls the four statements the chapter's deliverable. The pair is an instance of a live general lemma, not a distinct result | `2c94bd7e` 2026-07-31, before the campaign | DELETE WITH A CLAUSE CUT. Cut the "second pair" clause in the recap. Reword the Order, Limit and Everything sentences. The doubt is in section 4 |
| 4 | `LsetGraph`. L/Coding/Sequence.lagda.md:353-354 | 2 | none. `LsetGraphAt` is live in 7 files. `LsetGraph` is its instance at slots zero and suc zero | own chapter: :368, :397, :413-414, :448. Everything: :593, :966. dev: lj-1.1-recon.md:23 | 1, genuine. The recap names it as the chapter's sentence | `dcd4f41d` 2026-07-29, before the campaign | KEEP. DD4 supports it too: the wing writes the exact shape `LsetGraphAt {2} zero (suc zero)`, which is its definition |

## 3. THE PROSE PROVENANCE FINDING

`ab99b23`, today at 14:01, wrote the recap clause that names `Codes-out` and
`Codes-in` at CodeSet.lagda.md:584-587 and :604. The same commit deleted
`Codes-spec`. That protection is circular. The Everything sentence "Each set's
in and out pair closes its round trip" at :517 comes from the same commit.

The old protections predate the campaign. FOL/Coding opening: `42a8cfdf`
2026-07-25. Sequence graph prose: `dcd4f41d` 2026-07-29. Table's four-statement
recap: `2c94bd7e` 2026-07-31. Everything :212 and :289: `42a8cfdf` 2026-07-25.
The CodeSet opening and its Both-directions and Round-trip sections:
`ec3beb95` and `aa7967a3` 2026-07-28. These are genuine class-1 protections.

The Chinese catalog in Everything still names nine deleted names: `asPure₁`
at :288, `allCodes` at :298, `memPairAt` and `seqSet` at :299, `Codes-spec`
and `AllCodes-spec` at :962, `val-defSet` at :963, `witnessInModel` at :969,
`codeFree-limit` at :974, `leastPin` at :977. `ab99b23` rewired the English
catalog and missed the Chinese one. This is stale prose, not a protection.

## 4. WHAT I COULD NOT DECIDE

Row 3, `ix-fill` and `ix-rep`: KEEP versus DELETE WITH A CLAUSE CUT. The recap
is old and calls the four statements the chapter's deliverable. No code
consumer exists. The live general pair covers the same shape. I recommend the
clause cut. The orchestrator may rule KEEP on the old prose.

Row 1, the arity-one CodeSet block: the class-1 protection is real in the old
sections. The clause cut is therefore not small. It removes the Both-directions
section and the Round-trip section in both languages. If the orchestrator will
not cut those sections, KEEP the block. I recommend the cut because the
AllCodes pair carries the same content at every arity.

The Chinese catalog rewire belongs to the deletion commit. It is a catalog
edit, not a `src/` deletion. It is listed here so the orchestrator plans it.

## 5. FALSE POSITIVES

`AllCodes`, `AllCodes-out`, `AllCodes-in`, `key∈AllCodes`, `IsKeyOverAny`:
alive. Consumers at Internal.lagda.md:66, :252-259, :354, :368; Uniform.lagda.md
:83, :136-137, :289, :296, :342, :377; Faithful.lagda.md:63, :301, :306, :344,
:351, :361, :366; Adequate.lagda.md:50, :315, :397-398, :516, :726-727, :804-805;
Order.lagda.md:68, :185, :241. The brief's premise for the AllCodes pair is
stale. The pair has live consumers today.

`LsetGraphAt`: alive in 7 files. Internal.lagda.md:69, :162-175. Faithful.lagda.md
:61, :164-239. Limit.lagda.md:56, :106-182. Order.lagda.md:65, :178-586.
Before.lagda.md:66, :455-1479. Hierarchy.lagda.md:62, :334-648.

`relL-fill`, `relL-rep`, `ixRel-fill`, `ixRel-rep`: alive. Hull.lagda.md:31,
:348-352. Order.lagda.md:59, :308, :698-702.

The settled list stays closed: `endExtension`, `defStage-ord`, `defStage-suc`,
`Lset-μ`, `Sat-out`, `σ₁-up`, `π₁-down`, and the Hull, Collapse and Presentation
modules. I did not re-open them.

## 6. DD4

Row 1: the wing cites CodeSet for `codeS`, `keyS` and the all-arity machinery.
The arity-one set is not a wing block. DD4 does not rescue it.

Row 2: the wing rides code values, not the relation. DD4 is neutral.

Row 3: the wing cites `relL-fill`, `relL-rep` and `ixRel-fill`, `ixRel-rep`.
It does not cite the pair at `relL`. DD4 does not rescue it.

Row 4: the wing certificate is the exact shape of `LsetGraph`. DD4 favors
KEEP, and class 1 already does.

One line for the rest: no other candidate is a name the wing would rebuild.

## 7. LITERATURE USED

`dev/literature/digest.md` and `dev/literature/j-hierarchy.md`: read. Nothing
names any candidate as a named orthodox result. The coding relation and the
code set are this project's internalization machinery. Jensen's master codes
at digest.md:352 are a different notion. Nothing else bears on the sweep.

## 8. ARCHIVE USED

`_build/lj-0.4m-report.md` sections 2 and 3, read first. Its keep list at
:43-58 is rows 2 and 4 of this table.

`_build/lj-0.4a-report.md` section 3 and :151-154. The original keep list at
:97-145 includes `ix-fill` and `ix-rep`. The false positives are at :151-154.

`_build/lj-0.8-review.md:492-509`. Item 7.6.1 priced the prose-bound deletions.
`ix-fill` and `ix-rep` were inside that count and were not deleted.

`dev/ARCHIVE.md:71`, `:84-85`. The Last green column accepts a commit as
provenance. `L.Rud.CodeSet` carries `1a2fbb0`. `L.Godel.Codes` carries
`7bf2913`.

`dev/LESSONS.md:568-594` and `:1700-1752`. Rule 20 carries commit `35cb762`.
D-27 carries the amended classes.

`_build/lj-1.1-recon.md:23-25`, `:65-66`, `:127`, `:196`. The funded wing
blocks, checked for DD4.

## 9. WHAT I AM NOT SURE OF

The working tree changes while I read. `[LJ-0.4n]` edits Sequence, Table,
Before and Hierarchy. Its uncommitted diff does not touch `LsetGraph` or the
`ix` pair, but the line numbers may drift. Re-verify before deleting.

The Sequence refactor moves `ApproxAt` and `GraphAt` into `module RecShape`.
It may orphan or rename other names. I did not judge its in-flight names.

`dev/LESSONS.md:697` (R-28) cites `witnessInModel`, which is deleted. Class 3
is withdrawn. Repoint R-28 at a commit, like Rule 20.

The Chinese catalog count is from the working tree at read time. It may drift
with the sibling's edits.

No Agda ran. No `make check` ran. No git reset, checkout, stash or clean ran.
