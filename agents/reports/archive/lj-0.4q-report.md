# LJ-0.4q: take the two DELETE rows [LJ-0.4p] traced

Status: COMPLETE. No commit, no push.

## 1. THE VERDICT

VERDICT: Row 1 LANDED, net minus 27. Row 2 LANDED, net minus 7.
Total net minus 34.

## 2. PER ROW

| Row | File | In-fence before | In-fence after | Net | Seconds before | Seconds after | Exit code | Verdict |
|---|---|---:|---:|---:|---:|---:|---:|---|
| 1 | src/L/Coding/CodeSet.lagda.md | 195 | 168 | -27 | 2.27 | 1.20 | 0 | LANDED |
| 2 | src/L/Choice/Table.lagda.md | 418 | 411 | -7 | 1.36 | 1.46 | 0 | LANDED |

The count uses the ledger caliber. A script counts non-blank lines inside
` ```agda ` fences. I did not count by hand. The before and after seconds are
warm runs with interface caches in place.

The first post-edit checks were cold. CodeSet took 3.48 s. Table took 33.78 s,
because the process re-checked Uniform, Powerset and Sequence. The check of
Order took 53.60 s, because the process re-checked Hierarchy, Internal,
Faithful, Limit, Before and Adequate. Every check exited 0.

## 3. WHAT THE CHAPTER LOSES

Row 1 loses the arity-one set `Codes` and its whole story. That story is the
predicate `isCode`, the superset and separation that cut the set out, and the
two directions `Codes-out` and `Codes-in` that characterized it. The chapter
also loses the "Both directions" and "Round trip" sections, which explained
that a member of `Codes` is exactly a key of an arity-one formula over the
carrier. It loses the definable-powerset motivation in the opening, which said
that `Def A` indexes by the arity-one class. What remains is the all-arity set
`AllCodes` with its predicate `isCodeAny` and its own two directions. The
shared witness machinery stays: `hasWitness`, `witnessAt-in`, `witnessAt-out`,
`witness-in`, `witness-out`, `smallAny`, `sepAny`, `keyS` and `codeS`.

Row 2 loses the two instantiations `ix-fill` and `ix-rep`. The recap clause
that named them is cut in both languages. The general pair `ixRel-fill` and
`ixRel-rep` and the siblings `relL-fill` and `relL-rep` remain.

## 4. THE CATALOG NAMES I COULD NOT TOUCH

The catalog names the deleted names at these lines. I did not touch the file.
The orchestrator rewires it.

| Deleted name | `src/Everything.lagda.md` line |
|---|---|
| `isCode` | :514 (English), :962 (Chinese) |
| the two-set description of CodeSet | :499-519 (English), :962 (Chinese) |
| `ix-fill`, `ix-rep` | :766 (English), :975 (Chinese) |
| the four-reading description of Table | :766 (English), :975 (Chinese) |

The import at `src/Everything.lagda.md:346` stays. The module
`L.Coding.CodeSet` survives the cut.

## 5. EVERY NAME I GREPPED, AND WHERE IT STILL APPEARS

| Name | Where it still appears |
|---|---|
| `Codes` (the CodeSet set) | deleted. No reference remains. The FOL.Coding relation `Codes` is a different live name (src/FOL/Coding.lagda.md:160-182 and prose at :23, :37, :90, :146, :152, :194, :198, :202, :211, :229; src/V/Coding.lagda.md:245, :248; src/Everything.lagda.md:212, :289). The dev prose words at dev/PLAN.md:192, dev/ARCHIVE.md:85 and dev/memos/* are not the CodeSet set |
| `Codes-out`, `Codes-in` | deleted. Remaining prose: dev/PLAN.md:415, dev/JOURNAL.md:165 |
| `key∈Codes` | deleted. No reference remains |
| `IsKeyOver` | deleted. No reference remains. `IsKeyOverAny` is live and distinct (CodeSet, Faithful.lagda.md:66) |
| `isCode` | deleted. Remaining: src/Everything.lagda.md:514, :962; _build/lj-1.1-recon.md:25 |
| `small`, `sep` (CodeSet privates) | deleted. The English word "small" remains in prose. The name `sep` remains as an unrelated local binding in Table.lagda.md:693, :783-791. No external reference to the CodeSet privates exists |
| `ix-fill`, `ix-rep` | deleted from Table. Remaining prose: src/Everything.lagda.md:766, :975; src/L/Choice/Order.lagda.md:639, :652; src/L/Choice/Limit.lagda.md:698-699, :705 |

I also grepped the live look-alikes. AllCodes, AllCodes-out, AllCodes-in,
key∈AllCodes, IsKeyOverAny, isCodeAny, smallAny and sepAny are alive.
keyArityAtL is alive through Powerset.lagda.md:59, :298, :306, :314.
arityNumAtL is alive through Faithful.lagda.md:64, :288-303. The general pair
ixRel-fill and ixRel-rep is alive in Table and Order. The relL siblings are
alive in Table and Order.

## 6. DD4

Row 1: the wing cites CodeSet for `codeS`, `keyS`, `isCodeAny` and the
all-arity machinery (_build/lj-1.1-recon.md:25, :66). The funded wing blocks
ride `LsetGraphAt`, `DefAt` and `orderL-fill`/`orderL-rep`
(_build/lj-1.1-recon.md:99). No block names the arity-one set or `isCode`.
The arity-one set is not a name the wing would rebuild. DD4 does not rescue it.

Row 2: the wing rides `orderL-fill` and `orderL-rep`, which are the relL pair
at the bounding ordinal. The general pair `ixRel-fill` and `ixRel-rep` stays
live. The wing does not cite the relL instantiation. DD4 does not rescue it.

## 7. LITERATURE USED

`dev/literature/digest.md`: read the sections on definability, the hierarchy
and master codes. The orthodox route states the definable powerset as
metatheory (SZ Lemma 1.4, digest.md:47-48). Master codes are fine-structure
reductions, a different notion (digest.md:352-360). No fetched text names an
arity-one code set as an object of the theory. The code set is this project's
internalization machinery.

`dev/literature/j-hierarchy.md`: read. The stratification and well-order
sections name no code set. Nothing in it bears on either row.

WHY NOT: no other file in `dev/literature/` was read. The question is narrow,
and the brief named these two files.

## 8. ARCHIVE USED

`_build/lj-0.4p-report.md`: read first. It traced both rows to every reference
and gave the prose provenance per row. Its line numbers drifted under
`[LJ-0.4n]`. I re-verified every line in the working tree before editing (D-10).

`_build/lj-0.4a-report.md:151-154`: read. The rendered-form false positives do
not apply to this cut. `keyArityAtL`, which `isCode` used, is alive through a
real code use in Powerset, not through a rendered form.

`dev/memos/simplification-register.md:33-38`: read. The S13-S18 verdicts do
not bear on either row.

`dev/LESSONS.md` D-27 at :1703 and D-10 at :1316: read. The D-27 operational
test was applied to both rows. Class 1 was the binding test.

`_build/lj-1.1-recon.md`: read. Its DD4-relevant lines are :25, :66 and :99.
The six funded wing blocks cite neither deleted name.

## 9. WHAT I AM NOT SURE OF

Order.lagda.md:639, :652 and Limit.lagda.md:698-699, :705 still name
`ix-fill` and `ix-rep` in prose. Both files are outside my write scope. The
orchestrator must rewire them or rule KEEP. The claims they make stay true
through the live general pair, but the names are stale.

The Everything catalog needs the rewire listed in section 4. The Chinese
catalog at :962 and :975 carries the same stale two-set and four-reading
descriptions as the English side.

`_build/lj-1.1-recon.md:25` names `isCode`. That dev line is now stale.
`dev/PLAN.md:415` and `dev/JOURNAL.md:165` record that the sweep stopped at
`Codes-out` and `Codes-in`. Those rows are now historical.

The seconds are warm and cold mixed. The cold re-check of Table included
re-checked consumers, so the before and after seconds are not directly
comparable. At 34 lines the seconds change is noise for DD24.

No `make check` ran. No whole-tree check ran. No git reset, checkout, stash or
clean ran. The working tree has exactly two modified files.
