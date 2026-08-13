# LJ-0.4m: the dead-name re-scan, after four rounds of deletion

Status: COMPLETE. No commit, no push. The tree is as this report describes.

## 1. THE VERDICT

Net landed: minus 68, measured by the ledger caliber. The AC side moves from
17,166 to 17,098. The whole tree moves from 17,766 to 17,698.

Every edited file typechecks. The linters are clean. The consumers check
green. The block is exhausted: no further dead name exists in the edit scope.
The remaining levers are content rulings, not deletions.

## 2. DELETED

Method, stated once. I verified every name with a boundary-aware whole-tree
grep in agda fences, then checked the rendered form, the pattern-match
position, and any open-public re-export. A name died only when no use existed
outside its own declaration. I deleted in batches by file and typechecked
after each batch.

| Name | File:line | Lines | Verification |
|---|---|---:|---|
| `defStage-ord` | L/Choice/Stage.lagda.md:266-268 | 8 | decl only, no prose name anywhere |
| `defStage-suc` | L/Choice/Stage.lagda.md:270-272 | (with above) | decl only; the opaque block died whole |
| `stepPath` | L/Choice/Step.lagda.md:778-790 | 36 | private; only consumer `sameStep`, deleted below; imports `J`, `PathP`, `isPropIsOrd`, `Lset-mono` fell out |
| `up` | L/Choice/Step.lagda.md:821-822 | (with above) | private; only consumers inside the dead block |
| `sameBirth` | L/Choice/Step.lagda.md:824-825 | (with above) | private; only consumers inside the dead block |
| `sameStep` | L/Choice/Step.lagda.md:827-830 | (with above) | private; only consumer `agree`, deleted below |
| `agree` | L/Choice/Step.lagda.md:832-835 | (with above) | private; served `endExtension`, deleted in `ab99b23` |
| `unfoldγ` | L/Choice/Step.lagda.md:837-838 | (with above) | private; served `endExtension` |
| `unfoldβ` | L/Choice/Step.lagda.md:840-841 | (with above) | private; served `endExtension` |
| `limitS` | L/Choice/Limit.lagda.md:406-407 | 2 | decl only, no prose name anywhere |
| `InLimitAt-out` | L/Choice/Internal.lagda.md:186-198 | 17 | decl only; `read` and `atValue` died with it; import `Lset-only` fell out |
| `Held` | L/Choice/Internal.lagda.md:173-176 | (with above) | only consumers were the dead `read` and `atValue` |
| `val-graph` | L/Recursion.lagda.md:195-197 | 3 | decl only; the statement still lives in `funct`'s type |
| `uniqueSetOf` | L/FOL/ZFModel.lagda.md:397-398 | 2 | decl and local prose only; alias of the live `setOf-unique` |

Line numbers are the original HEAD positions. The per-file deltas below are
the measured ledger figures. `agree` in `L.Choice.Finite` is a different
definition and stays.

## 3. KEPT AND WHY

The `Codes` and `CodesT` families in `src/FOL/Coding.lagda.md:156-182`,
including the fourteen `c-*` constructors. They have no code consumer in the
whole tree. They are content. The chapter's recap names `Codes` as its real
interface, and `src/Everything.lagda.md:212` and `:289` name it the same way.
Deleting the relation would remove the chapter's stated subject, exactly the
`Codes-out`/`Codes-in` ruling. They stay.

`LsetGraph` in `src/L/Coding/Sequence.lagda.md:364-365`. No code consumer
exists. The chapter prose names it as the deliverable, and
`src/Everything.lagda.md:593` and `:965` name it. It stays.

The End-extension prose in `src/L/Choice/Step.lagda.md:793-813` (both
languages). It states the end-extension fact and records the measured cost of
the construction. I deleted the proof machinery, not the statement. The
statement and the measurement stay as content.

## 4. BLOCKED BY THE CATALOG

These names are dead in code. Their only surviving references are prose in
`src/Everything.lagda.md`, which I may not edit. I list them for the
orchestrator to free.

| Name | File:line | Everything prose |
|---|---|---|
| `Codes`, `CodesT` and the `c-*` family | FOL/Coding.lagda.md:156-182 | :212, :289 |
| `LsetGraph` | L/Coding/Sequence.lagda.md:364-365 | :593, :965 |

`Codes` and `CodesT` are also content under rule 2. Freeing the catalog prose
alone is not enough; the orchestrator must rule on the content line before
deleting the family.

## 5. FALSE POSITIVES

Names my scan or the brief flagged that are alive, and how they are reached:

| Name | File:line | Why it lives |
|---|---|---|
| `∅-layer` | L/Constructible.lagda.md:177 | pattern-matched in `layer-trans` at :185 |
| `union-layer` | L/Constructible.lagda.md:179 | pattern-matched in `layer-trans` at :187 |
| `union₂-layer` | L/Constructible.lagda.md:180 | pattern-matched in `layer-trans` at :188 |
| `isSetΩ` | Base/Truth.lagda.md:50 | record field, supplied at :99; named in Prelude prose |
| `defines` | L/Recursion.lagda.md:281 | record field, used as `D.defines` in `asRecursion` |
| `isSet⟪_⟫` | V/Model.lagda.md:444 | rendered form at :462, as block A recorded |

The `c-*` constructors and `CodesT` are dead in code but kept as content, not
flagged here as alive.

## 6. THE NUMBER

Measured with the ledger's own count function on the working tree
(`at_head=False`, the same algorithm and caliber). The ledger tool reads HEAD
at `scripts/ledger.py:84-88`; the orchestrator will see these figures after
committing.

| File | HEAD | Tree | Delta |
|---|---:|---:|---:|
| src/FOL/ZFModel.lagda.md | 91 | 89 | -2 |
| src/L/Choice/Internal.lagda.md | 797 | 780 | -17 |
| src/L/Choice/Limit.lagda.md | 456 | 454 | -2 |
| src/L/Choice/Stage.lagda.md | 136 | 128 | -8 |
| src/L/Choice/Step.lagda.md | 359 | 323 | -36 |
| src/L/Recursion.lagda.md | 97 | 94 | -3 |
| Net | 1,936 | 1,868 | -68 |

Trophy split by the same caliber: base 1,918, ac-only 302, shared 14,878,
gch-only 600. AC total 17,098. Standing 17,698.

The AC target needs 98 more lines. This block has no further dead names to
offer.

## 7. SECONDS

Every edited file, `GHCRTS="-A64m -I0 -M8g"`, one process at a time:

| File | Exit | Seconds |
|---|---|---:|
| src/L/Choice/Stage.lagda.md | 0 | 1.5 |
| src/L/Choice/Step.lagda.md | 0 | 2.1 |
| src/L/Choice/Limit.lagda.md | 0 | 2.4 |
| src/L/Recursion.lagda.md | 0 | 0.9 |
| src/FOL/ZFModel.lagda.md | 0 | 0.8 |
| src/L/Choice/Internal.lagda.md | 0 | 98.0 |

The Internal figure includes a cold re-elaboration of its import closure.
Block A measured 35.2 seconds with a warm cache. No seconds lever exists in
deletion (P-q); I claim no timing movement beyond the wall times above.

Consumer sanity checks:

| File | Exit | Seconds |
|---|---|---:|
| src/L/Choice/Faithful.lagda.md | 0 | 5.8 |
| src/L/Choice/Adequate.lagda.md | 0 | 14.7 |

`lint-prose.py --check` clean on every edited file. `lint-agda.py --check`
clean on the tree. `weave-i18n.py --check` clean on every edited file.

## 8. DD4

One line: this block deletes, so DD4 applies in the negative and nothing was
built or shared.

Recorded for the GCH wing, with file:line, so nothing is deleted silently:

| Name | File:line | How the wing rebuilds it |
|---|---|---|
| `defStage-ord`, `defStage-suc` | L/Choice/Stage.lagda.md:266-272 | one-line extractions from `thePred` at :255-257 |
| `val-graph` | L/Recursion.lagda.md:195-197 | one-line projection from `funct` at :107-109 |
| `InLimitAt-out` | L/Choice/Internal.lagda.md:186-198 | derivable from `LsetGraph-out` at L/Coding/Sequence.lagda.md:378-379 |
| `limitS` | L/Choice/Limit.lagda.md:406-407 | still inline as `limitEl` at Limit :406 and as `ωStage` at Internal :151 |
| `uniqueSetOf` | FOL/ZFModel.lagda.md:397-398 | alias; `setOf-unique` stays live at :95-97 |
| Step end-extension machinery | L/Choice/Step.lagda.md:778-841 | the fact stays in prose; `orderAt-step` at :745-746 is the unsealing lemma |

## 9. LITERATURE USED

`dev/literature/digest.md` and `dev/literature/j-hierarchy.md`: checked for
any named result matching the deleted names. None exists. Every deleted name
is proof machinery or a local alias, not a named theorem of the orthodox
development. The end-extension fact stays stated in the chapter prose, and its
theorem was already deleted before this block.

## 10. ARCHIVE USED

`_build/lj-0.4a-report.md`: read first. It is the model return. Its false
positive list at :151-154 and its residual doubt at :277-279 drove my
verification steps.

`_build/lj-0.8-review.md` 6.1 and 7.6: the within-file dedup scan and the
orchestrator-side actions. My block is the re-scan the brief orders, and it
completes the deletion class the review priced.

`dev/memos/simplification-register.md:33-38`: S13 to S18 verdicts. No
reverted shape was re-proposed.

Commit `ab99b23`: the deletion of `endExtension` and `Lset-μ`. I verified the
worked example at its own site. The cascade was real: `endExtension`'s helpers
were dead, and `Lset-μ`'s consumer `defStage-suc` was dead.

`dev/LESSONS.md` via `python3 scripts/rules.py --for build`: D-10, P-q, P-m,
C-12, C-22. I re-derived every residue against the tree. I ran one Agda
process at a time under the cap. I wrote the report incrementally.

## 11. WHAT I AM NOT SURE OF

1. The End-extension prose in Step stays, and it now describes deleted code.
   It states a design fact and records a measurement, which is why I kept it.
   The orchestrator may rule it stale instead.
2. The `Codes` and `CodesT` families are dead in code with zero consumers.
   They are the largest single lever in the tree, about 28 fence lines, but
   they are content and catalog-blocked. Deleting them needs a content ruling,
   not a deletion dispatch.
3. The AC side ends 98 lines above the 17,000 target. This block confirms the
   honest reachable figure from above; the remaining mass is content.
4. The Internal check time includes a cold dependency re-elaboration. I make
   no seconds claim for that file.
5. The after figures are the working-tree counts by the ledger algorithm. The
   ledger tool itself reads HEAD, so the numbers land when the orchestrator
   commits.
