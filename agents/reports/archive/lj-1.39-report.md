# LJ-1.39 report: measure the de Bruijn index padding compression

Status: COMPLETE. Written incrementally per C-22. No commit, no push.
The report uses ASD-STE100.

## 1. THE VERDICT

**DELIVERED.** The compression saves 318 in-fence non-blank lines (2031 to
1713, a 15.7 percent cut) and the file checks FASTER: median 8.9 seconds of
user time against the control's 9.26, one process, cold, dependencies warm.
The seconds delta is inside the noise rule (0.5 s or 5 percent) and is never
slower on any run. Both stop-lines pass. No exported signature changed.

## 2. THE VARIANT THAT WON

A private abbreviation kit in the `Before.lagda.md` shape, made arity-generic:
the two-shift helper `sh2` plus named constants `z2` to `z9` for the
zero-based successor chains, then a mechanical re-flow that merges short
argument lines into their application heads. I measured option 1 (named
literals) and option 2 (shift helper). Option 1 did not disappoint, so per
the brief I did not build option 3.

The numeric option would fail its own condition anyway. `fromℕ'` takes an
explicit `m < n` proof at every use site, and the proof differs per arity
(`src/FOL/Count.lagda.md:16,285`). That is a coercion at every site. C-33:
the brief named idioms, and the job is "spell each index at its use site with
the fewest tokens"; the named-literal plus shift-helper combination is the
cheapest measured route to that job.

## 3. LINES AND SECONDS

| variant | lines | cold user s | delta |
|---|---:|---:|---|
| control, committed `92e8b8b` (= HEAD) | 2031 | 10.01, 9.20, 9.26 (median 9.26) | - |
| A1 nomerge, `sh2` only, no re-flow | 2037 | 9.00 | +6 (kit only) |
| A2 nomerge, `z` + `sh2`, no re-flow | 2053 | same terms as A2 | +22 (kit only) |
| A1 at 120 cols, `sh2` only, re-flow | 1738 | 8.95, 9.20, 9.18 (median 9.18) | -293, -0.08 |
| **A2 at 120 cols, `z` + `sh2`, re-flow** | **1713** | 8.94, 8.57, 8.94, 8.81 (median 8.9) | **-318, -0.36** |
| A1 at 160 cols | 1628 | same terms as A1 | -403 |
| A2 at 160 cols | 1623 | same terms as A2 | -408 |
| A1 at 200 cols | 1577 | same terms as A1 | -454 |
| A2 at 200 cols | 1579 | same terms as A2 | -452 |

Merging is whitespace-only, so the seconds do not depend on the column
budget. I measured control, A1 and A2 only. Rates: control 9.26 / 2031 =
0.00456; A2 8.9 / 1713 = 0.00520. The rate rises because the same cost
divides by fewer lines. P-q names this: a rising rate after a successful
deduplication is the certificate becoming honest, not a regression.

## 4. DID ANY EXPORTED SIGNATURE CHANGE?

NO. I diffed the exported signatures of the control and both variants with
`Cmd_show_module_contents_toplevel` (Simplified) through one loader that
imports all three probe modules. Each module exports 107 names. The name-set
delta is empty, and the type delta is empty after normalizing the module-name
prefix and whitespace. No theorem statement or type changed.

The file stays `--safe`: no `postulate`, no `TERMINATING`, no hole. No
placement was introduced: no `absFo`, no `placeFo`, no `mapΔ₀`, no `mapΣ`
(P-u's load-bearing zero is untouched). D-26 does not bear. The compression
changes how an index is SPELLED and touches no key, no tower and no
statement. The signature diff is the canary, and it stayed green.

## 5. THE EXACT PATCH

The orchestrator applies this to the master after `[LJ-1.38]` lands. Per
C-32, re-measure the gate on the final file. My numbers are for the committed
2,031-line state.

Edit 1: insert the kit immediately after
`module Cnt = FOL.Count.Count {ℓ = ℓ-suc ℓ} S`:

```agda
private
  -- de Bruijn index abbreviations.  sh2 shifts a Fin index by two;
  -- z_d is the depth-d successor chain above zero.  Generic in the
  -- tail arity, so one kit serves every environment length (DD4).
  sh2 : {n : ℕ} → Fin n → Fin (suc (suc n))
  sh2 i = suc (suc i)

  z2 : {n : ℕ} → Fin (suc (suc (suc n)))
  z2 = suc (suc zero)
  z3 : {n : ℕ} → Fin (suc (suc (suc (suc n))))
  z3 = suc (suc (suc zero))
  z4 : {n : ℕ} → Fin (suc (suc (suc (suc (suc n)))))
  z4 = suc (suc (suc (suc zero)))
  z5 : {n : ℕ} → Fin (suc (suc (suc (suc (suc (suc n))))))
  z5 = suc (suc (suc (suc (suc zero))))
  z6 : {n : ℕ} → Fin (suc (suc (suc (suc (suc (suc (suc n)))))))
  z6 = suc (suc (suc (suc (suc (suc zero)))))
  z7 : {n : ℕ} → Fin (suc (suc (suc (suc (suc (suc (suc (suc n))))))))
  z7 = suc (suc (suc (suc (suc (suc (suc zero))))))
  z8 : {n : ℕ} → Fin (suc (suc (suc (suc (suc (suc (suc (suc (suc n)))))))))
  z8 = suc (suc (suc (suc (suc (suc (suc (suc zero)))))))
  z9 : {n : ℕ} → Fin (suc (suc (suc (suc (suc (suc (suc (suc (suc (suc n))))))))))
  z9 = suc (suc (suc (suc (suc (suc (suc (suc (suc zero))))))))
```

Edit 2: replace literals in body positions only. Never touch a line where a
`:` precedes the first literal (the six signature lines that carry chains:
`src/L/Condensation.lagda.md:964,977,1035,1048,1057,1070`). For each balanced
chain `(suc^k base)` with depth k at least 2, replace it with
`(name)` plus the same number of trailing closing parens that followed the
chain:

- base `zero`, k = 2 to 9: the name is `z_k`.
- any base (including `zero` at k at least 10, and every variable base): the
  name is the `sh2` power. k even: `sh2 (sh2 (... base))`, k/2 applications.
  k odd: `suc (sh2 (sh2 (... base)))`, (k-1)/2 applications.
- depth-1 literals `(suc base)` stay unchanged.

Examples: `(suc (suc (suc K)))` becomes `(suc (sh2 K))`;
`(suc (suc (suc (suc (suc (suc (suc (suc K))))))))` becomes
`(sh2 (sh2 (sh2 (sh2 K))))`;
`(suc (suc (suc (suc (suc (suc (suc (suc (suc (suc t0))))))))))` becomes
`(sh2 (sh2 (sh2 (sh2 (sh2 t0)))))`.

After the `z` replacements, drop the parens around a bare `z_k`
(`(z3)` becomes `z3`). Keep the parens around `sh2` applications; they are
load-bearing.

Edit 3: re-flow. Merge each line into the previous line while the previous
line has positive paren balance and the merged line stays within 120
columns. This converts the replacement into line savings. Without the
re-flow the kit only adds lines (2037 and 2053 against 2031).

The full mechanical transform is generated by `/tmp/compress_lj139.py` in
mode `a2` into `src/ProbeLJ139V2.agda`. Diff `src/ProbeLJ139V2.agda` against
`src/ProbeLJ139.agda` for the exact edit list. The rules are mechanical and
cover the post-`[LJ-1.38]` block 3 as well; run the script on the final
master rather than hand-applying.

## 6. THE TREE-WIDE COUNT

Top five masters by index-only line count. My strict definition is a line
whose only content is one index literal plus the enclosing application's
closing parens.

| master | index-only lines | in-fence non-blank |
|---|---:|---:|
| `src/L/Condensation.lagda.md` | 191 (brief's looser count: 218) | 2031 |
| `src/L/Coding/Unique.lagda.md` | 7 | 630 |
| `src/L/Coding/Sound.lagda.md` | 5 | 801 |
| `src/L/Coding/Shape.lagda.md` | 2 | 354 |
| `src/L/Choice/Before.lagda.md` | 1 | 1052 |

The mass is Condensation by two orders of magnitude. No FOL master has an
index-only line. Four other masters hold a handful each; they are not worth a
kit.

## 7. DD4

An arity-generic abbreviation block is FREE here, measured. The kit types
carry an implicit tail arity (`{n : ℕ} → Fin (suc (suc n))`). The sites solve
it by unification without unfolding the bodies, and the seconds are flat.
The same literal text serves at least three distinct arity types in this
file: Clause's `K : Fin (suc n)`, the envHyp family's `Fin m`, and
DefBodyB's `Fin (5 + n)`. A fixed-arity kit (`Before`'s `s1 : Fin 5` shape)
needs a name per (literal, arity) pair, which is more kit, not less. The kit
mentions no tower, so both towers can share it.

## 8. ARCHIVE USED

- `src/L/Condensation.lagda.md` as committed at `92e8b8b` (= HEAD `c50adf9`),
  whole. Took the 2,031-line control, the literal inventory, and the module
  structure: `:54-56` (Clause's K), `:562-568` (envHypU), `:2234-2244`
  (DefBodyB), `:964-1070` (the protected signature lines).
- `src/L/Choice/Before.lagda.md`, whole. Took the `sh2` helper at `:104-105`
  and the private-block shape at `:248-257`.
- `src/L/Coding/Shape.lagda.md`, whole. Took the `fromℕ'` idiom at `:428` and
  the per-site proof requirement that rejects the numeric option.
- `_build/lj-1.37-report.md`, whole. Took the 2,031 figure and the cold-run
  protocol (one process, `GHCRTS="-A64m -I0 -M8g"`, own interface moved
  aside, dependencies warm).
- `dev/LESSONS.md`, not archived and binding. Read in full: D-28, C-30, P-q,
  P-l, P-m, P-u, D-1, D-10, C-12, C-22, C-32, C-33, C-34, D-26.
- `dev/literature/`: none bears. This is presentational compression inside
  this tree's own code; I spent nothing there.

## 9. WHAT I AM NOT SURE OF

1. The 218 versus 191 index-only count. My strict single-literal count is
   191, and the brief's top-literal frequencies match exactly (23, 16, 12,
   12). The 27-line gap and the 272 versus 116 distinct-literal gap are
   definitional tails I could not reproduce. The compression result does not
   depend on the tail.
2. The 120-column merge budget is my choice. At 160 the saving grows to 403
   to 408 lines, and at 200 to 452 to 454. The seconds are identical at every
   budget because merging is whitespace-only. The orchestrator should pick
   the house style.
3. The sibling's live edits. `[LJ-1.38]` changed the master under me
   mid-session. I pinned every measurement to the committed `92e8b8b` (=
   HEAD) state and never touched the live file or its interface. Per C-32 the
   orchestrator must re-measure the gate on the final file. The patch rules
   are mechanical and cover block 3's literals; my numbers are for the
   2,031-line state.
4. I could not verify a quiet machine. `ps` is blocked in my sandbox. The
   control's first run (10.01) and the run-to-run spread of about 0.6 s
   suggest some background load. All deltas are medians of 3 to 4 cold runs.
5. The `(z3)` to `z3` paren-strip is safe by typecheck and signature diff on
   the committed file. A different context in the post-`[LJ-1.38]` block 3
   could in principle reintroduce a case. Run the mechanical script on the
   final master; do not hand-apply.
