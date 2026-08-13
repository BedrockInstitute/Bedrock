# LJ-1.153 report: a delivered frame states a hypothesis that is FALSE

tier: opus (version `override`). Written incrementally (C-22). Every negative is
marked **MEASURED** or **INFERRED**.

**STATUS: STOPPED EARLY ON THE COORDINATOR'S CHECKPOINT ORDER (machine restart).
The tree is in the SAFE state: every master I edited typechecks, exit 0.**
Section 10 is the handover.

## 0. LEAD

- **Refutable: 36 of 38. MEASURED**, exit 0, five shapes, one probe:
  `agents/tasks/LJ-1-153/ProbeLJ1153A.agda`.
- **Not refutable: 2. MEASURED.** Both are checker false positives, section 7.
- **Repaired: 20** (the whole `valK` and `valK-un` family).
- **Not yet repaired: 16** (the rule-2 family). Refuted, unrepaired, section 8.
- **`check-unbound-hyp.py`: 38 BEFORE, 18 AFTER.**
- **Four masters green after the repair**, exit 0 each: `L.Condensation`,
  `L.Condensation.LowerAgree`, `L.Condensation.UpperAgree`,
  `L.Condensation.TwelveAgree`, plus the downstream consumer
  `L.BoundedSubset`.

**The brief's named one-line fix is applied, verified, and its call sites
supply it.**

## 1. Checker baseline (MEASURED)

`.venv/bin/python scripts/check-unbound-hyp.py`, before any edit: **38**.

| rule | count | names |
|---|---:|---|
| rule 1, conclusion subject unconstrained | 20 | `valK` (17), `valK-un` (3) |
| rule 2, premise bound only by free variables | 16 | `codesK`, `unCodesK`, `entryK`, `closedEntryK`, `domEntryK`, `domK`, `wCodesK`, `wUnCodesK`, `wEntryK`, `gCodesK`, `gUnCodesK`, `gEntryK` |
| rule 3, no premise at all | 2 | `answers`, `ih` |

After the repair: **18** (16 rule-2, 2 rule-3). The 20 rule-1 flags are gone.

## 2. Census: every flag, its site, its verdict

**Line numbers in this section are HEAD's**, so they match the brief. My edits
shift `src/L/Condensation.lagda.md` down by 43 lines from `:2731` on.

### 2.1 Rule 1, the `valK` family. 20 flags, ALL REFUTABLE, ALL REPAIRED

`src/L/Condensation.lagda.md`, the twelve row modules, 14 declarations:

| HEAD line | module | arity, tag | kind |
|---:|---|---|---|
| 2740 | `BotAgree` | unary, 7 | uses `valK` |
| 3249 | `PropAgree` | binary, `k` | uses `valK` |
| 3499 | `AndAgree` | binary, 2 | passes to `PropAgree` |
| 3552 | `OrAgree` | binary, 3 | passes to `PropAgree` |
| 3624 | `TopAgree` | unary, 6 | uses `valK` |
| 3689 | `NegAgree` | unary, 5 | uses `valK` |
| 3794 | `ForallAgree` | unary, 9 | uses `valK` |
| 3898 | `ExistAgree` | unary, 8 | uses `valK` |
| 4072 | `ClauseAgree` | unary, 8 | passes to `ExistAgree` |
| 4336 | `MemAgree` | binary, 0 | uses `valK` |
| 4927 | `AllInAgree` | binary, 10 | uses `valK` |
| 5047 | `ExInAgree` | binary, 11 | uses `valK` |
| 5166 | `ImpAgree` | binary, 4 | uses `valK` |
| 5258 | `EqAgree` | binary, 1 | uses `valK` |

The three abstract frames, 6 declarations:
`src/L/Condensation/LowerAgree.lagda.md:105` and `:108`,
`src/L/Condensation/UpperAgree.lagda.md:109` and `:112`,
`src/L/Condensation/TwelveAgree.lagda.md:155` and `:158`.

**`src/L/Condensation.lagda.md:4129` carries a THIRD `valK`, in `AtomLeaf`, and
the checker does NOT flag it.** I read it and left it alone: its conclusion
subject `w` is bound by a premise. **MEASURED**, by the checker's silence and by
reading the type.

### 2.2 Rule 2, the containing-set family. 16 flags, ALL REFUTABLE, NOT repaired

All in `src/L/Condensation.lagda.md`:

| HEAD lines | module | free variable |
|---|---|---|
| 6436, 6440, 6443 | `WitnessAgree` | `w` |
| 6698, 6703, 6707, 6713 | `SatGraphAgree` | `d` |
| 6710 | `SatGraphAgree` (`domEntryK`) | `e` |
| 6930, 6935, 6939 | `LeafAgree` (the `w*` group) | `w'` |
| 6948, 6954, 6959, 6965 | `LeafAgree` (the `g*` group and `domK`) | `d` |
| 6962 | `LeafAgree` (`domEntryK`) | `e` |

### 2.3 Rule 3. 2 flags, NEITHER refutable

`src/L/Reflect.lagda.md:365` (`answers`) and `src/L/StageCardinal.lagda.md:281`
(`ih`). Section 7.

## 3. The refutations (MEASURED, exit 0)

`agents/tasks/LJ-1-153/ProbeLJ1153A.agda`, one agda run, **exit 0, 1.10 s real**,
load average 6.10 at start, `GHCRTS="-A64m -I0 -M8g"`.

Five modules, each ending in `Empty.⊥`:

| module | probe line | shapes it refutes | hypotheses |
|---|---:|---|---|
| `Refute-val` | 88 | `valK`, 17 sites | ONE |
| `Refute-val-un` | 103 | `valK-un`, 3 sites | ONE |
| `Refute-codes` | 120 | `codesK`, `unCodesK`, `wCodesK`, `wUnCodesK`, `gCodesK`, `gUnCodesK` | **NONE** |
| `Refute-entry` | 137 | `entryK`, `closedEntryK`, `domEntryK`, `wEntryK`, `gEntryK` | **NONE** |
| `Refute-dom` | 155 | `domK` | **NONE** |

**The rule-2 refutations are UNCONDITIONAL, and that is stronger than the brief
expected.** A rule-1 hypothesis names the clause set through a SLOT, which a
refuter cannot choose, so it keeps one hypothesis: the clause set holds one code
of the row's own tag, which is the row's own situation. **A rule-2 hypothesis
quantifies over the containing set ITSELF**, so the refuter picks it. The whole
construction is `sucʟ x`, which holds `x` at every `x : S`
(`ProbeLJ1153A.agda:55-56`).

**No refutation uses any property of `K` beyond `K : S`. MEASURED**: every
`Refute-*` module takes `K` as a bare `S`.

**One improvement over `[LJ-1.151]`'s probe B.** That probe hypothesized both the
clause-set membership and the shape equation. Mine BUILDS the code
(`binCode`, `unCode`, `ProbeLJ1153A.agda:58-79`) and PROVES the shape equation,
so only the membership stays a hypothesis.

## 4. The repair, stated before and after

### 4.1 The row modules, 14 declarations

**Before** (`src/L/Condensation.lagda.md` at HEAD `:3249`, the binary archetype):

```agda
  (valK : (c ar a b yc : S) → ⟨ fst c ∈ fst (lookup C γ) ⟩
         → fst c ≡ pr (fst ar) (pr (# k) (pr (fst a) (fst b)))
         → ⟨ fst yc ∈ fst (lookup K γ) ⟩)
```

**After:**

```agda
  (valK : (c ar a b yc : S) → ⟨ fst c ∈ fst (lookup C γ) ⟩
         → fst c ≡ pr (fst ar) (pr (# k) (pr (fst a) (fst b)))
         → ⟨ pr (fst c) (fst yc) ∈ fst (lookup T γ) ⟩
         → ⟨ fst yc ∈ fst (lookup K γ) ⟩)
```

**The premise that now constrains `yc`: `pr c yc ∈ T`, the GRAPH ENTRY.** It says
the graph records `yc` as the value at the code `c`. `yc` is no longer free: it
is the recorded value and nothing else.

**This does NOT weaken the statement to make it true.** The repaired `valK` still
asserts, for every recorded value, that the value is in `K`. That is the honest
content, and `[LJ-1.151]` measured it supplyable in 21 lines at a concrete level
(`agents/tasks/LJ-1-151/lj-1.151-report.md:94-101`): `pr c yc` sits in the graph,
the graph sits in `K`, and `K` is transitive.

**This does NOT change what any theorem SAYS.** `valK` is a module HYPOTHESIS.
Adding a premise to a hypothesis leaves every module conclusion word for word
unchanged. **MEASURED**: no `out`, `back`, `bot-out` or `bot-in` type was edited;
the diff touches only telescope lines and 11 `let` bindings.

### 4.2 The three abstract frames, 6 declarations

The same premise at the frames' own slot spelling. The frames instantiate the
rows at `C = suc (suc zero)`, `T = suc zero`, `B = zero`
(`src/L/Condensation/LowerAgree.lagda.md:208`), so the frame writes:

```agda
          → ⟨ pr (fst c) (fst yc) ∈ fst (lookup (suc zero) γ') ⟩
```

### 4.3 The shared transport, which is the only new code

`binClauseAt` and `unClauseAt` bind the graph entry as the READER `appAt T c yc`,
not as a membership (`src/L/Coding/Model.lagda.md:901`, `:993`). One adequacy
transport converts it. **I wrote it ONCE, as `module GraphEntry`, at
`src/L/Condensation.lagda.md:2731-2771`, the module header at `:2752`** (new), with `bin` and `un`.

**Size: 12 non-blank in-fence lines for the module, 20 premise lines across the
20 declarations, and 11 call-site extensions. No line was deleted.**

## 5. The call sites supply it (C-38, the half that decides)

**Every row's `back` ALREADY BINDS the graph entry**, under the name `hc`, in the
same argument position in both frames. It was bound and thrown away. **MEASURED**
at these 11 sites (current line numbers), each of which now reads
`... c∈ shEq (GraphEntry.bin {m} T γ c ar a b yc hc)` or the `un` form:

| current line | module | binder that supplies it |
|---:|---|---|
| 2803 | `BotAgree.bot-in` | `λ c c∈ ar a yc shD hc →` at `:2798` |
| 3505 | `PropAgree.back` | `λ c c∈ ar a b yc shD hc ya yb hya hyb →` at `:3500` |
| 3708 | `TopAgree.back` | `λ c c∈ ar a yc shD hc E hE →` |
| 3791 | `NegAgree.back` | `λ c c∈ ar a yc shD hc ya E hya hE →` |
| 3907 | `ForallAgree.back` | `λ c c∈ ar a yc shD hc ya E hya hE →` |
| 4079 | `ExistAgree.back` | `λ c c∈ ar a yc shD hc ya E hya hE →` |
| 4445 | `MemAgree.back` | `λ c c∈ ar a b yc shD hc E hE →` |
| 5058 | `AllInAgree.back` | `λ c c∈ ar a b yc shD hc yb E hb hE →` |
| 5179 | `ExInAgree.back` | `λ c c∈ ar a b yc shD hc yb E hb hE →` |
| 5278 | `ImpAgree.back` | `λ c c∈ ar a b yc shD hc ya yb E ha hb hE →` |
| 5371 | `EqAgree.back` | `λ c c∈ ar a b yc shD hc E hE →` |

**The three pass-through rows need no call-site change**: `AndAgree`, `OrAgree`
and `ClauseAgree` hand their own `valK` to `PropAgree` or `ExistAgree`, and both
sides gained the same premise.

**The frames need no call-site change either.** `LowerAgree` and `UpperAgree`
apply `(valK k)` partially (`src/L/Condensation/LowerAgree.lagda.md:212`), and
the new premise is at the END, so partial application is untouched. **MEASURED**
by the green typecheck.

**So the repair is a SUPPLY and not C-38's restatement.** Nothing new has to be
proved anywhere for the rows to keep working: the fact was already in scope.

## 6. Consumer verdicts (C-40). ALL GREEN

One agda process, `GHCRTS="-A64m -I0 -M8g"`, cap never raised.

| master | verdict | real s | load at start |
|---|---|---:|---:|
| `agents/tasks/LJ-1-153/ProbeLJ1153A.agda` | **exit 0** | 1.10 | 6.10 |
| `src/L/Condensation.lagda.md` | **exit 0** | 129.83 | 4.26 |
| `src/L/Condensation/TwelveAgree.lagda.md` | **exit 0** | 61.32 | (with the two below) |
| `src/L/Condensation/LowerAgree.lagda.md` | **exit 0** | in the run above | |
| `src/L/Condensation/UpperAgree.lagda.md` | **exit 0** | in the run above | |
| `src/L/BoundedSubset.lagda.md` | **exit 0** | 16.78 | 19.64 |

**No unsolved metavariable, no warning of any kind.** Each log holds only its
`Checking` lines. I-5 holds.

**The consumer list is complete. MEASURED**: `grep -rln "L.Condensation" src/`
returns exactly the four masters above plus `src/Everything.lagda.md` (never
touched, the orchestrator's) and `src/L/Condensation/README.md` (prose).
`L.BoundedSubset` imports only `DefBodyB`, `Δ₀-DefBodyB` and `module GraphB`
(`src/L/BoundedSubset.lagda.md:29-32`), none of which I edited, and it is green
anyway.

**THE MACHINE WAS BUSY THROUGHOUT.** `[LJ-1.152]` held an agda process
(pid 73169, `agents/tasks/LJ-1-152/ProbeLJ1152*`) for my whole run. Load averages
ran 4.26 to 42.77. **My figures are correctness, so the load cost me time and
nothing else. No second above should be quoted as a price.** C-31, C-32.

**No heap exhaustion, no kill, no wall.**

## 7. The two flags that are NOT refutable (MEASURED)

**A flag is a suspicion. These two are false positives of rule 3, and I say how I
tried.**

### 7.1 `answers`, `src/L/Reflect.lagda.md:365`

```agda
(answers : (n : ℕ) (ms : ⟪ Lset (G n) ⟫ ^ k)
         → ⟨ pickStage ψ (LsetEnv (G n) (G-ord n) ms) ∈ G (suc n) ⟩)
```

Rule 3 fires because the hypothesis has no premise. **But `ms` is not a free
subject: the conclusion's subject is `pickStage ψ (LsetEnv ... ms)`, a FUNCTION
of `ms`.** A refuter cannot choose it, so regularity has nothing to bite on.

**MEASURED, and this is the decisive evidence: the type is INHABITED at a
delivered site.** `src/L/Reflect.lagda.md:488-489` supplies it as
`answers n = pickLand (βₙ n) (βₙ-ord n)`, and `:493` consumes it as
`L.closure ψ answers`. **An empty type cannot be supplied by a green module**,
so `answers` is not refutable. I left it exactly as it stands.

### 7.2 `ih`, `src/L/StageCardinal.lagda.md:281`

```agda
(ih : (m : ⟪ α ⟫) → ⟪ Lset (⟪ α ⟫↪ m) ⟫ ↪ ⟪ α ⟫)
```

**The conclusion holds NO membership at all. It is an injection.** C-38's
refutation shape cannot even be stated against it: there is nothing for
`∈-irrefl` to close. **MEASURED**, by reading the type. `m` occurs in the
conclusion, so it is not free either.

`src/L/StageCardinal.lagda.md:396-403` (`limit-step`) passes `ih` straight
through. **I did NOT trace `limit-step` to a site that BUILDS an `ih`, so I do
not claim inhabitation by supply here.** The structural argument above stands on
its own.

**Neither belongs in the brief's write scope for a repair, and I recommend NO
change to either.** The right cure is a checker refinement: rule 3 should not
fire when every telescope-bound set variable occurs inside an APPLIED position of
the conclusion's subject. That is a `scripts/check-unbound-hyp.py` change, and it
is the orchestrator's call.

## 8. What I did NOT repair, and exactly how to finish it

**The 16 rule-2 flags are REFUTED and UNREPAIRED.** I was about to edit them when
the checkpoint order arrived. I had read every site and settled the repair; I had
written NO character of it. Section 10 carries the plan at full detail.

**This is not a C-38 stop.** I did not find a site that cannot supply the repair.
I ran out of time.

## 9. DD4

**Every line I wrote is TEMPLATE content. It names no tower.**

| block | in-fence lines | tower |
|---|---:|---|
| `module GraphEntry`, `bin` and `un` | 12 | **SHARED.** It names `appAt`, `pr` and the carrier. No `Lset`, no `Sset`, no `J` |
| the 20 premise lines | 20 | **SHARED.** Slot arithmetic and the pair encoding |
| the 11 call-site extensions | 0 new lines | **SHARED** |

**So this confirms `[LJ-1.151]` section 6 and extends it.** That report measured
19 of 21 lines naming no tower and corrected `[LJ-1.146]` section 6, which had
put the instantiation on the per-tower side. **My 32 lines are 32 of 32.** The
repaired STATEMENT is template content in full; only its eventual SUPPLY at a
concrete `K` carries the two per-tower lines `[LJ-1.151]` measured.

**One measurement that sharpens it.** `GraphEntry` is written once and used at 11
row sites. Written per row it would have cost about 11 copies of a 4-line
transport. **The saving is real and it is the DD4 shape: one generic module, 12
lines, against 44 written fixed.** P-w's module-application caution does not bite
here, because `GraphEntry` sits at the TOP LEVEL and the rows apply it as a
qualified name rather than copying its body, which is the same choice
`src/L/Condensation/TwelveAgree.lagda.md:68-72` records for `sixes→twelve`.

**No stop-line pushed me toward writing fixed.**

## 10. HANDOVER: what a successor needs and only I know

### 10.1 State of the tree

**SAFE STATE, option one: every master I edited typechecks.** I did not revert.
Verified at section 6, five masters, exit 0 each, after the last edit.

Files I changed:

- `src/L/Condensation.lagda.md`: `GraphEntry` inserted at `:2731-2771`, its module header at `:2752`; 14 `valK`
  premise lines; 11 call-site extensions. 26 diff hunks, **all mine**
  (`git diff -U0 | grep -c "^@@"` = 26).
- `src/L/Condensation/LowerAgree.lagda.md`: 2 insertions.
- `src/L/Condensation/UpperAgree.lagda.md`: 2 insertions.
- `src/L/Condensation/TwelveAgree.lagda.md`: 2 insertions.
- `agents/tasks/LJ-1-153/ProbeLJ1153A.agda`: new, tracked location, never
  deleted.
- `agents/tasks/LJ-1-153/lj-1.153-report.md`: this file.

**Nothing else. `src/Everything.lagda.md` never opened.
`src/L/Coding/Graph.lagda.md` read only, never written.
`src/ProbeLJ1134A.agda` and `src/ProbeLJ1136*.agda` untouched. No commit, no
push, no `git checkout`, `stash`, `reset` or `clean`.**

### 10.2 THE MISTAKE I MADE, so nobody pays for it twice

**I clobbered 14 shape premises with an off-by-one and had to restore them.**

I wrote a Python edit that read the conclusion at `L[n+1]` (0-based, so line
`n+2`) but wrote back to `L[(n+1)-1]` (line `n+1`, the SHAPE line). Every row
lost `→ fst c ≡ pr (fst ar) (pr (# k) ...)` and gained a duplicated conclusion.

The symptom was a **ParseError**, not a type error:

```
src/L/Condensation.lagda.md:2785.10: error: [ParseError]
→<ERROR>  ⟨ fst yc ∈ fst (lookup K γ) ⟩...
```

**I restored the 14 lines from `git show HEAD:src/L/Condensation.lagda.md`, not
by hand**, matching the two files' `^  (valK :` occurrences in order. Verified by
`git diff -U0 | grep "^-"`, which now shows ONLY the 11 call-site lines as
deleted. **The 14 declaration hunks are pure insertions.**

**The lesson for the next mechanical multi-site edit: assert the text you are
about to overwrite, not only the text you read.** My script asserted the read and
not the write, so it passed its own check while destroying content.

### 10.3 THE REPAIR THAT IS PLANNED AND NOT WRITTEN

**The tie for all 16: the containing set is in `K`.** It is the SAME shape as the
`valK` repair, which is why it is worth doing as one batch.

**Why this tie and not another.** With `w ∈ K` and `K` transitive, `c ∈ w` gives
`c ∈ K`; then `ar ∈ {ar} ∈ pr ar _ = c` gives `ar ∈ K` by two more steps. **That
is exactly `[LJ-1.151]`'s `prK`** (`agents/tasks/LJ-1-151/lj-1.151-report.md:97`).
So one delivered lemma supplies the `valK` family AND all 16 of these.

**A. `WitnessAgree`** (current `:6492`, `:6496`, `:6499`). Insert after the
`(w : S)` / `(w x' y : S)` binder:

```agda
           → ⟨ fst w ∈ fst (lookup K γ) ⟩
```

Call sites: `(codesK w) (unCodesK w) (entryK w)` at `:6518` and `(codesK w)
(unCodesK w)` at `:6523` become `(codesK w wK)` and so on, where

- in `out.go` (`:6509`), `wK = witK w (hxw , (hcl , hsh))`, which the body
  already computes at `:6510`;
- in `back.go` (`:6537` region), `wK` is bound by the pattern
  `go (w , (wK , (hxw , (hcl , hsh))))`. **It is already there and already
  unused.**

`ClosedAgree` and `ShapedAgree` need NO change: they receive `codesK w wK`, whose
type after the two applications is what they already expect, because
`lookup zero (w ∷ γ)` is `w` definitionally.

**B. `SatGraphAgree`** (current `:6754`, `:6759`, `:6763`, `:6769` tie `d`;
`:6766` ties `e`). Insert after the `(d e f : S)` binder:

```agda
           → ⟨ fst d ∈ fst (lookup (suc (suc (suc K))) γ) ⟩
```

and the `e` form for `domEntryK`.

Call sites are the two where-blocks of `body-out` and `body-back`:

- `body-out d e f h`: `h` has EXACTLY `witK`'s premise type (compare `:6769-6775`
  with `:6715-6721` at HEAD), **so `body-out` can compute `ks = witK d e f h`
  itself and use `ks .fst` and `ks .snd .fst`. No signature change.**
- `body-back d e f h`: `h` is the BOUNDED form, so `witK` does not apply.
  **Give `body-back` two extra parameters `dK` and `eK`** and pass them at the
  one call, `back` at HEAD `:6904`, where the patterns
  `(d , (dK , hT))`, `(e , (eK , hb))` and `(f , (fK , body))` ALREADY BIND them
  and already discard them.

**C. `LeafAgree`** (current `:6986`, `:6991`, `:6995` tie `w'`; `:7004`, `:7010`,
`:7015`, `:7021` tie `d`; `:7018` ties `e`). **Pure pass-through: add the same
premises and change nothing else.** It hands these straight to `WitnessAgree`
(HEAD `:6994`) and `SatGraphAgree` (HEAD `:7001`), and the types then match by
construction.

**D. The chain TERMINATES at `LeafAgree`. MEASURED**: `grep -rn "LeafAgree" src/`
returns only its own comment and its own module header. **No consumer breaks, and
there is no fourth level.** `WitnessAgree` and `SatGraphAgree` have no
instantiation outside `LeafAgree`.

**E. Then typecheck `src/L/Condensation.lagda.md` and re-run the checker. It
should read 2, and the 2 are section 7's false positives.**

### 10.4 What I had verified but not yet used

- `appAt-adequate` is already imported into `L.Condensation`
  (`src/L/Condensation.lagda.md:31`), so `GraphEntry` needed no new import. The
  rule-2 repair needs no new import either.
- `sucʟ`, `sucʟ-fst`, `self∈sucV`, `prʟ`, `prʟ-fst`, `numeralL`, `numeralL-fst`
  are the whole toolkit for the unconditional refutations, and they are all
  delivered. See `ProbeLJ1153A.agda:35-38`.
- The probe compiles under the repo's own library file: `bedrock.agda-lib`
  carries `include: src agents/tasks`, so `agda agents/tasks/LJ-1-153/ProbeLJ1153A.agda`
  needs no `-i` flag.

### 10.5 Nothing else failed

**Apart from the off-by-one at 10.2, no experiment failed.** The probe compiled
first try. The valK repair compiled first try after the restoration. I hit no
wall, no heap exhaustion and no conversion blow-up.

## 11. Checkers

- `scripts/check-unbound-hyp.py`: **38 before, 18 after.**
- `scripts/lint-agda.py --check`: **exit 0.**
- `scripts/check-probes.py --check`: **clean**, 1645 tracked files, no probe
  outside `agents/tasks/`.
- `scripts/ledger.py --brief`: standing **28,723 lines over 85 masters**,
  measured from HEAD; thresholds SUSPENDED per the ledger header. **My edit adds
  32 in-fence lines and deletes none.**
- `scripts/lint-prose.py --check`: run at the close of this file.
- **No `make check`.** The orchestrator runs it.

## 12. The rules, answered

- **C-38 as extended.** Section 5 is the whole answer: the graph entry was
  ALREADY BOUND at all 11 row sites, so the repair is a supply and not a
  restatement. Section 8 says plainly which 16 remain unsupplied.
- **C-40.** Section 6. Five masters, not the one I edited.
- **C-36.** I wrote the term I could not write: `GraphEntry.bin` and
  `GraphEntry.un` are the transport nobody had written, and the 20 premises are
  the statement nobody had stated.
- **C-39.** Section 13.
- **C-12.** One agda process, `-M8g`, cap never raised. The sibling's process was
  never touched. Load reported beside every figure.
- **C-22.** This file was a skeleton before I read the archive, and it was
  written in four passes.
- **C-31, C-32.** Section 6 says the seconds are indicative on a busy machine.
- **C-33.** Section 4.1 states the obligation as an obligation.
- **C-34.** Section 10.3 names the remaining cure at full detail, so nothing is
  left named and unpriced.
- **C-35.** I report 20 of 36 repaired, not "the defect is fixed". Section 0 says
  the count in its first four lines.
- **C-37.** Section 7 gives the checker's own limit rather than working around it
  silently.
- **D-1.** The abort criterion was in the brief before I ran and I did not move
  it. I stopped on the coordinator's order, not on my own reading.
- **D-10.** This whole task is D-10: the recorded residue's TARGET was false.
- **D-26.** Section 14 uses the digest's per-step carrier column.
- **D-29, D-30.** I report the narrowing (the rows already bind `hc`) and do NOT
  bank it as a saving anywhere.
- **I-5.** No unsolved meta in any run.
- **P-l.** I did not carry the `valK` measurement onto the rule-2 family by
  analogy. I refuted the rule-2 shapes at their own site, in their own probe
  modules.
- **P-y, P-x.** The repaired premises are telescope facts and I left them as
  telescope facts. I moved nothing into a record.
- **DD8.** One figure per term, each with its basis.
- **DD23.** No mathematical prose written. `GraphEntry` carries code comments,
  which the brief allows.
- **DD4.** Section 9.

## 13. C-39: what a prohibition closed

**"Do not touch `src/L/Coding/Graph.lagda.md`" cost me nothing and it was
right.** I read `twelveAt` there (`:94-100`) to confirm the frames' slot order,
`C = 2`, `T = 1`, `B = 0`. The repair needed the reading and not the file.

**"Do not run `make check`" cost me nothing.** The five targeted runs cover every
consumer, and section 6 proves the coverage by `grep`.

**One brief line DID bind harder than the goal, and I obeyed it.** The brief's
write scope names `src/L/StageCardinal.lagda.md`, so I could have edited `ih`.
**Section 7.2 says I should not, and I did not.** The flag is a checker
imprecision, and editing a sound statement to quiet a checker is exactly the
weakening the brief forbids.

## 14. ARCHIVE USED (DD18)

- **`agents/tasks/LJ-1-151/lj-1.151-report.md`, read WHOLE.** TOOK the
  refutation and its status as a defect rather than a debt (`:22-46`); the
  21-line supply and its parts (`:94-104`); the finding that the proof uses `hc`
  alone and that `C`, `c∈` and `shape` are dead weight (`:151-161`); the DD4
  split, 19 of 21 lines naming no tower (`:288-318`); and **the exact one-line
  fix at `:441-446`, which section 4 applies and section 5 verifies.** That
  report says "The rows already bind that premise, so no consumer breaks.
  INFERRED. I did not run the consumers." **I ran them. It is now MEASURED.**
- **`agents/tasks/LJ-1-151/ProbeLJ1151B.agda`, read WHOLE.** TOOK the refutation
  shape (`:48-58`). My `Refute-val` strengthens it by building the code.
- `agents/tasks/LJ-1-151/LJ-1.151.md`: not read; its content reaches me through
  the report.
- **`scripts/check-unbound-hyp.py`, read WHOLE.** TOOK the three rules and, more
  usefully, **what they do NOT claim** (`:28-32`): a flag is a question. Section
  7 is built on `telescope()` (`:192-210`) and rule 3 (`:296-299`), which is why
  I can say precisely why the two survivors are false positives. TOOK also
  `resolve_lookups` (`:236-269`), which is why the frames' `lookup (suc zero) γ`
  premise reads as a real tie and not as noise.
- `agents/tasks/LJ-1-97/ProbeLJ197A.agda`: **NOT read.** The checker names it as
  the probe shape, and `ProbeLJ1151B.agda` carries the same shape at a site I had
  to read anyway. **I record this as a gap, not as a judgment that it holds
  nothing.**
- `agents/tasks/archive/LJ-1-95/` through `LJ-1-112/`: **NOT read, and this is my
  largest archive gap.** The brief calls the arc the playbook. I took its cure
  shape through `[LJ-1.151]`'s citations and through the delivered comment at
  `src/L/Condensation.lagda.md:2765-2772` (HEAD), which records `[LJ-1.99]`'s
  four-step pair chain and says in the tree itself that **"the untied `entryK` is
  refuted at the abstract frame ([LJ-1.97], ProbeLJ197A); the tied form (premise
  `z ∈ K`) is the honest one".** That comment is the playbook in one sentence and
  it is what section 10.3 follows.
- `agents/tasks/LJ-1-113/lj-1.113-report.md`: **NOT read.** Its content reaches
  me through `[LJ-1.151]` sections 4 and 7 at `file:line`.
- **`dev/LESSONS.md`**: C-12, C-22, D-1, D-10, P-l loaded through
  `scripts/rules.py --for rewrite` and read. C-38, C-36, C-39, C-40, C-35 read
  through the brief and through `[LJ-1.151]:394-430`.
- **`AGENTS.md`, read WHOLE and fresh**, as the brief ordered. My probe obeys the
  new rule: it lives in `agents/tasks/LJ-1-153/`, it is tracked, and it is not
  deleted.
- `src/L/Coding/Model.lagda.md`, read `:160-172`, `:860-940`, `:978-1010`. TOOK
  `appAt-adequate` (`:163-165`), `binClauseAt` and `binClause-out` (`:897-917`),
  `unClauseAt` and `unClause-out` (`:989-1006`), and the slot abbreviations
  `sh5`, `c5`, `yc5`, `sh4`, `c4`, `yc4` (`:886-895`, `:979-987`) that
  `GraphEntry` spells out.
- `src/L/Coding/Graph.lagda.md`, read `:94-100` only. **NOT edited.**
- `src/L/Axioms/Numerals.lagda.md`, read `:95-185`. TOOK `pairʟ`, `sucʟ`
  (`:98-107`), `sucʟ-fst` (`:152`), `numeralL` and `numeralL-fst` (`:175-181`).
- `src/V/Model.lagda.md`, read `:236-237`. TOOK `self∈sucV`, which is the whole
  content of the three unconditional refutations.
- `src/V/Hierarchy.lagda.md`, read `:155`. TOOK `∈-irrefl`.
- `src/L/Reflect.lagda.md`, read `:340-395` and `:470-500`. **NOT edited.**
- `src/L/StageCardinal.lagda.md`, read `:255-325` and `:390-405`. **NOT edited**,
  though the brief's write scope allows it. Section 13.
- `archive/` and `archive/dev/`: **NOT read.** No archived record bears on
  whether a live telescope hypothesis is empty; the live checker and a probe
  settle that.

## 15. LITERATURE USED (DD18)

**`dev/literature/devlin-II5.md`: NOT read in this dispatch, and I say so
plainly rather than citing it second hand.** The checkpoint order arrived first.

**The brief's question — does Devlin's own argument need the free subject at all,
or is it an artifact of our frame — is therefore ANSWERED ONLY IN PART, and the
part I can defend is structural.**

**MEASURED, from the repair itself: the free subject is an ARTIFACT of our
frame.** The evidence is that the repaired premise was ALREADY BOUND at every one
of the 11 row sites, under the name `hc`, and simply not passed on
(section 5). A statement whose missing premise is already in scope at every use
site did not come from the mathematics. It came from writing the telescope
without checking it against the frame that feeds it.

**`[LJ-1.151]` reached the same conclusion from the literature and I take its
citation at `file:line`** (`agents/tasks/LJ-1-151/lj-1.151-report.md:517-532`):
Devlin binds the Def step's quantifiers by one concrete `K(u)` and "does not
require them to have any particular shape"; `dev/literature/devlin-II5.md:375`,
row C2, classes the bounded Def-step matrix as per-tower content and names our
side as "the coding analogue". **So Devlin has no `valK` and no `yc`. He has one
sentence about `K(u)`'s construction, and our twelve rows turn it into a bill of
site facts.** **INFERRED**, because I did not open the digest myself.

---

# RESUMPTION: the sixteen rule-2 repairs, finished

Appended after the restart. `make check` was EXIT 0 on the first twenty
(commit `093a3da`), so this section starts from a green tree.

## R0. Lead

- **`check-unbound-hyp.py`: 18 BEFORE this section, 2 AFTER.**
- **All 16 rule-2 hypotheses repaired. NONE was left unrepaired.**
- **The 2 that remain are `answers` and `ih`**, the checker false positives of
  section 7. They are untouched, as ruled.
- **Across the whole task: 38 to 2. 36 refuted, 36 repaired.**
- **Every consumer green**, exit 0, section R4.

**Nothing walled. No heap exhaustion. `src/L/Condensation.lagda.md` compiled
first try after the edits, and so did every consumer.**

## R1. The repair, stated before and after

**One tie serves all sixteen: THE CONTAINING SET IS IN `K`.** It is the same
shape as the `valK` repair, and for the same reason: with `K` transitive,
`c ∈ w ∈ K` gives `c ∈ K`, and two more steps down the Kuratowski pair give the
components. **That is `[LJ-1.151]`'s `prK`**
(`agents/tasks/LJ-1-151/lj-1.151-report.md:97`). One delivered lemma supplies the
`valK` family and all sixteen of these.

### R1.1 `WitnessAgree`, 3 hypotheses

**Before** (`src/L/Condensation.lagda.md` at `093a3da:6492`):

```agda
  (codesK : (w : S) → (k : ℕ) → (c ar a b : S) → ⟨ fst c ∈ fst w ⟩
           → fst c ≡ pr (fst ar) (pr (# k) (pr (fst a) (fst b)))
           → ⟨ fst ar ∈ fst (lookup K γ) ⟩ × ... )
```

**After** (now `:6500`):

```agda
  (codesK : (w : S) → ⟨ fst w ∈ fst (lookup K γ) ⟩
           → (k : ℕ) → (c ar a b : S) → ⟨ fst c ∈ fst w ⟩
           → fst c ≡ pr (fst ar) (pr (# k) (pr (fst a) (fst b)))
           → ⟨ fst ar ∈ fst (lookup K γ) ⟩ × ... )
```

`unCodesK` takes the same premise. `entryK` takes it too, and its binder group
`(w x' y : S)` had to SPLIT into `(w : S) → ⟨ ... ⟩ → (x' y : S)`, because the
tie has to sit between `w` and the rest.

**The premise that now constrains `w`: `w ∈ K`.** Untied, `w` was any set at all.

### R1.2 `SatGraphAgree`, 5 hypotheses

`codesK`, `unCodesK`, `closedEntryK` and `domK` take
`⟨ fst d ∈ fst (lookup (suc (suc (suc K))) γ) ⟩`, the CLAUSE SET in `K`.
`domEntryK` takes the `e` form, the GRAPH in `K`, because its premise reads the
`e` slot and not the `d` slot. **I checked that slot by slot rather than tying
all five to `d`**: `domEntryK`'s premise is at
`lookup (suc zero) (f ∷ e ∷ d ∷ γ)`, which is `e`.

### R1.3 `LeafAgree`, 8 hypotheses

**Pure pass-through, no proof content.** The `w*` group takes the `w' ∈ K` form
for `WitnessAgree`; the `g*` group, `domEntryK` and `domK` take the `d ∈ K` or
`e ∈ K` form for `SatGraphAgree`. The two module applications
(`:7093`, `:7105`) needed NO change: the types line up by construction.

### R1.4 This does not weaken the statements

**Each repaired hypothesis keeps its whole conclusion.** `codesK` still says
every code in the set has its three components in `K`; `entryK` still says both
sides of every recorded pair are in `K`; `domK` still says every member is in
`K`. **What changed is that the set is no longer arbitrary.**

**And no theorem changed what it SAYS.** All sixteen are module HYPOTHESES.
**MEASURED**: `git diff` deletes 32 lines and every one is a line I replaced in
place; **no `out`, `back`, `body-out` or `body-back` CONCLUSION type was
touched.** The single signature change is `body-back`, which gained two
arguments and lost nothing.

## R2. The call sites supply it (C-38, the deciding half)

**Every site already held the tie and threw it away. That is the same finding as
the first twenty, and it is why this repair is a supply and not a restatement.**

| site | `file:line` | what supplies the tie |
|---|---|---|
| `WitnessAgree.out.go` | `:6524-6525`, used at `:6531` | `witK w (hxw , (hcl , hsh))`. **The body already computed this at `093a3da:6510` and used it only for the output pair.** I named it `wK` and passed it |
| `WitnessAgree.back.go` | `:6550`, used at `:6559` | `wK`, **bound by the pattern `go (w , (wK , ...))` and UNUSED before this repair** |
| `SatGraphAgree.body-out` | `:6885-6887` | `witK d e f h`. **`h` IS `witK`'s premise, at the same environment**, so the direction supplies both ties from what it holds. No signature change |
| `SatGraphAgree.body-back` | `:6913-6915`, called at `:6999` | two new arguments, **bound and discarded by the three patterns `(d , (dK , hT))`, `(e , (eK , hb))`, `(f , (fK , body))`** |
| `LeafAgree` | `:7093`, `:7105` | nothing: it is a pass-through and holds no proof |

**So no site needed a new fact.** The strongest single measurement in this
section: **`WitnessAgree.back` had `wK` bound by its own pattern and never used
it.** The checker was pointing at a premise the code had in its hand.

## R3. The chain terminates, so no consumer can break

**MEASURED**: `grep -rn "LeafAgree" src/` returns only its own comment banner and
its own module header. **`WitnessAgree` and `SatGraphAgree` have no
instantiation outside `LeafAgree`.** There is no fourth level and no orphaned
obligation created by this repair.

**This does NOT discharge anything, and I say so plainly (C-38).** `KFacts` still
has no instance in `src/`, exactly as `[LJ-1.151]` section 3 measured. My repair
makes sixteen empty types inhabitable; it does not inhabit them.

## R4. Consumer verdicts (C-40). ALL GREEN

One agda process, `GHCRTS="-A64m -I0 -M8g"`, cap never raised.

| master | verdict | real s | load at start |
|---|---|---:|---:|
| `src/L/Condensation.lagda.md` | **exit 0** | 124.41 | 5.94 |
| `src/L/Condensation/TwelveAgree.lagda.md` | **exit 0** | 58.68 | 5.20 |
| `src/L/Condensation/LowerAgree.lagda.md` | **exit 0** | in the run above | |
| `src/L/Condensation/UpperAgree.lagda.md` | **exit 0** | in the run above | |
| `src/L/BoundedSubset.lagda.md` | **exit 0** | 16.35 | 5.42 |

**No unsolved metavariable and no warning.** Each log holds only its `Checking`
lines. I-5 holds.

**The machine was QUIET for this section**, load 5.20 to 5.94, one user. **I did
not see `[LJ-1.154]` take a process while I ran.** The seconds above are
therefore comparable with each other, but I still do not offer them as a price:
they are a repair's incidental cost, not a measured term (C-31).

## R5. Checkers

- `scripts/check-unbound-hyp.py`: **18 before, 2 after.**
  **Whole task: 38 before, 2 after.**
- `scripts/lint-agda.py --check`: **exit 0.**
- `scripts/check-probes.py --check`: **clean**, 1654 tracked files.
- `scripts/lint-prose.py --check` on this report: exit 0.
- **No `make check`.** The orchestrator runs it.

## R6. The diff, audited line by line

**32 lines deleted, and every one is a line I replaced in place.** I read the
whole deletion list rather than trusting the count, because section 10.2 is my
own lesson. **Nothing was lost.** The blank line before `body-back` is the only
non-declaration deletion, and a comment banner replaced it.

| figure | value |
|---|---:|
| lines added | 82 |
| of which in-fence code | 54 |
| of which code comments | 28 |
| lines removed, all replaced in place | 32 |
| **net in-fence code** | **+23** |

**I applied my own 10.2 lesson.** The one scripted multi-site edit in this
section asserts BOTH the string it matches AND the string it writes, and asserts
the match count is exactly 1 per site. The two-site edit asserts the count is
exactly 2, which is what proves it hit `body-out` and `body-back` and not one of
them twice. **Every other edit was one site at a time.**

## R7. DD4

**All 23 net in-fence lines are TEMPLATE content. They name no tower.**

Every line added is a membership premise at a slot, or one `let`-level binding of
a fact the site already held. **No `Lset`, no `Sset`, no `J`, no `π`.** A J tower
re-pays none of it.

**The DD4 reading now covers the whole task, and it is one figure: 55 net
in-fence lines added, 55 of them shared.** That is 32 from the `valK` half and 23
from this half.

**This strengthens `[LJ-1.151]` section 6, which corrected `[LJ-1.146]` section
6.** That report measured 19 of 21 lines naming no tower and called the
instantiation mostly template. **The repaired STATEMENTS are 100 percent
template.** The per-tower part is only the eventual SUPPLY at a concrete `K`,
which `[LJ-1.151]` measured at two lines.

## R8. What I could NOT repair

**Nothing in the sixteen. Every one is repaired and every consumer is green.**

**Two flags remain and neither is a defect. MEASURED, section 7:**

- `src/L/Reflect.lagda.md:365` (`answers`): the conclusion's subject is a
  FUNCTION of the flagged variable, and the type is INHABITED at a delivered site
  (`src/L/Reflect.lagda.md:488-489`). **An empty type cannot be supplied by a
  green module.**
- `src/L/StageCardinal.lagda.md:281` (`ih`): the conclusion holds NO membership,
  so C-38's refutation cannot even be stated against it.

**Both untouched, as ruled. The right cure is a `check-unbound-hyp.py` rule-3
refinement and it is the owner's call.**

## R9. One thing the orchestrator should decide

**`scripts/check-unbound-hyp.py` now has exactly two flags, and both are false
positives.** Until rule 3 is refined, the checker cannot be armed with `--check`
in `make check`: it would fail closed on two sound statements.

**The refinement I recommend, stated so it can be priced:** rule 3 should not
fire when every telescope-bound set variable occurs inside an APPLIED position of
the conclusion's subject, rather than as the subject itself. That distinguishes
`pickStage ψ (LsetEnv ... ms)` from a bare `yc`. **I did not write it, and I did
not measure what else it would silence.** `[LJ-1.153]` is not the dispatch that
owns that file.

## R10. ARCHIVE USED, addendum

- **`src/L/Condensation.lagda.md`, read `:6360-6372` (`ClosedAgree`),
  `:6422-6425` (`DomainAgree`).** TOOK their `codesK`, `entryK` and `domK`
  parameter types, which are stated at a SLOT (`lookup C γ`, `lookup f γ`,
  `lookup d γ`) and therefore needed NO change. **That reading is what made the
  repair a one-level edit**: applying the extra argument leaves exactly the type
  those two modules already expect, because `lookup zero (w ∷ γ)` reduces to `w`.
- `src/L/Condensation.lagda.md:2765-2772` (HEAD numbering), read again. **It is
  the playbook in one sentence** and this section follows it to the letter:
  "the untied `entryK` is refuted at the abstract frame ([LJ-1.97],
  ProbeLJ197A); the tied form (premise `z ∈ K`) is the honest one, supplied by
  arityK."
- **`agents/tasks/archive/LJ-1-95/` through `LJ-1-112/`: still NOT read.** The
  gap I declared in section 14 stands. **I did not need it**: the delivered
  comment above carries the cure shape, and my own sixteen refutations priced the
  defect directly. I record this so nobody reads my green result as evidence that
  the arc holds nothing.
