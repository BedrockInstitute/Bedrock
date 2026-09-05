# LJ-1.50 review (DD25): the 150-second transfer and the exit that was not built

Status: COMPLETE. Written incrementally per C-22. ASD-STE100.
No master edited. No commit. No push.
Probes are `src/ProbeDD25H1.agda` to `src/ProbeDD25H8.agda`, plus
the negative control `src/ProbeDD25H2N.agda`.

## 1. THE VERDICT

**OVERTURN.** The return's central number does not measure the
obligation. It measures its own probe's spelling.

The same `erase-Δ₀` call, on the same `DefBodyB` leaf, with the same
certificate, costs **220 ms** when the count proof is a NAMED
definition. The return's control costs **150,133 ms** for it, because
that probe writes `refl` inline twice.

| probe | the count proof | `transfer-concrete`, profiled |
|---|---|---:|
| `src/ProbeLJ150Control.agda:39-40`, the return's control | inline `refl`, twice | **150,133 ms** |
| `src/ProbeDD25H3.agda:44-49`, the same call | `count-defb`, named | **220 ms** (213 / 224 / 224) |

`src/ProbeDD25H3.agda` is `src/ProbeLJ150Control.agda` with ONE change:
the count proof has a name. Nothing else moves. The factor is **681**.

**The full matrix, which the return could not finish, finishes.**
`src/ProbeDD25H7.agda` is the same obligation at
`LevelHood0.matrix` with the count proof named: **811 ms**
(787 / 851 / 795), whole probe 3.08 s. The return reports two
interrupted attempts at about 570 s and about 520 s and no number.

**And the exit the return declined to build is built and green.**
`src/ProbeDD25H2.agda` instantiates the delivered `EraseTransfer`
template at that same leaf, with all five fields named and typed. It
checks in **1.56 s user**, the transfer itself is below the profiler's
reporting threshold, and it never calls `erase-Δ₀`.

**The classification the retrospective asks for: this negative rests on
an INFERENCE.** The return's measurements are sound and its method is
careful. Its ATTRIBUTION is not measured: it took one lump and assigned
it to the structural recursion of `erase-Δ₀`. That step was never
tested, and it is wrong.

**What I UPHOLD.** The return's directional finding about the brief's
cure survives at the corrected spelling. Variable slots are still
slower than the concrete leaf: 327 ms against 220 ms (section 3.4).
The return was right that P-u's slot action does not help. It was
wrong about why, and wrong by a factor of about 500 about how much.

## 2. THE `EraseTransfer` EXIT: BUILT

### 2.1 What was built

`src/ProbeDD25H2.agda` applies the delivered template `EraseTransfer`
(`src/L/Condensation.lagda.md:273-294`) to the `DefBodyB` leaf at
`n = 0`, all sixteen slots at zero. That is the same object the
return's control measures (`src/ProbeLJ150Control.agda:28-36`).

It is the shape of the delivered `RowTransfer`
(`src/L/Condensation.lagda.md:1772-1783`), which already applies the
same template to the twelve rows and is green in the tree. Every field
carries an explicit type, so nothing is left unforced:

```agda
module LeafTransfer (γ : S ^ 8) where
  module E = EraseTransfer defb count-defb Δ₀-defb γ
  σL : Formula S 8                                     -- E.σL
  σL≡ : σL ≡ defb                                      -- E.σL≡
  σL-eq : ⟨ γ ⊨ defb ⟩ ≡ ⟨ γ ⊨ σL ⟩                    -- E.σL-eq
  σL-transfer : ⟨ γ ⊨ σL ⟩ ≡ ⟨ map fst γ ⊨ᵛ σL ⟩       -- E.σL-transfer
  σL-up : ⟨ γ ⊨ σL ⟩ → ⟨ map fst γ ⊨ᵛ σL ⟩             -- E.σL-up
```

**1.62 / 1.53 / 1.54 s user**, mean **1.56 s**, spread 0.09 s
(5.8 percent). Agda's attribution reports only
`ProbeDD25H2.count-defb` at 53 to 55 ms. `LeafTransfer` sits below the
reporting threshold.

**A negative control shows the module is not vacuous.**
`src/ProbeDD25H2N.agda` is H2 with `σL-up` stated in the WRONG
direction. Agda rejects it at `:73` with `[UnequalTerms]`. So Agda does
check each field's declared type against its body, and H2's green is a
real green.

### 2.2 The answer to the review's precise question

**YES.** The connector can obtain what it needs without ever running
the erase-to-Δ₀ recursion, and the reason is structural, not lucky.

`EraseTransfer` keeps the certificate on the ORIGINAL formula and
crosses by two syntactic congs around one `abs₀`
(`src/L/Condensation.lagda.md:287-291`). And `abs₀` recurses on the Δ₀
**WITNESS**, not on the formula
(`src/FOL/Absoluteness.lagda.md:122-127`). A witness passed as an
argument is never reduced during elaboration: its type comes from the
signature.

### 2.3 The delivered architecture already answers this

Three machine-checked facts, each with its site:

1. **`erase-Δ₀` (`src/L/BoundedSubset.lagda.md:505-518`) is the only
   declaration in the tree that manufactures a Levy certificate on an
   erased formula, and it has ZERO use sites in every master.**
   `_build/lj-1.7-review.md:218-220` recorded that fact already.
2. **The one live site that demands `Δ₀` at the erased constant type is
   `src/L/BoundedSubset.lagda.md:608`**, through
   `module D0 = Δ₀Small {K = ⊥* ...}` (`:572`). It consumes
   `Δ₀-isOrdAt` (`:480`) on `isOrdAt` (`:475-478`), a two-clause
   formula **WRITTEN DIRECTLY** at `⊥*`. Nothing there crosses
   `erase`.
3. **Nothing forces the erased spelling.** `Δ₀Small` is generic in the
   constant type (`src/V/Smallness.lagda.md:248-252`), and
   `separateFromSmall` (`:207-209`) takes no formula at all, only a
   predicate plus pointwise smallness.

**So the tree's own pattern for a parameter-free Δ₀ obligation is:
write the formula at `⊥*`, or keep the certificate on the original and
cross semantically. It is never: push a certificate through `erase`.**

### 2.4 Why the exit is cheap BY CONSTRUCTION

Agda checks a parameterized module's body ONCE, at the abstract
parameters. A module application then makes definitions that APPLY the
checked ones; it does not re-check the bodies. `EraseTransfer`'s body
was already paid for inside `L.Condensation` at abstract `φ`, so every
instantiation is close to free.

That is the same reason the twelve delivered rows are affordable, and
it is P-u's action stated as engineering: certify at the abstract
form, instantiate once.

### 2.5 THE FULL MATRIX

`[LJ-1.50]` section 3 reports two interrupted attempts on
`LevelHood0.matrix`, and concludes that "a recursion that costs 150 s
on one leaf cannot finish the matrix inside any budget that fits the
wing".

Two independent measurements refute that.

- **On the `erase-Δ₀` route with the count proof named**
  (`src/ProbeDD25H7.agda`): `transfer-matrix` costs **787 / 851 /
  795 ms**, mean 811 ms, spread 64 ms (7.9 percent). Whole probe 3.04 /
  3.08 / 3.11 s user.
- **On the `EraseTransfer` route** (`src/ProbeDD25H5.agda` part 1):
  `MatrixTransfer` does not appear in Agda's attribution in any of
  three runs. It is below the reporting threshold. Its count proof
  costs 197 / 203 / 210 ms.

### 2.6 The statement level, and a caution about MY OWN first spelling

The adequacy connector moves a Σ₁ statement, not a Δ₀ one. There is no
`erase-Σ₁` in the tree, and none is needed: `σ₁-up`
(`src/FOL/Absoluteness.lagda.md:182-185`) also recurses on the WITNESS
and bottoms out at `abs₀` on the original formula. The delivered
`CertTransfer` (`src/L/Condensation.lagda.md:398-400`) already takes
that route for the clause's Σ₁ certificate.

**My first spelling was bad and I report its number.**
`src/ProbeDD25H5.agda` part 2 writes the Σ₁ transfer DIRECTLY at the
concrete `LevelHood0.Σ₂`. `StmtTransfer.σL-up` costs **129,422 /
127,627 / 128,270 ms**. That is P-t's class exactly, and it is my
error, not the return's.

**`src/ProbeDD25H8.agda` states the same mathematics as a TEMPLATE**,
with the formula abstract, then instantiates once:

```agda
module EraseTransferΣ₁ {m : ℕ} (φ : Formula S m) (p : countFo φ ≡ 0)
                        (s : Σ₁ φ) (γ : S ^ m) where
  ...
  σL-up : ⟨ γ ⊨ σL ⟩ → ⟨ map fst γ ⊨ᵛ σL ⟩
  σL-up h = transport σL-eqᵛ (AbsL.σ₁-up s γ (transport (sym σL-eq) h))
```

**2.89 / 2.83 / 2.76 s user**, mean 2.83 s. `EraseTransferΣ₁` and its
instantiation `StmtTransfer` are both below the profiler's threshold;
only `count-Σ₂` shows, at 202 to 208 ms. **129 s becomes unmeasurable,
by stating the transfer at the abstract formula.**

That module is DD4 content: it mentions no L syntax, so the J tower
instantiates it exactly as the L tower does. It is the template
`L.Condensation` is missing, and I recommend the connector build
place it beside `EraseTransfer`.

## 3. IS THE 150 s REALLY UNAVOIDABLE

**No, and it is not even the obligation's cost.** It is an artefact of
how the probe spells one proof.

### 3.1 The isolation

`src/ProbeDD25H3.agda` differs from `src/ProbeLJ150Control.agda` in one
respect. The control writes:

```agda
transfer-concrete : Δ₀ (Cnt.erase defb refl)
transfer-concrete = erase-Δ₀ defb refl Δ₀-defb
```

H3 writes:

```agda
count-defb : countFo defb ≡ 0
count-defb = refl

transfer-concrete : Δ₀ (Cnt.erase defb count-defb)
transfer-concrete = erase-Δ₀ defb count-defb Δ₀-defb
```

The formula, the certificate, the imports and the function are
identical. 150,133 ms becomes 220 ms.

### 3.2 The mechanism, MEASURED

The control elaborates `refl` TWICE, once in the declaration's type
and once in its body. Agda must then decide whether
`Cnt.erase defb refl₁` and `Cnt.erase defb refl₂` are the same
formula. The two elaborations need not produce the same term, so the
conversion checker unfolds `Cnt.erase` and runs the erasure over the
whole built tree. With ONE named proof both sides are literally the
same term, the check is syntactic, and no unfolding happens.

**`src/ProbeDD25H4.agda` confirms this.** It names the proof in the
TYPE and writes `refl` in the BODY. One spelling difference, nothing
else:

| probe | type | body | `transfer-concrete` |
|---|---|---|---:|
| `ProbeDD25H3` | `count-defb` | `count-defb` | **220 ms** |
| `ProbeDD25H4` | `count-defb` | `refl` | **151,402 ms** |
| `ProbeLJ150Control` | `refl` | `refl` | **150,133 ms** |

**One spelling difference is the whole 150 s.** The recursion of
`erase-Δ₀` is not involved: H3 runs the same recursion for 220 ms.

### 3.2a THIS IS P-v, ONE LEVEL DOWN

P-v (`dev/LESSONS.md:3037-3062`) says: "the type names the same built
construction TWICE, in two spellings, and the elaborator pays to
reconcile them at every use." P-v's measured factor is 499. This one
is 681.

**The new content is WHERE the second spelling hides.** P-v was
written about two names for one FORMULA. Here both sites write the
same formula `Cnt.erase defb ...`, and the second spelling is in a
PROOF ARGUMENT. An inline `refl` is a spelling. See section 6.

### 3.3 What this does to the return's table

**Every row of the return's table shares the defect.**
`src/ProbeLJ150Slots.agda:37-42`, `src/ProbeLJ150Linear.agda:66`,
`src/ProbeLJ150MatrixSlots.agda:37` and
`src/ProbeLJ150MatrixControl.agda:34` all write `refl` inline. So:

- The control at 150.74 s measures the artefact.
- The variable-slot probe at 167.64 s measures the artefact again.
- **The 17 s gap between them is a gap between two artefacts.** It
  cannot carry the conclusion "the cost follows the formula's CLASS,
  not the slot spelling", because neither figure measures the class.
- The profile line `EraseLeaf.transfer 166,571 ms` is real, and the
  return read it correctly as "the module body holds the cost". It
  then inferred WHICH part of the body, and that inference is the
  error.
- The two matrix attempts were interrupted while checking the
  artefact, not the obligation.

### 3.4 The slot comparison, redone honestly

`src/ProbeDD25H6.agda` is the return's variable-slot probe with the
count proof named. Now the comparison isolates the slot spelling and
nothing else:

| spelling | module body | instantiation | total |
|---|---:|---:|---:|
| concrete leaf (H3) | 220 ms | n/a | **220 ms** |
| variable slots (H6) | 216 ms | 111 ms | **327 ms** |

**The return's direction is right.** Variable slots cost about
1.5 times the concrete leaf, because the instantiation is no longer
free once the body is cheap. The return measured 1.11 times on the
artefact. **P-u's slot action does not help, and I do not re-open
that.** The magnitude is 327 ms against 150 s.

## 4. DID THE BRIEF CAUSE IT

**Partly yes, and the part it caused is a road P-t had already
closed.**

### 4.1 The brief prescribed an action P-u does not prescribe

The brief says (`_build/briefs/LJ-1.50.md:39-43`):

> **P-u: CERTIFY BEFORE YOU PLACE.** The move is to build the
> certificate at VARIABLE SLOTS and instantiate ONCE at the end.

P-u's own text prescribes a different action
(`dev/LESSONS.md:2908-2940`):

> So certify the formula BEFORE you place it, then **compose the
> absoluteness through the unplaced form.**
> ... **The route out is upstream: a formula with NO constants reaches
> the parameter-free axis through the delivered `erase` with no
> placement anywhere.**

"Compose the absoluteness through the unplaced form" IS
`EraseTransfer`. **P-u already names the exit that the return then
called a design decision.** The brief replaced that action with a
slot-spelling action and attributed the substitute to P-u.

### 4.2 P-t says the substitute cannot work, and says why

P-t (`dev/LESSONS.md:2601-2630`) states that the class "is not whether
the carrier is concrete or variable", and records that the campaign
"spent two days reading 0.297 as 'the carrier is concrete, so this is
instantiation content', and looked for a cure by moving to a variable
carrier". The brief made that same move a third time, and quoted the
return's phrase "instantiation-class cost"
(`_build/briefs/LJ-1.50.md:41-43`) as its warrant.

So the brief spent the dispatch's budget on the one axis its own
rulebook says does not decide the cost. The agent measured it
correctly and reported that it does not help. **That part of the
return is right and I uphold it.**

### 4.3 What the brief did NOT cause

The brief did not cause the inline-`refl` artefact. That spelling was
inherited from the earlier probe and copied into all five of the
return's probes.

The brief also warned correctly. It cited C-34 by name at
`_build/briefs/LJ-1.50.md:55`: "build the cure or report the wall that
stopped you." The return named a cure inside its own verdict paragraph
and deferred it anyway. **That is C-34's exact failure mode for the
third time in this phase**, after `[LJ-1.33]` and `[LJ-1.34]`.

### 4.4 The consequence for the second task

The brief's stop rule was: do not price `levelIn`'s
collapse-of-the-level step if the 150 s stands. It does not stand, so
that price is now owed and nobody has it.

## 5. THE ROUTE FITS: THE PREMISE OF SECTION 5 FAILS

The brief asks what the alternatives cost IF the route does not fit.
**The premise does not hold, so I do not price alternatives.**

The return's arithmetic was: one piece at 150 to 172 s against a whole
wing budget of 99.6 to 147.7 s (`dev/ledger.toml:305`, which I read and
confirm), therefore the route cannot fit. I re-derived the DD24 bar
myself: 0.011057 (`dev/ledger.toml:2590`) times 1.15
(`dev/ledger.toml:2810`) is 0.012716. The brief's figure is right.

The corrected pieces, all profiled, all three runs:

| the piece | the return's figure | measured here |
|---|---:|---:|
| certificate transfer at the `DefBodyB` leaf | 150.74 s | **0.220 s** |
| the same at variable slots | 167.64 s | **0.327 s** |
| the full `LevelHood0.matrix` | did not finish | **0.811 s** |
| the leaf on the `EraseTransfer` route | not measured | **below threshold** |
| the matrix on the `EraseTransfer` route | not measured | **below threshold** |
| the Σ₁ statement as a template | not measured | **below threshold** |

Against a 99.6 to 147.7 s budget, these are noise. **No piece measured
in this review exceeds one second.**

**One thing the route still owes.** The brief's second task, the price
of the collapse-of-the-level step for `levelIn`, is unpriced. The
return skipped it under the brief's own stop rule, and that rule's
condition has now failed. That price is the next real question, and
this review does not answer it.

## 6. AN EXTENSION TO P-v THAT I PROPOSE, with its measurement

I do not assign the ID; the orchestrator does. **I propose this as a
new paragraph inside P-v, not as a new law**, because the mechanism is
P-v's own and a second entry would split one rule across two homes.

**The statement to add.** The second spelling does not have to be a
second NAME for the formula. **It can hide in a PROOF ARGUMENT.** A
proof written inline at two sites is two elaborations. When that proof
is an argument of a transparent recursion, such as the count proof of
`Cnt.erase`, deciding that the two elaborations agree unfolds the
whole built tree.

**The action.** **Bind the proof to a NAME and use the name at every
site, starting with the declaration's own type.** Never write `refl`
inline as an argument that appears in both a declaration's type and
its body.

**The measurement, 2026-08-11, this review.** Three probes, one
object, one caliber:

| probe | type | body | `transfer-concrete` |
|---|---|---|---:|
| `src/ProbeDD25H3.agda:44-49` | `count-defb` | `count-defb` | **213 / 224 / 224 ms** |
| `src/ProbeDD25H4.agda:47-49` | `count-defb` | `refl` | **151,402 ms** |
| `src/ProbeLJ150Control.agda:39-40` | `refl` | `refl` | **150,133 ms** |

**A factor of 681, from one spelling.** The same change at the matrix
(`src/ProbeDD25H7.agda`) turns two interrupted runs into 811 ms.

**Why it deserves the paragraph.** It is not a rate or a style point.
It turned a correct measurement into a wrong verdict, and that verdict
would have stopped the phase. It is also cheap to enforce: a linter can
find a `refl` in an argument position when the same argument position
in the declaration's own type is spelled otherwise.

## 7. WHAT I AM NOT SURE OF

1. **The micro-mechanism is now measured, but only at ONE site.**
   `src/ProbeDD25H4.agda` isolates it: same proof named in the type,
   `refl` in the body, 151,402 ms. I have not tested whether every
   transparent recursion with a proof argument behaves this way. The
   verdict does not depend on the generality.
2. **The connector is still not built.** I show that the delivered tree
   consumes Levy certificates only at the ORIGINAL formula, and that
   `erase-Δ₀` has zero consumers. I have NOT proved that no future step
   will want `Δ₀ (Cnt.erase φ p)`. I do not need to: if one does, it
   costs 0.220 s at the leaf and 0.811 s at the matrix.
3. **My Σ₁ template is a probe, not a placed master edit.** Placing
   `EraseTransferΣ₁` in `L.Condensation` is a build task. Its marginal
   cost inside the master is not measured here.
4. **The `Miscellaneous` line.** Each probe pays 1.5 to 2.9 s to load
   interfaces. That is per-invocation cost, not content cost; the
   ledger says so itself at `dev/ledger.toml:2580-2586`. Wherever the
   comparison decides anything I use the PROFILED per-definition lines,
   not the probe totals.
5. **I re-ran only the control unchanged.** I did not re-run the
   return's `Slots`, `Linear`, `MatrixSlots` or `MatrixControl` probes
   as written. I read the inline `refl` in each and give the
   `file:line`; H6 and H7 measure the corrected spellings instead.
6. **The 129 s in `src/ProbeDD25H5.agda` part 2 is mine.** It shows the
   Σ₁ transfer can be spelled badly. It is not evidence about the
   return.
7. **Machine load.** It read 3.1 to 4.9 for most runs and touched 8.6
   during the H6 batch. H6's figures are the ones to distrust, and they
   are 2.1 to 2.3 s, so the load cannot change any conclusion.
8. **`levelIn`'s collapse-of-the-level step is still unpriced**, and it
   is now the phase's widest unmeasured term.

## 8. MEASUREMENTS

Caliber: USER seconds from `/usr/bin/time -p`, and Agda's own
`--profile=definitions` attribution in milliseconds. ONE caliber for
each comparison; I never mix them. Cold probe: the probe's own
interface is removed before every run. Dependencies warm. ONE agda
process at a time. `GHCRTS="-A64m -I0 -M8g"`, cap never raised. No heap
exhaustion at any run. Every run exited 0. There is no interruption and
no stop in this review: every figure below is a completed run.

| probe | what it checks | runs, user s | mean | spread |
|---|---|---|---:|---:|
| `ProbeLJ150Control` (return's, unchanged) | `erase-Δ₀` at the leaf, inline `refl` | 151.44 | n/a | one run |
| `ProbeDD25H1` | the decomposition, named proof | 2.07 | n/a | one run |
| `ProbeDD25H3` | the control with ONLY the proof named | 2.11 / 2.19 / 2.20 | 2.17 | 0.09 (4.2 pc) |
| `ProbeDD25H2` | **THE EXIT**, `EraseTransfer` at the leaf | 1.62 / 1.53 / 1.54 | 1.56 | 0.09 (5.8 pc) |
| `ProbeDD25H5` | matrix on the exit route, plus a bad Σ₁ spelling | 139.21 / 137.70 / 138.49 | 138.47 | 1.51 (1.1 pc) |
| `ProbeDD25H8` | **the Σ₁ TEMPLATE**, then one instantiation | 2.89 / 2.83 / 2.76 | 2.83 | 0.13 (4.6 pc) |
| `ProbeDD25H7` | **the full matrix**, named proof | 3.04 / 3.08 / 3.11 | 3.08 | 0.07 (2.3 pc) |
| `ProbeDD25H6` | variable slots, named proof | 2.27 / 2.16 / 2.13 | 2.19 | 0.14 (6.4 pc) |
| `ProbeDD25H4` | the mechanism: two spellings of one proof | 152.35 | n/a | one run |

Agda's per-definition attribution, same runs, milliseconds:

| definition | ms |
|---|---:|
| `ProbeLJ150Control.transfer-concrete` | **150,133** |
| `ProbeDD25H4.transfer-concrete` | **151,402** |
| `ProbeDD25H4.count-defb` | 56 |
| `ProbeDD25H3.transfer-concrete` | **213 / 224 / 224** |
| `ProbeDD25H3.count-defb` | 57 / 59 / 61 |
| `ProbeDD25H1.transfer-concrete` | 203 |
| `ProbeDD25H1.erased-defb` | 102 |
| `ProbeDD25H1.count-defb` | 54 |
| `ProbeDD25H2.count-defb` | 53 / 53 / 55 |
| `ProbeDD25H2.LeafTransfer.*` | **below threshold** |
| `ProbeDD25H7.transfer-matrix` | **787 / 851 / 795** |
| `ProbeDD25H7.count-matrix` | 199 / 201 / 198 |
| `ProbeDD25H6.EraseLeaf.transfer` | 218 / 218 / 212 |
| `ProbeDD25H6.transfer-concrete` | 112 / 112 / 108 |
| `ProbeDD25H6.EraseLeaf.count-φ` | 54 / 55 / 52 |
| `ProbeDD25H5.MatrixTransfer.*` | **below threshold** |
| `ProbeDD25H5.count-matrix` | 197 / 203 / 210 |
| `ProbeDD25H5.StmtTransfer.σL-up` (bad spelling) | 129,422 / 127,627 / 128,270 |
| `ProbeDD25H5.StmtTransfer.σL≡` | 7,385 / 7,428 / 7,575 |
| `ProbeDD25H8.count-Σ₂` | 205 / 208 / 202 |
| `ProbeDD25H8.EraseTransferΣ₁.*`, `StmtTransfer.*` | **below threshold** |

The control's own profile line, 150,133 ms, reproduces the 150.13 s
that `[LJ-1.49]` recorded and `[LJ-1.50]` carried forward, and my whole
run at 151.44 s sits inside the return's own three-run range of 149.73
to 152.19 s. **I do not dispute any number the return reports. I
dispute what it is a number OF.**

## 9. DD4

The exit is template content, and the template already exists. Both
towers instantiate `EraseTransfer`
(`src/L/Condensation.lagda.md:273-294`); it mentions no L syntax. The
one thing missing is its Σ₁ counterpart, and
`src/ProbeDD25H8.agda:49-69` supplies it in 16 non-blank lines with the
same property. **The J tower inherits a module, not a measurement.**

## 10. ARCHIVE USED

- `_build/lj-1.50-report.md`, read WHOLE. Took the verdict (`:9-45`),
  the probe table (`:59-63`), the profile (`:67-71`), the matrix stops
  (`:88-102`), the DD4 answer (`:130-142`) and the not-sure list
  (`:187-203`).
- `_build/briefs/LJ-1.50.md`, read WHOLE. Took the P-u instruction
  (`:39-43`), the three cures table (`:45-51`), the C-34 sentence
  (`:55`), the caliber trap (`:84-89`) and the threshold (`:91-95`).
- `_build/lj-1.7-review.md:218-220`, the `erase-Δ₀` zero-consumer fact.
- `_build/lj-1.49-report.md:87-94`, the adequacy obligation as stated.
- `src/L/Condensation.lagda.md`: `EraseTransfer` (`:273-294`),
  `ClauseDecode`'s instantiation (`:351-352`), `CertTransfer`
  (`:398-400`), `RowTransfer` (`:1772-1783`), `DefBodyB` and
  `Δ₀-DefBodyB` (`:2316-2348`).
- `src/L/BoundedSubset.lagda.md`: `isOrdAt` and `Δ₀-isOrdAt`
  (`:475-482`), `erase-Δ₀` (`:503-518`), `LevelHood0` (`:520-548`),
  `D0` (`:572`), `Condense` and `β-sep` (`:596-614`).
- `src/FOL/Absoluteness.lagda.md`: `Single` (`:57-76`), `abs₀`
  (`:122-127`), `σ₁-up` (`:182-185`).
- `src/FOL/LevyHierarchy.lagda.md`: `Δ₀` (`:47-58`), `Σ₁` and `σ-Δ₀` (`:73-76`).
- `src/FOL/Count.lagda.md`: `erase` and `erase-inv` (`:594-637`).
- `src/V/Smallness.lagda.md`: `separateFromSmall` (`:207-209`),
  `Δ₀Small` (`:248-252`).
- `dev/ledger.toml`: the seconds budget (`:305`), the AC rate
  (`:2590`), the tolerance (`:2810`), the caliber note
  (`:2580-2586`).
- `dev/LESSONS.md`: P-l (`:2305`), P-t (`:2601-2630`), P-u
  (`:2908-2940`), P-v (`:3037`), C-34 (`:3065-3092`), C-36
  (`:3178-3224`), D-30 (`:3226`), C-37 (`:3275`).

Nothing in `archive/` was read. WHY NOT: the question is an elaborator
cost and an architecture fact on this tree's own delivered code. The
retired route holds neither, and its condensation target is false
(`[LJ-1.11]`).

## 11. LITERATURE USED

NONE. This is an elaborator cost measurement and a reading of the
delivered tree's own consumers. `dev/literature/` was not opened, for
the reason the brief gives at `_build/briefs/LJ-1.50.md:124-126`.
