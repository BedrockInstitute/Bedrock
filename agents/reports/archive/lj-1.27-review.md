# LJ-1.27 review: the DD25 adversarial attack on the NO-GO

Status: COMPLETE. Written incrementally per C-22. Untracked probes, no
commit, no push. ASD-STE100.

## 1. THE VERDICT

**UPHOLD. The NO-GO stands.**

The number that decides it: **the cure the return hypothesized walls at 8 GB.**
I built the Delta-0 preservation lemma the return names in its section 9. It is
13 lines, and 16 with its instance. With it, the block does not check at 0.01
seconds per line. It does not check at all. Agda exhausts an 8 GB heap after 55
seconds.

The block's own rate is confirmed. It checks at 0.113 seconds per line on a
gross basis and 0.110 on a net basis. The gate says NO-GO at or above 0.100.
Both bases give NO-GO.

I attacked the negative on all four DD25 questions. Three of them return
nothing for the orchestrator. The fourth returns one cure, and that cure is
upstream and unmeasured. Section 6 names it.

## 2. IS THE MEASUREMENT SOUND?

YES. I re-verified every load-bearing figure with my own runs.

| figure | the return says | I measure |
|---|---:|---:|
| `src/ProbeLJ127.agda` cold, user seconds | 32.17 to 33.27 | 32.07 |
| `src/ProbeLJ127.agda` cold, wall seconds | 33.63 to 34.83 | 33.35 |
| non-blank non-comment lines | 283 | 283 |
| `src/ProbeLJ115.agda` calibration lines | 246 | 246 |
| `σL-transfer` seconds | 24.8 | 25.63, isolated |
| base variant lines | 209 | 209 |
| warm interface read, user seconds | 1.21 | 1.05 |

The line convention reproduces exactly. `grep -v '^[[:space:]]*$' | grep -vc
'^[[:space:]]*--'` gives 283 for `src/ProbeLJ127.agda` and 246 for
`src/ProbeLJ115.agda`.

I confirmed the profile by an independent method. `src/ProbeDD25C.agda` holds
the clause, its Delta-0 witnesses, `σL`, and ONLY the composed `σL-transfer`.
It checks in 25.63 seconds. That agrees with the return's profile attribution
of 24.8 seconds to `σL-transfer`.

**One accounting wrinkle, and it does not change any verdict.** The return
compares a NET base figure with a GROSS headline. Its 1.11 seconds for the
base variant has the interface read taken out. Its 33.3 seconds for the block
does not. I measured the base variant at 2.38 seconds gross and the warm read
at 1.05 to 1.09 seconds. On one basis throughout:

| basis | block | base variant |
|---|---:|---:|
| gross | 0.113 | 0.0114 |
| net | 0.110 | 0.0062 |

The block is NO-GO on both. The base variant is GO on both. The wrinkle makes
the gap look 2x wider than it is, and nothing more.

## 3. DID THE BRIEF CAUSE THE OUTCOME?

**NO.** I am the interested party here, and I tested this first. The answer is
clean.

The brief says: "Embed ONE bounded clause at `Sʟ` with `embed`"
(`_build/briefs/LJ-1.27.md:36`). `embed` accepts a parameter-free formula only
(`src/FOL/Manipulation/Relabelling.lagda.md:117`). So the instruction does
force a placement for a clause that carries constants. That much of the
return's section 9 is right.

**But the placement is not the brief's doing. It is forced by the delivered
coding layer, sixteen times over.**

The return says the clause carries "the constant `numeralL 8`", one constant
(`_build/lj-1.27-report.md:104-106`). I removed that constant. I gave the
clause a fourth slot `N` and wrote `var N` in place of `con (numeralL 8)`. Then
I asked Agda for the count. `src/ProbeDD25E.agda:273` reports:

```
16 != 0 of type ℕ
when checking that the expression refl has type
countFo (Clause.existBndAt C T B N) ≡ 0
```

**Sixteen constants remain after the numeral is gone.** I located them.
`src/ProbeDD25F.agda` measures each delivered coding reader:

| reader | constants |
|---|---:|
| `prAtL` | 0 |
| `appAt` | 0 |
| `sucAtL` | 0 |
| `tagAtL` | 1 |
| **`consAtL`** | **16** |

`consAtL` is used once, in `bodyBnd` (`src/ProbeLJ127.agda:114`). It carries 16
constants by itself. Its source is `consAt`
(`src/L/Coding/Environment.lagda.md:338-343`), which names `tagAt` twice and
`shiftPairAt` twice.

So the brief's instruction contributed 1 constant of 17. **The return's second
uncertainty is false.** Section 9 says: "If the intended clause was the
parameter-free form from the start, the placement vanishes and the block
shrinks" (`_build/lj-1.27-report.md:208-210`). It does not vanish. This clause
cannot be written parameter-free while it uses the delivered `consAtL`.

The brief named `embed`, and `embed` is the architecture's own entrance to the
parameter-free axis. The archive enters by the same door
(`archive/rud-route/src/L/Condensation.lagda.md:824`). The difference is that
the archive's story is BORN parameter-free, so it never places. This clause
cannot be born that way.

## 4. THE Δ₀ PRESERVATION LEMMA

**It exists. It is 13 lines. It walls.**

I built it. It is the exact mirror of the delivered `mapΔ₀`
(`src/FOL/Manipulation/Relabelling.lagda.md:209-220`), one clause per Delta-0
constructor:

```agda
placeΔ₀ : ∀ {ℓz ℓc} {K : Type ℓc} {n k} {φ : Formula K n}
        → Δ₀ φ → (θ : Fin (countFo φ) → Fin (n + k))
        → Δ₀ (placeFo {ℓz = ℓz} φ θ)
```

The return is right that the lemma is small. It needs no new idea. With it the
transfer becomes one line:

```agda
Δ₀-σL       = mapΔ₀ Empty.rec* (absΔ₀ (Clause.Δ₀-existBndAt {n} C T B))
σL-transfer = cong ⟨_⟩ (AbsL.abs₀ Δ₀-σL δ)
```

**Measured result: heap exhaustion at 8 GB.**

| probe | content | lines | result |
|---|---|---:|---|
| `src/ProbeDD25A.agda` | the whole block, direct route | 276 | **WALL**, 71.95 s |
| `src/ProbeDD25B.agda` | `σL` and the direct transfer only | 188 | **WALL**, 55.16 s |
| `src/ProbeDD25D.agda` | `Δ₀-σL` only, no transfer at all | 186 | **WALL**, 55.52 s |
| `src/ProbeDD25H.agda` | `Δ₀-σL` only, explicit placements | 194 | **WALL**, 63.16 s |
| `src/ProbeDD25C.agda` | `σL` and the composed transfer only | 213 | GREEN, 25.63 s |

Read the table in this order.

`src/ProbeDD25D.agda` locates the wall exactly. It stops after `Δ₀-σL`. It
never mentions `abs₀`. It still exhausts the heap. **So the wall is in BUILDING
the Delta-0 witness for the placed formula, and not in applying absoluteness to
it.** The elaborator must normalize `placeFo` over the whole clause tree, and
every node carries the placed subformula as an implicit argument.

`src/ProbeDD25H.agda` is the fair second formulation. I wrote every placement
out by hand, so no meta-solving is involved. It still walls. The wall is not an
artefact of how I wrote the lemma.

`src/ProbeDD25C.agda` is the control. The return's composed route, in the same
isolation, is GREEN at 25.63 seconds.

**The return composed the transfer through four generic theorems because the
direct route does not exist at this size. It paid 25 seconds. The direct route
costs infinity.** That is the opposite of what section 9 hoped for, and I
report it as an adversarial reviewer who wanted the overturn.

All runs used `GHCRTS="-A64m -I0 -M8g"`, one process, per C-12. No sibling Agda
process ran. I never raised the cap.

## 5. IS THE Σ₁ WITNESS FOR THE PLACED FORMULA REALLY UNDELIVERED?

The return's claim is half right, and the half that is wrong does not help it.

**For the EMBEDDING, the witness IS delivered.** `mapΔ₀` is at
`src/FOL/Manipulation/Relabelling.lagda.md:209-220`. `mapΣₙ` is at `:232-236`.
`mapΠₙ` is at `:238-242`. They carry a Levy witness along any constant
relabelling, and `embed` is one (`:117-118`).

**For the PLACEMENT, the witness is NOT delivered, and I confirm it
structurally.** `src/FOL/Manipulation/Parameters.lagda.md` does not import
`FOL.LevyHierarchy`. The import block is at `:24-33` and the grep count for
`LevyHierarchy` in that file is zero. No Levy transport can exist in that file.
The return is correct.

**Two corrections to the return's wording.**

First, `σL` needs a Delta-0 witness, not a Sigma-1 witness. `σL` is the matrix
(`src/ProbeLJ127.agda:277`). The Sigma-1 level enters only at `existCertAt`.

Second, at `existCertAt` the Sigma-1 witness IS built and `σ₁-up` IS applied in
one line. `Σ₁-cert` is at `src/ProbeLJ127.agda:211-212`. `cert-transfer =
AbsL.σ₁-up (Σ₁-cert C T B) γ'` is at `:366-368`. The return itself measures
that line at 179 milliseconds (`_build/lj-1.27-report.md:93-95`). **The
delivered one-line shape is already in the probe and already cheap.** It is
cheap because it acts on the UNPLACED clause.

**The archive is not a counter-example.** Its `levelStory` is born
parameter-free, as `Formula ⊥* 2`, so it never places at all. It then takes its
witness from the delivered relabelling transport:
`levelΣ₁L = mapΣ₁ Empty.rec* levelStoryΣ₁`
(`archive/rud-route/src/L/Condensation.lagda.md:830-831`). Its one-line
`σ₁-up` at `:845-848` works for that reason and no other. Section 3 shows this
clause cannot be born parameter-free.

## 6. WHAT THE GATE SHOULD SAY NOW, AND WHETHER ROUTE A FUNDS

**The gate says NO-GO, at 0.110 to 0.113 seconds per line. Route A does not
fund in its present shape.** The phase stops for a re-route under DD8, as the
return says.

Three of the four ways out are now closed by measurement, not by argument:

1. The Delta-0 placement lemma walls, in two formulations (section 4).
2. A parameter-free clause is impossible while `consAtL` is used (section 3).
3. The delivered one-line `σ₁-up` is already in the block and already cheap. It
   does not carry the two-carrier comparison the crossing needs (section 5).

**There is a fourth way out. It is upstream, it is real, and I did NOT measure
it.** Make `consAtL` constant-free.

The reasoning, and I mark it as a hypothesis and not a price. The clause has 17
constants. 16 come from `consAtL` and 1 from the numeral. If `consAtL` were
constant-free, and the numeral moved to a slot, then `countFo` of the clause
would be 0. A formula with no constants reaches the parameter-free axis by the
DELIVERED `erase`, with no placement at any point:

- `erase : (φ : Formula K n) → countFo φ ≡ 0 → Formula (⊥* {ℓ}) n`
  (`src/FOL/Count.lagda.md:598-611`)
- `erase-inv : mapFo Empty.rec* (erase φ p) ≡ φ` (`src/FOL/Count.lagda.md:617-637`)

Then `σL = embed (erase φ refl)` and `erase-inv` says `σL ≡ φ` as syntax. The
transfer becomes two syntactic `cong`s plus one `abs₀` at the original clause.
The return measures that `abs₀` at about 1.6 seconds
(`_build/lj-1.27-report.md:95`). `σL-eq` becomes one `cong` and drops its two
generic theorems. I wrote this variant as `src/ProbeDD25E.agda`. It fails at
one line only, the `refl` that asserts the count is zero.

**I did not measure it, because it needs a rewrite of `L.Coding.Model` and
`L.Coding.Environment` that is outside a probe's scope.** P-l forbids me from
pricing it by analogy. Treat it as a recon target, not as funding.

Its own risk is plain. The 16 constants sit in `tagAt` and `shiftPairAt` inside
`consAt` (`src/L/Coding/Environment.lagda.md:338-343`). Those readers name
concrete coded objects. Moving 16 constants into environment slots widens every
consumer's arity, and nobody has measured what that costs. `dev/LESSONS.md:2330-2348`
records that four of five transplants in this tree FAILED.

**Candidate law, with its measurement, for the orchestrator to number or
reject.** A Levy witness travels along a constant relabelling for free, and it
does not travel along a parameter placement at all. Certify the formula BEFORE
you place it, then compose the absoluteness through the unplaced form. Measured
at `[LJ-1.27]`'s clause: the placed witness exhausts 8 GB in 55 seconds
(`src/ProbeDD25D.agda`), and the composed route through the unplaced form
checks in 25.6 seconds (`src/ProbeDD25C.agda`). This also confirms P-t from a
new direction: the class follows the FORMULA, and placing the formula changes
the class.

## 7. WHAT I AM NOT SURE OF

**The `consAtL` cure is unmeasured, and it is the one live route.** I gave the
mechanism and the delivered lemmas it would ride. I did not build it. It could
fail for a reason nobody sees yet, and the widened arity is the obvious
suspect.

**I did not test whether the crossing needs `σL` at all.** The whole 31 seconds
buys ONE formula readable at two carriers. `[LJ-1.26]`'s design asks for it, and
I take that as given. If the crossing can be restated so that each carrier
keeps its own formula and only the MEANINGS are compared, the apparatus goes
away and the base rate governs. That is an architecture question and it belongs
to the orchestrator, not to a probe.

**The 8 GB wall is a wall, not a price.** I report it as C-12 requires. I did
not raise the cap, so I do not know whether the direct route finishes at 16 GB
or never. A wall at 8 GB is already a NO-GO for a 3,300-line block, so the
distinction does not change the verdict.

**My base-variant figure is 2.38 seconds gross where the return says 1.11
seconds net.** I reconciled them through the 1.05 second warm read. The
residual gap is about 0.2 seconds, inside the noise rule.

**One probe of mine is red by design.** `src/ProbeDD25E.agda` does not
typecheck. Its error message IS its measurement, and section 3 quotes it.

## 8. THE PROBES

All are untracked and none is committed. `scripts/check-probes.py` stays green.

| file | what it measures |
|---|---|
| `src/ProbeDD25A.agda` | the whole block on the direct route |
| `src/ProbeDD25B.agda` | the direct transfer, isolated |
| `src/ProbeDD25C.agda` | the composed transfer, isolated (control) |
| `src/ProbeDD25D.agda` | the placed Delta-0 witness alone |
| `src/ProbeDD25E.agda` | the constant count after the numeral is removed |
| `src/ProbeDD25F.agda` | the constant count of each coding reader |
| `src/ProbeDD25G.agda` | the base variant, re-verified at 209 lines |
| `src/ProbeDD25H.agda` | the placed witness with explicit placements |
