# LJ-1.161 report: the transfer half of `CrossOut`, gated at 60 lines

tier: opus (version `override`). **No master was changed. One probe was written
and it runs GREEN, exit 0. No commit, no push.** Every negative is marked
**MEASURED** or **INFERRED**. Written incrementally (C-22).

## 0. LEAD

### 0.1 The verdict, against the criterion `[LJ-1.160]` fixed in advance

**GO. The ONE TRANSFER is 20 in-fence lines against a 60-line criterion.**

`agents/tasks/LJ-1-161/ProbeLJ1161A.agda`, block 1, exit 0.

**The NO-GO branch is MEASURED FALSE.** The certificate's formula DOES sit at
the image's carrier without re-labelling. The relabelling kit
(`src/FOL/Manipulation/Bounding.lagda.md:146`) never enters, so the archive's
`Transport` comparable is not the price here.

### 0.2 What the 20 lines are, and what I excluded

**Excluded**: the OPTIONS header, every import, the module header, the four
module aliases (`CS`, `Cnt`, `SemV`, `open SemV`), every comment, every blank
line, the site module `AtSite`, block 2 and block 3.

**Counted**: the code lines of block 1, non-blank and non-comment.

| part | lines | what it is |
|---:|---:|---|
| `mapΣ₁` | 4 | `Σ₁` travels with a relabelling. The tree delivers `mapΔ₀` and `mapΣₙ`, not this |
| `erase-Σ₁` | 4 | `Σ₁` reaches the parameter-free axis. The tree delivers `erase-Δ₀` |
| `module AtImage` + `module Abs =` | 2 | `FOL.Absoluteness.Single` opened at the image |
| `at` | 2 | any parameter-free class-carrier formula, AT the image |
| `transfer` | 4 | `TransferM` itself, generic in the certificate: one `σ₁-up` |
| `cert-transfer` | 4 | **C-38**: the instance at the REAL `Σ₁-cert` |
| **TOTAL** | **20** | |

**File totals, separately, as the brief demands**: 69 non-blank non-comment
lines; 158 non-blank lines; 189 lines. **The 69 includes block 2, which the gate
does not count; block 3 walled and is kept as comment, so it counts in the 158
and not in the 69.**

### 0.3 Why it is cheap, in one sentence

**The delivered certificate carries NO CONSTANT, so it reaches the image's
carrier through the parameter-free axis, and the `Relabel` kit never enters.**

`src/L/Condensation.lagda.md:439-440` states this in the master itself: "The tag
numerals are slots, so every row formula carries `countFo = 0` and instantiates
the `EraseTransfer` template." `:362` proves it, with `refl` as the count.

**This is the NO-GO branch NOT taken, and it is the whole finding.** The archive
needed `Relabel` because ITS level formula had constants at the class carrier:
`module Down = Relabel {K = Sʟ} {K' = Sᴹ} fst fst InM ...` at
`archive/src/2026-08-09-rud-route/L/Condensation.lagda.md:137-138`, and its
`Transport` takes a per-constant certificate `BoundedFo InM Φ` as an UNPRICED
module hypothesis (`:278`). **The current tree's certificate has no constant to
certify.**

### 0.4 The delivered comparable, in the same file, at `file:line`

**`module CertTransfer` at `src/L/Condensation.lagda.md:409-411` is the SAME
move at the CLASS carrier, and it is 3 code lines**:

```agda
module CertTransfer {n : ℕ} (C T B N : Fin n) (γ' : S ^ n) where
  cert-transfer : ⟨ γ' ⊨ existCertAt C T B N ⟩ → ⟨ map fst γ' ⊨ᵛ existCertAt C T B N ⟩
  cert-transfer = AbsL.σ₁-up (Σ₁-cert C T B N) γ'
```

**So the whole cost of moving the transfer from the class carrier to the
collapse image is 20 lines against 3.** This is a comparable in the SAME file on
the SAME tower, which is what P-l asks for; the archive's `Transport` sits on
the rud tower and I do not use it as the anchor.

### 0.5 The counterweight, and it is the size of the GO

**The certificate the brief named is not the certificate `CrossOut` consumes.**
`Σ₁-cert` certifies ONE row of the twelve-row satisfaction table. **What
`CrossOut` needs is `LevelHood.Σ₁-levelHood`
(`src/L/BoundedSubset.lagda.md:145-146`), which is Devlin's `∃z Φ(z, v, γ)` and
is also delivered.**

**Block 1 is generic and takes either. I tried the second one and it WALLED at
20 minutes** (section 6.3). **MEASURED.** So the transfer half is cheap and the
thing it is for is not yet reachable in one agda process. **Nobody should carry
"the transfer half is 20 lines" without also carrying that sentence.**

## 1. THE MEASUREMENT

### 1.1 The three blocks, and only the first is gated

| block | what it measures | code lines | result |
|---|---|---:|---|
| **1** | **the ONE TRANSFER at the real `Σ₁-cert`** | **20** | **exit 0** |
| 2 | the moved formula MEANS the delivered one | 18 | exit 0 |
| 3 | the same block at the delivered LEVEL-HOOD certificate | 10 | **WALL at 20 minutes** |

**Block 1 alone answers the brief.** Blocks 2 and 3 answer the RETURN's second
question, "what remains open in `CrossOut` after it".

**Block 3's wall is itself an answer and I lead with it rather than bury it:
the transfer machine is generic and free, and the LEVEL-HOOD certificate cannot
be fed to it in one process. Section 6.3 gives the figure and the diagnosis.**

### 1.2 Block 1, line by line

```agda
mapΣ₁ : ∀ {ℓc ℓd} {K : Type ℓc} {K' : Type ℓd} (f : K → K')
        {n} {φ : Formula K n} → Σ₁ φ → Σ₁ (mapFo f φ)
mapΣ₁ f (σ-Δ₀ d) = σ-Δ₀ (mapΔ₀ f d)
mapΣ₁ f (σ-∃ s)  = σ-∃ (mapΣ₁ f s)

erase-Σ₁ : {m : ℕ} (φ : Formula CS.S m) (p : countFo φ ≡ 0)
         → Σ₁ φ → Σ₁ (Cnt.erase φ p)
erase-Σ₁ φ p (σ-Δ₀ d)    = σ-Δ₀ (erase-Δ₀ φ p d)
erase-Σ₁ (∃̇ φ) p (σ-∃ s) = σ-∃ (erase-Σ₁ φ p s)

module AtImage (P : S) (Ptr : isTrans P) where
  module Abs = FOL.Absoluteness.Single 𝒮ᵥ (λ x → x ∈ˢ P) Ptr
  at : {m : ℕ} (φ : Formula CS.S m) (p : countFo φ ≡ 0) → Formula Abs.SM m
  at φ p = embed (Cnt.erase φ p)
  transfer : {m : ℕ} (φ : Formula CS.S m) (p : countFo φ ≡ 0) → Σ₁ φ
           → (γ : Abs.SM Abs.^ m)
           → ⟨ γ Abs.⊨ᵐ at φ p ⟩ → ⟨ map fst γ Abs.⊨ᵛ at φ p ⟩
  transfer φ p s = Abs.σ₁-up (mapΣ₁ Empty.rec* (erase-Σ₁ φ p s))
  cert-transfer : ∀ {n} (C T B N : Fin n) (γ : Abs.SM Abs.^ n)
                → ⟨ γ Abs.⊨ᵐ at (existCertAt C T B N) refl ⟩
                → ⟨ map fst γ Abs.⊨ᵛ at (existCertAt C T B N) refl ⟩
  cert-transfer C T B N = transfer (existCertAt C T B N) refl (Σ₁-cert C T B N)
```

**Two of the twenty lines were the only new mathematics**: `mapΣ₁` and
`erase-Σ₁` are the two carriers of a Levy witness the tree does not deliver.
**MEASURED, by `grep` over `src/`: `mapΣ₁` does not exist** (only `mapΔ₀`,
`mapΣₙ` and `mapΠₙ`, `src/FOL/Manipulation/Relabelling.lagda.md:209`, `:232`,
`:238`); **`erase-Δ₀` does exist** (`src/L/BoundedSubset.lagda.md:825`) and
`erase-Σ₁` is its four-line `Σ₁` companion.

### 1.3 The C-38 guard, answered directly

**`Σ₁-cert` is CONSUMED at `cert-transfer`, not restated.** `existCertAt` is the
delivered formula. The probe writes no certificate of its own and postulates
nothing.

**And a fact that sharpens the guard. MEASURED, by `grep` over `src/`:
`existCertAt` and `Σ₁-cert` have NO consumer outside their own master.** They
appear at `src/L/Condensation.lagda.md:266`, `:267`, `:269`, `:270` and `:410`
only, and `module CertTransfer` at `:409` has no consumer either. **My probe is
the certificate's first consumer outside the file that defines it.**

### 1.4 Block 3, and its abort criterion, fixed BEFORE the result

**Block 3 is NOT part of the gate.** It asks whether block 1's generic transfer
also carries the delivered LEVEL-HOOD certificate,
`LevelHood.Σ₁-levelHood` (`src/L/BoundedSubset.lagda.md:145-146`), which is what
`CrossOut` actually consumes.

**The criterion, written before the result**: **20 minutes of wall time**, under
`GHCRTS="-A64m -I0 -M8g"` and ONE agda process. Past that I record a **WALL**, I
remove block 3 from the probe so that blocks 1 and 2 stand green, and I report
the wall as a measured cost of `countFo ≡ 0` at that formula. **I never raise
the cap and I never re-price the gate on block 3's outcome.**

**Why 20 minutes is the honest bound and not a convenience.** `AGENTS.md`
records a cold whole-tree typecheck at about twelve minutes. **A single probe
declaration that outruns the whole tree has already told me its answer**, and
`dev/PLAN.md` DD15 forbids holding a session on a long check.

**The criterion fired. Section 6.3 reports the WALL and I did not move the
criterion after I saw the clock.**

## 2. WHAT REMAINS OPEN IN `CrossOut`

### 2.1 The chain, with each leg's state

`CrossOut` at the image is
`(v b : Sᴾ) → IsOrd (fst b) → Believes v b → fst v ≡ Lset (fst b)`.

| leg | what it is | state |
|---|---|---|
| 1 | inner reading at `C.πX` ⇒ ambient reading, at the moved certificate | **MEASURED, 20 lines.** Block 1 |
| 2 | the moved formula MEANS the delivered one | **MEASURED, 18 lines.** Block 2 |
| 3 | ambient reading ⇒ `v ≡ Lset b` | **OPEN.** This is the term the brief's GO clause predicted |

**`[LJ-1.160]`'s GO clause said the open term would narrow to "the ambient
identification alone". It does. Section 2.2 says what that term is made of.**

### 2.2 The ambient identification, named at `file:line`

**The delivered identification is `Lset-only`** at
`src/L/Hierarchy.lagda.md:334-335`:

```agda
  Lset-only : ⟨ γ ⊨ LsetGraphAt w b ⟩ → IsOrd (fst (lookup b γ))
            → fst (lookup w γ) ≡ Lset (fst (lookup b γ))
```

**Three MEASURED facts separate it from what block 1 produces.**

1. **Its `⊨` is the INNER reading at the L CLASS**, not the ambient reading and
   not a reading at the image. `module AbsL = FOL.Absoluteness.Single 𝒮ᵥ isL
   isL-trans` and `open AbsL renaming ( _⊨ᵐ_ to _⊨_ )` at
   `src/L/Hierarchy.lagda.md:78-79`.
2. **Its formula is the UNBOUNDED tower graph.** `GraphAt w b = ∃̇ (ApproxAt
   zero (suc b) ∧̇ Step (suc w) (suc b) zero)` at
   `src/L/Coding/Sequence.lagda.md:291-292`, and `ApproxAt` carries `∀̇ (∀̇ ...)`
   at `:286-290`. **Two UNBOUNDED universal quantifiers**, so the formula is not
   Δ₀ and not Σ₁, and neither `abs₀` nor `σ₁-up` can carry it.
3. **MEASURED, by `grep` over `src/`: no `Δ₀` or `Σ₁` witness exists for
   `ApproxAt`, `StepAt`, `GraphAt` or `LsetGraphAt` anywhere.**
   `src/L/Coding/Sequence.lagda.md` contains no `Δ₀` and no `Σ₁` at all.

**And the repair is already delivered, which is the good half of this section.**
`GraphB.graphBndAt` with `Δ₀-graphBndAt` at
`src/L/Condensation.lagda.md:2489-2493` is the BOUNDED restatement of the same
graph, and it is **Δ₀**, not merely Σ₁. `LevelHood.levelHoodΣ₁` with
`Σ₁-levelHood` at `src/L/BoundedSubset.lagda.md:144-146` puts the unbounded
witness over that bounded matrix. **That is Devlin's `∃z Φ(z, v, γ)` exactly.**

**So the open term is the adequacy between the bounded restatement and the
unbounded graph, at the ambient reading. INFERRED**, because I did not write it;
**the three `*Agree` masters are that same work for the twelve-row satisfaction
table** (`src/L/Condensation/README.md:1-19`), so the shape of the remaining work
is delivered elsewhere in the tree and is not a new kind of thing.

**And block 3 measured the price of NOT respecting that shape.** Feeding the
whole level-hood formula to one process walls at 20 minutes (section 6.3).
**Whoever funds the next block should assume the split, not discover it.**

### 2.3 The second open half, and I state it so nobody banks the first

**`σ₁-up` is one-way and it puts the existential witness in the AMBIENT world.**
`Lset-only` wants the witness inside `L`. **INFERRED**: getting the witness back
inside is not free, and block 1 does not touch it. **C-36 binds: I do not claim
no cheap route exists. I claim I did not measure one.**

## 3. `HasLevels` AND `Covered`: SAME OR DIFFERENT

**They look the SAME as each other and DIFFERENT from `CrossOut`'s transfer
half. MEASURED on the types, INFERRED on the price.**

### 3.1 The direction is opposite, and that is the whole difference

`CrossOut` consumes `Believes` and produces an identification, so its transfer
runs OUT of the image: inner reading to ambient reading, by `σ₁-up`.

`HasLevels` and `Covered` PRODUCE `Believes`:

```agda
  HasLevels φ = (b : Sᴹ) → IsOrd (fst b) → ∥ Σ[ v ∈ Sᴹ ] Believes φ v b ∥₁
  Covered φ = (x : Sᴹ) → ∥ Σ[ b ∈ Sᴹ ] Σ[ v ∈ Sᴹ ]
                (IsOrd (fst b) × Believes φ v b × ⟨ fst x ∈ˢ fst v ⟩) ∥₁
```

(`archive/src/2026-08-09-rud-route/L/Condensation.lagda.md:173-180`.) **Both are
truncated existentials whose payload is a belief AT the image. Nothing can
export them; something must import them.**

### 3.2 Their machine is delivered, and it is NOT `σ₁-up`

**`IsoInv.iso-inv` at `src/L/BoundedSubset.lagda.md:195-196` and `iso-inv-bwd`
at `:250-251` transport satisfaction across the collapse in BOTH directions, for
EVERY formula, with no Levy grade at all.** They are wrapped for the site as
`AtHullInstance.transfer` at `:777-780`, over `CollapseIso` at `:321-350`, whose
own inputs are `C.πX-intro`, `CI.iso`, `CI.π-inj` and `C.πX-member`, all
delivered in `src/V/Collapse.lagda.md`.

**This confirms `[LJ-1.160]`'s INFERRED row and upgrades it.** `[LJ-1.160]` said
satisfaction "transports along the collapse isomorphism" and marked the
induction "not written". **MEASURED: it IS written, at
`src/L/BoundedSubset.lagda.md:194-251`, and it is a mutual induction over the
formula, not over a Levy witness.**

### 3.3 What is left for them, then

**The hull's belief.** `iso-inv` moves a satisfaction from the hull `M` to the
image `C.πX`; something must first show the hull believes the level formula at
each of its ordinals. **That is `ElemDown`, the elementarity residue**
(`src/L/BoundedSubset.lagda.md:782-786`, `DR.down-reflect`). **`[LJ-1.51]`
already named it unbuilt** and `[LJ-1.160]` measured that both routes need it,
so it does not separate the three open facts. **MEASURED, from the two reports
read side by side, and re-confirmed at the live `file:line` above.**

## 4. DD4

**Maximize the code the two proofs share, and write it generic.**

### 4.1 The answer the brief asked for, in one line

**16 of the 20 gated lines are TEMPLATE content. 4 name the Def tower.**

| part | lines | class | why |
|---|---:|---|---|
| `mapΣ₁` | 4 | **TEMPLATE** | generic in `K`, `K'`, `f`, `n` and `φ`. Names no carrier |
| `erase-Σ₁` | 4 | **TEMPLATE in shape** | names `CS.S`, the L class CARRIER, only because the delivered `erase-Δ₀` is specialized to it. Its body is carrier-blind |
| `at`, `transfer`, module header | 8 | **TEMPLATE** | generic in the formula. Zero `Lset`, zero `Def`, zero rud |
| `cert-transfer` | 4 | **PER-TOWER (Def)** | names `existCertAt` and `Σ₁-cert` |

**MEASURED by reading the block: `Lset` appears ZERO times in block 1.** The
only tower tokens are the two names in `cert-transfer`.

### 4.2 The J tower's cost, stated as a prediction and marked as one

**INFERRED**: a J tower supplies its own parameter-free Σ₁ certificate and
instantiates `transfer` in 4 lines, the shape of `cert-transfer`. **The 16
template lines are written once.** This agrees with `[LJ-1.151]`'s 19-of-21 and
`[LJ-1.160]`'s 73 percent, and it is a THIRD site, not a restatement of theirs.

### 4.3 The generic form was the short form again

**No stop-line pushed me toward writing fixed.** I first wrote `transfer`
specialised to `existCertAt` and it was 18 lines; making it generic and adding
the C-38 instance cost 2 lines and bought block 3 for free. **That is the third
time this phase the generic form was within two lines of the fixed one**
(`[LJ-1.151]`, `[LJ-1.160]`, here).

**The limit, so nobody over-reads it.** The template is the TRANSFER. The
certificate itself is per-tower content, as `dev/literature/devlin-II5.md:375`
row C1 says, and this measurement does not touch that.

## 5. EVERY NEGATIVE, CLASSIFIED

| statement | class |
|---|---|
| the ONE TRANSFER exceeds 60 lines | **MEASURED FALSE.** 20 lines, block 1, exit 0 |
| the certificate needs the relabelling kit | **MEASURED FALSE.** `countFo (existCertAt ...) ≡ 0` by `refl`; `Relabel` needs a constant to certify and there is none |
| the certificate cannot reach the image's carrier | **MEASURED FALSE.** `at` reaches it in 2 lines through the delivered `embed` |
| the moved formula is a different sentence | **MEASURED FALSE.** Block 2, `ambient-agrees`, exit 0 |
| the tree delivers `mapΣ₁` | **MEASURED FALSE.** Only `mapΔ₀`, `mapΣₙ`, `mapΠₙ` exist |
| the tree delivers `erase-Δ₀` | **MEASURED TRUE.** `src/L/BoundedSubset.lagda.md:825` |
| `Σ₁-cert` had a consumer before this task | **MEASURED FALSE.** No use outside its own master |
| `CertTransfer` has a consumer | **MEASURED FALSE.** Defined at `:409`, never used |
| the transfer discharges `CrossOut` | **MEASURED FALSE.** It supplies one leg of three. Section 2.1 |
| `Lset-only` accepts what the transfer produces | **MEASURED FALSE.** It wants the INNER reading at the L class, of the UNBOUNDED graph |
| the unbounded tower graph is Σ₁ | **MEASURED FALSE.** `ApproxAt` carries two unbounded `∀̇` |
| a Levy witness for `LsetGraphAt` exists | **MEASURED FALSE.** None in `src/` |
| the level-hood certificate exists | **MEASURED TRUE.** `LevelHood.Σ₁-levelHood`, `src/L/BoundedSubset.lagda.md:145-146` |
| satisfaction transports along the collapse | **MEASURED TRUE, and it upgrades `[LJ-1.160]`'s INFERRED row.** `IsoInv.iso-inv`, `src/L/BoundedSubset.lagda.md:195-196`, `:250-251` |
| `HasLevels` and `Covered` need the same machine as `CrossOut`'s transfer | **MEASURED FALSE.** They need `iso-inv`, not `σ₁-up`, and they run the other way |
| `HasLevels` and `Covered` are the same as each other | **MEASURED TRUE on the types.** Both are truncated existentials over `Believes` |
| the elementarity residue separates the three open facts | **MEASURED FALSE.** All three need it. Section 3.3 |
| the ambient identification is priced | **NOT CLAIMED.** I give it no number. C-40 |
| no cheap route puts the existential witness back inside L | **NOT CLAIMED.** C-36. I did not search |
| the transfer block carries the level-hood certificate in one process | **MEASURED FALSE.** WALL at 20 min 0 s, exit 143. Section 6.3 |
| the level-hood certificate cannot be transferred at all | **NOT CLAIMED.** C-36. The wall is on `countFo ≡ 0` by `refl`, not on the transfer |
| block 3's wall is a new kind of obstruction | **MEASURED FALSE.** It is the wall the three `*Agree` masters exist to route around (`src/L/Condensation/README.md:1-3`) |
| block 3's wall moves the gate | **MEASURED FALSE.** Block 1 is 20 lines and exits 0 without block 3. Run 5 |

## 6. GATES AND MEASUREMENTS

### 6.1 The machine, as C-12 requires

**The machine was quiet. One user, load averages 4.32, 4.03, 3.52 at 2026-08-14
00:56.** My gate figure is LINES, so a busy machine costs me time only. **Block
3's figure is SECONDS, so I say the load beside it.**

**`GHCRTS="-A64m -I0 -M8g"`. ONE agda process at a time. The cap was never
raised.**

### 6.2 The runs

| run | probe state | result | wall |
|---:|---|---|---:|
| 1 | block 1 only, specialised at `existCertAt` | **exit 0** | **13.1 s** |
| 2 | + block 2, interpretation levels unpinned | exit 42, unsolved metas | seconds |
| 3 | block 2 with `ιP` and `ιL` pinned | **exit 0** | seconds |
| 4 | blocks 1 to 3, block 1 made generic | **WALL, SIGTERM, exit 143** | **20 min 0 s** |
| 5 | blocks 1 and 2, block 3 commented, interface deleted first | **exit 0** | **25 s** |

**Run 5 is the standing result.** `agents/tasks/LJ-1-161/ProbeLJ1161A.agda`,
exit 0, 25 s, no unsolved meta, no hole, no postulate.

**Run 2's failure is worth one line for the next agent**: `⊨-map` cannot infer
the target constant domain from a bare `fst`, and naming the two interpretations
(`ιP`, `ιL`) fixes it. That is 4 of block 2's 18 lines.

### 6.3 Block 3, against its fixed criterion: WALL

**MEASURED. Block 3 ran 20 minutes 0 seconds of wall time and did not finish.**

| figure | value |
|---|---|
| wall time | **20 min 0 s**, then SIGTERM, exit 143 |
| resident set | **9.03 GB, pinned and unchanging for the last 7 minutes** |
| heap cap | `-M8g`. **NO heap exhaustion. The cap held and was never raised** |
| processes | **ONE**. Load averages 4.32 to 4.43, one user |

**What walls, exactly. INFERRED from the structure, not measured by bisection:
`refl : countFo LH.levelHoodΣ₁ ≡ 0`.** Block 1 is generic and takes any
parameter-free Σ₁ certificate; the PROOF that this particular formula is
parameter-free forces `countFo` over a graph that nests the twelve-row bounded
table TWICE (`LevelHood`'s two `DefBodyB` arguments,
`src/L/BoundedSubset.lagda.md:81-105`).

**And the tree already knows this cost.** `src/L/Condensation/README.md:1-3`:
"The twelve-row agreement, split across separate masters so no single Agda
process elaborates all twelve rows." **So block 3's wall is the SAME wall the
three `*Agree` masters exist to route around, met at a new site. It is not a new
kind of obstruction and it does not touch the gate.**

**The pinned resident set is the signal I report and do not over-read.** A flat
9.03 GB under an 8 GB heap cap is the shape of garbage collection at the
ceiling. **MEASURED: the figure. INFERRED: the diagnosis.**

**What this does NOT say.** It does not say the level-hood certificate cannot
be transferred. **C-36 binds.** It says one process cannot prove that formula
parameter-free by `refl` inside 20 minutes, and that the cure is the delivered
one: split, or carry the `countFo ≡ 0` proof as a hypothesis instead of
recomputing it. **I did not price either cure.**

### 6.4 Checkers

| checker | result |
|---|---|
| `scripts/lint-agda.py --check` on the probe | **exit 0** |
| `scripts/check-unbound-hyp.py` on the probe | **clean (1 file)** |
| `scripts/check-probes.py --check` | **clean, 1,763 tracked files** |
| `scripts/lint-prose.py --check` on this report | **exit 0** |
| `scripts/ledger.py --brief` | standing **28,940 lines over 85 masters**, from HEAD; thresholds SUSPENDED per the ledger header |
| `make check` | **NOT RUN.** The orchestrator runs it |

### 6.5 Prohibitions, answered

**No master was edited.** `src/Everything.lagda.md` was never opened. The three
`*Agree` masters were read at their `README.md` and their first 20 lines only,
and never edited. **No commit, no push, no `git checkout`, `stash`, `reset` or
`clean`. No `make check`.** My only files are
`agents/tasks/LJ-1-161/lj-1.161-report.md` and
`agents/tasks/LJ-1-161/ProbeLJ1161A.agda`. **The probe is tracked, it sits
beside the report, and it is never deleted.**

## 6A. THE RULES, ANSWERED

- **D-1.** The gate's criterion was `[LJ-1.160]`'s, unchanged, and block 3's
  own criterion is written in section 1.4 with a number, before its result. The
  probe is in `agents/tasks/LJ-1-161/`, tracked, run while my task was live.
- **DD8.** One best-effort figure per term, each with its basis. The gate figure
  is 20 lines, basis: the probe. The comparable is live and in the same file
  (section 0.4), not an archive analogy.
- **P-l.** **This law decided my comparable.** The archive's `Transport` sits on
  the rud tower with an unpriced boundedness hypothesis; I refuse it as the
  anchor and use `CertTransfer` at `src/L/Condensation.lagda.md:409-411`, the
  same move on the same tower in the same file. **A measured cure does not
  transfer by analogy.**
- **P-i.** **This law bit and I obeyed its first clause.** Block 3 hangs, and
  P-i says the cause is one of three heavy-thing classes forced into
  normalization and that the cure is selected by the decision tree, never by
  trial. **I ran no trial and no surgery.** I recorded the wall, named the term
  I believe forces it, marked that INFERRED, and stopped. **The cure is the next
  brief's to fund.**
- **C-38 as extended.** Section 1.3. `Σ₁-cert` is CONSUMED at `cert-transfer`.
  **And I report the sharper fact the law asks for: before this probe the
  certificate had no instantiation anywhere, so `CertTransfer` at `:409` was a
  restatement by C-38's own test.**
- **C-36.** Sections 2.3 and 5's last rows. I do not claim no cheap route
  exists for the open legs. I claim I did not measure one.
- **C-40.** I re-price nothing. The gate figure covers the transfer and says so;
  the identification term gets no number.
- **C-12.** One agda process, `-M8g`, cap never raised, load beside the seconds.
- **C-22.** This file was a skeleton before I opened `L.Condensation`.
- **C-31 to C-34, C-37.** Section 2 names each open leg as an obligation with
  its `file:line`, and leaves no cure named and unpriced.
- **D-10.** The residue I priced is `[LJ-1.160]`'s obligation. **Its TRUTH held:
  the transfer is real and cheap.** What moved is the target: the certificate
  the phase needs is the LEVEL-HOOD one, not the satisfaction row, and section
  2.2 says so.
- **D-26, D-29, D-30.** Section 2 reports the reduction and does not bank it.
- **I-5.** Blocks 1 and 2 leave no unsolved meta and no hole.
- **DD13.** Section 0.4 prices the ideal form first, against a live comparable.
- **DD23.** No mathematical prose was written. The probe carries comments only.
- **DD4.** Section 4.
- **C-39.** Section 9.

## 7. ARCHIVE USED (DD18)

- **`archive/src/2026-08-09-rud-route/L/Condensation.lagda.md`**, read
  `:126-300`. **TOOK the crossing face (`:162-187`), `CrossOut` (`:168-170`),
  `HasLevels` (`:173-175`), `Covered` (`:177-180`), `Assembly` (`:208`),
  `level-in` (`:240-247`), `M⊆L` (`:249-257`), `Transport` (`:278-287`) and
  `TransferM` (`:291-293`).**
  - **`TransferM` at `:291-293` is the statement this task supplies.** I state
    it at the certificate's own arity instead of the archive's fixed arity 2,
    because `existCertAt` has four designated slots and an arity-2 instance
    would force them to collide.
  - **`:137-138`, `module Down = Relabel {K = Sʟ} {K' = Sᴹ} fst fst InM ...`,
    is the NO-GO branch's whole reason, and it does not apply here.** The
    archive relabelled because its formula had constants at the class carrier.
    **MEASURED: the current certificate has `countFo ≡ 0`, so `Relabel`'s
    per-constant certificate has nothing to certify.**
  - **The comparable, counted**: `Transport` plus `TransferM` is 13 in-fence
    lines at `:277-294`, and `InM` plus `Down` is 10 more at `:126-140`. **But
    `Transport` takes `BoundedFo InM Φ` as an UNPRICED module hypothesis
    (`:278`), so its 23 lines are not a complete price and I do not use them as
    my anchor.** Section 0.4 uses a live comparable instead (P-l).
- `agents/tasks/LJ-1-160/lj-1.160-report.md`, **READ WHOLE.** TOOK the
  obligation and its criterion (`:295-305`), the three open facts (`:266-279`),
  the 16-line re-route (`:196-201`), the archive's refuted instance
  (`:124-132`), and the DD4 split (`:383-390`).
- `agents/tasks/LJ-1-160/ProbeLJ1160A.agda`, **READ WHOLE.** TOOK the site
  match (`:108-131`) and the `Single`-at-the-image opening (`:49-55`). **My
  block 1 is the next leg of the same route and reuses its shape.**
- **`agents/tasks/archive/LJ-1-1/lj-1.1-recon.md:241`**, the ADAPTABLE IN SHAPE
  ONLY row that lists `CrossOut`, `HasLevels` and `Covered` by name. **Read.
  Section 3 answers the second and third names on that list.**
- `archive/dev/`: **NOT read.** No `D`-series ruling bears on a line count.

## 8. LITERATURE USED (DD18)

**`dev/literature/devlin-II5.md`, read `:90-115` and `:240-262`.**

**What Devlin transports, and how, in his own chain (`:102-106`):**

> the Σ₁ statement "∃v∃z φ(z, v, γ)" is transferred from L_α to X
> (Σ₁-elementarity, downward) and along the collapse to M; 1.9.15 converts M's
> satisfaction of the Σ₀ matrix into ambient Φ; (a) turns Φ into "v = L_γ"

**Three readings, and each maps onto one leg of section 2.1.**

1. **"along the collapse to M"** is `iso-inv`
   (`src/L/BoundedSubset.lagda.md:194-196`). Section 3.2.
2. **"1.9.15 converts M's satisfaction of the Σ₀ matrix into ambient Φ" is
   EXACTLY the transfer I measured.** 1.9.15 is Σ₀ absoluteness at a transitive
   carrier, our `abs₀` under `σ₁-up`. **Devlin's statement has the shape "one
   existential over a Σ₀ matrix", and `existCertAt = ∃̇ (existBndAt)` with
   `Δ₀-existBndAt` has that shape to the character.**
3. **"(a) turns Φ into `v = L_γ`" is the open leg.** Devlin's (a) is his 2.7:
   `∀v∀γ [v = L_γ ↔ ∃z Φ(z, v, γ)]`, an AMBIENT equivalence
   (`:95-99`). **Section 2.2's open term is Devlin's (a), and nothing else.**

**MEASURED against `[LJ-1.160]`: it read the same passage and reached the same
split. I confirm it and I add which of our names sits at each step.**

`dev/literature/devlin-II5.md:243-246`, the Δ₀-versus-Σ₁ correction, read and
used at section 2.2: level-hood is used at Σ₁ strength, so the delivered
`Σ₁-levelHood` is the right grade and `[LJ-1.2]`'s Δ₀ NO-GO does not bite.

`_build/literature/dev2.txt`: **NOT opened.** Every citation is through the
digest. `dev/literature/devlin-errata.md`: **NOT read**, on `[LJ-1.136]`'s
measurement that the errata touch no part of II.5.

## 9. C-39: WHAT A PROHIBITION CLOSED, AND WHAT IT DID NOT

**The brief's prohibitions cost me nothing, and I say so plainly rather than
inventing a complaint.**

- **"Do not build `CrossOut`."** Correct, and I obeyed it. The gate needed one
  leg and I built one leg.
- **"Do not touch the three `*Agree` masters."** Correct, and it cost nothing.
  I read their `README.md` and their headers only, and that reading is what
  section 2.2 uses to say the remaining adequacy is a delivered SHAPE.
- **"A NO-GO is a complete answer."** This line changed how I worked. I looked
  for the NO-GO FIRST, at `countFo`, before writing any transfer, and the
  answer arrived in one grep of the master's own comment at
  `src/L/Condensation.lagda.md:439-440`.

**The one line I would add to the next brief, offered and not assumed.** The
brief named `Σ₁-cert` as "ONE delivered `Σ₁` certificate", which it is. **It is
not the certificate `CrossOut` consumes.** `LevelHood.Σ₁-levelHood`
(`src/L/BoundedSubset.lagda.md:145-146`) is. **The gate is still answered,
because block 1 is generic and takes either certificate as an argument**, but a
brief that named the level-hood certificate would have put block 3 on the
critical path with its own budget, instead of leaving it as my spare
measurement that then walled.

**And that is the honest shape of this return.** The gate is a clean GO at 20
lines. **The thing the gate lets through is not yet reachable in one process,
and I found that out only because I spent the spare measurement.** A brief that
gates a transfer should say which certificate the phase will actually feed it.
