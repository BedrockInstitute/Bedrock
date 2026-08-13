# L3.31-LS lesson-backlog dossier (read-only audit)

**Date:** 2026-08-03. **Auditor:** L3.31-LS (sweep agent). **Scope:** the R5-B
execution record's "filed at discharge" backlog, the kernel batches (D1, D2,
K1-K4), the other R5-era reports, the two named R3-era reports
(r3a-walls, reshape), and the residual lesson language in any other
`_build/*-report.md`. **Deliverable:** this file. Nothing else was written;
no Agda ran; `dev/LESSONS.md` was not touched.

## 1. The promise being audited

`dev/PLAN.md:849` (the L3.31 row, execution record):

> Lesson backlog (probe 4, G1G6 4, G2 6, bridge 2, part-M 2) files at
> discharge.

The same row records the kernel batches and their flags: "its D-10 audit
clearing three mines", "the base block is registered as its own new residue",
"law I-5 minted from its six one-cause walls", and the K4 verdict. The kernel
reports (k1-k4) all label their sections "Lesson candidates (IDs to be
assigned by the owner)" (`_build/k1-report.md:92`, `k2-report.md:217`,
`k3-report.md:269`, `k4-report.md:314`).

**Sources swept.** The scratchpad finals with R5-era or K-era goal codes
(`g2p-final.md:19` and `g1g6-final.md` list the same candidates as their
`_build` report twins; `k1-final.md:27-29` lists K1's; `kernel-recon-final.md`
carries no new candidates and cites r5d1's), the R5-era recons
(`recon-a-final.md`, `recon-b-final.md`, `routeb-recon-final.md`, and the
`r5recon-*`/`kernel-recon.md` reports, which flag no new candidates), the ten
named `_build` reports, and every other `_build/*.md` mentioning "lesson".
The table below quotes the `_build` reports, the detailed record; the
scratchpad finals are noted where they are the discharge claim.

## 2. The law book as it stands

`dev/LESSONS.md` holds 72 entries (P-a..P-i 9, R-series 34, T-1/T-2 2, I-1..I-5
5, D-1..D-10 10, C-1..C-12 12). The last entry ever filed is **I-5**, minted
with the K3 commit `9c379eb` (2026-08-03 15:42), which adds exactly that one
entry (`git show 9c379eb -- dev/LESSONS.md`). `git log --follow --
dev/LESSONS.md` shows no later commit. Therefore nothing from D1, D2, K1, K2,
K4, or any R5-B batch was filed as an entry, and no measured datum was
appended to any existing entry after I-5.

## 3. Count arithmetic: the named 18 vs the reports

The record's "4+4+6+2+2 = 18" does **not** match what the reports flag:

| batch | record claims | report flags | delta |
|---|---|---|---|
| probe (R5-G2p) | 4 | 4 (`g2p-report.md:206-229`) | 0 |
| G1G6 | 4 | 4 (`g1g6-report.md:151-179`) | 0 |
| G2 | 6 | 6 (`g2-report.md:211-285`) | 0 |
| bridge | 2 | 3 (`g3g4g5-report.md:253-276`) | +1 |
| part-M | 2 | 4 (`g3g4g5-report.md:420-434`) | +2 |
| **named total** | **18** | **21** | **+3** |

The kernel batches flag 37 candidate-claims (D1 4, D2 10, K1 5, K2 4, K3 7,
K4 7; K2's fifth list item is an asset note, "⌜⌝-inj has its second consumer",
`k2-report.md:241`, not a rule-claim), of which exactly one (K3's branch-type
rule) was filed, as I-5.

## 4. Candidate table

Columns: source (`file:line`), quote (trimmed), classification, proposal.
Classifications: **COVERED** (entry already states it; cited), **FILE-NEW**
(no entry covers it; proposed entry listed as P-xx), **MERGE-INTO** (entry
covers the mechanism; datum worth appending; cited), **INFO** (measurement or
registration, no rule to file; excluded from the covered/new/merge tally).
Proposed-entry letters are provisional; the owner assigns final IDs.

### A. The named R5-B backlog (21 claims)

| # | source | quote | class | proposal |
|---|---|---|---|---|
| A-01 | `_build/g2p-report.md:208` | "LC-1: price decode-uniqueness once per arity, not per clause... a shared `DecK-unique` lemma (R-36 pattern) removes it from every clause." | FILE-NEW | → P-D-11 with A-09 |
| A-02 | `_build/g2p-report.md:211` | "LC-2: the hProp `⊓` carrier is a dependent `Σ`, untruncated. Consuming a spec's hProp-⊓ codomain needs no `PT.rec`." | FILE-NEW | → P-I-6 with B-15 |
| A-03 | `_build/g2p-report.md:214` | "LC-3: the domain operation's native projection is convention-dependent... which coordinate that is depends on the tuple nesting." | FILE-NEW | → P-D-12 with A-10 |
| A-04 | `_build/g2p-report.md:219` | "LC-4: the pure-variable satisfaction fragment is constructive and transitivity-free. No LEM and no `Utrans`... Keeps the G2 telescope honest." | FILE-NEW | → P-R-39 |
| A-05 | `_build/g1g6-report.md:157` | "Lesson candidate: 'membership-monotonicity of a union-of-extensions family is a family-member argument, not an induction'." | FILE-NEW | → P-D-16 |
| A-06 | `_build/g1g6-report.md:162` | "Lesson candidate: annotate `∈∈ₛ` direction usage in the style sheet." | FILE-NEW | → P-C-14 (low) |
| A-07 | `_build/g1g6-report.md:165` | "`∈sucV-elim`'s motive must live in `Type (ℓ-suc ℓ)` (P-series): the not-a-successor branches needed the `⊥*`/`rec*` lift pattern." | FILE-NEW | → P-I-7 with B-35, E-01 |
| A-08 | `_build/g1g6-report.md:170` | "Lesson candidate: spell `P` and the path endpoints explicitly in block equalities" (four early subst-direction flips). | FILE-NEW | → P-C-13 with E-04, E-13 |
| A-09 | `_build/g2-report.md:213` | "LC-G2-1... State two-way adequacy AT A TUPLE... the probe's negation clause 56 lines → 7 lines arity-generic (16x); zero `pr-inj` chases." | FILE-NEW | → P-D-11 |
| A-10 | `_build/g2-report.md:224` | "LC-G2-2. Under de Bruijn binding the quantified coordinate is the tuple's HEAD... the same choice fixes which of `F3`/`F4` does the atom plumbing. Refines the probe's LC-3." | FILE-NEW | → P-D-12 |
| A-11 | `_build/g2-report.md:233` | "LC-G2-3. The diagonal of a transitive rud-closed level is constructible from the basis... equality atoms need no new operation and no syntactic elimination of `≐`." | FILE-NEW | → P-D-13 with C-08 |
| A-12 | `_build/g2-report.md:252` | "LC-G2-4. Recurse on the ARITY, never permute coordinates." | FILE-NEW | → P-D-14 |
| A-13 | `_build/g2-report.md:261` | "LC-G2-5. One abstract binary-relation interface, instantiated at a relation and at its converse, yields both atom kinds from one recursion." | FILE-NEW | → P-D-15 |
| A-14 | `_build/g2-report.md:271` | "LC-G2-6 (process). The first-formulation discipline held... ten incremental checks, every one green on first submission... no wall." | MERGE-INTO | I-4 (`dev/LESSONS.md:1062`) already names the protocol; append the 1,285-line datum |
| A-15 | `_build/g3g4g5-report.md:255` | "D-10 extension... price the truth of the recorded target's index translation too. The r5recon's `Lset α ≡ Jset (b α)` is false at `α = 1`... made a 100-180 line chapter unnecessary." | MERGE-INTO | D-10 (`dev/LESSONS.md:1105`); append the index-translation datum |
| A-16 | `_build/g3g4g5-report.md:265` | "New (D-series candidate): a self-containing operator's junk is junk only relative to the tower reading it... choose the carrier by *what it can contain*." | FILE-NEW | → P-D-19 |
| A-17 | `_build/g3g4g5-report.md:272` | "P-i [A] as a prophylactic, second datum after R5a's... 40 s total with zero walls." | MERGE-INTO | P-i [A] (`dev/LESSONS.md:200`) |
| A-18 | `_build/g3g4g5-report.md:421` | "P-i layer cap, first hypothesis-type instance. 44 s → 90 s → 44 s across four exposed `Lset ∘ sucV` layers... a *hypothesis type in a module telescope* is enough." | MERGE-INTO | P-i [B] layer-cap sub-rule |
| A-19 | `_build/g3g4g5-report.md:424` | "A hypothesis must be priced for dischargeability, not just for truth... `F3`/`F4` nest two pairs." | MERGE-INTO | D-10; sibling rule, append |
| A-20 | `_build/g3g4g5-report.md:427` | "Reformulating the target can delete a chapter... the induction is 149 lines and mentions no arithmetic; the block-indexed version would have needed the missing dichotomy." | MERGE-INTO | D-10 |
| A-21 | `_build/g3g4g5-report.md:430` | "Mandated-first-formulation paid negatively... Recording *why* a proposed route cannot close is cheaper than trying it, when the obstruction is an index arithmetic mismatch." | MERGE-INTO | D-10 |

### B. The kernel batches (37 claims)

| # | source | quote | class | proposal |
|---|---|---|---|---|
| B-01 | `_build/r5d1-report.md:230` | "D-10 extension: price the residue's WITNESS, not only its statement... both failures... were invisible in the statement of the residue itself." | MERGE-INTO | D-10 |
| B-02 | `_build/r5d1-report.md:239` | "New (D-series candidate): a closure fragment cannot live inside the block it closes... the base block of every rud-versus-Def statement is a separate theorem with a finiteness proof." | FILE-NEW | → P-D-20 (also cited by `kernel-recon.md:107,113`) |
| B-03 | `_build/r5d1-report.md:246` | "The equivalence test for a reduction. Before reporting a residue as a reduction, check whether the residue implies the target *and* the target implies the residue." | FILE-NEW | → P-D-21 with B-34 |
| B-04 | `_build/r5d1-report.md:252` | "The probe as the type check. A scratchpad module that applies the consuming module... caught exactly the class of drift a same-wave sibling can cause." | FILE-NEW | → P-C-17 with B-36 |
| B-05 | `_build/r5d2-report.md:221` | "A 'Δ₀ wall' that was never a wall: price the *face*, not the shape... the consumer is `𝒟ₒ`, whose formulas are **unrestricted**... one 36-line equality frame plus a 165-line pair kit." | MERGE-INTO | D-10 |
| B-06 | `_build/r5d2-report.md:232` | "The inner semantics is directly workable, and nothing in the tree had tried it... `defSet-mem` is used at face value." | FILE-NEW | → P-D-22 with B-13, B-27 |
| B-07 | `_build/r5d2-report.md:238` | "A residue's hypothesis list is part of its truth... the missing datum is... a *parameter of the ambient module* that the formula must name." | MERGE-INTO | D-10 |
| B-08 | `_build/r5d2-report.md:245` | "I-4 confirmed on first contact. `↾-reflects` at the restricted structure left its class implicit and never solved... one-line instance of the recorded rule." | COVERED | I-4 (`dev/LESSONS.md:1062`) |
| B-09 | `_build/r5d2-report.md:250` | "P-i [A] again, third datum... 47.8 s for a 1,200-line file..." | MERGE-INTO | P-i [A] |
| B-10 | `_build/r5d2-report.md:417` | "P-i [F], first instance in this chapter... a formula index is a huge argument even when the formula itself is small, once it sits under a satisfaction head." | MERGE-INTO | P-i [F] (`dev/LESSONS.md:220`) |
| B-11 | `_build/r5d2-report.md:427` | "The junk of a total projection is describable without a case split, if you describe the definition instead of the cases... Sibling of D-2." | FILE-NEW | → P-D-23 with C-12 |
| B-12 | `_build/r5d2-report.md:436` | "A shared frame is worth writing even for four consumers. `tupleOut`/`tupleIn` (40 lines)..." | FILE-NEW | → P-C-19 |
| B-13 | `_build/r5d2-report.md:442` | "The methodological headline of part 1 held all the way to the theorem. No Δ₀ witness was constructed anywhere..." | FILE-NEW | → P-D-22 |
| B-14 | `_build/r5d2-report.md:402` | P5: "`left`/`right`... in **statement** positions... at 170 s... seal `leftOf`/`rightOf` aliases opaque in this file (R-36 shape, ~20 lines)." | MERGE-INTO | R-38 (`dev/LESSONS.md:771`); statement-position datum |
| B-15 | `_build/k1-report.md:94` | "The hProp-join double-truncation trap (extends I-2): `⟨ P ⊔ Q ⟩` is already the truncation `∥ ⟨ P ⟩ ⊎ ⟨ Q ⟩ ∥₁`... `PT.rec` double-truncates." | FILE-NEW | → P-I-6 |
| B-16 | `_build/k1-report.md:101` | "Step's `f0..f15` aliases are definitions, not constructors: using them as enumeration patterns fails... Extends the P-a tag-discipline family." | MERGE-INTO | P-a (`dev/LESSONS.md:32`) |
| B-17 | `_build/k1-report.md:104` | "`Sset-zero` is not exported by `L.Rud.Step`... costing a 6-line local proof (`Sset-zero-∅`). Candidate: export it from Step." | FILE-NEW | → P-C-15 with C-13 |
| B-18 | `_build/k1-report.md:108` | "R-35/P-c applied before a wall (second instance of R-38's prophylactic datum)... whole chapter ran at 1.3 s warm with no wall event." | MERGE-INTO | R-38 |
| B-19 | `_build/k1-report.md:113` | "R-37 held: no lemma statement carries a transported membership at a concrete `Sset (sucV β)`." | COVERED | R-37 (`dev/LESSONS.md:793`) |
| B-20 | `_build/k2-report.md:219` | "D-series (new): a family indexed by an inductive type is cofinal, so 'member at a finite offset' is never its target... transitivity of the levels refutes every finite offset." | FILE-NEW | → P-D-24 with B-32 |
| B-21 | `_build/k2-report.md:227` | "D-10 sub-rule: calibrate against a retiring chapter's transitive closure, not its file... the honest figure is 3-4x." | FILE-NEW | → P-D-25 with B-26 |
| B-22 | `_build/k2-report.md:231` | "R-35 positive datum. The small-indexed `sett` over external syntax gave both membership directions definitionally... at 45 lines and zero walls." | MERGE-INTO | R-35 (`dev/LESSONS.md:737`) |
| B-23 | `_build/k2-report.md:236` | "A reduction is a deliverable... it should be treated as the standing shape for 'named and left standing'." | FILE-NEW | → P-D-26 |
| B-24 | `_build/k3-report.md:271` | "R-series, sharpened: write the branch type... any elimination branch whose type is inferred... gets a named `where` function with a written type." | COVERED | I-5 (`dev/LESSONS.md:1045`), filed at `9c379eb` |
| B-25 | `_build/k3-report.md:278` | "A wall that survives the obvious seal is a mis-diagnosis, and the seal should be reported as unmeasured... after a seal fails to move a wall, **stop sealing and start bisecting**." | FILE-NEW | → P-C-20 |
| B-26 | `_build/k3-report.md:283` | "D-10 sub-rule, second instance: a re-price that omits a construction is wrong by that construction... the introduction has been the larger half twice." | FILE-NEW | → P-D-25 |
| B-27 | `_build/k3-report.md:290` | "The inner world's second dividend: an imported pair kit... this chapter imported it whole and spent **zero** lines on the `Base`-class apparatus." | FILE-NEW | → P-D-22 |
| B-28 | `_build/k3-report.md:297` | "A twelve-way disjunction should be a fold over `ℕ`, not a right-nested chain of injections... 188 lines... against `Shape`'s 354." | FILE-NEW | → P-D-27 |
| B-29 | `_build/k3-report.md:304` | "P-i [A], third datum... 1,347 lines, 9.5 s cold, no heap event." | MERGE-INTO | P-i [A] |
| B-30 | `_build/k3-report.md:310` | "R-16 datum: environments spelled out, and the rent was low... paid in lines, not in seconds: roughly 60 lines." | MERGE-INTO | R-16 (`dev/LESSONS.md:525`) |
| B-31 | `_build/k4-report.md:316` | "D-10, sharpened: a residue's INDEX can be refuted by the theorem the residue serves... the refuting instance... is only satisfiable **under the conclusion of the very induction the residue feeds**." | MERGE-INTO | D-10 |
| B-32 | `_build/k4-report.md:325` | "A cofinality recorded as 'a fact about the target' may be a fact about the encoding... A flat coding has all codes of bounded rank and no cofinality at all." | FILE-NEW | → P-D-24 (corrects B-20's generalization) |
| B-33 | `_build/k4-report.md:332` | "The identity fragment is the native shape, twice... before building the machinery a two-sided approximation needs, check whether the approximation's own target is the witness." | FILE-NEW | → P-D-28 |
| B-34 | `_build/k4-report.md:338` | "The equivalence test, applied as standing practice. r5d1 proposed it; this batch ran it on its own residue (`fragment`/`pow-from-fragment`, 4 lines)." | FILE-NEW | → P-D-21 |
| B-35 | `_build/k4-report.md:342` | "`∈sucV-elim`'s motive is pinned at `ℓ-suc ℓ`, so `Empty.⊥` cannot be the target of an ordinal contradiction... must land in `Empty.⊥* {ℓ-suc ℓ}`." | FILE-NEW | → P-I-7 |
| B-36 | `_build/k4-report.md:347` | "A close-out module beats a close-out probe, and then the probe still earns its keep... Recommend both, in that order." | FILE-NEW | → P-C-17 |
| B-37 | `_build/k4-report.md:352` | "P-i [A] datum, and a cheap-chapter datum... **none of the conversion machinery fires when the chapter's own content is set-level identities at abstract carriers**." | MERGE-INTO | P-i [A] |

### C. Other R5-era reports (16 claims: r5a 10, r5b 6)

| # | source | quote | class | proposal |
|---|---|---|---|---|
| C-01 | `_build/r5a-report.md:279` | "'Circular' was a scoping artefact, not a fact... Candidate rule: when two routes to a base case are circular, the finding to record is 'two routes are circular', never 'the base case is circular'." | FILE-NEW | → P-C-22 |
| C-02 | `_build/r5a-report.md:289` | "(design, new) Choose the induction carrier by which operations are homomorphic." | COVERED | D-9 (`dev/LESSONS.md:1090`), filed at `4eb9604` |
| C-03 | `_build/r5a-report.md:297` | "(measured, R-38 confirmed prophylactically) Sealing at birth kept a 731-line tower-heavy file at 2.8 s." | COVERED | R-38, datum already appended |
| C-04 | `_build/r5a-report.md:308` | "(craft) The tuple calculus has exactly three moves, and naming them dissolved the design work." | FILE-NEW | → P-D-29 |
| C-05 | `_build/r5a-report.md:317` | "(inference trap, minor, extends I-2/I-4) `dne` is at level `ℓ`, so structure-level memberships must be bridged." | FILE-NEW | → P-I-8 |
| C-06 | `_build/r5a-report.md:475` | "The transparent Images kit has an invocation cost, not only a sealing hazard... `right-spec a b` costs **25.7 s**... while its sibling `left-spec a b` costs **64 ms**... paying it exactly once." | MERGE-INTO | R-38 |
| C-07 | `_build/r5a-report.md:488` | "P-i [A], measured again: the obvious cheaper replacement is worse, and walls... file went from 30 s to **killed past 600 s**." | MERGE-INTO | P-i [A] |
| C-08 | `_build/r5a-report.md:497` | "In this tuple calculus the identity graph is the only permutation primitive... A calculus of this shape should build its diagonal first." | FILE-NEW | → P-D-13 |
| C-09 | `_build/r5a-report.md:508` | "(estimation) Per-clause cost is ambient-set bookkeeping... price roughly 3 lines of bookkeeping per line of content." | MERGE-INTO | D-6 (`dev/LESSONS.md:1012`); PLAN.md:849 calls it a "D-6-family calibration datum" |
| C-10 | `_build/r5a-report.md:514` | "(craft, confirming part 1's item 2) The carrier principle held to the end." | COVERED | D-9 |
| C-11 | `_build/r5b-report.md:260` | "(D series, new) A closure hypothesis on the carrier is worth more than a description chapter... Rule: before instantiating a delivered description at a carrier, ask whether the carrier's own closure already puts the value inside it." | FILE-NEW | → P-D-17 |
| C-12 | `_build/r5b-report.md:273` | "(D series, new) The junk branch you feared may not exist: read the operation before the specification." | FILE-NEW | → P-D-23 |
| C-13 | `_build/r5b-report.md:284` | "(C series, new) A three-times-restated helper is a delivery defect, not a coincidence." | FILE-NEW | → P-C-15 |
| C-14 | `_build/r5b-report.md:294` | "(reading of the R3 residue, corrected) A residue can be stated at a target that is false... when a batch records a residue, record the *statement* it intends, and price its truth before the next batch prices its proof." | COVERED | D-10, filed with this provenance |
| C-15 | `_build/r5b-report.md:303` | "(craft) Generalizing a working frame from 'at the free variable' to 'at an index' cost nothing and bought the hardest two operations." | FILE-NEW | → P-C-16 |
| C-16 | `_build/r5b-report.md:314` | "(measurement) The classical spend of this chapter is one, and it is in the last case." | INFO | measurement datum (D-7-adjacent); no rule to file |

### D. The named R3-era reports (6 claims)

| # | source | quote | class | proposal |
|---|---|---|---|---|
| D-01 | `_build/r3a-walls-report.md:250` | "(new, P series) An implicit that must be inverted through `⟨_⟩` is a blocked constraint, not an error..." | COVERED | I-4 (provenance `r3a-walls-report.md`) |
| D-02 | `_build/r3a-walls-report.md:260` | "(new, D or P series) State a subset-of-`u` characterization at the restricted carrier `SM`..." | COVERED | I-4 (restricted-carrier clause) |
| D-03 | `_build/r3a-walls-report.md:267` | "(new, P-i [E] instance) A bounded quantifier over a transitive `u` ranges its image over `u`..." | COVERED | I-4 (companion-reshape clause) |
| D-04 | `_build/r3a-walls-report.md:274` | "(amendment to P-h, measured counter-instance) Face abstraction is not a cure for a conversion wall by itself." | COVERED | I-4 (B/C delta recorded there) |
| D-05 | `_build/r3a-walls-report.md:281` | "(craft) The `map fst` formulation of the witness stack makes the term view's weakening law three `refl` clauses." | FILE-NEW | → P-C-23 (low) |
| D-06 | `_build/reshape-report.md:182` | "Note for the lesson book (not filed; out of scope)... worth a **D-series** entry... A step operator that contains its own argument cannot be monotone in the subset order; state its monotonicity conditioned on membership." | COVERED | D-8 (`dev/LESSONS.md:1121`), filed with `reshape-report.md` in its provenance |

### E. Pre-R5 residuals found by the "any *-report.md mentioning lesson" sweep

These are older-wave candidates (R1-R4 era, L3.29/L3.30) never filed; the
remaining pre-R5 candidates in those reports were filed by their own batches
(I-2, I-3, D-7, D-8, R-35, R-36, R-37, R-38, P-i, C-11, C-12...).

| # | source | quote | class | proposal |
|---|---|---|---|---|
| E-01 | `_build/r2b-report.md:190` | "`∈sucV-elim`'s motive lives at `Type (ℓ-suc ℓ)`, so a refutation motive must be `⊥* {ℓ-suc ℓ}`..." | FILE-NEW | → P-I-7 (duplicate of A-07/B-35) |
| E-02 | `_build/r1b-report.md:93` | "Unsolved constraints report as `error: [UnsolvedConstraints]` with exit 42 while the log tail otherwise looks like a clean check. Always read the exit code, not the tail." | FILE-NEW | → P-C-24 (low) |
| E-03 | `_build/r2a-report.md:98` | "before LEM can decide a witness-shaped proposition, verify at-most-one witnesses; injectivity is often the missing lemma." | FILE-NEW | → P-I-9 (low) |
| E-04 | `_build/r2a-report.md:111` | "when transporting a membership with a fixed left argument, the path must run in the second argument, i.e. `sym` of the equality as stated." | FILE-NEW | → P-C-13 (duplicate of A-08) |
| E-05 | `_build/r2c-report.md:468` | "a private helper that a consumer's proof needs must be re-exported as a public lemma; privacy is a name-and-reduction wall, not just a hygiene marker." | FILE-NEW | → P-C-27 |
| E-06 | `_build/r2c-report.md:711` | "an opaque index family wants a small block of unfolding equalities next to it, as the operation index's official interface." | MERGE-INTO | R-36 |
| E-07 | `_build/r3b2-report.md:186` | "when a seal is exposed by a read, the read's direction is a public interface choice, and a consumer that needs both directions must state the reverse read as its dependency." | MERGE-INTO | R-36 |
| E-08 | `_build/r3c-report.md:316` | "(craft) A path lambda is a normalization request. `λ i → op (p i) (q i)`... forces `op` to whnf at both ends." | FILE-NEW | → P-P-j |
| E-09 | `_build/r3c-report.md:321` | "(D series, new) An exported theorem that hides a certificate its only consumer needs is an interface bug... transparency of a syntax-directed recursion is an interface asset; seal the heavy *values*, not the syntax walk." | FILE-NEW | → P-D-30 |
| E-10 | `_build/p1-report.md:150` | "Where-clauses do not see a signature's implicit arguments unless re-bound in the function's own patterns." | FILE-NEW | → P-C-28 (low) |
| E-11 | `_build/r2b-report.md:178` | "never write `∈ˢ ⋃` / `⊆ ⋃` directly; always bind the union term." | FILE-NEW | → P-C-25 (low) |
| E-12 | `_build/r2b-report.md:166` | "telescope types may only use level-generic imported names; any level-parameterized predicate must be inlined into the header..." | FILE-NEW | → P-C-26 (low) |
| E-13 | `_build/r2c-report.md:898` | "`subst` direction discipline, third occurrence... the pattern is now stable in the report and should be checked by..." | FILE-NEW | → P-C-13 (duplicate of A-08) |

## 5. Proposed FILE-NEW entries (drafts in the book's measured style)

Series letters and IDs are provisional; the owner assigns final IDs.

**P-D-11. State two-way adequacy at a tuple, not at a member.** Rule: quantify
adequacy over the environment, never over a member, so the equation
`m ≡ Tup n δ` never appears in a clause; recover the member-level pair once
through a subset lemma (`T-sub`). Measured: the probe's 56-line negation clause
became 7 lines arity-generic (16x), zero `pr-inj` chases in twelve clauses,
total adequacy 245 lines both directions (G2, 2026-08-03). This is the
tuple-level restatement of "price decode-uniqueness once per arity".

**P-D-12. The quantified coordinate is the tuple's head; fix the convention by
the projection.** Rule: under de Bruijn binding the quantified coordinate is
the tuple's HEAD, so the tuple convention is fixed by which projection the
quantifier needs, and the same choice fixes which of F3/F4 does the atom
plumbing. Measured: one 41-line range operation amortised over four consumers
bought the coordinate families free; the probe's F6-only reading of the fork
got the sign backwards (G2, 2026-08-03).

**P-D-13. Build the diagonal first; it is the only permutation primitive.**
Rule: in the tuple calculus F3 inserts after the first coordinate, F4 appends
a block at a pair's end, `ranOp` strips the leading coordinate, and none moves
a coordinate left past another; the identity graph pays for every such move,
so build it first and treat it as the coordinate-permutation primitive. Measured:
the equality atom needs no foundation axiom and no `≐`-elimination: diagonal
130 lines, converse 30, self-membership slice 30, all from extensionality plus
the range (G2); R5a-2 then spent the identity graph five times (2026-08-03).

**P-D-14. Recurse on the arity, never permute coordinates.** Rule: an atom
relating two coordinates of an (n+1)-tuple splits four ways on whether each
index is the head: both past the head is a cylinder one arity down; head
against a later coordinate is the F3-insertion family; the converse is the
same family at the converse relation; both at the head is the diagonal slice.
Measured: `LR` 3 clauses, `Bin` 5, `Sel` 3; the whole k-ary plumbing 211 lines
with no permutation lemma (G2, 2026-08-03).

**P-D-15. One abstract binary-relation interface at a relation and its
converse.** Rule: a module generic in a relation (membership plus in/out) gives
the insertion family; instantiating it at a relation, its converse and the
diagonal slice covers both atom kinds from one recursion. Measured: 169 lines
of shared machinery covering 2 atom relations x every index pair, versus a
per-relation build that would have doubled it (G2, 2026-08-03).

**P-R-39. State the satisfaction telescope at the fragment that consumes it.**
Rule: keep a satisfaction telescope honest by the fragment: the pure
atom/negation/existential core is constructive and transitivity-free (JU + Jrud
only); Utrans enters at parameter atoms and bounded quantifiers, UmemInJ at
`con c` atoms. Measured: the probe's three clauses plus adequacy in 286 lines,
1.8 s cold, zero Utrans uses (G2p, 2026-08-03).

**P-I-6. hProp connective carriers come pre-shaped; consume at the carrier
level.** Rule: the library connectives' carriers are not opaque: `⟨ P ⊔ Q ⟩`
is already `∥ ⟨ P ⟩ ⊎ ⟨ Q ⟩ ∥₁` and an hProp `⊓` codomain is an untruncated
dependent Σ; consume them at the carrier level (apply the join-valued function
directly and do the `PT.rec` at the plain-sum level, or project the pair), never
wrap the result in another `PT.rec`. Measured: probe LC-2 (no `PT.rec` needed
at `⊓`); K1 lost three ~10 s checks to the double-truncation confusion
(2026-08-03). Neighbor of I-2, whose signature-side rule this consumption-side
rule completes.

**P-D-16. Membership-monotonicity of a union-of-extensions family is a
family-member argument.** Rule: for a single-equation family
`b α = ⋃ { +ω (b δ) | δ ∈ α }`, membership monotonicity is a family-member
argument, not an induction: the block at β is a member of its own ω-extension,
which is a member of the family b α unions over. Measured: `b-mono` holds for
every pair of indices, constructively, with no ordinality; laws 1-26 lines
each, module 45.6 s cold (G6, 2026-08-03).

**P-C-13. Subst direction discipline: spell P and the path endpoints.** Rule:
`subst P p` moves `P x → P y` along `p : x ≡ y`; in membership rewrites decide
whether the path acts on the element or the level, and spell `P` and both
endpoints in block equalities. Measured: four early flips in G6, two
`sym`-direction errors in R2a, the stable pattern in R2c's twelve trans cases
(2026-08-02/03).

**P-C-14. Annotate the small/big membership conversion direction.** Rule: the
small/big membership equivalence (`a ∈ b ⇔ a ∈ₛ b`) has `.fst` big-to-small and
`.snd` small-to-big; annotate the direction usage in the style sheet. Measured:
one fibre step in `+ω-out` was written the wrong way and only the error text
exposed it (G6, 2026-08-03).

**P-I-7. Refutations through `∈sucV-elim` land in `⊥*` at `ℓ-suc ℓ`.** Rule:
`∈sucV-elim`'s motive lives at `Type (ℓ-suc ℓ)`, so an ordinal no-go
eliminated through it must land in `Empty.⊥* {ℓ-suc ℓ}` with
`Empty.isProp⊥* {ℓ-suc ℓ}`, not `Empty.⊥`; the consumer is `Empty.rec*`.
Measured: G6's not-a-successor branches, R2b's refutation motive, K4's ordinal
contradiction, three occurrences, one of K4's three errors (2026-08-02/03).

**P-D-19. Junk is junk only relative to the tower reading it.** Rule: a value
class is junk or not relative to the tower that reads it: the rud step's
level-slot junk is irreducible against the rud level (which cannot contain
itself) and evaporates against the Def tower the moment a stage holds the level
as a member. Measured: `Ljunk` 11 lines, a two-case split, where LevelDesc
spends ~700 lines on the same level cases; choose the carrier by what it can
contain, a sibling of D-9 (G3G4G5, 2026-08-03).

**P-D-20. A closure fragment cannot live inside the block it closes.** Rule:
any bounding object asked to be closed under the sixteen operations is infinite
(singletons), so it is never a member of the first rud level `Sset ω`, whose
members are all finite; the base block of every rud-versus-Def statement is a
separate theorem with a finiteness proof, and no offset engineering merges it
with the general case. Measured negatively: it removed a planned 150-line layer
(D1, 2026-08-03); the kernel recon registered the base block as its own residue.

**P-D-21. Before reporting a reduction, apply the equivalence test.** Rule:
before reporting a residue as a reduction, check whether the residue implies
the target *and* the target implies the residue; a failure means the product is
a chain around a weakening, not a reduction. Measured: `DefFragment` passes
(one line of reasoning, licensing the trade); K4 ran it on
`fragment`/`pow-from-fragment` in 4 lines (r5d1, K4, 2026-08-03).

**P-C-17. Close out with a consumer probe; the module beats the probe, then the
probe still earns its keep.** Rule: for any batch that exports into a fixed
telescope, apply the consuming module inside the exporting chapter (making the
telescope match a typechecking obligation), then run the scratchpad probe,
since it is the only place the module parameters get concrete. Measured: the
25-line `Bridge.Reduce` probe caught `f3ad704`'s mid-batch telescope change in
1.7 s; K4's in-file application plus probe exercised `slot-empty` at `A := ∅`
(2026-08-03).

**P-D-22. The inner semantics is the working face; Δ₀ absoluteness is a
crossing tax only.** Rule: write readers and formulas in the inner semantics at
an abstract transitive carrier; Δ₀ is needed only when a proof crosses between
the ambient and the inner reading, and inner-world readers are reusable across
chapters because they carry no absoluteness obligation. Measured: the
Graphs-class re-run estimate (~1k lines, the G2 wall class) became 2,124 lines
of ordinary reading work with zero walls; the pair kit imported whole cost zero
lines against 187; no Δ₀ witness was constructed anywhere (D2, K3,
2026-08-03).

**P-D-23. Read the definition, not the case analysis.** Rule: describe a total
projection (or an operation's junk) through its definition, not the case
analysis that motivated it: `left b = ⋃ (⋂ b)` has one equality frame over the
intersection's two-clause membership, and an operation whose members are pairs
definitionally needs no pairhood split. Measured: 30 lines of formula and
adequacy against an estimated 90, removing two of three junk readings; F11-F14
at four operations cost zero case splits (r5d2, r5b, 2026-08-03).

**P-C-19. A shared frame is worth writing even for four consumers.** Rule:
write the shared tuple frame even for a handful of consumers: one 40-line
`tupleOut`/`tupleIn` pair turned four arms that each needed the projection
descriptions, their adequacy and carrier memberships into four arms that needed
only the value's shape. Measured: the four arms stayed the largest block (303
lines) even so, which prices what the frame saved (D2, 2026-08-03).

**P-C-15. A restated helper or a missing export is a delivery defect.** Rule: a
helper written a third time, or a case equation the definition site fails to
export, is a delivery defect, not a coincidence: host the arbitrary-domain
reader once and export the bottom equation at the definition site. Measured:
`prAt′` written three times (57 lines, no risk, the third copy the signal);
`Sset-zero` missing from Step's exports cost a 6-line local proof at the base
block (r5b, K1, 2026-08-03).

**P-D-24. Cofinality audits: count rank growth per member, then decide where
the ranks come from.** Rule: before pricing a "gather the family as one set"
residue at a finite offset, count the constructor cost per member; if rank
grows with the index, transitivity refutes every finite offset and the
surviving target is a satisfaction obligation, not an arm obligation. When the
cofinality is then recorded as a fact about the target, check whether the ranks
come from the mathematics or the representation: nested-pair codes are cofinal
because one Kuratowski pair per formula layer grows rank with depth, and a flat
coding has bounded rank and no cofinality at all. Measured: K2 refuted the
finite-offset target in five minutes (193 lines for the corrected pair); K4
showed the cofinality is the coding's artifact, removable by rank-bounded codes
(2026-08-03).

**P-D-25. Price a port against the retiring tree's transitive closure, and
split both directions.** Rule: a "port the pattern" estimate is calibrated
against the retiring chapter's import graph, not its file, and every
both-directions adequacy estimate is split into elimination and introduction
and priced separately, because the introduction has been the larger half twice.
Measured: 250-450 became 3-4x against a 616-line chapter importing ~1,400 code
lines; K3's re-price omitted the 274-line witness-set construction (2026-08-03).

**P-D-26. A reduction is a deliverable.** Rule: when a residue cannot be
discharged, deliver the reduction: state the residue for an arbitrary target
with an extensional entry point (two containments at a variable member instead
of a set equation) and treat it as the standing shape for "named and left
standing". Measured: 30 lines; second instance of the
`DefFragment`/`Discharge` pattern (K2, 2026-08-03).

**P-C-20. A wall that survives the obvious seal is a mis-diagnosis.** Rule:
after a seal fails to move a wall, stop sealing and start bisecting the
elaboration; report the failed seal as unmeasured rather than retro-fitting
credit when the real cause is found. Measured: the textbook pr-seal was wrong
in K3, costing one full rewrite and three wall events before bisection found
the branch-type cause (2026-08-03).

**P-D-27. A many-way disjunction is a fold over ℕ, not a right-nested injection
chain.** Rule: a twelve-way disjunction should be a fold over ℕ
(`orUpto` by induction on the bound), not a right-nested chain of injections;
no truncation nests deeper than one. Measured: the twelve-way layer cost 188
lines including both meta-level translations, against Shape's 354 for the
disjunction alone (K3, 2026-08-03).

**P-D-28. Check whether the approximation's own target is the witness.** Rule:
before building the machinery a two-sided approximation needs, check whether
the approximation's own target is the witness: the identity fragment collapses
to `λ y k → k`, so the residue is a membership and the fragment formulation is
an indirection. Measured: both halves of the fragment collapse at ω and at
general limits (`powFragment`); removed `Sep`/`Sstage₂` from the general case
(BaseBlock, K4, 2026-08-03).

**P-C-22. Record "two routes are circular", never "the base case is
circular".** Rule: when two routes to a base case are circular, the finding to
record is "two routes are circular", never "the base case is circular"; the
third route is often the textbook's. Measured: R3c's recorded circularity was a
scoping artefact; the classical construction is extensionality relativized to
`p ∪ ⋃p`, 95 lines with one `dne` per direction (R5a, 2026-08-03).

**P-D-29. The tuple calculus has exactly three moves; name them.** Rule: the
tuple calculus has exactly three moves (F3 inserts a coordinate after the
first, F4 appends one at the end of a pair or a whole block with a product
argument, `ranOp` strips the leading coordinate); choose the coordinate order
in which the quantified variables lead, pad each constraint into the common
tuple space, intersect, strip. Measured: `swp` fell from a four-coordinate
design to a three-coordinate one, half the code (R5a, 2026-08-03).

**P-I-8. `dne` is at level ℓ; bridge structure-level memberships before
classical steps.** Rule: `Switch.dne` takes an `hProp ℓ` while `∈ˢ` lands in
`hProp (ℓ-suc ℓ)`, so every classical step on a structure-level membership goes
`∈s`, then `dne`, then `∈S`; invisible until the error appears. Measured:
`cap-outr` (not `cap-outl`) is the classical half, a one-line idiom (R5a,
2026-08-03).

**P-D-17. A closure hypothesis on the carrier is worth more than a description
chapter.** Rule: before instantiating a delivered description at a carrier, ask
whether the carrier's own closure already puts the value inside it: at a
rud-closed carrier the whole plain-argument half of `ImgArm` is `Jset-rud`
followed by `memArm`, one line per operation. Measured: 16 dispatch lines plus
a 12-line helper vs the anticipated several hundred (R5b, 2026-08-03).

**P-C-16. Generalize a working frame from the free variable to an index.**
Rule: when a frame works "at the free variable", generalize it to "at an index"
(the target term becomes `var k`, shifted by the binders) and keep the original
as the zero case; the generalization is a mechanical edit that buys every
deeper binder. Measured: `prDesc` → `prDescAt k` made F3/F4's six cases green
on the first check; all de Bruijn arithmetic lives in one 20-line definition
(R5b, 2026-08-03).

**P-C-23. The `map fst` formulation makes the weakening law `refl`.** Rule:
state the witness stack as `map fst` so the term view's weakening law is three
`refl` clauses: `lookup (suc j) (fst w ∷ map fst ws)` computes to
`lookup j (map fst ws)`. Measured: r3a needed `lookup-map` and a
`valSplit-suc` chain for the same fact (r3a-walls, 2026-08-03).

Pre-R5 residuals (drafts kept short; several are one-line conventions):

**P-C-24. Read the exit code, not the log tail.** UnsolvedConstraints exits 42
while the tail looks clean; always read the exit code (r1b).
**P-I-9. Verify at-most-one witnesses before LEM decides a witness-shaped
proposition.** `isSucc` forced `sucV-inj-ord` (27 lines), a gap the brief did
not list (r2a).
**P-C-27. A private helper a consumer's proof needs must be re-exported as a
public lemma.** Privacy is a name-and-reduction wall, not a hygiene marker;
`rightSlice`/`sndExtract` were unnameable and blocked F11-F14's junk facts
(r2c).
**P-P-j. A path lambda is a normalization request.** `λ i → op (p i) (q i)`
forces `op` to whnf at both endpoints; nine of ten `eval-agree` clauses were
free and the one fatal differed only in whether `op` was sealed (r3c).
**P-D-30. Transparency of a syntax-directed recursion is an interface asset.**
Seal the heavy values, not the syntax walk: `Realize`'s dropped certificates
were recoverable from outside in 78 lines only because the walk stayed
transparent (r3c).
**P-C-28. Where-clauses do not see a signature's implicit arguments unless
re-bound in the function's own patterns.** Explicitly bound pattern variables
are visible (p1).
**P-C-25. Never write `∈ˢ ⋃` / `⊆ ⋃` directly; bind the union term.** Agda's
mixfix parser rejects an infix operator applied to a prefix `⋃` operand (r2b).
**P-C-26. Telescope types may only use level-generic imported names.** Inline
level-parameterized predicates into the header, or take subject parameters in an
inner `module _` block (r2b).

## 6. Proposed MERGE-INTO sentences (one per target entry)

- **D-10** (`dev/LESSONS.md:1105`) — append: "Same-day extensions, all
  measured: price the recorded target's index translation (the block-translated
  `Lset α ≡ Jset (b α)` is false at α = 1); price a reduction's hypotheses for
  dischargeability and for nameability of every module parameter they
  implicitly quantify over (`values∈L` was underspecified by two nested pairs;
  `stepSet∈L` is not dischargeable until the telescope names A); price the
  residue against the interface that actually consumes it (Δ₀ was a crossing
  tax, not a wall); price the supplier's INDEX against the consumer's
  quantifier (the two-limit supplier fails at γ = ω·2, ζ = ω+3); and let a
  corrected target delete a chapter (the same-index restatement removed the
  block map and its missing dichotomy)."
- **P-i [A]** (`dev/LESSONS.md:200`) — append the five datums: prophylactic
  use before a wall (sixteen heavy modules at abstract carriers, 40 s total,
  G3G4G5); a 1,200-line abstract-carrier file at 47.8 s (D2); a 1,347-line
  predicate at a seven-fact telescope, 9.5 s cold (K3); set-level identities at
  abstract carriers fire none of the machinery, 246 lines at 1.9 s (K4); and
  the obvious cheaper replacement is worse when extensionality meets a tower
  built from cheap sealed parts (600 s kill, R5a-2).
- **P-i [B] layer cap** (`dev/LESSONS.md:228`) — append: "trigger widened: four
  exposed `Lset ∘ sucV` layers in a module HYPOTHESIS type doubled a file's
  check (44 s → 90 s) and one 18-line seal restored it; the layers need not be
  in a term (part M, 2026-08-03)."
- **P-i [F]** (`dev/LESSONS.md:220`) — append: "sub-case: a formula index is a
  huge argument even when the formula itself is small, once it sits under a
  satisfaction head (implicit φ ψ cost a 168 s check; explicit indices and
  fifteen named tails fixed it, D2)."
- **R-38** (`dev/LESSONS.md:771`) — append: "statement positions count:
  naming transparent `left`/`right` in a theorem statement cost 170.7 s cold
  (D2); an imported transparent operation can cost 25.7 s to invoke even at
  variable arguments and sealing only moves the cost, so the alias's job is to
  be the single site that invokes it (R5a-2); second prophylactic datum: the
  base block ran at 1.3 s warm with the discipline applied first (K1)."
- **R-35** (`dev/LESSONS.md:737`) — append: "first pre-wall syntax-indexed
  datum: the small-indexed sett over external syntax gave both membership
  directions definitionally in 45 lines (K2)."
- **R-16** (`dev/LESSONS.md:525`) — append: "datum: environments spelled out at
  fixed concrete arities cost ~60 lines in a 1,347-line chapter, and generic
  arities were not the wall source (probe 11 vs 13, K3)."
- **P-a** (`dev/LESSONS.md:32`) — append: "derived operation aliases
  (`f0..f15`) are not constructors: enumerating over them fails with
  `Op16.op0 != f0`; enumerate over the underlying constructors `op0..op15`
  (K1)."
- **I-4** (`dev/LESSONS.md:1062`) — append: "the mandated-first-formulation
  protocol then held a 1,285-line chapter: ten incremental checks, one
  scope-level fix, no formulation retry, no wall (G2)."
- **D-6** (`dev/LESSONS.md:1012`) — append: "family calibration datum:
  graph-style chapters price ambient-set bookkeeping at roughly 3:1 over
  content lines, not zero (R5a-2's clause table)."
- **R-36** (`dev/LESSONS.md:753`) — append: "the read's direction is a public
  interface choice, and a consumer needing both directions must state the
  reverse read as its dependency (r3b2); an opaque index family wants a small
  block of unfolding equalities next to it as its official interface (r2c)."

## 7. Summary counts

Primary scope (the named R5-B backlog + the kernel batches + the other R5-era
reports + the two named R3-era reports):

| metric | count |
|---|---|
| flagged candidate-claims found | **80** (79 rule-claims + 1 INFO) |
| COVERED | **12** |
| MERGE-INTO | **23** |
| FILE-NEW | **44** |

Distinct proposals: the 44 FILE-NEW rows collapse to **31 new entries** (plus 8
more from the pre-R5 residual sweep, 39 total), and the 23 MERGE-INTO rows
target **11 existing entries** (D-10, P-i [A], P-i [B], P-i [F], R-38, R-35,
R-16, P-a, I-4, D-6, R-36). Pre-R5 residual sweep adds 13 rows: 2 MERGE-INTO
(R-36), 11 FILE-NEW (3 of them duplicates of primary proposals; 8 genuinely
new, mostly low priority).

Within the five named batches alone: 21 claims found (not 18; bridge 3 and
part-M 4), of which 0 were filed as entries and 7 are mechanism-subsumed by
already-filed entries (the bridge's false-target catches and part M's
hypothesis/reformulation/route-pricing items → D-10; part M's layer cap →
P-i [B]; the G2 discipline datum → I-4; the P-i prophylactic datum → P-i [A])
without their datums appended; the remaining 14 are new. Kernel: 37 claims
found, exactly 1 filed (K3's branch-type rule → I-5); 15 more are
mechanism-covered by existing entries (2 COVERED: I-4, R-37; 13 MERGE-INTO),
and 21 are new.

## 8. Verdict

**The "filed at discharge" promise was not kept.** `dev/PLAN.md:849` records
the sentence and the kernel reports all carry "lesson candidates (IDs to be
assigned by the owner)", but the law book received nothing for them: the last
filing in `dev/LESSONS.md` is I-5, minted with the K3 commit `9c379eb`
(2026-08-03), and the git history shows no later lesson commit. The named
arithmetic is also wrong at the source: the five named batches flag 21
candidate-claims, not 18 (the bridge batch's report carries three lesson
candidates and part M carries four, against the record's 2 and 2), and the
kernel batches flag 37. The diff is therefore not a filing gap of degree but of
kind: of the 58 R5-B-plus-kernel claims, none appears in the book as an entry
except K3's branch-type rule (filed as I-5), a handful are mechanisms the book
already covers (D-10 subsuming the bridge false-target catches and the
hypothesis-pricing family, P-i subsuming the layer-cap and conversion datums,
R-38/R-35/R-16/P-a/I-4 absorbing the datum-class items), and the rest,
including every probe/G1G6/G2 candidate, the closure-fragment law, the
cofinality audit, the inner-world law, the equivalence test and the close-out
probe, are absent entirely with their measurements unrecorded. The discharge
sentence was an accounting claim, not a filing action: the backlog was named in
PLAN and never materialised in the law book, so the orchestrator must rule on
the 39 proposed entries (31 from the R5/K era, 8 pre-R5 residuals) and the 11
merge targets above before the promise can be said to have been kept.
