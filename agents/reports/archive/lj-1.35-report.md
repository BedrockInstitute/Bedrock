# LJ-1.35 report: the bound-fact construction, priced

Status: COMPLETE. Written incrementally per C-22. Untracked probes, no
commit, no push. The report uses ASD-STE100.

## 1. THE VERDICT

**BETWEEN. The measured rate is 0.0241 seconds per line.** The gate is
GO at or below 0.013 and NO-GO at or above 0.05. The number leans GO:
it is 0.48 of the NO-GO bar and 1.85 times the GO bar.

The number comes from two flat cold runs of `src/ProbeLJ135.agda`:
3.21 and 3.16 seconds of user time over 132 non-blank non-comment
lines. The pair is flat under the noise rule: the delta is 0.05
seconds, under 0.5.

The construction is not one content class. The reading layer is P-m
instantiation content. The assembly is parameterized content. The
reading layer is a fixed per-clause cost of about 2 seconds. Twelve
clauses at that cost fund inside the GCH budget.

## 2. THE BOUND FACTS ENUMERATED

Every probe in the lineage assumes the same family. The bounds make
the story's quantifiers bounded. The facts discharge them at the real
site. The family splits into three groups.

### 2.1 The leaf bound facts

| fact | file:line | type |
|---|---|---|
| `G.LeafBndG`, generic | `src/ProbeDD25D5.agda:113-116` | `(c' v' : S) → (x : S) → ⟨ (v' ∷ c' ∷ x ∷ δ) ⊨ ψ ⟩ → ⟨ fst c' ∈ fst (lookup KB δ) ⟩ × ⟨ fst v' ∈ fst (lookup KB δ) ⟩` |
| `G.StepAgreeG.OuterBndG`, generic | `:166-171` | `(c w d : S) → ⟨ (d ∷ w ∷ c ∷ z ∷ γ) ⊨ BodyD ⟩ → ⟨ fst c ∈ fst (lookup B₁ γ) ⟩ × (⟨ fst w ∈ fst (lookup K γ) ⟩ × ⟨ fst d ∈ fst (lookup K γ) ⟩)` |
| `G.StepAgreeG.LeafFactsG`, generic | `:173-174` | `(c w d : S) → LeafBndG (d ∷ w ∷ c ∷ z ∷ γ)` |
| `LeafBnd`, concrete at `DefBody` | `:226-230` | the same at `ψ = DefBody (suc zero)`, `KB` slot |
| `OuterBnd`, concrete at `StepBody` | `:243-248` | the same at the delivered `StepBody B₁ F₁` |
| `LeafFacts`, concrete | `:250-251` | `(c w d : S) → LeafBnd (d ∷ w ∷ c ∷ z ∷ γ)` |

### 2.2 The content-level bound facts

| fact | file:line | type |
|---|---|---|
| `Triple.Bounds`, generic | `src/ProbeDD25CD.agda:68-73` | `(c w d : S) → ⟨ (d ∷ w ∷ c ∷ z ∷ γ) ⊨ φ ⟩ → c ∈ Bs × w ∈ Ks × d ∈ Ks` |
| `StepAgree.BoundOK` | `:172-176` | `(c w : S) → Records B₁ F₁ γ c w → w ∈ K` and `𝒟ₒ w ∈ K` |
| `discharge` | `:177-203` | derives `Bounds` from `BoundOK` and `PowOK`; the built bridge, not a hypothesis |
| `extAtB`'s extra fact | `src/ProbeDD25D2.agda:121-123` | the bounded ext's second conjunct needs every satisfier of the body inside K |

### 2.3 The condensation decode's membership facts

`src/L/Condensation.lagda.md` already writes its clause bounded. Its
decode takes the memberships as inputs:

| fact | file:line |
|---|---|
| `c ∈ C`, `ar ∈ K`, `a ∈ K`, `yc ∈ K` | `src/L/Condensation.lagda.md:253-258` |
| `ya ∈ K`, `E ∈ K`, `e ∈ yc` | `:259-263` |
| the same, in the in direction | `:273-290` |
| the same, at the embedded clause | `:315-343` |

## 3. WHICH ARE DELIVERED

A name is not a signature. Each delivered item below has its checked
signature.

| fact | delivered at | signature |
|---|---|---|
| the code is a key over the carrier | `src/L/Coding/Powerset.lagda.md:308-314` | `codeAt-out : ⟨ γ ⊨ isCodeAt c w ⟩ → ∥ Σ ψ . fst (lookup c γ) ≡ fst (keyS A ψ) ∥₁` |
| codes lie in the code set | `src/L/Coding/CodeSet.lagda.md:443-447` | `key∈AllCodes : ⟨ keyS φ ∈ˢ AllCodes ⟩` |
| `AllCodes` is an element of `L` | `src/L/Coding/CodeSet.lagda.md:471` | prose; `AllCodes-out` and `AllCodes-in` at `:449-461` |
| the graph witness over the carrier | `src/L/Coding/Graph.lagda.md:202-206` | `graphAt-out : ⟨ γ ⊨ satGraphAt B x y ⟩ → ∥ GraphWitAt B x y γ ∥₁` |
| the value is the recursion's value | `src/L/Coding/Powerset.lagda.md:379-385` | `graphAt-unique : ... → fst (lookup v γ) ≡ fst (Sat B φ)` |
| `d = 𝒟ₒ w` | `src/L/Coding/Powerset.lagda.md:662-666` | `DefAt-out : DefOK A → fst (lookup w γ) ≡ fst A → ⟨ γ ⊨ DefAt u w ⟩ → fst (lookup u γ) ≡ 𝒟ₒ (fst A)` |
| the recorded-pair reading | `src/L/Coding/Model.lagda.md:163-166` | `appAt-adequate : (γ ⊨ appAt f x y) ≡ (pr (lookup x) (lookup y) ∈ lookup f)` |
| transitivity of `L` | `src/L/Constructible.lagda.md:379-380` | `isL-trans : y ∈ x → isL x → isL y` |
| satisfiers of the step lie in the stage | `src/L/Hierarchy.lagda.md:191-196` | `step-Lset : ⟨ γ ⊨ StepAt v b f ⟩ → ... → fst (lookup v γ) ≡ Lset (fst (lookup b γ))` |
| recorded values are the tower | `src/L/Hierarchy.lagda.md:274-301` | `approx-val : ... → fst z ≡ Lset u` |
| the successor stage is the powerset | `src/L/Axioms/Basic.lagda.md:196-197` | `Lset-suc : Lset (sucV σ) ≡ 𝒟ₒ (Lset σ)` |
| cumulativity of the tower | `src/L/Constructible.lagda.md:355-356` | `Lset-mono : β ∈ α → x ∈ Lset β → x ∈ Lset α` |

The delivered readers are the pieces. The assembly into the probes'
`LeafBnd` and `OuterBnd` is NOT delivered. The K-membership at the
story's own bound slot is NOT delivered. The bounded restatement of
the leaf content is NOT delivered. Those three are the rest.

## 4. WHAT THE REST COSTS

I built the smallest decisive miniature: the leaf bound facts and the
outer bound facts at a sealed carrier, from the delivered readers and
two site facts. The site facts are the substrate's code-set half,
survey-priced at 0.2 to 0.5k lines. The probe is `src/ProbeLJ135.agda`.

Cold profile, one process, `GHCRTS="-A64m -I0 -M8g"`, quiet machine,
dependencies warm, the probe's own interface moved aside per run:

| definition | ms |
|---|---:|
| `LeafBound.graph-read` | 1,569 |
| `LeafBound.code-read` | 362 |
| miscellaneous, the import cone | 1,131 |
| `CodeLeafCert.Δ₀-prAtL` | 68 |
| the assembly: `step`, `vstep`, `outer-bnd` | 41 |
| total | 3,174 |

Two cold runs: 3.21 and 3.16 seconds user. Rate: 3.185 / 132 =
0.0241 seconds per line.

The reading layer is the cost. `graph-read` is one definition, five
lines, 1.57 seconds. `code-read` is one definition, three lines, 0.36
seconds. The reading of the built `DefBody` satisfaction through the
delivered readers is P-m's instantiation class at 0.16 seconds per
line: 1.93 seconds of fixed work per clause at the measured site.

The assembly is free. `leaf-bnd`, `vstep`, `outer-bnd` and the
certificate's `Δ₀-prAtL` cost 109 milliseconds together. The assembly
is parameterized content.

The pinned alternative reads the value as the delivered `Sat A (toS
psi)` through `graphAt-unique`. It costs the same 1.57 seconds. I
measured both routes in one file, then removed the pinned one. The
spelling of the site fact does not move the reading cost.

## 5. DOES `Δ₀ (DefBody (suc zero))` FOLLOW?

NO. It is a separate obligation.

The bound facts are satisfaction-level membership facts. The `Δ₀`
data is syntactic (`src/FOL/LevyHierarchy.lagda.md:47-57`). Its
constructors cover bounded quantifiers only. The delivered `DefBody`
leaves carry unbounded quantifiers: `keyArityAtL c k = ∃̇ (tagAtL
(suc c) k zero)` (`src/L/Coding/CodeSet.lagda.md:135-136`),
`hasWitnessAt` has one unbounded existential (`:240-241`),
`satGraphAt` has three (`src/L/Coding/Graph.lagda.md:104-112`,
`:191-192`), and `DefinesAt` has an `extAt` plus one unbounded
existential (`src/L/Coding/Powerset.lagda.md:217-219`). No membership
fact changes the formula's syntax.

The certificate needs the bounded restatement of the leaves. That is
the substrate's code-set half. `src/ProbeLJ135.agda` section 3 builds
the restatement of the code leaf, `keyArityBnd`, with its certificate
`Δ₀-keyArityBnd`. The restatement certifies. The delivered leaf does
not.

`[LJ-1.34-R]` measured the shape already: `Δ₀-clause : Δ₀ (DefBody
...) → Δ₀ ClauseBB` checks in 756 milliseconds (`src/ProbeDD25D2.agda:
172-179`). The whole story clause certificate closes from the leaf
certificate. The leaf certificate is the substrate's content.

The bound facts and the restatement are joint halves. The D5 layer's
`leaf-in` and `leaf-out` take `LeafBnd` as hypotheses. They make the
bounded restatement adequate. The certificate makes it `Δ₀`. Neither
half implies the other.

## 6. THE PRICE OF THE NEXT BLOCK

On my numbers, with every MEASURED row from this probe or the cited
reviews:

| piece | lines | seconds | class |
|---|---:|---:|---|
| the leaf bound facts, reading and assembly, one clause | 132 | 3.19 | MEASURED, this probe |
| the reading alone, one clause | 12 | 1.93 | MEASURED, this probe |
| the assembly alone | 35 | 0.04 | MEASURED, this probe |
| the clause certificate from the leaf | 9 | 0.76 | MEASURED, `[LJ-1.34-R]` |
| the bounded code-set description, the substrate's half | 0.2-0.5k | 1.6-4.0 | SURVEY, `_build/lj-1.12-report.md:30` |
| the other eleven clauses' bound facts | 0.4-0.8k | 22-31 | PROJECTED on one measured comparable, at about 2 seconds per clause |

The per-clause projection is a hypothesis, not a price. P-l forbids
pricing by analogy. One clause is measured here; the other clauses'
bodies differ.

The block funds inside the GCH budget of 99.6 to 147.7 seconds
(`dev/ledger.toml:305`). The clause residue at the measured 0.0241
plus the substrate survey lands near the low end. The bound-fact
construction is no longer the widest unmeasured term.

## 7. DD4

Each fact falls on one side.

| fact | side |
|---|---|
| the reading layer: `code-read`, `graph-read`, the outer read | PER-TOWER (Def). It reads the Def tower's built syntax through Def-specific delivered readers. Measured: 1.93 seconds per clause, the whole cost |
| the site facts: codes in K, values in K, `val-in-K`, `D0-in-K` | PER-TOWER CONTENT, TEMPLATE SHAPE. The content is the Def tower's code set and table, satisfaction-bound `K(u)` (`dev/literature/devlin-II5.md:375`). The shape, a K-membership fact at a sealed carrier, is generic |
| the assembly: `leaf-bnd`, `outer-bnd` | TEMPLATE. Measured: 41 milliseconds. It is generic in the reading's output and the site facts |
| the certificate restatement | PER-TOWER (Def). The bounded code leaf is Def syntax |

D-26's prediction holds. Anything keyed on the Def syntax, the reading
and the restatement, is per-tower. The carrier-keyed assembly is
template. The J tower's bound facts are structural, generation data
with no satisfaction to read, so the expensive half does not reach it.

## 8. LITERATURE USED

`dev/literature/devlin-II5.md`, Step C (`:209-256`, summary `:299-302`,
D-26 table `:375`). Took the requirement: bind every quantifier of the
Def step by the concrete set `K(u)`, the finite sequences over the
formula set, the variables and the members of `u`. Devlin assumes the
set `K(u)` exists and that its formula is `Σ₁`. The formal proof must
supply the membership facts instead: the code, the value, the
witnesses and the satisfiers all lie inside `K(u)`. Those facts are
exactly the site facts and the reading layer this probe prices. The
book asserts absoluteness where the formal proof must prove a decode,
so it cannot price any row here.

`dev/literature/devlin-errata.md`. NOT read. WHY NOT: `[LJ-1.14]`
verified it does not cover Chapter II section 5, and the brief rules
out re-checking it.

## 9. ARCHIVE USED

`_build/lj-1.34-review.md`, whole. Took the verdict at `:8`, the D5
row at `:53`, the one surviving obstruction at `:249` and section 3.1,
the bound-fact construction as the widest term at `:390` and `:403`,
and the DD4 split at `:409-425`.

`_build/lj-1.34-report.md`, whole. Took the failing certificate at
`:48-60` and the leaf agreement's 41.7 seconds at `:85-96`.

`_build/lj-1.33-review.md`, whole. Took the 2x2 at `:70-84`, the
layer's 34 milliseconds at `:29`, and the not-sure list at `:238-247`.

`_build/lj-1.5-report.md`, whole. Took block 1's rate at `:8-13` and
the next-block list at `:96-108`.

`_build/lj-1.2-gate.md`, whole. Took the missing bounds at `:60-63`,
the substrate at `:87-89`, and the corrected 5,047-line figure at
`:126-128`.

`src/L/Condensation.lagda.md`, whole. Took the decode memberships at
`:253-290` and `:315-343`.

`src/L/Coding/Powerset.lagda.md`, whole. Took `DefBody` at `:437-440`,
`DefAt` at `:442-443`, `codeAt-out` at `:308-314`, `DefAt-out` at
`:662-666`, and the delivered reading of `DefBody` at `:556-558`.

`src/ProbeDD25D5.agda`, whole. Took the bound-fact statements at
`:113-116`, `:166-174` and `:226-251`.

`src/ProbeDD25CD.agda`, whole. Took `Bounds` at `:68-73`, `BoundOK` at
`:172-176` and `discharge` at `:177-203`.

`dev/LESSONS.md` is not archived and binds. P-l decided section 4. P-m
named the content classes. P-t named the mechanism, the built tree.
P-v decided the spelling: the machine's spelling throughout. P-u held:
no placement anywhere. D-1, D-10, C-12, C-22, C-32, C-33 and C-34
were followed.

## 10. WHAT I AM NOT SURE OF

1. I measured ONE clause's leaf reading. The other clauses' bodies
   differ, and their readings are unmeasured. The 2 seconds per clause
   projection is a hypothesis.
2. The graph witness's own existentials, the code set `C`, the table
   `T` and the carrier `b`, need K-membership too in the substrate's
   bounded restatement. My probe bounds the code and the value, which
   are the story's own quantifiers. The witness memberships are
   substrate content of the same shape, unmeasured here.
3. The K-membership at the real site is stated as site facts, not
   built. The substrate's code-set half carries them. Its 0.2 to 0.5k
   line survey has not been re-measured.
4. The rate meter is weak at this size. The cone is 1.13 seconds of
   the 3.19. The reading is a fixed per-clause cost, so more lines
   dilute the rate. DD24's seconds-per-line meter mostly measures the
   cone here.
5. I did not re-open leg D's shape. The brief rules it settled, and
   `[LJ-1.34-R]` measured it.
