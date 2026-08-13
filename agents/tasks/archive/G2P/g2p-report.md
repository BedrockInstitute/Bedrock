# g2p probe report: the t-phi satisfaction-set construction, priced in miniature

**Verdict: GO, with one priced convention fork.** The D-1 probe of
`[L3.31-R5-G2p]` builds the engine of the full switch (satisfaction SETS
`T_phi` as members of the rud closure, value-level sets, satisfaction
external) for the mini fragment (membership atom, negation, unbounded
existential) over an abstract P-h interface. All three clauses build as
closure members and carry two-way adequacy against the external face. 286
code lines, cold check 1.8 s wall, no wall, no postulates, no holes, no
`TERMINATING` pragmas, no consumer-side seal was needed. The deep-satisfaction
wall class (B4e / P-i) did not fire at the mini scale; the price table and the
G2 extrapolation are below, and section 6 states the D-10 target check.

Probe file: `src/ProbeSatSets.agda` (untracked, 379 lines total, 286 code
lines, stop-line 600). Checked with `GHCRTS=-M8g agda src/ProbeSatSets.agda`,
one check at a time, from this worktree.

## 1. What the probe prices

The pinned design, executed as specified: an abstract module over `U : V`,
its transitivity, and the closure interface (`InJ : V -> Type`, `Jrud` the
sixteen-operation closure fact, `U` itself `InJ`, members of `U` `InJ` via
transitivity); left-nested k-tuples over `pr` with the tuple space as
`F2`-iterated closure member, its membership characterization stated once;
three clauses (atom as F7-slice, negation as F1-complement, unbounded
existential as F6 domain/projection one arity down); adequacy in both
directions per clause, `m in T_phi` iff the external satisfaction holds at the
decoded tuple.

### 1.1 Design choices (recorded as the brief requires)

- **Abstract closure interface, P-h style, Switch.Closure shape.** The probe
  takes `InJ` abstract, a local `Op16` index (mirroring `L.Rud.Step`'s), the
  sixteen-op `Jrud` fact over an abstract `Fof`, the four `Fof-f*` tag
  equations, `JU : InJ U`, and `Jtrans` from which `UmemInJ` (members of `U`
  are `InJ`) is derived. The per-op arms `JF1/JF2/JF6/JF7` are exactly
  Switch.Closure's `J-F1`-style `subst InJ (Fof-f*) (Jrud ...)`. The probe
  imports only committed, brief-designated modules: `L.Rud.Ops` (the sealed
  F1/F2/F6/F7 and their read/write lemmas), `V.Coding` (`pr`, `pr-inj`),
  `V.Hierarchy` (`𝒮ᵥ`), `FOL.ZFStructure`, `Base.*`. Nothing concrete
  unfolds; no in-flight module is imported (the assembly obligation at
  `Jset-rud` is priced in section 5).
- **Tuple convention: LEFT-nested.** `(x1,...,xk) = pr (pr x1 x2) ... xk`, so
  `U^k = F2 (F2 ... (F2 U U) ...) U`. This is a deliberate, recorded
  deviation from the delivered F3/F4 right-nested convention, and it is the
  one structural choice that matters: under left-nesting the existential on
  the LAST free variable is F6's native projection (the outermost pair's left
  component is the k-tuple, its right component the witness), and the atom on
  the FIRST two coordinates is the F7-slice at the head pair. Under the
  delivered right-nesting the same existential needs a pair-reversal
  (converse-relation) step, which is where the F8/F10 machinery genuinely
  enters; that is priced in section 5, not smuggled into the mini fragment.
- **Mini fragment.** Arity-3 formulas `Fm3 = atom | neg` (atom = `x1 in x2`)
  and arity-2 formulas `Fm2 = ex | neg2` where `ex phi` is the unbounded
  existential over the last free variable, ranging over `U` itself (the
  Delta-0 route's impossible clause). Negation is exercised at both arities
  to price "one clause, every arity".
- **External satisfaction, Type-valued.** `Sat3`/`Sat2` are plain types over
  the coordinates (`atom` is `⟨ a in b ⟩`, `ex` is `Σ c, c in U × Sat3`).
  Adequacy is stated as per-clause direction pairs over the carriers with
  explicit truncation (lesson I-4 as the FIRST formulation, not a repair):
  `Dec3/Dec2` are the decoded-tuple existentials, and `adeq3-in/out`,
  `adeq2-in/out` are the two directions per clause.
- **Decode is existential-shaped, not a partial projection.** The tuple's
  coordinates come from the sealed F2/F7 read lemmas; there is no `left`/
  `right` projection in the probe (Images is out of scope), so two decodes of
  one tuple are identified by `pr-inj` plus `Sat3-cong`/`Sat2-cong`, pure
  Type-level substs with no formula induction.

## 2. Per-clause price table

Code lines exclude blank and comment lines; timings are the cold whole-file
check (the per-clause checks are not separable below the 1.8 s granularity, so
the table reports the whole-file cold check plus the heaviest single
definitions from `--profile=definitions`).

| Item | Code lines | Cold time | What it is |
|---|---|---|---|
| imports + `Op16` | 19 | - | the sixteen-op index, local |
| abstract interface telescope | 13 | - | U, Utrans, InJ, Jtrans, Fof, Jrud, Fof-f1/f2/f6/f7, JU |
| closure arms + `UmemInJ` | 10 | - | JF1/JF2/JF6/JF7 via subst; members of U in J |
| tuple spaces + characterizations | 54 | ~100 ms (m in U3 57 ms, m in U2 37 ms) | U2, U3, hU2, hU3, U2-char, U3-char, stated ONCE (R-36), consumed by every clause |
| fragment syntax + external Sat | 12 | - | Fm3/Fm2, Sat3/Sat2 |
| T construction + engine | 12 | - | T3/T2 and the InJ proofs hT3/hT2 (the engine is 12 lines; the cost is all in adequacy) |
| adequacy shape + congruence | 20 | - | Dec3/Dec2, Sat3-cong/Sat2-cong |
| **atom clause** (fwd+bwd) | 16 | ~40 ms | F2-read + F7-read in, F7-write + F2-write out |
| **negation clause** (fwd+bwd, arity 3) | 56 | ~120 ms (inner 28 ms, outer 15 ms) | F1 complement; the bulk is decode-uniqueness (two decodes of one tuple identified by pr-inj + Sat3-cong) |
| **unbounded existential clause** (fwd+bwd) | 16 | ~50 ms | F6-read in, F6-write out |
| negation at arity 2 (fwd+bwd) | 56 | ~90 ms | the same F1 mechanism one level down |
| **totals** | **286** | **1,621 ms cold, 1.8 s wall** | stop-line 600, used 48% |

**Clause verdicts: GO / GO / GO.** The atom, negation, and unbounded
existential clauses each typecheck with both-direction adequacy, no
postulate, no hole, no LEM spend (the fragment's algebra is constructive: F1
difference, F6 domain, F7 relation need no classical law; LEM is a D-7 item
for the intersection clause only, which is outside the mini fragment).

## 3. Which LESSONS carried the weight

- **I-4 (carrier-level combinators, first formulation).** Every adequacy
  statement is a pair of functions over the carrier with explicit
  memberships and explicit truncation; no implicit is ever inverted through
  a content-of projection. The wall class the probe exists to detect had no
  formulation to fire on (the R5a prophylactic pattern, applied before any
  wall).
- **R-36 / R-38 / P-c (seal discipline at the source).** The probe consumed
  F1/F2/F6/F7 exclusively through the sealed read/write surface delivered in
  Ops; the tuple characterizations are composed reads, never unfolded
  bodies. The transparent ops (F0/F5/F9) are unused, so no consumer-side
  alias became a birth site: zero new `opaque` blocks were needed. The
  delivered seal discipline is exactly what kept the probe clean.
- **R-35 (small indices).** No union-representation extraction, no fiber
  extraction over `⟪ ⋃ x ⟫`; the constructions live at the stuck-member
  level throughout.
- **P-h (abstract module parameters).** The walk runs over abstract
  `InJ`/`Jrud`/`U`; nothing concrete is in scope to unfold.
- **P-d (direction pairs, not hProp paths).** Adequacy is delivered as
  fwd/bwd pairs per clause, never as a path or iff between satisfactions.
- **I-2 + C-11 + R-34-class hygiene.** hProp carriers wrapped in `⟨_⟩`,
  signature-level hProp connectives avoided; the parameterized module body
  indented deeper than its header; levels explicit through the module
  telescope.

Carried-but-unconsumed (reported honestly): `Utrans` is consumed ZERO times
by the pure-variable fragment, and `Jtrans`/`UmemInJ` are exercised only by
the derived lemma, not by any clause. The pure-variable fragment needs only
`JU` + `Jrud`; transitivity enters the real G2 at the parameter atoms and the
bounded quantifiers (section 6).

## 4. Walls and formulation trail

**No wall.** Every check ran under 2 s cold (`GHCRTS=-M8g`, one check at a
time), versus the 180 s tripwire; no heap exhaustion, no killed process, no
180 s+ check. The formulation obstacles below were first-attempt fixes, not
wall-protocol stops, and are recorded as surprises:

1. **Mutual-block clause contiguity.** Interleaving the two directions of
   `adeq3-in`/`adeq3-out` inside one `mutual` failed scope checking
   (`MissingTypeSignature`): each function's clauses must be contiguous
   inside the block. Restructure only.
2. **The hProp `⊓` carrier is a dependent `Σ`, not `×`.** F1-spec's forward
   codomain `⟨ A ⊓ (¬ B) ⟩` arrives as an UNTRUNCATED `Σ[ _ ∈ ⟨ A ⟩ ] (⟨ B ⟩
   → ⊥)`; the first negation-in formulation wrapped it in `PT.rec` and
   mismatched. Consume it directly.
3. **Transport order in `Sat3-cong`.** The coordinate substs must be applied
   outermost-first along the path endpoints (a-subst on `sat`, then b, then
   c); the naive nesting failed on the innermost motive. Once-flipped, both
   congruence lemmas are instant.

## 5. Extrapolation to the real G2 (P1-report style)

The probe's clause work is 88 lines (16 atom + 56 negation + 16 existential);
the shared machinery is 198 (interface 42, tuples+chars 54, syntax+Sat 12,
T+engine 12, adequacy shape+cong 20, plus the arity-2 negation 56 which the
real G2 does not pay twice: its `DecK` is one arity-generic shape). The real
G2 adds the full `Formula` type (all connectives), equality and parameter
atoms, the k-ary plumbing, and the Def-face bridge.

| Probe item | Probe lines | Real G2 analogue | Multiplier | What the multiplier covers |
|---|---|---|---|---|
| atom | 16 | all atom shapes | 3-5x | `≐` atoms, parameter atoms (`var in con c`, `con c in var`), coordinate-pair reads at arbitrary (i,j): the tuple-shuffle ops F11-F14 / left-right reads |
| negation | 56 (paid twice) | one arity-generic clause | 1.2-1.5x | `DecK` + ONE decode-uniqueness lemma (the probe re-proved the pr-inj identification per arity; G2 states it once) |
| existential | 16 | full `∃` clause | 1.5-2x + reorder | `∃` at any variable position: under the delivered right-nested convention the last-coordinate projection needs the F8/F10 converse step; mid-variable `∃` needs re-association |
| new connectives | 0 | `∧`, `∨`, `⇒`, bounded `∀`/`∃` | n/a | 30-50 / 25-40 / 15-25 / 40-70 probe-discipline lines: intersection spends LEM at the D-7 spot, `∨` via De Morgan or direct union, `⇒` via `¬∧`, bounded quantifiers consume `Utrans` |
| k-ary plumbing | 54+20 | `DecK` family, `U^k` Nat-indexed, decode-uniqueness at k, reorder | n/a | 150-250 lines; the single largest residual, the same P1-style parameter plumbing |
| statement bridge + assembly | 12 | `definable→closure` face + `Jset-rud` instantiation | n/a | 60-120 lines: aligning `DefOf.defSet`'s inner-satisfaction face with the external `Sat` face, and discharging `Fof`/`Jrud`/`JU`/`Jtrans`/`Utrans` at `(Jset α lim, Jset-rud α lim)` with `U = Jset β limβ`, `β ∈ α` |
| **totals** | **286** | | **1.6-2.6x** | **460-750 probe-discipline lines** |

Applying the D-6 production factor (readers both directions, dispatch over
the full formula type, environment plumbing), with the caveat that this probe
ALREADY pays both-direction adequacy so the factor sits between 2x and 3x:
the real G2 build prices at roughly **1,000-2,250 lines**. That brackets the
recon's 400-1,200 band from above: the recon priced the theorem at delivery
discipline; the probe says the full formula-type G2 with all connectives and
k-ary plumbing is at the upper end of, or beyond, that band once the
production factors are counted, and the F8/F10 converse step is the true
price of the delivered tuple convention. This matches the recon's wall-class
rating and the B4e/P-d/P-i record, and it says the probe's 600-line
stop-line is adequate for the miniature but not for G2 itself.

## 6. Is the target right? (D-10)

The target route is TRUE for the pure-variable fragment at small arity: the
constructions are real closure members (`hT3`, `hT2` from the abstract
`Jrud`), and the adequacy holds in both directions against the external face
(no vacuous clause: the atom's decode carries `a in b`, the existential's
carries the witness `c in U`, the negation's carries `¬Sat`). Three
corrections the probe forces onto the real G2's shape:

1. **The satisfaction-set tuple convention must be chosen against F6, not
   inherited from F3/F4.** Left-nesting makes the last-variable `∃` F6-native
   (16 lines). The delivered right-nesting makes it the F8/F10 converse step
   (the genuine reason the design names "F6/F8/F10 machinery"); the real G2
   should either adopt left-nested satisfaction tuples and pay one
   re-association at the F3/F4 interface, or price the converse explicitly.
2. **`Utrans` is not needed by the satisfaction sets themselves.** The
   pure-variable fragment consumes only `JU` + `Jrud`. The real G2's
   telescope should carry `Utrans` into the parameter-atom and bounded-
   quantifier clauses only, and `UmemInJ` enters exactly at `con c` atoms.
3. **Negation is not the F1 cost; it is the decode-uniqueness cost.** The
   difference op is one line; the clause is 56 because two decodes of one
   tuple must be identified. G2 should ship one decode-uniqueness lemma per
   arity (R-36-style) and let every clause consume it, which is the single
   biggest structural saving the probe identifies.

## 7. Lesson candidates

- **LC-1: price decode-uniqueness once per arity, not per clause.** The
  negation clause's bulk is the pr-inj identification of two decodes; a
  shared `DecK-unique` lemma (R-36 pattern) removes it from every clause.
- **LC-2: the hProp `⊓` carrier is a dependent `Σ`, untruncated.** Consuming
  a spec's hProp-⊓ codomain needs no `PT.rec`; truncation appears only where
  the goal is a truncated sum. (I-series neighbor of I-2.)
- **LC-3: the domain operation's native projection is convention-dependent.**
  F6 projects the pair's left component; which coordinate that is depends on
  the tuple nesting. Choose the satisfaction-set convention against the
  projection (D-9's carrier-choice thinking applied to tuple encoding), and
  price the re-association or the F8/F10 converse as the real G2's plumbing.
- **LC-4: the pure-variable satisfaction fragment is constructive and
  transitivity-free.** No LEM and no `Utrans` are consumed by atom/negation/
  existential over the abstract closure; both enter later (intersection via
  D-7, parameters and bounded quantifiers). Keeps the G2 telescope honest.

