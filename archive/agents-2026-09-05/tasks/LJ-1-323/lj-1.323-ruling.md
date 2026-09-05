# LJ-1.323 ruling: the natural statement of both trophies

tier: fable (in-harness-subagent-mode), effort max. Ruled 2026-08-16 under the
owner's 2026-08-15 delegation. Writes are in `agents/tasks/LJ-1-323/` only.
This file is the ruling of record. The probe `Statement.agda` in this
directory typechecks the proposed statement: exit 0, wall 2.39 s, 0 of 2
Agda slots in use before the run, 1-minute load 4.39,
`GHCRTS="-A64m -I0 -M8g"`, one process, cap not raised.

DD4, stated (the gate reads the heading): maximize the code the two proofs
share, and write it generic. This ruling's answer is in section 7.5: the two
statements now share their whole semantic frame, the internal-truth reading
of `⊨`, and the statement adds no per-trophy device.

## 0. Verdict, one sentence per trophy

- **`L ⊨ AC`: the statement DOES NOT change.** `L⊨ZFC : isZFCModel` at
  `src/L/Model.lagda.md:99` is the internal choice-set axiom over `𝒮ʟ` and it
  passes both lenses as written.
- **`L ⊨ GCH`: the statement CHANGES.** The `sq` hypothesis leaves the
  statement; every ambient injection type leaves the statement; the
  conclusion becomes the L-internal cardinal EQUALITY `2^κ = κ⁺`: two
  merely-existing coded injections at the successor cardinal, with leastness
  by the model's own `⊆ˢ` and an ordinal certificate on every cardinal.

The asymmetry is right because the defect was asymmetric. AC was born as a
field of the model record, so the internal-truth discipline was forced on it.
GCH was stated freestanding and drifted into the ambient vocabulary of its
route.

## 1. The statements, exact Agda text

### 1.1 `L ⊨ AC`, unchanged

The delivered text stands. `src/FOL/ZFModel.lagda.md:419-431` and
`src/L/Model.lagda.md:83-100`:

```agda
record isZFCModel : Type (ℓ-suc ℓ) where
  field
    zf : isZFModel
  open isZFModel zf public
  field
    hasChoice :
      (a : S)
      → ((x : S) → ⟨ x ∈ˢ a ⟩ → ∥ Σ[ y ∈ S ] ⟨ y ∈ˢ x ⟩ ∥₁)
      → ((x y : S) → ⟨ x ∈ˢ a ⟩ → ⟨ y ∈ˢ a ⟩
           → ∥ Σ[ z ∈ S ] (⟨ z ∈ˢ x ⟩ × ⟨ z ∈ˢ y ⟩) ∥₁ → x ≡ y)
      → ∥ Σ[ c ∈ S ] ((x : S) → ⟨ x ∈ˢ a ⟩
           → isContr (Σ[ z ∈ S ] ⟨ z ∈ˢ (c ∩ x) ⟩)) ∥₁

L⊨ZFC : isZFCModel
L⊨ZFC = record { zf = L⊨ZF ; hasChoice = hasChoiceL L⊨ZF }
```

### 1.2 `L ⊨ GCH`, the replacement statement

This is the full replacement for the code fence of `src/L/GCH.lagda.md`.
It typechecks: `agents/tasks/LJ-1-323/Statement.agda`, exit 0, 2.39 s.

```agda
{-# OPTIONS --cubical --safe --guardedness #-}

open import Base.Prelude
open import Base.Truth
open import Base.Classical using ( LEM )

module L.GCH {ℓ : Level} (lem : LEM (ℓ-suc ℓ)) where

open import FOL.ZFStructure using ( module hPropStructure )
import FOL.ZFModel
open import V.Hierarchy {ℓ} using ( 𝒮ᵥ )
open import L.Constructible {ℓ} using ( 𝒮ʟ; IsOrd )
open import L.Cardinal {ℓ} lem using ( IsCardinalL; InjCode )
open import Cubical.HITs.CumulativeHierarchy.Base using ( _∈_ )
open import Cubical.HITs.CumulativeHierarchy.Constructions
  using ( module InfinitySet )
open InfinitySet {ℓ} using ( ω )
import Cubical.Data.Empty as Empty
import Cubical.HITs.PropositionalTruncation as PT
open PT using ( ∥_∥₁ )

open TruthAlgebra (hPropAlgebra (ℓ-suc ℓ))
open hPropStructure 𝒮ᵥ using ( _∈ˢ_ )
open hPropStructure 𝒮ʟ using ( S )

module ModelL = FOL.ZFModel 𝒮ʟ
open ModelL using ( _⊆ˢ_ )

-- The L-internal injection: the model's own truth value of the internal
-- statement「some F in L is an injection of a into b」.  The model's ∃
-- is the truncated Σ over the carrier, and `InjCode`'s conjuncts are
-- satisfaction facts (src/L/Cardinal.lagda.md:223-228).  This is the
-- refutand of `IsCardinalL`, reused positively.
InjL : S → S → Type (ℓ-suc ℓ)
InjL a b = ∥ Σ[ F ∈ S ] InjCode F a b ∥₁

-- δ is THE successor cardinal of κ in the sense of L: an ordinal
-- L-cardinal above κ, below or equal to every ordinal L-cardinal above
-- κ.  Leastness is the ordinal order: for ordinals, δ ⊆ c is δ ≤ c, and
-- `_⊆ˢ_` is the model's own subset relation
-- (src/FOL/ZFModel.lagda.md:141-142).  Every component is an hProp, so
-- the witness δ is unique and the truncation below is the classical ∃.
SuccCardL : S → S → Type (ℓ-suc ℓ)
SuccCardL δ κ =
    IsOrd (fst δ)
  × IsCardinalL δ
  × ⟨ fst κ ∈ fst δ ⟩
  × ((c : S) → IsOrd (fst c) → IsCardinalL c → ⟨ fst κ ∈ fst c ⟩
             → ⟨ δ ⊆ˢ c ⟩)

-- THE STATEMENT.  L satisfies the generalized continuum hypothesis:
-- for every infinite cardinal κ of L, 2^κ = κ⁺ in the sense of L.  The
-- equality is the pair of internal injections at the successor
-- cardinal; the power set is the model's own.  No hypothesis remains
-- beyond κ itself, and no ambient function type crosses the ⊨ boundary.
GCHStatement : ModelL.isZFModel → Type (ℓ-suc ℓ)
GCHStatement zf =
  (κ : S)
  → IsOrd (fst κ)
  → IsCardinalL κ
  → (⟨ fst κ ∈ˢ ω ⟩ → Empty.⊥)
  → ∥ Σ[ δ ∈ S ]
       ( SuccCardL δ κ
       × InjL (𝒫 κ) δ
       × InjL δ (𝒫 κ) ) ∥₁
  where open ModelL.isZFModel zf using ( 𝒫 )
```

Optional, recommended: the two certificates from `Statement.agda`,
`isPropSuccCardL` and `isPropGCHStatement` (10 lines plus one HLevels
import). They pin section 5's policy mechanically at the statement site:
a trophy statement is a proposition, and the checker is Agda itself.

### 1.3 The endpoint pair, one hand

```agda
L⊨ZFC : isZFCModel            -- delivered, src/L/Model.lagda.md:99
L⊨GCH : GCHStatement L⊨ZF     -- the target the proof must inhabit
```

The second line is the future capstone, not part of this landing. It is the
exact sibling of `hasChoiceL : (zf : isZFModel) → ChoiceStatement zf`
applied at `L⊨ZF` (`src/L/Choice/Transversal.lagda.md:372-385`).

## 2. The two readings (native prose of each field, exempt from STE)

### 2.1 The set theorist reads `L⊨ZFC`

"The constructible structure satisfies extensionality, regularity,
pairing, union, separation, replacement, power set, infinity, and
Zermelo's choice-set axiom: every set of nonempty pairwise disjoint sets
admits a transversal meeting each member in exactly one point, all
relativized to L. That is Goedel's theorem: L is a model of ZFC, so AC
holds in L."

### 2.2 The cubical type theorist reads `L⊨ZFC`

"A record over the hProp-valued membership structure 𝒮ʟ: twelve ZF fields
plus choice, with the internal ∃ interpreted as the propositional
truncation of a Σ over the carrier and 'exactly one' as contractibility of
a prop-indexed Σ. The inhabitant is assembled field by field from the axiom
chapters. That is how you present a model of a first-order theory in a
univalent setting."

### 2.3 The set theorist reads the new `GCHStatement`

"For every κ in L which is an ordinal, is not a natural number, and is a
cardinal in the sense of L, that is, no F in L injects κ into any smaller
ordinal: there exists δ such that δ is a cardinal of L above κ and lies
below or equal to every cardinal of L above κ, so δ is κ⁺ as computed in
L; and 𝒫(κ), as computed in L, injects into δ inside L, and δ injects
into 𝒫(κ) inside L, so |𝒫(κ)| = κ⁺ in L by Cantor-Bernstein. In one
line: relativized to L, every infinite cardinal κ satisfies 2^κ = κ⁺.
That is (GCH)^L, Devlin's 5.7, Jech's 13.20."

### 2.4 The cubical type theorist reads the new `GCHStatement`

"A mere proposition over the model: a Π over the carrier with
propositional hypotheses, an ordinal certificate, the internal-cardinal
predicate, and non-membership in ω, concluding in the truncation of a Σ
whose payload is a product of hProps: the successor-cardinal
specification, all components propositional, and two merely-existing
coded injections, which are the model's truth values of the internal
statements |𝒫κ| ≤ δ and δ ≤ |𝒫κ|. Every ∃ is ∥Σ∥₁, matching the
semantics of the structure's ⋁; cardinal inequality as truncated
injection is Definition 10.2.7 of the HoTT Book; the successor cardinal
is unique, so the outer truncation is even redundant, kept for uniformity
with hasChoice. No ambient function type crosses the ⊨ boundary. That is
the standard internal-model idiom: satisfaction facts in, satisfaction
facts out."

## 3. The diff against the delivered text, line by line

Target: `src/L/GCH.lagda.md`, delivered fence `:3-88`. The AC side has no
diff.

1. Imports (`:16-25`): drop `_↪_` from the `L.Cardinal` list, add
   `InjCode`. Drop the `L.Absorption` import (`:17`). Drop `⟪_⟫`
   (`:19`). Keep `ω`; drop `sucV` and `#_` (`:22`). Add
   `open ModelL using ( _⊆ˢ_ )` after `:31`.
2. `SqShape` (`:44-47`): OUT of the statement file. It is proof-side
   route interface. Its two delivered consumers spell their own `sq`
   parameters and do not import it (MEASURED:
   `src/L/StageCardinal.lagda.md:17-19`,
   `src/L/BoundedSubset.lagda.md:1388-1390`, and grep: no `src/` file
   outside `L/GCH.lagda.md` names `SqShape`).
3. `AbsorbsShape`, `absorbsL` (`:51-63`): OUT of the statement file.
   Recommended home: beside `absorbs` in `src/L/Absorption.lagda.md`,
   whose own comment at `:610` already names the shape. No `src/`
   consumer exists (MEASURED, same grep).
4. `SuccCardL` (`:67-71`): add `IsOrd (fst δ)`; replace the leastness
   clause `(c : S) → IsCardinalL c → ⟨ fst κ ∈ fst c ⟩ →
   (⟪ fst δ ⟫ ↪ ⟪ fst c ⟫)` with
   `(c : S) → IsOrd (fst c) → IsCardinalL c → ⟨ fst κ ∈ fst c ⟩ →
   ⟨ δ ⊆ˢ c ⟩`.
5. `GCHStatement` (`:78-87`): delete `(sq : SqShape)` (`:80`); add
   `IsOrd (fst κ)` after `(κ : S)`; replace the conclusion conjunct
   `(⟪ fst (𝒫 κ) ⟫ ↪ ⟪ fst δ ⟫)` with
   `InjL (𝒫 κ) δ × InjL δ (𝒫 κ)`.
6. New definition `InjL` (6 lines with comment).
7. Prose and A-numbering comments (`:33-40`, `:57-61`, `:73-77`): rewrite
   to match; the owner's freeze on mathematical prose is lifted for this
   file by the delegation.

## 4. The damage, named plainly

**No delivered proof breaks.** `GCHStatement` and `SuccCardL` have zero
consumers in `src/` outside the statement file (MEASURED, grep 2026-08-16).
The GCH proof is not wired; the ledger's own note says the closure is the
statement's (`dev/ledger.toml:204`). The four probe files that import
`L.GCH` (`LJ-1-280`, `LJ-1-284`, `LJ-1-286`, `LJ-1-300`) belong to closed
tasks; a probe is not typechecked after its task closes. The orchestrator
should confirm the live sibling task does not import `SqShape` before
landing.

**What is discarded.** The delivered statement text, about 30 fence lines,
and `absorbsL`'s role as a statement-side supply line. Nothing else. The
Absorption chapter, the square-law machinery, the InjChain, and the
BoundedSubset work are untouched: they change role from
statement-adjacent to proof-side lemmas, which is where Devlin keeps
them.

**What the right statement newly costs.** Three proof-side obligations,
none of which blocks the landing of the statement itself:

1. **The square law becomes an obligation instead of a hypothesis.** This
   was always owed for an unconditional trophy. The funded door probe of
   `[LJ-1.319]` section 2.3 is already pointed at it. No new mathematics.
2. **The conclusion must be delivered coded.** The route's final
   injections are built ambient today (`absorbs`,
   `src/L/Absorption.lagda.md:613-618`). The proof must intern its final
   injection as an L-set `F` with `InjCode`, or re-derive the final leg
   internally, as Devlin's own proof does, entirely inside L. Estimate:
   about 800 naive lines, basis: survey against the delivered coding
   readback half of `src/L/Coding/Injection.lagda.md`, which is the same
   texture. Gate before funding (DD8): the widest unmeasured term is
   the interning of ONE delivered ambient injection, and the decisive
   miniature is to code `absorbs` at its smallest site into an `InjCode`
   witness.
3. **The reverse bound `InjL δ (𝒫 κ)` is new.** It is NOT free
   (MEASURED: grep finds no Cantor lemma and no lemma of this shape in
   `src/`). The classical route: each α in δ carries a least-coded
   well-order of κ of type α, consuming the square law, `leastOf`
   selection, and the delivered coding. Estimate: about 600 naive lines,
   basis: survey against `LeastCardInjL` plus `Canonical` plus readback,
   about 350 delivered lines of the same texture. Gate before funding
   with its own miniature.

Both estimates are pre-probe survey figures. The statement ruling does
not depend on them; a wall re-prices the proof, it does not reverse the
statement (section 6).

## 5. The truncation policy (the general rule, so the next statement needs no ruling)

1. **A theorem statement is a proposition.** Every existential in a
   statement is `∥ Σ ... ∥₁`, or an equivalent proposition such as a
   unique existence. Hypotheses truncated makes the theorem stronger;
   conclusions truncated is the honest classical ∃; both match the
   model's own semantics of ∃ and HoTT Book Definition 10.2.7 for
   cardinal claims.
2. **A statement about the model stays inside the model.** Anything the
   sentence asserts under `⊨` uses the coded face:
   `∥ Σ[ F ∈ S ] ...Code... ∥₁`. Ambient `⟪ a ⟫ ↪ ⟪ b ⟫` never appears
   in a trophy about the model's truth.
3. **Bare `A ↪ B` in an interface is proof-side only**, and only where a
   measured consumer consumes data (the square law's two consumers,
   MEASURED in `[LJ-1.314]` section 2.2). The data is then CONSTRUCTED,
   by canonical selection (`leastOf` plus readback), never assumed as a
   principle. `[LJ-1.319]`'s refusal of `InjData` stands.
4. **When a proof stalls on `∥ A ∥₁`**, the order of attack is the
   digest's checklist (`dev/literature/truncation-and-selection.md`
   section 4): propositional motive, unique choice, `rec→Set` with a
   `2-Constant` map, `leastOf` over a well-order with a propositional
   payload, Kraus Theorem 16, and only then a ruling.
5. **Ambient cardinal-inequality lemmas**, where the ambient is the
   subject, say `∥ ⟪ a ⟫ ↪ ⟪ b ⟫ ∥₁`; a bare ambient injection is
   reserved for a named uniform construction that the lemma itself
   delivers.

## 6. What would reverse this ruling, observable conditions

1. **The face reverses** only if the owner re-rules what the trophy is
   about: ambient cardinal arithmetic of L-carriers instead of internal
   truth. That is a charter-level change; the observable is an owner
   ruling that rewrites the endpoint's wording, which today says the
   internal reading (`archive/dev/DECISIONS-archived.md:29`, carried
   into DD2's route statement).
2. **The equality reverses to a one-sided bound** only if the reverse
   bound is refuted in this setting. The literature says it is a ZF
   theorem, so the practical observable is a measured wall in BOTH the
   interning miniature and an internal re-derivation of the same leg,
   surviving an adversarial review. A cost overrun alone re-prices; it
   does not reverse.
3. **`sq` returns to the statement** only if the square law is measured
   independent of this ambient, which would contradict its ZF
   provability; a wall in the funded probe does not qualify. A
   conditional trophy is what this ruling exists to remove.
4. **The `⊆ˢ` leastness reverses to injection leastness** if a green
   consumer chain is delivered that needs the injection form at the
   statement level and cannot derive it from `⊆ˢ` plus the delivered
   machinery. INFERRED impossible for ordinals under LEM, since subset
   leastness implies injection leastness by the inclusion map; no term
   was built.

## 7. The five tensions, ruled one by one

### 7.1 Truncated or data: TRUNCATED, and the inconsistency was real

The delivered file demands data in the hypothesis and delivers a
proposition in the conclusion (`src/L/GCH.lagda.md:44-47` against
`:84-86`). No classical source faces an untruncation problem at this
step because the classical conclusion is a cardinal equation, and a
cardinal inequality IS a truncated existence (HoTT Book Definition
10.2.7; `dev/literature/truncation-and-selection.md:72-86`;
`[LJ-1.316]` :117-119: the data demand is this project's own choice).
With `sq` out of the statement, no bare injection remains in either
trophy. The general rule is section 5.

### 7.2 Is `sq` a hypothesis: NO, it is a lemma

Devlin proves the square law en route and states the GCH without a
caveat (`dev/literature/devlin-II5.md:145-169`). A trophy with an
undischarged hypothesis claims a conditional Goedel's theorem, which is
less than the project's endpoint (`archive/dev/DECISIONS-archived.md:29`).
The statement drops `sq`; the proof owes it; the ledger already reads
the situation this way (`dev/ledger.toml:204`, "sq alone remains an
unsupplied Pi-parameter").

### 7.3 Which cardinal face: the CODED face, everywhere, from meaning

`⊨` is internal satisfaction. `IsCardinalL`'s refutand is literally the
model's truth value of the internal formula "some F injects κ into δ"
(`src/L/Cardinal.lagda.md:223-233`), so `IsCardinalL` says "L believes
κ is a cardinal", which is what "cardinal" means inside `L ⊨ GCH`. The
ambient face names a sub-class (`amb→code` with no converse,
`dev/PLAN.md:415-421`; `[LJ-1.314]` section 2.3), and it skips exactly
the κ where GCH-in-L has content under an adversarial ambient, since
`AmbientToCode` is independent (`[LJ-1.300]`, recorded at
`dev/PLAN.md:423-426`). The conclusion moves to the same face for the
same reason: an ambient injection between L-carriers is not a statement
L makes, and under a collapsed ambient it can hold for reasons that have
nothing to do with L, so the delivered conclusion is weaker than the
theorem's name (argument, not a built model). The delivered MIXTURE,
internal cardinals with ambient injections, appears in no source
(INFERRED: neither Devlin's nor Jech's statement has a second universe
to mix with; checked against the digest's statements of 5.6, 5.7 and
13.20). The fork registered at `dev/PLAN.md:410-431` closes on meaning,
as the brief ordered, not on cost: `[LJ-1.314]` had already measured
that no face is the cheap one.

### 7.4 Bound or equality: the EQUALITY, and it is not free

A set theorist reading GCH expects `2^κ = κ⁺`; a one-sided bound makes
the reader supply Cantor and leastness in their head, which is the exact
failure the acceptance test forbids. The reverse bound has no delivered
lemma (MEASURED, grep: no Cantor in `src/`). The statement names the
equality anyway and the proof pays; the price and its gate are in
section 4. The equality is spelled as mutual internal injections rather
than a coded bijection: the two texts prove exactly the two
inequalities, mutual injection IS cardinal equality under
Cantor-Bernstein, and a bijection spelling would force internal CSB or a
well-ordering conversion into every proof while adding no meaning. A
coded bijection is expressible today if ever wanted: `ranAt` carries
both directions (`src/L/Coding/Injection.lagda.md:230-248`).

### 7.5 Both trophies, one hand: they match at the semantic level

Both trophies are now internal-truth statements over `𝒮ʟ` with the same
∃ discipline. The literary difference stays and is right: AC is an
AXIOM, so it sits as a field of `isZFCModel`, which is Goedel's own
packaging of the headline "L ⊨ ZFC"; GCH is a THEOREM about the model,
so it is a Π-statement over the model, the exact `ChoiceStatement` and
`hasChoiceL` pattern (`src/L/Choice/Transversal.lagda.md:372-385`) that
the delivered GCH file's A7 comment already names as its model. The
match direction: GCH moves toward AC's internality; AC does not move.
DD4's answer: the shared object is the semantic frame itself, and the
statement adds no per-trophy device; the proof-side sharing is untouched
by this ruling.

## 8. Machine and process discipline

- Slot count before the one Agda run: 0 of 2, by the brief's exact
  command. One process, `GHCRTS="-A64m -I0 -M8g"`, cap not raised.
- The one run: `Statement.agda`, exit 0, wall 2.39 s, 1-minute load 4.39.
  MEASURED FALSE: any invocation past 30 minutes. MEASURED FALSE: any
  heap exhaustion.
- Writes: `lj-1.323-ruling.md` and `Statement.agda`, both in
  `agents/tasks/LJ-1-323/`. No edit outside the directory. No commit, no
  push, no `make check`.
- No constraint in the brief blocked the judgement.

## 9. ARCHIVE USED

- `archive/dev/DECISIONS-archived.md`, line read `:29` (D1): the endpoint
  is "the same L satisfies GCH, **stated internally**, yielding
  Con(ZF) → Con(ZFC + GCH) under the same relativization". TOOK: the
  retired route had already ruled the internal face at statement level;
  the delivered text drifted from it. WHAT DOES NOT TRANSFER: D1's route
  context and every price in the archived series; D33 and D39 are route
  economics, not statement content.
- `archive/dev/TASKS-archived.md`, lines read `:53` (T18, GCH scope gate,
  NO-GO) and `:126` (T91, walk the whole path, COMPLETE with owed gaps).
  TOOK, SHAPE ONLY: the retired route stated GCH as an unconditional
  endpoint with owed proof gaps, never as a conditional theorem. WHAT
  DOES NOT TRANSFER: its statement rode the Def-side internalization
  machinery that D39 replaced, so none of its statement text or prices
  carries.

## 10. LITERATURE USED

- `dev/literature/truncation-and-selection.md`: READ WHOLE. Line
  `:75-77`: a cardinal inequality is a truncated existence, HoTT Book
  10.2.7. TOOK: the ground for 7.1 and 7.4, the checklist for section 5,
  and section 2.7, AC does not untruncate, for the policy's rationale.
- `dev/literature/devlin-II5.md`: READ WHOLE. Line `:159-169`: 5.6, 5.7,
  5.8, the GCH as a cardinal equation and its relativization
  ZF ⊢ (GCH)^L. TOOK: the classical statement being ported is the
  relativized one; the square law is a lemma; the conclusion is an
  equation.
- `dev/literature/level-formula-slot-roles.md`: READ `:1-80`, the table
  and the three laws. WHY NOT the rest: the slot arithmetic binds the
  crossing formula, not the trophy statement; nothing there names
  truncation, faces or cardinal statements.
- Jech 13, Schindler-Zeman, HoTT Book, Kraus et al.: through the two
  digests above, at the locators they carry. WHY NOT re-fetched: the
  digests landed 2026-08-15 from the primary sources with mechanical
  label checks (`[LJ-1.316]` section 2.2), and this ruling takes only
  statement-level facts from them.
- `agents/tasks/LJ-1-316/lj-1.316-report.md`: READ WHOLE. Line
  `:117-119`: the data demand is the project's own choice. TOOK: 7.1.
- `agents/tasks/LJ-1-314/lj-1.314-report.md`: READ WHOLE. Line
  `:199-203`: ambient cardinals are a sub-class and an ambient-face
  trophy is a different theorem. TOOK: 7.3's class argument and the
  section 2.2 measurement.
- `agents/tasks/LJ-1-319/lj-1.319-ruling.md`: READ sections 4 to 7. Line
  `:175-185`: the data demand flagged to the owner with the re-spell
  exit. TOOK: the escalation this ruling answers.

## 11. What I re-derived and what I did not (the brief's one binding rule)

Re-derived here: the delivered statement text, read whole; the
no-consumer claims, my own greps; the face relationships, read at
`IsCardinalL`, `InjCode`, `Small` and the `amb→code` record; the
prop-ness of the new statement, typechecked, not asserted
(`isPropSuccCardL`, `isPropGCHStatement`, exit 0); `ranAt`'s two
directions, read at `src/L/Coding/Injection.lagda.md:241-248`.

Taken on the record, marked: the independence of `AmbientToCode`
(INFERRED from `[LJ-1.300]` via `dev/PLAN.md:423-426`; no model built
here); the HoTT Book numbers (the digest's mechanical label check); the
`[LJ-1.314]` closure table and consumer measurement.
