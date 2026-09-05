# LJ-1-270: why the Coq reification framework is unused on the AC side, and whether it still says nothing to GCH

> Recon over documents. No Agda ran. The reference clone of MetaZF at
> `../fol-reification/reference/_clone_MetaZF` was read directly, file by
> file, not through the review's summary. All line counts in this report are
> mine (`wc -l`) unless a file:line citation says otherwise.

## RETURN LEAD

**NO.** MetaZF does not bear on Bedrock's GCH side. The silence holds. Details
and the one boundary case are in section 1.

## 1. Question 3: does MetaZF bear on the GCH side? NO

**The silence holds, and it is MEASURED, not inferred.** I read the whole
MetaZF corpus: 20 `.v` files, 3,272 lines total, at
`../fol-reification/reference/_clone_MetaZF`.

A search for `formula`, `satisf`, `code`, `enco`, `de Bruijn`, `godel`,
`eval`, `⊨`, `⊧` across every `.v` file returns zero hits for the first
seven and only four `⊨` characters, all in comments that mean "the model
satisfies the ZF axioms" (`ZF/Universe.v:8`, `ZF/InnerModel.v:8`,
`ZF/InnerModel.v:65`, `ZF/Hierarchy.v:8`). **MEASURED.**

The structure class itself has no syntax. `ZF结构` (`ZF/ZF.v:9-14`) carries a
carrier `集`, membership `属 : 集 → 集 → Prop` as a host proposition, and
`空/并/幂/替` as total function operators. `替 : (集→集→Prop) → 集 → 集` eats
host relations. `分` is derived from `替` via a partial-identity relation.
Nothing in MetaZF represents a formula, a variable, a binder, or a
satisfaction relation.

The four load-bearing layers of the GCH wing have no MetaZF counterpart:

1. **A `Formula` layer.** `src/FOL/Syntax.lagda.md:44` defines `Formula K n`
   with de Bruijn variables `var : Fin n → Term K n`. MetaZF has no object
   language at all. **MEASURED.**
2. **De Bruijn slot handling.** `src/L/Coding/` (23 files, 13,055 lines,
   measured by me) names and reads variable slots (`Slot.lagda.md`,
   `Key.lagda.md`). MetaZF's only "slot" is the numeral embedding
   `嵌入 : nat → 𝓜` (`ZF/ZF.v:119`), which is not syntax. **MEASURED.**
3. **Satisfaction coding.** `src/L/Coding/Sat.lagda.md` evaluates one formula
   at a time. MetaZF evaluates nothing. **MEASURED.**
4. **Condensation with Σ₁ absoluteness.** `src/L/Condensation.lagda.md`
   (7,319 lines, measured by me) and `src/FOL/Absoluteness.lagda.md`. MetaZF
   has no Σ₁, no absoluteness, and no model-internal collapse. Its `相似`
   (`ZF/Embedding.v:27-33`) is a bisimulation between two different models.
   **MEASURED.**

**The boundary case, stated precisely.** MetaZF is NOT textually silent on
the ordinal-to-numeral ⊆ direction. It proves
`投影存在 : ∀ n ∈ ω, ∃ m : nat, 嵌入 m = n` (`ZF/Omega.v:118`), which is
exactly "every member of ω is a numeral image". But its route is not
transferable: its ω is the second-order minimal inductive set
`自然数 n := ∀ A, 归纳集 A → n ∈ A` (`ZF/Omega.v:14`), and its projection is
classical `iota` from `Coq.Logic.ClassicalDescription` (`ZF/Omega.v:3,128`).
Bedrock's direction must be definitional (the coded set's membership IS the
numeral image) and first-order. So review point ⑤'s claim
「序数↔数码⊆方向，全是我们的活」 is true in the sense that MetaZF's route
contributes nothing, and not true in the sense that MetaZF has no such
theorem. The silence holds for the GCH work.

**Verdict on the abort criterion.** THE SILENCE HOLDS. Question 3 is answered
NO with evidence. This is the STOP outcome.

## 2. Question 1: why is the Coq reification framework unused on the AC side?

**The recorded verdict.** `../fol-reification/docs/governance/METAZF-REVIEW.md:6`
holds the one-sentence conclusion: 「架构已验证,无需重写」 (the architecture is
verified, no rewrite needed). It was settled 2026-06-15 by a fourteen-agent
workflow, line by line against MetaZF source, and recorded at
`GOAL-DRIVEN-DECISIONS.md:5` point ①.

The reason is at `METAZF-REVIEW.md:14-16`: MetaZF's closure machinery (the
`替代封闭类` field of `封闭类`, the `内模型` functor, `分`-from-`替`) grants
second-order separation and replacement silently. Importing it would collapse
the first-order definability distinction that Bedrock's Def/Formula design
exists to keep. `ZF/InnerModel.v:14` confirms the shape: `ℙ : Type :=
Σ x, x ∈ₚ P`, a subtype carrier over host predicates.

**Is the verdict stale?** NO. **MEASURED.**

- All six per-item wins are visible in the delivered tree, at the citations
  in section 3. Nothing the review closed has been reopened.
- The AC trophy landed. `dev/PLAN.md` row `[LJ-1.9]` reads "the bar was fixed
  when the AC trophy landed".
- The route change (RUD to the two-tower bridge, `archive/dev/DECISIONS-archived.md:58`
  row D39, 2026-08-09) moved the AC side's suppliers: the trophy now rides
  the bridge between the Def tower and the J tower. MetaZF has no rud, no J,
  and no bridge. A search for `rud`, `Jensen`, `definab`, `constructib`
  across the corpus returns zero hits. **MEASURED.** The new content sits
  outside MetaZF's scope, so nothing the review closed could be reopened by
  it.

## 3. Question 2: why was it not needed? The measured per-item table

The per-item table is `METAZF-REVIEW.md` section 1, and it is measured: each
row names a MetaZF cost at file:line and a Bedrock native win. I re-verified
the MetaZF side of every row against the corpus. **Every row is a REAL win,
not a preference:** each removes an axiom or a hand proof from the host. The
wins below cite both sides.

| # | MetaZF pays | Bedrock has | Verdict |
|---|---|---|---|
| 1 | `δ` unique-choice trick (`ZF/Basic.v:333`) | `℩` isContr projection, zero axioms (`src/FOL/ZFModel.lagda.md:379` `ω = ℩ hasInfinity`) | REAL: an axiom-free projection replaces a classical detour |
| 2 | Global `ProofIrrelevance` axiom (`ZF/Basic.v:3` `Require Export Classical ProofIrrelevance`) | hProp membership: proof irrelevance is a theorem | REAL: an axiom becomes a theorem |
| 3 | `正则` as a class axiom, inductive accessibility (`ZF/ZF.v:53`) | `foundationV` via `elimProp` + `isPropAcc`, zero axioms (`src/V/Model.lagda.md`, `regularityV`) | REAL: an axiom becomes a theorem |
| 4 | Classical `iota` projection (`ZF/Omega.v:3,128`) | `∈-asFiber` + `identityPrinciple`, non-truncated reversible fibers (`src/V/Smallness.lagda.md:69-81`) | REAL: no choice-like operator |
| 5 | `proof_irrelevance` Σ-carrier (`ZF/InnerModel.v:14,46-48`) | `_↾_` + `↾-reflects`, `Σ≡Prop` free | REAL: carrier equality is a proposition for free |
| 6 | Hand-proved bisimulation `相似的函数性` (`ZF/Embedding.v:58`) | SIP/extensionality, collapse uniqueness free (`src/V/Collapse.lagda.md`) | REAL: a hand proof becomes a free theorem |

The review's own wording is stronger than mine: cubical native resources win
at every pricing point (`METAZF-REVIEW.md:6`). My reading confirms the claim
holds against MetaZF's source, not just against the review's summary.

## 4. The eight not-to-borrow items

`METAZF-REVIEW.md` section 5 lists them. All eight were NOT taken. Each was
checked against the delivered tree. **MEASURED.**

1. **Inductive `Ord`** (`ZF/Ordinal.v:11-13`). NOT taken. Bedrock keeps
   `IsOrd` (`src/L/Ordinal.lagda.md:45,77`).
2. **`有穷`/`遗传有穷` predicates** for "finite ordinal = numeral"
   (`ZF/Finiteness.v:9-11`). NOT taken. I read the whole file: the predicate
   never mentions `Ord` or `ω`. Bedrock's numerals are definitional via the
   library `#` (`src/V/Model.lagda.md:169`).
3. **The `封闭类→内模型` functor / `替代封闭类` field** (`ZF/ZF.v:106-111`,
   `ZF/InnerModel.v`). NOT taken. Only the subtype-carrier shape transferred,
   and Bedrock already had it as `_↾_`.
4. **`分`-from-`替`**, second-order full separation. NOT taken. Bedrock's
   Δ₀ separation is zero-axiom (`sepΔ₀`); full separation pays `VResizing`.
5. **`δ` / `集化大消除`** (`ZF/Basic.v:333,348`). NOT taken. `℩` is in place.
6. **The constructor-free comparison route** (`层对关系的归纳法`,
   `ZF/Hierarchy.v:37`). NOT taken. Bedrock keeps its constructor route
   for the h-set host.
7. **`相似`/categoricity as a Mostowski tool** (`ZF/Embedding.v`,
   `ZF/Categoricity.v:18`). NOT taken. Bedrock's collapse is model-internal
   via SIP (`src/V/Collapse.lagda.md:1`).
8. **Universe/ZFₙ level counting and the HF decidable layer**
   (`ZF/Universe.v:10`, `ZF/MinimalModel.v`, `HF/`). NOT taken. HIT-V members
   are true hProps and ω is infinite.

## 5. The four deferred transferables, and whether Bedrock took any

`METAZF-REVIEW.md` section 6 lists them. Two were taken, two were not.

1. **`adj x y = y ∪ ⁅x⁆s` + `adj-mem`.** NOT taken. The union/pairing/
   singleton boilerplate is still written out at
   `src/V/Model.lagda.md:185-192` (`numeralV`, `numeralV≡#`,
   `pair-singleton`). The third duplication the review waited for
   (`hasInfinityₗ`) appeared and was resolved WITHOUT `adj`, by the
   ∈ˢ-extensional pinning and chain-transport route that is now a measured
   law (`../fol-reification/docs/WORKLOG.md` §5 case 11). `adj` still applies
   as DRY, but it sits on no path.
2. **`defSet≡` reuse lemma.** TAKEN. `src/L/Axioms/Basic.lagda.md:328-329`
   states `defSet≡` (the carved set equals the finite family), and it feeds
   `finSet∈𝒟ₒ` and `finSetL`. The review's blowup-prevention prescription
   (keep φ and the target abstract) was implemented by a different mechanism:
   `sealedDefSet` as an opaque SET (`WORKLOG.md` §5 case 8). Same law, other
   tool.
3. **`hasInfinity` round trip without classical `iota`.** TAKEN.
   `src/L/Axioms/Infinity.lagda.md:94-95` (`hasInfinityL = uniqueL isNumeralL
   (ωʟ , ω-specL)`). ω's sett-membership is definitionally the numeral
   image. No `ω = I ∩ₚ 自然数` (`ZF/Omega.v:15`) and no `iota`. The round
   trip became a measured law (`WORKLOG.md` §5 case 11, the [E] obligation
   shape fix).
4. **The intersection-again ordinal trichotomy reserve**
   (`ZF/Ordinal.v:203,211-221`). NOT taken. `ord-tri` was built directly at
   `src/L/Ordinal/Linear.lagda.md` by ⊆ᵇ-comparison and LEM. The `precedes`
   comparison at `L.Choice.Finite` uses a different technique (first point of
   disagreement, layer key first). The reserve still applies only as a
   lem-cone restructure, which the review itself said saves no lem budget.
   Its non-use matches the review's own assessment.

## 6. DD4: power-set monotonicity and the two-tower bridge

MetaZF is a third development beside Bedrock's two towers. It has ONE tower,
stepped by `𝒫`, and ONE proof. It has no rud, no J, no bridge, and no second
proof to share with. **MEASURED** (zero corpus hits for rud, Jensen,
definable, constructible). A single-tower development cannot model sharing
between two proofs, so it suggests nothing new for Def/J sharing.

The `幂单调` difference does not bear on the bridge. MetaZF's level comparison
(`层线序_引理`, `ZF/Hierarchy.v:51-63`) and its limit-level closure
(`极限层对幂集封闭`, `ZF/Hierarchy.v:232-257`) rest on power-set monotonicity
(`ZF/Basic.v:233`), which the `𝒟` step lacks. That is why the review ruled
those proofs non-portable and Bedrock uses WFI-rank instead (`METAZF-REVIEW.md`
sections 2 and 3). Neither Bedrock tower steps by `𝒫`: the Def tower steps by
`Def`, the J tower steps by rud closure (Schindler-Zeman Definition 1.6, as
recorded in `dev/literature/j-hierarchy.md`). The bridge's content is the
comprehension theorem and the reindexing, which are first-order and
rudimentary facts that MetaZF has no apparatus for. The only way `幂单调`
bears on the bridge is negative: it is why MetaZF's generation-data-style
level proofs cannot be borrowed at all, and the J tower's generation data is
the other horn of D-26, which Bedrock already knows. This last judgment (that
the bridge does not need power-set monotonicity) is INFERRED from the bridge's
content as described in the literature digests, since no Agda ran.

## ARCHIVE USED

One line per file read.

- `../fol-reification/docs/governance/METAZF-REVIEW.md` :6 the one-sentence
  verdict 「架构已验证,无需重写」, read whole (69 lines).
- `../fol-reification/docs/governance/GOAL-DRIVEN-DECISIONS.md` :5 point ⑤,
  the silence statement 「MetaZF 沉默处=一阶核心(无 Formula 层)」, read whole
  (172 lines).
- `../fol-reification/docs/WORKLOG.md` §5 header: the conversion-blowup
  playbook; case 11 (the `hasInfinity` [E] fix) and case 8 (`sealedDefSet`)
  are the measured laws that absorbed two of the review's transferables.
- `dev/PLAN.md` :28-29 the sibling checkout record and its pin `8b190d5`;
  §11 rows `[LJ-1.7]`, `[LJ-1.8]`, `[LJ-1.9]` for the current goal status.
- `archive/dev/DECISIONS-archived.md` :58 row D39, the two-tower bridge
  route, which supersedes every earlier route ruling.
- `archive/dev/TASKS-archived.md` :262 row T257, the GCH wing price on the
  internalization route, for the shape of the route the verdict predates.
- `archive/dev/STATUS-archived.md` :98-99 rows L3.30/L3.31, the rud
  re-architecture history, for the shape of the retired RUD route.
- The MetaZF corpus itself, `../fol-reification/reference/_clone_MetaZF`,
  20 `.v` files, 3,272 lines, read as the primary source for every claim
  about MetaZF.

## LITERATURE USED

YES, the literature bears on the choice. Devlin, Constructibility (1984),
presents L by first-order definability and J by rudimentary functions, and
the project's own digest `dev/literature/devlin-II5.md:9-11` frames every
condensation step as "Def tower (syntax) or J tower (generation data)", which
is exactly the Formula-layer versus Formula-free choice. Schindler-Zeman and
Mathias (`dev/literature/j-hierarchy.md`, `dev/literature/rudimentary-functions.md`)
supply the rud side. None of them favors a Formula-free second-order
presentation as a replacement for the Formula layer, and the review itself
(`METAZF-REVIEW.md:14-16`) records that such a presentation collapses the
first-order definability distinction. Why not used further: Devlin and the
digests are already Bedrock's source for both towers, so they add nothing
new; MetaZF's own `ZF.v` was checked directly instead.
