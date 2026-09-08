# K0 audit: obtaining one ordinary ultrafilter from `L`

Date: 2026-09-08. Baseline: `f61112d4`. This is a read-only source audit, reviewed against the named definitions by the coordinator. The proposed extraction is not yet a checked Agda probe. See the [ordinary-model probe ledger](k0-ordinary-model-probes-2026-09.md) and [Cohen roadmap](cohen-implementation-roadmap-2026-09.md).

## Result

There is a viable **bounded canonical-extraction route**, but the theorem that
starts it is absent.  The existing development proves the model-level Choice
field for `L`; it does not yet prove the Boolean prime ideal/ultrafilter theorem
inside that model.  Once a missing theorem returns truncated existence of an
`L`-set `U` which is a subset of the given `B`, the existing stage well-order and
`leastOf` can select a particular such `U` without host `SetChoice`.

Bell's Theorem 4.1 supports the intended endgame: an **arbitrary ordinary**
ultrafilter `U` on `B`, together with the Maximum Principle/fullness, suffices
for the two-valued quotient truth theorem.  It need not be `L`-generic or
externally complete (`dev/literature/bell-2005-boolean-valued-models.fulltext.md:4939-4970`,
PDF page 109 / printed page 89).  Genericity first appears after Theorem 4.1 as
the stronger `P^(M)(B)`-completeness condition.  Thus the ordinary-`U` quotient
branch can avoid construction of an `L`-generic filter, provided K12a really
proves fullness and K12b constructs/decodes `U` as below.

## 1. Missing internal existence theorem

The reusable input should be a theorem specialized only to the model's Boolean
algebra interface, schematically

```text
internal-ultrafilter-exists :
  (B : LSet) -> InternalNontrivialBA B ->
  ∥ Sigma[ U ∈ LSet ] (U ⊆ˢ B × InternalUltrafilter B U) ∥₁
```

or, better for extraction, with the power-set membership packaged explicitly:

```text
  ∥ Sigma[ U ∈ LSet ] (U ∈ˢ PB × InternalUltrafilter B U) ∥₁
```

where `PB = ℩ (isZFModel.hasPower L⊨ZF B)` and `℩-spec` identifies
`U ∈ˢ PB` with `U ⊆ˢ B`.  `hasPowerL` already has the exact semantic
specification

```text
hasPowerL : (a : S) -> isContr (SetOf (lambda x -> x ⊆ˢ a))
```

at `src/L/Axioms/Power.lagda.md:237-246`.  The model record supplies only
first-order Separation/Replacement and power set at
`src/FOL/ZFModel.lagda.md:217-230`.

No ultrafilter/filter/Boolean-algebra theorem exists in the current `src` tree.
In particular, `L⊨ZFC` merely installs

```text
L⊨ZFC : isZFCModel
L⊨ZFC = record { zf = L⊨ZF ; hasChoice = hasChoiceL L⊨ZF }
```

(`src/L/Model.lagda.md:91-107`).  Its Choice field is the disjoint-family
transversal statement, with a **truncated** choice-set conclusion
(`src/FOL/ZFModel.lagda.md:473-484`).  The concrete proof
`hasChoiceL : (zf : isZFModel) -> ChoiceStatement zf` also returns a truncation
(`src/L/Choice/Transversal.lagda.md:421-432`).  A direct semantic proof of the
ultrafilter lemma, or a formal object-language derivation of the ultrafilter
theorem plus soundness, is still required.  One cannot cite the `hasChoice`
record field as though every ZFC consequence were already implemented.

The missing proof must keep the construction set-sized: work with the internal
power set of this one `B` (and, for a Zorn/well-order recursion, a set of partial
filters or subsets of `B`).  It must not collect all formula constants or all
objects of the proper-class `L` carrier into a set.  The internal completeness
of `B` is useful for forcing semantics but is not what proves ordinary
ultrafilter existence; internal Choice/Boolean prime ideal reasoning does.

## 2. Decoding the selected `L`-set as an ordinary ultrafilter

Here and below, `LSet` denotes the restricted carrier of `𝒮ʟ`, whose elements
are pairs `(x : V ℓ , isL x)`; `VSet = V ℓ` denotes the ambient hierarchy
carrier.  Source modules often call either locally opened carrier `S`, so the
distinction must be made explicit in the new API.

For `B : LSet`, K1/K2 must expose an interpreted host Boolean carrier whose points
have `L` representatives in `fst B`, and prove that interpreted `0`, `1`, meet,
join and complement agree with the internal coded operations.  For an actual
`U : LSet`, define ordinary membership pointwise by

```text
b ∈U  =  ⟨ rep b ∈ˢ U ⟩
```

This is already a host h-proposition; no choice is involved.  The missing
decode theorem should transport the internal clauses to an ordinary proper
filter and prove the ultrafilter dichotomy/maximality on the interpreted
carrier.  Suggested contract:

```text
decode-ultrafilter :
  U ∈ˢ PB -> InternalUltrafilter B U ->
  OrdinaryUltrafilter (interpretBA B)
```

The transport proof needs named operation-correctness and carrier-surjectivity
lemmas from K1/K2.  Internal disjunction/existence is propositional truncation:
the hProp interpretation uses truncated sigma for `⋁`
(`src/Base/Truth.lagda.md:119-130,148-151`).  Therefore a proof of an internal
clause such as "`b ∈ U` or `¬b ∈ U`" must not simply be pattern-matched as a
host coproduct.  Either state ordinary ultrafilter primeness as an hProp, or use
the supplied `LEM (ℓ-suc ℓ)` to decide the two membership propositions and
derive the required data.  Record this use explicitly.

No external completeness of `U` should be claimed.  In Bell's existential
case, an arbitrary ultrafilter does not preserve the defining arbitrary join;
fullness first supplies a single name attaining the existential Boolean value,
after which ordinary filter closure suffices.  This is exactly why K12a and
K12b must stay separate.

## 3. Canonical extraction from truncated existence

The reusable eliminator is already present:

```text
leastOf : {ℓ'' : Level} -> LEM (ℓ-max ℓc (ℓ-max ℓp ℓ''))
        -> (P : A -> hProp ℓ'')
        -> ∥ Sigma[ a ∈ A ] ⟨ P a ⟩ ∥₁
        -> Sigma[ a ∈ A ] IsLeast P a
```

at `src/L/WellOrder/Base.lagda.md:169-183`; uniqueness/propositionality is
`isPropLeastOf` at lines 147-155.  Thus truncation is eliminated only because
"the least candidate" is unique, not because internal AC has become host
choice.

Use the precise bounded carrier

```text
A = Mem (Lset gamma)  -- ambient V members
```

where `Mem A = Sigma[ x ∈ VSet ] ⟨ x ∈ A ⟩` has type `Type (ℓ-suc ℓ)`
(`src/L/Choice/StageOrders.lagda.md:255-262`) and

```text
orderAt : (gamma : VSet) -> IsOrd gamma -> SWO (Mem (Lset gamma))
```

is exported at `src/L/Choice/StageOrders.lagda.md:790-792`.
Here `gamma : VSet`: `StageOrders` opens the ambient hierarchy structure, so its
`S` and `Mem` are not the restricted carrier of `𝒮ʟ`.
A concrete safe choice is `gamma = stageBound (fst PB) (snd PB) .fst`, or the smaller birth
stage if its membership proof is convenient.  `stageBound` and its ordinal
proof are at `src/L/Choice/FirstIntersectionStage.lagda.md:255-262`, while
`stage-below` at lines 245-248 maps every `U ∈ˢ PB` into the required
`U ∈ˢ Lset gamma` (followed by `Lset-mono` for `stageBound`).  Equivalently,
`L.Choice.InternalWellOrder.Bound (fst PB) (snd PB)` exposes `boundOrd`,
`boundOrd-ord`, and
`boundOrder : SWO (Mem (Lset boundOrd))` at
`src/L/Choice/InternalWellOrder.lagda.md:770-793`.

Map the missing restricted-carrier witness `(U : LSet , U∈PB , uf)` to the
ambient-stage member `((fst U , U∈Lgamma) : Mem (Lset gamma))`.  Conversely, a
candidate `(x , hx) : Mem (Lset gamma)` is lifted back to the restricted carrier
as

```text
xL = (x , Lset→isL gamma ordGamma x hx) : LSet
```

and the hProp candidate predicate says `xL ∈ˢ PB` and
`InternalUltrafilter B xL`.  For the mapped witness, proof irrelevance in the
`isL` subtype identifies this reconstructed `xL` with the original `U`, allowing
`U∈PB` and `uf` to transport.  Apply `leastOf` on the ambient `Mem` carrier; its
selected ambient set is then lifted by the displayed `Lset→isL` proof to return
the requested specific `U : LSet`.  Candidates do **not** need to be enumerated as a host family,
and no global `SWO S` is needed.  `smallDom` is not the right escape hatch here:
it only accepts `X : Type ℓ` (`src/L/Recursion.lagda.md:141-150`), whereas
`Mem` and the `L` carrier live at `Type (ℓ-suc ℓ)`.

Universe ledger: for `A = Mem ...`, the carrier and its order propositions are
at the successor level (`Mem : Type (ℓ-suc ℓ)` and `relOf : ... -> Type
(ℓ-suc ℓ)`).  If `InternalUltrafilter B U` is kept as an hProp at
`ℓ-suc ℓ`, `leastOf` asks for `LEM (ℓ-suc ℓ)` after maxima normalize, matching
the current module parameter.  This is a source-level expectation, not a
checked theorem: K1/K2's actual Boolean carrier and the final predicate's
inferred universe must be compiled before the assumption ledger is closed.

## Pitfalls and next probe

- Do not use `PT.rec` directly into `S`, a quotient carrier, a coproduct, or an
  ordinary-ultrafilter record.  The least-candidate sigma is eliminable because
  `isPropLeastOf` proves it is a proposition.
- Do not seek a global canonical well-order of the proper-class carrier `S`.
  The existing API is explicitly stage bounded.
- Do not confuse the internal transversal `hasChoiceL` with `SetChoice`; the
  latter is the host principle used by `V.Model.ChoiceLemma`
  (`src/V/Model.lagda.md:508-531`) and is absent from the `L` construction.
- Do not require `U` to meet every dense set in `L`.  Bell 4.1 plus fullness
  uses any ordinary ultrafilter; genericity is a later, stronger property.
- Do not claim that this route preserves the LEM budget until the internal
  ultrafilter proof, candidate hProp, and decode theorem typecheck.

Recommended next safe probe: in a temporary module, define only an abstract
`InternalUltrafilter : LSet -> LSet -> hProp (ℓ-suc ℓ)` and assume the precise
truncated theorem above.  Instantiate `PB`,
`Bound (fst PB) (snd PB)`, map `fst U` into
`Mem (Lset Bound.boundOrd)`, and typecheck the `leastOf` extraction.  This will
settle the universe maxima and stage-membership plumbing independently of the
substantive Boolean prime ideal proof and independently of K13's quotient.
