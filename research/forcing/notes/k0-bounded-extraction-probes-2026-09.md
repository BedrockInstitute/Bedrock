# K0 bounded extraction and unique semantic values

Date: 2026-09-08. Source baseline: `c451387629f0817feb6b26db7281251983f219d8`. Status: three safe probes checked; K0 remains in progress. This follow-up retires the generic bounded-extraction universe risk and checks obtaining a unique Boolean value without choosing a bound. It does not prove the internal ultrafilter theorem, internal name closure or the forcing compiler. See the [roadmap](cohen-implementation-roadmap-2026-09.md), [no-host-choice policy](no-host-choice-audit-2026-09.md), and [previous ordinary-model probes](k0-ordinary-model-probes-2026-09.md).

## 1. Actual bounded selection in L

The agent ran this command from `/tmp/bedrock-k0-probes/extraction/compile-root`:

```text
GHCRTS="-A64m -I0 -M8g" agda src/BoundedExtraction.agda
```

Exit 0; the final log contains only the checking message. The coordinator reviewed the complete source and log. The probe uses actual existing `stage`, `stage-below`, `orderAt`, `Lset→isL`, `leastOf` and `isPropLeastOf`, not an assumed new selector. It returns an actual witness and proves independence of the input existence witness.

Exact public contract, schematically:

```text
LEM (ℓ-suc ℓ)
B : LSet
P : LSet → hProp (ℓ-suc ℓ)
∥ Σ U : LSet, U ∈ B × P(U) ∥
  → Σ U : LSet, U ∈ B × P(U)
```

B here is the bounding set, not the forcing Boolean algebra. For ultrafilter extraction it will be the L-internal power set PB. P may be an arbitrary host hProp predicate at the stated level: selection works because the bounded carrier has a proved actual well-order. This does not prove P is internally definable, that its satisfying objects form an L-set, or that any witness exists. Those are separate obligations for applying the theorem to ultrafilters. There is no selector for arbitrary host types and no global L well-order premise.

The smaller birth stage of the bounding set suffices; the larger `InternalWellOrder.Bound` stage proposed by the earlier audit is unnecessary for this probe. Ambient stage members and restricted L elements are connected by actual subtype transports. All relevant levels normalize to `ℓ-suc ℓ`, so this generic extraction introduces neither a higher LEM instance nor a host choice axiom.

The source dependencies were copied from the isolated research worktree; the agent reports all 123 copied baseline source files byte-identical after compilation. Existing copied caches were reused, no `Everything` check ran, and no repository source/cache was written. Two setup failures (module search path and a name clash with `lift`) were corrected before the successful check; they were not unresolved mathematical obligations. The temporary evidence report is `/tmp/bedrock-k0-probes/extraction/REPORT.md`.

## 2. Return the unique value, not a selected bound

The coordinator ran these serial commands from `/tmp/bedrock-k0-probes/names`:

```text
GHCRTS="-A64m -I0 -M8g" agda UniqueValue.agda
GHCRTS="-A64m -I0 -M8g" agda UniqueValueInstance.agda
```

Both exited 0 without warnings. `UniqueValue` is universe-polymorphic in the target domain, value carrier, proposition-valued relation and certificate types. Given antisymmetry, it proves that a value paired with its full least-upper-bound specification is a proposition. Thus truncated existence of such a value yields the actual uniquely specified value. More generally, from merely inhabited bound certificates and a proof that each certificate computes the required LUB, it returns that value without returning or selecting a certificate. Two different certificate types give the same value.

No LEM, Choice, DC, resizing or Boolean maximum principle is used. Antisymmetry and proposition-valued order are explicit assumptions. The theorem does not manufacture a supremum or a bound without an existence proof. It is not unrestricted completeness for all host families; it is an extraction principle once sufficient existence/correctness has been established.

`UniqueValueInstance` connects this generic construction to the previously checked `Bounds` predicate over the infinite carrier of finite binary names. Merely having a sufficient bound gives an actual Boolean value and its upper/least specification. The value agrees with every sufficient bound and equals the partial value `a`; the four-code bound is an explicit instance. No representative bound is extracted. Internal Separation/Collection must still construct the relevant existence/correctness evidence for genuine fixed-formula forcing semantics.

## 3. K0 decisions and remaining work

Accepted direction: generic quantifier evaluation may consume merely existing adequate bounds and return the unique specified truth value. It must not require a globally selected rank bound or name witness for every formula/parameter tuple. Fullness remains a later, formula-indexed propositional theorem.

Accepted bounded-extraction interface: the L instance can obtain actual candidate data from a nonempty bounded hProp predicate using only the existing successor-level LEM. This resolves the generic extraction plumbing and universe maxima. It does not close K12b; the actual ultrafilter predicate, internal existence theorem and Boolean-operation decoding are still missing.

K0 remains open primarily at the production internal-name representation, code/support/weight closure, and noncircular fixed-formula internal value-set/Collection interface. The general completeness/ultrafilter theorem and full quotient truth remain K2/K12/K13 implementation packages rather than requirements to prove in full during K0. Next briefs should test those representation and internalization contracts, not repeat the now-checked extraction examples.

## 4. Checked source snapshots

These text fences archive the exact probe sources, not production imports.

### extraction/compile-root/src/BoundedExtraction.agda

SHA-256: `728579ec062f3c0d8fbb41b633665139088509a53d647e7cbd724b07e3d3eed9`

```text
{-# OPTIONS --cubical --safe --guardedness #-}

open import Base.Prelude
open import Base.Classical using ( LEM )

module BoundedExtraction {ℓ : Level} (lem : LEM (ℓ-suc ℓ)) where

open import FOL.ZFStructure using ( module hPropStructure )
open import V.Hierarchy {ℓ} using ( 𝒮ᵥ )
open import L.Constructible {ℓ} using ( 𝒮ʟ; isL; Lset; Lset→isL )
open import L.Stage {ℓ} lem using ( stage; stage-ord )
open import L.Choice.FirstIntersectionStage {ℓ} lem using ( stage-below )
open import L.Choice.StageOrders {ℓ} lem using ( Mem; orderAt )
open import L.WellOrder.Base {ℓ-suc ℓ} using ( SWO; IsLeast; leastOf; isPropLeastOf )
open import Cubical.Data.Sigma using ( Σ≡Prop )
open import Cubical.Foundations.HLevels using ( isProp× )
import Cubical.HITs.PropositionalTruncation as PT
open PT using ( ∥_∥₁; ∣_∣₁ )

open hPropStructure 𝒮ᵥ using () renaming ( S to VSet; _∈ˢ_ to _∈ᵛ_ )
open hPropStructure 𝒮ʟ using () renaming ( S to LSet; _∈ˢ_ to _∈ʟ_ )

module _ (B : LSet) (P : LSet → hProp (ℓ-suc ℓ)) where

  Witness : LSet → Type (ℓ-suc ℓ)
  Witness U = ⟨ U ∈ʟ B ⟩ × ⟨ P U ⟩

  Candidate : Type (ℓ-suc ℓ)
  Candidate = Σ[ U ∈ LSet ] Witness U

  γ : VSet
  γ = stage (fst B) (snd B)

  StageMember : Type (ℓ-suc ℓ)
  StageMember = Mem (Lset γ)

  toL : StageMember → LSet
  toL (x , h) = x , Lset→isL γ (stage-ord (fst B) (snd B)) x h

  w : SWO StageMember
  w = orderAt γ (stage-ord (fst B) (snd B))

  Q : StageMember → hProp (ℓ-suc ℓ)
  Q a = Witness (toL a) , isProp× (snd (toL a ∈ʟ B)) (snd (P (toL a)))

  intoStage : Candidate → Σ[ a ∈ StageMember ] ⟨ Q a ⟩
  intoStage (U , p) = a , subst Witness (sym e) p
    where
    a : StageMember
    a = fst U , stage-below (fst B) (snd B) (fst U) (fst p)

    e : toL a ≡ U
    e = Σ≡Prop (λ x → snd (isL x)) refl

  leastCandidate : ∥ Candidate ∥₁ → Σ[ a ∈ StageMember ] IsLeast w Q a
  leastCandidate e = leastOf w lem Q (PT.map intoStage e)

  fromLeast : (Σ[ a ∈ StageMember ] IsLeast w Q a) → Candidate
  fromLeast (a , p , m) = toL a , p

  extract : ∥ Candidate ∥₁ → Candidate
  extract e = fromLeast (leastCandidate e)

  extract-independent : (e f : ∥ Candidate ∥₁) → extract e ≡ extract f
  extract-independent e f =
    cong fromLeast (isPropLeastOf w Q (leastCandidate e) (leastCandidate f))

  witness-independent : (a b : Candidate) → extract ∣ a ∣₁ ≡ extract ∣ b ∣₁
  witness-independent a b = extract-independent ∣ a ∣₁ ∣ b ∣₁
```

### names/UniqueValue.agda

SHA-256: `587492897c6be8755e44ab1e4981732278f99c31efb649f26c1c84c83fb4509d`

```text
{-# OPTIONS --cubical --safe --guardedness #-}

module UniqueValue where

open import Cubical.Foundations.Prelude using
  ( Level; Type; _≡_; cong; isProp )
open import Cubical.Foundations.HLevels using
  ( hProp; isPropΠ; isProp× )
open import Cubical.Data.Sigma using
  ( Σ; _×_; _,_; fst; snd; Σ≡Prop )
open import Cubical.HITs.PropositionalTruncation using ( ∥_∥₁ )
import Cubical.HITs.PropositionalTruncation as PT

module Supremum {ℓs ℓb ℓr : Level}
  (S : Type ℓs) (B : Type ℓb) (R : B → B → hProp ℓr)
  (antisym : (a b : B) → fst (R a b) → fst (R b a) → a ≡ b)
  (φ : S → B) where

  Upper : B → Type _
  Upper b = (x : S) → fst (R (φ x) b)

  upper-is-prop : (b : B) → isProp (Upper b)
  upper-is-prop b = isPropΠ (λ x → snd (R (φ x) b))

  Specification : B → Type _
  Specification b = Upper b × ((c : B) → Upper c → fst (R b c))

  specification-is-prop : (b : B) → isProp (Specification b)
  specification-is-prop b = isProp× (upper-is-prop b)
    (isPropΠ (λ c → isPropΠ (λ _ → snd (R b c))))

  Result : Type _
  Result = Σ B Specification

  result-is-prop : isProp Result
  result-is-prop (a , au , al) (b , bu , bl) =
    Σ≡Prop specification-is-prop (antisym a b (al b bu) (bl a au))

  realize : ∥ Result ∥₁ → Result
  realize = PT.rec result-is-prop (λ r → r)

  module Certificates {ℓc : Level} (C : Type ℓc)
    (value : C → B) (correct : (c : C) → Specification (value c)) where

    from-bound-existence : ∥ C ∥₁ → Result
    from-bound-existence = PT.rec result-is-prop (λ c → value c , correct c)

    independent : (p q : ∥ C ∥₁)
      → fst (from-bound-existence p) ≡ fst (from-bound-existence q)
    independent p q = cong fst
      (result-is-prop (from-bound-existence p) (from-bound-existence q))

  compare-certificates : {ℓc ℓd : Level} (C : Type ℓc) (D : Type ℓd)
    (cv : C → B) (dv : D → B)
    (cs : (c : C) → Specification (cv c))
    (ds : (d : D) → Specification (dv d))
    (p : ∥ C ∥₁) (q : ∥ D ∥₁)
    → fst (Certificates.from-bound-existence C cv cs p)
      ≡ fst (Certificates.from-bound-existence D dv ds q)
  compare-certificates C D cv dv cs ds p q = cong fst
    (result-is-prop (Certificates.from-bound-existence C cv cs p)
      (Certificates.from-bound-existence D dv ds q))
```

### names/UniqueValueInstance.agda

SHA-256: `f10a034369e17dc25a4f8d37a526e28e7963cd4f0e6a5f4d9dc8116390ed8f50`

```text
{-# OPTIONS --cubical --safe --guardedness #-}

module UniqueValueInstance where

open import Cubical.Foundations.Prelude using ( Type; _≡_; refl; cong; _∙_ )
open import Cubical.Data.Sigma using ( _,_; fst; snd )
open import Cubical.HITs.PropositionalTruncation using ( ∥_∥₁; ∣_∣₁ )
open import Names using ( Name; B; a; _≤ᴮ_ )
open import Bounds using
  ( φ; RangeBound; existentialValue; bound-upper; bound-least
  ; order-is-prop; order-antisymmetric; twoBound; fourBound; existential-partial )
open import UniqueValue using ( module Supremum )

module Value = Supremum Name B
  (λ b c → (b ≤ᴮ c) , order-is-prop b c) order-antisymmetric φ

Bound : Type₀
Bound = RangeBound Name φ

correct : (c : Bound) → Value.Specification (existentialValue c)
correct c = bound-upper c , bound-least c

module FromBound = Value.Certificates Bound existentialValue correct

value-from-mere-bound : ∥ Bound ∥₁ → B
value-from-mere-bound e = fst (FromBound.from-bound-existence e)

value-specification : (e : ∥ Bound ∥₁)
  → Value.Specification (value-from-mere-bound e)
value-specification e = FromBound.from-bound-existence e .snd

value-agrees-with-every-bound : (e : ∥ Bound ∥₁) (c : Bound)
  → value-from-mere-bound e ≡ existentialValue c
value-agrees-with-every-bound e c = cong fst
  (Value.result-is-prop (FromBound.from-bound-existence e)
    (existentialValue c , correct c))

partial-value-from-any-mere-bound : (e : ∥ Bound ∥₁)
  → value-from-mere-bound e ≡ a
partial-value-from-any-mere-bound e =
  value-agrees-with-every-bound e twoBound ∙ existential-partial

four-code-result : value-from-mere-bound ∣ fourBound ∣₁ ≡ a
four-code-result = partial-value-from-any-mere-bound ∣ fourBound ∣₁
```

