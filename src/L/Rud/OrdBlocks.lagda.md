# The ordinal extension

<!--en-->
The bridge between the two towers runs on ordinals, and its endpoints read the
rud tower one block of `ω` successors above a given index. This chapter
delivers that extension: the operation `+ω`, its membership read in both
directions, the facts that the base and every finite iterate lie inside it,
its ordinality, and the law the endpoints spend: the extension of an ordinal
is a limit. A block map iterating the extension along the ordinals was built
here once, for a bridge target later corrected to an index-free form; it was
retired with that correction, and the extension family is what remains.
<!--zh-->
两塔之间的桥跑在序数上，其端点在给定索引之上一个 `ω` 后继块处读初步函数塔。本章交付这个延拓：运算 `+ω`、双向的成员读法、底与每个有限迭代落于其内的事实、序数性，以及端点所花费的那条律：序数的延拓是极限。沿序数迭代延拓的块映射曾在此建成一次，服务于后来被修正为免索引形式的桥目标；它随该修正退役，留下的就是延拓族。
<!--/-->

```agda
{-# OPTIONS --cubical --safe --guardedness #-}

open import Base.Prelude
open import Base.Truth
open import Base.Classical using ( LEM )

module L.Rud.OrdBlocks {ℓ : Level} (lem : LEM (ℓ-suc ℓ)) where

open import FOL.ZFStructure using ( module hPropStructure )
open import V.Hierarchy {ℓ} using ( 𝒮ᵥ; extensionalV; ∈-irrefl )
open import V.Model {ℓ} using ( ∈sucV-elim; ∈sucV-inl; self∈sucV )
open import L.Constructible {ℓ} using ( IsOrd )
open import L.Ordinal {ℓ} using ( suc-ord; setUnion-ord )
open import L.Rud.OrdArith {ℓ} lem using ( isLimit; isSucc )

import Cubical.Data.Empty as Empty
import Cubical.HITs.PropositionalTruncation as PT
open PT using ( ∣_∣₁; ∥_∥₁; squash₁ )
open import Cubical.Functions.Logic using ( ⇔toPath; ∃[]-syntax )
open import Cubical.HITs.CumulativeHierarchy.Base using ( sett )
open import Cubical.HITs.CumulativeHierarchy.Properties using ( _∈ₛ_; ∈∈ₛ )
open import Cubical.HITs.CumulativeHierarchy.Constructions
  using ( ∅; ∅-empty; ⋃_; union-ax; module InfinitySet )
open InfinitySet using ( sucV )

open TruthAlgebra (hPropAlgebra (ℓ-suc ℓ))
open hPropStructure 𝒮ᵥ
```

<!--en-->
## Inclusion
<!--zh-->
## 包含
<!--/-->

<!--en-->
Inclusion is written pointwise, and mutual inclusion is equality by the
hierarchy's extensionality, exactly as in the tower chapter; this is the only
equality engine the case equations use.
<!--zh-->
包含逐点写出，互相包含按层级的外延性即相等，与塔章完全一致；这是分情形方程唯一用到的相等引擎。
<!--/-->

```agda
_⊆_ : S → S → Type (ℓ-suc ℓ)
u ⊆ v = (x : S) → ⟨ x ∈ˢ u ⟩ → ⟨ x ∈ˢ v ⟩

ext-⊆ : {u v : S} → u ⊆ v → v ⊆ u → u ≡ v
ext-⊆ {u} {v} sub sup = extensionalV (λ x → ⇔toPath (sub x) (sup x))
```

<!--en-->
## The ω-extension
<!--zh-->
## ω 延拓
<!--/-->

<!--en-->
The block added at a successor is `u` plus `ω` further successors: the union of
the finitely iterated successors of `u`, indexed by the naturals. This is the
formulation the laws spend least on: the level `u` itself and every finite
iterate sit in `+ω u` by one membership step, ordinality comes from the
ordinal chapter's union closure in one line, and the successor-absorption law
below reads off the same family. The two membership directions are named
first, since every later argument reaches for one of them.
<!--zh-->
后继处所加的块是 `u` 再添 `ω` 个后继：以自然数为索引、对 `u` 有限迭代后继所得之并。这是诸律花费最少的表述：`u` 自身与每个有限迭代落在 `+ω u` 里只花一步隶属，序数性由序数章的并闭包一行到手，下方的后继吸收律也读同一个族。两条隶属方向先具名，因为此后每个论证都要取其中之一。
<!--/-->

```agda
sucIter : ℕ → S → S
sucIter zero u = u
sucIter (suc n) u = sucV (sucIter n u)

+ω : S → S
+ω u = ⋃ (sett (Lift {ℓ-zero} {ℓ} ℕ) (λ m → sucIter (suc (lower m)) u))

+ω-in : (u x : S) → (n : ℕ) → ⟨ x ∈ˢ sucIter (suc n) u ⟩ → ⟨ x ∈ˢ +ω u ⟩
+ω-in u x n x∈ = ∈∈ₛ {a = x} {b = +ω u} .snd
  (union-ax (sett (Lift {ℓ-zero} {ℓ} ℕ) F) x .snd
    ∣ sucIter (suc n) u , (memb , x∈ₛ) ∣₁)
  where
  F : Lift {ℓ-zero} {ℓ} ℕ → S
  F m = sucIter (suc (lower m)) u
  memb : ⟨ sucIter (suc n) u ∈ₛ sett (Lift {ℓ-zero} {ℓ} ℕ) F ⟩
  memb = ∈∈ₛ {a = sucIter (suc n) u} {b = sett (Lift {ℓ-zero} {ℓ} ℕ) F} .fst
    ∣ lift n , refl ∣₁
  x∈ₛ : ⟨ x ∈ₛ sucIter (suc n) u ⟩
  x∈ₛ = ∈∈ₛ {a = x} {b = sucIter (suc n) u} .fst x∈

+ω-out : (u x : S) → ⟨ x ∈ˢ +ω u ⟩
        → ∥ Σ[ n ∈ ℕ ] ⟨ x ∈ˢ sucIter (suc n) u ⟩ ∥₁
+ω-out u x x∈ = PT.rec squash₁ uStep
  (union-ax (sett (Lift {ℓ-zero} {ℓ} ℕ) F) x .fst
    (∈∈ₛ {a = x} {b = +ω u} .fst x∈))
  where
  F : Lift {ℓ-zero} {ℓ} ℕ → S
  F m = sucIter (suc (lower m)) u
  uStep : Σ[ v ∈ S ] (⟨ v ∈ₛ sett (Lift {ℓ-zero} {ℓ} ℕ) F ⟩ × ⟨ x ∈ₛ v ⟩)
        → ∥ Σ[ n ∈ ℕ ] ⟨ x ∈ˢ sucIter (suc n) u ⟩ ∥₁
  uStep (v , v∈ₛsett , x∈ₛv) = PT.rec squash₁ atFib
    (∈∈ₛ {a = v} {b = sett (Lift {ℓ-zero} {ℓ} ℕ) F} .snd v∈ₛsett)
    where
    atFib : Σ[ m ∈ Lift {ℓ-zero} {ℓ} ℕ ] (F m ≡ v)
          → ∥ Σ[ n ∈ ℕ ] ⟨ x ∈ˢ sucIter (suc n) u ⟩ ∥₁
    atFib (m , Fm≡v) =
      ∣ lower m , subst (λ w → ⟨ x ∈ˢ w ⟩) (sym Fm≡v)
          (∈∈ₛ {a = x} {b = v} .snd x∈ₛv) ∣₁

+ω-mem : (u : S) → ⟨ u ∈ˢ +ω u ⟩
+ω-mem u = +ω-in u u 0 (self∈sucV u)

+ω-sup : (u : S) → u ⊆ +ω u
+ω-sup u x x∈u = +ω-in u x 0 (∈sucV-inl x∈u)

+ω-iter : (n : ℕ) → (u : S) → ⟨ sucIter n u ∈ˢ +ω u ⟩
+ω-iter n u = +ω-in u (sucIter n u) n (self∈sucV (sucIter n u))
```

<!--en-->
Ordinality of the extension is the ordinal chapter's union closure applied to
the family of iterated successors; each iterate is an ordinal by one step of
the successor-ordinal lemma. This is the fact the bridge's limit certificates
will lean on.
<!--zh-->
延拓的序数性是序数章并闭包施于迭代后继之族的结果；每个迭代由后继序数引理一步成为序数。这是桥的极限证书将要倚靠的事实。
<!--/-->

```agda
sucIter-ord : {u : S} → (n : ℕ) → IsOrd u → IsOrd (sucIter n u)
sucIter-ord zero ou = ou
sucIter-ord (suc n) ou = suc-ord (sucIter-ord n ou)

+ω-ord : (u : S) → IsOrd u → IsOrd (+ω u)
+ω-ord u ou = setUnion-ord (Lift {ℓ-zero} {ℓ} ℕ) (λ m → sucIter (suc (lower m)) u)
  (λ m → sucIter-ord (suc (lower m)) ou)
```

<!--en-->
The extension of an ordinal is a limit: it is an ordinal, it holds its own
base, and it is not a successor, since a successor inside the extension would
force its predecessor into some finite iterate and close a self-membership
through transitivity. The successor-inclusion lemma carries the descent.
<!--zh-->
序数的延拓是极限：它是序数、含自己的底，且不是后继，因为延拓内的后继会把其前驱逼入某个有限迭代，再经传递性闭成自属。后继包含引理承载这段下行。
<!--/-->

```agda
suc-⊆ : {A x : S} → IsOrd A → ⟨ x ∈ˢ A ⟩ → sucV x ⊆ A
suc-⊆ {A} {x} ordA x∈A z z∈sucx = ∈sucV-elim (snd (z ∈ˢ A)) z∈sucx
  (λ z∈x → ordA .fst {x = x} {y = z} z∈x x∈A)
  (λ z≡x → subst (λ w → ⟨ w ∈ˢ A ⟩) (sym z≡x) x∈A)

+ω-limit : (u : S) → IsOrd u → ⟨ isLimit (+ω u) ⟩
+ω-limit u ou = ( +ω-ord u ou
                , nz
                , ns )
  where
  nz : (+ω u ≡ ∅) → Empty.⊥
  nz e = ∅-empty u (∈∈ₛ {a = u} {b = ∅} .fst (subst (λ w → ⟨ u ∈ˢ w ⟩) e (+ω-mem u)))
  ns : ⟨ isSucc (+ω u) ⟩ → Empty.⊥
  ns (γ , ordγ , sucγ≡) = PT.rec Empty.isProp⊥ uStep (+ω-out u γ γ∈)
    where
    γ∈ : ⟨ γ ∈ˢ +ω u ⟩
    γ∈ = subst (λ w → ⟨ γ ∈ˢ w ⟩) sucγ≡ (self∈sucV γ)
    uStep : Σ[ n ∈ ℕ ] ⟨ γ ∈ˢ sucIter (suc n) u ⟩ → Empty.⊥
    uStep (n , γ∈sucn) = Empty.rec* {A = Empty.⊥}
      (∈sucV-elim {P = Empty.⊥* {ℓ-suc ℓ}} (Empty.isProp⊥* {ℓ-suc ℓ})
        γ∈sucn (λ γ∈n → lift (in1 γ∈n)) (λ γ≡n → lift (in2 γ≡n)))
      where
      t∈sucγ : ⟨ sucIter (suc n) u ∈ˢ sucV γ ⟩
      t∈sucγ = subst (λ w → ⟨ sucIter (suc n) u ∈ˢ w ⟩) (sym sucγ≡) (+ω-iter (suc n) u)
      in2 : γ ≡ sucIter n u → Empty.⊥
      in2 γ≡n = ∈-irrefl (sucV γ) t∈sucγ'
        where
        t∈sucγ' : ⟨ sucV γ ∈ˢ sucV γ ⟩
        t∈sucγ' = subst (λ w → ⟨ w ∈ˢ sucV γ ⟩) (sym (cong sucV γ≡n)) t∈sucγ
      in1 : ⟨ γ ∈ˢ sucIter n u ⟩ → Empty.⊥
      in1 γ∈n = Empty.rec* {A = Empty.⊥}
        (∈sucV-elim {P = Empty.⊥* {ℓ-suc ℓ}} (Empty.isProp⊥* {ℓ-suc ℓ}) t∈sucγ
          (λ t∈γ → lift (∈-irrefl (sucIter n u)
            (sucIter-ord n ou .fst {x = γ} {y = sucIter n u}
              (ordγ .fst {x = sucIter (suc n) u} {y = sucIter n u}
                (self∈sucV (sucIter n u)) t∈γ) γ∈n)))
          (λ t≡γ → lift (∈-irrefl (sucIter n u)
            (sucIter-ord n ou .fst {x = γ} {y = sucIter n u}
              (subst (λ w → ⟨ sucIter n u ∈ˢ w ⟩) t≡γ (self∈sucV (sucIter n u))) γ∈n))))
```
