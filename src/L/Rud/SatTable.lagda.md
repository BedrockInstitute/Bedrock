# The definable power as the image of a table

<!--en-->
The bridge's last hypothesis is one set: the totality of the definable subsets
of a constructible stage, asked to be a member of a rud level. This chapter
says what shape that set has, closes the shape into a theorem, and reports
exactly which object is still missing and why the object the previous two
chapters built is not it.

The shape is the classical one. A coded satisfaction relation over a carrier is
a set of pairs, a code with a member the coded formula selects; slicing it at
one code returns that formula's definable set, and collecting the slices over
the whole code set returns the definable power. Both operations are in the rud
basis, the slice as the tenth and the collection as the eighth, so a level that
holds the relation and the code set holds the definable power outright, with no
offset at all. That is the first half of this chapter, and it is proved at an
arbitrary code map so that no choice of coding is baked into it.

The second half is the index, and it is where the news is. The fragment the
Def-stage chapter left standing quantifies over **every** limit level above the
carrier, and the two-limit index the code set is delivered at is not available
at all of them: at a limit that is exactly one ω-block above the carrier's entry
stage there is no limit level below it holding the carrier, and by the code
set's own cofinality there is no member of that level holding all the codes
either. So the reduction runs the other way from the one the plan expected: the
whole fragment collapses to a **single** uniform ω-block statement, the base
case of which is already closed, and the coded table is a route to it only where
the block statement is not the content.
<!--zh-->
桥的最后一条假设是一个集合：可构造阶段的全体可定义子集，被要求成为某个初步函数层的成员。本章说清该集合是什么形状，把这个形状封成定理，并如实报告仍然缺失的是哪个对象，以及为什么前两章所造的那个对象不是它。

形状是经典的那个。载体之上的一条编码满足关系是一个对之集，即一条码配上该码所指公式选中的一个成员；在单条码处切片，取回那条公式的可定义集，而在整个码集上收拢诸切片，取回可定义幂。两个运算都在初步基底之内，切片是第十个、收拢是第八个，故持有该关系与该码集的层直接持有可定义幂，一点偏移也不用。这是本章的前一半，并且是在任意码映射上证出的，好让任何编码选择都不被烙进来。

后一半是索引，而新闻在这里。Def 阶段那一章留下的片段对载体之上的**每个**极限层量化，而码集所交付的那个双极限索引并非在每个极限层处都可用：在恰好高出载体进场阶段一个 ω 块的极限处，其下没有持有该载体的极限层，而按码集自身的共尾性，该层里也没有任何成员持有全部的码。故归约走的方向与计划所预期的相反：整个片段坍缩为**单独**一条一致的 ω 块陈述，其基本情形已经关闭，而编码表只在该块陈述不是内容之处才算通向它的一条路。
<!--/-->

```agda
{-# OPTIONS --cubical --safe --guardedness #-}

open import Base.Prelude
open import Base.Truth
open import Base.Classical using ( LEM )
open import Cubical.HITs.CumulativeHierarchy.Base using ( V )

module L.Rud.SatTable {ℓ : Level} (lem : LEM (ℓ-suc ℓ)) (A : V ℓ) where

open import FOL.ZFStructure using ( module hPropStructure )
open import FOL.Syntax using ( Formula )
open import V.Hierarchy {ℓ} using ( 𝒮ᵥ; extensionalV; ∈-irrefl )
open import V.Model {ℓ} using ( ∈sucV-elim )
open import L.Definability {ℓ} using ( module DefOf )
open import L.Constructible {ℓ} using ( IsOrd; Lset; 𝒟ₒ; 𝒟ₒ-intro; 𝒟ₒ-inv; isL )
open import L.Ordinal {ℓ} using ( numeral-ord; ω-ord; #∈ω )
open import L.Ordinal.Linear {ℓ} lem using ( ord-tri )
open import L.Rud.Images {ℓ} using ( F8; F8-spec; F10 )
open import L.Rud.Step {ℓ} lem A using
  ( f8; Fof-f8; Sset; Sset-trans; Sset-mem; Jset-rud )
open import L.Rud.OrdArith {ℓ} lem using
  ( isLimit; isLimit-ord; isLimit-not-zero; isLimit-not-succ; limit-mem-ord )
open import L.Rud.OrdBlocks {ℓ} lem using
  ( sucIter; sucIter-ord; +ω; +ω-ord; +ω-out )
open import L.Rud.CodeSet {ℓ} lem A using ( module Codes )
open import L.Rud.CodePred {ℓ} lem A using ( module At )
open import L.Rud.ClassJ {ℓ} lem A using ( isJ )
open import L.Rud.DefInJ {ℓ} lem A using
  ( DefFragment; Sstage; Lsuc≡Def; module Discharge )
open import L.Rud.BaseBlock {ℓ} lem A using ( baseDefPow )
open import L.Rud.Bridge {ℓ} lem A using ( module Reduce; ∅∈Lset )
open import L.Rud.StepInL {ℓ} lem A using ( stepSet∈L; values∈L )

open import Cubical.Functions.Logic using ( ⇔toPath )
open import Cubical.HITs.CumulativeHierarchy.Properties
  using ( ⟪_⟫; ⟪_⟫↪; ∈∈ₛ; ∈ₛ⟪_⟫↪_; ∈-asFiber )
open import Cubical.HITs.CumulativeHierarchy.Constructions
  using ( ∅; module InfinitySet )
import Cubical.Data.Empty as Empty
open import Cubical.Data.Sum using ( _⊎_; inl; inr )
import Cubical.HITs.PropositionalTruncation as PT
open PT using ( ∥_∥₁; ∣_∣₁ )

module IS = InfinitySet {ℓ}

open TruthAlgebra (hPropAlgebra (ℓ-suc ℓ))
open hPropStructure 𝒮ᵥ
```

<!--en-->
## The slice and the collection

The definable power is one collection of one relation's slices, and the whole
identity is stated at an abstract code map. A code map assigns a set to each
formula over the carrier; a set **covers** the map when it holds every code and
holds nothing else; and a relation **slices** to the map when its slice at a
formula's code is that formula's definable set. Under those two, the collection
of the relation's slices over the covering set is the definable power on the
nose.

Nothing about the coding is used, and that is deliberate: the identity is the
part of this chapter that survives a change of coding, and the index section
below is the part that does not.
<!--zh-->
## 切片与收拢

可定义幂就是某一条关系的诸切片的一次收拢，而整条恒等式是在抽象的码映射上陈述的。码映射把载体之上的每条公式指派到一个集合；一个集合**覆盖**该映射，当它持有每条码且不持有别的东西；而一条关系**切合**该映射，当它在某条公式之码处的切片就是该公式的可定义集。在这两条之下，该关系在覆盖集上诸切片的收拢，恰好就是可定义幂。

编码的任何细节都没有被用到，而这是有意为之：这条恒等式是本章中经得起编码更换的那一部分，而下面的索引一节则是经不起的那一部分。
<!--/-->

```agda
private
  ext-⊆ : {u v : S} → ((x : S) → ⟨ x ∈ˢ u ⟩ → ⟨ x ∈ˢ v ⟩)
        → ((x : S) → ⟨ x ∈ˢ v ⟩ → ⟨ x ∈ˢ u ⟩) → u ≡ v
  ext-⊆ sub sup = extensionalV (λ x → ⇔toPath (sub x) (sup x))

module Pow (C : S) where

  open DefOf C using ( defSet )

  Cod : Type (ℓ-suc ℓ)
  Cod = Formula ⟪ C ⟫ 1 → S

  Covers : S → Cod → Type (ℓ-suc ℓ)
  Covers K cod =
      ((φ : Formula ⟪ C ⟫ 1) → ⟨ cod φ ∈ˢ K ⟩)
    × ((c : S) → ⟨ c ∈ˢ K ⟩ → ∥ Σ[ φ ∈ Formula ⟪ C ⟫ 1 ] (cod φ ≡ c) ∥₁)

  Slices : S → Cod → Type (ℓ-suc ℓ)
  Slices R cod = (φ : Formula ⟪ C ⟫ 1) → F10 R (cod φ) ≡ defSet φ

  pow≡ : (K R : S) (cod : Cod) → Covers K cod → Slices R cod → F8 R K ≡ 𝒟ₒ C
  pow≡ K R cod (into , outof) sl = ext-⊆ sub sup
    where
    sub : (y : S) → ⟨ y ∈ˢ F8 R K ⟩ → ⟨ y ∈ˢ 𝒟ₒ C ⟩
    sub y h = PT.rec (snd (y ∈ˢ 𝒟ₒ C)) atIdx (subst ⟨_⟩ (F8-spec R K y) h)
      where
      atIdx : Σ[ m ∈ ⟪ K ⟫ ] (F10 R (⟪ K ⟫↪ m) ≡ y) → ⟨ y ∈ˢ 𝒟ₒ C ⟩
      atIdx (m , e) = PT.rec (snd (y ∈ˢ 𝒟ₒ C)) atFo
        (outof (⟪ K ⟫↪ m) (∈∈ₛ {a = ⟪ K ⟫↪ m} {b = K} .snd (∈ₛ⟪ K ⟫↪ m)))
        where
        atFo : Σ[ φ ∈ Formula ⟪ C ⟫ 1 ] (cod φ ≡ ⟪ K ⟫↪ m) → ⟨ y ∈ˢ 𝒟ₒ C ⟩
        atFo (φ , q) =
          𝒟ₒ-intro C y ∣ φ , (sym (sl φ) ∙ cong (F10 R) q ∙ e) ∣₁
    sup : (y : S) → ⟨ y ∈ˢ 𝒟ₒ C ⟩ → ⟨ y ∈ˢ F8 R K ⟩
    sup y h = PT.rec (snd (y ∈ˢ F8 R K)) atFo (𝒟ₒ-inv C y h)
      where
      atFo : Σ[ φ ∈ Formula ⟪ C ⟫ 1 ] (defSet φ ≡ y) → ⟨ y ∈ˢ F8 R K ⟩
      atFo (φ , q) = subst ⟨_⟩ (sym (F8-spec R K y)) ∣ fib .fst , path ∣₁
        where
        fib : Σ[ m ∈ ⟪ K ⟫ ] (⟪ K ⟫↪ m ≡ cod φ)
        fib = ∈-asFiber {a = cod φ} {b = K} (into φ)
        path : F10 R (⟪ K ⟫↪ (fib .fst)) ≡ y
        path = cong (F10 R) (fib .snd) ∙ sl φ ∙ q

  pow∈J : (γ : S) → ⟨ isLimit γ ⟩ → (K R : S) (cod : Cod)
        → Covers K cod → Slices R cod
        → ⟨ K ∈ˢ Sset γ ⟩ → ⟨ R ∈ˢ Sset γ ⟩ → ⟨ 𝒟ₒ C ∈ˢ Sset γ ⟩
  pow∈J γ limγ K R cod cov sl hK hR =
    subst (λ w → ⟨ w ∈ˢ Sset γ ⟩) (Fof-f8 R K ∙ pow≡ K R cod cov sl)
      (Jset-rud γ limγ f8 R K hR hK)
```

<!--en-->
At the delivered coding the covering half is free, since the code set's two
membership directions are exactly the two clauses, and the missing object is
named once: a **coded satisfaction relation**, a member of the level whose
slice at each code is that formula's definable set. This is the object the
coded-satisfaction table would produce, and it is the only object between the
code set and the definable power.
<!--zh-->
在已交付的编码处，覆盖那一半是免费的，因为码集的两个隶属方向恰是那两条子句，而缺失的对象一次点名：一条**编码满足关系**，它是该层的成员，且在每条码处的切片就是那条公式的可定义集。这正是编码满足表所要产出的对象，也是码集与可定义幂之间唯一的对象。
<!--/-->

```agda
module Coded (γ : S) (limγ : ⟨ isLimit γ ⟩) (C : S) where

  open Codes C using ( code; codeSet; codeSet-out; code∈codeSet )
  open Pow C using ( Cod; Covers; Slices; pow∈J )

  codeMap : Cod
  codeMap φ = code φ

  codeCovers : Covers (codeSet 1) codeMap
  codeCovers = code∈codeSet 1 , codeSet-out 1

  SatRelation : S → Type (ℓ-suc ℓ)
  SatRelation R = ⟨ R ∈ˢ Sset γ ⟩ × Slices R codeMap

  coded-pow : (R : S) → SatRelation R → ⟨ codeSet 1 ∈ˢ Sset γ ⟩
            → ⟨ 𝒟ₒ C ∈ˢ Sset γ ⟩
  coded-pow R (hR , sl) hK =
    pow∈J γ limγ (codeSet 1) R codeMap codeCovers sl hK hR
```

<!--en-->
The code set's own membership is delivered, and its index is the two-limit one:
the predicate is read in a limit level holding the carrier, and the set lands in
any limit above that. Plugging it in leaves the relation as the only hypothesis,
which is the statement of what the code chapters buy. The telescope of this
module is also the exact price of that purchase, and the next section is about
whether the fragment's consumer can pay it.
<!--zh-->
码集自身的隶属已经交付，其索引正是那个双极限的：谓词在持有载体的某个极限层中读出，而该集合落进其上任意一个极限。把它接进来，就只剩那条关系一条假设，这也就是编码诸章所买到的东西的陈述。本模块的望远镜同时也是那次购买的确切价钱，而下一节谈的是片段的消费方付不付得起。
<!--/-->

```agda
module TwoLimit (γ : S) (limγ : ⟨ isLimit γ ⟩)
                (δ : S) (limδ : ⟨ isLimit δ ⟩) (δ∈γ : ⟨ δ ∈ˢ γ ⟩)
                (C : S) (C∈δ : ⟨ C ∈ˢ Sset δ ⟩) where

  private
    module CP = At γ limγ δ limδ δ∈γ C C∈δ

  open Coded γ limγ C using ( SatRelation; coded-pow )

  codeSet∈J : ⟨ Codes.codeSet C 1 ∈ˢ Sset γ ⟩
  codeSet∈J = CP.codeSet∈J 1

  two-limit-pow : (R : S) → SatRelation R → ⟨ 𝒟ₒ C ∈ˢ Sset γ ⟩
  two-limit-pow R sr = coded-pow R sr codeSet∈J
```

<!--en-->
## Where a limit stands against the first one

Two facts about limits carry the whole index discussion. A limit is the first
one or lies above it, which is the trichotomy of the ordinals against `ω`
together with the reading of a member of `ω` as a numeral: a numeral is zero or
a successor, and a limit is neither. And every limit holds the empty set, which
is the first fact read once at `ω` and once above it. The second is what places
the relativization slot of the plain trunk.
<!--zh-->
## 一个极限相对于第一个极限站在哪里

关于极限的两条事实承载整场索引讨论。一个极限要么就是第一个，要么在它之上，这是诸序数对着 `ω` 的三歧，外加把 `ω` 的成员读作数码：数码要么是零、要么是后继，而极限两者都不是。以及每个极限都持有空集，这是把前一条事实在 `ω` 处读一次、在其上读一次。后者正是安放非相对化主干那个相对化槽之物。
<!--/-->

```agda
limit-ω-case : (γ : S) → ⟨ isLimit γ ⟩ → (γ ≡ IS.ω) ⊎ ⟨ IS.ω ∈ˢ γ ⟩
limit-ω-case γ limγ = pick (ord-tri IS.ω ω-ord γ (isLimit-ord γ limγ))
  where
  atK : (j : ℕ) → IS.# j ≡ γ → Empty.⊥
  atK zero    e = isLimit-not-zero γ limγ (sym e)
  atK (suc j) e = isLimit-not-succ γ limγ (IS.# j , (numeral-ord j , e))
  below : Σ[ k ∈ Lift ℕ ] (IS.# (lower k) ≡ γ) → Empty.⊥
  below (k , q) = atK (lower k) q
  pick : ⟨ IS.ω ∈ˢ γ ⟩ ⊎ ((IS.ω ≡ γ) ⊎ ⟨ γ ∈ˢ IS.ω ⟩)
       → (γ ≡ IS.ω) ⊎ ⟨ IS.ω ∈ˢ γ ⟩
  pick (inl h)         = inr h
  pick (inr (inl e))   = inl (sym e)
  pick (inr (inr h))   = Empty.rec (PT.rec Empty.isProp⊥ below h)

∅∈limit : (γ : S) → ⟨ isLimit γ ⟩ → ⟨ ∅ ∈ˢ γ ⟩
∅∈limit γ limγ = go (limit-ω-case γ limγ)
  where
  go : (γ ≡ IS.ω) ⊎ ⟨ IS.ω ∈ˢ γ ⟩ → ⟨ ∅ ∈ˢ γ ⟩
  go (inl e) = subst (λ w → ⟨ ∅ ∈ˢ w ⟩) (sym e) (#∈ω zero)
  go (inr h) = isLimit-ord γ limγ .fst {x = IS.ω} {y = ∅} (#∈ω zero) h
```

<!--en-->
## The fragment, split as the discharge wants it

The residue is stated once more, at the shape the Def-stage chapter's discharge
consumes, and it is stated as a **membership** rather than as a fragment: the
definable power of the stage is a member of the level. That form implies the
fragment outright, because the definable power is its own bounding fragment,
both inclusions being the identity. This is the base block's own witness shape,
now read at every limit.

The split is by the first limit. At `ω` the base block closes the case by
hereditary finiteness. Above it the residue stands, and it is named here with
the room condition it is entitled to: the level is a limit strictly above the
first one.
<!--zh-->
## 片段，按兑付所要的方式切分

存留再陈述一遍，取 Def 阶段那一章的兑付所消费的形状，而且陈述为一条**隶属**而非一个片段：该阶段的可定义幂是该层的成员。这个形式直接蕴涵那个片段，因为可定义幂就是它自己的定界片段，两条包含都是恒等。这正是基块自己的见证形状，如今在每个极限处读出。

切分依第一个极限而作。在 `ω` 处，基块以遗传有穷性关闭该情形。在其上，存留仍在，此处连同它有资格索取的余地条件一并具名：该层是严格高于第一个极限的极限。
<!--/-->

```agda
GeneralPow : Type (ℓ-suc ℓ)
GeneralPow = (ζ γ : S) → ⟨ isLimit γ ⟩ → ⟨ IS.ω ∈ˢ γ ⟩ → ⟨ ζ ∈ˢ γ ⟩
           → ⟨ Lset ζ ∈ˢ Sset γ ⟩ → ⟨ 𝒟ₒ (Lset ζ) ∈ˢ Sset γ ⟩

powFragment : (ζ γ : S) → ⟨ 𝒟ₒ (Lset ζ) ∈ˢ Sset γ ⟩
            → ∥ Σ[ F ∈ S ] ( ⟨ F ∈ˢ Sset γ ⟩
              × (((y : S) → ⟨ y ∈ˢ 𝒟ₒ (Lset ζ) ⟩ → ⟨ y ∈ˢ F ⟩)
              × ((y : S) → ⟨ y ∈ˢ F ⟩
                → ((w : S) → ⟨ w ∈ˢ y ⟩ → ⟨ w ∈ˢ Lset ζ ⟩)
                → ⟨ y ∈ˢ 𝒟ₒ (Lset ζ) ⟩))) ∥₁
powFragment ζ γ h = ∣ 𝒟ₒ (Lset ζ)
  , ( h , ( (λ y k → k) , (λ y k _ → k) ) ) ∣₁

defPow : GeneralPow → (ζ γ : S) → ⟨ isLimit γ ⟩ → ⟨ ζ ∈ˢ γ ⟩
       → ⟨ Lset ζ ∈ˢ Sset γ ⟩ → ⟨ 𝒟ₒ (Lset ζ) ∈ˢ Sset γ ⟩
defPow gp ζ γ limγ ζ∈γ L∈ = go (limit-ω-case γ limγ)
  where
  go : (γ ≡ IS.ω) ⊎ ⟨ IS.ω ∈ˢ γ ⟩ → ⟨ 𝒟ₒ (Lset ζ) ∈ˢ Sset γ ⟩
  go (inl e) = subst (λ w → ⟨ 𝒟ₒ (Lset ζ) ∈ˢ Sset w ⟩) (sym e)
    (baseDefPow ζ (subst (λ w → ⟨ ζ ∈ˢ w ⟩) e ζ∈γ)
                  (subst (λ w → ⟨ Lset ζ ∈ˢ Sset w ⟩) e L∈))
  go (inr ω∈γ) = gp ζ γ limγ ω∈γ ζ∈γ L∈

fragment : GeneralPow → DefFragment
fragment gp ζ γ limγ ζ∈γ L∈ = powFragment ζ γ (defPow gp ζ γ limγ ζ∈γ L∈)

pow-from-fragment : DefFragment → GeneralPow
pow-from-fragment fr ζ γ limγ ω∈γ ζ∈γ L∈ =
  subst (λ w → ⟨ w ∈ˢ Sset γ ⟩) (Lsuc≡Def ζ)
    (Discharge.defStage∈J fr ζ γ limγ ζ∈γ L∈)
```

<!--en-->
The two travel together, so nothing is weakened by trading one for the other:
the fragment yields the membership through the discharge and the successor
collapse, and the membership yields the fragment as its own bound. Recording
the equivalence is what keeps the reduction honest, since a residue that is
merely implied by the target would be a restatement dressed as progress.
<!--zh-->
二者同行，故以其一换其二并未削弱任何东西：片段经兑付与后继坍缩给出隶属，而隶属以自身为界给出片段。把这条等价记下来，正是使归约保持诚实之事，因为只被目标蕴涵的存留，不过是伪装成进展的重述。
<!--/-->

<!--en-->
## The residue is one ω-block, not a family over the limits

The residue as just stated still quantifies over the levels, and it does not
have to. A stage the level holds as a member enters at some index strictly
below, and the ω-extension of that index is a limit that is at most the level
itself. So a **uniform** statement, the definable power of a stage is a member
of the ω-block above the stage's entry index, gives the residue at every limit
at once: below the level the extension is reached by monotonicity, and at the
level it is the level.

Two facts make the comparison. A limit cannot lie inside the ω-extension of one
of its own members, since a member of that extension is reached by finitely many
successors and the limit is neither the base nor a successor. And the extension
is an ordinal, so the trichotomy leaves only the two cases wanted.
<!--zh-->
## 存留是一个 ω 块，而不是遍及诸极限的一族

刚陈述的存留仍然对诸层量化，而它不必如此。层作为成员收下的阶段，在严格更低的某个索引处进场，而那个索引的 ω 延拓是一个至多等于该层自身的极限。故一条**一致的**陈述，即某阶段的可定义幂是该阶段进场索引之上那个 ω 块的成员，一次给出每个极限处的存留：在层之下由单调性到达该延拓，而在层处它就是该层。

两条事实作成这次比较。极限不可能落在它自己某个成员的 ω 延拓之内，因为该延拓的成员经有穷多次后继到达，而极限既非底、也非后继。而该延拓是序数，故三歧只剩下所要的两种情形。
<!--/-->

```agda
BlockPow : Type (ℓ-suc ℓ)
BlockPow = (ζ δ : S) → IsOrd δ → ⟨ Lset ζ ∈ˢ Sset δ ⟩
         → ⟨ 𝒟ₒ (Lset ζ) ∈ˢ Sset (+ω δ) ⟩

+ω-fits : (δ γ : S) → ⟨ isLimit γ ⟩ → IsOrd δ → ⟨ δ ∈ˢ γ ⟩
        → ⟨ +ω δ ∈ˢ γ ⟩ ⊎ (+ω δ ≡ γ)
+ω-fits δ γ limγ ordδ δ∈γ =
  pick (ord-tri (+ω δ) (+ω-ord δ ordδ) γ (isLimit-ord γ limγ))
  where
  Bot : Type (ℓ-suc ℓ)
  Bot = Empty.⊥* {ℓ-suc ℓ}
  atEq : (n : ℕ) → γ ≡ sucIter n δ → Bot
  atEq zero    e = Empty.rec (∈-irrefl δ (subst (λ w → ⟨ δ ∈ˢ w ⟩) e δ∈γ))
  atEq (suc n) e = Empty.rec (isLimit-not-succ γ limγ
    (sucIter n δ , (sucIter-ord n ordδ , sym e)))
  no : (n : ℕ) → ⟨ γ ∈ˢ sucIter n δ ⟩ → Bot
  no zero    h = Empty.rec
    (∈-irrefl γ (isLimit-ord γ limγ .fst {x = δ} {y = γ} h δ∈γ))
  no (suc n) h = ∈sucV-elim {A = sucIter n δ} {x = γ}
    (Empty.isProp⊥* {ℓ-suc ℓ}) h (no n) (atEq n)
  deep : Σ[ n ∈ ℕ ] ⟨ γ ∈ˢ sucIter (suc n) δ ⟩ → Bot
  deep (n , h) = no (suc n) h
  pick : ⟨ +ω δ ∈ˢ γ ⟩ ⊎ ((+ω δ ≡ γ) ⊎ ⟨ γ ∈ˢ +ω δ ⟩)
       → ⟨ +ω δ ∈ˢ γ ⟩ ⊎ (+ω δ ≡ γ)
  pick (inl h)       = inl h
  pick (inr (inl e)) = inr e
  pick (inr (inr h)) =
    Empty.rec* (PT.rec (Empty.isProp⊥* {ℓ-suc ℓ}) deep (+ω-out δ γ h))

block→general : BlockPow → GeneralPow
block→general bp ζ γ limγ ω∈γ ζ∈γ L∈ =
  PT.rec (snd (𝒟ₒ (Lset ζ) ∈ˢ Sset γ)) atStage (Sstage γ limγ (Lset ζ) L∈)
  where
  atStage : Σ[ δ ∈ S ] (⟨ δ ∈ˢ γ ⟩ × ⟨ Lset ζ ∈ˢ Sset δ ⟩)
          → ⟨ 𝒟ₒ (Lset ζ) ∈ˢ Sset γ ⟩
  atStage (δ , δ∈γ , L∈δ) = place
    (+ω-fits δ γ limγ (limit-mem-ord γ limγ δ δ∈γ) δ∈γ)
    where
    inBlock : ⟨ 𝒟ₒ (Lset ζ) ∈ˢ Sset (+ω δ) ⟩
    inBlock = bp ζ δ (limit-mem-ord γ limγ δ δ∈γ) L∈δ
    place : ⟨ +ω δ ∈ˢ γ ⟩ ⊎ (+ω δ ≡ γ) → ⟨ 𝒟ₒ (Lset ζ) ∈ˢ Sset γ ⟩
    place (inl h) = Sset-trans γ {x = Sset (+ω δ)} {y = 𝒟ₒ (Lset ζ)}
      inBlock (Sset-mem {α = γ} {β = +ω δ} h)
    place (inr e) = subst (λ w → ⟨ 𝒟ₒ (Lset ζ) ∈ˢ Sset w ⟩) e inBlock
```

<!--en-->
## The close-out

Everything the bridge's reduction wants is now one hypothesis away. The
discharge of the Def-stage chapter turns the fragment into the reduction's first
hypothesis; the other three are delivered, the two rud-step readings by the
step-in-L chapter and the relativization slot by the empty set at the plain
trunk. The reduction then delivers the direction that needs no identification,
`bridge-isJ→isL`{.Agda}, in the lines the bridge already wrote.

The module below is the close-out check as well as the export: it applies the
reduction to the four hypotheses in place, so the typechecker verifies that the
discharge lands at the exact telescope the bridge fixed, which is the check a
scratchpad probe would otherwise perform.
<!--zh-->
## 收尾

桥的归约所要的一切，如今只差一条假设。Def 阶段那一章的兑付把片段变成归约的第一条假设；另外三条都已交付，两条初步函数单步读法由 step-in-L 那一章给出，相对化槽则在非相对化主干处由空集给出。归约随即产出两塔的认同，而类的等价由桥已经写好的三行随之而来。

下面这个模块既是收尾检查、也是导出：它就地把归约施于那四条假设，故类型检查器核实了兑付恰好落在桥所固定的那条望远镜上，而这正是草稿探针本会做的那次检查。
<!--/-->

```agda
slot-empty : A ≡ ∅ → (γ : S) → ⟨ isLimit γ ⟩ → ⟨ A ∈ˢ Lset γ ⟩
slot-empty e γ limγ = subst (λ w → ⟨ w ∈ˢ Lset γ ⟩) (sym e)
  (∅∈Lset γ limγ (∅∈limit γ limγ))

module Landing (gp : GeneralPow)
               (slot∈L : (γ : S) → ⟨ isLimit γ ⟩ → ⟨ A ∈ˢ Lset γ ⟩) where

  open Discharge (fragment gp) using ( defStage∈J )

  module R = Reduce defStage∈J stepSet∈L values∈L slot∈L

  bridge-isJ→isL : (x : S) → ⟨ isJ x ⟩ → ⟨ isL x ⟩
  bridge-isJ→isL = R.bridge-isJ→isL
```

<!--en-->
## Recap

The definable power of a carrier is the eighth basis operation applied to a
coded satisfaction relation and a set covering the codes (`pow≡`{.Agda}), so a
limit level holding both holds the definable power with no offset
(`pow∈J`{.Agda}); at the delivered coding the covering half is the code set's own
two membership directions, and the one missing object is the relation
(`SatRelation`{.Agda}, `coded-pow`{.Agda}), which the code chapters' own index
supplies only two limits up (`TwoLimit`{.Agda}).

The definable power is its own bounding fragment (`powFragment`{.Agda}), so the
Def-stage chapter's residue is the membership statement rather than a fragment,
and the two are interchangeable (`fragment`{.Agda},
`pow-from-fragment`{.Agda}). Split at the first limit, the base case is the base
block's (`defPow`{.Agda}), and what remains is `GeneralPow`{.Agda}: the definable
power of a stage is a member of every limit level above the first one that holds
the stage. That in turn follows from one uniform ω-block statement
(`BlockPow`{.Agda}, `block→general`{.Agda}), which quantifies over no level at
all. Given either, the bridge's reduction runs at its exact telescope and
delivers its unconditional direction (`Landing`{.Agda}).
<!--zh-->
## 小结

载体的可定义幂是第八个基底运算施于一条编码满足关系与一个覆盖诸码的集合之值 (`pow≡`{.Agda})，故同时持有二者的极限层不带任何偏移地持有可定义幂 (`pow∈J`{.Agda})；在已交付的编码处，覆盖那一半就是码集自己的两个隶属方向，而唯一缺失的对象是那条关系 (`SatRelation`{.Agda}、`coded-pow`{.Agda})，而编码诸章自身的索引只在高出两个极限之处供给它 (`TwoLimit`{.Agda})。

可定义幂就是它自己的定界片段 (`powFragment`{.Agda})，故 Def 阶段那一章的存留是那条隶属陈述、而非一个片段，且二者可以互换 (`fragment`{.Agda}、`pow-from-fragment`{.Agda})。按第一个极限切分，基本情形归基块所有 (`defPow`{.Agda})，余下的是 `GeneralPow`{.Agda}：某阶段的可定义幂，是持有该阶段、且高于第一个极限的每个极限层的成员。它又由单独一条一致的 ω 块陈述推出 (`BlockPow`{.Agda}、`block→general`{.Agda})，而后者完全不对层量化。有了其中任一条，桥的归约便在它那条确切的望远镜上跑起来，交付它那个无条件的方向 (`Landing`{.Agda})。
<!--/-->
