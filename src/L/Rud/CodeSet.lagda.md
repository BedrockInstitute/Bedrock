# The codes over a carrier, as one set

<!--en-->
The satisfaction engine answers one formula at a time, and the fragment the
bridge is waiting for asks for the totality. Between the two stands an object
the rud route has never built: the codes of the formulas over a carrier,
gathered into a single set. This chapter builds that set, says exactly which
sets belong to it, and settles where it stands with respect to the tower.

The coding itself is already delivered and is not touched: a formula's code is
a tagged Kuratowski pair, the tag a numeral and the payload the codes of the
parts, with constants coding themselves. What is new here is the family. The
codes of the formulas over a carrier form a small family indexed by the
**external** syntax, so the set is a `sett`{.Agda} over that index type, and its
membership is read at the small index in both directions. Collecting a union and
extracting fibers from it is the one construction this chapter refuses.

Where the set stands is two questions, not one, and they have different answers.
Every code is a member of any limit level that holds the carrier: one Kuratowski
pair is one application of the pairing operation, so an induction over the
formula walks each code into the level through the closure. The **set** is
another matter. A level is transitive, so if the code set were a member at some
stage, every code would have entered by that stage; but a code's pair depth
grows with the formula, one arm per layer, and the depths are unbounded. The
codes are therefore cofinal below any stage that could hold them, and no finite
offset above the carrier holds the family. That is not a gap in the proof, it is
a fact about the target, and the chapter records it where it is discovered.

What remains true, and is stated here with its discharge, is that membership
would follow from one thing only: a formula of the object language whose
definable set is the code set. The engine turns such a formula into the arms by
itself. So the chapter closes with the reduction rather than with the theorem,
and names what a later chapter has to build.
<!--zh-->
满足集引擎一次只答一条公式，而桥所等待的那个片段索取的是全体。二者之间立着一个初步函数路线从未造过的对象：某载体之上诸公式的码，收拢成单一集合。本章造出该集合，说清哪些集合属于它，并厘定它相对于塔的位置。

编码本身早已交付，此处不动它：公式的码是一个带标签的 Kuratowski 对，标签是数码，载荷是各部分的码，而常量编码自身。此处新增的是那个族。载体之上诸公式的码构成一个以**外部**语法为索引的小族，故该集合是那个索引类型上的 `sett`{.Agda}，其隶属在小索引处双向读出。收拢一个并、再从中抽取纤维，正是本章拒绝的那种构造。

该集合站在哪里，是两个问题而非一个，且答案不同。每个码都是任何持有该载体的极限层的成员：一个 Kuratowski 对就是配对运算的一次施用，故沿公式的一次归纳把每个码经闭包走进该层。但那个**集合**是另一回事。层是传递的，故若码集在某阶段处是成员，则每个码都已在该阶段之前进场；然而码的对深度随公式增长，每层一臂，而诸深度无界。于是诸码在任何足以持有它们的阶段之下共尾，载体之上没有任何有限偏移持有这个族。这不是证明里的缺口，而是关于目标本身的事实，本章在发现之处把它记下。

仍然为真、并在此连同其兑付一并陈述的是：隶属性只依赖一件事，即对象语言里的一条公式，其可定义集恰是该码集。引擎会自行把这样一条公式转成诸臂。故本章以归约而非以定理收尾，并点名后续某章必须造出的东西。
<!--/-->

```agda
{-# OPTIONS --cubical --safe --guardedness #-}

open import Base.Prelude
open import Base.Truth
open import Base.Classical using ( LEM )
open import Cubical.HITs.CumulativeHierarchy.Base using ( V; sett )

module L.Rud.CodeSet {ℓ : Level} (lem : LEM (ℓ-suc ℓ)) (A : V ℓ) where

open import FOL.ZFStructure using ( module hPropStructure )
open import FOL.Syntax
  using ( Term; con; var; Formula
        ; _∈̇_; _≐_; _∧̇_; _∨̇_; _⇒̇_; ¬̇_; ⊤̇; ⊥̇; ∃̇_; ∀̇_; ∀̇∈; ∃̇∈ )
open import FOL.Manipulation.Relabelling using ( mapTm; mapFo )
open import V.Hierarchy {ℓ} using ( 𝒮ᵥ; extensionalV )
open import V.Coding {ℓ} using ( pr; module VCode )
open import L.Definability {ℓ} using ( module DefOf )
open import L.Rud.Ops {ℓ} using ( F1-spec )
open import L.Rud.Step {ℓ} lem A
  using ( f0; f1; f5; f9; Fof; Fof-f0; Fof-f1; Fof-f5; Fof-f9; singl≡pair
        ; Sset; Sset-trans; Sset-mem; Jset-rud )
open import L.Rud.OrdArith {ℓ} lem using ( isLimit )
open import L.Rud.SatSets {ℓ} lem A using ( module Sat )

open import Cubical.Data.FinData using ( toℕ )
open import Cubical.Data.Sigma using ( Σ≡Prop )
open import Cubical.Functions.Logic using ( ⇔toPath )
open import Cubical.HITs.CumulativeHierarchy.Properties
  using ( ⟪_⟫; ⟪_⟫↪; ∈∈ₛ; ∈ₛ⟪_⟫↪_ )
open import Cubical.HITs.CumulativeHierarchy.Constructions
  using ( ∅; ∅-empty; ⁅_,_⁆; ⁅_⁆s; ⋃_; module InfinitySet )
open InfinitySet using ( sucV; #_ )
import Cubical.Data.Empty as Empty
import Cubical.HITs.PropositionalTruncation as PT
open PT using ( ∥_∥₁; ∣_∣₁; squash₁ )

open TruthAlgebra (hPropAlgebra (ℓ-suc ℓ))
open hPropStructure 𝒮ᵥ
```

<!--en-->
## The codes over a carrier
<!--zh-->
## 载体之上的诸码
<!--/-->

<!--en-->
The carrier is a set, and its alphabet is the type of its own members. A formula
over that alphabet becomes a formula over the hierarchy by naming each member,
and the delivered coding then applies. Nothing here is new mathematics: the two
definitions are a relabelling followed by the code function.

The class the two directions below are about is written once, at each arity and
across all of them. Which of the two a consumer wants is decided by what it does
with the codes: the definable powerset indexes by one arity, and a recursion
over subcodes needs every arity, since a quantifier's subformula lives one arity
up.
<!--zh-->
载体是一个集合，其字母表就是它自身诸成员的类型。该字母表之上的一条公式，经把每个成员点名而成为层级之上的一条公式，交付好的编码随即适用。此处没有新数学：两条定义就是一次重贴标签，再接上码函数。

下面两个方向所谈的那一类只写一次，一次落在每个元数上，一次跨越全部元数。消费方要哪一个，由它拿这些码去做什么决定：可定义幂集以单一元数为索引，而对诸子码的递归需要每个元数，因为量词的子公式住在高一级的元数上。
<!--/-->

```agda
module Codes (C : S) where

  ι : ⟪ C ⟫ → S
  ι = ⟪ C ⟫↪

  codeTm : ∀ {n} → Term ⟪ C ⟫ n → S
  codeTm t = VCode.⌜ mapTm ι t ⌝ᵗ

  code : ∀ {n} → Formula ⟪ C ⟫ n → S
  code φ = VCode.⌜ mapFo ι φ ⌝

  IsCodeAt : ℕ → S → Ω
  IsCodeAt k x = ∥ Σ[ φ ∈ Formula ⟪ C ⟫ k ] (code φ ≡ x) ∥₁ , squash₁

  IsCodeAny : S → Ω
  IsCodeAny x =
    ∥ Σ[ k ∈ ℕ ] Σ[ φ ∈ Formula ⟪ C ⟫ k ] (code φ ≡ x) ∥₁ , squash₁
```

<!--en-->
## The family as one set
<!--zh-->
## 作为一个集合的族
<!--/-->

<!--en-->
Both sets are the same construction at two index types, and both are sealed
where they are built. The seal is not caution about size: it is the standing
rule that a heavy set is opaque at its birth site, so that no later type
mentioning one drags the presentation machinery into conversion. The two
directions of membership are proved inside the seal, and they are all the
surface a consumer gets.

Neither direction has any content, and that is the point of building the set
this way. Membership in a `sett`{.Agda} **is** being merely hit by the indexing
family, so introduction is the index itself and elimination is the identity. Cut
the same class out of a superset instead, and both directions become separation
lemmas over a union, which is the shape that has to be avoided.
<!--zh-->
两个集合是同一套构造落在两个索引类型上，且都在被造出之处封印。封印不是对尺寸的谨慎：它是那条常设规矩，重集合在其诞生处封为不透明，使此后任何提到它的类型都不把呈现机器拖进转换检查。隶属的两个方向在封印之内证出，而它们就是消费方所得的全部表面。

两个方向都没有内容，而这正是这样造这个集合的用意。属于一个 `sett`{.Agda} **就是**仅仅被索引族命中，故引入就是索引本身，消去就是恒等。若改从某个超集中把同一类切出来，两个方向就都成了跨越一个并的分离引理，而那正是必须避开的形状。
<!--/-->

```agda
  opaque
    codeSet : ℕ → S
    codeSet k = sett (Formula ⟪ C ⟫ k) code

    allCodes : S
    allCodes = sett (Σ[ k ∈ ℕ ] Formula ⟪ C ⟫ k) (λ p → code (p .snd))

    code∈codeSet : (k : ℕ) (φ : Formula ⟪ C ⟫ k) → ⟨ code φ ∈ˢ codeSet k ⟩
    code∈codeSet k φ = ∣ φ , refl ∣₁

    codeSet-out : (k : ℕ) (x : S) → ⟨ x ∈ˢ codeSet k ⟩ → ⟨ IsCodeAt k x ⟩
    codeSet-out k x h = h

    code∈allCodes : (k : ℕ) (φ : Formula ⟪ C ⟫ k) → ⟨ code φ ∈ˢ allCodes ⟩
    code∈allCodes k φ = ∣ (k , φ) , refl ∣₁

    allCodes-out : (x : S) → ⟨ x ∈ˢ allCodes ⟩ → ⟨ IsCodeAny x ⟩
    allCodes-out x = PT.map (λ { ((k , φ) , q) → k , φ , q })

  codeSet-in : (k : ℕ) (x : S) → ⟨ IsCodeAt k x ⟩ → ⟨ x ∈ˢ codeSet k ⟩
  codeSet-in k x = PT.rec (snd (x ∈ˢ codeSet k))
    (λ { (φ , q) →
      subst (λ w → ⟨ w ∈ˢ codeSet k ⟩) q (code∈codeSet k φ) })

  codeSet-spec : (k : ℕ) (x : S) → (x ∈ˢ codeSet k) ≡ IsCodeAt k x
  codeSet-spec k x = ⇔toPath (codeSet-out k x) (codeSet-in k x)

  allCodes-in : (x : S) → ⟨ IsCodeAny x ⟩ → ⟨ x ∈ˢ allCodes ⟩
  allCodes-in x = PT.rec (snd (x ∈ˢ allCodes))
    (λ { (k , φ , q) →
      subst (λ w → ⟨ w ∈ˢ allCodes ⟩) q (code∈allCodes k φ) })

  allCodes-spec : (x : S) → (x ∈ˢ allCodes) ≡ IsCodeAny x
  allCodes-spec x = ⇔toPath (allCodes-out x) (allCodes-in x)
```

<!--en-->
## The code determines the formula
<!--zh-->
## 码决定公式
<!--/-->

<!--en-->
Elimination as stated is truncated, because it must be: the alphabet is a
presentation of the carrier by its members, and two indices may name the same
set, so a member of the code set does not determine a formula over the alphabet.
Over the hierarchy itself it does, and that is the sharper reading the coding
chapter's injectivity was proved for. At a **fixed** arity the pair of a formula
and a proof that it codes the given set is a proposition, so the truncation may
be removed and the decode returns the formula outright.

The arity has to be fixed for this, and the all-arity set is left truncated on
purpose. A code carries its constructor in its tag and its parts in its payload;
it does not carry the arity, and a formula with no free variables has the same
code at every arity. So over `allCodes`{.Agda} the pair is genuinely not a
proposition, and no injectivity argument can make it one.
<!--zh-->
消去如上所陈是被截断的，而它必须如此：字母表是载体由其诸成员给出的一个呈现，两个索引可以点名同一个集合，故码集的一个成员并不决定字母表之上的一条公式。在层级自身之上它确实决定，而这正是编码那一章的单射性所为之而证的那种更锐的读法。在**固定的**元数上，「一条公式连同它编码给定集合的证明」这一对是一个命题，故截断可以去掉，解码直接把公式交出来。

为此元数必须固定，而全元数那个集合被有意留作截断。码在标签里携带构造子、在载荷里携带各部分；它不携带元数，而没有自由变元的公式在每个元数上有相同的码。故在 `allCodes`{.Agda} 之上那一对确实不是命题，任何单射性论证都无法使它成为命题。
<!--/-->

```agda
  private
    isPropCoded : (k : ℕ) (x : S)
                → isProp (Σ[ χ ∈ Formula S k ] (VCode.⌜ χ ⌝ ≡ x))
    isPropCoded k x (χ , p) (ψ , q) =
      Σ≡Prop (λ ξ → isSetS VCode.⌜ ξ ⌝ x) (VCode.⌜⌝-inj χ ψ (p ∙ sym q))

  codeSet-decode : (k : ℕ) (x : S) → ⟨ x ∈ˢ codeSet k ⟩
                 → Σ[ χ ∈ Formula S k ] (VCode.⌜ χ ⌝ ≡ x)
  codeSet-decode k x h = PT.rec (isPropCoded k x)
    (λ { (φ , q) → mapFo ι φ , q }) (codeSet-out k x h)
```

<!--en-->
## Numerals and pairs inside a level
<!--zh-->
## 层内的数码与对
<!--/-->

<!--en-->
A limit level is closed under the sixteen operations, and that is all the
arithmetic a code needs. The Kuratowski pair is the ninth operation outright.
The empty set is the difference of any member with itself. The successor is
three operations deep, the unordered pair of a set with its own singleton,
unioned; the singleton is the unordered pair of a set with itself, which is the
same equation the step's transitivity cases already use. Numerals follow by
induction, and the induction needs one member of the level to start the empty
set from.

The three equations are stated at a variable argument and proved once, so no
concrete level is ever handed to conversion. Each is read through the sealed
operation family, never through an operation's own body.
<!--zh-->
极限层对十六个运算封闭，而这就是一个码所需的全部算术。Kuratowski 对直接就是第九个运算。空集是任何成员与自身的差。后继深三层，即一个集合与它自己的单点集所成的无序对，再取并；而单点集是一个集合与自身的无序对，这与 step 的传递性诸情形已在用的是同一条等式。数码随之由归纳而来，而该归纳需要该层的一个成员，好据以起出空集。

三条等式在变元实参上陈述、一次证完，故任何具体的层都不会被交给转换检查。每一条都经封好的运算族读出，而不经某个运算自身的体。
<!--/-->

```agda
private
  ext-⊆ : {u v : S} → ((x : S) → ⟨ x ∈ˢ u ⟩ → ⟨ x ∈ˢ v ⟩)
        → ((x : S) → ⟨ x ∈ˢ v ⟩ → ⟨ x ∈ˢ u ⟩) → u ≡ v
  ext-⊆ sub sup = extensionalV (λ x → ⇔toPath (sub x) (sup x))

empty-rud : (a : S) → Fof f1 a a ≡ ∅
empty-rud a = ext-⊆ sub sup
  where
  sub : (x : S) → ⟨ x ∈ˢ Fof f1 a a ⟩ → ⟨ x ∈ˢ ∅ ⟩
  sub x h = Empty.rec (both .snd (both .fst))
    where
    both : ⟨ (x ∈ˢ a) ⊓ (¬ (x ∈ˢ a)) ⟩
    both = F1-spec a a x .fst
      (subst (λ w → ⟨ x ∈ˢ w ⟩) (Fof-f1 a a) h)
  sup : (x : S) → ⟨ x ∈ˢ ∅ ⟩ → ⟨ x ∈ˢ Fof f1 a a ⟩
  sup x h = Empty.rec (∅-empty x (∈∈ₛ {a = x} {b = ∅} .fst h))

singleton-rud : (x : S) → Fof f0 x x ≡ ⁅ x ⁆s
singleton-rud x = Fof-f0 x x ∙ sym (singl≡pair x)

sucV-rud : (x : S) → Fof f5 (Fof f0 x (Fof f0 x x)) x ≡ sucV x
sucV-rud x = Fof-f5 (Fof f0 x (Fof f0 x x)) x
  ∙ cong ⋃_ (Fof-f0 x (Fof f0 x x)
             ∙ cong (λ w → ⁅ x , w ⁆) (singleton-rud x))

module InLevel (γ : S) (limγ : ⟨ isLimit γ ⟩) where

  InJ : S → Type (ℓ-suc ℓ)
  InJ x = ⟨ x ∈ˢ Sset γ ⟩

  pr∈J : (a b : S) → InJ a → InJ b → InJ (pr a b)
  pr∈J a b ha hb = subst (λ w → ⟨ w ∈ˢ Sset γ ⟩) (Fof-f9 a b)
    (Jset-rud γ limγ f9 a b ha hb)

  ∅∈J : (a : S) → InJ a → InJ ∅
  ∅∈J a ha = subst (λ w → ⟨ w ∈ˢ Sset γ ⟩) (empty-rud a)
    (Jset-rud γ limγ f1 a a ha ha)

  sucV∈J : (x : S) → InJ x → InJ (sucV x)
  sucV∈J x hx = subst (λ w → ⟨ w ∈ˢ Sset γ ⟩) (sucV-rud x)
    (Jset-rud γ limγ f5 (Fof f0 x (Fof f0 x x)) x
      (Jset-rud γ limγ f0 x (Fof f0 x x) hx
        (Jset-rud γ limγ f0 x x hx hx))
      hx)

  numeral∈J : (a : S) → InJ a → (k : ℕ) → InJ (# k)
  numeral∈J a ha zero    = ∅∈J a ha
  numeral∈J a ha (suc k) = sucV∈J (# k) (numeral∈J a ha k)
```

<!--en-->
## Every code is a member
<!--zh-->
## 每个码都是成员
<!--/-->

<!--en-->
With the carrier a member of the level, its members are members too, since a
level is transitive, and that is the only thing the constants of a formula need.
A tag is a pair of a numeral with a payload, so one lemma covers all twelve
tags, and the induction over the formula is then twelve applications of it,
mirroring the code function's own clauses one for one.

The consequence is the containment half, stated for both sets: every member of
the code set is a member of the level. It holds at any limit level that holds
the carrier, with no condition on how much room lies above the carrier's own
stage, because the closure is applied inside the level and never climbs.
<!--zh-->
载体既是该层的成员，它的诸成员也就是成员，因为层是传递的，而这正是一条公式的诸常量所需的全部。标签是数码与载荷所成的对，故一条引理覆盖全部十二个标签，而沿公式的归纳随即是它的十二次施用，与码函数自己的诸子句一一对应。

推论是包含的那一半，对两个集合都陈述：码集的每个成员都是该层的成员。它在任何持有该载体的极限层处成立，对载体自身阶段之上还有多少余地不加任何条件，因为闭包是在层内施用的，从不上爬。
<!--/-->

```agda
module Carrier (γ : S) (limγ : ⟨ isLimit γ ⟩)
               (C : S) (C∈ : ⟨ C ∈ˢ Sset γ ⟩) where

  open Codes C
  open InLevel γ limγ

  member∈J : (m : ⟪ C ⟫) → InJ (ι m)
  member∈J m = Sset-trans γ {x = C} {y = ι m}
    (∈∈ₛ {a = ι m} {b = C} .snd (∈ₛ⟪ C ⟫↪ m)) C∈

  numeralJ : (k : ℕ) → InJ (# k)
  numeralJ = numeral∈J C C∈

  mkTag∈J : (k : ℕ) (x : S) → InJ x → InJ (VCode.mkTag k x)
  mkTag∈J k x hx = pr∈J (# k) x (numeralJ k) hx

  codeTm∈J : ∀ {n} (t : Term ⟪ C ⟫ n) → InJ (codeTm t)
  codeTm∈J (con m) = mkTag∈J 0 (ι m) (member∈J m)
  codeTm∈J (var i) = mkTag∈J 1 (# (toℕ i)) (numeralJ (toℕ i))

  code∈J : ∀ {n} (φ : Formula ⟪ C ⟫ n) → InJ (code φ)
  code∈J (t ∈̇ u) = mkTag∈J 0 (pr (codeTm t) (codeTm u))
    (pr∈J (codeTm t) (codeTm u) (codeTm∈J t) (codeTm∈J u))
  code∈J (t ≐ u) = mkTag∈J 1 (pr (codeTm t) (codeTm u))
    (pr∈J (codeTm t) (codeTm u) (codeTm∈J t) (codeTm∈J u))
  code∈J (φ ∧̇ ψ) = mkTag∈J 2 (pr (code φ) (code ψ))
    (pr∈J (code φ) (code ψ) (code∈J φ) (code∈J ψ))
  code∈J (φ ∨̇ ψ) = mkTag∈J 3 (pr (code φ) (code ψ))
    (pr∈J (code φ) (code ψ) (code∈J φ) (code∈J ψ))
  code∈J (φ ⇒̇ ψ) = mkTag∈J 4 (pr (code φ) (code ψ))
    (pr∈J (code φ) (code ψ) (code∈J φ) (code∈J ψ))
  code∈J (¬̇ φ)    = mkTag∈J 5 (code φ) (code∈J φ)
  code∈J ⊤̇        = mkTag∈J 6 (# 0) (numeralJ 0)
  code∈J ⊥̇        = mkTag∈J 7 (# 0) (numeralJ 0)
  code∈J (∃̇ φ)    = mkTag∈J 8 (code φ) (code∈J φ)
  code∈J (∀̇ φ)    = mkTag∈J 9 (code φ) (code∈J φ)
  code∈J (∀̇∈ t φ) = mkTag∈J 10 (pr (codeTm t) (code φ))
    (pr∈J (codeTm t) (code φ) (codeTm∈J t) (code∈J φ))
  code∈J (∃̇∈ t φ) = mkTag∈J 11 (pr (codeTm t) (code φ))
    (pr∈J (codeTm t) (code φ) (codeTm∈J t) (code∈J φ))

  codeSet⊆J : (k : ℕ) (x : S) → ⟨ x ∈ˢ codeSet k ⟩ → InJ x
  codeSet⊆J k x h = PT.rec (snd (x ∈ˢ Sset γ))
    (λ { (φ , q) → subst (λ w → ⟨ w ∈ˢ Sset γ ⟩) q (code∈J φ) })
    (codeSet-out k x h)

  allCodes⊆J : (x : S) → ⟨ x ∈ˢ allCodes ⟩ → InJ x
  allCodes⊆J x h = PT.rec (snd (x ∈ˢ Sset γ))
    (λ { (k , φ , q) → subst (λ w → ⟨ w ∈ˢ Sset γ ⟩) q (code∈J φ) })
    (allCodes-out x h)
```

<!--en-->
## The set itself, and what it would take
<!--zh-->
## 集合自身，以及它要什么
<!--/-->

<!--en-->
The containment half does not give the member half, and the gap is not an
artefact of how the set was built. A level is transitive, so a code set that was
a member at a stage would have all of its members at that stage; one arm of the
step adds one pair layer, a code's pair depth grows with the formula, and the
depths are unbounded. So the codes are cofinal below any stage that could hold
them, and **no finite offset above the carrier's stage holds the family.** The
statement to aim at is membership in a limit level, and even there membership
factors through one arm at one stage, so it asks for a rud value equal to the
code set.

Exactly one delivered machine manufactures such a value out of a description,
and it is the satisfaction engine: for any carrier the tower already holds, and
any formula of the object language over it, the set that formula defines is a
member of the limit level. That is the reduction stated here, and it is stated
for an arbitrary target rather than for the code set, since both sets need it
and neither uses anything about itself. The entry point is written so that a
discharge never has to produce an equation between sets: two containments at a
variable member are enough, which is how the bounding fragment of the Def-stage
chapter is stated as well.

What is left open is one object, named and typed: a formula over a level whose
definable set is the code set, which is the object-language predicate "is a code
of a formula over the carrier" together with both directions of its adequacy.
The engine supplies everything else.
<!--zh-->
包含的那一半给不出隶属的那一半，而这个缺口不是这个集合造法带来的假象。层是传递的，故若某个码集在某阶段处是成员，它的全部成员都已在该阶段到齐；而 step 的一臂只添一层对，码的对深度随公式增长，且诸深度无界。于是诸码在任何足以持有它们的阶段之下共尾，**载体所在阶段之上没有任何有限偏移持有这个族**。该瞄准的陈述是「属于某个极限层」，而即便在那里，隶属仍要经某个阶段处的某一臂分解，故它索取的是一个等于该码集的初步函数值。

交付好的机器里恰有一台能从一份描述造出这样的值，那就是满足集引擎：对塔已经持有的任何载体、以及其上对象语言的任何公式，该公式所定义的集合是该极限层的成员。此处陈述的就是这条归约，而且是对任意目标陈述、而非只对码集，因为两个集合都要用它，而它又不用关于自身的任何东西。入口写成这样：兑付方永远不必造出集合之间的等式，在变元成员上给两条包含即可，Def 阶段那一章的定界片段也正是这样陈述的。

留下未决的是一个对象，已具名、已定型：某层之上的一条公式，其可定义集就是该码集，也就是对象语言谓词「是载体之上某条公式的码」连同其适足性的两个方向。其余一切由引擎供给。
<!--/-->

```agda
  defSet∈J : (δ : S) → ⟨ δ ∈ˢ γ ⟩ → (Φ : Formula ⟪ Sset δ ⟫ 1)
           → InJ (DefOf.defSet (Sset δ) Φ)
  defSet∈J δ δ∈γ = SD.defSet-InJ
    where
    module SD = Sat (Sset δ)
      (λ x y x∈y y∈W → Sset-trans δ {x = y} {y = x} x∈y y∈W)
      InJ
      (λ a b hb a∈b → Sset-trans γ {x = b} {y = a} a∈b hb)
      (Jset-rud γ limγ)
      (Sset-mem {α = γ} {β = δ} δ∈γ)

  Description : S → Type (ℓ-suc ℓ)
  Description y =
    ∥ Σ[ δ ∈ S ] ( ⟨ δ ∈ˢ γ ⟩
      × (Σ[ Φ ∈ Formula ⟪ Sset δ ⟫ 1 ]
           (DefOf.defSet (Sset δ) Φ ≡ y)) ) ∥₁

  described∈J : (y : S) → Description y → InJ y
  described∈J y = PT.rec (snd (y ∈ˢ Sset γ)) go
    where
    go : Σ[ δ ∈ S ] ( ⟨ δ ∈ˢ γ ⟩
         × (Σ[ Φ ∈ Formula ⟪ Sset δ ⟫ 1 ]
              (DefOf.defSet (Sset δ) Φ ≡ y)) )
       → InJ y
    go (δ , δ∈γ , Φ , q) =
      subst (λ w → ⟨ w ∈ˢ Sset γ ⟩) q (defSet∈J δ δ∈γ Φ)

  description-write : (y δ : S) → ⟨ δ ∈ˢ γ ⟩ → (Φ : Formula ⟪ Sset δ ⟫ 1)
                    → ((x : S) → ⟨ x ∈ˢ DefOf.defSet (Sset δ) Φ ⟩ → ⟨ x ∈ˢ y ⟩)
                    → ((x : S) → ⟨ x ∈ˢ y ⟩ → ⟨ x ∈ˢ DefOf.defSet (Sset δ) Φ ⟩)
                    → Description y
  description-write y δ δ∈γ Φ sub sup = ∣ δ , (δ∈γ , (Φ , ext-⊆ sub sup)) ∣₁

  codeSet∈J : (k : ℕ) → Description (codeSet k) → InJ (codeSet k)
  codeSet∈J k = described∈J (codeSet k)

  allCodes∈J : Description allCodes → InJ allCodes
  allCodes∈J = described∈J allCodes
```

<!--en-->
## Recap
<!--zh-->
## 小结
<!--/-->

<!--en-->
The codes of the formulas over a carrier are one set at each arity
(`codeSet`{.Agda}) and one set across all of them (`allCodes`{.Agda}), each a
small family indexed by the external syntax, sealed at birth, with membership
characterized in both directions (`codeSet-spec`{.Agda},
`allCodes-spec`{.Agda}); at a fixed arity a member determines its formula over
the hierarchy outright (`codeSet-decode`{.Agda}), by the coding chapter's
injectivity. Every code is a member of any limit level holding the carrier
(`code∈J`{.Agda}), so both sets are subsets of that level
(`codeSet⊆J`{.Agda}, `allCodes⊆J`{.Agda}), the walk being one application of the
pairing operation per pair layer, three per numeral, and one for the empty set.

The set's own membership is not proved and not provable at a finite offset: the
codes are cofinal below every stage that could hold them. It is reduced instead
to a single missing object, the object-language predicate that defines the code
set over a level (`Description`{.Agda}, `codeSet∈J`{.Agda},
`allCodes∈J`{.Agda}), whose discharge the satisfaction engine converts into the
arms by itself.
<!--zh-->
载体之上诸公式的码，在每个元数上是一个集合 (`codeSet`{.Agda})，跨全部元数是一个集合 (`allCodes`{.Agda})，各自都是以外部语法为索引的小族，在诞生处封印，隶属双向刻画 (`codeSet-spec`{.Agda}、`allCodes-spec`{.Agda})；在固定元数上，一个成员直接决定它在层级之上的那条公式 (`codeSet-decode`{.Agda})，凭的是编码那一章的单射性。每个码都是任何持有该载体的极限层的成员 (`code∈J`{.Agda})，故两个集合都是该层的子集 (`codeSet⊆J`{.Agda}、`allCodes⊆J`{.Agda})，这趟行走每层对施用一次配对运算、每个数码三次、空集一次。

该集合自身的隶属未被证出，且在有限偏移处不可证：诸码在每个足以持有它们的阶段之下共尾。它转而被归约到单一一件缺失的对象，即在某层之上定义该码集的那条对象语言谓词 (`Description`{.Agda}、`codeSet∈J`{.Agda}、`allCodes∈J`{.Agda})，而它的兑付会被满足集引擎自行转成诸臂。
<!--/-->
