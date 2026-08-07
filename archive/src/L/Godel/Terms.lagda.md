# The combinator terms

<!--en-->
The syntax the tower will quantify. A combinator term mirrors a formula
constructor for constructor, but where a formula means through satisfaction,
a term means through **one set operation per node**: the atoms are selection
leaves, conjunction is the intersection, negation the difference from all
assignments, the existential the shift. Two easy inductions pin the mirror
down. Soundness reads each constructor's meaning back as a satisfaction set,
one reversed case equation per node, so a term can never denote anything a
formula does not. Completeness assigns every formula a term, through the
same reductions the satisfaction chapter proved, so a formula never means
anything a term cannot reach. The syntax has **no binders**: an arity index
does what the binders did, and that is why the recursion that will run over
its codes belongs to the cheap class the probes measured, not to the
satisfaction class this route replaced.
<!--zh-->
塔将要量化的语法。组合子项与公式逐构造子镜像对应，但公式经满足关系获得含义，项经**每节点一个集合运算**获得含义：原子是选择叶，合取是交，否定是对全体赋值的差，存在量词是移位。两个容易的归纳把这面镜子钉死。可靠性把每个构造子的含义读回为一个满足集，每节点一条反向的情形等式，故项决不能指称公式所不指称的东西。完备性给每条公式指派一个项，靠的正是满足关系那一章已证的那些化归，故公式决不意指项所够不着的东西。这套语法**没有绑定子**：一个元数索引干了绑定子的活，而这正是将来跑在其码上的递归属于探针所测的便宜类别、而非本路线所取代的满足类别的原因。
<!--/-->

```agda
{-# OPTIONS --cubical --safe --guardedness #-}

open import Base.Prelude

module L.Godel.Terms {ℓ : Level} where

open import Base.Classical using ( LEM )

open import FOL.Syntax
  using ( Formula; Term; var; con
        ; _∈̇_; _≐_; _∧̇_; _∨̇_; _⇒̇_; ¬̇_; ∃̇_; ∀̇_; ∀̇∈; ∃̇∈; ⊤̇; ⊥̇ )
open import FOL.Manipulation.Renaming using ( renameTm )
open import L.Godel.Operations {ℓ}
  using ( _∪_; _∩_; _∖_; ∖-self
        ; selectMember; selectEqual; extendFamily; shiftDown; values )
open import L.Godel.Tuples {ℓ} using ( allTuples )
open import L.Definability {ℓ} using ( module DefOf )
open import L.Godel.Satisfaction {ℓ}
  using ( satSet; sat-⊥; sat-⊤; sat-∧; sat-∨; sat-¬; sat-∈vv; sat-≐vv
        ; sat-≐vc; sat-∃; sat-defSet
        ; red-∈cv; red-∈vc; red-∈cc; red-≐cv; red-≐cc; red-∃∈; red-∀∈
        ; module Classical )

open import V.Hierarchy {ℓ} using ( extensionalV )

open import Cubical.Data.FinData using ( toℕ )
import Cubical.HITs.PropositionalTruncation as PT
open import Cubical.Functions.Logic using ( ⇔toPath )
open import Cubical.HITs.CumulativeHierarchy.Base using ( V; sett; _∈_ )
open import Cubical.HITs.CumulativeHierarchy.Properties using ( ⟪_⟫; ⟪_⟫↪ )
open import Cubical.HITs.CumulativeHierarchy.Constructions
  using ( ⁅_⁆s; module InfinitySet )
open InfinitySet using ( #_ )
```

<!--en-->
## The syntax

Four leaves and four nodes, indexed by the arity. The leaves are all
assignments, the two selections at variable keys, and the one selection
against a constant, which is the exceptional atom in combinator form; the
constant enters as a parameter of the leaf. The nodes are intersection,
union, complement against all assignments, and the shift, which lowers the
arity by one and is the only constructor that moves it. The syntax is
declared at an abstract parameter type and applied at the carrier's members,
per the recorded law.
<!--zh-->
## 语法

四种叶与四种节点，以元数为索引。叶是全体赋值、变元键处的两种选择，与对常元的那一种选择，即例外原子的组合子形态；常元以叶的参数进场。节点是交、并、对全体赋值的补，与移位，后者把元数降一并且是唯一移动元数的构造子。语法按已记录的定律在抽象参数类型处声明、在载体成员处应用。
<!--/-->

```agda
data KT (P : Type ℓ) : ℕ → Type ℓ where
  allK      : {n : ℕ} → KT P n
  selMemK   : {n : ℕ} → Fin n → Fin n → KT P n
  selEqK    : {n : ℕ} → Fin n → Fin n → KT P n
  selEqConK : {n : ℕ} → Fin n → P → KT P n
  interK unionK : {n : ℕ} → KT P n → KT P n → KT P n
  complK    : {n : ℕ} → KT P n → KT P n
  shiftK    : {n : ℕ} → KT P (suc n) → KT P n
```

<!--en-->
## Denotation, and the mirror formula

A term denotes a set by structural recursion, one operation application per
node, over the operations' sealed heads. In the other direction every term
carries a formula, its mirror image constructor by constructor.
<!--zh-->
## 指称，与镜像公式

项经结构递归指称一个集合，每节点一次运算应用，落在诸运算的封印头上。反过来每个项携带一条公式，即它逐构造子的镜像。
<!--/-->

```agda
module _ (A : V ℓ) where
  open DefOf A using ( Def )

  private
    κ : ⟪ A ⟫ → V ℓ
    κ = ⟪ A ⟫↪

  ⟦_⟧ᴷ : {n : ℕ} → KT ⟪ A ⟫ n → V ℓ
  ⟦_⟧ᴷ {n} allK = allTuples A n
  ⟦_⟧ᴷ {n} (selMemK i j) =
    selectMember (allTuples A n) ⁅ # (toℕ i) ⁆s ⁅ # (toℕ j) ⁆s
  ⟦_⟧ᴷ {n} (selEqK i j) =
    selectEqual (allTuples A n) ⁅ # (toℕ i) ⁆s ⁅ # (toℕ j) ⁆s
  ⟦_⟧ᴷ {n} (selEqConK i a) =
    shiftDown (selectEqual (extendFamily (allTuples A n) ⁅ κ a ⁆s)
                ⁅ # (suc (toℕ i)) ⁆s ⁅ # 0 ⁆s)
  ⟦ interK s t ⟧ᴷ = ⟦ s ⟧ᴷ ∩ ⟦ t ⟧ᴷ
  ⟦ unionK s t ⟧ᴷ = ⟦ s ⟧ᴷ ∪ ⟦ t ⟧ᴷ
  ⟦_⟧ᴷ {n} (complK t) = allTuples A n ∖ ⟦ t ⟧ᴷ
  ⟦ shiftK t ⟧ᴷ = shiftDown ⟦ t ⟧ᴷ

  toFormula : {n : ℕ} → KT ⟪ A ⟫ n → Formula ⟪ A ⟫ n
  toFormula allK = ⊤̇
  toFormula (selMemK i j) = var i ∈̇ var j
  toFormula (selEqK i j) = var i ≐ var j
  toFormula (selEqConK i a) = var i ≐ con a
  toFormula (interK s t) = toFormula s ∧̇ toFormula t
  toFormula (unionK s t) = toFormula s ∨̇ toFormula t
  toFormula (complK t) = ¬̇ toFormula t
  toFormula (shiftK t) = ∃̇ toFormula t
```

<!--en-->
## Soundness

Every term denotes the satisfaction set of its mirror formula. Each case is
the corresponding case equation of the satisfaction chapter run backward,
and the composite cases carry the induction hypotheses across by
congruence. This is the direction the old route had no cheap counterpart
for: it says the combinators can never overshoot definability.
<!--zh-->
## 可靠性

每个项指称其镜像公式的满足集。每个情形是满足关系那一章相应情形等式的反向运行，复合情形由同余把归纳假设搬过去。这是旧路线没有便宜对应物的那个方向：它说组合子决不越出可定义性。
<!--/-->

```agda
  sound : {n : ℕ} (t : KT ⟪ A ⟫ n) → ⟦ t ⟧ᴷ ≡ satSet A (toFormula t)
  sound allK = sym (sat-⊤ A)
  sound (selMemK i j) = sym (sat-∈vv A i j)
  sound (selEqK i j) = sym (sat-≐vv A i j)
  sound (selEqConK i a) = sym (sat-≐vc A i a)
  sound (interK s t) =
    cong₂ _∩_ (sound s) (sound t)
    ∙ sym (sat-∧ A (toFormula s) (toFormula t))
  sound (unionK s t) =
    cong₂ _∪_ (sound s) (sound t)
    ∙ sym (sat-∨ A (toFormula s) (toFormula t))
  sound (complK t) =
    cong (allTuples A _ ∖_) (sound t) ∙ sym (sat-¬ A (toFormula t))
  sound (shiftK t) =
    cong shiftDown (sound t) ∙ sym (sat-∃ A (toFormula t))

  termDef : V ℓ
  termDef = sett (KT ⟪ A ⟫ 1) (λ t → values ⟦ t ⟧ᴷ)
```

<!--en-->
## Completeness

Every formula has a term denoting its satisfaction set. The mirror lemma
`Mirror`{.Agda} packages the term with its denotation path; the atoms go by
cases on the two terms through the reductions, the guarded quantifiers
through their weakenings, and the implication and the universal through the
classical equations, so the whole assignment stands under the one
assumption those two cases already cost.
<!--zh-->
## 完备性

每条公式有一个指称其满足集的项。镜像引理 `Mirror`{.Agda} 把项与其指称路径打包；原子对两个词项分情形、经诸化归而过，受卫量词经各自的弱化，蕴含与全称经经典等式，故整个指派立于那两个情形本就要花的那一份假设之下。
<!--/-->

```agda
  Mirror : {n : ℕ} → Formula ⟪ A ⟫ n → Type (ℓ-suc ℓ)
  Mirror {n} φ = Σ[ t ∈ KT ⟪ A ⟫ n ] (⟦ t ⟧ᴷ ≡ satSet A φ)

  private
    mirrorBy : {n : ℕ} {φ ψ : Formula ⟪ A ⟫ n}
             → Mirror ψ → satSet A φ ≡ satSet A ψ → Mirror φ
    mirrorBy (t , e) eq = t , e ∙ sym eq

    existsInter : {n : ℕ} (φ ψ : Formula ⟪ A ⟫ (suc n))
                → Mirror φ → Mirror ψ → Mirror (∃̇ (φ ∧̇ ψ))
    existsInter φ ψ (t₁ , e₁) (t₂ , e₂) =
      shiftK (interK t₁ t₂)
      , cong shiftDown (cong₂ _∩_ e₁ e₂ ∙ sym (sat-∧ A φ ψ))
      ∙ sym (sat-∃ A (φ ∧̇ ψ))

    atom≐ : {n : ℕ} (t u : Term ⟪ A ⟫ n) → Mirror (t ≐ u)
    atom≐ (var i) (var j) = selEqK i j , sym (sat-≐vv A i j)
    atom≐ (var i) (con a) = selEqConK i a , sym (sat-≐vc A i a)
    atom≐ (con a) (var i) = mirrorBy
      {φ = con a ≐ var i} {ψ = var i ≐ con a}
      (selEqConK i a , sym (sat-≐vc A i a)) (red-≐cv A i a)
    atom≐ (con a) (con b) = mirrorBy
      {φ = con a ≐ con b}
      {ψ = ∃̇ ((var zero ≐ con a) ∧̇ (var zero ≐ con b))}
      (existsInter (var zero ≐ con a) (var zero ≐ con b)
        (selEqConK zero a , sym (sat-≐vc A zero a))
        (selEqConK zero b , sym (sat-≐vc A zero b)))
      (red-≐cc A a b)

    atom∈ : {n : ℕ} (t u : Term ⟪ A ⟫ n) → Mirror (t ∈̇ u)
    atom∈ (var i) (var j) = selMemK i j , sym (sat-∈vv A i j)
    atom∈ (var i) (con a) = mirrorBy
      {φ = var i ∈̇ con a}
      {ψ = ∃̇ ((var zero ≐ con a) ∧̇ (var (suc i) ∈̇ var zero))}
      (existsInter (var zero ≐ con a) (var (suc i) ∈̇ var zero)
        (selEqConK zero a , sym (sat-≐vc A zero a))
        (selMemK (suc i) zero , sym (sat-∈vv A (suc i) zero)))
      (red-∈vc A i a)
    atom∈ (con a) (var j) = mirrorBy
      {φ = con a ∈̇ var j}
      {ψ = ∃̇ ((var zero ≐ con a) ∧̇ (var zero ∈̇ var (suc j)))}
      (existsInter (var zero ≐ con a) (var zero ∈̇ var (suc j))
        (selEqConK zero a , sym (sat-≐vc A zero a))
        (selMemK zero (suc j) , sym (sat-∈vv A zero (suc j))))
      (red-∈cv A j a)
    atom∈ (con a) (con b) = mirrorBy
      {φ = con a ∈̇ con b}
      {ψ = ∃̇ ((var zero ≐ con b) ∧̇ (con a ∈̇ var zero))}
      (existsInter (var zero ≐ con b) (con a ∈̇ var zero)
        (selEqConK zero b , sym (sat-≐vc A zero b))
        (mirrorBy
          {φ = con a ∈̇ var zero}
          {ψ = ∃̇ ((var zero ≐ con a) ∧̇ (var zero ∈̇ var (suc zero)))}
          (existsInter (var zero ≐ con a) (var zero ∈̇ var (suc zero))
            (selEqConK zero a , sym (sat-≐vc A zero a))
            (selMemK zero (suc zero) , sym (sat-∈vv A zero (suc zero))))
          (red-∈cv A zero a)))
      (red-∈cc A a b)

  module WithLEM (lem : LEM (ℓ-suc ℓ)) where
    private module C = Classical A lem

    private
      mirrorAnd : {n : ℕ} (φ ψ : Formula ⟪ A ⟫ n)
                → Mirror φ → Mirror ψ → Mirror (φ ∧̇ ψ)
      mirrorAnd φ ψ (t₁ , e₁) (t₂ , e₂) =
        interK t₁ t₂ , cong₂ _∩_ e₁ e₂ ∙ sym (sat-∧ A φ ψ)

      mirrorOr : {n : ℕ} (φ ψ : Formula ⟪ A ⟫ n)
               → Mirror φ → Mirror ψ → Mirror (φ ∨̇ ψ)
      mirrorOr φ ψ (t₁ , e₁) (t₂ , e₂) =
        unionK t₁ t₂ , cong₂ _∪_ e₁ e₂ ∙ sym (sat-∨ A φ ψ)

      mirrorNeg : {n : ℕ} (φ : Formula ⟪ A ⟫ n)
                → Mirror φ → Mirror (¬̇ φ)
      mirrorNeg {n} φ (t , e) =
        complK t , cong (allTuples A n ∖_) e ∙ sym (sat-¬ A φ)

      mirrorImp : {n : ℕ} (φ ψ : Formula ⟪ A ⟫ n)
                → Mirror φ → Mirror ψ → Mirror (φ ⇒̇ ψ)
      mirrorImp {n} φ ψ (t₁ , e₁) (t₂ , e₂) =
        complK (interK t₁ (complK t₂))
        , cong (allTuples A n ∖_)
            (cong₂ _∩_ e₁ (cong (allTuples A n ∖_) e₂))
        ∙ sym (C.sat-⇒ φ ψ)

      mirrorEx : {n : ℕ} (φ : Formula ⟪ A ⟫ (suc n))
               → Mirror φ → Mirror (∃̇ φ)
      mirrorEx φ (t , e) =
        shiftK t , cong shiftDown e ∙ sym (sat-∃ A φ)

      mirrorAll : {n : ℕ} (φ : Formula ⟪ A ⟫ (suc n))
                → Mirror φ → Mirror (∀̇ φ)
      mirrorAll {n} φ (t , e) =
        complK (shiftK (complK t))
        , cong (allTuples A n ∖_)
            (cong shiftDown (cong (allTuples A (suc n) ∖_) e))
        ∙ sym (C.sat-∀ φ)

      mirrorExB : {n : ℕ} (t : Term ⟪ A ⟫ n) (φ : Formula ⟪ A ⟫ (suc n))
                → Mirror φ → Mirror (∃̇∈ t φ)
      mirrorExB t φ mφ = mirrorBy
        {φ = ∃̇∈ t φ}
        {ψ = ∃̇ ((var zero ∈̇ renameTm suc t) ∧̇ φ)}
        (existsInter (var zero ∈̇ renameTm suc t) φ
          (atom∈ (var zero) (renameTm suc t)) mφ)
        (red-∃∈ A t φ)

      mirrorAllB : {n : ℕ} (t : Term ⟪ A ⟫ n) (φ : Formula ⟪ A ⟫ (suc n))
                 → Mirror φ → Mirror (∀̇∈ t φ)
      mirrorAllB {n} t φ (tb , eb) = mirrorBy
        {φ = ∀̇∈ t φ}
        {ψ = ∀̇ ((var zero ∈̇ renameTm suc t) ⇒̇ φ)}
        (let (tg , eg) = atom∈ (var zero) (renameTm suc t)
         in complK (shiftK (complK (complK (interK tg (complK tb)))))
          , cong (allTuples A n ∖_)
              (cong shiftDown (cong (allTuples A (suc n) ∖_)
                ( cong (allTuples A (suc n) ∖_)
                    (cong₂ _∩_ eg (cong (allTuples A (suc n) ∖_) eb))
                ∙ sym (C.sat-⇒ (var zero ∈̇ renameTm suc t) φ) )))
          ∙ sym (C.sat-∀ ((var zero ∈̇ renameTm suc t) ⇒̇ φ)))
        (red-∀∈ A t φ)

    mirror : {n : ℕ} (φ : Formula ⟪ A ⟫ n) → Mirror φ
    mirror {n} ⊥̇ = complK allK
      , ∖-self (allTuples A n) ∙ sym (sat-⊥ A)
    mirror ⊤̇ = allK , sym (sat-⊤ A)
    mirror (t ∈̇ u) = atom∈ t u
    mirror (t ≐ u) = atom≐ t u
    mirror (φ ∧̇ ψ) = mirrorAnd φ ψ (mirror φ) (mirror ψ)
    mirror (φ ∨̇ ψ) = mirrorOr φ ψ (mirror φ) (mirror ψ)
    mirror (¬̇ φ) = mirrorNeg φ (mirror φ)
    mirror (φ ⇒̇ ψ) = mirrorImp φ ψ (mirror φ) (mirror ψ)
    mirror (∃̇ φ) = mirrorEx φ (mirror φ)
    mirror (∀̇ φ) = mirrorAll φ (mirror φ)
    mirror (∃̇∈ t φ) = mirrorExB t φ (mirror φ)
    mirror (∀̇∈ t φ) = mirrorAllB t φ (mirror φ)
```

<!--en-->
## The definable powerset, through the terms

The equivalence the tower will spend. The set of values of arity-one terms
**is** the definable powerset: one inclusion sends a term to its mirror
formula by soundness and the values bridge, the other sends a formula to its
mirror term by completeness and the same bridge. From here on, quantifying
the definable subsets and quantifying the arity-one terms are the same act,
and only the second one is available to a recursion without binders.
<!--zh-->
## 可定义幂集，经由诸项

塔将要花掉的等价。元数一诸项的取值之集**就是**可定义幂集：一个包含把项经可靠性与取值之桥送到其镜像公式，另一个把公式经完备性与同一座桥送到其镜像项。自此，量化诸可定义子集与量化元数一诸项是同一个动作，而只有后者是无绑定子的递归所能企及的。
<!--/-->

```agda
    termDef≡Def : termDef ≡ Def
    termDef≡Def = extensionalV λ w → ⇔toPath (toDef w) (fromDef w)
      where
      toDef : (w : V ℓ) → ⟨ w ∈ termDef ⟩ → ⟨ w ∈ Def ⟩
      toDef w = PT.map λ { (t , e) →
        toFormula t
        , sym (sat-defSet A (toFormula t))
        ∙ cong values (sym (sound t)) ∙ e }
      fromDef : (w : V ℓ) → ⟨ w ∈ Def ⟩ → ⟨ w ∈ termDef ⟩
      fromDef w = PT.map λ { (φ , e) →
        mirror φ .fst
        , cong values (mirror φ .snd) ∙ sat-defSet A φ ∙ e }
```

<!--en-->
## Recap

The combinator syntax `KT`{.Agda} with its denotation and mirror formula,
`sound`{.Agda} reading every term back as the satisfaction set of its
mirror, `mirror`{.Agda} assigning every formula a term under the one
classical assumption, and the payoff `termDef≡Def`{.Agda}: the values of
the arity-one terms `termDef`{.Agda} **are** the definable powerset. From
here on, quantifying the definable subsets and quantifying the terms are
the same act, and the terms do it without binders, which is what the
internal recursion over their codes will spend.
<!--zh-->
## 小结

组合子语法 `KT`{.Agda} 连同指称与镜像公式，`sound`{.Agda} 把每个项读回为其镜像的满足集，`mirror`{.Agda} 在那一份经典假设下给每条公式指派一个项，以及回报 `termDef≡Def`{.Agda}：元数一诸项的取值之集 `termDef`{.Agda} **就是**可定义幂集。自此，量化诸可定义子集与量化诸项是同一个动作，而项不用绑定子就做到了，这正是跑在其码上的内部递归将要花掉的东西。
<!--/-->
