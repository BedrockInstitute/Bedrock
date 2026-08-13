# g2 report: the full switch at arbitrary formulas, delivered

**Delivered, no wall, no residue.** `src/L/Rud/SatSets.lagda.md` builds the
satisfaction sets `T n φ` for **every** formula of the tree's FOL over the carrier
of a transitive rud-closed `U`, proves each one a member of the abstract closure,
proves two-way adequacy against the external face (`DefOf U`'s inner satisfaction
`⊨ᵐ`, the very face `smallSat`/`defSet` are built from), identifies the arity-one
satisfaction set with `defSet φ` on the nose, and discharges the closure at a pair
of limit levels to give

```agda
module LimitFullSwitch (α) (limα) (β) (limβ) (β∈α) where
  full-switch-⊇ : (φ : Formula ⟪ Ju ⟫ 1) → ⟨ DefOf.defSet Ju φ ∈ˢ Jα ⟩
```

with `Ju = Jset β limβ`, `Jα = Jset α limα`. That is gap G2 exactly as
`_build/r5recon-b.md` §2 states it, with **no Δ₀ hypothesis and no residue**.

**1,285 code lines, 6.2 s wall cold (interface deleted; 1.28 s pure typechecking),
no postulate, no hole,
no `TERMINATING`, no wall event, every check under `GHCRTS=-M12g`.** The probe
extrapolated 1,000-2,250; the build landed at the **low end** of that band, 54% of
the 2,400 stop-line. The engine half closed at 987 lines, under the 1,200 pause
gate, so no pause was taken.

---

## 1. Price table against the probe's extrapolation

Code lines exclude blanks and comments. "Probe" is the probe report's §5 row;
"shared kit" lines are counted once and consumed by many clauses.

| Item | Probe extrapolation | Actual | Verdict |
|---|---|---|---|
| all atom shapes (`∈̇`, `≐`, var/var, var/con, con/var, con/con), both directions | 48-80 | **134** | over: the probe priced one atom shape, not eight |
| k-ary plumbing (`Coord`/`LR`, `Atoms`/`Bin`, `Sel`, decode) | 150-250 | **211** | in band |
| negation, one arity-generic clause | 67-84 | **7** | **10x under** (see §3) |
| unbounded `∃̇` clause | 24-32 | **19** + 41 shared (`ranOp`) | in band |
| `∧̇` | 30-50 | **10** + 17 shared (`capOp`) | under |
| `∨̇` | 25-40 | **19** + 20 shared (`cupOp`) | in band |
| `⇒̇` | 15-25 | **18** | in band |
| `⊤̇`, `⊥̇` | not priced | **8** | - |
| bounded `∀̇∈`/`∃̇∈` (incl. the term-evaluation set `Ev`) | 40-70 | **127** | over: `Ev` + two classical clauses |
| `∀̇` (not separately priced) | - | **36** | - |
| the three base relations on the level (`Mem`, `Diag`, `Memᶜ`, `Slf`, `Up`, the triple sets) | not priced | **341** | the probe's blind spot (see §4) |
| tuple spaces, `Tup`, `Us-in/out`, `Tup-inj`, `Sat-cong` | 54+20 (probe: 74) | **35** | **2x under** |
| closure interface + sixteen-op arms | 42 (probe) | **30** | under |
| `T-sub` (the satisfaction set is inside the tuple space) | not priced | **32** | new obligation, see LC-G2-1 |
| the `defSet` bridge + limit-level assembly | 60-120 | **52** | under |
| **total** | **1,000-2,250** (D-6 applied) | **1,285** | **low end of the band** |

Per-section totals as the file is laid out: preamble 33, derived operations 85,
closure interface 30, tuple spaces 35, base relations 341, coordinate families
(incl. `Atoms`, `Sel`) 256, atoms + engine 208, adequacy 245, `defSet` bridge 37,
limit switch 15.

**Timings** (each check `GHCRTS=-M12g`, one at a time, warm dependencies): 1.3 s
(tuple spaces) → 1.4 s (derived ops) → 1.7 s (base relations) → 2.0 s (diagonal) →
2.3 s (converse, self-membership, `Up`) → 2.8 s (`Coord`) → 4.2 s (`Atoms`,
`Sel`) → 5.0 s (atoms, `Ev`, `T`, engine) → 5.8 s (adequacy) → **6.35 s** (bridge
+ limit switch); 6.2 s on a true cold re-check with the interface deleted. Monotone, no step above 1.5 s of marginal cost, tripwire 180 s
never approached. `--profile=definitions` attributes 1,279 ms and reports no
definition above the noise floor, so there is no hot spot to name.

## 2. The convention fork, recorded

**Ruling followed: the delivered right-nested convention was not touched.** No
re-association of `F3`/`F4`; the converse step is paid explicitly, as its own
sealed helper with an R-36 read.

The helper is the **range**:

```agda
opaque
  ranOp : V ℓ → V ℓ
  ranOp x = F5 (F8 x (F6 x x)) (F8 x (F6 x x))
  ranOp-in  : (x m : V ℓ) → ⟨ m ∈ˢ ranOp x ⟩ → ∥ Σ[ u ∈ V ℓ ] ⟨ pr u m ∈ˢ x ⟩ ∥₁
  ranOp-out : (x u m : V ℓ) → ⟨ pr u m ∈ˢ x ⟩ → ⟨ m ∈ˢ ranOp x ⟩
```

classically `ran x = ⋃ { x"{u} ∣ u ∈ dom x }`. **Measured fork cost: 41 code
lines** (33 for the operation with both directions of its spec inside the seal,
8 for the closure arm `J-ran` in its own `opaque unfolding` block). Nothing else
in the file pays for the convention.

**A correction to the probe's fork analysis, and it flips the sign.** The probe
said left-nesting makes the *last-variable* existential `F6`-native. Under de
Bruijn binding the quantifier binds variable **zero**, which is the **head** of
the environment, so the coordinate the existential eliminates is the head, not the
tail. With right-nested tuples `⟨v₀,v₁,…⟩ = pr v₀ ⟨v₁,…⟩` the head is the pair's
left component, so the needed projection is the **range**, not the domain: hence
`ranOp`. With left-nested tuples the head would be the outermost right component,
`F6` would still not be native (it projects left), and the *atom* families would
lose `F3`/`F4`, which are precisely right-nested: `F4 (Us n) R` starts a
coordinate family and `F3 U _` walks it up one arity, both by their delivered
specs, with no shuffling. So the frozen-surface ruling was also the **cheap**
choice: it localises the whole convention cost in 41 lines of `ranOp` and buys the
entire atom plumbing for free. The delta versus re-association is therefore
**negative** (re-association would have cost more), and no cheaper route was
found.

Second-order dividend: `ranOp` is then reused three more times, in the diagonal
(`Dif2`, `Dif2'`), the converse of membership (`Memᶜ`) and the self-membership
slice (`Slf`), so its 41 lines are amortised over four consumers.

## 3. The decode-uniqueness dividend, measured

The probe's correction 3 was the biggest structural saving it identified: state
decode-uniqueness once per arity so no clause re-proves the `pr-inj`
identification. Applied here **before any clause work**, and it generalised
further than the probe predicted.

```agda
Tup-inj  : (n : ℕ) (δ ε : Vec SM (suc n)) → Tup n δ ≡ Tup n ε → δ ≡ ε   -- 6 lines
Sat-cong : (n) (φ) (δ ε) → Tup n δ ≡ Tup n ε → ⟨ ε ⊨ᵐ φ ⟩ → ⟨ δ ⊨ᵐ φ ⟩  -- 3 lines
```

Nine lines, once, arity-generic and formula-generic. The consequence is a change
of **shape**, not just of size: adequacy is stated **at a tuple**,

```agda
adeq-mem : (n) (φ) (δ) → ⟨ Tup n δ ∈ˢ T n φ ⟩ → ⟨ δ ⊨ᵐ φ ⟩
adeq-set : (n) (φ) (δ) → ⟨ δ ⊨ᵐ φ ⟩ → ⟨ Tup n δ ∈ˢ T n φ ⟩
```

and the arbitrary-member form (`adeq-in`/`adeq-out`, the probe's shape) is derived
once in 13 lines, routed through the new subset lemma
`T-sub : ⟨ m ∈ˢ T n φ ⟩ → ⟨ m ∈ˢ Us n ⟩` (32 lines). Because both directions live
at a tuple, **no clause ever holds two decodes of one member**.

**Measured dividend.** The probe's negation clause cost 56 lines and was paid
twice (112 lines for two arities), and the probe attributed the whole bulk to the
`pr-inj` identification. Here negation costs **7 lines total** across `T`, `hT`,
`T-sub`, `adeq-mem` and `adeq-set`, arity-generic:

```agda
T n (¬̇ φ) = F1 (Us n) (T n φ)
hT n (¬̇ φ) = JF1 (Us n) (T n φ) (hUs n) (hT n φ)
T-sub n (¬̇ φ) m h = dif-in (Us n) (T n φ) m h .fst
adeq-mem n (¬̇ φ) δ h sat = dif-in (Us n) (T n φ) (Tup n δ) h .snd (adeq-set n φ δ sat)
adeq-set n (¬̇ φ) δ sat = dif-out (Us n) (T n φ) (Tup n δ) (Us-out n δ) (λ k → sat (adeq-mem n φ δ k))
```

That is a **16x reduction on the probe's own clause**, and the same shape carries
`⇒̇` (18 lines), `∀̇` (36) and `∀̇∈` (55) with no decode work at all. LC-1 of the
probe report is confirmed and should be strengthened (see §6, LC-G2-1).

## 4. The probe's other two corrections, and its one blind spot

**Correction 2 (`Utrans` is not needed by the satisfaction sets themselves)** is
confirmed exactly. `Utrans` is consumed **5 times**, all in the places the probe
predicted plus one it did not: the diagonal's two extensionality directions
(`Diag-read`), the diagonal's forward witness (`Dif2-out` via `Diag-read`), the
parameter atom `var i ∈̇ con d` (the `Sel` subset side condition), and the
bounded-quantifier term set `Ev n (con c)`. `UmemInJ` (from `Jtrans`) is consumed
**6 times**, all at parameter atoms and their closure arms, exactly as predicted.
No connective and no unbounded quantifier consumes either.

**Correction 1 (choose the tuple convention against the projection)** is §2.

**The blind spot: the probe never priced the equality atom.** Its mini fragment
had only `∈`. The full `Formula` type has `_≐_`, and the object language's
`≐` atom at two variable positions needs the **diagonal of `U` as a set in the
closure**, which is not in the sixteen-function basis and is not a slice of
anything the basis names. That is the 341-line "three base relations" section and
it is the single largest item the extrapolation missed. It is solved without any
new basis operation and without a syntactic elimination of `≐` (see LC-G2-3).

## 5. The theorem as proved, and what it does not need

```agda
module LimitFullSwitch (α : V ℓ) (limα : ⟨ isLimit α ⟩)
                       (β : V ℓ) (limβ : ⟨ isLimit β ⟩) (β∈α : ⟨ β ∈ˢ α ⟩) where
  Ju = Jset β limβ ; Jα = Jset α limα
  module S = Sat Ju Jutrans (λ x → ⟨ x ∈ˢ Jα ⟩) Jαtrans (Jset-rud α limα) Ju∈Jα
  full-switch-⊇ : (φ : Formula ⟪ Ju ⟫ 1) → ⟨ DefOf.defSet Ju φ ∈ˢ Jα ⟩
```

Discharged entirely from delivered exports: `Jset`, `Jset-rud`, `Sset-trans`,
`Sset-mem` (all from `L.Rud.Step`'s `ConcreteS`), `isLimit` from `OrdArith`,
`Ops`/`Images` for the basis, `L.Definability`'s `DefOf` for the face. **No lemma
the delivered tree lacks was needed, so there is no R-36 stop and no residue.**

**A bonus worth flagging to the owner.** The delivered Δ₀ switch
`LimitSwitch.Up.definable→closure` (Switch:1158) lives inside `module Up (Jimg …)`
and is therefore **conditional on the rud image principle**, the standing residue
of the Switch chapter. `full-switch-⊇` is **unconditional**: it never runs the
composite-realization walk, so it never meets `imgC`. The general theorem is
strictly less hypothesis-laden than the special case as delivered. If the bridge
(G3) is built on `full-switch-⊇` instead of `definable→closure`, the `Jimg`
residue drops out of the Def→rud half of the bridge altogether.

**Ruled deviation, recorded.** `L.Rud.Switch` is **not** imported. Its `interOp`
(intersection by double difference with the D-7 excluded-middle spend) is rebuilt
locally as `capOp`, sealed at birth with both spec directions inside, 17 lines,
plus 3 lines for the `J-cap` arm. The brief sanctioned either route; the local
copy keeps the import surface at `Ops` + `Images` + `Step` + `Definability` +
`Syntax`/`Semantics`/`Smallness` and avoids pulling `Realize`/`Describe` through
`Switch`. **Delta: +20 lines, one duplicated 2-line operation body.** The
statement's shape is nonetheless drop-in beside `LimitSwitch` (same five module
parameters, same `Jset`/`Jset-rud` discharge), so a future assembly can place the
two side by side or fold `SatSets`'s module into `Switch` at zero cost.

**Classical spend.** `dneV` (double-negation elimination from `lem`) at 8 sites:
`capOp-in` (the D-7 spot), the diagonal's two subset directions, and the three
classical clauses `⇒̇`, `∀̇`, `∀̇∈`. `lem` is also called directly at the two
constant-constant atoms (`con c ∈̇ con d`, `con c ≐ con d`), dispatched through an
explicit-argument decision helper `condSet`/`cond-in`/`cond-out`, never `with`
(R-10, P-i [C′]).

## 6. Lesson candidates, with measurements

**LC-G2-1 (strengthens the probe's LC-1). State two-way adequacy AT A TUPLE, and
derive the arbitrary-member form once through a subset lemma.** The probe's
recommendation was "one decode-uniqueness lemma per arity". The stronger form is
to change the statement shape: `adeq-mem`/`adeq-set` quantify over the environment
`δ`, not over a member `m`, so the equation `m ≡ Tup n δ` never appears in a
clause. The member-level pair is recovered in 13 lines from `Us-in` plus a new
obligation `T-sub : T n φ ⊆ Us n` (32 lines, one clause per constructor, mostly
one-liners). **Measured: the probe's negation clause 56 lines → 7 lines
arity-generic (16x); zero `pr-inj` chases in any of the twelve clauses; total
adequacy 245 lines for twelve constructors in both directions.**

**LC-G2-2. Under de Bruijn binding the quantified coordinate is the tuple's HEAD,
so the tuple convention is fixed by which projection the quantifier needs, and the
same choice fixes which of `F3`/`F4` does the atom plumbing.** Both constraints
pull the same way under the delivered right-nested convention: pay one range
operation (41 lines) and get the coordinate families for free (`F4` starts,
`F3` walks up, `F2` cylindrifies). Refines the probe's LC-3, which read the fork
off `F6` alone and therefore got the sign backwards. **Measured: 41 lines of
`ranOp`, amortised over 4 consumers; 0 lines of tuple shuffling in the atoms.**

**LC-G2-3. The diagonal of a transitive rud-closed level is constructible from the
basis, via extensionality plus the range; equality atoms need no new operation and
no syntactic elimination of `≐`.** Concretely, with `Us1 = U×U`, `Us2 = U³`,
`In3L = F4 U (F7 U U)` (`{⟨a,b,c⟩ : a ∈ b}`) and `In3R = F3 U (F7 U U)`
(`{⟨a,b,c⟩ : a ∈ c}`),

```
Diag = Us1 ∖ ( ran (In3L ∩ (Us2 ∖ In3R))  ∪  ran (In3R ∩ (Us2 ∖ In3L)) )
```

reads "no member of one that the other lacks, either way", and extensionality
closes it. From the diagonal, the converse of membership is
`Memᶜ = ran (In3L ∩ F3 U Diag)` and the self-membership slice (the equal-index
`∈` atom) is `Slf = ran (Mem ∩ Diag)`, both by the same one-line pattern.
**Measured: 130 lines for the diagonal with both directions, 30 for the converse,
30 for the self-membership slice; no foundation axiom, no `≐`-elimination pass,
no new basis operation.** This is the item the probe's extrapolation missed
entirely.

**LC-G2-4. Recurse on the ARITY, never permute coordinates.** An atom relating two
coordinates of an `(n+1)`-tuple splits four ways on whether each index is the head:
both past the head is a cylinder `F2 U _` one arity down; head against a later
coordinate is the `F3`-insertion family started by `F4`; a later coordinate against
the head is the same family at the **converse** relation; both at the head is the
diagonal slice. **Measured: `LR` 3 clauses, `Bin` 5 clauses, `Sel` 3 clauses; the
whole k-ary plumbing 211 lines, at the low end of the probe's 150-250, with
`F11`-`F14` and any permutation lemma entirely unused.**

**LC-G2-5. One abstract binary-relation interface, instantiated at a relation and
at its converse, yields both atom kinds from one recursion.** `module Coord (R)
(Rel) (R-in) (R-out)` gives the insertion family; `module Atoms` takes `R`, its
converse `Rc` (with `Rel` flipped) and the diagonal slice `D`, and builds `Bin`.
Two instantiations cover the whole object language: `(∈ˢ, Mem, Memᶜ, Slf)` and
`(≡ₕ, Diag, Diag, U)`, the second reusing `Diag` as its own converse by symmetry
and `U` as its own diagonal slice. **Measured: 169 lines of shared machinery
(`Coord` 83 + `Atoms` 86) covering 2 atom relations x every index pair, versus a
per-relation build that would have doubled it.**

**LC-G2-6 (process). The first-formulation discipline held, and the probe's
prediction that no wall would fire was correct.** I-4 first (every adequacy
statement is a Π/Σ over carriers with explicit truncation, no implicit inverted
through `⟨_⟩`), R-38 at birth (five sealed birth sites: `capOp`, `cupOp`,
`ranOp`, `Up`, plus the three `opaque unfolding` closure arms), R-35 (memberships
at small indices; the one fiber extraction is over the sealed `⟪ F6 x x ⟫`, never
over a `⋃`-representation), P-h (the whole engine runs over an abstract `InJ`,
`Jrud`, `U`; nothing concrete is in scope until the last 15 lines), I-2/I-3
(every signature-level hProp wrapped in `⟨_⟩`, every `opaque` binding ascribed),
C-11 (module bodies indented deeper than their headers). **Result: ten
incremental checks, every one green on first submission except two scope-level
fixes (`Σ≡Prop` lives in `Cubical.Data.Sigma`, and `_^_` is a `FOL.Semantics`
name, so environments are written `Vec SM (suc n)`), no formulation retry, no
deletion-bisect, no wall.** The mandated-first-formulation protocol is now
measured on a 1,285-line chapter, not just on a probe.

## 7. Surprises

1. **`ι c .fst` is `⟪ U ⟫↪ c` definitionally**, as `L.Definability`'s prose
   claims, so the parameter atoms need no bridging path at all. Tested by writing
   the clauses with `refl`-level reuse; all eight atom clauses went through.
2. **`Fin` is `Cubical.Data.FinData`'s inductive family**, so `Fin (suc n)` splits
   as `zero`/`suc` and `Fin 1` needs only the `zero` clause. The coordinate
   recursions are total with no absurd patterns.
3. **The `mutual` block wants signatures first, clauses contiguous** (the probe's
   surprise 1 again). Two signatures, then twelve clauses of `adeq-mem`, then
   twelve of `adeq-set`; the termination checker accepts it without help because
   every clause descends on the formula.
4. **`⟨ ⊥ ⟩` is `⊥*`, not `⊥`.** The `⊥̇` clause of `adeq-set` needs `Empty.rec*`;
   `Empty.rec` does not apply. (Sibling of the probe's LC-2 on the `⊓` carrier.)

## 8. Files

- **`src/L/Rud/SatSets.lagda.md`** (new, 1,654 lines / 1,285 code lines). Prose
  en + zh, glossary-clean, prose-lint clean, `lint-agda` clean.
- Nothing else was created or edited. `Everything.lagda.md` was not touched, so
  the chapter is not yet on the `make check` gate; adding it is a one-line
  assembly decision for the owner.
