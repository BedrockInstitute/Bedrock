# review-of-picommute-D: a STATED NO-GO, and a GO beside it

## HEAD
head_slot: coder
machine: shared
agda_tier: wide
task: LJ-1.652
obligation: agents/tasks/LJ-1-652/Probe652.agda::picommute-D-from-elem
verdict: **NO-GO at the brief's hypothesis list, and the reason is
measured. ELEMENTARITY DOES REACH `𝒟ₒ`: the transfer is built, green and
generic. What it does not reach is the HULL'S CLOSURE under `𝒟ₒ`, and
that closure is the one thing left. Clause (iii)'s `Commute` closes
OUTRIGHT from the same proof, because `Commute` carries its side
condition inside its own type and this obligation carries none.**

The obligation term is NOT written. The witness meter reads
`1 UNRESOLVED of 1, 3.07 s, probe_red=False`
(`agents/tasks/LJ-1-652/runs/meter-obligation.out:2`). The probe is green
and carries no hole (`runs/p-final.out:2`, `EXIT=0`). Nineteen other
delivered names meter `0 UNRESOLVED of 19`
(`runs/meter-names.out:20`).

**THIS IS NOT A REFUTATION OF `PiCommuteD`.** I did not build a term of
its negation and I do not claim one exists. The statement is true about
the real hull. What is measured is that the brief's three hypotheses do
not produce it, that exactly one more is needed, and what that one is.

---

## 1. WHAT ELEMENTARITY BUYS, AND IT IS THE WHOLE CHAIN

`[LJ-1.489]` stopped with "The two sides cannot agree without
elementarity" (`agents/tasks/LJ-1-489/lj-1.489-report.md:139-140`). The
brief's premise 2 is right: the tree has elementarity and that task did
not use it. This task uses it, and the chain it opens is three steps and
is green.

`Carry.push` (`Probe652.agda:185-192`) carries ambient truth at hull
members to ambient truth at their collapse values, for EVERY Δ₀
parameter-free formula at EVERY arity:

- `atM` (`:171-183`) goes DOWN INTO the hull by `elem`. The hull is not
  transitive (`agents/tasks/LJ-1-160/lj-1.160-report.md:249`), so Δ₀
  absoluteness is unavailable at this step and elementarity is exactly
  what replaces it.
- `iso-inv` (`src/L/BoundedSubset.lagda.md:195-196`) goes ACROSS, along
  the collapse. Its own side condition `isExt M` is NOT a hypothesis
  here: `hullExt` (`src/L/BoundedSubset.lagda.md:1340`) is green in the
  tree, and `Mext` (`Probe652.agda:152-153`) is that term.
- `atπ` (`:166-168`) comes OUT by Δ₀ absoluteness, because the
  collapse's range IS transitive (`πX-trans`,
  `src/V/Collapse.lagda.md:89`).

`AtTrans.read` (`:118-124`) is the absoluteness step written ONCE at a
generic transitive carrier (W2) and instantiated at the stage and at the
collapse.

## 2. THE RESIDUE, PRINTED BY AGDA AND NOT ARGUED

`Op.commute₂` (`Probe652.agda:206-211`) is the obligation for a generic
operation `F`, and it takes ONE side condition: `⟨ F y ∈ˢ M ⟩`.

`runs/RESIDUE.agda.txt` states the brief's obligation at the brief's own
hypothesis list and feeds `commute₂` the wrong witness on purpose. Agda
prints the type it wanted (`runs/residue-1.out:4`):

```
when checking that the expression y∈M has type ⟨ 𝒟ₒ y ∈ˢ F.HS.M ⟩
```

`runs/FLOOR.agda.txt` is the same file with a hole in that position:
exit 42 at the one designed hole (`runs/floor-1.out:2`), 4.82 s, peak
1,004,257,280 bytes against the 2,147,483,648-byte cap.

So the residue is `DeeInHull` (`Probe652.agda:280-281`):

```
DeeInHull = (y : S) → ⟨ y ∈ˢ HS.M ⟩ → ⟨ 𝒟ₒ y ∈ˢ HS.M ⟩
```

and `picommute-D-from-hull` (`:283-284`) is the obligation from it.

## 3. WHY CLAUSE (iii)'s `Commute` CLOSES AND THIS ONE DOES NOT

The difference is not the mathematics. It is the two TYPES.

`Commute` (`Probe652.agda:249-253`), which is `[LJ-1.641]`'s type
(`agents/tasks/LJ-1-641/Probe641.agda:69-73`), carries
`(Lδ∈M : ⟨ Lset δ ∈ˢ HS.M ⟩)` as its own hypothesis. That hypothesis IS
`commute₂`'s side condition at `F := Lset`. So the residue is paid
inside the statement and nothing is owed:

- `commute-from-lset-formula` (`:255-257`) is `Commute` from
  elementarity and `lset-formula` alone. The `IsOrd (HS.C.π δ)` argument
  is never read.
- `commute-641` (`:305-306`) checks that claim against `[LJ-1.641]`'s
  OWN module rather than against my copy of its lines, so the type
  identity is decided by Agda.

`PiCommuteD` (`:273-275`), which is `[LJ-1.489]`'s type
(`agents/tasks/LJ-1-489/Probe489.agda:139-141`), is stated at a GENERAL
hull member and carries no side condition at all. Nothing inside it pays
`commute₂`'s one.

**So the brief's premise 4 is half right.** `[LJ-1.648]` measured that
`DefFwd` and `DefBwd` are one statement and that statement is
`[LJ-1.489]`'s. Section 3 shows that the half of it which clause (iii)
actually consumes is not `[LJ-1.489]`'s general statement but `Commute`,
and `Commute` is now closed.

## 4. D-10, AND THE RISK IS IN THE HYPOTHESIS, NOT IN THE TARGET

`Matrix₂` (`Probe652.agda:75-85`) is the brief's reading of
`[LJ-1.651]`: a two-slot Σ₀ matrix whose ambient reading holds exactly
of `(F p , p)`. **The literature says that object does not exist.**
`dev/literature/devlin-II5.md:95`:

```
> By 2.7 there is a Σ₀ formula Φ(z, v, γ) of LST such that
```

and `:96`:

```
> (a) ∀v∀γ [v = L_γ ↔ ∃z Φ(z, v, γ)]
```

The Σ₀ form has a WITNESS slot `z`, and the graph is `∃z Φ`, which is
Σ₁ and not Δ₀. A two-slot Δ₀ matrix for the graph would make the graph
Δ₀, which contradicts (a) being the best the literature offers.

So every consumer in this file is built TWICE, once at each shape, and
nothing here depends on which one `[LJ-1.651]` can deliver:

- `Witnessed` (`:87-92`) is Devlin's shape: three slots, Δ₀, with the
  soundness half outright and the witness left to the consumer.
- `commute₃` (`:215-224`) is `commute₂` at that shape.
- `commute-from-witnessed` (`:266-268`) and `picommute-D-from-witness`
  (`:292-293`) are the two instances.

At Devlin's shape the residue grows by exactly one item, the WITNESS
inside the hull (`LsetGrounded` `:260-264`, `DeeGrounded` `:286-290`),
and that is Devlin's own step: "the Σ₁ statement ... is transferred from
L_α to X ... and along the collapse to M"
(`dev/literature/devlin-II5.md:102-104`).

## 5. THE RESIDUE IS A SEARCH, AND `hull-closed` CAN ANSWER IT

`[LJ-1.648]`'s language argument
(`agents/tasks/LJ-1-648/review-of-commute-from-keystone.md`, part 3)
killed `DefBwd` because its condition names `HS.C.π y ≡ z` and `π` is
not a term of the hull's language. **`DeeInHull` names no `π` at all.**
It is a hull-member search whose condition names only `𝒟ₒ` and a hull
member, which is the shape `hull-closed` (`src/L/Hull.lagda.md:415`) was
built to answer.

It is also the SAME SHAPE as the keystone. `[LJ-1.648]` measured the
keystone to be exactly `HullClosedLsetOrd`
(`agents/tasks/LJ-1-648/Probe648.agda:203-213`), which is
`(y : S) → ⟨ y ∈ˢ M ⟩ → IsOrd y → ⟨ Lset y ∈ˢ M ⟩`. `DeeInHull` is that
statement with `Lset` replaced by `𝒟ₒ` and the ordinality dropped.

## 6. WHAT I DID NOT DO

- I did not inhabit `picommute-D-from-elem`.
- I did not inhabit `DeeInHull`, `DeeGrounded` or `LsetGrounded`.
- I did not inhabit `Matrix₂` or `Witnessed` at either operation. The
  brief forbids building either hypothesis.
- I did not refute `PiCommuteD`.
- I did not edit `src/`. I did not commit and did not push.
- I did not set `GHCRTS`. I did not start a second Agda process.
- I did not postulate and I did not leave a hole in `Probe652.agda`.
