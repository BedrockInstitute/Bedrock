# NO-GO: `beta-into-alpha-coded`

The obligation
`agents/tasks/LJ-1-580/Probe580.agda::beta-into-alpha-coded` is NOT in the
probe. This file states why, names the leg that blocks it, and names the one
residue that remains.

**THE PROBE IS GREEN, EXIT 0** (`agents/tasks/LJ-1-580/runs/final-1.out`).
Nothing is postulated, there is no hole, and nothing landed in `src/`.

## THE OBLIGATION'S TYPE IS WRITTEN AND IT IS NOT INHABITED

`BetaIntoAlphaCoded` (`agents/tasks/LJ-1-580/Probe580.agda:292`) is
`gap-is-a-code`'s antecedent (`agents/tasks/LJ-1-577/Probe577.agda:368-369`) at
the pair the brief names. `gap-is-a-code` is IMPORTED and not restated
(`agents/tasks/LJ-1-580/Probe580.agda:34`), so the interface cannot drift.

## HALF OF IT IS DELIVERED, AND THAT HALF IS LEG 1

`β↪α` (`src/L/BoundedSubset.lagda.md:1578-1582`) is exactly two legs, and the
elaborator says so: `two-legs` (`agents/tasks/LJ-1-580/Probe580.agda:192`) is
`refl`.

**LEG 1 IS CODED.** `leg1-coded : InjCode Leg1.G βᴸ πXᴸ`
(`agents/tasks/LJ-1-580/Probe580.agda:232`). Leg 1 is the stage-cardinality
bound at β (`src/L/BoundedSubset.lagda.md:1581`, body
`src/L/StageCardinal.lagda.md:209-211`), which IS the inclusion β ⊆ Lset β
(`src/L/StageCardinal.lagda.md:193-195`) moved along `ext`
(`src/L/BoundedSubset.lagda.md:1568`). The tree codes any inclusion between two
L-elements: `InclGraph` (`src/L/InjChain.lagda.md:575-598`) over `inclFo`
(`:445-446`), through `hasSeparationL`.

Two level-hood facts were needed and one of them is new here:
`ord-isL` (`Probe580.agda:95`) and `Lset-isL` (`Probe580.agda:104`). **Every
STAGE of the tower is an L-element**, from `defSet ⊤̇ ≡ A`
(`src/L/Definability.lagda.md:178`) and `Lset-in`
(`src/L/Constructible.lagda.md:319`). `grep -rn "isL (Lset" src/` returns
nothing, so that shape was not in the tree.

## LEG 2 IS THE BLOCK, AND IT IS NOT BUILT FROM L-DATA

**W3 SETTLED WHAT THE LEG DELIVERS.** `CodeSelect`
(`src/L/BoundedSubset.lagda.md:1099-1140`), applied at its own parameters,
delivers `CSel.leg2 : ⟪ M ⟫ ↪ ⟪ α ⟫` and nothing else
(`agents/tasks/LJ-1-580/Probe580.agda:73-74`, `runs/w3-1.out`, GREEN, 3.04 s).
It is a bare `_↪_`: a function and an injectivity proof, with no `Formula` in
the type and no `InjCode`.

**AND ITS VALUE IS COMPUTED FROM `absorbs`, WHICH IS AN UNCODED AMBIENT
INJECTION.** `count-applies-absorbs` (`agents/tasks/LJ-1-580/Probe580.agda:148`)
is `refl`:

    CC.count (base m) ≡ B.pair (B.numeral 0)
                          (fst (stage-card-upper α ordα _ α∉ω) (fst absorbs m))

`CSel`'s counting parameter is `CC.count` (`src/L/BoundedSubset.lagda.md
:1518-1520`), `CC` is `CodeCount code-inj` (`:1515`), and `code-inj` is
`comp-inj absorbs (stage-card-upper ...)` (`:1512-1513`). `absorbs` is the
TWELFTH parameter of `Devlin55.BoundedSubsetAt`
(`src/L/BoundedSubset.lagda.md:1392`), a bare `_↪_` with no `Formula`.

**NO SITE IN `src/` SUPPLIES IT.** `grep -rn "absorbs" src/` outside
`src/L/BoundedSubset.lagda.md` gives `src/L/StageBound.lagda.md:69`, `:76`,
`:97`, `:116`: a parameter passed on, never applied and never built.
`src/L/Absorption.lagda.md:635` is a DIFFERENT shape,
`⟪ sucV (fst γ) ⟫ ↪ ⟪ fst γ ⟫`, and it does not fit this slot.

**SO `[LJ-1.577]` IS WRONG ON ITS OWN PREMISE 5, AND THE BRIEF ORDERED THIS
SAID.** `agents/tasks/LJ-1-577/review-of-bounded-subset-internal.md:79-81`
reads "`β↪α` is the composite of a stage-cardinality bound and a code selection
over the hull's term algebra, and both legs are built from L-data." **Leg 1 is.
Leg 2 is not.** Leg 2's value is a function of `absorbs`, and `absorbs` is
ambient data handed in from outside the module. Coding it is
`[LJ-1.533]`'s wall (`agents/tasks/LJ-1-533/lj-1.533-report.md:42-43`), at a
site `[LJ-1.577]` said was the opposite case.

## WHAT REMAINS IS ONE STATEMENT

With leg 1 coded and `Comp` (`src/L/InjChain.lagda.md:314-433`) in the tree, the
whole obligation is leg 2's code and nothing else:

- `leg2-coded→at-β : InjL πXᴸ αᴸ → InjL βᴸ αᴸ`
  (`agents/tasks/LJ-1-580/Probe580.agda:245`);
- `at-β→at-κ` (`:263`) carries it to the pair the step actually spends at,
  which is `(κᴸ , αᴸ)` and not `(βᴸ , αᴸ)`;
- `obligation-from-leg2 : Leg2Coded → BetaIntoAlphaCoded` (`:303`), which does
  not even read the ambient injection;
- `gap-closed : Leg2Coded → GapAtPair βᴸ αᴸ` (`:320`), through the IMPORTED
  `gap-is-a-code`.

`obligation-from-leg2` carries `Leg2Coded` to the left of its arrow, which the
obligation does not have. It is not the obligation and it is not offered as one.

**AND THE RESIDUE IS NOT ABOUT THE HULL. IT IS ABOUT A STAGE.**
`residue-is-a-stage-bound` (`agents/tasks/LJ-1-580/Probe580.agda:311`) proves

    Leg2Coded ≡ InjL (Lset β) α

because `ext` says the collapse IS `Lset β`. In words: **in L, the stage
`Lset β` injects into α.** That is Devlin 1.1(vii)'s size equation, internal, at
one pair (`dev/literature/devlin-II5.md:156`).

## WHY THAT RESIDUE HAS NO PRODUCER TODAY

`src/` has exactly TWO `InjCode` producers and both deliver the single shape
`InjCode F (sucʟ γ) γ`: `src/L/Absorption.lagda.md:611-614` and
`src/L/CodedShift.lagda.md:40`. Independently grepped at today's tree
(`grep -rn "InjCode" src/`). Neither is a stage bound.

`[LJ-1.568]` settled what such a producer needs. `Def`
(`agents/tasks/LJ-1-568/Probe568.agda:189-190`) is "some formula of the object
language describes `g` on the members of `a`", `def-restricted` (`:252-253`)
proves it sufficient, and `weakest` (`:377-381`) proves EVERY sufficient
hypothesis implies it. So the residue is a demand for one formula, at one pair,
and this task did not find it.

## WHAT WOULD REOPEN IT

An internal stage-cardinality bound: a formula, with parameters in L, that
describes an injection of `Lset β` into α. The tree has the AMBIENT one
(`stage-card-upper`, `src/L/BoundedSubset.lagda.md:1400-1402`, body
`src/L/StageCardinal.lagda.md`), and it has the general law that reading it as
a code is exactly `Def` (`agents/tasks/LJ-1-568/Probe568.agda:377-381`). It does
not have the formula.

**IT IS NOT A CODE FOR AN ARBITRARY AMBIENT INJECTION.** `Lset β` and α are both
L-elements, β is an ordinal, and the statement is a size fact about a stage.
That is a different question from `[LJ-1.533]`'s, and this file does not claim
it is refuted. What is measured here is that the ROUTE THROUGH `β↪α` cannot
deliver it, because that route computes through `absorbs`.
