# review-of-hoodexists: the obligation is not reachable AS PINNED

**THE STOP.** `hoodexists-at-levelhood0` is not in `Probe662.agda`. The brief
names `[LJ-1.653]`'s `HoodExistsP φ₀` "at `φ₀` pinned to the chapter's
`LevelHood0` shape". The pinning is DONE and it is green
(`Probe662.agda:122`, `runs/meter-names.out`, `0 UNRESOLVED of 21`). The
obligation is not, and the reason is NOT the transport the brief expected.

The brief's NO-GO clause reads: "**NO-GO** earns why the witness does not
survive the move into the collapse image". **The witness survives that move.**
`hoodExistsP-from-cover` (`Probe662.agda:215`) carries it from the stage to
the collapse and is green. What is missing sits one layer EARLIER, at the
stage, and it is the chapter's own priced residue.

## 1. WHAT THE OBLIGATION REDUCES TO, EXACTLY

`Probe662.agda:294` and `:331`: the whole existential half follows from

    SatAtLevel φ₀   (Probe662.agda:284)
    ElemDown        (Probe662.agda:182)

and nothing else. `SatAtLevel φ₀` says: at every ordinal `γ` of the stage,
the stage member `Lset γ` satisfies the chapter's own level-hood matrix at
the pair `Lset γ ∷ γ ∷ []`. That is the ADEQUACY of the chapter's formula,
read at the stage.

`ElemDown` is not the blocker. The chapter discharges it at its own consumer
(`src/L/BoundedSubset.lagda.md:1667-1668`, `elem-down = HEDC.elem-down`), and
`[LJ-1.609]` built the code selection it needs
(`agents/tasks/LJ-1-609/Probe609.agda:345`).

## 2. THE ADEQUACY IS NOT DELIVERED, AND FOUR GREPS SAY SO

1. **`LevelHood0` HAS NO CONSUMER.** `grep -rn "LevelHood" src/` outside
   `src/L/BoundedSubset.lagda.md` returns **0** lines. Inside that file the
   module is defined (`src/L/BoundedSubset.lagda.md:840`) and never used.
   The chapter says the same in words at `src/L/BoundedSubset.lagda.md:901-902`:
   "the level-hood instantiation at the hull is the priced residue".
2. **THE BOUNDED GRAPH IS NEVER TIED TO THE UNBOUNDED ONE.** `graphBndAt`
   occurs at exactly six lines in `src/`: its definition and certificate
   (`src/L/Condensation.lagda.md:2492-2496`) and the chapter's two uses
   (`src/L/BoundedSubset.lagda.md:111`, `:115`). **No theorem in `src/`
   relates it to `LsetGraphAt`.**
3. **THE DELIVERED ADEQUACY IS FOR THE UNBOUNDED GRAPH AT THE CLASS
   CARRIER.** `Lset-only` (`src/L/Hierarchy.lagda.md:334`) and
   `Lset-defines` (`src/L/Hierarchy.lagda.md:646`), ridden at
   `src/L/Condensation.lagda.md:423-431`. Both read `⟨ γ ⊨ LsetGraphAt w b ⟩`
   at `𝒮ʟ`. `SatAtLevel` reads at `Lset lam`. A Σ₁ statement moves UP from a
   stage to `L` and not down, so this is not the same fact.
4. **THE LEAF THAT WOULD BRIDGE THEM NEEDS ONE `KFacts`.** `LeafAgree`
   (`src/L/Condensation.lagda.md:7224`) takes a `KFacts` record
   (`src/L/Condensation.lagda.md:6079`) and the tree carries exactly ONE
   value of it, `KValue.facts` (`src/L/Condensation.lagda.md:7411`).

## 3. AND AT `LevelHood0`'s OWN ARITY THE BRIDGE CANNOT BE RIDDEN

This is a counting fact and it is the finding to act on.

`KValue.facts` sits at `Kenv : S ^ 14` (`src/L/Condensation.lagda.md:7389`):
the carrier, the bound, and **twelve numeral columns**. Each `tagEq` field
asks that its column hold `numeralL k`.

`LevelHood0` is `LevelHood {0}` (`src/L/BoundedSubset.lagda.md:844`). Its
twenty-eight tag parameters are typed `Fin 5` and `Fin 7`
(`src/L/BoundedSubset.lagda.md:841-842`), and the matrix's own environment
is five slots, `w ∷ u ∷ v ∷ γ ∷ K ∷ []`
(`src/L/BoundedSubset.lagda.md:68-72`, the matrix at `:108-111`). All five
are committed by the shape itself: the bounded witness, the unused slot, the
value, the ordinal index, and the bound.

**Twelve numeral columns cannot be chosen from five committed slots.** So no
choice of `LevelHood0`'s parameters can carry a `KFacts`, and the leaf
agreement cannot be ridden at `LevelHood0` for ANY choice.

## 4. THE TENSION THE NEXT BRIEF MUST PRICE

Two demands pull opposite ways, and `LevelHood0` resolves the tension in the
direction that loses the adequacy.

| demand | source | what it forces |
|---|---|---|
| a parameter-free formula of arity **2** | `HoodExistsP` (`agents/tasks/LJ-1-653/Probe653.agda:283`) | no constants, two free slots |
| **fourteen** pinned environment columns | `KFacts` (`src/L/Condensation.lagda.md:6079`), the only value at `S ^ 14` (`:7389`) | fourteen slots held at named values |

`LevelHood {n}` for `n ≥ 14` has room for the columns, and its matrix then
has arity `4 + n`. Closing the surplus slots by `∃̇` reaches arity 2 again,
and **that is where the tag equations are lost**: a bound slot is no longer
known to hold `numeralL k`. A brief that pins the level-hood must say which
side it pays.

## 5. D-10: THE TARGET'S TRUTH, PRICED BEFORE ITS PROOF

The obligation as pinned is a claim about EVERY choice of the twenty-eight
tag indices, because `LevelHood0` supplies no choice of its own. The indices
range over the five and seven slots of section 3, none of which holds a
numeral, so the tree gives no reason to believe the resulting matrix at any
choice.

**I did not refute it, and that is a measurement rather than a shrug.**
A refutation must decide a membership of `M = H.T.Hull`, which is a truncated
existence over codes that nothing in the tree computes
(`agents/tasks/LJ-1-653/lj-1.653-report.md:250-259`). So the honest reading
is: NOT proved, NOT refuted, and the pin is wrong rather than the statement.

## 6. WHAT IS GREEN AND SHOULD BE TAKEN AS DELIVERED

- `Pinned.φ₀` (`Probe662.agda:122`): the chapter's matrix, re-slotted to the
  pair `v ∷ γ ∷ []` and ERASED to the parameter-free alphabet, with
  `count-hood2 = refl` (`Probe662.agda:119`) and `φ₀-inv`
  (`Probe662.agda:127`). **The alphabet gap `[LJ-1.657]` measured FATAL does
  not arise at the chapter's own shape.**
- `Bridge.pro` (`Probe662.agda:179`): premise 4's staleness cured by import.
- `Bridge.hoodExistsP-from-cover` (`Probe662.agda:215`): the transport the
  brief expected to be the risk. It is not the risk.
- `Bridge.level-in-stage` (`Probe662.agda:268`): premise 3, measured at the
  VALUE slot and not only at the ordinal.
- `AtLevelHood0.levelin-at-levelhood0` (`Probe662.agda:338`): premise 1
  composed. With a sibling's `HoodSoundP` the pair closes `levelIn`.

The one fact still owed is `SatAtLevel` (`Probe662.agda:284`).
