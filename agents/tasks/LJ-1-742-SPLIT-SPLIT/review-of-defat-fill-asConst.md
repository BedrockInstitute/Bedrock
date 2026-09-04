# Review of `defat-fill-asConst` (LJ-1.742-SPLIT-SPLIT)

**Verdict: NOT DISCHARGED. PARTIAL: PARK.**

`defat-fill-asConst` is not inhabited. The probe is delivered as
`Probe742SplitSplit.agda.txt` (1948 lines); its checker frontier at return
(runs/final-frontier.out, rc 42, 638 s at the pane caliber) is:

1. `defat-fill-asConst` declared at the file's top level (line 238), body
   pending.
2. Two deferred level-metas at the Fill's `astg` transport and the
   `Δ₀-pairsIn` leaf (they resolve once the twelve-clause instantiations
   land).

## What the two open conjuncts need

`remaining-goal`'s conjunct 2 (`satGraphAt`) needs the bounded twelve-clause
walk at the graph environment `gEnv = A ∷ satTable A phi ∷ slot A phi ∷ δG`.
That walk is replayed, not rewritten: the meta inversions are Sound's own
`Atom`/`Un`/`UnSucc`/`Bin`/`BinSucc`/`Const` frames (imported, public), the
staging descent is `EnvSupply.Fact` (`valK`, `tmValK`, `valV`, `valW`,
`subKSucc-gen`, `ConsKClosed` with `FiniteSup.finSetK`) plus
`Key.FiniteSup`, and the bounded ambient moves are this dispatch's
`Ambientᴬ` (complete in the file). Conjunct 3 (`DefinesAtᴬ`) is a
replay of Powerset's `into`/`back` under `extAtᴬ`.

## What this dispatch built (all in the .agda.txt)

- The frozen prefix repairs: the Section 13 substitution direction
  (`sucStg`), the clause frames' `Stg` handover and 5-deep environments,
  `ClOf.closedOfᴬ` generalized to an arbitrary slot index, `ShW.isTmAtᴬ-in`
  stated as slot-membership plus the slot's stagedness, `Walk`'s conjunct 1
  moved to the `z`-carrying environment.
- The bounded ambient moves `Ambientᴬ` (`recᴬ`, `intoᴬ`, `outofᴬ`,
  `asEnvᴬ`): the Recover replay under the bounded reading, with every svAt /
  domAt / valuesIn instance at staged sets and `pairsInAt` joined by the
  Δ₀-transport on a built certificate.
- The pointwise extractions `svAtᴬ-out`, `domAtᴬ-in`, `valuesInAtᴬ-out`,
  `ovᴬ-in`, the `tmValAtᴬ` var/con intros and outs, `envStg`, and the
  staging helpers.

## What the next brief must fund

The five clause-family bodies (atom ×2, prop ×2, top/bot, neg, quant ×2,
bnd ×2) written against the now-complete frames, then the graph assembly and
`DefinesAtᴬ`. Estimated remainder: 300 to 400 lines. Nothing in the prefix
needs re-funding: `Ambientᴬ` is the last reusable piece that was missing.
