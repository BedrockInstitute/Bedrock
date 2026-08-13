# LJ-1.3 report: the Skolem hull

Status: COMPLETE. The chapter typechecks. No commit was made.

## 1. WHAT LANDED

The deliverable is `src/L/Hull.lagda.md`. The module `L.Hull` (line 10) takes
the universe and the excluded middle as parameters.

`AtStage` (line 57) fixes the stage `α` and its ordinal witness. `SL` (line 64)
is the stage's inner world. `wL` (line 67) is the delivered well-order at the
stage.

`AtM` (line 70) fixes a transitive set carrier inside the stage. `Elementary`
(line 80) and `TarskiVaught` (line 84) are the two notions. `elem→TV` (line
104) and `TV→elem` (line 110) prove the two directions. `TV-thm` (line 183)
packages the equivalence.

`Hull` (line 190) fixes the parameter set `X` inside the stage. `SatAt` (line
206) is the satisfaction at the stage's inner world. `Witnessed` (line 212) and
`Witnessed-small` (line 215) are the two existence shapes. `leastSearch` (line
235) is the sealed least-witness search. `leastWit` (line 246) and
`leastWit-spec` (line 249) are the search and its `IsLeast` reading. `Hull`
(line 263) is the sett over formula-and-small-witness pairs. `Hull⊆L` (line
266) proves the hull lies in the stage. `hull-member` (line 275) reads a hull
member back as a least-witness value. `leastWit-in-Hull` (line 280) places
every least witness in the hull. `X⊆M` (line 314) proves the hull contains
`X`. `hull-closed` (line 317) proves the Tarski-Vaught criterion at the
parameter source.

`OrderAt` (line 341) is the order atom. `ordL` (line 343) is the order element.
`ordL-fill` (line 346) and `ordL-rep` (line 350) are its two-way adequacy.
`φ<` (line 354) is the order membership formula. `Δ₀-φbody` (line 360) and
`Σ₁-φ<` (line 364) are the Levy certificate. `φ<-fill` (line 367) and
`φ<-rep` (line 377) are the formula's two-way adequacy. `φ<-irr` (line 402)
and `φ<-trans` (line 406) are the order-law consequences. `OrderAtom` (line
419) instantiates the atom at the delivered `Bound.orderL`. `OrderAtStage`
(line 426) instantiates it at the hull's own stage.

## 2. PORT OR FRESH WRITE

Port. The archive is `archive/rud-route/src/L/Hull.lagda.md` at 241 in-fence
lines. The port price is the archive code with re-pointed imports. The fresh
write price is the same content re-derived at 280 to 390 lines. The port is
cheaper, because the content is verified and generic. A fresh write spends the
same lines and adds authoring risk.

The adaptation points were small. `_^_` now comes from a concrete `SemV`
instance, because `FOL.Semantics` is module-parameterized. `V.Presentation` is
restored, so `member` and `fiber` work as the archive used them. I chose
`V.Presentation` over a direct `∈-asFiber` use, because it matches the
archive's shape and it rides `∈-asFiber` internally. Nothing else changed in
the port.

## 3. GENERIC OR FIXED

Everything stays generic. The stage `α` and the parameter set `X` are module
parameters (P-h). The stage stays an atom to the elaborator (P-l). The one
fixed atom is the order membership `pr x y ∈̇ con orderL` at the delivered
`Bound.orderL`, with its adequacy from `orderL-fill` and `orderL-rep`. The
atom is one generic module `OrderAt` at an ordinal. The two instances fix only
the ordinal: `OrderAtom` at the bounding ordinal and `OrderAtStage` at the
hull's own stage. I fixed nothing else.

## 4. THE TARSKI-VAUGHT EQUIVALENCE

True at the generality used. `TV-thm` holds at any transitive set carrier
inside a stage. The proof is one induction over the full syntax. The universal
case consumes the excluded middle. The bounded cases consume the carrier's
transitivity. The typecheck is the check.

The hull's criterion instance is `hull-closed`. It holds because the
least-witness search produces an `IsLeast` witness. That witness lies in the
hull by construction and satisfies the matrix by the `IsLeast` first
component. The typecheck is the check.

The recorded residue "the full elementary reading at parameters from the
hull" is not delivered. The hull is not transitive in general, so
`AtM Hull` does not apply as delivered. The leastness encoding needs the order
element as a stage member. That face is not delivered. It is priced in section
6.

## 5. THE MEASUREMENT

The chapter has 343 non-blank in-fence lines. I measured with the ledger
counting algorithm on the working tree. The ledger tool reads HEAD, and the
chapter is not committed.

The typecheck returned exit code 0. I ran one process under
`GHCRTS="-A64m -I0 -M8g"`. The dependency interfaces were cached. The module's
own elaboration was cold. The wall time was 2.31 to 2.43 seconds over three
runs. The median is about 2.4 seconds.

The ratio is 2.4 divided by 343, about 0.00700 seconds per line. The tree
baseline is 0.007693 (`dev/ledger.toml` [ratio]). The chapter sits at 0.91
times the baseline, inside the DD24 tolerance of 1.15.

The target band was 340 to 540 lines. The delivered 343 sits inside the band.
The band's basis was the archive (241) plus the W3 residue (100 to 300). The
residue closes at about 80 in-fence lines, because the order element and the
pair reader are delivered.

`lint-prose.py --check` and `lint-agda.py` both pass on the file. `make check`
was not run, per the brief.

## 6. WHAT THE CONDENSATION BLOCK WILL NEED FROM YOU

`TV-thm` gives elementarity from the criterion at any transitive carrier.
`hull-closed` gives the criterion at the hull's parameter source. `Hull⊆L` and
`hull-member` give the hull's stage membership and its least-witness reading.
`leastWit-spec` gives the leastness of every hull value. `OrderAtStage` gives
the order atom at the hull's stage, with `Σ₁-φ<` for the transfers.

Three pieces remain standing.

First, the order element's stage membership. The condensation block needs
`⟨ fst (relL β ...) ∈ˢ Lset γ ⟩` for the right stages `β` and `γ`. The
delivered tree has no such lemma. Price it at 30 to 80 lines, riding
`pr∈Lset-suc` and `LsetS`.

Second, the leastness encoding. "Every hull member is the unique witness of a
formula with parameters from `X`" needs the pair reader at the hull's
parameter domain and the order element as a constant. Price it at 80 to 150
lines, including the carrier transfer between `Small.⊨ᵐ` and the ambient
reading.

Third, the two Devlin 5.3 consequences. The full elementary reading at hull
parameters and the smallestness clause both ride the encoding. Price them at
100 to 200 lines together. They were left standing in the archive and remain
standing here.

## 7. ARCHIVE USED

`archive/rud-route/src/L/Hull.lagda.md`, 241 in-fence lines. Took: the
`Elementary` and `TarskiVaught` notions, the `TV-thm` induction, the
least-witness hull shape, `X⊆M`, and `hull-closed`, code verbatim with
re-pointed imports. Took the design note at lines 5 to 9: the hull must ride
the meta well-order, never reflection. Rejected: the residue as left standing.
This block closes the order atom; the two consequences stay standing.

`_build/lj-1.1-recon.md`. Took: block 1 at section 4, the one-atom pricing at
section 4, and the archive verdict at section 8. The recon priced the residue
at 100 to 300 lines; this tree closes it at about 80.

`_build/lj-1.4-report.md`. Took: the sibling's port method and its measurement
convention. The collapse ported at 181 archived lines to 239 delivered.

`src/V/Collapse.lagda.md`. Took: the idiom. No prose under DD23, opaque seals
with `-- perf:` markers, and module-parameterized carriers.

`dev/STYLE-agda.md` and `dev/STYLE-i18n.md`. Took: the marker grammar, the
import discipline, and the perf marker rule. The chapter has no prose, so it
has no language markers.

`dev/LESSONS.md` through `scripts/rules.py --for build`. Took: P-h, P-l, P-m,
R-36, R-40, C-12, C-22, D-10, and I-5.

## 8. WHAT I AM NOT SURE OF

1. The wall time varies from 2.31 to 3.43 seconds across runs. The median is
   about 2.37. A quiet-machine audit should re-measure.
2. The rep direction of the order atom is truncated. The exact rep needs
   propositionality of the delivered order relation, which the tree does not
   package. A consumer that needs exact rep from a formula satisfaction should
   price the `isProp` proof in the next block.
3. The two instances of the atom duplicate nothing, but they instantiate the
   same module at two ordinals. If the condensation block needs a third
   instance, the generic module is the single source.
4. The three standing pieces in section 6 are survey prices. The order
   element's stage membership may be cheaper or more expensive than the band.
   A probe in the next block should settle it before the encoding is priced.
5. The chapter is not in `Everything.lagda.md`. The orchestrator wires it.
   Until then, the tree index does not see it.
