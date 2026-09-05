# LJ-1.267 report: re-derive `[LJ-1.7]`'s residue

tier: pi (deepseek-subagent-mode), model `deepseek-v4-pro`. No Agda ran. No
slot held. No master, brief or report edited. No commit, no push. Written
incrementally (C-22). Every negative is MEASURED or INFERRED, in those words.

## 0. LEAD

**The seven parameters of `module Whole`, one word each.**

| parameter | status |
|---|---|
| `el` | **SUPPLIED** |
| `fwd` | **SUPPLIED** |
| `bwd` | **SUPPLIED** |
| `sl` | **BUILT** |
| `sc` | **BUILT** |
| `s₁` | **BUILT** |
| `amb` | **OPEN** |

**The residue is the SAME SIZE the record says: four obligations.** The
finding this task was sent for is the opposite of the feared one: `el`,
`fwd` and `bwd` are not unpriced obligations. They are delivered in `src/`
and the phase's record never said so. That closes a three-parameter hole in
the accounting and confirms, rather than grows, the four-item residue.

## 1. THE SEVEN PARAMETERS, WITH EVIDENCE

The object is `module Whole` at
`agents/tasks/LJ-1-178/ProbeLJ1178A.agda:489-493`. Its seven parameters build
`levelIn` and `cover` at `src/L/BoundedSubset.lagda.md:1555-1556`, which are
the real site's two open hypotheses (`theorem` at `:1621`).

### 1.1 `el : A.Elementary` (the hull's elementarity). SUPPLIED

**Type.** `src/L/Hull.lagda.md:174-176`:
`Elementary = (n : ℕ) (φ : Formula SM n) (δ : SM ^ n) → (δ ⊨ᵐ φ) ≡ (map inL δ AbsL.⊨ᵐ (mapFo inL φ))`.

**Term.** `src/L/BoundedSubset.lagda.md:759` (`elem : A.Elementary`) and
`:760` (`elem = A.TV-thm .snd tv`). `tv` is a proved Tarski-Vaught witness,
built from the delivered `H.hull-closed` (`:704-710`). It is not a relay.

**Instantiation audit.** The module that holds `elem` is
`HullElemDown (α ordα X X⊆L ∅∈α)` at `:667-668`, opened at the real site at
`:1543` with `lam ordλ UK.X UK.X⊆Lλ UK.∅∈λ`; its `WithCode` is opened at
`:1544` with the delivered `hedF hedF-spec` (`:1532-1541`). Every parameter of
the telescope has a delivered argument. So `HEDC.elem` is a discharged term.

**This is the first parameter the record never named.** `[LJ-1.225]`'s table
lists four hypotheses and omits it; `[LJ-1.251]` does the same. MEASURED, by
reading both reports.

### 1.2 `fwd : IsoFwd` and `bwd : IsoBwd` (the collapse satisfaction iso). SUPPLIED

**Types.** `ProbeLJ1178A.agda:370-377`. `IsoFwd` is the hull-to-image
direction, `IsoBwd` the image-to-hull direction, both over the collapse map
`g` (`:362-363`).

**Terms.** `src/L/BoundedSubset.lagda.md`:
- the generic iso at `:152-318` (`module IsoInv`): `iso-inv` at `:195-249`,
  `iso-inv-bwd` at `:250-318`, one induction over formula syntax each;
- the collapse instance at `:321-350` (`module CollapseIso`), wired at
  `:350` (`module I = IsoInv X PM p p∈ iso-fwd iso-bwd p-inj surj`);
- the site instance at `:770-780` (`module AtHullInstance`): `:774`
  (`module CIso = CollapseIso X Xext`) and `:780`
  (`transfer {n} φ δ = CIso.I.iso-inv n φ δ , CIso.I.iso-inv-bwd n φ δ`).

`transfer` is a pair whose two components are exactly `fwd` and `bwd`. The
`IsoInv` telescope (`M PM p p∈ iso-fwd iso-bwd p-inj surj`, `:152-160`) is
discharged at `:350` from the delivered `Collapse X`. MEASURED.

**These two were also never named.** The probe's own comment at
`ProbeLJ1178A.agda:481-482` says `fwd, bwd` are DELIVERED (`:195-318`), but no
report in the phase repeats it.

### 1.3 `sl : StageLevels`. BUILT

**Type.** `ProbeLJ1178A.agda:360-361`: the stage believes every ordinal has a
level.

**Term.** `ProbeLJ1237A.agda:191-201`, the body of `sl`. It is inside
`module Build (lh : (v b : SL) → IsOrd (fst b) → fst v ≡ Lset (fst b) → ⟨ (v ∷ b ∷ []) AbsL.⊨ᵐ embed φ₀ ⟩)`
at `:178-181`, and it applies `lh` at `:191`. So `sl` is a conditional term
over `lh`. `lh` is a bare parameter: `module StageLH` takes `φ₀` with no
hypothesis about it at `:127-129`. MEASURED.

`sl` also consumes `succα` (the successor closure of the stage, its own
parameter at `:190`). So the built term stands over `lh` AND `succα`.

### 1.4 `sc : StageCovered`. BUILT

**Type.** `ProbeLJ1178A.agda:405-406`: the stage believes every set lies in a
level below it.

**Term.** `ProbeLJ1237A.agda:205-246`, the body of `sc`, in the same
`module Build` over `lh` (applied at `:233`) and `succα` (at `:205`). Same
conditional shape. MEASURED.

### 1.5 `s₁ : Σ₁ Cr.φP`. BUILT

**Type.** `ProbeLJ1178A.agda:492`, with `Cr.φP = embed φ₀` at `:143-144`.

**Shape is delivered, the term is not.** The probe defines `mapΣ₁` (`:73-77`)
and `embed-Σ₁` (`:79-80`), so a `Σ₁ (embed φ₀)` follows from a `Σ₁ φ₀`. The
matrix's Δ₀ witness is delivered (`src/L/BoundedSubset.lagda.md:141-142`,
`Δ₀-levelHoodB`). What is not written in `src/` is the certificate `Σ₁ φ₀`
itself. The delivered certificate `Σ₁-levelHood` at
`src/L/BoundedSubset.lagda.md:145-146` is for `levelHoodΣ₁ = ∃̇ levelHoodB`
over `CS.S`, a different formula from the parameter-free `φ₀` (arity two over
`⊥*`). MEASURED.

So `s₁` is BUILT in shape and not SUPPLIED. `[LJ-1.225]` called this the
"2-line gap".

### 1.6 `amb : AmbientCross.AmbientRead P Ptr φ₀`. OPEN

**Type.** `ProbeLJ1178A.agda:190-192`: ambient believes `φP(v,b)` at an
ordinal `b` implies `v ≡ Lset b`. Devlin's clause (a) at the ambient carrier.

**The supply is conditional, and the condition is undischarged.**
`ProbeLJ1184B.agda:128-129` defines `amb P Ptr = A.clause-a fst φ₀ go`. It sits
inside `module AmbientStep` (`:101-113`), whose telescope carries
`(q : Graph {2} zero (suc zero) ≡ embed φ₀)` at `:112`. `go` spends `q` at
`:122` (`subst (λ ψ → ⟨ A.ambient γ ψ ⟩) (sym q) h`). `q` is an equation
between two independently quantified terms, so `refl` cannot close it
(C-45 shape). MEASURED.

**Instantiation audit.** Nothing instantiates `AmbientStep`.
`[LJ-1.243]` section 2.2 measured this by repository-wide search; the only
application, `ProbeLJ1184C.agda:83`, feeds `q` from its own telescope. So the
supply relays `q` and never discharges it. `amb` is OPEN.

## 2. DID THE RESIDUE SHRINK, HOLD OR GROW TODAY?

**IT HELD.**

The record (through `[LJ-1.225]` and `[LJ-1.251]`) counts four obligations:
`amb` OPEN, `sl` and `sc` BUILT over `lh`, `s₁` BUILT in shape. My
re-derivation confirms exactly those four, with the same statuses, and adds
that `el`, `fwd`, `bwd` are SUPPLIED.

Today's green work (`[LJ-1.254]` through `[LJ-1.263]`) moved step 6's 28
fields to reachable, landed the numeral premise and the three L-rows, and
supplied `finSetK`. None of it touches any of the seven parameters directly.
Step 6 is `lh`'s supply, and `[LJ-1.251]` measured 0 of the 28 supplied. The
`q` bridge under `amb` is untouched by step 6 work. So today bought
**reachability, not discharge**. MEASURED for the 0-of-28 and for the four
statuses; the claim that no seven-parameter changed is MEASURED by reading
each landing's report against the seven types.

## 3. DO `el`, `fwd` OR `bwd` OWE ANYTHING NOBODY HAS PRICED?

**NO.**

All three are delivered in `src/` and discharged. MEASURED, section 1.1 and
1.2. They are not unpriced obligations, so the abort branch "the residue is
larger" does not fire.

**One qualifier, and it is not a charge against them.** The three are the
NEW-route transports. The retired route worked at a transitive carrier `Sᴹ`
directly, so it needed no hull elementarity and no collapse satisfaction iso;
its condensation face names `CrossOut`, `HasLevels`, `Covered`, `SucClosed`
(`archive/src/2026-08-09-rud-route/L/Condensation.lagda.md:168-189`) and has
no `Elementary` or `IsoInv` obligation. The current route works at the hull
`X` and collapses it, so it pays `el`, `fwd`, `bwd` up front, and they are
already paid. SHAPE TAKEN from the archive, no figure. MEASURED for the
absence in the archived face.

## 4. DD4: THE AXIS FOR EACH PARAMETER

Two axes, per `[LJ-1.262]`: Devlin's Def-against-J (the twelve-row table), and
the port's L-against-ambient.

| parameter | Devlin II.5 row | Def-vs-J mark | L-vs-ambient side |
|---|---|---|---|
| `el` | C4 (transfer along Σ₁-elementarity) | **EITHER**, neither-tower carrier | L side (hull of `L_α`) |
| `fwd` | B / C4 (collapse, transfer along it) | **EITHER**, neither-tower carrier | neither (Mostowski collapse, general) |
| `bwd` | B / C4 | **EITHER** | neither |
| `sl` | C1 (level-hood formula, witness in carrier) | **PER-TOWER** | L side (stage fact at `L_α`) |
| `sc` | C1 (the coverage half) | **PER-TOWER** | L side |
| `s₁` | C1 (the Σ₁-with-Σ₀-matrix certificate) | **PER-TOWER** | neither (syntactic, carrier-free) |
| `amb` | C1 (clause (a), ambient level-hood) | **PER-TOWER** | **ambient side** |

**Reading.** Four of the seven (`sl`, `sc`, `s₁`, `amb`) are one object,
Devlin's level-hood certificate (Step C, row C1). Three (`el`, `fwd`, `bwd`)
are shared either-tower machinery (rows B and C4). None sits on C2, C3, C5,
C6, D, E, F or G, and none has no row. The well-order (rows D and G) is not in
this chain.

**The axis split is now usable.** `amb` is the only parameter whose tower
status is on the L-against-ambient axis at the ambient end. `el`, `sl`, `sc`
are on the L end. `s₁` is carrier-free, so its PER-TOWER mark lives on the
Def-vs-J axis alone. `fwd` and `bwd` are general set theory, so the tower
question does not apply to them on either axis. This is the single labelling
the brief asked for.

## 5. EVERY NEGATIVE, CLASSIFIED

| negative | class |
|---|---|
| `el` is an unpriced obligation | **MEASURED FALSE.** `src/L/BoundedSubset.lagda.md:759-760` |
| `fwd`/`bwd` are unpriced obligations | **MEASURED FALSE.** `src/L/BoundedSubset.lagda.md:195-318`, `:780` |
| `el`, `fwd`, `bwd` were discussed in this phase's record | **MEASURED FALSE.** `[LJ-1.225]`'s four-row table and `[LJ-1.251]` name only `amb`, `sl`, `sc`, `s₁` |
| `amb` is supplied outright | **MEASURED FALSE.** `q` at `ProbeLJ1184B.agda:112`, undischarged |
| `sl` and `sc` are supplied | **MEASURED FALSE.** Both stand over `lh`, `ProbeLJ1237A.agda:178-181` |
| `s₁` is supplied in `src/` | **MEASURED FALSE.** `Σ₁-levelHood` is at `CS.S`; `Σ₁ φ₀` is not written |
| today's work discharged one of the seven | **MEASURED FALSE.** Step 6 content does not touch the seven |
| the residue is smaller than the record says | **MEASURED FALSE.** Four obligations, four statuses unchanged |
| the residue is larger than the record says | **MEASURED FALSE.** `el`, `fwd`, `bwd` are SUPPLIED |
| `[LJ-1.251]` says verbatim "`lh`'s supply IS step 6" | **MEASURED FALSE.** It says `sl`/`sc` stand over `lh` and separately prices step 6; the brief's sentence is the orchestrator's synthesis |

## 6. ARCHIVE USED (DD18)

One line read named per archived file.

- `agents/tasks/LJ-1-178/ProbeLJ1178A.agda`, read WHOLE, FIRST. **Line read
  `:489`**, `module Whole`, the object. Its section 6 comment, **line read
  `:481-482`**, "`el` ... DELIVERED (:759, :1544)" and "`fwd, bwd` ...
  DELIVERED (:195-:318)", the probe's own admission that the three are not
  hypotheses.
- `agents/tasks/LJ-1-178/lj-1.178-report.md`, read WHOLE. **Line read `:21`**,
  "Four hypotheses stay open", the origin of the four-item count that omits
  `el`, `fwd`, `bwd`.
- `agents/tasks/LJ-1-251/lj-1.251-report.md`, read WHOLE. **Line read `:165`**,
  "Step 6 re-prices at about 255 and is UNBUILT".
- `agents/tasks/LJ-1-243/lj-1.243-report.md`, read WHOLE. **Line read `:14`**,
  "`amb` was never supplied outright"; I took the `q` shape from section 2.2.
- `agents/tasks/LJ-1-237/ProbeLJ1237A.agda`, read WHOLE. **Line read `:191`**,
  `sl`'s body, and `:205`, `sc`'s body.
- `agents/tasks/LJ-1-184/ProbeLJ1184B.agda`, read `:100-160`. **Line read
  `:112`**, `(q : Graph {2} zero (suc zero) ≡ embed φ₀)`.
- `agents/tasks/LJ-1-184/ProbeLJ1184C.agda`, read `:80-95`. **Line read `:83`**,
  the only `AmbientStep` application, which feeds `q` from its own telescope.
- `agents/tasks/LJ-1-225/lj-1.225-report.md`, read WHOLE. **Line read `:26`**,
  the `amb` SUPPLIED row that is now MEASURED FALSE.
- `agents/tasks/LJ-1-260/lj-1.260-report.md` and `agents/tasks/LJ-1-263/lj-1.263-report.md`, read WHOLE. **Line read `lj-1.260-report.md:18`**, "net +42", the numeral-premise landing.
- `src/L/BoundedSubset.lagda.md`, read `:130-350`, `:665-790`, `:1540-1621`.
  **Line read `:759`**, `elem : A.Elementary`.
- `src/L/Coding/Key.lagda.md`, read WHOLE. **Line read `:504`**,
  `union∈Lset-suc`, the first of the three landed L-rows.
- `archive/dev/TASKS-archived.md`, read for SHAPE. **Line read `:217`**,
  `L3.32-T194`, the retired green re-instantiation over a false bridge.
- `archive/src/2026-08-09-rud-route/L/Condensation.lagda.md`, read `:150-210`,
  `:780-890`. **Line read `:168-169`**, `CrossOut φ`, the archived `amb`
  analogue, and the absence of `Elementary`/`IsoInv` in the face.

## 7. LITERATURE USED (DD18)

`dev/literature/devlin-II5.md`, read `:365-395` (the twelve-row table) and
`:88-115` (clause (a)).

- **Row C1 carries `sl`, `sc`, `s₁`, `amb`.** The row is
  "Σ₁-with-Σ₀-matrix, uniform Δ₁, witness in carrier", PER-TOWER content
  (`dev/literature/devlin-II5.md:374`). Clause (a) is quoted at `:93-96`:
  "∀v∀γ [v = L_γ ↔ ∃z Φ(z, v, γ)]". `amb` states the "←" half at the ambient
  carrier; `s₁` is the Σ₁ certificate; `sl` and `sc` are the stage-level
  existence and coverage halves.
- **Row C4 carries `el`.** "Transfer along Σ₁-elementarity and the collapse",
  EITHER, neither-tower carrier (`dev/literature/devlin-II5.md:377`). `el` is
  full elementarity, stronger than the Σ₁-elementarity the row needs.
- **Row B carries `fwd` and `bwd`.** "Collapsing Lemma 1.7.1", EITHER
  (`dev/literature/devlin-II5.md:376`). The collapse iso is general set
  theory.
- **WHY NOT the rest.** I did not use C2, C3, C5, C6, D, E, F or G. None of
  the seven parameters is the bounded Def-step matrix (C2), the well-order
  (D, G), the counting (E) or the cardinal chain (F). The well-order is not in
  this chain.

## 8. RULES ANSWERED

- **C-38 as extended.** Section 1 audits the instantiation for all seven. A
  term with a delivered telescope is SUPPLIED; a term over a bare parameter
  is BUILT; a relayed equation is OPEN.
- **C-45.** `amb` is audited at its use site `ProbeLJ1184B.agda:122`, not at
  its name. `el`/`fwd`/`bwd` are audited at their delivered bodies, not at
  their module headers.
- **C-44.** The brief's claim "`[LJ-1.251]` measured `lh`'s supply IS step 6"
  does not reproduce verbatim; I say so in section 5 rather than carry it.
- **D-10.** I priced the truth of the recorded residue before pricing any
  proof: the four-item residue is true, and the three never-named parameters
  are not obligations.
- **P-l.** A judgement at one parameter is not a judgement at another. `el`
  SUPPLIED does not imply `sl` supplied; each was judged at its own site.
- **D-26.** Section 4 labels each parameter's carrier on the Def-vs-J axis.
- **C-22.** This report existed as a skeleton before the first source closed.
- **C-42.** I measured the seven parameters at one site, `module Whole`, and
  I did not sweep for other modules with the same shape.
- **C-36.** I did not treat the missing `Σ₁ φ₀` or the missing `q` as
  impossible. I named them.
- **C-43.** No escape hatch was offered and none was taken.
- **DD4.** Section 4 is the axis labelling, per parameter.
- **DD8.** One status per parameter, each with its basis at `file:line`.
- **DD18.** Sections 6 and 7.
- **I-5, C-12.** No Agda ran. No probe written. No slot held.
