# Review of `grounded-from-complete` (LJ-1.718)

**Verdict: NO-GO.** The composition the brief names does not close, and
the wall is not a mismatch between `Completeness`'s codes and the
hull's δ. The codes match, and the `Completeness` -> `hull-closed`
half composes green. The wall is the **application of `At.Convert`**:
checking `conv ca cp a sat` does not terminate at this frame under the
wide caliber, at six shapes, in two module placements, and the
predecessor's own attempt on the same route hung the same way. No
`grounded-from-complete` term exists in the tree after this task.

## 1. WHAT CLOSED

The repaired statement is delivered as types in
`agents/tasks/LJ-1-718/Probe718.agda`, and the probe is green
(`runs/p-2.out`, `EXIT=0` at `:22`, 9.27 s, peak 1,759,444,992 bytes
against the 2,147,483,648-byte wide cap):

- `Convert`, Probe673's type verbatim (`Probe718.agda:74-75`).
- `Completeness` with the critic's repair, `IsOrd` on the parameter
  code (`Probe718.agda:81-86`), as `Commute` already carries `IsOrd`
  on its collapse (`Probe652.agda:249-253`).
- `GroundedFromComplete`, the obligation's whole telescope
  (`Probe718.agda:93-101`), including `IsOrd δ` in the conclusion's
  own telescope. The term is not declared and no
  `grounded-from-complete` name exists in the file, so the witness
  meter reads the truth: MISSING.

The frame floor is green too: statement-only, hole body, cold
(`runs/floor-1.out`, 120.49 s, peak 1,792,933,888 bytes, the only
error the designed hole at `runs/FLOOR.agda.txt:103`).

**The codes match the hull's δ.** The composition's first half,
`Completeness ca cp …` fed to `hull-closed (A.inBound ca cp)` across
the module boundary, typechecks and exits 0 (`runs/d-2.out`, 108.47
s, peak 1,771,179,392 bytes, `EXIT=0` at `:22`). The two code readbacks
compose with `subst IsOrd` and `cong Lset` exactly as the brief's W3
hypothesized.

## 2. WHAT WALLED, WITH THE MEASUREMENTS

The second half, `conv ca cp a sat`, producing the ambient triple at
the code values, does not elaborate. All runs one Agda process at a
time, `GHCRTS="-A64m -I0 -M2g"`, the wide caliber set on the pane.

| run | shape | outcome | evidence |
|---|---|---|---|
| `p-1` | the full body, first shape | killed at the 900 s tool cap, no `ended` | `runs/p-1.out` |
| `d-1` | full body, `comp` application holed | killed at the 300 s tool cap | `runs/d-1.out` |
| `d-3` | full composition, plain-argument lemma | `EXIT=251`, heap exhausted, 282.36 s, peak 2,604,580,864 | `runs/d-3.out:4-6` |
| `d-4` | `conv` + `subst` only, no tuple | `EXIT=251`, heap exhausted, 283.63 s, peak 2,551,070,720 | `runs/d-4.out:4-6` |
| `d-5` | the bare `conv` application | killed at the 300 s tool cap | `runs/d-5.out` |
| `d-7` | the bare application in a lean module, no `Build` | killed at the 300 s tool cap | `runs/d-7.out` |

The green controls that isolate the poison:

| run | shape | outcome | evidence |
|---|---|---|---|
| `d-2` | `hull-closed (A.inBound ca cp)` fed `A.BoundInStage` | `EXIT=0`, 108.47 s | `runs/d-2.out:22` |
| `d-6` | `conv`'s whole domain STATED in a signature (`mapFo val (A.inBound ca cp)`, the `fst (val c)` environments) | green but for the designed hole, 7.59 s | `runs/d-6.out` |

So the signature of the application is cheap and the `hull-closed`
half is cheap; the cost fires only when `At.Convert`'s body is
computed FOR an application and its domain compared against the
argument. Peak over the cap with one application present
(`runs/d-3.out:4`: "agda: Heap exhausted") is a heap wall on the
minimal shape, and the coder clause's restructuring duty is spent:
split to one application (`d-5`), move the application out of the
frame module (`d-7`), drop `subst` (`d-5`), drop `comp` (`d-1`). The
application alone still hangs.

**`Convert` is not avoidable in the proof.** The obligation's third
hypothesis is the matrix's soundness (`a ≡ Lset p` FROM a triple); it
consumes triples and produces none. `Completeness` produces stage
satisfactions, and `hull-closed` produces hull members with stage
satisfactions. The ambient `⊨ₚ` triple at `(Lset δ, δ, z)` has exactly
one producer in the brief's hypothesis set: `Convert`.

## 3. THE PREDECESSOR'S INDEPENDENT WALL

`[LJ-1.673]`'s own report records the same route dying: "A
substitution into the ambient reading of `matrix₃` did not return a
checker (`runs/p-4.out`)" (`agents/tasks/LJ-1-673/lj-1.673-report.md`,
section 11, "What the shape resisted"), and its next-brief list asks
to "FUND `Convert` AS A GENERIC UNPACK AT A 3-SLOT Δ₀ FORMULA, not as
a substitution into this matrix's ambient reading. That substitution
is the checker `runs/p-4.out` did not finish"
(`agents/tasks/LJ-1-673/lj-1.673-report.md`, section 12, item 2). My
`d`-grid reproduces that wall with the heap capped and isolated to
one application.

## 4. THE REMAINING MISMATCH, NAMED

Not the codes. The brief's W3 alternative, "Completeness's codes do
not match the hull's δ", is measured FALSE: `d-2` is the codes
flowing into `hull-closed` and it is green. The remaining obstruction
is elaboration-level: `At.Convert`'s application, whose domain type
carries `mapFo val (inBound ca cp)` at a module path that must be
unfolded against the argument's path at application time. Stating the
same domain type is cheap (`d-6`); comparing it for an application is
not. This is a property of the type's PLACEMENT (stated inside
`At` at `Probe673.agda:115-119`, applied outside), not of the
mathematics, and the mathematics of the composition is otherwise
complete.

## 5. WHAT THE NEXT BRIEF NEEDS

1. **Do not re-dispatch the hypothesis-based composition as stated.**
   Six shapes measured; the application of `At.Convert` is the wall.
2. **Fund `Convert` as a CONSTRUCTED term at this frame and compose
   against the construction**: `[LJ-1.692]`'s
   `hull-convert-at-matrix` already inhabits `At.Convert` at the
   `(Lset lam)` instance by construction, and its file is green
   (`agents/tasks/LJ-1-692/Probe692.agda:61-66`). A composition
   against a delivered `Convert` changes the obligation's content
   (the hypothesis is spent, not assumed), so that is the
   mathematician's call, not mine.
3. **Or fund the generic unpack at a 3-slot Δ₀ formula**, the
   predecessor's own recommendation (section 3 above), and restate
   the obligation against it.
4. **The repaired telescope is settled.** `GroundedFromComplete`
   (`Probe718.agda:93-101`) is the statement the next attempt should
   carry, with `IsOrd δ` in the conclusion's own telescope and
   `IsOrd (fst (val cp))` on the supplier.
