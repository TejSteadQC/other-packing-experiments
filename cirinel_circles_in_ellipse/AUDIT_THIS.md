# How to be sure the Lean proof proves the right thing (human audit)

**Result:** the smallest ellipse containing two interior-disjoint unit circles has area exactly
(3√3/2)π — found numerically by James Buddenhagen (2004), never proved until now.
**Status:** fully kernel-certified in Lean 4 + mathlib. Zero `sorry`. Only the 3 standard axioms.

Lean's kernel guarantees "the proof term matches the stated theorem." It does NOT guarantee the
statement is the right problem. THAT is what you (the human) must check. Here is the whole surface
to audit — it's small.

## 1. The capstone theorem (Ellipse/Area.lean)
```lean
theorem area_toReal_ge_of_feasibleGen (A B C : ℝ) (c : ℝ × ℝ) (hfeas : FeasibleGen A B C c) :
    3 * Real.sqrt 3 / 2 * Real.pi ≤ (MeasureTheory.volume (ellipseGenSet A B C c)).toReal
```
Read in English: for any ellipse described by (A,B,C,c) that is `FeasibleGen` (= positive-definite
and holds two disjoint unit disks), its area is ≥ (3√3/2)π.
Plus `feasible_optimal : Feasible (9/2) (3/2)` — the optimum is ACHIEVED (theorem not vacuous).

## 2. Check each definition is faithful (these are the trust surface)
- `ellipseGenSet A B C c = {x : ℝ×ℝ | A*(x.1-c.1)^2 + 2*B*(x.1-c.1)*(x.2-c.2) + C*(x.2-c.2)^2 ≤ 1}`
  — the genuine filled ellipse `(x-c)ᵀ M (x-c) ≤ 1` for `M = ![![A,B],[B,C]]`. (Proven equal to
  the real matrix form by `quadForm_eq_matrix`; `genDet A B C = A*C-B^2` proven `= Matrix.det M`
  by `genMat_det`.) ✓ genuine, arbitrary tilt and center.
- `diskSet cx cy = {p : ℝ×ℝ | (p.1-cx)^2 + (p.2-cy)^2 ≤ 1}` — genuine closed unit disk, Euclidean. ✓
- `FeasibleGen A B C c := 0 < A ∧ 0 < genDet A B C ∧ ∃ d₁ d₂, diskSet d₁ ⊆ ellipseGenSet ∧
  diskSet d₂ ⊆ ellipseGenSet ∧ 4 ≤ nrm2 (d₁-d₂)`. `0<A ∧ 0<genDet` is Sylvester's criterion =
  M positive definite (a genuine ellipse, not a parabola/hyperbola). `⊆` is genuine set
  containment. `4 ≤ nrm2(d₁-d₂)` is centers ≥2 apart. ✓
- `MeasureTheory.volume` is genuine Lebesgue measure (confirmed: a type-ascription example using
  `MeasureTheory.volume` directly compiles against the theorem). ✓
- "disjoint interiors": `Disjoint.lean`'s `interior_disjoint_iff` proves
  `interior (diskSet a) ∩ interior (diskSet b) = ∅ ↔ 4 ≤ nrm2 (a-b)`, so the center-distance
  encoding IS the literal interior-disjoint condition. ✓ (`area_ge_of_feasible'` states the main
  bound with the literal `interior ∩ interior = ∅`.)

## 3. Check the axioms (the cheapest, strongest check)
Run (or read `Ellipse/MyAuditArea.lean`):
```
import Ellipse.Area
#print axioms area_toReal_ge_of_feasibleGen
```
It must print exactly `[propext, Classical.choice, Quot.sound]` — the 3 standard mathlib axioms.
If `sorryAx` appeared, there'd be a hidden gap. It does not. (This check is transitive: it covers
every lemma the theorem depends on, in every imported file, no matter how deep.)

## 4. Non-vacuity
`feasible_optimal : Feasible (9/2) (3/2)` proves the (9/2,3/2) ellipse genuinely contains two
disjoint unit disks (centers (±1,0)), so the bound is attained and the theorem is not vacuously
true. `area_optimal : Real.sqrt ((9/2)*(3/2)) = 3*Real.sqrt 3/2` ties it to the exact value.

## What is NOT claimed
- The hand-proof PDF (`../ellipse_proof/proof_ellipse_n2.tex`) is a separate, human-readable
  argument; the Lean uses a cleaner route for one step (a cone-restricted rotation identity instead
  of the PDF's ψ₀≤π/4 rotation argument). Both reach the same theorem. The PDF is for reading; the
  Lean is the certificate.
- This proves the area BOUND and that it's attained. "Uniqueness of the optimal ellipse" is shown
  at the (u,v) level (strict for v≠3/2) but not separately packaged.

Bottom line: if you accept the ~5 definitions above as faithful (they are plain), and the
`#print axioms` output, then the theorem is true with the same confidence as mathlib itself.
