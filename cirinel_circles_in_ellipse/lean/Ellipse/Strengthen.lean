import Ellipse.Area

/-!
# Strengthening: `IsLeast` packaging of the minimum area

This file packages the two halves of the headline result — the **lower bound**
(`area_toReal_ge_of_feasibleGen`) and the **attainment** (`feasible_optimal` at the optimal
ellipse) — into a single standard mathlib statement:

```
theorem isLeast_minArea : IsLeast achievableAreas (3 * Real.sqrt 3 / 2 * Real.pi)
```

`IsLeast S x` unfolds to `x ∈ S ∧ x ∈ lowerBounds S`, i.e. `x ∈ S ∧ ∀ y ∈ S, x ≤ y`.  So this
one line says, in mathlib's own vocabulary, that `(3√3/2)·π` **is the minimum** of the set of
achievable areas:
* it is **attained** (membership) — there is a genuine ellipse (positive-definite matrix) holding two
  interior-disjoint unit disks whose Lebesgue area equals `(3√3/2)·π`;
* it is a **lower bound** — every such ellipse has area at least `(3√3/2)·π`.

The optimal ellipse `x²/(9/2) + y²/(3/2) ≤ 1` is, in `(A,B,C,c)` form, `A = 2/9`, `B = 0`,
`C = 2/3`, `c = (0,0)`: `genDet = (2/9)(2/3) - 0 = 4/27`, area `= π/√(4/27) = π·√(27/4) =
(3√3/2)·π`.  Its `FeasibleGen` witness is transported from `feasible_optimal`.
-/

namespace Ellipse

open MeasureTheory Set

noncomputable section

/-! ## The optimal ellipse in `(A,B,C,c)` form is `FeasibleGen`

`ellipseGenSet (2/9) 0 (2/3) (0,0)` is literally the same set as `ellipseSet (9/2) (3/2)`
(since `(2/9)·x² = x²/(9/2)` and `(2/3)·y² = y²/(3/2)`), so the two-disk witness from
`feasible_optimal` transfers verbatim. -/

/-- The optimal ellipse `(A,B,C,c) = (2/9, 0, 2/3, (0,0))` is the axis-aligned ellipse
`x²/(9/2) + y²/(3/2) ≤ 1`. -/
theorem ellipseGenSet_optimal :
    ellipseGenSet (2 / 9) 0 (2 / 3) (0, 0) = ellipseSet (9 / 2) (3 / 2) := by
  ext z
  simp only [ellipseGenSet, ellipseSet, quadForm, Set.mem_setOf_eq,
    sub_zero, mul_zero, zero_mul, add_zero]
  constructor <;> intro h <;> nlinarith [h]

/-- **The optimal ellipse is `FeasibleGen`** — it is positive-definite (`0 < 2/9`,
`0 < genDet = 4/27`) and holds two interior-disjoint unit disks (centers `(±1,0)`), inherited
from `feasible_optimal`. -/
theorem feasibleGen_optimal : FeasibleGen (2 / 9) 0 (2 / 3) (0, 0) := by
  refine ⟨by norm_num, by simp only [genDet]; norm_num, ?_⟩
  obtain ⟨c₁, c₂, h1, h2, hd⟩ := feasible_optimal
  rw [ellipseGenSet_optimal]
  exact ⟨c₁, c₂, h1, h2, hd⟩

/-- `genDet (2/9) 0 (2/3) = 4/27`. -/
theorem genDet_optimal : genDet (2 / 9) 0 (2 / 3) = 4 / 27 := by
  simp only [genDet]; norm_num

/-- **The optimal ellipse has Lebesgue area exactly `(3√3/2)·π`.** -/
theorem volume_optimal_toReal :
    (volume (ellipseGenSet (2 / 9) 0 (2 / 3) (0, 0))).toReal = 3 * Real.sqrt 3 / 2 * Real.pi := by
  rw [volume_ellipseGenSet (2 / 9) 0 (2 / 3) (0, 0) (by norm_num) (by rw [genDet_optimal]; norm_num)]
  rw [genDet_optimal]
  have hge0 : (0 : ℝ) ≤ Real.pi / Real.sqrt (4 / 27) := by positivity
  rw [ENNReal.toReal_ofReal hge0]
  -- π / √(4/27) = π · √(27/4) = π · (3√3/2)
  have hmul : Real.pi / Real.sqrt (4 / 27) = Real.pi * Real.sqrt (27 / 4) := by
    rw [div_eq_iff (by positivity), mul_assoc, ← Real.sqrt_mul (by norm_num),
      show (27 : ℝ) / 4 * (4 / 27) = 1 by norm_num, Real.sqrt_one, mul_one]
  rw [hmul, sqrt_27_div_4, mul_comm]

/-! ## The achievable-area set and the headline `IsLeast` theorem -/

/-- The set of areas achievable by some ellipse (with positive-definite matrix) holding two
interior-disjoint unit disks. -/
def achievableAreas : Set ℝ :=
  { a | ∃ (A B C : ℝ) (c : ℝ × ℝ), FeasibleGen A B C c ∧
        a = (volume (ellipseGenSet A B C c)).toReal }

/-- The achievable-area set is nonempty (the optimal ellipse witnesses it). -/
theorem achievableAreas_nonempty : achievableAreas.Nonempty :=
  ⟨_, 2 / 9, 0, 2 / 3, (0, 0), feasibleGen_optimal, rfl⟩

/-- **The headline result.** `(3√3/2)·π` is the *least* achievable area: it is
both attained (by the optimal ellipse) and a lower bound for every feasible ellipse.  This is
the single statement "the minimum area of an ellipse containing two interior-disjoint unit
disks is `(3√3/2)·π`", in mathlib's `IsLeast` vocabulary. -/
theorem isLeast_minArea :
    IsLeast achievableAreas (3 * Real.sqrt 3 / 2 * Real.pi) := by
  constructor
  · -- membership: attained at the optimal ellipse
    exact ⟨2 / 9, 0, 2 / 3, (0, 0), feasibleGen_optimal, volume_optimal_toReal.symm⟩
  · -- lower bound: every achievable area is ≥ (3√3/2)·π
    rintro a ⟨A, B, C, c, hfeas, rfl⟩
    exact area_toReal_ge_of_feasibleGen A B C c hfeas

end

end Ellipse
