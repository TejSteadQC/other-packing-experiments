import Ellipse.Area
import Mathlib.Analysis.InnerProductSpace.PiL2

/-!
# Bridging `diskSet` to the genuine Euclidean `Metric.closedBall`

`diskSet cx cy = {p : ℝ×ℝ | (p.1-cx)² + (p.2-cy)² ≤ 1}` is the genuine *Euclidean* closed unit
disk.  But the **default metric on `ℝ × ℝ` is the sup-norm**, so `Metric.closedBall (cx,cy) 1` in
`ℝ × ℝ` is a SQUARE, not the disk — we must NOT identify `diskSet` with that.

The faithful bridge is through `EuclideanSpace ℝ (Fin 2)`, where `Metric.closedBall` IS the
genuine Euclidean disk.  We reuse the measurable equivalence `prodEuclidEquiv : ℝ×ℝ ≃ᵐ
EuclideanSpace ℝ (Fin 2)` (which sends `p ↦ ![p.1, p.2]`, an isometry for the Euclidean metric)
already defined in `Ellipse.Area`, and prove:

```
diskSet cx cy = prodEuclidEquiv ⁻¹' (Metric.closedBall (prodEuclidEquiv (cx, cy)) 1)
```

i.e. `diskSet cx cy` is exactly the Euclidean closed ball of radius `1` about the point
`(cx, cy)` (viewed in `EuclideanSpace`), transported back through the standard equivalence.
Equivalently `p ∈ diskSet cx cy ↔ dist (prodEuclidEquiv p) (prodEuclidEquiv (cx,cy)) ≤ 1` where
`dist` is the genuine Euclidean distance.
-/

namespace Ellipse

open MeasureTheory Set

noncomputable section

/-- The Euclidean distance (in `EuclideanSpace ℝ (Fin 2)`) between the images of two points of
`ℝ × ℝ` is the genuine Euclidean distance `√((p.1-q.1)² + (p.2-q.2)²)`.  This is the squared
form, which is the convenient one. -/
theorem prodEuclidEquiv_dist_sq (p q : ℝ × ℝ) :
    dist (prodEuclidEquiv p) (prodEuclidEquiv q) ^ 2
      = (p.1 - q.1) ^ 2 + (p.2 - q.2) ^ 2 := by
  rw [EuclideanSpace.dist_sq_eq, Fin.sum_univ_two,
    prodEuclidEquiv_apply_zero, prodEuclidEquiv_apply_one,
    prodEuclidEquiv_apply_zero, prodEuclidEquiv_apply_one]
  simp only [Real.dist_eq, sq_abs]

/-- **Membership form of the bridge.** A point of `ℝ × ℝ` lies in `diskSet cx cy` iff its image
in `EuclideanSpace ℝ (Fin 2)` is at genuine Euclidean distance `≤ 1` from the image of the center
`(cx, cy)`. -/
theorem mem_diskSet_iff_dist (cx cy : ℝ) (p : ℝ × ℝ) :
    p ∈ diskSet cx cy ↔ dist (prodEuclidEquiv p) (prodEuclidEquiv (cx, cy)) ≤ 1 := by
  simp only [diskSet, Set.mem_setOf_eq]
  set d : ℝ := dist (prodEuclidEquiv p) (prodEuclidEquiv (cx, cy)) with hd
  have hd0 : 0 ≤ d := dist_nonneg
  have hsq : d ^ 2 = (p.1 - (cx, cy).1) ^ 2 + (p.2 - (cx, cy).2) ^ 2 :=
    prodEuclidEquiv_dist_sq p (cx, cy)
  -- (p.1-cx)²+(p.2-cy)² ≤ 1 ↔ d² ≤ 1 ↔ d ≤ 1 (since d ≥ 0).
  rw [← hsq]
  constructor
  · intro h; nlinarith [hd0, h]
  · intro h; nlinarith [hd0, h]

/-- **The `closedBall` bridge.** `diskSet cx cy` is exactly the genuine Euclidean
closed unit ball about `(cx, cy)`, transported back from `EuclideanSpace ℝ (Fin 2)` through the
standard measurable equivalence `prodEuclidEquiv`.  (We do NOT use `Metric.closedBall` on
`ℝ × ℝ` itself, whose metric is the sup-norm and whose ball is a square.) -/
theorem diskSet_eq_closedBall_preimage (cx cy : ℝ) :
    diskSet cx cy
      = prodEuclidEquiv ⁻¹' (Metric.closedBall (prodEuclidEquiv (cx, cy)) 1) := by
  ext p
  rw [Set.mem_preimage, Metric.mem_closedBall, mem_diskSet_iff_dist]

end

end Ellipse
