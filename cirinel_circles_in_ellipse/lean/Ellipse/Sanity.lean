import Ellipse.Strengthen
import Mathlib.Analysis.Real.Pi.Bounds

/-!
# Sanity and falsifiability theorems

These are *non-vacuity* and *falsifiability* checks: each would FAIL to prove if the
definitions secretly encoded a trivial or wrong problem.  Proving them is strong, cheap
evidence that the encoding is right.

* `not_feasible_unit_circle : ¬ Feasible 1 1` — the unit-circle ellipse (`u=v=1`, area `π`)
  provably CANNOT hold two interior-disjoint unit disks.  (A unit disk inside the unit disk
  must be concentric, so both centers are forced to the origin, distance `0 < 2`.)  If
  `Feasible` were trivially satisfiable this would be unprovable.
* `unitDisk_in_unitDisk_concentric` — the supporting lemma: a unit disk contained in the unit
  disk is centered at the origin.
* `minArea_lt`, `minArea_gt`, `minArea_pos` — numeric sanity: the minimum area `(3√3/2)·π`
  lies strictly between `8` and `8.2` (so it is neither a degenerate `0` nor `∞`).
* `achievableAreas_nonempty'` — restates that the achievable set is nonempty (the result is
  not vacuous), pointing at the optimal witness.
-/

namespace Ellipse

open Set

/-! ## A unit disk inside the unit disk is concentric -/

/-- **A unit disk contained in the unit disk is concentric.**  If `diskSet cx cy ⊆ ellipseSet 1 1`
(the closed unit disk), then `(cx, cy) = (0, 0)`.

Proof: containment forces `fits 1 1 cx cy`, i.e. every boundary point `(cx+c, cy+s)`
(`c²+s²=1`) of the inner disk lies in the unit disk.  Plugging the antipodal pair `(c,s)` and
`(-c,-s)` and adding gives `cx²+cy²+1 ≤ 1`, so `cx²+cy² ≤ 0`, hence `cx = cy = 0`. -/
theorem unitDisk_in_unitDisk_concentric (cx cy : ℝ)
    (hsub : diskSet cx cy ⊆ ellipseSet 1 1) : cx = 0 ∧ cy = 0 := by
  have hfits : fits 1 1 cx cy := fits_of_subset 1 1 cx cy hsub
  -- pick a unit direction (c,s) with c²+s²=1; use (1,0) and (-1,0) for one coordinate,
  -- (0,1) and (0,-1) for the other.  Adding antipodal pairs kills the cross term.
  -- horizontal antipodes:
  have h1 := hfits 1 0 (by ring)
  have h2 := hfits (-1) 0 (by ring)
  -- vertical antipodes:
  have h3 := hfits 0 1 (by ring)
  have h4 := hfits 0 (-1) (by ring)
  simp only [div_one] at h1 h2 h3 h4
  -- h1: (cx+1)²+cy² ≤ 1 ; h2: (cx-1)²+cy² ≤ 1 ; h3: cx²+(cy+1)² ≤ 1 ; h4: cx²+(cy-1)² ≤ 1
  -- adding h1+h2: 2cx²+2cy²+2 ≤ 2 ⟹ cx²+cy² ≤ 0.  Same from h3+h4.
  constructor
  · nlinarith [h1, h2, sq_nonneg cx, sq_nonneg cy]
  · nlinarith [h3, h4, sq_nonneg cx, sq_nonneg cy]

/-! ## The unit circle is not feasible -/

/-- **Falsifiability.** The unit-circle "ellipse" `x² + y² ≤ 1` (`u = v = 1`)
CANNOT hold two interior-disjoint unit disks.  Both disk-centers are forced to the origin
(concentric), so their distance is `0`, contradicting the required `≥ 2`. -/
theorem not_feasible_unit_circle : ¬ Feasible 1 1 := by
  rintro ⟨c₁, c₂, h1, h2, hd⟩
  obtain ⟨hx1, hy1⟩ := unitDisk_in_unitDisk_concentric c₁.1 c₁.2 h1
  obtain ⟨hx2, hy2⟩ := unitDisk_in_unitDisk_concentric c₂.1 c₂.2 h2
  -- both centers are the origin, so nrm2 (c₁ - c₂) = 0, contradicting 4 ≤ it.
  simp only [nrm2, Prod.fst_sub, Prod.snd_sub, hx1, hy1, hx2, hy2] at hd
  norm_num at hd

/-! ## Numeric sanity of the minimum area

`(3√3/2)·π` is a genuine finite positive number, between `8` and `8.2` — it is neither a
degenerate `0` nor `∞`.  We use `1.732 < √3 < 1.7321` and `3.1415 < π < 3.1416`. -/

private theorem sqrt3_bounds : 1.732 < Real.sqrt 3 ∧ Real.sqrt 3 < 1.7321 := by
  constructor
  · rw [show (1.732 : ℝ) = Real.sqrt (1.732 ^ 2) by rw [Real.sqrt_sq (by norm_num)]]
    apply Real.sqrt_lt_sqrt (by norm_num); norm_num
  · rw [show (1.7321 : ℝ) = Real.sqrt (1.7321 ^ 2) by rw [Real.sqrt_sq (by norm_num)]]
    apply Real.sqrt_lt_sqrt (by norm_num); norm_num

/-- **The minimum area is strictly less than `8.2`.** -/
theorem minArea_lt : 3 * Real.sqrt 3 / 2 * Real.pi < 8.2 := by
  obtain ⟨_, hub⟩ := sqrt3_bounds
  have hpi : Real.pi < 3.1416 := Real.pi_lt_d4
  have hpipos : 0 < Real.pi := Real.pi_pos
  -- 3·√3/2·π < 3·1.7321/2·3.1416 < 8.2
  nlinarith [hub, hpi, hpipos, Real.sqrt_nonneg 3]

/-- **The minimum area is strictly greater than `8`.** -/
theorem minArea_gt : (8 : ℝ) < 3 * Real.sqrt 3 / 2 * Real.pi := by
  obtain ⟨hlb, _⟩ := sqrt3_bounds
  have hpi : 3.1415 < Real.pi := Real.pi_gt_d4
  -- 3·√3/2·π > 3·1.732/2·3.1415 = 2.598·3.1415 > 8
  nlinarith [hlb, hpi, Real.sqrt_nonneg 3, Real.pi_pos]

/-- **The minimum area is positive.** (So the result is not a degenerate `0`.) -/
theorem minArea_pos : 0 < 3 * Real.sqrt 3 / 2 * Real.pi := by
  have : (8 : ℝ) < 3 * Real.sqrt 3 / 2 * Real.pi := minArea_gt
  linarith

/-- Restatement that the achievable-area set is nonempty (non-vacuity of the result),
pointing at the optimal ellipse as the explicit witness. -/
theorem achievableAreas_nonempty' : (3 * Real.sqrt 3 / 2 * Real.pi) ∈ achievableAreas :=
  isLeast_minArea.1

end Ellipse
