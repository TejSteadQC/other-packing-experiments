import Ellipse.Reduction

/-!
# Main theorem: the smallest ellipse containing two unit circles

We assemble the algebraic spine (`Ellipse.Algebra`) and the convexity reduction
(`Ellipse.Convex`, `Ellipse.Reduction`).

The genuinely-proved scalar invariant is `u * v = (ab)²`, the area-squared over `π²`.
The full proof shows: any feasible `(u,v)` (ellipse holding two interior-disjoint unit
disks) has `u*v ≥ 27/4`, with the optimum `u=9/2, v=3/2` achieving it; equivalently
the area `π√(uv) ≥ (3√3/2)π`.

The chain to "two interior-disjoint unit disks ⊆ ellipse" uses:
* `disk ⊆ ellipse → fits` (easy: boundary points are in the disk),
* the Step-2 reduction `fits-of-two-disjoint` (`Ellipse.Reduction`; Step 2c now closed),
* the lower bound `uv_ge_of_fits` (`Ellipse.Algebra`, fully proved).
-/

namespace Ellipse

open Set

/-! ## Bridge: disk containment ⟹ `fits` (easy direction)

A boundary point of the unit disk centered at `(p,q)` is `(p+c, q+s)` with `c²+s²=1`,
and it lies in the disk (distance exactly 1 ≤ 1).  So `diskSet ⊆ ellipseSet` forces
each such point into the ellipse, i.e. `fits`. -/

/-- If the closed unit disk at `(p,q)` is contained in the ellipse, then `fits`. -/
theorem fits_of_subset (u v p q : ℝ)
    (hsub : diskSet p q ⊆ ellipseSet u v) : fits u v p q := by
  intro c s hcs
  have hmem : (p + c, q + s) ∈ diskSet p q := by
    simp only [diskSet, Set.mem_setOf_eq]
    -- ((p+c) - p)² + ((q+s) - q)² = c² + s² = 1 ≤ 1
    have : ((p + c) - p) ^ 2 + ((q + s) - q) ^ 2 = c ^ 2 + s ^ 2 := by ring
    rw [this, hcs]
  have := hsub hmem
  simpa [ellipseSet] using this

/-! ## Feasibility predicate

`Feasible u v` : the ellipse `x²/u + y²/v ≤ 1` contains two interior-disjoint closed
unit disks.  "Interior-disjoint" is encoded as the centers being at Euclidean distance
`≥ 2` (`nrm2 (c₁ - c₂) ≥ 4`), the standard characterization for unit disks. -/

/-- The ellipse holds two interior-disjoint unit disks, with explicit centers. -/
def Feasible (u v : ℝ) : Prop :=
  ∃ c₁ c₂ : ℝ × ℝ,
    diskSet c₁.1 c₁.2 ⊆ ellipseSet u v ∧
    diskSet c₂.1 c₂.2 ⊆ ellipseSet u v ∧
    4 ≤ nrm2 (c₁ - c₂)

/-! ## The lower bound on `u * v`

Given feasibility and `u ≥ v > 0`, plus `O ∈ E₁` (which holds once `v ≥ 1`; we get
`v ≥ 1` from one disk fitting), the Step-2 reduction yields `fits u v 1 0`, and then
`uv_ge_of_fits` gives `u*v ≥ 27/4`.

Step 2c (`fits_axis_of_fits_unitVec`) is now fully proved, so this theorem is
kernel-certified (axioms `[propext, Classical.choice, Quot.sound]` only). -/

/-- **Main lower bound.** Any ellipse `x²/u + y²/v ≤ 1` (with `u ≥ v > 0`) that holds
two interior-disjoint unit disks satisfies `u * v ≥ 27/4`. -/
theorem uv_ge_of_feasible (u v : ℝ) (hv : 0 < v) (huv : v ≤ u)
    (hfeas : Feasible u v) : (27 : ℝ) / 4 ≤ u * v := by
  have hu : 0 < u := lt_of_lt_of_le hv huv
  obtain ⟨c₁, c₂, hc₁, hc₂, hdist⟩ := hfeas
  -- both centers are in E₁
  have hf1 : fits u v c₁.1 c₁.2 := fits_of_subset u v _ _ hc₁
  have hf2 : fits u v c₂.1 c₂.2 := fits_of_subset u v _ _ hc₂
  have hp : c₁ ∈ E₁ u v := hf1
  have hq : c₂ ∈ E₁ u v := hf2
  -- v ≥ 1: the disk at c₁ fits, so its "side point" gives 1/u + 1/v ≤ 1 after centering...
  -- Simpler: a single unit disk fitting forces the minor axis ≥ 1.  We extract v ≥ 1
  -- from `fits` at c₁ via the worst vertical chord.  Use the side-point bound at the
  -- *origin-centered* reduction is cleaner *after* we have fits(1,0); but we need O∈E₁
  -- first. We instead get v ≥ 1 directly from fits at c₁:
  have hv1 : 1 ≤ v := by
    -- For ANY center (p,q) that fits, plugging the two antipodal vertical boundary points
    -- (c,s)=(0,1) and (0,-1) gives (p)²/u + (q±1)²/v ≤ 1; summing kills the cross term:
    --   2p²/u + ((q+1)²+(q-1)²)/v ≤ 2, i.e. 2p²/u + (2q²+2)/v ≤ 2, so (q²+1)/v ≤ 1, v ≥ q²+1 ≥ 1.
    have ha := hf1 0 1 (by ring)
    have hb := hf1 0 (-1) (by ring)
    -- ha : (c₁.1+0)²/u + (c₁.2+1)²/v ≤ 1 ; hb : (c₁.1+0)²/u + (c₁.2-1)²/v ≤ 1
    have e1 : (c₁.1 + 0) ^ 2 / u + (c₁.2 + 1) ^ 2 / v ≤ 1 := ha
    have e2 : (c₁.1 + 0) ^ 2 / u + (c₁.2 + -1) ^ 2 / v ≤ 1 := hb
    -- add them; the p²/u terms are nonneg, the v-terms sum to (2 c₁.2² + 2)/v.
    have hpos : 0 ≤ (c₁.1 + 0) ^ 2 / u := by positivity
    -- (c₁.2+1)²/v + (c₁.2-1)²/v = (2 c₁.2² + 2)/v ≥ 2/v
    have hsum : (c₁.2 + 1) ^ 2 / v + (c₁.2 + -1) ^ 2 / v ≤ 2 := by linarith
    have hge : (2 : ℝ) / v ≤ (c₁.2 + 1) ^ 2 / v + (c₁.2 + -1) ^ 2 / v := by
      rw [← add_div]
      apply div_le_div_of_nonneg_right _ hv.le
      nlinarith [sq_nonneg c₁.2]
    have : (2 : ℝ) / v ≤ 2 := le_trans hge hsum
    rw [div_le_iff₀ hv] at this
    linarith
  -- O ∈ E₁
  have hO : (0, 0) ∈ E₁ u v := origin_mem_E₁ u v hu hv hv1 huv
  -- Step-2 reduction ⟹ fits(1,0)
  have hfits10 : fits u v 1 0 :=
    fits_axis_of_two_disjoint u v hu hv huv hO c₁ c₂ hp hq hdist
  exact uv_ge_of_fits u v hv huv hfits10

/-! ## The optimal ellipse is feasible (upper bound / construction)

At `u=9/2, v=3/2`, the disks at `(±1,0)` fit and are at distance 2. -/

/-- The optimal ellipse holds two interior-disjoint unit disks (at `(±1,0)`). -/
theorem feasible_optimal : Feasible (9 / 2) (3 / 2) := by
  refine ⟨(1, 0), (-1, 0), ?_, ?_, ?_⟩
  · -- disk at (1,0) ⊆ ellipse: this is the boundary-fits ⟹ subset for the *interior* too.
    -- We need the FULL disk in the ellipse, not just the boundary.  Use convexity of the
    -- ellipse: but here we give a direct certificate.  A point (x,y) in the disk at (1,0)
    -- has (x-1)²+y² ≤ 1; we must show x²/(9/2)+y²/(3/2) ≤ 1.
    intro z hz
    simp only [diskSet, Set.mem_setOf_eq] at hz
    simp only [ellipseSet, Set.mem_setOf_eq]
    -- 1 - (x²/(9/2)+y²/(3/2)) = (4/9)(... ) ; with (x-1)²+y²≤1 ⟹ result ≤ 1.
    -- Multiply target by 9/2>0: want x² + 3y² ≤ 9/2.  From disk: y² ≤ 1-(x-1)² = 2x - x² - ... wait
    -- (x-1)²+y² ≤ 1 ⟹ y² ≤ 1-(x-1)² = -x²+2x.  Then x²+3y² ≤ x²+3(-x²+2x)= -2x²+6x = -2(x²-3x).
    -- max of -2x²+6x is at x=3/2, value 9/2.  So x²+3y² ≤ 9/2. ✓ (nlinarith)
    nlinarith [hz, sq_nonneg (z.1 - 3/2), sq_nonneg z.2]
  · intro z hz
    simp only [diskSet, Set.mem_setOf_eq] at hz
    simp only [ellipseSet, Set.mem_setOf_eq]
    nlinarith [hz, sq_nonneg (z.1 + 3/2), sq_nonneg z.2]
  · -- centers (1,0) and (-1,0): nrm2 ((1,0)-(-1,0)) = nrm2 (2,0) = 4
    simp only [nrm2, Prod.fst_sub, Prod.snd_sub]
    norm_num

/-! ## The clean numeric form of the bound -/

/-- `√(27/4) = 3√3/2`. -/
theorem sqrt_27_div_4 : Real.sqrt (27 / 4) = 3 * Real.sqrt 3 / 2 := by
  rw [show (27 : ℝ) / 4 = (3 * Real.sqrt 3 / 2) ^ 2 by
    rw [div_pow, mul_pow, Real.sq_sqrt (by norm_num : (3:ℝ) ≥ 0)]; norm_num]
  exact Real.sqrt_sq (by positivity)

/-! ## The area form of the bound

For an ellipse of area `A = π√(uv)`, the lower bound `uv ≥ 27/4` gives
`A ≥ π·√(27/4) = (3√3/2)π`.  We state this as a clean corollary on the scalar
`√(uv)` (the area divided by `π`). -/

/-- **Main theorem (area form, lower bound).** Any feasible ellipse `x²/u+y²/v ≤ 1`
(`u ≥ v > 0`, holding two interior-disjoint unit disks) has `√(uv) ≥ 3√3/2`; i.e. its
area `π√(uv)` is at least `(3√3/2)π`.  Kernel-certified (Step 2c now closed). -/
theorem area_ge_of_feasible (u v : ℝ) (hv : 0 < v) (huv : v ≤ u)
    (hfeas : Feasible u v) :
    3 * Real.sqrt 3 / 2 ≤ Real.sqrt (u * v) := by
  have h := uv_ge_of_feasible u v hv huv hfeas
  rw [← sqrt_27_div_4]
  exact Real.sqrt_le_sqrt h

/-- **Optimum achieves the bound.** At `u=9/2, v=3/2`, `√(uv) = 3√3/2` exactly. -/
theorem area_optimal : Real.sqrt ((9 / 2) * (3 / 2)) = 3 * Real.sqrt 3 / 2 := by
  rw [show (9 / 2 : ℝ) * (3 / 2) = 27 / 4 by norm_num]
  exact sqrt_27_div_4

end Ellipse
