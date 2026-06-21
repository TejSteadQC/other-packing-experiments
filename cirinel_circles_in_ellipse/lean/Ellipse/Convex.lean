import Ellipse.Algebra
import Mathlib.Analysis.Convex.Basic
import Mathlib.Analysis.Convex.Function

/-!
# Step 2: the convexity reduction

The set of admissible centers `E₁ = {z | fits u v z.1 z.2}` is convex and centrally
symmetric.  Combined with "interior-disjoint ⟹ centers ≥ 2 apart" this forces a unit
vector into `E₁`, and then the Step 2c lemma (`Ncubic_unit_le_axis`) gives `fits (1,0)`.

We work in `ℝ × ℝ` with the (Euclidean) quadratic disk/ellipse sets defined explicitly
(the *metric* on `ℝ × ℝ` is the sup-norm, so we do NOT use `Metric.closedBall`).
-/

namespace Ellipse

open Set

/-- The closed unit disk centered at `(cx, cy)` (Euclidean), as an explicit set. -/
def diskSet (cx cy : ℝ) : Set (ℝ × ℝ) :=
  {p : ℝ × ℝ | (p.1 - cx) ^ 2 + (p.2 - cy) ^ 2 ≤ 1}

/-- The closed ellipse `x²/u + y²/v ≤ 1`, as an explicit set. -/
def ellipseSet (u v : ℝ) : Set (ℝ × ℝ) :=
  {p : ℝ × ℝ | p.1 ^ 2 / u + p.2 ^ 2 / v ≤ 1}

/-- The set of admissible disk-centers: those `z` whose unit disk's *boundary circle*
sits inside the ellipse (`fits`). -/
def E₁ (u v : ℝ) : Set (ℝ × ℝ) :=
  {z : ℝ × ℝ | fits u v z.1 z.2}

/-! ## 2a-i: convexity of `E₁`

For each fixed boundary direction `(c,s)`, the constraint
`(p+c)²/u + (q+s)²/v ≤ 1` cuts out a convex set in `(p,q)` (a sublevel set of a convex
quadratic).  `E₁` is the intersection over all such `(c,s)`, hence convex.
We prove each piece convex *directly* from the definition (midpoint inequality is
`nlinarith` on `(p₁-p₂)² ≥ 0`), avoiding the `ConvexOn` composition machinery. -/

/-- One boundary constraint cuts out a convex set in the center plane. -/
theorem convex_constraint (u v c s : ℝ) (hu : 0 < u) (hv : 0 < v) :
    Convex ℝ {z : ℝ × ℝ | (z.1 + c) ^ 2 / u + (z.2 + s) ^ 2 / v ≤ 1} := by
  intro x hx y hy a b ha hb hab
  simp only [Set.mem_setOf_eq] at hx hy ⊢
  -- a•x + b•y has coordinates (a x.1 + b y.1, a x.2 + b y.2)
  have hx1 : (a • x + b • y).1 = a * x.1 + b * y.1 := by
    simp [Prod.smul_def, smul_eq_mul]
  have hx2 : (a • x + b • y).2 = a * x.2 + b * y.2 := by
    simp [Prod.smul_def, smul_eq_mul]
  rw [hx1, hx2]
  -- per-coordinate convexity of t ↦ (t+c)²/u (and (t+s)²/v), as numerator inequalities.
  -- The gap a·(x+c)² + b·(y+c)² − (ax+by+c)² = ab(x−y)² ≥ 0 (using a+b=1).
  have key1 : (a * x.1 + b * y.1 + c) ^ 2
      ≤ a * (x.1 + c) ^ 2 + b * (y.1 + c) ^ 2 := by
    have hgap : a * (x.1 + c) ^ 2 + b * (y.1 + c) ^ 2 - (a * x.1 + b * y.1 + c) ^ 2
        = a * b * (x.1 - y.1) ^ 2 := by
      have : b = 1 - a := by linarith
      rw [this]; ring
    nlinarith [hgap, mul_nonneg (mul_nonneg ha hb) (sq_nonneg (x.1 - y.1))]
  have key2 : (a * x.2 + b * y.2 + s) ^ 2
      ≤ a * (x.2 + s) ^ 2 + b * (y.2 + s) ^ 2 := by
    have hgap : a * (x.2 + s) ^ 2 + b * (y.2 + s) ^ 2 - (a * x.2 + b * y.2 + s) ^ 2
        = a * b * (x.2 - y.2) ^ 2 := by
      have : b = 1 - a := by linarith
      rw [this]; ring
    nlinarith [hgap, mul_nonneg (mul_nonneg ha hb) (sq_nonneg (x.2 - y.2))]
  -- convert numerator inequalities to the divided form (u, v > 0).
  have conv1 : (a * x.1 + b * y.1 + c) ^ 2 / u
      ≤ a * ((x.1 + c) ^ 2 / u) + b * ((y.1 + c) ^ 2 / u) := by
    rw [show a * ((x.1 + c) ^ 2 / u) + b * ((y.1 + c) ^ 2 / u)
          = (a * (x.1 + c) ^ 2 + b * (y.1 + c) ^ 2) / u by ring]
    exact div_le_div_of_nonneg_right key1 hu.le
  have conv2 : (a * x.2 + b * y.2 + s) ^ 2 / v
      ≤ a * ((x.2 + s) ^ 2 / v) + b * ((y.2 + s) ^ 2 / v) := by
    rw [show a * ((x.2 + s) ^ 2 / v) + b * ((y.2 + s) ^ 2 / v)
          = (a * (x.2 + s) ^ 2 + b * (y.2 + s) ^ 2) / v by ring]
    exact div_le_div_of_nonneg_right key2 hv.le
  -- combine: a·(≤1) + b·(≤1) ≤ a + b = 1.
  have ax : a * ((x.1 + c) ^ 2 / u + (x.2 + s) ^ 2 / v) ≤ a * 1 :=
    mul_le_mul_of_nonneg_left hx ha
  have by' : b * ((y.1 + c) ^ 2 / u + (y.2 + s) ^ 2 / v) ≤ b * 1 :=
    mul_le_mul_of_nonneg_left hy hb
  nlinarith [conv1, conv2, ax, by', hab]

/-- `E₁` is convex (intersection of the convex boundary constraints). -/
theorem convex_E₁ (u v : ℝ) (hu : 0 < u) (hv : 0 < v) :
    Convex ℝ (E₁ u v) := by
  -- E₁ = ⋂ over (c,s) with c²+s²=1 of the convex constraints.
  have hEq : E₁ u v =
      ⋂ (cs : ℝ × ℝ) (_ : cs.1 ^ 2 + cs.2 ^ 2 = 1),
        {z : ℝ × ℝ | (z.1 + cs.1) ^ 2 / u + (z.2 + cs.2) ^ 2 / v ≤ 1} := by
    ext z
    simp only [E₁, fits, Set.mem_setOf_eq, Set.mem_iInter]
    constructor
    · intro h cs hcs
      exact h cs.1 cs.2 hcs
    · intro h c s hcs
      exact h (c, s) hcs
  rw [hEq]
  apply convex_iInter
  intro cs
  apply convex_iInter
  intro _
  exact convex_constraint u v cs.1 cs.2 hu hv

/-! ## 2a-ii: central symmetry of `E₁`

`fits` depends only on `p²` and `q²` (the constraint set `{(c,s) : c²+s²=1}` is symmetric
under `c ↦ -c`, `s ↦ -s`), so `fits u v p q ↔ fits u v (-p) (-q)`.  Hence `E₁` is
symmetric about the origin: `z ∈ E₁ ↔ -z ∈ E₁`. -/

/-- `fits` is invariant under negating the center (central symmetry).
The boundary circle is reflection-symmetric, so we reflect the witness `(c,s) ↦ (-c,-s)`. -/
theorem fits_neg (u v p q : ℝ) : fits u v p q ↔ fits u v (-p) (-q) := by
  have hcirc : ∀ c s : ℝ, c ^ 2 + s ^ 2 = 1 → (-c) ^ 2 + (-s) ^ 2 = 1 := by
    intro c s h; nlinarith [h]
  constructor
  · intro h c s hcs
    have h' := h (-c) (-s) (hcirc c s hcs)
    calc (-p + c) ^ 2 / u + (-q + s) ^ 2 / v
        = (p + -c) ^ 2 / u + (q + -s) ^ 2 / v := by ring_nf
      _ ≤ 1 := h'
  · intro h c s hcs
    have h' := h (-c) (-s) (hcirc c s hcs)
    calc (p + c) ^ 2 / u + (q + s) ^ 2 / v
        = (-p + -c) ^ 2 / u + (-q + -s) ^ 2 / v := by ring
      _ ≤ 1 := h'

/-- Central symmetry of `E₁`. -/
theorem E₁_symm (u v : ℝ) (z : ℝ × ℝ) : z ∈ E₁ u v ↔ -z ∈ E₁ u v := by
  simp only [E₁, Set.mem_setOf_eq, Prod.fst_neg, Prod.snd_neg]
  exact fits_neg u v z.1 z.2

/-- The origin is in `E₁` provided `v ≥ 1` (a single unit disk centered at the origin
fits when the minor semi-axis `b = √v ≥ 1`). -/
theorem origin_mem_E₁ (u v : ℝ) (_hu : 0 < u) (hv : 0 < v) (hv1 : 1 ≤ v)
    (huv : v ≤ u) : (0, 0) ∈ E₁ u v := by
  simp only [E₁, fits, Set.mem_setOf_eq]
  intro c s hcs
  -- (0+c)²/u + (0+s)²/v = c²/u + s²/v ≤ c²/v + s²/v = 1/v ≤ 1
  have hc2 : (0 + c) ^ 2 = c ^ 2 := by ring
  have hs2 : (0 + s) ^ 2 = s ^ 2 := by ring
  rw [hc2, hs2]
  have h1 : c ^ 2 / u ≤ c ^ 2 / v :=
    div_le_div_of_nonneg_left (sq_nonneg c) hv huv
  have h2 : c ^ 2 / v + s ^ 2 / v = 1 / v := by
    rw [← add_div, hcs]
  have h3 : (1 : ℝ) / v ≤ 1 := by
    rw [div_le_one hv]; exact hv1
  calc c ^ 2 / u + s ^ 2 / v ≤ c ^ 2 / v + s ^ 2 / v := by linarith
    _ = 1 / v := h2
    _ ≤ 1 := h3

end Ellipse
