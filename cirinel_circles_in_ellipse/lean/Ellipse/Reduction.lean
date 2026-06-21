import Ellipse.Convex

/-!
# Step 2b/2c/2d: from convexity to `fits (1,0)`

* **2b** (`unitVec_mem_E₁_of_two`): if `E₁` contains two points at (Euclidean)
  distance `≥ 2`, then — using convexity, central symmetry, and `O ∈ E₁` — it
  contains a *unit vector*.  Fully proved.
* **2c** (`fits_axis_of_fits_unitVec`): if a unit-vector center fits, the `(1,0)`
  center fits.  This is the rotation argument of the hand-proof, here formalized
  *algebraically* (rotation inequality at cone points + explicit S-procedure
  multipliers).  **Fully proved** — see the note above the theorem.
* **2d** (`fits_axis_of_two_disjoint`): combine 2b+2c.
-/

namespace Ellipse

open Set

/-- Euclidean squared norm on `ℝ × ℝ` (NOT the sup-metric one). -/
def nrm2 (z : ℝ × ℝ) : ℝ := z.1 ^ 2 + z.2 ^ 2

/-- Scalar multiple lands in coordinates as expected. -/
theorem smul_coords (t : ℝ) (z : ℝ × ℝ) :
    (t • z).1 = t * z.1 ∧ (t • z).2 = t * z.2 := by
  constructor <;> simp [Prod.smul_def, smul_eq_mul]

/-! ## 2b: convexity + symmetry force a unit vector into `E₁` -/

/-- **Step 2b.** If `E₁` contains the origin and two points `p, q` with Euclidean
distance `≥ 2` (i.e. `nrm2 (p - q) ≥ 4`), then `E₁` contains a unit vector. -/
theorem unitVec_mem_E₁_of_two (u v : ℝ) (hu : 0 < u) (hv : 0 < v)
    (hO : (0, 0) ∈ E₁ u v)
    (p q : ℝ × ℝ) (hp : p ∈ E₁ u v) (hq : q ∈ E₁ u v)
    (hdist : 4 ≤ nrm2 (p - q)) :
    ∃ m : ℝ × ℝ, nrm2 m = 1 ∧ m ∈ E₁ u v := by
  have hconv := convex_E₁ u v hu hv
  -- -p ∈ E₁ (central symmetry)
  have hnp : -p ∈ E₁ u v := (E₁_symm u v p).1 hp
  -- midpoint w = (1/2)•q + (1/2)•(-p) ∈ E₁
  have hw : (1/2 : ℝ) • q + (1/2 : ℝ) • (-p) ∈ E₁ u v :=
    hconv hq hnp (by norm_num) (by norm_num) (by norm_num)
  set w : ℝ × ℝ := (1/2 : ℝ) • q + (1/2 : ℝ) • (-p) with hwdef
  -- coordinates of w: w = (1/2)(q - p)
  have hw1 : w.1 = (q.1 - p.1) / 2 := by
    simp only [hwdef, Prod.fst_add, (smul_coords _ _).1, Prod.fst_neg]; ring
  have hw2 : w.2 = (q.2 - p.2) / 2 := by
    simp only [hwdef, Prod.snd_add, (smul_coords _ _).2, Prod.snd_neg]; ring
  -- nrm2 w = (1/4) nrm2 (p - q) ≥ 1
  have hnw : nrm2 w = nrm2 (p - q) / 4 := by
    simp only [nrm2, hw1, hw2, Prod.fst_sub, Prod.snd_sub]; ring
  have hnw1 : 1 ≤ nrm2 w := by rw [hnw]; linarith
  -- w ≠ 0
  have hwpos : 0 < nrm2 w := by linarith
  have hwne : Real.sqrt (nrm2 w) ≠ 0 := by
    positivity
  set r : ℝ := Real.sqrt (nrm2 w) with hrdef
  have hr2 : r ^ 2 = nrm2 w := by rw [hrdef, Real.sq_sqrt (le_of_lt hwpos)]
  have hrpos : 0 < r := Real.sqrt_pos.mpr hwpos
  -- m := (1/r) • w is a unit vector and lies on segment [O, w] ⊆ E₁.
  set m : ℝ × ℝ := (1 / r) • w with hmdef
  have hm1 : m.1 = w.1 / r := by simp only [hmdef, (smul_coords _ _).1]; ring
  have hm2 : m.2 = w.2 / r := by simp only [hmdef, (smul_coords _ _).2]; ring
  have hmunit : nrm2 m = 1 := by
    simp only [nrm2, hm1, hm2, div_pow]
    rw [← add_div, ← nrm2, hr2]
    exact div_self (ne_of_gt hwpos)
  refine ⟨m, hmunit, ?_⟩
  -- m is a convex combination of O and w (since 0 ≤ 1/r ≤ 1, because r ≥ 1).
  have hr_ge1 : 1 ≤ r := by
    have : (1:ℝ) ≤ r ^ 2 := by rw [hr2]; exact hnw1
    nlinarith [hrpos, this]
  -- write m = (1 - 1/r)•O + (1/r)•w  with coefficients in [0,1].
  have hcoef0 : 0 ≤ 1 / r := by positivity
  have hcoef1 : 1 / r ≤ 1 := by rw [div_le_one hrpos]; exact hr_ge1
  have hmem : (1 - 1 / r) • ((0:ℝ),(0:ℝ)) + (1 / r) • w ∈ E₁ u v :=
    hconv hO hw (by linarith) hcoef0 (by ring)
  have heq : (1 - 1 / r) • ((0:ℝ),(0:ℝ)) + (1 / r) • w = m := by
    rw [hmdef]
    rw [show ((0:ℝ),(0:ℝ)) = (0 : ℝ × ℝ) from rfl, smul_zero, zero_add]
  rwa [heq] at hmem

/-! ## 2c: the major-axis vector is easiest (CLOSED)

The hand-proof's rotation argument (Step 2c of `proof_ellipse_n2.tex`), formalized
*algebraically*.  The key idea is a **rotation inequality at chosen cone points**:
for a fitting first-quadrant unit vector `m = (m₁,m₂)`, and any point `B₀ = (bx, by)` on
the boundary circle of the `(1,0)`-disk lying in the cone `bx ≥ by ≥ 0`, rotating `B₀`
by the angle of `m` lands on the `m`-disk boundary and *does not decrease* `Q`:
    `Q(B₀) ≤ Q(R_φ B₀) ≤ 1`   (the second `≤` is `fits m`).
This is `rotation_ge`/`cone_point_le_one` below — the rotation inequality is the exact
identity
    `Q(R_φ B₀) − Q(B₀) = (u−v)·m₂·[(bx²−by²)·m₂ + 2·bx·by·m₁] / (u v) ≥ 0`,
sign-definite precisely on the cone `bx ≥ by ≥ 0` with `m₁,m₂ ≥ 0` (so this is NOT the
naive pointwise rotation witness, which fails off the cone).

Applying this at the cone points `(2,0)` (far vertex) and `(1+c*, s*)` (`c* = v/(u−v)`,
the regime-i maximizer, which lies in the cone since `c* ≥ 0`) extracts the three scalar
facts `u ≥ 4` and — when `u ≥ 2v` — `(u−v)(v−1) ≥ v`.  These conditions are then
*sufficient* for `fits u v 1 0` via the easy S-procedure direction `fits_of_lagrangian`
with the explicit multipliers `λ = 1/v` (regime i) and `λ = 2/u` (regime ii):
    regime i:  `(u−v)·uv·H = ((u−v)c − v)² + u·((u−v)(v−1) − v) ≥ 0`,
    regime ii: `uv·H = v(c−1)² + (2v−u)s² + v(u−4) ≥ 0`.
General `m` is reduced to the first quadrant by the reflection symmetries `fits_reflect_*`
(the extracted facts depend only on `u, v`). -/

/-- `fits` at `(p,q)` gives `fits` at `(-p, q)` (reflect the witness `c ↦ -c`). -/
theorem fits_reflect_fst (u v p q : ℝ) (h : fits u v p q) : fits u v (-p) q := by
  intro c s hcs
  have hcs' : (-c) ^ 2 + s ^ 2 = 1 := by nlinarith [hcs]
  have := h (-c) s hcs'
  calc (-p + c) ^ 2 / u + (q + s) ^ 2 / v
      = (p + -c) ^ 2 / u + (q + s) ^ 2 / v := by ring_nf
    _ ≤ 1 := this

/-- `fits` at `(p,q)` gives `fits` at `(p, -q)` (reflect the witness `s ↦ -s`). -/
theorem fits_reflect_snd (u v p q : ℝ) (h : fits u v p q) : fits u v p (-q) := by
  intro c s hcs
  have hcs' : c ^ 2 + (-s) ^ 2 = 1 := by nlinarith [hcs]
  have := h c (-s) hcs'
  calc (p + c) ^ 2 / u + (-q + s) ^ 2 / v
      = (p + c) ^ 2 / u + (q + -s) ^ 2 / v := by ring_nf
    _ ≤ 1 := this

/-- `fits` at `(p,q)` gives `fits` at `(|p|, |q|)`. -/
theorem fits_abs (u v p q : ℝ) (h : fits u v p q) : fits u v |p| |q| := by
  rcases abs_choice p with hp | hp <;> rcases abs_choice q with hq | hq <;> rw [hp, hq]
  · exact h
  · exact fits_reflect_snd u v p q h
  · exact fits_reflect_fst u v p q h
  · exact fits_reflect_snd u v (-p) q (fits_reflect_fst u v p q h)

/-- The key rotation identity. With `R_φ B₀ = (m₁·bx − m₂·by, m₂·bx + m₁·by)` (rotation
by the angle of the unit vector `m = (m₁,m₂)`), the change in `Q`, cleared by `uv`, is
`(u−v)·m₂·[(bx²−by²)·m₂ + 2·bx·by·m₁]`. -/
theorem rotation_identity (u v m1 m2 bx by_ : ℝ) (hu : 0 < u) (hv : 0 < v)
    (hm : m1 ^ 2 + m2 ^ 2 = 1) :
    ((m1 * bx - m2 * by_) ^ 2 / u + (m2 * bx + m1 * by_) ^ 2 / v)
      - (bx ^ 2 / u + by_ ^ 2 / v)
      = (u - v) * m2 * ((bx ^ 2 - by_ ^ 2) * m2 + 2 * bx * by_ * m1) / (u * v) := by
  field_simp
  linear_combination (bx ^ 2 * v + by_ ^ 2 * u) * hm

/-- **Rotation inequality.** For `u ≥ v > 0`, `m₁,m₂ ≥ 0` on the unit circle, and a cone
point `B₀ = (bx, by)` with `bx ≥ by ≥ 0`, rotating `B₀` by the angle of `m` does not
decrease `Q`: `Q(B₀) ≤ Q(R_φ B₀)`. -/
theorem rotation_ge (u v m1 m2 bx by_ : ℝ) (hu : 0 < u) (hv : 0 < v) (huv : v ≤ u)
    (hm : m1 ^ 2 + m2 ^ 2 = 1) (hm1 : 0 ≤ m1) (hm2 : 0 ≤ m2)
    (hby : 0 ≤ by_) (hbxby : by_ ≤ bx) :
    bx ^ 2 / u + by_ ^ 2 / v
      ≤ (m1 * bx - m2 * by_) ^ 2 / u + (m2 * bx + m1 * by_) ^ 2 / v := by
  have hid := rotation_identity u v m1 m2 bx by_ hu hv hm
  have hbx : 0 ≤ bx := le_trans hby hbxby
  have hbracket : 0 ≤ (bx ^ 2 - by_ ^ 2) * m2 + 2 * bx * by_ * m1 := by
    have h1 : 0 ≤ (bx ^ 2 - by_ ^ 2) * m2 := by
      apply mul_nonneg _ hm2
      nlinarith [hbxby, hby, hbx]
    have h2 : 0 ≤ 2 * bx * by_ * m1 := by positivity
    linarith
  have hnum : 0 ≤ (u - v) * m2 * ((bx ^ 2 - by_ ^ 2) * m2 + 2 * bx * by_ * m1) := by
    apply mul_nonneg
    apply mul_nonneg (by linarith) hm2
    exact hbracket
  have hpos : 0 < u * v := mul_pos hu hv
  have : 0 ≤ (u - v) * m2 * ((bx ^ 2 - by_ ^ 2) * m2 + 2 * bx * by_ * m1) / (u * v) :=
    div_nonneg hnum hpos.le
  linarith [hid]

/-- A cone point `B₀ = (bx, by)` on the boundary circle of the `(1,0)`-disk
(`(bx−1)² + by² = 1`) with `bx ≥ by ≥ 0` satisfies `Q(B₀) ≤ 1`, given `fits` at the
first-quadrant unit vector `m`.  The witness `(c,s) = R_φ B₀ − m` is a unit vector and
`m + (c,s) = R_φ B₀`, so `fits m` bounds `Q(R_φ B₀) ≤ 1`; then `rotation_ge` descends to
`Q(B₀)`. -/
theorem cone_point_le_one (u v m1 m2 bx by_ : ℝ) (hu : 0 < u) (hv : 0 < v) (huv : v ≤ u)
    (hm : m1 ^ 2 + m2 ^ 2 = 1) (hm1 : 0 ≤ m1) (hm2 : 0 ≤ m2)
    (hfit : fits u v m1 m2)
    (hcirc : (bx - 1) ^ 2 + by_ ^ 2 = 1)
    (hby : 0 ≤ by_) (hbxby : by_ ≤ bx) :
    bx ^ 2 / u + by_ ^ 2 / v ≤ 1 := by
  set c : ℝ := m1 * bx - m2 * by_ - m1 with hc
  set s : ℝ := m2 * bx + m1 * by_ - m2 with hs
  have hcs : c ^ 2 + s ^ 2 = 1 := by
    have : c ^ 2 + s ^ 2 = (bx - 1) ^ 2 + by_ ^ 2 := by
      rw [hc, hs]; nlinarith [hm]
    rw [this, hcirc]
  have hrot := hfit c s hcs
  have he1 : m1 + c = m1 * bx - m2 * by_ := by rw [hc]; ring
  have he2 : m2 + s = m2 * bx + m1 * by_ := by rw [hs]; ring
  rw [he1, he2] at hrot
  have := rotation_ge u v m1 m2 bx by_ hu hv huv hm hm1 hm2 hby hbxby
  linarith

/-- From `fits` at a first-quadrant unit vector, `u ≥ 4` (cone point = far vertex `(2,0)`). -/
theorem u_ge_four_unit (u v m1 m2 : ℝ) (hu : 0 < u) (hv : 0 < v) (huv : v ≤ u)
    (hm : m1 ^ 2 + m2 ^ 2 = 1) (hm1 : 0 ≤ m1) (hm2 : 0 ≤ m2)
    (hfit : fits u v m1 m2) : (4 : ℝ) ≤ u := by
  have h := cone_point_le_one u v m1 m2 2 0 hu hv huv hm hm1 hm2 hfit
    (by ring) (le_refl 0) (by norm_num)
  have h' : (4 : ℝ) / u ≤ 1 := by
    have : (2 : ℝ) ^ 2 / u + (0:ℝ) ^ 2 / v = 4 / u := by ring
    linarith [this ▸ h]
  rwa [div_le_one hu] at h'

/-- Regime (i) extraction from `fits` at a first-quadrant unit vector: if `u ≥ 2v`, then
`(u−v)(v−1) ≥ v`.  Cone point = the regime-i maximizer `(1+c*, s*)`, `c* = v/(u−v)`. -/
theorem regimeI_cond_unit (u v m1 m2 : ℝ) (hu : 0 < u) (hv : 0 < v) (huv : v ≤ u)
    (hu2v : 2 * v ≤ u)
    (hm : m1 ^ 2 + m2 ^ 2 = 1) (hm1 : 0 ≤ m1) (hm2 : 0 ≤ m2)
    (hfit : fits u v m1 m2) : v ≤ (u - v) * (v - 1) := by
  have huv0 : 0 < u - v := by linarith
  set cstar : ℝ := v / (u - v) with hc
  have hcstar_nonneg : 0 ≤ cstar := by rw [hc]; positivity
  have hcstar_le1 : cstar ≤ 1 := by
    rw [hc, div_le_one huv0]; linarith
  have hsq : 0 ≤ 1 - cstar ^ 2 := by nlinarith [hcstar_le1, hcstar_nonneg]
  set s : ℝ := Real.sqrt (1 - cstar ^ 2) with hs
  have hs2 : s ^ 2 = 1 - cstar ^ 2 := by rw [hs, Real.sq_sqrt hsq]
  have hsnn : 0 ≤ s := Real.sqrt_nonneg _
  have hcircB : ((1 + cstar) - 1) ^ 2 + s ^ 2 = 1 := by rw [hs2]; ring
  have hsle1 : s ≤ 1 := by
    rw [show (1:ℝ) = Real.sqrt 1 by rw [Real.sqrt_one]]
    apply Real.sqrt_le_sqrt; nlinarith [sq_nonneg cstar]
  have hcone : s ≤ 1 + cstar := by linarith
  have hkey := cone_point_le_one u v m1 m2 (1 + cstar) s hu hv huv hm hm1 hm2 hfit
    hcircB hsnn hcone
  have hu0 : 0 < u := hu
  rw [hs2] at hkey
  have hmul : v * (1 + cstar) ^ 2 + u * (1 - cstar ^ 2) ≤ u * v := by
    have e1 : (1 + cstar) ^ 2 / u * (u * v) = v * (1 + cstar) ^ 2 := by field_simp
    have e2 : (1 - cstar ^ 2) / v * (u * v) = u * (1 - cstar ^ 2) := by field_simp
    have hh := mul_le_mul_of_nonneg_right hkey (by positivity : (0:ℝ) ≤ u * v)
    calc v * (1 + cstar) ^ 2 + u * (1 - cstar ^ 2)
        = (1 + cstar) ^ 2 / u * (u * v) + (1 - cstar ^ 2) / v * (u * v) := by rw [e1, e2]
      _ = ((1 + cstar) ^ 2 / u + (1 - cstar ^ 2) / v) * (u * v) := by ring
      _ ≤ 1 * (u * v) := hh
      _ = u * v := by ring
  have hcv : cstar * (u - v) = v := by rw [hc]; field_simp
  have hd2 : 0 < (u - v) ^ 2 := by positivity
  nlinarith [mul_le_mul_of_nonneg_right hmul (le_of_lt hd2), hcv,
    sq_nonneg (u - v), hu0, hv, huv0]

/-- Regime (i) sufficiency, via `λ = 1/v` (needs `u ≥ 2v` so that `u − v > 0`). -/
theorem fits10_regimeI (u v : ℝ) (hu : 0 < u) (hv : 0 < v) (hu2v : 2 * v ≤ u)
    (hcon : v ≤ (u - v) * (v - 1)) : fits u v 1 0 := by
  have huv0 : 0 < u - v := by linarith
  apply fits_of_lagrangian u v 1 0 (1 / v)
  intro c s
  have hHeq : (u - v) * (u * v) *
      (1 - ((1 + c) ^ 2 / u + (0 + s) ^ 2 / v) + (1 / v) * (c ^ 2 + s ^ 2 - 1))
      = ((u - v) * c - v) ^ 2 + u * ((u - v) * (v - 1) - v) := by
    field_simp
    ring
  have hrhs : 0 ≤ ((u - v) * c - v) ^ 2 + u * ((u - v) * (v - 1) - v) := by
    have h2 : 0 ≤ u * ((u - v) * (v - 1) - v) := mul_nonneg hu.le (by linarith)
    have h1 : 0 ≤ ((u - v) * c - v) ^ 2 := sq_nonneg _
    linarith
  have hcoef : 0 < (u - v) * (u * v) := mul_pos huv0 (mul_pos hu hv)
  nlinarith [hHeq, hrhs, hcoef]

/-- Regime (ii) sufficiency, via `λ = 2/u` (needs `u ≤ 2v` and `u ≥ 4`). -/
theorem fits10_regimeII (u v : ℝ) (hu : 0 < u) (hv : 0 < v) (hu2v : u ≤ 2 * v)
    (hu4 : 4 ≤ u) : fits u v 1 0 := by
  apply fits_of_lagrangian u v 1 0 (2 / u)
  intro c s
  have hHeq : (u * v) *
      (1 - ((1 + c) ^ 2 / u + (0 + s) ^ 2 / v) + (2 / u) * (c ^ 2 + s ^ 2 - 1))
      = v * (c - 1) ^ 2 + (2 * v - u) * s ^ 2 + v * (u - 4) := by
    field_simp
    ring
  have hrhs : 0 ≤ v * (c - 1) ^ 2 + (2 * v - u) * s ^ 2 + v * (u - 4) := by
    have h1 : 0 ≤ v * (c - 1) ^ 2 := mul_nonneg hv.le (sq_nonneg _)
    have h2 : 0 ≤ (2 * v - u) * s ^ 2 := mul_nonneg (by linarith) (sq_nonneg _)
    have h3 : 0 ≤ v * (u - 4) := mul_nonneg hv.le (by linarith)
    linarith
  have hcoef : 0 < u * v := mul_pos hu hv
  nlinarith [hHeq, hrhs, hcoef]

/-- **Sufficiency.** The scalar conditions `u ≥ 4` and (`u ≥ 2v → (u−v)(v−1) ≥ v`) imply
`fits u v 1 0`, by the regime split and the easy S-procedure direction. -/
theorem fits10_of_conditions (u v : ℝ) (hu : 0 < u) (hv : 0 < v)
    (hu4 : 4 ≤ u)
    (hregI : 2 * v ≤ u → v ≤ (u - v) * (v - 1)) :
    fits u v 1 0 := by
  rcases le_or_gt (2 * v) u with hge | hlt
  · exact fits10_regimeI u v hu hv hge (hregI hge)
  · exact fits10_regimeII u v hu hv (le_of_lt hlt) hu4

/-- **Step 2c (CLOSED).** The major-axis unit vector `(1,0)` is the easiest unit vector
to contain: `fits u v m.1 m.2 → fits u v 1 0` for unit `m`, `u ≥ v > 0`. -/
theorem fits_axis_of_fits_unitVec (u v : ℝ) (_hu : 0 < u) (_hv : 0 < v) (_huv : v ≤ u)
    (m : ℝ × ℝ) (_hm : nrm2 m = 1) (_hfit : fits u v m.1 m.2) :
    fits u v 1 0 := by
  -- reduce to the first quadrant via the reflection symmetries
  set p := |m.1| with hp
  set q := |m.2| with hq
  have hpq : p ^ 2 + q ^ 2 = 1 := by
    rw [hp, hq, sq_abs, sq_abs]; exact _hm
  have hp0 : 0 ≤ p := abs_nonneg _
  have hq0 : 0 ≤ q := abs_nonneg _
  have hfit' : fits u v p q := fits_abs u v m.1 m.2 _hfit
  -- extract the scalar conditions and conclude via sufficiency
  have hu4 : (4 : ℝ) ≤ u := u_ge_four_unit u v p q _hu _hv _huv hpq hp0 hq0 hfit'
  have hregI : 2 * v ≤ u → v ≤ (u - v) * (v - 1) := fun hge =>
    regimeI_cond_unit u v p q _hu _hv _huv hge hpq hp0 hq0 hfit'
  exact fits10_of_conditions u v _hu _hv hu4 hregI

/-! ## 2d: the full Step-2 reduction -/

/-- **Step 2d.** If `E₁` (with origin and convexity) contains two points ≥ 2 apart,
then the disk at `(1,0)` fits.  Combines 2b and 2c. -/
theorem fits_axis_of_two_disjoint (u v : ℝ) (hu : 0 < u) (hv : 0 < v) (huv : v ≤ u)
    (hO : (0, 0) ∈ E₁ u v)
    (p q : ℝ × ℝ) (hp : p ∈ E₁ u v) (hq : q ∈ E₁ u v)
    (hdist : 4 ≤ nrm2 (p - q)) :
    fits u v 1 0 := by
  obtain ⟨m, hmunit, hmem⟩ := unitVec_mem_E₁_of_two u v hu hv hO p q hp hq hdist
  exact fits_axis_of_fits_unitVec u v hu hv huv m hmunit hmem

end Ellipse
