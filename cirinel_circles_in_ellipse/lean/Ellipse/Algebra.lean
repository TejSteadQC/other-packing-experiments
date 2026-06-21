import Mathlib.Tactic

/-!
# Algebraic spine of the "smallest ellipse containing two unit circles" proof

This file contains the *algebraic* lemmas of the proof (Steps 2c, 3, 4, 5 of
`proof_ellipse_n2.tex`), each a standalone `ring`/`nlinarith`/`positivity` fact.
The analytic reduction (Step 2: convexity of the erosion set) lives in `Ellipse.Convex`.

Throughout, `u = a²` (square of the semi-major axis) and `v = b²` (semi-minor),
with `u ≥ v > 0`.  A unit disk centered at `(p,q)` "fits" inside the ellipse
`{(x,y) | x²/u + y²/v ≤ 1}` iff every boundary point of the disk is inside.
-/

namespace Ellipse

/-- A unit disk centered at `(p, q)` *fits* inside the ellipse `x²/u + y²/v ≤ 1`
iff every boundary point `(p+c, q+s)` (with `c²+s²=1`) lies in the ellipse.
(For a convex ellipse, the whole disk is inside iff its boundary circle is.) -/
def fits (u v p q : ℝ) : Prop :=
  ∀ c s : ℝ, c ^ 2 + s ^ 2 = 1 → (p + c) ^ 2 / u + (q + s) ^ 2 / v ≤ 1

/-- The S-procedure cubic in the multiplier `λ` for a disk centered at `(p,q)`.
`N` is the value, scaled by `uv`, that controls global nonnegativity of the
Lagrangian `1 - g + λ(c²+s²-1)`.  Only `p²` and `q²` enter, via `P := p²`, `Q := q²`. -/
def Ncubic (u v P Q lam : ℝ) : ℝ :=
  -lam ^ 3 * u * v - lam ^ 2 * (P * v + Q * u) + lam ^ 2 * (u * v + u + v)
    + lam * (P + Q - u - v - 1) + 1

/-! ## Lemma 1: the easy (sufficient) direction of the S-procedure

If the Lagrangian `1 - g + λ(c²+s²-1)` is globally `≥ 0`, then the disk fits.
The load-bearing fact is the exact ring identity
`(1 - g + λ(c²+s²-1)) - (1 - g) = λ(c²+s²-1)`, so on the circle `c²+s²=1` the
Lagrangian equals `1 - g`. -/

/-- The exact ring identity underlying the easy S-procedure direction. -/
theorem lagrangian_identity (u v p q c s lam : ℝ) :
    (1 - ((p + c) ^ 2 / u + (q + s) ^ 2 / v) + lam * (c ^ 2 + s ^ 2 - 1))
      - (1 - ((p + c) ^ 2 / u + (q + s) ^ 2 / v))
      = lam * (c ^ 2 + s ^ 2 - 1) := by
  ring

/-- Easy direction: a global PSD certificate `λ` for the Lagrangian implies `fits`. -/
theorem fits_of_lagrangian (u v p q : ℝ)
    (lam : ℝ)
    (hPSD : ∀ c s : ℝ,
      0 ≤ 1 - ((p + c) ^ 2 / u + (q + s) ^ 2 / v) + lam * (c ^ 2 + s ^ 2 - 1)) :
    fits u v p q := by
  intro c s hcs
  have h := hPSD c s
  -- on the circle, λ(c²+s²-1) = 0, so the Lagrangian *equals* 1 - g.
  have hzero : lam * (c ^ 2 + s ^ 2 - 1) = 0 := by
    rw [hcs]; ring
  rw [hzero] at h
  linarith

/-! ## Lemma 2 (Step 2c): the major-axis unit vector is the easiest

The exact ring identity `N(unit;β) - N((1,0)) = -β·λ²·(u-v)`, where a unit vector
center has `p² = 1-β`, `q² = β`.  Hence for `u ≥ v` and `β ≥ 0` the cubic for a
unit-vector center never exceeds the cubic for `(1,0)`. -/

/-- The Step 2c identity (exact, `ring`): the difference of the S-cubic at a
unit-vector center `(P,Q) = (1-β, β)` and at `(1,0)` is `-β λ² (u-v)`. -/
theorem Ncubic_unit_sub_axis (u v beta lam : ℝ) :
    Ncubic u v (1 - beta) beta lam - Ncubic u v 1 0 lam
      = -beta * lam ^ 2 * (u - v) := by
  unfold Ncubic
  ring

/-- Step 2c, sign form: for `u ≥ v` and `β ≥ 0`, the unit-vector cubic is `≤` the
`(1,0)` cubic, for every `λ`. -/
theorem Ncubic_unit_le_axis (u v beta lam : ℝ)
    (huv : v ≤ u) (hbeta : 0 ≤ beta) :
    Ncubic u v (1 - beta) beta lam ≤ Ncubic u v 1 0 lam := by
  have hid := Ncubic_unit_sub_axis u v beta lam
  nlinarith [sq_nonneg lam, mul_nonneg hbeta (sq_nonneg lam), huv, hbeta]

/-! ## Lemma 3 (Step 3): containment condition for the disk at `(1,0)`

`fits u v 1 0` means the parabola `g(c) = (1+c)²/u + (1-c²)/v ≤ 1` for all
`c ∈ [-1,1]`.  We extract the two regime inequalities by plugging in witness points. -/

/-- Regime (i) extraction: if `fits u v 1 0` with the vertex `c* = v/(u-v)` in
range (`u ≥ 2v`, which makes `(c*)² ≤ 1`), then `(u-v)(v-1) ≥ v`.
We plug the boundary point `c = v/(u-v)`, `s = √(1-c²)`. -/
theorem regimeI_of_fits (u v : ℝ) (hv : 0 < v) (hu2v : 2 * v ≤ u)
    (hfits : fits u v 1 0) : v ≤ (u - v) * (v - 1) := by
  have hvu : v < u := by linarith
  have huv0 : 0 < u - v := by linarith
  set cstar : ℝ := v / (u - v) with hc
  -- c* ∈ [0,1]: c* ≥ 0 and c* ≤ 1 (the latter from u ≥ 2v).
  have hcstar_nonneg : 0 ≤ cstar := by
    rw [hc]; positivity
  have hcstar_le1 : cstar ≤ 1 := by
    rw [hc, div_le_one huv0]; linarith
  -- so 1 - c*² ≥ 0, choose s = √(1 - c*²).
  have hsq : 0 ≤ 1 - cstar ^ 2 := by nlinarith [hcstar_le1, hcstar_nonneg]
  set s : ℝ := Real.sqrt (1 - cstar ^ 2) with hs
  have hs2 : s ^ 2 = 1 - cstar ^ 2 := by
    rw [hs, Real.sq_sqrt hsq]
  have hcirc : cstar ^ 2 + s ^ 2 = 1 := by rw [hs2]; ring
  have h := hfits cstar s hcirc
  -- h : (1+c*)²/u + (0+s)²/v ≤ 1.  Substitute s² and clear denominators.
  rw [show (1 : ℝ) + cstar = 1 + cstar from rfl] at h
  have hu0 : 0 < u := by linarith
  -- (1+c*)²/u + s²/v ≤ 1  with s² = 1 - c*²
  have hkey : (1 + cstar) ^ 2 / u + (0 + s) ^ 2 / v ≤ 1 := h
  have hs2' : (0 + s) ^ 2 = 1 - cstar ^ 2 := by rw [zero_add]; exact hs2
  rw [hs2'] at hkey
  -- multiply through by u*v > 0:  v(1+c*)² + u(1-c*²) ≤ uv
  have hmul : v * (1 + cstar) ^ 2 + u * (1 - cstar ^ 2) ≤ u * v := by
    have e1 : (1 + cstar) ^ 2 / u * (u * v) = v * (1 + cstar) ^ 2 := by
      field_simp
    have e2 : (1 - cstar ^ 2) / v * (u * v) = u * (1 - cstar ^ 2) := by
      field_simp
    have := mul_le_mul_of_nonneg_right hkey (by positivity : (0:ℝ) ≤ u * v)
    -- this : ((1+c*)²/u + (1-c*²)/v) * (uv) ≤ 1 * (uv)
    calc v * (1 + cstar) ^ 2 + u * (1 - cstar ^ 2)
        = (1 + cstar) ^ 2 / u * (u * v) + (1 - cstar ^ 2) / v * (u * v) := by
          rw [e1, e2]
      _ = ((1 + cstar) ^ 2 / u + (1 - cstar ^ 2) / v) * (u * v) := by ring
      _ ≤ 1 * (u * v) := this
      _ = u * v := by ring
  -- now substitute c* = v/(u-v) and simplify to (u-v)(v-1) ≥ v.
  -- Express everything over (u-v): cstar*(u-v) = v.
  have hcv : cstar * (u - v) = v := by
    rw [hc]; field_simp
  -- multiply hmul by (u-v)² > 0 and use hcv to eliminate the fraction.
  have hd2 : 0 < (u - v) ^ 2 := by positivity
  nlinarith [mul_le_mul_of_nonneg_right hmul (le_of_lt hd2), hcv,
    sq_nonneg (u - v), hu0, hv, huv0]

/-- Regime (ii) extraction: if `fits u v 1 0` then `u ≥ 4` (plug `c = 1`, `s = 0`,
the far vertex `(2,0)`). This holds in *both* regimes; it is the binding one when
`u < 2v`. -/
theorem far_vertex_of_fits (u v : ℝ) (hfits : fits u v 1 0) :
    (4 : ℝ) / u ≤ 1 := by
  have h := hfits 1 0 (by ring)
  -- (1+1)²/u + (0+0)²/v ≤ 1  ⟹  4/u ≤ 1
  have h' : (1 + 1 : ℝ) ^ 2 / u + (0 + 0) ^ 2 / v ≤ 1 := h
  have e : (1 + 1 : ℝ) ^ 2 / u + (0 + 0) ^ 2 / v = 4 / u := by ring
  rw [e] at h'
  exact h'

theorem u_ge_four_of_fits (u v : ℝ) (hu : 0 < u) (hfits : fits u v 1 0) :
    (4 : ℝ) ≤ u := by
  have h := far_vertex_of_fits u v hfits
  rw [div_le_one hu] at h
  linarith

/-! ## Lemma 4 (Step 4): the polynomial minimization `uv ≥ 27/4`

The heart: `4v³ - 27v + 27 = (2v-3)²(v+3) ≥ 0`, giving `v³/(v-1) ≥ 27/4` on `v>1`.
We feed the regime inequalities to `nlinarith`. -/

/-- The core SOS factorization, an exact `ring` identity. -/
theorem core_factor (v : ℝ) :
    4 * v ^ 3 - 27 * v + 27 = (2 * v - 3) ^ 2 * (v + 3) := by ring

/-- In regime (i): the constraints `(u-v)(v-1) ≥ v`, `u ≥ 2v`, `v > 1` force
`uv ≥ 27/4`. -/
theorem uv_ge_regimeI (u v : ℝ) (hv1 : 1 < v) (hu2v : 2 * v ≤ u)
    (hcon : v ≤ (u - v) * (v - 1)) : (27 : ℝ) / 4 ≤ u * v := by
  -- From hcon: u(v-1) ≥ v², i.e. u ≥ v²/(v-1).  So uv ≥ v³/(v-1) ≥ 27/4.
  have hv0 : 0 < v - 1 := by linarith
  -- u ≥ v²/(v-1):  (u-v)(v-1) ≥ v ⟺ uv - v² - u + v ≥ v ⟺ u(v-1) ≥ v².
  have hu_lb : v ^ 2 ≤ u * (v - 1) := by nlinarith [hcon]
  -- multiply by v>0: uv(v-1) ≥ v³.  And 4v³ - 27(v-1) = (2v-3)²(v+3) ≥ 0.
  have hsos : 0 ≤ (2 * v - 3) ^ 2 * (v + 3) := by positivity
  have hv : 0 < v := by linarith
  nlinarith [mul_le_mul_of_nonneg_left hu_lb (le_of_lt hv), hsos,
    core_factor v, hv0, hv, mul_pos hv hv0]

/-- In regime (ii): `u ≥ 4` and `u < 2v` force `uv > 8 ≥ 27/4`. -/
theorem uv_ge_regimeII (u v : ℝ) (hu4 : 4 ≤ u) (huv : u < 2 * v) :
    (27 : ℝ) / 4 ≤ u * v := by
  -- v > u/2 ≥ 2, so uv > 4*2 = 8 > 27/4.
  nlinarith [hu4, huv]

/-! ## The lower bound assembled: `fits u v 1 0` with `u ≥ v > 0` ⟹ `uv ≥ 27/4`.

This is Step 5's lower bound, combining the regime split. Note `fits` also forces
`v ≥ 1` (a unit disk centered at `(1,0)` needs the minor axis `≥ 1`); we derive the
needed `v > 1` strictness within each regime. -/

/-- A unit disk centered at `(1,0)` fitting forces `v ≥ 1`: plug the side point
`c = 0`, `s = 1`, giving `1/u + 1/v ≤ 1`, hence `v > 1` (since also `u` finite).
Actually we get the sharper `1/u + 1/v ≤ 1`. -/
theorem side_point_of_fits (u v : ℝ) (hfits : fits u v 1 0) :
    (1 : ℝ) / u + 1 / v ≤ 1 := by
  have h := hfits 0 1 (by ring)
  -- (1+0)²/u + (0+1)²/v ≤ 1
  have h' : (1 + 0 : ℝ) ^ 2 / u + (0 + 1) ^ 2 / v ≤ 1 := h
  have e : (1 + 0 : ℝ) ^ 2 / u + (0 + 1) ^ 2 / v = 1 / u + 1 / v := by ring
  rw [e] at h'
  exact h'

/-- **Lower bound (Step 5).** If a unit disk centered at `(1,0)` fits in the
ellipse `x²/u + y²/v ≤ 1` with `u ≥ v > 0`, then `uv ≥ 27/4`. -/
theorem uv_ge_of_fits (u v : ℝ) (hv : 0 < v) (huv : v ≤ u)
    (hfits : fits u v 1 0) : (27 : ℝ) / 4 ≤ u * v := by
  have hu : 0 < u := by linarith
  -- v > 1: from the side point 1/u + 1/v ≤ 1 and 0 < 1/u, we get 1/v < 1, so v > 1.
  have hside := side_point_of_fits u v hfits
  have hv1 : 1 < v := by
    by_contra h
    rw [not_lt] at h  -- v ≤ 1
    -- then 1/v ≥ 1, and 1/u > 0, contradicting 1/u + 1/v ≤ 1.
    have h1v : 1 ≤ 1 / v := by rw [le_div_iff₀ hv]; nlinarith
    have h1u : 0 < 1 / u := by positivity
    linarith
  rcases le_or_gt (2 * v) u with hge | hlt
  · -- regime (i)
    have hcon := regimeI_of_fits u v hv hge hfits
    exact uv_ge_regimeI u v hv1 hge hcon
  · -- regime (ii): u < 2v
    have hu4 := u_ge_four_of_fits u v hu hfits
    exact uv_ge_regimeII u v hu4 hlt

/-! ## Lemma 5 (Step 5): the construction certificate (upper bound)

At `u = 9/2`, `v = 3/2`, the certificate `27/4·(1-g(c)) = 3(c - 1/2)²` shows the
disk at `(1,0)` fits, with equality (tangency) only at `c = 1/2`. -/

/-- The exact tangency certificate `ring` identity at the optimum. -/
theorem tangency_certificate (c : ℝ) :
    (27 / 4 : ℝ) * (1 - ((1 + c) ^ 2 / (9 / 2) + (1 - c ^ 2) / (3 / 2)))
      = 3 * (c - 1 / 2) ^ 2 := by
  ring

/-- **Upper bound (construction).** The unit disk centered at `(1,0)` fits inside
the optimal ellipse `x²/(9/2) + y²/(3/2) ≤ 1`. -/
theorem fits_optimal : fits (9 / 2) (3 / 2) 1 0 := by
  intro c s hcs
  -- replace s² by 1 - c²
  have hs2 : s ^ 2 = 1 - c ^ 2 := by linarith [hcs]
  -- goal: (1+c)²/(9/2) + (0+s)²/(3/2) ≤ 1
  have hcert := tangency_certificate c
  have hsq : 0 ≤ 3 * (c - 1 / 2) ^ 2 := by positivity
  -- (0+s)² = s² = 1 - c²
  have hzero_add : (0 + s) ^ 2 = 1 - c ^ 2 := by rw [zero_add]; exact hs2
  rw [hzero_add]
  nlinarith [hcert, hsq]

end Ellipse
