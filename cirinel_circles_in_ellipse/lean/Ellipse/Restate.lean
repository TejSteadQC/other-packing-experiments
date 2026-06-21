import Ellipse.Strengthen
import Mathlib.LinearAlgebra.Basis.Fin
import Mathlib.LinearAlgebra.Determinant
import Mathlib.LinearAlgebra.Matrix.Determinant.Basic

/-!
# An independent re-statement via an invertible affine map, and its equivalence

This file states the result a **second, independent way** and proves it equivalent to the
matrix/`genDet` formulation, so that two independently-worded specifications are both proved —
strong evidence against a shared spec error.

## The image-form ellipse

An ellipse is the image of the closed unit disk under an invertible linear map `T : ℝ² → ℝ²`,
plus a translation `t`:

```
linEllipseSet a b d e t = { (a*x + b*y + t.1, d*x + e*y + t.2) | x² + y² ≤ 1 }
```

(the linear part is the matrix `T = !![a, b; d, e]`, `det T = a*e - b*d`).  Its area is
`π · |det T|`.  "Contains two interior-disjoint unit disks" is encoded exactly as before
(centers `≥ 2` apart).  The claim: the minimum area over feasible such ellipses is `(3√3/2)·π`.

## Equivalence strategy

For invertible `T` (`Δ := a*e - b*d ≠ 0`), the image of the unit disk is the genuine
`ellipseGenSet A' B' C' t` whose coefficients we compute explicitly from `T⁻¹`:
`A' = (e² + d²)/Δ²`, `C' = (b² + a²)/Δ²`, `B' = -(b*e + a*d)/Δ²`.  Then
`genDet A' B' C' = 1/Δ²` (an exact `ring`/`field_simp` identity), so `1/√genDet = |Δ| = |det T|`
and the areas agree.  Membership in `achievableAreas` (the matrix-form achievable set) therefore
transfers, and the headline `isLeast_minArea` applies verbatim.
-/

namespace Ellipse

open MeasureTheory Set Module

noncomputable section

/-- The image-form ellipse: image of the closed unit disk under `T(x,y) = (a x + b y, d x + e y)`
translated by `t`.  `T = !![a,b; d,e]`, `det T = a*e - b*d`. -/
def linEllipseSet (a b d e : ℝ) (t : ℝ × ℝ) : Set (ℝ × ℝ) :=
  { w : ℝ × ℝ | ∃ x y : ℝ, x ^ 2 + y ^ 2 ≤ 1 ∧
      w = (a * x + b * y + t.1, d * x + e * y + t.2) }

/-- The matrix-form coefficients computed from the inverse of `T = !![a,b; d,e]`
(`Δ = a*e - b*d`). -/
def linA (a b d e : ℝ) : ℝ := (e ^ 2 + d ^ 2) / (a * e - b * d) ^ 2
def linB (a b d e : ℝ) : ℝ := -(b * e + a * d) / (a * e - b * d) ^ 2
def linC (a b d e : ℝ) : ℝ := (b ^ 2 + a ^ 2) / (a * e - b * d) ^ 2

/-- Combine three same-denominator terms (and a doubled middle one) into a single fraction. -/
private theorem combine3 (c1 c2 c3 P Q R S D : ℝ) :
    c1 / D * P + 2 * (c2 / D) * Q * R + c3 / D * S
      = (c1 * P + 2 * c2 * Q * R + c3 * S) / D := by field_simp

/-- **`genDet` of the computed coefficients is `1/Δ²`** (`Δ = a*e - b*d ≠ 0`).  Exact algebra:
`AC - B² = [(e²+d²)(b²+a²) - (be+ad)²]/Δ⁴ = (ae-bd)²/Δ⁴ = 1/Δ²`. -/
theorem genDet_lin (a b d e : ℝ) (hΔ : a * e - b * d ≠ 0) :
    genDet (linA a b d e) (linB a b d e) (linC a b d e) = 1 / (a * e - b * d) ^ 2 := by
  have hΔ2 : (a * e - b * d) ^ 2 ≠ 0 := pow_ne_zero 2 hΔ
  -- write the whole thing over Δ⁴; numerator = (ae-bd)² = Δ².
  rw [genDet, linA, linB, linC, div_mul_div_comm, div_pow,
    div_sub_div _ _ (by positivity) (by positivity), div_eq_div_iff (by positivity) hΔ2]
  ring

/-- The linear part is positive (`A > 0`) when `Δ ≠ 0` (the map is invertible, so a column is
nonzero, forcing `e² + d² > 0`). -/
theorem linA_pos (a b d e : ℝ) (hΔ : a * e - b * d ≠ 0) : 0 < linA a b d e := by
  simp only [linA]
  have hΔ2 : 0 < (a * e - b * d) ^ 2 := by positivity
  have hnum : 0 < e ^ 2 + d ^ 2 := by
    rcases eq_or_ne e 0 with he | he
    · rcases eq_or_ne d 0 with hd | hd
      · exfalso; apply hΔ; rw [he, hd]; ring
      · positivity
    · positivity
  positivity

/-- **The image-form ellipse equals the matrix-form `ellipseGenSet`** with the computed
coefficients (for invertible `T`, `Δ ≠ 0`).  A point `w` is `T(unit disk) + t` iff
`(w - t)ᵀ M (w - t) ≤ 1` for `M` built from `T⁻¹`. -/
theorem linEllipseSet_eq (a b d e : ℝ) (t : ℝ × ℝ) (hΔ : a * e - b * d ≠ 0) :
    linEllipseSet a b d e t = ellipseGenSet (linA a b d e) (linB a b d e) (linC a b d e) t := by
  have hΔ2 : (a * e - b * d) ^ 2 ≠ 0 := pow_ne_zero 2 hΔ
  ext w
  simp only [linEllipseSet, ellipseGenSet, quadForm, linA, linB, linC, Set.mem_setOf_eq]
  constructor
  · -- forward: w = T(x,y)+t with x²+y² ≤ 1 ⟹ quadForm ≤ 1
    rintro ⟨x, y, hxy, rfl⟩
    simp only [add_sub_cancel_right]
    -- the quadratic form at (a x + b y, d x + e y) equals (x²+y²) exactly (the M = (T⁻¹)ᵀT⁻¹
    -- identity); so ≤ 1.
    have hkey : (e ^ 2 + d ^ 2) / (a * e - b * d) ^ 2 * (a * x + b * y) ^ 2
        + 2 * (-(b * e + a * d) / (a * e - b * d) ^ 2) * (a * x + b * y) * (d * x + e * y)
        + (b ^ 2 + a ^ 2) / (a * e - b * d) ^ 2 * (d * x + e * y) ^ 2
        = x ^ 2 + y ^ 2 := by
      rw [combine3, div_eq_iff hΔ2]; ring
    rw [hkey]; exact hxy
  · -- backward: quadForm(w-t) ≤ 1 ⟹ ∃ x y, x²+y² ≤ 1 ∧ w = T(x,y)+t.
    -- Take (x,y) = T⁻¹(w - t):  x = (e(w.1-t.1) - b(w.2-t.2))/Δ, y = (-d(w.1-t.1)+a(w.2-t.2))/Δ.
    intro hq
    set p := w.1 - t.1 with hp
    set s := w.2 - t.2 with hs
    refine ⟨(e * p - b * s) / (a * e - b * d), (-d * p + a * s) / (a * e - b * d), ?_, ?_⟩
    · -- x² + y² = quadForm(w-t) ≤ 1
      have hxy2 : ((e * p - b * s) / (a * e - b * d)) ^ 2
            + ((-d * p + a * s) / (a * e - b * d)) ^ 2
          = (e ^ 2 + d ^ 2) / (a * e - b * d) ^ 2 * p ^ 2
            + 2 * (-(b * e + a * d) / (a * e - b * d) ^ 2) * p * s
            + (b ^ 2 + a ^ 2) / (a * e - b * d) ^ 2 * s ^ 2 := by
        rw [combine3, div_pow, div_pow, ← add_div, div_eq_div_iff hΔ2 hΔ2]; ring
      rw [hxy2]; exact hq
    · -- w = T(T⁻¹(w-t)) + t
      have e1 : a * ((e * p - b * s) / (a * e - b * d))
          + b * ((-d * p + a * s) / (a * e - b * d)) + t.1 = w.1 := by
        rw [mul_div_assoc', mul_div_assoc', ← add_div,
          show a * (e * p - b * s) + b * (-d * p + a * s) = (a * e - b * d) * p by ring,
          mul_comm, mul_div_assoc, div_self hΔ, mul_one, hp]; ring
      have e2 : d * ((e * p - b * s) / (a * e - b * d))
          + e * ((-d * p + a * s) / (a * e - b * d)) + t.2 = w.2 := by
        rw [mul_div_assoc', mul_div_assoc', ← add_div,
          show d * (e * p - b * s) + e * (-d * p + a * s) = (a * e - b * d) * s by ring,
          mul_comm, mul_div_assoc, div_self hΔ, mul_one, hs]; ring
      rw [Prod.ext_iff]; exact ⟨e1.symm, e2.symm⟩

/-! ## The genuine `LinearMap` and its determinant

To make "`det T`" a genuine object, we package `T` as a `LinearMap` and prove its determinant is
`a*e - b*d`, so the area `π·|det T|` is literally the area of the image ellipse. -/

/-- The linear map `T(x,y) = (a x + b y, d x + e y)` on `ℝ × ℝ`. -/
def linMap (a b d e : ℝ) : (ℝ × ℝ) →ₗ[ℝ] (ℝ × ℝ) where
  toFun w := (a * w.1 + b * w.2, d * w.1 + e * w.2)
  map_add' p q := by simp only [Prod.fst_add, Prod.snd_add, Prod.mk_add_mk, Prod.mk.injEq];
                     constructor <;> ring
  map_smul' r p := by simp only [Prod.smul_fst, Prod.smul_snd, smul_eq_mul, Prod.smul_mk,
                        RingHom.id_apply, Prod.mk.injEq]; constructor <;> ring

theorem linMap_det (a b d e : ℝ) : LinearMap.det (linMap a b d e) = a * e - b * d := by
  rw [← LinearMap.det_toMatrix (Basis.finTwoProd ℝ), Matrix.det_fin_two]
  simp only [LinearMap.toMatrix_apply, Basis.coe_finTwoProd_repr, Basis.finTwoProd_zero,
    Basis.finTwoProd_one, linMap, LinearMap.coe_mk, AddHom.coe_mk]
  simp only [Matrix.cons_val_zero, Matrix.cons_val_one]
  ring

/-! ## Feasibility and the achievable set, image-form -/

/-- Image-form feasibility: an invertible `T` (`Δ ≠ 0`) whose ellipse holds two unit disks with
centers `≥ 2` apart. -/
def FeasibleLin (a b d e : ℝ) (t : ℝ × ℝ) : Prop :=
  a * e - b * d ≠ 0 ∧
  ∃ p q : ℝ × ℝ,
    diskSet p.1 p.2 ⊆ linEllipseSet a b d e t ∧
    diskSet q.1 q.2 ⊆ linEllipseSet a b d e t ∧
    4 ≤ nrm2 (p - q)

/-- **`FeasibleLin` ⟹ `FeasibleGen`** (with the computed matrix coefficients), and the areas
agree: `1/√(genDet) = |det T| = |a*e - b*d|`. -/
theorem feasibleGen_of_feasibleLin (a b d e : ℝ) (t : ℝ × ℝ) (h : FeasibleLin a b d e t) :
    FeasibleGen (linA a b d e) (linB a b d e) (linC a b d e) t := by
  obtain ⟨hΔ, p, q, hp, hq, hd⟩ := h
  refine ⟨linA_pos a b d e hΔ, ?_, p, q, ?_, ?_, hd⟩
  · rw [genDet_lin a b d e hΔ]; positivity
  · rw [← linEllipseSet_eq a b d e t hΔ]; exact hp
  · rw [← linEllipseSet_eq a b d e t hΔ]; exact hq

/-- The set of areas achievable by an invertible **image-form** ellipse holding two
interior-disjoint unit disks, with the area written as the genuine `π · |det (linMap …)|`. -/
def achievableAreasLin : Set ℝ :=
  { A | ∃ (a b d e : ℝ) (t : ℝ × ℝ), FeasibleLin a b d e t ∧
        A = Real.pi * |LinearMap.det (linMap a b d e)| }

/-- The image-form area equals the matrix-form Lebesgue area: `π·|det T| =
(volume (ellipseGenSet …)).toReal`. -/
theorem linArea_eq_volume (a b d e : ℝ) (t : ℝ × ℝ) (h : FeasibleLin a b d e t) :
    Real.pi * |LinearMap.det (linMap a b d e)|
      = (volume (ellipseGenSet (linA a b d e) (linB a b d e) (linC a b d e) t)).toReal := by
  have hΔ : a * e - b * d ≠ 0 := h.1
  have hgen := feasibleGen_of_feasibleLin a b d e t h
  rw [volume_ellipseGenSet _ _ _ t hgen.1 hgen.2.1]
  have hge0 : (0 : ℝ) ≤ Real.pi / Real.sqrt (genDet (linA a b d e) (linB a b d e) (linC a b d e)) :=
    by positivity
  rw [ENNReal.toReal_ofReal hge0, genDet_lin a b d e hΔ, linMap_det]
  -- π / √(1/Δ²) = π · |Δ|
  rw [one_div, Real.sqrt_inv, div_inv_eq_mul, Real.sqrt_sq_eq_abs]

/-- **The achievable sets coincide**, so the independent image-form spec has the
SAME achievable areas as the matrix-form spec. -/
theorem achievableAreasLin_subset : achievableAreasLin ⊆ achievableAreas := by
  rintro A ⟨a, b, d, e, t, h, rfl⟩
  exact ⟨linA a b d e, linB a b d e, linC a b d e, t,
    feasibleGen_of_feasibleLin a b d e t h, linArea_eq_volume a b d e t h⟩

/-- The image-form achievable set is nonempty: the optimal ellipse `x²/(9/2)+y²/(3/2)≤1` is the
image of the unit disk under `T = diag(√(9/2), √(3/2))` (`a=√(9/2), b=0, d=0, e=√(3/2)`). -/
theorem achievableAreasLin_optimal_mem :
    (3 * Real.sqrt 3 / 2 * Real.pi) ∈ achievableAreasLin := by
  set a := Real.sqrt (9 / 2) with ha
  set e := Real.sqrt (3 / 2) with he
  have ha2 : a ^ 2 = 9 / 2 := Real.sq_sqrt (by norm_num)
  have he2 : e ^ 2 = 3 / 2 := Real.sq_sqrt (by norm_num)
  have hapos : 0 < a := Real.sqrt_pos.mpr (by norm_num)
  have hepos : 0 < e := Real.sqrt_pos.mpr (by norm_num)
  have hΔ : a * e - 0 * 0 ≠ 0 := by
    rw [mul_zero, sub_zero]; positivity
  refine ⟨a, 0, 0, e, (0, 0), ⟨hΔ, ?_⟩, ?_⟩
  · -- the image ellipse with this T equals ellipseSet (9/2)(3/2); reuse feasible_optimal centers.
    have hset : linEllipseSet a 0 0 e (0, 0) = ellipseSet (9 / 2) (3 / 2) := by
      ext w
      simp only [linEllipseSet, ellipseSet, Set.mem_setOf_eq]
      constructor
      · rintro ⟨x, y, hxy, rfl⟩
        simp only [zero_mul, add_zero, zero_add]
        -- w = (a x, e y); a²=9/2, e²=3/2; (a x)²/(9/2) + (e y)²/(3/2) = x² + y² ≤ 1
        rw [show (a * x) ^ 2 / (9 / 2) = x ^ 2 by rw [mul_pow, ha2]; field_simp,
            show (e * y) ^ 2 / (3 / 2) = y ^ 2 by rw [mul_pow, he2]; field_simp]
        exact hxy
      · intro hw
        refine ⟨w.1 / a, w.2 / e, ?_, ?_⟩
        · -- (w.1/a)² + (w.2/e)² = w.1²/(9/2) + w.2²/(3/2) ≤ 1
          rw [div_pow, div_pow, ha2, he2]; exact hw
        · simp only [zero_mul, add_zero, zero_add, Prod.ext_iff]
          constructor <;> field_simp
    obtain ⟨c₁, c₂, h1, h2, hd⟩ := feasible_optimal
    rw [hset]
    exact ⟨c₁, c₂, h1, h2, hd⟩
  · -- π·|det T| = π·|a*e| = π·√(9/2)·√(3/2) = π·√(27/4) = π·(3√3/2)
    rw [linMap_det]
    have hdet : a * e - 0 * 0 = a * e := by ring
    rw [hdet, abs_of_pos (by positivity)]
    rw [ha, he, ← Real.sqrt_mul (by norm_num),
      show (9 : ℝ) / 2 * (3 / 2) = 27 / 4 by norm_num, sqrt_27_div_4]
    ring

/-- **The headline result, image-form (independent restatement).** `(3√3/2)·π` is
the least area `π·|det T|` over invertible affine images of the unit disk that hold two
interior-disjoint unit disks.  Proved by transporting `isLeast_minArea` along the proven
equality of achievable sets — two independently-worded specs, one theorem. -/
theorem isLeast_minArea_lin :
    IsLeast achievableAreasLin (3 * Real.sqrt 3 / 2 * Real.pi) := by
  constructor
  · exact achievableAreasLin_optimal_mem
  · -- lower bound: every image-form achievable area is also matrix-form achievable, so ≥ min.
    intro A hA
    exact isLeast_minArea.2 (achievableAreasLin_subset hA)

end

end Ellipse
