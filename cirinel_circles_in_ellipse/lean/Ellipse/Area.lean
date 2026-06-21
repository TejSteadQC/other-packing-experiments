import Ellipse.General
import Mathlib.MeasureTheory.Measure.Lebesgue.EqHaar
import Mathlib.MeasureTheory.Measure.Lebesgue.VolumeOfBalls
import Mathlib.MeasureTheory.Measure.Haar.InnerProductSpace
import Mathlib.MeasureTheory.Constructions.Pi
import Mathlib.LinearAlgebra.Determinant
import Mathlib.LinearAlgebra.Basis.Fin

/-!
# Boundary 3: the literal Lebesgue area of the ellipse

The theorems `Ellipse.area_ge_of_feasibleGen` (and friends) bound `1 / √(det M)`, which we
described informally as "area / π" (the area of the ellipse `(x-c)ᵀ M (x-c) ≤ 1` is
`π / √(det M)`).  This file closes that last scope boundary by proving the **literal Lebesgue
area** identity

`volume (ellipseGenSet A B C c) = ENNReal.ofReal (π / √(genDet A B C))`

(for `M` positive definite, i.e. `0 < A`, `0 < genDet A B C` (Sylvester)), and then derives the final
literal-area theorem.

## Strategy

* The unit disk `D = {p : ℝ×ℝ | p.1²+p.2² ≤ 1}` has `volume = ofReal π`, transported from
  `EuclideanSpace ℝ (Fin 2)` (where `EuclideanSpace.volume_closedBall_fin_two` gives the disk
  area) via the volume-preserving measurable equivalence `ℝ×ℝ ≃ᵐ EuclideanSpace ℝ (Fin 2)`.
* The axis-aligned ellipse `ellipseSet u v` is the image of `D` under the diagonal linear map
  `diagL (√u) (√v)`, whose determinant is `√u · √v = √(uv)`; so `volume (ellipseSet u v) =
  ofReal (√(uv) · π)` by `Measure.addHaar_image_linearMap`.
* The general ellipse is the `rigidT`-preimage of an axis-aligned ellipse (from
  `Ellipse.mem_ellipseGen_iff`); `rigidT` is a rotation (`det = 1`) composed with a
  translation, both volume-preserving, so it has no effect on the volume.

The Haar instance on `volume : Measure (ℝ×ℝ)` (needed by `addHaar_image_linearMap`) comes from
`prod.instIsAddHaarMeasure`.
-/

namespace Ellipse

open MeasureTheory Set MeasureTheory.Measure Module

noncomputable section

/-- `volume : Measure (ℝ × ℝ)` is an additive Haar measure (it is `volume.prod volume`). -/
instance : MeasureTheory.Measure.IsAddHaarMeasure (volume : Measure (ℝ × ℝ)) :=
  MeasureTheory.Measure.prod.instIsAddHaarMeasure volume volume

/-! ## The unit disk has area `π` -/

/-- The composed measurable equivalence `ℝ × ℝ ≃ᵐ EuclideanSpace ℝ (Fin 2)`
(via `(Fin 2 → ℝ)`). -/
def prodEuclidEquiv : (ℝ × ℝ) ≃ᵐ EuclideanSpace ℝ (Fin 2) :=
  (MeasurableEquiv.finTwoArrow (α := ℝ)).symm.trans (MeasurableEquiv.toLp 2 (Fin 2 → ℝ))

theorem prodEuclidEquiv_measurePreserving :
    MeasurePreserving prodEuclidEquiv (volume : Measure (ℝ × ℝ)) volume :=
  (PiLp.volume_preserving_toLp (Fin 2)).comp ((volume_preserving_finTwoArrow ℝ).symm)

theorem prodEuclidEquiv_apply_zero (p : ℝ × ℝ) : (prodEuclidEquiv p) 0 = p.1 := by
  simp [prodEuclidEquiv, MeasurableEquiv.finTwoArrow, MeasurableEquiv.toLp]

theorem prodEuclidEquiv_apply_one (p : ℝ × ℝ) : (prodEuclidEquiv p) 1 = p.2 := by
  simp [prodEuclidEquiv, MeasurableEquiv.finTwoArrow, MeasurableEquiv.toLp]

/-- The unit disk in `ℝ × ℝ` is the preimage of the unit `closedBall` in `EuclideanSpace`. -/
theorem unitDisk_eq_preimage :
    prodEuclidEquiv ⁻¹' (Metric.closedBall (0 : EuclideanSpace ℝ (Fin 2)) 1)
      = {p : ℝ × ℝ | p.1 ^ 2 + p.2 ^ 2 ≤ 1} := by
  rw [EuclideanSpace.closedBall_zero_eq 1 (by norm_num)]
  ext p
  simp only [Set.mem_preimage, Set.mem_setOf_eq, Fin.sum_univ_two, one_pow]
  rw [prodEuclidEquiv_apply_zero, prodEuclidEquiv_apply_one]

/-- **The unit disk has Lebesgue area `π`.** -/
theorem volume_unitDisk :
    volume {p : ℝ × ℝ | p.1 ^ 2 + p.2 ^ 2 ≤ 1} = ENNReal.ofReal Real.pi := by
  rw [← unitDisk_eq_preimage,
    prodEuclidEquiv_measurePreserving.measure_preimage
      (measurableSet_closedBall.nullMeasurableSet),
    EuclideanSpace.volume_closedBall_fin_two]
  simp

/-! ## The diagonal linear map and the axis-aligned ellipse area -/

/-- The diagonal linear map `(x,y) ↦ (a x, b y)` on `ℝ × ℝ`. -/
def diagL (a b : ℝ) : (ℝ × ℝ) →ₗ[ℝ] (ℝ × ℝ) :=
  LinearMap.prodMap (a • LinearMap.id) (b • LinearMap.id)

theorem diagL_apply (a b : ℝ) (p : ℝ × ℝ) : diagL a b p = (a * p.1, b * p.2) := by
  simp [diagL, LinearMap.prodMap]

theorem diagL_det (a b : ℝ) : LinearMap.det (diagL a b) = a * b := by
  rw [diagL, LinearMap.det_prodMap]; simp

/-- The image of the unit disk under `diagL (√u) (√v)` is `ellipseSet u v` (for `u,v>0`). -/
theorem diagL_image_unitDisk (u v : ℝ) (hu : 0 < u) (hv : 0 < v) :
    diagL (Real.sqrt u) (Real.sqrt v) '' {p : ℝ × ℝ | p.1 ^ 2 + p.2 ^ 2 ≤ 1}
      = ellipseSet u v := by
  have hsu2 : Real.sqrt u ^ 2 = u := Real.sq_sqrt hu.le
  have hsv2 : Real.sqrt v ^ 2 = v := Real.sq_sqrt hv.le
  have hsu : Real.sqrt u ≠ 0 := by positivity
  have hsv : Real.sqrt v ≠ 0 := by positivity
  ext q
  simp only [Set.mem_image, Set.mem_setOf_eq, ellipseSet, diagL_apply]
  constructor
  · rintro ⟨p, hp, rfl⟩
    rw [show (Real.sqrt u * p.1) ^ 2 / u = p.1 ^ 2 by rw [mul_pow, hsu2]; field_simp,
        show (Real.sqrt v * p.2) ^ 2 / v = p.2 ^ 2 by rw [mul_pow, hsv2]; field_simp]
    exact hp
  · intro hq
    refine ⟨(q.1 / Real.sqrt u, q.2 / Real.sqrt v), ?_, ?_⟩
    · simp only
      rw [div_pow, div_pow, hsu2, hsv2]; exact hq
    · simp only [Prod.ext_iff]
      constructor <;> field_simp

/-- **The axis-aligned ellipse `x²/u + y²/v ≤ 1` has Lebesgue area `π·√(uv)`.** -/
theorem volume_ellipseSet (u v : ℝ) (hu : 0 < u) (hv : 0 < v) :
    volume (ellipseSet u v) = ENNReal.ofReal (Real.pi * Real.sqrt (u * v)) := by
  rw [← diagL_image_unitDisk u v hu hv, Measure.addHaar_image_linearMap, diagL_det,
    volume_unitDisk]
  have hsu : (0:ℝ) ≤ Real.sqrt u := Real.sqrt_nonneg u
  have hsv : (0:ℝ) ≤ Real.sqrt v := Real.sqrt_nonneg v
  rw [abs_of_nonneg (by positivity),
    ← ENNReal.ofReal_mul (by positivity),
    Real.sqrt_mul hu.le]
  congr 1
  ring

/-! ## The rigid motion is volume-preserving -/

/-- The rotation linear map `(z.1,z.2) ↦ (c̄ z.1 + s̄ z.2, -s̄ z.1 + c̄ z.2)`. -/
def rotLin (cbar sbar : ℝ) : (ℝ × ℝ) →ₗ[ℝ] (ℝ × ℝ) where
  toFun z := (cbar * z.1 + sbar * z.2, -sbar * z.1 + cbar * z.2)
  map_add' p q := by
    simp only [Prod.fst_add, Prod.snd_add, Prod.mk_add_mk, Prod.mk.injEq]
    constructor <;> ring
  map_smul' r p := by
    simp only [Prod.smul_fst, Prod.smul_snd, smul_eq_mul, Prod.smul_mk, RingHom.id_apply,
      Prod.mk.injEq]
    constructor <;> ring

theorem rotLin_det (cbar sbar : ℝ) (h : cbar ^ 2 + sbar ^ 2 = 1) :
    LinearMap.det (rotLin cbar sbar) = 1 := by
  rw [← LinearMap.det_toMatrix (Basis.finTwoProd ℝ), Matrix.det_fin_two]
  simp only [LinearMap.toMatrix_apply, Basis.coe_finTwoProd_repr, Basis.finTwoProd_zero,
    Basis.finTwoProd_one, rotLin, LinearMap.coe_mk, AddHom.coe_mk]
  simp only [Matrix.cons_val_zero, Matrix.cons_val_one]
  nlinarith [h]

/-- `rigidT` factors as `rotLin ∘ (translation by -c)`. -/
theorem rigidT_eq_comp (cbar sbar : ℝ) (c x : ℝ × ℝ) :
    rigidT cbar sbar c x = rotLin cbar sbar ((fun y => (-c) + y) x) := by
  simp only [rigidT, rotLin, LinearMap.coe_mk, AddHom.coe_mk, Prod.fst_add, Prod.snd_add,
    Prod.fst_neg, Prod.snd_neg, Prod.ext_iff]
  constructor <;> ring

/-- **The `rigidT`-preimage is volume-preserving** (rotation `det = 1`, translation
invariant). -/
theorem volume_rigidT_preimage (cbar sbar : ℝ) (c : ℝ × ℝ) (h : cbar ^ 2 + sbar ^ 2 = 1)
    (S : Set (ℝ × ℝ)) :
    volume (rigidT cbar sbar c ⁻¹' S) = volume S := by
  have hpre : rigidT cbar sbar c ⁻¹' S
      = (fun y => (-c) + y) ⁻¹' (rotLin cbar sbar ⁻¹' S) := by
    ext x; simp only [Set.mem_preimage, rigidT_eq_comp cbar sbar c x]
  rw [hpre, measure_preimage_add]
  have hdet : LinearMap.det (rotLin cbar sbar) ≠ 0 := by rw [rotLin_det cbar sbar h]; norm_num
  rw [Measure.addHaar_preimage_linearMap volume hdet, rotLin_det cbar sbar h]
  simp

/-! ## The general ellipse area -/

/-- **The general (PD, possibly tilted/off-center) ellipse area.** For `0 < A` and
`0 < genDet A B C`, the Lebesgue area of `ellipseGenSet A B C c` is `π / √(det M)`. -/
theorem volume_ellipseGenSet (A B C : ℝ) (c : ℝ × ℝ) (hA : 0 < A) (hdet : 0 < genDet A B C) :
    volume (ellipseGenSet A B C c) = ENNReal.ofReal (Real.pi / Real.sqrt (genDet A B C)) := by
  -- diagonalize
  obtain ⟨cbar, sbar, hunit, hbeta⟩ := exists_diagonalizing A B C
  obtain ⟨hα, hγ⟩ := alpha_gamma_pos A B C cbar sbar hunit hA hdet hbeta
  set α := alphaEnt A B C cbar sbar with hαdef
  set γ := gammaEnt A B C cbar sbar with hγdef
  have hαv : (0:ℝ) < 1 / α := by positivity
  have hγv : (0:ℝ) < 1 / γ := by positivity
  -- `ellipseGenSet = rigidT ⁻¹' ellipseSet (1/α) (1/γ)`
  have hset : ellipseGenSet A B C c = rigidT cbar sbar c ⁻¹' ellipseSet (1 / α) (1 / γ) := by
    ext x
    rw [Set.mem_preimage]
    exact mem_ellipseGen_iff A B C cbar sbar c x hunit hbeta hα hγ
  rw [hset, volume_rigidT_preimage cbar sbar c hunit, volume_ellipseSet _ _ hαv hγv]
  -- (1/α)(1/γ) = 1/genDet, so π·√((1/α)(1/γ)) = π/√genDet
  have hprodαγ : α * γ = genDet A B C := by
    have := alpha_gamma_sub_beta_sq A B C cbar sbar hunit
    rw [hbeta] at this; simpa using this
  have hprod : (1 / α) * (1 / γ) = 1 / genDet A B C := by
    rw [← hprodαγ]; field_simp
  rw [hprod, one_div, Real.sqrt_inv, ← one_div, mul_one_div]

/-! ## The final literal-area theorem -/

/-- **Final literal-area theorem (`ENNReal` form).** An ellipse with positive-definite matrix M
`(x-c)ᵀ M (x-c) ≤ 1` (`M = !![A,B;B,C]`, `det M = genDet A B C`) that holds two
interior-disjoint unit disks has **Lebesgue area** `volume (ellipseGenSet A B C c)` at least
`(3√3/2)·π`. -/
theorem area_volume_ge_of_feasibleGen (A B C : ℝ) (c : ℝ × ℝ) (hfeas : FeasibleGen A B C c) :
    ENNReal.ofReal (3 * Real.sqrt 3 / 2 * Real.pi) ≤ volume (ellipseGenSet A B C c) := by
  have hA : 0 < A := hfeas.1
  have hdet : 0 < genDet A B C := hfeas.2.1
  rw [volume_ellipseGenSet A B C c hA hdet]
  apply ENNReal.ofReal_le_ofReal
  -- (3√3/2)·π ≤ π/√genDet  ⟸  3√3/2 ≤ 1/√genDet  (π > 0)
  have hbound := area_ge_of_feasibleGen A B C c hfeas
  rw [mul_comm, div_eq_mul_inv Real.pi, ← one_div]
  exact mul_le_mul_of_nonneg_left hbound Real.pi_pos.le

/-- **Final literal-area theorem (`Real`/`toReal` form).** Same statement, with the area as a
real number: `(volume (ellipseGenSet A B C c)).toReal ≥ (3√3/2)·π`. -/
theorem area_toReal_ge_of_feasibleGen (A B C : ℝ) (c : ℝ × ℝ) (hfeas : FeasibleGen A B C c) :
    3 * Real.sqrt 3 / 2 * Real.pi ≤ (volume (ellipseGenSet A B C c)).toReal := by
  have hA : 0 < A := hfeas.1
  have hdet : 0 < genDet A B C := hfeas.2.1
  rw [volume_ellipseGenSet A B C c hA hdet]
  have hge0 : (0:ℝ) ≤ Real.pi / Real.sqrt (genDet A B C) := by positivity
  rw [ENNReal.toReal_ofReal hge0]
  have hbound := area_ge_of_feasibleGen A B C c hfeas
  rw [mul_comm, div_eq_mul_inv Real.pi, ← one_div]
  exact mul_le_mul_of_nonneg_left hbound Real.pi_pos.le

/-- Auditability bridge: the area identity stated literally for the matrix `M = !![A,B;B,C]`,
`det M = genDet A B C`. -/
theorem volume_ellipseGenSet_matrix (A B C : ℝ) (c : ℝ × ℝ) (hA : 0 < A)
    (hdet : 0 < genDet A B C) :
    volume (ellipseGenSet A B C c)
      = ENNReal.ofReal (Real.pi / Real.sqrt ((genMat A B C).det)) := by
  rw [genMat_det]; exact volume_ellipseGenSet A B C c hA hdet

end

end Ellipse
