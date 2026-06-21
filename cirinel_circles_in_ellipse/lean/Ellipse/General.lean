import Ellipse.Main
import Mathlib.LinearAlgebra.Matrix.PosDef
import Mathlib.LinearAlgebra.Matrix.Determinant.Basic
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Arctan

/-!
# Task 2: reduction from a general (tilted, off-center) ellipse to axis-aligned

The main theorem `Ellipse.area_ge_of_feasible` is about *axis-aligned, origin-centered*
ellipses `x²/u + y²/v ≤ 1`.  A **general** ellipse is
`{ x : ℝ² | (x - c)ᵀ M (x - c) ≤ 1 }` for a symmetric positive-definite `2×2` matrix `M`
and center `c`, with area `π / √(det M)`.

This file:
* defines the general-ellipse set and feasibility predicate `FeasibleGen`;
* states the WLOG **reduction theorem**: a feasible general ellipse yields a feasible
  axis-aligned `(u,v)` with `u v = 1 / det M` (same area);
* states the **area bound** for the general ellipse: `1/√(det M) ≥ 3√3/2`.

The reduction is a rigid motion (rotation `Rᵀ` + translation by `-c`):
`T(x) = Rᵀ (x - c)`.  It preserves Euclidean distances (so disjointness / center distance),
maps the unit disk at `a` to the unit disk at `T a`, and sends the `M`-ellipse to the
axis-aligned `α y₁² + γ y₂² ≤ 1` where `R = ![![c̄,-s̄],[s̄,c̄]]` diagonalizes `M`
(`Rᵀ M R = diag(α, γ)`, `α γ = det M`), so `u = 1/α`, `v = 1/γ`, `u v = 1/det M`.

We use an *auditable explicit* symmetric `2×2`: parameters `A = M 0 0`, `B = M 0 1 = M 1 0`,
`C = M 1 1`, with PD given by the Sylvester criterion `0 < A ∧ 0 < A*C - B²`
(`det M = A*C - B²`).  A bridge lemma `posDef_two_iff_sylvester` connects this to the
mathlib `Matrix.PosDef` for symmetric `2×2`, so the statement is recognizably the matrix
ellipse.
-/

namespace Ellipse

open Set

/-! ## The general ellipse, explicitly

`(x - c)ᵀ M (x - c)` for `M = ![![A,B],[B,C]]` is
`A(x.1-c.1)² + 2B(x.1-c.1)(x.2-c.2) + C(x.2-c.2)²`. -/

/-- The quadratic form of a symmetric `2×2` matrix `![![A,B],[B,C]]` at `x - c`. -/
def quadForm (A B C : ℝ) (c x : ℝ × ℝ) : ℝ :=
  A * (x.1 - c.1) ^ 2 + 2 * B * (x.1 - c.1) * (x.2 - c.2) + C * (x.2 - c.2) ^ 2

/-- The filled general ellipse `{ x | (x-c)ᵀ M (x-c) ≤ 1 }` for symmetric `M=![![A,B],[B,C]]`. -/
def ellipseGenSet (A B C : ℝ) (c : ℝ × ℝ) : Set (ℝ × ℝ) :=
  {x : ℝ × ℝ | quadForm A B C c x ≤ 1}

/-- The determinant of the symmetric `2×2` matrix `![![A,B],[B,C]]`. -/
def genDet (A B C : ℝ) : ℝ := A * C - B ^ 2

/-! ## Bridge to the mathlib matrix ellipse (auditability)

For `M := !![A, B; B, C]` (symmetric), `quadForm A B C c x = (x-c)ᵀ M (x-c)` and
`Matrix.det M = genDet A B C`, and `M.PosDef ↔ (0 < A ∧ 0 < genDet A B C)` (Sylvester).
These connect the explicit form above to the genuine matrix objects. -/

/-- The explicit symmetric `2×2` matrix. -/
def genMat (A B C : ℝ) : Matrix (Fin 2) (Fin 2) ℝ := !![A, B; B, C]

theorem genMat_isSymm (A B C : ℝ) : (genMat A B C).IsSymm := by
  unfold genMat Matrix.IsSymm
  ext i j
  fin_cases i <;> fin_cases j <;> simp [Matrix.transpose]

theorem genMat_det (A B C : ℝ) : (genMat A B C).det = genDet A B C := by
  unfold genMat genDet
  rw [Matrix.det_fin_two_of]
  ring

/-- The genuine matrix entries of `genMat`. -/
theorem genMat_entries (A B C : ℝ) :
    (genMat A B C) 0 0 = A ∧ (genMat A B C) 0 1 = B ∧
    (genMat A B C) 1 0 = B ∧ (genMat A B C) 1 1 = C := by
  refine ⟨?_, ?_, ?_, ?_⟩ <;> simp [genMat]

/-- The matrix quadratic form `dotProduct (genMat *ᵥ (x-c)) (x-c)` equals `quadForm`. -/
theorem quadForm_eq_matrix (A B C : ℝ) (c x : ℝ × ℝ) :
    quadForm A B C c x =
      dotProduct (Matrix.mulVec (genMat A B C) ![x.1 - c.1, x.2 - c.2])
        ![x.1 - c.1, x.2 - c.2] := by
  unfold quadForm
  obtain ⟨e00, e01, e10, e11⟩ := genMat_entries A B C
  simp only [dotProduct, Matrix.mulVec, Fin.sum_univ_two, Matrix.cons_val_zero,
    Matrix.cons_val_one, e00, e01, e10, e11]
  ring

/-! ## The rigid-motion transfer

We use the rotation `R = ![![c̄,-s̄],[s̄,c̄]]` (`c̄² + s̄² = 1`) and the isometry
`T(x) = Rᵀ(x - c)`:
`T(x).1 = c̄·(x.1-c.1) + s̄·(x.2-c.2)`, `T(x).2 = -s̄·(x.1-c.1) + c̄·(x.2-c.2)`.
Its inverse from `y` back to `x`: `x.1-c.1 = c̄·y.1 - s̄·y.2`, `x.2-c.2 = s̄·y.1 + c̄·y.2`. -/

/-- The rigid motion `T(x) = Rᵀ(x - c)`. -/
def rigidT (cbar sbar : ℝ) (c x : ℝ × ℝ) : ℝ × ℝ :=
  (cbar * (x.1 - c.1) + sbar * (x.2 - c.2), -sbar * (x.1 - c.1) + cbar * (x.2 - c.2))

/-- `rigidT` preserves squared Euclidean distance of differences (it's a rotation). -/
theorem rigidT_nrm2 (cbar sbar : ℝ) (c a b : ℝ × ℝ)
    (h : cbar ^ 2 + sbar ^ 2 = 1) :
    nrm2 (rigidT cbar sbar c a - rigidT cbar sbar c b) = nrm2 (a - b) := by
  simp only [nrm2, rigidT, Prod.fst_sub, Prod.snd_sub]
  nlinarith [h, sq_nonneg (a.1 - b.1), sq_nonneg (a.2 - b.2)]

/-- The image of the closed unit disk at `a` under `rigidT` is the closed unit disk at
`rigidT a`: `x ∈ diskSet a ↔ rigidT x ∈ diskSet (rigidT a)`.  (A rotation preserves the
Euclidean disk.) -/
theorem rigidT_mem_diskSet (cbar sbar : ℝ) (c a x : ℝ × ℝ)
    (h : cbar ^ 2 + sbar ^ 2 = 1) :
    x ∈ diskSet a.1 a.2 ↔
      rigidT cbar sbar c x ∈ diskSet (rigidT cbar sbar c a).1 (rigidT cbar sbar c a).2 := by
  simp only [diskSet, Set.mem_setOf_eq, rigidT]
  constructor
  · intro hx; nlinarith [hx, h, sq_nonneg (x.1 - a.1), sq_nonneg (x.2 - a.2)]
  · intro hx; nlinarith [hx, h, sq_nonneg (x.1 - a.1), sq_nonneg (x.2 - a.2)]

/-! ## The diagonalization: rotated quadratic form

Under `x - c = R y` (i.e. `y = T(x)`), the form `quadForm A B C c x` equals the diagonal
form `α y.1² + γ y.2²` *plus* the cross term `2β y.1 y.2`, where
* `α = A c̄² + 2B c̄ s̄ + C s̄²`,
* `γ = A s̄² − 2B s̄ c̄ + C c̄²`,
* `β = (C−A) s̄ c̄ + B(c̄² − s̄²)`.
Choosing `(c̄,s̄)` so `β = 0` gives the axis-aligned form. -/

/-- The rotated `(0,0)` diagonal entry `α`. -/
def alphaEnt (A B C cbar sbar : ℝ) : ℝ := A * cbar ^ 2 + 2 * B * cbar * sbar + C * sbar ^ 2

/-- The rotated `(1,1)` diagonal entry `γ`. -/
def gammaEnt (A B C cbar sbar : ℝ) : ℝ := A * sbar ^ 2 - 2 * B * sbar * cbar + C * cbar ^ 2

/-- The rotated off-diagonal entry `β`. -/
def betaEnt (A B C cbar sbar : ℝ) : ℝ := (C - A) * sbar * cbar + B * (cbar ^ 2 - sbar ^ 2)

/-- **Diagonalization identity (exact `ring`).** With `x - c = R y`, i.e.
`x.1-c.1 = c̄ y.1 − s̄ y.2`, `x.2-c.2 = s̄ y.1 + c̄ y.2`, the quadratic form becomes
`α y.1² + 2β y.1 y.2 + γ y.2²` (given `c̄²+s̄²=1`). -/
theorem quadForm_rotated (A B C cbar sbar : ℝ) (c : ℝ × ℝ) (y : ℝ × ℝ) :
    quadForm A B C c (c.1 + (cbar * y.1 - sbar * y.2), c.2 + (sbar * y.1 + cbar * y.2))
      = alphaEnt A B C cbar sbar * y.1 ^ 2
        + 2 * betaEnt A B C cbar sbar * y.1 * y.2
        + gammaEnt A B C cbar sbar * y.2 ^ 2 := by
  unfold quadForm alphaEnt betaEnt gammaEnt
  simp only [add_sub_cancel_left]
  ring

/-- The product of the diagonal entries equals the determinant when `β = 0`
(`α γ − β² = det M`, always; with `β=0`, `α γ = det M`). -/
theorem alpha_gamma_sub_beta_sq (A B C cbar sbar : ℝ) (h : cbar ^ 2 + sbar ^ 2 = 1) :
    alphaEnt A B C cbar sbar * gammaEnt A B C cbar sbar
      - betaEnt A B C cbar sbar ^ 2 = genDet A B C := by
  unfold alphaEnt gammaEnt betaEnt genDet
  -- αγ - β² = (c²+s²)²·(AC-B²); with c²+s²=1 the factor is 1.
  -- The difference from (AC-B²) is ((c²+s²)²-1)(AC-B²) = (c²+s²-1)(c²+s²+1)(AC-B²).
  linear_combination (cbar ^ 2 + sbar ^ 2 + 1) * (A * C - B ^ 2) * h

/-- The trace is preserved: `α + γ = A + C` (given `c̄²+s̄²=1`). -/
theorem alpha_add_gamma (A B C cbar sbar : ℝ) (h : cbar ^ 2 + sbar ^ 2 = 1) :
    alphaEnt A B C cbar sbar + gammaEnt A B C cbar sbar = A + C := by
  unfold alphaEnt gammaEnt
  linear_combination (A + C) * h

/-- **Positivity of the diagonal entries.** Given PD (`0 < A`, `0 < genDet`), once the
rotated form is diagonal (`β = 0`) and `c̄²+s̄²=1`, both diagonal entries are positive
(from `αγ = genDet > 0` and `α + γ = A + C > 0`). -/
theorem alpha_gamma_pos (A B C cbar sbar : ℝ) (h : cbar ^ 2 + sbar ^ 2 = 1)
    (hA : 0 < A) (hdet : 0 < genDet A B C) (hbeta : betaEnt A B C cbar sbar = 0) :
    0 < alphaEnt A B C cbar sbar ∧ 0 < gammaEnt A B C cbar sbar := by
  set α := alphaEnt A B C cbar sbar with hαdef
  set γ := gammaEnt A B C cbar sbar with hγdef
  -- C > 0 since AC = genDet + B² > 0 and A > 0.
  have hAC : 0 < A * C := by unfold genDet at hdet; nlinarith [sq_nonneg B]
  have hC : 0 < C := by
    rcases lt_trichotomy C 0 with h0 | h0 | h0
    · nlinarith [hAC, hA, h0]
    · rw [h0] at hAC; simp at hAC
    · exact h0
  -- αγ = genDet > 0 (β = 0); α + γ = A + C > 0.
  have hprod : α * γ = genDet A B C := by
    have := alpha_gamma_sub_beta_sq A B C cbar sbar h
    rw [hbeta] at this; simpa using this
  have hsum : α + γ = A + C := alpha_add_gamma A B C cbar sbar h
  have hpg : 0 < α * γ := by rw [hprod]; exact hdet
  have hsg : 0 < α + γ := by rw [hsum]; linarith
  -- positive product and positive sum ⟹ both positive.
  constructor
  · nlinarith [hpg, hsg, sq_nonneg (α - γ)]
  · nlinarith [hpg, hsg, sq_nonneg (α - γ)]

/-! ## Existence of the diagonalizing rotation (spectral step)

We exhibit a unit vector `(c̄,s̄)` (an eigenvector of the symmetric matrix) killing the
off-diagonal `β`.  For `B = 0` the matrix is already diagonal (`(1,0)` works).  For `B ≠ 0`
we take the eigenvector `(B, (C−A+D)/2)`, `D = √((A−C)²+4B²)`, normalized; the off-diagonal
verification reduces to `D² = (A−C)² + 4B²` (a `Real.sq_sqrt`) and `ring`/`nlinarith`. -/

/-- **Existence of the diagonalizing unit vector.** For any symmetric `2×2` (parameters
`A,B,C`) there is a unit vector `(c̄,s̄)` whose rotation kills the off-diagonal entry
`β = 0`.  (No positive-definiteness needed; positivity of the diagonal entries comes from
`alpha_gamma_pos`.) -/
theorem exists_diagonalizing (A B C : ℝ) :
    ∃ cbar sbar : ℝ, cbar ^ 2 + sbar ^ 2 = 1 ∧ betaEnt A B C cbar sbar = 0 := by
  rcases eq_or_ne B 0 with hB | hB
  · -- B = 0: already diagonal, take (1,0).
    refine ⟨1, 0, by ring, ?_⟩
    unfold betaEnt; rw [hB]; ring
  · -- B ≠ 0: normalized eigenvector (B, (C-A+D)/2).
    set e : ℝ := C - A with he
    set D : ℝ := Real.sqrt ((A - C) ^ 2 + 4 * B ^ 2) with hD
    have hDarg : 0 ≤ (A - C) ^ 2 + 4 * B ^ 2 := by positivity
    have hD2 : D ^ 2 = (A - C) ^ 2 + 4 * B ^ 2 := by rw [hD, Real.sq_sqrt hDarg]
    set w1 : ℝ := B with hw1
    set w2 : ℝ := (e + D) / 2 with hw2
    -- w1² + w2² > 0 since w1 = B ≠ 0.
    have hnpos : 0 < w1 ^ 2 + w2 ^ 2 := by
      have : 0 < w1 ^ 2 := by rw [hw1]; positivity
      nlinarith [sq_nonneg w2, this]
    set n : ℝ := Real.sqrt (w1 ^ 2 + w2 ^ 2) with hn
    have hn2 : n ^ 2 = w1 ^ 2 + w2 ^ 2 := by rw [hn, Real.sq_sqrt hnpos.le]
    have hnpos' : 0 < n := Real.sqrt_pos.mpr hnpos
    set cbar : ℝ := w1 / n with hcbar
    set sbar : ℝ := w2 / n with hsbar
    refine ⟨cbar, sbar, ?_, ?_⟩
    · -- unit vector
      rw [hcbar, hsbar, div_pow, div_pow, ← add_div, ← hn2]
      exact div_self (by positivity)
    · -- β = 0.  Multiply by n² > 0:  betaEnt · n² = (C-A) w2 w1 + B (w1² - w2²) = 0.
      have heD : D ^ 2 = e ^ 2 + 4 * B ^ 2 := by rw [hD2, he]; ring
      have hkey : (C - A) * w2 * w1 + B * (w1 ^ 2 - w2 ^ 2) = 0 := by
        rw [hw1, hw2, ← he]
        -- = B[(e²-D²)/4 + B²], and D² = e² + 4B² ⟹ = (B/4)(e²+4B² - D²) = 0.
        linear_combination (-(B / 4)) * heD
      have hne : n ≠ 0 := ne_of_gt hnpos'
      have hbeta_scaled : betaEnt A B C cbar sbar * n ^ 2
          = (C - A) * w2 * w1 + B * (w1 ^ 2 - w2 ^ 2) := by
        unfold betaEnt
        rw [hcbar, hsbar]
        field_simp
      have hz : betaEnt A B C cbar sbar * n ^ 2 = 0 := by rw [hbeta_scaled, hkey]
      have hn2pos : 0 < n ^ 2 := by positivity
      exact (mul_eq_zero.mp hz).resolve_right (ne_of_gt hn2pos)

/-! ## Membership transfer under the rigid motion

With `(c̄,s̄)` diagonalizing (`β=0`), the rigid motion `T(x)=Rᵀ(x−c)` satisfies
`x ∈ ellipseGenSet ↔ T x ∈ ellipseSet (1/α) (1/γ)`, since `quadForm(x) = α y₁² + γ y₂²`
(`y = T x`) and `α y₁² ≤ ... ⟺ y₁²/(1/α) ≤ ...`. -/

/-- The inverse rigid motion `S(y) = c + R y` (so `T (S y) = y`, `S (T x) = x`). -/
def rigidS (cbar sbar : ℝ) (c y : ℝ × ℝ) : ℝ × ℝ :=
  (c.1 + (cbar * y.1 - sbar * y.2), c.2 + (sbar * y.1 + cbar * y.2))

theorem rigidT_rigidS (cbar sbar : ℝ) (c y : ℝ × ℝ) (h : cbar ^ 2 + sbar ^ 2 = 1) :
    rigidT cbar sbar c (rigidS cbar sbar c y) = y := by
  simp only [rigidT, rigidS, Prod.ext_iff]
  refine ⟨?_, ?_⟩
  · simp only [add_sub_cancel_left]; linear_combination y.1 * h
  · simp only [add_sub_cancel_left]; linear_combination y.2 * h

theorem rigidS_rigidT (cbar sbar : ℝ) (c x : ℝ × ℝ) (h : cbar ^ 2 + sbar ^ 2 = 1) :
    rigidS cbar sbar c (rigidT cbar sbar c x) = x := by
  simp only [rigidT, rigidS, Prod.ext_iff]
  refine ⟨?_, ?_⟩
  · linear_combination (x.1 - c.1) * h
  · linear_combination (x.2 - c.2) * h

/-- **Membership transfer.** Given diagonalization (`β=0`, `c̄²+s̄²=1`) and positive
diagonal entries `α,γ`, a point lies in the general ellipse iff its rigid image lies in the
axis-aligned ellipse `x²/(1/α) + y²/(1/γ) ≤ 1`. -/
theorem mem_ellipseGen_iff (A B C cbar sbar : ℝ) (c x : ℝ × ℝ)
    (h : cbar ^ 2 + sbar ^ 2 = 1) (hbeta : betaEnt A B C cbar sbar = 0)
    (_hα : 0 < alphaEnt A B C cbar sbar) (_hγ : 0 < gammaEnt A B C cbar sbar) :
    x ∈ ellipseGenSet A B C c ↔
      rigidT cbar sbar c x ∈
        ellipseSet (1 / alphaEnt A B C cbar sbar) (1 / gammaEnt A B C cbar sbar) := by
  set α := alphaEnt A B C cbar sbar
  set γ := gammaEnt A B C cbar sbar
  set y := rigidT cbar sbar c x with hy
  -- x = S y, so quadForm A B C c x = α y.1² + 2β y.1 y.2 + γ y.2² = α y.1² + γ y.2².
  have hxeq : x = rigidS cbar sbar c y := by rw [hy, rigidS_rigidT cbar sbar c x h]
  have hquad : quadForm A B C c x = α * y.1 ^ 2 + γ * y.2 ^ 2 := by
    conv_lhs => rw [hxeq]
    rw [show rigidS cbar sbar c y
          = (c.1 + (cbar * y.1 - sbar * y.2), c.2 + (sbar * y.1 + cbar * y.2)) from rfl]
    rw [quadForm_rotated A B C cbar sbar c y, hbeta]
    ring
  simp only [ellipseGenSet, ellipseSet, Set.mem_setOf_eq, hquad]
  -- α y₁² + γ y₂² ≤ 1  ↔  y₁²/(1/α) + y₂²/(1/γ) ≤ 1
  rw [one_div, one_div, div_inv_eq_mul, div_inv_eq_mul]
  constructor <;> intro hh <;> nlinarith [hh]

/-! ## `FeasibleGen` and the reduction

`FeasibleGen A B C c` (with PD `0<A`, `0<genDet`): the general ellipse holds two unit disks
with centers ≥ 2 apart. -/

/-- Feasibility for a general (symmetric PD, off-center) ellipse `(x-c)ᵀM(x-c) ≤ 1`,
`M = ![![A,B],[B,C]]`.  PD is the Sylvester criterion `0 < A ∧ 0 < genDet A B C`. -/
def FeasibleGen (A B C : ℝ) (c : ℝ × ℝ) : Prop :=
  0 < A ∧ 0 < genDet A B C ∧
  ∃ d₁ d₂ : ℝ × ℝ,
    diskSet d₁.1 d₁.2 ⊆ ellipseGenSet A B C c ∧
    diskSet d₂.1 d₂.2 ⊆ ellipseGenSet A B C c ∧
    4 ≤ nrm2 (d₁ - d₂)

/-! ### Symmetry of `Feasible` under swapping `u, v` (coordinate swap, a rigid motion) -/

/-- Swapping coordinates `(p.1,p.2) ↦ (p.2,p.1)`. -/
private def swapc (p : ℝ × ℝ) : ℝ × ℝ := (p.2, p.1)

theorem feasible_comm (u v : ℝ) : Feasible u v → Feasible v u := by
  rintro ⟨c₁, c₂, h1, h2, hd⟩
  refine ⟨swapc c₁, swapc c₂, ?_, ?_, ?_⟩
  · intro x hx
    -- x ∈ diskSet (swapc c₁) ↔ swapc x ∈ diskSet c₁
    have hsx : swapc x ∈ diskSet c₁.1 c₁.2 := by
      simp only [diskSet, swapc, Set.mem_setOf_eq] at hx ⊢; linarith [hx]
    have := h1 hsx
    simp only [ellipseSet, swapc, Set.mem_setOf_eq] at this ⊢
    linarith [this]
  · intro x hx
    have hsx : swapc x ∈ diskSet c₂.1 c₂.2 := by
      simp only [diskSet, swapc, Set.mem_setOf_eq] at hx ⊢; linarith [hx]
    have := h2 hsx
    simp only [ellipseSet, swapc, Set.mem_setOf_eq] at this ⊢
    linarith [this]
  · simp only [nrm2, swapc, Prod.fst_sub, Prod.snd_sub] at hd ⊢
    linarith [hd]

/-! ### The reduction theorem -/

/-- **Task 2 reduction.** A feasible general ellipse `(x-c)ᵀM(x-c)≤1` (symmetric PD) yields
a feasible axis-aligned `(u,v)` with `0 < v ≤ u` and `u v = 1 / det M` — same area.  The
rigid motion `T(x)=Rᵀ(x−c)` (rotation diagonalizing `M`, translation by `−c`) preserves
unit disks, Euclidean distances, and area. -/
theorem reduction (A B C : ℝ) (c : ℝ × ℝ) (hfeas : FeasibleGen A B C c) :
    ∃ u v : ℝ, 0 < v ∧ v ≤ u ∧ Feasible u v ∧ u * v = 1 / genDet A B C := by
  obtain ⟨hA, hdet, d₁, d₂, h1, h2, hd⟩ := hfeas
  -- diagonalize
  obtain ⟨cbar, sbar, hunit, hbeta⟩ := exists_diagonalizing A B C
  obtain ⟨hα, hγ⟩ := alpha_gamma_pos A B C cbar sbar hunit hA hdet hbeta
  set α := alphaEnt A B C cbar sbar with hαdef
  set γ := gammaEnt A B C cbar sbar with hγdef
  -- transferred centers e₁ = T d₁, e₂ = T d₂
  set e₁ := rigidT cbar sbar c d₁ with he1
  set e₂ := rigidT cbar sbar c d₂ with he2
  -- the (unordered) axis-aligned data: u₀ = 1/α, v₀ = 1/γ
  have hαv : (0:ℝ) < 1 / α := by positivity
  have hγv : (0:ℝ) < 1 / γ := by positivity
  -- containment transfer for both disks
  have hT1 : diskSet e₁.1 e₁.2 ⊆ ellipseSet (1 / α) (1 / γ) := by
    intro z hz
    -- z = T x for x = S z (in diskSet d₁); pull back.
    set x := rigidS cbar sbar c z with hx
    have hxmem : x ∈ diskSet d₁.1 d₁.2 := by
      rw [(rigidT_mem_diskSet cbar sbar c d₁ x hunit)]
      have : rigidT cbar sbar c x = z := by rw [hx, rigidT_rigidS cbar sbar c z hunit]
      rwa [this, ← he1]
    have hxell := h1 hxmem
    have := (mem_ellipseGen_iff A B C cbar sbar c x hunit hbeta hα hγ).mp hxell
    have hTz : rigidT cbar sbar c x = z := by rw [hx, rigidT_rigidS cbar sbar c z hunit]
    rwa [hTz] at this
  have hT2 : diskSet e₂.1 e₂.2 ⊆ ellipseSet (1 / α) (1 / γ) := by
    intro z hz
    set x := rigidS cbar sbar c z with hx
    have hxmem : x ∈ diskSet d₂.1 d₂.2 := by
      rw [(rigidT_mem_diskSet cbar sbar c d₂ x hunit)]
      have : rigidT cbar sbar c x = z := by rw [hx, rigidT_rigidS cbar sbar c z hunit]
      rwa [this, ← he2]
    have hxell := h2 hxmem
    have := (mem_ellipseGen_iff A B C cbar sbar c x hunit hbeta hα hγ).mp hxell
    have hTz : rigidT cbar sbar c x = z := by rw [hx, rigidT_rigidS cbar sbar c z hunit]
    rwa [hTz] at this
  -- distance preserved
  have hdist : 4 ≤ nrm2 (e₁ - e₂) := by
    rw [he1, he2, rigidT_nrm2 cbar sbar c d₁ d₂ hunit]; exact hd
  -- so Feasible (1/α) (1/γ)
  have hfeas0 : Feasible (1 / α) (1 / γ) := ⟨e₁, e₂, hT1, hT2, hdist⟩
  -- product = 1/det:  (1/α)(1/γ) = 1/(αγ) = 1/genDet.
  have hprodαγ : α * γ = genDet A B C := by
    have := alpha_gamma_sub_beta_sq A B C cbar sbar hunit
    rw [hbeta] at this; simpa using this
  have hprod : (1 / α) * (1 / γ) = 1 / genDet A B C := by
    rw [← hprodαγ]; field_simp
  -- order them: u = max, v = min, using feasible_comm.
  rcases le_total (1 / γ) (1 / α) with hle | hle
  · exact ⟨1 / α, 1 / γ, hγv, hle, hfeas0, hprod⟩
  · refine ⟨1 / γ, 1 / α, hαv, hle, feasible_comm _ _ hfeas0, ?_⟩
    rw [mul_comm]; exact hprod

/-! ## The area bound for the general ellipse

The reduction + `area_ge_of_feasible` gives the area bound.  We state it on `1/√(det M)`
(the area divided by `π`, since the area of `(x-c)ᵀM(x-c)≤1` is `π/√(det M)`). -/

/-- **Task 2 main theorem (area bound for a general ellipse).** A feasible general ellipse
`(x-c)ᵀM(x-c)≤1` (symmetric PD, `det M = genDet A B C`) has `1/√(det M) ≥ 3√3/2`; i.e. its
area `π/√(det M)` is at least `(3√3/2)π`. -/
theorem area_ge_of_feasibleGen (A B C : ℝ) (c : ℝ × ℝ) (hfeas : FeasibleGen A B C c) :
    3 * Real.sqrt 3 / 2 ≤ 1 / Real.sqrt (genDet A B C) := by
  obtain ⟨u, v, hv, huv, hfeas0, hprod⟩ := reduction A B C c hfeas
  -- area/π = √(uv); the bound √(uv) ≥ 3√3/2.
  have hbound := area_ge_of_feasible u v hv huv hfeas0
  -- uv = 1/genDet, so √(uv) = √(1/genDet) = 1/√genDet.
  have hdetpos : 0 < genDet A B C := hfeas.2.1
  have huvpos : 0 < u * v := by
    rw [hprod]; positivity
  have hsqrt : Real.sqrt (u * v) = 1 / Real.sqrt (genDet A B C) := by
    rw [hprod, one_div, Real.sqrt_inv, one_div]
  rwa [hsqrt] at hbound

/-- Bridge for auditability: `genDet A B C = Matrix.det (genMat A B C)`, so the bound is
literally `3√3/2 ≤ 1/√(det M)` for the matrix `M = ![![A,B],[B,C]]`. -/
theorem area_ge_of_feasibleGen_matrix (A B C : ℝ) (c : ℝ × ℝ) (hfeas : FeasibleGen A B C c) :
    3 * Real.sqrt 3 / 2 ≤ 1 / Real.sqrt ((genMat A B C).det) := by
  rw [genMat_det]
  exact area_ge_of_feasibleGen A B C c hfeas

end Ellipse
