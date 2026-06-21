import Ellipse.Main
import Mathlib.Topology.MetricSpace.Basic
import Mathlib.Analysis.InnerProductSpace.EuclideanDist

/-!
# Task 1: interior-disjoint ⟺ centers ≥ 2 apart, for unit disks

The main theorem (`Ellipse.area_ge_of_feasible`) encodes "two interior-disjoint unit
disks" as "centers at Euclidean distance ≥ 2" (`4 ≤ nrm2 (c₁ - c₂)`).  Here we show that
encoding is *faithful*: two closed unit disks have disjoint interiors iff their centers
are at Euclidean distance ≥ 2.

We work with the explicit sets `diskSet cx cy = {p | (p.1-cx)² + (p.2-cy)² ≤ 1}` (the
*metric* on `ℝ × ℝ` is the sup-norm, so we do NOT use `Metric.closedBall`).  We first
characterize the interior as the strict set `{p | (p.1-cx)² + (p.2-cy)² < 1}`, then prove
the equivalence elementarily.
-/

namespace Ellipse

open Set

/-- The *open* unit disk centered at `(cx, cy)` (Euclidean), as an explicit set. -/
def openDiskSet (cx cy : ℝ) : Set (ℝ × ℝ) :=
  {p : ℝ × ℝ | (p.1 - cx) ^ 2 + (p.2 - cy) ^ 2 < 1}

/-- The squared Euclidean distance from `p` to the center `(cx, cy)`. -/
private noncomputable def f (cx cy : ℝ) (p : ℝ × ℝ) : ℝ :=
  (p.1 - cx) ^ 2 + (p.2 - cy) ^ 2

private theorem continuous_f (cx cy : ℝ) : Continuous (f cx cy) := by
  unfold f
  fun_prop

/-- The open disk set is open (preimage of `(-∞, 1)` under the continuous `f`). -/
theorem isOpen_openDiskSet (cx cy : ℝ) : IsOpen (openDiskSet cx cy) := by
  have : openDiskSet cx cy = (f cx cy) ⁻¹' (Set.Iio 1) := by
    ext p; simp [openDiskSet, f, Set.mem_Iio]
  rw [this]
  exact (continuous_f cx cy).isOpen_preimage _ isOpen_Iio

theorem openDiskSet_subset_diskSet (cx cy : ℝ) :
    openDiskSet cx cy ⊆ diskSet cx cy := by
  intro p hp
  simp only [openDiskSet, diskSet, Set.mem_setOf_eq] at *
  linarith

/-! ## The interior of the closed disk is the open disk.

The open disk is open and ⊆ the closed disk, so it is ⊆ interior.  Conversely a
*boundary* point (where `f = 1`) is not interior: any neighborhood contains points just
outside, found by moving radially outward from the center. -/

/-- A boundary point `p` (with `f p = 1`) of the closed disk is not in its interior. -/
private theorem boundary_not_interior (cx cy : ℝ) (p : ℝ × ℝ)
    (hp : (p.1 - cx) ^ 2 + (p.2 - cy) ^ 2 = 1) :
    p ∉ interior (diskSet cx cy) := by
  intro hmem
  -- p is in an open set ⊆ diskSet; so some metric ball around p is ⊆ diskSet.
  rw [mem_interior] at hmem
  obtain ⟨t, htsub, hopen, hpt⟩ := hmem
  rw [Metric.isOpen_iff] at hopen
  obtain ⟨ε, hε, hball⟩ := hopen p hpt
  -- Move radially outward by a small amount δ in the direction (p - center)/|p - center|.
  -- Since f p = 1, the radius |p - center| = 1, so the unit outward direction is (p - center).
  -- Set q = p + δ • (p - center) for small δ > 0; then q is at distance δ (sup or euclid)
  -- from p, inside the ball, but f q > 1.
  -- Choose δ small enough that q ∈ Metric.ball p ε (sup-metric distance < ε), but f q > 1.
  set dx : ℝ := p.1 - cx with hdx
  set dy : ℝ := p.2 - cy with hdy
  -- pick δ = ε/2 capped below 1 to keep it simple; the perturbation q = p + δ•(dx,dy).
  set δ : ℝ := min (ε / 2) (1 / 2) with hδdef
  have hδpos : 0 < δ := by
    rw [hδdef]; exact lt_min (by linarith) (by norm_num)
  have hδlt : δ < ε := by
    rw [hδdef]
    calc min (ε / 2) (1 / 2) ≤ ε / 2 := min_le_left _ _
      _ < ε := by linarith
  set q : ℝ × ℝ := (p.1 + δ * dx, p.2 + δ * dy) with hqdef
  -- distance from q to p in the sup-metric is max(|δ dx|, |δ dy|) ≤ δ * max(|dx|,|dy|).
  -- We have dx² + dy² = 1, so |dx| ≤ 1 and |dy| ≤ 1, hence the sup-distance ≤ δ < ε.
  have hdsq : dx ^ 2 + dy ^ 2 = 1 := by rw [hdx, hdy]; exact hp
  have hdx1 : |dx| ≤ 1 := by
    nlinarith [sq_nonneg dy, abs_nonneg dx, sq_abs dx, hdsq]
  have hdy1 : |dy| ≤ 1 := by
    nlinarith [sq_nonneg dx, abs_nonneg dy, sq_abs dy, hdsq]
  have hqdist : dist q p < ε := by
    rw [Prod.dist_eq]
    apply lt_of_le_of_lt (max_le _ _) hδlt
    · rw [hqdef]; simp only [Real.dist_eq]
      rw [show p.1 + δ * dx - p.1 = δ * dx by ring, abs_mul, abs_of_pos hδpos]
      nlinarith [hdx1, hδpos.le, abs_nonneg dx]
    · rw [hqdef]; simp only [Real.dist_eq]
      rw [show p.2 + δ * dy - p.2 = δ * dy by ring, abs_mul, abs_of_pos hδpos]
      nlinarith [hdy1, hδpos.le, abs_nonneg dy]
  -- so q ∈ ball ⊆ t ⊆ diskSet, giving f q ≤ 1.
  have hqmem : q ∈ diskSet cx cy := htsub (hball (by rwa [Metric.mem_ball]))
  simp only [diskSet, Set.mem_setOf_eq] at hqmem
  -- but f q = (1 + δ)² (dx² + dy²) = (1+δ)² > 1, contradiction.
  have hfq : (q.1 - cx) ^ 2 + (q.2 - cy) ^ 2 = (1 + δ) ^ 2 := by
    rw [hqdef]
    simp only
    have e1 : p.1 + δ * dx - cx = (1 + δ) * dx := by rw [hdx]; ring
    have e2 : p.2 + δ * dy - cy = (1 + δ) * dy := by rw [hdy]; ring
    rw [e1, e2]
    nlinarith [hdsq]
  rw [hfq] at hqmem
  nlinarith [hδpos, hqmem]

/-- **Interior characterization.** The interior of the closed unit disk is the open
unit disk. -/
theorem interior_diskSet (cx cy : ℝ) :
    interior (diskSet cx cy) = openDiskSet cx cy := by
  apply Set.Subset.antisymm
  · -- interior ⊆ open disk: a point of the interior with f = 1 is excluded; else f < 1.
    intro p hp
    simp only [openDiskSet, Set.mem_setOf_eq]
    by_contra hcon
    rw [not_lt] at hcon  -- 1 ≤ (p.1-cx)² + (p.2-cy)²
    -- p ∈ interior ⊆ diskSet, so f p ≤ 1, hence f p = 1; then boundary_not_interior.
    have hmemdisk : p ∈ diskSet cx cy := interior_subset hp
    have hle : (p.1 - cx) ^ 2 + (p.2 - cy) ^ 2 ≤ 1 := by
      simpa only [diskSet, Set.mem_setOf_eq] using hmemdisk
    have heq : (p.1 - cx) ^ 2 + (p.2 - cy) ^ 2 = 1 := le_antisymm hle hcon
    exact boundary_not_interior cx cy p heq hp
  · -- open disk ⊆ interior: open disk is open and ⊆ diskSet.
    exact (isOpen_openDiskSet cx cy).subset_interior_iff.mpr
      (openDiskSet_subset_diskSet cx cy)

/-! ## The disjointness equivalence

Two open unit disks meet iff their centers are < 2 apart.  Combined with the interior
characterization, this gives the faithful encoding. -/

/-- **Task 1, main equivalence.** Two closed unit disks have disjoint interiors iff their
centers are at Euclidean distance ≥ 2 (`4 ≤ nrm2 (a - b)`). -/
theorem interior_disjoint_iff (a b : ℝ × ℝ) :
    interior (diskSet a.1 a.2) ∩ interior (diskSet b.1 b.2) = ∅ ↔
      4 ≤ nrm2 (a - b) := by
  rw [interior_diskSet, interior_diskSet]
  rw [Set.eq_empty_iff_forall_notMem]
  simp only [openDiskSet, nrm2, Prod.fst_sub, Prod.snd_sub, Set.mem_inter_iff,
    Set.mem_setOf_eq, not_and]
  constructor
  · -- (⟹) contrapositive: if centers < 2 apart, the midpoint is in both open disks.
    intro h
    by_contra hcon
    rw [not_le] at hcon  -- nrm2 (a - b) < 4
    -- midpoint m = ((a.1+b.1)/2, (a.2+b.2)/2)
    set m : ℝ × ℝ := ((a.1 + b.1) / 2, (a.2 + b.2) / 2) with hm
    -- f_a m = ((a.1+b.1)/2 - a.1)² + ... = ((b.1-a.1)/2)² + ((b.2-a.2)/2)² = nrm2(a-b)/4 < 1
    have hfa : (m.1 - a.1) ^ 2 + (m.2 - a.2) ^ 2 = ((a.1 - b.1) ^ 2 + (a.2 - b.2) ^ 2) / 4 := by
      rw [hm]; simp only; ring
    have hfb : (m.1 - b.1) ^ 2 + (m.2 - b.2) ^ 2 = ((a.1 - b.1) ^ 2 + (a.2 - b.2) ^ 2) / 4 := by
      rw [hm]; simp only; ring
    have hma : (m.1 - a.1) ^ 2 + (m.2 - a.2) ^ 2 < 1 := by rw [hfa]; linarith
    have hmb : (m.1 - b.1) ^ 2 + (m.2 - b.2) ^ 2 < 1 := by rw [hfb]; linarith
    exact (h m hma) hmb
  · -- (⟸): if centers ≥ 2 apart, no point is in both open disks (triangle inequality).
    intro hge p hpa hpb
    -- p in both: (p-a)² < 1 and (p-b)² < 1.  But (a-b)² ≤ 2((p-a)²+(p-b)²) < 4.
    -- Sum of squared distances bounds the squared center distance:
    -- (a.i - b.i)² = ((a.i - p.i) + (p.i - b.i))² ≤ 2((a.i-p.i)² + (p.i-b.i)²).
    have hx : (a.1 - b.1) ^ 2 ≤ 2 * ((p.1 - a.1) ^ 2 + (p.1 - b.1) ^ 2) := by
      nlinarith [sq_nonneg ((p.1 - a.1) - (p.1 - b.1)), sq_nonneg ((p.1 - a.1) + (p.1 - b.1))]
    have hy : (a.2 - b.2) ^ 2 ≤ 2 * ((p.2 - a.2) ^ 2 + (p.2 - b.2) ^ 2) := by
      nlinarith [sq_nonneg ((p.2 - a.2) - (p.2 - b.2)), sq_nonneg ((p.2 - a.2) + (p.2 - b.2))]
    -- combine: (a-b)² ≤ 2((p-a)² + (p-b)²) < 2(1+1) = 4, contradicting ≥ 4.
    nlinarith [hx, hy, hpa, hpb, hge]

/-! ## Transfer to a literal interior-disjoint feasibility predicate

We restate `Feasible` with the *literal* interior-disjoint condition and show it is
equivalent to the distance-encoded `Feasible`.  The main theorem then transfers verbatim
to the interior-disjoint statement. -/

/-- Feasibility with the *literal* interior-disjoint condition. -/
def Feasible' (u v : ℝ) : Prop :=
  ∃ c₁ c₂ : ℝ × ℝ,
    diskSet c₁.1 c₁.2 ⊆ ellipseSet u v ∧
    diskSet c₂.1 c₂.2 ⊆ ellipseSet u v ∧
    interior (diskSet c₁.1 c₁.2) ∩ interior (diskSet c₂.1 c₂.2) = ∅

/-- `Feasible'` (literal interior-disjoint) is equivalent to `Feasible` (centers ≥ 2). -/
theorem feasible'_iff_feasible (u v : ℝ) : Feasible' u v ↔ Feasible u v := by
  unfold Feasible' Feasible
  constructor
  · rintro ⟨c₁, c₂, h1, h2, hdisj⟩
    exact ⟨c₁, c₂, h1, h2, (interior_disjoint_iff c₁ c₂).mp hdisj⟩
  · rintro ⟨c₁, c₂, h1, h2, hdist⟩
    exact ⟨c₁, c₂, h1, h2, (interior_disjoint_iff c₁ c₂).mpr hdist⟩

/-- **Main theorem, literal interior-disjoint form.** Any ellipse `x²/u + y²/v ≤ 1`
(`u ≥ v > 0`) holding two unit disks with *disjoint interiors* has `√(uv) ≥ 3√3/2`. -/
theorem area_ge_of_feasible' (u v : ℝ) (hv : 0 < v) (huv : v ≤ u)
    (hfeas : Feasible' u v) :
    3 * Real.sqrt 3 / 2 ≤ Real.sqrt (u * v) :=
  area_ge_of_feasible u v hv huv ((feasible'_iff_feasible u v).mp hfeas)

end Ellipse
