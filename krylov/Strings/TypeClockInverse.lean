import krylov.Strings.TypeClock
import Mathlib.Analysis.Calculus.Deriv.Inverse
import Mathlib.Topology.Order.MonotoneContinuity

/-!
Article: main_krylov, apC:eq:reduced.
Use: an actual inverse of a strictly increasing continuous type clock on a
finite physical window. The density need only be measurable: the inverse
formula uses an ordinary derivative at the physical point, not a C¹ inverse
function theorem.
Source: the intermediate value theorem and mathlib's local inverse derivative
formula (`HasDerivAt.of_local_left_inverse`).
-/

namespace krylov.Strings.TypeChange
noncomputable section
open Set Filter MeasureTheory Function
open scoped Topology

/-- The inverse physical position on a compact type window. Values outside
its clock image are immaterial to all local statements below. -/
def inverse (Y : ℝ → ℝ) (a b : ℝ) : ℝ → ℝ := invFunOn Y (Icc a b)

variable {Y : ℝ → ℝ} {a b : ℝ}

/-- The continuous clock traverses the entire closed type window. -/
theorem clock_surj (hab : a ≤ b) (hc : ContinuousOn Y (Icc a b)) :
    SurjOn Y (Icc a b) (Icc (Y a) (Y b)) :=
  hc.surjOn_Icc ⟨le_rfl, hab⟩ ⟨hab, le_rfl⟩

/-- The chosen inverse has its genuine physical-window value. -/
theorem inverse_mem (hab : a ≤ b) (hc : ContinuousOn Y (Icc a b))
    {y : ℝ} (hy : y ∈ Icc (Y a) (Y b)) : inverse Y a b y ∈ Icc a b :=
  invFunOn_mem (clock_surj hab hc hy)

/-- Exact right inverse throughout the closed type window. -/
theorem clock_inverse (hab : a ≤ b) (hc : ContinuousOn Y (Icc a b))
    {y : ℝ} (hy : y ∈ Icc (Y a) (Y b)) : Y (inverse Y a b y) = y :=
  invFunOn_eq (clock_surj hab hc hy)

/-- Exact left inverse throughout the closed physical window. -/
theorem inverse_clock (hm : StrictMonoOn Y (Icc a b)) {x : ℝ}
    (hx : x ∈ Icc a b) : inverse Y a b (Y x) = x :=
  hm.injOn.leftInvOn_invFunOn hx

/-- Strict monotonicity survives inversion, without regularity of the density. -/
theorem inverse_strictMonoOn (hab : a ≤ b) (hc : ContinuousOn Y (Icc a b))
    (hm : StrictMonoOn Y (Icc a b)) :
    StrictMonoOn (inverse Y a b) (Icc (Y a) (Y b)) := by
  intro y hy z hz hyz
  have hxy := inverse_mem hab hc hy
  have hxz := inverse_mem hab hc hz
  by_contra h
  have hle := hm.monotoneOn hxz hxy (le_of_not_gt h)
  rw [clock_inverse hab hc hz, clock_inverse hab hc hy] at hle
  exact hyz.not_ge hle

/-- Interior type points correspond exactly to interior physical points. -/
theorem inverse_mem_interior (hab : a ≤ b) (hc : ContinuousOn Y (Icc a b))
    (_hm : StrictMonoOn Y (Icc a b)) {y : ℝ} (hy : y ∈ Ioo (Y a) (Y b)) :
    inverse Y a b y ∈ Ioo a b := by
  have hx := inverse_mem hab hc ⟨hy.1.le, hy.2.le⟩
  constructor
  · by_contra h
    have he : inverse Y a b y = a := le_antisymm (le_of_not_gt h) hx.1
    have he' := clock_inverse hab hc ⟨hy.1.le, hy.2.le⟩
    rw [he] at he'
    exact hy.1.ne he'
  · by_contra h
    have he : inverse Y a b y = b := le_antisymm hx.2 (le_of_not_gt h)
    have he' := clock_inverse hab hc ⟨hy.1.le, hy.2.le⟩
    rw [he] at he'
    exact hy.2.ne' he'

/-- The inverse maps the open clock window onto the open physical window. -/
theorem inverse_image_interior (hab : a ≤ b) (hc : ContinuousOn Y (Icc a b))
    (hm : StrictMonoOn Y (Icc a b)) :
    inverse Y a b '' Ioo (Y a) (Y b) = Ioo a b := by
  apply Subset.antisymm
  · rintro x ⟨y, hy, rfl⟩
    exact inverse_mem_interior hab hc hm hy
  · intro x hx
    have hx' : x ∈ Icc a b := ⟨hx.1.le, hx.2.le⟩
    refine ⟨Y x, ⟨hm ⟨le_rfl, hab⟩ hx' hx.1,
      hm hx' ⟨hab, le_rfl⟩ hx.2⟩, inverse_clock hm hx'⟩

/-- Continuity of the genuine inverse at every interior type point. -/
theorem inverse_continuousAt (hab : a ≤ b) (hc : ContinuousOn Y (Icc a b))
    (hm : StrictMonoOn Y (Icc a b)) {y : ℝ} (hy : y ∈ Ioo (Y a) (Y b)) :
    ContinuousAt (inverse Y a b) y := by
  have hx := inverse_mem_interior hab hc hm hy
  apply ((inverse_strictMonoOn hab hc hm).mono Ioo_subset_Icc_self).continuousAt_of_image_mem_nhds (Ioo_mem_nhds hy.1 hy.2)
  rw [inverse_image_interior hab hc hm]
  exact Ioo_mem_nhds hx.1 hx.2

/-- The inverse-clock derivative is valid at every physical differentiability
point with positive density, with no continuity hypothesis on that density. -/
theorem inverse_hasDerivAt (hab : a ≤ b) (hc : ContinuousOn Y (Icc a b))
    (hm : StrictMonoOn Y (Icc a b)) {y v : ℝ} (hy : y ∈ Ioo (Y a) (Y b))
    (hd : HasDerivAt Y v (inverse Y a b y)) (hv : v ≠ 0) :
    HasDerivAt (inverse Y a b) v⁻¹ y := by
  apply HasDerivAt.of_local_left_inverse (inverse_continuousAt hab hc hm hy) hd hv
  filter_upwards [Ioo_mem_nhds hy.1 hy.2] with z hz
  exact clock_inverse hab hc ⟨hz.1.le, hz.2.le⟩

end
end krylov.Strings.TypeChange
