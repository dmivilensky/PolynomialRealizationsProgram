import polyak.ModeLocking.TwoLag.ExactGap
import polyak.ModeLocking.TwoLag.ExactThreshold
import polyak.ModeLocking.Boundary.Frontier

/-! The original boundary membership and exact two-frequency determinant
at every exact point; plateau continuation uses the regular-point theorem. -/
noncomputable section
namespace polyak.ModeLocking.TwoLag.ExactData
open General Levels Geometry
variable {q : Tuning} {s : ℝ} {K L : ℕ} (D : ExactData q s K L)

include D in
theorem determinant_zero :
    (Geometry.shiftedCurve q s).lag 1 (D.u 0)*(Geometry.shiftedCurve q s).lag (-(K : ℤ)) (D.u 1)-
      (Geometry.shiftedCurve q s).lag 1 (D.u 1)*(Geometry.shiftedCurve q s).lag (-(K : ℤ)) (D.u 0)=0 := by
  have h : D.b*((Geometry.shiftedCurve q s).lag 1 (D.u 0)*(Geometry.shiftedCurve q s).lag (-(K : ℤ)) (D.u 1)-
      (Geometry.shiftedCurve q s).lag 1 (D.u 1)*(Geometry.shiftedCurve q s).lag (-(K : ℤ)) (D.u 0))=0 := by
    linear_combination (Geometry.shiftedCurve q s).lag 1 (D.u 0)*D.dual_zero 1-
      (Geometry.shiftedCurve q s).lag 1 (D.u 1)*D.dual_zero 0
  exact (mul_eq_zero.mp h).resolve_left D.b_pos.ne'

variable (D₀ : ExactData q 0 K L)

include D₀ in
theorem boundary_of_first_contact_window (hwin : InWindow K (D₀.u 0)) : q∈BoundaryInGap K :=
  (boundaryInGap_iff K q).mpr ⟨D₀.gap_of_first_contact_window hwin,D₀.sigma_eq⟩

include D₀ in
theorem boundary_determinant_zero :
    (tuningCurve q).lag 1 (D₀.u 0)*(tuningCurve q).lag (-(K : ℤ)) (D₀.u 1)-
      (tuningCurve q).lag 1 (D₀.u 1)*(tuningCurve q).lag (-(K : ℤ)) (D₀.u 0)=0 := by
  simpa only [Geometry.shiftedCurve_zero] using D₀.determinant_zero

end polyak.ModeLocking.TwoLag.ExactData
