import jacobi.Reference.ContourMajorant
import jacobi.Reference.CharacteristicProduct

/-!
Article: jacobi, Appendix C.2 (exact parity splitting).
The actual energy circles lie halfway between consecutive original
reference frequencies. Every original reference denominator is
nonzero there, with a lower bound by the exact real quadratic gap.
The entire reciprocal-Gamma characteristic consequently has no zero
on any of these circles.
Use: defines the original pole-free energy circles in the parity contour argument.
-/
namespace jacobi.Reference
noncomputable section
open Real Set _root_.Complex
set_option backward.isDefEq.respectTransparency false

/-- The radius halfway between the original reference frequencies of indices m and m+1.
Use: defines the original pole-free energy circles in the parity contour argument.
Article: jacobi, Appendix C.2 (exact parity splitting).
-/
def contourRadius (a : ℝ) (m : ℕ) : ℝ := Real.pi*((m:ℝ)+gamma a+1/2)

/-- Every original midpoint contour radius is strictly positive.
Use: permits the original inverse-square contour bound and fixes the genuine energy circle radius.
Article: jacobi, Appendix C.2 (exact parity splitting).
Proof: gamma>1/4, the contour index is nonnegative and pi is positive. -/
theorem contourRadius_pos {a : ℝ} (ha : -1<a) (m : ℕ) : 0<contourRadius a m := by
  unfold contourRadius
  have hg := (parameters ha).1
  positivity

/-- The true reference spectral denominator on an original energy circle dominates its exact radial quadratic gap.
Use: contour_factor_bound estimates the literal relative spectral perturbations, rather than an auxiliary product.
Article: jacobi, Appendix C.2 (exact parity splitting).
Proof: apply both reverse triangle inequalities to the actual shifted
energy and the positive real squared reference frequency. Their norms
are exactly the prescribed original circle radius squared and varpi_l squared. -/
theorem contour_denominator_lower {a : ℝ} (_ha : -1<a) (m l : ℕ) {z : ℂ}
    (hz : ‖z-(jacobi.Jacobi.endpointCorrection a:ℂ)‖=(contourRadius a m)^2) :
    Real.pi^2*|((l:ℝ)+gamma a)^2-((m:ℝ)+gamma a+1/2)^2|≤
      ‖(eigenvalue a l:ℂ)-z‖ := by
  -- The energy shift cancels exactly; no estimate of the complex square-root branch is required.
  let p : ℝ := Real.pi^2*((l:ℝ)+gamma a)^2
  have hp : 0≤p := by dsimp [p]; positivity
  have he : (eigenvalue a l:ℂ)-z=(p:ℂ)-(z-(jacobi.Jacobi.endpointCorrection a:ℂ)) := by
    unfold eigenvalue p
    push_cast
    ring
  have hl := norm_sub_norm_le (p:ℂ) (z-(jacobi.Jacobi.endpointCorrection a:ℂ))
  have hr := norm_sub_norm_le (z-(jacobi.Jacobi.endpointCorrection a:ℂ)) (p:ℂ)
  rw [Complex.norm_real,Real.norm_eq_abs,abs_of_nonneg hp,hz] at hl hr
  rw [norm_sub_rev] at hr
  have hh := abs_le.mpr (show -(‖(p:ℂ)-(z-(jacobi.Jacobi.endpointCorrection a:ℂ))‖)≤
      p-(contourRadius a m)^2 ∧ p-(contourRadius a m)^2≤
      ‖(p:ℂ)-(z-(jacobi.Jacobi.endpointCorrection a:ℂ))‖ from ⟨by linarith,hl⟩)
  rw [he]
  have hrad : p-(contourRadius a m)^2=
      Real.pi^2*(((l:ℝ)+gamma a)^2-((m:ℝ)+gamma a+1/2)^2) := by
    dsimp [p,contourRadius]
    ring
  rw [hrad,abs_mul,abs_of_nonneg (sq_nonneg Real.pi)] at hh
  exact hh

/-- Every original reference denominator is nonzero on every original midpoint energy circle.
Use: justifies the actual relative product with reference denominators and excludes all reference poles in the parity contour integral.
Article: jacobi, Appendix C.2 (exact parity splitting).
Proof: equality of the two positive squared frequencies would force an
integer frequency index to equal a midpoint index, already excluded by halfDistance_ne_zero. -/
theorem contour_denominator_ne_zero {a : ℝ} (ha : -1<a) (m l : ℕ) {z : ℂ}
    (hz : ‖z-(jacobi.Jacobi.endpointCorrection a:ℂ)‖=(contourRadius a m)^2) :
    (eigenvalue a l:ℂ)-z≠0 := by
  -- The half-integer separation handles the entire spectral sequence, including its finite prefix.
  have hg : 0<gamma a := by linarith [(parameters ha).1]
  have hx : 0<(m:ℝ)+gamma a+1/2 := by positivity
  have hy : 0<(l:ℝ)+gamma a := by positivity
  have hne : ((l:ℝ)+gamma a)^2-((m:ℝ)+gamma a+1/2)^2≠0 := by
    intro h
    have he : (l:ℝ)-m-1/2=0 := by nlinarith
    exact halfDistance_ne_zero m l he
  have hp := mul_pos (sq_pos_of_pos Real.pi_pos) (abs_pos.mpr hne)
  intro h
  have hh := contour_denominator_lower ha m l hz
  rw [h,norm_zero] at hh
  exact (not_le_of_gt hp) hh

/-- The literal reference characteristic has no zero on any original midpoint energy circle.
Use: the contour product comparison and reference reciprocal characteristic are genuinely defined on the whole contour.
Article: jacobi, Appendix C.2 (exact parity splitting).
Proof: the proved exhaustive complex reference zero set would give a vanishing original spectral denominator. -/
theorem characteristicTau_contour_ne_zero {a : ℝ} (ha : -1<a) (m : ℕ) {z : ℂ}
    (hz : ‖z-(jacobi.Jacobi.endpointCorrection a:ℂ)‖=(contourRadius a m)^2) :
    characteristicTau a z≠0 := by
  intro h
  obtain ⟨l,rfl⟩ := (characteristicTau_zero_iff a z).mp h
  exact contour_denominator_ne_zero ha m l hz (sub_self _)

end
end jacobi.Reference
