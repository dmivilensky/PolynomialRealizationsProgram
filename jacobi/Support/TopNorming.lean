import jacobi.Support.TopFullUniform
import jacobi.Support.TopNormalization
import jacobi.Reference.Orthogonality

/-!
Article: jacobi, Appendix C.3 (support weights and segment bounds).
The genuine top-node limiting squared norm is exactly the printed
Gamma amplitude times the original reference ground-state norm.
All normalizations come from the already proved original functions.
Use: topProfile_reference_square identifies the genuine support top-node limit's norm with the same actual reference norming integral used by Proposition C.2.
-/
namespace jacobi.Support
noncomputable section
open Real Set MeasureTheory jacobi.Reference

/-- The original reference ground eigenfunction is precisely its original normalized sine-power prefactor.
Use: topProfile_reference_square identifies the genuine support top-node limit's norm with the same actual reference norming integral used by Proposition C.2.
Article: jacobi, Appendix C.3 (support weights and segment bounds).
Proof: the original degree-zero normalized Jacobi polynomial is exactly one. -/
theorem reference_ground (a t:ℝ) : eigenfunction a 0 t=weight a t := by
  simp [eigenfunction,jacobi.Jacobi.angular,jacobi.Jacobi.shiftedPolynomial,jacobi.Jacobi.coefficient_zero]

/-- The genuine support top-node limiting squared amplitude is the printed Gamma scale times the actual reference ground eigenfunction square.
Use: topProfile_norming evaluates the full original limiting norm for the genuine top-node spectral probability.
Article: jacobi, Appendix C.3 (support weights and segment bounds).
Proof: the exact original top-profile square has its proved Gamma amplitude, and the actual reference ground function is the same positive sine power in endpoint normalization. -/
theorem topProfile_reference_square {a b:ℝ} (ha:-1<a) (hb:-1<b) {t:ℝ} (ht:t∈Icc 0 1) :
    topProfile a b t^2=topAmplitudeSquare a b*(eigenfunction a 0 t)^2 := by
  have hs : 0≤sin (π*t) := sin_nonneg_of_mem_Icc ⟨mul_nonneg pi_pos.le ht.1,by nlinarith [pi_pos,ht.2]⟩
  rw [topProfile_sq ha hb hs,reference_ground,weight]
  congr 1
  rw [← rpow_mul_natCast (div_nonneg hs pi_pos.le)]
  congr 1
  ring

/-- The full genuine support top-node limiting norm equals its actual printed Gamma amplitude times the original positive reference norming integral.
Use: topWeight_limit identifies the actual original spectral weight limit with the exact printed positive normalization, rather than an unspecified integral constant.
Article: jacobi, Appendix C.3 (complex edge-wave convergence).
Proof: the proved actual profile-square identity holds throughout the physical integration interval; pull its literal constant out of the convergent original integral. -/
theorem topProfile_norming {a b:ℝ} (ha:-1<a) (hb:-1<b) :
    (∫t in (0:ℝ)..1,topProfile a b t^2)=topAmplitudeSquare a b*norming a 0 := by
  rw [norming,← intervalIntegral.integral_const_mul]
  apply intervalIntegral.integral_congr_uIoo
  intro t ht
  apply topProfile_reference_square ha hb
  have h : t∈Ioo (0:ℝ) 1 := by simpa only [uIoo_of_lt (by norm_num : (0:ℝ)<1)] using ht
  exact ⟨h.1.le,h.2.le⟩

end
end jacobi.Support
