import chebyshev1.Nonlinear.AveragedHessian

/-!
Article: main_krylov, thm:RFCS and apG:sc(iii), actual probe/step Hessian comparison.
Use: Reuse the earlier proved segment-averaged derivative to identify actual
probe secants, compare true shared-origin averaged Hessians with the sharp
one-half Lipschitz factor and extend bounded probe averages through zero.
Source: the earlier Nonlinear.averagedDerivative_apply FTC theorem, the real
Bochner integral norm inequality and the exact integral of t on [0,1].
-/

namespace krylov.Nonlinear
noncomputable section
open Set MeasureTheory chebyshev1.Nonlinear
open scoped NNReal
variable {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [NormedAddCommGroup F] [NormedSpace ℝ F]

/-- Two genuine shared-origin segment-averaged derivatives differ by at most half the Lipschitz constant times their endpoint displacement.
Use: Supply the real nonlinear bounded-probe and final probe-mismatch foundations of the original RFC-S consequence.
Article: main_krylov, thm:RFCS, original nonlinear averaged-Hessian comparison.
Proof: Use the genuine segment integral and FTC, integrate the exact shared-origin distance weight t, and retain the original real query endpoints.
-/
theorem averagedDerivative_segment_comparison (A : E → E →L[ℝ] F) (x u v : E) (L : ℝ)
    (hu : ContinuousOn (fun t : ℝ => A (x+t • u)) (Icc 0 1))
    (hv : ContinuousOn (fun t : ℝ => A (x+t • v)) (Icc 0 1))
    (hlip : ∀ t∈Icc (0 : ℝ) 1,
      ‖A (x+t • u)-A (x+t • v)‖≤L*‖(x+t • u)-(x+t • v)‖) :
    ‖averagedDerivative A x u-averagedDerivative A x v‖≤L*‖u-v‖/2 := by
  -- Subtract the two genuine operator integrals before integrating their shared-origin endpoint distance, whose exact weight integral is one half.
  have hiu := hu.intervalIntegrable_of_Icc (μ := volume) (by norm_num : (0 : ℝ)≤1)
  have hiv := hv.intervalIntegrable_of_Icc (μ := volume) (by norm_num : (0 : ℝ)≤1)
  rw [averagedDerivative,averagedDerivative,← intervalIntegral.integral_sub hiu hiv]
  have hb := intervalIntegral.norm_integral_le_of_norm_le (by norm_num : (0 : ℝ)≤1)
    (f := fun t : ℝ => A (x+t • u)-A (x+t • v)) (g := fun t : ℝ => t*(L*‖u-v‖)) (μ := volume)
    (by
      apply Filter.Eventually.of_forall
      intro t ht
      have ht' : t∈Icc (0 : ℝ) 1 := ⟨ht.1.le,ht.2⟩
      have he : (x+t • u)-(x+t • v)=t • (u-v) := by rw [smul_sub]; abel
      simpa only [he,norm_smul,Real.norm_eq_abs,abs_of_nonneg ht'.1,mul_left_comm,mul_comm,mul_assoc] using hlip t ht')
    ((continuous_id.mul continuous_const).intervalIntegrable 0 1)
  convert hb using 1
  rw [intervalIntegral.integral_mul_const,integral_id]
  ring

/-- A genuine local Hessian Lipschitz bound gives the exact one-half operator mismatch bound on any two actual enclosed query segments.
Use: Supply the real nonlinear bounded-probe and final probe-mismatch foundations of the original RFC-S consequence.
Article: main_krylov, thm:RFCS, original nonlinear averaged-Hessian comparison.
Proof: Use the genuine segment integral and FTC, integrate the exact shared-origin distance weight t, and retain the original real query endpoints.
-/
theorem averagedDerivative_comparison_lipschitzOn (A : E → E →L[ℝ] F) (x u v : E)
    {L : ℝ≥0} {K : Set E} (hL : LipschitzOnWith L A K)
    (hu : ∀ t∈Icc (0 : ℝ) 1, x+t • u∈K) (hv : ∀ t∈Icc (0 : ℝ) 1, x+t • v∈K) :
    ‖averagedDerivative A x u-averagedDerivative A x v‖≤(L : ℝ)*‖u-v‖/2 := by
  apply averagedDerivative_segment_comparison
  · exact hL.continuousOn.comp (continuous_const.add (continuous_id.smul continuous_const)).continuousOn hu
  · exact hL.continuousOn.comp (continuous_const.add (continuous_id.smul continuous_const)).continuousOn hv
  · intro t ht
    exact hL.norm_sub_le (hu t ht) (hv t ht)

/-- The normalized genuine segment average at zero displacement is precisely the actual derivative at its original base point.
Use: Supply the real nonlinear bounded-probe and final probe-mismatch foundations of the original RFC-S consequence.
Article: main_krylov, thm:RFCS, original nonlinear averaged-Hessian comparison.
Proof: Use the genuine segment integral and FTC, integrate the exact shared-origin distance weight t, and retain the original real query endpoints.
-/
theorem averagedDerivative_zero [CompleteSpace F] (A : E → E →L[ℝ] F) (x : E) :
    averagedDerivative A x 0=A x := by simp [averagedDerivative]

/-- Every nonzero actual finite gradient probe has exactly the genuine segment-averaged derivative action as its measured normalized secant.
Use: Supply the real nonlinear bounded-probe and final probe-mismatch foundations of the original RFC-S consequence.
Article: main_krylov, thm:RFCS, original nonlinear averaged-Hessian comparison.
Proof: Use the genuine segment integral and FTC, integrate the exact shared-origin distance weight t, and retain the original real query endpoints.
-/
theorem averaged_probe_secant [CompleteSpace F] (g : E → F) (A : E → E →L[ℝ] F) (x d : E) {h : ℝ} (hh : h≠0)
    (hA : ContinuousOn (fun t : ℝ => A (x+t • (h • d))) (Icc 0 1))
    (hg : ∀ t∈Icc (0 : ℝ) 1, HasFDerivAt g (A (x+t • (h • d))) (x+t • (h • d))) :
    h⁻¹ • (g (x+h • d)-g x)=averagedDerivative A x (h • d) d := by
  have he := averagedDerivative_apply g A x (h • d) hA hg
  rw [map_smul] at he
  rw [← he,smul_smul,inv_mul_cancel₀ hh,one_smul]


/-- The genuine averaged derivative is Lipschitz in its actual displacement with exactly half the original local derivative Lipschitz constant.
Use: Supply the real nonlinear bounded-probe and final probe-mismatch foundations of the original RFC-S consequence.
Article: main_krylov, thm:RFCS, original nonlinear averaged-Hessian comparison.
Proof: Use the genuine segment integral and FTC, integrate the exact shared-origin distance weight t, and retain the original real query endpoints.
-/
theorem averagedDerivative_lipschitzOn (A : E → E →L[ℝ] F) (x : E)
    {L : ℝ≥0} {K U : Set E} (hL : LipschitzOnWith L A K)
    (hU : ∀ u∈U, ∀ t∈Icc (0 : ℝ) 1, x+t • u∈K) :
    LipschitzOnWith (L/2) (fun u => averagedDerivative A x u) U := by
  rw [lipschitzOnWith_iff_norm_sub_le]
  intro u hu v hv
  simpa only [NNReal.coe_div,NNReal.coe_ofNat,div_mul_eq_mul_div] using
    averagedDerivative_comparison_lipschitzOn A x u v hL (hU u hu) (hU v hv)

/-- The actual normalized derivative probe family is Lipschitz in probe length, including zero length, on every genuinely enclosed local query family.
Use: Supply the real nonlinear bounded-probe and final probe-mismatch foundations of the original RFC-S consequence.
Article: main_krylov, thm:RFCS, original nonlinear averaged-Hessian comparison.
Proof: Use the genuine segment integral and FTC, integrate the exact shared-origin distance weight t, and retain the original real query endpoints.
-/
theorem averaged_probe_lipschitzOn (A : E → E →L[ℝ] F) (x d : E)
    {L : ℝ≥0} {K : Set E} {P : Set ℝ} (hL : LipschitzOnWith L A K)
    (hP : ∀ h∈P, ∀ t∈Icc (0 : ℝ) 1, x+t • (h • d)∈K) :
    LipschitzOnWith (L*‖d‖₊/2) (fun h => averagedDerivative A x (h • d)) P := by
  rw [lipschitzOnWith_iff_norm_sub_le]
  intro h hh k hk
  have hb := averagedDerivative_comparison_lipschitzOn A x (h • d) (k • d) hL (hP h hh) (hP k hk)
  rw [← sub_smul,norm_smul] at hb
  simpa only [NNReal.coe_div,NNReal.coe_mul,NNReal.coe_ofNat,coe_nnnorm] using
    hb.trans_eq (by ring)

/-- The genuine RFC-S probe and full evaluated-step averaged Hessians obey the printed one-half Lipschitz mismatch bound with the actual line/probe difference and physical correction movement.
Use: Supply the real nonlinear bounded-probe and final probe-mismatch foundations of the original RFC-S consequence.
Article: main_krylov, thm:RFCS, original nonlinear averaged-Hessian comparison.
Proof: Use the genuine segment integral and FTC, integrate the exact shared-origin distance weight t, and retain the original real query endpoints.
-/
theorem averaged_probe_step_difference (A : E → E →L[ℝ] F) (x d w : E) (α h : ℝ)
    {L : ℝ≥0} {K : Set E} (hL : LipschitzOnWith L A K)
    (ha : ∀ t∈Icc (0 : ℝ) 1, x+t • (α • d+w)∈K)
    (hh : ∀ t∈Icc (0 : ℝ) 1, x+t • (h • d)∈K) :
    ‖averagedDerivative A x (α • d+w)-averagedDerivative A x (h • d)‖≤
      (L : ℝ)/2*(|α-h| *‖d‖+‖w‖) := by
  -- Compare the actual full evaluated step to the actual probe, then separate only their true line mismatch and physical correction movement.
  have hb := averagedDerivative_comparison_lipschitzOn A x (α • d+w) (h • d) hL ha hh
  have he : (α • d+w)-h • d=(α-h) • d+w := by rw [sub_smul]; abel
  have hn : ‖(α • d+w)-h • d‖≤|α-h| *‖d‖+‖w‖ := by
    rw [he]
    simpa only [norm_smul,Real.norm_eq_abs] using norm_add_le ((α-h) • d) w
  exact hb.trans (by nlinarith [mul_le_mul_of_nonneg_left hn (show 0≤(L : ℝ) by positivity)])

end
end krylov.Nonlinear
