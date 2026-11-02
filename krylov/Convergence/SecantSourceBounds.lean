import krylov.Functions.SegmentHessian
import krylov.Nonlinear.GradientQuadratic
import krylov.Functions.NativeRFCSymmetry

/-!
Article: main_krylov, thm:G, thm:Ip and lem:ss1-local.
Use: sharp actual segment estimates, before constructing any sliding model.
Source: the fundamental theorem of calculus and the half-weight endpoint
estimate already proved in SegmentHessian. The resulting constants are the
constants in the original Appendix G proof.
-/

namespace krylov.Convergence
noncomputable section
open Set krylov.Functions chebyshev1.Nonlinear
open scoped NNReal
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]

/-- A genuine segment secant differs from the limiting Hessian by the sharp
half-weighted endpoint radius. -/
theorem secant_operator_endpoint_bound (H : E → E →L[ℝ] E)
    (S : Set E) (hS : Convex ℝ S) (h₀ : (0:E)∈S)
    {L : ℝ≥0} (hH : LipschitzOnWith L H S) (a b : E) (ha : a∈S) (hb : b∈S) :
    ‖averagedDerivative H a (b-a)-H 0‖≤(L:ℝ)/2*(‖a‖+‖b‖) := by
  have hp t (ht : t∈Icc (0:ℝ) 1) : a+t • (b-a)∈S := by
    apply hS.add_smul_mem ha _ ht
    simpa only [add_sub_cancel] using hb
  have hc := hH.continuousOn.comp
    (continuous_const.add (continuous_id.smul continuous_const)).continuousOn hp
  have hh := averagedHessian_endpoint_bound H a (b-a) 0 0 L hc
    (by simpa only [smul_zero,zero_add] using
      (continuousOn_const : ContinuousOn (fun _ : ℝ=>H 0) (Icc 0 1)))
    L.coe_nonneg (fun t ht=>by
      simpa only [smul_zero,zero_add,sub_zero] using hH.norm_sub_le (hp t ht) h₀)
  simpa only [averagedDerivative,smul_zero,zero_add,
    intervalIntegral.integral_const,sub_zero,one_smul,add_sub_cancel,
    sub_zero] using hh

/-- Actual gradient differences have the same sharp relative secant error.
The observed images are derived by the FTC, rather than postulated. -/
theorem secant_image_endpoint_bound (G : E → E) (H : E → E →L[ℝ] E)
    (S : Set E) (hS : Convex ℝ S) (h₀ : (0:E)∈S)
    {L : ℝ≥0} (hH : LipschitzOnWith L H S)
    (hG : ∀ z∈S, HasFDerivAt G (H z) z)
    (a b : E) (ha : a∈S) (hb : b∈S) :
    ‖G b-G a-H 0 (b-a)‖≤(L:ℝ)/2*(‖a‖+‖b‖)*‖b-a‖ := by
  have hp t (ht : t∈Icc (0:ℝ) 1) : a+t • (b-a)∈S := by
    apply hS.add_smul_mem ha _ ht
    simpa only [add_sub_cancel] using hb
  have hc := hH.continuousOn.comp
    (continuous_const.add (continuous_id.smul continuous_const)).continuousOn hp
  have he := averagedDerivative_apply G H a (b-a) hc (fun t ht=>hG _ (hp t ht))
  simp only [add_sub_cancel] at he
  have hid : G b-G a-H 0 (b-a)=(averagedDerivative H a (b-a)-H 0) (b-a) := by
    rw [_root_.sub_apply,he]
  rw [hid]
  exact ((averagedDerivative H a (b-a)-H 0).le_opNorm _).trans
    (mul_le_mul_of_nonneg_right (secant_operator_endpoint_bound H S hS h₀ hH a b ha hb)
      (norm_nonneg _))

/-- The actual radial gradient model has the exact one-half quadratic error. -/
theorem radial_gradient_endpoint_bound (G : E → E) (H : E → E →L[ℝ] E)
    (S : Set E) (hS : Convex ℝ S) (h₀ : (0:E)∈S)
    {L : ℝ≥0} (hH : LipschitzOnWith L H S)
    (hG : ∀ z∈S, HasFDerivAt G (H z) z) (hG₀ : G 0=0)
    (x : E) (hx : x∈S) :
    ‖G x-H 0 x‖≤(L:ℝ)/2*‖x‖^2 := by
  have hh := secant_image_endpoint_bound G H S hS h₀ hH hG 0 x h₀ hx
  simpa only [hG₀,sub_zero,norm_zero,zero_add,pow_two,mul_assoc] using hh

end
end krylov.Convergence
