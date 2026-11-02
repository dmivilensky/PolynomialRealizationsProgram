import jacobi.GelfandLevitan.MidpointDiagonalZero
import jacobi.Reference.LaplaceEndpoint

/-!
Article: jacobi, Appendix C.2 (transformed ODE and Green identity).
The proved original midpoint diagonal zero removes the first Laplace
boundary term in its actual K row. The weighted kernel integral is
therefore o(1/y) relative to the midpoint exponential. This supplies
the sharper actual a/a_0 comparison needed to exclude a Robin term.
Use: midpoint_kernel_laplace_zero applies the already proved endpoint Laplace theorem to the original midpoint kernel, with its actual boundary value zero.
-/
namespace jacobi.GelfandLevitan
noncomputable section
open Real Set Filter MeasureTheory jacobi.Reference
open scoped Topology
set_option backward.isDefEq.respectTransparency false

/-- The actual absolute reflected midpoint K row, continuously extended by the original physical clamp.
Use: midpoint_kernel_laplace_zero applies the already proved endpoint Laplace theorem to the original midpoint kernel, with its actual boundary value zero.
Article: jacobi, Appendix C.2 (transformed ODE and Green identity).
-/
def midpointKernelReflected (a : ℝ) (ha : -1<a) (s : ℝ) : ℝ :=
  |transformationKernel a ha halfMidpoint (halfParameterClamp ((1/2)-s))|

/-- The actual reflected midpoint kernel row is continuous on the real line.
Use: midpoint_kernel_laplace_zero has the true continuity hypothesis at its Laplace endpoint, with the original K unchanged.
Article: jacobi, Appendix C.2 (transformed ODE and Green identity).
Proof: compose the independently proved genuine K continuity with the true continuous physical clamp and absolute value. -/
theorem midpointKernelReflected_continuous (a : ℝ) (ha : -1<a) :
    Continuous (midpointKernelReflected a ha) :=
  ((transformationKernel_continuous a ha).comp
    (continuous_const.prodMk (halfParameterClamp.continuous.comp (continuous_const.sub continuous_id)))).abs

/-- The reflected original midpoint row has genuine value zero at the Laplace endpoint.
Use: midpoint_kernel_laplace_zero obtains a vanishing leading term rather than an assumed remainder improvement.
Article: jacobi, Appendix C.2 (transformed ODE and Green identity).
Proof: the original real clamp fixes the genuine midpoint, where the independently proved actual diagonal vanishes. -/
theorem midpointKernelReflected_zero (a : ℝ) (ha : -1<a) : midpointKernelReflected a ha 0=0 := by
  have ht : halfParameterClamp ((1/2:ℝ)-0)=halfMidpoint := by
    change Set.projIcc (0:ℝ) (1/2) (by norm_num) ((1/2)-0)=halfMidpoint
    simpa only [sub_zero,halfMidpoint] using
      (Set.projIcc_of_mem (by norm_num : (0:ℝ)≤1/2) (by norm_num : (1/2:ℝ)∈Icc (0:ℝ) (1/2)))
  change |transformationKernel a ha halfMidpoint (halfParameterClamp ((1/2)-0))|=0
  rw [ht]
  change |kernelDiagonal a ha halfMidpoint|=0
  rw [kernelDiagonal_midpoint_zero,abs_zero]

/-- The actual reflected midpoint row vanishes beyond the physical integration interval.
Use: midpoint_kernel_laplace_zero identifies the full positive-half-line Laplace integral with the unchanged physical finite-interval integral.
Article: jacobi, Appendix C.2 (transformed ODE and Green identity).
Proof: beyond one half the real clamp is the original zero endpoint, where the original K right endpoint value is zero. -/
theorem midpointKernelReflected_tail_zero (a : ℝ) (ha : -1<a) {s : ℝ} (hs : 1/2≤s) :
    midpointKernelReflected a ha s=0 := by
  have ht : halfParameterClamp ((1/2)-s)=halfZero :=
    Set.projIcc_of_le_left (by norm_num) (by linarith)
  rw [midpointKernelReflected,ht,transformationKernel_zero_right,abs_zero]

/-- The actual original midpoint K row has zero first normalized Laplace boundary term.
Use: the improved original midpoint value asymptotic in the Neumann identification follows by the actual reference envelope and positive midpoint lower bound.
Article: jacobi, Appendix C.2 (transformed ODE and Green identity).
Proof: apply the proved endpoint Laplace theorem with exponent one to the genuine continuous bounded reflected K row. Its true endpoint value is zero. Its true support reduces the half-line integral to the physical half interval; reflection of that same integral supplies the original exponential normalization. -/
theorem midpoint_kernel_laplace_zero (a : ℝ) (ha : -1<a) :
    Tendsto (fun y:ℝ => y*Real.exp (-y/2)*
      (∫ s in (0:ℝ)..(1/2:ℝ),|transformationKernel a ha halfMidpoint (halfParameterClamp s)| * Real.exp (s*y)))
      atTop (𝓝 0) := by
  -- The source kernel, its endpoints and its physical support have all been fixed before invoking the shared analytic Laplace theorem.
  obtain ⟨B,hB,hbound⟩ := transformationKernel_bounded a ha
  have hb : ∃ M:ℝ,0≤M ∧ ∀ s,|midpointKernelReflected a ha s|≤M :=
    ⟨B,hB.le,fun s => by rw [midpointKernelReflected,abs_abs]; exact hbound _ _⟩
  have h := laplace_endpoint_limit (by norm_num : (0:ℝ)<1)
    (midpointKernelReflected_continuous a ha).measurable
    (midpointKernelReflected_continuous a ha).continuousAt hb
  simp only [Real.rpow_one,sub_self,Real.rpow_zero,mul_one,midpointKernelReflected_zero,mul_zero] at h
  apply h.congr'
  filter_upwards [] with y
  have hrestrict : (∫ s:ℝ in Ioi 0,Real.exp (-(y*s))*midpointKernelReflected a ha s)=
      ∫ s in (0:ℝ)..(1/2:ℝ),Real.exp (-(y*s))*midpointKernelReflected a ha s := by
    rw [intervalIntegral.integral_of_le (by norm_num : (0:ℝ)≤1/2)]
    apply setIntegral_eq_of_subset_of_forall_sdiff_eq_zero measurableSet_Ioi (fun _ hs => hs.1)
    intro s hs
    have hs' : 1/2≤s := by
      have hh := hs.1
      have hn := hs.2
      simp only [mem_Ioi,mem_Ioc,not_and,not_le] at hh hn
      exact (hn hh).le
    rw [midpointKernelReflected_tail_zero a ha hs',mul_zero]
  rw [hrestrict]
  let f := fun s:ℝ => Real.exp (-(y*s))*midpointKernelReflected a ha s
  have hr := intervalIntegral.integral_comp_sub_left f (1/2:ℝ) (a := (0:ℝ)) (b := (1/2:ℝ))
  simp only [sub_self,sub_zero] at hr
  have he (s : ℝ) : f ((1/2)-s)=Real.exp (-y/2)*
      (|transformationKernel a ha halfMidpoint (halfParameterClamp s)| * Real.exp (s*y)) := by
    dsimp [f,midpointKernelReflected]
    rw [show (1/2:ℝ)-((1/2)-s)=s by ring,
      show -(y*((1/2)-s))= -y/2+s*y by ring,Real.exp_add]
    ring
  simp_rw [he] at hr
  rw [intervalIntegral.integral_const_mul] at hr
  rw [← hr]
  ring

end
end jacobi.GelfandLevitan
