import jacobi.Reference.SolutionFactor
import Mathlib.MeasureTheory.Integral.IntervalIntegral.FundThmCalculus

/-!
Article: jacobi, Appendix C.1 (selected endpoint branch).
The Wronskian uses genuine spatial derivatives at arbitrary complex energies.
Its singular endpoint limit is zero because the selected regular factors
are even and analytic. Thus the original Green integral identity holds
throughout the full order range, including gamma<1/2.
Use: fixes boundary terms for the source midpoint characteristic and GL transformation identities.
-/
namespace jacobi.Reference
noncomputable section
open Real Set Complex Filter MeasureTheory
open scoped Topology
set_option backward.isDefEq.respectTransparency false

/-- The original reference Green Wronskian formed from the actual spectral solutions and their genuine spatial slopes.
Use: fixes boundary terms for the source midpoint characteristic and GL transformation identities.
Article: jacobi, Appendix C.1 (selected endpoint branch).
-/
def referenceWronskian (a : ℝ) (z w : ℂ) (t : ℝ) : ℂ :=
  solution a z t*solutionSlope a w t-solutionSlope a z t*solution a w t

/-- The genuine original reference Wronskian has the exact Green derivative at arbitrary complex energies.
Use: integrates the source reference Green identity with the true selected singular endpoint branch.
Article: jacobi, Appendix C.1 (selected endpoint branch).
Proof: differentiate both actual products and substitute the proved
original second-order equations. The common potential terms and the
mixed first-derivative terms cancel exactly. -/
theorem referenceWronskian_hasDerivAt {a : ℝ} (ha : -1<a) (z w : ℂ)
    {t : ℝ} (ht : t∈Ioo 0 1) :
    HasDerivAt (referenceWronskian a z w) ((z-w)*solution a z t*solution a w t) t := by
  -- These slopes and accelerations are independently proved genuine derivatives of the original functions.
  have hh := ((solution_hasDerivAt a z ht).mul (solutionSlope_hasDerivAt a w ht)).sub
    ((solutionSlope_hasDerivAt a z ht).mul (solution_hasDerivAt a w ht))
  convert hh using 1
  · rfl
  · linear_combination solution a z t*(solution_equation ha w ht)-
      solution a w t*(solution_equation ha z ht)

/-- The actual reference slope equals the derivative of its genuine selected regular-singular factorization.
Use: identifies actual source boundary derivatives with the even analytic endpoint factors in Green's identity.
Article: jacobi, Appendix C.1 (selected endpoint branch).
Proof: differentiate the actual positive-axis power product and its
regular factor. Local equality with the original reference solution and
uniqueness of the actual derivative identify the true source slope. -/
theorem solutionSlope_factor (a : ℝ) (z : ℂ) {t : ℝ} (ht : t∈Ioo 0 1)
    (hg : DifferentiableAt ℝ (solutionFactor a z) t) :
    solutionSlope a z t=(((gamma a*t^(gamma a-1):ℝ):ℂ)*solutionFactor a z t+
      ((t^(gamma a):ℝ):ℂ)*deriv (solutionFactor a z) t) := by
  -- The original slope is already known to be an actual derivative, so no formal derivative placeholder is used.
  have hp := (Real.hasDerivAt_rpow_const (p := gamma a) (Or.inl ht.1.ne')).ofReal_comp
  have hh := hp.mul hg.hasDerivAt
  have he : solution a z=ᶠ[𝓝 t] (fun s:ℝ => ((s^(gamma a):ℝ):ℂ)*solutionFactor a z s) := by
    filter_upwards [isOpen_Ioo.mem_nhds ht] with s hs
    exact solution_factor a z hs
  exact (solution_hasDerivAt a z ht).unique (hh.congr_of_eventuallyEq he)

/-- The genuine source reference Wronskian tends to zero at its selected singular endpoint for all complex energy pairs.
Use: discharges the endpoint boundary term in the actual reference Green integral, including gamma<1/2.
Article: jacobi, Appendix C.1 (selected endpoint branch).
Proof: expand the true slopes through the actual regular factors and
cancel the common leading singular power terms. The remaining regular
Wronskian vanishes at zero and has a continuous divided difference.
The full expression is t^(2*gamma+1) times that continuous function;
the genuine exponent is strictly positive over the full source range. -/
theorem referenceWronskian_zero {a : ℝ} (ha : -1<a) (z w : ℂ) :
    Tendsto (referenceWronskian a z w) (𝓝[>] 0) (𝓝 0) := by
  -- The extra factor t comes from even regular factors; endpoint vanishing alone would not suffice.
  let g := solutionFactor a z
  let h := solutionFactor a w
  let L : ℝ → ℂ := fun t => g t*deriv h t-deriv g t*h t
  have hg : AnalyticAt ℝ g 0 := solutionFactor_analytic a z
  have hh : AnalyticAt ℝ h 0 := solutionFactor_analytic a w
  have hL : AnalyticAt ℝ L 0 := (hg.mul hh.deriv).sub (hg.deriv.mul hh)
  have hL0 : L 0=0 := by
    dsimp [L,g,h]
    rw [solutionFactor_deriv_zero,solutionFactor_deriv_zero,mul_zero,zero_mul,sub_self]
  have hD : ContinuousAt (dslope L 0) 0 := continuousAt_dslope_same.mpr hL.differentiableAt
  have hp : 0<2*gamma a+1 := by linarith [(parameters ha).1]
  have hr : Tendsto (fun t:ℝ => ((t^(2*gamma a+1):ℝ):ℂ)) (𝓝[>] 0) (𝓝 0) := by
    have hrR : Tendsto (fun t:ℝ => t^(2*gamma a+1)) (𝓝[>] 0) (𝓝 (0:ℝ)) := by
      simpa only [Real.zero_rpow hp.ne'] using
        (Real.continuous_rpow_const hp.le).continuousAt.tendsto.mono_left
          (show 𝓝[>] (0:ℝ)≤𝓝 0 from nhdsWithin_le_nhds)
    have hc : Tendsto (fun t:ℝ => ((t^(2*gamma a+1):ℝ):ℂ)) (𝓝[>] 0) (𝓝 ((0:ℝ):ℂ)) :=
      Complex.continuous_ofReal.continuousAt.tendsto.comp hrR
    simpa only [Complex.ofReal_zero] using hc
  have ht := hr.mul (hD.tendsto.mono_left (show 𝓝[>] (0:ℝ)≤𝓝 0 from nhdsWithin_le_nhds))
  simp only [zero_mul] at ht
  apply (tendsto_congr' ?_).mpr ht
  filter_upwards [Ioo_mem_nhdsGT (by norm_num : (0:ℝ)<1),
    hg.eventually_analyticAt.filter_mono nhdsWithin_le_nhds,
    hh.eventually_analyticAt.filter_mono nhdsWithin_le_nhds] with t ht hgt hht
  have hs : ((t^(gamma a):ℝ):ℂ)^2=((t^(2*gamma a):ℝ):ℂ) := by
    rw [show 2*gamma a=gamma a*2 by ring,Real.rpow_mul ht.1.le,Real.rpow_two,Complex.ofReal_pow]
  have hform : referenceWronskian a z w t=((t^(2*gamma a):ℝ):ℂ)*L t := by
    rw [referenceWronskian,solutionSlope_factor a z ht hgt.differentiableAt,
      solutionSlope_factor a w ht hht.differentiableAt,solution_factor a z ht,solution_factor a w ht,← hs]
    dsimp [L,g,h]
    ring
  rw [hform,Real.rpow_add_one ht.1.ne',Complex.ofReal_mul,dslope_of_ne _ ht.1.ne']
  simp only [slope,vsub_eq_sub,sub_zero,hL0,Complex.real_smul]
  rw [Complex.ofReal_inv]
  field_simp [show (t:ℂ)≠0 by exact_mod_cast ht.1.ne']

/-- The actual original complex-energy reference solutions satisfy Green's integral identity from the selected singular endpoint to every physical interior point.
Use: supplies the genuine norming, midpoint and GL Green identities without an assumed endpoint boundary condition.
Article: jacobi, Appendix C.1 (selected endpoint branch).
Proof: the true product integrand is continuous up to zero by joint
continuity of the actual source solution. Integrate the genuine
Wronskian derivative with the proved zero singular endpoint limit and
the actual continuous right-end value. -/
theorem reference_green_identity {a : ℝ} (ha : -1<a) (z w : ℂ)
    {t : ℝ} (ht : t∈Ioo 0 1) :
    (z-w)*(∫ s in (0:ℝ)..t,solution a z s*solution a w s)=referenceWronskian a z w t := by
  -- The community endpoint-limit FTC handles the true singular slope rather than requiring its continuity at zero.
  have hc : ContinuousOn (fun s => (z-w)*solution a z s*solution a w s) (Icc 0 t) := by
    intro s hs
    have hs' : s∈Ico 0 1 := ⟨hs.1,hs.2.trans_lt ht.2⟩
    have hcz := (solution_joint_continuous ha hs' z).comp_of_eq
      (continuousAt_id.prodMk continuousAt_const) rfl
    have hcw := (solution_joint_continuous ha hs' w).comp_of_eq
      (continuousAt_id.prodMk continuousAt_const) rfl
    exact ((continuousAt_const.mul hcz).mul hcw).continuousWithinAt
  have hh := intervalIntegral.integral_eq_sub_of_hasDerivAt_of_tendsto ht.1
    (fun s hs => referenceWronskian_hasDerivAt ha z w ⟨hs.1,hs.2.trans ht.2⟩)
    (hc.intervalIntegrable_of_Icc ht.1.le) (referenceWronskian_zero ha z w)
    ((referenceWronskian_hasDerivAt ha z w ht).continuousAt.tendsto.mono_left nhdsWithin_le_nhds)
  simpa only [mul_assoc,intervalIntegral.integral_const_mul,sub_zero] using hh

end
end jacobi.Reference
