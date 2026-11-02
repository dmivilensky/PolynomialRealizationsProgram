import jacobi.Reference.JointContinuity
import jacobi.Reference.SolutionEndpoint
import Mathlib.Analysis.Analytic.Order

/-!
Article: jacobi, Appendix C.1 (selected endpoint branch).
At every true complex energy, the original solution is t^gamma times an
even analytic regular factor with value one. The actual first derivative
of that factor vanishes at zero. A genuine Taylor argument proves the
quadratic relative remainder at each fixed energy; compact-uniform energy
bounds are a separate assertion.
Use: fixes the selected branch and the extra vanishing order in the genuine reference Green boundary term.
-/
namespace jacobi.Reference
noncomputable section
open Real Set Complex Filter Asymptotics
open scoped Topology
set_option backward.isDefEq.respectTransparency false

/-- The actual regular factor of the original arbitrary-energy reference solution at its singular left endpoint.
Use: fixes the selected branch and the extra vanishing order in the genuine reference Green boundary term.
Article: jacobi, Appendix C.1 (selected endpoint branch).
-/
def solutionFactor (a : ℝ) (z : ℂ) (t : ℝ) : ℂ :=
  (((Real.sinc (Real.pi*t))^(gamma a):ℝ):ℂ)*
    waveCore a (Complex.sqrt (z-(jacobi.Jacobi.endpointCorrection a:ℂ))) (coordinate t:ℂ)

/-- The original arbitrary-energy reference regular factor is even in its real spatial argument.
Use: its actual first derivative vanishes at zero, ensuring the source quadratic endpoint order.
Article: jacobi, Appendix C.1 (selected endpoint branch).
Proof: the actual sinc and cosine coordinates are even, so both genuine regular-factor components are unchanged by spatial reflection. -/
theorem solutionFactor_even (a : ℝ) (z : ℂ) (t : ℝ) :
    solutionFactor a z (-t)=solutionFactor a z t := by
  simp only [solutionFactor,coordinate,mul_neg,Real.sinc_neg,Real.cos_neg]

/-- The genuine regular factor of the original reference solution is analytic at the singular endpoint for every complex energy.
Use: gives the actual selected endpoint branch and a quadratic Taylor remainder without assuming a Frobenius expansion.
Article: jacobi, Proposition C.4.
Proof: the real sinc power is analytic at its positive central value.
The actual complex hypergeometric core is analytic at its zero spatial
argument; restrict scalars and compose with the genuine analytic cosine
coordinate, then multiply the two regular factors. -/
theorem solutionFactor_analytic (a : ℝ) (z : ℂ) : AnalyticAt ℝ (solutionFactor a z) 0 := by
  -- Only the regular factor is asserted analytic; the actual singular outer power is kept separate.
  have hi : AnalyticAt ℝ (fun t:ℝ => Real.pi*t) 0 := analyticAt_const.mul analyticAt_id
  have hs := (jacobi.Jacobi.sinc_analytic (Real.pi*0)).comp (f := fun t:ℝ => Real.pi*t) hi
  have hp := jacobi.Jacobi.analytic_positive_rpow hs (by norm_num) (gamma a)
  have hpc : AnalyticAt ℝ (fun t:ℝ => (((Real.sinc (Real.pi*t))^(gamma a):ℝ):ℂ)) 0 :=
    (Complex.ofRealCLM.analyticAt _).comp hp
  have hcoord : AnalyticAt ℝ coordinate 0 :=
    ((analyticAt_const.sub (Real.analyticAt_cos.comp hi)).div_const)
  have hcc : AnalyticAt ℝ (fun t:ℝ => (coordinate t:ℂ)) 0 :=
    (Complex.ofRealCLM.analyticAt _).comp hcoord
  have hc : AnalyticAt ℂ (waveCore a (Complex.sqrt (z-(jacobi.Jacobi.endpointCorrection a:ℂ)))) 0 :=
    Hypergeometric.analytic (by norm_num)
  have hh := hc.restrictScalars (𝕜 := ℝ)
  have hh' : AnalyticAt ℝ (waveCore a (Complex.sqrt (z-(jacobi.Jacobi.endpointCorrection a:ℂ)))) (coordinate 0:ℂ) := by
    simpa only [coordinate_properties.1,Complex.ofReal_zero] using hh
  exact hpc.mul (hh'.comp (f := fun t:ℝ => (coordinate t:ℂ)) hcc)

/-- The genuine arbitrary-energy endpoint regular factor has exactly normalization one.
Use: selects the original nonzero reference branch and fixes all norming constants.
Article: jacobi, Appendix C.1 (selected endpoint branch).
Proof: sinc(0)=1, the actual coordinate is zero and the genuine 2F1 central value is one. -/
theorem solutionFactor_zero (a : ℝ) (z : ℂ) : solutionFactor a z 0=1 := by
  simp only [solutionFactor,mul_zero,Real.sinc_zero,Real.one_rpow,Complex.ofReal_one,
    coordinate_properties.1,Complex.ofReal_zero,waveCore,ordinaryHypergeometric_zero,one_mul]

/-- The genuine complex-valued reference regular factor has zero first spatial derivative at the endpoint.
Use: gives the extra endpoint order in the source reference Green identities for every complex energy.
Article: jacobi, Appendix C.1 (selected endpoint branch).
Proof: differentiate its actual evenness at zero and use uniqueness of the real derivative; the derivative equals its negative. -/
theorem solutionFactor_deriv_zero (a : ℝ) (z : ℂ) : deriv (solutionFactor a z) 0=0 := by
  -- Differentiate actual evenness using the real scalar chain rule for the complex-valued regular factor.
  have hf := (solutionFactor_analytic a z).differentiableAt.hasDerivAt
  have hd : HasDerivAt (solutionFactor a z) (deriv (solutionFactor a z) 0) (-0:ℝ) := by simpa only [neg_zero] using hf
  have hn := hd.scomp 0 (hasDerivAt_neg (0:ℝ))
  have he : (fun t:ℝ => solutionFactor a z (-t))=solutionFactor a z := funext (solutionFactor_even a z)
  change HasDerivAt (fun t:ℝ => solutionFactor a z (-t)) ((-1:ℝ) • deriv (solutionFactor a z) 0) 0 at hn
  rw [he] at hn
  have hh := hn.unique hf
  simp only [neg_smul,one_smul] at hh
  linear_combination -hh/2

/-- The actual original reference solution has exactly its selected power times the genuine regular endpoint factor at every physical interior point.
Use: relates the source ODE solution and its actual derivatives to the even analytic factor in singular Green identities.
Article: jacobi, Proposition C.4.
Proof: the actual sine prefactor factors as t^gamma*sinc(pi*t)^gamma on the positive physical interval, by the already proved degree-zero reference identity. -/
theorem solution_factor (a : ℝ) (z : ℂ) {t : ℝ} (ht : t∈Ioo 0 1) :
    solution a z t=((t^(gamma a):ℝ):ℂ)*solutionFactor a z t := by
  have hp : jacobi.Jacobi.shiftedPolynomial (jacobiIndex a) (jacobiIndex a) 0=1 := by
    simp [jacobi.Jacobi.shiftedPolynomial,jacobi.Jacobi.coefficient_zero]
  have hw := eigenfunction_factor a 0 ht
  simp only [eigenfunction,regularFactor,jacobi.Jacobi.angular,hp,Polynomial.eval_one,mul_one] at hw
  unfold solution wave solutionFactor
  rw [hw,Complex.ofReal_mul]
  ring

/-- The genuine regular endpoint factor differs from one by a quadratic remainder at each fixed complex energy.
Use: proves the source selected branch with its actual extra endpoint order, including gamma<1/2.
Article: jacobi, Lemma C.1.
Proof: the actual analytic Taylor expansion has constant coefficient
one and zero linear coefficient. Its remaining quadratic factor is
analytic, hence locally bounded; multiply that bound by the true square
of the spatial argument. -/
theorem solutionFactor_quadratic (a : ℝ) (z : ℂ) :
    (fun t:ℝ => solutionFactor a z t-1)=O[𝓝 0](fun t:ℝ => t^2) := by
  -- This is a proved fixed-energy estimate; no compact-uniform energy claim is hidden in the notation.
  obtain ⟨F,hF,hEq⟩ := (solutionFactor_analytic a z).exists_eventuallyEq_sum_add_pow_mul 2
  have hFbound := hF.continuousAt.tendsto.isBigO_one ℝ
  have hmul := (isBigO_refl (fun t:ℝ => t^2) (𝓝 0)).smul hFbound
  simp only [smul_eq_mul,mul_one] at hmul
  apply hmul.congr' ?_ EventuallyEq.rfl
  filter_upwards [hEq] with t ht
  simp only [Finset.sum_range_succ,Finset.sum_range_zero,zero_add,pow_zero,
    Nat.factorial_zero,Nat.cast_one,div_one,iteratedDeriv_zero,one_smul,
    pow_one,Nat.factorial_one,iteratedDeriv_one,solutionFactor_zero,
    solutionFactor_deriv_zero,smul_zero,add_zero] at ht
  exact (sub_eq_iff_eq_add.mpr (by simpa only [add_comm] using ht)).symm

end
end jacobi.Reference
