import jacobi.Jacobi.RegularPotential
import jacobi.Jacobi.EndpointDerivatives
import Mathlib.Analysis.SpecialFunctions.Complex.Analytic

/-!
Article: jacobi, Appendix C.1 (selected endpoint branch).
The actual Jacobi Liouville wave is theta^(alpha+1/2) times a genuine even
analytic factor with its exact nonzero value at zero. This supplies the
zero endpoint Wronskian needed for Sturm comparison for every alpha>-1.
Use: proves the actual analytic endpoint factor of the Jacobi Liouville wave for all real endpoint exponents.
-/
namespace jacobi.Jacobi
noncomputable section
open Real Set Filter
open scoped Topology
set_option backward.isDefEq.respectTransparency false

/-- A positive analytic real function retains analyticity after any fixed real power.
Use: proves the actual analytic endpoint factor of the Jacobi Liouville wave for all real endpoint exponents.
Article: jacobi, Proposition B.1.
Source: the positive real-power identity exp(p*log(x)) and analytic composition.
Proof: positivity persists on a neighborhood, where the actual real power
agrees with the analytic logarithm/exponential composition. -/
theorem analytic_positive_rpow {f : ℝ → ℝ} {x : ℝ} (hf : AnalyticAt ℝ f x)
    (hp : 0<f x) (p : ℝ) : AnalyticAt ℝ (fun t => (f t)^p) x := by
  have he : AnalyticAt ℝ (fun t : ℝ => exp (log (f t)*p)) x :=
    analyticAt_rexp.comp ((hf.log hp).mul analyticAt_const)
  apply he.congr
  filter_upwards [hf.continuousAt.eventually (Ioi_mem_nhds hp)] with t ht
  exact (Real.rpow_def_of_pos ht p).symm

/-- The literal regular factor left after removing the singular endpoint power from the original Jacobi Liouville wave.
Use: its actual parity and analytic regularity fix the selected endpoint branch in the zero-comparison proof.
Article: jacobi, Proposition B.1.
-/
def endpointFactor (a b : ℝ) (n : ℕ) (t : ℝ) : ℝ :=
  (sinc (t/2)/2)^(a+1/2)*cos (t/2)^(b+1/2)*angular a b n t

/-- The genuine endpoint factor is even as a function of the real angle.
Use: its actual first derivative vanishes at zero, giving the convergent singular-endpoint Wronskian.
Article: jacobi, Proposition B.1.
Proof: sinc, cosine and the original cosine-composed finite polynomial are all even; their actual real powers retain parity. -/
theorem endpointFactor_even (a b : ℝ) (n : ℕ) (t : ℝ) :
    endpointFactor a b n (-t)=endpointFactor a b n t := by
  simp only [endpointFactor,neg_div,sinc_neg,cos_neg,angular]

/-- The original Jacobi angular polynomial is real analytic everywhere.
Use: the source's analytic endpoint factor uses the actual finite polynomial, with no independent analytic solution assumed.
Article: jacobi, Proposition B.1.
Proof: compose the community analytic polynomial evaluation with the actual analytic cosine affine argument. -/
theorem angular_analytic (a b : ℝ) (n : ℕ) (t : ℝ) : AnalyticAt ℝ (angular a b n) t := by
  have hc : AnalyticAt ℝ (fun x : ℝ => (1-cos x)/2) t :=
    (analyticAt_const.sub Real.analyticAt_cos).div_const
  exact (AnalyticOnNhd.eval_polynomial (shiftedPolynomial a b n) _ (mem_univ _)).comp
    (f := fun x : ℝ => (1-cos x)/2) hc

/-- The actual endpoint factor of the genuine Jacobi Liouville wave is analytic at zero for arbitrary real parameters.
Use: discharges the regular-singular endpoint regularity in the complete parameter range, including alpha<-1/2.
Article: jacobi, Proposition B.1.
Proof: the two real-power bases take the strictly positive values 1/2
and 1 at zero. Apply analytic positive-power composition and multiply by
the actual entire angular Jacobi polynomial. -/
theorem endpointFactor_analytic (a b : ℝ) (n : ℕ) : AnalyticAt ℝ (endpointFactor a b n) 0 := by
  -- Analyticity belongs to the regular factor; the singular outer power is not asserted analytic at zero.
  have hi : AnalyticAt ℝ (fun x : ℝ => x/2) 0 := analyticAt_id.div_const
  have hs := (sinc_analytic (0/2)).comp (f := fun x : ℝ => x/2) hi
  have hc := Real.analyticAt_cos.comp (f := fun x : ℝ => x/2) hi
  have hsp : 0<sinc (0/2)/2 := by norm_num
  have hcp : 0<cos (0/2) := by norm_num
  exact ((analytic_positive_rpow hs.div_const hsp (a+1/2)).mul
    (analytic_positive_rpow hc hcp (b+1/2))).mul (angular_analytic a b n 0)

/-- The actual regular endpoint factor has its exact positive normalization.
Use: selects the genuine nonzero branch and the initial sign required by the first-interval Sturm argument.
Article: jacobi, Proposition B.1.
Proof: the actual angular value at zero is the proved finite polynomial endpoint normalization; both other bases have their literal central values. -/
theorem endpointFactor_zero (a b : ℝ) (n : ℕ) :
    endpointFactor a b n 0=(1/2:ℝ)^(a+1/2) := by
  simp only [endpointFactor,zero_div,sinc_zero,cos_zero,Real.one_rpow,mul_one,
    angular,sub_self,shiftedPolynomial_zero]

/-- The genuine endpoint factor starts strictly positive and has zero actual first derivative at zero.
Use: fixes the initial source branch and the extra vanishing order in its singular-endpoint Wronskian.
Article: jacobi, Proposition B.1.
Proof: its exact endpoint value is a real power of the positive number one half; even analytic functions have zero central derivative. -/
theorem endpointFactor_properties (a b : ℝ) (n : ℕ) :
    0<endpointFactor a b n 0 ∧ deriv (endpointFactor a b n) 0=0 := by
  refine ⟨?_,even_derivative_zero (endpointFactor_analytic a b n).differentiableAt
    (endpointFactor_even a b n)⟩
  rw [endpointFactor_zero]
  exact Real.rpow_pos_of_pos (by norm_num) _

/-- The source's actual Jacobi Liouville wave has the exact selected regular-singular factorization on the whole positive angular interval.
Use: the endpoint Wronskian and zero comparison apply to the already constructed original wave, without a branch hypothesis.
Article: jacobi, Proposition B.1.
Proof: sin(theta/2)=theta*sinc(theta/2)/2 on the positive branch. The
positive-base real-power product formula factors out the actual singular
power of theta and leaves precisely the genuine analytic factor. -/
theorem liouville_endpoint_factor (a b : ℝ) (n : ℕ) {t : ℝ} (ht : t∈Ioo 0 Real.pi) :
    liouville a b n t=t^(a+1/2)*endpointFactor a b n t := by
  -- Both bases in the real-power multiplication law are actual positive real numbers.
  have hh : t/2≠0 := ne_of_gt (by linarith [ht.1])
  have hsinc : 0<sinc (t/2)/2 := by
    rw [sinc_of_ne_zero hh]
    exact div_pos (div_pos (half_angle_positive ht).1 (by linarith [ht.1])) (by norm_num)
  have he : sin (t/2)=t*(sinc (t/2)/2) := by
    rw [sinc_of_ne_zero hh]
    field_simp [ht.1.ne']
  unfold liouville liouvilleWeight endpointFactor
  rw [he,Real.mul_rpow ht.1.le hsinc.le]
  ring

end
end jacobi.Jacobi
