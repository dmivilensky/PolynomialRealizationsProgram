import nesterov.Trace.Cancellation
import nesterov.Trace.BoundaryAlgebra

/-! Exact agreement between an analytic canceled quotient and the source
weighted spectral symbol, away from the two real endpoints. -/
namespace nesterov.Trace
noncomputable section
open Complex Metric Polynomial Set
open scoped Topology

namespace StableQuotient
variable (A : StableQuotient)

theorem diskFunction_conj (z : ℂ) : A.diskFunction (star z)=star (A.diskFunction z) := by
  simp only [diskFunction,eval_conj,star_sub,star_div₀,star_one]

theorem boundaryValue_conj {z : ℂ} (hz : Complex.normSq z=1) (hreal : (A.diskFunction 1).im=0) :
    boundaryValue A.diskFunction (star z)=boundaryValue A.diskFunction z := by
  by_cases hz1 : z=1
  · simp only [hz1,star_one]
  have hzc : Complex.normSq (star z)=1 := by simpa only [Complex.star_def,Complex.normSq_conj] using hz
  have hzne : star z≠1 := fun he=>hz1 (by simpa only [star_one,star_star] using congrArg star he)
  rw [boundaryValue_eq_weighted_im hzc hzne hreal,boundaryValue_eq_weighted_im hz hz1 hreal,A.diskFunction_conj]
  simp only [Complex.star_def,Complex.conj_re,Complex.conj_im]
  ring
end StableQuotient

namespace DoubleRootData
variable (A : DoubleRootData)

def traceIntegrand (ω : ℝ) : ℝ :=
  (1+Real.cos ω)*A.symbol ω/
    ((1-Real.cos ω)^2*Complex.normSq (eval (A.phi 1) (Complex.exp ((ω:ℂ)*Complex.I))))

theorem representation_one (R : QuotientRepresentation A.numerator (A.phi 1)) :
    R.quotient.diskFunction 1=((2/A.y-1:ℝ):ℂ) := by
  rw [R.diskFunction_reciprocal (by norm_num : (1:ℂ)≠0) (by simp)]
  simp only [inv_one,eval_one,A.numerator_one,A.phi_one,Complex.ofReal_one,
    div_one,Complex.ofReal_sub,Complex.ofReal_div]

theorem representation_boundary (R : QuotientRepresentation A.numerator (A.phi 1))
    {z : ℂ} (hz : Complex.normSq z=1) (hz1 : z≠1) (hd : eval (A.phi 1) z≠0) :
    boundaryValue R.quotient.diskFunction z=
      (1+z.re)*((1-z)*eval (A.phi 0) z*star (eval (A.phi 1) z)).re/
        (2*(1-z.re)^2*Complex.normSq (eval (A.phi 1) z)) := by
  have hz0 : z≠0 := by intro hh;simp only [hh,Complex.normSq_zero] at hz;norm_num at hz
  have hi : z⁻¹=star z := by
    rw [Complex.inv_def,hz]
    simp only [inv_one,Complex.ofReal_one,mul_one,Complex.star_def]
  have hdc : eval (A.phi 1) z⁻¹≠0 := by
    rw [hi,eval_conj]
    exact star_ne_zero.mpr hd
  have hFi : (R.quotient.diskFunction z).im=
      -(((-z*(z+1)*eval A.q z)/eval (A.phi 1) z).im) := by
    rw [R.diskFunction_reciprocal hz0 hdc,hi,eval_conj,eval_conj]
    rw [←star_div₀]
    simp only [Complex.sub_im,Complex.one_im,sub_zero,Complex.star_def,Complex.conj_im,A.numerator_eval]
  have hreal : (R.quotient.diskFunction 1).im=0 := by rw [A.representation_one];rfl
  rw [boundaryValue_eq_weighted_im hz hz1 hreal,hFi]
  have hφ0 : eval (A.phi 0) z= -(z-1)^2*eval A.q z := by
    simp only [phi,C_0,zero_mul,zero_sub,eval_neg]
    change -eval A.method.recurrencePolynomial z=_
    rw [A.factor,eval_mul,eval_pow,eval_sub,eval_X,eval_C,Complex.ofReal_one]
    ring
  rw [hφ0]
  simpa only [mul_neg,neg_mul] using weighted_quotient_identity hz hz1 (eval A.q z) (eval (A.phi 1) z) hd

end DoubleRootData
end
end nesterov.Trace
