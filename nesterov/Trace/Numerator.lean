import nesterov.Trace.Reciprocal

/-! Polynomial numerator and degree identities for the source trace quotient. -/
namespace nesterov.Trace
noncomputable section
open Polynomial Complex
namespace DoubleRootData
variable (A : DoubleRootData)

def numerator : Polynomial ℝ := -X*(X+C 1)*A.q

theorem numerator_degree : A.numerator.natDegree=A.method.memory := by
  have hx : (X-C (1:ℝ))≠0 := X_sub_C_ne_zero 1
  have hx' : (X+C (1:ℝ))≠0 := (monic_X_add_C 1).ne_zero
  have hv : A.method.recurrencePolynomial.natDegree=2+A.q.natDegree := by
    rw [A.factor,natDegree_mul (pow_ne_zero 2 hx) A.q_ne_zero,natDegree_pow,natDegree_X_sub_C]
  rw [←A.method.recurrencePolynomial_natDegree,numerator,
    natDegree_mul (mul_ne_zero (neg_ne_zero.mpr X_ne_zero) hx') A.q_ne_zero,
    natDegree_mul (neg_ne_zero.mpr X_ne_zero) hx',natDegree_neg,natDegree_X,natDegree_X_add_C]
  omega

theorem numerator_leading : A.numerator.leadingCoeff= -A.q.leadingCoeff := by
  simp only [numerator,leadingCoeff_mul,leadingCoeff_neg,leadingCoeff_X,leadingCoeff_X_add_C,
    neg_mul,one_mul]

theorem v_leading : A.v.leadingCoeff=A.q.leadingCoeff := by
  change A.method.recurrencePolynomial.leadingCoeff=A.q.leadingCoeff
  rw [A.factor,leadingCoeff_mul,leadingCoeff_pow,leadingCoeff_X_sub_C,one_pow,one_mul]

theorem numerator_eval (z : ℂ) : eval A.numerator z= -z*(z+1)*eval A.q z := by
  simp only [numerator,eval_mul,eval_neg,eval_X,eval_add,eval_C,Complex.ofReal_one]

theorem numerator_one : A.numerator.eval 1=2/A.y := by
  simp only [numerator,Polynomial.eval_mul,Polynomial.eval_neg,Polynomial.eval_X,
    Polynomial.eval_add,Polynomial.eval_C,A.q_one]
  ring

def strictQuotient (hs : ∀ z : ℂ,eval (A.phi 1) z=0 → ‖z‖<1) : StableQuotient where
  numerator := A.numerator
  denominator := A.phi 1
  denominator_ne := by
    intro he
    have h := A.phi_one 1
    rw [he,Polynomial.eval_zero] at h
    norm_num at h
  degree_eq := A.numerator_degree.trans (A.phi_natDegree 1).symm
  leading_eq := by rw [A.numerator_leading,A.phi_leadingCoeff,A.v_leading]
  roots_inside := hs

theorem strictQuotient_one (hs : ∀ z : ℂ,eval (A.phi 1) z=0 → ‖z‖<1) :
    (A.strictQuotient hs).diskFunction 1=(2/A.y-1:ℝ) := by
  have hd : eval (A.strictQuotient hs).denominator (1:ℂ)⁻¹≠0 := by
    change eval (A.phi 1) (1:ℂ)⁻¹≠0
    simp
  rw [StableQuotient.diskFunction_reciprocal _ (by norm_num : (1:ℂ)≠0) hd]
  simp only [strictQuotient,inv_one,eval_one,A.numerator_one,A.phi_one,Complex.ofReal_one,
    div_one,Complex.ofReal_sub,Complex.ofReal_div]

end DoubleRootData
end
end nesterov.Trace
