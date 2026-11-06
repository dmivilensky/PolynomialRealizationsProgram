import nesterov.Trace.Numerator
import nesterov.Trace.BoundaryAlgebra
import Mathlib.Algebra.Polynomial.FieldDivision

/-! Cancellation of the possible simple characteristic root at −1. -/
namespace nesterov.Trace
noncomputable section
open Polynomial Complex

/-- A quotient representation retains both exact original polynomial factors. -/
structure QuotientRepresentation (N D : Polynomial ℝ) where
  quotient : StableQuotient
  common : Polynomial ℝ
  numerator_factor : N=common*quotient.numerator
  denominator_factor : D=common*quotient.denominator

namespace QuotientRepresentation
variable {N D : Polynomial ℝ} (R : QuotientRepresentation N D)

theorem ratio_eq {z : ℂ} (hd : eval D z≠0) :
    eval R.quotient.numerator z/eval R.quotient.denominator z=eval N z/eval D z := by
  have hde : eval D z=eval R.common z*eval R.quotient.denominator z := by
    simpa only [eval_mul] using congrArg (fun p=>eval p z) R.denominator_factor
  have hn : eval N z=eval R.common z*eval R.quotient.numerator z := by
    simpa only [eval_mul] using congrArg (fun p=>eval p z) R.numerator_factor
  have hc : eval R.common z≠0 := fun hh=>hd (by rw [hde,hh,zero_mul])
  rw [hn,hde,mul_div_mul_left _ _ hc]

theorem diskFunction_reciprocal {z : ℂ} (hz : z≠0) (hd : eval D z⁻¹≠0) :
    R.quotient.diskFunction z=eval N z⁻¹/eval D z⁻¹-1 := by
  have hde : eval R.quotient.denominator z⁻¹≠0 := by
    intro hh
    apply hd
    rw [R.denominator_factor,eval_mul,hh,mul_zero]
  rw [R.quotient.diskFunction_reciprocal hz hde,R.ratio_eq hd]
end QuotientRepresentation

namespace DoubleRootData
variable (A : DoubleRootData)

def SchurExceptMinusOne : Prop := ∀ z : ℂ,eval (A.phi 1) z=0 →
  ‖z‖<1 ∨ (z= -1 ∧ (A.phi 1).derivative.eval (-1)≠0)

private theorem memory_eq_two_add : A.method.memory=2+A.q.natDegree := by
  have hx : (X-C (1:ℝ))≠0 := X_sub_C_ne_zero 1
  rw [←A.method.recurrencePolynomial_natDegree,A.factor,natDegree_mul (pow_ne_zero 2 hx) A.q_ne_zero,
    natDegree_pow,natDegree_X_sub_C]

theorem exists_quotientRepresentation (hs : A.SchurExceptMinusOne) :
    Nonempty (QuotientRepresentation A.numerator (A.phi 1)) := by
  by_cases hm : (A.phi 1).eval (-1)=0
  · let d := A.phi 1 /ₘ (X-C (-1))
    have hdf : (X-C (-1))*d=A.phi 1 := mul_divByMonic_eq_iff_isRoot.mpr hm
    have hn : A.numerator=(X-C (-1))*(-X*A.q) := by unfold numerator;simp only [Polynomial.C_neg,Polynomial.C_1];ring
    have hd0 : d≠0 := by
      intro he
      have hh := congrArg (Polynomial.eval (1:ℝ)) hdf
      rw [he,mul_zero,Polynomial.eval_zero,A.phi_one] at hh
      norm_num at hh
    have hddeg : d.natDegree=1+A.q.natDegree := by
      dsimp [d]
      rw [natDegree_divByMonic _ (monic_X_sub_C _),A.phi_natDegree,natDegree_X_sub_C,A.memory_eq_two_add]
      omega
    have hndeg : (-X*A.q).natDegree=d.natDegree := by
      rw [natDegree_mul (neg_ne_zero.mpr X_ne_zero) A.q_ne_zero,natDegree_neg,natDegree_X,hddeg]
    have hlead : (-X*A.q).leadingCoeff=d.leadingCoeff := by
      have hh := congrArg Polynomial.leadingCoeff hdf
      rw [leadingCoeff_mul,leadingCoeff_X_sub_C,one_mul,A.phi_leadingCoeff,A.v_leading] at hh
      simpa only [leadingCoeff_mul,leadingCoeff_neg,leadingCoeff_X,neg_mul,one_mul] using hh.symm
    have hdstable : ∀ z : ℂ,eval d z=0 → ‖z‖<1 := by
      intro z hz
      have hzphi : eval (A.phi 1) z=0 := by rw [←hdf,eval_mul,hz,mul_zero]
      rcases hs z hzphi with h|⟨rfl,hsimple⟩
      · exact h
      · have hzreal : d.eval (-1)=0 := by exact_mod_cast (by simpa only [eval_neg_one] using hz : ((d.eval (-1):ℝ):ℂ)=0)
        have hh := congrArg (fun p : Polynomial ℝ=>p.derivative.eval (-1)) hdf
        simp only [Polynomial.derivative_mul,Polynomial.derivative_sub,Polynomial.derivative_X,
          Polynomial.derivative_C,sub_zero,Polynomial.eval_add,Polynomial.eval_mul,
          Polynomial.eval_sub,Polynomial.eval_X,Polynomial.eval_C,sub_self,one_mul] at hh
        exact False.elim (hsimple (by simpa only [hzreal,zero_mul,add_zero] using hh.symm))
    exact ⟨⟨⟨-X*A.q,d,hd0,hndeg,hlead,hdstable⟩,X-C (-1),hn,hdf.symm⟩⟩
  · have hstrict : ∀ z : ℂ,eval (A.phi 1) z=0 → ‖z‖<1 := by
      intro z hz
      rcases hs z hz with h|⟨rfl,_⟩
      · exact h
      · apply False.elim
        apply hm
        exact_mod_cast (by simpa only [eval_neg_one] using hz : (((A.phi 1).eval (-1):ℝ):ℂ)=0)
    exact ⟨⟨A.strictQuotient hstrict,1,by simp [strictQuotient],by simp [strictQuotient]⟩⟩

end DoubleRootData
end
end nesterov.Trace
