import Mathlib.Data.Nat.Choose.Sum
import Mathlib.Data.Nat.Choose.Bounds
import Mathlib.Tactic

/-!
Article: jacobi, Appendix C.3 (discrete Volterra equation and cosh estimates).
Exact binomial iterates of the elementary positive linear discrete
Volterra kernel. They provide the factorial denominator in the printed
cosh bound without a separate power-sum estimate for each exponent.
Source: Pascal's identity and finite discrete integration.
Use: linear_kernel_choose computes the genuine iterates of the positive linear kernel that bounds the original weighted support kernel.
-/
namespace jacobi.Finite
noncomputable section
open Finset

/-- One exact discrete integral of the original Volterra binomial coefficient is the next original binomial coefficient.
Use: linear_kernel_choose computes the genuine iterates of the positive linear kernel that bounds the original weighted support kernel.
Article: jacobi, Appendix C.3 (discrete Volterra equation and cosh estimates).
Source: Pascal's identity, Nat.choose_succ_succ.
Proof: Pascal's identity makes every summand an exact forward difference; the initial binomial coefficient is genuinely zero. -/
theorem sum_shifted_choose (k m : ℕ) :
    (∑j∈range m,((j+k).choose (2*k):ℝ))=((m+k).choose (2*k+1):ℝ) := by
  -- The zero binomial terms automatically retain every original index below the first nonzero iterate.
  have hstep (j : ℕ) : ((j+k).choose (2*k):ℝ)=
      (((j+1)+k).choose (2*k+1):ℝ)-((j+k).choose (2*k+1):ℝ) := by
    have h := Nat.choose_succ_succ (j+k) (2*k)
    have h' : (((j+k+1).choose (2*k+1)):ℝ)=((j+k).choose (2*k):ℝ)+((j+k).choose (2*k+1):ℝ) := by exact_mod_cast h
    rw [show j+k+1=j+1+k by omega] at h'
    linarith
  simp_rw [hstep]
  rw [sum_range_sub (fun j => ((j+k).choose (2*k+1):ℝ)) m]
  simp only [Nat.zero_add,Nat.choose_eq_zero_of_lt (show k<2*k+1 by omega),Nat.cast_zero,sub_zero]

/-- The elementary positive linear Volterra kernel integrates its genuine binomial iterate exactly to the next one.
Use: linear_volterra_cosh bounds the actual support wave by the original factorial hyperbolic-cosine majorant.
Article: jacobi, Appendix C.3 (discrete Volterra equation and cosh estimates).
Proof: appending one genuine original row adds the preceding row sum and its final coefficient. The proved discrete binomial integral and two exact Pascal identities yield precisely choose(m+k+1,2*k+2). -/
theorem linear_kernel_choose (k m : ℕ) :
    (∑j∈range m,((m-j:ℕ):ℝ)*((j+k).choose (2*k):ℝ))=
      ((m+k+1).choose (2*k+2):ℝ) := by
  -- The exact original index deficit is retained, including both empty and zero-iterate cases.
  induction m with
  | zero => simp [Nat.choose_eq_zero_of_lt (show k+1<2*k+2 by omega)]
  | succ m ih =>
    rw [sum_range_succ]
    have hs : (∑j∈range m,((m+1-j:ℕ):ℝ)*((j+k).choose (2*k):ℝ))=
        (∑j∈range m,((m-j:ℕ):ℝ)*((j+k).choose (2*k):ℝ))+
          ∑j∈range m,((j+k).choose (2*k):ℝ) := by
      rw [← sum_add_distrib]
      apply sum_congr rfl
      intro j hj
      rw [show m+1-j=(m-j)+1 by have := mem_range.mp hj; omega]
      push_cast
      ring
    rw [hs,ih,sum_shifted_choose,show m+1-m=1 by omega,Nat.cast_one,one_mul]
    have h₁ := Nat.choose_succ_succ (m+k) (2*k)
    have h₂ := Nat.choose_succ_succ (m+k+1) (2*k+1)
    have hp₁ : ((m+k+1).choose (2*k+1):ℝ)=
        ((m+k).choose (2*k):ℝ)+((m+k).choose (2*k+1):ℝ) := by exact_mod_cast h₁
    have hp₂ : ((m+k+2).choose (2*k+2):ℝ)=
        ((m+k+1).choose (2*k+1):ℝ)+((m+k+1).choose (2*k+2):ℝ) := by exact_mod_cast h₂
    rw [show m+1+k+1=m+k+2 by omega]
    linarith

end
end jacobi.Finite
