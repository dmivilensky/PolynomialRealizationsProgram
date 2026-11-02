import jacobi.Finite.DiscreteWronskian

/-!
Article: jacobi, Appendix C.3 (discrete Volterra equation and cosh estimates).
Source: discrete Green formula and reduction of order.
Use: discreteVolterra turns the summed original edge flux into the printed source-index Green sum.
-/
namespace jacobi.Finite
noncomputable section
open Finset

/-- The two exact orders of summation on an original finite lower triangle agree.
Use: discreteVolterra turns the summed original edge flux into the printed source-index Green sum.
Article: jacobi, Appendix C.3 (discrete Volterra equation and cosh estimates).
Proof: append the final row and column; every old interval receives precisely its new final term. -/
theorem triangular_sum_swap (f g : ℕ→ℂ) (m : ℕ) :
    (∑l∈range m,f l*∑j∈range (l+1),g j)=
      ∑j∈range m,g j*∑l∈Ico j m,f l := by
  -- Finite induction includes the actual empty triangle and has no convergence hypotheses.
  induction m with
  | zero => simp
  | succ m ih =>
    have hs : (∑j∈range m,g j*∑l∈Ico j (m+1),f l)=
        (∑j∈range m,g j*∑l∈Ico j m,f l)+(∑j∈range m,g j)*f m := by
      rw [sum_mul,← sum_add_distrib]
      apply sum_congr rfl
      intro j hj
      rw [sum_Ico_succ_top (Nat.le_of_lt (mem_range.mp hj))]
      ring
    rw [sum_range_succ (fun l => f l*∑j∈range (l+1),g j) m,
      sum_range_succ (fun j => g j*∑l∈Ico j (m+1),f l) m,hs,ih]
    rw [sum_Ico_succ_top (show m≤m by rfl)]
    simp only [Ico_self,sum_empty,zero_add,sum_range_succ]
    ring

/-- The original exact reduction-of-order Green kernel for a nonzero discrete reference solution.
Use: discreteVolterra represents the actual original wave, and Support.volterraKernel specializes this definition to the genuine positive top-node spectral polynomial.
Article: jacobi, Appendix C.3 (discrete Volterra equation and cosh estimates).
-/
def discreteGreen (a u : ℕ→ℂ) (m j : ℕ) : ℂ :=
  u m*u j*∑l∈Ico j m,(a (l+1)*u l*u (l+1))⁻¹

/-- The original complex spectral wave obeys the full exact original discrete Volterra equation.
Use: Support.naturalWave_volterra applies it to the actual normalized support polynomials and their proved positive original top-node values; the resulting kernel is the one used by the edge limit and envelope estimates.
Article: jacobi, Appendix C.3 (discrete Volterra equation and cosh estimates).
Source: discrete Green formula, proved here from the genuine original Lagrange identity.
Proof: divide each genuine Wronskian source sum by its nonzero original edge factors, telescope the quotient v/u from the true common initial value, and interchange the two finite triangular sums. Multiplication by the same actual reference solution produces exactly the printed kernel. -/
theorem discreteVolterra (a b u v : ℕ→ℂ) (y₀ y : ℂ) (N : ℕ)
    (hu : ∀m<N,a (m+1)*u (m+1)+(if m=0 then 0 else a m*u (m-1))+b m*u m=y₀*u m)
    (hv : ∀m<N,a (m+1)*v (m+1)+(if m=0 then 0 else a m*v (m-1))+b m*v m=y*v m)
    (ha : ∀m<N,a (m+1)≠0) (hu0:u 0=1) (hv0:v 0=1)
    (huz : ∀m≤N,u m≠0) {m : ℕ} (hm:m≤N) :
    v m=u m+(y-y₀)*∑j∈range m,discreteGreen a u m j*v j := by
  -- Telescope the original quotient first; the Green formula then follows by an exact finite interchange.
  have ht := sum_range_sub (fun j => v j/u j) m
  simp only [hu0,hv0,div_one] at ht
  have hs : (∑l∈range m,(v (l+1)/u (l+1)-v l/u l))=
      (y-y₀)*∑l∈range m,(a (l+1)*u l*u (l+1))⁻¹*∑j∈range (l+1),u j*v j := by
    rw [mul_sum]
    apply sum_congr rfl
    intro l hl
    have hlm := mem_range.mp hl
    rw [discrete_quotient_difference a b u v y₀ y N hu hv (by omega)
      (ha l (by omega)) (huz l (by omega)) (huz (l+1) (by omega))]
    ring
  rw [hs,triangular_sum_swap] at ht
  have ht' : v m/u m=1+(y-y₀)*∑j∈range m,u j*v j*∑l∈Ico j m,(a (l+1)*u l*u (l+1))⁻¹ := by
    linear_combination -ht
  calc
    v m=(1+(y-y₀)*∑j∈range m,u j*v j*∑l∈Ico j m,(a (l+1)*u l*u (l+1))⁻¹)*u m :=
      (div_eq_iff (huz m hm)).mp ht'
    _ = _ := by
      rw [add_mul,one_mul,mul_assoc]
      congr 1
      rw [sum_mul]
      congr 1
      apply sum_congr rfl
      intro j hj
      dsimp [discreteGreen]
      ring

end
end jacobi.Finite
