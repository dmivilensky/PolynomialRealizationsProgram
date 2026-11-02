import jacobi.Finite.PolynomialRecurrence

/-!
Article: jacobi, Appendix C.3 (discrete Volterra equation and cosh estimates).
Source: discrete Lagrange identity and reduction of order.
Use: discreteWronskian_sum proves the exact source term, and discrete_quotient_difference supplies the reduction-of-order kernel.
-/
namespace jacobi.Finite
noncomputable section
open Finset

/-- The actual oriented discrete Wronskian across one original adjacent edge.
Use: discreteWronskian_sum proves the exact source term, and discrete_quotient_difference supplies the reduction-of-order kernel.
Article: jacobi, Appendix C.3 (discrete Volterra equation and cosh estimates).
-/
def discreteWronskian (a u v : ℕ→ℂ) (m : ℕ) : ℂ :=
  a (m+1)*(u m*v (m+1)-u (m+1)*v m)

/-- Summing the genuine two original three-term equations gives the exact discrete Wronskian source sum.
Use: discrete_quotient_difference and discreteVolterra recover the original spectral wave from the same actual top-node solution.
Article: jacobi, Appendix C.3 (discrete Volterra equation and cosh estimates).
Source: discrete Lagrange identity, proved here by the actual recurrence subtraction.
Proof: multiply the original wave equation by the reference solution and subtract the reference equation times the wave. The left boundary Wronskian is zero; induction telescopes every original adjacent flux. -/
theorem discreteWronskian_sum (a b u v : ℕ→ℂ) (y₀ y : ℂ) (N : ℕ)
    (hu : ∀m<N,a (m+1)*u (m+1)+(if m=0 then 0 else a m*u (m-1))+b m*u m=y₀*u m)
    (hv : ∀m<N,a (m+1)*v (m+1)+(if m=0 then 0 else a m*v (m-1))+b m*v m=y*v m)
    {m : ℕ} (hm:m<N) :
    discreteWronskian a u v m=(y-y₀)*∑j∈range (m+1),u j*v j := by
  -- The source is summed with its original sign; the left endpoint has no fictitious negative-index contribution.
  induction m with
  | zero =>
    have hu0 := hu 0 hm
    have hv0 := hv 0 hm
    simp [discreteWronskian] at hu0 hv0 ⊢
    linear_combination u 0*hv0-v 0*hu0
  | succ m ih =>
    have hprev := ih (by omega)
    have hum := hu (m+1) hm
    have hvm := hv (m+1) hm
    simp only [ite_eq_right (Nat.succ_ne_zero m),Nat.add_sub_cancel] at hum hvm
    rw [sum_range_succ]
    dsimp [discreteWronskian] at *
    linear_combination hprev+u (m+1)*hvm-v (m+1)*hum

/-- The quotient of the original wave by its genuine nonzero reference solution has the exact reduction-of-order forward difference.
Use: discreteVolterra telescopes these same genuine quotients and produces the article's original Green kernel.
Article: jacobi, Appendix C.3 (discrete Volterra equation and cosh estimates).
Proof: the proved actual Wronskian sum is divided by the three stated nonzero original edge factors, retaining the full original source sum. -/
theorem discrete_quotient_difference (a b u v : ℕ→ℂ) (y₀ y : ℂ) (N : ℕ)
    (hu : ∀m<N,a (m+1)*u (m+1)+(if m=0 then 0 else a m*u (m-1))+b m*u m=y₀*u m)
    (hv : ∀m<N,a (m+1)*v (m+1)+(if m=0 then 0 else a m*v (m-1))+b m*v m=y*v m)
    {m : ℕ} (hm:m<N) (ha:a (m+1)≠0) (h0:u m≠0) (h1:u (m+1)≠0) :
    v (m+1)/u (m+1)-v m/u m=
      (y-y₀)*(∑j∈range (m+1),u j*v j)/(a (m+1)*u m*u (m+1)) := by
  have h := discreteWronskian_sum a b u v y₀ y N hu hv hm
  dsimp [discreteWronskian] at h
  apply (eq_div_iff (mul_ne_zero (mul_ne_zero ha h0) h1)).mpr
  field_simp [h0,h1]
  linear_combination h

end
end jacobi.Finite
