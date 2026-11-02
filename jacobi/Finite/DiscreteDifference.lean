import jacobi.Finite.DiscreteWronskian

/-!
Article: jacobi, Appendix C.3 (discrete Volterra equation and cosh estimates).
The exact original Wronskian gives the first-difference error directly.
This avoids differentiating the factorial majorant and retains the
original complex recurrence and spectral parameter.
Use: Support.naturalWave_difference_identity and naturalWave_firstDifference prove the printed support-polynomial first-difference estimate with every actual recurrence premise discharged.
-/
namespace jacobi.Finite
noncomputable section
open Finset

/-- The genuine recurrence Wronskian decomposes the first-difference error into a top-node difference and one finite source sum.
Use: Support.naturalWave_difference_identity and naturalWave_firstDifference prove the printed support-polynomial first-difference estimate with every actual recurrence premise discharged.
Article: jacobi, Appendix C.3 (discrete Volterra equation and cosh estimates).
Source: discrete Lagrange identity, applied to the original reference and wave recurrences.
Proof: use the exact summed recurrence Wronskian, divide by its nonzero original coupling and reference value, and rearrange the original adjacent differences. -/
theorem discrete_difference_error (a b u v : ℕ→ℂ) (y₀ y : ℂ) (N : ℕ)
    (hu : ∀m<N,a (m+1)*u (m+1)+(if m=0 then 0 else a m*u (m-1))+b m*u m=y₀*u m)
    (hv : ∀m<N,a (m+1)*v (m+1)+(if m=0 then 0 else a m*v (m-1))+b m*v m=y*v m)
    {m : ℕ} (hm:m<N) (ha:a (m+1)≠0) (h0:u m≠0) :
    (v (m+1)-v m)-(u (m+1)-u m)=
      ((v m-u m)/u m)*(u (m+1)-u m)+
      (y-y₀)*(∑j∈range (m+1),u j*v j)/(a (m+1)*u m) := by
  have h := discreteWronskian_sum a b u v y₀ y N hu hv hm
  dsimp [discreteWronskian] at h
  field_simp [ha,h0]
  linear_combination h

end
end jacobi.Finite
