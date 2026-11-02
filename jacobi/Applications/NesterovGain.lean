import jacobi.Applications.NesterovKernel
import jacobi.Applications.NesterovSums
import jacobi.Applications.SpectralGain

/-!
Article: jacobi, Theorem 5.1.
The full spectral-pair supremum of the original b=1 iteration is
attained at zero, and its finite squared gain is evaluated exactly.
Use: BlockComparison compares this genuine gain with the terminal-equivalent
Jacobi block, keeping their original common application count.
-/
namespace jacobi.Applications
noncomputable section
open chebyshev1 Set
set_option backward.isDefEq.respectTransparency false

/-- The original b=1 Nesterov gain is attained by the zero spectral pair.
Use: its exact finite formula is obtained from the actual endpoint kernels without weakening the full spectral supremum.
Article: jacobi, Theorem 5.1.
Proof: every actual insertion kernel has the same maximizing endpoint pair by the polynomial wave bound. Apply the proved generic full-square maximization theorem. -/
theorem nesterov_gain_eq_endpoint (k:ℕ) :
    unitSpectralGain (nesterovMethod 1) k=(nesterovMethod 1).kernelNorm k 0 0 :=
  unitSpectralGain_eq_endpoint _ k (fun _ hs _ hl _ hv => nesterov_kernel_le_endpoint hs hl hv)

/-- The true squared full spectral gain of the original Nesterov method has exactly the article's finite-horizon value.
Use: proves the original leading constant and its ratio to the optimal Jacobi-block gain.
Article: jacobi, Theorem 5.1.
Proof: the common zero endpoint attains the actual spectral supremum. Its genuine kernels are -(s+1)*(k-s)/k. Square, sum, and apply the exact discrete-antiderivative evaluation of the original weights. -/
theorem nesterov_gain_square (k:ℕ) :
    (unitSpectralGain (nesterovMethod 1) k)^2=(((k:ℝ)+1)^5-((k:ℝ)+1))/(30*(k:ℝ)^2) := by
  -- No asymptotic replaces the finite gain: all lower-order horizon corrections are retained exactly.
  rw [nesterov_gain_eq_endpoint,Realization.kernelNorm,Real.sq_sqrt (Finset.sum_nonneg (fun _ _ => sq_nonneg _))]
  have he (s:ℕ) (hs:s∈Finset.range k) :
      ((nesterovMethod 1).kernel k s 0 0)^2=
        (((s:ℝ)+1)^2*((k:ℝ)-s)^2)/(k:ℝ)^2 := by
    have hsk := Finset.mem_range.mp hs
    have hi : k-s-1+1=k-s := by omega
    rw [nesterov_kernel hsk,nesterovWave_endpoint,nesterovWave_endpoint,div_pow,neg_sq,mul_pow]
    have hc : (k-s-1:ℕ)+1=(k:ℝ)-s := by
      have hh := congrArg (fun j:ℕ => (j:ℝ)) hi
      simpa only [Nat.cast_add,Nat.cast_one,Nat.cast_sub (by omega : s≤k)] using hh
    rw [hc]
    ring
  rw [Finset.sum_congr rfl he,← Finset.sum_div,nesterov_endpoint_sum]
  ring

end
end jacobi.Applications
