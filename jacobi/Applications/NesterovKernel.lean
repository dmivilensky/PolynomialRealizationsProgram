import jacobi.Applications.NesterovQueries
import jacobi.Applications.NesterovTail

/-!
Article: jacobi, Theorem 5.1.
The explicit two-variable formula is proved for the original method's
actual first-variation kernel from chebyshev1, at every genuine step.
Use: NesterovGain evaluates its sharp supremum on the full spectral square.
-/
namespace jacobi.Applications
noncomputable section
open Matrix chebyshev1 Set
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1000000

/-- The actual original Nesterov insertion factors into its causal tail and genuine extrapolated query.
Use: nesterov_kernel computes the same kernel whose operator derivative was proved in the first article.
Article: jacobi, Theorem 5.1.
Proof: expand the original rank-one query factor and input/output contraction over the two memory coordinates. Matrix multiplication separates the tail column and the forward query. -/
theorem nesterov_kernel_factorization (b:ℝ) (k s:ℕ) (l v:ℝ) :
    (nesterovMethod b).kernel k s l v=
      -(orderedProduct (fun i => (nesterovMethod b).scalarStep (s+1+i) l) (k-(s+1)) 0 0)*
        nesterovQuery b s v := by
  simp [Realization.kernel,Realization.scalarContract,Realization.queryFactor,nesterovQuery,
    Matrix.mul_apply,Matrix.mulVec,Matrix.vecMulVec,Fin.sum_univ_two,nesterovMethod,Matrix.vecHead,Matrix.vecTail]
  ring

/-- The actual first-variation kernel of the original b=1 Nesterov iteration has the exact printed separated polynomial formula.
Use: its endpoint domination and exact squared sum give the sharp full spectral-pair gain.
Article: jacobi, Theorem 5.1.
Proof: the true insertion factorization combines the proved actual forward query and the true causal ordered tail. Their positive intermediate iteration count cancels, leaving precisely the original horizon denominator. -/
theorem nesterov_kernel {k s:ℕ} (hs:s<k) (l v:ℝ) :
    (nesterovMethod 1).kernel k s l v=
      -(nesterovWave (k-s-1) l*nesterovWave s v)/(k:ℝ) := by
  rw [nesterov_kernel_factorization,nesterov_tail_fundamental (by omega) (by omega),nesterov_query_wave]
  rw [show k-(s+1)=k-s-1 by omega]
  push_cast
  field_simp

/-- Every true original Nesterov insertion is maximized in absolute value at the same zero spectral pair.
Use: proves attainment of the actual supremum over both spectral parameters, not merely the endpoint channel.
Article: jacobi, Theorem 5.1.
Proof: each of the two genuine polynomial waves is bounded by its exact zero-endpoint value. The true positive horizon divides their product, so the same pair maximizes every insertion simultaneously. -/
theorem nesterov_kernel_le_endpoint {k s:ℕ} (hs:s<k) {l v:ℝ}
    (hl:l∈Icc (0:ℝ) 1) (hv:v∈Icc (0:ℝ) 1) :
    |(nesterovMethod 1).kernel k s l v|≤|(nesterovMethod 1).kernel k s 0 0| := by
  -- One common endpoint maximizes every term before the squared time norm is summed.
  have hkp : 0<(k:ℝ) := by exact_mod_cast (by omega : 0<k)
  rw [nesterov_kernel hs,nesterov_kernel hs,nesterovWave_endpoint,nesterovWave_endpoint,
    abs_div,abs_neg,abs_mul,abs_div,abs_neg,abs_mul,abs_of_pos hkp]
  rw [abs_of_pos (by positivity : (0:ℝ)<(k-s-1:ℕ)+1),abs_of_pos (by positivity : (0:ℝ)<(s:ℝ)+1)]
  exact div_le_div_of_nonneg_right (mul_le_mul (nesterovWave_bound _ hl)
    (nesterovWave_bound _ hv) (abs_nonneg _) (by positivity)) hkp.le

end
end jacobi.Applications
