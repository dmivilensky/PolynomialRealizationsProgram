import jacobi.Applications.UniformUChain
import jacobi.Applications.EndpointKernel
import jacobi.Applications.TerminalRealization

/-!
Article: jacobi, Theorem 5.1.
Every actual principal U block has the same sharp Chebyshev endpoint
bound, and the original normalized terminal residual is bounded by one.
Use: UniformBlockGain maximizes every genuine insertion of both stages
at one common pair, before evaluating the complete spectral supremum.
-/
namespace jacobi.Applications
noncomputable section
open Polynomial Polynomial.Chebyshev Matrix Set jacobi.Finite chebyshev1 chebyshev2
set_option backward.isDefEq.respectTransparency false

/-- Every genuine U-chain principal continuant has its sharp absolute maximum at one.
Use: the two actual complementary blocks in uniformU_kernel_le_endpoint are simultaneously maximized.
Article: jacobi, Theorem 5.1.
Proof: substitute the exact monic U continuant, retain its positive scale and apply the first article's proved sharp Chebyshev bound. -/
theorem uniformU_block_bound (m r n:ℕ) (hn:r+n≤m) {x:ℝ} (hx:|x|≤1) :
    |((uniformUChain m).data.block r n).eval x|≤((uniformUChain m).data.block r n).eval 1 := by
  rw [uniformU_block m r n hn]
  simp only [eval_mul,eval_C,U_eval_one,Int.cast_natCast,abs_mul,abs_of_nonneg (by positivity : (0:ℝ)≤(1/2)^n)]
  exact mul_le_mul_of_nonneg_left (abs_U_eval_le n hx) (by positivity)

/-- Every true U-stage insertion is sharply bounded by its same zero-endpoint insertion throughout the full spectral square.
Use: the actual first-stage part of the terminal-equivalent block has no larger spectral pair.
Article: jacobi, Theorem 5.1.
Proof: the true kernel is minus two times its two complementary continuants divided by the positive full endpoint determinant. Their sharp Chebyshev bounds apply to 1-2*lambda and 1-2*nu simultaneously. -/
theorem uniformU_kernel_le_endpoint {m s:ℕ} (hs:s<m) {l v:ℝ}
    (hl:l∈Icc (0:ℝ) 1) (hv:v∈Icc (0:ℝ) 1) :
    |(endpointMethod (uniformUChain m)).realization.kernel m s l v|≤
      |(endpointMethod (uniformUChain m)).realization.kernel m s 0 0| := by
  -- Both sharp bounds concern the actual blocks of the same original finite matrix.
  let S := jacobi.Jacobi.nodes (1/2) (1/2) (by norm_num) (by norm_num) m
  have hJ := uniformU_inFiber m
  have hp := endpoint_prefix_pos S hJ (show m≤m from le_rfl)
  have hleft : 0<((uniformUChain m).data.leading s).eval 1 := endpoint_prefix_pos S hJ hs.le
  have hright : 0<((uniformUChain m).data.block (s+1) (m-(s+1))).eval 1 := by
    rw [uniformU_block m (s+1) (m-(s+1)) (by omega)]
    simp only [eval_mul,eval_C,U_eval_one,Int.cast_natCast]
    positivity
  rw [endpoint_kernel S hJ hs,endpoint_kernel S hJ hs]
  simp only [mul_zero,sub_zero,abs_div,abs_mul,abs_neg,abs_of_nonneg (by norm_num : (0:ℝ)≤2),abs_of_pos hp,abs_of_pos hleft,abs_of_pos hright]
  apply div_le_div_of_nonneg_right ?_ hp.le
  apply mul_le_mul (mul_le_mul_of_nonneg_left
    (uniformU_block_bound m 0 s (by omega) (by rw [abs_le]; constructor <;> linarith [hv.1,hv.2])) (by norm_num))
    (uniformU_block_bound m (s+1) (m-(s+1)) (by omega) (by rw [abs_le]; constructor <;> linarith [hl.1,hl.2]))
    (abs_nonneg _) (by positivity)

/-- The original genuine U-stage terminal transfer is precisely U_m(1-2*lambda)/(m+1).
Use: the complete appended Landweber-stage kernels retain the exact original residual and are bounded by one.
Article: jacobi, Theorem 5.1.
Proof: the true prefix transfer equals its original normalized continuant. Substitute the actual U polynomial at both arguments and cancel only its genuinely positive monic scale. -/
theorem uniformU_transfer (m:ℕ) (l:ℝ) :
    (endpointMethod (uniformUChain m)).realization.scalarTransfer m l=(U ℝ (m:ℤ)).eval (1-2*l)/((m:ℝ)+1) := by
  let S := jacobi.Jacobi.nodes (1/2) (1/2) (by norm_num) (by norm_num) m
  rw [← Realization.residualPolynomial_eval,endpoint_prefix_exact S (uniformU_inFiber m) m le_rfl,endpointResidual_eval]
  simp only [JacobiData.leading]
  rw [uniformU_block m 0 m (by omega)]
  simp only [eval_mul,eval_C,U_eval_one,Int.cast_natCast]
  field_simp

/-- The actual normalized U-stage terminal transfer is bounded in absolute value by one on the entire original unit spectral interval.
Use: each appended Landweber kernel is maximized at the original zero endpoint.
Article: jacobi, Theorem 5.1.
Proof: its genuine numerator is sharply bounded by m+1, which is exactly its true positive denominator. -/
theorem uniformU_transfer_bound (m:ℕ) {l:ℝ} (hl:l∈Icc (0:ℝ) 1) :
    |(endpointMethod (uniformUChain m)).realization.scalarTransfer m l|≤1 := by
  rw [uniformU_transfer,abs_div,abs_of_pos (by positivity : (0:ℝ)<(m:ℝ)+1)]
  exact (div_le_one (by positivity : (0:ℝ)<(m:ℝ)+1)).mpr
    (abs_U_eval_le m (by rw [abs_le]; constructor <;> linarith [hl.1,hl.2]))

end
end jacobi.Applications
