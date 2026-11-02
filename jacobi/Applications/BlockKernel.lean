import jacobi.Applications.AppendLandweber
import jacobi.Applications.EndpointKernel

/-!
Article: jacobi, Proposition 1.2.
Both stages of the true appended block have their original first-variation
kernels. The exact endpoint identity applies to every matrix in the full
Jacobi fibre, including the empty stage, before any spectral optimization.
Use: UniformBlockGain and BlockComparison compare the true spectral gains.
-/
namespace jacobi.Applications
noncomputable section
open Matrix Polynomial jacobi.Finite chebyshev1 chebyshev2
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1000000

/-- The true two-term spectral kernel factors into its actual tail, original step size and genuine prefix transfer.
Use: both appended-stage kernel formulas use the earlier article's actual first variation.
Article: jacobi, Proposition 1.2.
Proof: the original TwoTerm query is the first memory coordinate and its injection is its original stepsize times that coordinate. Expand the reused rank-one kernel and contract its first row and column. -/
theorem twoTerm_kernel_factorization (S:TwoTerm) (k s:ℕ) (l v:ℝ) :
    S.realization.kernel k s l v=
      -(orderedProduct (fun i => S.realization.scalarStep (s+1+i) l) (k-(s+1)) 0 0*
        S.gamma s*S.realization.scalarTransfer s v) := by
  simp [Realization.kernel,Realization.scalarTransfer,Matrix.mul_apply,Fin.sum_univ_two]

/-- Every first-stage genuine insertion acquires exactly the terminal Landweber factor.
Use: UniformBlockGain applies the sharp Chebyshev bound to the actual original Jacobi-stage kernels.
Article: jacobi, Proposition 1.2.
Proof: the original causal kernel factors at its insertion. Its true tail crosses the boundary by append_tail_stage, while its prefix and stepsize remain exactly those of the unchanged original stage. -/
theorem append_kernel_stage (S:TwoTerm) {m s:ℕ} (hs:s<m) (d:ℕ) (l v:ℝ) :
    (appendLandweber S m).realization.kernel (m+d) s l v=
      (1-l)^d*S.realization.kernel m s l v := by
  -- The actual derivative includes every appended step after the insertion, in its original causal order.
  rw [twoTerm_kernel_factorization,twoTerm_kernel_factorization]
  rw [show m+d-(s+1)=m-(s+1)+d by omega,append_tail_stage S (by omega)]
  have hp : (appendLandweber S m).realization.scalarTransfer s v=S.realization.scalarTransfer s v := by
    simp only [Realization.scalarTransfer,TwoTerm.scalarContract]
    simpa only [Nat.zero_add] using congrArg (fun M:Matrix (Fin 2) (Fin 2) ℝ => M 0 0)
      (append_prefix S (m := m) (r := 0) (n := s) (by omega) v)
  rw [hp]
  simp only [appendLandweber,ite_eq_left hs]
  ring

/-- Every genuine Landweber-stage insertion has exactly its two scalar propagation factors and the true original stage residual.
Use: proves the complete terminal-equivalent block gain, including the contributions of all appended Hessian queries.
Article: jacobi, Proposition 1.2.
Proof: after the insertion the actual first row is the true Landweber power; before it the exact causal split gives the original stage residual multiplied by j actual Landweber factors. Its actual stepsize is one. -/
theorem append_kernel_landweber (S:TwoTerm) (m:ℕ) {d j:ℕ} (hj:j<d) (l v:ℝ) :
    (appendLandweber S m).realization.kernel (m+d) (m+j) l v=
      -(1-l)^(d-j-1)*(1-v)^j*S.realization.scalarTransfer m v := by
  rw [twoTerm_kernel_factorization]
  rw [show m+d-(m+j+1)=d-j-1 by omega,(append_tail_after S (m := m) (r := m+j+1) (by omega) (d-j-1) l).1,
    append_transfer]
  simp only [appendLandweber,ite_eq_right (not_lt.mpr (Nat.le_add_right m j))]
  ring

/-- The original endpoint-normalized Jacobi stage followed by literal Landweber steps.
Use: block_endpoint_square holds over the complete original fibre and the canonical U block attains the optimal leading full spectral gain.
Article: jacobi, Proposition 1.2.
-/
def blockMethod {m:ℕ} (J:Jacobi m) : TwoTerm := appendLandweber (endpointMethod J) m

/-- The original Jacobi-stage transfer is exactly one at the zero spectral endpoint.
Use: each genuine appended Landweber endpoint insertion has amplitude minus one.
Article: jacobi, Proposition 1.2.
Proof: exact prefix polynomial semantics give p_m(1)/p_m(1); the actual original fibre makes that denominator strictly positive. -/
theorem endpoint_transfer_zero {m:ℕ} (S:Nodes m) {J:Jacobi m} (hJ:InFiber J S.polynomial) :
    (endpointMethod J).realization.scalarTransfer m 0=1 := by
  rw [← Realization.residualPolynomial_eval,endpoint_prefix_exact S hJ m le_rfl,endpointResidual_eval]
  simp [(endpoint_prefix_pos S hJ le_rfl).ne']

/-- The exact endpoint squared gain of every true terminal-equivalent Jacobi block equals four times its original inverse energy plus its Landweber stage length.
Use: the complete-fibre lower bound and the canonical upper candidate in Theorem 5.1 use precisely the same original endpoint channel.
Article: jacobi, Theorem 5.1.
Proof: split the genuine squared kernel sum at the exact stage boundary. Every original Jacobi endpoint insertion is -2*d_i by its actual cofactor identity; every appended Landweber endpoint insertion is -1 by exact terminal normalization. -/
theorem block_endpoint_square {m:ℕ} (S:Nodes m) {J:Jacobi m} (hJ:InFiber J S.polynomial) (d:ℕ) :
    (blockMethod J).realization.kernelNorm (m+d) 0 0^2=4*J.energy+(d:ℝ) := by
  -- Both true stages contribute; no unperturbed terminal-polynomial identity is substituted for a first variation.
  rw [Realization.kernelNorm,Real.sq_sqrt (Finset.sum_nonneg (fun _ _ => sq_nonneg _)),Finset.sum_range_add]
  have hfirst : (∑ s∈Finset.range m,((blockMethod J).realization.kernel (m+d) s 0 0)^2)=4*J.energy := by
    calc
      _ = ∑ s∈Finset.range m,((endpointMethod J).realization.kernel m s 0 0)^2 := by
        apply Finset.sum_congr rfl
        intro s hs
        rw [blockMethod,append_kernel_stage _ (Finset.mem_range.mp hs)]
        simp
      _ = ∑ s:Fin m,((endpointMethod J).realization.kernel m s.val 0 0)^2 :=
        (Fin.sum_univ_eq_sum_range _ _).symm
      _ = 4*J.energy := by
        rw [Jacobi.energy,Finset.mul_sum]
        apply Finset.sum_congr rfl
        intro s _
        rw [endpoint_kernel_green S hJ]
        ring
  rw [hfirst]
  congr 1
  calc
    _ = ∑ _s∈Finset.range d,(1:ℝ) := by
      apply Finset.sum_congr rfl
      intro j hj
      rw [blockMethod,append_kernel_landweber _ m (Finset.mem_range.mp hj),endpoint_transfer_zero S hJ]
      norm_num
    _ = _ := by simp

end
end jacobi.Applications
