import jacobi.Applications.EndpointKernel
import chebyshev1.Realization.GainBounds

/-!
Article: jacobi, Proposition 1.2.
The first article's exact Jacobi first variation applies to every original
polynomial fibre. Its normalization denominators follow from the actual
prescribed spectrum, without a Chebyshev terminal-polynomial assumption.
Use: Article combines this general interval theorem with EndpointKernel's
zero-lower-endpoint result to check the complete source proposition.
-/
namespace jacobi.Applications
noncomputable section
open Polynomial jacobi.Finite chebyshev1 chebyshev2
set_option maxHeartbeats 1000000

/-- Every original arbitrary polynomial-fibre matrix has positive Jacobi normalization denominators on every original positive spectral interval.
Use: general_drift_kernel invokes the reused actual first-variation theorem with all admissibility hypotheses discharged.
Article: jacobi, Proposition 1.2.
Proof: the exact original matrix spectrum is the prescribed node list in (-1,1). The earlier general principal-pencil positivity theorem applies to that spectrum. -/
theorem general_drift_admissible {N:ℕ} (S:Nodes N) {J:Jacobi N}
    (hJ:InFiber J S.polynomial) (I:SpectralInterval) : J.data.Admissible I N := by
  apply J.data.admissible_of_spectrum I N J.coupling_nonneg
  intro x hx
  change x∈spectrum ℝ J.matrix at hx
  rw [S.spectrum_eq hJ] at hx
  obtain ⟨i,rfl⟩:=hx
  exact ⟨(S.interval i).1.le,(S.interval i).2.le⟩

/-- The actual arbitrary-fibre realization has the printed full two-spectral-variable kernel on every positive spectral interval.
Use: general_drift_endpoint identifies the endpoint channel with the original inverse diagonal.
Article: jacobi, Proposition 1.2.
Proof: reuse the first article's genuine operator first-variation kernel and exact two-sided continuant factorization. The original fibre's spectrum proves admissibility. -/
theorem general_drift_kernel {N:ℕ} (S:Nodes N) {J:Jacobi N}
    (hJ:InFiber J S.polynomial) (I:SpectralInterval) {i:ℕ} (hi:i<N) (l v:ℝ) :
    (J.data.realization I).kernel N i l v=
      -2*(J.data.leading i).eval (I.z v)*(J.data.block (i+1) (N-(i+1))).eval (I.z l)/
        (I.delta*J.data.den I N) := by
  rw [J.data.kernel_eq I (general_drift_admissible S hJ I) i hi]
  ring

/-- Every actual original endpoint insertion is the printed positive-normalization multiple of its genuine resolvent diagonal.
Use: general_drift_endpoint_norm gives the exact time norm and the complete full-gain energy lower bound.
Article: jacobi, Proposition 1.2.
Proof: the actual endpoint coordinate is one. Its two true complementary continuants are the independently proved diagonal cofactor quotient, whose full normalization is strictly positive. -/
theorem general_drift_endpoint {N:ℕ} (S:Nodes N) {J:Jacobi N}
    (hJ:InFiber J S.polynomial) (I:SpectralInterval) (i:Fin N) :
    (J.data.realization I).kernel N i I.mu I.mu=
      -(2*(J.data.leading N).eval 1/(I.delta*J.data.den I N))*J.green i i := by
  have hN:0<N:=by have hi:=i.isLt; omega
  rw [general_drift_kernel S hJ I i.isLt,I.z_mu,J.green_diagonal hN]
  field_simp [(endpoint_prefix_pos S hJ le_rfl).ne']

/-- The actual positive-interval endpoint time norm is exactly the printed original inverse-energy expression.
Use: general_drift_gain_lower bounds the full original spectral gain with no terminal-polynomial restriction.
Article: jacobi, Proposition 1.2.
Proof: square the actual endpoint kernels and sum their exact cofactor values over every original vertex. The positive normalization fixes the nonnegative square-root branch. -/
theorem general_drift_endpoint_norm {N:ℕ} (S:Nodes N) {J:Jacobi N}
    (hJ:InFiber J S.polynomial) (I:SpectralInterval) :
    (J.data.realization I).kernelNorm N I.mu I.mu=
      (2*(J.data.leading N).eval 1/(I.delta*J.data.den I N))*Real.sqrt J.energy := by
  -- Every original endpoint insertion contributes its own true inverse-diagonal square.
  let c:=2*(J.data.leading N).eval 1/(I.delta*J.data.den I N)
  have hc:0<c:=div_pos (mul_pos (by norm_num) (endpoint_prefix_pos S hJ le_rfl))
    (mul_pos I.delta_pos (general_drift_admissible S hJ I N le_rfl))
  have he:(∑ i:Fin N,((J.data.realization I).kernel N i I.mu I.mu)^2)=c^2*J.energy:=by
    rw [Jacobi.energy,Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro i _
    rw [general_drift_endpoint S hJ I i]
    change (-c*J.green i i)^2=c^2*(J.green i i)^2
    ring
  rw [Fin.sum_univ_eq_sum_range (f:=fun i:ℕ=>((J.data.realization I).kernel N i I.mu I.mu)^2)] at he
  rw [Realization.kernelNorm,he,Real.sqrt_mul (sq_nonneg _),Real.sqrt_sq_eq_abs,abs_of_pos hc]

/-- The true full spectral gain of every original arbitrary-fibre Jacobi realization dominates the article's inverse-energy endpoint value.
Use: Article checks the complete positive-interval conclusion of Proposition 1.2, alongside the proved unit-interval equality.
Article: jacobi, Proposition 1.2.
Proof: the original lower endpoint belongs to the genuine spectral interval, so its exactly evaluated time norm is bounded by the actual compact spectral supremum. -/
theorem general_drift_gain_lower {N:ℕ} (S:Nodes N) {J:Jacobi N}
    (hJ:InFiber J S.polynomial) (I:SpectralInterval) :
    (2*(J.data.leading N).eval 1/(I.delta*J.data.den I N))*Real.sqrt J.energy≤
      (J.data.realization I).gain I N := by
  rw [← general_drift_endpoint_norm S hJ I]
  exact Realization.kernelNorm_le_gain _ I N ⟨le_rfl,I.mu_lt_L.le⟩ ⟨le_rfl,I.mu_lt_L.le⟩

end
end jacobi.Applications
