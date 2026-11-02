import jacobi.Applications.BlockKernel
import jacobi.Applications.UniformUEnvelope
import jacobi.Applications.SpectralGain

/-!
Article: jacobi, Theorem 5.1.
The spectral endpoint maximizes every actual insertion in both the
uniform U stage and the complete appended Landweber stage. The genuine
full supremum therefore has the exact original finite-horizon formula.
Use: BlockComparison gives the optimum over the entire original U fibre
and its asymptotic comparison with the original Nesterov method.
-/
namespace jacobi.Applications
noncomputable section
open Set Polynomial jacobi.Finite chebyshev1
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1000000

/-- Every genuine canonical U-block insertion is maximized by the zero spectral pair, across both stages.
Use: uniformU_block_gain_eq_endpoint evaluates the actual supremum over the full original unit spectral square.
Article: jacobi, Theorem 5.1.
Proof: in the first stage the actual Chebyshev kernel is multiplied by a Landweber power of magnitude at most one. Every appended-stage kernel has two such powers and the true normalized U residual of magnitude at most one. Their endpoint values attain all these bounds simultaneously. -/
theorem uniformU_block_kernel_le_endpoint {m d s:ℕ} (hs:s<m+d) {l v:ℝ}
    (hl:l∈Icc (0:ℝ) 1) (hv:v∈Icc (0:ℝ) 1) :
    |(blockMethod (uniformUChain m)).realization.kernel (m+d) s l v|≤
      |(blockMethod (uniformUChain m)).realization.kernel (m+d) s 0 0| := by
  -- Both stage identities are for the actual full-horizon first variation, including all appended queries.
  have hpow (j:ℕ) {x:ℝ} (hx:x∈Icc (0:ℝ) 1) : |(1-x)^j|≤1 := by
    rw [abs_of_nonneg (pow_nonneg (by linarith [hx.2]) _)]
    exact pow_le_one₀ (by linarith [hx.2]) (by linarith [hx.1])
  by_cases hsm:s<m
  · rw [blockMethod,append_kernel_stage _ hsm,append_kernel_stage _ hsm]
    simp only [sub_zero,one_pow,one_mul,abs_mul]
    exact (mul_le_mul_of_nonneg_right (hpow d hl) (abs_nonneg _)).trans
      (by simpa only [one_mul] using uniformU_kernel_le_endpoint hsm hl hv)
  · let j := s-m
    have he : s=m+j := by dsimp [j]; omega
    have hj : j<d := by dsimp [j]; omega
    rw [he,blockMethod,append_kernel_landweber _ m hj,append_kernel_landweber _ m hj]
    rw [endpoint_transfer_zero _ (uniformU_inFiber m)]
    simp only [sub_zero,one_pow,neg_mul,mul_one,abs_neg,abs_one,abs_mul]
    exact (mul_le_mul (mul_le_mul (hpow (d-j-1) hl) (hpow j hv) (abs_nonneg _) zero_le_one)
      (uniformU_transfer_bound m hv) (abs_nonneg _) (by norm_num)).trans_eq (by ring)

/-- The true full spectral gain of every canonical U-plus-Landweber block is attained at the zero spectral pair.
Use: its squared value is the exact original energy identity, rather than only an endpoint lower bound.
Article: jacobi, Theorem 5.1.
Proof: apply the genuine compact-square maximization theorem to the actual simultaneous two-stage kernel bounds. -/
theorem uniformU_block_gain_eq_endpoint (m d:ℕ) :
    unitSpectralGain (blockMethod (uniformUChain m)).realization (m+d)=
      (blockMethod (uniformUChain m)).realization.kernelNorm (m+d) 0 0 :=
  unitSpectralGain_eq_endpoint _ _ (fun _ hs _ hl _ hv => uniformU_block_kernel_le_endpoint hs hl hv)

/-- The full genuine spectral gain of the original canonical block has exactly its inverse-energy value.
Use: the even-horizon formula and the full-fibre optimal leading gain use the same actual block and full spectral supremum.
Article: jacobi, Theorem 5.1.
Proof: the genuine endpoint attains the full gain; the proved actual two-stage endpoint identity gives its exact original inverse energy plus every appended step. -/
theorem uniformU_block_gain_energy (m d:ℕ) :
    (unitSpectralGain (blockMethod (uniformUChain m)).realization (m+d))^2=
      4*(uniformUChain m).energy+(d:ℝ) := by
  rw [uniformU_block_gain_eq_endpoint]
  exact block_endpoint_square _ (uniformU_inFiber m) d

/-- The exact canonical even-horizon block gain includes all of the article's finite corrections.
Use: BlockComparison proves the sharp full-fibre leading constant and its sqrt(2) ratio to the original Nesterov gain.
Article: jacobi, Theorem 5.1.
Proof: use the true full spectral maximum and exact finite U energy, then rewrite the original application count k=m+(m+2). All remaining arithmetic is an exact rational identity. -/
theorem uniformU_even_block_gain_square (m:ℕ) :
    (unitSpectralGain (blockMethod (uniformUChain m)).realization (2*m+2))^2=
      ((2*m+2:ℕ):ℝ)^3/15+((2*m+2:ℕ):ℝ)/2+1-16/(15*((2*m+2:ℕ):ℝ)) := by
  rw [show 2*m+2=m+(m+2) by omega,uniformU_block_gain_energy,uniformU_energy]
  push_cast
  field_simp
  ring

end
end jacobi.Applications
