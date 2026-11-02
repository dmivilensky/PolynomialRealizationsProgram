import jacobi.Variational.SpectralStability

/-!
Article: jacobi, Theorem C.5.
Multiplication by an actual scalar tending to one preserves a genuine
L1 spectral limit. The proof uses only summability and a direct norm bound.
Use: shiftedNodes_spectral_limit removes the actual source affine normalization theta_N.
-/
namespace jacobi.Analysis
noncomputable section
open Real Filter jacobi.Variational
open scoped Topology

/-- Scalar normalization tending to one preserves the entire original L1 spectral limit.
Use: shiftedNodes_spectral_limit removes the actual source affine normalization theta_N.
Article: jacobi, Theorem C.5.
Source: continuity of scalar multiplication in l1, proved here by its elementary series estimate.
Proof: split c*r-L as c*(r-L)+(c-1)*L. The two summed absolute errors
are bounded by |c| times the original L1 error and |c-1| times the fixed
summable limiting absolute mass; both tend to zero. -/
theorem scaled_spectral_limit {r:ℕ→ℕ→ℝ} {L:ℕ→ℝ} {c:ℕ→ℝ}
    (hr:∀n,Summable (r n)) (hL:Summable L)
    (hd:Tendsto (fun n => distance (r n) L) atTop (𝓝 0))
    (hc:Tendsto c atTop (𝓝 1)) :
    Tendsto (fun n => distance (fun k => c n*r n k) L) atTop (𝓝 0) := by
  -- Keep the limiting absolute mass fixed; no unproved uniform finite-mass bound is required.
  have hb := (hc.abs.mul hd).add (((hc.sub_const 1).abs).mul_const (∑'k,|L k|))
  simp only [abs_one,mul_zero,sub_self,abs_zero,zero_mul,add_zero] at hb
  apply squeeze_zero (fun _ => tsum_nonneg (fun _ => abs_nonneg _)) _ hb
  intro n
  have hp (k:ℕ) : |c n*r n k-L k|≤|c n| * |r n k-L k|+|c n-1| * |L k| := by
    rw [show c n*r n k-L k=c n*(r n k-L k)+(c n-1)*L k by ring]
    exact (abs_add_le ..).trans_eq (by rw [abs_mul,abs_mul])
  have hs := (((hr n).sub hL).abs.mul_left |c n|).add (hL.abs.mul_left |c n-1|)
  have ht := Summable.tsum_le_tsum hp (((hr n).mul_left (c n)).sub hL).abs hs
  rw [(((hr n).sub hL).abs.mul_left |c n|).tsum_add (hL.abs.mul_left |c n-1|),
    tsum_mul_left,tsum_mul_left] at ht
  exact ht

end
end jacobi.Analysis
