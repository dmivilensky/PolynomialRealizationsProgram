import jacobi.Analysis.WeightedSeriesLimit

/-!
Article: jacobi, Theorem 2.1.
The same L1 spectral summation argument works in every real Banach
space, in particular the nuclear-norm space already constructed in
chebyshev2. This preserves trace norm rather than only operator norm.
Source: Banach-valued dominated convergence for series.
Use: the finite embedded eigenprojectors converge in the actual nuclear-norm Banach space, proving the trace-norm assertion of Theorem 2.1.
-/
namespace jacobi.Analysis
noncomputable section
open Real Filter
open scoped Topology

/-- A genuine L1 spectral limit passes through bounded Banach-valued
observables with their actual coordinatewise norm limits.
Use: the finite embedded eigenprojectors converge in the actual
nuclear-norm Banach space, proving the trace-norm assertion of Theorem 2.1.
Article: jacobi, Theorem 2.1.
Proof: split the spectral-weight error from the moving-vector error.
The first is bounded by C times the original L1 spectral distance;
the second is dominated by the actual summable limiting spectrum. -/
theorem weighted_series_normed {E:Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E]
    {r:ℕ→ℕ→ℝ} {L:ℕ→ℝ} {f:ℕ→ℕ→E} {g:ℕ→E}
    (hr:∀n,Summable (r n)) (hL:Summable L)
    (hd:Tendsto (fun n => ∑'k,|r n k-L k|) atTop (𝓝 0))
    {C:ℝ} (hf:∀ᶠn in atTop,∀k,‖f n k‖≤C)
    (hp:∀k,Tendsto (fun n => f n k) atTop (𝓝 (g k))) :
    Tendsto (fun n => ∑'k,r n k • f n k) atTop (𝓝 (∑'k,L k • g k)) := by
  -- The limiting spectrum alone supplies the summable domination.
  have hlim : Tendsto (fun n => ∑'k,L k • f n k) atTop (𝓝 (∑'k,L k • g k)) := by
    apply tendsto_tsum_of_dominated_convergence (hL.abs.mul_right C)
      (fun k => (hp k).const_smul (L k))
    filter_upwards [hf] with n hn k
    rw [norm_smul,Real.norm_eq_abs]
    exact mul_le_mul_of_nonneg_left (hn k) (abs_nonneg _)
  have herr : Tendsto (fun n => (∑'k,r n k • f n k)-(∑'k,L k • f n k)) atTop (𝓝 0) := by
    apply squeeze_zero_norm' ?_ (by simpa only [mul_zero] using hd.const_mul C)
    filter_upwards [hf] with n hn
    have hb (v:ℕ→ℝ) (hv:Summable v) : Summable (fun k => v k • f n k) :=
      (hv.abs.mul_right C).of_norm_bounded (fun k => by
        rw [norm_smul,Real.norm_eq_abs]
        exact mul_le_mul_of_nonneg_left (hn k) (abs_nonneg _))
    rw [← (hb (r n) (hr n)).tsum_sub (hb L hL)]
    simp_rw [← sub_smul]
    have hpoint (k:ℕ) : ‖(r n k-L k) • f n k‖≤|r n k-L k| * C := by
      rw [norm_smul,Real.norm_eq_abs]
      exact mul_le_mul_of_nonneg_left (hn k) (abs_nonneg _)
    have hsNorm := (((hr n).sub hL).abs.mul_right C).of_nonneg_of_le (fun _ => norm_nonneg _) hpoint
    have hle := Summable.tsum_le_tsum hpoint hsNorm (((hr n).sub hL).abs.mul_right C)
    exact (norm_tsum_le_tsum_norm hsNorm).trans (by simpa only [tsum_mul_right,mul_comm C] using hle)
  simpa only [sub_add_cancel,zero_add] using herr.add hlim

end
end jacobi.Analysis
