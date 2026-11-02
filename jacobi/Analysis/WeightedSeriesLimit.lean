import Mathlib.Analysis.Normed.Group.InfiniteSum
import Mathlib.MeasureTheory.Integral.DominatedConvergence
import Mathlib.Analysis.Normed.Group.Tannery
import Mathlib.Tactic

/-!
Article: jacobi, Theorem 2.1.
A genuinely L1-convergent spectral weight array can be summed against
uniformly bounded moving observables with coordinatewise limits. Only
the fixed limiting spectrum is used for dominated convergence.
Source: dominated convergence for series and the triangle inequality.
Use: the original eigenvector products yield the actual finite Green matrix limit, its diagonal profile and the persymmetric energy limit.
-/
namespace jacobi.Analysis
noncomputable section
open Real Filter
open scoped Topology

/-- An actual L1 spectral limit passes through every bounded moving
spectral observable with its genuine coordinatewise limit.
Use: the original eigenvector products yield the actual finite Green
matrix limit, its diagonal profile and the persymmetric energy limit.
Article: jacobi, Theorem 2.1.
Proof: split the sum into the spectral-weight error against the bounded
finite observable and the limiting weights against the moving observable.
The first error is bounded by its L1 distance; the second converges by
dominated convergence with the actual summable limiting spectrum. -/
theorem weighted_series_limit {r:ℕ→ℕ→ℝ} {L:ℕ→ℝ} {f:ℕ→ℕ→ℝ} {g:ℕ→ℝ}
    (hr:∀n,Summable (r n)) (hL:Summable L)
    (hd:Tendsto (fun n => ∑'k,|r n k-L k|) atTop (𝓝 0))
    {C:ℝ} (hf:∀ᶠn in atTop,∀k,|f n k|≤C)
    (hp:∀k,Tendsto (fun n => f n k) atTop (𝓝 (g k))) :
    Tendsto (fun n => ∑'k,r n k*f n k) atTop (𝓝 (∑'k,L k*g k)) := by
  -- The finite spectra need no common summable pointwise majorant.
  have hlim' : Tendsto (fun n => ∑'k,L k*f n k) atTop (𝓝 (∑'k,L k*g k)) := by
    apply tendsto_tsum_of_dominated_convergence (hL.abs.mul_right C)
      (fun k => (hp k).const_mul (L k))
    filter_upwards [hf] with n hn k
    rw [norm_mul,Real.norm_eq_abs,Real.norm_eq_abs]
    exact mul_le_mul_of_nonneg_left (hn k) (abs_nonneg _)
  have herr : Tendsto (fun n => (∑'k,r n k*f n k)-(∑'k,L k*f n k)) atTop (𝓝 0) := by
    apply squeeze_zero_norm' ?_ (by simpa only [mul_zero] using hd.const_mul C)
    filter_upwards [hf] with n hn
    have hs : Summable (fun k => (r n k-L k)*f n k) :=
      ((hr n).sub hL).abs.mul_right C |>.of_norm_bounded
        (fun k => by rw [norm_mul,Real.norm_eq_abs,Real.norm_eq_abs]; exact mul_le_mul_of_nonneg_left (hn k) (abs_nonneg _))
    have hsR : Summable (fun k => r n k*f n k) :=
      (hr n).abs.mul_right C |>.of_norm_bounded
        (fun k => by rw [norm_mul,Real.norm_eq_abs,Real.norm_eq_abs]; exact mul_le_mul_of_nonneg_left (hn k) (abs_nonneg _))
    have hsL : Summable (fun k => L k*f n k) :=
      hL.abs.mul_right C |>.of_norm_bounded
        (fun k => by rw [norm_mul,Real.norm_eq_abs,Real.norm_eq_abs]; exact mul_le_mul_of_nonneg_left (hn k) (abs_nonneg _))
    rw [← hsR.tsum_sub hsL]
    simp_rw [← sub_mul]
    have hpoint (k:ℕ) : ‖(r n k-L k)*f n k‖≤|r n k-L k| * C := by
      rw [norm_mul,Real.norm_eq_abs,Real.norm_eq_abs]
      exact mul_le_mul_of_nonneg_left (hn k) (abs_nonneg _)
    have hle := Summable.tsum_le_tsum hpoint
      hs.norm (((hr n).sub hL).abs.mul_right C)
    exact (norm_tsum_le_tsum_norm hs.norm).trans (by simpa only [tsum_mul_right,mul_comm C] using hle)
  simpa only [sub_add_cancel,zero_add] using herr.add hlim'

end
end jacobi.Analysis
