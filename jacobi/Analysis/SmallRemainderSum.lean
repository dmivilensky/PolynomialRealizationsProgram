import Mathlib.Analysis.Normed.Group.Tannery
import Mathlib.Tactic

/-!
Article: jacobi, Appendix C.4 (uniform Gram limit and coercivity).
A finite row dominated by a summable positive sequence plus an error
whose total row mass vanishes has the sum of its pointwise limits.
This retains the original little-o remainder of the actual Gram
summands instead of assuming an unavailable pure summable bound.
Source: Tannery's theorem and a finite-sum norm estimate.
Use: the actual Gram half-rows satisfy exactly C/(k+1)^2+epsilon_n from gramSummand_bound, with (N n+1)*epsilon_n->0. This theorem proves the full growing spectral-tail passage required by the two-edge Gram limit.
-/
namespace jacobi.Analysis
noncomputable section
open Real Finset Filter
open scoped Topology

/-- Finite original rows with a summable majorant and a uniformly distributed vanishing total remainder converge to the sum of their genuine pointwise limits.
Use: the actual Gram half-rows satisfy exactly C/(k+1)^2+epsilon_n from gramSummand_bound, with (N n+1)*epsilon_n->0. This theorem proves the full growing spectral-tail passage required by the two-edge Gram limit.
Article: jacobi, Appendix C.4 (uniform Gram limit and coercivity).
Source: mathlib tendsto_tsum_of_dominated_convergence, Tannery's theorem.
Proof: damp each original row value by g_k/(g_k+epsilon_n). The damped rows have the genuine fixed summable majorant g and the same pointwise limits. Their original finite-row difference has norm at most (N n+1)*epsilon_n, which tends to zero. Tannery gives the damped-row limit and adding the vanishing difference recovers the entire original row. -/
theorem finite_row_small_remainder (N:ℕ→ℕ) (f:ℕ→ℕ→ℝ) (F g:ℕ→ℝ) (ε:ℕ→ℝ)
    (hg:∀k,0<g k) (hgs:Summable g) (hε:∀n,0≤ε n)
    (hεlim:Tendsto (fun n:ℕ => ((N n:ℝ)+1)*ε n) atTop (𝓝 0))
    (hsupport:∀n k,N n<k→f n k=0)
    (hbound:∀ᶠn:ℕ in atTop,∀k,|f n k|≤g k+ε n)
    (hpoint:∀k,Tendsto (fun n => f n k) atTop (𝓝 (F k))) :
    Tendsto (fun n:ℕ => ∑k∈range (N n+1),f n k) atTop (𝓝 (∑'k,F k)) := by
  -- The original common remainder is summed over its actual finite row, rather than over an artificial infinite row.
  have hεzero : Tendsto ε atTop (𝓝 0) := squeeze_zero (fun n => hε n)
    (fun n => by nlinarith [hε n,Nat.cast_nonneg (N n) (α:=ℝ)]) hεlim
  let d (n k:ℕ) : ℝ := f n k*g k/(g k+ε n)
  have hden (n k:ℕ) : 0<g k+ε n := add_pos_of_pos_of_nonneg (hg k) (hε n)
  have hdpoint (k:ℕ) : Tendsto (fun n => d n k) atTop (𝓝 (F k)) := by
    have h := ((hpoint k).mul_const (g k)).div (hεzero.const_add (g k)) (by simpa using (hg k).ne')
    change Tendsto (fun n => f n k*g k/(g k+ε n)) atTop (𝓝 (F k*g k/(g k+0))) at h
    simpa only [d,add_zero,mul_div_cancel_right₀ _ (hg k).ne'] using h
  have hdbound : ∀ᶠn:ℕ in atTop,∀k,‖d n k‖≤g k := by
    filter_upwards [hbound] with n hn
    intro k
    dsimp only [d]
    rw [Real.norm_eq_abs,abs_div,abs_mul,abs_of_pos (hg k),abs_of_pos (hden n k)]
    exact (div_le_iff₀ (hden n k)).mpr
      (by nlinarith [mul_le_mul_of_nonneg_right (hn k) (hg k).le])
  have hdlim := tendsto_tsum_of_dominated_convergence hgs hdpoint hdbound
  have hdsum (n:ℕ) : (∑'k,d n k)=∑k∈range (N n+1),d n k := by
    apply tsum_eq_sum
    intro k hk
    have hnk : N n<k := by have := not_lt.mp (show ¬k<N n+1 by simpa only [mem_range] using hk); omega
    simp only [d,hsupport n k hnk,zero_mul,zero_div]
  have herr : Tendsto (fun n:ℕ => ∑k∈range (N n+1),(f n k-d n k)) atTop (𝓝 0) := by
    apply squeeze_zero_norm' _ hεlim
    filter_upwards [hbound] with n hn
    have hterm (k:ℕ) : |f n k-d n k|≤ε n := by
      have he : f n k-d n k=f n k*ε n/(g k+ε n) := by
        dsimp [d]
        field_simp [(hden n k).ne']
        ring
      rw [he,abs_div,abs_mul,abs_of_nonneg (hε n),abs_of_pos (hden n k)]
      exact (div_le_iff₀ (hden n k)).mpr
        (by nlinarith [mul_le_mul_of_nonneg_right (hn k) (hε n)])
    calc
      _ ≤ ∑k∈range (N n+1),‖f n k-d n k‖ := norm_sum_le _ _
      _ ≤ ∑_k∈range (N n+1),ε n := sum_le_sum (fun k _ => by simpa only [Real.norm_eq_abs] using hterm k)
      _ = _ := by simp only [sum_const,card_range,nsmul_eq_mul,Nat.cast_add,Nat.cast_one]
  have h := herr.add hdlim
  simp only [zero_add] at h
  apply (tendsto_congr ?_).mpr h
  intro n
  rw [hdsum,sum_sub_distrib,sub_add_cancel]

end
end jacobi.Analysis
