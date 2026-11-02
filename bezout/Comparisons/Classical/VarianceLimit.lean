import bezout.Comparisons.Classical.Variance
import bezout.Comparisons.Classical.Exterior
import Mathlib.Analysis.SpecificLimits.Normed

/-!
Article: bezout, the fixed-interval positive classical variance limit after
Equation `eq:classical-variance`.
Use: distinguishes the classical exact-terminal history from the vanishing
Flat variance coefficient without any numerical experiment.
Proof: reverse the finite energy sum, use an exact geometric envelope, and
apply dominated convergence for an absolutely summable weighted geometric series.
-/

namespace bezout.Classical
noncomputable section
open Filter Topology
open scoped BigOperators

/-- Reverse-time variance summand, extended by zero beyond the actual horizon. -/
def varianceTerm (I : chebyshev1.SpectralInterval) (N k : ℕ) : ℝ :=
  if 0<k ∧ k≤N then
    ((k:ℝ)*(I.epsilon N*I.den (N-k))*initialWeight (N-k))^2 else 0

/-- The positive limiting weighted-geometric variance coefficient. -/
def varianceLimit (I : chebyshev1.SpectralInterval) : ℝ :=
  (16/I.delta^2)*∑' k : ℕ, (k:ℝ)^2*decay I^(2*k)

/-- Startup never enlarges the full geometric majorant. -/
theorem initialWeight_le_one (s : ℕ) : initialWeight s ≤ 1 := by
  unfold initialWeight
  split_ifs <;> norm_num

/-- The zero reversed coefficient is absent for every horizon. -/
@[simp] theorem varianceTerm_zero (I : chebyshev1.SpectralInterval) (N : ℕ) :
    varianceTerm I N 0=0 := by simp [varianceTerm]

/-- Every reversed finite summand has a horizon-independent summable envelope. -/
theorem varianceTerm_le (I : chebyshev1.SpectralInterval) (N k : ℕ) :
    ‖varianceTerm I N k‖ ≤ 4*((k:ℝ)^2*decay I^(2*k)) := by
  unfold varianceTerm
  split_ifs with hk
  · rw [Real.norm_eq_abs, abs_of_nonneg (sq_nonneg _), decay_pow_two]
    have hc := scaled_den_le I N k hk.2
    have hw := initialWeight_le_one (N-k)
    have hw0 := (initialWeight_pos (N-k)).le
    have hx0 : 0 ≤ I.epsilon N*I.den (N-k) :=
      mul_nonneg (one_div_pos.mpr (I.den_pos N)).le (I.den_pos _).le
    have hp0 := pow_nonneg (decay_mem I).1.le k
    have hbound : (k:ℝ)*(I.epsilon N*I.den (N-k))*initialWeight (N-k) ≤
        2*((k:ℝ)*decay I^k) := by
      calc
        _ ≤ (k:ℝ)*(I.epsilon N*I.den (N-k))*1 :=
          mul_le_mul_of_nonneg_left hw (mul_nonneg (Nat.cast_nonneg k) hx0)
        _ ≤ _ := by nlinarith [mul_le_mul_of_nonneg_left hc (Nat.cast_nonneg k)]
    have hleft : 0 ≤ (k:ℝ)*(I.epsilon N*I.den (N-k))*initialWeight (N-k) := by positivity
    have hright : 0 ≤ 2*((k:ℝ)*decay I^k) := by positivity
    have hs := (sq_le_sq₀ hleft hright).mpr hbound
    nlinarith
  · simp only [norm_zero]
    exact mul_nonneg (by norm_num) (mul_nonneg (sq_nonneg _) (pow_nonneg (decay_mem I).1.le _))

/-- Each fixed reversed summand converges to its geometric limiting term. -/
theorem varianceTerm_tendsto (I : chebyshev1.SpectralInterval) (k : ℕ) :
    Tendsto (fun N : ℕ => varianceTerm I N k) atTop
      (𝓝 ((k:ℝ)^2*decay I^(2*k))) := by
  by_cases hk : k=0
  · subst k
    simp only [varianceTerm_zero, Nat.cast_zero, zero_pow (by decide : 2≠0), zero_mul]
    exact tendsto_const_nhds
  · have h := ((scaled_den_tendsto I k).const_mul (k:ℝ)).pow 2
    have he : ((k:ℝ)*decay I^k)^2=(k:ℝ)^2*decay I^(2*k) := by
      rw [decay_pow_two]
      ring
    rw [he] at h
    apply h.congr'
    filter_upwards [eventually_gt_atTop k] with N hN
    have hnk : N-k≠0 := by omega
    simp only [varianceTerm, show 0<k ∧ k≤N by omega, and_self, ite_true,
      initialWeight, hnk, ite_false, mul_one]

/-- Weighted geometric variance tails are absolutely summable. -/
theorem variance_series_summable (I : chebyshev1.SpectralInterval) :
    Summable (fun k : ℕ => (k:ℝ)^2*decay I^(2*k)) := by
  have hr : ‖decay I^2‖<1 := by
    rw [Real.norm_eq_abs, abs_of_nonneg (sq_nonneg _)]
    have h := mul_lt_mul_of_pos_left (decay_mem I).2 (decay_mem I).1
    nlinarith [(decay_mem I).2]
  have h := summable_pow_mul_geometric_of_norm_lt_one 2 hr
  simpa only [← pow_mul] using h

/-- The finite physical variance energy is exactly the sum of the reversed coefficients. -/
theorem variance_eq_tsum (I : chebyshev1.SpectralInterval) (N : ℕ) :
    variance I N=(16/I.delta^2)*∑' k : ℕ, varianceTerm I N k := by
  rw [tsum_eq_sum (s := Finset.range (N+1)) (by
    intro k hk
    have hnk : ¬k≤N := by simpa using hk
    simp only [varianceTerm, hnk, and_false, ite_false])]
  rw [← Finset.sum_range_reflect (fun k => varianceTerm I N k) (N+1)]
  simp only [Nat.add_sub_cancel]
  rw [Finset.sum_range_succ]
  simp only [Nat.sub_self, varianceTerm_zero, add_zero]
  unfold variance
  change (∑ s : Fin N, (fun s : ℕ => responseBound I N s^2) s.val)=_
  rw [Fin.sum_univ_eq_sum_range (fun s : ℕ => responseBound I N s^2) N, Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro s hs
  have hsN := Finset.mem_range.mp hs
  have hks : 0<N-s ∧ N-s≤N := by omega
  have hback : N-(N-s)=s := by omega
  simp only [varianceTerm, hks, and_self, ite_true, hback]
  have hcast : ((N-s:ℕ):ℝ)=(N:ℝ)-s := Nat.cast_sub (by omega)
  rw [hcast]
  unfold responseBound
  ring

/-- At every fixed strict positive spectral interval classical noise variance
converges to the article's positive infinite-series constant. -/
theorem variance_tendsto (I : chebyshev1.SpectralInterval) :
    Tendsto (variance I) atTop (𝓝 (varianceLimit I)) := by
  have ht := tendsto_tsum_of_dominated_convergence
    ((variance_series_summable I).mul_left 4) (varianceTerm_tendsto I)
    (Filter.Eventually.of_forall (fun N k => varianceTerm_le I N k))
  have h := ht.const_mul (16/I.delta^2)
  simpa only [← variance_eq_tsum, varianceLimit] using h

/-- The fixed-interval classical limiting noise coefficient is strictly positive. -/
theorem varianceLimit_pos (I : chebyshev1.SpectralInterval) : 0<varianceLimit I := by
  apply mul_pos (div_pos (by norm_num) (sq_pos_of_pos I.delta_pos))
  apply (variance_series_summable I).tsum_pos
    (fun k => mul_nonneg (sq_nonneg _) (pow_nonneg (decay_mem I).1.le _)) 1
  simpa using sq_pos_of_pos (decay_mem I).1

end
end bezout.Classical
