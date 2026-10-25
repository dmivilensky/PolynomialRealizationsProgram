import Mathlib.Analysis.SpecificLimits.Normed
import Mathlib.Topology.Algebra.InfiniteSum.Real
import Mathlib.Analysis.SpecialFunctions.Exp
import Mathlib.Tactic

/-!
Article: Appendix C, Lemmas prices and exactprice.
Use: an actual discounted one-step inequality controls the entire nonnegative
energy series once its terminal price tends to zero. The stationary geometric
series yields the exact uniform one-half lower bound used in the limit.
-/
noncomputable section
namespace polyak.FiniteHorizon
open Filter
open scoped BigOperators Topology

theorem discounted_price_partial (P a : ℕ → ℝ) {r δ : ℝ} (hr : 0≤r)
    (hstep : ∀ n, δ*a n≤P n-r*P (n+1)) (N : ℕ) :
    δ*(∑ i ∈ Finset.range N, r^i*a i)≤P 0-r^N*P N := by
  induction N with
  | zero => simp
  | succ N ih =>
    have hs:=mul_le_mul_of_nonneg_left (hstep N) (pow_nonneg hr N)
    rw [Finset.sum_range_succ,pow_succ]
    nlinarith

/-- A vanishing terminal price proves every finite partial energy bound. -/
theorem discounted_price_finite_bound (P a : ℕ → ℝ) {r δ : ℝ}
    (hr : 0≤r) (hδ : 0≤δ) (ha : ∀ n,0≤a n)
    (hstep : ∀ n, δ*a n≤P n-r*P (n+1))
    (htail : Tendsto (fun n => r^n*P n) atTop (𝓝 0)) (N : ℕ) :
    δ*(∑ i ∈ Finset.range N, r^i*a i)≤P 0 := by
  have hlim : Tendsto (fun n => P 0-r^n*P n) atTop (𝓝 (P 0)):=by
    simpa using tendsto_const_nhds.sub htail
  apply ge_of_tendsto hlim
  filter_upwards [eventually_ge_atTop N] with n hn
  have hs : (∑ i ∈ Finset.range N, r^i*a i)≤∑ i ∈ Finset.range n, r^i*a i :=
    Finset.sum_le_sum_of_subset_of_nonneg (Finset.range_mono hn)
      (fun i _ _ => mul_nonneg (pow_nonneg hr i) (ha i))
  exact (mul_le_mul_of_nonneg_left hs hδ).trans (discounted_price_partial P a hr hstep n)

/-- In particular, the actual price is nonnegative along every such trajectory. -/
theorem discounted_price_nonneg (P a : ℕ → ℝ) {r δ : ℝ}
    (hr : 0≤r) (hδ : 0≤δ) (ha : ∀ n,0≤a n)
    (hstep : ∀ n, δ*a n≤P n-r*P (n+1))
    (htail : Tendsto (fun n => r^n*P n) atTop (𝓝 0)) : 0≤P 0 := by
  simpa using discounted_price_finite_bound P a hr hδ ha hstep htail 0

/-- The full energy sum is summable and is bounded by the initial actual price. -/
theorem discounted_price_series (P a : ℕ → ℝ) {r δ : ℝ}
    (hr : 0≤r) (hδ : 0<δ) (ha : ∀ n,0≤a n)
    (hstep : ∀ n, δ*a n≤P n-r*P (n+1))
    (htail : Tendsto (fun n => r^n*P n) atTop (𝓝 0)) :
    Summable (fun n => r^n*a n) ∧ δ*(∑' n, r^n*a n)≤P 0 := by
  have hb (N : ℕ) : (∑ i ∈ Finset.range N,r^i*a i)≤P 0/δ := by
    apply (le_div_iff₀ hδ).mpr
    simpa only [mul_comm] using discounted_price_finite_bound P a hr hδ.le ha hstep htail N
  have hs : Summable (fun n => r^n*a n):=
    summable_of_sum_range_le (fun n => mul_nonneg (pow_nonneg hr n) (ha n)) hb
  refine ⟨hs,?_⟩
  have hlim : Tendsto (fun N => δ*(∑ i ∈ Finset.range N,r^i*a i)) atTop
      (𝓝 (δ*(∑' i,r^i*a i))) := tendsto_const_nhds.mul hs.hasSum.tendsto_sum_nat
  exact le_of_tendsto hlim (Eventually.of_forall
    (discounted_price_finite_bound P a hr hδ.le ha hstep htail))

/-- The stationary geometric energy has the uniform lower bound printed in exactprice. -/
theorem stationary_price_half_bound {δ c P : ℝ} (hδ : 0<δ) (hc : 0≤c)
    (hb : ∀ N : ℕ, δ*(∑ i ∈ Finset.range N, Real.exp (-2*δ)^i*c)≤P) : c/2≤P := by
  have hr : |Real.exp (-2*δ)|<1:=by rw [abs_of_pos (Real.exp_pos _)]; exact Real.exp_lt_one_iff.mpr (by linarith)
  have hs:=(summable_geometric_of_abs_lt_one hr).mul_right c
  have hsum : (∑' i : ℕ,Real.exp (-2*δ)^i*c)=c/(1-Real.exp (-2*δ)) := by
    rw [tsum_mul_right,tsum_geometric_of_abs_lt_one hr]
    ring
  have hp : δ*(c/(1-Real.exp (-2*δ)))≤P := by
    have hlim : Tendsto (fun N => δ*(∑ i ∈ Finset.range N,Real.exp (-2*δ)^i*c)) atTop
        (𝓝 (δ*(∑' i,Real.exp (-2*δ)^i*c))) :=
      tendsto_const_nhds.mul hs.hasSum.tendsto_sum_nat
    rw [hsum] at hlim
    exact le_of_tendsto hlim (Eventually.of_forall hb)
  have hd : 0<1-Real.exp (-2*δ):=by linarith [(abs_lt.mp hr).2]
  have he:=Real.add_one_le_exp (-2*δ)
  have hhalf : c/2≤δ*(c/(1-Real.exp (-2*δ))) := by
    rw [←mul_div_assoc]
    apply (le_div_iff₀ hd).mpr
    have hm:=mul_nonneg hc (show 0≤2*δ-(1-Real.exp (-2*δ)) by linarith)
    nlinarith
  exact hhalf.trans hp

end polyak.FiniteHorizon
