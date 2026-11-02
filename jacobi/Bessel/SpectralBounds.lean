import jacobi.Jacobi.PaddedSpectrum
import Mathlib.Analysis.PSeries
import Mathlib.Analysis.Normed.Group.Tannery

/-!
Article: jacobi, Lemma 1.3.
The actual Bessel edge spectrum is genuinely summable. Passing the exact
finite Jacobi second traces through a summable inverse-square bound proves
the full second Rayleigh sum. The first sum is only bounded here; its
exact equality is a separate no-loss-of-mass argument.
Source: genuine ordered Jacobi limits, bounded positive traces and the community dominated convergence theorem for series.
Use: proves genuine summability before any canonical product or exact first Rayleigh sum is used.
-/
namespace jacobi.Bessel
noncomputable section
open Set Filter
open scoped Topology
set_option backward.isDefEq.respectTransparency false

/-- Every initial sum of the actual Bessel edge spectrum is bounded by the printed mass expression.
Use: proves genuine summability before any canonical product or exact first Rayleigh sum is used.
Article: jacobi, Lemma 1.3.
Proof: use the actual Jacobi family with beta=0. Each finite prefix
converges coordinatewise and is bounded by its genuine full finite trace,
whose exact limit is the printed M. Pass this inequality to the limit. -/
theorem edgeValue_partial_sum_le {a : ℝ} (ha : -1<a) (K : ℕ) :
    (∑ k∈Finset.range K,edgeValue a ha k)≤1/(2*(a+1)) := by
  -- A concrete valid finite Jacobi family supplies the bound, without any infinite spectral-sum assumption.
  have hb : (-1:ℝ)<0 := by norm_num
  have hp := tendsto_finsetSum (Finset.range K) (fun k _ => jacobi.Jacobi.finiteLambdaAt_tendsto ha hb k)
  have hm := jacobi.Jacobi.finiteLambda_sum_tendsto ha hb
  apply le_of_tendsto_of_tendsto hp hm
  exact Eventually.of_forall fun n => by
    change (∑ k∈Finset.range K,jacobi.Jacobi.finiteLambdaAt a 0 ha hb n k)≤
      ∑ i:Fin n,jacobi.Jacobi.finiteLambda a 0 ha hb n i
    have he := jacobi.Jacobi.finiteLambdaAt_tsum ha hb n id rfl
    simp only [id_eq] at he
    rw [← he]
    exact (jacobi.Jacobi.finiteLambdaAt_summable ha hb n).sum_le_tsum (Finset.range K)
      (fun k _ => jacobi.Jacobi.finiteLambdaAt_nonneg ha hb n k)

/-- The actual infinite Bessel edge spectrum is genuinely summable.
Use: defines the true convergent spectral sums and the actual genus-zero canonical product.
Article: jacobi, Lemma 1.3.
Proof: the actual positive spectrum has uniformly bounded genuine partial sums, so the community nonnegative-series theorem applies. -/
theorem edgeValue_summable {a : ℝ} (ha : -1<a) : Summable (edgeValue a ha) :=
  summable_of_sum_range_le (fun k => (edgeValue_properties ha).1 k |>.le) (edgeValue_partial_sum_le ha)

/-- The actual infinite Bessel edge mass is at most the printed mass expression.
Use: records the rigorous preliminary mass bound without silently assuming equality or excluding escape of finite trace.
Article: jacobi, Proposition C.4.
Proof: apply the genuine nonnegative tsum bound to the proved bounds for every partial sum. -/
theorem edgeValue_mass_le {a : ℝ} (ha : -1<a) :
    (∑' k,edgeValue a ha k)≤1/(2*(a+1)) :=
  Real.tsum_le_of_sum_range_le (fun k => (edgeValue_properties ha).1 k |>.le) (edgeValue_partial_sum_le ha)

/-- The inverse-square integer majorant with any fixed scalar numerator is genuinely summable.
Use: bounds every finite squared spectral entry and every resolvent remainder uniformly in finite degree.
Article: jacobi, Lemma 1.3.
Source: the classical p-series theorem for exponent two, proved in mathlib.
Proof: shift the community inverse-square series by one and multiply by the fixed numerator. -/
theorem inverse_square_majorant_summable (C : ℝ) : Summable (fun k : ℕ => C^2/(k+1:ℝ)^2) := by
  have h : Summable (fun k : ℕ => 1/(k:ℝ)^2) := Real.summable_one_div_nat_pow.mpr (by norm_num)
  have hs := h.comp_injective Nat.succ_injective
  have hm := hs.mul_left (C^2)
  simpa only [Function.comp_def,Nat.cast_succ,mul_one_div] using hm

/-- The squares of the actual Bessel edge eigenvalues are genuinely summable.
Use: the second Rayleigh sum and resolvent defect are true convergent series.
Article: jacobi, Section 3.2 (sharp comparison at U).
Proof: the positive decreasing spectrum is bounded by its first value;
each square is therefore at most that first value times the actual summable entry. -/
theorem edgeValue_square_summable {a : ℝ} (ha : -1<a) : Summable (fun k => (edgeValue a ha k)^2) := by
  apply ((edgeValue_summable ha).mul_left (edgeValue a ha 0)).of_nonneg_of_le (fun k => sq_nonneg _)
  intro k
  simpa only [pow_two] using mul_le_mul_of_nonneg_right
    ((edgeValue_properties ha).2.antitone (Nat.zero_le k)) ((edgeValue_properties ha).1 k).le

/-- The actual Bessel edge spectrum has the exact printed second Rayleigh sum.
Use: discharges T_2 for the genuine Bessel spectrum without a canonical-product or first-sum premise.
Article: jacobi, Lemma 1.3.
Proof: each genuine finite spectral entry converges to its canonical
Bessel entry. The actual bounded finite first traces and decreasing order
give C/(k+1) bounds, hence a summable inverse-square majorant for their
squares. Dominated convergence transfers the already evaluated exact
finite second traces to the actual infinite second Rayleigh sum. -/
theorem second_rayleigh_sum {a : ℝ} (ha : -1<a) :
    (∑' k,(edgeValue a ha k)^2)=1/(4*(a+1)^2*(a+2)) := by
  -- The finite reference uses beta=0 only to choose one genuine approximating family; the conclusion is the actual beta-independent Bessel sum.
  have hb : (-1:ℝ)<0 := by norm_num
  let C := jacobi.Jacobi.traceBound a 0
  have h := tendsto_tsum_of_dominated_convergence (inverse_square_majorant_summable C)
    (fun k => (jacobi.Jacobi.finiteLambdaAt_tendsto ha hb k).pow 2)
    (show ∀ᶠ n:ℕ in atTop,∀ k,‖(jacobi.Jacobi.finiteLambdaAt a 0 ha hb n k)^2‖≤C^2/(k+1:ℝ)^2 from by
      filter_upwards [eventually_gt_atTop (0:ℕ)] with n hn k
      rw [Real.norm_eq_abs,abs_of_nonneg (sq_nonneg _)]
      have hbnd := jacobi.Jacobi.finiteLambdaAt_index_bound ha hb hn k
      have hnon := jacobi.Jacobi.finiteLambdaAt_nonneg ha hb n k
      have hp := pow_le_pow_left₀ hnon hbnd 2
      simpa only [div_pow] using hp)
  have he : (fun n : ℕ => ∑' k,(jacobi.Jacobi.finiteLambdaAt a 0 ha hb n k)^2)=
      fun n : ℕ => ∑ i:Fin n,(jacobi.Jacobi.finiteLambda a 0 ha hb n i)^2 :=
    funext fun n => jacobi.Jacobi.finiteLambdaAt_tsum ha hb n (fun x => x^2) (by norm_num)
  rw [he] at h
  exact tendsto_nhds_unique h (jacobi.Jacobi.finiteLambda_square_sum_tendsto ha hb)

end
end jacobi.Bessel
