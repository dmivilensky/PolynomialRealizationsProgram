import Mathlib.Analysis.Calculus.MeanValue
import Mathlib.Topology.Algebra.Order.LiminfLimsup
import Mathlib.Analysis.SpecificLimits.Basic
import Mathlib.Analysis.BoundedVariation

/-!
Article: main_krylov, apC:lem:fund, Taylor-sum justification of BV calculus.
Use: prove the nonlinear first-order remainder estimate and its accumulation
along finite partitions. A uniform small derivative oscillation costs only
that oscillation times the total variation, not the number of partition cells.
Source: mathlib's mean value inequality on convex segments and telescoping sums.
This is the analytic Taylor-sum step; identification of the limiting sums with
the continuous vector-measure integral remains a separate result.
-/

namespace krylov.ContinuumBV
noncomputable section
open Set Filter
open scoped Topology

variable {E : Type*} [NormedAddCommGroup E]

/-- A derivative oscillation bound on the genuine segment gives the exact
first-order Taylor remainder estimate used in the continuous BV chain rule. -/
theorem taylor_remainder_le [NormedSpace ℝ E] {F : E → ℝ} {D : E → E →L[ℝ] ℝ}
    {x y : E} {ε : ℝ}
    (hF : ∀ w ∈ segment ℝ x y, HasFDerivAt F (D w) w)
    (hD : ∀ w ∈ segment ℝ x y, ‖D w - D x‖ ≤ ε) :
    ‖F y - F x - D x (y - x)‖ ≤ ε * ‖y - x‖ := by
  have hd : ∀ w ∈ segment ℝ x y,
      HasFDerivWithinAt (fun z => F z - D x z) (D w - D x) (segment ℝ x y) w := by
    intro w hw
    exact ((hF w hw).sub (D x).hasFDerivAt).hasFDerivWithinAt
  have hb := (convex_segment x y).norm_image_sub_le_of_norm_hasFDerivWithin_le
    hd hD (left_mem_segment ℝ x y) (right_mem_segment ℝ x y)
  convert hb using 1
  rw [map_sub]
  congr 1
  ring

/-- Sum of local derivative actions along a finite state partition. -/
def derivativeSum [NormedSpace ℝ E] (D : E → E →L[ℝ] ℝ) (u : ℕ → E) (n : ℕ) : ℝ :=
  ∑ i ∈ Finset.range n, D (u i) (u (i + 1) - u i)

/-- The Taylor errors telescope exactly before any limiting argument. -/
theorem taylor_error_telescope [NormedSpace ℝ E] (F : E → ℝ) (D : E → E →L[ℝ] ℝ)
    (u : ℕ → E) (n : ℕ) :
    F (u n) - F (u 0) - derivativeSum D u n =
      ∑ i ∈ Finset.range n, (F (u (i + 1)) - F (u i) - D (u i) (u (i + 1) - u i)) := by
  rw [Finset.sum_sub_distrib, Finset.sum_range_sub (fun i => F (u i)) n]
  rfl

/-- The global partition error is bounded by derivative oscillation times
the total variation of this partition. The estimate is independent of its size. -/
theorem derivativeSum_error_le [NormedSpace ℝ E] {F : E → ℝ} {D : E → E →L[ℝ] ℝ}
    (u : ℕ → E) (n : ℕ) {ε : ℝ}
    (hF : ∀ i < n, ∀ w ∈ segment ℝ (u i) (u (i + 1)), HasFDerivAt F (D w) w)
    (hD : ∀ i < n, ∀ w ∈ segment ℝ (u i) (u (i + 1)), ‖D w - D (u i)‖ ≤ ε) :
    ‖F (u n) - F (u 0) - derivativeSum D u n‖ ≤
      ε * ∑ i ∈ Finset.range n, ‖u (i + 1) - u i‖ := by
  rw [taylor_error_telescope]
  calc
    _ ≤ ∑ i ∈ Finset.range n, ‖F (u (i + 1)) - F (u i) - D (u i) (u (i + 1) - u i)‖ :=
      norm_sum_le _ _
    _ ≤ ∑ i ∈ Finset.range n, ε * ‖u (i + 1) - u i‖ := by
      apply Finset.sum_le_sum
      intro i hi
      exact taylor_remainder_le (hF i (Finset.mem_range.1 hi)) (hD i (Finset.mem_range.1 hi))
    _ = _ := (Finset.mul_sum _ _ _).symm

/-- The real total variation controls every monotone physical partition.
This supplies the uniform bound independently of how fine the partition is. -/
theorem partition_variation_le {z : ℝ → E} {s : Set ℝ}
    (hz : BoundedVariationOn z s) {t : ℕ → ℝ} (ht : Monotone t)
    (hmem : ∀ i, t i ∈ s) (n : ℕ) :
    (∑ i ∈ Finset.range n, ‖z (t (i + 1)) - z (t i)‖) ≤
      (eVariationOn z s).toReal := by
  have he := ENNReal.toReal_mono hz (eVariationOn.sum_le ht hmem (n := n))
  rw [ENNReal.toReal_sum (fun _ _ => edist_ne_top _ _)] at he
  simpa only [edist_eq_enorm_sub, toReal_enorm] using he

/-- If the derivative oscillation vanishes and partition variation stays
bounded, the true nonlinear Taylor sums converge to the potential difference.
These are actual derivative sums, rather than an assumed BV chain identity. -/
theorem derivativeSum_tendsto [NormedSpace ℝ E] {F : E → ℝ} {D : E → E →L[ℝ] ℝ}
    (u : ℕ → ℕ → E) (n : ℕ → ℕ) {a b : E} {ε : ℕ → ℝ} {V : ℝ}
    (ha : ∀ k, u k 0 = a) (hb : ∀ k, u k (n k) = b)
    (hF : ∀ k i, i < n k → ∀ w ∈ segment ℝ (u k i) (u k (i + 1)),
      HasFDerivAt F (D w) w)
    (hD : ∀ k i, i < n k → ∀ w ∈ segment ℝ (u k i) (u k (i + 1)),
      ‖D w - D (u k i)‖ ≤ ε k)
    (hε : ∀ k, 0 ≤ ε k) (hεlim : Tendsto ε atTop (𝓝 0))
    (hV : ∀ k, (∑ i ∈ Finset.range (n k), ‖u k (i + 1) - u k i‖) ≤ V) :
    Tendsto (fun k => derivativeSum D (u k) (n k)) atTop (𝓝 (F b - F a)) := by
  apply tendsto_iff_norm_sub_tendsto_zero.2
  have hbound : ∀ k, ‖derivativeSum D (u k) (n k) - (F b - F a)‖ ≤ ε k * V := by
    intro k
    have he := derivativeSum_error_le (u k) (n k) (hF k) (hD k)
    rw [ha k, hb k] at he
    rw [norm_sub_rev]
    exact he.trans (mul_le_mul_of_nonneg_left (hV k) (hε k))
  apply squeeze_zero (fun _ => norm_nonneg _) hbound
  simpa only [zero_mul] using hεlim.mul_const V

end
end krylov.ContinuumBV
