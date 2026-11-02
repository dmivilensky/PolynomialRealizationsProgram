import krylov.Functions.SegmentHessian
import Mathlib.Analysis.Calculus.FDeriv.Basic

/-!
Article: main_krylov, apG:sc(iv), uniform midpoint expansion for actual secants.
Use: derive the small-o bound uniformly over every segment in a shrinking ball,
from the genuine derivative of the Hessian at the centre. No remainder is a field.
Source: first-order Frechet differentiability, averaged along the actual segment.
-/

namespace krylov.Functions
noncomputable section
open Set Metric Filter Topology MeasureTheory chebyshev1.Nonlinear
variable {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [NormedAddCommGroup F] [NormedSpace ℝ F] [CompleteSpace F]

/-- A genuine Hessian derivative gives a uniform midpoint expansion on all small segments.
Article: main_krylov, apG:sc(iv).
Proof: the real Frechet little-o estimate holds on one common ball; integrate it
and evaluate the affine Hessian integral exactly at the midpoint. -/
theorem averagedHessian_midpoint_expansion (H : E → E →L[ℝ] F)
    (T : E →L[ℝ] E →L[ℝ] F) {r₀ : ℝ} (hr₀ : 0 < r₀)
    (hc : ContinuousOn H (ball 0 r₀)) (hD : HasFDerivAt H T 0) :
    ∀ ε : ℝ, 0 < ε → ∃ δ : ℝ, 0 < δ ∧ δ ≤ r₀ ∧
      ∀ R : ℝ, 0 ≤ R → R < δ → ∀ a u : E,
      (∀ t ∈ Icc (0 : ℝ) 1, ‖a + t • u‖ ≤ R) →
      ‖averagedDerivative H a u - H 0 - T (a + (1 / 2 : ℝ) • u)‖ ≤ ε * R := by
  intro ε hε
  have he : ∀ᶠ z : E in 𝓝 0, ‖H z - H 0 - T z‖ ≤ ε * ‖z‖ := by
    simpa only [zero_add] using
      Asymptotics.isLittleO_iff.mp (hasFDerivAt_iff_isLittleO_nhds_zero.mp hD) hε
  obtain ⟨r, hr, hrem⟩ := Metric.eventually_nhds_iff.mp he
  refine ⟨min r r₀, lt_min hr hr₀, min_le_right _ _, ?_⟩
  intro R _ hR a u hseg
  have hsub (t : ℝ) (ht : t ∈ Icc (0 : ℝ) 1) : a + t • u ∈ ball 0 r₀ := by
    rw [mem_ball, dist_zero_right]
    exact (hseg t ht).trans_lt (hR.trans_le (min_le_right _ _))
  have hiH : IntervalIntegrable (fun t : ℝ => H (a + t • u)) volume 0 1 :=
    (hc.comp (continuous_const.add (continuous_id.smul continuous_const)).continuousOn
    hsub).intervalIntegrable_of_Icc (μ := volume) (by norm_num : (0 : ℝ) ≤ 1)
  have hiA : IntervalIntegrable (fun t : ℝ => H 0 + T (a + t • u)) volume 0 1 :=
    (by fun_prop : Continuous _).intervalIntegrable 0 1
  have hI : averagedDerivative H a u - H 0 - T (a + (1 / 2 : ℝ) • u) =
      ∫ t in (0 : ℝ)..1, H (a + t • u) - (H 0 + T (a + t • u)) := by
    rw [intervalIntegral.integral_sub hiH hiA]
    change averagedDerivative H a u - H 0 - T (a + (1 / 2 : ℝ) • u) =
      averagedDerivative H a u - averagedDerivative (fun x => H 0 + T x) a u
    rw [averagedHessian_affine (H 0) T a u]
    abel
  rw [hI]
  have hb := intervalIntegral.norm_integral_le_of_norm_le (μ := volume)
    (by norm_num : (0 : ℝ) ≤ 1)
    (f := fun t : ℝ => H (a + t • u) - (H 0 + T (a + t • u)))
    (g := fun _ : ℝ => ε * R)
    (Filter.Eventually.of_forall fun t ht => by
      have ht' : t ∈ Icc (0 : ℝ) 1 := ⟨ht.1.le, ht.2⟩
      have hz : dist (a + t • u) 0 < r := by
        rw [dist_zero_right]
        exact (hseg t ht').trans_lt (hR.trans_le (min_le_left _ _))
      simpa only [sub_add_eq_sub_sub] using
        (hrem hz).trans (mul_le_mul_of_nonneg_left (hseg t ht') hε.le)) intervalIntegrable_const
  simpa using hb

end
end krylov.Functions
