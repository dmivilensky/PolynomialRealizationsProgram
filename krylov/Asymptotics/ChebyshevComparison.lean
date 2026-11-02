import krylov.LotkaVolterra.HalfCoarseBound
import krylov.Asymptotics.DesignUpperBound
import krylov.Design.PoissonMajorants
import Mathlib.Analysis.Complex.ExponentialBounds
import Mathlib.Analysis.Real.Pi.Bounds

/-!
Article: main_krylov, thm:limit, comparison with the Chebyshev majorant.
Use: certify the retained kappa>=1600 statement with a modest rational
shooting bound, actual Poisson remainder positivity and elementary calculus.
Source: the proved rational half-gamma barrier and mathlib's pi/log(2) bounds.
-/

namespace krylov.Asymptotics
noncomputable section
open Real Set MeasureTheory
open krylov.Design krylov.LotkaVolterra krylov.ContinuumControl
open scoped Topology

/-- A coarse elementary logarithm upper bound, proved by differentiating
the symmetric rational majorant rather than evaluating log numerically. -/
theorem log_le_half_sub_inv {x : ℝ} (hx : 1 ≤ x) : log x ≤ (x - x⁻¹) / 2 := by
  let f : ℝ → ℝ := fun x ↦ (x - x⁻¹) / 2 - log x
  have hd (y : ℝ) (hy : 1 ≤ y) : HasDerivAt f ((1 + y⁻¹ ^ 2) / 2 - y⁻¹) y := by
    have hn : y ≠ 0 := by linarith
    convert (((hasDerivAt_id y).sub ((hasDerivAt_id y).inv hn)).div_const 2).sub
      (hasDerivAt_log hn) using 1
    · rfl
    · simp only [id_eq]
      field_simp [hn]
      ring
  have hm : MonotoneOn f (Ici 1) := by
    apply monotoneOn_of_deriv_nonneg (convex_Ici 1)
      (fun y hy ↦ (hd y hy).continuousAt.continuousWithinAt)
      (fun y hy ↦ (hd y (interior_subset hy)).differentiableAt.differentiableWithinAt)
    intro y hy
    rw [(hd y (interior_subset hy)).deriv]
    nlinarith [sq_nonneg (1 - y⁻¹)]
  have hh := hm (by simp : (1 : ℝ) ∈ Ici 1) hx hx
  simpa only [f, inv_one, sub_self, zero_div, log_one, sub_nonneg] using hh

/-- The single logarithm bound needed at the comparison threshold. -/
theorem log_1600_le : log (1600 : ℝ) ≤ 739 / 100 := by
  have h2 : log (2 : ℝ) ≤ 347 / 500 := by linarith [log_two_lt_d9]
  have h5 := log_le_half_sub_inv (by norm_num : (1 : ℝ) ≤ 5 / 4)
  norm_num only [inv_div, inv_one] at h5
  have he : log (1600 : ℝ) = 10 * log 2 + 2 * log (5 / 4) := by
    rw [show (1600 : ℝ) = 2 ^ 10 * (5 / 4) ^ 2 by norm_num,
      log_mul (by norm_num) (by norm_num), log_pow, log_pow]
    norm_num
  rw [he]
  linarith

private def coarseChebyshevGap (x : ℝ) : ℝ :=
  (191 / 1600) * x - (3 / 8) * log (x ^ 2 + 1) - 2

private theorem coarseChebyshevGap_pos {x : ℝ} (hx : (1999 / 50 : ℝ) ≤ x) :
    0 < coarseChebyshevGap x := by
  have hd (y : ℝ) : HasDerivAt coarseChebyshevGap
      ((191 / 1600) - (3 / 4) * y / (y ^ 2 + 1)) y := by
    have hp : 0 < y ^ 2 + 1 := by positivity
    have hl := ((((hasDerivAt_id y).pow 2).add_const 1).log hp.ne').const_mul (3 / 8)
    have hh := (((hasDerivAt_id y).const_mul (191 / 1600)).sub hl).sub_const 2
    convert hh using 1
    · rfl
    · norm_num
      ring
  have hm : MonotoneOn coarseChebyshevGap (Ici (1999 / 50)) := by
    apply monotoneOn_of_deriv_nonneg (convex_Ici _)
      (fun y _ ↦ (hd y).continuousAt.continuousWithinAt)
      (fun y _ ↦ (hd y).differentiableAt.differentiableWithinAt)
    intro y hy
    have hy' : (1999 / 50 : ℝ) ≤ y := interior_subset hy
    rw [(hd y).deriv]
    apply sub_nonneg.mpr
    apply (div_le_iff₀ (by positivity : 0 < y ^ 2 + 1)).mpr
    nlinarith [sq_nonneg (y - 10)]
  have hlog : log (((1999 / 50 : ℝ) ^ 2) + 1) ≤ 739 / 100 :=
    (log_le_log (by norm_num) (by norm_num : ((1999 / 50 : ℝ) ^ 2) + 1 ≤ 1600)).trans log_1600_le
  have hbase : 0 < coarseChebyshevGap (1999 / 50) := by
    dsimp only [coarseChebyshevGap]
    linarith
  exact hbase.trans_le (hm (by simp) hx hx)

/-- A rigorous four-decimal shooting enclosure suffices to improve the
leading Chebyshev lower estimate at every kappa>=1600. -/
theorem half_upper_lt_chebyshev_leading {a κ : ℝ} (ha : a ≤ 333 / 250) (hκ : 1600 ≤ κ) :
    a / 2 * sqrt (κ - 1) + (3 / 8) * log κ + 3 / 2 <
      (π / 4) * sqrt (κ - 1) - 1 / 2 := by
  have hx : (1999 / 50 : ℝ) ≤ sqrt (κ - 1) := by
    apply (le_sqrt (by norm_num) (by linarith : 0 ≤ κ - 1)).mpr
    nlinarith
  have hg := coarseChebyshevGap_pos hx
  have hs := sq_sqrt (by linarith : 0 ≤ κ - 1)
  have hlog : sqrt (κ - 1) ^ 2 + 1 = κ := by linarith
  dsimp only [coarseChebyshevGap] at hg
  rw [hlog] at hg
  have hπ : 191 / 1600 ≤ π / 4 - a / 2 := by linarith [pi_gt_d4]
  have hh := mul_le_mul_of_nonneg_right hπ (sqrt_nonneg (κ - 1))
  nlinarith

/-- The actual source half-gamma finite upper bound improves on the
actual sampled-sech Chebyshev majorant for every kappa>=1600. -/
theorem half_finite_upper_lt_sampledSech (I : chebyshev1.SpectralInterval)
    (G : SubcriticalGraph (1 / 2)) (hκ : 1600 ≤ I.kappa) :
    finiteDesignUpper I (1 / 2) (1 / 2) G.σ < sampledSech (designSpacing I) := by
  have hfirst := half_upper_lt_chebyshev_leading G.half_crossing_sqrt_le hκ
  have hθ := designSpacing_pos I
  have hroot : 0 < sqrt (I.kappa - 1) := sqrt_pos.mpr (by linarith)
  have hθroot : designSpacing I * sqrt (I.kappa - 1) ≤ 2 :=
    (le_div_iff₀ hroot).mp (designSpacing_bounds I).2
  have hlead : (π / 4) * sqrt (I.kappa - 1) ≤ π / (2 * designSpacing I) := by
    apply (le_div_iff₀ (mul_pos (by norm_num : (0 : ℝ) < 2) hθ)).mpr
    nlinarith [mul_le_mul_of_nonneg_left hθroot pi_pos.le]
  have hpoisson := (poisson_remainders_pos hθ).1
  have hG := G.positive (by norm_num : (0 : ℝ) < 1 / 2)
    (by norm_num : (1 / 2 : ℝ) < 1) (by norm_num : (0 : ℝ) < 1)
  have hv : feedbackValue (1 / 2) G.σ 1 = sqrt (G.σ 1) := by
    dsimp only [feedbackValue]
    field_simp [(sqrt_pos.mpr hG).ne']
    nlinarith [sq_sqrt hG.le]
  have he : finiteDesignUpper I (1 / 2) (1 / 2) G.σ =
      sqrt (G.σ 1) / 2 * sqrt (I.kappa - 1) + (3 / 8) * log I.kappa + 3 / 2 := by
    rw [finiteDesignUpper, hv]
    ring
  rw [he]
  linarith

/-- The retained comparison holds for the genuine infinite optimized
criterion, with no assumed numerical value of the continuum constant. -/
theorem infinitePowerValue_half_lt_sampledSech (I : chebyshev1.SpectralInterval)
    (hκ : 1600 ≤ I.kappa) :
    infinitePowerValue I (1 / 2) < sampledSech (designSpacing I) := by
  obtain ⟨G⟩ := exists_subcriticalGraph (by norm_num : (0 : ℝ) < 1 / 2)
    (by norm_num : (1 / 2 : ℝ) < 1)
  have hgraph : ∀ r ≥ 1, FeedbackGraphAt (1 / 2) G.σ r := fun r hr ↦
    subcritical_feedbackGraphAt G (by norm_num) (by norm_num) (by linarith)
  have hlog : ∀ r ≥ 1, 0 ≤ logSlope G.σ r ∧ logSlope G.σ r ≤ 1 / 2 := fun r hr ↦
    SubcriticalGraph.logSlope_bounds G (by norm_num) (by norm_num) (by linarith)
  exact (infinitePowerValue_sharp_upper I (by norm_num) (by norm_num) (by norm_num) hgraph hlog).trans_lt
    (half_finite_upper_lt_sampledSech I G hκ)

/-- Every genuine finite optimized criterion satisfies the same strict
Chebyshev comparison under the printed condition-number threshold. -/
theorem optimalValue_half_lt_sampledSech (I : chebyshev1.SpectralInterval) (M : ℕ)
    (hκ : 1600 ≤ I.kappa) :
    optimalValue I M (fun _ ↦ 1) (1 / 2) < sampledSech (designSpacing I) := by
  obtain ⟨G⟩ := exists_subcriticalGraph (by norm_num : (0 : ℝ) < 1 / 2)
    (by norm_num : (1 / 2 : ℝ) < 1)
  have hgraph : ∀ r ≥ 1, FeedbackGraphAt (1 / 2) G.σ r := fun r hr ↦
    subcritical_feedbackGraphAt G (by norm_num) (by norm_num) (by linarith)
  have hlog : ∀ r ≥ 1, 0 ≤ logSlope G.σ r ∧ logSlope G.σ r ≤ 1 / 2 := fun r hr ↦
    SubcriticalGraph.logSlope_bounds G (by norm_num) (by norm_num) (by linarith)
  exact (optimalValue_sharp_upper I M (by norm_num) (by norm_num) (by norm_num) hgraph hlog).trans_lt
    (half_finite_upper_lt_sampledSech I G hκ)

end
end krylov.Asymptotics
