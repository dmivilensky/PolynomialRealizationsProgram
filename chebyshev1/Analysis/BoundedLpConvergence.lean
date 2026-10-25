import Mathlib.MeasureTheory.Function.LpSeminorm.Basic
import Mathlib.MeasureTheory.Integral.Lebesgue.DominatedConvergence

/-!
Article: chebyshev1, Theorem 5.1.
Bounded pointwise convergence on a finite measure space implies every finite Lp convergence.
Use: `chebyshev1.Analysis.bounded_tendsto_eLpNorm` feeds
`chebyshev1.SineJacobi.greenProfile_eLpNorm_limit` (E.3: the actual Green step profiles converge
in every finite Lp, including L2).
Proof chain: `chebyshev1.SineJacobi.diagonalProfile_eLpNorm_limit` — chebyshev1, Theorem 5.1;
Endpoint-profile L2 convergence and limiting Green energy.
Source: mathlib, Mathlib.MeasureTheory.Function.LpSeminorm.Basic,
Mathlib.MeasureTheory.Integral.Lebesgue.DominatedConvergence — bounded convergence in finite Lp
spaces. The needed form is proved here.
-/
namespace chebyshev1.Analysis
noncomputable section
open Filter Topology MeasureTheory
open scoped ENNReal

/--
Bounded pointwise convergence on a finite measure space implies every finite Lp convergence.

Convergence along the specified source filter to the specified limit: `Tendsto (fun n =>
eLpNorm (fun x => F n x-f x) p μ) atTop (𝓝 0)`.

Use: `chebyshev1.SineJacobi.diagonalProfile_eLpNorm_limit` uses this limit to establish
convergence along the specified source filter to the specified limit: `Tendsto (fun N : ℕ =>
eLpNorm (fun t => diagonalProfile N t-sineDensity t) p (volume.restrict (Ioo (0:ℝ) 1))) atTop
(𝓝 0)`.

Article: chebyshev1, Theorem 5.1 via
`chebyshev1.SineJacobi.diagonalProfile_eLpNorm_limit`.

Source: mathlib, Mathlib.MeasureTheory.Function.LpSeminorm.Basic,
Mathlib.MeasureTheory.Integral.Lebesgue.DominatedConvergence — bounded convergence in finite Lp
spaces.

Proof: Intersect the eventual or almost-everywhere hypotheses, then prove the asserted relation
at an arbitrary point in that intersection. Prove equality of functions by evaluating both
sides at an arbitrary argument.
-/
theorem bounded_tendsto_eLpNorm {α : Type*} [MeasurableSpace α] {μ : Measure α}
    [IsFiniteMeasure μ] {F : ℕ → α → ℝ} {f : α → ℝ} {C : ℝ} {p : ℝ≥0∞}
    (hp0 : p ≠ 0) (hpt : p ≠ ∞) (_hC : 0 ≤ C)
    (hF : ∀ n, AEStronglyMeasurable (F n) μ) (hf : AEStronglyMeasurable f μ)
    (hFb : ∀ᶠ n in atTop, ∀ᵐ x ∂μ, ‖F n x‖ ≤ C)
    (hfb : ∀ᵐ x ∂μ, ‖f x‖ ≤ C)
    (hlim : ∀ᵐ x ∂μ, Tendsto (fun n => F n x) atTop (𝓝 (f x))) :
    Tendsto (fun n => eLpNorm (fun x => F n x-f x) p μ) atTop (𝓝 0) := by
  -- Intersect the eventual or almost-everywhere hypotheses, then prove the asserted relation
  -- at an arbitrary point in that intersection.
  have hp : 0 < p.toReal := ENNReal.toReal_pos hp0 hpt
  have hd (n : ℕ) : AEStronglyMeasurable (fun x => F n x-f x) μ := (hF n).sub hf
  have hb : ∀ᶠ n in atTop, ∀ᵐ x ∂μ,
      ‖F n x-f x‖ₑ ^ p.toReal ≤ (ENNReal.ofReal (2*C)) ^ p.toReal := by
    filter_upwards [hFb] with n hn
    filter_upwards [hn, hfb] with x hx hfx
    apply ENNReal.rpow_le_rpow _ hp.le
    rw [← ofReal_norm]
    apply ENNReal.ofReal_le_ofReal
    exact (norm_sub_le _ _).trans (by linarith)
  have hi := tendsto_lintegral_filter_of_dominated_convergence'
    (μ := μ) (bound := fun _ => ENNReal.ofReal (2*C)^p.toReal)
    (F := fun n x => ‖F n x-f x‖ₑ ^ p.toReal) (f := fun _ => 0)
    (Eventually.of_forall fun n => (hd n).aemeasurable.enorm.pow_const _) hb
    (show (∫⁻ _, ENNReal.ofReal (2*C)^p.toReal ∂μ) ≠ ∞ from by
      rw [lintegral_const]; finiteness)
    (show ∀ᵐ x ∂μ, Tendsto (fun n => ‖F n x-f x‖ₑ ^ p.toReal) atTop (𝓝 0) from by
      filter_upwards [hlim] with x hx
      have h := (hx.sub (tendsto_const_nhds (x := f x))).enorm
      simpa only [sub_self, enorm_zero, ENNReal.zero_rpow_of_pos hp, Function.comp_def] using
        (ENNReal.continuous_rpow_const (y := p.toReal)).continuousAt.tendsto.comp h)
  simp only [lintegral_zero] at hi
  have hh := (ENNReal.continuous_rpow_const (y := 1/p.toReal)).continuousAt.tendsto.comp hi
  simp only [ENNReal.zero_rpow_of_pos (one_div_pos.mpr hp)] at hh
  convert hh using 1
  funext n
  exact eLpNorm_eq_lintegral_rpow_enorm_toReal hp0 hpt (hd n)

end
end chebyshev1.Analysis
