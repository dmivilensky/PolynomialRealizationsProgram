import polyak.Spiral.Feasibility
import polyak.Spiral.Threshold
import polyak.Realization.Rate
import polyak.Realization.Polyak
import polyak.Threshold.Upper

/-!
Article: threshold lower bound and the special spiral from rest.
Use: one actual function in dimension three and one initial point work for every
horizon; the lower rate is the root of the original quartic.
Proof: instantiate the proved one-coordinate initialization with the explicit singleton spectrum.
-/

noncomputable section

namespace polyak.Threshold

open Spectral Waves Dynamics

/-- Article: the actual spiral exponent for the source curvature pair. -/
def spiralExponent (μ L : ℝ) : ℝ := Real.log (Spiral.factor (polyakQ μ L))

/-- Article: the one-atom spectral feasibility required by source initialization. -/
theorem source_spiral_feasible {μ L : ℝ} (hμ : 0 < μ) (hL : μ < L) :
    MixtureFeasible
      (finiteSpectrum (fun _ : Fin 1 => (1 : NNReal)) (fun _ => Spiral.atom (spiralExponent μ L))
        (by simp))
      (multiplierMap (normalizedA μ L (polyakAlpha μ L) (polyakBeta μ L))
        (normalizedB μ L (polyakAlpha μ L)) (polyakBeta μ L) (spiralExponent μ L))
      (Spiral.valueConstant (spiralExponent μ L)) (spiralExponent μ L) := by
  rw [Spiral.finiteSpectrum_one_eq,polyak_normalizedA hμ hL,polyak_normalizedB hμ hL]
  exact Spiral.actual_mixture_feasible (polyakQ_pos hμ hL) (polyakQ_lt_one hμ hL)

/-- Article: strict source minimizer reserve, required only for a growing spiral. -/
theorem source_spiral_strict {μ L : ℝ} (hμ : 0 < μ) (hL : μ < L) :
    |Spiral.valueConstant (spiralExponent μ L)| <
      spectrumG
        (finiteSpectrum (fun _ : Fin 1 => (1 : NNReal)) (fun _ => Spiral.atom (spiralExponent μ L))
          (by simp))
        (multiplierMap (normalizedA μ L (polyakAlpha μ L) (polyakBeta μ L))
          (normalizedB μ L (polyakAlpha μ L)) (polyakBeta μ L) (spiralExponent μ L)) := by
  rw [Spiral.finiteSpectrum_one_eq,polyak_normalizedA hμ hL,polyak_normalizedB hμ hL]
  simp only [polyakBeta,spiralExponent]
  rw [Spiral.actual_mixture_gap (polyakQ_pos hμ hL) (polyakQ_lt_one hμ hL)]
  exact Spiral.abs_valueConstant_lt_gap _

/-- Article: the realized special spiral from zero impulse, in exactly three real dimensions.
Use: the function and its start are independent of the horizon.
The explicit universal constant 1/√5 is the separate finite-certificate task in stage eleven. -/
theorem exists_spiral_example {μ L : ℝ} (hμ : 0 < μ) (hL : μ < L) :
    ∃ f : EuclideanSpace ℝ (Fin 3) → ℝ, CenteredSmoothStronglyConvex μ L f ∧
      ∃ x₀, x₀ ≠ 0 ∧ ∃ c₀ : ℝ, 0 < c₀ ∧ ∀ N : ℕ,
        c₀*Spiral.factor (polyakQ μ L)^N*‖x₀‖ ≤
          ‖iterate (gradient f) (polyakAlpha μ L) (polyakBeta μ L) x₀ N‖ := by
  have hβ := polyakBeta_mem hμ hL
  have hresult := Realization.exists_startup hμ hL
    (polyakAlpha_pos hμ hL) hβ.1 hβ.2 (polyak_quadratic_condition hμ hL).2
    (fun _ : Fin 1 => (1 : NNReal)) (fun _ => Spiral.atom (spiralExponent μ L)) (by simp)
    (source_spiral_feasible hμ hL) (fun _ => source_spiral_strict hμ hL)
  obtain ⟨f,hf,x₀,hx,c₀,hc,hbound⟩ := hresult
  refine ⟨f,hf,x₀,hx,c₀,hc,fun N => ?_⟩
  have he : Real.exp (N*spiralExponent μ L) = Spiral.factor (polyakQ μ L)^N := by
    rw [Real.exp_nat_mul,spiralExponent,Real.exp_log
      (Spiral.factor_spec (polyakQ_pos hμ hL) (polyakQ_lt_one hμ hL)).1]
  have hh := hbound N
  rw [he] at hh
  convert hh using 1 <;> rfl

/-- Article: the original nonlinear rate is at least the realized spiral factor. -/
theorem spiralFactor_le_originalRate {μ L : ℝ} (hμ : 0 < μ) (hL : μ < L) :
    Spiral.factor (polyakQ μ L) ≤ rate μ L (polyakAlpha μ L) (polyakBeta μ L) := by
  have hβ := polyakBeta_mem hμ hL
  have hh := Realization.exp_le_originalRate hμ hL
    (polyakAlpha_pos hμ hL) hβ.1 hβ.2 (polyak_quadratic_condition hμ hL).2
    (fun _ : Fin 1 => (1 : NNReal)) (fun _ => Spiral.atom (spiralExponent μ L)) (by simp)
    (source_spiral_feasible hμ hL) (fun _ => source_spiral_strict hμ hL)
  rwa [spiralExponent,Real.exp_log
    (Spiral.factor_spec (polyakQ_pos hμ hL) (polyakQ_lt_one hμ hL)).1] at hh

/-- Article: exact critical rate, using the three-cycle lower spectrum and strict strip upper bound. -/
theorem original_polyakRate_critical {μ L : ℝ} (hμ : 0 < μ) (hL : μ < L)
    (hc : polyakQ μ L = criticalQ) :
    rate μ L (polyakAlpha μ L) (polyakBeta μ L) = 1 := by
  apply le_antisymm
  · exact (original_polyakRate_le_growth hμ hL).trans (by
      rw [hc]
      exact polyakGrowthRate_critical_le_one)
  · have hh := spiralFactor_le_originalRate hμ hL
    rwa [hc,Spiral.factor_critical] at hh

/-- Article: every supercritical source condition has worst-case rate strictly greater than one. -/
theorem one_lt_original_polyakRate {μ L : ℝ} (hμ : 0 < μ) (hL : μ < L)
    (hc : criticalQ < polyakQ μ L) :
    1 < rate μ L (polyakAlpha μ L) (polyakBeta μ L) :=
  (Spiral.one_lt_factor (polyakQ_pos hμ hL) (polyakQ_lt_one hμ hL) hc).trans_le
    (spiralFactor_le_originalRate hμ hL)

end polyak.Threshold
